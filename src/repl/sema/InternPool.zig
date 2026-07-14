//! Runtime-only port of the compiler's `src/InternPool.zig`. Drops
//! incremental-compilation machinery (`*_deps`, `TrackedInst`, `AnalUnit`,
//! thread sharding, `memoized_call`) and keeps the canonical-storage core.
//!
//! Reference: src/InternPool.zig in the Zig compiler tree.

const std = @import("std");
const assert = std.debug.assert;
const Allocator = std.mem.Allocator;
const BigIntConst = std.math.big.int.Const;

const InternPool = @This();

/// Stable handle into the pool. The first `first_dynamic_index` slots are
/// reserved for well-known entries populated by `init`; later slots come
/// from dynamic interning. `none` is the null sentinel.
///
/// Ordering mirrors the compiler's enum so `SimpleType`/`SimpleValue` can
/// pin variant values to the corresponding Index via `@intFromEnum`.
pub const Index = enum(u32) {
    // Fixed-width integer types (Key.int_type). Slot ordering and
    // membership mirrors `std.zig.Zir.Inst.Ref` so a Zir ref's
    // integer value can be used as an `Index` directly for
    // well-known slots -- the identity in `Sema.wellKnownRefToValue`
    // depends on this 1:1 alignment.
    u0_type,
    u1_type,
    u8_type,
    i8_type,
    u16_type,
    i16_type,
    u29_type,
    u32_type,
    i32_type,
    u64_type,
    i64_type,
    u80_type,
    u128_type,
    i128_type,
    u256_type,

    // Target-dependent / nominal primitive types (Key.simple_type).
    usize_type,
    isize_type,
    c_char_type,
    c_short_type,
    c_ushort_type,
    c_int_type,
    c_uint_type,
    c_long_type,
    c_ulong_type,
    c_longlong_type,
    c_ulonglong_type,
    c_longdouble_type,

    // Float types (Key.simple_type).
    f16_type,
    f32_type,
    f64_type,
    f80_type,
    f128_type,

    // Language-primitive types (Key.simple_type).
    anyopaque_type,
    bool_type,
    void_type,
    type_type,
    anyerror_type,
    comptime_int_type,
    comptime_float_type,
    noreturn_type,
    anyframe_type,
    null_type,
    undefined_type,
    enum_literal_type,

    // Pointer/slice specializations (Key.ptr_type).
    ptr_usize_type,
    ptr_const_comptime_int_type,
    manyptr_u8_type,
    manyptr_const_u8_type,
    manyptr_const_u8_sentinel_0_type,
    slice_const_u8_type,
    slice_const_u8_sentinel_0_type,

    manyptr_const_slice_const_u8_type,
    slice_const_slice_const_u8_type,

    optional_type_type,
    manyptr_const_type_type,
    slice_const_type_type,

    // Vector specializations (Key.vector_type).
    vector_8_i8_type,
    vector_16_i8_type,
    vector_32_i8_type,
    vector_64_i8_type,
    vector_1_u8_type,
    vector_2_u8_type,
    vector_4_u8_type,
    vector_8_u8_type,
    vector_16_u8_type,
    vector_32_u8_type,
    vector_64_u8_type,
    vector_2_i16_type,
    vector_4_i16_type,
    vector_8_i16_type,
    vector_16_i16_type,
    vector_32_i16_type,
    vector_4_u16_type,
    vector_8_u16_type,
    vector_16_u16_type,
    vector_32_u16_type,
    vector_2_i32_type,
    vector_4_i32_type,
    vector_8_i32_type,
    vector_16_i32_type,
    vector_4_u32_type,
    vector_8_u32_type,
    vector_16_u32_type,
    vector_2_i64_type,
    vector_4_i64_type,
    vector_8_i64_type,
    vector_2_u64_type,
    vector_4_u64_type,
    vector_8_u64_type,
    vector_1_u128_type,
    vector_2_u128_type,
    vector_1_u256_type,
    vector_4_f16_type,
    vector_8_f16_type,
    vector_16_f16_type,
    vector_32_f16_type,
    vector_2_f32_type,
    vector_4_f32_type,
    vector_8_f32_type,
    vector_16_f32_type,
    vector_2_f64_type,
    vector_4_f64_type,
    vector_8_f64_type,

    optional_noreturn_type,
    anyerror_void_error_union_type,
    /// Used for the inferred error set of inline/comptime function calls.
    adhoc_inferred_error_set_type,
    /// A type that is unknown until a generic function is instantiated:
    /// the declared type of a generic parameter or return whose value
    /// depends on a comptime argument. `evalFunc` stores it as a func's
    /// return type when AstGen marks the signature generic; `evalCall`
    /// re-resolves the concrete type once the comptime args are bound.
    generic_poison_type,
    /// The zero-field tuple type -- `@TypeOf(.{})`.
    empty_tuple_type,

    // Values.
    /// `undefined` (untyped)
    undef,
    /// `@as(bool, undefined)`
    undef_bool,
    /// `@as(usize, undefined)`
    undef_usize,
    /// `@as(u1, undefined)`
    undef_u1,
    /// `0` (comptime_int)
    zero,
    /// `@as(usize, 0)`
    zero_usize,
    /// `@as(u1, 0)`
    zero_u1,
    /// `@as(u8, 0)`
    zero_u8,
    /// `1` (comptime_int)
    one,
    /// `@as(usize, 1)`
    one_usize,
    /// `@as(u1, 1)`
    one_u1,
    /// `@as(u8, 1)`
    one_u8,
    /// `@as(u8, 4)`
    four_u8,
    /// `-1` (comptime_int)
    negative_one,
    /// `{}`
    void_value,
    /// `unreachable` (noreturn)
    unreachable_value,
    /// `null` (untyped)
    null_value,
    /// `true`
    bool_true,
    /// `false`
    bool_false,
    /// `.{}` -- the empty tuple value, of type `empty_tuple_type`.
    empty_tuple,

    /// Used by Air/Sema only.
    none = std.math.maxInt(u32),

    _,

    /// Range bounds for well-known types. Anything strictly between these
    /// (inclusive) is a type whose Key shape can be looked up via `get`
    /// without further checks. Dynamic indices fall outside this range.
    pub const first_type: Index = .u0_type;
    pub const last_type: Index = .empty_tuple_type;
    pub const first_value: Index = .undef;
    pub const last_value: Index = .empty_tuple;

    pub fn isWellKnownType(index: Index) bool {
        const raw = @intFromEnum(index);
        return raw >= @intFromEnum(first_type) and raw <= @intFromEnum(last_type);
    }

    pub fn isWellKnownValue(index: Index) bool {
        const raw = @intFromEnum(index);
        return raw >= @intFromEnum(first_value) and raw <= @intFromEnum(last_value);
    }
};

const first_dynamic_index: u32 = @intFromEnum(Index.empty_tuple) + 1;

/// Stable handle to an interned, null-terminated string. Mirrors the
/// compiler's `InternPool.NullTerminatedString` (`src/InternPool.zig`
/// ~1798): zero is the sentinel for the empty string; every other
/// value is an opaque index into the pool's string table that only
/// the pool itself decodes.
///
/// Known deviations from the compiler shape (single-threaded REPL):
///
///   * No thread-local sharding (`Zcu.PerThread.Id`) -- one storage.
///   * No `Slice` subtype yet -- the compiler exposes it for
///     `error_set_type.names` etc.; we add when a `Key` variant needs it.
pub const NullTerminatedString = enum(u32) {
    empty = 0,
    _,

    pub fn toOptional(string: NullTerminatedString) OptionalNullTerminatedString {
        return @enumFromInt(@intFromEnum(string));
    }

    /// Whether this interned string equals `slice`. Mirrors the compiler's
    /// `NullTerminatedString.eqlSlice`: compares an interned name against a
    /// literal (e.g. a field's `len`) without interning the literal.
    pub fn eqlSlice(string: NullTerminatedString, slice: []const u8, ip: *const InternPool) bool {
        return std.mem.eql(u8, ip.stringSlice(string), slice);
    }

    /// The string parsed as a base-10 `u32`, or null if it is not a canonical
    /// unsigned literal -- rejecting a leading zero and any `_` so a tuple field
    /// name like `"01"` or `"1_0"` is not a valid index. Verbatim from the
    /// compiler's `NullTerminatedString.toUnsigned` (used by `@hasField` on a
    /// tuple).
    pub fn toUnsigned(string: NullTerminatedString, ip: *const InternPool) ?u32 {
        const slice = ip.stringSlice(string);
        if (slice.len > 1 and slice[0] == '0') return null;
        if (std.mem.indexOfScalar(u8, slice, '_')) |_| return null;
        return std.fmt.parseUnsigned(u32, slice, 10) catch null;
    }

    const FormatData = struct {
        string: NullTerminatedString,
        ip: *const InternPool,
        id: bool,
    };
    fn format(data: FormatData, writer: *std.Io.Writer) std.Io.Writer.Error!void {
        const slice = data.ip.stringSlice(data.string);
        if (!data.id) {
            try writer.writeAll(slice);
        } else {
            try writer.print("{f}", .{std.zig.fmtIdP(slice)});
        }
    }

    pub fn fmt(string: NullTerminatedString, ip: *const InternPool) std.fmt.Alt(FormatData, format) {
        return .{ .data = .{ .string = string, .ip = ip, .id = false } };
    }

    pub fn fmtId(string: NullTerminatedString, ip: *const InternPool) std.fmt.Alt(FormatData, format) {
        return .{ .data = .{ .string = string, .ip = ip, .id = true } };
    }
};

/// Optional version of `NullTerminatedString`. Sentinel `none` is
/// `maxInt(u32)`, matching the compiler's `OptionalNullTerminatedString`
/// (`src/InternPool.zig` ~1902) so a caller can `@bitCast` /
/// `@enumFromInt` between the two enums.
pub const OptionalNullTerminatedString = enum(u32) {
    none = std.math.maxInt(u32),
    _,

    pub fn init(maybe_string: ?NullTerminatedString) OptionalNullTerminatedString {
        const string = maybe_string orelse return .none;
        return string.toOptional();
    }

    pub fn unwrap(opt: OptionalNullTerminatedString) ?NullTerminatedString {
        if (opt == .none) return null;
        return @enumFromInt(@intFromEnum(opt));
    }
};

/// Navigable declaration. Mirrors the compiler's `InternPool.Nav`
/// (`src/InternPool.zig` ~544): a named decl whose value may or may
/// not be resolved. `Nav.Index` is the stable handle interned in
/// `pool.navs`.
///
/// Known deviations from full compiler shape, each documented at
/// its field site:
///
///   * `analysis.zir_index` is a `Zir.Inst.Index`, not a
///     `TrackedInst.Index`. `TrackedInst` is the compiler's
///     incremental-compilation bookkeeping (a ZIR instruction
///     tracked across edits between recompiles). The REPL re-parses
///     each line; there is no incremental mode. Porting `TrackedInst`
///     would drag in `src/Zcu/PerThread.zig` and the change-tracking
///     subsystem for zero runtime gain.
///   * `analysis` is always `null` in REPL today. We evaluate
///     eagerly in `bindDecls` and populate `resolved` directly;
///     the field is preserved so the type matches the compiler's
///     exactly, but flipping it to non-`null` is the hook for any
///     future lazy mode.
///   * Backing storage is `ArrayListUnmanaged(Nav)` rather than the
///     compiler's `MultiArrayList(Repr)` with pack/unpack. The
///     compiler's column layout pays off in its multi-threaded
///     resize-hot path; the REPL's single-threaded usage doesn't
///     benefit, and the pack/unpack indirection costs readability.
///     Migration is internal -- public API (`getNav` / `navPtr` /
///     `createNav`) is identical to the compiler's.
pub const Nav = struct {
    /// Unqualified name of this Nav (the identifier under which a
    /// namespace lookup would find it).
    name: NullTerminatedString,
    /// Fully-qualified name, including any parent-namespace prefix.
    /// For the session root the parent prefix is empty, so `fqn` and
    /// `name` typically agree. Mirrors the compiler's `Nav.fqn`, which
    /// feeds `@typeName` and qualified diagnostics; the REPL has no reader
    /// yet (the qualified name reaches the struct namer via
    /// `Sema.type_name_ctx`), so it is populated ahead of that consumer.
    fqn: NullTerminatedString,
    /// Populated IFF this Nav is resolved by semantic analysis. The
    /// compiler uses `analysis != null` to mean "Nav exists but not
    /// yet analysed; Sema will analyse on demand". REPL evaluates
    /// eagerly so this is always `null` today.
    analysis: ?struct {
        namespace: NamespaceIndex,
        zir_index: std.zig.Zir.Inst.Index,
        wanted: bool,
    },
    /// `null` IFF semantic analysis has not yet resolved this Nav.
    /// In REPL `bindDecls` populates it eagerly, so non-generic
    /// flows always see `resolved != null`.
    resolved: ?Resolved,

    pub const Resolved = struct {
        /// Resolved type of the Nav. Never `.none` -- if the type
        /// isn't known the whole `Resolved` is `null`.
        type: InternPool.Index,
        @"align": Alignment,
        @"linksection": OptionalNullTerminatedString,
        @"addrspace": std.lang.AddressSpace,
        @"const": bool,
        @"threadlocal": bool,
        /// True IFF this Nav binds an `extern` decl (`linkage == .@"extern"`).
        is_extern_decl: bool,
        /// The decl's value. Compiler shape: `.none` is the
        /// "type resolved but value not yet" sentinel -- NOT an
        /// optional. The eager evaluator always populates it
        /// with a real index for `.@"const"` / `.@"var"` kinds.
        value: InternPool.Index,
    };

    /// Stable handle into `pool.navs`. Opaque integer so callers
    /// cannot confuse it with `InternPool.Index` or arithmetic-into
    /// the storage array.
    pub const Index = enum(u32) { _ };
};

/// Stable handle into `pool.namespaces`. Defined here so `Nav`'s
/// `analysis.namespace` field can reference it without forward-
/// declaration acrobatics.
pub const NamespaceIndex = enum(u32) { _ };

pub const OptionalNamespaceIndex = enum(u32) {
    none = std.math.maxInt(u32),
    _,

    pub fn init(maybe_ns: ?NamespaceIndex) OptionalNamespaceIndex {
        const ns = maybe_ns orelse return .none;
        return @enumFromInt(@intFromEnum(ns));
    }

    pub fn unwrap(opt: OptionalNamespaceIndex) ?NamespaceIndex {
        if (opt == .none) return null;
        return @enumFromInt(@intFromEnum(opt));
    }
};

/// Stable handle into the file table. Defined here so `Namespace.file_scope`
/// matches the compiler's `Zcu.File.Index` type. Same shape as `src/Zcu.zig:1232`.
pub const FileIndex = enum(u32) { _ };

/// Optional `FileIndex`. The REPL session-root namespace uses `.none`
/// because there is no on-disk file backing it; module
/// loading populates real file indices for loaded modules. Stdlib's
/// compiler keeps `Namespace.file_scope` non-optional because every
/// compiler namespace originates from a parsed file -- we deviate to
/// `Optional` so the session root has a place to live without a
/// synthetic "<repl>" file entry.
pub const OptionalFileIndex = enum(u32) {
    none = std.math.maxInt(u32),
    _,

    pub fn init(maybe_file: ?FileIndex) OptionalFileIndex {
        const file = maybe_file orelse return .none;
        return @enumFromInt(@intFromEnum(file));
    }

    pub fn unwrap(opt: OptionalFileIndex) ?FileIndex {
        if (opt == .none) return null;
        return @enumFromInt(@intFromEnum(opt));
    }
};

/// Power-of-two alignment with an explicit `none` sentinel for
/// "implicit / use the type's natural alignment". Mirrors the
/// compiler's `Alignment` (`src/InternPool.zig` ~5793). Stdlib's
/// `std.mem.Alignment` covers the same power-of-two values but
/// without the `.none` sentinel that decl-attribute handling needs;
/// the compiler re-defines its own for that reason and so do we.
pub const Alignment = enum(u6) {
    @"1" = 0,
    @"2" = 1,
    @"4" = 2,
    @"8" = 3,
    @"16" = 4,
    @"32" = 5,
    @"64" = 6,
    none = std.math.maxInt(u6),
    _,

    /// Power-of-two byte count -> log2 alignment; `0` maps to `.none`
    /// (natural alignment). Mirrors the compiler's `Alignment.fromByteUnits`.
    pub fn fromByteUnits(n: u64) Alignment {
        if (n == 0) return .none;
        assert(std.math.isPowerOfTwo(n));
        return @enumFromInt(@ctz(n));
    }

    /// log2 alignment -> byte count, or `null` for `.none`. Mirrors the
    /// compiler's `Alignment.toByteUnits`.
    pub fn toByteUnits(a: Alignment) ?u64 {
        return switch (a) {
            .none => null,
            else => @as(u64, 1) << @intFromEnum(a),
        };
    }

    /// Compare two alignments, treating `.none` as the weakest. Mirrors the
    /// compiler's `Alignment.compare` / `toRelaxedCompareUnits`.
    pub fn compare(lhs: Alignment, op: std.math.CompareOperator, rhs: Alignment) bool {
        return std.math.compare(lhs.toRelaxedCompareUnits(), op, rhs.toRelaxedCompareUnits());
    }

    pub fn toRelaxedCompareUnits(a: Alignment) u8 {
        const n: u8 = @intFromEnum(a);
        assert(n <= @intFromEnum(Alignment.none));
        if (n == @intFromEnum(Alignment.none)) return 0;
        return n + 1;
    }
};

/// A `comptime { ... }` top-level block. Mirrors the compiler's
/// `InternPool.ComptimeUnit` (`src/InternPool.zig` ~498). Recorded so
/// `bindDecls` can register them in a namespace's `comptime_decls` list.
///
/// Known deviation: `zir_index` is `Zir.Inst.Index`, not
/// `TrackedInst.Index` (see `Nav.analysis.zir_index` for the
/// reasoning).
pub const ComptimeUnit = struct {
    zir_index: std.zig.Zir.Inst.Index,
    namespace: NamespaceIndex,

    pub const Id = enum(u32) { _ };
};

/// A lookup scope. Mirrors the compiler's `Zcu.Namespace`
/// (`src/Zcu.zig` ~844): a parent-chained map of named decls plus
/// side lists for tests and comptime blocks. Every field present in
/// the compiler's struct lives here too, even when the current
/// subset leaves it at a sentinel default -- the vestigial fields
/// make aggregates / modules / FFI additive rather than
/// schema-changing.
pub const Namespace = struct {
    parent: OptionalNamespaceIndex,
    /// The file backing this namespace. `.none` for the session-root
    /// namespace; the module loader populates real file
    /// indices for loaded modules. Stdlib keeps this non-optional
    /// because every compiler namespace originates from a parsed
    /// file -- we use `Optional` to give the session root a home.
    file_scope: OptionalFileIndex,
    /// Bumped each time the namespace is re-resolved during
    /// incremental compilation. REPL re-parses each line outright
    /// and has no incremental mode, so this stays `0`. Kept so a
    /// future incremental layer can flip it without a schema
    /// change.
    generation: u32,
    /// The struct / enum / union / opaque whose `Key` owns this
    /// namespace. `.none` for the session root; aggregates
    /// set it on inner namespaces created by `struct_decl` /
    /// `union_decl` / `enum_decl` / `opaque_decl`.
    owner_type: Index,
    /// Members of the namespace which are marked `pub`. Ordered for
    /// stable `:scope` enumeration and matches the compiler's choice
    /// of `ArrayHashMapUnmanaged(..., true)` (the `true` is
    /// `store_hash`, which preserves insertion order).
    pub_decls: std.ArrayHashMapUnmanaged(Nav.Index, void, NavNameContext, true),
    /// Members of the namespace which are *not* marked `pub`.
    priv_decls: std.ArrayHashMapUnmanaged(Nav.Index, void, NavNameContext, true),
    /// Tests in this namespace, in declaration order. Separate from
    /// `pub_decls` because tests don't participate in name lookup
    /// (the test runner enumerates them, the user can't reference
    /// them by name).
    test_decls: std.ArrayListUnmanaged(Nav.Index),
    /// `comptime { ... }` blocks in this namespace, in declaration
    /// order. Indices into `pool.comptime_units` rather than `Nav`
    /// because comptime blocks have no name / fqn / value-binding
    /// surface.
    comptime_decls: std.ArrayListUnmanaged(ComptimeUnit.Id),

    /// Hashmap context that keys `Nav.Index` entries by the bound
    /// nav's interned name. Holds `*const InternPool` so `hash` /
    /// `eql` can re-fetch the Nav on every probe -- the pool pointer
    /// is stable, but the Nav storage may relocate on resize, so
    /// holding a `*Nav` would dangle. Same shape as the compiler's
    /// `NavNameContext` (`src/Zcu.zig:864`).
    pub const NavNameContext = struct {
        pool: *const InternPool,

        pub fn hash(ctx: NavNameContext, nav: Nav.Index) u32 {
            const name = ctx.pool.getNav(nav).name;
            return std.hash.int(@intFromEnum(name));
        }

        pub fn eql(ctx: NavNameContext, a_nav: Nav.Index, b_nav: Nav.Index, b_index: usize) bool {
            _ = b_index;
            const a_name = ctx.pool.getNav(a_nav).name;
            const b_name = ctx.pool.getNav(b_nav).name;
            return a_name == b_name;
        }
    };

    /// Adapter that lets `pub_decls.getKeyAdapted(name, NameAdapter)`
    /// look up by an interned name without a sentinel Nav.Index.
    /// `bindDecls` uses this to check "does this name already exist
    /// in the namespace?" before inserting.
    pub const NameAdapter = struct {
        pool: *const InternPool,

        pub fn hash(_: NameAdapter, name: NullTerminatedString) u32 {
            return std.hash.int(@intFromEnum(name));
        }

        pub fn eql(ctx: NameAdapter, a_name: NullTerminatedString, b_nav: Nav.Index, b_index: usize) bool {
            _ = b_index;
            return a_name == ctx.pool.getNav(b_nav).name;
        }
    };

    /// Look up `name` in this namespace's `pub_decls` then `priv_decls`.
    /// Does NOT walk the parent chain -- that's `Sema.lookupName`'s
    /// job. Returns null when the name is absent from both maps.
    /// Mirrors the `lookupInNamespace` step inside the compiler's
    /// `lookupIdentifier` (`src/Sema.zig:5920`), which walks the
    /// pub/priv split via two separate `getKeyAdapted` calls.
    pub fn lookupNav(
        ns: *const Namespace,
        pool: *const InternPool,
        name: NullTerminatedString,
    ) ?Nav.Index {
        const adapter: NameAdapter = .{ .pool = pool };
        if (ns.pub_decls.getKeyAdapted(name, adapter)) |nav_idx| return nav_idx;
        return ns.priv_decls.getKeyAdapted(name, adapter);
    }
};

/// Each variant's integer value is the corresponding `Index`, so converting
/// between the two is identity.
pub const SimpleType = enum(u32) {
    usize = @intFromEnum(Index.usize_type),
    isize = @intFromEnum(Index.isize_type),
    c_char = @intFromEnum(Index.c_char_type),
    c_short = @intFromEnum(Index.c_short_type),
    c_ushort = @intFromEnum(Index.c_ushort_type),
    c_int = @intFromEnum(Index.c_int_type),
    c_uint = @intFromEnum(Index.c_uint_type),
    c_long = @intFromEnum(Index.c_long_type),
    c_ulong = @intFromEnum(Index.c_ulong_type),
    c_longlong = @intFromEnum(Index.c_longlong_type),
    c_ulonglong = @intFromEnum(Index.c_ulonglong_type),
    c_longdouble = @intFromEnum(Index.c_longdouble_type),
    f16 = @intFromEnum(Index.f16_type),
    f32 = @intFromEnum(Index.f32_type),
    f64 = @intFromEnum(Index.f64_type),
    f80 = @intFromEnum(Index.f80_type),
    f128 = @intFromEnum(Index.f128_type),
    anyopaque = @intFromEnum(Index.anyopaque_type),
    bool = @intFromEnum(Index.bool_type),
    void = @intFromEnum(Index.void_type),
    type = @intFromEnum(Index.type_type),
    anyerror = @intFromEnum(Index.anyerror_type),
    comptime_int = @intFromEnum(Index.comptime_int_type),
    comptime_float = @intFromEnum(Index.comptime_float_type),
    noreturn = @intFromEnum(Index.noreturn_type),
    null = @intFromEnum(Index.null_type),
    undefined = @intFromEnum(Index.undefined_type),
    enum_literal = @intFromEnum(Index.enum_literal_type),
    adhoc_inferred_error_set = @intFromEnum(Index.adhoc_inferred_error_set_type),
    generic_poison = @intFromEnum(Index.generic_poison_type),
};

/// Same identity trick as `SimpleType`: each variant's value is its `Index`.
pub const SimpleValue = enum(u32) {
    void = @intFromEnum(Index.void_value),
    null = @intFromEnum(Index.null_value),
    true = @intFromEnum(Index.bool_true),
    false = @intFromEnum(Index.bool_false),
    @"unreachable" = @intFromEnum(Index.unreachable_value),
};

pub const Key = union(enum) {
    simple_type: SimpleType,
    simple_value: SimpleValue,
    /// A bare enum literal (`.foo`), type `enum_literal_type`; carries only the
    /// name and coerces to a concrete enum/union on use.
    enum_literal: NullTerminatedString,
    /// Concrete fixed-width integer type. Shape matches `@typeInfo(T).int`.
    int_type: std.lang.Type.Int,
    /// Payload is `.none` for untyped `anyframe`, or the child type's
    /// Index for `anyframe->T`.
    anyframe_type: Index,
    /// An integer value tagged with its type. Mirrors the compiler's
    /// `Key.int`: storage holds the value as the narrowest variant that
    /// fits -- inline `u64`/`i64` for small magnitudes, `big_int` for
    /// arbitrary precision. For `big_int`, the limbs slice borrows from
    /// the pool's arena and is valid for the pool's lifetime.
    int: Int,
    /// A floating-point value tagged with its type. Mirrors the compiler's
    /// `Key.float`. The storage variant must match the type's bit width,
    /// except for `c_longdouble_type` (storage may be any width -- promoted
    /// to f128 on emit unless f80) and `comptime_float_type` (always
    /// f128).
    float: Float,
    /// `undefined` of type `Index`. Untyped `undefined` uses
    /// `.undefined_type` here; the well-known `Index.undef` slot stores
    /// exactly that shape.
    undef: Index,
    /// A pointer type (`*T`, `*const T`, `[*]T`, `[]T`, etc.). Mirrors
    /// the compiler's `Key.PtrType` -- the same shape but a subset of
    /// the flag set: what the alloc/store/load subset needs.
    ptr_type: PtrType,
    /// A pointer value.
    ptr: Ptr,
    /// A slice value: `{ty, ptr, len}`. Mirrors the compiler's `Key.Slice`
    /// (`ptr_slice`): `ptr` addresses the elements, `len` is a `usize` value.
    slice: Slice,
    /// An error set type (`error{Foo, Bar}`). The compiler keeps
    /// names sorted for deterministic dedup; we do the same. Names
    /// are interned via `getOrPutString` so two error-set types
    /// sharing the same name set hash and compare equal.
    error_set_type: ErrorSetType,
    /// An error value (`error.Foo`). Mirrors the compiler's
    /// `Key.err`: `ty` is the error-set type the value inhabits,
    /// `name` is the interned error name. The compiler's
    /// `zirErrorValue` constructs a *singleton* set per `error.X`
    /// expression so the value has a precise type, then composite
    /// sets get formed via union / coercion. We do the same.
    err: Error,
    /// An error-union type (`E!T`). Mirrors the compiler's
    /// `Key.ErrorUnionType`: the pair of an error-set type and a
    /// payload type. Two error-union types are equal IFF both
    /// component Indices match -- error_set sub-typing / supersetting
    /// is a coercion-time concern, not a Key-identity concern.
    error_union_type: ErrorUnionType,
    /// A value of an error-union type. Either an error (carrying
    /// just the name; the error-set type lives in `ty`'s payload)
    /// or a payload value of the union's payload type. Mirrors
    /// `Key.ErrorUnion` (`src/InternPool.zig` ~2382).
    error_union: ErrorUnion,
    /// A function type (`fn (P0, P1, ...) R`). Mirrors the
    /// compiler's `Key.FuncType` (`src/InternPool.zig` ~2154):
    /// same field set with the heavy incremental-compilation
    /// extras stripped. `comptime_bits` / `noalias_bits` are
    /// per-parameter bitmasks; the helper methods on `FuncType`
    /// return the per-index flag.
    func_type: FuncType,
    /// A function value. Mirrors `Key.Func` (`src/InternPool.zig`
    /// ~2228) with the comptime-only minimum: `ty` and the ZIR
    /// instruction that owns the body. The compiler's
    /// `analysis_extra_index` / `branch_quota_extra_index` /
    /// source-range fields are omitted -- no incremental compilation;
    /// same deferred-vestigial story as `Nav.analysis.zir_index`.
    func: Func,
    /// `[N]T` and `[N:s]T` array types. Stored across two
    /// `Item.Tag` entries: `type_array_small` (no sentinel, len fits
    /// in u32) and `type_array_big` (sentinel OR len >= 2^32).
    /// Mirrors the compiler's `Key.ArrayType` shape (`src/InternPool.zig`
    /// ~2098); the Tag split mirrors `type_array_small` / `type_array_big`
    /// (`src/InternPool.zig` ~4171-4172).
    array_type: ArrayType,
    /// `@Vector(len, child)`. A single `Item.Tag` (`type_vector`) since
    /// `len` is always a `u32` -- no big/small split like `array_type`.
    /// Mirrors the compiler's `Key.VectorType` (`src/InternPool.zig`
    /// ~2104) and its `type_vector` Tag (`src/InternPool.zig` ~4168).
    vector_type: VectorType,
    /// `?child`. Stored inline (`type_optional`, data = child Index)
    /// like `anyframe_type`. Mirrors the compiler's `Key.opt_type`
    /// (`src/InternPool.zig` ~1969).
    opt_type: Index,
    /// An optional value. `val == .none` means `null`; otherwise `val`
    /// is the payload Index (already of the optional's child type).
    /// Split across `opt_payload` (a `{ty, val}` repr) and `opt_null`
    /// (inline ty), mirroring the compiler's `Key.opt` / `Tag.opt_payload`
    /// + `opt_null` (`src/InternPool.zig` ~2006,4230,4231).
    opt: Opt,
    /// A tuple type: the per-field types. The compiler's `Key.TupleType`
    /// also carries a parallel `values` slice (comptime-field defaults);
    /// omitted here -- deferred, see `Sema.evalArrayInitAnon`.
    tuple_type: TupleType,
    /// A named struct type (`struct { x: i32 }`). Nominal: identity is
    /// `(source_zir_id, decl_inst, captures)` -- two distinct declarations are
    /// distinct types even with identical fields, and two instantiations of one
    /// generic decl differ by their captured values, mirroring the compiler's
    /// `ContainerType.declared` (`zir_index` + captures). `name` is the
    /// fully-qualified name baked at
    /// creation (`setTypeName`'s model), excluded from identity (the
    /// compiler keeps it in `LoadedStructType`, not the hash). A shell
    /// mirroring `getDeclaredStructType` (identity only) before lazy
    /// `resolveStructFieldTypes`: field names/types are resolved on
    /// demand from the decl's ZIR, not stored here.
    struct_type: StructType,
    /// A named enum type (`enum { a, b }`). Nominal, like `struct_type`:
    /// identity is `(source_zir_id, decl_inst, captures)`. Field names, the
    /// integer tag type, and per-field values are resolved on demand from the
    /// decl's ZIR (`enumFieldByName`), not stored here. Mirrors the compiler's
    /// `LoadedEnumType` shell before its fields are resolved.
    enum_type: EnumType,
    /// A named union type (`union(enum) { a: u8, b: u16 }`). Nominal like
    /// `enum_type`: identity is `(source_zir_id, decl_inst, captures)`; field
    /// names and types are resolved on demand from the decl's ZIR.
    union_type: UnionType,
    /// An aggregate value (array, vector, struct -- the type
    /// determines which). Storage is either an N-element slice or a
    /// single-element repetition. Mirrors compiler `Key.Aggregate`
    /// (`src/InternPool.zig` ~2542) split across `Item.Tag.aggregate`
    /// and `Item.Tag.repeated` (`src/InternPool.zig` ~4276,4283).
    /// `bytes`-storage flavor deferred until embedded-NUL string
    /// support arrives -- our `getOrPutString` asserts no embedded
    /// 0 bytes (`src/sema/InternPool.zig` ~`getOrPutString`), so we
    /// can't safely store an arbitrary `[]u8` array as a string yet.
    aggregate: Aggregate,
    /// An enum tag value: an enum type plus the integer tag it holds (an `int`
    /// value of the enum's integer tag type). Mirrors compiler `Key.EnumTag`.
    enum_tag: EnumTag,
    /// A union value: `{ty, tag, val}` -- the union type, the active field's tag,
    /// and its payload. Mirrors compiler `Key.un` (`Key.Union`); `tag` is an
    /// `enum_tag` of the union's generated tag enum. Stored under
    /// `Item.Tag.union_value`, as in the compiler.
    un: Union,

    pub const Int = struct {
        ty: Index,
        storage: Storage,

        pub const Storage = union(enum) {
            u64: u64,
            i64: i64,
            big_int: BigIntConst,

            /// Materialise the value as a `BigIntConst` regardless of
            /// storage variant. The returned slice borrows from either
            /// the pool's arena (`.big_int`) or the caller-provided
            /// `BigIntSpace` (`.u64` / `.i64`).
            pub fn toBigInt(storage: Storage, space: *BigIntSpace) BigIntConst {
                return switch (storage) {
                    .big_int => |b| b,
                    inline .u64, .i64 => |v| std.math.big.int.Mutable.init(&space.limbs, v).toConst(),
                };
            }

            /// Big enough to fit any non-`big_int` storage variant. The
            /// +1 is headroom so a `Mutable` built from this buffer can
            /// be incremented or decremented once without spilling.
            /// Matches the compiler's `Key.Int.Storage.BigIntSpace`.
            pub const BigIntSpace = struct {
                limbs: [(@sizeOf(u64) / @sizeOf(std.math.big.Limb)) + 1]std.math.big.Limb,
            };
        };
    };

    pub const Float = struct {
        ty: Index,
        /// The storage variant used must match the size of the float type
        /// being represented (except for `c_longdouble_type`, see the
        /// emit dispatcher).
        storage: Storage,

        pub const Storage = union(enum) {
            f16: f16,
            f32: f32,
            f64: f64,
            f80: f80,
            f128: f128,
        };
    };

    /// Pointer type. A subset of the compiler's `Key.PtrType` -- shape
    /// matches but the flag field carries only what the supported pointer
    /// syntax needs (size, alignment, is_const, is_volatile, is_allowzero,
    /// address_space). The compiler's `vector_index` and `packed_offset`
    /// (bit-range) field are omitted. An `extern struct` to match the
    /// compiler's `Key.PtrType` layout discipline.
    pub const PtrType = extern struct {
        child: Index,
        sentinel: Index = .none,
        flags: Flags = .{},

        pub const Flags = packed struct(u32) {
            size: Size = .one,
            /// `.none` means the pointee type's natural alignment; an explicit
            /// `*align(N) T` stores `Alignment.fromByteUnits(N)` verbatim, even
            /// when N equals the natural alignment. The compiler renders an
            /// explicit alignment verbatim too (`*align(4) u32`, not `*u32`),
            /// so the stored value is not normalised against the pointee's ABI
            /// alignment.
            alignment: Alignment = .none,
            is_const: bool = false,
            is_volatile: bool = false,
            is_allowzero: bool = false,
            address_space: AddressSpace = .generic,
            _reserved: u16 = 0,
        };

        // Reuse stdlib's enums verbatim -- same shape as the compiler's
        // `Key.PtrType.{Size,AddressSpace}` aliases at
        // `src/InternPool.zig:2093-2094`. Saves duplicating the variant
        // lists and stays in sync if stdlib adds CPU/GPU address spaces.
        pub const Size = std.lang.Type.Pointer.Size;
        pub const AddressSpace = std.lang.AddressSpace;
    };

    /// Pointer value. `ty` is the pointer's type (always a `ptr_type`
    /// Index). `base_addr` identifies the storage the pointer addresses and
    /// `byte_offset` the offset within it. `BaseAddr` is a subset of the
    /// compiler's `Key.Ptr.BaseAddr` (`src/InternPool.zig`).
    pub const Ptr = struct {
        ty: Index,
        base_addr: BaseAddr,
        byte_offset: u64,

        pub const BaseAddr = union(enum) {
            comptime_alloc: ComptimeAllocIndex,
            /// A pointer to a declaration's storage (`&x` where `x` is a decl).
            /// Reading resolves the Nav's value; a comptime store through it is
            /// rejected -- the decl is runtime storage the compiler defers to
            /// codegen. Mirrors the compiler's `BaseAddr.nav`.
            nav: Nav.Index,
            /// A pointer to a single unnamed constant value (`&"str"`,
            /// `&[_]T{...}`): the pointee is stored inline (`val`), so the
            /// pointer is self-contained and outlives the ephemeral
            /// `comptime_allocs` slots -- the REPL's cross-line analogue of the
            /// compiler promoting a comptime alloc to an anonymous decl in
            /// `make_ptr_const`. Mirrors the compiler's `BaseAddr.uav`.
            uav: Uav,
            /// A pointer to a field of an auto-layout aggregate: `base` is the
            /// parent pointer, `index` the field index. Mirrors the compiler's
            /// `BaseAddr.field`.
            field: BaseIndex,
            /// A pointer to an element of an array: `base` is the array pointer,
            /// `index` the element index. Mirrors the compiler's `BaseAddr.arr_elem`.
            /// Shares `BaseIndex` with `.field`; in this no-layout evaluator both
            /// resolve by index projection (the compiler splits them for byte
            /// stride vs field offset).
            arr_elem: BaseIndex,
            /// A pointer to the payload of an optional: `base` is the pointer to
            /// the optional (`*?T`), and loading resolves that optional's payload.
            /// Produced by `optional_payload_*_ptr` (`p.?` in an lvalue context).
            /// Mirrors the compiler's `BaseAddr.opt_payload`.
            opt_payload: Index,
            /// A pointer to the payload of an error union: `base` is the pointer to
            /// the error union (`*E!T`), and loading resolves that union's payload.
            /// Produced by `err_union_payload_unsafe_ptr` (the payload branch of a
            /// pointer-form `catch`/`try`). Mirrors the compiler's `BaseAddr.eu_payload`.
            eu_payload: Index,

            pub const BaseIndex = struct {
                base: Index,
                index: u64,
            };
            /// `val` is the pointee value; `orig_ty` the canonical pointer type
            /// of the anonymous declaration (the compiler keeps it for lowering
            /// alignment, and it participates in identity). Mirrors the
            /// compiler's `Key.Ptr.BaseAddr.Uav`.
            pub const Uav = extern struct {
                val: Index,
                orig_ty: Index,
            };
        };
    };

    /// A slice value. Mirrors the compiler's `Key.Slice`: `ty` is the slice type,
    /// `ptr` the pointer to the elements, `len` a `usize` value.
    pub const Slice = struct {
        ty: Index,
        ptr: Index,
        len: Index,
    };

    /// Opaque handle into `Sema.comptime_allocs`. Mirrors the compiler's
    /// `InternPool.ComptimeAllocIndex` -- the alloc's mutable state
    /// lives in Sema, not in the pool; this Index is the stable
    /// reference shared by every interned `Key.Ptr` pointing at the
    /// alloc.
    pub const ComptimeAllocIndex = enum(u32) { _ };

    /// Sorted, deduped list of error names. Mirrors the compiler's
    /// `Key.ErrorSetType` (`src/InternPool.zig`): the canonical
    /// representation is name-sorted so two sets with the same
    /// membership intern to the same `Index` regardless of source
    /// ordering. `names` borrows from the pool's extra arena and is
    /// valid for the pool's lifetime.
    pub const ErrorSetType = struct {
        names: []const NullTerminatedString,

        pub fn nameIndex(self: ErrorSetType, pool: *const InternPool, name: NullTerminatedString) ?u32 {
            _ = pool;
            const i = std.mem.indexOfScalar(NullTerminatedString, self.names, name) orelse return null;
            return @intCast(i);
        }
    };

    /// Anonymous tuple type: one type per positional field.
    pub const TupleType = struct {
        types: []const Index,
    };

    /// The identity of a container type (struct/enum/union), mirroring the
    /// compiler's `ContainerType`. A container is one of three flavors and is
    /// hashed/compared per flavor (see `hashContainerId`/`eqlContainerId`):
    ///  - `declared`: from source ZIR, identified by its instruction plus captures;
    ///  - `reified`: from `@Enum`/`@Struct`/`@Union` or an anonymous init,
    ///    identified by its instruction plus a `type_hash` that Sema computes over
    ///    the type's fields/attributes (kept out of the InternPool to avoid an
    ///    over-complex Key);
    ///  - `generated_union_tag`: a union's auto-generated tag enum, identified by
    ///    the union index alone.
    /// The REPL's instruction token is `(source_zir_id, decl_inst)` where the
    /// compiler uses one `TrackedInst.Index`; captures are a flat `[]const Index`
    /// rather than the compiler's owned/external split.
    pub const ContainerId = union(enum) {
        declared: Declared,
        reified: Reified,
        generated_union_tag: Index,

        pub const Declared = struct {
            source_zir_id: u32,
            decl_inst: std.zig.Zir.Inst.Index,
            /// Comptime values captured from the enclosing scope at declaration
            /// time (`const Line = struct { a: P }` captures `P`). A `closure_get`
            /// in a field/decl body reads these by index. Stored on the type
            /// because the defining scope is gone by the time a body is lazily
            /// resolved. Two instantiations of one generic decl (`Box(u8)` vs
            /// `Box(u16)`) capture different values and are distinct types.
            captures: []const Index = &.{},
        };
        pub const Reified = struct {
            source_zir_id: u32,
            decl_inst: std.zig.Zir.Inst.Index,
            type_hash: u64,
        };

        /// The source-ZIR instruction token. A generated tag enum has none -- it
        /// resolves through its owner union, which is unwrapped before this is read.
        pub fn sourceZirId(self: ContainerId) u32 {
            return switch (self) {
                .declared => |d| d.source_zir_id,
                .reified => |r| r.source_zir_id,
                .generated_union_tag => unreachable,
            };
        }
        pub fn declInst(self: ContainerId) std.zig.Zir.Inst.Index {
            return switch (self) {
                .declared => |d| d.decl_inst,
                .reified => |r| r.decl_inst,
                .generated_union_tag => unreachable,
            };
        }
        /// Captures live only on a declared type; reified/generated have none.
        pub fn captures(self: ContainerId) []const Index {
            return switch (self) {
                .declared => |d| d.captures,
                else => &.{},
            };
        }
        /// The owner union of a generated tag enum, or `.none` for other flavors.
        pub fn generatedUnion(self: ContainerId) Index {
            return switch (self) {
                .generated_union_tag => |idx| idx,
                else => .none,
            };
        }
    };

    /// Named struct type. `id` is the nominal identity; `name` is the
    /// fully-qualified name (e.g. `repl.P`). Fields are not stored on a declared
    /// struct -- they are resolved on demand from the decl's ZIR (see the
    /// `struct_type` Key doc).
    pub const StructType = struct {
        name: NullTerminatedString,
        id: ContainerId,
        /// The enclosing container this type is declared in, or `.none` at the
        /// session/file top level. The REPL's stand-in for `Namespace.parent`:
        /// `evalDeclVal` walks it outward so a nested container resolves an
        /// unqualified enclosing decl. Not part of identity (a decl site has one
        /// parent, fixed by its zir position).
        parent: Index = .none,
        /// This container's declaration namespace, or `.none` until scanned. Not
        /// part of identity -- filled after creation. Mirrors the compiler's
        /// `struct_type.namespace`.
        namespace: OptionalNamespaceIndex = .none,
    };

    /// A named enum type. Nominal like `StructType`; field names / tag type /
    /// values are resolved on demand from the decl's ZIR for a declared enum, or
    /// stored at creation for a reified one. Mirrors `getDeclaredEnumType`'s shell.
    pub const EnumType = struct {
        name: NullTerminatedString,
        id: ContainerId,
        /// Enclosing container, or `.none`. See `StructType.parent`.
        parent: Index = .none,
        /// Declaration namespace, or `.none` until scanned. See `StructType.namespace`.
        namespace: OptionalNamespaceIndex = .none,
    };

    /// A named union type. Nominal like `EnumType`; field names/types resolved on
    /// demand from the decl's ZIR. Mirrors `getDeclaredUnionType`'s shell.
    pub const UnionType = struct {
        name: NullTerminatedString,
        id: ContainerId,
        /// Enclosing container, or `.none`. See `StructType.parent`.
        parent: Index = .none,
        /// Declaration namespace, or `.none` until scanned. See `StructType.namespace`.
        namespace: OptionalNamespaceIndex = .none,
    };

    /// A union value: the union type, the active field's tag (its integer index),
    /// and the payload. Mirrors compiler `Key.Union {ty, tag, val}`.
    pub const Union = struct {
        ty: Index,
        tag: Index,
        val: Index,
    };

    /// An enum tag value: the enum type and the integer tag it holds. `int` is an
    /// `int` value whose type is the enum's integer tag type. Mirrors the
    /// compiler's `Key.EnumTag` (`ty`, `int`).
    pub const EnumTag = struct {
        ty: Index,
        int: Index,
    };

    /// An error value. `ty` is always an `error_set_type` Index --
    /// the most precise type the value inhabits, typically a
    /// singleton set created at the `error.X` source site. `name`
    /// is the interned identifier and is what global error-id
    /// comparison ultimately keys on (matching the compiler's global
    /// error table contract: `error.Foo` from two different sets
    /// share the same name interning). An `extern struct` to match the
    /// compiler's `Key.Error` layout discipline.
    pub const Error = extern struct {
        ty: Index,
        name: NullTerminatedString,
    };

    /// Type-side `E!T`. Pair of (error_set type Index, payload type
    /// Index). Mirrors `Key.ErrorUnionType` (`src/InternPool.zig`
    /// ~2035), including the `extern struct` layout discipline.
    /// Identity is structural: two unions are equal IFF both halves
    /// are equal Indices.
    pub const ErrorUnionType = extern struct {
        error_set_type: Index,
        payload_type: Index,
    };

    /// An aggregate value -- the in-memory contents of an array,
    /// vector, or struct. Storage variants compact the common cases:
    /// `repeated_elem` for "every slot equal" and `elems` for the
    /// general case. `bytes` is the third compiler variant (deferred
    /// here -- see the union doc above). Mirrors compiler
    /// `Key.Aggregate` (`src/InternPool.zig` ~2542).
    pub const Aggregate = struct {
        /// Aggregate type Index. Must resolve through `indexToKey`
        /// to an array_type / vector_type / struct_type so the
        /// decoder can compute the element count.
        ty: Index,
        storage: Storage,

        pub const Storage = union(enum) {
            /// Every slot is set to `repeated_elem`. The canonical
            /// form when all `elems` values are equal -- the
            /// `internAggregate` wrapper rewrites that case to this
            /// variant before dedup lookup so `[5,5,5]` and
            /// `repeated_elem = 5` intern at one Index.
            repeated_elem: Index,
            /// Per-slot Indices, length determined by the
            /// aggregate type's element count.
            elems: []const Index,
        };
    };

    /// `[len]child` (sentinel == .none) or `[len:sentinel]child`.
    /// Mirrors compiler `Key.ArrayType` (`src/InternPool.zig` ~2094)
    /// including the `extern struct` discipline -- the layout is
    /// pinned so the value can be memory-reinterpreted for hashing.
    /// `len` is a u64 to match the compiler's range; the storage
    /// layer routes lens < 2^32 with no sentinel into the compact
    /// `type_array_small` Tag.
    pub const ArrayType = extern struct {
        len: u64,
        child: Index,
        sentinel: Index = .none,

        /// Effective slot count including the sentinel terminator.
        /// Mirrors `Key.ArrayType.lenIncludingSentinel`
        /// (`src/InternPool.zig` ~2099).
        pub fn lenIncludingSentinel(at: ArrayType) u64 {
            return at.len + @intFromBool(at.sentinel != .none);
        }
    };

    /// `@Vector(len, child)`. Mirrors compiler `Key.VectorType`
    /// (`src/InternPool.zig` ~2104) including the `extern struct`
    /// discipline -- the layout is pinned for memory-reinterpret hashing.
    pub const VectorType = extern struct {
        len: u32,
        child: Index,
    };

    /// An optional value. Mirrors compiler `Key.Opt`
    /// (`src/InternPool.zig` ~2523).
    pub const Opt = extern struct {
        /// The optional type (`?T`), not the payload type `T`.
        ty: Index,
        /// The payload Index, or `.none` when the optional is `null`.
        val: Index,
    };

    /// Value of an error-union type. Either the `.err` arm
    /// (carrying the interned error name) or the `.payload` arm
    /// (carrying the payload Value's Index). `ty` is always an
    /// `error_union_type` Index. Mirrors `Key.ErrorUnion`.
    pub const ErrorUnion = struct {
        ty: Index,
        val: Value,

        pub const Value = union(enum) {
            err_name: NullTerminatedString,
            payload: Index,
        };
    };

    pub const FuncType = struct {
        param_types: []const Index,
        return_type: Index,
        /// LSB is parameter 0. The compiler caps this at u32 so
        /// fn signatures wider than 32 parameters cannot be marked
        /// individually -- same constraint here.
        comptime_bits: u32 = 0,
        noalias_bits: u32 = 0,
        cc: std.lang.CallingConvention = .auto,
        is_var_args: bool = false,
        is_noinline: bool = false,

        pub fn paramIsComptime(self: FuncType, i: u5) bool {
            assert(i < self.param_types.len);
            return @as(u1, @truncate(self.comptime_bits >> i)) != 0;
        }

        pub fn paramIsNoalias(self: FuncType, i: u5) bool {
            assert(i < self.param_types.len);
            return @as(u1, @truncate(self.noalias_bits >> i)) != 0;
        }
    };

    pub const Func = struct {
        /// Identifies which frozen ZIR snapshot owns this func's
        /// body. `maxInt` is the sentinel for "the currently-active
        /// `sema.zir`" -- used during a `analyze()` pass where the
        /// func is bound in the SAME ZIR being walked. The driver
        /// registers that line as a `Session.File` before analysis, so
        /// the func's `source_zir_id` is its stable `File.Index` and the
        /// next analyze resolves it via `Session.files`.
        /// Mirrors the compiler's `TrackedInst.Index` purpose
        /// (cross-update body identity) at the storage layer.
        source_zir_id: u32 = std.math.maxInt(u32),
        /// Effective function type, post-coercion. For `func_decl`
        /// this matches `uncoerced_ty`; for `func_coerced` this is
        /// the destination type; for `func_instance` this is the
        /// instance's resolved type (which may have fewer params
        /// than the generic owner's type).
        ty: Index,
        /// Function type at the original declaration site. Equals
        /// `ty` unless the value came from `coerceValueToType`
        /// retargeting an existing func value to a new fn type --
        /// i.e. `Tag.func_coerced`. See `src/InternPool.zig`
        /// `Key.Func.uncoerced_ty`.
        uncoerced_ty: Index,
        /// The ZIR `func` / `func_inferred` / `func_fancy`
        /// instruction that owns the body. The compiler uses
        /// `TrackedInst.Index` here for incremental-update
        /// bookkeeping; we use the bare `Zir.Inst.Index` -- same
        /// deferred-vestigial story as `Nav.analysis.zir_index`.
        zir_body_inst: std.zig.Zir.Inst.Index,
        /// The container type whose namespace declared this function -- where
        /// its body resolves bare sibling names (a type `Set` referenced
        /// unqualified). `.none` for a function with no enclosing container (a
        /// REPL top-level `fn`, whose siblings resolve through the session
        /// namespace). Named like the `parent` a container type stores.
        ///
        /// The compiler reaches the same information through `owner_nav ->
        /// Nav.analysis.namespace -> owner_type`, but the REPL builds a `Nav`
        /// only for a session-level declaration, not for a container member
        /// resolved lazily from ZIR by `containerDeclByName` -- so a function
        /// pulled out of `std` has no `owner_nav` to follow. Capturing the
        /// definition-site container here is the stand-in. Storing `owner_nav`
        /// verbatim would require eagerly building a `Nav` (and namespace) for
        /// every container member, i.e. the whole-program `Zcu`/Nav graph the
        /// lazy model deliberately avoids.
        parent: Index = .none,
        /// `.none` unless this is a generic-fn instantiation. When
        /// set, points at the `func_decl` this instance was spawned
        /// from. Mirrors `Key.Func.generic_owner`.
        generic_owner: Index = .none,
        /// Empty unless this is a generic-fn instantiation. Each
        /// element is the comptime-known value bound to the
        /// corresponding parameter of `generic_owner`'s type
        /// (`.none` for runtime-known elements). Mirrors
        /// `Key.Func.comptime_args`.
        comptime_args: []const Index = &.{},
    };

    /// Stable hash for dedup. Storage variants of `int` are
    /// normalised to `BigIntConst` before hashing so that
    /// `.{ .u64 = 5 }` and `.{ .big_int = +5 }` hash identically -- the
    /// read-side compresses limbs back to inline storage so the pool's
    /// canonical form is stable, but a freshly constructed Key may
    /// arrive in any variant. Same canonicalization in `eql`.
    pub fn hash64(key: Key, pool: *const InternPool) u64 {
        var hasher = std.hash.Wyhash.init(0);
        const Tag = @typeInfo(Key).@"union".tag_type.?;
        std.hash.autoHash(&hasher, @as(Tag, key));
        switch (key) {
            .simple_type => |s| std.hash.autoHash(&hasher, s),
            .simple_value => |s| std.hash.autoHash(&hasher, s),
            .enum_literal => |n| std.hash.autoHash(&hasher, n),
            .int_type => |it| {
                std.hash.autoHash(&hasher, it.signedness);
                std.hash.autoHash(&hasher, it.bits);
            },
            .anyframe_type => |child| std.hash.autoHash(&hasher, child),
            .int => |i| {
                std.hash.autoHash(&hasher, i.ty);
                var space: Int.Storage.BigIntSpace = undefined;
                const big = i.storage.toBigInt(&space);
                std.hash.autoHash(&hasher, big.positive);
                for (big.limbs) |limb| std.hash.autoHash(&hasher, limb);
            },
            .float => |f| {
                std.hash.autoHash(&hasher, f.ty);
                switch (f.storage) {
                    inline else => |v| {
                        const Bits = @Int(.unsigned, @bitSizeOf(@TypeOf(v)));
                        std.hash.autoHash(&hasher, @as(Bits, @bitCast(v)));
                    },
                }
            },
            .undef => |ty| std.hash.autoHash(&hasher, ty),
            .ptr_type => |pt| {
                std.hash.autoHash(&hasher, pt.child);
                std.hash.autoHash(&hasher, pt.sentinel);
                std.hash.autoHash(&hasher, @as(u32, @bitCast(pt.flags)));
            },
            .ptr => |p| {
                std.hash.autoHash(&hasher, p.ty);
                std.hash.autoHash(&hasher, p.byte_offset);
                const BaseTag = @typeInfo(Ptr.BaseAddr).@"union".tag_type.?;
                std.hash.autoHash(&hasher, @as(BaseTag, p.base_addr));
                switch (p.base_addr) {
                    .comptime_alloc => |slot| std.hash.autoHash(&hasher, slot),
                    .nav => |nav| std.hash.autoHash(&hasher, nav),
                    .uav => |uav| {
                        std.hash.autoHash(&hasher, uav.val);
                        std.hash.autoHash(&hasher, uav.orig_ty);
                    },
                    .field, .arr_elem => |f| {
                        std.hash.autoHash(&hasher, f.base);
                        std.hash.autoHash(&hasher, f.index);
                    },
                    .opt_payload, .eu_payload => |base| std.hash.autoHash(&hasher, base),
                }
            },
            .error_set_type => |es| {
                std.hash.autoHash(&hasher, @as(u32, @intCast(es.names.len)));
                for (es.names) |name| std.hash.autoHash(&hasher, name);
            },
            .tuple_type => |tt| {
                std.hash.autoHash(&hasher, @as(u32, @intCast(tt.types.len)));
                for (tt.types) |ty| std.hash.autoHash(&hasher, ty);
            },
            // Nominal: identity is the container flavor and its per-flavor data
            // (`name` is derived from the site, so it is excluded here and in
            // `eql`). One helper covers struct/enum/union alike.
            .struct_type => |st| hashContainerId(&hasher, st.id),
            .enum_type => |et| hashContainerId(&hasher, et.id),
            .enum_tag => |et| {
                std.hash.autoHash(&hasher, et.ty);
                std.hash.autoHash(&hasher, et.int);
            },
            .union_type => |ut| hashContainerId(&hasher, ut.id),
            .un => |uv| {
                std.hash.autoHash(&hasher, uv.ty);
                std.hash.autoHash(&hasher, uv.tag);
                std.hash.autoHash(&hasher, uv.val);
            },
            .slice => |s| {
                std.hash.autoHash(&hasher, s.ty);
                std.hash.autoHash(&hasher, s.ptr);
                std.hash.autoHash(&hasher, s.len);
            },
            .err => |e| {
                std.hash.autoHash(&hasher, e.ty);
                std.hash.autoHash(&hasher, e.name);
            },
            .error_union_type => |eu| {
                std.hash.autoHash(&hasher, eu.error_set_type);
                std.hash.autoHash(&hasher, eu.payload_type);
            },
            .array_type => |at| {
                std.hash.autoHash(&hasher, at.len);
                std.hash.autoHash(&hasher, at.child);
                std.hash.autoHash(&hasher, at.sentinel);
            },
            .vector_type => |vt| {
                std.hash.autoHash(&hasher, vt.len);
                std.hash.autoHash(&hasher, vt.child);
            },
            .opt_type => |child| std.hash.autoHash(&hasher, child),
            .opt => |o| {
                std.hash.autoHash(&hasher, o.ty);
                std.hash.autoHash(&hasher, o.val);
            },
            .aggregate => |agg| {
                std.hash.autoHash(&hasher, agg.ty);
                // Hash structurally across element Indices regardless of
                // the storage flavor -- mirrors the compiler's per-element
                // hash at src/InternPool.zig ~3050 so `.elems = [I, I, I]`
                // and `.repeated_elem = I` (same `ty`) hash identically
                // and intern at one Index.
                const count = aggregateLen(pool, agg);
                var i: u64 = 0;
                while (i < count) : (i += 1) {
                    std.hash.autoHash(&hasher, aggregateElementAt(agg, i));
                }
            },
            .error_union => |eu| {
                std.hash.autoHash(&hasher, eu.ty);
                const ValueTag = @typeInfo(ErrorUnion.Value).@"union".tag_type.?;
                std.hash.autoHash(&hasher, @as(ValueTag, eu.val));
                switch (eu.val) {
                    .err_name => |name| std.hash.autoHash(&hasher, name),
                    .payload => |idx| std.hash.autoHash(&hasher, idx),
                }
            },
            .func_type => |ft| {
                for (ft.param_types) |p| std.hash.autoHash(&hasher, p);
                std.hash.autoHash(&hasher, ft.return_type);
                std.hash.autoHash(&hasher, ft.comptime_bits);
                std.hash.autoHash(&hasher, ft.noalias_bits);
                std.hash.autoHash(&hasher, @as(std.lang.CallingConvention.Tag, ft.cc));
                std.hash.autoHash(&hasher, ft.is_var_args);
                std.hash.autoHash(&hasher, ft.is_noinline);
            },
            .func => |f| {
                std.hash.autoHash(&hasher, f.source_zir_id);
                std.hash.autoHash(&hasher, f.ty);
                std.hash.autoHash(&hasher, f.uncoerced_ty);
                std.hash.autoHash(&hasher, f.zir_body_inst);
                std.hash.autoHash(&hasher, f.parent);
                std.hash.autoHash(&hasher, f.generic_owner);
                for (f.comptime_args) |arg| std.hash.autoHash(&hasher, arg);
            },
        }
        return hasher.final();
    }

    /// Structural equality, paired with `hash64`. See `hash64` for the
    /// `int` canonicalization rationale.
    pub fn eql(a: Key, b: Key, pool: *const InternPool) bool {
        const Tag = @typeInfo(Key).@"union".tag_type.?;
        if (@as(Tag, a) != @as(Tag, b)) return false;
        return switch (a) {
            .simple_type => |x| x == b.simple_type,
            .simple_value => |x| x == b.simple_value,
            .enum_literal => |x| x == b.enum_literal,
            .int_type => |x| x.signedness == b.int_type.signedness and
                x.bits == b.int_type.bits,
            .anyframe_type => |x| x == b.anyframe_type,
            .int => |x| blk: {
                const y = b.int;
                if (x.ty != y.ty) break :blk false;
                var sa: Int.Storage.BigIntSpace = undefined;
                var sb: Int.Storage.BigIntSpace = undefined;
                break :blk x.storage.toBigInt(&sa).eql(y.storage.toBigInt(&sb));
            },
            .float => |x| blk: {
                const y = b.float;
                if (x.ty != y.ty) break :blk false;
                // c_longdouble may be stored as any width and is promoted to
                // f128 on emit (except f80, which has its own tag). Two
                // c_longdouble Keys with different storage widths compare
                // equal IFF they round-trip to the same f128 bit-pattern.
                if (x.ty == .c_longdouble_type and x.storage != .f80) {
                    const a_bits: u128 = switch (x.storage) {
                        inline else => |v| @bitCast(@as(f128, @floatCast(v))),
                    };
                    const b_bits: u128 = switch (y.storage) {
                        inline else => |v| @bitCast(@as(f128, @floatCast(v))),
                    };
                    break :blk a_bits == b_bits;
                }
                const StorageTag = @typeInfo(Float.Storage).@"union".tag_type.?;
                if (@as(StorageTag, x.storage) != @as(StorageTag, y.storage)) break :blk false;
                break :blk switch (x.storage) {
                    inline else => |xv, tag| eq: {
                        const Bits = @Int(.unsigned, @bitSizeOf(@TypeOf(xv)));
                        const yv = @field(y.storage, @tagName(tag));
                        break :eq @as(Bits, @bitCast(xv)) == @as(Bits, @bitCast(yv));
                    },
                };
            },
            .undef => |x| x == b.undef,
            .ptr_type => |x| blk: {
                const y = b.ptr_type;
                if (x.child != y.child) break :blk false;
                if (x.sentinel != y.sentinel) break :blk false;
                break :blk @as(u32, @bitCast(x.flags)) == @as(u32, @bitCast(y.flags));
            },
            .ptr => |x| blk: {
                const y = b.ptr;
                if (x.ty != y.ty) break :blk false;
                if (x.byte_offset != y.byte_offset) break :blk false;
                const BaseTag = @typeInfo(Ptr.BaseAddr).@"union".tag_type.?;
                if (@as(BaseTag, x.base_addr) != @as(BaseTag, y.base_addr)) break :blk false;
                break :blk switch (x.base_addr) {
                    .comptime_alloc => |slot| slot == y.base_addr.comptime_alloc,
                    .nav => |nav| nav == y.base_addr.nav,
                    .uav => |uav| uav.val == y.base_addr.uav.val and uav.orig_ty == y.base_addr.uav.orig_ty,
                    .field => |f| f.base == y.base_addr.field.base and f.index == y.base_addr.field.index,
                    .arr_elem => |f| f.base == y.base_addr.arr_elem.base and f.index == y.base_addr.arr_elem.index,
                    .opt_payload => |base| base == y.base_addr.opt_payload,
                    .eu_payload => |base| base == y.base_addr.eu_payload,
                };
            },
            .error_set_type => |x| std.mem.eql(NullTerminatedString, x.names, b.error_set_type.names),
            .tuple_type => |x| std.mem.eql(Index, x.types, b.tuple_type.types),
            .struct_type => |x| eqlContainerId(x.id, b.struct_type.id),
            .enum_type => |x| eqlContainerId(x.id, b.enum_type.id),
            .enum_tag => |x| blk: {
                const y = b.enum_tag;
                break :blk x.ty == y.ty and x.int == y.int;
            },
            .union_type => |x| eqlContainerId(x.id, b.union_type.id),
            .un => |x| blk: {
                const y = b.un;
                break :blk x.ty == y.ty and x.tag == y.tag and x.val == y.val;
            },
            .slice => |x| blk: {
                const y = b.slice;
                break :blk x.ty == y.ty and x.ptr == y.ptr and x.len == y.len;
            },
            .err => |x| blk: {
                const y = b.err;
                break :blk x.ty == y.ty and x.name == y.name;
            },
            .error_union_type => |x| blk: {
                const y = b.error_union_type;
                break :blk x.error_set_type == y.error_set_type and
                    x.payload_type == y.payload_type;
            },
            .array_type => |x| blk: {
                const y = b.array_type;
                if (x.len != y.len) break :blk false;
                if (x.child != y.child) break :blk false;
                break :blk x.sentinel == y.sentinel;
            },
            .vector_type => |x| blk: {
                const y = b.vector_type;
                break :blk x.len == y.len and x.child == y.child;
            },
            .opt_type => |x| x == b.opt_type,
            .opt => |x| blk: {
                const y = b.opt;
                break :blk x.ty == y.ty and x.val == y.val;
            },
            .aggregate => |x| blk: {
                const y = b.aggregate;
                if (x.ty != y.ty) break :blk false;
                // Structural element-by-element equality regardless of
                // storage flavor (src/InternPool.zig). `.elems = [I, I, I]`
                // and `.repeated_elem = I` (same `ty`) compare equal even
                // though their storage variants differ.
                const count = aggregateLen(pool, x);
                if (count != aggregateLen(pool, y)) break :blk false;
                var i: u64 = 0;
                while (i < count) : (i += 1) {
                    if (aggregateElementAt(x, i) != aggregateElementAt(y, i)) {
                        break :blk false;
                    }
                }
                break :blk true;
            },
            .error_union => |x| blk: {
                const y = b.error_union;
                if (x.ty != y.ty) break :blk false;
                const ValueTag = @typeInfo(ErrorUnion.Value).@"union".tag_type.?;
                if (@as(ValueTag, x.val) != @as(ValueTag, y.val)) break :blk false;
                break :blk switch (x.val) {
                    .err_name => |name| name == y.val.err_name,
                    .payload => |idx| idx == y.val.payload,
                };
            },
            .func_type => |x| blk: {
                const y = b.func_type;
                if (x.return_type != y.return_type) break :blk false;
                if (x.comptime_bits != y.comptime_bits) break :blk false;
                if (x.noalias_bits != y.noalias_bits) break :blk false;
                if (x.is_var_args != y.is_var_args) break :blk false;
                if (x.is_noinline != y.is_noinline) break :blk false;
                if (@as(std.lang.CallingConvention.Tag, x.cc) !=
                    @as(std.lang.CallingConvention.Tag, y.cc)) break :blk false;
                break :blk std.mem.eql(Index, x.param_types, y.param_types);
            },
            .func => |x| blk: {
                const y = b.func;
                if (x.source_zir_id != y.source_zir_id) break :blk false;
                if (x.ty != y.ty) break :blk false;
                if (x.uncoerced_ty != y.uncoerced_ty) break :blk false;
                if (x.zir_body_inst != y.zir_body_inst) break :blk false;
                if (x.parent != y.parent) break :blk false;
                if (x.generic_owner != y.generic_owner) break :blk false;
                break :blk std.mem.eql(Index, x.comptime_args, y.comptime_args);
            },
        };
    }

    /// Whether this Key denotes a type -- i.e. a value whose own type is
    /// `type` (`Value.typeOf` returns `.type_type` for exactly this set).
    /// Single owner of the type/value partition: `typeOf`, the value
    /// renderer, and `resolveDestType` all consult it instead of each
    /// re-listing the type tags. Exhaustive (no `else`) so a new Key must
    /// be classified here.
    pub fn isType(key: Key) bool {
        return switch (key) {
            .simple_type,
            .int_type,
            .anyframe_type,
            .ptr_type,
            .error_set_type,
            .error_union_type,
            .func_type,
            .array_type,
            .vector_type,
            .opt_type,
            .tuple_type,
            .struct_type,
            .enum_type,
            .union_type,
            => true,
            .simple_value,
            .enum_literal,
            .int,
            .float,
            .ptr,
            .slice,
            .undef,
            .err,
            .error_union,
            .opt,
            .func,
            .aggregate,
            .enum_tag,
            .un,
            => false,
        };
    }
};

/// Hash a container type's identity by flavor. The active tag is folded in first so
/// a `declared` and a `reified` type sharing an instruction never collide. Captures
/// (declared) and the Sema-computed `type_hash` (reified) are part of identity; a
/// generated tag enum is identified by its owner union alone. `name` is derived
/// from the site, so it is excluded (as in `eqlContainerId`).
fn hashContainerId(hasher: *std.hash.Wyhash, id: Key.ContainerId) void {
    std.hash.autoHash(hasher, @as(std.meta.Tag(Key.ContainerId), id));
    switch (id) {
        .declared => |d| {
            std.hash.autoHash(hasher, d.source_zir_id);
            std.hash.autoHash(hasher, d.decl_inst);
            for (d.captures) |c| std.hash.autoHash(hasher, c);
        },
        .reified => |r| {
            std.hash.autoHash(hasher, r.source_zir_id);
            std.hash.autoHash(hasher, r.decl_inst);
            std.hash.autoHash(hasher, r.type_hash);
        },
        .generated_union_tag => |idx| std.hash.autoHash(hasher, idx),
    }
}

/// Container identity equality, the counterpart to `hashContainerId`: different
/// flavors are never equal, and each flavor compares its own identity data.
fn eqlContainerId(x: Key.ContainerId, y: Key.ContainerId) bool {
    if (@as(std.meta.Tag(Key.ContainerId), x) != @as(std.meta.Tag(Key.ContainerId), y)) return false;
    return switch (x) {
        .declared => |xd| xd.source_zir_id == y.declared.source_zir_id and
            xd.decl_inst == y.declared.decl_inst and
            std.mem.eql(Index, xd.captures, y.declared.captures),
        .reified => |xr| xr.source_zir_id == y.reified.source_zir_id and
            xr.decl_inst == y.reified.decl_inst and
            xr.type_hash == y.reified.type_hash,
        .generated_union_tag => |xi| xi == y.generated_union_tag,
    };
}

/// Tagged storage. `data` interpretation depends on `tag`.
const Item = struct {
    tag: Tag,
    data: u32,

    const Tag = enum(u8) {
        simple_type, // data = SimpleType ordinal == Index of the corresponding type
        simple_value, // data = SimpleValue ordinal == Index of the corresponding value
        enum_literal, // data = the literal name (NullTerminatedString)
        type_int_unsigned, // data = bits
        type_int_signed, // data = bits
        type_anyframe, // data = Index of the frame's child type (or .none for untyped anyframe)
        // Type-specialised int storage. The tag implies the type; the value
        // is inline in `data`.
        int_u8, // ty = .u8_type;  data = the u8 value
        int_u16, // ty = .u16_type; data = the u16 value
        int_u32, // ty = .u32_type; data = the u32 value
        int_i32, // ty = .i32_type; data = the i32 value (bit-cast to u32)
        int_usize, // ty = .usize_type; data = u32 value
        int_comptime_int_u32, // ty = .comptime_int_type; data = u32 value (positive)
        int_comptime_int_i32, // ty = .comptime_int_type; data = i32 value (bit-cast)
        // Fallback for typed `u64` values whose type isn't covered by a
        // specialised tag above. data = extra index of IntSmall.
        int_small,
        // Arbitrary-precision integer. Sign is in the tag; the packed `Int`
        // header (ty + limbs_len) lives at `big_int_limbs[data]` and
        // occupies `IntBigHeader.limbs_items_len` Limb slots, with the
        // actual limbs trailing directly after.
        int_positive,
        int_negative,
        // Floats. Tag implies the type. For f16/f32 the bit-pattern fits in
        // `data` directly. f64/f80/f128 spill to `extra` as packed u32 pieces
        // (see Float64 / Float80 / Float128). c_longdouble has two tags
        // because the compiler stores either f80 (native x87) or f128 (every
        // other target); a runtime-only port doesn't pick the active arm but
        // mirrors the storage so the tag set matches the compiler exactly.
        // `comptime_float` is always stored as f128.
        float_f16, // ty = .f16_type;  data = @as(u16, @bitCast(f16)) inline
        float_f32, // ty = .f32_type;  data = @as(u32, @bitCast(f32)) inline
        float_f64, // ty = .f64_type;  data = extra index of Float64
        float_f80, // ty = .f80_type;  data = extra index of Float80
        float_f128, // ty = .f128_type; data = extra index of Float128
        float_c_longdouble_f80, // ty = .c_longdouble_type; storage f80, data = extra index of Float80
        float_c_longdouble_f128, // ty = .c_longdouble_type; storage f128, data = extra index of Float128
        float_comptime_float, // ty = .comptime_float_type; data = extra index of Float128
        undef, // data = Index of the value's type (`undefined_type` for untyped)
        // Pointer type. data = extra index of PtrTypeRepr (3 u32 slots:
        // child, sentinel, flags).
        type_pointer,
        // Pointer value with `BaseAddr.comptime_alloc`. data = extra
        // index of PtrComptimeAllocRepr (4 u32 slots: ty,
        // comptime_alloc index, byte_offset_lo, byte_offset_hi).
        ptr_comptime_alloc,
        // Pointer value with `BaseAddr.nav`. data = extra index of a
        // PtrNavRepr.
        ptr_nav,
        // Pointer value with `BaseAddr.uav`. data = extra index of a
        // PtrUavRepr.
        ptr_uav,
        // Pointer value with `BaseAddr.field`. data = extra index of 6 u32
        // slots: ty, base ptr Index, index_lo, index_hi, byte_offset_lo,
        // byte_offset_hi.
        ptr_field,
        // Pointer value with `BaseAddr.arr_elem`. Same PtrFieldRepr layout as
        // `ptr_field`.
        ptr_arr_elem,
        // Pointer value with `BaseAddr.opt_payload`. data = extra index of
        // `PtrBase` (ty, base ptr, byte_offset).
        ptr_opt_payload,
        // Pointer value with `BaseAddr.eu_payload`. Same `PtrBase` layout as
        // `ptr_opt_payload`.
        ptr_eu_payload,
        // Slice value. data = extra index of SliceRepr (3 u32 slots: ty, ptr,
        // len).
        ptr_slice,
        // Error set type. data = extra index of `[names_len, name0,
        // name1, ...]` -- one u32 length followed by `names_len`
        // interned-string handles.
        type_error_set,
        // Anonymous tuple type. data = extra index of `[types_len,
        // type0, type1, ...]` -- one u32 length then `types_len`
        // field-type Indices. The compiler additionally trails per-field
        // values (deferred, see the `tuple_type` Key doc).
        type_tuple,
        // Named struct type. data = extra index of StructTypeRepr (3 u32
        // slots: source_zir_id, decl_inst, name). Nominal identity; fields
        // are resolved from the decl's ZIR on demand, not stored.
        type_struct,
        // Named enum type. data = extra index of EnumTypeRepr (4 u32 slots:
        // source_zir_id, decl_inst, name, generated_union) then trailing captures,
        // laid out like `type_struct`. Nominal identity; field names / tag type /
        // values are resolved from the decl's ZIR on demand.
        type_enum,
        // Enum tag value. data = extra index of EnumTagRepr (2 u32 slots: ty,
        // int).
        enum_tag,
        // Named union type. data = extra index of UnionTypeRepr (3 u32 slots) then
        // trailing captures, laid out exactly like `type_enum`.
        type_union,
        // Union value. data = extra index of UnionValueRepr (3 u32 slots: ty, tag,
        // val).
        union_value,
        // Error value. data = extra index of ErrRepr (2 u32 slots:
        // ty, name).
        error_set_error,
        // Error-union type (`E!T`). data = extra index of
        // ErrorUnionTypeRepr (2 u32 slots: error_set, payload).
        type_error_union,
        // Error-union value carrying an error. data = extra index of
        // ErrorUnionErrRepr (2 u32 slots: ty, err_name).
        error_union_error,
        // Error-union value carrying a payload. data = extra index of
        // ErrorUnionPayloadRepr (2 u32 slots: ty, payload).
        error_union_payload,
        // Function type. data = extra index of FuncTypeRepr (3 u32
        // slots) plus trailing comptime_bits / noalias_bits (when
        // present per flags) and `param_types[N]`.
        type_function,
        // Function value at a declaration site. data = extra index
        // of FuncDeclRepr (2 u32 slots: ty, zir_body_inst). Omits the
        // compiler's incremental-compilation extras.
        func_decl,
        // Function value from a generic-fn instantiation. data =
        // extra index of FuncInstanceRepr (3 u32 slots: ty,
        // generic_owner, comptime_args_len) plus trailing
        // `comptime_args[comptime_args_len]`. The tag exists so the
        // dispatcher, hash, and eql paths cover the variant even
        // before generics emit it.
        func_instance,
        // Function value coerced to a different fn type. data =
        // extra index of FuncCoercedRepr (2 u32 slots: ty,
        // inner_func). The inner index points at another
        // func_decl / func_instance; `uncoerced_ty` derives from
        // the inner's `ty`.
        func_coerced,
        // `@Vector(len, child)`. data = extra index of VectorTypeRepr
        // (2 u32 slots: len, child).
        type_vector,
        // `?child` optional type. data = the child type Index.
        type_optional,
        // Sentinel-free `[len]child` array type where len fits in
        // u32. data = extra index of VectorTypeRepr (2 u32 slots:
        // len, child), reusing the same `len, child` packing.
        type_array_small,
        // Array type with a sentinel value OR with len >= 2^32.
        // data = extra index of ArrayTypeBigRepr (4 u32 slots:
        // len_lo, len_hi, child, sentinel).
        type_array_big,
        // Aggregate value with one element per slot. data = extra
        // index of AggregateRepr (1 u32 slot: ty) followed by
        // `element_values[N]` where N = effective element count
        // derived from `ty`.
        aggregate,
        // Aggregate value with every slot equal. data = extra
        // index of RepeatedRepr (2 u32 slots: ty, elem_val).
        repeated,
        // Non-null optional value. data = extra index of OptPayloadRepr
        // (2 u32 slots: ty, val).
        opt_payload,
        // Null optional value. data = the optional type Index.
        opt_null,
    };
};

/// Extra-arena payload for `Item.Tag.int_small`: a typed value that fits
/// in `u32` but whose type isn't covered by the type-specialised inline
/// tags. Stored as two consecutive `u32`s in `extra`: `ty` then `value`.
/// Values that exceed `u32` skip this encoding and go straight to
/// `int_positive` / `int_negative`.
const IntSmall = extern struct {
    ty: u32,
    value: u32,
};

/// Extra-arena payload for `Item.Tag.type_pointer`. Three u32 slots:
/// child, sentinel, and the bit-packed `Key.PtrType.Flags`. Narrower
/// than the compiler's `Tag.TypePointer`, which also carries a
/// `packed_offset` the REPL has no need for.
const PtrTypeRepr = extern struct {
    child: u32,
    sentinel: u32,
    flags: u32,
};

/// Extra-arena header for `Item.Tag.type_function`. Three u32
/// slots followed by optional `comptime_bits` / `noalias_bits`
/// and `param_types[params_len]`.
const FuncTypeRepr = extern struct {
    params_len: u32,
    return_type: u32,
    flags: u32,

    /// Minimal CC packing: `cc_tag` only. The compiler
    /// uses `PackedCallingConvention(u18)` which also carries
    /// `incoming_stack_alignment` + per-variant `extra`. We
    /// reconstruct the full `std.lang.CallingConvention` on unpack
    /// with default-initialised payloads since REPL paths today
    /// only need `.auto` / `.c`; FFI widens to the
    /// full pack.
    const Flags = packed struct(u32) {
        cc_tag: std.lang.CallingConvention.Tag,
        is_var_args: bool,
        is_noinline: bool,
        has_comptime_bits: bool,
        has_noalias_bits: bool,
        _reserved: u20 = 0,
    };
};

/// Extra-arena payload for `Item.Tag.func_decl`. Three u32 slots:
/// the source ZIR id (matches `Sema.current_zir_id` at intern time;
/// a `File.Index` into `Session.files`), `ty`, and the ZIR
/// func-instruction index within that file.
const FuncDeclRepr = extern struct {
    source_zir_id: u32,
    ty: u32,
    zir_body_inst: u32,
    parent: u32,
};

/// Extra-arena header for `Item.Tag.func_instance`. Four u32
/// slots followed by `comptime_args[comptime_args_len]`. The
/// generic_owner index resolves through `indexToKey` to its
/// `func_decl` and contributes the body inst + source_zir_id.
const FuncInstanceRepr = extern struct {
    source_zir_id: u32,
    ty: u32,
    generic_owner: u32,
    comptime_args_len: u32,
};

/// Extra-arena payload for `Item.Tag.func_coerced`. Two u32
/// slots: the destination fn type and the inner func index whose
/// `uncoerced_ty` becomes this Key.Func's `uncoerced_ty`. The
/// source_zir_id is inherited from the inner func -- no extra
/// slot needed since the inner-index chase recovers it.
const FuncCoercedRepr = extern struct {
    ty: u32,
    inner_func: u32,
};

/// Extra-arena payload for `Item.Tag.type_vector` -- `len` then
/// `child`. `Item.Tag.type_array_small` reuses this same layout for
/// sentinel-free arrays whose len fits in u32; the Tag, not the repr,
/// is what `indexToKey` discriminates on.
const VectorTypeRepr = extern struct {
    len: u32,
    child: u32,
};

/// Extra-arena payload for `Item.Tag.opt_payload` -- the optional type
/// then the (non-none) payload value. `opt_null` needs no repr; it
/// stores the optional type inline.
const OptPayloadRepr = extern struct {
    ty: u32,
    val: u32,
};

/// Extra-arena payload for `Item.Tag.type_array_big`. Four u32
/// slots: `len_lo`, `len_hi`, `child`, `sentinel`. Sentinel == 0
/// (`Index.none`) is invalid here -- the dispatcher routes to
/// `type_array_small` in that case. The u32 pair holds the 64-bit length.
const ArrayTypeBigRepr = extern struct {
    len_lo: u32,
    len_hi: u32,
    child: u32,
    sentinel: u32,
};

/// Extra-arena header for `Item.Tag.aggregate`. One u32 slot for
/// the aggregate `ty`; the N element Indices follow inline. N is
/// not stored -- it derives from the aggregate type's element
/// count (`lenIncludingSentinel` for arrays).
const AggregateRepr = extern struct {
    ty: u32,
};

/// Extra-arena payload for `Item.Tag.repeated`. Two u32 slots:
/// `ty` then `elem_val`.
const RepeatedRepr = extern struct {
    ty: u32,
    elem_val: u32,
};

/// A container's identity flavor is folded onto its `captures_len` slot: a real
/// value is a declared type's capture count; the sentinels select a reified or
/// generated-tag type whose trailing data differs (see
/// `appendContainerId`/`readContainerId`). Captures, `type_hash`, and
/// `owner_union` are mutually exclusive trailing data, so one word selects all of it.
const captures_len_reified: u32 = std.math.maxInt(u32);
const captures_len_generated_union_tag: u32 = std.math.maxInt(u32) - 1;

/// The `captures_len` slot value for a container identity (see the sentinels above).
fn containerCapturesLen(id: Key.ContainerId) u32 {
    return switch (id) {
        .declared => |d| @intCast(d.captures.len),
        .reified => captures_len_reified,
        .generated_union_tag => captures_len_generated_union_tag,
    };
}

/// Append a container's identity trailing data after its fixed repr, in the
/// compiler's order (owner_union? / zir_index? / type_hash? / captures?). The fixed
/// repr's `captures_len` slot (from `containerCapturesLen`) selects which are
/// present; the REPL's zir token is the pair `(source_zir_id, decl_inst)`.
fn appendContainerId(pool: *InternPool, id: Key.ContainerId) Allocator.Error!void {
    switch (id) {
        .generated_union_tag => |owner_union| try pool.extra.append(pool.gpa, @intFromEnum(owner_union)),
        .declared => |d| {
            try pool.extra.append(pool.gpa, d.source_zir_id);
            try pool.extra.append(pool.gpa, @intFromEnum(d.decl_inst));
            // An all-u32 `[]Index`, same reinterpret trick as tuple/error-set types.
            try pool.extra.appendSlice(pool.gpa, @ptrCast(d.captures));
        },
        .reified => |r| {
            try pool.extra.append(pool.gpa, r.source_zir_id);
            try pool.extra.append(pool.gpa, @intFromEnum(r.decl_inst));
            try pool.extra.append(pool.gpa, @truncate(r.type_hash));
            try pool.extra.append(pool.gpa, @truncate(r.type_hash >> 32));
        },
    }
}

/// Decode container identity trailing at `off`, the counterpart to
/// `appendContainerId`. A declared type's captures borrow `extra`.
fn readContainerId(pool: *const InternPool, captures_len: u32, off: u32) Key.ContainerId {
    if (captures_len == captures_len_generated_union_tag)
        return .{ .generated_union_tag = @enumFromInt(pool.extra.items[off]) };
    const source_zir_id = pool.extra.items[off];
    const decl_inst: std.zig.Zir.Inst.Index = @enumFromInt(pool.extra.items[off + 1]);
    if (captures_len == captures_len_reified) return .{ .reified = .{
        .source_zir_id = source_zir_id,
        .decl_inst = decl_inst,
        .type_hash = @as(u64, pool.extra.items[off + 3]) << 32 | pool.extra.items[off + 2],
    } };
    return .{ .declared = .{
        .source_zir_id = source_zir_id,
        .decl_inst = decl_inst,
        .captures = @ptrCast(pool.extra.items[off + 2 ..][0..captures_len]),
    } };
}

/// Extra-arena payload for `Item.Tag.type_struct`: the interned name, the enclosing
/// `parent`, and the container identity's flavor/capture count, with the identity
/// trailing data following (see `appendContainerId`).
const StructTypeRepr = extern struct {
    name: u32,
    parent: u32,
    /// Offset into `extra` of this struct's resolved field storage (see
    /// `structFields`), or `fields_unresolved`. A reified struct fills it at
    /// creation; a declared struct reads its fields from ZIR, so this stays unset.
    /// Not part of identity, like `EnumTypeRepr.field_data`.
    field_data: u32,
    captures_len: u32,
    /// This container's declaration namespace (`OptionalNamespaceIndex`), or
    /// `.none` until `getNamespaceIndex` scans it. Filled after creation, so not
    /// part of identity -- the compiler's `struct_type.namespace`.
    namespace: u32,
};

/// Extra-arena payload for `Item.Tag.type_enum`. Like `StructTypeRepr` plus
/// `field_data`.
const EnumTypeRepr = extern struct {
    name: u32,
    parent: u32,
    /// Offset into `extra` of this enum's resolved field storage
    /// (`[int_tag_type, names_len, values_len, names..., values...]`, `values`
    /// empty for an auto enum), or `fields_unresolved`. Not part of the type's
    /// identity -- filled after creation, so it is excluded from the dedup Key
    /// (`enumTypeFromExtra` does not read it).
    field_data: u32,
    captures_len: u32,
    namespace: u32,
};

/// Sentinel `EnumTypeRepr.field_data` value meaning the enum's fields have not been
/// resolved into storage yet (a declared enum resolves them lazily on first access;
/// a reified enum sets them at creation).
const fields_unresolved: u32 = std.math.maxInt(u32);

/// Extra-arena payload for `Item.Tag.enum_tag`. Two u32 slots: the enum type and
/// the integer tag value.
const EnumTagRepr = extern struct {
    ty: u32,
    int: u32,
};

/// Extra-arena payload for `Item.Tag.type_union`. Same shape/trailing as
/// `StructTypeRepr` (name + parent + `field_data` + identity, identity data
/// trailing).
const UnionTypeRepr = extern struct {
    name: u32,
    parent: u32,
    /// Offset into `extra` of this union's resolved field storage (see
    /// `unionFields`), or `fields_unresolved`. Filled by a reified union; a declared
    /// union reads its fields from ZIR. Not part of identity.
    field_data: u32,
    captures_len: u32,
    namespace: u32,
};

/// Extra-arena payload for `Item.Tag.union_value`. Three u32 slots: union type,
/// tag, payload.
const UnionValueRepr = extern struct {
    ty: u32,
    tag: u32,
    val: u32,
};

/// Extra-arena payload for `Item.Tag.ptr_slice`. Three u32 slots: slice type,
/// ptr value, len value.
const SliceRepr = extern struct {
    ty: u32,
    ptr: u32,
    len: u32,
};

/// Extra-arena payload for `Item.Tag.ptr_comptime_alloc`. Four u32 slots: ty,
/// comptime-alloc index, and the 64-bit byte_offset split into lo/hi u32s.
/// An allocation born in Sema rather than backed by a declaration.
const PtrComptimeAllocRepr = extern struct {
    ty: u32,
    alloc_index: u32,
    byte_offset_lo: u32,
    byte_offset_hi: u32,
};

/// Extra-arena payload for `Item.Tag.ptr_nav`. Four u32 slots: ty, nav index,
/// and the 64-bit byte_offset split into lo/hi u32s. A pointer backed by a
/// declaration rather than a Sema alloc.
const PtrNavRepr = extern struct {
    ty: u32,
    nav_index: u32,
    byte_offset_lo: u32,
    byte_offset_hi: u32,
};

/// Extra-arena payload for `Item.Tag.ptr_uav`. Five u32 slots: ty, the inline
/// pointee value, the canonical pointer type, and the 64-bit byte_offset split
/// into lo/hi u32s. A pointer to an anonymous decl whose value is stored inline.
const PtrUavRepr = extern struct {
    ty: u32,
    val: u32,
    orig_ty: u32,
    byte_offset_lo: u32,
    byte_offset_hi: u32,
};

/// Extra-arena payload for `Item.Tag.ptr_field`. Six u32 slots: ty, the base
/// pointer, the 64-bit field index (lo/hi), and byte_offset (lo/hi).
const PtrFieldRepr = extern struct {
    ty: u32,
    base: u32,
    index_lo: u32,
    index_hi: u32,
    byte_offset_lo: u32,
    byte_offset_hi: u32,
};

/// Extra-arena payload for base-plus-offset pointers -- `Item.Tag.ptr_opt_payload`
/// and `ptr_eu_payload`. Four u32 slots: ty, the base pointer, and the 64-bit
/// byte_offset split high (`_a`) then low (`_b`).
const PtrBase = extern struct {
    ty: u32,
    base: u32,
    byte_offset_a: u32,
    byte_offset_b: u32,
};

/// Extra-arena payload for `Item.Tag.error_set_error`. Two u32 slots: the
/// error-set type Index and the interned error-name handle.
const ErrRepr = extern struct {
    ty: u32,
    name: u32,
};

/// Extra-arena payload for `Item.Tag.type_error_union`. Two u32
/// slots: the error-set type Index and the payload type Index.
const ErrorUnionTypeRepr = extern struct {
    error_set: u32,
    payload: u32,
};

/// Extra-arena payload for `Item.Tag.error_union_error`. Two u32
/// slots: the error-union type Index and the interned error name.
const ErrorUnionErrRepr = extern struct {
    ty: u32,
    err_name: u32,
};

/// Extra-arena payload for `Item.Tag.error_union_payload`. Two u32
/// slots: the error-union type Index and the payload value Index.
const ErrorUnionPayloadRepr = extern struct {
    ty: u32,
    payload: u32,
};

/// Header for `Item.Tag.int_positive` / `Item.Tag.int_negative`. Lives at
/// the front of a contiguous `big_int_limbs` slice, with the actual limbs
/// trailing directly after. Sign is in the Item tag, not here.
const IntBigHeader = packed struct {
    ty: u32,
    limbs_len: u32,

    /// Number of Limb slots this header occupies (1 on 64-bit, 2 on 32-bit).
    const limbs_items_len = @divExact(@sizeOf(IntBigHeader), @sizeOf(std.math.big.Limb));
};

/// Extra-arena payload for `Item.Tag.float_f64`: the f64 bit-pattern split
/// into two u32 pieces so it fits in the u32-typed `extra` array.
pub const Float64 = extern struct {
    piece0: u32,
    piece1: u32,

    pub fn pack(value: f64) Float64 {
        const bits: u64 = @bitCast(value);
        return .{
            .piece0 = @truncate(bits),
            .piece1 = @truncate(bits >> 32),
        };
    }

    pub fn get(self: Float64) f64 {
        const bits: u64 = @as(u64, self.piece0) | (@as(u64, self.piece1) << 32);
        return @bitCast(bits);
    }
};

/// Extra-arena payload for `Item.Tag.float_f80` and
/// `Item.Tag.float_c_longdouble_f80`: the f80 bit-pattern split across two
/// u32 pieces and one u16 piece (zero-padded to a u32 slot).
pub const Float80 = extern struct {
    piece0: u32,
    piece1: u32,
    /// Low u16 carries the high 16 bits of the f80; upper u16 is zero.
    piece2: u32,

    pub fn pack(value: f80) Float80 {
        const bits: u80 = @bitCast(value);
        return .{
            .piece0 = @truncate(bits),
            .piece1 = @truncate(bits >> 32),
            .piece2 = @truncate(bits >> 64),
        };
    }

    pub fn get(self: Float80) f80 {
        const bits: u80 = @as(u80, self.piece0) |
            (@as(u80, self.piece1) << 32) |
            (@as(u80, self.piece2) << 64);
        return @bitCast(bits);
    }
};

/// Extra-arena payload for `Item.Tag.float_f128`,
/// `Item.Tag.float_c_longdouble_f128`, and
/// `Item.Tag.float_comptime_float`: the f128 bit-pattern split into four
/// u32 pieces.
pub const Float128 = extern struct {
    piece0: u32,
    piece1: u32,
    piece2: u32,
    piece3: u32,

    pub fn pack(value: f128) Float128 {
        const bits: u128 = @bitCast(value);
        return .{
            .piece0 = @truncate(bits),
            .piece1 = @truncate(bits >> 32),
            .piece2 = @truncate(bits >> 64),
            .piece3 = @truncate(bits >> 96),
        };
    }

    pub fn get(self: Float128) f128 {
        const bits: u128 = @as(u128, self.piece0) |
            (@as(u128, self.piece1) << 32) |
            (@as(u128, self.piece2) << 64) |
            (@as(u128, self.piece3) << 96);
        return @bitCast(bits);
    }
};

gpa: Allocator,
items: std.MultiArrayList(Item),
extra: std.ArrayListUnmanaged(u32),
/// Limb-aligned arena holding `int_positive` / `int_negative` payloads
/// (packed `IntBigHeader` at the head + trailing limbs).
big_int_limbs: std.ArrayListUnmanaged(std.math.big.Limb),
/// Dedup map. Entries are appended in lockstep with `items`, so the
/// map's insertion-order index is the `Item` index (and thus the
/// `Index` enum value). The key is `void` because the canonical Key is
/// reconstructed via `indexToKey`; lookup goes through `KeyAdapter`.
/// Single-shard equivalent of the compiler's sharded `getOrPutKey`.
map: std.AutoArrayHashMapUnmanaged(void, void),

/// Raw bytes of every interned string, each followed by a `0` sentinel.
/// Byte `0` is the lone sentinel for `NullTerminatedString.empty`, so
/// `string_starts.items[0]` is always `0` and the first dynamic
/// string begins at offset `1`.
string_bytes: std.ArrayListUnmanaged(u8),
/// One-past-each-string offsets into `string_bytes`. The string
/// referenced by `NullTerminatedString = N` occupies
/// `string_bytes[string_starts.items[N] .. string_starts.items[N + 1] - 1 :0]`
/// (the `- 1` strips the sentinel; the `:0` keeps it as the slice's
/// terminator). `string_starts.items.len` is always `N + 1` where
/// `N` is the number of interned strings, so the final entry is the
/// one-past-end cursor for the next append.
string_starts: std.ArrayListUnmanaged(u32),
/// Dedup map keyed by `NullTerminatedString`. Like the canonical `map`,
/// the key is `void`; entries are appended in lockstep with
/// `string_starts` so the map's insertion-order index is the
/// `NullTerminatedString`'s integer value. Lookup goes through
/// `StringAdapter` (raw bytes -> existing index) for `getOrPutString`.
string_map: std.AutoArrayHashMapUnmanaged(void, void),
/// Backing store for `Nav.Index`. Append-only -- a Nav, once
/// created, never moves and is referenced for the lifetime of the
/// pool. The compiler uses `MultiArrayList(Nav.Repr)` for column-
/// access density; we use the simpler flat layout (see the
/// `Nav.Index` doc comment for why).
navs: std.ArrayListUnmanaged(Nav),
/// Backing store for `NamespaceIndex`. Append-only.
namespaces: std.ArrayListUnmanaged(Namespace),
/// Backing store for `ComptimeUnit.Id`. Append-only.
comptime_units: std.ArrayListUnmanaged(ComptimeUnit),
/// Every error name that has been assigned a global integer, in assignment
/// order; the value of `error.X` is its index + 1 (0 means "no error").
/// `@intFromError` / `@errorFromInt` map between an error and this number.
/// Order-dependent: the incremental REPL
/// registers names as they are first seen, so a multi-error program's numbers need
/// not match a whole-program `zig run` (a single-error program's do).
global_error_set: std.AutoArrayHashMapUnmanaged(NullTerminatedString, void),

/// Adapter for `string_map.getOrPutAdapted(bytes, StringAdapter)`:
/// hashes / compares against the byte content reachable through
/// `pool.stringSlice(idx)`. The pool pointer must outlive every
/// `getOrPut` call, but `string_bytes` only grows (never shrinks)
/// so reads through it stay valid across appends.
const StringAdapter = struct {
    pool: *const InternPool,

    pub fn hash(_: StringAdapter, key: []const u8) u32 {
        return @truncate(std.hash.Wyhash.hash(0, key));
    }

    pub fn eql(self: StringAdapter, key: []const u8, _: void, b_index: usize) bool {
        const existing = self.pool.stringSlice(@enumFromInt(@as(u32, @intCast(b_index))));
        return std.mem.eql(u8, key, existing);
    }
};

/// Adapter that lets `getOrPutAdapted` hash and compare a `Key` against
/// entries stored as bare `Index`es.
const KeyAdapter = struct {
    pool: *const InternPool,

    pub fn hash(self: KeyAdapter, key: Key) u32 {
        return @truncate(key.hash64(self.pool));
    }

    pub fn eql(self: KeyAdapter, key: Key, _: void, b_index: usize) bool {
        const existing = self.pool.indexToKey(@enumFromInt(@as(u32, @intCast(b_index))));
        return key.eql(existing, self.pool);
    }
};

pub fn init(gpa: Allocator) Allocator.Error!InternPool {
    var pool: InternPool = .{
        .gpa = gpa,
        .items = .{},
        .extra = .empty,
        .big_int_limbs = .empty,
        .map = .empty,
        .string_bytes = .empty,
        .string_starts = .empty,
        .string_map = .empty,
        .navs = .empty,
        .namespaces = .empty,
        .comptime_units = .empty,
        .global_error_set = .empty,
    };
    errdefer pool.deinit();

    try pool.items.ensureTotalCapacity(gpa, first_dynamic_index);
    try pool.map.ensureTotalCapacity(gpa, first_dynamic_index);
    try pool.seedEmptyString();
    try populateWellKnown(&pool);
    assert(pool.items.len == first_dynamic_index);
    assert(pool.map.count() == first_dynamic_index);
    return pool;
}

pub fn deinit(pool: *InternPool) void {
    pool.global_error_set.deinit(pool.gpa);
    pool.items.deinit(pool.gpa);
    pool.extra.deinit(pool.gpa);
    pool.string_bytes.deinit(pool.gpa);
    pool.string_starts.deinit(pool.gpa);
    pool.string_map.deinit(pool.gpa);
    for (pool.namespaces.items) |*ns| {
        ns.pub_decls.deinit(pool.gpa);
        ns.priv_decls.deinit(pool.gpa);
        ns.test_decls.deinit(pool.gpa);
        ns.comptime_decls.deinit(pool.gpa);
    }
    pool.namespaces.deinit(pool.gpa);
    pool.comptime_units.deinit(pool.gpa);
    pool.navs.deinit(pool.gpa);
    pool.big_int_limbs.deinit(pool.gpa);
    pool.map.deinit(pool.gpa);
    pool.* = undefined;
}

/// The global integer for error `name`, assigning the next one if unseen. The
/// value is the 1-based insertion index (0 is reserved for "no error").
pub fn getErrorValue(pool: *InternPool, name: NullTerminatedString) Allocator.Error!u32 {
    const gop = try pool.global_error_set.getOrPut(pool.gpa, name);
    return @intCast(gop.index + 1);
}

/// Like `getErrorValue` but returns null instead of assigning.
pub fn getErrorValueIfExists(pool: *const InternPool, name: NullTerminatedString) ?u32 {
    return @intCast((pool.global_error_set.getIndex(name) orelse return null) + 1);
}

/// The unsigned integer type wide enough for any error value. With the default
/// `error_limit` of `maxInt(u16) - 1`, `errorSetBits()` is 16, so `u16`.
pub fn errorIntType(_: *const InternPool) Index {
    return .u16_type;
}

/// Seed `NullTerminatedString.empty` so a handle of `0` always
/// decodes as `""`. The book-keeping otherwise shared with
/// `getOrPutString` is expressed directly here because the empty-key
/// case sidesteps the dedup adapter -- an empty `key` would compare
/// equal to every other empty query, which `getOrPutAdapted` has no
/// need to handle separately.
fn seedEmptyString(pool: *InternPool) Allocator.Error!void {
    assert(pool.string_bytes.items.len == 0);
    assert(pool.string_starts.items.len == 0);
    assert(pool.string_map.count() == 0);

    try pool.string_bytes.append(pool.gpa, 0);
    try pool.string_starts.append(pool.gpa, 0);
    try pool.string_starts.append(pool.gpa, 1);
    try pool.string_map.put(pool.gpa, {}, {});

    assert(pool.string_starts.items.len == 2);
    assert(pool.string_map.count() == 1);
}

/// Intern `bytes` and return its stable `NullTerminatedString` handle.
/// Single-threaded shape: append bytes, then dedup via one map (the
/// compiler shards this map). The dedup-hit rollback is trivial -- the
/// trailing append simply leaves dead bytes that nothing references.
///
/// Asserts there are no embedded `0` bytes. Current callers (decl
/// names, type names) cannot legally contain them.
pub fn getOrPutString(
    pool: *InternPool,
    gpa: Allocator,
    bytes: []const u8,
) Allocator.Error!NullTerminatedString {
    assert(std.mem.indexOfScalar(u8, bytes, 0) == null);

    if (bytes.len == 0) return .empty;

    const gop = try pool.string_map.getOrPutAdapted(gpa, bytes, StringAdapter{ .pool = pool });
    if (gop.found_existing) return @enumFromInt(@as(u32, @intCast(gop.index)));

    try pool.string_bytes.ensureUnusedCapacity(gpa, bytes.len + 1);
    pool.string_bytes.appendSliceAssumeCapacity(bytes);
    pool.string_bytes.appendAssumeCapacity(0);
    try pool.string_starts.append(gpa, @intCast(pool.string_bytes.items.len));

    const new_index: u32 = @intCast(gop.index);
    assert(new_index + 1 == pool.string_starts.items.len - 1);
    return @enumFromInt(new_index);
}

/// Read back the bytes referenced by `string` as a sentinel-
/// terminated slice. Asserts the handle is in range; safe to call on
/// `.empty` (returns the zero-length slice).
pub fn stringSlice(pool: *const InternPool, string: NullTerminatedString) [:0]const u8 {
    const raw = @intFromEnum(string);
    assert(raw + 1 < pool.string_starts.items.len);

    const start = pool.string_starts.items[raw];
    const end = pool.string_starts.items[raw + 1] - 1;
    assert(pool.string_bytes.items[end] == 0);
    return pool.string_bytes.items[start..end :0];
}

/// Append a fresh Nav with the given `name` and `fqn`. The Nav is
/// created with `analysis = null` and `resolved = null`; the caller
/// (typically `Sema.bindDecls`) populates `resolved` immediately
/// after evaluating the decl's value body.
pub fn createNav(
    pool: *InternPool,
    gpa: Allocator,
    name: NullTerminatedString,
    fqn: NullTerminatedString,
) Allocator.Error!Nav.Index {
    const new_index_raw: u32 = @intCast(pool.navs.items.len);
    try pool.navs.append(gpa, .{
        .name = name,
        .fqn = fqn,
        .analysis = null,
        .resolved = null,
    });
    assert(pool.navs.items.len == new_index_raw + 1);
    return @enumFromInt(new_index_raw);
}

/// Read a Nav by handle. Returns by value because Nav is small and
/// callers typically read one or two fields; mutable access goes
/// through `navPtr` instead.
pub fn getNav(pool: *const InternPool, index: Nav.Index) Nav {
    const raw: u32 = @intFromEnum(index);
    assert(raw < pool.navs.items.len);
    return pool.navs.items[raw];
}

/// Mutable handle into the Nav storage. Used by `bindDecls` to set
/// `resolved` after evaluating the value body. The returned pointer
/// is valid until the next `createNav` that triggers a resize --
/// keep the dereference local.
pub fn navPtr(pool: *InternPool, index: Nav.Index) *Nav {
    const raw: u32 = @intFromEnum(index);
    assert(raw < pool.navs.items.len);
    return &pool.navs.items[raw];
}

/// Create a fresh empty namespace whose `parent` chain begins at
/// `parent` (or `.none` for the session root). All four side maps
/// start empty; the caller's `bindDecls` populates them.
pub fn createNamespace(
    pool: *InternPool,
    gpa: Allocator,
    parent: OptionalNamespaceIndex,
) Allocator.Error!NamespaceIndex {
    const new_index_raw: u32 = @intCast(pool.namespaces.items.len);
    try pool.namespaces.append(gpa, .{
        .parent = parent,
        .file_scope = .none,
        .generation = 0,
        .owner_type = .none,
        .pub_decls = .empty,
        .priv_decls = .empty,
        .test_decls = .empty,
        .comptime_decls = .empty,
    });
    assert(pool.namespaces.items.len == new_index_raw + 1);
    return @enumFromInt(new_index_raw);
}

/// Mutable handle into the namespace storage. Decl insertion
/// (`pub_decls.put` / `test_decls.append`) goes through this pointer.
/// Valid until the next `createNamespace`-induced resize.
pub fn namespacePtr(pool: *InternPool, index: NamespaceIndex) *Namespace {
    const raw: u32 = @intFromEnum(index);
    assert(raw < pool.namespaces.items.len);
    return &pool.namespaces.items[raw];
}

/// The session root namespace's name. The compiler derives a file's
/// root container name from its path; a REPL session has no file, so
/// every fully-qualified name bottoms out here instead.
pub const root_namespace_name = "repl";

/// A container type's name, used to qualify the names of its members.
fn containerTypeName(pool: *const InternPool, ty: Index) NullTerminatedString {
    return switch (pool.indexToKey(ty)) {
        .struct_type => |st| st.name,
        .enum_type => |et| et.name,
        .union_type => |ut| ut.name,
        else => unreachable, // only named containers own a namespace
    };
}

/// A namespace's own name -- the prefix its members qualify under: its
/// owner container's name, or the session root (`repl`) when nothing owns
/// it. This is the base of the fully-qualified-name recursion and the
/// seed for the root naming context.
pub fn namespaceName(
    pool: *InternPool,
    gpa: Allocator,
    ns_idx: NamespaceIndex,
) Allocator.Error!NullTerminatedString {
    const ns = pool.namespacePtr(ns_idx);
    if (ns.owner_type == .none) return pool.getOrPutString(gpa, root_namespace_name);
    return containerTypeName(pool, ns.owner_type);
}

/// Fully-qualified name of declaration `name` in `ns_idx`:
/// `<namespace name>.<name>`. Every caller qualifies a real declaration
/// name, so the empty-name case is not handled.
pub fn fullyQualifiedName(
    pool: *InternPool,
    gpa: Allocator,
    ns_idx: NamespaceIndex,
    name: NullTerminatedString,
) Allocator.Error!NullTerminatedString {
    assert(name != .empty);
    const ns_name = try pool.namespaceName(gpa, ns_idx);

    // `allocPrint` copies both borrowed slices into a fresh `text` before
    // `getOrPutString`, whose append can resize `string_bytes` (which the
    // slices borrow) -- so the borrows can't dangle.
    const text = try std.fmt.allocPrint(gpa, "{s}.{s}", .{ pool.stringSlice(ns_name), pool.stringSlice(name) });
    defer gpa.free(text);
    return pool.getOrPutString(gpa, text);
}

/// Record a `comptime { ... }` block. Returns its stable `Id` so
/// the namespace's `comptime_decls` list can reference it. Execution
/// is deferred to the `@comptime` evaluator.
pub fn createComptimeUnit(
    pool: *InternPool,
    gpa: Allocator,
    namespace: NamespaceIndex,
    zir_index: std.zig.Zir.Inst.Index,
) Allocator.Error!ComptimeUnit.Id {
    const new_index_raw: u32 = @intCast(pool.comptime_units.items.len);
    try pool.comptime_units.append(gpa, .{
        .zir_index = zir_index,
        .namespace = namespace,
    });
    assert(pool.comptime_units.items.len == new_index_raw + 1);
    return @enumFromInt(new_index_raw);
}

pub fn getComptimeUnit(pool: *const InternPool, id: ComptimeUnit.Id) ComptimeUnit {
    const raw: u32 = @intFromEnum(id);
    assert(raw < pool.comptime_units.items.len);
    return pool.comptime_units.items[raw];
}

/// Comptime well-known table: each entry corresponds 1:1 to an `Index`
/// position; `populateWellKnown` iterates and dispatches per Key variant.
const static_keys: [first_dynamic_index]Key = .{
    .{ .int_type = .{ .signedness = .unsigned, .bits = 0 } },
    .{ .int_type = .{ .signedness = .unsigned, .bits = 1 } },
    .{ .int_type = .{ .signedness = .unsigned, .bits = 8 } },
    .{ .int_type = .{ .signedness = .signed, .bits = 8 } },
    .{ .int_type = .{ .signedness = .unsigned, .bits = 16 } },
    .{ .int_type = .{ .signedness = .signed, .bits = 16 } },
    .{ .int_type = .{ .signedness = .unsigned, .bits = 29 } },
    .{ .int_type = .{ .signedness = .unsigned, .bits = 32 } },
    .{ .int_type = .{ .signedness = .signed, .bits = 32 } },
    .{ .int_type = .{ .signedness = .unsigned, .bits = 64 } },
    .{ .int_type = .{ .signedness = .signed, .bits = 64 } },
    .{ .int_type = .{ .signedness = .unsigned, .bits = 80 } },
    .{ .int_type = .{ .signedness = .unsigned, .bits = 128 } },
    .{ .int_type = .{ .signedness = .signed, .bits = 128 } },
    .{ .int_type = .{ .signedness = .unsigned, .bits = 256 } },

    .{ .simple_type = .usize },
    .{ .simple_type = .isize },
    .{ .simple_type = .c_char },
    .{ .simple_type = .c_short },
    .{ .simple_type = .c_ushort },
    .{ .simple_type = .c_int },
    .{ .simple_type = .c_uint },
    .{ .simple_type = .c_long },
    .{ .simple_type = .c_ulong },
    .{ .simple_type = .c_longlong },
    .{ .simple_type = .c_ulonglong },
    .{ .simple_type = .c_longdouble },

    .{ .simple_type = .f16 },
    .{ .simple_type = .f32 },
    .{ .simple_type = .f64 },
    .{ .simple_type = .f80 },
    .{ .simple_type = .f128 },

    .{ .simple_type = .anyopaque },
    .{ .simple_type = .bool },
    .{ .simple_type = .void },
    .{ .simple_type = .type },
    .{ .simple_type = .anyerror },
    .{ .simple_type = .comptime_int },
    .{ .simple_type = .comptime_float },
    .{ .simple_type = .noreturn },
    .{ .anyframe_type = .none },
    .{ .simple_type = .null },
    .{ .simple_type = .undefined },
    .{ .simple_type = .enum_literal },

    // *usize
    .{ .ptr_type = .{ .child = .usize_type, .flags = .{} } },
    // *const comptime_int
    .{ .ptr_type = .{ .child = .comptime_int_type, .flags = .{ .is_const = true } } },
    // [*]u8
    .{ .ptr_type = .{ .child = .u8_type, .flags = .{ .size = .many } } },
    // [*]const u8
    .{ .ptr_type = .{ .child = .u8_type, .flags = .{ .size = .many, .is_const = true } } },
    // [*:0]const u8
    .{ .ptr_type = .{ .child = .u8_type, .sentinel = .zero_u8, .flags = .{ .size = .many, .is_const = true } } },
    // []const u8
    .{ .ptr_type = .{ .child = .u8_type, .flags = .{ .size = .slice, .is_const = true } } },
    // [:0]const u8
    .{ .ptr_type = .{ .child = .u8_type, .sentinel = .zero_u8, .flags = .{ .size = .slice, .is_const = true } } },

    // [*]const []const u8
    .{ .ptr_type = .{ .child = .slice_const_u8_type, .flags = .{ .size = .many, .is_const = true } } },
    // []const []const u8
    .{ .ptr_type = .{ .child = .slice_const_u8_type, .flags = .{ .size = .slice, .is_const = true } } },

    // ?type
    .{ .opt_type = .type_type },
    // [*]const type
    .{ .ptr_type = .{ .child = .type_type, .flags = .{ .size = .many, .is_const = true } } },
    // []const type
    .{ .ptr_type = .{ .child = .type_type, .flags = .{ .size = .slice, .is_const = true } } },

    .{ .vector_type = .{ .len = 8, .child = .i8_type } },
    .{ .vector_type = .{ .len = 16, .child = .i8_type } },
    .{ .vector_type = .{ .len = 32, .child = .i8_type } },
    .{ .vector_type = .{ .len = 64, .child = .i8_type } },
    .{ .vector_type = .{ .len = 1, .child = .u8_type } },
    .{ .vector_type = .{ .len = 2, .child = .u8_type } },
    .{ .vector_type = .{ .len = 4, .child = .u8_type } },
    .{ .vector_type = .{ .len = 8, .child = .u8_type } },
    .{ .vector_type = .{ .len = 16, .child = .u8_type } },
    .{ .vector_type = .{ .len = 32, .child = .u8_type } },
    .{ .vector_type = .{ .len = 64, .child = .u8_type } },
    .{ .vector_type = .{ .len = 2, .child = .i16_type } },
    .{ .vector_type = .{ .len = 4, .child = .i16_type } },
    .{ .vector_type = .{ .len = 8, .child = .i16_type } },
    .{ .vector_type = .{ .len = 16, .child = .i16_type } },
    .{ .vector_type = .{ .len = 32, .child = .i16_type } },
    .{ .vector_type = .{ .len = 4, .child = .u16_type } },
    .{ .vector_type = .{ .len = 8, .child = .u16_type } },
    .{ .vector_type = .{ .len = 16, .child = .u16_type } },
    .{ .vector_type = .{ .len = 32, .child = .u16_type } },
    .{ .vector_type = .{ .len = 2, .child = .i32_type } },
    .{ .vector_type = .{ .len = 4, .child = .i32_type } },
    .{ .vector_type = .{ .len = 8, .child = .i32_type } },
    .{ .vector_type = .{ .len = 16, .child = .i32_type } },
    .{ .vector_type = .{ .len = 4, .child = .u32_type } },
    .{ .vector_type = .{ .len = 8, .child = .u32_type } },
    .{ .vector_type = .{ .len = 16, .child = .u32_type } },
    .{ .vector_type = .{ .len = 2, .child = .i64_type } },
    .{ .vector_type = .{ .len = 4, .child = .i64_type } },
    .{ .vector_type = .{ .len = 8, .child = .i64_type } },
    .{ .vector_type = .{ .len = 2, .child = .u64_type } },
    .{ .vector_type = .{ .len = 4, .child = .u64_type } },
    .{ .vector_type = .{ .len = 8, .child = .u64_type } },
    .{ .vector_type = .{ .len = 1, .child = .u128_type } },
    .{ .vector_type = .{ .len = 2, .child = .u128_type } },
    .{ .vector_type = .{ .len = 1, .child = .u256_type } },
    .{ .vector_type = .{ .len = 4, .child = .f16_type } },
    .{ .vector_type = .{ .len = 8, .child = .f16_type } },
    .{ .vector_type = .{ .len = 16, .child = .f16_type } },
    .{ .vector_type = .{ .len = 32, .child = .f16_type } },
    .{ .vector_type = .{ .len = 2, .child = .f32_type } },
    .{ .vector_type = .{ .len = 4, .child = .f32_type } },
    .{ .vector_type = .{ .len = 8, .child = .f32_type } },
    .{ .vector_type = .{ .len = 16, .child = .f32_type } },
    .{ .vector_type = .{ .len = 2, .child = .f64_type } },
    .{ .vector_type = .{ .len = 4, .child = .f64_type } },
    .{ .vector_type = .{ .len = 8, .child = .f64_type } },

    // ?noreturn
    .{ .opt_type = .noreturn_type },
    // anyerror!void
    .{ .error_union_type = .{ .error_set_type = .anyerror_type, .payload_type = .void_type } },
    .{ .simple_type = .adhoc_inferred_error_set },
    .{ .simple_type = .generic_poison },
    // empty_tuple_type -- the REPL's TupleType has no `values` field.
    .{ .tuple_type = .{ .types = &.{} } },

    .{ .undef = .undefined_type },
    .{ .undef = .bool_type },
    .{ .undef = .usize_type },
    .{ .undef = .u1_type },
    .{ .int = .{ .ty = .comptime_int_type, .storage = .{ .u64 = 0 } } },
    .{ .int = .{ .ty = .usize_type, .storage = .{ .u64 = 0 } } },
    .{ .int = .{ .ty = .u1_type, .storage = .{ .u64 = 0 } } },
    .{ .int = .{ .ty = .u8_type, .storage = .{ .u64 = 0 } } },
    .{ .int = .{ .ty = .comptime_int_type, .storage = .{ .u64 = 1 } } },
    .{ .int = .{ .ty = .usize_type, .storage = .{ .u64 = 1 } } },
    .{ .int = .{ .ty = .u1_type, .storage = .{ .u64 = 1 } } },
    .{ .int = .{ .ty = .u8_type, .storage = .{ .u64 = 1 } } },
    .{ .int = .{ .ty = .u8_type, .storage = .{ .u64 = 4 } } },
    .{ .int = .{ .ty = .comptime_int_type, .storage = .{ .i64 = -1 } } },
    .{ .simple_value = .void },
    .{ .simple_value = .@"unreachable" },
    .{ .simple_value = .null },
    .{ .simple_value = .true },
    .{ .simple_value = .false },
    .{ .aggregate = .{ .ty = .empty_tuple_type, .storage = .{ .elems = &.{} } } },
};

fn populateWellKnown(pool: *InternPool) Allocator.Error!void {
    assert(pool.items.len == 0);
    assert(pool.map.count() == 0);

    inline for (static_keys, 0..) |key, expected_position| {
        const index = try pool.get(key);
        // Sema's wellKnownRefToValue maps a Zir.Inst.Ref to its Index by this
        // position, so the ordering is load-bearing across that boundary.
        assert(@intFromEnum(index) == expected_position);
    }
}

fn appendIntType(pool: *InternPool, signedness: std.lang.Signedness, bits: u16) void {
    const tag: Item.Tag = switch (signedness) {
        .unsigned => .type_int_unsigned,
        .signed => .type_int_signed,
    };
    pool.items.appendAssumeCapacity(.{ .tag = tag, .data = bits });
}

fn appendSimpleType(pool: *InternPool, simple: SimpleType) void {
    pool.items.appendAssumeCapacity(.{
        .tag = .simple_type,
        .data = @intFromEnum(simple),
    });
}

fn appendSimpleValue(pool: *InternPool, simple: SimpleValue) void {
    pool.items.appendAssumeCapacity(.{
        .tag = .simple_value,
        .data = @intFromEnum(simple),
    });
}

fn appendAnyframeType(pool: *InternPool, child: Index) void {
    pool.items.appendAssumeCapacity(.{
        .tag = .type_anyframe,
        .data = @intFromEnum(child),
    });
}

/// Intern a `Key`, returning a stable `Index`. Dedups against existing
/// entries via `getOrPutAdapted`. Single-threaded equivalent of the
/// compiler's `pub fn get(ip, gpa, io, tid, key) !Index` (the
/// `getOrPutKey` + emit dispatcher in `src/InternPool.zig`).
///
/// Invariant: `map` and `items` are appended in lockstep, so the map's
/// insertion-order `gop.index` equals the `items.len` at the time of
/// the miss (and the resulting `Item`'s position). This is what makes
/// the bare-`void` map sound -- the adapter reconstructs the existing
/// Key from the position alone via `indexToKey`.
pub fn get(pool: *InternPool, key: Key) Allocator.Error!Index {
    const adapter: KeyAdapter = .{ .pool = pool };
    const gop = try pool.map.getOrPutAdapted(pool.gpa, key, adapter);
    if (gop.found_existing) {
        const existing: u32 = @intCast(gop.index);
        assert(existing < pool.items.len);
        return @enumFromInt(existing);
    }
    assert(gop.index == pool.items.len);

    try pool.items.ensureUnusedCapacity(pool.gpa, 1);
    switch (key) {
        .simple_type => |s| appendSimpleType(pool, s),
        .simple_value => |s| appendSimpleValue(pool, s),
        .enum_literal => |n| pool.items.appendAssumeCapacity(.{ .tag = .enum_literal, .data = @intFromEnum(n) }),
        .int_type => |it| appendIntType(pool, it.signedness, it.bits),
        .anyframe_type => |child| appendAnyframeType(pool, child),
        .undef => |ty| {
            assert(ty != .none);
            pool.items.appendAssumeCapacity(.{
                .tag = .undef,
                .data = @intFromEnum(ty),
            });
        },
        .int => |i| try emitInt(pool, i),
        .float => |f| try emitFloat(pool, f),
        .ptr_type => |pt| try emitPtrType(pool, pt),
        .ptr => |p| try emitPtr(pool, p),
        .slice => |s| try emitSlice(pool, s),
        .error_set_type => |es| try emitErrorSetType(pool, es),
        .tuple_type => |tt| try emitTupleType(pool, tt),
        .struct_type => |st| try emitStructType(pool, st),
        .enum_type => |et| try emitEnumType(pool, et),
        .enum_tag => |et| try emitEnumTag(pool, et),
        .union_type => |ut| try emitUnionType(pool, ut),
        .un => |uv| try emitUnionValue(pool, uv),
        .err => |e| try emitErr(pool, e),
        .error_union_type => |eu| try emitErrorUnionType(pool, eu),
        .error_union => |eu| try emitErrorUnion(pool, eu),
        .func_type => |ft| try emitFuncType(pool, ft),
        .func => |f| try emitFunc(pool, f),
        .array_type => |at| try emitArrayType(pool, at),
        .vector_type => |vt| try emitVectorType(pool, vt),
        .opt_type => |child| appendOptionalType(pool, child),
        .opt => |o| try emitOpt(pool, o),
        .aggregate => |agg| try emitAggregate(pool, agg),
    }

    assert(pool.items.len == gop.index + 1);
    return @enumFromInt(@as(u32, @intCast(gop.index)));
}

pub fn zigTypeTag(pool: *const InternPool, index: Index) std.lang.TypeId {
    return switch (index) {
        .u0_type,
        .u1_type,
        .u8_type,
        .i8_type,
        .u16_type,
        .i16_type,
        .u29_type,
        .u32_type,
        .i32_type,
        .u64_type,
        .i64_type,
        .u80_type,
        .u128_type,
        .i128_type,
        .u256_type,
        .usize_type,
        .isize_type,
        .c_char_type,
        .c_short_type,
        .c_ushort_type,
        .c_int_type,
        .c_uint_type,
        .c_long_type,
        .c_ulong_type,
        .c_longlong_type,
        .c_ulonglong_type,
        => .int,

        .c_longdouble_type,
        .f16_type,
        .f32_type,
        .f64_type,
        .f80_type,
        .f128_type,
        => .float,

        .anyopaque_type => .@"opaque",
        .bool_type => .bool,
        .void_type => .void,
        .type_type => .type,
        .anyerror_type, .adhoc_inferred_error_set_type => .error_set,
        .comptime_int_type => .comptime_int,
        .comptime_float_type => .comptime_float,
        .noreturn_type => .noreturn,
        .anyframe_type => .@"anyframe",
        .null_type => .null,
        .undefined_type => .undefined,
        .enum_literal_type => .enum_literal,

        .ptr_usize_type,
        .ptr_const_comptime_int_type,
        .manyptr_u8_type,
        .manyptr_const_u8_type,
        .manyptr_const_u8_sentinel_0_type,
        .manyptr_const_slice_const_u8_type,
        .slice_const_u8_type,
        .slice_const_u8_sentinel_0_type,
        .slice_const_slice_const_u8_type,
        .manyptr_const_type_type,
        .slice_const_type_type,
        => .pointer,

        .vector_8_i8_type,
        .vector_16_i8_type,
        .vector_32_i8_type,
        .vector_64_i8_type,
        .vector_1_u8_type,
        .vector_2_u8_type,
        .vector_4_u8_type,
        .vector_8_u8_type,
        .vector_16_u8_type,
        .vector_32_u8_type,
        .vector_64_u8_type,
        .vector_2_i16_type,
        .vector_4_i16_type,
        .vector_8_i16_type,
        .vector_16_i16_type,
        .vector_32_i16_type,
        .vector_4_u16_type,
        .vector_8_u16_type,
        .vector_16_u16_type,
        .vector_32_u16_type,
        .vector_2_i32_type,
        .vector_4_i32_type,
        .vector_8_i32_type,
        .vector_16_i32_type,
        .vector_4_u32_type,
        .vector_8_u32_type,
        .vector_16_u32_type,
        .vector_2_i64_type,
        .vector_4_i64_type,
        .vector_8_i64_type,
        .vector_2_u64_type,
        .vector_4_u64_type,
        .vector_8_u64_type,
        .vector_1_u128_type,
        .vector_2_u128_type,
        .vector_1_u256_type,
        .vector_4_f16_type,
        .vector_8_f16_type,
        .vector_16_f16_type,
        .vector_32_f16_type,
        .vector_2_f32_type,
        .vector_4_f32_type,
        .vector_8_f32_type,
        .vector_16_f32_type,
        .vector_2_f64_type,
        .vector_4_f64_type,
        .vector_8_f64_type,
        => .vector,

        .optional_type_type => .optional,
        .optional_noreturn_type => .optional,
        .anyerror_void_error_union_type => .error_union,
        .empty_tuple_type => .@"struct",

        .generic_poison_type => unreachable,

        // values, not types
        .undef,
        .undef_bool,
        .undef_usize,
        .undef_u1,
        .zero,
        .zero_usize,
        .zero_u1,
        .zero_u8,
        .one,
        .one_usize,
        .one_u1,
        .one_u8,
        .four_u8,
        .negative_one,
        .void_value,
        .unreachable_value,
        .null_value,
        .bool_true,
        .bool_false,
        .empty_tuple,
        => unreachable,

        .none => unreachable,

        // Dynamically-interned types, resolved through the `Key` variant.
        _ => switch (pool.indexToKey(index)) {
            .int_type => .int,
            .array_type => .array,
            .vector_type => .vector,
            .ptr_type => .pointer,
            .opt_type => .optional,
            .anyframe_type => .@"anyframe",
            .error_union_type => .error_union,
            .error_set_type => .error_set,
            .tuple_type => .@"struct",
            .struct_type => .@"struct",
            .union_type => .@"union",
            .enum_type => .@"enum",
            .func_type => .@"fn",
            // A `simple_type` is always a well-known Index, handled above.
            else => unreachable,
        },
    };
}

/// The child type of a pointer/array/vector/optional/anyframe.
pub fn childType(pool: *const InternPool, i: Index) Index {
    return switch (pool.indexToKey(i)) {
        .ptr_type => |ptr_type| ptr_type.child,
        .vector_type => |vector_type| vector_type.child,
        .array_type => |array_type| array_type.child,
        .opt_type, .anyframe_type => |child| child,
        else => unreachable,
    };
}

pub fn indexToKey(pool: *const InternPool, index: Index) Key {
    assert(index != .none);
    const i = @intFromEnum(index);
    assert(i < pool.items.len);
    const item = pool.items.get(i);
    return switch (item.tag) {
        .simple_type => .{ .simple_type = @enumFromInt(item.data) },
        .simple_value => .{ .simple_value = @enumFromInt(item.data) },
        .enum_literal => .{ .enum_literal = @enumFromInt(item.data) },
        .type_int_unsigned => .{ .int_type = .{
            .signedness = .unsigned,
            .bits = @intCast(item.data),
        } },
        .type_int_signed => .{ .int_type = .{
            .signedness = .signed,
            .bits = @intCast(item.data),
        } },
        .type_anyframe => .{ .anyframe_type = @enumFromInt(item.data) },
        .int_u8 => intKey(.u8_type, .{ .u64 = item.data }),
        .int_u16 => intKey(.u16_type, .{ .u64 = item.data }),
        .int_u32 => intKey(.u32_type, .{ .u64 = item.data }),
        .int_i32 => intKey(.i32_type, .{ .i64 = @as(i32, @bitCast(item.data)) }),
        .int_usize => intKey(.usize_type, .{ .u64 = item.data }),
        .int_comptime_int_u32 => intKey(.comptime_int_type, .{ .u64 = item.data }),
        .int_comptime_int_i32 => intKey(.comptime_int_type, .{ .i64 = @as(i32, @bitCast(item.data)) }),
        .int_small => intSmallFromExtra(pool, item.data),
        .int_positive => intBigFromArena(pool, item.data, true),
        .int_negative => intBigFromArena(pool, item.data, false),
        .float_f16 => .{ .float = .{
            .ty = .f16_type,
            .storage = .{ .f16 = @bitCast(@as(u16, @intCast(item.data))) },
        } },
        .float_f32 => .{ .float = .{
            .ty = .f32_type,
            .storage = .{ .f32 = @bitCast(item.data) },
        } },
        .float_f64 => .{ .float = .{
            .ty = .f64_type,
            .storage = .{ .f64 = extraData(pool, Float64, item.data).get() },
        } },
        .float_f80 => .{ .float = .{
            .ty = .f80_type,
            .storage = .{ .f80 = extraData(pool, Float80, item.data).get() },
        } },
        .float_f128 => .{ .float = .{
            .ty = .f128_type,
            .storage = .{ .f128 = extraData(pool, Float128, item.data).get() },
        } },
        .float_c_longdouble_f80 => .{ .float = .{
            .ty = .c_longdouble_type,
            .storage = .{ .f80 = extraData(pool, Float80, item.data).get() },
        } },
        .float_c_longdouble_f128 => .{ .float = .{
            .ty = .c_longdouble_type,
            .storage = .{ .f128 = extraData(pool, Float128, item.data).get() },
        } },
        .float_comptime_float => .{ .float = .{
            .ty = .comptime_float_type,
            .storage = .{ .f128 = extraData(pool, Float128, item.data).get() },
        } },
        .undef => .{ .undef = @enumFromInt(item.data) },
        .type_pointer => ptrTypeFromExtra(pool, item.data),
        .ptr_comptime_alloc => ptrComptimeAllocFromExtra(pool, item.data),
        .ptr_nav => ptrNavFromExtra(pool, item.data),
        .ptr_uav => ptrUavFromExtra(pool, item.data),
        .ptr_field => ptrFieldFromExtra(pool, item.data),
        .ptr_opt_payload => ptrOptPayloadFromExtra(pool, item.data, false),
        .ptr_eu_payload => ptrOptPayloadFromExtra(pool, item.data, true),
        .ptr_arr_elem => ptrArrElemFromExtra(pool, item.data),
        .ptr_slice => sliceFromExtra(pool, item.data),
        .type_error_set => errorSetTypeFromExtra(pool, item.data),
        .type_tuple => tupleTypeFromExtra(pool, item.data),
        .type_struct => structTypeFromExtra(pool, item.data),
        .type_enum => enumTypeFromExtra(pool, item.data),
        .enum_tag => enumTagFromExtra(pool, item.data),
        .type_union => unionTypeFromExtra(pool, item.data),
        .union_value => unionValueFromExtra(pool, item.data),
        .error_set_error => errFromExtra(pool, item.data),
        .type_error_union => errorUnionTypeFromExtra(pool, item.data),
        .error_union_error => errorUnionErrFromExtra(pool, item.data),
        .error_union_payload => errorUnionPayloadFromExtra(pool, item.data),
        .type_function => funcTypeFromExtra(pool, item.data),
        .func_decl => funcDeclFromExtra(pool, item.data),
        .func_instance => funcInstanceFromExtra(pool, item.data),
        .func_coerced => funcCoercedFromExtra(pool, item.data),
        .type_vector => vectorTypeFromExtra(pool, item.data),
        .type_optional => .{ .opt_type = @enumFromInt(item.data) },
        .opt_payload => optPayloadFromExtra(pool, item.data),
        .opt_null => .{ .opt = .{ .ty = @enumFromInt(item.data), .val = .none } },
        .type_array_small => arrayTypeSmallFromExtra(pool, item.data),
        .type_array_big => arrayTypeBigFromExtra(pool, item.data),
        .aggregate => aggregateFromExtra(pool, item.data),
        .repeated => repeatedFromExtra(pool, item.data),
    };
}

fn ptrTypeFromExtra(pool: *const InternPool, extra_index: u32) Key {
    const r = pool.extraData(PtrTypeRepr, extra_index);
    return .{ .ptr_type = .{
        .child = @enumFromInt(r.child),
        .sentinel = @enumFromInt(r.sentinel),
        .flags = @bitCast(r.flags),
    } };
}

fn tupleTypeFromExtra(pool: *const InternPool, extra_index: u32) Key {
    assert(extra_index < pool.extra.items.len);
    const types_len = pool.extra.items[extra_index];
    assert(extra_index + 1 + types_len <= pool.extra.items.len);

    const raw_types = pool.extra.items[extra_index + 1 ..][0..types_len];
    return .{
        // Reinterpret the u32 slice as `[]const Index` -- Index is
        // `enum(u32)`; the slice shares the pool's extra arena for its
        // lifetime. Same trick as `errorSetTypeFromExtra`.
        .tuple_type = .{ .types = @ptrCast(raw_types) },
    };
}

fn structTypeFromExtra(pool: *const InternPool, extra_index: u32) Key {
    const r = pool.extraData(StructTypeRepr, extra_index);
    const id_at = extra_index + @sizeOf(StructTypeRepr) / 4;
    return .{
        .struct_type = .{
            .name = @enumFromInt(r.name),
            .id = readContainerId(pool, r.captures_len, id_at),
            .parent = @enumFromInt(r.parent),
            .namespace = @enumFromInt(r.namespace),
        },
    };
}

fn enumTypeFromExtra(pool: *const InternPool, extra_index: u32) Key {
    const r = pool.extraData(EnumTypeRepr, extra_index);
    const id_at = extra_index + @sizeOf(EnumTypeRepr) / 4;
    return .{ .enum_type = .{
        .name = @enumFromInt(r.name),
        .id = readContainerId(pool, r.captures_len, id_at),
        .parent = @enumFromInt(r.parent),
        .namespace = @enumFromInt(r.namespace),
    } };
}

fn enumTagFromExtra(pool: *const InternPool, extra_index: u32) Key {
    const r = pool.extraData(EnumTagRepr, extra_index);
    return .{ .enum_tag = .{ .ty = @enumFromInt(r.ty), .int = @enumFromInt(r.int) } };
}

fn sliceFromExtra(pool: *const InternPool, extra_index: u32) Key {
    const r = pool.extraData(SliceRepr, extra_index);
    return .{ .slice = .{ .ty = @enumFromInt(r.ty), .ptr = @enumFromInt(r.ptr), .len = @enumFromInt(r.len) } };
}

fn unionTypeFromExtra(pool: *const InternPool, extra_index: u32) Key {
    const r = pool.extraData(UnionTypeRepr, extra_index);
    const id_at = extra_index + @sizeOf(UnionTypeRepr) / 4;
    return .{ .union_type = .{
        .name = @enumFromInt(r.name),
        .id = readContainerId(pool, r.captures_len, id_at),
        .parent = @enumFromInt(r.parent),
        .namespace = @enumFromInt(r.namespace),
    } };
}

fn unionValueFromExtra(pool: *const InternPool, extra_index: u32) Key {
    const r = pool.extraData(UnionValueRepr, extra_index);
    return .{ .un = .{ .ty = @enumFromInt(r.ty), .tag = @enumFromInt(r.tag), .val = @enumFromInt(r.val) } };
}

fn errorSetTypeFromExtra(pool: *const InternPool, extra_index: u32) Key {
    assert(extra_index < pool.extra.items.len);
    const names_len = pool.extra.items[extra_index];
    assert(extra_index + 1 + names_len <= pool.extra.items.len);

    const raw_names = pool.extra.items[extra_index + 1 ..][0..names_len];
    return .{
        .error_set_type = .{
            // Reinterpret the u32 slice as a `[]const NullTerminatedString`
            // slice -- the enum's backing type is u32 and storage is
            // identity, so this `@ptrCast` shares the pool's extra arena
            // for the slice's lifetime.
            .names = @ptrCast(raw_names),
        },
    };
}

fn errFromExtra(pool: *const InternPool, extra_index: u32) Key {
    const r = pool.extraData(ErrRepr, extra_index);
    return .{ .err = .{
        .ty = @enumFromInt(r.ty),
        .name = @enumFromInt(r.name),
    } };
}

fn errorUnionTypeFromExtra(pool: *const InternPool, extra_index: u32) Key {
    const r = pool.extraData(ErrorUnionTypeRepr, extra_index);
    return .{ .error_union_type = .{
        .error_set_type = @enumFromInt(r.error_set),
        .payload_type = @enumFromInt(r.payload),
    } };
}

fn arrayTypeSmallFromExtra(pool: *const InternPool, extra_index: u32) Key {
    const r = pool.extraData(VectorTypeRepr, extra_index);
    return .{ .array_type = .{
        .len = r.len,
        .child = @enumFromInt(r.child),
        .sentinel = .none,
    } };
}

fn vectorTypeFromExtra(pool: *const InternPool, extra_index: u32) Key {
    const r = pool.extraData(VectorTypeRepr, extra_index);
    return .{ .vector_type = .{
        .len = r.len,
        .child = @enumFromInt(r.child),
    } };
}

fn optPayloadFromExtra(pool: *const InternPool, extra_index: u32) Key {
    const r = pool.extraData(OptPayloadRepr, extra_index);
    return .{ .opt = .{
        .ty = @enumFromInt(r.ty),
        .val = @enumFromInt(r.val),
    } };
}

fn arrayTypeBigFromExtra(pool: *const InternPool, extra_index: u32) Key {
    const r = pool.extraData(ArrayTypeBigRepr, extra_index);
    return .{ .array_type = .{
        .len = (@as(u64, r.len_hi) << 32) | r.len_lo,
        .child = @enumFromInt(r.child),
        .sentinel = @enumFromInt(r.sentinel),
    } };
}

fn aggregateFromExtra(pool: *const InternPool, extra_index: u32) Key {
    assert(extra_index + 2 <= pool.extra.items.len);
    const ty: Index = @enumFromInt(pool.extra.items[extra_index]);
    // The element count is stored explicitly (not derived from the type) so a
    // struct aggregate -- whose `struct_type` does not carry a field count --
    // decodes without resolving layout.
    const count: u32 = pool.extra.items[extra_index + 1];
    assert(extra_index + 2 + count <= pool.extra.items.len);
    const raw_elems = pool.extra.items[extra_index + 2 ..][0..count];
    return .{
        .aggregate = .{
            .ty = ty,
            // Reinterpret the u32 slice as `[]const Index` -- Index is
            // `enum(u32)` and the slice shares the pool's extra arena
            // for its lifetime. Same trick as `errorSetTypeFromExtra`.
            .storage = .{ .elems = @ptrCast(raw_elems) },
        },
    };
}

fn repeatedFromExtra(pool: *const InternPool, extra_index: u32) Key {
    const r = pool.extraData(RepeatedRepr, extra_index);
    return .{ .aggregate = .{
        .ty = @enumFromInt(r.ty),
        .storage = .{ .repeated_elem = @enumFromInt(r.elem_val) },
    } };
}

fn errorUnionErrFromExtra(pool: *const InternPool, extra_index: u32) Key {
    const r = pool.extraData(ErrorUnionErrRepr, extra_index);
    return .{ .error_union = .{
        .ty = @enumFromInt(r.ty),
        .val = .{ .err_name = @enumFromInt(r.err_name) },
    } };
}

fn errorUnionPayloadFromExtra(pool: *const InternPool, extra_index: u32) Key {
    const r = pool.extraData(ErrorUnionPayloadRepr, extra_index);
    return .{ .error_union = .{
        .ty = @enumFromInt(r.ty),
        .val = .{ .payload = @enumFromInt(r.payload) },
    } };
}

fn ptrComptimeAllocFromExtra(pool: *const InternPool, extra_index: u32) Key {
    const r = pool.extraData(PtrComptimeAllocRepr, extra_index);
    return .{ .ptr = .{
        .ty = @enumFromInt(r.ty),
        .base_addr = .{ .comptime_alloc = @enumFromInt(r.alloc_index) },
        .byte_offset = (@as(u64, r.byte_offset_hi) << 32) | r.byte_offset_lo,
    } };
}

fn ptrNavFromExtra(pool: *const InternPool, extra_index: u32) Key {
    const r = pool.extraData(PtrNavRepr, extra_index);
    return .{ .ptr = .{
        .ty = @enumFromInt(r.ty),
        .base_addr = .{ .nav = @enumFromInt(r.nav_index) },
        .byte_offset = (@as(u64, r.byte_offset_hi) << 32) | r.byte_offset_lo,
    } };
}

fn ptrUavFromExtra(pool: *const InternPool, extra_index: u32) Key {
    const r = pool.extraData(PtrUavRepr, extra_index);
    return .{ .ptr = .{
        .ty = @enumFromInt(r.ty),
        .base_addr = .{ .uav = .{ .val = @enumFromInt(r.val), .orig_ty = @enumFromInt(r.orig_ty) } },
        .byte_offset = (@as(u64, r.byte_offset_hi) << 32) | r.byte_offset_lo,
    } };
}

fn ptrFieldFromExtra(pool: *const InternPool, extra_index: u32) Key {
    return ptrBaseIndexFromExtra(pool, extra_index, false);
}

fn ptrArrElemFromExtra(pool: *const InternPool, extra_index: u32) Key {
    return ptrBaseIndexFromExtra(pool, extra_index, true);
}

/// Decode a `PtrBase` into an `.opt_payload` or `.eu_payload` ptr (identical layout).
fn ptrOptPayloadFromExtra(pool: *const InternPool, extra_index: u32, is_eu: bool) Key {
    const r = pool.extraData(PtrBase, extra_index);
    const base: Index = @enumFromInt(r.base);
    return .{ .ptr = .{
        .ty = @enumFromInt(r.ty),
        .base_addr = if (is_eu) .{ .eu_payload = base } else .{ .opt_payload = base },
        .byte_offset = (@as(u64, r.byte_offset_a) << 32) | r.byte_offset_b,
    } };
}

/// Decode a `PtrFieldRepr` into a `.field` or `.arr_elem` ptr (identical layout).
fn ptrBaseIndexFromExtra(pool: *const InternPool, extra_index: u32, is_arr_elem: bool) Key {
    const r = pool.extraData(PtrFieldRepr, extra_index);
    const bi: Key.Ptr.BaseAddr.BaseIndex = .{
        .base = @enumFromInt(r.base),
        .index = (@as(u64, r.index_hi) << 32) | r.index_lo,
    };
    return .{ .ptr = .{
        .ty = @enumFromInt(r.ty),
        .base_addr = if (is_arr_elem) .{ .arr_elem = bi } else .{ .field = bi },
        .byte_offset = (@as(u64, r.byte_offset_hi) << 32) | r.byte_offset_lo,
    } };
}

/// Read an all-u32 extra-arena payload `T` back from `extra_index`, one field per
/// consecutive slot in declaration order. The `*Repr` structs pre-flatten every
/// field to u32 -- Index/enum via `@intFromEnum`, u64 split into lo/hi, flag
/// packs bitcast at the call site -- so each field maps to exactly one slot; the
/// comptime `field.type == u32` check pins that contract. Pairs with `addExtra`.
fn extraData(pool: *const InternPool, comptime T: type, extra_index: u32) T {
    const info = @typeInfo(T).@"struct";
    assert(extra_index + info.field_names.len <= pool.extra.items.len);
    var result: T = undefined;
    inline for (info.field_names, info.field_types, 0..) |name, field_type, i| {
        comptime assert(field_type == u32);
        @field(result, name) = pool.extra.items[extra_index + i];
    }
    return result;
}

/// Append an all-u32 extra-arena payload `repr` and return its start index --
/// the write side of `extraData`. Each field is one slot in declaration order,
/// so layout lives in the struct definition alone (no hand-synced slot counts
/// between emit and read).
fn addExtra(pool: *InternPool, repr: anytype) Allocator.Error!u32 {
    const info = @typeInfo(@TypeOf(repr)).@"struct";
    const index: u32 = @intCast(pool.extra.items.len);
    try pool.extra.ensureUnusedCapacity(pool.gpa, info.field_names.len);
    inline for (info.field_names, info.field_types) |name, field_type| {
        comptime assert(field_type == u32);
        pool.extra.appendAssumeCapacity(@field(repr, name));
    }
    return index;
}

inline fn intKey(ty: Index, storage: Key.Int.Storage) Key {
    return .{ .int = .{ .ty = ty, .storage = storage } };
}

fn intSmallFromExtra(pool: *const InternPool, extra_index: u32) Key {
    assert(extra_index + 2 <= pool.extra.items.len);
    const slice = pool.extra.items[extra_index..][0..2];
    const ty: Index = @enumFromInt(slice[0]);
    return intKey(ty, .{ .u64 = slice[1] });
}

/// Reconstruct an `int_positive` / `int_negative` Key (compiler's
/// `indexToKeyBigInt`, `src/InternPool.zig`): on read, a big-int whose
/// value fits in `u64` (or `i64` when negative) is re-surfaced as the
/// matching inline storage variant so the read-side shape stays symmetric
/// with the intern-side compression. Dedup requires it: hashing an inserted
/// Key as `.u64=x` must agree with hashing the reconstructed Key.
fn intBigFromArena(pool: *const InternPool, limb_index: u32, positive: bool) Key {
    const header_end = limb_index + IntBigHeader.limbs_items_len;
    assert(header_end <= pool.big_int_limbs.items.len);

    const header_slice = pool.big_int_limbs.items[limb_index..][0..IntBigHeader.limbs_items_len];
    const header: IntBigHeader = @bitCast(header_slice.*);
    const limbs_len = header.limbs_len;
    assert(limbs_len > 0);

    const limbs_end = header_end + limbs_len;
    assert(limbs_end <= pool.big_int_limbs.items.len);
    const limbs = pool.big_int_limbs.items[header_end..limbs_end];

    const big_int: BigIntConst = .{ .limbs = limbs, .positive = positive };
    const storage: Key.Int.Storage = if (big_int.toInt(u64)) |x|
        .{ .u64 = x }
    else |_| if (big_int.toInt(i64)) |x|
        .{ .i64 = x }
    else |_|
        .{ .big_int = big_int };

    return intKey(@enumFromInt(header.ty), storage);
}

/// Intern a fixed-width integer type. Well-known widths dedup to their
/// reserved well-known `Index` through the `get` map. Zig permits
/// `u0`..`u65535` / `i0`..`i65535` -- the language limit is the `u16`
/// width of `std.lang.Type.Int.bits`.
pub fn internIntType(
    pool: *InternPool,
    signedness: std.lang.Signedness,
    bits: u16,
) Allocator.Error!Index {
    return pool.get(.{ .int_type = .{ .signedness = signedness, .bits = bits } });
}

/// Emit the `Item` (and any extra / limbs) for a `Key.int` (the `.int =>` arm of
/// the compiler's `intern`, `src/InternPool.zig`). Callers must have ensured one
/// item of capacity -- only reachable from `get`'s miss path.
fn emitInt(pool: *InternPool, int: Key.Int) Allocator.Error!void {
    assert(isIntegerType(pool, int.ty));
    const ty = int.ty;

    b: {
        switch (ty) {
            .u8_type => switch (int.storage) {
                .big_int => |big_int| {
                    pool.items.appendAssumeCapacity(.{
                        .tag = .int_u8,
                        .data = big_int.toInt(u8) catch unreachable,
                    });
                    break :b;
                },
                inline .u64, .i64 => |x| {
                    pool.items.appendAssumeCapacity(.{
                        .tag = .int_u8,
                        .data = @as(u8, @intCast(x)),
                    });
                    break :b;
                },
            },
            .u16_type => switch (int.storage) {
                .big_int => |big_int| {
                    pool.items.appendAssumeCapacity(.{
                        .tag = .int_u16,
                        .data = big_int.toInt(u16) catch unreachable,
                    });
                    break :b;
                },
                inline .u64, .i64 => |x| {
                    pool.items.appendAssumeCapacity(.{
                        .tag = .int_u16,
                        .data = @as(u16, @intCast(x)),
                    });
                    break :b;
                },
            },
            .u32_type => switch (int.storage) {
                .big_int => |big_int| {
                    pool.items.appendAssumeCapacity(.{
                        .tag = .int_u32,
                        .data = big_int.toInt(u32) catch unreachable,
                    });
                    break :b;
                },
                inline .u64, .i64 => |x| {
                    pool.items.appendAssumeCapacity(.{
                        .tag = .int_u32,
                        .data = @as(u32, @intCast(x)),
                    });
                    break :b;
                },
            },
            .i32_type => switch (int.storage) {
                .big_int => |big_int| {
                    const casted = big_int.toInt(i32) catch unreachable;
                    pool.items.appendAssumeCapacity(.{
                        .tag = .int_i32,
                        .data = @as(u32, @bitCast(casted)),
                    });
                    break :b;
                },
                inline .u64, .i64 => |x| {
                    pool.items.appendAssumeCapacity(.{
                        .tag = .int_i32,
                        .data = @as(u32, @bitCast(@as(i32, @intCast(x)))),
                    });
                    break :b;
                },
            },
            .usize_type => switch (int.storage) {
                .big_int => |big_int| if (big_int.toInt(u32)) |casted| {
                    pool.items.appendAssumeCapacity(.{ .tag = .int_usize, .data = casted });
                    break :b;
                } else |_| {},
                inline .u64, .i64 => |x| if (std.math.cast(u32, x)) |casted| {
                    pool.items.appendAssumeCapacity(.{ .tag = .int_usize, .data = casted });
                    break :b;
                },
            },
            .comptime_int_type => switch (int.storage) {
                .big_int => |big_int| {
                    if (big_int.toInt(u32)) |casted| {
                        pool.items.appendAssumeCapacity(.{ .tag = .int_comptime_int_u32, .data = casted });
                        break :b;
                    } else |_| {}
                    if (big_int.toInt(i32)) |casted| {
                        pool.items.appendAssumeCapacity(.{
                            .tag = .int_comptime_int_i32,
                            .data = @as(u32, @bitCast(casted)),
                        });
                        break :b;
                    } else |_| {}
                },
                inline .u64, .i64 => |x| {
                    if (std.math.cast(u32, x)) |casted| {
                        pool.items.appendAssumeCapacity(.{ .tag = .int_comptime_int_u32, .data = casted });
                        break :b;
                    }
                    if (std.math.cast(i32, x)) |casted| {
                        pool.items.appendAssumeCapacity(.{
                            .tag = .int_comptime_int_i32,
                            .data = @as(u32, @bitCast(casted)),
                        });
                        break :b;
                    }
                },
            },
            else => {},
        }

        switch (int.storage) {
            .big_int => |big_int| {
                if (big_int.toInt(u32)) |casted| {
                    const extra_index: u32 = @intCast(pool.extra.items.len);
                    try pool.extra.appendSlice(pool.gpa, &.{ @intFromEnum(ty), casted });
                    pool.items.appendAssumeCapacity(.{ .tag = .int_small, .data = extra_index });
                    break :b;
                } else |_| {}
                try addBigInt(pool, ty, big_int);
            },
            inline .u64, .i64 => |x| {
                if (std.math.cast(u32, x)) |casted| {
                    const extra_index: u32 = @intCast(pool.extra.items.len);
                    try pool.extra.appendSlice(pool.gpa, &.{ @intFromEnum(ty), casted });
                    pool.items.appendAssumeCapacity(.{ .tag = .int_small, .data = extra_index });
                    break :b;
                }
                var buf: Key.Int.Storage.BigIntSpace = undefined;
                const big_int = std.math.big.int.Mutable.init(&buf.limbs, x).toConst();
                try addBigInt(pool, ty, big_int);
            },
        }
    }
}

/// Intern an integer value with any storage form.
pub fn internInt(pool: *InternPool, int: Key.Int) Allocator.Error!Index {
    return pool.get(.{ .int = int });
}

/// Emit the `Item` (and any extra) for a `Key.float` (the `.float =>` arm of the
/// compiler's `intern`, `src/InternPool.zig`). The c_longdouble arm picks a tag by
/// storage variant (f80 -> its own tag, otherwise promoted to f128); comptime_float
/// always stores as f128. Callers must have ensured one item of capacity -- only
/// reachable from `get`'s miss path.
fn emitFloat(pool: *InternPool, float: Key.Float) Allocator.Error!void {
    assert(isFloatType(float.ty));
    switch (float.ty) {
        .f16_type => {
            assert(float.storage == .f16);
            pool.items.appendAssumeCapacity(.{
                .tag = .float_f16,
                .data = @as(u16, @bitCast(float.storage.f16)),
            });
        },
        .f32_type => {
            assert(float.storage == .f32);
            pool.items.appendAssumeCapacity(.{
                .tag = .float_f32,
                .data = @as(u32, @bitCast(float.storage.f32)),
            });
        },
        .f64_type => {
            assert(float.storage == .f64);
            const extra_index = try addExtra(pool, Float64.pack(float.storage.f64));
            pool.items.appendAssumeCapacity(.{ .tag = .float_f64, .data = extra_index });
        },
        .f80_type => {
            assert(float.storage == .f80);
            const extra_index = try addExtra(pool, Float80.pack(float.storage.f80));
            pool.items.appendAssumeCapacity(.{ .tag = .float_f80, .data = extra_index });
        },
        .f128_type => {
            assert(float.storage == .f128);
            const extra_index = try addExtra(pool, Float128.pack(float.storage.f128));
            pool.items.appendAssumeCapacity(.{ .tag = .float_f128, .data = extra_index });
        },
        .c_longdouble_type => switch (float.storage) {
            .f80 => |v| {
                const extra_index = try addExtra(pool, Float80.pack(v));
                pool.items.appendAssumeCapacity(.{
                    .tag = .float_c_longdouble_f80,
                    .data = extra_index,
                });
            },
            inline .f16, .f32, .f64, .f128 => |v| {
                const extra_index = try addExtra(pool, Float128.pack(@floatCast(v)));
                pool.items.appendAssumeCapacity(.{
                    .tag = .float_c_longdouble_f128,
                    .data = extra_index,
                });
            },
        },
        .comptime_float_type => {
            assert(float.storage == .f128);
            const extra_index = try addExtra(pool, Float128.pack(float.storage.f128));
            pool.items.appendAssumeCapacity(.{
                .tag = .float_comptime_float,
                .data = extra_index,
            });
        },
        else => unreachable,
    }
}

/// Intern a float value with any storage form.
pub fn internFloat(pool: *InternPool, float: Key.Float) Allocator.Error!Index {
    return pool.get(.{ .float = float });
}

fn emitPtrType(pool: *InternPool, pt: Key.PtrType) Allocator.Error!void {
    assert(pt.child != .none);
    const extra_index = try pool.addExtra(PtrTypeRepr{
        .child = @intFromEnum(pt.child),
        .sentinel = @intFromEnum(pt.sentinel),
        .flags = @bitCast(pt.flags),
    });
    pool.items.appendAssumeCapacity(.{ .tag = .type_pointer, .data = extra_index });
}

/// Emit a `ptr` Item, tag selected by base-address flavor.
fn emitPtr(pool: *InternPool, p: Key.Ptr) Allocator.Error!void {
    assert(p.ty != .none);
    switch (p.base_addr) {
        .comptime_alloc => |idx| {
            const extra_index = try pool.addExtra(PtrComptimeAllocRepr{
                .ty = @intFromEnum(p.ty),
                .alloc_index = @intFromEnum(idx),
                .byte_offset_lo = @truncate(p.byte_offset),
                .byte_offset_hi = @truncate(p.byte_offset >> 32),
            });
            pool.items.appendAssumeCapacity(.{ .tag = .ptr_comptime_alloc, .data = extra_index });
        },
        .nav => |nav| {
            const extra_index = try pool.addExtra(PtrNavRepr{
                .ty = @intFromEnum(p.ty),
                .nav_index = @intFromEnum(nav),
                .byte_offset_lo = @truncate(p.byte_offset),
                .byte_offset_hi = @truncate(p.byte_offset >> 32),
            });
            pool.items.appendAssumeCapacity(.{ .tag = .ptr_nav, .data = extra_index });
        },
        .uav => |uav| {
            const extra_index = try pool.addExtra(PtrUavRepr{
                .ty = @intFromEnum(p.ty),
                .val = @intFromEnum(uav.val),
                .orig_ty = @intFromEnum(uav.orig_ty),
                .byte_offset_lo = @truncate(p.byte_offset),
                .byte_offset_hi = @truncate(p.byte_offset >> 32),
            });
            pool.items.appendAssumeCapacity(.{ .tag = .ptr_uav, .data = extra_index });
        },
        .field, .arr_elem => |f| {
            const extra_index = try pool.addExtra(PtrFieldRepr{
                .ty = @intFromEnum(p.ty),
                .base = @intFromEnum(f.base),
                .index_lo = @truncate(f.index),
                .index_hi = @truncate(f.index >> 32),
                .byte_offset_lo = @truncate(p.byte_offset),
                .byte_offset_hi = @truncate(p.byte_offset >> 32),
            });
            const tag: Item.Tag = if (p.base_addr == .field) .ptr_field else .ptr_arr_elem;
            pool.items.appendAssumeCapacity(.{ .tag = tag, .data = extra_index });
        },
        .opt_payload, .eu_payload => |base| {
            const extra_index = try pool.addExtra(PtrBase{
                .ty = @intFromEnum(p.ty),
                .base = @intFromEnum(base),
                .byte_offset_a = @truncate(p.byte_offset >> 32),
                .byte_offset_b = @truncate(p.byte_offset),
            });
            const tag: Item.Tag = if (p.base_addr == .opt_payload) .ptr_opt_payload else .ptr_eu_payload;
            pool.items.appendAssumeCapacity(.{ .tag = tag, .data = extra_index });
        },
    }
}

/// Emit a `type_error_set` Item. Layout in `extra`:
/// `[names_len, name0, name1, ...]` -- a u32 length followed by
/// `names_len` interned-string handles. Caller must have already
/// sorted+deduped `names` (see `internErrorSetType`).
fn emitErrorSetType(pool: *InternPool, es: Key.ErrorSetType) Allocator.Error!void {
    assert(es.names.len <= std.math.maxInt(u32));

    const extra_index: u32 = @intCast(pool.extra.items.len);
    try pool.extra.ensureUnusedCapacity(pool.gpa, 1 + es.names.len);
    pool.extra.appendAssumeCapacity(@intCast(es.names.len));
    for (es.names) |name| pool.extra.appendAssumeCapacity(@intFromEnum(name));
    pool.items.appendAssumeCapacity(.{ .tag = .type_error_set, .data = extra_index });
}

fn emitTupleType(pool: *InternPool, tt: Key.TupleType) Allocator.Error!void {
    assert(tt.types.len <= std.math.maxInt(u32));

    const extra_index: u32 = @intCast(pool.extra.items.len);
    try pool.extra.ensureUnusedCapacity(pool.gpa, 1 + tt.types.len);
    pool.extra.appendAssumeCapacity(@intCast(tt.types.len));
    for (tt.types) |ty| pool.extra.appendAssumeCapacity(@intFromEnum(ty));
    pool.items.appendAssumeCapacity(.{ .tag = .type_tuple, .data = extra_index });
}

/// Emit a `type_struct` Item: the fixed `StructTypeRepr` then the container
/// identity's trailing data (see `appendContainerId`).
fn emitStructType(pool: *InternPool, st: Key.StructType) Allocator.Error!void {
    const extra_index = try pool.addExtra(StructTypeRepr{
        .name = @intFromEnum(st.name),
        .parent = @intFromEnum(st.parent),
        .field_data = fields_unresolved,
        .captures_len = containerCapturesLen(st.id),
        .namespace = @intFromEnum(st.namespace),
    });
    try pool.appendContainerId(st.id);
    pool.items.appendAssumeCapacity(.{ .tag = .type_struct, .data = extra_index });
}

/// Emit a `type_enum` Item. Same layout as `type_struct` (fixed repr + trailing
/// identity data).
fn emitEnumType(pool: *InternPool, et: Key.EnumType) Allocator.Error!void {
    const extra_index = try pool.addExtra(EnumTypeRepr{
        .name = @intFromEnum(et.name),
        .parent = @intFromEnum(et.parent),
        .field_data = fields_unresolved,
        .captures_len = containerCapturesLen(et.id),
        .namespace = @intFromEnum(et.namespace),
    });
    try pool.appendContainerId(et.id);
    pool.items.appendAssumeCapacity(.{ .tag = .type_enum, .data = extra_index });
}

/// The resolved fields of an enum type, borrowing into `extra`. Mirrors the
/// compiler's `LoadedEnumType` field data (names + values + `int_tag_type`); the
/// per-name/value lookup maps are omitted -- the REPL scans linearly. `values` is
/// empty for an auto-numbered enum (tag value == field index), as the compiler
/// leaves `field_values` empty (see `enumValueFieldIndex`).
pub const EnumFields = struct {
    int_tag_type: Index,
    nonexhaustive: bool,
    names: []const NullTerminatedString,
    values: []const Index,
};

/// This enum's resolved fields, or null if not resolved yet. A generated-union tag
/// enum never stores fields (its fields are the union's, read through the union).
/// Storage block layout: `[int_tag_type, nonexhaustive, names_len, values_len,
/// names..., values...]`.
pub fn enumFields(pool: *const InternPool, enum_ty: Index) ?EnumFields {
    const item = pool.items.get(@intFromEnum(enum_ty));
    assert(item.tag == .type_enum);
    const off = pool.extra.items[item.data + @offsetOf(EnumTypeRepr, "field_data") / 4];
    if (off == fields_unresolved) return null;
    const names_len = pool.extra.items[off + 2];
    const values_len = pool.extra.items[off + 3];
    return .{
        .int_tag_type = @enumFromInt(pool.extra.items[off]),
        .nonexhaustive = pool.extra.items[off + 1] != 0,
        .names = @ptrCast(pool.extra.items[off + 4 ..][0..names_len]),
        .values = @ptrCast(pool.extra.items[off + 4 + names_len ..][0..values_len]),
    };
}

/// Store this enum's resolved fields (idempotent -- a no-op once set). `values` is
/// empty for an auto-numbered enum (each tag value is its field index, as
/// `enumValueFieldIndex` computes); otherwise `values[i]` is `names[i]`'s interned
/// `int_tag_type` value. The identity Key is unchanged; only the `field_data` slot
/// is filled, in place.
pub fn setEnumFields(
    pool: *InternPool,
    enum_ty: Index,
    int_tag_type: Index,
    nonexhaustive: bool,
    names: []const NullTerminatedString,
    values: []const Index,
) Allocator.Error!void {
    assert(values.len == 0 or values.len == names.len);
    const item = pool.items.get(@intFromEnum(enum_ty));
    assert(item.tag == .type_enum);
    const slot = item.data + @offsetOf(EnumTypeRepr, "field_data") / 4;
    if (pool.extra.items[slot] != fields_unresolved) return;
    const off: u32 = @intCast(pool.extra.items.len);
    try pool.extra.ensureUnusedCapacity(pool.gpa, 4 + names.len + values.len);
    pool.extra.appendAssumeCapacity(@intFromEnum(int_tag_type));
    pool.extra.appendAssumeCapacity(@intFromBool(nonexhaustive));
    pool.extra.appendAssumeCapacity(@intCast(names.len));
    pool.extra.appendAssumeCapacity(@intCast(values.len));
    for (names) |n| pool.extra.appendAssumeCapacity(@intFromEnum(n));
    for (values) |v| pool.extra.appendAssumeCapacity(@intFromEnum(v));
    pool.extra.items[slot] = off;
}

/// The resolved fields of a reified struct, borrowing into `extra`. Mirrors the
/// comptime-relevant part of `LoadedStructType` (the runtime layout fields -- size,
/// offsets, class -- are not modelled). `defaults`/`aligns` are empty when no field
/// has one; `comptime_bits` (one bit per field, LSB-first within each u32) is empty
/// when no field is comptime. Storage block layout: `[layout, backing_int,
/// fields_len, defaults_len, aligns_len, comptime_len, names..., types...,
/// defaults..., aligns..., comptime_bits...]`.
pub const StructFields = struct {
    layout: std.lang.Type.ContainerLayout,
    backing_int: Index,
    names: []const NullTerminatedString,
    types: []const Index,
    defaults: []const Index,
    aligns: []const Index,
    comptime_bits: []const u32,
};

/// This struct's resolved fields, or null if it stores none (a declared struct,
/// which reads its fields from ZIR).
pub fn structFields(pool: *const InternPool, struct_ty: Index) ?StructFields {
    const item = pool.items.get(@intFromEnum(struct_ty));
    assert(item.tag == .type_struct);
    const off = pool.extra.items[item.data + @offsetOf(StructTypeRepr, "field_data") / 4];
    if (off == fields_unresolved) return null;
    const fields_len = pool.extra.items[off + 2];
    const defaults_len = pool.extra.items[off + 3];
    const aligns_len = pool.extra.items[off + 4];
    const comptime_len = pool.extra.items[off + 5];
    var base = off + 6;
    const names: []const NullTerminatedString = @ptrCast(pool.extra.items[base..][0..fields_len]);
    base += fields_len;
    const types: []const Index = @ptrCast(pool.extra.items[base..][0..fields_len]);
    base += fields_len;
    const defaults: []const Index = @ptrCast(pool.extra.items[base..][0..defaults_len]);
    base += defaults_len;
    const aligns: []const Index = @ptrCast(pool.extra.items[base..][0..aligns_len]);
    base += aligns_len;
    return .{
        .layout = @enumFromInt(pool.extra.items[off]),
        .backing_int = @enumFromInt(pool.extra.items[off + 1]),
        .names = names,
        .types = types,
        .defaults = defaults,
        .aligns = aligns,
        .comptime_bits = pool.extra.items[base..][0..comptime_len],
    };
}

/// Store a reified struct's resolved fields (idempotent -- a no-op once set). Each
/// `defaults[i]`/`aligns[i]` is `.none` for a field without that attribute; the
/// slice is empty when no field has one. The identity Key is unchanged; only the
/// `field_data` slot is filled, in place.
pub fn setStructFields(
    pool: *InternPool,
    struct_ty: Index,
    layout: std.lang.Type.ContainerLayout,
    backing_int: Index,
    names: []const NullTerminatedString,
    types: []const Index,
    defaults: []const Index,
    aligns: []const Index,
    comptime_bits: []const u32,
) Allocator.Error!void {
    assert(types.len == names.len);
    assert(defaults.len == 0 or defaults.len == names.len);
    assert(aligns.len == 0 or aligns.len == names.len);
    const item = pool.items.get(@intFromEnum(struct_ty));
    assert(item.tag == .type_struct);
    const slot = item.data + @offsetOf(StructTypeRepr, "field_data") / 4;
    if (pool.extra.items[slot] != fields_unresolved) return;
    const off: u32 = @intCast(pool.extra.items.len);
    try pool.extra.ensureUnusedCapacity(pool.gpa, 6 + names.len + types.len + defaults.len + aligns.len + comptime_bits.len);
    pool.extra.appendAssumeCapacity(@intFromEnum(layout));
    pool.extra.appendAssumeCapacity(@intFromEnum(backing_int));
    pool.extra.appendAssumeCapacity(@intCast(names.len));
    pool.extra.appendAssumeCapacity(@intCast(defaults.len));
    pool.extra.appendAssumeCapacity(@intCast(aligns.len));
    pool.extra.appendAssumeCapacity(@intCast(comptime_bits.len));
    for (names) |n| pool.extra.appendAssumeCapacity(@intFromEnum(n));
    for (types) |t| pool.extra.appendAssumeCapacity(@intFromEnum(t));
    for (defaults) |d| pool.extra.appendAssumeCapacity(@intFromEnum(d));
    for (aligns) |a| pool.extra.appendAssumeCapacity(@intFromEnum(a));
    for (comptime_bits) |b| pool.extra.appendAssumeCapacity(b);
    pool.extra.items[slot] = off;
}

/// The declaration namespace stored on a container type, or `.none` for a
/// non-container or an as-yet-unscanned container. Mirrors `Type.getNamespace`.
pub fn typeNamespace(pool: *const InternPool, ty: Index) OptionalNamespaceIndex {
    return switch (pool.indexToKey(ty)) {
        .struct_type => |st| st.namespace,
        .enum_type => |et| et.namespace,
        .union_type => |ut| ut.namespace,
        else => .none,
    };
}

/// Store `ns` as the container type's declaration namespace. The slot mirrors
/// `setStructFields`'s `field_data` mutation -- non-hashed, filled once.
pub fn setNamespace(pool: *InternPool, ty: Index, ns: NamespaceIndex) void {
    const item = pool.items.get(@intFromEnum(ty));
    const slot = switch (item.tag) {
        .type_struct => item.data + @offsetOf(StructTypeRepr, "namespace") / 4,
        .type_enum => item.data + @offsetOf(EnumTypeRepr, "namespace") / 4,
        .type_union => item.data + @offsetOf(UnionTypeRepr, "namespace") / 4,
        else => unreachable,
    };
    pool.extra.items[slot] = @intFromEnum(OptionalNamespaceIndex.init(ns));
}

fn emitEnumTag(pool: *InternPool, et: Key.EnumTag) Allocator.Error!void {
    const extra_index = try pool.addExtra(EnumTagRepr{
        .ty = @intFromEnum(et.ty),
        .int = @intFromEnum(et.int),
    });
    pool.items.appendAssumeCapacity(.{ .tag = .enum_tag, .data = extra_index });
}

/// Emit a `type_union` Item. Same layout as `type_enum` (fixed repr + trailing
/// identity data).
fn emitUnionType(pool: *InternPool, ut: Key.UnionType) Allocator.Error!void {
    const extra_index = try pool.addExtra(UnionTypeRepr{
        .name = @intFromEnum(ut.name),
        .parent = @intFromEnum(ut.parent),
        .field_data = fields_unresolved,
        .captures_len = containerCapturesLen(ut.id),
        .namespace = @intFromEnum(ut.namespace),
    });
    try pool.appendContainerId(ut.id);
    pool.items.appendAssumeCapacity(.{ .tag = .type_union, .data = extra_index });
}

/// The resolved fields of a reified union, borrowing into `extra`. Mirrors the
/// comptime-relevant part of `LoadedUnionType`. `tag_type` is the explicit tag enum
/// (`.none` for an untagged union); `backing_int` is the packed backing integer
/// (`.none` unless a packed union); `aligns` is empty when no field has an explicit
/// alignment. Union fields carry no comptime/default (unlike struct fields). Storage
/// block layout: `[layout, tag_type, backing_int, fields_len, aligns_len, names...,
/// types..., aligns...]`.
pub const UnionFields = struct {
    layout: std.lang.Type.ContainerLayout,
    tag_type: Index,
    backing_int: Index,
    names: []const NullTerminatedString,
    types: []const Index,
    aligns: []const Index,
};

/// This union's resolved fields, or null if it stores none (a declared union, which
/// reads its fields from ZIR).
pub fn unionFields(pool: *const InternPool, union_ty: Index) ?UnionFields {
    const item = pool.items.get(@intFromEnum(union_ty));
    assert(item.tag == .type_union);
    const off = pool.extra.items[item.data + @offsetOf(UnionTypeRepr, "field_data") / 4];
    if (off == fields_unresolved) return null;
    const fields_len = pool.extra.items[off + 3];
    const aligns_len = pool.extra.items[off + 4];
    var base = off + 5;
    const names: []const NullTerminatedString = @ptrCast(pool.extra.items[base..][0..fields_len]);
    base += fields_len;
    const types: []const Index = @ptrCast(pool.extra.items[base..][0..fields_len]);
    base += fields_len;
    return .{
        .layout = @enumFromInt(pool.extra.items[off]),
        .tag_type = @enumFromInt(pool.extra.items[off + 1]),
        .backing_int = @enumFromInt(pool.extra.items[off + 2]),
        .names = names,
        .types = types,
        .aligns = @ptrCast(pool.extra.items[base..][0..aligns_len]),
    };
}

/// Store a reified union's resolved fields (idempotent -- a no-op once set). Each
/// `aligns[i]` is `.none` for a field without an explicit alignment; the slice is
/// empty when no field has one. Only the `field_data` slot is filled, in place.
pub fn setUnionFields(
    pool: *InternPool,
    union_ty: Index,
    layout: std.lang.Type.ContainerLayout,
    tag_type: Index,
    backing_int: Index,
    names: []const NullTerminatedString,
    types: []const Index,
    aligns: []const Index,
) Allocator.Error!void {
    assert(types.len == names.len);
    assert(aligns.len == 0 or aligns.len == names.len);
    const item = pool.items.get(@intFromEnum(union_ty));
    assert(item.tag == .type_union);
    const slot = item.data + @offsetOf(UnionTypeRepr, "field_data") / 4;
    if (pool.extra.items[slot] != fields_unresolved) return;
    const off: u32 = @intCast(pool.extra.items.len);
    try pool.extra.ensureUnusedCapacity(pool.gpa, 5 + names.len + types.len + aligns.len);
    pool.extra.appendAssumeCapacity(@intFromEnum(layout));
    pool.extra.appendAssumeCapacity(@intFromEnum(tag_type));
    pool.extra.appendAssumeCapacity(@intFromEnum(backing_int));
    pool.extra.appendAssumeCapacity(@intCast(names.len));
    pool.extra.appendAssumeCapacity(@intCast(aligns.len));
    for (names) |n| pool.extra.appendAssumeCapacity(@intFromEnum(n));
    for (types) |t| pool.extra.appendAssumeCapacity(@intFromEnum(t));
    for (aligns) |a| pool.extra.appendAssumeCapacity(@intFromEnum(a));
    pool.extra.items[slot] = off;
}

fn emitUnionValue(pool: *InternPool, uv: Key.Union) Allocator.Error!void {
    const extra_index = try pool.addExtra(UnionValueRepr{
        .ty = @intFromEnum(uv.ty),
        .tag = @intFromEnum(uv.tag),
        .val = @intFromEnum(uv.val),
    });
    pool.items.appendAssumeCapacity(.{ .tag = .union_value, .data = extra_index });
}

/// Emit a `ptr_slice` Item.
fn emitSlice(pool: *InternPool, s: Key.Slice) Allocator.Error!void {
    const extra_index = try pool.addExtra(SliceRepr{
        .ty = @intFromEnum(s.ty),
        .ptr = @intFromEnum(s.ptr),
        .len = @intFromEnum(s.len),
    });
    pool.items.appendAssumeCapacity(.{ .tag = .ptr_slice, .data = extra_index });
}

/// Emit an `error_set_error` Item.
fn emitErr(pool: *InternPool, e: Key.Error) Allocator.Error!void {
    assert(e.ty != .none);

    const extra_index = try pool.addExtra(ErrRepr{
        .ty = @intFromEnum(e.ty),
        .name = @intFromEnum(e.name),
    });
    pool.items.appendAssumeCapacity(.{ .tag = .error_set_error, .data = extra_index });
}

/// Effective element count for an aggregate type; for an array it's
/// `lenIncludingSentinel`. Used by both the encoder (deciding trailing length) and
/// the decoder (slicing the trailing Indices). The compiler has the equivalent
/// inline at the call sites of `Tag.Aggregate.trailing.element_values.len`
/// (`src/InternPool.zig`).
pub fn aggregateElementCount(pool: *const InternPool, ty: Index) u64 {
    assert(ty != .none);
    const key = pool.indexToKey(ty);
    return switch (key) {
        .array_type => |at| at.lenIncludingSentinel(),
        .vector_type => |vt| vt.len,
        .tuple_type => |tt| tt.types.len,
        else => unreachable,
    };
}

/// Element count of an aggregate *value* from its storage: `.elems` is its
/// own length; `.repeated_elem` needs the type's count. Lets struct
/// aggregates (whose `struct_type` is not in `aggregateElementCount`, since
/// fields aren't stored in the Key) hash/compare without a type-side count.
fn aggregateLen(pool: *const InternPool, agg: Key.Aggregate) u64 {
    return switch (agg.storage) {
        .elems => |es| es.len,
        .repeated_elem => aggregateElementCount(pool, agg.ty),
    };
}

/// Resolve element `i` from any storage flavor. Hash and eql use this to walk the
/// expanded element sequence so `.elems = [I, I, I]` and `.repeated_elem = I` (same
/// `ty`) produce the same hash + compare equal without insert-time canonicalization.
pub fn aggregateElementAt(agg: Key.Aggregate, i: u64) Index {
    return switch (agg.storage) {
        .repeated_elem => |e| e,
        .elems => |es| blk: {
            assert(i < es.len);
            break :blk es[@intCast(i)];
        },
    };
}

/// Emit an aggregate value. The caller's storage flavor picks the
/// Tag (`elems` -> `aggregate`, `repeated_elem` -> `repeated`).
/// Hash/eql canonicalization in `get()` ensures equivalent
/// sequences across flavors land at one Index without modifying
/// caller input.
fn emitAggregate(pool: *InternPool, agg: Key.Aggregate) Allocator.Error!void {
    assert(agg.ty != .none);
    switch (agg.storage) {
        .repeated_elem => |elem| {
            const extra_index = try pool.addExtra(RepeatedRepr{
                .ty = @intFromEnum(agg.ty),
                .elem_val = @intFromEnum(elem),
            });
            pool.items.appendAssumeCapacity(.{ .tag = .repeated, .data = extra_index });
        },
        .elems => |elems| {
            const extra_index: u32 = @intCast(pool.extra.items.len);
            try pool.extra.ensureUnusedCapacity(pool.gpa, 2 + elems.len);
            pool.extra.appendAssumeCapacity(@intFromEnum(agg.ty));
            pool.extra.appendAssumeCapacity(@intCast(elems.len));
            for (elems) |e| pool.extra.appendAssumeCapacity(@intFromEnum(e));
            pool.items.appendAssumeCapacity(.{ .tag = .aggregate, .data = extra_index });
        },
    }
}

/// Emit an array type. Picks `type_array_small` when the length
/// fits in u32 AND there's no sentinel; otherwise `type_array_big`.
/// Adding sentinel support for the small Tag would force a Tag-shape
/// change; routing through big when a sentinel is present keeps
/// `type_array_small` faithful to its "Vector { len, child }" layout.
fn emitArrayType(pool: *InternPool, at: Key.ArrayType) Allocator.Error!void {
    assert(at.child != .none);
    if (at.sentinel == .none and at.len <= std.math.maxInt(u32)) {
        const extra_index = try pool.addExtra(VectorTypeRepr{
            .len = @intCast(at.len),
            .child = @intFromEnum(at.child),
        });
        pool.items.appendAssumeCapacity(.{ .tag = .type_array_small, .data = extra_index });
        return;
    }
    const extra_index = try pool.addExtra(ArrayTypeBigRepr{
        .len_lo = @truncate(at.len),
        .len_hi = @truncate(at.len >> 32),
        .child = @intFromEnum(at.child),
        .sentinel = @intFromEnum(at.sentinel),
    });
    pool.items.appendAssumeCapacity(.{ .tag = .type_array_big, .data = extra_index });
}

/// Emit a `type_vector` Item. Two u32 slots: `len`, `child`.
fn emitVectorType(pool: *InternPool, vt: Key.VectorType) Allocator.Error!void {
    assert(vt.child != .none);
    const extra_index = try pool.addExtra(VectorTypeRepr{
        .len = vt.len,
        .child = @intFromEnum(vt.child),
    });
    pool.items.appendAssumeCapacity(.{ .tag = .type_vector, .data = extra_index });
}

/// Emit a `type_optional` Item. data = the child type Index (inline,
/// like `type_anyframe`).
fn appendOptionalType(pool: *InternPool, child: Index) void {
    assert(child != .none);
    pool.items.appendAssumeCapacity(.{
        .tag = .type_optional,
        .data = @intFromEnum(child),
    });
}

/// Emit an optional value. A `null` optional (`val == .none`) is the
/// inline `opt_null` Tag carrying the optional type; otherwise the
/// `opt_payload` Tag stores `(ty, val)` in extra.
fn emitOpt(pool: *InternPool, o: Key.Opt) Allocator.Error!void {
    assert(o.ty != .none);
    if (o.val == .none) {
        pool.items.appendAssumeCapacity(.{
            .tag = .opt_null,
            .data = @intFromEnum(o.ty),
        });
        return;
    }
    const extra_index = try pool.addExtra(OptPayloadRepr{
        .ty = @intFromEnum(o.ty),
        .val = @intFromEnum(o.val),
    });
    pool.items.appendAssumeCapacity(.{ .tag = .opt_payload, .data = extra_index });
}

/// Emit a `type_error_union` Item. Two u32 slots: `error_set`, `payload`.
fn emitErrorUnionType(pool: *InternPool, eu: Key.ErrorUnionType) Allocator.Error!void {
    assert(eu.error_set_type != .none);
    assert(eu.payload_type != .none);

    const extra_index = try pool.addExtra(ErrorUnionTypeRepr{
        .error_set = @intFromEnum(eu.error_set_type),
        .payload = @intFromEnum(eu.payload_type),
    });
    pool.items.appendAssumeCapacity(.{ .tag = .type_error_union, .data = extra_index });
}

/// Emit an error-union value. Two tags discriminate the `.err` vs
/// `.payload` variants; each carries (ty, payload_u32).
fn emitErrorUnion(pool: *InternPool, eu: Key.ErrorUnion) Allocator.Error!void {
    assert(eu.ty != .none);

    switch (eu.val) {
        .err_name => |name| {
            const extra_index = try pool.addExtra(ErrorUnionErrRepr{
                .ty = @intFromEnum(eu.ty),
                .err_name = @intFromEnum(name),
            });
            pool.items.appendAssumeCapacity(.{ .tag = .error_union_error, .data = extra_index });
        },
        .payload => |idx| {
            const extra_index = try pool.addExtra(ErrorUnionPayloadRepr{
                .ty = @intFromEnum(eu.ty),
                .payload = @intFromEnum(idx),
            });
            pool.items.appendAssumeCapacity(.{ .tag = .error_union_payload, .data = extra_index });
        },
    }
}

pub fn internPtrType(pool: *InternPool, pt: Key.PtrType) Allocator.Error!Index {
    return pool.get(.{ .ptr_type = pt });
}

pub fn internPtr(pool: *InternPool, p: Key.Ptr) Allocator.Error!Index {
    return pool.get(.{ .ptr = p });
}

pub fn internTupleType(pool: *InternPool, types: []const Index) Allocator.Error!Index {
    return pool.get(.{ .tuple_type = .{ .types = types } });
}

pub fn internStructType(pool: *InternPool, st: Key.StructType) Allocator.Error!Index {
    return pool.get(.{ .struct_type = st });
}

pub fn internEnumType(pool: *InternPool, et: Key.EnumType) Allocator.Error!Index {
    return pool.get(.{ .enum_type = et });
}

pub fn internEnumTag(pool: *InternPool, et: Key.EnumTag) Allocator.Error!Index {
    return pool.get(.{ .enum_tag = et });
}

pub fn internUnionType(pool: *InternPool, ut: Key.UnionType) Allocator.Error!Index {
    return pool.get(.{ .union_type = ut });
}

pub fn internUnion(pool: *InternPool, uv: Key.Union) Allocator.Error!Index {
    return pool.get(.{ .un = uv });
}

/// Intern an error-set type from `names`. Sorts the names by their
/// `NullTerminatedString` integer value first so two sets sharing
/// the same membership intern to the same `Index` regardless of
/// source ordering -- mirrors the compiler's
/// `errorSetFromUnsortedNames` discipline. Caller-provided `names`
/// is not mutated; sorting happens on a fresh copy.
pub fn internErrorSetType(
    pool: *InternPool,
    names: []const NullTerminatedString,
) Allocator.Error!Index {
    const sorted = try pool.gpa.dupe(NullTerminatedString, names);
    defer pool.gpa.free(sorted);
    std.mem.sortUnstable(NullTerminatedString, sorted, {}, lessThanString);
    return pool.get(.{ .error_set_type = .{ .names = sorted } });
}

fn lessThanString(_: void, a: NullTerminatedString, b: NullTerminatedString) bool {
    return @intFromEnum(a) < @intFromEnum(b);
}

/// Convenience: intern the singleton error-set `error{<name>}`.
/// Matches the compiler's `pt.singleErrorSetType(name)` -- used by
/// `evalErrorValue` to give each `error.X` expression its most
/// precise type.
pub fn singletonErrorSetType(
    pool: *InternPool,
    name: NullTerminatedString,
) Allocator.Error!Index {
    return pool.internErrorSetType(&.{name});
}

pub fn internErr(pool: *InternPool, e: Key.Error) Allocator.Error!Index {
    return pool.get(.{ .err = e });
}

pub fn internArrayType(pool: *InternPool, at: Key.ArrayType) Allocator.Error!Index {
    return pool.get(.{ .array_type = at });
}

pub fn internVectorType(pool: *InternPool, vt: Key.VectorType) Allocator.Error!Index {
    return pool.get(.{ .vector_type = vt });
}

pub fn internOptionalType(pool: *InternPool, child: Index) Allocator.Error!Index {
    return pool.get(.{ .opt_type = child });
}

pub fn internOpt(pool: *InternPool, o: Key.Opt) Allocator.Error!Index {
    return pool.get(.{ .opt = o });
}

/// Intern an aggregate value. The caller's storage flavor is
/// preserved; structural eql in `get()` collapses `.elems` and
/// `.repeated_elem` to the same Index when they represent the same
/// per-element sequence (matching compiler src/InternPool.zig
/// ~3057). First-inserted storage flavor wins on subsequent lookups.
pub fn internAggregate(pool: *InternPool, agg: Key.Aggregate) Allocator.Error!Index {
    return pool.get(.{ .aggregate = agg });
}

pub fn internErrorUnionType(pool: *InternPool, eu: Key.ErrorUnionType) Allocator.Error!Index {
    return pool.get(.{ .error_union_type = eu });
}

pub fn internErrorUnion(pool: *InternPool, eu: Key.ErrorUnion) Allocator.Error!Index {
    return pool.get(.{ .error_union = eu });
}

pub fn internFuncType(pool: *InternPool, ft: Key.FuncType) Allocator.Error!Index {
    return pool.get(.{ .func_type = ft });
}

pub fn internFunc(pool: *InternPool, f: Key.Func) Allocator.Error!Index {
    return pool.get(.{ .func = f });
}

/// Emit a `type_function` Item. Header is `FuncTypeRepr` (3 u32
/// slots); trailing `comptime_bits` / `noalias_bits` slots appear
/// only when the flags say so; then `param_types[params_len]`.
fn emitFuncType(pool: *InternPool, ft: Key.FuncType) Allocator.Error!void {
    assert(ft.return_type != .none);
    assert(ft.param_types.len <= std.math.maxInt(u32));

    const has_comptime_bits = ft.comptime_bits != 0;
    const has_noalias_bits = ft.noalias_bits != 0;
    const flags: FuncTypeRepr.Flags = .{
        .cc_tag = ft.cc,
        .is_var_args = ft.is_var_args,
        .is_noinline = ft.is_noinline,
        .has_comptime_bits = has_comptime_bits,
        .has_noalias_bits = has_noalias_bits,
    };

    const extra_index: u32 = @intCast(pool.extra.items.len);
    const header_slots: u32 = 3;
    const opt_slots: u32 = @as(u32, @intFromBool(has_comptime_bits)) +
        @as(u32, @intFromBool(has_noalias_bits));
    const param_slots: u32 = @intCast(ft.param_types.len);
    try pool.extra.ensureUnusedCapacity(pool.gpa, header_slots + opt_slots + param_slots);

    pool.extra.appendAssumeCapacity(@intCast(ft.param_types.len));
    pool.extra.appendAssumeCapacity(@intFromEnum(ft.return_type));
    pool.extra.appendAssumeCapacity(@bitCast(flags));
    if (has_comptime_bits) pool.extra.appendAssumeCapacity(ft.comptime_bits);
    if (has_noalias_bits) pool.extra.appendAssumeCapacity(ft.noalias_bits);
    for (ft.param_types) |p| pool.extra.appendAssumeCapacity(@intFromEnum(p));

    pool.items.appendAssumeCapacity(.{ .tag = .type_function, .data = extra_index });
}

/// Emit a `func` Item. Dispatches between Tag.func_decl,
/// Tag.func_instance, and Tag.func_coerced based on the Key.Func
/// shape.
fn emitFunc(pool: *InternPool, f: Key.Func) Allocator.Error!void {
    assert(f.ty != .none);
    assert(f.uncoerced_ty != .none);

    const extra_index: u32 = @intCast(pool.extra.items.len);
    if (f.generic_owner != .none) {
        try pool.extra.ensureUnusedCapacity(pool.gpa, 4 + f.comptime_args.len);
        pool.extra.appendAssumeCapacity(f.source_zir_id);
        pool.extra.appendAssumeCapacity(@intFromEnum(f.ty));
        pool.extra.appendAssumeCapacity(@intFromEnum(f.generic_owner));
        pool.extra.appendAssumeCapacity(@intCast(f.comptime_args.len));
        for (f.comptime_args) |arg| pool.extra.appendAssumeCapacity(@intFromEnum(arg));
        pool.items.appendAssumeCapacity(.{ .tag = .func_instance, .data = extra_index });
        return;
    }
    if (f.uncoerced_ty != f.ty) {
        // func_coerced: store the destination ty + the inner
        // (uncoerced) func index. The inner index round-trips back
        // through indexToKey to recover uncoerced_ty,
        // zir_body_inst, and source_zir_id.
        const inner = try pool.internFunc(.{
            .source_zir_id = f.source_zir_id,
            .ty = f.uncoerced_ty,
            .uncoerced_ty = f.uncoerced_ty,
            .zir_body_inst = f.zir_body_inst,
            .parent = f.parent,
        });
        const coerced_extra: u32 = @intCast(pool.extra.items.len);
        try pool.extra.appendSlice(pool.gpa, &.{
            @intFromEnum(f.ty),
            @intFromEnum(inner),
        });
        pool.items.appendAssumeCapacity(.{ .tag = .func_coerced, .data = coerced_extra });
        return;
    }
    try pool.extra.appendSlice(pool.gpa, &.{
        f.source_zir_id,
        @intFromEnum(f.ty),
        @intFromEnum(f.zir_body_inst),
        @intFromEnum(f.parent),
    });
    pool.items.appendAssumeCapacity(.{ .tag = .func_decl, .data = extra_index });
}

fn funcTypeFromExtra(pool: *const InternPool, extra_index: u32) Key {
    assert(extra_index + 3 <= pool.extra.items.len);
    const params_len = pool.extra.items[extra_index];
    const return_type: Index = @enumFromInt(pool.extra.items[extra_index + 1]);
    const flags: FuncTypeRepr.Flags = @bitCast(pool.extra.items[extra_index + 2]);

    var trail: usize = extra_index + 3;
    const comptime_bits: u32 = if (flags.has_comptime_bits) blk: {
        const v = pool.extra.items[trail];
        trail += 1;
        break :blk v;
    } else 0;
    const noalias_bits: u32 = if (flags.has_noalias_bits) blk: {
        const v = pool.extra.items[trail];
        trail += 1;
        break :blk v;
    } else 0;
    assert(trail + params_len <= pool.extra.items.len);

    // Park the param slice straight from `extra`. Lifetime matches
    // the pool's; callers should not retain across pool mutations
    // that may reallocate `extra` (same discipline as
    // `error_set_type.names`).
    const param_slots = pool.extra.items[trail..][0..params_len];
    const param_types: []const Index = @ptrCast(param_slots);

    // Minimal calling-convention storage: reconstruct the CC variant
    // with a default-initialised payload (incoming_stack_alignment =
    // null for variants that carry one). FFI widens to full
    // `PackedCallingConvention` round-trip.
    const cc: std.lang.CallingConvention = ccFromTag(flags.cc_tag);

    return .{ .func_type = .{
        .param_types = param_types,
        .return_type = return_type,
        .comptime_bits = comptime_bits,
        .noalias_bits = noalias_bits,
        .cc = cc,
        .is_var_args = flags.is_var_args,
        .is_noinline = flags.is_noinline,
    } };
}

fn funcDeclFromExtra(pool: *const InternPool, extra_index: u32) Key {
    assert(extra_index + 4 <= pool.extra.items.len);
    const source_zir_id = pool.extra.items[extra_index];
    const ty: Index = @enumFromInt(pool.extra.items[extra_index + 1]);
    return .{ .func = .{
        .source_zir_id = source_zir_id,
        .ty = ty,
        .uncoerced_ty = ty,
        .zir_body_inst = @enumFromInt(pool.extra.items[extra_index + 2]),
        .parent = @enumFromInt(pool.extra.items[extra_index + 3]),
    } };
}

fn funcInstanceFromExtra(pool: *const InternPool, extra_index: u32) Key {
    assert(extra_index + 4 <= pool.extra.items.len);
    const source_zir_id = pool.extra.items[extra_index];
    const ty: Index = @enumFromInt(pool.extra.items[extra_index + 1]);
    const generic_owner: Index = @enumFromInt(pool.extra.items[extra_index + 2]);
    const args_len = pool.extra.items[extra_index + 3];
    assert(extra_index + 4 + args_len <= pool.extra.items.len);
    const args_slots = pool.extra.items[extra_index + 4 ..][0..args_len];
    const comptime_args: []const Index = @ptrCast(args_slots);

    // Body inst comes from the generic owner's func_decl.
    const owner_key = pool.indexToKey(generic_owner).func;
    return .{ .func = .{
        .source_zir_id = source_zir_id,
        .ty = ty,
        .uncoerced_ty = ty,
        .zir_body_inst = owner_key.zir_body_inst,
        .generic_owner = generic_owner,
        .comptime_args = comptime_args,
    } };
}

fn funcCoercedFromExtra(pool: *const InternPool, extra_index: u32) Key {
    assert(extra_index + 2 <= pool.extra.items.len);
    const ty: Index = @enumFromInt(pool.extra.items[extra_index]);
    const inner_index: Index = @enumFromInt(pool.extra.items[extra_index + 1]);
    // Invariant: `inner_func` is always a flattened `func_decl` or
    // `func_instance` -- never another `func_coerced`. `emitFunc`
    // enforces this on the write side (it builds `inner` via a
    // direct `internFunc` of the uncoerced form). Asserting here
    // keeps the recursion through indexToKey bounded at one level,
    // matching the compiler's flatten-on-intern discipline.
    const inner_tag = pool.items.get(@intFromEnum(inner_index)).tag;
    assert(inner_tag == .func_decl or inner_tag == .func_instance);
    const inner_key = pool.indexToKey(inner_index).func;
    return .{ .func = .{
        .source_zir_id = inner_key.source_zir_id,
        .ty = ty,
        .uncoerced_ty = inner_key.uncoerced_ty,
        .zir_body_inst = inner_key.zir_body_inst,
        .parent = inner_key.parent,
        .generic_owner = inner_key.generic_owner,
        .comptime_args = inner_key.comptime_args,
    } };
}

/// Reconstruct a `std.lang.CallingConvention` from its packed tag.
/// Minimal storage keeps only the tag; the payload is reconstructed
/// here for the safe variants AstGen emits in normal user code
/// (void-payload CCs + the common per-target `.c` aliases whose
/// payload is `CommonOptions{}`, all-default-fields). Variants
/// whose payload has required fields (`spirv_*.mode`,
/// `arm_interrupt.type`, etc.) panic loudly here so a future ZIR
/// path using one of them surfaces immediately rather than reading
/// undefined memory; lifted to full pack/unpack with FFI.
fn ccFromTag(tag: std.lang.CallingConvention.Tag) std.lang.CallingConvention {
    return switch (tag) {
        .auto => .auto,
        .async => .async,
        .naked => .naked,
        .@"inline" => .@"inline",
        .x86_64_sysv => .{ .x86_64_sysv = .{} },
        .x86_64_win => .{ .x86_64_win = .{} },
        .x86_sysv => .{ .x86_sysv = .{} },
        .x86_win => .{ .x86_win = .{} },
        .x86_stdcall => .{ .x86_stdcall = .{} },
        .x86_fastcall => .{ .x86_fastcall = .{} },
        .x86_thiscall => .{ .x86_thiscall = .{} },
        .x86_vectorcall => .{ .x86_vectorcall = .{} },
        .aarch64_aapcs => .{ .aarch64_aapcs = .{} },
        .aarch64_aapcs_darwin => .{ .aarch64_aapcs_darwin = .{} },
        .aarch64_aapcs_win => .{ .aarch64_aapcs_win = .{} },
        .aarch64_vfabi => .{ .aarch64_vfabi = .{} },
        .aarch64_vfabi_sve => .{ .aarch64_vfabi_sve = .{} },
        .arm_aapcs => .{ .arm_aapcs = .{} },
        .arm_aapcs_vfp => .{ .arm_aapcs_vfp = .{} },
        .riscv64_lp64 => .{ .riscv64_lp64 = .{} },
        .riscv32_ilp32 => .{ .riscv32_ilp32 = .{} },
        else => @panic("InternPool: round-trip for this CallingConvention.Tag variant not yet implemented"),
    };
}

/// True IFF `ty` identifies a Zig float type.
fn isFloatType(ty: Index) bool {
    return switch (ty) {
        .f16_type,
        .f32_type,
        .f64_type,
        .f80_type,
        .f128_type,
        .c_longdouble_type,
        .comptime_float_type,
        => true,
        else => false,
    };
}

/// True if `ty` identifies a Zig integer type: any int_type slot, any
/// fixed-width int, comptime_int, usize / isize, or the c_* family.
fn isIntegerType(pool: *const InternPool, ty: Index) bool {
    return switch (ty) {
        .comptime_int_type,
        .usize_type,
        .isize_type,
        .c_char_type,
        .c_short_type,
        .c_ushort_type,
        .c_int_type,
        .c_uint_type,
        .c_long_type,
        .c_ulong_type,
        .c_longlong_type,
        .c_ulonglong_type,
        => true,
        else => switch (pool.indexToKey(ty)) {
            .int_type => true,
            else => isWellKnownFixedWidthIntType(ty),
        },
    };
}

fn isWellKnownFixedWidthIntType(ty: Index) bool {
    return switch (ty) {
        .u0_type,
        .u1_type,
        .u8_type,
        .i8_type,
        .u16_type,
        .i16_type,
        .u29_type,
        .u32_type,
        .i32_type,
        .u64_type,
        .i64_type,
        .u80_type,
        .u128_type,
        .i128_type,
        .u256_type,
        => true,
        else => false,
    };
}

pub fn internIntValue(
    pool: *InternPool,
    ty: Index,
    value: BigIntConst,
) Allocator.Error!Index {
    return internInt(pool, .{ .ty = ty, .storage = .{ .big_int = value } });
}

fn limbsAliasPool(pool: *const InternPool, limbs: []const std.math.big.Limb) bool {
    if (limbs.len == 0) return false;

    const buffer = pool.big_int_limbs.allocatedSlice();
    if (buffer.len == 0) return false;

    const buf_start = @intFromPtr(buffer.ptr);
    const buf_end = buf_start + buffer.len * @sizeOf(std.math.big.Limb);
    assert(buf_end >= buf_start); // no wraparound

    const slice_start = @intFromPtr(limbs.ptr);
    return slice_start >= buf_start and slice_start < buf_end;
}

/// Append an `int_positive` / `int_negative` item: packed
/// `IntBigHeader` at the head of a `big_int_limbs` slot, limbs
/// trailing inline. Aliasing-safe: dups through gpa if the source
/// limbs reference the arena itself.
fn addBigInt(pool: *InternPool, ty: Index, value: BigIntConst) Allocator.Error!void {
    assert(ty != .none);
    assert(value.limbs.len > 0);
    assert(value.limbs.len <= std.math.maxInt(u32));

    if (limbsAliasPool(pool, value.limbs)) {
        const copy = try pool.gpa.dupe(std.math.big.Limb, value.limbs);
        defer pool.gpa.free(copy);
        try addBigIntAssumingSafe(pool, ty, copy, value.positive);
        return;
    }
    try addBigIntAssumingSafe(pool, ty, value.limbs, value.positive);
}

fn addBigIntAssumingSafe(
    pool: *InternPool,
    ty: Index,
    limbs: []const std.math.big.Limb,
    positive: bool,
) Allocator.Error!void {
    assert(!limbsAliasPool(pool, limbs));

    const limb_index: u32 = @intCast(pool.big_int_limbs.items.len);
    try pool.big_int_limbs.ensureUnusedCapacity(pool.gpa, IntBigHeader.limbs_items_len + limbs.len);

    const header: IntBigHeader = .{ .ty = @intFromEnum(ty), .limbs_len = @intCast(limbs.len) };
    const header_words: [IntBigHeader.limbs_items_len]std.math.big.Limb = @bitCast(header);
    pool.big_int_limbs.appendSliceAssumeCapacity(&header_words);
    pool.big_int_limbs.appendSliceAssumeCapacity(limbs);

    try pool.items.append(pool.gpa, .{
        .tag = if (positive) .int_positive else .int_negative,
        .data = limb_index,
    });
}

pub fn internComptimeInt(pool: *InternPool, value: BigIntConst) Allocator.Error!Index {
    return pool.internIntValue(.comptime_int_type, value);
}

pub fn itemCount(pool: *const InternPool) u32 {
    return @intCast(pool.items.len);
}

test "well-known types have expected keys" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    try std.testing.expectEqual(@as(u16, 8), pool.indexToKey(.u8_type).int_type.bits);
    try std.testing.expectEqual(@as(u16, 32), pool.indexToKey(.u32_type).int_type.bits);
    try std.testing.expectEqual(std.lang.Signedness.signed, pool.indexToKey(.i32_type).int_type.signedness);

    try std.testing.expectEqual(SimpleType.usize, pool.indexToKey(.usize_type).simple_type);
    try std.testing.expectEqual(SimpleType.c_int, pool.indexToKey(.c_int_type).simple_type);
    try std.testing.expectEqual(SimpleType.f64, pool.indexToKey(.f64_type).simple_type);
    try std.testing.expectEqual(SimpleType.bool, pool.indexToKey(.bool_type).simple_type);
}

test "i0_type and anyframe_type slots match compiler ordering" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    // Zir.Inst.Ref has no i0_type slot, so our Index doesn't either.
    // `internIntType(.signed, 0)` therefore allocates a fresh dynamic
    // item rather than landing on a well-known slot.
    const items_before = pool.itemCount();
    const signed_zero_idx = try pool.internIntType(.signed, 0);
    try std.testing.expect(@intFromEnum(signed_zero_idx) >= first_dynamic_index);
    try std.testing.expectEqual(items_before + 1, pool.itemCount());
    try std.testing.expectEqual(@as(u16, 0), pool.indexToKey(signed_zero_idx).int_type.bits);
    try std.testing.expectEqual(std.lang.Signedness.signed, pool.indexToKey(signed_zero_idx).int_type.signedness);

    try std.testing.expectEqual(Index.none, pool.indexToKey(.anyframe_type).anyframe_type);
}

test "well-known values have expected keys" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    try std.testing.expectEqual(SimpleValue.true, pool.indexToKey(.bool_true).simple_value);
    try std.testing.expectEqual(SimpleValue.false, pool.indexToKey(.bool_false).simple_value);
    try std.testing.expectEqual(SimpleValue.void, pool.indexToKey(.void_value).simple_value);

    const zero = pool.indexToKey(.zero).int;
    try std.testing.expectEqual(Index.comptime_int_type, zero.ty);
    try std.testing.expectEqual(@as(u64, 0), zero.storage.u64);

    const negative_one = pool.indexToKey(.negative_one).int;
    try std.testing.expectEqual(@as(i64, -1), negative_one.storage.i64);
}

test "range markers cover the well-known sets" {
    try std.testing.expect(Index.isWellKnownType(.u0_type));
    try std.testing.expect(Index.isWellKnownType(.enum_literal_type));
    try std.testing.expect(!Index.isWellKnownType(.bool_true));
    try std.testing.expect(!Index.isWellKnownType(.none));

    try std.testing.expect(Index.isWellKnownValue(.undef));
    try std.testing.expect(Index.isWellKnownValue(.bool_false));
    try std.testing.expect(!Index.isWellKnownValue(.u8_type));
}

test "arbitrary-width int types intern dynamically" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    const items_before = pool.itemCount();
    const u32_idx = try pool.internIntType(.unsigned, 32);
    try std.testing.expectEqual(Index.u32_type, u32_idx);
    try std.testing.expectEqual(items_before, pool.itemCount());

    const u17_idx = try pool.internIntType(.unsigned, 17);
    try std.testing.expect(!Index.isWellKnownType(u17_idx));
    const @"u17" = pool.indexToKey(u17_idx).int_type;
    try std.testing.expectEqual(std.lang.Signedness.unsigned, @"u17".signedness);
    try std.testing.expectEqual(@as(u16, 17), @"u17".bits);

    const u65535_idx = try pool.internIntType(.unsigned, std.math.maxInt(u16));
    const @"u65535" = pool.indexToKey(u65535_idx).int_type;
    try std.testing.expectEqual(@as(u16, std.math.maxInt(u16)), @"u65535".bits);
}

test "internInt big-int storage is aliasing-safe under buffer growth" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    // A multi-limb value forces the big-int path; the small int_u8..int_small
    // fast paths would otherwise compress 42 to an inline tag.
    var big_src = [_]std.math.big.Limb{ 0, 1 }; // 2^@bitSizeOf(Limb)
    const a_idx = try pool.internIntValue(.u128_type, .{ .limbs = &big_src, .positive = true });

    // Force `big_int_limbs` to capacity so the next append must
    // reallocate. Without the aliasing guard the subsequent reintern
    // would memcpy from a stale source pointer (the limbs slice we
    // pulled from the just-interned value lives inside the arena).
    while (pool.big_int_limbs.items.len < pool.big_int_limbs.capacity) {
        try pool.big_int_limbs.append(pool.gpa, 0);
    }

    const a_view = pool.indexToKey(a_idx).int.storage.big_int;
    const aliased: BigIntConst = .{ .limbs = a_view.limbs, .positive = false };

    const b_idx = try pool.internIntValue(.u128_type, aliased);
    const b = pool.indexToKey(b_idx).int.storage.big_int;
    try std.testing.expectEqual(@as(usize, 2), b.limbs.len);
    try std.testing.expectEqual(@as(std.math.big.Limb, 0), b.limbs[0]);
    try std.testing.expectEqual(@as(std.math.big.Limb, 1), b.limbs[1]);
    try std.testing.expectEqual(false, b.positive);
}

test "small comptime int compresses to inline tag" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    var limbs = [_]std.math.big.Limb{42};
    const value: BigIntConst = .{ .limbs = &limbs, .positive = true };
    const idx = try pool.internComptimeInt(value);

    // 42 fits in u32 so the compressor picks `int_comptime_int_u32` and
    // surfaces the value as `.storage.u64`, not `.big_int`.
    const round = pool.indexToKey(idx).int;
    try std.testing.expectEqual(Index.comptime_int_type, round.ty);
    try std.testing.expectEqual(@as(u64, 42), round.storage.u64);
}

test "float storage: per-type tags and bit-pattern round-trip" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    const f32_idx = try pool.internFloat(.{ .ty = .f32_type, .storage = .{ .f32 = 1.5 } });
    const f32_round = pool.indexToKey(f32_idx).float;
    try std.testing.expectEqual(Index.f32_type, f32_round.ty);
    try std.testing.expectEqual(@as(f32, 1.5), f32_round.storage.f32);

    const f64_idx = try pool.internFloat(.{
        .ty = .f64_type,
        .storage = .{ .f64 = 3.141592653589793 },
    });
    const f64_round = pool.indexToKey(f64_idx).float;
    try std.testing.expectEqual(Index.f64_type, f64_round.ty);
    try std.testing.expectEqual(@as(f64, 3.141592653589793), f64_round.storage.f64);

    const f128_idx = try pool.internFloat(.{
        .ty = .f128_type,
        .storage = .{ .f128 = 1e30 },
    });
    const f128_round = pool.indexToKey(f128_idx).float;
    try std.testing.expectEqual(Index.f128_type, f128_round.ty);
    try std.testing.expectEqual(@as(f128, 1e30), f128_round.storage.f128);
}

test "float dedup: equal values intern once; equal bit-patterns dedup; differing NaNs do not" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    const items_before = pool.itemCount();
    const a = try pool.internFloat(.{ .ty = .f32_type, .storage = .{ .f32 = 2.5 } });
    const b = try pool.internFloat(.{ .ty = .f32_type, .storage = .{ .f32 = 2.5 } });
    try std.testing.expectEqual(a, b);
    try std.testing.expectEqual(items_before + 1, pool.itemCount());

    // NaN with identical bit-pattern: dedups. (eql compares bit-patterns,
    // not float equality, so NaN==NaN at the bit level.)
    const nan_bits: u32 = 0x7fc00001;
    const nan1: f32 = @bitCast(nan_bits);
    const nan2: f32 = @bitCast(nan_bits);
    const n1 = try pool.internFloat(.{ .ty = .f32_type, .storage = .{ .f32 = nan1 } });
    const n2 = try pool.internFloat(.{ .ty = .f32_type, .storage = .{ .f32 = nan2 } });
    try std.testing.expectEqual(n1, n2);

    const other_nan: f32 = @bitCast(@as(u32, 0x7fc00002));
    const n3 = try pool.internFloat(.{ .ty = .f32_type, .storage = .{ .f32 = other_nan } });
    try std.testing.expect(n1 != n3);
}

test "undef Key variant: well-known slot and typed undef" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    // The well-known `Index.undef` slot is untyped undef, i.e. undef
    // whose carrier type is `.undefined_type`.
    const untyped = pool.indexToKey(.undef).undef;
    try std.testing.expectEqual(Index.undefined_type, untyped);

    // Re-interning the same untyped undef must return the well-known slot,
    // not a fresh dynamic item.
    const round = try pool.get(.{ .undef = .undefined_type });
    try std.testing.expectEqual(Index.undef, round);

    const u32_undef = try pool.get(.{ .undef = .u32_type });
    try std.testing.expect(u32_undef != .undef);
    try std.testing.expectEqual(Index.u32_type, pool.indexToKey(u32_undef).undef);
}

test "interning identical keys dedups to a single Index" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    // Dynamic int_type -- hits the dedup map on the second call.
    const items_before = pool.itemCount();
    const u17_a = try pool.internIntType(.unsigned, 17);
    const u17_b = try pool.internIntType(.unsigned, 17);
    try std.testing.expectEqual(u17_a, u17_b);
    try std.testing.expectEqual(items_before + 1, pool.itemCount());

    // Storage normalisation: `.u64=5` and `.big_int=+5` (as a single
    // u32-fitting limb) must dedup, because `indexToKey` re-emits the
    // big-int as `.u64` and `Key.hash64` normalises inline storage to
    // BigIntConst before hashing.
    var limb = [_]std.math.big.Limb{5};
    const big5: BigIntConst = .{ .limbs = &limb, .positive = true };
    const a = try pool.internInt(.{ .ty = .comptime_int_type, .storage = .{ .u64 = 5 } });
    const b = try pool.internInt(.{ .ty = .comptime_int_type, .storage = .{ .big_int = big5 } });
    try std.testing.expectEqual(a, b);

    // Well-known slots are reached through the same map, so re-interning
    // their key returns the well-known Index (not a fresh dynamic one).
    const zero_again = try pool.internInt(.{ .ty = .comptime_int_type, .storage = .{ .u64 = 0 } });
    try std.testing.expectEqual(Index.zero, zero_again);
}

test "big comptime int round-trips through int_positive limbs" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    // 2^@bitSizeOf(Limb) -- guaranteed multi-limb, doesn't fit in u64
    // on any host (where Limb >= u32, two limbs always exceed u64).
    var limbs = [_]std.math.big.Limb{ 0, 1 };
    const value: BigIntConst = .{ .limbs = &limbs, .positive = true };
    const idx = try pool.internIntValue(.u128_type, value);

    const round = pool.indexToKey(idx).int;
    try std.testing.expectEqual(Index.u128_type, round.ty);
    const big = round.storage.big_int;
    try std.testing.expect(big.positive);
    try std.testing.expectEqual(@as(usize, 2), big.limbs.len);
    try std.testing.expectEqual(@as(std.math.big.Limb, 0), big.limbs[0]);
    try std.testing.expectEqual(@as(std.math.big.Limb, 1), big.limbs[1]);
}

test "ptr_type round-trip and dedup" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    const items_before = pool.itemCount();
    const ty_const_u8 = try pool.internPtrType(.{
        .child = .u8_type,
        .flags = .{ .size = .one, .is_const = true },
    });
    const round = pool.indexToKey(ty_const_u8).ptr_type;
    try std.testing.expectEqual(Index.u8_type, round.child);
    try std.testing.expectEqual(true, round.flags.is_const);
    try std.testing.expectEqual(Key.PtrType.Size.one, round.flags.size);

    const dedup = try pool.internPtrType(.{
        .child = .u8_type,
        .flags = .{ .size = .one, .is_const = true },
    });
    try std.testing.expectEqual(ty_const_u8, dedup);
    try std.testing.expectEqual(items_before + 1, pool.itemCount());

    const ty_mut_u8 = try pool.internPtrType(.{
        .child = .u8_type,
        .flags = .{ .size = .one, .is_const = false },
    });
    try std.testing.expect(ty_mut_u8 != ty_const_u8);
}

test "ptr value round-trip and dedup by base_addr + offset" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    const ptr_ty = try pool.internPtrType(.{ .child = .u32_type });
    const items_before = pool.itemCount();

    const p0 = try pool.internPtr(.{
        .ty = ptr_ty,
        .base_addr = .{ .comptime_alloc = @enumFromInt(7) },
        .byte_offset = 16,
    });
    const round = pool.indexToKey(p0).ptr;
    try std.testing.expectEqual(ptr_ty, round.ty);
    try std.testing.expectEqual(@as(u64, 16), round.byte_offset);
    try std.testing.expectEqual(@as(Key.ComptimeAllocIndex, @enumFromInt(7)), round.base_addr.comptime_alloc);

    const p_dup = try pool.internPtr(.{
        .ty = ptr_ty,
        .base_addr = .{ .comptime_alloc = @enumFromInt(7) },
        .byte_offset = 16,
    });
    try std.testing.expectEqual(p0, p_dup);
    try std.testing.expectEqual(items_before + 1, pool.itemCount());

    const p_other_offset = try pool.internPtr(.{
        .ty = ptr_ty,
        .base_addr = .{ .comptime_alloc = @enumFromInt(7) },
        .byte_offset = 24,
    });
    try std.testing.expect(p_other_offset != p0);
}

test "ptr byte_offset survives the 32-bit boundary" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    const ptr_ty = try pool.internPtrType(.{ .child = .u8_type });
    const huge: u64 = (@as(u64, 1) << 40) + 0xdead;
    const p = try pool.internPtr(.{
        .ty = ptr_ty,
        .base_addr = .{ .comptime_alloc = @enumFromInt(0) },
        .byte_offset = huge,
    });
    try std.testing.expectEqual(huge, pool.indexToKey(p).ptr.byte_offset);
}

test "string interning: empty handle is the well-known sentinel" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    try std.testing.expectEqual(NullTerminatedString.empty, try pool.getOrPutString(pool.gpa, ""));
    try std.testing.expectEqualStrings("", pool.stringSlice(.empty));
}

test "string interning: round-trip a single name" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    const handle = try pool.getOrPutString(pool.gpa, "decl_name");
    try std.testing.expectEqualStrings("decl_name", pool.stringSlice(handle));
}

test "string interning: identical bytes dedup to the same handle" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    const first = try pool.getOrPutString(pool.gpa, "x");
    const second = try pool.getOrPutString(pool.gpa, "x");
    try std.testing.expectEqual(first, second);

    // The second intern should not have grown string_bytes (rollback
    // path: the adapter found the existing key before we appended).
    const bytes_after_first = pool.string_bytes.items.len;
    _ = try pool.getOrPutString(pool.gpa, "x");
    try std.testing.expectEqual(bytes_after_first, pool.string_bytes.items.len);
}

test "string interning: distinct names occupy distinct handles" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    const foo = try pool.getOrPutString(pool.gpa, "foo");
    const bar = try pool.getOrPutString(pool.gpa, "bar");
    try std.testing.expect(foo != bar);
    try std.testing.expectEqualStrings("foo", pool.stringSlice(foo));
    try std.testing.expectEqualStrings("bar", pool.stringSlice(bar));
}

test "string interning: OptionalNullTerminatedString round-trips" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    const handle = try pool.getOrPutString(pool.gpa, "thing");
    const opt = handle.toOptional();
    try std.testing.expect(opt != .none);
    try std.testing.expectEqual(handle, opt.unwrap().?);

    const none: OptionalNullTerminatedString = .init(null);
    try std.testing.expect(none == .none);
    try std.testing.expect(none.unwrap() == null);
}

test "string interning: many names round-trip and dedup correctly" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    const names = [_][]const u8{ "alpha", "beta", "gamma", "delta", "epsilon" };
    var handles: [names.len]NullTerminatedString = undefined;
    for (names, &handles) |name, *out| out.* = try pool.getOrPutString(pool.gpa, name);

    for (handles, names) |handle, expected| {
        try std.testing.expectEqualStrings(expected, pool.stringSlice(handle));
    }

    try std.testing.expectEqual(handles[2], try pool.getOrPutString(pool.gpa, "gamma"));
    try std.testing.expectEqual(handles[0], try pool.getOrPutString(pool.gpa, "alpha"));
    try std.testing.expectEqual(handles[4], try pool.getOrPutString(pool.gpa, "epsilon"));
}

test "Nav: createNav appends with analysis = null and resolved = null" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    const name = try pool.getOrPutString(pool.gpa, "foo");
    const fqn = name;
    const idx = try pool.createNav(pool.gpa, name, fqn);

    const nav = pool.getNav(idx);
    try std.testing.expectEqual(name, nav.name);
    try std.testing.expectEqual(fqn, nav.fqn);
    try std.testing.expect(nav.analysis == null);
    try std.testing.expect(nav.resolved == null);
}

test "Nav: navPtr lets bindDecls populate Resolved in place" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    const name = try pool.getOrPutString(pool.gpa, "answer");
    const idx = try pool.createNav(pool.gpa, name, name);

    pool.navPtr(idx).resolved = .{
        .type = .u32_type,
        .@"align" = .none,
        .@"linksection" = .none,
        .@"addrspace" = .generic,
        .@"const" = true,
        .@"threadlocal" = false,
        .is_extern_decl = false,
        .value = .one,
    };

    const round_trip = pool.getNav(idx).resolved.?;
    try std.testing.expectEqual(Index.u32_type, round_trip.type);
    try std.testing.expectEqual(Index.one, round_trip.value);
    try std.testing.expect(round_trip.@"const");
    try std.testing.expect(!round_trip.@"threadlocal");
    try std.testing.expect(!round_trip.is_extern_decl);
}

test "Nav: createNav allocates a fresh handle each call (no dedup)" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    // Same name twice: createNav is *not* dedup-by-name -- a name
    // collision is a namespace concern (the pub_decls map),
    // not a pool concern. createNav blindly appends.
    const name = try pool.getOrPutString(pool.gpa, "x");
    const first = try pool.createNav(pool.gpa, name, name);
    const second = try pool.createNav(pool.gpa, name, name);
    try std.testing.expect(first != second);
    try std.testing.expectEqual(name, pool.getNav(first).name);
    try std.testing.expectEqual(name, pool.getNav(second).name);
}

test "Namespace: createNamespace seeds an empty parent-less scope" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    const ns_idx = try pool.createNamespace(pool.gpa, .none);
    const ns = pool.namespacePtr(ns_idx);

    // Parent-chain + vestigial fields default to "session root":
    // no parent, no file backing, generation = 0, no owner type.
    try std.testing.expectEqual(OptionalNamespaceIndex.none, ns.parent);
    try std.testing.expectEqual(OptionalFileIndex.none, ns.file_scope);
    try std.testing.expectEqual(@as(u32, 0), ns.generation);
    try std.testing.expectEqual(Index.none, ns.owner_type);

    try std.testing.expectEqual(@as(usize, 0), ns.pub_decls.count());
    try std.testing.expectEqual(@as(usize, 0), ns.priv_decls.count());
    try std.testing.expectEqual(@as(usize, 0), ns.test_decls.items.len);
    try std.testing.expectEqual(@as(usize, 0), ns.comptime_decls.items.len);
}

test "fullyQualifiedName: a root-namespace decl qualifies under the session root" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    const ns = try pool.createNamespace(pool.gpa, .none); // owner_type .none == session root
    const name = try pool.getOrPutString(pool.gpa, "P");
    const fqn = try pool.fullyQualifiedName(pool.gpa, ns, name);
    try std.testing.expectEqualStrings("repl.P", pool.stringSlice(fqn));
}

test "fullyQualifiedName: a member of a named container nests under it" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    // A namespace owned by a struct type named `repl.Outer`; its members
    // qualify under that name. This exercises the owner-type recursion
    // (`containerTypeName`) that activates once a container owns a scope.
    const outer = try pool.internStructType(.{
        .name = try pool.getOrPutString(pool.gpa, "repl.Outer"),
        .id = .{ .declared = .{ .source_zir_id = 0, .decl_inst = @enumFromInt(1) } },
    });
    const ns = try pool.createNamespace(pool.gpa, .none);
    pool.namespacePtr(ns).owner_type = outer;

    const inner = try pool.getOrPutString(pool.gpa, "Inner");
    const fqn = try pool.fullyQualifiedName(pool.gpa, ns, inner);
    try std.testing.expectEqualStrings("repl.Outer.Inner", pool.stringSlice(fqn));
}

test "Namespace: NavNameContext dedups Nav.Index entries by interned name" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    const x = try pool.getOrPutString(pool.gpa, "x");
    const y = try pool.getOrPutString(pool.gpa, "y");
    const first_x = try pool.createNav(pool.gpa, x, x);
    const second_x = try pool.createNav(pool.gpa, x, x);
    const just_y = try pool.createNav(pool.gpa, y, y);

    const ns_idx = try pool.createNamespace(pool.gpa, .none);
    const ns = pool.namespacePtr(ns_idx);
    const ctx: Namespace.NavNameContext = .{ .pool = &pool };

    const gop_x = try ns.pub_decls.getOrPutContext(pool.gpa, first_x, ctx);
    try std.testing.expect(!gop_x.found_existing);
    const gop_y = try ns.pub_decls.getOrPutContext(pool.gpa, just_y, ctx);
    try std.testing.expect(!gop_y.found_existing);

    const gop_x_again = try ns.pub_decls.getOrPutContext(pool.gpa, second_x, ctx);
    try std.testing.expect(gop_x_again.found_existing);
    try std.testing.expectEqual(first_x, gop_x_again.key_ptr.*);

    try std.testing.expectEqual(@as(usize, 2), ns.pub_decls.count());
}

test "Namespace: NameAdapter looks up Nav.Index by interned name" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    const x = try pool.getOrPutString(pool.gpa, "x");
    const nav_x = try pool.createNav(pool.gpa, x, x);

    const ns_idx = try pool.createNamespace(pool.gpa, .none);
    const ns = pool.namespacePtr(ns_idx);
    const ctx: Namespace.NavNameContext = .{ .pool = &pool };
    _ = try ns.pub_decls.getOrPutContext(pool.gpa, nav_x, ctx);

    const adapter: Namespace.NameAdapter = .{ .pool = &pool };
    const found_x = ns.pub_decls.getKeyAdapted(x, adapter);
    try std.testing.expectEqual(@as(?Nav.Index, nav_x), found_x);

    const missing = try pool.getOrPutString(pool.gpa, "missing");
    try std.testing.expectEqual(@as(?Nav.Index, null), ns.pub_decls.getKeyAdapted(missing, adapter));
}

test "Namespace.lookupNav: walks pub_decls then priv_decls, no parent chain" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    const x = try pool.getOrPutString(pool.gpa, "x");
    const y = try pool.getOrPutString(pool.gpa, "y");
    const missing = try pool.getOrPutString(pool.gpa, "z");
    const nav_x = try pool.createNav(pool.gpa, x, x);
    const nav_y = try pool.createNav(pool.gpa, y, y);

    const ns_idx = try pool.createNamespace(pool.gpa, .none);
    const ns = pool.namespacePtr(ns_idx);
    const ctx: Namespace.NavNameContext = .{ .pool = &pool };
    _ = try ns.pub_decls.getOrPutContext(pool.gpa, nav_x, ctx);
    _ = try ns.priv_decls.getOrPutContext(pool.gpa, nav_y, ctx);

    try std.testing.expectEqual(@as(?Nav.Index, nav_x), ns.lookupNav(&pool, x));
    try std.testing.expectEqual(@as(?Nav.Index, nav_y), ns.lookupNav(&pool, y));
    try std.testing.expectEqual(@as(?Nav.Index, null), ns.lookupNav(&pool, missing));
}

test "Namespace.lookupNav: pub_decls takes precedence over priv_decls" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    const x = try pool.getOrPutString(pool.gpa, "x");
    const nav_pub = try pool.createNav(pool.gpa, x, x);
    const nav_priv = try pool.createNav(pool.gpa, x, x);

    const ns_idx = try pool.createNamespace(pool.gpa, .none);
    const ns = pool.namespacePtr(ns_idx);
    const ctx: Namespace.NavNameContext = .{ .pool = &pool };

    // Both maps hold a Nav with name "x" (different Nav.Index values).
    // In real Sema this wouldn't happen (AstGen rejects duplicate names)
    // but the lookup precedence is a contract we want to pin: pub
    // wins, matching the compiler's lookupInNamespace order.
    _ = try ns.priv_decls.getOrPutContext(pool.gpa, nav_priv, ctx);
    _ = try ns.pub_decls.getOrPutContext(pool.gpa, nav_pub, ctx);
    try std.testing.expectEqual(@as(?Nav.Index, nav_pub), ns.lookupNav(&pool, x));
}

test "error_set_type: round-trip + sort discipline" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    const foo = try pool.getOrPutString(pool.gpa, "Foo");
    const bar = try pool.getOrPutString(pool.gpa, "Bar");
    const baz = try pool.getOrPutString(pool.gpa, "Baz");

    // Names provided unsorted; intern sorts by NullTerminatedString
    // integer value so dedup is canonical regardless of source order.
    const idx_a = try pool.internErrorSetType(&.{ baz, foo, bar });
    const idx_b = try pool.internErrorSetType(&.{ foo, bar, baz });
    try std.testing.expectEqual(idx_a, idx_b);

    const round = pool.indexToKey(idx_a).error_set_type;
    try std.testing.expectEqual(@as(usize, 3), round.names.len);
    try std.testing.expect(@intFromEnum(round.names[0]) <= @intFromEnum(round.names[1]));
    try std.testing.expect(@intFromEnum(round.names[1]) <= @intFromEnum(round.names[2]));
}

test "error_set_type: distinct membership produces distinct indices" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    const foo = try pool.getOrPutString(pool.gpa, "Foo");
    const bar = try pool.getOrPutString(pool.gpa, "Bar");
    const baz = try pool.getOrPutString(pool.gpa, "Baz");

    const fb = try pool.internErrorSetType(&.{ foo, bar });
    const fz = try pool.internErrorSetType(&.{ foo, baz });
    try std.testing.expect(fb != fz);
}

test "singletonErrorSetType: one-name set round-trips" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    const foo = try pool.getOrPutString(pool.gpa, "Foo");
    const idx = try pool.singletonErrorSetType(foo);

    const round = pool.indexToKey(idx).error_set_type;
    try std.testing.expectEqual(@as(usize, 1), round.names.len);
    try std.testing.expectEqual(foo, round.names[0]);
}

test "internErr: same {ty, name} dedups" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    const foo = try pool.getOrPutString(pool.gpa, "Foo");
    const ty = try pool.singletonErrorSetType(foo);
    const a = try pool.internErr(.{ .ty = ty, .name = foo });
    const b = try pool.internErr(.{ .ty = ty, .name = foo });
    try std.testing.expectEqual(a, b);

    const round = pool.indexToKey(a).err;
    try std.testing.expectEqual(ty, round.ty);
    try std.testing.expectEqual(foo, round.name);
}

test "error_union_type: round-trip + dedup by (error_set, payload)" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    const bad = try pool.getOrPutString(pool.gpa, "Bad");
    const es = try pool.singletonErrorSetType(bad);

    const eu_a = try pool.internErrorUnionType(.{ .error_set_type = es, .payload_type = .u32_type });
    const eu_b = try pool.internErrorUnionType(.{ .error_set_type = es, .payload_type = .u32_type });
    try std.testing.expectEqual(eu_a, eu_b);

    const eu_c = try pool.internErrorUnionType(.{ .error_set_type = es, .payload_type = .i32_type });
    try std.testing.expect(eu_a != eu_c);

    const round = pool.indexToKey(eu_a).error_union_type;
    try std.testing.expectEqual(es, round.error_set_type);
    try std.testing.expectEqual(Index.u32_type, round.payload_type);
}

test "error_union value: both arms round-trip and dedup independently" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    const bad = try pool.getOrPutString(pool.gpa, "Bad");
    const es = try pool.singletonErrorSetType(bad);
    const eu_ty = try pool.internErrorUnionType(.{ .error_set_type = es, .payload_type = .u32_type });

    const err_val = try pool.internErrorUnion(.{ .ty = eu_ty, .val = .{ .err_name = bad } });
    const err_dup = try pool.internErrorUnion(.{ .ty = eu_ty, .val = .{ .err_name = bad } });
    try std.testing.expectEqual(err_val, err_dup);

    const payload_inner = try pool.get(.{ .int = .{ .ty = .u32_type, .storage = .{ .u64 = 42 } } });
    const payload_val = try pool.internErrorUnion(.{ .ty = eu_ty, .val = .{ .payload = payload_inner } });
    try std.testing.expect(payload_val != err_val);

    const round_err = pool.indexToKey(err_val).error_union;
    try std.testing.expect(round_err.val == .err_name);
    try std.testing.expectEqual(bad, round_err.val.err_name);

    const round_payload = pool.indexToKey(payload_val).error_union;
    try std.testing.expect(round_payload.val == .payload);
    try std.testing.expectEqual(payload_inner, round_payload.val.payload);
}

test "func_type: round-trip + dedup by (params, return, flags)" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    const params = [_]Index{ .u32_type, .i32_type };
    const ft: Key.FuncType = .{ .param_types = &params, .return_type = .void_type };

    const a = try pool.internFuncType(ft);
    const b = try pool.internFuncType(.{ .param_types = &params, .return_type = .void_type });
    try std.testing.expectEqual(a, b);

    const round = pool.indexToKey(a).func_type;
    try std.testing.expectEqual(@as(usize, 2), round.param_types.len);
    try std.testing.expectEqual(Index.u32_type, round.param_types[0]);
    try std.testing.expectEqual(Index.i32_type, round.param_types[1]);
    try std.testing.expectEqual(Index.void_type, round.return_type);
    try std.testing.expectEqual(false, round.is_var_args);
    try std.testing.expectEqual(std.lang.CallingConvention.Tag.auto, round.cc);
}

test "func_type: distinct return type produces distinct index" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    const params = [_]Index{.u32_type};
    const a = try pool.internFuncType(.{ .param_types = &params, .return_type = .void_type });
    const b = try pool.internFuncType(.{ .param_types = &params, .return_type = .u32_type });
    try std.testing.expect(a != b);
}

test "func_type: comptime_bits round-trip via flags" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    const params = [_]Index{ .u32_type, .u32_type };
    const a = try pool.internFuncType(.{
        .param_types = &params,
        .return_type = .void_type,
        .comptime_bits = 0b10, // param 1 is comptime
    });
    const round = pool.indexToKey(a).func_type;
    try std.testing.expectEqual(@as(u32, 0b10), round.comptime_bits);
    try std.testing.expect(!round.paramIsComptime(0));
    try std.testing.expect(round.paramIsComptime(1));
}

test "func_decl: round-trip + dedup by (ty, zir_body_inst)" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    const params = [_]Index{.u32_type};
    const fn_ty = try pool.internFuncType(.{ .param_types = &params, .return_type = .u32_type });
    const body_inst: std.zig.Zir.Inst.Index = @enumFromInt(42);

    const a = try pool.internFunc(.{ .ty = fn_ty, .uncoerced_ty = fn_ty, .zir_body_inst = body_inst });
    const b = try pool.internFunc(.{ .ty = fn_ty, .uncoerced_ty = fn_ty, .zir_body_inst = body_inst });
    try std.testing.expectEqual(a, b);

    const round = pool.indexToKey(a).func;
    try std.testing.expectEqual(fn_ty, round.ty);
    try std.testing.expectEqual(fn_ty, round.uncoerced_ty);
    try std.testing.expectEqual(body_inst, round.zir_body_inst);
    try std.testing.expectEqual(Index.none, round.generic_owner);
    try std.testing.expectEqual(@as(usize, 0), round.comptime_args.len);
}

test "func_decl: distinct zir_body_inst produces distinct index" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    const params = [_]Index{};
    const fn_ty = try pool.internFuncType(.{ .param_types = &params, .return_type = .void_type });

    const a = try pool.internFunc(.{ .ty = fn_ty, .uncoerced_ty = fn_ty, .zir_body_inst = @enumFromInt(1) });
    const b = try pool.internFunc(.{ .ty = fn_ty, .uncoerced_ty = fn_ty, .zir_body_inst = @enumFromInt(2) });
    try std.testing.expect(a != b);
}

test "func_coerced: ty != uncoerced_ty routes through Tag.func_coerced" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    const params = [_]Index{};
    const ty_void = try pool.internFuncType(.{ .param_types = &params, .return_type = .void_type });
    const ty_u32 = try pool.internFuncType(.{ .param_types = &params, .return_type = .u32_type });

    const body_inst: std.zig.Zir.Inst.Index = @enumFromInt(7);
    _ = try pool.internFunc(.{ .ty = ty_void, .uncoerced_ty = ty_void, .zir_body_inst = body_inst });
    const coerced = try pool.internFunc(.{ .ty = ty_u32, .uncoerced_ty = ty_void, .zir_body_inst = body_inst });

    const round = pool.indexToKey(coerced).func;
    try std.testing.expectEqual(ty_u32, round.ty);
    try std.testing.expectEqual(ty_void, round.uncoerced_ty);
    try std.testing.expectEqual(body_inst, round.zir_body_inst);
}

test "ComptimeUnit: createComptimeUnit + getComptimeUnit round-trip" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    const ns_idx = try pool.createNamespace(pool.gpa, .none);
    const zir_inst: std.zig.Zir.Inst.Index = @enumFromInt(42);
    const id = try pool.createComptimeUnit(pool.gpa, ns_idx, zir_inst);

    const unit = pool.getComptimeUnit(id);
    try std.testing.expectEqual(zir_inst, unit.zir_index);
    try std.testing.expectEqual(ns_idx, unit.namespace);
}
