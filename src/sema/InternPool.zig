//! Runtime-only port of the compiler's `src/InternPool.zig`. Drops
//! incremental-compilation machinery (`*_deps`, `TrackedInst`, `AnalUnit`,
//! thread sharding, `memoized_call`) and keeps the canonical-storage core.
//!
//! Reference: src/InternPool.zig in the Zig compiler tree.
//! The well-known `Index` set, `SimpleType`/`SimpleValue` shape, and
//! `Item.Tag` naming mirror the compiler so the port reads against it
//! directly. Compiler-internal markers (`adhoc_inferred_error_set`,
//! `generic_poison`) plus the convenience pointer/slice/vector well-knowns
//! are deliberately deferred -- they need Key variants (`ptr_type`,
//! `vector_type`, etc.) that land alongside their handlers.

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

    // Values.
    /// `undefined` (untyped)
    undef,
    /// `0` (comptime_int)
    zero,
    /// `1` (comptime_int)
    one,
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

    /// Used by Air/Sema only.
    none = std.math.maxInt(u32),

    _,

    /// Range bounds for well-known types. Anything strictly between these
    /// (inclusive) is a type whose Key shape can be looked up via `get`
    /// without further checks. Dynamic indices fall outside this range.
    pub const first_type: Index = .u0_type;
    pub const last_type: Index = .enum_literal_type;
    pub const first_value: Index = .undef;
    pub const last_value: Index = .bool_false;

    pub fn isWellKnownType(index: Index) bool {
        const raw = @intFromEnum(index);
        return raw >= @intFromEnum(first_type) and raw <= @intFromEnum(last_type);
    }

    pub fn isWellKnownValue(index: Index) bool {
        const raw = @intFromEnum(index);
        return raw >= @intFromEnum(first_value) and raw <= @intFromEnum(last_value);
    }
};

const first_dynamic_index: u32 = @intFromEnum(Index.bool_false) + 1;

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
    /// `name` typically agree.
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
    /// In REPL `bindDecls` populates it eagerly, so non-Stage-7
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
        /// True IFF this Nav is the binding for an `extern` decl.
        /// Stage 5/8 sets it; Stage 2 leaves it false.
        is_extern_decl: bool,
        /// The decl's value. Compiler shape: `.none` is the
        /// "type resolved but value not yet" sentinel -- NOT an
        /// optional. Stage 2's eager evaluator always populates it
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
/// declaration acrobatics; the storage and methods land in commit 3.
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

/// Stable handle into a file table that lands with Stage 6 (modules).
/// Defined here so `Namespace.file_scope` matches the compiler's
/// `Zcu.File.Index` type today; the actual file storage is empty
/// until the loader exists. Same shape as `src/Zcu.zig:1232`.
pub const FileIndex = enum(u32) { _ };

/// Optional `FileIndex`. The REPL session-root namespace uses `.none`
/// because there is no on-disk file backing it; Stage 6 module
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
};

/// A `comptime { ... }` top-level block. Mirrors the compiler's
/// `InternPool.ComptimeUnit` (`src/InternPool.zig` ~498). Stage 2
/// records these so `bindDecls` can register them in a namespace's
/// `comptime_decls` list; execution lands when Sema gains a
/// comptime evaluator (Stage 7).
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
/// the compiler's struct lives here too, even when Stage 2 leaves
/// it at a sentinel default -- the vestigial fields make Stage 4 /
/// 6 / 8 additive rather than schema-changing.
pub const Namespace = struct {
    parent: OptionalNamespaceIndex,
    /// The file backing this namespace. `.none` for the session-root
    /// namespace; Stage 6's module loader populates real file
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
    /// namespace. `.none` for the session root; Stage 4 aggregates
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

/// Mirrors compiler `InternPool.SimpleType`. Each variant's integer value is
/// the corresponding `Index`, so converting between the two is identity.
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
};

/// Mirrors compiler `InternPool.SimpleValue`. Same identity trick as `SimpleType`.
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
    /// exactly that shape. Mirrors the compiler's `Key.undef`.
    undef: Index,
    /// A value whose runtime type is `type` and whose payload is the
    /// interned type itself.
    type_value: Index,
    /// A pointer type (`*T`, `*const T`, `[*]T`, `[]T`, etc.). Mirrors
    /// the compiler's `Key.PtrType` -- the same shape but a subset of
    /// the flag set; we start with what Stage 2's alloc/store/load
    /// needs and widen with each stage.
    ptr_type: PtrType,
    /// A pointer value. Mirrors the compiler's `Key.Ptr`. `base_addr`
    /// today only has `.comptime_alloc` -- enough for REPL session
    /// allocations; `.nav` / `.uav` / `.int` etc. land alongside their
    /// dependent stages.
    ptr: Ptr,
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
    /// `generic_owner` / `comptime_args` / source-range fields
    /// land if/when incremental compilation does -- same
    /// deferred-vestigial story as `Nav.analysis.zir_index`.
    func: Func,

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

    /// Pointer type. Stage 2's minimal subset of the compiler's
    /// `Key.PtrType` -- shape matches but the flag field carries only
    /// what `alloc` / `store` / `load` need (size, is_const, address
    /// space). Sentinel and alignment will be wired alongside Stage 4
    /// aggregates.
    pub const PtrType = struct {
        child: Index,
        sentinel: Index = .none,
        flags: Flags = .{},

        pub const Flags = packed struct(u32) {
            size: Size = .one,
            is_const: bool = false,
            is_volatile: bool = false,
            is_allowzero: bool = false,
            address_space: AddressSpace = .generic,
            _reserved: u22 = 0,
        };

        // Reuse stdlib's enums verbatim -- same shape as the compiler's
        // `Key.PtrType.{Size,AddressSpace}` aliases at
        // `src/InternPool.zig:2093-2094`. Saves duplicating the variant
        // lists and stays in sync if stdlib adds CPU/GPU address spaces.
        pub const Size = std.lang.Type.Pointer.Size;
        pub const AddressSpace = std.lang.AddressSpace;
    };

    /// Pointer value. `ty` is the pointer's type (always a `ptr_type`
    /// Index). `base_addr` identifies the storage region; `byte_offset`
    /// is the offset within that region. Stage 2 ships
    /// `.comptime_alloc` only; later stages add `.nav` (declarations),
    /// `.uav` (anonymous addressable values), `.int` (`@ptrFromInt`),
    /// `.eu_payload`, `.opt_payload`, `.comptime_field`, etc. as their
    /// dependent ZIR tags land. Variant naming mirrors the compiler's
    /// `Key.Ptr.BaseAddr` (`src/InternPool.zig`).
    pub const Ptr = struct {
        ty: Index,
        base_addr: BaseAddr,
        byte_offset: u64,

        pub const BaseAddr = union(enum) {
            comptime_alloc: ComptimeAllocIndex,
        };
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
    };

    /// An error value. `ty` is always an `error_set_type` Index --
    /// the most precise type the value inhabits, typically a
    /// singleton set created at the `error.X` source site. `name`
    /// is the interned identifier and is what global error-id
    /// comparison ultimately keys on (matching the compiler's global
    /// error table contract: `error.Foo` from two different sets
    /// share the same name interning).
    pub const Error = struct {
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
        /// bookkeeping; we use the bare `Zir.Inst.Index` until
        /// incremental compilation lands -- same deferred-vestigial
        /// story as `Nav.analysis.zir_index`.
        zir_body_inst: std.zig.Zir.Inst.Index,
        /// `.none` unless this is a generic-fn instantiation. When
        /// set, points at the `func_decl` this instance was spawned
        /// from. Mirrors `Key.Func.generic_owner`.
        generic_owner: Index = .none,
        /// Empty unless this is a generic-fn instantiation. Each
        /// element is the comptime-known value bound to the
        /// corresponding parameter of `generic_owner`'s type
        /// (`.none` for runtime-known elements). Mirrors
        /// `Key.Func.comptime_args`. Stage 7 generics populate this.
        comptime_args: []const Index = &.{},
    };

    /// Stable hash for dedup. `pool` is reserved for future Key variants
    /// (e.g. `struct_type`) whose canonical form requires pool lookup;
    /// today's variants ignore it. Storage variants of `int` are
    /// normalised to `BigIntConst` before hashing so that
    /// `.{ .u64 = 5 }` and `.{ .big_int = +5 }` hash identically -- the
    /// read-side compresses limbs back to inline storage so the pool's
    /// canonical form is stable, but a freshly constructed Key may
    /// arrive in any variant. Same canonicalisation in `eql`.
    pub fn hash64(key: Key, pool: *const InternPool) u64 {
        _ = pool;
        var hasher = std.hash.Wyhash.init(0);
        const Tag = @typeInfo(Key).@"union".tag_type.?;
        std.hash.autoHash(&hasher, @as(Tag, key));
        switch (key) {
            .simple_type => |s| std.hash.autoHash(&hasher, s),
            .simple_value => |s| std.hash.autoHash(&hasher, s),
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
            .type_value => |t| std.hash.autoHash(&hasher, t),
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
                }
            },
            .error_set_type => |es| {
                std.hash.autoHash(&hasher, @as(u32, @intCast(es.names.len)));
                for (es.names) |name| std.hash.autoHash(&hasher, name);
            },
            .err => |e| {
                std.hash.autoHash(&hasher, e.ty);
                std.hash.autoHash(&hasher, e.name);
            },
            .error_union_type => |eu| {
                std.hash.autoHash(&hasher, eu.error_set_type);
                std.hash.autoHash(&hasher, eu.payload_type);
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
                std.hash.autoHash(&hasher, f.ty);
                std.hash.autoHash(&hasher, f.uncoerced_ty);
                std.hash.autoHash(&hasher, f.zir_body_inst);
                std.hash.autoHash(&hasher, f.generic_owner);
                for (f.comptime_args) |arg| std.hash.autoHash(&hasher, arg);
            },
        }
        return hasher.final();
    }

    /// Structural equality, paired with `hash64`. See `hash64` for the
    /// `int` canonicalisation rationale.
    pub fn eql(a: Key, b: Key, pool: *const InternPool) bool {
        _ = pool;
        const Tag = @typeInfo(Key).@"union".tag_type.?;
        if (@as(Tag, a) != @as(Tag, b)) return false;
        return switch (a) {
            .simple_type => |x| x == b.simple_type,
            .simple_value => |x| x == b.simple_value,
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
                // Mirrors the compiler's `Key.eql` branch.
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
            .type_value => |x| x == b.type_value,
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
                };
            },
            .error_set_type => |x| blk: {
                const y = b.error_set_type;
                if (x.names.len != y.names.len) break :blk false;
                for (x.names, y.names) |xn, yn| if (xn != yn) break :blk false;
                break :blk true;
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
                if (x.param_types.len != y.param_types.len) break :blk false;
                for (x.param_types, y.param_types) |xp, yp| if (xp != yp) break :blk false;
                break :blk true;
            },
            .func => |x| blk: {
                const y = b.func;
                if (x.ty != y.ty) break :blk false;
                if (x.uncoerced_ty != y.uncoerced_ty) break :blk false;
                if (x.zir_body_inst != y.zir_body_inst) break :blk false;
                if (x.generic_owner != y.generic_owner) break :blk false;
                if (x.comptime_args.len != y.comptime_args.len) break :blk false;
                for (x.comptime_args, y.comptime_args) |xa, ya| if (xa != ya) break :blk false;
                break :blk true;
            },
        };
    }
};

/// Tagged storage. `data` interpretation depends on `tag`. Naming mirrors
/// the compiler's `Item.Tag` to keep ports legible.
const Item = struct {
    tag: Tag,
    data: u32,

    const Tag = enum(u8) {
        simple_type, // data = SimpleType ordinal == Index of the corresponding type
        simple_value, // data = SimpleValue ordinal == Index of the corresponding value
        type_int_unsigned, // data = bits
        type_int_signed, // data = bits
        type_anyframe, // data = Index of the frame's child type (or .none for untyped anyframe)
        // Type-specialised int storage. The tag implies the type; the value
        // is inline in `data`. Mirrors the compiler's compact encoding.
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
        // actual limbs trailing directly after. Mirrors the compiler's
        // `int_positive` / `int_negative` encoding (packed header at the
        // head of a Limb-aligned arena, limbs trailing).
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
        type_value, // data = Index of the interned type
        // Pointer type. data = extra index of PtrTypeRepr (3 u32 slots:
        // child, sentinel, flags). Mirrors the compiler's
        // `Item.Tag.type_pointer`.
        type_pointer,
        // Pointer value with `BaseAddr.comptime_alloc`. data = extra
        // index of PtrComptimeAllocRepr (4 u32 slots: ty,
        // comptime_alloc index, byte_offset_lo, byte_offset_hi).
        // Mirrors the compiler's `Item.Tag.ptr_comptime_alloc`.
        ptr_comptime_alloc,
        // Error set type. data = extra index of `[names_len, name0,
        // name1, ...]` -- one u32 length followed by `names_len`
        // interned-string handles. Mirrors the compiler's
        // `Item.Tag.type_error_set`.
        type_error_set,
        // Error value. data = extra index of ErrRepr (2 u32 slots:
        // ty, name). Mirrors the compiler's `Item.Tag.error_set_error`.
        error_set_error,
        // Error-union type (`E!T`). data = extra index of
        // ErrorUnionTypeRepr (2 u32 slots: error_set, payload).
        // Mirrors `Item.Tag.type_error_union`.
        type_error_union,
        // Error-union value carrying an error. data = extra index of
        // ErrorUnionErrRepr (2 u32 slots: ty, err_name).
        error_union_error,
        // Error-union value carrying a payload. data = extra index of
        // ErrorUnionPayloadRepr (2 u32 slots: ty, payload).
        error_union_payload,
        // Function type. data = extra index of FuncTypeRepr (3 u32
        // slots) plus trailing comptime_bits / noalias_bits (when
        // present per flags) and `param_types[N]`. Mirrors the
        // compiler's `Item.Tag.type_function`.
        type_function,
        // Function value at a declaration site. data = extra index
        // of FuncDeclRepr (2 u32 slots: ty, zir_body_inst). Mirrors
        // the compiler's `Item.Tag.func_decl` minus the
        // incremental-compilation extras. Today this is the only
        // func tag the REPL emits.
        func_decl,
        // Function value from a generic-fn instantiation. data =
        // extra index of FuncInstanceRepr (3 u32 slots: ty,
        // generic_owner, comptime_args_len) plus trailing
        // `comptime_args[comptime_args_len]`. Lands with Stage 7
        // generics; the tag slot exists today so the dispatcher,
        // hash, and eql paths cover the variant without later
        // refactoring.
        func_instance,
        // Function value coerced to a different fn type. data =
        // extra index of FuncCoercedRepr (2 u32 slots: ty,
        // inner_func). The inner index points at another
        // func_decl / func_instance; `uncoerced_ty` derives from
        // the inner's `ty`. Lands when fn coercion does -- shape
        // ready today.
        func_coerced,
    };
};

/// Extra-arena payload for `Item.Tag.int_small`. Mirrors the compiler's
/// `IntSmall`: a typed value that fits in `u32` but whose type isn't
/// covered by the type-specialised inline tags. Stored as two
/// consecutive `u32`s in `extra`: `ty` then `value`. Values that
/// exceed `u32` skip this encoding and go straight to
/// `int_positive` / `int_negative`.
const IntSmall = extern struct {
    ty: u32,
    value: u32,
};

/// Extra-arena payload for `Item.Tag.type_pointer`. Three u32 slots:
/// child, sentinel, and the bit-packed `Key.PtrType.Flags`. Mirrors
/// the compiler's `Tag.TypePointer` storage shape (smaller because we
/// haven't ported `packed_offset` yet -- adds when Stage 4's
/// host-int-backed slice machinery needs it).
const PtrTypeRepr = extern struct {
    child: u32,
    sentinel: u32,
    flags: u32,
};

/// Extra-arena payload for `Item.Tag.ptr_comptime_alloc`. Four u32
/// slots: ty, comptime-alloc index, and the 64-bit byte_offset split
/// into lo/hi u32s. Mirrors the compiler's `Tag.PtrComptimeAlloc` --
/// allocations born in Sema rather than backed by a declaration.
/// Extra-arena header for `Item.Tag.type_function`. Three u32
/// slots followed by optional `comptime_bits` / `noalias_bits`
/// and `param_types[params_len]`. The compiler's
/// `Tag.TypeFunction` shape; storage discipline matches.
const FuncTypeRepr = extern struct {
    params_len: u32,
    return_type: u32,
    flags: u32,

    /// Stage-3-minimum CC packing: `cc_tag` only. The compiler
    /// uses `PackedCallingConvention(u18)` which also carries
    /// `incoming_stack_alignment` + per-variant `extra`. We
    /// reconstruct the full `std.lang.CallingConvention` on unpack
    /// with default-initialised payloads since REPL paths today
    /// only need `.auto` / `.c`; FFI (Stage 5/8) widens to the
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

/// Extra-arena payload for `Item.Tag.func_decl`. Two u32 slots:
/// `ty` and the ZIR func-instruction index.
const FuncDeclRepr = extern struct {
    ty: u32,
    zir_body_inst: u32,
};

/// Extra-arena header for `Item.Tag.func_instance`. Three u32
/// slots followed by `comptime_args[comptime_args_len]`. The
/// generic_owner index resolves through `indexToKey` to its
/// `func_decl` and contributes the body inst.
const FuncInstanceRepr = extern struct {
    ty: u32,
    generic_owner: u32,
    comptime_args_len: u32,
};

/// Extra-arena payload for `Item.Tag.func_coerced`. Two u32
/// slots: the destination fn type and the inner func index whose
/// `uncoerced_ty` becomes this Key.Func's `uncoerced_ty`.
const FuncCoercedRepr = extern struct {
    ty: u32,
    inner_func: u32,
};

const PtrComptimeAllocRepr = extern struct {
    ty: u32,
    alloc_index: u32,
    byte_offset_lo: u32,
    byte_offset_hi: u32,
};

/// Extra-arena payload for `Item.Tag.error_set_error`. Two u32 slots: the
/// error-set type Index and the interned error-name handle. Mirrors
/// the compiler's `Tag.Err` shape.
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
/// trailing directly after. Sign is in the Item tag, not here. Matches the
/// compiler's packed `Int`.
const IntBigHeader = packed struct {
    ty: u32,
    limbs_len: u32,

    /// Number of Limb slots this header occupies (1 on 64-bit, 2 on 32-bit).
    const limbs_items_len = @divExact(@sizeOf(IntBigHeader), @sizeOf(std.math.big.Limb));
};

/// Extra-arena payload for `Item.Tag.float_f64`. Mirrors the compiler's
/// `Float64`: the f64 bit-pattern split into two u32 pieces so it fits
/// in the u32-typed `extra` array.
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
/// `Item.Tag.float_c_longdouble_f80`. Mirrors the compiler's `Float80`:
/// the f80 bit-pattern split across two u32 pieces and one u16 piece
/// (zero-padded to a u32 slot).
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
/// `Item.Tag.float_comptime_float`. Mirrors the compiler's `Float128`:
/// the f128 bit-pattern split into four u32 pieces.
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
/// Mirrors the compiler's `string_bytes` (`src/InternPool.zig`). Byte
/// `0` is the lone sentinel for `NullTerminatedString.empty`, so
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
/// entries stored as bare `Index`es. Mirrors the role of the compiler's
/// `KeyAdapter`.
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
/// Mirrors the compiler's `getOrPutString` (`src/InternPool.zig`
/// ~11255) collapsed to single-threaded shape: the compiler's
/// implementation appends bytes, then dedups via a sharded map; we do
/// the same with one map. The dedup-hit rollback is identical -- the
/// trailing append simply leaves dead bytes that nothing references.
///
/// Asserts there are no embedded `0` bytes. Stage 2 callers (decl
/// names, type names) cannot legally contain them. When a `Key`
/// variant eventually needs embedded-null content (e.g. error names),
/// add an `EmbeddedNulls` policy parameter mirroring the compiler's
/// `getOrPutString` signature.
pub fn getOrPutString(
    pool: *InternPool,
    gpa: Allocator,
    bytes: []const u8,
) Allocator.Error!NullTerminatedString {
    assert(@intFromPtr(pool) != 0);
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
    assert(@intFromPtr(pool) != 0);

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
/// after evaluating the decl's value body. Mirrors the compiler's
/// `createNav` for the non-extern path (`src/InternPool.zig` ~11041)
/// minus the multi-threaded acquire/release plumbing.
pub fn createNav(
    pool: *InternPool,
    gpa: Allocator,
    name: NullTerminatedString,
    fqn: NullTerminatedString,
) Allocator.Error!Nav.Index {
    assert(@intFromPtr(pool) != 0);

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
    assert(@intFromPtr(pool) != 0);
    const raw: u32 = @intFromEnum(index);
    assert(raw < pool.navs.items.len);
    return pool.navs.items[raw];
}

/// Mutable handle into the Nav storage. Used by `bindDecls` to set
/// `resolved` after evaluating the value body. The returned pointer
/// is valid until the next `createNav` that triggers a resize --
/// keep the dereference local.
pub fn navPtr(pool: *InternPool, index: Nav.Index) *Nav {
    assert(@intFromPtr(pool) != 0);
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
    assert(@intFromPtr(pool) != 0);

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
    assert(@intFromPtr(pool) != 0);
    const raw: u32 = @intFromEnum(index);
    assert(raw < pool.namespaces.items.len);
    return &pool.namespaces.items[raw];
}

/// Record a `comptime { ... }` block. Returns its stable `Id` so
/// the namespace's `comptime_decls` list can reference it. Execution
/// is deferred to Stage 7 (`@comptime` evaluator).
pub fn createComptimeUnit(
    pool: *InternPool,
    gpa: Allocator,
    namespace: NamespaceIndex,
    zir_index: std.zig.Zir.Inst.Index,
) Allocator.Error!ComptimeUnit.Id {
    assert(@intFromPtr(pool) != 0);

    const new_index_raw: u32 = @intCast(pool.comptime_units.items.len);
    try pool.comptime_units.append(gpa, .{
        .zir_index = zir_index,
        .namespace = namespace,
    });
    assert(pool.comptime_units.items.len == new_index_raw + 1);
    return @enumFromInt(new_index_raw);
}

/// Read a recorded `ComptimeUnit` by id.
pub fn getComptimeUnit(pool: *const InternPool, id: ComptimeUnit.Id) ComptimeUnit {
    assert(@intFromPtr(pool) != 0);
    const raw: u32 = @intFromEnum(id);
    assert(raw < pool.comptime_units.items.len);
    return pool.comptime_units.items[raw];
}

/// Comptime well-known table mirroring the compiler's `static_keys` array
/// in `src/InternPool.zig`. Each entry corresponds 1:1 to an `Index`
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

    // Untyped `undefined` -- same shape as the compiler.
    .{ .undef = .undefined_type },
    .{ .int = .{ .ty = .comptime_int_type, .storage = .{ .u64 = 0 } } },
    .{ .int = .{ .ty = .comptime_int_type, .storage = .{ .u64 = 1 } } },
    .{ .int = .{ .ty = .comptime_int_type, .storage = .{ .i64 = -1 } } },
    .{ .simple_value = .void },
    .{ .simple_value = .@"unreachable" },
    .{ .simple_value = .null },
    .{ .simple_value = .true },
    .{ .simple_value = .false },
};

fn populateWellKnown(pool: *InternPool) Allocator.Error!void {
    assert(pool.items.len == 0);
    assert(pool.map.count() == 0);

    inline for (static_keys, 0..) |key, expected_position| {
        const index = try pool.get(key);
        // Identity of static_keys position to Index enum value is
        // load-bearing: SimpleType / SimpleValue variant values are pinned
        // via `@intFromEnum(Index.X)`, and Sema's `wellKnownRefToValue`
        // assumes positions 0..44 match `Zir.Inst.Ref`'s well-known set.
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
        .int_type => |it| appendIntType(pool, it.signedness, it.bits),
        .anyframe_type => |child| appendAnyframeType(pool, child),
        .type_value => |t| pool.items.appendAssumeCapacity(.{
            .tag = .type_value,
            .data = @intFromEnum(t),
        }),
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
        .error_set_type => |es| try emitErrorSetType(pool, es),
        .err => |e| try emitErr(pool, e),
        .error_union_type => |eu| try emitErrorUnionType(pool, eu),
        .error_union => |eu| try emitErrorUnion(pool, eu),
        .func_type => |ft| try emitFuncType(pool, ft),
        .func => |f| try emitFunc(pool, f),
    }

    assert(pool.items.len == gop.index + 1);
    return @enumFromInt(@as(u32, @intCast(gop.index)));
}

/// Look up the `Key` for an `Index`. Mirrors the compiler's
/// `indexToKey` (`src/InternPool.zig`).
pub fn indexToKey(pool: *const InternPool, index: Index) Key {
    assert(index != .none);
    const i = @intFromEnum(index);
    assert(i < pool.items.len);
    const item = pool.items.get(i);
    return switch (item.tag) {
        .simple_type => .{ .simple_type = @enumFromInt(item.data) },
        .simple_value => .{ .simple_value = @enumFromInt(item.data) },
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
            .storage = .{ .f64 = floatFromExtra(pool, Float64, item.data).get() },
        } },
        .float_f80 => .{ .float = .{
            .ty = .f80_type,
            .storage = .{ .f80 = floatFromExtra(pool, Float80, item.data).get() },
        } },
        .float_f128 => .{ .float = .{
            .ty = .f128_type,
            .storage = .{ .f128 = floatFromExtra(pool, Float128, item.data).get() },
        } },
        .float_c_longdouble_f80 => .{ .float = .{
            .ty = .c_longdouble_type,
            .storage = .{ .f80 = floatFromExtra(pool, Float80, item.data).get() },
        } },
        .float_c_longdouble_f128 => .{ .float = .{
            .ty = .c_longdouble_type,
            .storage = .{ .f128 = floatFromExtra(pool, Float128, item.data).get() },
        } },
        .float_comptime_float => .{ .float = .{
            .ty = .comptime_float_type,
            .storage = .{ .f128 = floatFromExtra(pool, Float128, item.data).get() },
        } },
        .undef => .{ .undef = @enumFromInt(item.data) },
        .type_value => .{ .type_value = @enumFromInt(item.data) },
        .type_pointer => ptrTypeFromExtra(pool, item.data),
        .ptr_comptime_alloc => ptrComptimeAllocFromExtra(pool, item.data),
        .type_error_set => errorSetTypeFromExtra(pool, item.data),
        .error_set_error => errFromExtra(pool, item.data),
        .type_error_union => errorUnionTypeFromExtra(pool, item.data),
        .error_union_error => errorUnionErrFromExtra(pool, item.data),
        .error_union_payload => errorUnionPayloadFromExtra(pool, item.data),
        .type_function => funcTypeFromExtra(pool, item.data),
        .func_decl => funcDeclFromExtra(pool, item.data),
        .func_instance => funcInstanceFromExtra(pool, item.data),
        .func_coerced => funcCoercedFromExtra(pool, item.data),
    };
}

fn ptrTypeFromExtra(pool: *const InternPool, extra_index: u32) Key {
    const fields = comptime @divExact(@sizeOf(PtrTypeRepr), @sizeOf(u32));
    assert(extra_index + fields <= pool.extra.items.len);
    const slice = pool.extra.items[extra_index..][0..fields];
    const repr: PtrTypeRepr = .{ .child = slice[0], .sentinel = slice[1], .flags = slice[2] };
    return .{ .ptr_type = .{
        .child = @enumFromInt(repr.child),
        .sentinel = @enumFromInt(repr.sentinel),
        .flags = @bitCast(repr.flags),
    } };
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
    const fields = comptime @divExact(@sizeOf(ErrRepr), @sizeOf(u32));
    assert(extra_index + fields <= pool.extra.items.len);
    const slice = pool.extra.items[extra_index..][0..fields];
    return .{ .err = .{
        .ty = @enumFromInt(slice[0]),
        .name = @enumFromInt(slice[1]),
    } };
}

fn errorUnionTypeFromExtra(pool: *const InternPool, extra_index: u32) Key {
    const fields = comptime @divExact(@sizeOf(ErrorUnionTypeRepr), @sizeOf(u32));
    assert(extra_index + fields <= pool.extra.items.len);
    const slice = pool.extra.items[extra_index..][0..fields];
    return .{ .error_union_type = .{
        .error_set_type = @enumFromInt(slice[0]),
        .payload_type = @enumFromInt(slice[1]),
    } };
}

fn errorUnionErrFromExtra(pool: *const InternPool, extra_index: u32) Key {
    const fields = comptime @divExact(@sizeOf(ErrorUnionErrRepr), @sizeOf(u32));
    assert(extra_index + fields <= pool.extra.items.len);
    const slice = pool.extra.items[extra_index..][0..fields];
    return .{ .error_union = .{
        .ty = @enumFromInt(slice[0]),
        .val = .{ .err_name = @enumFromInt(slice[1]) },
    } };
}

fn errorUnionPayloadFromExtra(pool: *const InternPool, extra_index: u32) Key {
    const fields = comptime @divExact(@sizeOf(ErrorUnionPayloadRepr), @sizeOf(u32));
    assert(extra_index + fields <= pool.extra.items.len);
    const slice = pool.extra.items[extra_index..][0..fields];
    return .{ .error_union = .{
        .ty = @enumFromInt(slice[0]),
        .val = .{ .payload = @enumFromInt(slice[1]) },
    } };
}

fn ptrComptimeAllocFromExtra(pool: *const InternPool, extra_index: u32) Key {
    const fields = comptime @divExact(@sizeOf(PtrComptimeAllocRepr), @sizeOf(u32));
    assert(extra_index + fields <= pool.extra.items.len);
    const slice = pool.extra.items[extra_index..][0..fields];
    const byte_offset = (@as(u64, slice[3]) << 32) | @as(u64, slice[2]);
    return .{ .ptr = .{
        .ty = @enumFromInt(slice[0]),
        .base_addr = .{ .comptime_alloc = @enumFromInt(slice[1]) },
        .byte_offset = byte_offset,
    } };
}

/// Reconstruct a packed `Float64` / `Float80` / `Float128` from `extra`.
/// The struct is stored as `@sizeOf(T) / 4` consecutive u32 slots.
fn floatFromExtra(pool: *const InternPool, comptime T: type, extra_index: u32) T {
    const pieces_len = comptime @divExact(@sizeOf(T), @sizeOf(u32));
    assert(extra_index + pieces_len <= pool.extra.items.len);
    const pieces: [pieces_len]u32 = pool.extra.items[extra_index..][0..pieces_len].*;
    return @bitCast(pieces);
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

/// Reconstruct an `int_positive` / `int_negative` Key. Mirrors the
/// compiler's `indexToKeyBigInt` (`src/InternPool.zig`): on read, a
/// big-int whose value fits in `u64` (or `i64` when negative) is
/// re-surfaced as the matching inline storage variant so the read-side
/// shape stays symmetric with the intern-side compression. Required for
/// future dedup: hashing an inserted Key as `.u64=x` must agree with
/// hashing the reconstructed Key.
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

/// Emit the `Item` (and any extra / limbs) for a `Key.int`. Mirrors the
/// `.int =>` arm of the compiler's `intern` (`src/InternPool.zig`): one
/// labelled-block switch on `ty` for the type-specialised inline tags,
/// then a fallthrough switch on `storage` for `int_small` or
/// `int_positive` / `int_negative`. Callers must have ensured one item
/// of capacity -- only reachable from `get`'s miss path.
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

/// Emit the `Item` (and any extra) for a `Key.float`. Mirrors the
/// `.float =>` arm of the compiler's `intern` (`src/InternPool.zig`):
/// outer switch on `float.ty`; the c_longdouble arm picks a tag based
/// on storage variant (f80 -> its own tag, otherwise promoted to f128);
/// comptime_float always stores as f128. Callers must have ensured one
/// item of capacity -- only reachable from `get`'s miss path.
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
            const extra_index = try addFloatExtra(pool, Float64.pack(float.storage.f64));
            pool.items.appendAssumeCapacity(.{ .tag = .float_f64, .data = extra_index });
        },
        .f80_type => {
            assert(float.storage == .f80);
            const extra_index = try addFloatExtra(pool, Float80.pack(float.storage.f80));
            pool.items.appendAssumeCapacity(.{ .tag = .float_f80, .data = extra_index });
        },
        .f128_type => {
            assert(float.storage == .f128);
            const extra_index = try addFloatExtra(pool, Float128.pack(float.storage.f128));
            pool.items.appendAssumeCapacity(.{ .tag = .float_f128, .data = extra_index });
        },
        .c_longdouble_type => switch (float.storage) {
            .f80 => |v| {
                const extra_index = try addFloatExtra(pool, Float80.pack(v));
                pool.items.appendAssumeCapacity(.{
                    .tag = .float_c_longdouble_f80,
                    .data = extra_index,
                });
            },
            inline .f16, .f32, .f64, .f128 => |v| {
                const extra_index = try addFloatExtra(pool, Float128.pack(@floatCast(v)));
                pool.items.appendAssumeCapacity(.{
                    .tag = .float_c_longdouble_f128,
                    .data = extra_index,
                });
            },
        },
        .comptime_float_type => {
            assert(float.storage == .f128);
            const extra_index = try addFloatExtra(pool, Float128.pack(float.storage.f128));
            pool.items.appendAssumeCapacity(.{
                .tag = .float_comptime_float,
                .data = extra_index,
            });
        },
        else => unreachable,
    }
}

/// Append a packed Float64/Float80/Float128 to `extra` and return its
/// starting u32 index. The struct is laid out as `@sizeOf(T) / 4`
/// consecutive u32 slots.
fn addFloatExtra(pool: *InternPool, value: anytype) Allocator.Error!u32 {
    const T = @TypeOf(value);
    const pieces_len = comptime @divExact(@sizeOf(T), @sizeOf(u32));
    const pieces: [pieces_len]u32 = @bitCast(value);
    const extra_index: u32 = @intCast(pool.extra.items.len);
    try pool.extra.appendSlice(pool.gpa, &pieces);
    return extra_index;
}

/// Intern a float value with any storage form.
pub fn internFloat(pool: *InternPool, float: Key.Float) Allocator.Error!Index {
    return pool.get(.{ .float = float });
}

/// Emit a `type_pointer` Item. Three u32 slots in extra:
/// child Index, sentinel Index, packed-flags as u32.
fn emitPtrType(pool: *InternPool, pt: Key.PtrType) Allocator.Error!void {
    assert(pt.child != .none);
    const extra_index: u32 = @intCast(pool.extra.items.len);
    try pool.extra.appendSlice(pool.gpa, &.{
        @intFromEnum(pt.child),
        @intFromEnum(pt.sentinel),
        @as(u32, @bitCast(pt.flags)),
    });
    pool.items.appendAssumeCapacity(.{ .tag = .type_pointer, .data = extra_index });
}

/// Emit a `ptr_alloc` Item for a `Key.ptr` whose base address is an
/// `comptime_alloc`. Four u32 slots: ty, alloc_index, byte_offset
/// (lo/hi).
fn emitPtr(pool: *InternPool, p: Key.Ptr) Allocator.Error!void {
    assert(p.ty != .none);
    switch (p.base_addr) {
        .comptime_alloc => |idx| {
            const extra_index: u32 = @intCast(pool.extra.items.len);
            try pool.extra.appendSlice(pool.gpa, &.{
                @intFromEnum(p.ty),
                @intFromEnum(idx),
                @as(u32, @truncate(p.byte_offset)),
                @as(u32, @truncate(p.byte_offset >> 32)),
            });
            pool.items.appendAssumeCapacity(.{ .tag = .ptr_comptime_alloc, .data = extra_index });
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

/// Emit an `err` Item. Two u32 slots: `ty`, `name`.
fn emitErr(pool: *InternPool, e: Key.Error) Allocator.Error!void {
    assert(e.ty != .none);

    const extra_index: u32 = @intCast(pool.extra.items.len);
    try pool.extra.appendSlice(pool.gpa, &.{
        @intFromEnum(e.ty),
        @intFromEnum(e.name),
    });
    pool.items.appendAssumeCapacity(.{ .tag = .error_set_error, .data = extra_index });
}

/// Emit a `type_error_union` Item. Two u32 slots: `error_set`, `payload`.
fn emitErrorUnionType(pool: *InternPool, eu: Key.ErrorUnionType) Allocator.Error!void {
    assert(eu.error_set_type != .none);
    assert(eu.payload_type != .none);

    const extra_index: u32 = @intCast(pool.extra.items.len);
    try pool.extra.appendSlice(pool.gpa, &.{
        @intFromEnum(eu.error_set_type),
        @intFromEnum(eu.payload_type),
    });
    pool.items.appendAssumeCapacity(.{ .tag = .type_error_union, .data = extra_index });
}

/// Emit an error-union value. Two tags discriminate the `.err` vs
/// `.payload` variants; each carries (ty, payload_u32).
fn emitErrorUnion(pool: *InternPool, eu: Key.ErrorUnion) Allocator.Error!void {
    assert(eu.ty != .none);

    const extra_index: u32 = @intCast(pool.extra.items.len);
    switch (eu.val) {
        .err_name => |name| {
            try pool.extra.appendSlice(pool.gpa, &.{
                @intFromEnum(eu.ty),
                @intFromEnum(name),
            });
            pool.items.appendAssumeCapacity(.{ .tag = .error_union_error, .data = extra_index });
        },
        .payload => |idx| {
            try pool.extra.appendSlice(pool.gpa, &.{
                @intFromEnum(eu.ty),
                @intFromEnum(idx),
            });
            pool.items.appendAssumeCapacity(.{ .tag = .error_union_payload, .data = extra_index });
        },
    }
}

/// Intern a pointer type.
pub fn internPtrType(pool: *InternPool, pt: Key.PtrType) Allocator.Error!Index {
    return pool.get(.{ .ptr_type = pt });
}

/// Intern a pointer value.
pub fn internPtr(pool: *InternPool, p: Key.Ptr) Allocator.Error!Index {
    return pool.get(.{ .ptr = p });
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
    assert(@intFromPtr(pool) != 0);

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

/// Intern an error value.
pub fn internErr(pool: *InternPool, e: Key.Error) Allocator.Error!Index {
    return pool.get(.{ .err = e });
}

/// Intern an error-union type (`E!T`).
pub fn internErrorUnionType(pool: *InternPool, eu: Key.ErrorUnionType) Allocator.Error!Index {
    return pool.get(.{ .error_union_type = eu });
}

/// Intern an error-union value.
pub fn internErrorUnion(pool: *InternPool, eu: Key.ErrorUnion) Allocator.Error!Index {
    return pool.get(.{ .error_union = eu });
}

/// Intern a function type.
pub fn internFuncType(pool: *InternPool, ft: Key.FuncType) Allocator.Error!Index {
    return pool.get(.{ .func_type = ft });
}

/// Intern a function value.
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
/// shape -- mirrors the compiler's three-Item-tag layout so
/// Stage 7 generics and the fn-coercion follow-up land as pure
/// emit additions without disturbing existing call sites.
fn emitFunc(pool: *InternPool, f: Key.Func) Allocator.Error!void {
    assert(f.ty != .none);
    assert(f.uncoerced_ty != .none);

    const extra_index: u32 = @intCast(pool.extra.items.len);
    if (f.generic_owner != .none) {
        try pool.extra.ensureUnusedCapacity(pool.gpa, 3 + f.comptime_args.len);
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
        // through indexToKey to recover uncoerced_ty and zir_body_inst.
        // Stage 3 has no fn coercion yet, so this branch is reachable
        // only via direct internFunc calls -- the shape is here so the
        // coercion handler can land without restructuring storage.
        const inner = try pool.internFunc(.{
            .ty = f.uncoerced_ty,
            .uncoerced_ty = f.uncoerced_ty,
            .zir_body_inst = f.zir_body_inst,
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
        @intFromEnum(f.ty),
        @intFromEnum(f.zir_body_inst),
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

    // Stage-3 simplification: reconstruct the CC variant with a
    // default-initialised payload (incoming_stack_alignment = null
    // for variants that carry one). Stage 5/8 widens to full
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
    assert(extra_index + 2 <= pool.extra.items.len);
    const ty: Index = @enumFromInt(pool.extra.items[extra_index]);
    return .{ .func = .{
        .ty = ty,
        .uncoerced_ty = ty,
        .zir_body_inst = @enumFromInt(pool.extra.items[extra_index + 1]),
    } };
}

fn funcInstanceFromExtra(pool: *const InternPool, extra_index: u32) Key {
    assert(extra_index + 3 <= pool.extra.items.len);
    const ty: Index = @enumFromInt(pool.extra.items[extra_index]);
    const generic_owner: Index = @enumFromInt(pool.extra.items[extra_index + 1]);
    const args_len = pool.extra.items[extra_index + 2];
    assert(extra_index + 3 + args_len <= pool.extra.items.len);
    const args_slots = pool.extra.items[extra_index + 3 ..][0..args_len];
    const comptime_args: []const Index = @ptrCast(args_slots);

    // Body inst comes from the generic owner's func_decl.
    const owner_key = pool.indexToKey(generic_owner).func;
    return .{ .func = .{
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
        .ty = ty,
        .uncoerced_ty = inner_key.uncoerced_ty,
        .zir_body_inst = inner_key.zir_body_inst,
        .generic_owner = inner_key.generic_owner,
        .comptime_args = inner_key.comptime_args,
    } };
}

/// Reconstruct a `std.lang.CallingConvention` from its packed tag.
/// Stage-3 storage keeps only the tag; the payload is reconstructed
/// here for the safe variants AstGen emits in normal user code
/// (void-payload CCs + the common per-target `.c` aliases whose
/// payload is `CommonOptions{}`, all-default-fields). Variants
/// whose payload has required fields (`spirv_*.mode`,
/// `arm_interrupt.type`, etc.) panic loudly here so a future ZIR
/// path using one of them surfaces immediately rather than reading
/// undefined memory; lifted to full pack/unpack with Stage 5/8 FFI.
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

/// True IFF `ty` identifies a Zig float type. Mirrors the compiler's
/// `isFloatType`.
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
/// Mirrors the compiler's `isIntegerType`.
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
    assert(@intFromPtr(pool) != 0);
    if (limbs.len == 0) return false;

    const buffer = pool.big_int_limbs.allocatedSlice();
    if (buffer.len == 0) return false;

    const buf_start = @intFromPtr(buffer.ptr);
    const buf_end = buf_start + buffer.len * @sizeOf(std.math.big.Limb);
    assert(buf_end >= buf_start); // no wraparound

    const slice_start = @intFromPtr(limbs.ptr);
    return slice_start >= buf_start and slice_start < buf_end;
}

/// Append an `int_positive` / `int_negative` item. Mirrors the compiler's
/// `addInt`: packed `IntBigHeader` at the head of a `big_int_limbs` slot,
/// limbs trailing inline. Aliasing-safe: dups through gpa if the source
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

/// Intern a value whose runtime type is `type` and whose payload is the
/// interned type identified by `ty`. This is how Sema returns "the
/// expression evaluated to a type" results (e.g. `@TypeOf(x)` or the
/// type computed by `typeof_log2_int_type`).
pub fn internTypeValue(pool: *InternPool, ty: Index) Allocator.Error!Index {
    assert(ty != .none);
    return pool.get(.{ .type_value = ty });
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

    // anyframe_type with .none child (untyped anyframe) at the position
    // between noreturn_type and null_type.
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

    // f32 inline tag.
    const f32_idx = try pool.internFloat(.{ .ty = .f32_type, .storage = .{ .f32 = 1.5 } });
    const f32_round = pool.indexToKey(f32_idx).float;
    try std.testing.expectEqual(Index.f32_type, f32_round.ty);
    try std.testing.expectEqual(@as(f32, 1.5), f32_round.storage.f32);

    // f64 extra-arena tag.
    const f64_idx = try pool.internFloat(.{
        .ty = .f64_type,
        .storage = .{ .f64 = 3.141592653589793 },
    });
    const f64_round = pool.indexToKey(f64_idx).float;
    try std.testing.expectEqual(Index.f64_type, f64_round.ty);
    try std.testing.expectEqual(@as(f64, 3.141592653589793), f64_round.storage.f64);

    // f128 extra-arena tag.
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

    // Same value, same type: single Item.
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

    // NaN with a different payload bit-pattern: distinct Index.
    const other_nan: f32 = @bitCast(@as(u32, 0x7fc00002));
    const n3 = try pool.internFloat(.{ .ty = .f32_type, .storage = .{ .f32 = other_nan } });
    try std.testing.expect(n1 != n3);
}

test "undef Key variant: well-known slot and typed undef" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    // The well-known `Index.undef` slot is untyped undef, i.e. undef
    // whose carrier type is `.undefined_type` -- compiler-exact shape.
    const untyped = pool.indexToKey(.undef).undef;
    try std.testing.expectEqual(Index.undefined_type, untyped);

    // Re-interning the same untyped undef must return the well-known slot,
    // not a fresh dynamic item.
    const round = try pool.get(.{ .undef = .undefined_type });
    try std.testing.expectEqual(Index.undef, round);

    // Typed undef: undef of u32 is a distinct entry and round-trips.
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

    // Same shape dedups; differing flag bits intern separately.
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

    // Same {ty, slot, offset} dedups to the same Index.
    const p_dup = try pool.internPtr(.{
        .ty = ptr_ty,
        .base_addr = .{ .comptime_alloc = @enumFromInt(7) },
        .byte_offset = 16,
    });
    try std.testing.expectEqual(p0, p_dup);
    try std.testing.expectEqual(items_before + 1, pool.itemCount());

    // Different offset (or slot) is a distinct value.
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

    // Round-trip every name via its stored handle.
    for (handles, names) |handle, expected| {
        try std.testing.expectEqualStrings(expected, pool.stringSlice(handle));
    }

    // Re-interning yields the same handle, regardless of order.
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
    // collision is a namespace concern (the upcoming pub_decls map),
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

    // All four decl containers start empty.
    try std.testing.expectEqual(@as(usize, 0), ns.pub_decls.count());
    try std.testing.expectEqual(@as(usize, 0), ns.priv_decls.count());
    try std.testing.expectEqual(@as(usize, 0), ns.test_decls.items.len);
    try std.testing.expectEqual(@as(usize, 0), ns.comptime_decls.items.len);
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

    // Insert two distinct-name Navs.
    const gop_x = try ns.pub_decls.getOrPutContext(pool.gpa, first_x, ctx);
    try std.testing.expect(!gop_x.found_existing);
    const gop_y = try ns.pub_decls.getOrPutContext(pool.gpa, just_y, ctx);
    try std.testing.expect(!gop_y.found_existing);

    // Same-name Nav re-insertion finds the existing entry.
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
    // x lives in pub_decls (e.g. `pub const x = ...`).
    _ = try ns.pub_decls.getOrPutContext(pool.gpa, nav_x, ctx);
    // y lives in priv_decls (top-level `const y = ...` without `pub`).
    _ = try ns.priv_decls.getOrPutContext(pool.gpa, nav_y, ctx);

    // lookupNav finds both regardless of which map they live in.
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

    // Two fn types that differ only in return type.
    const params = [_]Index{};
    const ty_void = try pool.internFuncType(.{ .param_types = &params, .return_type = .void_type });
    const ty_u32 = try pool.internFuncType(.{ .param_types = &params, .return_type = .u32_type });

    const body_inst: std.zig.Zir.Inst.Index = @enumFromInt(7);
    // First intern the underlying func_decl.
    _ = try pool.internFunc(.{ .ty = ty_void, .uncoerced_ty = ty_void, .zir_body_inst = body_inst });
    // Now request a coerced view: ty = ty_u32, uncoerced_ty = ty_void.
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
