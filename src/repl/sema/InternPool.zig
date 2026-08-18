const std = @import("std");
const assert = std.debug.assert;
const Allocator = std.mem.Allocator;
const BigIntConst = std.math.big.int.Const;

const InternPool = @This();

pub const Index = enum(u32) {
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

    f16_type,
    f32_type,
    f64_type,
    f80_type,
    f128_type,

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
    adhoc_inferred_error_set_type,
    generic_poison_type,
    empty_tuple_type,

    undef,
    undef_bool,
    undef_usize,
    undef_u1,
    zero,
    zero_usize,
    zero_u1,
    zero_u8,
    one,
    one_usize,
    one_u1,
    one_u8,
    four_u8,
    negative_one,
    void_value,
    unreachable_value,
    null_value,
    bool_true,
    bool_false,
    empty_tuple,

    none = std.math.maxInt(u32),

    _,

    pub const first_type: Index = .u0_type;
    pub const last_type: Index = .empty_tuple_type;
    pub const first_value: Index = .undef;
    pub const last_value: Index = .empty_tuple;

    pub fn isWellKnownType(index: Index) bool {
        const raw = @backingInt(index);
        return raw >= @backingInt(first_type) and raw <= @backingInt(last_type);
    }

    pub fn isWellKnownValue(index: Index) bool {
        const raw = @backingInt(index);
        return raw >= @backingInt(first_value) and raw <= @backingInt(last_value);
    }

    const Adapter = struct {
        indexes: []const Index,

        pub fn eql(ctx: @This(), a: Index, b_void: void, b_map_index: usize) bool {
            _ = b_void;
            return a == ctx.indexes[b_map_index];
        }

        pub fn hash(ctx: @This(), a: Index) u32 {
            _ = ctx;
            return std.hash.int(@backingInt(a));
        }
    };
};

const first_dynamic_index: u32 = @backingInt(Index.empty_tuple) + 1;

const EmbeddedNulls = enum {
    no_embedded_nulls,
    maybe_embedded_nulls,

    fn StringType(comptime embedded_nulls: EmbeddedNulls) type {
        return switch (embedded_nulls) {
            .no_embedded_nulls => NullTerminatedString,
            .maybe_embedded_nulls => String,
        };
    }
};

/// A byte string whose length is known from context (e.g. an aggregate's array type) rather than
/// NUL-termination, so it may contain embedded NUL bytes. Shares the string table with
/// NullTerminatedString.
pub const String = enum(u32) {
    empty = 0,
    _,

    pub fn at(string: String, index: u64, pool: *const InternPool) u8 {
        const start = pool.string_starts.items[@backingInt(string)];
        return pool.string_bytes.items[@intCast(start + index)];
    }

    pub fn toSlice(string: String, len: u64, pool: *const InternPool) []const u8 {
        const start = pool.string_starts.items[@backingInt(string)];
        return pool.string_bytes.items[start..][0..@intCast(len)];
    }
};

pub const NullTerminatedString = enum(u32) {
    empty = 0,
    _,

    pub fn toOptional(string: NullTerminatedString) OptionalNullTerminatedString {
        return @fromBackingInt(@intCast(@backingInt(string)));
    }

    pub fn eqlSlice(string: NullTerminatedString, slice: []const u8, ip: *const InternPool) bool {
        return std.mem.eql(u8, ip.stringSlice(string), slice);
    }

    pub fn toUnsigned(string: NullTerminatedString, ip: *const InternPool) ?u32 {
        const slice = ip.stringSlice(string);
        if (slice.len > 1 and slice[0] == '0') return null;
        if (std.mem.indexOfScalar(u8, slice, '_')) |_| return null;
        return std.fmt.parseUnsigned(u32, slice, 10) catch null;
    }

    const Adapter = struct {
        strings: []const NullTerminatedString,

        pub fn eql(ctx: @This(), a: NullTerminatedString, b_void: void, b_map_index: usize) bool {
            _ = b_void;
            return a == ctx.strings[b_map_index];
        }

        pub fn hash(ctx: @This(), a: NullTerminatedString) u32 {
            _ = ctx;
            return std.hash.int(@backingInt(a));
        }
    };

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

pub const OptionalNullTerminatedString = enum(u32) {
    none = std.math.maxInt(u32),
    _,

    pub fn init(maybe_string: ?NullTerminatedString) OptionalNullTerminatedString {
        const string = maybe_string orelse return .none;
        return string.toOptional();
    }

    pub fn unwrap(opt: OptionalNullTerminatedString) ?NullTerminatedString {
        if (opt == .none) return null;
        return @fromBackingInt(@intCast(@backingInt(opt)));
    }
};

pub const Nav = struct {
    name: NullTerminatedString,
    fqn: NullTerminatedString,
    analysis: ?struct {
        namespace: NamespaceIndex,
        zir_index: std.zig.Zir.Inst.Index,
        wanted: bool,
    },
    resolved: ?Resolved,

    pub const Resolved = struct {
        type: InternPool.Index,
        @"align": Alignment,
        @"linksection": OptionalNullTerminatedString,
        @"addrspace": std.lang.AddressSpace,
        @"const": bool,
        @"threadlocal": bool,
        is_extern_decl: bool,
        value: InternPool.Index,
    };

    pub const Index = enum(u32) {
        _,

        pub fn toOptional(i: Nav.Index) Optional {
            return @fromBackingInt(@intCast(@backingInt(i)));
        }

        pub const Optional = enum(u32) {
            none = std.math.maxInt(u32),
            _,

            pub fn unwrap(opt: Optional) ?Nav.Index {
                return switch (opt) {
                    .none => null,
                    _ => @fromBackingInt(@intCast(@backingInt(opt))),
                };
            }
        };
    };
};

pub const NamespaceIndex = enum(u32) { _ };

pub const OptionalNamespaceIndex = enum(u32) {
    none = std.math.maxInt(u32),
    _,

    pub fn init(maybe_ns: ?NamespaceIndex) OptionalNamespaceIndex {
        const ns = maybe_ns orelse return .none;
        return @fromBackingInt(@intCast(@backingInt(ns)));
    }

    pub fn unwrap(opt: OptionalNamespaceIndex) ?NamespaceIndex {
        if (opt == .none) return null;
        return @fromBackingInt(@intCast(@backingInt(opt)));
    }
};

pub const FileIndex = enum(u32) { _ };

pub const OptionalFileIndex = enum(u32) {
    none = std.math.maxInt(u32),
    _,

    pub fn init(maybe_file: ?FileIndex) OptionalFileIndex {
        const file = maybe_file orelse return .none;
        return @fromBackingInt(@intCast(@backingInt(file)));
    }

    pub fn unwrap(opt: OptionalFileIndex) ?FileIndex {
        if (opt == .none) return null;
        return @fromBackingInt(@intCast(@backingInt(opt)));
    }
};

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

    pub fn fromByteUnits(n: u64) Alignment {
        if (n == 0) return .none;
        assert(std.math.isPowerOfTwo(n));
        return @fromBackingInt(@intCast(@ctz(n)));
    }

    pub fn fromNonzeroByteUnits(n: u64) Alignment {
        assert(n != 0);
        return fromByteUnits(n);
    }

    pub fn toByteUnits(a: Alignment) ?u64 {
        return switch (a) {
            .none => null,
            else => @as(u64, 1) << @backingInt(a),
        };
    }

    pub fn check(a: Alignment, addr: u64) bool {
        assert(a != .none);
        return @ctz(addr) >= @backingInt(a);
    }

    pub fn compare(lhs: Alignment, op: std.math.CompareOperator, rhs: Alignment) bool {
        return std.math.compare(lhs.toRelaxedCompareUnits(), op, rhs.toRelaxedCompareUnits());
    }

    pub fn toRelaxedCompareUnits(a: Alignment) u8 {
        const n: u8 = @backingInt(a);
        assert(n <= @backingInt(Alignment.none));
        if (n == @backingInt(Alignment.none)) return 0;
        return n + 1;
    }

    pub fn max(lhs: Alignment, rhs: Alignment) Alignment {
        if (lhs == .none) return rhs;
        if (rhs == .none) return lhs;
        return maxStrict(lhs, rhs);
    }

    pub fn maxStrict(lhs: Alignment, rhs: Alignment) Alignment {
        assert(lhs != .none);
        assert(rhs != .none);
        return @fromBackingInt(@intCast(@max(@backingInt(lhs), @backingInt(rhs))));
    }

    pub fn forward(a: Alignment, addr: u64) u64 {
        assert(a != .none);
        const x = (@as(u64, 1) << @backingInt(a)) - 1;
        return (addr + x) & ~x;
    }

    pub fn fromLog2Units(a: u32) Alignment {
        assert(a != @backingInt(Alignment.none));
        return @fromBackingInt(@intCast(a));
    }

    pub fn compareStrict(lhs: Alignment, op: std.math.CompareOperator, rhs: Alignment) bool {
        assert(lhs != .none);
        assert(rhs != .none);
        return std.math.compare(@backingInt(lhs), op, @backingInt(rhs));
    }

    pub fn min(lhs: Alignment, rhs: Alignment) Alignment {
        if (lhs == .none) return lhs;
        if (rhs == .none) return rhs;
        return minStrict(lhs, rhs);
    }

    pub fn minStrict(lhs: Alignment, rhs: Alignment) Alignment {
        assert(lhs != .none);
        assert(rhs != .none);
        return @fromBackingInt(@intCast(@min(@backingInt(lhs), @backingInt(rhs))));
    }

    // A view over the per-field alignments stored one-per-`extra` slot. The compiler packs these
    // (Alignment is u6); the REPL keeps one u32 slot each, like `field_offsets`.
    pub const Slice = struct {
        start: []const u32,

        pub const empty: Slice = .{ .start = &.{} };

        pub fn get(s: Slice, i: usize) Alignment {
            return @fromBackingInt(@intCast(@as(u6, @intCast(s.start[i]))));
        }

        pub fn getOrNone(s: Slice, i: usize) Alignment {
            if (s.start.len == 0) return .none;
            return s.get(i);
        }
    };
};

pub const ComptimeUnit = struct {
    zir_index: std.zig.Zir.Inst.Index,
    namespace: NamespaceIndex,

    pub const Id = enum(u32) { _ };
};

pub const Namespace = struct {
    parent: OptionalNamespaceIndex,
    file_scope: OptionalFileIndex,
    generation: u32,
    owner_type: Index,
    pub_decls: std.ArrayHashMapUnmanaged(Nav.Index, void, NavNameContext, true),
    priv_decls: std.ArrayHashMapUnmanaged(Nav.Index, void, NavNameContext, true),
    test_decls: std.ArrayListUnmanaged(Nav.Index),
    comptime_decls: std.ArrayListUnmanaged(ComptimeUnit.Id),

    pub const NavNameContext = struct {
        pool: *const InternPool,

        pub fn hash(ctx: NavNameContext, nav: Nav.Index) u32 {
            const name = ctx.pool.getNav(nav).name;
            return std.hash.int(@backingInt(name));
        }

        pub fn eql(ctx: NavNameContext, a_nav: Nav.Index, b_nav: Nav.Index, b_index: usize) bool {
            _ = b_index;
            const a_name = ctx.pool.getNav(a_nav).name;
            const b_name = ctx.pool.getNav(b_nav).name;
            return a_name == b_name;
        }
    };

    pub const NameAdapter = struct {
        pool: *const InternPool,

        pub fn hash(_: NameAdapter, name: NullTerminatedString) u32 {
            return std.hash.int(@backingInt(name));
        }

        pub fn eql(ctx: NameAdapter, a_name: NullTerminatedString, b_nav: Nav.Index, b_index: usize) bool {
            _ = b_index;
            return a_name == ctx.pool.getNav(b_nav).name;
        }
    };

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

pub const SimpleType = enum(u32) {
    usize = @backingInt(Index.usize_type),
    isize = @backingInt(Index.isize_type),
    c_char = @backingInt(Index.c_char_type),
    c_short = @backingInt(Index.c_short_type),
    c_ushort = @backingInt(Index.c_ushort_type),
    c_int = @backingInt(Index.c_int_type),
    c_uint = @backingInt(Index.c_uint_type),
    c_long = @backingInt(Index.c_long_type),
    c_ulong = @backingInt(Index.c_ulong_type),
    c_longlong = @backingInt(Index.c_longlong_type),
    c_ulonglong = @backingInt(Index.c_ulonglong_type),
    c_longdouble = @backingInt(Index.c_longdouble_type),
    f16 = @backingInt(Index.f16_type),
    f32 = @backingInt(Index.f32_type),
    f64 = @backingInt(Index.f64_type),
    f80 = @backingInt(Index.f80_type),
    f128 = @backingInt(Index.f128_type),
    anyopaque = @backingInt(Index.anyopaque_type),
    bool = @backingInt(Index.bool_type),
    void = @backingInt(Index.void_type),
    type = @backingInt(Index.type_type),
    anyerror = @backingInt(Index.anyerror_type),
    comptime_int = @backingInt(Index.comptime_int_type),
    comptime_float = @backingInt(Index.comptime_float_type),
    noreturn = @backingInt(Index.noreturn_type),
    null = @backingInt(Index.null_type),
    undefined = @backingInt(Index.undefined_type),
    enum_literal = @backingInt(Index.enum_literal_type),
    adhoc_inferred_error_set = @backingInt(Index.adhoc_inferred_error_set_type),
    generic_poison = @backingInt(Index.generic_poison_type),
};

pub const SimpleValue = enum(u32) {
    void = @backingInt(Index.void_value),
    null = @backingInt(Index.null_value),
    true = @backingInt(Index.bool_true),
    false = @backingInt(Index.bool_false),
    @"unreachable" = @backingInt(Index.unreachable_value),
};

pub const Key = union(enum) {
    simple_type: SimpleType,
    simple_value: SimpleValue,
    enum_literal: NullTerminatedString,
    int_type: std.lang.Type.Int,
    anyframe_type: Index,
    int: Int,
    float: Float,
    undef: Index,
    ptr_type: PtrType,
    ptr: Ptr,
    slice: Slice,
    error_set_type: ErrorSetType,
    err: Error,
    error_union_type: ErrorUnionType,
    error_union: ErrorUnion,
    func_type: FuncType,
    func: Func,
    @"extern": Extern,
    array_type: ArrayType,
    vector_type: VectorType,
    opt_type: Index,
    opt: Opt,
    tuple_type: TupleType,
    struct_type: ContainerType,
    enum_type: ContainerType,
    union_type: ContainerType,
    opaque_type: ContainerType,
    aggregate: Aggregate,
    enum_tag: EnumTag,
    un: Union,
    bitpack: Bitpack,

    pub const Int = struct {
        ty: Index,
        storage: Storage,

        pub const Storage = union(enum) {
            u64: u64,
            i64: i64,
            big_int: BigIntConst,

            pub fn toBigInt(storage: Storage, space: *BigIntSpace) BigIntConst {
                return switch (storage) {
                    .big_int => |b| b,
                    inline .u64, .i64 => |v| std.math.big.int.Mutable.init(&space.limbs, v).toConst(),
                };
            }

            pub const BigIntSpace = struct {
                limbs: [(@sizeOf(u64) / @sizeOf(std.math.big.Limb)) + 1]std.math.big.Limb,
            };
        };
    };

    pub const Float = struct {
        ty: Index,
        storage: Storage,

        pub const Storage = union(enum) {
            f16: f16,
            f32: f32,
            f64: f64,
            f80: f80,
            f128: f128,
        };
    };

    pub const PtrType = extern struct {
        child: Index,
        sentinel: Index = .none,
        flags: Flags = .{},
        packed_offset: PackedOffset = .{ .host_size = 0, .bit_offset = 0 },

        pub const VectorIndex = enum(u16) {
            none = std.math.maxInt(u16),
            _,
        };

        pub const Flags = packed struct(u32) {
            size: Size = .one,
            alignment: Alignment = .none,
            is_const: bool = false,
            is_volatile: bool = false,
            is_allowzero: bool = false,
            address_space: AddressSpace = .generic,
            vector_index: VectorIndex = .none,
        };

        pub const PackedOffset = packed struct(u32) {
            /// If this is non-zero it means the pointer points to a sub-byte range of data, which is
            /// backed by a "host integer" with this number of bytes. When host_size=pointee_abi_size
            /// and bit_offset=0, this must be represented with host_size=0 instead.
            host_size: u16,
            bit_offset: u16,
        };

        pub const Size = std.lang.Type.Pointer.Size;
        pub const AddressSpace = std.lang.AddressSpace;
    };

    pub const Ptr = struct {
        ty: Index,
        base_addr: BaseAddr,
        byte_offset: u64,

        pub const BaseAddr = union(enum) {
            comptime_alloc: ComptimeAllocIndex,
            nav: Nav.Index,
            uav: Uav,
            comptime_field: Index,
            int,
            field: BaseIndex,
            arr_elem: BaseIndex,
            opt_payload: Index,
            eu_payload: Index,

            pub const BaseIndex = struct {
                base: Index,
                index: u64,
            };
            pub const Uav = extern struct {
                val: Index,
                orig_ty: Index,
            };
        };
    };

    pub const Slice = struct {
        ty: Index,
        ptr: Index,
        len: Index,
    };

    pub const ComptimeAllocIndex = enum(u32) { _ };

    pub const ErrorSetType = struct {
        names: []const NullTerminatedString,

        pub fn nameIndex(self: ErrorSetType, pool: *const InternPool, name: NullTerminatedString) ?u32 {
            _ = pool;
            const i = std.mem.indexOfScalar(NullTerminatedString, self.names, name) orelse return null;
            return @intCast(i);
        }
    };

    pub const TupleType = struct {
        types: []const Index,
        values: []const Index,
    };

    pub const ContainerType = union(enum) {
        declared: Declared,
        reified: Reified,
        generated_union_tag: Index,

        pub const Declared = struct {
            source_zir_id: u32,
            decl_inst: std.zig.Zir.Inst.Index,
            captures: []const Index = &.{},
        };
        pub const Reified = struct {
            source_zir_id: u32,
            decl_inst: std.zig.Zir.Inst.Index,
            type_hash: u64,
        };

        pub fn sourceZirId(self: ContainerType) u32 {
            return switch (self) {
                .declared => |d| d.source_zir_id,
                .reified => |r| r.source_zir_id,
                .generated_union_tag => unreachable,
            };
        }
        pub fn declInst(self: ContainerType) std.zig.Zir.Inst.Index {
            return switch (self) {
                .declared => |d| d.decl_inst,
                .reified => |r| r.decl_inst,
                .generated_union_tag => unreachable,
            };
        }
        pub fn captures(self: ContainerType) []const Index {
            return switch (self) {
                .declared => |d| d.captures,
                else => &.{},
            };
        }
        pub fn generatedUnion(self: ContainerType) Index {
            return switch (self) {
                .generated_union_tag => |idx| idx,
                else => .none,
            };
        }
    };

    pub const Union = struct {
        ty: Index,
        tag: Index,
        val: Index,
    };

    pub const EnumTag = struct {
        ty: Index,
        int: Index,
    };

    pub const Bitpack = struct {
        ty: Index,
        backing_int_val: Index,
    };

    pub const Error = extern struct {
        ty: Index,
        name: NullTerminatedString,
    };

    pub const ErrorUnionType = extern struct {
        error_set_type: Index,
        payload_type: Index,
    };

    pub const Aggregate = struct {
        ty: Index,
        storage: Storage,

        pub const Storage = union(enum) {
            bytes: String,
            repeated_elem: Index,
            elems: []const Index,

            pub fn values(self: *const Storage) []const Index {
                return switch (self.*) {
                    .bytes => &.{},
                    .elems => |elems| elems,
                    .repeated_elem => |*elem| @as(*const [1]Index, elem),
                };
            }
        };
    };

    pub const ArrayType = extern struct {
        len: u64,
        child: Index,
        sentinel: Index = .none,

        pub fn lenIncludingSentinel(at: ArrayType) u64 {
            return at.len + @intFromBool(at.sentinel != .none);
        }
    };

    pub const VectorType = extern struct {
        len: u32,
        child: Index,
    };

    pub const Opt = extern struct {
        ty: Index,
        val: Index,
    };

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
        source_zir_id: u32 = std.math.maxInt(u32),
        ty: Index,
        uncoerced_ty: Index,
        zir_body_inst: std.zig.Zir.Inst.Index,
        parent: Index = .none,
        generic_owner: Index = .none,
        comptime_args: []const Index = &.{},
        /// The `Nav` that owns this function. Ignored by hashing and equality (a function alias
        /// shares the aliased function's value, hence its owner). `.none` for a function with no
        /// owning declaration, e.g. a bare function literal evaluated at the session prompt.
        owner_nav: Nav.Index.Optional = .none,
    };

    /// An external symbol whose value is supplied by the linker at runtime. The comptime
    /// layer only ever holds it; name/is_const/alignment come from `owner_nav`, matching
    /// the compiler's `Tag.Extern`. The linker-only fields (linkage, visibility, relocation,
    /// decoration, source) have no comptime meaning here and are not modelled.
    pub const Extern = struct {
        ty: Index,
        owner_nav: Nav.Index,
    };

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
                std.hash.autoHash(&hasher, @as(u32, @bitCast(pt.packed_offset)));
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
                    .comptime_field => |val| std.hash.autoHash(&hasher, val),
                    .int => {},
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
                for (tt.values) |val| std.hash.autoHash(&hasher, val);
            },
            .struct_type => |ct| hashContainerType(&hasher, ct),
            .enum_type => |ct| hashContainerType(&hasher, ct),
            .enum_tag => |et| {
                std.hash.autoHash(&hasher, et.ty);
                std.hash.autoHash(&hasher, et.int);
            },
            .union_type => |ct| hashContainerType(&hasher, ct),
            .opaque_type => |ct| hashContainerType(&hasher, ct),
            .un => |uv| {
                std.hash.autoHash(&hasher, uv.ty);
                std.hash.autoHash(&hasher, uv.tag);
                std.hash.autoHash(&hasher, uv.val);
            },
            .bitpack => |b| {
                std.hash.autoHash(&hasher, b.ty);
                std.hash.autoHash(&hasher, b.backing_int_val);
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
                const len = pool.aggregateElementCount(agg.ty);
                const KeyTag = @typeInfo(Key).@"union".tag_type.?;
                const child = switch (pool.indexToKey(agg.ty)) {
                    .array_type => |array_type| array_type.child,
                    .vector_type => |vector_type| vector_type.child,
                    .tuple_type, .struct_type => .none,
                    else => unreachable,
                };

                if (child == .u8_type) {
                    switch (agg.storage) {
                        .bytes => |bytes| for (bytes.toSlice(len, pool)) |byte| {
                            std.hash.autoHash(&hasher, KeyTag.int);
                            std.hash.autoHash(&hasher, byte);
                        },
                        .elems => |elems| for (elems[0..@intCast(len)]) |elem| {
                            const elem_key = pool.indexToKey(elem);
                            std.hash.autoHash(&hasher, @as(KeyTag, elem_key));
                            switch (elem_key) {
                                .undef => {},
                                .int => |int| std.hash.autoHash(&hasher, @as(u8, @intCast(int.storage.u64))),
                                else => unreachable,
                            }
                        },
                        .repeated_elem => |elem| {
                            const elem_key = pool.indexToKey(elem);
                            var remaining = len;
                            while (remaining > 0) : (remaining -= 1) {
                                std.hash.autoHash(&hasher, @as(KeyTag, elem_key));
                                switch (elem_key) {
                                    .undef => {},
                                    .int => |int| std.hash.autoHash(&hasher, @as(u8, @intCast(int.storage.u64))),
                                    else => unreachable,
                                }
                            }
                        },
                    }
                    return hasher.final();
                }

                switch (agg.storage) {
                    .bytes => unreachable,
                    .elems => |elems| for (elems[0..@intCast(len)]) |elem| std.hash.autoHash(&hasher, elem),
                    .repeated_elem => |elem| {
                        var remaining = len;
                        while (remaining > 0) : (remaining -= 1) std.hash.autoHash(&hasher, elem);
                    },
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
                std.hash.autoHash(&hasher, ft.cc);
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
            .@"extern" => |e| {
                std.hash.autoHash(&hasher, e.ty);
                std.hash.autoHash(&hasher, e.owner_nav);
            },
        }
        return hasher.final();
    }

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
                if (@as(u32, @bitCast(x.flags)) != @as(u32, @bitCast(y.flags))) break :blk false;
                break :blk @as(u32, @bitCast(x.packed_offset)) == @as(u32, @bitCast(y.packed_offset));
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
                    .comptime_field => |val| val == y.base_addr.comptime_field,
                    .int => true,
                    .field => |f| f.base == y.base_addr.field.base and f.index == y.base_addr.field.index,
                    .arr_elem => |f| f.base == y.base_addr.arr_elem.base and f.index == y.base_addr.arr_elem.index,
                    .opt_payload => |base| base == y.base_addr.opt_payload,
                    .eu_payload => |base| base == y.base_addr.eu_payload,
                };
            },
            .error_set_type => |x| std.mem.eql(NullTerminatedString, x.names, b.error_set_type.names),
            .tuple_type => |x| std.mem.eql(Index, x.types, b.tuple_type.types) and std.mem.eql(Index, x.values, b.tuple_type.values),
            .struct_type => |x| eqlContainerType(x, b.struct_type),
            .enum_type => |x| eqlContainerType(x, b.enum_type),
            .enum_tag => |x| blk: {
                const y = b.enum_tag;
                break :blk x.ty == y.ty and x.int == y.int;
            },
            .union_type => |x| eqlContainerType(x, b.union_type),
            .opaque_type => |x| eqlContainerType(x, b.opaque_type),
            .un => |x| blk: {
                const y = b.un;
                break :blk x.ty == y.ty and x.tag == y.tag and x.val == y.val;
            },
            .bitpack => |x| blk: {
                const y = b.bitpack;
                break :blk x.ty == y.ty and x.backing_int_val == y.backing_int_val;
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

                const len = pool.aggregateElementCount(x.ty);
                const StorageTag = @typeInfo(Key.Aggregate.Storage).@"union".tag_type.?;
                if (@as(StorageTag, x.storage) != @as(StorageTag, y.storage)) {
                    for (0..@intCast(len)) |elem_index| {
                        const a_elem = switch (x.storage) {
                            .bytes => |bytes| pool.getIfExists(.{ .int = .{
                                .ty = .u8_type,
                                .storage = .{ .u64 = bytes.at(elem_index, pool) },
                            } }) orelse break :blk false,
                            .elems => |elems| elems[elem_index],
                            .repeated_elem => |elem| elem,
                        };
                        const b_elem = switch (y.storage) {
                            .bytes => |bytes| pool.getIfExists(.{ .int = .{
                                .ty = .u8_type,
                                .storage = .{ .u64 = bytes.at(elem_index, pool) },
                            } }) orelse break :blk false,
                            .elems => |elems| elems[elem_index],
                            .repeated_elem => |elem| elem,
                        };
                        if (a_elem != b_elem) break :blk false;
                    }
                    break :blk true;
                }

                switch (x.storage) {
                    .bytes => |a_bytes| {
                        const b_bytes = y.storage.bytes;
                        break :blk a_bytes == b_bytes or
                            std.mem.eql(u8, a_bytes.toSlice(len, pool), b_bytes.toSlice(len, pool));
                    },
                    .elems => |a_elems| {
                        const b_elems = y.storage.elems;
                        break :blk std.mem.eql(Index, a_elems[0..@intCast(len)], b_elems[0..@intCast(len)]);
                    },
                    .repeated_elem => |a_elem| break :blk a_elem == y.storage.repeated_elem,
                }
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
                if (!x.cc.eql(y.cc)) break :blk false;
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
            .@"extern" => |x| x.ty == b.@"extern".ty and x.owner_nav == b.@"extern".owner_nav,
        };
    }

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
            .opaque_type,
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
            .@"extern",
            .aggregate,
            .enum_tag,
            .un,
            .bitpack,
            => false,
        };
    }
};

fn hashContainerType(hasher: *std.hash.Wyhash, id: Key.ContainerType) void {
    std.hash.autoHash(hasher, @as(std.meta.Tag(Key.ContainerType), id));
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

fn eqlContainerType(x: Key.ContainerType, y: Key.ContainerType) bool {
    if (@as(std.meta.Tag(Key.ContainerType), x) != @as(std.meta.Tag(Key.ContainerType), y)) return false;
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

const Item = struct {
    tag: Tag,
    data: u32,

    const Tag = enum(u8) {
        simple_type,
        simple_value,
        enum_literal,
        type_int_unsigned,
        type_int_signed,
        type_anyframe,
        int_u8,
        int_u16,
        int_u32,
        int_i32,
        int_usize,
        int_comptime_int_u32,
        int_comptime_int_i32,
        int_small,
        int_positive,
        int_negative,
        float_f16,
        float_f32,
        float_f64,
        float_f80,
        float_f128,
        float_c_longdouble_f80,
        float_c_longdouble_f128,
        float_comptime_float,
        undef,
        type_pointer,
        ptr_comptime_alloc,
        ptr_nav,
        ptr_uav,
        ptr_comptime_field,
        ptr_int,
        ptr_field,
        ptr_arr_elem,
        ptr_opt_payload,
        ptr_eu_payload,
        ptr_slice,
        type_error_set,
        type_tuple,
        type_struct,
        type_enum,
        enum_tag,
        type_union,
        type_opaque,
        union_value,
        bitpack,
        error_set_error,
        type_error_union,
        error_union_error,
        error_union_payload,
        type_function,
        func_decl,
        func_instance,
        func_coerced,
        extern_decl,
        type_vector,
        type_optional,
        type_array_small,
        type_array_big,
        aggregate,
        aggregate_bytes,
        repeated,
        opt_payload,
        opt_null,
    };
};

const TypePointer = struct {
    child: Index,
    sentinel: Index,
    flags: Key.PtrType.Flags,
    packed_offset: Key.PtrType.PackedOffset,
};

const FuncTypeRepr = struct {
    params_len: u32,
    return_type: Index,
    flags: Flags,

    const Flags = packed struct(u32) {
        cc: PackedCallingConvention,
        is_var_args: bool,
        is_noinline: bool,
        has_comptime_bits: bool,
        has_noalias_bits: bool,
        _reserved: u10 = 0,
    };
};

const PackedCallingConvention = packed struct(u18) {
    tag: std.lang.CallingConvention.Tag,
    /// May be ignored depending on `tag`.
    incoming_stack_alignment: Alignment,
    /// Interpretation depends on `tag`.
    extra: u4,

    fn pack(cc: std.lang.CallingConvention) PackedCallingConvention {
        return switch (cc) {
            inline else => |pl, tag| switch (@TypeOf(pl)) {
                void => .{
                    .tag = tag,
                    .incoming_stack_alignment = .none, // unused
                    .extra = 0, // unused
                },
                std.lang.CallingConvention.CommonOptions => .{
                    .tag = tag,
                    .incoming_stack_alignment = .fromByteUnits(pl.incoming_stack_alignment orelse 0),
                    .extra = 0, // unused
                },
                std.lang.CallingConvention.X86RegparmOptions => .{
                    .tag = tag,
                    .incoming_stack_alignment = .fromByteUnits(pl.incoming_stack_alignment orelse 0),
                    .extra = pl.register_params,
                },
                std.lang.CallingConvention.ArcInterruptOptions => .{
                    .tag = tag,
                    .incoming_stack_alignment = .fromByteUnits(pl.incoming_stack_alignment orelse 0),
                    .extra = @backingInt(pl.type),
                },
                std.lang.CallingConvention.ArmInterruptOptions => .{
                    .tag = tag,
                    .incoming_stack_alignment = .fromByteUnits(pl.incoming_stack_alignment orelse 0),
                    .extra = @backingInt(pl.type),
                },
                std.lang.CallingConvention.MicroblazeInterruptOptions => .{
                    .tag = tag,
                    .incoming_stack_alignment = .fromByteUnits(pl.incoming_stack_alignment orelse 0),
                    .extra = @backingInt(pl.type),
                },
                std.lang.CallingConvention.MipsInterruptOptions => .{
                    .tag = tag,
                    .incoming_stack_alignment = .fromByteUnits(pl.incoming_stack_alignment orelse 0),
                    .extra = @backingInt(pl.mode),
                },
                std.lang.CallingConvention.RiscvInterruptOptions => .{
                    .tag = tag,
                    .incoming_stack_alignment = .fromByteUnits(pl.incoming_stack_alignment orelse 0),
                    .extra = @backingInt(pl.mode),
                },
                std.lang.CallingConvention.ShInterruptOptions => .{
                    .tag = tag,
                    .incoming_stack_alignment = .fromByteUnits(pl.incoming_stack_alignment orelse 0),
                    .extra = @backingInt(pl.save),
                },
                std.lang.CallingConvention.SpirvKernelOptions => .{
                    .tag = tag,
                    .incoming_stack_alignment = .none,
                    .extra = 0,
                },
                std.lang.CallingConvention.SpirvFragmentOptions => .{
                    .tag = tag,
                    .incoming_stack_alignment = .none,
                    .extra = @as(u4, @backingInt(pl.depth_assumption)) << 1 | @intFromBool(pl.pixel_centered_integer),
                },
                std.lang.CallingConvention.SpirvMeshOptions => .{
                    .tag = tag,
                    .incoming_stack_alignment = .none,
                    .extra = @backingInt(pl.stage_output),
                },
                else => comptime unreachable,
            },
        };
    }

    fn extraLen(cc: PackedCallingConvention) u2 {
        return switch (cc.tag) {
            .spirv_kernel, .spirv_task => 3,
            .spirv_mesh => 2,
            else => 0,
        };
    }

    fn unpack(cc: PackedCallingConvention, trailing: []const u32) std.lang.CallingConvention {
        return switch (cc.tag) {
            inline else => |tag| @unionInit(
                std.lang.CallingConvention,
                @tagName(tag),
                switch (@FieldType(std.lang.CallingConvention, @tagName(tag))) {
                    void => {},
                    std.lang.CallingConvention.CommonOptions => .{
                        .incoming_stack_alignment = cc.incoming_stack_alignment.toByteUnits(),
                    },
                    std.lang.CallingConvention.X86RegparmOptions => .{
                        .incoming_stack_alignment = cc.incoming_stack_alignment.toByteUnits(),
                        .register_params = @intCast(cc.extra),
                    },
                    std.lang.CallingConvention.ArcInterruptOptions => .{
                        .incoming_stack_alignment = cc.incoming_stack_alignment.toByteUnits(),
                        .type = @fromBackingInt(@intCast(cc.extra)),
                    },
                    std.lang.CallingConvention.ArmInterruptOptions => .{
                        .incoming_stack_alignment = cc.incoming_stack_alignment.toByteUnits(),
                        .type = @fromBackingInt(@intCast(cc.extra)),
                    },
                    std.lang.CallingConvention.MicroblazeInterruptOptions => .{
                        .incoming_stack_alignment = cc.incoming_stack_alignment.toByteUnits(),
                        .type = @fromBackingInt(@intCast(cc.extra)),
                    },
                    std.lang.CallingConvention.MipsInterruptOptions => .{
                        .incoming_stack_alignment = cc.incoming_stack_alignment.toByteUnits(),
                        .mode = @fromBackingInt(@intCast(cc.extra)),
                    },
                    std.lang.CallingConvention.RiscvInterruptOptions => .{
                        .incoming_stack_alignment = cc.incoming_stack_alignment.toByteUnits(),
                        .mode = @fromBackingInt(@intCast(cc.extra)),
                    },
                    std.lang.CallingConvention.ShInterruptOptions => .{
                        .incoming_stack_alignment = cc.incoming_stack_alignment.toByteUnits(),
                        .save = @fromBackingInt(@intCast(cc.extra)),
                    },
                    std.lang.CallingConvention.SpirvKernelOptions => .{
                        .x = trailing[0],
                        .y = trailing[1],
                        .z = trailing[2],
                    },
                    std.lang.CallingConvention.SpirvFragmentOptions => .{
                        .pixel_centered_integer = @bitCast(@as(u1, @truncate(cc.extra))),
                        .depth_assumption = @fromBackingInt(@intCast(@as(u2, @truncate(cc.extra >> 1)))),
                    },
                    std.lang.CallingConvention.SpirvMeshOptions => .{
                        .stage_output = @fromBackingInt(@intCast(cc.extra)),
                        .max_primitives = trailing[0],
                        .max_vertices = trailing[1],
                    },
                    else => comptime unreachable,
                },
            ),
        };
    }
};

const FuncDeclRepr = struct {
    source_zir_id: u32,
    ty: Index,
    zir_body_inst: std.zig.Zir.Inst.Index,
    parent: Index,
    owner_nav: Nav.Index.Optional,
};

const FuncInstanceRepr = struct {
    source_zir_id: u32,
    ty: Index,
    generic_owner: Index,
    comptime_args_len: u32,
    owner_nav: Nav.Index.Optional,
};

const FuncCoercedRepr = struct {
    ty: Index,
    inner_func: Index,
};

pub const PackedU64 = packed struct(u64) {
    a: u32,
    b: u32,

    pub fn get(x: PackedU64) u64 {
        return @bitCast(x);
    }

    pub fn init(x: u64) PackedU64 {
        return @bitCast(x);
    }
};

const Vector = struct {
    len: u32,
    child: Index,
};

const Array = struct {
    len0: u32,
    len1: u32,
    child: Index,
    sentinel: Index,

    pub const Length = PackedU64;

    fn getLength(a: Array) u64 {
        return (PackedU64{
            .a = a.len0,
            .b = a.len1,
        }).get();
    }
};

const Repeated = struct {
    ty: Index,
    elem_val: Index,
};

const AggregateBytes = struct {
    ty: Index,
    bytes: String,
};

const captures_len_reified: u32 = std.math.maxInt(u32);
const captures_len_generated_union_tag: u32 = std.math.maxInt(u32) - 1;

fn containerCapturesLen(id: Key.ContainerType) u32 {
    return switch (id) {
        .declared => |d| @intCast(d.captures.len),
        .reified => captures_len_reified,
        .generated_union_tag => captures_len_generated_union_tag,
    };
}

fn appendContainerType(pool: *InternPool, id: Key.ContainerType) Allocator.Error!void {
    switch (id) {
        .generated_union_tag => |owner_union| try pool.extra.append(pool.gpa, @backingInt(owner_union)),
        .declared => |d| {
            try pool.extra.append(pool.gpa, d.source_zir_id);
            try pool.extra.append(pool.gpa, @backingInt(d.decl_inst));
            try pool.extra.appendSlice(pool.gpa, @ptrCast(d.captures));
        },
        .reified => |r| {
            try pool.extra.append(pool.gpa, r.source_zir_id);
            try pool.extra.append(pool.gpa, @backingInt(r.decl_inst));
            const type_hash: PackedU64 = .init(r.type_hash);
            try pool.extra.append(pool.gpa, type_hash.a);
            try pool.extra.append(pool.gpa, type_hash.b);
        },
    }
}

fn readContainerType(pool: *const InternPool, captures_len: u32, off: u32) Key.ContainerType {
    if (captures_len == captures_len_generated_union_tag)
        return .{ .generated_union_tag = @fromBackingInt(@intCast(pool.extra.items[off])) };
    const source_zir_id = pool.extra.items[off];
    const decl_inst: std.zig.Zir.Inst.Index = @fromBackingInt(@intCast(pool.extra.items[off + 1]));
    if (captures_len == captures_len_reified) return .{ .reified = .{
        .source_zir_id = source_zir_id,
        .decl_inst = decl_inst,
        .type_hash = (PackedU64{ .a = pool.extra.items[off + 2], .b = pool.extra.items[off + 3] }).get(),
    } };
    return .{ .declared = .{
        .source_zir_id = source_zir_id,
        .decl_inst = decl_inst,
        .captures = @ptrCast(pool.extra.items[off + 2 ..][0..captures_len]),
    } };
}

pub const TypeClass = enum(u3) {
    no_possible_value,
    one_possible_value,
    runtime,
    partially_comptime,
    fully_comptime,
};

const TypeStruct = struct {
    name: NullTerminatedString,
    namespace: OptionalNamespaceIndex,
    fields_len: u32,
    field_name_map: OptionalMapIndex,
    backing_int: Index,
    size: u32,
    captures_len: u32,
    flags: Flags,

    const Flags = packed struct(u32) {
        layout: enum(u2) { auto, @"extern", @"packed" },
        any_comptime_fields: bool,
        any_field_defaults: bool,
        any_field_aligns: bool,
        class: TypeClass,
        alignment: Alignment,
        want_layout: bool,
        fields_resolved: bool,
        _: u16 = 0,
    };
};

fn containerIdTrailingLen(captures_len: u32) u32 {
    if (captures_len == captures_len_generated_union_tag) return 1;
    if (captures_len == captures_len_reified) return 4;
    return 2 + captures_len;
}

const TypeEnum = struct {
    name: NullTerminatedString,
    namespace: OptionalNamespaceIndex,
    int_tag_type: Index,
    fields_len: u32,
    field_name_map: OptionalMapIndex,
    field_value_map: OptionalMapIndex,
    captures_len: u32,
    flags: Flags,

    const Flags = packed struct(u32) {
        nonexhaustive: bool,
        has_values: bool,
        fields_resolved: bool,
        want_layout: bool,
        int_tag_mode: BackingTypeMode,
        _: u27 = 0,
    };
};

const TypeUnion = struct {
    name: NullTerminatedString,
    namespace: OptionalNamespaceIndex,
    enum_tag_type: Index,
    backing_int: Index,
    fields_len: u32,
    field_name_map: OptionalMapIndex,
    captures_len: u32,
    size: u32,
    flags: Flags,

    const Flags = packed struct(u32) {
        layout: enum(u2) { auto, @"extern", @"packed" },
        any_field_aligns: bool,
        want_layout: bool,
        fields_resolved: bool,
        has_runtime_tag: bool,
        class: TypeClass,
        alignment: Alignment,
        tag_usage: UnionFields.TagUsage,
        _: u15 = 0,
    };
};

const TypeOpaque = struct {
    name: NullTerminatedString,
    namespace: OptionalNamespaceIndex,
    captures_len: u32,
};

const PtrComptimeAlloc = struct {
    ty: Index,
    index: Key.ComptimeAllocIndex,
    byte_offset_a: u32,
    byte_offset_b: u32,
    fn init(ty: Index, index: Key.ComptimeAllocIndex, byte_offset: u64) PtrComptimeAlloc {
        return .{ .ty = ty, .index = index, .byte_offset_a = @intCast(byte_offset >> 32), .byte_offset_b = @truncate(byte_offset) };
    }
    fn byteOffset(data: PtrComptimeAlloc) u64 {
        return @as(u64, data.byte_offset_a) << 32 | data.byte_offset_b;
    }
};

const PtrNav = struct {
    ty: Index,
    nav: Nav.Index,
    byte_offset_a: u32,
    byte_offset_b: u32,
    fn init(ty: Index, nav: Nav.Index, byte_offset: u64) PtrNav {
        return .{ .ty = ty, .nav = nav, .byte_offset_a = @intCast(byte_offset >> 32), .byte_offset_b = @truncate(byte_offset) };
    }
    fn byteOffset(data: PtrNav) u64 {
        return @as(u64, data.byte_offset_a) << 32 | data.byte_offset_b;
    }
};

const PtrUav = struct {
    ty: Index,
    val: Index,
    orig_ty: Index,
    byte_offset_a: u32,
    byte_offset_b: u32,
    fn init(ty: Index, val: Index, orig_ty: Index, byte_offset: u64) PtrUav {
        return .{ .ty = ty, .val = val, .orig_ty = orig_ty, .byte_offset_a = @intCast(byte_offset >> 32), .byte_offset_b = @truncate(byte_offset) };
    }
    fn byteOffset(data: PtrUav) u64 {
        return @as(u64, data.byte_offset_a) << 32 | data.byte_offset_b;
    }
};

const PtrBaseIndex = struct {
    ty: Index,
    base: Index,
    index_a: u32,
    index_b: u32,
    byte_offset_a: u32,
    byte_offset_b: u32,
    fn init(ty: Index, base: Index, index: u64, byte_offset: u64) PtrBaseIndex {
        return .{
            .ty = ty,
            .base = base,
            .index_a = @intCast(index >> 32),
            .index_b = @truncate(index),
            .byte_offset_a = @intCast(byte_offset >> 32),
            .byte_offset_b = @truncate(byte_offset),
        };
    }
    fn indexValue(data: PtrBaseIndex) u64 {
        return @as(u64, data.index_a) << 32 | data.index_b;
    }
    fn byteOffset(data: PtrBaseIndex) u64 {
        return @as(u64, data.byte_offset_a) << 32 | data.byte_offset_b;
    }
};

const PtrBase = struct {
    ty: Index,
    base: Index,
    byte_offset_a: u32,
    byte_offset_b: u32,
    fn init(ty: Index, base: Index, byte_offset: u64) PtrBase {
        return .{ .ty = ty, .base = base, .byte_offset_a = @intCast(byte_offset >> 32), .byte_offset_b = @truncate(byte_offset) };
    }
    fn byteOffset(data: PtrBase) u64 {
        return @as(u64, data.byte_offset_a) << 32 | data.byte_offset_b;
    }
};

const PtrInt = struct {
    ty: Index,
    byte_offset_a: u32,
    byte_offset_b: u32,
    fn init(ty: Index, byte_offset: u64) PtrInt {
        return .{ .ty = ty, .byte_offset_a = @intCast(byte_offset >> 32), .byte_offset_b = @truncate(byte_offset) };
    }
    fn byteOffset(data: PtrInt) u64 {
        return @as(u64, data.byte_offset_a) << 32 | data.byte_offset_b;
    }
};

const ErrorUnionErrRepr = struct {
    ty: Index,
    err_name: NullTerminatedString,
};

const ErrorUnionPayloadRepr = struct {
    ty: Index,
    payload: Index,
};

const IntBigHeader = packed struct {
    ty: u32,
    limbs_len: u32,

    const limbs_items_len = @divExact(@sizeOf(IntBigHeader), @sizeOf(std.math.big.Limb));
};

pub const Float64 = struct {
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

pub const Float80 = struct {
    piece0: u32,
    piece1: u32,
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

pub const Float128 = struct {
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

const FieldMap = std.array_hash_map.Custom(void, void, std.array_hash_map.AutoContext(void), false);

pub const OptionalMapIndex = enum(u32) {
    none = std.math.maxInt(u32),
    _,

    pub fn unwrap(oi: OptionalMapIndex) ?MapIndex {
        if (oi == .none) return null;
        return @fromBackingInt(@intCast(@backingInt(oi)));
    }
};

pub const MapIndex = enum(u32) {
    _,

    pub fn get(map_index: MapIndex, ip: *const InternPool) *FieldMap {
        return &ip.maps.items[@backingInt(map_index)];
    }

    pub fn toOptional(i: MapIndex) OptionalMapIndex {
        return @fromBackingInt(@intCast(@backingInt(i)));
    }
};

gpa: Allocator,
items: std.MultiArrayList(Item),
extra: std.ArrayListUnmanaged(u32),
big_int_limbs: std.ArrayListUnmanaged(std.math.big.Limb),
map: std.AutoArrayHashMapUnmanaged(void, void),

string_bytes: std.ArrayListUnmanaged(u8),
string_starts: std.ArrayListUnmanaged(u32),
string_map: std.AutoArrayHashMapUnmanaged(void, void),
navs: std.ArrayListUnmanaged(Nav),
namespaces: std.ArrayListUnmanaged(Namespace),
maps: std.ArrayListUnmanaged(FieldMap),
comptime_units: std.ArrayListUnmanaged(ComptimeUnit),
global_error_set: std.AutoArrayHashMapUnmanaged(NullTerminatedString, void),

const StringAdapter = struct {
    pool: *const InternPool,

    pub fn hash(_: StringAdapter, key: []const u8) u32 {
        return @truncate(std.hash.Wyhash.hash(0, key));
    }

    pub fn eql(self: StringAdapter, key: []const u8, _: void, b_index: usize) bool {
        const existing = self.pool.stringSlice(@fromBackingInt(@intCast(@as(u32, @intCast(b_index)))));
        return std.mem.eql(u8, key, existing);
    }
};

const KeyAdapter = struct {
    pool: *const InternPool,

    pub fn hash(self: KeyAdapter, key: Key) u32 {
        return @truncate(key.hash64(self.pool));
    }

    pub fn eql(self: KeyAdapter, key: Key, _: void, b_index: usize) bool {
        const existing = self.pool.indexToKey(@fromBackingInt(@intCast(@as(u32, @intCast(b_index)))));
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
        .maps = .empty,
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
    for (pool.maps.items) |*m| m.deinit(pool.gpa);
    pool.maps.deinit(pool.gpa);
    pool.comptime_units.deinit(pool.gpa);
    pool.navs.deinit(pool.gpa);
    pool.big_int_limbs.deinit(pool.gpa);
    pool.map.deinit(pool.gpa);
    pool.* = undefined;
}

fn addMap(pool: *InternPool, gpa: Allocator, cap: usize) Allocator.Error!MapIndex {
    const index: MapIndex = @fromBackingInt(@intCast(pool.maps.items.len));
    const ptr = try pool.maps.addOne(gpa);
    errdefer pool.maps.items.len -= 1;
    ptr.* = .{};
    try ptr.ensureTotalCapacity(gpa, cap);
    return index;
}

pub fn addFieldName(
    pool: *InternPool,
    names: []NullTerminatedString,
    map: MapIndex,
    name: NullTerminatedString,
) ?u32 {
    const m = map.get(pool);
    const field_idx = m.count();
    names[field_idx] = name;
    const adapter: NullTerminatedString.Adapter = .{ .strings = names[0..field_idx] };
    const gop = m.getOrPutAssumeCapacityAdapted(name, adapter);
    if (gop.found_existing) return @intCast(gop.index);
    assert(gop.index == field_idx);
    return null;
}

pub fn addFieldTagValue(
    pool: *InternPool,
    values: []Index,
    map: MapIndex,
    value: Index,
) ?u32 {
    const m = map.get(pool);
    const field_idx = m.count();
    values[field_idx] = value;
    const adapter: Index.Adapter = .{ .indexes = values[0..field_idx] };
    const gop = m.getOrPutAssumeCapacityAdapted(value, adapter);
    if (gop.found_existing) return @intCast(gop.index);
    assert(gop.index == field_idx);
    return null;
}

pub fn getErrorValue(pool: *InternPool, name: NullTerminatedString) Allocator.Error!u32 {
    const gop = try pool.global_error_set.getOrPut(pool.gpa, name);
    return @intCast(gop.index + 1);
}

pub fn getErrorValueIfExists(pool: *const InternPool, name: NullTerminatedString) ?u32 {
    return @intCast((pool.global_error_set.getIndex(name) orelse return null) + 1);
}

pub fn errorIntType(pool: *InternPool) Allocator.Error!Index {
    return pool.internIntType(.unsigned, pool.errorSetBits());
}

pub fn errorSetBits(pool: *const InternPool) u16 {
    const error_limit: u32 = @intCast(pool.global_error_set.count());
    if (error_limit == 0) return 0;
    return @as(u16, std.math.log2_int(u32, error_limit)) + 1;
}

pub fn aggregateTypeLen(pool: *const InternPool, ty: Index) u64 {
    return switch (pool.indexToKey(ty)) {
        .struct_type => pool.loadStructType(ty).field_types.len,
        .tuple_type => |tuple_type| tuple_type.types.len,
        .array_type => |array_type| array_type.len,
        .vector_type => |vector_type| vector_type.len,
        else => unreachable,
    };
}

pub fn aggregateTypeLenIncludingSentinel(pool: *const InternPool, ty: Index) u64 {
    return switch (pool.indexToKey(ty)) {
        .struct_type => pool.loadStructType(ty).field_types.len,
        .tuple_type => |tuple_type| tuple_type.types.len,
        .array_type => |array_type| array_type.lenIncludingSentinel(),
        .vector_type => |vector_type| vector_type.len,
        else => unreachable,
    };
}

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

pub fn getOrPutString(
    pool: *InternPool,
    gpa: Allocator,
    bytes: []const u8,
    comptime embedded_nulls: EmbeddedNulls,
) Allocator.Error!embedded_nulls.StringType() {
    if (embedded_nulls == .no_embedded_nulls) assert(std.mem.indexOfScalar(u8, bytes, 0) == null);

    if (bytes.len == 0) return .empty;

    const gop = try pool.string_map.getOrPutAdapted(gpa, bytes, StringAdapter{ .pool = pool });
    if (gop.found_existing) return @fromBackingInt(@intCast(@as(u32, @intCast(gop.index))));

    try pool.string_bytes.ensureUnusedCapacity(gpa, bytes.len + 1);
    pool.string_bytes.appendSliceAssumeCapacity(bytes);
    pool.string_bytes.appendAssumeCapacity(0);
    try pool.string_starts.append(gpa, @intCast(pool.string_bytes.items.len));

    const new_index: u32 = @intCast(gop.index);
    assert(new_index + 1 == pool.string_starts.items.len - 1);
    return @fromBackingInt(@intCast(new_index));
}

/// Mirrors the compiler's `getOrPutStringFmt`. The compiler writes the formatted bytes straight into
/// its per-thread string buffer via `getOrPutTrailingString`; the single-threaded pool here has no such
/// buffer, so the bytes go through a scratch allocation before `getOrPutString`.
pub fn getOrPutStringFmt(
    pool: *InternPool,
    gpa: Allocator,
    comptime format: []const u8,
    args: anytype,
    comptime embedded_nulls: EmbeddedNulls,
) Allocator.Error!embedded_nulls.StringType() {
    const len: usize = @intCast(std.fmt.count(format, args));
    const scratch = try gpa.alloc(u8, len);
    defer gpa.free(scratch);
    assert((std.fmt.bufPrint(scratch, format, args) catch unreachable).len == len);
    return pool.getOrPutString(gpa, scratch, embedded_nulls);
}

pub fn stringSlice(pool: *const InternPool, string: NullTerminatedString) [:0]const u8 {
    const raw = @backingInt(string);
    assert(raw + 1 < pool.string_starts.items.len);

    const start = pool.string_starts.items[raw];
    const end = pool.string_starts.items[raw + 1] - 1;
    assert(pool.string_bytes.items[end] == 0);
    return pool.string_bytes.items[start..end :0];
}

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
    return @fromBackingInt(@intCast(new_index_raw));
}

pub fn getNav(pool: *const InternPool, index: Nav.Index) Nav {
    const raw: u32 = @backingInt(index);
    assert(raw < pool.navs.items.len);
    return pool.navs.items[raw];
}

pub fn navPtr(pool: *InternPool, index: Nav.Index) *Nav {
    const raw: u32 = @backingInt(index);
    assert(raw < pool.navs.items.len);
    return &pool.navs.items[raw];
}

pub fn createNamespace(
    pool: *InternPool,
    gpa: Allocator,
    initialization: struct {
        parent: OptionalNamespaceIndex = .none,
        owner_type: Index = .none,
        file_scope: OptionalFileIndex = .none,
    },
) Allocator.Error!NamespaceIndex {
    const new_index_raw: u32 = @intCast(pool.namespaces.items.len);
    try pool.namespaces.append(gpa, .{
        .parent = initialization.parent,
        .file_scope = initialization.file_scope,
        .generation = 0,
        .owner_type = initialization.owner_type,
        .pub_decls = .empty,
        .priv_decls = .empty,
        .test_decls = .empty,
        .comptime_decls = .empty,
    });
    assert(pool.namespaces.items.len == new_index_raw + 1);
    return @fromBackingInt(@intCast(new_index_raw));
}

pub fn namespacePtr(pool: *InternPool, index: NamespaceIndex) *Namespace {
    const raw: u32 = @backingInt(index);
    assert(raw < pool.namespaces.items.len);
    return &pool.namespaces.items[raw];
}

pub const root_namespace_name = "repl";

pub fn namespaceName(
    pool: *InternPool,
    gpa: Allocator,
    ns_idx: NamespaceIndex,
) Allocator.Error!NullTerminatedString {
    const ns = pool.namespacePtr(ns_idx);
    if (ns.owner_type == .none) return pool.getOrPutString(gpa, root_namespace_name, .no_embedded_nulls);
    return pool.typeName(ns.owner_type);
}

pub fn fullyQualifiedName(
    pool: *InternPool,
    gpa: Allocator,
    ns_idx: NamespaceIndex,
    name: NullTerminatedString,
) Allocator.Error!NullTerminatedString {
    assert(name != .empty);
    const ns_name = try pool.namespaceName(gpa, ns_idx);

    const text = try std.fmt.allocPrint(gpa, "{s}.{s}", .{ pool.stringSlice(ns_name), pool.stringSlice(name) });
    defer gpa.free(text);
    return pool.getOrPutString(gpa, text, .no_embedded_nulls);
}

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
    return @fromBackingInt(@intCast(new_index_raw));
}

pub fn getComptimeUnit(pool: *const InternPool, id: ComptimeUnit.Id) ComptimeUnit {
    const raw: u32 = @backingInt(id);
    assert(raw < pool.comptime_units.items.len);
    return pool.comptime_units.items[raw];
}

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

    .{ .ptr_type = .{ .child = .usize_type, .flags = .{} } },
    .{ .ptr_type = .{ .child = .comptime_int_type, .flags = .{ .is_const = true } } },
    .{ .ptr_type = .{ .child = .u8_type, .flags = .{ .size = .many } } },
    .{ .ptr_type = .{ .child = .u8_type, .flags = .{ .size = .many, .is_const = true } } },
    .{ .ptr_type = .{ .child = .u8_type, .sentinel = .zero_u8, .flags = .{ .size = .many, .is_const = true } } },
    .{ .ptr_type = .{ .child = .u8_type, .flags = .{ .size = .slice, .is_const = true } } },
    .{ .ptr_type = .{ .child = .u8_type, .sentinel = .zero_u8, .flags = .{ .size = .slice, .is_const = true } } },

    .{ .ptr_type = .{ .child = .slice_const_u8_type, .flags = .{ .size = .many, .is_const = true } } },
    .{ .ptr_type = .{ .child = .slice_const_u8_type, .flags = .{ .size = .slice, .is_const = true } } },

    .{ .opt_type = .type_type },
    .{ .ptr_type = .{ .child = .type_type, .flags = .{ .size = .many, .is_const = true } } },
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

    .{ .opt_type = .noreturn_type },
    .{ .error_union_type = .{ .error_set_type = .anyerror_type, .payload_type = .void_type } },
    .{ .simple_type = .adhoc_inferred_error_set },
    .{ .simple_type = .generic_poison },
    .{ .tuple_type = .{ .types = &.{}, .values = &.{} } },

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
        assert(@backingInt(index) == expected_position);
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
        .data = @backingInt(simple),
    });
}

fn appendSimpleValue(pool: *InternPool, simple: SimpleValue) void {
    pool.items.appendAssumeCapacity(.{
        .tag = .simple_value,
        .data = @backingInt(simple),
    });
}

fn appendAnyframeType(pool: *InternPool, child: Index) void {
    pool.items.appendAssumeCapacity(.{
        .tag = .type_anyframe,
        .data = @backingInt(child),
    });
}

pub fn getIfExists(pool: *const InternPool, key: Key) ?Index {
    const adapter: KeyAdapter = .{ .pool = pool };
    const map_index = pool.map.getIndexAdapted(key, adapter) orelse return null;
    const existing: u32 = @intCast(map_index);
    assert(existing < pool.items.len);
    return @fromBackingInt(@intCast(existing));
}

pub fn get(pool: *InternPool, key: Key) Allocator.Error!Index {
    const adapter: KeyAdapter = .{ .pool = pool };
    const gop = try pool.map.getOrPutAdapted(pool.gpa, key, adapter);
    if (gop.found_existing) {
        const existing: u32 = @intCast(gop.index);
        assert(existing < pool.items.len);
        return @fromBackingInt(@intCast(existing));
    }
    assert(gop.index == pool.items.len);

    try pool.items.ensureUnusedCapacity(pool.gpa, 1);
    switch (key) {
        .simple_type => |s| appendSimpleType(pool, s),
        .simple_value => |s| appendSimpleValue(pool, s),
        .enum_literal => |n| pool.items.appendAssumeCapacity(.{ .tag = .enum_literal, .data = @backingInt(n) }),
        .int_type => |it| appendIntType(pool, it.signedness, it.bits),
        .anyframe_type => |child| appendAnyframeType(pool, child),
        .undef => |ty| {
            assert(ty != .none);
            pool.items.appendAssumeCapacity(.{
                .tag = .undef,
                .data = @backingInt(ty),
            });
        },
        .int => |i| try emitInt(pool, i),
        .float => |f| try emitFloat(pool, f),
        .ptr_type => |pt| try emitPtrType(pool, pt),
        .ptr => |p| try emitPtr(pool, p),
        .slice => |s| try emitSlice(pool, s),
        .error_set_type => |es| try emitErrorSetType(pool, es),
        .tuple_type => |tt| try emitTupleType(pool, tt),
        .struct_type => unreachable,
        .enum_type => unreachable,
        .enum_tag => |et| try emitEnumTag(pool, et),
        .union_type => unreachable,
        .opaque_type => unreachable,
        .un => |uv| try emitUnionValue(pool, uv),
        .bitpack => |b| try emitBitpack(pool, b),
        .err => |e| try emitErr(pool, e),
        .error_union_type => |eu| try emitErrorUnionType(pool, eu),
        .error_union => |eu| try emitErrorUnion(pool, eu),
        .func_type => |ft| try emitFuncType(pool, ft),
        .func => |f| try emitFunc(pool, f),
        .@"extern" => |e| try emitExtern(pool, e),
        .array_type => |at| try emitArrayType(pool, at),
        .vector_type => |vt| try emitVectorType(pool, vt),
        .opt_type => |child| appendOptionalType(pool, child),
        .opt => |o| try emitOpt(pool, o),
        .aggregate => |agg| try emitAggregate(pool, agg),
    }

    assert(pool.items.len == gop.index + 1);
    return @fromBackingInt(@intCast(@as(u32, @intCast(gop.index))));
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
            .opaque_type => .@"opaque",
            .func_type => .@"fn",
            .simple_type,
            .simple_value,
            .enum_literal,
            .int,
            .float,
            .undef,
            .ptr,
            .slice,
            .err,
            .error_union,
            .func,
            .@"extern",
            .opt,
            .aggregate,
            .enum_tag,
            .un,
            .bitpack,
            => unreachable,
        },
    };
}

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
    const i = @backingInt(index);
    assert(i < pool.items.len);
    const item = pool.items.get(i);
    return switch (item.tag) {
        .simple_type => .{ .simple_type = @fromBackingInt(@intCast(item.data)) },
        .simple_value => .{ .simple_value = @fromBackingInt(@intCast(item.data)) },
        .enum_literal => .{ .enum_literal = @fromBackingInt(@intCast(item.data)) },
        .type_int_unsigned => .{ .int_type = .{
            .signedness = .unsigned,
            .bits = @intCast(item.data),
        } },
        .type_int_signed => .{ .int_type = .{
            .signedness = .signed,
            .bits = @intCast(item.data),
        } },
        .type_anyframe => .{ .anyframe_type = @fromBackingInt(@intCast(item.data)) },
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
        .undef => .{ .undef = @fromBackingInt(@intCast(item.data)) },
        .type_pointer => ptrTypeFromExtra(pool, item.data),
        .ptr_comptime_alloc => ptrComptimeAllocFromExtra(pool, item.data),
        .ptr_nav => ptrNavFromExtra(pool, item.data),
        .ptr_uav => ptrUavFromExtra(pool, item.data),
        .ptr_comptime_field => ptrComptimeFieldFromExtra(pool, item.data),
        .ptr_int => ptrIntFromExtra(pool, item.data),
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
        .bitpack => bitpackFromExtra(pool, item.data),
        .type_union => unionTypeFromExtra(pool, item.data),
        .type_opaque => opaqueTypeFromExtra(pool, item.data),
        .union_value => unionValueFromExtra(pool, item.data),
        .error_set_error => errFromExtra(pool, item.data),
        .type_error_union => errorUnionTypeFromExtra(pool, item.data),
        .error_union_error => errorUnionErrFromExtra(pool, item.data),
        .error_union_payload => errorUnionPayloadFromExtra(pool, item.data),
        .type_function => funcTypeFromExtra(pool, item.data),
        .func_decl => funcDeclFromExtra(pool, item.data),
        .func_instance => funcInstanceFromExtra(pool, item.data),
        .func_coerced => funcCoercedFromExtra(pool, item.data),
        .extern_decl => externFromExtra(pool, item.data),
        .type_vector => vectorTypeFromExtra(pool, item.data),
        .type_optional => .{ .opt_type = @fromBackingInt(@intCast(item.data)) },
        .opt_payload => optPayloadFromExtra(pool, item.data),
        .opt_null => .{ .opt = .{ .ty = @fromBackingInt(@intCast(item.data)), .val = .none } },
        .type_array_small => arrayTypeSmallFromExtra(pool, item.data),
        .type_array_big => arrayTypeBigFromExtra(pool, item.data),
        .aggregate => aggregateFromExtra(pool, item.data),
        .aggregate_bytes => aggregateBytesFromExtra(pool, item.data),
        .repeated => repeatedFromExtra(pool, item.data),
    };
}

fn ptrTypeFromExtra(pool: *const InternPool, extra_index: u32) Key {
    const r = pool.extraData(TypePointer, extra_index);
    return .{ .ptr_type = .{
        .child = r.child,
        .sentinel = r.sentinel,
        .flags = r.flags,
        .packed_offset = r.packed_offset,
    } };
}

fn tupleTypeFromExtra(pool: *const InternPool, extra_index: u32) Key {
    assert(extra_index < pool.extra.items.len);
    const types_len = pool.extra.items[extra_index];
    assert(extra_index + 1 + types_len <= pool.extra.items.len);

    const raw_types = pool.extra.items[extra_index + 1 ..][0..types_len];
    const raw_values = pool.extra.items[extra_index + 1 + types_len ..][0..types_len];
    return .{
        .tuple_type = .{ .types = @ptrCast(raw_types), .values = @ptrCast(raw_values) },
    };
}

fn structTypeFromExtra(pool: *const InternPool, extra_index: u32) Key {
    const trail = pool.extraDataTrail(TypeStruct, extra_index);
    return .{ .struct_type = readContainerType(pool, trail.data.captures_len, trail.end) };
}

fn enumTypeFromExtra(pool: *const InternPool, extra_index: u32) Key {
    const trail = pool.extraDataTrail(TypeEnum, extra_index);
    return .{ .enum_type = readContainerType(pool, trail.data.captures_len, trail.end) };
}

fn enumTagFromExtra(pool: *const InternPool, extra_index: u32) Key {
    return .{ .enum_tag = pool.extraData(Key.EnumTag, extra_index) };
}

fn bitpackFromExtra(pool: *const InternPool, extra_index: u32) Key {
    return .{ .bitpack = pool.extraData(Key.Bitpack, extra_index) };
}

fn sliceFromExtra(pool: *const InternPool, extra_index: u32) Key {
    return .{ .slice = pool.extraData(Key.Slice, extra_index) };
}

fn unionTypeFromExtra(pool: *const InternPool, extra_index: u32) Key {
    const trail = pool.extraDataTrail(TypeUnion, extra_index);
    return .{ .union_type = readContainerType(pool, trail.data.captures_len, trail.end) };
}

fn opaqueTypeFromExtra(pool: *const InternPool, extra_index: u32) Key {
    const trail = pool.extraDataTrail(TypeOpaque, extra_index);
    return .{ .opaque_type = readContainerType(pool, trail.data.captures_len, trail.end) };
}

fn unionValueFromExtra(pool: *const InternPool, extra_index: u32) Key {
    return .{ .un = pool.extraData(Key.Union, extra_index) };
}

fn errorSetTypeFromExtra(pool: *const InternPool, extra_index: u32) Key {
    assert(extra_index < pool.extra.items.len);
    const names_len = pool.extra.items[extra_index];
    assert(extra_index + 1 + names_len <= pool.extra.items.len);

    const raw_names = pool.extra.items[extra_index + 1 ..][0..names_len];
    return .{
        .error_set_type = .{
            .names = @ptrCast(raw_names),
        },
    };
}

fn errFromExtra(pool: *const InternPool, extra_index: u32) Key {
    return .{ .err = pool.extraData(Key.Error, extra_index) };
}

fn errorUnionTypeFromExtra(pool: *const InternPool, extra_index: u32) Key {
    return .{ .error_union_type = pool.extraData(Key.ErrorUnionType, extra_index) };
}

fn arrayTypeSmallFromExtra(pool: *const InternPool, extra_index: u32) Key {
    const r = pool.extraData(Vector, extra_index);
    return .{ .array_type = .{
        .len = r.len,
        .child = r.child,
        .sentinel = .none,
    } };
}

fn vectorTypeFromExtra(pool: *const InternPool, extra_index: u32) Key {
    const r = pool.extraData(Vector, extra_index);
    return .{ .vector_type = .{
        .len = r.len,
        .child = r.child,
    } };
}

fn optPayloadFromExtra(pool: *const InternPool, extra_index: u32) Key {
    return .{ .opt = pool.extraData(Key.Opt, extra_index) };
}

fn arrayTypeBigFromExtra(pool: *const InternPool, extra_index: u32) Key {
    const r = pool.extraData(Array, extra_index);
    return .{ .array_type = .{
        .len = r.getLength(),
        .child = r.child,
        .sentinel = r.sentinel,
    } };
}

fn aggregateFromExtra(pool: *const InternPool, extra_index: u32) Key {
    assert(extra_index + 2 <= pool.extra.items.len);
    const ty: Index = @fromBackingInt(@intCast(pool.extra.items[extra_index]));
    const count: u32 = pool.extra.items[extra_index + 1];
    assert(extra_index + 2 + count <= pool.extra.items.len);
    const raw_elems = pool.extra.items[extra_index + 2 ..][0..count];
    return .{
        .aggregate = .{
            .ty = ty,
            .storage = .{ .elems = @ptrCast(raw_elems) },
        },
    };
}

fn aggregateBytesFromExtra(pool: *const InternPool, extra_index: u32) Key {
    const r = pool.extraData(AggregateBytes, extra_index);
    return .{ .aggregate = .{
        .ty = r.ty,
        .storage = .{ .bytes = r.bytes },
    } };
}

fn repeatedFromExtra(pool: *const InternPool, extra_index: u32) Key {
    const r = pool.extraData(Repeated, extra_index);
    return .{ .aggregate = .{
        .ty = r.ty,
        .storage = .{ .repeated_elem = r.elem_val },
    } };
}

fn errorUnionErrFromExtra(pool: *const InternPool, extra_index: u32) Key {
    const r = pool.extraData(ErrorUnionErrRepr, extra_index);
    return .{ .error_union = .{ .ty = r.ty, .val = .{ .err_name = r.err_name } } };
}

fn errorUnionPayloadFromExtra(pool: *const InternPool, extra_index: u32) Key {
    const r = pool.extraData(ErrorUnionPayloadRepr, extra_index);
    return .{ .error_union = .{ .ty = r.ty, .val = .{ .payload = r.payload } } };
}

fn ptrComptimeAllocFromExtra(pool: *const InternPool, extra_index: u32) Key {
    const r = pool.extraData(PtrComptimeAlloc, extra_index);
    return .{ .ptr = .{
        .ty = r.ty,
        .base_addr = .{ .comptime_alloc = r.index },
        .byte_offset = r.byteOffset(),
    } };
}

fn ptrNavFromExtra(pool: *const InternPool, extra_index: u32) Key {
    const r = pool.extraData(PtrNav, extra_index);
    return .{ .ptr = .{
        .ty = r.ty,
        .base_addr = .{ .nav = r.nav },
        .byte_offset = r.byteOffset(),
    } };
}

fn ptrUavFromExtra(pool: *const InternPool, extra_index: u32) Key {
    const r = pool.extraData(PtrUav, extra_index);
    return .{ .ptr = .{
        .ty = r.ty,
        .base_addr = .{ .uav = .{ .val = r.val, .orig_ty = r.orig_ty } },
        .byte_offset = r.byteOffset(),
    } };
}

fn ptrFieldFromExtra(pool: *const InternPool, extra_index: u32) Key {
    return ptrBaseIndexFromExtra(pool, extra_index, false);
}

fn ptrArrElemFromExtra(pool: *const InternPool, extra_index: u32) Key {
    return ptrBaseIndexFromExtra(pool, extra_index, true);
}

fn ptrOptPayloadFromExtra(pool: *const InternPool, extra_index: u32, is_eu: bool) Key {
    const r = pool.extraData(PtrBase, extra_index);
    return .{ .ptr = .{
        .ty = r.ty,
        .base_addr = if (is_eu) .{ .eu_payload = r.base } else .{ .opt_payload = r.base },
        .byte_offset = r.byteOffset(),
    } };
}

fn ptrComptimeFieldFromExtra(pool: *const InternPool, extra_index: u32) Key {
    const r = pool.extraData(PtrBase, extra_index);
    return .{ .ptr = .{
        .ty = r.ty,
        .base_addr = .{ .comptime_field = r.base },
        .byte_offset = r.byteOffset(),
    } };
}

fn ptrIntFromExtra(pool: *const InternPool, extra_index: u32) Key {
    const r = pool.extraData(PtrInt, extra_index);
    return .{ .ptr = .{
        .ty = r.ty,
        .base_addr = .int,
        .byte_offset = r.byteOffset(),
    } };
}

fn ptrBaseIndexFromExtra(pool: *const InternPool, extra_index: u32, is_arr_elem: bool) Key {
    const r = pool.extraData(PtrBaseIndex, extra_index);
    const bi: Key.Ptr.BaseAddr.BaseIndex = .{ .base = r.base, .index = r.indexValue() };
    return .{ .ptr = .{
        .ty = r.ty,
        .base_addr = if (is_arr_elem) .{ .arr_elem = bi } else .{ .field = bi },
        .byte_offset = r.byteOffset(),
    } };
}

fn addExtra(pool: *InternPool, item: anytype) Allocator.Error!u32 {
    const info = @typeInfo(@TypeOf(item)).@"struct";
    const index: u32 = @intCast(pool.extra.items.len);
    try pool.extra.ensureUnusedCapacity(pool.gpa, info.field_names.len);
    inline for (info.field_types, info.field_names) |field_type, field_name| {
        pool.extra.appendAssumeCapacity(switch (field_type) {
            Index,
            Nav.Index,
            Nav.Index.Optional,
            NamespaceIndex,
            OptionalNamespaceIndex,
            MapIndex,
            OptionalMapIndex,
            NullTerminatedString,
            String,
            Key.ComptimeAllocIndex,
            std.zig.Zir.Inst.Index,
            => @backingInt(@field(item, field_name)),

            u32,
            i32,
            Key.PtrType.Flags,
            Key.PtrType.PackedOffset,
            FuncTypeRepr.Flags,
            TypeStruct.Flags,
            TypeEnum.Flags,
            TypeUnion.Flags,
            => @bitCast(@field(item, field_name)),

            else => @compileError("bad field type: " ++ @typeName(field_type)),
        });
    }
    return index;
}

fn extraDataTrail(pool: *const InternPool, comptime T: type, index: u32) struct { data: T, end: u32 } {
    const field_names = @typeInfo(T).@"struct".field_names;
    const field_types = @typeInfo(T).@"struct".field_types;
    assert(index + field_names.len <= pool.extra.items.len);
    var result: T = undefined;
    inline for (field_names, field_types, index..) |field_name, field_type, extra_index| {
        const extra_item = pool.extra.items[extra_index];
        @field(result, field_name) = switch (field_type) {
            Index,
            Nav.Index,
            Nav.Index.Optional,
            NamespaceIndex,
            OptionalNamespaceIndex,
            MapIndex,
            OptionalMapIndex,
            NullTerminatedString,
            String,
            Key.ComptimeAllocIndex,
            std.zig.Zir.Inst.Index,
            => @fromBackingInt(@intCast(extra_item)),

            u32,
            i32,
            Key.PtrType.Flags,
            Key.PtrType.PackedOffset,
            FuncTypeRepr.Flags,
            TypeStruct.Flags,
            TypeEnum.Flags,
            TypeUnion.Flags,
            => @bitCast(extra_item),

            else => @compileError("bad field type: " ++ @typeName(field_type)),
        };
    }
    return .{ .data = result, .end = @intCast(index + field_names.len) };
}

fn extraData(pool: *const InternPool, comptime T: type, index: u32) T {
    return extraDataTrail(pool, T, index).data;
}

inline fn intKey(ty: Index, storage: Key.Int.Storage) Key {
    return .{ .int = .{ .ty = ty, .storage = storage } };
}

fn intSmallFromExtra(pool: *const InternPool, extra_index: u32) Key {
    assert(extra_index + 2 <= pool.extra.items.len);
    const slice = pool.extra.items[extra_index..][0..2];
    const ty: Index = @fromBackingInt(@intCast(slice[0]));
    return intKey(ty, .{ .u64 = slice[1] });
}

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

    return intKey(@fromBackingInt(@intCast(header.ty)), storage);
}

pub fn internIntType(
    pool: *InternPool,
    signedness: std.lang.Signedness,
    bits: u16,
) Allocator.Error!Index {
    return pool.get(.{ .int_type = .{ .signedness = signedness, .bits = bits } });
}

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
                    try pool.extra.appendSlice(pool.gpa, &.{ @backingInt(ty), casted });
                    pool.items.appendAssumeCapacity(.{ .tag = .int_small, .data = extra_index });
                    break :b;
                } else |_| {}
                try addBigInt(pool, ty, big_int);
            },
            inline .u64, .i64 => |x| {
                if (std.math.cast(u32, x)) |casted| {
                    const extra_index: u32 = @intCast(pool.extra.items.len);
                    try pool.extra.appendSlice(pool.gpa, &.{ @backingInt(ty), casted });
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

pub fn internInt(pool: *InternPool, int: Key.Int) Allocator.Error!Index {
    return pool.get(.{ .int = int });
}

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

pub fn internFloat(pool: *InternPool, float: Key.Float) Allocator.Error!Index {
    return pool.get(.{ .float = float });
}

fn emitPtrType(pool: *InternPool, pt: Key.PtrType) Allocator.Error!void {
    assert(pt.child != .none);
    const extra_index = try pool.addExtra(TypePointer{
        .child = pt.child,
        .sentinel = pt.sentinel,
        .flags = pt.flags,
        .packed_offset = pt.packed_offset,
    });
    pool.items.appendAssumeCapacity(.{ .tag = .type_pointer, .data = extra_index });
}

fn emitPtr(pool: *InternPool, p: Key.Ptr) Allocator.Error!void {
    assert(p.ty != .none);
    switch (p.base_addr) {
        .comptime_alloc => |idx| {
            const extra_index = try pool.addExtra(PtrComptimeAlloc.init(p.ty, idx, p.byte_offset));
            pool.items.appendAssumeCapacity(.{ .tag = .ptr_comptime_alloc, .data = extra_index });
        },
        .nav => |nav| {
            const extra_index = try pool.addExtra(PtrNav.init(p.ty, nav, p.byte_offset));
            pool.items.appendAssumeCapacity(.{ .tag = .ptr_nav, .data = extra_index });
        },
        .uav => |uav| {
            const extra_index = try pool.addExtra(PtrUav.init(p.ty, uav.val, uav.orig_ty, p.byte_offset));
            pool.items.appendAssumeCapacity(.{ .tag = .ptr_uav, .data = extra_index });
        },
        .comptime_field => |val| {
            const extra_index = try pool.addExtra(PtrBase.init(p.ty, val, p.byte_offset));
            pool.items.appendAssumeCapacity(.{ .tag = .ptr_comptime_field, .data = extra_index });
        },
        .int => {
            const extra_index = try pool.addExtra(PtrInt.init(p.ty, p.byte_offset));
            pool.items.appendAssumeCapacity(.{ .tag = .ptr_int, .data = extra_index });
        },
        .field, .arr_elem => |f| {
            const extra_index = try pool.addExtra(PtrBaseIndex.init(p.ty, f.base, f.index, p.byte_offset));
            const tag: Item.Tag = if (p.base_addr == .field) .ptr_field else .ptr_arr_elem;
            pool.items.appendAssumeCapacity(.{ .tag = tag, .data = extra_index });
        },
        .opt_payload, .eu_payload => |base| {
            const extra_index = try pool.addExtra(PtrBase.init(p.ty, base, p.byte_offset));
            const tag: Item.Tag = if (p.base_addr == .opt_payload) .ptr_opt_payload else .ptr_eu_payload;
            pool.items.appendAssumeCapacity(.{ .tag = tag, .data = extra_index });
        },
    }
}

fn emitErrorSetType(pool: *InternPool, es: Key.ErrorSetType) Allocator.Error!void {
    assert(es.names.len <= std.math.maxInt(u32));

    const extra_index: u32 = @intCast(pool.extra.items.len);
    try pool.extra.ensureUnusedCapacity(pool.gpa, 1 + es.names.len);
    pool.extra.appendAssumeCapacity(@intCast(es.names.len));
    for (es.names) |name| pool.extra.appendAssumeCapacity(@backingInt(name));
    pool.items.appendAssumeCapacity(.{ .tag = .type_error_set, .data = extra_index });
}

fn emitTupleType(pool: *InternPool, tt: Key.TupleType) Allocator.Error!void {
    assert(tt.types.len <= std.math.maxInt(u32));
    assert(tt.types.len == tt.values.len);

    const extra_index: u32 = @intCast(pool.extra.items.len);
    try pool.extra.ensureUnusedCapacity(pool.gpa, 1 + tt.types.len + tt.values.len);
    pool.extra.appendAssumeCapacity(@intCast(tt.types.len));
    for (tt.types) |ty| pool.extra.appendAssumeCapacity(@backingInt(ty));
    for (tt.values) |val| pool.extra.appendAssumeCapacity(@backingInt(val));
    pool.items.appendAssumeCapacity(.{ .tag = .type_tuple, .data = extra_index });
}

pub const BackingTypeMode = enum(u1) {
    explicit,
    auto,
};

pub const LoadedEnumType = struct {
    int_tag_type: Index,
    int_tag_mode: BackingTypeMode,
    nonexhaustive: bool,
    field_names: []const NullTerminatedString,
    field_values: []const Index,
    field_name_map: MapIndex,
    field_value_map: OptionalMapIndex,

    pub fn nameIndex(fields: LoadedEnumType, pool: *const InternPool, name: NullTerminatedString) ?u32 {
        const map = fields.field_name_map.get(pool);
        const adapter: NullTerminatedString.Adapter = .{ .strings = fields.field_names };
        const field_index = map.getIndexAdapted(name, adapter) orelse return null;
        return @intCast(field_index);
    }

    pub fn tagValueIndex(fields: LoadedEnumType, pool: *const InternPool, tag_val: Index) ?u32 {
        assert(pool.indexToKey(tag_val) == .int);
        if (fields.field_value_map.unwrap()) |field_value_map| {
            const map = field_value_map.get(pool);
            const adapter: Index.Adapter = .{ .indexes = fields.field_values };
            const field_index = map.getIndexAdapted(tag_val, adapter) orelse return null;
            return @intCast(field_index);
        }
        const field_index = switch (pool.indexToKey(tag_val).int.storage) {
            inline .u64, .i64 => |x| std.math.cast(u32, x) orelse return null,
            .big_int => |x| x.toInt(u32) catch return null,
        };
        return if (field_index < fields.field_names.len) field_index else null;
    }
};

pub fn loadEnumType(pool: *const InternPool, enum_ty: Index) LoadedEnumType {
    const item = pool.items.get(@backingInt(enum_ty));
    assert(item.tag == .type_enum);
    const trail = pool.extraDataTrail(TypeEnum, item.data);
    const r = trail.data;
    assert(r.flags.fields_resolved);
    const fields_len = r.fields_len;
    var base = trail.end + containerIdTrailingLen(r.captures_len);
    const names: []const NullTerminatedString = @ptrCast(pool.extra.items[base..][0..fields_len]);
    base += fields_len;
    const values: []const Index = if (r.flags.has_values) @ptrCast(pool.extra.items[base..][0..fields_len]) else &.{};
    return .{
        .int_tag_type = r.int_tag_type,
        .int_tag_mode = r.flags.int_tag_mode,
        .nonexhaustive = r.flags.nonexhaustive,
        .field_names = names,
        .field_values = values,
        .field_name_map = r.field_name_map.unwrap().?,
        .field_value_map = r.field_value_map,
    };
}

pub fn setEnumFields(
    pool: *InternPool,
    enum_ty: Index,
    int_tag_type: Index,
    nonexhaustive: bool,
    names: []const NullTerminatedString,
    values: []const Index,
) Allocator.Error!void {
    assert(values.len == 0 or values.len == names.len);
    const item = pool.items.get(@backingInt(enum_ty));
    assert(item.tag == .type_enum);
    const trail = pool.extraDataTrail(TypeEnum, item.data);
    const r = trail.data;
    if (r.flags.fields_resolved) return;
    assert(r.fields_len == names.len);
    assert(r.flags.has_values == (values.len != 0));
    var base = trail.end + containerIdTrailingLen(r.captures_len);
    for (names, 0..) |n, i| pool.extra.items[base + i] = @backingInt(n);
    base += r.fields_len;
    for (values, 0..) |v, i| pool.extra.items[base + i] = @backingInt(v);
    const name_map = try pool.addMap(pool.gpa, names.len);
    const value_map: OptionalMapIndex = if (values.len != 0) (try pool.addMap(pool.gpa, values.len)).toOptional() else .none;
    pool.extra.items[item.data + std.meta.fieldIndex(TypeEnum, "int_tag_type").?] = @backingInt(int_tag_type);
    pool.extra.items[item.data + std.meta.fieldIndex(TypeEnum, "field_name_map").?] = @backingInt(name_map.toOptional());
    pool.extra.items[item.data + std.meta.fieldIndex(TypeEnum, "field_value_map").?] = @backingInt(value_map);
    var flags = r.flags;
    flags.nonexhaustive = nonexhaustive;
    flags.fields_resolved = true;
    pool.extra.items[item.data + std.meta.fieldIndex(TypeEnum, "flags").?] = @bitCast(flags);
}

pub const RuntimeOrder = enum(u32) {
    unresolved = std.math.maxInt(u32) - 0,
    omitted = std.math.maxInt(u32) - 1,
    _,

    pub fn toInt(i: RuntimeOrder) ?u32 {
        return switch (i) {
            .omitted => null,
            .unresolved => unreachable,
            else => @backingInt(i),
        };
    }
};

pub const LoadedStructType = struct {
    layout: std.lang.Type.ContainerLayout,
    packed_backing_int_type: Index,
    field_names: []const NullTerminatedString,
    field_types: []const Index,
    field_defaults: []const Index,
    field_aligns: Alignment.Slice,
    field_is_comptime_bits: []const u32,
    field_name_map: MapIndex,
    field_runtime_order: []const RuntimeOrder,
    field_offsets: []const u32,
    class: TypeClass,
    size: u32,
    alignment: Alignment,

    pub fn nameIndex(fields: LoadedStructType, pool: *const InternPool, name: NullTerminatedString) ?u32 {
        const map = fields.field_name_map.get(pool);
        const adapter: NullTerminatedString.Adapter = .{ .strings = fields.field_names };
        const field_index = map.getIndexAdapted(name, adapter) orelse return null;
        return @intCast(field_index);
    }

    pub fn iterateRuntimeOrder(s: LoadedStructType) RuntimeOrderIterator {
        return switch (s.layout) {
            .auto => .{
                .runtime_order = std.mem.sliceTo(s.field_runtime_order, .omitted),
                .fields_len = @intCast(std.mem.sliceTo(s.field_runtime_order, .omitted).len),
                .next_index = 0,
            },
            .@"extern" => .{
                .runtime_order = null,
                .fields_len = @intCast(s.field_names.len),
                .next_index = 0,
            },
            .@"packed" => unreachable,
        };
    }

    pub const RuntimeOrderIterator = struct {
        runtime_order: ?[]const RuntimeOrder,
        fields_len: u32,
        next_index: u32,
        pub fn next(it: *RuntimeOrderIterator) ?u32 {
            const i = it.next_index;
            if (i == it.fields_len) return null;
            it.next_index = i + 1;
            const ro = it.runtime_order orelse return i;
            return ro[i].toInt().?;
        }
    };
};

pub fn typeToStruct(pool: *const InternPool, ty: Index) ?LoadedStructType {
    if (ty == .none) return null;
    return switch (pool.indexToKey(ty)) {
        .struct_type => pool.loadStructType(ty),
        else => null,
    };
}

pub fn loadStructType(pool: *const InternPool, struct_ty: Index) LoadedStructType {
    const item = pool.items.get(@backingInt(struct_ty));
    assert(item.tag == .type_struct);
    const trail = pool.extraDataTrail(TypeStruct, item.data);
    const r = trail.data;
    const fields_len = r.fields_len;
    var base = trail.end + containerIdTrailingLen(r.captures_len);
    const names: []const NullTerminatedString = @ptrCast(pool.extra.items[base..][0..fields_len]);
    base += fields_len;
    const types: []const Index = @ptrCast(pool.extra.items[base..][0..fields_len]);
    base += fields_len;
    const defaults: []const Index = if (r.flags.any_field_defaults) @ptrCast(pool.extra.items[base..][0..fields_len]) else &.{};
    base += if (r.flags.any_field_defaults) fields_len else 0;
    const aligns: Alignment.Slice = .{ .start = if (r.flags.any_field_aligns) pool.extra.items[base..][0..fields_len] else &.{} };
    base += if (r.flags.any_field_aligns) fields_len else 0;
    const comptime_len: u32 = if (r.flags.any_comptime_fields) (fields_len + 31) / 32 else 0;
    const comptime_bits = pool.extra.items[base..][0..comptime_len];
    base += comptime_len;
    const layout: std.lang.Type.ContainerLayout = switch (r.flags.layout) {
        .auto => .auto,
        .@"extern" => .@"extern",
        .@"packed" => .@"packed",
    };
    const runtime_order_len: u32 = if (layout == .auto) fields_len else 0;
    const runtime_order: []const RuntimeOrder = @ptrCast(pool.extra.items[base..][0..runtime_order_len]);
    base += runtime_order_len;
    const offsets: []const u32 = if (layout == .@"packed") &.{} else pool.extra.items[base..][0..fields_len];
    return .{
        .layout = layout,
        .packed_backing_int_type = r.backing_int,
        .field_names = names,
        .field_types = types,
        .field_defaults = defaults,
        .field_aligns = aligns,
        .field_is_comptime_bits = comptime_bits,
        .field_name_map = r.field_name_map.unwrap().?,
        .field_runtime_order = runtime_order,
        .field_offsets = offsets,
        .class = r.flags.class,
        .size = r.size,
        .alignment = r.flags.alignment,
    };
}

pub fn structLayoutResolved(pool: *const InternPool, struct_ty: Index) bool {
    const item = pool.items.get(@backingInt(struct_ty));
    assert(item.tag == .type_struct);
    return pool.extraData(TypeStruct, item.data).flags.want_layout;
}

pub fn fillDeclaredStructFields(
    pool: *InternPool,
    struct_ty: Index,
    names: []NullTerminatedString,
    types: []const Index,
    aligns: []const Alignment,
    comptime_bits: []const u32,
) Allocator.Error!void {
    const item = pool.items.get(@backingInt(struct_ty));
    assert(item.tag == .type_struct);
    const trail = pool.extraDataTrail(TypeStruct, item.data);
    const r = trail.data;
    if (r.flags.fields_resolved) return;
    assert(r.fields_len == names.len);
    assert(r.fields_len == types.len);
    const base = trail.end + containerIdTrailingLen(r.captures_len);
    for (names, 0..) |n, i| pool.extra.items[base + i] = @backingInt(n);
    for (types, 0..) |t, i| pool.extra.items[base + r.fields_len + i] = @backingInt(t);
    var off = base + r.fields_len + r.fields_len;
    if (r.flags.any_field_aligns) {
        for (aligns, 0..) |a, i| pool.extra.items[off + i] = @backingInt(a);
        off += r.fields_len;
    }
    if (r.flags.any_comptime_fields) {
        for (comptime_bits, 0..) |b, i| pool.extra.items[off + i] = b;
    }
    const map = r.field_name_map.unwrap().?;
    map.get(pool).clearRetainingCapacity();
    for (names) |field_name| assert(pool.addFieldName(names, map, field_name) == null);
    var flags = r.flags;
    flags.fields_resolved = true;
    pool.extra.items[item.data + std.meta.fieldIndex(TypeStruct, "flags").?] = @bitCast(flags);
}

pub fn setStructPackedBackingInt(pool: *InternPool, struct_ty: Index, backing: Index) void {
    const item = pool.items.get(@backingInt(struct_ty));
    assert(item.tag == .type_struct);
    pool.extra.items[item.data + std.meta.fieldIndex(TypeStruct, "backing_int").?] = @backingInt(backing);
}

pub fn setUnionPackedBackingInt(pool: *InternPool, union_ty: Index, backing: Index) void {
    const item = pool.items.get(@backingInt(union_ty));
    assert(item.tag == .type_union);
    pool.extra.items[item.data + std.meta.fieldIndex(TypeUnion, "backing_int").?] = @backingInt(backing);
}

pub fn setStructLayout(
    pool: *InternPool,
    struct_ty: Index,
    runtime_order: []const RuntimeOrder,
    offsets: []const u32,
    size: u32,
    alignment: Alignment,
    class: TypeClass,
) void {
    const item = pool.items.get(@backingInt(struct_ty));
    assert(item.tag == .type_struct);
    const trail = pool.extraDataTrail(TypeStruct, item.data);
    const r = trail.data;
    var base = trail.end + containerIdTrailingLen(r.captures_len) + r.fields_len + r.fields_len;
    if (r.flags.any_field_defaults) base += r.fields_len;
    if (r.flags.any_field_aligns) base += r.fields_len;
    if (r.flags.any_comptime_fields) base += (r.fields_len + 31) / 32;
    if (r.flags.layout == .auto) {
        for (runtime_order, 0..) |o, i| pool.extra.items[base + i] = @backingInt(o);
        base += r.fields_len;
    }
    if (r.flags.layout != .@"packed") {
        for (offsets, 0..) |o, i| pool.extra.items[base + i] = o;
    }
    pool.extra.items[item.data + std.meta.fieldIndex(TypeStruct, "size").?] = size;
    var flags = r.flags;
    flags.alignment = alignment;
    flags.class = class;
    flags.want_layout = true;
    pool.extra.items[item.data + std.meta.fieldIndex(TypeStruct, "flags").?] = @bitCast(flags);
}

pub fn typeName(pool: *const InternPool, ty: Index) NullTerminatedString {
    const item = pool.items.get(@backingInt(ty));
    return switch (item.tag) {
        .type_struct => pool.extraData(TypeStruct, item.data).name,
        .type_enum => pool.extraData(TypeEnum, item.data).name,
        .type_union => pool.extraData(TypeUnion, item.data).name,
        .type_opaque => pool.extraData(TypeOpaque, item.data).name,
        else => unreachable,
    };
}

pub fn typeNamespace(pool: *const InternPool, ty: Index) OptionalNamespaceIndex {
    const item = pool.items.get(@backingInt(ty));
    return switch (item.tag) {
        .type_struct => pool.extraData(TypeStruct, item.data).namespace,
        .type_enum => pool.extraData(TypeEnum, item.data).namespace,
        .type_union => pool.extraData(TypeUnion, item.data).namespace,
        .type_opaque => pool.extraData(TypeOpaque, item.data).namespace,
        else => .none,
    };
}

pub fn setNamespace(pool: *InternPool, ty: Index, ns: NamespaceIndex) void {
    const item = pool.items.get(@backingInt(ty));
    const slot = switch (item.tag) {
        .type_struct => item.data + std.meta.fieldIndex(TypeStruct, "namespace").?,
        .type_enum => item.data + std.meta.fieldIndex(TypeEnum, "namespace").?,
        .type_union => item.data + std.meta.fieldIndex(TypeUnion, "namespace").?,
        .type_opaque => item.data + std.meta.fieldIndex(TypeOpaque, "namespace").?,
        else => unreachable,
    };
    pool.extra.items[slot] = @backingInt(OptionalNamespaceIndex.init(ns));
}

fn emitEnumTag(pool: *InternPool, et: Key.EnumTag) Allocator.Error!void {
    const extra_index = try pool.addExtra(et);
    pool.items.appendAssumeCapacity(.{ .tag = .enum_tag, .data = extra_index });
}

fn emitBitpack(pool: *InternPool, b: Key.Bitpack) Allocator.Error!void {
    const extra_index = try pool.addExtra(b);
    pool.items.appendAssumeCapacity(.{ .tag = .bitpack, .data = extra_index });
}

pub const UnionFields = struct {
    layout: std.lang.Type.ContainerLayout,
    tag_usage: TagUsage,
    enum_tag_type: Index,
    packed_backing_int_type: Index,
    field_names: []const NullTerminatedString,
    field_types: []const Index,
    field_aligns: Alignment.Slice,
    field_name_map: MapIndex,
    has_runtime_tag: bool,
    class: TypeClass,
    size: u32,
    alignment: Alignment,

    pub const TagUsage = enum(u2) {
        none,
        safety,
        tagged,
    };
};

pub fn unionFields(pool: *const InternPool, union_ty: Index) UnionFields {
    const item = pool.items.get(@backingInt(union_ty));
    assert(item.tag == .type_union);
    const trail = pool.extraDataTrail(TypeUnion, item.data);
    const r = trail.data;
    const fields_len = r.fields_len;
    var base = trail.end + containerIdTrailingLen(r.captures_len);
    const names: []const NullTerminatedString = @ptrCast(pool.extra.items[base..][0..fields_len]);
    base += fields_len;
    const types: []const Index = @ptrCast(pool.extra.items[base..][0..fields_len]);
    base += fields_len;
    const aligns: Alignment.Slice = .{ .start = if (r.flags.any_field_aligns) pool.extra.items[base..][0..fields_len] else &.{} };
    return .{
        .layout = switch (r.flags.layout) {
            .auto => .auto,
            .@"extern" => .@"extern",
            .@"packed" => .@"packed",
        },
        .tag_usage = r.flags.tag_usage,
        .enum_tag_type = r.enum_tag_type,
        .packed_backing_int_type = r.backing_int,
        .field_names = names,
        .field_types = types,
        .field_aligns = aligns,
        .field_name_map = r.field_name_map.unwrap().?,
        .has_runtime_tag = r.flags.has_runtime_tag,
        .class = r.flags.class,
        .size = r.size,
        .alignment = r.flags.alignment,
    };
}

pub fn unionLayoutResolved(pool: *const InternPool, union_ty: Index) bool {
    const item = pool.items.get(@backingInt(union_ty));
    assert(item.tag == .type_union);
    return pool.extraData(TypeUnion, item.data).flags.want_layout;
}

// The REPL analog of the compiler's Type.assertHasLayout, which asserts (in runtime-safety builds) that a
// type's layout is resolved. The compiler builds that on Zcu.assertUpToDate (incremental-analysis currency),
// which the REPL doesn't model; here it checks the container's own resolved flag.
pub fn assertLayoutResolved(pool: *const InternPool, ty: Index) void {
    switch (pool.indexToKey(ty)) {
        .struct_type => assert(pool.structLayoutResolved(ty)),
        .union_type => assert(pool.unionLayoutResolved(ty)),
        else => {},
    }
}

pub fn fillDeclaredUnionFields(
    pool: *InternPool,
    union_ty: Index,
    names: []NullTerminatedString,
    types: []const Index,
    aligns: []const Alignment,
) Allocator.Error!void {
    const item = pool.items.get(@backingInt(union_ty));
    assert(item.tag == .type_union);
    const trail = pool.extraDataTrail(TypeUnion, item.data);
    const r = trail.data;
    if (r.flags.fields_resolved) return;
    assert(r.fields_len == names.len);
    assert(r.fields_len == types.len);
    const base = trail.end + containerIdTrailingLen(r.captures_len);
    for (names, 0..) |n, i| pool.extra.items[base + i] = @backingInt(n);
    for (types, 0..) |t, i| pool.extra.items[base + r.fields_len + i] = @backingInt(t);
    if (r.flags.any_field_aligns) {
        for (aligns, 0..) |a, i| pool.extra.items[base + r.fields_len + r.fields_len + i] = @backingInt(a);
    }
    const map = r.field_name_map.unwrap().?;
    map.get(pool).clearRetainingCapacity();
    for (names) |field_name| assert(pool.addFieldName(names, map, field_name) == null);
    var flags = r.flags;
    flags.fields_resolved = true;
    pool.extra.items[item.data + std.meta.fieldIndex(TypeUnion, "flags").?] = @bitCast(flags);
}

pub fn setUnionLayout(
    pool: *InternPool,
    union_ty: Index,
    size: u32,
    alignment: Alignment,
    class: TypeClass,
    has_runtime_tag: bool,
) void {
    const item = pool.items.get(@backingInt(union_ty));
    assert(item.tag == .type_union);
    const r = pool.extraData(TypeUnion, item.data);
    pool.extra.items[item.data + std.meta.fieldIndex(TypeUnion, "size").?] = size;
    var flags = r.flags;
    flags.alignment = alignment;
    flags.class = class;
    flags.has_runtime_tag = has_runtime_tag;
    flags.want_layout = true;
    pool.extra.items[item.data + std.meta.fieldIndex(TypeUnion, "flags").?] = @bitCast(flags);
}

fn emitUnionValue(pool: *InternPool, uv: Key.Union) Allocator.Error!void {
    const extra_index = try pool.addExtra(uv);
    pool.items.appendAssumeCapacity(.{ .tag = .union_value, .data = extra_index });
}

fn emitSlice(pool: *InternPool, s: Key.Slice) Allocator.Error!void {
    const extra_index = try pool.addExtra(s);
    pool.items.appendAssumeCapacity(.{ .tag = .ptr_slice, .data = extra_index });
}

fn emitErr(pool: *InternPool, e: Key.Error) Allocator.Error!void {
    assert(e.ty != .none);

    const extra_index = try pool.addExtra(e);
    pool.items.appendAssumeCapacity(.{ .tag = .error_set_error, .data = extra_index });
}

pub fn aggregateElementCount(pool: *const InternPool, ty: Index) u64 {
    assert(ty != .none);
    const key = pool.indexToKey(ty);
    return switch (key) {
        .struct_type => pool.loadStructType(ty).field_types.len,
        .array_type => |at| at.len,
        .vector_type => |vt| vt.len,
        .tuple_type => |tt| tt.types.len,
        else => unreachable,
    };
}

pub fn aggregateElementAt(pool: *InternPool, agg: Key.Aggregate, i: u64) Allocator.Error!Index {
    return switch (agg.storage) {
        .bytes => |bytes| try pool.get(.{ .int = .{ .ty = .u8_type, .storage = .{ .u64 = bytes.at(i, pool) } } }),
        .repeated_elem => |e| e,
        .elems => |es| blk: {
            assert(i < es.len);
            break :blk es[@intCast(i)];
        },
    };
}

fn emitAggregate(pool: *InternPool, agg: Key.Aggregate) Allocator.Error!void {
    assert(agg.ty != .none);
    switch (agg.storage) {
        .bytes => |bytes| {
            const extra_index = try pool.addExtra(AggregateBytes{ .ty = agg.ty, .bytes = bytes });
            pool.items.appendAssumeCapacity(.{ .tag = .aggregate_bytes, .data = extra_index });
        },
        .repeated_elem => |elem| {
            const extra_index = try pool.addExtra(Repeated{ .ty = agg.ty, .elem_val = elem });
            pool.items.appendAssumeCapacity(.{ .tag = .repeated, .data = extra_index });
        },
        .elems => |elems| {
            const extra_index: u32 = @intCast(pool.extra.items.len);
            try pool.extra.ensureUnusedCapacity(pool.gpa, 2 + elems.len);
            pool.extra.appendAssumeCapacity(@backingInt(agg.ty));
            pool.extra.appendAssumeCapacity(@intCast(elems.len));
            for (elems) |e| pool.extra.appendAssumeCapacity(@backingInt(e));
            pool.items.appendAssumeCapacity(.{ .tag = .aggregate, .data = extra_index });
        },
    }
}

fn emitArrayType(pool: *InternPool, at: Key.ArrayType) Allocator.Error!void {
    assert(at.child != .none);
    if (at.sentinel == .none and at.len <= std.math.maxInt(u32)) {
        const extra_index = try pool.addExtra(Vector{ .len = @intCast(at.len), .child = at.child });
        pool.items.appendAssumeCapacity(.{ .tag = .type_array_small, .data = extra_index });
        return;
    }
    const length = Array.Length.init(at.len);
    const extra_index = try pool.addExtra(Array{
        .len0 = length.a,
        .len1 = length.b,
        .child = at.child,
        .sentinel = at.sentinel,
    });
    pool.items.appendAssumeCapacity(.{ .tag = .type_array_big, .data = extra_index });
}

fn emitVectorType(pool: *InternPool, vt: Key.VectorType) Allocator.Error!void {
    assert(vt.child != .none);
    const extra_index = try pool.addExtra(Vector{ .len = vt.len, .child = vt.child });
    pool.items.appendAssumeCapacity(.{ .tag = .type_vector, .data = extra_index });
}

fn appendOptionalType(pool: *InternPool, child: Index) void {
    assert(child != .none);
    pool.items.appendAssumeCapacity(.{
        .tag = .type_optional,
        .data = @backingInt(child),
    });
}

fn emitOpt(pool: *InternPool, o: Key.Opt) Allocator.Error!void {
    assert(o.ty != .none);
    if (o.val == .none) {
        pool.items.appendAssumeCapacity(.{
            .tag = .opt_null,
            .data = @backingInt(o.ty),
        });
        return;
    }
    const extra_index = try pool.addExtra(o);
    pool.items.appendAssumeCapacity(.{ .tag = .opt_payload, .data = extra_index });
}

fn emitErrorUnionType(pool: *InternPool, eu: Key.ErrorUnionType) Allocator.Error!void {
    assert(eu.error_set_type != .none);
    assert(eu.payload_type != .none);

    const extra_index = try pool.addExtra(eu);
    pool.items.appendAssumeCapacity(.{ .tag = .type_error_union, .data = extra_index });
}

fn emitErrorUnion(pool: *InternPool, eu: Key.ErrorUnion) Allocator.Error!void {
    assert(eu.ty != .none);

    switch (eu.val) {
        .err_name => |name| {
            const extra_index = try pool.addExtra(ErrorUnionErrRepr{ .ty = eu.ty, .err_name = name });
            pool.items.appendAssumeCapacity(.{ .tag = .error_union_error, .data = extra_index });
        },
        .payload => |idx| {
            const extra_index = try pool.addExtra(ErrorUnionPayloadRepr{ .ty = eu.ty, .payload = idx });
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

pub fn internTupleType(pool: *InternPool, types: []const Index, values: []const Index) Allocator.Error!Index {
    return pool.get(.{ .tuple_type = .{ .types = types, .values = values } });
}

pub const WipContainerType = struct {
    index: Index,

    pub const Result = union(enum) {
        wip: WipContainerType,
        existing: Index,
    };
};

fn getOrPutContainer(pool: *InternPool, key: Key) Allocator.Error!struct { existing: ?Index, index: u32 } {
    const adapter: KeyAdapter = .{ .pool = pool };
    const gop = try pool.map.getOrPutAdapted(pool.gpa, key, adapter);
    if (gop.found_existing) return .{ .existing = @fromBackingInt(@intCast(@as(u32, @intCast(gop.index)))), .index = 0 };
    assert(gop.index == pool.items.len);
    try pool.items.ensureUnusedCapacity(pool.gpa, 1);
    return .{ .existing = null, .index = @intCast(gop.index) };
}

pub fn getDeclaredStructType(
    pool: *InternPool,
    name: NullTerminatedString,
    id: Key.ContainerType,
    fields_len: u32,
    layout: std.lang.Type.ContainerLayout,
    any_field_aligns: bool,
    any_comptime_fields: bool,
) Allocator.Error!WipContainerType.Result {
    const gop = try pool.getOrPutContainer(.{ .struct_type = id });
    if (gop.existing) |e| return .{ .existing = e };
    const runtime_order_len: u32 = if (layout == .auto) fields_len else 0;
    const comptime_len: u32 = if (any_comptime_fields) (fields_len + 31) / 32 else 0;
    const field_name_map = try pool.addMap(pool.gpa, fields_len);
    const extra_index = try pool.addExtra(TypeStruct{
        .name = name,
        .namespace = .none,
        .fields_len = fields_len,
        .field_name_map = field_name_map.toOptional(),
        .backing_int = .none,
        .size = 0,
        .captures_len = containerCapturesLen(id),
        .flags = .{
            .layout = switch (layout) {
                .auto => .auto,
                .@"extern" => .@"extern",
                .@"packed" => .@"packed",
            },
            .any_comptime_fields = any_comptime_fields,
            .any_field_defaults = false,
            .any_field_aligns = any_field_aligns,
            .class = .no_possible_value,
            .alignment = .none,
            .want_layout = false,
            .fields_resolved = false,
        },
    });
    try pool.appendContainerType(id);
    try pool.extra.ensureUnusedCapacity(pool.gpa, fields_len + fields_len +
        (if (any_field_aligns) fields_len else 0) + comptime_len + runtime_order_len + fields_len);
    pool.extra.appendNTimesAssumeCapacity(0, fields_len + fields_len +
        (if (any_field_aligns) fields_len else 0) + comptime_len);
    pool.extra.appendNTimesAssumeCapacity(@backingInt(RuntimeOrder.unresolved), runtime_order_len);
    pool.extra.appendNTimesAssumeCapacity(0, fields_len);
    pool.items.appendAssumeCapacity(.{ .tag = .type_struct, .data = extra_index });
    return .{ .wip = .{ .index = @fromBackingInt(@intCast(gop.index)) } };
}

pub fn getReifiedStructType(pool: *InternPool, ini: struct {
    name: NullTerminatedString,
    id: Key.ContainerType,
    layout: std.lang.Type.ContainerLayout,
    backing_int: Index,
    names: []const NullTerminatedString,
    types: []const Index,
    defaults: []const Index,
    aligns: []const Alignment,
    comptime_bits: []const u32,
}) Allocator.Error!Index {
    assert(ini.types.len == ini.names.len);
    const gop = try pool.getOrPutContainer(.{ .struct_type = ini.id });
    if (gop.existing) |e| return e;
    const fields_len: u32 = @intCast(ini.names.len);
    const any_defaults = ini.defaults.len != 0;
    const any_aligns = ini.aligns.len != 0;
    const any_comptime = ini.comptime_bits.len != 0;
    const runtime_order_len: u32 = if (ini.layout == .auto) fields_len else 0;
    const field_name_map = try pool.addMap(pool.gpa, fields_len);
    const extra_index = try pool.addExtra(TypeStruct{
        .name = ini.name,
        .namespace = .none,
        .fields_len = fields_len,
        .field_name_map = field_name_map.toOptional(),
        .backing_int = ini.backing_int,
        .size = 0,
        .captures_len = containerCapturesLen(ini.id),
        .flags = .{
            .layout = switch (ini.layout) {
                .auto => .auto,
                .@"extern" => .@"extern",
                .@"packed" => .@"packed",
            },
            .any_comptime_fields = any_comptime,
            .any_field_defaults = any_defaults,
            .any_field_aligns = any_aligns,
            .class = .no_possible_value,
            .alignment = .none,
            .want_layout = false,
            .fields_resolved = true,
        },
    });
    try pool.appendContainerType(ini.id);
    try pool.extra.ensureUnusedCapacity(pool.gpa, fields_len + fields_len +
        (if (any_defaults) fields_len else 0) + (if (any_aligns) fields_len else 0) +
        @as(u32, @intCast(ini.comptime_bits.len)) + runtime_order_len + fields_len);
    for (ini.names) |n| pool.extra.appendAssumeCapacity(@backingInt(n));
    for (ini.types) |t| pool.extra.appendAssumeCapacity(@backingInt(t));
    if (any_defaults) for (ini.defaults) |d| pool.extra.appendAssumeCapacity(@backingInt(d));
    if (any_aligns) for (ini.aligns) |a| pool.extra.appendAssumeCapacity(@backingInt(a));
    if (any_comptime) for (ini.comptime_bits) |b| pool.extra.appendAssumeCapacity(b);
    pool.extra.appendNTimesAssumeCapacity(@backingInt(RuntimeOrder.unresolved), runtime_order_len);
    pool.extra.appendNTimesAssumeCapacity(0, fields_len);
    pool.items.appendAssumeCapacity(.{ .tag = .type_struct, .data = extra_index });
    return @fromBackingInt(@intCast(gop.index));
}

pub fn getDeclaredEnumType(
    pool: *InternPool,
    name: NullTerminatedString,
    id: Key.ContainerType,
    fields_len: u32,
    has_values: bool,
    int_tag_mode: BackingTypeMode,
) Allocator.Error!WipContainerType.Result {
    const gop = try pool.getOrPutContainer(.{ .enum_type = id });
    if (gop.existing) |e| return .{ .existing = e };
    const extra_index = try pool.addExtra(TypeEnum{
        .name = name,
        .namespace = .none,
        .int_tag_type = .none,
        .fields_len = fields_len,
        .field_name_map = .none,
        .field_value_map = .none,
        .captures_len = containerCapturesLen(id),
        .flags = .{ .nonexhaustive = false, .has_values = has_values, .fields_resolved = false, .want_layout = false, .int_tag_mode = int_tag_mode },
    });
    try pool.appendContainerType(id);
    const reserved = fields_len + if (has_values) fields_len else 0;
    try pool.extra.ensureUnusedCapacity(pool.gpa, reserved);
    pool.extra.appendNTimesAssumeCapacity(0, reserved);
    pool.items.appendAssumeCapacity(.{ .tag = .type_enum, .data = extra_index });
    return .{ .wip = .{ .index = @fromBackingInt(@intCast(gop.index)) } };
}

pub fn getReifiedEnumType(pool: *InternPool, ini: struct {
    name: NullTerminatedString,
    id: Key.ContainerType,
    int_tag_type: Index,
    nonexhaustive: bool,
    names: []const NullTerminatedString,
    values: []const Index,
}) Allocator.Error!Index {
    assert(ini.values.len == 0 or ini.values.len == ini.names.len);
    const gop = try pool.getOrPutContainer(.{ .enum_type = ini.id });
    if (gop.existing) |e| return e;
    const fields_len: u32 = @intCast(ini.names.len);
    const has_values = ini.values.len != 0;
    const field_name_map = try pool.addMap(pool.gpa, fields_len);
    const field_value_map: OptionalMapIndex = if (has_values) (try pool.addMap(pool.gpa, fields_len)).toOptional() else .none;
    const extra_index = try pool.addExtra(TypeEnum{
        .name = ini.name,
        .namespace = .none,
        .int_tag_type = ini.int_tag_type,
        .fields_len = fields_len,
        .field_name_map = field_name_map.toOptional(),
        .field_value_map = field_value_map,
        .captures_len = containerCapturesLen(ini.id),
        .flags = .{ .nonexhaustive = ini.nonexhaustive, .has_values = has_values, .fields_resolved = true, .want_layout = false, .int_tag_mode = .explicit },
    });
    try pool.appendContainerType(ini.id);
    try pool.extra.ensureUnusedCapacity(pool.gpa, fields_len + if (has_values) fields_len else 0);
    for (ini.names) |n| pool.extra.appendAssumeCapacity(@backingInt(n));
    if (has_values) for (ini.values) |v| pool.extra.appendAssumeCapacity(@backingInt(v));
    pool.items.appendAssumeCapacity(.{ .tag = .type_enum, .data = extra_index });
    return @fromBackingInt(@intCast(gop.index));
}

pub fn internEnumTag(pool: *InternPool, et: Key.EnumTag) Allocator.Error!Index {
    return pool.get(.{ .enum_tag = et });
}

pub fn getDeclaredUnionType(
    pool: *InternPool,
    name: NullTerminatedString,
    id: Key.ContainerType,
    fields_len: u32,
    layout: std.lang.Type.ContainerLayout,
    any_field_aligns: bool,
    tag_usage: UnionFields.TagUsage,
) Allocator.Error!WipContainerType.Result {
    const gop = try pool.getOrPutContainer(.{ .union_type = id });
    if (gop.existing) |e| return .{ .existing = e };
    const field_name_map = try pool.addMap(pool.gpa, fields_len);
    const extra_index = try pool.addExtra(TypeUnion{
        .name = name,
        .namespace = .none,
        .enum_tag_type = .none,
        .backing_int = .none,
        .fields_len = fields_len,
        .field_name_map = field_name_map.toOptional(),
        .captures_len = containerCapturesLen(id),
        .size = 0,
        .flags = .{
            .layout = switch (layout) {
                .auto => .auto,
                .@"extern" => .@"extern",
                .@"packed" => .@"packed",
            },
            .any_field_aligns = any_field_aligns,
            .want_layout = false,
            .fields_resolved = false,
            .has_runtime_tag = false,
            .class = .no_possible_value,
            .alignment = .none,
            .tag_usage = tag_usage,
        },
    });
    try pool.appendContainerType(id);
    const reserved = fields_len + fields_len + if (any_field_aligns) fields_len else 0;
    try pool.extra.ensureUnusedCapacity(pool.gpa, reserved);
    pool.extra.appendNTimesAssumeCapacity(0, reserved);
    pool.items.appendAssumeCapacity(.{ .tag = .type_union, .data = extra_index });
    return .{ .wip = .{ .index = @fromBackingInt(@intCast(gop.index)) } };
}

pub fn getDeclaredOpaqueType(pool: *InternPool, name: NullTerminatedString, id: Key.ContainerType) Allocator.Error!WipContainerType.Result {
    const gop = try pool.getOrPutContainer(.{ .opaque_type = id });
    if (gop.existing) |e| return .{ .existing = e };
    const extra_index = try pool.addExtra(TypeOpaque{
        .name = name,
        .namespace = .none,
        .captures_len = containerCapturesLen(id),
    });
    try pool.appendContainerType(id);
    pool.items.appendAssumeCapacity(.{ .tag = .type_opaque, .data = extra_index });
    return .{ .wip = .{ .index = @fromBackingInt(@intCast(gop.index)) } };
}

pub fn getReifiedUnionType(pool: *InternPool, ini: struct {
    name: NullTerminatedString,
    id: Key.ContainerType,
    layout: std.lang.Type.ContainerLayout,
    tag_usage: UnionFields.TagUsage,
    enum_tag_type: Index,
    backing_int: Index,
    names: []const NullTerminatedString,
    types: []const Index,
    aligns: []const Alignment,
}) Allocator.Error!Index {
    assert(ini.types.len == ini.names.len);
    assert(ini.aligns.len == 0 or ini.aligns.len == ini.names.len);
    const gop = try pool.getOrPutContainer(.{ .union_type = ini.id });
    if (gop.existing) |e| return e;
    const fields_len: u32 = @intCast(ini.names.len);
    const any_aligns = ini.aligns.len != 0;
    const field_name_map = try pool.addMap(pool.gpa, fields_len);
    const extra_index = try pool.addExtra(TypeUnion{
        .name = ini.name,
        .namespace = .none,
        .enum_tag_type = ini.enum_tag_type,
        .backing_int = ini.backing_int,
        .fields_len = fields_len,
        .field_name_map = field_name_map.toOptional(),
        .captures_len = containerCapturesLen(ini.id),
        .size = 0,
        .flags = .{
            .layout = switch (ini.layout) {
                .auto => .auto,
                .@"extern" => .@"extern",
                .@"packed" => .@"packed",
            },
            .any_field_aligns = any_aligns,
            .want_layout = false,
            .fields_resolved = true,
            .has_runtime_tag = false,
            .class = .no_possible_value,
            .alignment = .none,
            .tag_usage = ini.tag_usage,
        },
    });
    try pool.appendContainerType(ini.id);
    try pool.extra.ensureUnusedCapacity(pool.gpa, fields_len + fields_len + if (any_aligns) fields_len else 0);
    for (ini.names) |n| pool.extra.appendAssumeCapacity(@backingInt(n));
    for (ini.types) |t| pool.extra.appendAssumeCapacity(@backingInt(t));
    if (any_aligns) for (ini.aligns) |a| pool.extra.appendAssumeCapacity(@backingInt(a));
    pool.items.appendAssumeCapacity(.{ .tag = .type_union, .data = extra_index });
    return @fromBackingInt(@intCast(gop.index));
}

pub fn internUnion(pool: *InternPool, uv: Key.Union) Allocator.Error!Index {
    return pool.get(.{ .un = uv });
}

pub fn internBitpack(pool: *InternPool, b: Key.Bitpack) Allocator.Error!Index {
    return pool.get(.{ .bitpack = b });
}

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
    return @backingInt(a) < @backingInt(b);
}

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

pub fn getExtern(pool: *InternPool, e: Key.Extern) Allocator.Error!Index {
    return pool.get(.{ .@"extern" = e });
}

fn emitExtern(pool: *InternPool, e: Key.Extern) Allocator.Error!void {
    assert(e.ty != .none);
    const extra_index = try pool.addExtra(e);
    pool.items.appendAssumeCapacity(.{ .tag = .extern_decl, .data = extra_index });
}

fn externFromExtra(pool: *const InternPool, extra_index: u32) Key {
    return .{ .@"extern" = pool.extraData(Key.Extern, extra_index) };
}

fn emitFuncType(pool: *InternPool, ft: Key.FuncType) Allocator.Error!void {
    assert(ft.return_type != .none);
    assert(ft.param_types.len <= std.math.maxInt(u32));

    const has_comptime_bits = ft.comptime_bits != 0;
    const has_noalias_bits = ft.noalias_bits != 0;
    const packed_cc: PackedCallingConvention = .pack(ft.cc);
    const cc_extra_len = packed_cc.extraLen();
    const flags: FuncTypeRepr.Flags = .{
        .cc = packed_cc,
        .is_var_args = ft.is_var_args,
        .is_noinline = ft.is_noinline,
        .has_comptime_bits = has_comptime_bits,
        .has_noalias_bits = has_noalias_bits,
    };

    const extra_index = try pool.addExtra(FuncTypeRepr{
        .params_len = @intCast(ft.param_types.len),
        .return_type = ft.return_type,
        .flags = flags,
    });
    const opt_slots: u32 = @as(u32, @intFromBool(has_comptime_bits)) +
        @as(u32, @intFromBool(has_noalias_bits));
    try pool.extra.ensureUnusedCapacity(pool.gpa, opt_slots + cc_extra_len + @as(u32, @intCast(ft.param_types.len)));
    if (has_comptime_bits) pool.extra.appendAssumeCapacity(ft.comptime_bits);
    if (has_noalias_bits) pool.extra.appendAssumeCapacity(ft.noalias_bits);
    switch (ft.cc) {
        .spirv_kernel, .spirv_task => |kernel| pool.extra.appendSliceAssumeCapacity(&.{ kernel.x, kernel.y, kernel.z }),
        .spirv_mesh => |mesh| pool.extra.appendSliceAssumeCapacity(&.{ mesh.max_primitives, mesh.max_vertices }),
        else => {},
    }
    for (ft.param_types) |p| pool.extra.appendAssumeCapacity(@backingInt(p));

    pool.items.appendAssumeCapacity(.{ .tag = .type_function, .data = extra_index });
}

fn emitFunc(pool: *InternPool, f: Key.Func) Allocator.Error!void {
    assert(f.ty != .none);
    assert(f.uncoerced_ty != .none);

    if (f.generic_owner != .none) {
        const extra_index = try pool.addExtra(FuncInstanceRepr{
            .source_zir_id = f.source_zir_id,
            .ty = f.ty,
            .generic_owner = f.generic_owner,
            .comptime_args_len = @intCast(f.comptime_args.len),
            .owner_nav = f.owner_nav,
        });
        try pool.extra.ensureUnusedCapacity(pool.gpa, @intCast(f.comptime_args.len));
        for (f.comptime_args) |arg| pool.extra.appendAssumeCapacity(@backingInt(arg));
        pool.items.appendAssumeCapacity(.{ .tag = .func_instance, .data = extra_index });
        return;
    }
    if (f.uncoerced_ty != f.ty) {
        const inner = try pool.internFunc(.{
            .source_zir_id = f.source_zir_id,
            .ty = f.uncoerced_ty,
            .uncoerced_ty = f.uncoerced_ty,
            .zir_body_inst = f.zir_body_inst,
            .parent = f.parent,
            .owner_nav = f.owner_nav,
        });
        const coerced_extra = try pool.addExtra(FuncCoercedRepr{ .ty = f.ty, .inner_func = inner });
        pool.items.appendAssumeCapacity(.{ .tag = .func_coerced, .data = coerced_extra });
        return;
    }
    const extra_index = try pool.addExtra(FuncDeclRepr{
        .source_zir_id = f.source_zir_id,
        .ty = f.ty,
        .zir_body_inst = f.zir_body_inst,
        .parent = f.parent,
        .owner_nav = f.owner_nav,
    });
    pool.items.appendAssumeCapacity(.{ .tag = .func_decl, .data = extra_index });
}

fn funcTypeFromExtra(pool: *const InternPool, extra_index: u32) Key {
    const trail = pool.extraDataTrail(FuncTypeRepr, extra_index);
    const r = trail.data;

    var t: u32 = trail.end;
    const comptime_bits: u32 = if (r.flags.has_comptime_bits) blk: {
        const v = pool.extra.items[t];
        t += 1;
        break :blk v;
    } else 0;
    const noalias_bits: u32 = if (r.flags.has_noalias_bits) blk: {
        const v = pool.extra.items[t];
        t += 1;
        break :blk v;
    } else 0;

    const cc_extra_len = r.flags.cc.extraLen();
    const cc_trailing = pool.extra.items[t..][0..cc_extra_len];
    t += cc_extra_len;
    const cc: std.lang.CallingConvention = r.flags.cc.unpack(cc_trailing);

    assert(t + r.params_len <= pool.extra.items.len);

    const param_slots = pool.extra.items[t..][0..r.params_len];
    const param_types: []const Index = @ptrCast(param_slots);

    return .{ .func_type = .{
        .param_types = param_types,
        .return_type = r.return_type,
        .comptime_bits = comptime_bits,
        .noalias_bits = noalias_bits,
        .cc = cc,
        .is_var_args = r.flags.is_var_args,
        .is_noinline = r.flags.is_noinline,
    } };
}

fn funcDeclFromExtra(pool: *const InternPool, extra_index: u32) Key {
    const r = pool.extraData(FuncDeclRepr, extra_index);
    return .{ .func = .{
        .source_zir_id = r.source_zir_id,
        .ty = r.ty,
        .uncoerced_ty = r.ty,
        .zir_body_inst = r.zir_body_inst,
        .parent = r.parent,
        .owner_nav = r.owner_nav,
    } };
}

fn funcInstanceFromExtra(pool: *const InternPool, extra_index: u32) Key {
    const trail = pool.extraDataTrail(FuncInstanceRepr, extra_index);
    const r = trail.data;
    assert(trail.end + r.comptime_args_len <= pool.extra.items.len);
    const args_slots = pool.extra.items[trail.end..][0..r.comptime_args_len];
    const comptime_args: []const Index = @ptrCast(args_slots);

    const owner_key = pool.indexToKey(r.generic_owner).func;
    return .{ .func = .{
        .source_zir_id = r.source_zir_id,
        .ty = r.ty,
        .uncoerced_ty = r.ty,
        .zir_body_inst = owner_key.zir_body_inst,
        .generic_owner = r.generic_owner,
        .comptime_args = comptime_args,
        .owner_nav = r.owner_nav,
    } };
}

fn funcCoercedFromExtra(pool: *const InternPool, extra_index: u32) Key {
    const r = pool.extraData(FuncCoercedRepr, extra_index);
    const ty = r.ty;
    const inner_index = r.inner_func;
    const inner_tag = pool.items.get(@backingInt(inner_index)).tag;
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
        .owner_nav = inner_key.owner_nav,
    } };
}

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

pub fn typeOf(pool: *const InternPool, val: Index) Index {
    return switch (pool.indexToKey(val)) {
        .simple_value => |sv| switch (sv) {
            .void => .void_type,
            .true, .false => .bool_type,
            .null => .null_type,
            .@"unreachable" => .noreturn_type,
        },
        .int => |iv| iv.ty,
        .float => |fv| fv.ty,
        .undef => |ty| ty,
        .ptr => |p| p.ty,
        .slice => |s| s.ty,
        .err => |e| e.ty,
        .error_union => |eu| eu.ty,
        .func => |f| f.ty,
        .@"extern" => |e| e.ty,
        .opt => |o| o.ty,
        .aggregate => |agg| agg.ty,
        .enum_tag => |et| et.ty,
        .enum_literal => .enum_literal_type,
        .un => |uv| uv.ty,
        .bitpack => |bp| bp.ty,
        else => |k| blk: {
            assert(k.isType());
            break :blk .type_type;
        },
    };
}

pub fn isOptionalType(pool: *const InternPool, ty: Index) bool {
    return pool.indexToKey(ty) == .opt_type;
}

pub fn isPointerType(pool: *const InternPool, ty: Index) bool {
    return pool.indexToKey(ty) == .ptr_type;
}

pub fn isErrorSetType(pool: *const InternPool, ty: Index) bool {
    return switch (ty) {
        .anyerror_type, .adhoc_inferred_error_set_type => true,
        else => pool.indexToKey(ty) == .error_set_type,
    };
}

pub fn isErrorUnionType(pool: *const InternPool, ty: Index) bool {
    return pool.indexToKey(ty) == .error_union_type;
}

pub fn slicePtrType(pool: *InternPool, index: Index) Allocator.Error!Index {
    const p = pool.indexToKey(index).ptr_type;
    var flags = p.flags;
    flags.size = .many;
    return pool.internPtrType(.{ .child = p.child, .sentinel = p.sentinel, .flags = flags, .packed_offset = p.packed_offset });
}

pub fn getCoercedInts(pool: *InternPool, int: Key.Int, new_ty: Index) Allocator.Error!Index {
    return pool.get(.{ .int = .{ .ty = new_ty, .storage = int.storage } });
}

/// The base-address tag reached by following a pointer value through its bases, or null if `val`
/// is not a pointer. Ported from the compiler's `getBackingAddrTag`.
pub fn getBackingAddrTag(pool: *const InternPool, val: Index) ?@typeInfo(Key.Ptr.BaseAddr).@"union".tag_type.? {
    var base = val;
    while (true) {
        switch (pool.indexToKey(base)) {
            .ptr => |ptr| switch (ptr.base_addr) {
                .nav => return .nav,
                .comptime_alloc => return .comptime_alloc,
                .uav => return .uav,
                .comptime_field => return .comptime_field,
                .int => return .int,
                .eu_payload, .opt_payload => |b| base = b,
                .field, .arr_elem => |f| base = f.base,
            },
            .slice => |s| base = s.ptr,
            else => return null,
        }
    }
}

pub fn getCoerced(pool: *InternPool, val: Index, new_ty: Index) Allocator.Error!Index {
    const old_ty = pool.typeOf(val);
    if (old_ty == new_ty) return val;

    switch (val) {
        .undef => return pool.get(.{ .undef = new_ty }),
        .null_value => {
            if (pool.isOptionalType(new_ty)) return pool.get(.{ .opt = .{ .ty = new_ty, .val = .none } });
            if (pool.isPointerType(new_ty)) switch (pool.indexToKey(new_ty).ptr_type.flags.size) {
                .one, .many, .c => return pool.get(.{ .ptr = .{ .ty = new_ty, .base_addr = .int, .byte_offset = 0 } }),
                .slice => return pool.get(.{ .slice = .{
                    .ty = new_ty,
                    .ptr = try pool.get(.{ .ptr = .{ .ty = try pool.slicePtrType(new_ty), .base_addr = .int, .byte_offset = 0 } }),
                    .len = .undef_usize,
                } }),
            };
        },
        else => {},
    }

    switch (pool.indexToKey(val)) {
        .undef => return pool.get(.{ .undef = new_ty }),
        .func => unreachable,

        .int => |int| switch (pool.indexToKey(new_ty)) {
            .enum_type => return pool.get(.{ .enum_tag = .{
                .ty = new_ty,
                .int = try pool.getCoerced(val, pool.loadEnumType(new_ty).int_tag_type),
            } }),
            .ptr_type => switch (int.storage) {
                inline .u64, .i64 => |int_val| return pool.get(.{ .ptr = .{ .ty = new_ty, .base_addr = .int, .byte_offset = @intCast(int_val) } }),
                .big_int => unreachable,
            },
            else => if (pool.isIntegerType(new_ty)) return pool.getCoercedInts(int, new_ty),
        },
        .float => |float| switch (pool.indexToKey(new_ty)) {
            .simple_type => |simple| switch (simple) {
                .f16, .f32, .f64, .f80, .f128, .c_longdouble, .comptime_float => return pool.get(.{ .float = .{ .ty = new_ty, .storage = float.storage } }),
                else => {},
            },
            else => {},
        },
        .enum_tag => |enum_tag| if (pool.isIntegerType(new_ty)) return pool.getCoercedInts(pool.indexToKey(enum_tag.int).int, new_ty),
        .enum_literal => |enum_literal| switch (pool.indexToKey(new_ty)) {
            .enum_type => {
                const enum_type = pool.loadEnumType(new_ty);
                const index = enum_type.nameIndex(pool, enum_literal).?;
                return pool.get(.{ .enum_tag = .{
                    .ty = new_ty,
                    .int = if (enum_type.field_values.len != 0)
                        enum_type.field_values[index]
                    else
                        try pool.get(.{ .int = .{ .ty = enum_type.int_tag_type, .storage = .{ .u64 = index } } }),
                } });
            },
            else => {},
        },
        .slice => |slice| if (pool.isPointerType(new_ty) and pool.indexToKey(new_ty).ptr_type.flags.size == .slice)
            return pool.get(.{ .slice = .{
                .ty = new_ty,
                .ptr = try pool.getCoerced(slice.ptr, try pool.slicePtrType(new_ty)),
                .len = slice.len,
            } })
        else if (pool.isIntegerType(new_ty))
            return pool.getCoerced(slice.ptr, new_ty),
        .ptr => |ptr| if (pool.isPointerType(new_ty) and pool.indexToKey(new_ty).ptr_type.flags.size != .slice)
            return pool.get(.{ .ptr = .{ .ty = new_ty, .base_addr = ptr.base_addr, .byte_offset = ptr.byte_offset } })
        else if (pool.isIntegerType(new_ty)) switch (ptr.base_addr) {
            .int => return pool.get(.{ .int = .{ .ty = .usize_type, .storage = .{ .u64 = @intCast(ptr.byte_offset) } } }),
            else => {},
        },
        .opt => |opt| switch (pool.indexToKey(new_ty)) {
            .ptr_type => |ptr_type| return switch (opt.val) {
                .none => switch (ptr_type.flags.size) {
                    .one, .many, .c => try pool.get(.{ .ptr = .{ .ty = new_ty, .base_addr = .int, .byte_offset = 0 } }),
                    .slice => try pool.get(.{ .slice = .{
                        .ty = new_ty,
                        .ptr = try pool.get(.{ .ptr = .{ .ty = try pool.slicePtrType(new_ty), .base_addr = .int, .byte_offset = 0 } }),
                        .len = .undef_usize,
                    } }),
                },
                else => try pool.getCoerced(opt.val, new_ty),
            },
            .opt_type => |child_type| return pool.get(.{ .opt = .{
                .ty = new_ty,
                .val = switch (opt.val) {
                    .none => .none,
                    else => try pool.getCoerced(opt.val, child_type),
                },
            } }),
            else => {},
        },
        .err => |err| if (pool.isErrorSetType(new_ty))
            return pool.get(.{ .err = .{ .ty = new_ty, .name = err.name } })
        else if (pool.isErrorUnionType(new_ty))
            return pool.get(.{ .error_union = .{ .ty = new_ty, .val = .{ .err_name = err.name } } }),
        .error_union => |error_union| if (pool.isErrorUnionType(new_ty))
            return pool.get(.{ .error_union = .{ .ty = new_ty, .val = error_union.val } }),
        .aggregate => |aggregate| {
            const new_len: usize = @intCast(pool.aggregateElementCount(new_ty));
            direct: {
                const old_ty_child = switch (pool.indexToKey(old_ty)) {
                    inline .array_type, .vector_type => |seq_type| seq_type.child,
                    .tuple_type, .struct_type => break :direct,
                    else => unreachable,
                };
                const new_ty_child = switch (pool.indexToKey(new_ty)) {
                    inline .array_type, .vector_type => |seq_type| seq_type.child,
                    .tuple_type, .struct_type => break :direct,
                    else => unreachable,
                };
                if (old_ty_child != new_ty_child) break :direct;
                switch (aggregate.storage) {
                    .bytes => |bytes| return pool.get(.{ .aggregate = .{ .ty = new_ty, .storage = .{ .bytes = bytes } } }),
                    .elems => |elems| {
                        const elems_copy = try pool.gpa.dupe(Index, elems[0..new_len]);
                        defer pool.gpa.free(elems_copy);
                        return pool.get(.{ .aggregate = .{ .ty = new_ty, .storage = .{ .elems = elems_copy } } });
                    },
                    .repeated_elem => |elem| return pool.get(.{ .aggregate = .{ .ty = new_ty, .storage = .{ .repeated_elem = elem } } }),
                }
            }
            const agg_elems = try pool.gpa.alloc(Index, new_len);
            defer pool.gpa.free(agg_elems);
            switch (aggregate.storage) {
                .bytes => |bytes| for (agg_elems, 0..) |*elem, index| {
                    elem.* = try pool.get(.{ .int = .{ .ty = .u8_type, .storage = .{ .u64 = bytes.at(index, pool) } } });
                },
                .elems => |elems| @memcpy(agg_elems, elems[0..new_len]),
                .repeated_elem => |elem| @memset(agg_elems, elem),
            }
            for (agg_elems, 0..) |*elem, i| {
                const new_elem_ty = switch (pool.indexToKey(new_ty)) {
                    inline .array_type, .vector_type => |seq_type| seq_type.child,
                    .tuple_type => |tuple_type| tuple_type.types[i],
                    .struct_type => pool.loadStructType(new_ty).field_types[i],
                    else => unreachable,
                };
                elem.* = try pool.getCoerced(elem.*, new_elem_ty);
            }
            return pool.get(.{ .aggregate = .{ .ty = new_ty, .storage = .{ .elems = agg_elems } } });
        },
        else => {},
    }

    switch (pool.indexToKey(new_ty)) {
        .opt_type => |child_type| switch (val) {
            .null_value => return pool.get(.{ .opt = .{ .ty = new_ty, .val = .none } }),
            else => return pool.get(.{ .opt = .{ .ty = new_ty, .val = try pool.getCoerced(val, child_type) } }),
        },
        .error_union_type => |error_union_type| return pool.get(.{ .error_union = .{
            .ty = new_ty,
            .val = .{ .payload = try pool.getCoerced(val, error_union_type.payload_type) },
        } }),
        else => {},
    }
    std.debug.panic("InternPool.getCoerced of {s} not implemented from {s} to {s}", .{
        @tagName(pool.indexToKey(val)),
        @tagName(pool.indexToKey(old_ty)),
        @tagName(pool.indexToKey(new_ty)),
    });
}

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
    assert(buf_end >= buf_start);

    const slice_start = @intFromPtr(limbs.ptr);
    return slice_start >= buf_start and slice_start < buf_end;
}

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

    const header: IntBigHeader = .{ .ty = @backingInt(ty), .limbs_len = @intCast(limbs.len) };
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

    const items_before = pool.itemCount();
    const signed_zero_idx = try pool.internIntType(.signed, 0);
    try std.testing.expect(@backingInt(signed_zero_idx) >= first_dynamic_index);
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

    var big_src = [_]std.math.big.Limb{ 0, 1 };
    const a_idx = try pool.internIntValue(.u128_type, .{ .limbs = &big_src, .positive = true });

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

    const untyped = pool.indexToKey(.undef).undef;
    try std.testing.expectEqual(Index.undefined_type, untyped);

    const round = try pool.get(.{ .undef = .undefined_type });
    try std.testing.expectEqual(Index.undef, round);

    const u32_undef = try pool.get(.{ .undef = .u32_type });
    try std.testing.expect(u32_undef != .undef);
    try std.testing.expectEqual(Index.u32_type, pool.indexToKey(u32_undef).undef);
}

test "interning identical keys dedups to a single Index" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    const items_before = pool.itemCount();
    const u17_a = try pool.internIntType(.unsigned, 17);
    const u17_b = try pool.internIntType(.unsigned, 17);
    try std.testing.expectEqual(u17_a, u17_b);
    try std.testing.expectEqual(items_before + 1, pool.itemCount());

    var limb = [_]std.math.big.Limb{5};
    const big5: BigIntConst = .{ .limbs = &limb, .positive = true };
    const a = try pool.internInt(.{ .ty = .comptime_int_type, .storage = .{ .u64 = 5 } });
    const b = try pool.internInt(.{ .ty = .comptime_int_type, .storage = .{ .big_int = big5 } });
    try std.testing.expectEqual(a, b);

    const zero_again = try pool.internInt(.{ .ty = .comptime_int_type, .storage = .{ .u64 = 0 } });
    try std.testing.expectEqual(Index.zero, zero_again);
}

test "big comptime int round-trips through int_positive limbs" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

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
        .base_addr = .{ .comptime_alloc = @fromBackingInt(@intCast(7)) },
        .byte_offset = 16,
    });
    const round = pool.indexToKey(p0).ptr;
    try std.testing.expectEqual(ptr_ty, round.ty);
    try std.testing.expectEqual(@as(u64, 16), round.byte_offset);
    try std.testing.expectEqual(@as(Key.ComptimeAllocIndex, @fromBackingInt(@intCast(7))), round.base_addr.comptime_alloc);

    const p_dup = try pool.internPtr(.{
        .ty = ptr_ty,
        .base_addr = .{ .comptime_alloc = @fromBackingInt(@intCast(7)) },
        .byte_offset = 16,
    });
    try std.testing.expectEqual(p0, p_dup);
    try std.testing.expectEqual(items_before + 1, pool.itemCount());

    const p_other_offset = try pool.internPtr(.{
        .ty = ptr_ty,
        .base_addr = .{ .comptime_alloc = @fromBackingInt(@intCast(7)) },
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
        .base_addr = .{ .comptime_alloc = @fromBackingInt(@intCast(0)) },
        .byte_offset = huge,
    });
    try std.testing.expectEqual(huge, pool.indexToKey(p).ptr.byte_offset);
}

test "string interning: empty handle is the well-known sentinel" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    try std.testing.expectEqual(NullTerminatedString.empty, try pool.getOrPutString(pool.gpa, "", .no_embedded_nulls));
    try std.testing.expectEqualStrings("", pool.stringSlice(.empty));
}

test "string interning: round-trip a single name" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    const handle = try pool.getOrPutString(pool.gpa, "decl_name", .no_embedded_nulls);
    try std.testing.expectEqualStrings("decl_name", pool.stringSlice(handle));
}

test "string interning: identical bytes dedup to the same handle" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    const first = try pool.getOrPutString(pool.gpa, "x", .no_embedded_nulls);
    const second = try pool.getOrPutString(pool.gpa, "x", .no_embedded_nulls);
    try std.testing.expectEqual(first, second);

    const bytes_after_first = pool.string_bytes.items.len;
    _ = try pool.getOrPutString(pool.gpa, "x", .no_embedded_nulls);
    try std.testing.expectEqual(bytes_after_first, pool.string_bytes.items.len);
}

test "string interning: distinct names occupy distinct handles" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    const foo = try pool.getOrPutString(pool.gpa, "foo", .no_embedded_nulls);
    const bar = try pool.getOrPutString(pool.gpa, "bar", .no_embedded_nulls);
    try std.testing.expect(foo != bar);
    try std.testing.expectEqualStrings("foo", pool.stringSlice(foo));
    try std.testing.expectEqualStrings("bar", pool.stringSlice(bar));
}

test "string interning: OptionalNullTerminatedString round-trips" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    const handle = try pool.getOrPutString(pool.gpa, "thing", .no_embedded_nulls);
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
    for (names, &handles) |name, *out| out.* = try pool.getOrPutString(pool.gpa, name, .no_embedded_nulls);

    for (handles, names) |handle, expected| {
        try std.testing.expectEqualStrings(expected, pool.stringSlice(handle));
    }

    try std.testing.expectEqual(handles[2], try pool.getOrPutString(pool.gpa, "gamma", .no_embedded_nulls));
    try std.testing.expectEqual(handles[0], try pool.getOrPutString(pool.gpa, "alpha", .no_embedded_nulls));
    try std.testing.expectEqual(handles[4], try pool.getOrPutString(pool.gpa, "epsilon", .no_embedded_nulls));
}

test "Nav: createNav appends with analysis = null and resolved = null" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    const name = try pool.getOrPutString(pool.gpa, "foo", .no_embedded_nulls);
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

    const name = try pool.getOrPutString(pool.gpa, "answer", .no_embedded_nulls);
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

    const name = try pool.getOrPutString(pool.gpa, "x", .no_embedded_nulls);
    const first = try pool.createNav(pool.gpa, name, name);
    const second = try pool.createNav(pool.gpa, name, name);
    try std.testing.expect(first != second);
    try std.testing.expectEqual(name, pool.getNav(first).name);
    try std.testing.expectEqual(name, pool.getNav(second).name);
}

test "Namespace: createNamespace seeds an empty parent-less scope" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    const ns_idx = try pool.createNamespace(pool.gpa, .{});
    const ns = pool.namespacePtr(ns_idx);

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

    const ns = try pool.createNamespace(pool.gpa, .{});
    const name = try pool.getOrPutString(pool.gpa, "P", .no_embedded_nulls);
    const fqn = try pool.fullyQualifiedName(pool.gpa, ns, name);
    try std.testing.expectEqualStrings("repl.P", pool.stringSlice(fqn));
}

test "fullyQualifiedName: a member of a named container nests under it" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    const outer = (try pool.getDeclaredStructType(
        try pool.getOrPutString(pool.gpa, "repl.Outer", .no_embedded_nulls),
        .{ .declared = .{ .source_zir_id = 0, .decl_inst = @fromBackingInt(@intCast(1)) } },
        0,
        .auto,
        false,
        false,
    )).wip.index;
    const ns = try pool.createNamespace(pool.gpa, .{});
    pool.namespacePtr(ns).owner_type = outer;

    const inner = try pool.getOrPutString(pool.gpa, "Inner", .no_embedded_nulls);
    const fqn = try pool.fullyQualifiedName(pool.gpa, ns, inner);
    try std.testing.expectEqualStrings("repl.Outer.Inner", pool.stringSlice(fqn));
}

test "Namespace: NavNameContext dedups Nav.Index entries by interned name" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    const x = try pool.getOrPutString(pool.gpa, "x", .no_embedded_nulls);
    const y = try pool.getOrPutString(pool.gpa, "y", .no_embedded_nulls);
    const first_x = try pool.createNav(pool.gpa, x, x);
    const second_x = try pool.createNav(pool.gpa, x, x);
    const just_y = try pool.createNav(pool.gpa, y, y);

    const ns_idx = try pool.createNamespace(pool.gpa, .{});
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

    const x = try pool.getOrPutString(pool.gpa, "x", .no_embedded_nulls);
    const nav_x = try pool.createNav(pool.gpa, x, x);

    const ns_idx = try pool.createNamespace(pool.gpa, .{});
    const ns = pool.namespacePtr(ns_idx);
    const ctx: Namespace.NavNameContext = .{ .pool = &pool };
    _ = try ns.pub_decls.getOrPutContext(pool.gpa, nav_x, ctx);

    const adapter: Namespace.NameAdapter = .{ .pool = &pool };
    const found_x = ns.pub_decls.getKeyAdapted(x, adapter);
    try std.testing.expectEqual(@as(?Nav.Index, nav_x), found_x);

    const missing = try pool.getOrPutString(pool.gpa, "missing", .no_embedded_nulls);
    try std.testing.expectEqual(@as(?Nav.Index, null), ns.pub_decls.getKeyAdapted(missing, adapter));
}

test "Namespace.lookupNav: walks pub_decls then priv_decls, no parent chain" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    const x = try pool.getOrPutString(pool.gpa, "x", .no_embedded_nulls);
    const y = try pool.getOrPutString(pool.gpa, "y", .no_embedded_nulls);
    const missing = try pool.getOrPutString(pool.gpa, "z", .no_embedded_nulls);
    const nav_x = try pool.createNav(pool.gpa, x, x);
    const nav_y = try pool.createNav(pool.gpa, y, y);

    const ns_idx = try pool.createNamespace(pool.gpa, .{});
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

    const x = try pool.getOrPutString(pool.gpa, "x", .no_embedded_nulls);
    const nav_pub = try pool.createNav(pool.gpa, x, x);
    const nav_priv = try pool.createNav(pool.gpa, x, x);

    const ns_idx = try pool.createNamespace(pool.gpa, .{});
    const ns = pool.namespacePtr(ns_idx);
    const ctx: Namespace.NavNameContext = .{ .pool = &pool };

    _ = try ns.priv_decls.getOrPutContext(pool.gpa, nav_priv, ctx);
    _ = try ns.pub_decls.getOrPutContext(pool.gpa, nav_pub, ctx);
    try std.testing.expectEqual(@as(?Nav.Index, nav_pub), ns.lookupNav(&pool, x));
}

test "error_set_type: round-trip + sort discipline" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    const foo = try pool.getOrPutString(pool.gpa, "Foo", .no_embedded_nulls);
    const bar = try pool.getOrPutString(pool.gpa, "Bar", .no_embedded_nulls);
    const baz = try pool.getOrPutString(pool.gpa, "Baz", .no_embedded_nulls);

    const idx_a = try pool.internErrorSetType(&.{ baz, foo, bar });
    const idx_b = try pool.internErrorSetType(&.{ foo, bar, baz });
    try std.testing.expectEqual(idx_a, idx_b);

    const round = pool.indexToKey(idx_a).error_set_type;
    try std.testing.expectEqual(@as(usize, 3), round.names.len);
    try std.testing.expect(@backingInt(round.names[0]) <= @backingInt(round.names[1]));
    try std.testing.expect(@backingInt(round.names[1]) <= @backingInt(round.names[2]));
}

test "error_set_type: distinct membership produces distinct indices" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    const foo = try pool.getOrPutString(pool.gpa, "Foo", .no_embedded_nulls);
    const bar = try pool.getOrPutString(pool.gpa, "Bar", .no_embedded_nulls);
    const baz = try pool.getOrPutString(pool.gpa, "Baz", .no_embedded_nulls);

    const fb = try pool.internErrorSetType(&.{ foo, bar });
    const fz = try pool.internErrorSetType(&.{ foo, baz });
    try std.testing.expect(fb != fz);
}

test "singletonErrorSetType: one-name set round-trips" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    const foo = try pool.getOrPutString(pool.gpa, "Foo", .no_embedded_nulls);
    const idx = try pool.singletonErrorSetType(foo);

    const round = pool.indexToKey(idx).error_set_type;
    try std.testing.expectEqual(@as(usize, 1), round.names.len);
    try std.testing.expectEqual(foo, round.names[0]);
}

test "internErr: same {ty, name} dedups" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    const foo = try pool.getOrPutString(pool.gpa, "Foo", .no_embedded_nulls);
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

    const bad = try pool.getOrPutString(pool.gpa, "Bad", .no_embedded_nulls);
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

    const bad = try pool.getOrPutString(pool.gpa, "Bad", .no_embedded_nulls);
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
        .comptime_bits = 0b10,
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
    const body_inst: std.zig.Zir.Inst.Index = @fromBackingInt(@intCast(42));

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

    const a = try pool.internFunc(.{ .ty = fn_ty, .uncoerced_ty = fn_ty, .zir_body_inst = @fromBackingInt(@intCast(1)) });
    const b = try pool.internFunc(.{ .ty = fn_ty, .uncoerced_ty = fn_ty, .zir_body_inst = @fromBackingInt(@intCast(2)) });
    try std.testing.expect(a != b);
}

test "func_coerced: ty != uncoerced_ty routes through Tag.func_coerced" {
    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    const params = [_]Index{};
    const ty_void = try pool.internFuncType(.{ .param_types = &params, .return_type = .void_type });
    const ty_u32 = try pool.internFuncType(.{ .param_types = &params, .return_type = .u32_type });

    const body_inst: std.zig.Zir.Inst.Index = @fromBackingInt(@intCast(7));
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

    const ns_idx = try pool.createNamespace(pool.gpa, .{});
    const zir_inst: std.zig.Zir.Inst.Index = @fromBackingInt(@intCast(42));
    const id = try pool.createComptimeUnit(pool.gpa, ns_idx, zir_inst);

    const unit = pool.getComptimeUnit(id);
    try std.testing.expectEqual(zir_inst, unit.zir_index);
    try std.testing.expectEqual(ns_idx, unit.namespace);
}
