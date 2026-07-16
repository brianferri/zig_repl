//! Thin newtype over `InternPool.Index` that names "this index refers to a
//! type". The pool itself enforces shape; this wrapper only documents intent
//! and gives type-related helpers a place to live.

const std = @import("std");
const builtin = @import("builtin");
const assert = std.debug.assert;

const InternPool = @import("InternPool.zig");
const Sema = @import("Sema.zig");
const Value = @import("Value.zig");

const Type = @This();

index: InternPool.Index,

pub fn minInt(ty: Type, sema: *Sema, dest_ty: Type) !Value {
    const pool = sema.intern_pool;
    const scalar = try minIntScalar(ty.scalarType(pool), sema, dest_ty.scalarType(pool));
    return if (ty.zigTypeTag(pool) == .vector) sema.aggregateSplatValue(dest_ty, scalar) else scalar;
}

pub fn minIntScalar(ty: Type, sema: *Sema, dest_ty: Type) !Value {
    const info = ty.intInfo(sema.intern_pool).?;
    if (info.signedness == .unsigned) return sema.intValue_u64(dest_ty, 0);
    if (std.math.cast(u6, info.bits - 1)) |shift| {
        const n = @as(i64, std.math.minInt(i64)) >> (63 - shift);
        return sema.intValue_i64(dest_ty, n);
    }
    var res = try std.math.big.int.Managed.init(sema.gpa);
    defer res.deinit();
    try res.setTwosCompIntLimit(.min, info.signedness, info.bits);
    return sema.intValue_big(dest_ty, res.toConst());
}

pub fn maxInt(ty: Type, sema: *Sema, dest_ty: Type) !Value {
    const pool = sema.intern_pool;
    const scalar = try maxIntScalar(ty.scalarType(pool), sema, dest_ty.scalarType(pool));
    return if (ty.zigTypeTag(pool) == .vector) sema.aggregateSplatValue(dest_ty, scalar) else scalar;
}

pub fn maxIntScalar(ty: Type, sema: *Sema, dest_ty: Type) !Value {
    const info = ty.intInfo(sema.intern_pool).?;
    switch (info.bits) {
        0 => return sema.intValue_u64(dest_ty, 0),
        1 => return switch (info.signedness) {
            .signed => sema.intValue_u64(dest_ty, 0),
            .unsigned => sema.intValue_u64(dest_ty, 1),
        },
        else => {},
    }
    if (std.math.cast(u6, info.bits - 1)) |shift| switch (info.signedness) {
        .signed => {
            const n = @as(i64, std.math.maxInt(i64)) >> (63 - shift);
            return sema.intValue_i64(dest_ty, n);
        },
        .unsigned => {
            const n = @as(u64, std.math.maxInt(u64)) >> (63 - shift);
            return sema.intValue_u64(dest_ty, n);
        },
    };
    var res = try std.math.big.int.Managed.init(sema.gpa);
    defer res.deinit();
    try res.setTwosCompIntLimit(.max, info.signedness, info.bits);
    return sema.intValue_big(dest_ty, res.toConst());
}

/// The single value inhabiting `ty`, or `null` if it has zero or many. Ports the
/// compiler's `Type.onePossibleValue` (`src/Type.zig`). Takes `sema` (like
/// `minInt`/`maxInt`) because the aggregate arms recurse through this evaluator's
/// field resolvers; the compiler reaches equivalent stored fields through public
/// `loadStructType`. The `one_possible_value` classification the compiler caches on
/// the type is computed on demand here by field recursion.
pub fn onePossibleValue(ty: Type, sema: *Sema) Sema.Error!?Value {
    const ip = sema.intern_pool;
    return switch (ip.indexToKey(ty.index)) {
        .ptr_type,
        .error_union_type,
        .func_type,
        .anyframe_type,
        .error_set_type,
        .opaque_type,
        => null,

        .simple_type => |t| switch (t) {
            .f16,
            .f32,
            .f64,
            .f80,
            .f128,
            .usize,
            .isize,
            .c_char,
            .c_short,
            .c_ushort,
            .c_int,
            .c_uint,
            .c_long,
            .c_ulong,
            .c_longlong,
            .c_ulonglong,
            .c_longdouble,
            .anyopaque,
            .bool,
            .type,
            .anyerror,
            .comptime_int,
            .comptime_float,
            .enum_literal,
            .adhoc_inferred_error_set,
            .null,
            .undefined,
            .noreturn,
            => null,

            .void => Value.void_value,

            .generic_poison => unreachable,
        },
        .int_type => |int_type| if (int_type.bits == 0) try sema.intValue_u64(ty, 0) else null,
        .array_type => |arr| {
            const has_sentinel = arr.sentinel != .none;
            if (arr.len + @intFromBool(has_sentinel) == 0) return try sema.aggregateValue(ty, &.{});
            if (try Type.fromIndex(arr.child).onePossibleValue(sema)) |opv| return try sema.aggregateSplatValue(ty, opv);
            return null;
        },
        .vector_type => |vec| {
            if (vec.len == 0) return try sema.aggregateValue(ty, &.{});
            if (try Type.fromIndex(vec.child).onePossibleValue(sema)) |opv| return try sema.aggregateSplatValue(ty, opv);
            return null;
        },
        .opt_type => |child| if (try sema.isNoPossibleValue(child))
            .{ .index = try ip.internOpt(.{ .ty = ty.index, .val = .none }) }
        else
            null,
        .enum_type => if (try Type.fromIndex(try sema.enumIntTagTypeOf(ty.index)).onePossibleValue(sema)) |int_tag_opv|
            .{ .index = try ip.internEnumTag(.{ .ty = ty.index, .int = int_tag_opv.index }) }
        else
            null,
        .tuple_type => |tuple| {
            const field_vals = try sema.arena.alloc(InternPool.Index, tuple.types.len);
            for (field_vals, tuple.types) |*field_val, field_ty| {
                field_val.* = ((try Type.fromIndex(field_ty).onePossibleValue(sema)) orelse return null).index;
            }
            return try sema.aggregateValue(ty, field_vals);
        },
        .struct_type => {
            const count = try sema.structFieldCount(ty.index);
            const field_vals = try sema.arena.alloc(InternPool.Index, count);
            for (field_vals, 0..) |*field_val, i| {
                const name = (try sema.structFieldNameAt(ty.index, @intCast(i))).?;
                const field = (try sema.structFieldByName(ty.index, name)).?;
                if (field.is_comptime) {
                    const default = try sema.structFieldDefault(ty.index, name);
                    assert(default != .none);
                    field_val.* = default;
                    continue;
                }
                field_val.* = ((try Type.fromIndex(field.ty).onePossibleValue(sema)) orelse return null).index;
            }
            return try sema.aggregateValue(ty, field_vals);
        },
        .union_type => {
            // The OPV comes from exactly one field whose type is OPV, all others NPV.
            const count = try sema.unionFieldCount(ty.index);
            var opv_index: ?u32 = null;
            var i: u32 = 0;
            while (i < count) : (i += 1) {
                const name = (try sema.unionFieldNameAt(ty.index, i)).?;
                const field_ty = (try sema.unionFieldByName(ty.index, name)).?.ty;
                if (try sema.isNoPossibleValue(field_ty)) continue;
                if (opv_index != null) return null; // more than one inhabitable field
                opv_index = i;
            }
            const field_index = opv_index orelse return null; // all fields NPV
            const name = (try sema.unionFieldNameAt(ty.index, field_index)).?;
            const field_ty = (try sema.unionFieldByName(ty.index, name)).?.ty;
            const payload = (try Type.fromIndex(field_ty).onePossibleValue(sema)) orelse return null;
            const tag_val = (try sema.enumValueFieldIndex(try sema.unionTagEnumType(ty.index), field_index)).?;
            return .{ .index = try ip.internUnion(.{ .ty = ty.index, .tag = tag_val.index, .val = payload.index }) };
        },

        // values, not types
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
        .opt,
        .aggregate,
        .enum_tag,
        .un,
        => unreachable,
    };
}

/// Ports the compiler's `Type.classify`: how a type's values split between comptime
/// and runtime state. A container's class is read from its resolved layout, so the
/// caller resolves it first (`ensureLayoutResolved`). Forced REPL deviations: no
/// `assertUpToDate` (single-shot, no dependency graph); the absent `spirv_type` and
/// `inferred_error_set_type` Key variants are not enumerated; a tuple stores no
/// per-field comptime values so `classifyTuple` classifies types only; union layout
/// is not modelled, so a union is `unreachable` here (a union field is rejected by
/// `abiAlignment` before layout resolution).
pub fn classify(start_ty: Type, pool: *const InternPool) InternPool.TypeClass {
    var extra_states: enum { none, one, many } = .none;
    var cur_ty = start_ty;
    const base: InternPool.TypeClass = while (true) break switch (pool.indexToKey(cur_ty.index)) {
        .simple_type => |t| switch (t) {
            .f16,
            .f32,
            .f64,
            .f80,
            .f128,
            .usize,
            .isize,
            .c_char,
            .c_short,
            .c_ushort,
            .c_int,
            .c_uint,
            .c_long,
            .c_ulong,
            .c_longlong,
            .c_ulonglong,
            .c_longdouble,
            .bool,
            .anyerror,
            .adhoc_inferred_error_set,
            => .runtime,

            .anyopaque => .no_possible_value,

            .type,
            .comptime_int,
            .comptime_float,
            .enum_literal,
            .null,
            .undefined,
            => .fully_comptime,

            .void => .one_possible_value,
            .noreturn => .no_possible_value,

            .generic_poison => unreachable,
        },

        .error_set_type,
        .ptr_type,
        .anyframe_type,
        => .runtime,

        .func_type => .fully_comptime,

        .opaque_type => .no_possible_value,

        .error_union_type => |eu| {
            extra_states = .many;
            cur_ty = fromIndex(eu.payload_type);
            continue;
        },

        .int_type => |int| switch (int.bits) {
            0 => .one_possible_value,
            else => .runtime,
        },
        .array_type => |arr| {
            if (arr.len == 0 and arr.sentinel == .none) break .one_possible_value;
            cur_ty = fromIndex(arr.child);
            continue;
        },
        .vector_type => |vec| {
            if (vec.len == 0) break .one_possible_value;
            cur_ty = fromIndex(vec.child);
            continue;
        },
        .opt_type => |child_ty| {
            extra_states = switch (extra_states) {
                .none => .one,
                .one, .many => .many,
            };
            cur_ty = fromIndex(child_ty);
            continue;
        },
        .tuple_type => |tuple| break classifyTuple(tuple.types, pool),
        .struct_type => break pool.loadStructType(cur_ty.index).?.class,
        .union_type => break pool.unionFields(cur_ty.index).?.class,
        .enum_type => {
            cur_ty = fromIndex(pool.loadEnumType(cur_ty.index).?.int_tag_type);
            continue;
        },

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
        .opt,
        .aggregate,
        .enum_tag,
        .un,
        => unreachable,
    };

    return switch (base) {
        .runtime => .runtime,
        .partially_comptime => .partially_comptime,
        .fully_comptime => .fully_comptime,
        .no_possible_value => switch (extra_states) {
            .none => .no_possible_value,
            .one => .one_possible_value,
            .many => .runtime,
        },
        .one_possible_value => switch (extra_states) {
            .none => .one_possible_value,
            .one, .many => .runtime,
        },
    };
}

/// Ports the compiler's `classifyTuple`. The REPL's tuple type stores no per-field
/// comptime values, so every field is a runtime slot (a comptime tuple field is a
/// forced gap).
fn classifyTuple(types: []const InternPool.Index, pool: *const InternPool) InternPool.TypeClass {
    var has_runtime_state = false;
    var has_comptime_state = false;
    for (types) |field_ty| {
        switch (fromIndex(field_ty).classify(pool)) {
            .no_possible_value => return .no_possible_value,
            .one_possible_value => {},
            .runtime => has_runtime_state = true,
            .fully_comptime => has_comptime_state = true,
            .partially_comptime => {
                has_runtime_state = true;
                has_comptime_state = true;
            },
        }
    }
    if (has_comptime_state) {
        return if (has_runtime_state) .partially_comptime else .fully_comptime;
    } else {
        return if (has_runtime_state) .runtime else .one_possible_value;
    }
}

/// Byte offset of struct field `index`, read from the resolved layout (the caller
/// runs `ensureLayoutResolved` first). Mirrors the compiler's `Type.structFieldOffset`
/// for a non-packed struct.
pub fn structFieldOffset(ty: Type, pool: *const InternPool, index: u32) u64 {
    return pool.loadStructType(ty.index).?.field_offsets[index];
}

pub fn fromIndex(index: InternPool.Index) Type {
    assert(index != .none);
    return .{ .index = index };
}

pub fn toIndex(ty: Type) InternPool.Index {
    return ty.index;
}

pub const void_type: Type = .{ .index = .void_type };
pub const bool_type: Type = .{ .index = .bool_type };
pub const type_type: Type = .{ .index = .type_type };
pub const comptime_int_type: Type = .{ .index = .comptime_int_type };

/// The host target -- the one `zig run` selects with no `-target`, so the ABI
/// results below match it. The whole REPL is compiled for, and evaluates as,
/// this single target.
const target: *const std.Target = &builtin.target;

/// ABI alignment of `ty`, or `null` for a type whose layout this subset does
/// not model yet (struct / vector / optional / tuple / error / fn). Ports
/// `Type.abiAlignment` (src/Type.zig). Comptime-only and `noreturn` types
/// return a real alignment here (as the compiler's function does); `@alignOf`
/// guards `noreturn` separately.
pub fn abiAlignment(ty: Type, pool: *const InternPool) ?InternPool.Alignment {
    return switch (pool.indexToKey(ty.index)) {
        .int_type => |it| if (it.bits == 0)
            .@"1"
        else
            .fromByteUnits(std.zig.target.intAlignment(target, it.bits)),
        .ptr_type, .anyframe_type => ptrAbiAlignment(),
        .array_type => |at| abiAlignment(fromIndex(at.child), pool),
        .simple_type => |t| switch (t) {
            .bool, .void, .noreturn, .anyopaque, .type, .comptime_int, .comptime_float, .null, .undefined, .enum_literal => .@"1",
            .anyerror, .adhoc_inferred_error_set => null, // error-set ABI not modelled yet
            .usize, .isize => .fromByteUnits(std.zig.target.intAlignment(target, target.ptrBitWidth())),
            .c_char => cTypeAlign(.char),
            .c_short => cTypeAlign(.short),
            .c_ushort => cTypeAlign(.ushort),
            .c_int => cTypeAlign(.int),
            .c_uint => cTypeAlign(.uint),
            .c_long => cTypeAlign(.long),
            .c_ulong => cTypeAlign(.ulong),
            .c_longlong => cTypeAlign(.longlong),
            .c_ulonglong => cTypeAlign(.ulonglong),
            .c_longdouble => cTypeAlign(.longdouble),
            .f16 => .@"2",
            .f32 => cTypeAlign(.float),
            .f64 => if (target.cTypeBitSize(.double) == 64) cTypeAlign(.double) else .@"8",
            .f80 => if (target.cTypeBitSize(.longdouble) == 80) cTypeAlign(.longdouble) else .fromByteUnits(std.zig.target.intAlignment(target, 80)),
            .f128 => if (target.cTypeBitSize(.longdouble) == 128) cTypeAlign(.longdouble) else .@"16",
            // An internal generic-return marker, never a real `@alignOf` operand.
            .generic_poison => unreachable,
        },
        // An enum's alignment is its integer tag type's, once resolved (the caller
        // runs `ensureLayoutResolved` first). Reads the header int tag type directly so
        // a union's generated tag enum -- whose fields stay lazy -- also measures.
        .enum_type => switch (pool.enumIntTagTypeStored(ty.index)) {
            .none => null,
            else => |int_ty| abiAlignment(fromIndex(int_ty), pool),
        },
        // A struct's alignment is stored in its header once layout is resolved (the
        // caller runs `ensureLayoutResolved` first). Mirrors `Type.abiAlignment`.
        .struct_type => if (pool.loadStructType(ty.index)) |f| f.alignment else null,
        .union_type => if (pool.unionFields(ty.index)) |f| f.alignment else null,
        else => null,
    };
}

/// ABI byte size of `ty`, or `null` for an unmodelled layout (same set as
/// `abiAlignment`). Comptime-only and uninstantiable simple types return `0`
/// here as the compiler's function does; `@sizeOf` rejects them before calling.
pub fn abiSize(ty: Type, pool: *const InternPool) ?u64 {
    return switch (pool.indexToKey(ty.index)) {
        .int_type => |it| std.zig.target.intByteSize(target, it.bits),
        .ptr_type => |pt| switch (pt.flags.size) {
            .slice => ptrByteSize() * 2,
            .one, .many, .c => ptrByteSize(),
        },
        .anyframe_type => ptrByteSize(),
        .array_type => |at| blk: {
            const child = abiSize(fromIndex(at.child), pool) orelse break :blk null;
            break :blk at.lenIncludingSentinel() * child;
        },
        .simple_type => |t| switch (t) {
            .void, .noreturn, .anyopaque, .type, .comptime_int, .comptime_float, .null, .undefined, .enum_literal => 0,
            .anyerror, .adhoc_inferred_error_set => null,
            .bool => 1,
            .usize, .isize => ptrByteSize(),
            .c_char => target.cTypeByteSize(.char),
            .c_short => target.cTypeByteSize(.short),
            .c_ushort => target.cTypeByteSize(.ushort),
            .c_int => target.cTypeByteSize(.int),
            .c_uint => target.cTypeByteSize(.uint),
            .c_long => target.cTypeByteSize(.long),
            .c_ulong => target.cTypeByteSize(.ulong),
            .c_longlong => target.cTypeByteSize(.longlong),
            .c_ulonglong => target.cTypeByteSize(.ulonglong),
            .c_longdouble => target.cTypeByteSize(.longdouble),
            .f16 => 2,
            .f32 => 4,
            .f64 => 8,
            .f80 => if (target.cTypeBitSize(.longdouble) == 80) target.cTypeByteSize(.longdouble) else std.zig.target.intByteSize(target, 80),
            .f128 => 16,
            .generic_poison => unreachable,
        },
        // An enum's size is its integer tag type's, once resolved (the caller runs
        // `ensureLayoutResolved` first). Reads the header int tag type directly so a
        // union's generated tag enum -- whose fields stay lazy -- also measures.
        .enum_type => switch (pool.enumIntTagTypeStored(ty.index)) {
            .none => null,
            else => |int_ty| abiSize(fromIndex(int_ty), pool),
        },
        // A struct's size is stored in its header once layout is resolved (the caller
        // runs `ensureLayoutResolved` first). Mirrors `Type.abiSize`.
        .struct_type => if (pool.loadStructType(ty.index)) |f| f.size else null,
        .union_type => if (pool.unionFields(ty.index)) |f| f.size else null,
        else => null,
    };
}

/// The type's meaningful bit width (`@bitSizeOf`). `null` for a type the
/// comptime-only model cannot measure (a struct, union, or enum, whose layout
/// is unresolved) -- the compiler's `else` arm reads `intInfo(zcu).bits`, which
/// the scalar cases below cover directly.
pub fn bitSize(ty: Type, pool: *const InternPool) ?u64 {
    return switch (pool.indexToKey(ty.index)) {
        .int_type => |it| it.bits,
        .ptr_type => |pt| switch (pt.flags.size) {
            .slice => target.ptrBitWidth() * 2,
            .one, .many, .c => target.ptrBitWidth(),
        },
        .array_type => |at| blk: {
            const child = bitSize(fromIndex(at.child), pool) orelse break :blk null;
            break :blk at.lenIncludingSentinel() * child;
        },
        .vector_type => |vt| blk: {
            const child = bitSize(fromIndex(vt.child), pool) orelse break :blk null;
            break :blk vt.len * child;
        },
        .simple_type => |t| switch (t) {
            .void => 0,
            .bool => 1,
            .usize, .isize => target.ptrBitWidth(),
            .c_char => target.cTypeBitSize(.char),
            .c_short => target.cTypeBitSize(.short),
            .c_ushort => target.cTypeBitSize(.ushort),
            .c_int => target.cTypeBitSize(.int),
            .c_uint => target.cTypeBitSize(.uint),
            .c_long => target.cTypeBitSize(.long),
            .c_ulong => target.cTypeBitSize(.ulong),
            .c_longlong => target.cTypeBitSize(.longlong),
            .c_ulonglong => target.cTypeBitSize(.ulonglong),
            .c_longdouble => target.cTypeBitSize(.longdouble),
            .f16 => 16,
            .f32 => 32,
            .f64 => 64,
            .f80 => 80,
            .f128 => 128,
            else => null,
        },
        else => null,
    };
}

/// `{signedness, bits}` of a fixed-width int, else null, unwrapping the wrappers
/// whose underlying representation is that int -- a vector to its element and an
/// enum to its tag type -- in a loop. The compiler's packed-struct/union and
/// error-set arms are omitted (the REPL models neither a packed backing int nor
/// `errorSetBits`, and routes error-set reflection separately); those and every
/// other non-int type return `null` (the compiler asserts unreachable there, but
/// the REPL uses `intInfo` as a nullable classifier).
pub fn intInfo(starting_ty: Type, pool: *const InternPool) ?std.lang.Type.Int {
    var ty = starting_ty;
    while (true) switch (ty.index) {
        .usize_type => return .{ .signedness = .unsigned, .bits = target.ptrBitWidth() },
        .isize_type => return .{ .signedness = .signed, .bits = target.ptrBitWidth() },
        .c_char_type => return .{ .signedness = target.cCharSignedness(), .bits = target.cTypeBitSize(.char) },
        .c_short_type => return .{ .signedness = .signed, .bits = target.cTypeBitSize(.short) },
        .c_ushort_type => return .{ .signedness = .unsigned, .bits = target.cTypeBitSize(.ushort) },
        .c_int_type => return .{ .signedness = .signed, .bits = target.cTypeBitSize(.int) },
        .c_uint_type => return .{ .signedness = .unsigned, .bits = target.cTypeBitSize(.uint) },
        .c_long_type => return .{ .signedness = .signed, .bits = target.cTypeBitSize(.long) },
        .c_ulong_type => return .{ .signedness = .unsigned, .bits = target.cTypeBitSize(.ulong) },
        .c_longlong_type => return .{ .signedness = .signed, .bits = target.cTypeBitSize(.longlong) },
        .c_ulonglong_type => return .{ .signedness = .unsigned, .bits = target.cTypeBitSize(.ulonglong) },
        else => switch (pool.indexToKey(ty.index)) {
            .int_type => |it| return it,
            .enum_type => ty = .fromIndex(pool.loadEnumType(ty.index).?.int_tag_type),
            .vector_type => |vector_type| ty = .fromIndex(vector_type.child),
            else => return null,
        },
    };
}

/// The unsigned integer type with the same width as `ty` (a signed int, or a
/// vector thereof). `usize`/`isize` map to `usize` and each `c_*` pair to its
/// unsigned member; `c_char` (absent from those pairs) falls to a plain unsigned
/// int of its width, as in the compiler.
pub fn toUnsigned(ty: Type, pool: *InternPool) std.mem.Allocator.Error!Type {
    return switch (ty.index) {
        .usize_type, .isize_type => .fromIndex(.usize_type),
        .c_ushort_type, .c_short_type => .fromIndex(.c_ushort_type),
        .c_uint_type, .c_int_type => .fromIndex(.c_uint_type),
        .c_ulong_type, .c_long_type => .fromIndex(.c_ulong_type),
        .c_ulonglong_type, .c_longlong_type => .fromIndex(.c_ulonglong_type),
        else => switch (ty.zigTypeTag(pool)) {
            .int => .fromIndex(try pool.internIntType(.unsigned, ty.intInfo(pool).?.bits)),
            .vector => .fromIndex(try pool.internVectorType(.{
                .len = ty.vectorLen(pool),
                .child = (try ty.childType(pool).toUnsigned(pool)).index,
            })),
            else => unreachable,
        },
    };
}

pub fn zigTypeTag(ty: Type, pool: *const InternPool) std.lang.TypeId {
    return pool.zigTypeTag(ty.index);
}

/// The child type of a pointer/array/vector/optional/anyframe.
pub fn childType(ty: Type, pool: *const InternPool) Type {
    return .fromIndex(pool.childType(ty.index));
}

/// The number of bits an unsigned integer needs to hold `max`.
pub fn smallestUnsignedBits(max: u64) u16 {
    return switch (max) {
        0 => 0,
        else => @as(u16, 1) + std.math.log2_int(u64, max),
    };
}

/// Bit width of a float type; `c_longdouble` resolves against the host target,
/// like the sibling `intInfo` c-type arms.
pub fn floatBits(ty: Type) u16 {
    return switch (ty.index) {
        .f16_type => 16,
        .f32_type => 32,
        .f64_type => 64,
        .f80_type => 80,
        .f128_type, .comptime_float_type => 128,
        .c_longdouble_type => target.cTypeBitSize(.longdouble),
        else => unreachable,
    };
}

/// Whether `ty` is a pointer at runtime -- a real pointer, or a pointer-like
/// optional.
pub fn isPtrAtRuntime(ty: Type, pool: *const InternPool) bool {
    return switch (pool.indexToKey(ty.index)) {
        .ptr_type => |ptr_type| switch (ptr_type.flags.size) {
            .slice => false,
            .one, .many, .c => true,
        },
        .opt_type => |child| switch (pool.indexToKey(child)) {
            .ptr_type => |p| switch (p.flags.size) {
                .slice, .c => false,
                .many, .one => !p.flags.is_allowzero,
            },
            else => false,
        },
        else => false,
    };
}

/// A pointer whose size is `.slice`.
pub fn isSlice(ty: Type, pool: *const InternPool) bool {
    return switch (pool.indexToKey(ty.index)) {
        .ptr_type => |ptr_type| ptr_type.flags.size == .slice,
        else => false,
    };
}

/// A `const` pointer.
pub fn isConstPtr(ty: Type, pool: *const InternPool) bool {
    return switch (pool.indexToKey(ty.index)) {
        .ptr_type => |ptr_type| ptr_type.flags.is_const,
        else => false,
    };
}

/// A `volatile` pointer.
pub fn isVolatilePtr(ty: Type, pool: *const InternPool) bool {
    return switch (pool.indexToKey(ty.index)) {
        .ptr_type => |ptr_type| ptr_type.flags.is_volatile,
        else => false,
    };
}

/// A pointer-like optional (`?*T`, `?[*]T`, `[*c]T`) -- represented as a bare
/// pointer with null as the zero address.
pub fn isPtrLikeOptional(ty: Type, pool: *const InternPool) bool {
    return switch (pool.indexToKey(ty.index)) {
        .ptr_type => |ptr_type| ptr_type.flags.size == .c,
        .opt_type => |child| switch (pool.indexToKey(child)) {
            .ptr_type => |ptr_type| switch (ptr_type.flags.size) {
                .slice, .c => false,
                .many, .one => !ptr_type.flags.is_allowzero,
            },
            else => false,
        },
        else => false,
    };
}

/// Whether a pointer (or pointer-like optional) admits the null address.
pub fn ptrAllowsZero(ty: Type, pool: *const InternPool) bool {
    return ty.isPtrLikeOptional(pool) or pool.indexToKey(ty.index).ptr_type.flags.is_allowzero;
}

/// The child of an optional (or a C pointer, which represents itself); asserts
/// `ty` is an optional or a C pointer.
pub fn optionalChild(ty: Type, pool: *const InternPool) Type {
    return switch (pool.indexToKey(ty.index)) {
        .opt_type => |child| .fromIndex(child),
        .ptr_type => |ptr_type| blk: {
            assert(ptr_type.flags.size == .c);
            break :blk ty;
        },
        else => unreachable,
    };
}

/// `{len, sentinel, elem_type}` of an array type; the sentinel is an interned
/// value `Index` (`null` when absent), so callers compare it by identity as the
/// compiler compares its `Value` after coercion.
pub const ArrayInfo = struct { len: u64, sentinel: ?InternPool.Index, elem_type: Type };
pub fn arrayInfo(ty: Type, pool: *const InternPool) ArrayInfo {
    const at = pool.indexToKey(ty.index).array_type;
    return .{
        .len = at.len,
        .sentinel = if (at.sentinel == .none) null else at.sentinel,
        .elem_type = .fromIndex(at.child),
    };
}

/// Element count of a vector.
pub fn vectorLen(ty: Type, pool: *const InternPool) u32 {
    return pool.indexToKey(ty.index).vector_type.len;
}

/// The element type of a vector; otherwise `ty` itself.
pub fn scalarType(ty: Type, pool: *const InternPool) Type {
    return switch (ty.zigTypeTag(pool)) {
        .vector => ty.childType(pool),
        else => ty,
    };
}

/// The payload type of an error union.
pub fn errorUnionPayload(ty: Type, pool: *const InternPool) Type {
    return .fromIndex(pool.indexToKey(ty.index).error_union_type.payload_type);
}

/// The error-set type of an error union.
pub fn errorUnionSet(ty: Type, pool: *const InternPool) Type {
    return .fromIndex(pool.indexToKey(ty.index).error_union_type.error_set_type);
}

pub fn errorSetIsEmpty(ty: Type, pool: *const InternPool) bool {
    return switch (ty.index) {
        .anyerror_type, .adhoc_inferred_error_set_type => false,
        else => switch (pool.indexToKey(ty.index)) {
            .error_set_type => |error_set_type| error_set_type.names.len == 0,
            else => unreachable,
        },
    };
}

pub fn isAnyError(ty: Type, pool: *const InternPool) bool {
    _ = pool;
    return switch (ty.index) {
        .anyerror_type => true,
        .adhoc_inferred_error_set_type => false,
        else => false,
    };
}

pub fn errorSetNames(ty: Type, pool: *const InternPool) []const InternPool.NullTerminatedString {
    return switch (pool.indexToKey(ty.index)) {
        .error_set_type => |x| x.names,
        else => unreachable,
    };
}

pub fn errorSetHasField(ty: Type, name: InternPool.NullTerminatedString, pool: *const InternPool) bool {
    return switch (ty.index) {
        .anyerror_type => true,
        else => switch (pool.indexToKey(ty.index)) {
            .error_set_type => |error_set_type| error_set_type.nameIndex(pool, name) != null,
            else => unreachable,
        },
    };
}

/// Peel optional and error-union wrappers to the innermost payload; `?T`, `E!T`,
/// and `?E!T` all yield `T`. A result-location type carries these wrappers (from
/// `@as(?S, .{...})`), but the init syntax binds against the payload container.
pub fn optEuBaseType(ty: Type, pool: *const InternPool) Type {
    var cur = ty;
    while (true) switch (cur.zigTypeTag(pool)) {
        .optional => cur = cur.optionalChild(pool),
        .error_union => cur = cur.errorUnionPayload(pool),
        else => return cur,
    };
}

/// A tuple type.
pub fn isTuple(ty: Type, pool: *const InternPool) bool {
    return pool.indexToKey(ty.index) == .tuple_type;
}

/// The element type of an indexable type (array/vector, or a pointer to one, or a
/// many/slice/C pointer).
pub fn indexableElem(ty: Type, pool: *const InternPool) Type {
    return switch (pool.indexToKey(ty.index)) {
        inline .array_type, .vector_type => |arr| .fromIndex(arr.child),
        .ptr_type => |ptr_type| switch (ptr_type.flags.size) {
            .many, .slice, .c => .fromIndex(ptr_type.child),
            .one => switch (pool.indexToKey(ptr_type.child)) {
                inline .array_type, .vector_type => |arr| .fromIndex(arr.child),
                else => unreachable,
            },
        },
        else => unreachable,
    };
}

/// The pointer's type info; asserts `ty` is a pointer.
pub fn ptrInfo(ty: Type, pool: *const InternPool) InternPool.Key.PtrType {
    return switch (pool.indexToKey(ty.index)) {
        .ptr_type => |p| p,
        // A pointer-like optional carries its pointer info on the payload.
        .opt_type => |child| pool.indexToKey(child).ptr_type,
        else => unreachable,
    };
}

/// Whether `ty` contains comptime-only state, so its values are never runtime-
/// known. Derived directly over the Key here, recursing on the child for
/// optional/array/vector/error-union. Nominal containers (struct/union/enum) need
/// resolved layout this pool-only query cannot reach; they are treated as not
/// comptime-only (they are unreachable on the `@memcpy` element path, which
/// recurses only through the arms below).
pub fn comptimeOnly(ty: Type, pool: *const InternPool) bool {
    return switch (pool.indexToKey(ty.index)) {
        .simple_type => |t| switch (t) {
            .type, .comptime_int, .comptime_float, .enum_literal, .null, .undefined => true,
            else => false,
        },
        .func_type => true,
        .int_type, .error_set_type, .ptr_type, .anyframe_type => false,
        .array_type => |arr| Type.fromIndex(arr.child).comptimeOnly(pool),
        .vector_type => |vec| Type.fromIndex(vec.child).comptimeOnly(pool),
        .opt_type => |child| Type.fromIndex(child).comptimeOnly(pool),
        .error_union_type => |eu| Type.fromIndex(eu.payload_type).comptimeOnly(pool),
        else => false,
    };
}

fn cTypeAlign(c: std.Target.CType) InternPool.Alignment {
    return .fromByteUnits(target.cTypeAlignment(c));
}

/// Pointer ABI alignment/size for the host: the pointer's byte width. Off the
/// eZ80 (whose 24-bit pointers we never host) this is exactly the pointer's byte
/// width.
fn ptrAbiAlignment() InternPool.Alignment {
    return .fromByteUnits(ptrByteSize());
}
fn ptrByteSize() u64 {
    return @divExact(target.ptrBitWidth(), 8);
}

/// Errors writing a type name: I/O, plus the allocation the `error{...}` name
/// sort needs (it dupes the names slice to order them alphabetically).
pub const PrintError = std.Io.Writer.Error || std.mem.Allocator.Error;

/// A `{f}`-formattable wrapper carrying the `InternPool` `print` needs (a plain
/// `format(self, writer)` method cannot take one), letting diagnostics write
/// `"found '{f}'"` with `ty.fmt(ip)`. OOM while sorting error-set names degrades
/// to `<type>` rather than propagating (a diagnostic is best-effort and `format`
/// yields only `Writer.Error`).
pub const Formatter = struct {
    ty: Type,
    pool: *const InternPool,
    pub fn format(self: Formatter, writer: *std.Io.Writer) std.Io.Writer.Error!void {
        self.ty.print(self.pool, writer) catch |err| switch (err) {
            error.WriteFailed => return error.WriteFailed,
            else => try writer.writeAll("<type>"),
        };
    }
};

pub fn fmt(ty: Type, pool: *const InternPool) Formatter {
    return .{ .ty = ty, .pool = pool };
}

/// Write `ty`'s Zig surface-syntax name with no trailing newline (`*const u8`,
/// `error{A,B}!u32`, `fn (u8) void`), recursing on container children. Ports
/// `Type.print` (src/Type.zig). Pointer sentinels and `align(N)` are printed;
/// pointer `address_space` / `vector_index` / `bit_range` prefixes are not yet
/// covered.
pub fn print(ty: Type, pool: *const InternPool, writer: *std.Io.Writer) PrintError!void {
    assert(ty.index != .none);
    switch (pool.indexToKey(ty.index)) {
        // Most simple types print as their tag name; the three literal types
        // have surface-syntax names that differ from the tag.
        .simple_type => |st| switch (st) {
            .null => try writer.writeAll("@TypeOf(null)"),
            .undefined => try writer.writeAll("@TypeOf(undefined)"),
            .enum_literal => try writer.writeAll("@EnumLiteral()"),
            else => try writer.print("{s}", .{@tagName(st)}),
        },
        .int_type => |it| try writer.print("{c}{d}", .{
            @as(u8, switch (it.signedness) {
                .signed => 'i',
                .unsigned => 'u',
            }),
            it.bits,
        }),
        .anyframe_type => |child| if (child == .none)
            try writer.writeAll("anyframe")
        else {
            try writer.writeAll("anyframe->");
            try print(fromIndex(child), pool, writer);
        },
        .ptr_type => |pt| try printPtr(pt, pool, writer),
        .error_set_type => |es| try printErrorSet(es, pool, writer),
        .error_union_type => |eu| try printErrorUnion(eu, pool, writer),
        .func_type => |ft| try printFunc(ft, pool, writer),
        .array_type => |at| try printArray(at, pool, writer),
        .vector_type => |vt| try printVector(vt, pool, writer),
        .opt_type => |child| {
            try writer.writeAll("?");
            try print(fromIndex(child), pool, writer);
        },
        .tuple_type => |tt| try printTuple(tt, pool, writer),
        // Nominal types print their fully-qualified `name`, baked at creation and
        // stored in the container header (not the identity Key).
        .struct_type, .enum_type, .union_type, .opaque_type => try writer.writeAll(pool.stringSlice(pool.typeName(ty.index))),
        // Unhandled *type* Keys (opaque, ...) aren't rendered yet. A value Key
        // reaching a type printer is a bug, so assert it's a type.
        else => |other| {
            assert(other.isType());
            try writer.writeAll("<type>");
        },
    }
}

/// Whether two values of this type can be compared with each other -- `==`/`!=`
/// when `is_equality_cmp`, `<`/`>`/... otherwise. Ports `Type.isSelfComparable`
/// (src/Type.zig), keyed on the pool Key in place of `zigTypeTag`. The REPL
/// models no `packed`/`opaque`/`frame`/`anyframe` values, so those fold to the
/// same `false`/`is_equality_cmp` result the compiler gives. Used by the
/// array-sentinel type check (`checkSentinelType`).
pub fn isSelfComparable(ty: Type, pool: *const InternPool, is_equality_cmp: bool) bool {
    return switch (pool.indexToKey(ty.index)) {
        .int_type => true,
        .simple_type => |s| switch (s) {
            .usize,
            .isize,
            .c_char,
            .c_short,
            .c_ushort,
            .c_int,
            .c_uint,
            .c_long,
            .c_ulong,
            .c_longlong,
            .c_ulonglong,
            .comptime_int, // .int / .comptime_int
            .f16,
            .f32,
            .f64,
            .f80,
            .f128,
            .c_longdouble,
            .comptime_float, // .float / .comptime_float
            => true,
            .bool, .type, .void, .anyerror, .adhoc_inferred_error_set, .enum_literal, .anyopaque => is_equality_cmp,
            .noreturn, .undefined, .null, .generic_poison => false,
        },
        .vector_type => |vt| fromIndex(vt.child).isSelfComparable(pool, is_equality_cmp),
        .enum_type, .error_set_type, .func_type, .anyframe_type => is_equality_cmp,
        .error_union_type, .array_type => false,
        // The REPL has only auto-layout aggregates; a non-packed struct/union is
        // not self-comparable (the compiler allows `packed` only).
        .struct_type, .union_type, .tuple_type => false,
        .ptr_type => |pt| pt.flags.size != .slice and (is_equality_cmp or pt.flags.size == .c),
        .opt_type => |child| is_equality_cmp and fromIndex(child).isSelfComparable(pool, is_equality_cmp),
        else => false,
    };
}

fn printPtr(pt: InternPool.Key.PtrType, pool: *const InternPool, writer: *std.Io.Writer) PrintError!void {
    assert(pt.child != .none);
    try writer.writeAll(switch (pt.flags.size) {
        .one => "*",
        .many => "[*]",
        .slice => "[]",
        .c => "[*c]",
    });
    if (pt.flags.is_allowzero and pt.flags.size != .c) try writer.writeAll("allowzero ");
    // An explicit alignment prints `align(N)`; natural alignment (`.none`)
    // is omitted.
    if (pt.flags.alignment.toByteUnits()) |bytes| try writer.print("align({d}) ", .{bytes});
    if (pt.flags.is_const) try writer.writeAll("const ");
    if (pt.flags.is_volatile) try writer.writeAll("volatile ");
    try print(fromIndex(pt.child), pool, writer);
}

/// `[N]T` or `[N:s]T`. The sentinel prints via its integer literal text for
/// the current numeric subset; other sentinel kinds fall back to `?`.
fn printArray(at: InternPool.Key.ArrayType, pool: *const InternPool, writer: *std.Io.Writer) PrintError!void {
    try writer.print("[{d}", .{at.len});
    if (at.sentinel != .none) {
        try writer.writeAll(":");
        switch (pool.indexToKey(at.sentinel)) {
            .int => |iv| {
                var space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
                try writer.print("{f}", .{iv.storage.toBigInt(&space)});
            },
            else => try writer.writeAll("?"),
        }
    }
    try writer.writeAll("]");
    try print(fromIndex(at.child), pool, writer);
}

/// `struct { T0, T1, ... }`; an empty tuple is `struct {}` (matching `@typeName`).
fn printTuple(tt: InternPool.Key.TupleType, pool: *const InternPool, writer: *std.Io.Writer) PrintError!void {
    if (tt.types.len == 0) {
        try writer.writeAll("struct {}");
        return;
    }
    try writer.writeAll("struct { ");
    for (tt.types, 0..) |field_ty, i| {
        if (i != 0) try writer.writeAll(", ");
        try print(fromIndex(field_ty), pool, writer);
    }
    try writer.writeAll(" }");
}

/// `@Vector(N, T)`.
fn printVector(vt: InternPool.Key.VectorType, pool: *const InternPool, writer: *std.Io.Writer) PrintError!void {
    try writer.print("@Vector({d}, ", .{vt.len});
    try print(fromIndex(vt.child), pool, writer);
    try writer.writeAll(")");
}

/// `[noinline] fn ([comptime|noalias] P0, ...[, ...]) [callconv(.@"name")] R`.
/// CC is omitted when `.auto`. Per-param `comptime`/`noalias` come from the
/// FuncType bitmasks (first 32 params).
fn printFunc(ft: InternPool.Key.FuncType, pool: *const InternPool, writer: *std.Io.Writer) PrintError!void {
    if (ft.is_noinline) try writer.writeAll("noinline ");
    try writer.writeAll("fn (");
    for (ft.param_types, 0..) |p, i| {
        if (i != 0) try writer.writeAll(", ");
        // Only the first 32 params have flag bits; std.math.cast succeeds IFF
        // `i` fits the u5 index `paramIsComptime`/`paramIsNoalias` take.
        if (std.math.cast(u5, i)) |idx| {
            if (ft.paramIsComptime(idx)) try writer.writeAll("comptime ");
            if (ft.paramIsNoalias(idx)) try writer.writeAll("noalias ");
        }
        try print(fromIndex(p), pool, writer);
    }
    if (ft.is_var_args) {
        try writer.writeAll(if (ft.param_types.len > 0) ", ..." else "...");
    }
    try writer.writeAll(") ");
    const cc_tag: std.lang.CallingConvention.Tag = ft.cc;
    if (cc_tag != .auto) {
        const name = @tagName(cc_tag);
        // Escape only names that are Zig keywords (`.@"async"`), as the
        // value-printer does, so render output stays byte-equal with `zig run`.
        if (std.zig.Token.getKeyword(name) != null) {
            try writer.print("callconv(.@\"{s}\") ", .{name});
        } else {
            try writer.print("callconv(.{s}) ", .{name});
        }
    }
    try print(fromIndex(ft.return_type), pool, writer);
}

fn printErrorUnion(eu: InternPool.Key.ErrorUnionType, pool: *const InternPool, writer: *std.Io.Writer) PrintError!void {
    try print(fromIndex(eu.error_set_type), pool, writer);
    try writer.writeAll("!");
    try print(fromIndex(eu.payload_type), pool, writer);
}

fn printErrorSet(es: InternPool.Key.ErrorSetType, pool: *const InternPool, writer: *std.Io.Writer) PrintError!void {
    // Display wants the members byte-sorted, but the pool stores them id-sorted,
    // so a sortable copy is needed. A stack buffer holds the common small set
    // (0-alloc); only an unusually large error set falls back to the heap.
    var stack_buf: [32]InternPool.NullTerminatedString = undefined;
    const on_heap = es.names.len > stack_buf.len;
    const sorted = if (on_heap)
        try pool.gpa.dupe(InternPool.NullTerminatedString, es.names)
    else sorted: {
        @memcpy(stack_buf[0..es.names.len], es.names);
        break :sorted stack_buf[0..es.names.len];
    };
    defer if (on_heap) pool.gpa.free(sorted);
    std.mem.sortUnstable(InternPool.NullTerminatedString, sorted, pool, lessThanByBytes);

    try writer.writeAll("error{");
    for (sorted, 0..) |name, i| {
        if (i != 0) try writer.writeAll(",");
        try writer.writeAll(pool.stringSlice(name));
    }
    try writer.writeAll("}");
}

fn lessThanByBytes(
    pool: *const InternPool,
    a: InternPool.NullTerminatedString,
    b: InternPool.NullTerminatedString,
) bool {
    return std.mem.lessThan(u8, pool.stringSlice(a), pool.stringSlice(b));
}
