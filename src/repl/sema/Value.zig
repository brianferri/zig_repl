//! Thin newtype over `InternPool.Index` that names "this index refers to a
//! value". Mirror of `Type` on the value side.

const std = @import("std");
const assert = std.debug.assert;

const InternPool = @import("InternPool.zig");
const Type = @import("Type.zig");

const Value = @This();

index: InternPool.Index,
/// Whether this value is comptime-known. The evaluator always has a concrete
/// `index` (it substitutes a call's args to evaluate the body), so this is a
/// *provenance* bit: a value built from literals and consts is comptime-known;
/// one derived from a non-`comptime` parameter is not. Coercion needs it -- a
/// comptime-known value coerces value-based (the value must fit), a runtime
/// value type-based (the source *type* must coerce) -- so the body of
/// `fn (a: u32) i32 { return a; }` is rejected as the compiler rejects it.
///
/// The compiler reads this structurally (a comptime value interns, a runtime
/// one is an Air instruction with no constant: `resolveValue(ref) != null`).
/// This evaluator has no Air, so it carries the bit. Seeded from the
/// parameter's `comptime`-ness (`Block.Param.is_comptime` / FuncType
/// `comptime_bits`) and ANDed through each operation that builds a value.
is_comptime: bool = true,

pub fn fromIndex(index: InternPool.Index) Value {
    assert(index != .none);
    return .{ .index = index };
}

pub fn toIndex(val: Value) InternPool.Index {
    return val.index;
}

/// Returns the type of the value, looked up through `pool`.
pub fn typeOf(val: Value, pool: *const InternPool) Type {
    const key = pool.indexToKey(val.index);
    return switch (key) {
        .simple_value => |sv| switch (sv) {
            .void => .void_type,
            .true, .false => .bool_type,
            .null => .{ .index = .null_type },
            .@"unreachable" => .{ .index = .noreturn_type },
        },
        .int => |iv| .{ .index = iv.ty },
        .float => |fv| .{ .index = fv.ty },
        .undef => |ty| .{ .index = ty },
        .ptr => |p| .{ .index = p.ty },
        .slice => |s| .{ .index = s.ty },
        .err => |e| .{ .index = e.ty },
        .error_union => |eu| .{ .index = eu.ty },
        .func => |f| .{ .index = f.ty },
        .opt => |o| .{ .index = o.ty },
        .aggregate => |agg| .{ .index = agg.ty },
        .enum_tag => |et| .{ .index = et.ty },
        .enum_literal => .{ .index = .enum_literal_type },
        .un => |uv| .{ .index = uv.ty },
        // Every remaining Key is a type used as a value, whose own type is
        // `type`. The value Keys above are exhaustive, so anything reaching
        // here is a type -- the assert turns a future unclassified value Key
        // into a loud crash rather than a silent `.type_type`.
        else => blk: {
            assert(key.isType());
            break :blk .type_type;
        },
    };
}

/// Interpret an int or float value as a float of type `T`. Ports `Value.toFloat`
/// (`zcu` -> `pool`).
pub fn toFloat(val: Value, comptime T: type, pool: *const InternPool) T {
    return switch (pool.indexToKey(val.index)) {
        .int => |int| switch (int.storage) {
            .big_int => |big_int| big_int.toFloat(T, .nearest_even)[0],
            inline .u64, .i64 => |x| {
                if (T == f80) {
                    @panic("TODO we can't lower this properly on non-x86 llvm backend yet");
                }
                return @floatFromInt(x);
            },
        },
        .float => |float| switch (float.storage) {
            inline else => |x| @floatCast(x),
        },
        else => unreachable,
    };
}

/// The element at `index` of an aggregate value (the childless undef of an undef
/// aggregate). Ports `Value.elemValue`; the storage variants are resolved by
/// `aggregateElementAt`.
pub fn elemValue(val: Value, pool: *InternPool, index: usize) std.mem.Allocator.Error!Value {
    switch (pool.indexToKey(val.index)) {
        .undef => |ty| return .fromIndex(try pool.get(.{ .undef = Type.fromIndex(ty).childType(pool).index })),
        .aggregate => |aggregate| return .fromIndex(InternPool.aggregateElementAt(aggregate, index)),
        else => unreachable,
    }
}

/// `@mulAdd(float_type, mulend1, mulend2, addend)`. Ports `Value.mulAdd`.
pub fn mulAdd(
    float_type: Type,
    mulend1: Value,
    mulend2: Value,
    addend: Value,
    arena: std.mem.Allocator,
    pool: *InternPool,
) std.mem.Allocator.Error!Value {
    if (float_type.zigTypeTag(pool) == .vector) {
        const result_data = try arena.alloc(InternPool.Index, float_type.vectorLen(pool));
        const scalar_ty = float_type.scalarType(pool);
        for (result_data, 0..) |*scalar, i| {
            const mulend1_elem = try mulend1.elemValue(pool, i);
            const mulend2_elem = try mulend2.elemValue(pool, i);
            const addend_elem = try addend.elemValue(pool, i);
            scalar.* = (try mulAddScalar(scalar_ty, mulend1_elem, mulend2_elem, addend_elem, pool)).index;
        }
        return .fromIndex(try pool.internAggregate(.{ .ty = float_type.index, .storage = .{ .elems = result_data } }));
    }
    return mulAddScalar(float_type, mulend1, mulend2, addend, pool);
}

pub fn mulAddScalar(
    float_type: Type,
    mulend1: Value,
    mulend2: Value,
    addend: Value,
    pool: *InternPool,
) std.mem.Allocator.Error!Value {
    const storage: InternPool.Key.Float.Storage = switch (float_type.floatBits()) {
        16 => .{ .f16 = @mulAdd(f16, mulend1.toFloat(f16, pool), mulend2.toFloat(f16, pool), addend.toFloat(f16, pool)) },
        32 => .{ .f32 = @mulAdd(f32, mulend1.toFloat(f32, pool), mulend2.toFloat(f32, pool), addend.toFloat(f32, pool)) },
        64 => .{ .f64 = @mulAdd(f64, mulend1.toFloat(f64, pool), mulend2.toFloat(f64, pool), addend.toFloat(f64, pool)) },
        80 => .{ .f80 = @mulAdd(f80, mulend1.toFloat(f80, pool), mulend2.toFloat(f80, pool), addend.toFloat(f80, pool)) },
        128 => .{ .f128 = @mulAdd(f128, mulend1.toFloat(f128, pool), mulend2.toFloat(f128, pool), addend.toFloat(f128, pool)) },
        else => unreachable,
    };
    return .fromIndex(try pool.internFloat(.{ .ty = float_type.index, .storage = storage }));
}

/// `@abs(val)` of type `ty`. Ports `Value.abs`.
pub fn abs(val: Value, ty: Type, arena: std.mem.Allocator, pool: *InternPool) std.mem.Allocator.Error!Value {
    if (ty.zigTypeTag(pool) == .vector) {
        const result_data = try arena.alloc(InternPool.Index, ty.vectorLen(pool));
        const scalar_ty = ty.scalarType(pool);
        for (result_data, 0..) |*scalar, i| {
            const elem_val = try val.elemValue(pool, i);
            scalar.* = (try absScalar(elem_val, scalar_ty, pool, arena)).index;
        }
        return .fromIndex(try pool.internAggregate(.{ .ty = ty.index, .storage = .{ .elems = result_data } }));
    }
    return absScalar(val, ty, pool, arena);
}

pub fn absScalar(val: Value, ty: Type, pool: *InternPool, arena: std.mem.Allocator) std.mem.Allocator.Error!Value {
    switch (ty.zigTypeTag(pool)) {
        .int => {
            var buffer: InternPool.Key.Int.Storage.BigIntSpace = undefined;
            var operand_bigint = try pool.indexToKey(val.index).int.storage.toBigInt(&buffer).toManaged(arena);
            operand_bigint.abs();
            return .fromIndex(try pool.internIntValue((try ty.toUnsigned(pool)).index, operand_bigint.toConst()));
        },
        .comptime_int => {
            var buffer: InternPool.Key.Int.Storage.BigIntSpace = undefined;
            var operand_bigint = try pool.indexToKey(val.index).int.storage.toBigInt(&buffer).toManaged(arena);
            operand_bigint.abs();
            return .fromIndex(try pool.internComptimeInt(operand_bigint.toConst()));
        },
        .comptime_float, .float => {
            const storage: InternPool.Key.Float.Storage = switch (ty.floatBits()) {
                16 => .{ .f16 = @abs(val.toFloat(f16, pool)) },
                32 => .{ .f32 = @abs(val.toFloat(f32, pool)) },
                64 => .{ .f64 = @abs(val.toFloat(f64, pool)) },
                80 => .{ .f80 = @abs(val.toFloat(f80, pool)) },
                128 => .{ .f128 = @abs(val.toFloat(f128, pool)) },
                else => unreachable,
            };
            return .fromIndex(try pool.internFloat(.{ .ty = ty.index, .storage = storage }));
        },
        else => unreachable,
    }
}

pub const void_value: Value = .{ .index = .void_value };
pub const bool_true: Value = .{ .index = .bool_true };
pub const bool_false: Value = .{ .index = .bool_false };
