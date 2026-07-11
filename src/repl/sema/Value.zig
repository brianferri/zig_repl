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

// The unary float builtins. Each pair ports the compiler's `Value.<op>` /
// `<op>Scalar`: a vector folds elementwise into an arena buffer, a scalar folds
// directly via the `floatBits` switch over `toFloat` at each width.

pub fn sqrt(val: Value, float_type: Type, arena: std.mem.Allocator, pool: *InternPool) std.mem.Allocator.Error!Value {
    if (float_type.zigTypeTag(pool) == .vector) {
        const result_data = try arena.alloc(InternPool.Index, float_type.vectorLen(pool));
        const scalar_ty = float_type.scalarType(pool);
        for (result_data, 0..) |*scalar, i| {
            const elem_val = try val.elemValue(pool, i);
            scalar.* = (try sqrtScalar(elem_val, scalar_ty, pool)).index;
        }
        return .fromIndex(try pool.internAggregate(.{ .ty = float_type.index, .storage = .{ .elems = result_data } }));
    }
    return sqrtScalar(val, float_type, pool);
}

pub fn sqrtScalar(val: Value, float_type: Type, pool: *InternPool) std.mem.Allocator.Error!Value {
    const storage: InternPool.Key.Float.Storage = switch (float_type.floatBits()) {
        16 => .{ .f16 = @sqrt(val.toFloat(f16, pool)) },
        32 => .{ .f32 = @sqrt(val.toFloat(f32, pool)) },
        64 => .{ .f64 = @sqrt(val.toFloat(f64, pool)) },
        80 => .{ .f80 = @sqrt(val.toFloat(f80, pool)) },
        128 => .{ .f128 = @sqrt(val.toFloat(f128, pool)) },
        else => unreachable,
    };
    return .fromIndex(try pool.internFloat(.{ .ty = float_type.index, .storage = storage }));
}

pub fn sin(val: Value, float_type: Type, arena: std.mem.Allocator, pool: *InternPool) std.mem.Allocator.Error!Value {
    if (float_type.zigTypeTag(pool) == .vector) {
        const result_data = try arena.alloc(InternPool.Index, float_type.vectorLen(pool));
        const scalar_ty = float_type.scalarType(pool);
        for (result_data, 0..) |*scalar, i| {
            const elem_val = try val.elemValue(pool, i);
            scalar.* = (try sinScalar(elem_val, scalar_ty, pool)).index;
        }
        return .fromIndex(try pool.internAggregate(.{ .ty = float_type.index, .storage = .{ .elems = result_data } }));
    }
    return sinScalar(val, float_type, pool);
}

pub fn sinScalar(val: Value, float_type: Type, pool: *InternPool) std.mem.Allocator.Error!Value {
    const storage: InternPool.Key.Float.Storage = switch (float_type.floatBits()) {
        16 => .{ .f16 = @sin(val.toFloat(f16, pool)) },
        32 => .{ .f32 = @sin(val.toFloat(f32, pool)) },
        64 => .{ .f64 = @sin(val.toFloat(f64, pool)) },
        80 => .{ .f80 = @sin(val.toFloat(f80, pool)) },
        128 => .{ .f128 = @sin(val.toFloat(f128, pool)) },
        else => unreachable,
    };
    return .fromIndex(try pool.internFloat(.{ .ty = float_type.index, .storage = storage }));
}

pub fn cos(val: Value, float_type: Type, arena: std.mem.Allocator, pool: *InternPool) std.mem.Allocator.Error!Value {
    if (float_type.zigTypeTag(pool) == .vector) {
        const result_data = try arena.alloc(InternPool.Index, float_type.vectorLen(pool));
        const scalar_ty = float_type.scalarType(pool);
        for (result_data, 0..) |*scalar, i| {
            const elem_val = try val.elemValue(pool, i);
            scalar.* = (try cosScalar(elem_val, scalar_ty, pool)).index;
        }
        return .fromIndex(try pool.internAggregate(.{ .ty = float_type.index, .storage = .{ .elems = result_data } }));
    }
    return cosScalar(val, float_type, pool);
}

pub fn cosScalar(val: Value, float_type: Type, pool: *InternPool) std.mem.Allocator.Error!Value {
    const storage: InternPool.Key.Float.Storage = switch (float_type.floatBits()) {
        16 => .{ .f16 = @cos(val.toFloat(f16, pool)) },
        32 => .{ .f32 = @cos(val.toFloat(f32, pool)) },
        64 => .{ .f64 = @cos(val.toFloat(f64, pool)) },
        80 => .{ .f80 = @cos(val.toFloat(f80, pool)) },
        128 => .{ .f128 = @cos(val.toFloat(f128, pool)) },
        else => unreachable,
    };
    return .fromIndex(try pool.internFloat(.{ .ty = float_type.index, .storage = storage }));
}

pub fn tan(val: Value, float_type: Type, arena: std.mem.Allocator, pool: *InternPool) std.mem.Allocator.Error!Value {
    if (float_type.zigTypeTag(pool) == .vector) {
        const result_data = try arena.alloc(InternPool.Index, float_type.vectorLen(pool));
        const scalar_ty = float_type.scalarType(pool);
        for (result_data, 0..) |*scalar, i| {
            const elem_val = try val.elemValue(pool, i);
            scalar.* = (try tanScalar(elem_val, scalar_ty, pool)).index;
        }
        return .fromIndex(try pool.internAggregate(.{ .ty = float_type.index, .storage = .{ .elems = result_data } }));
    }
    return tanScalar(val, float_type, pool);
}

pub fn tanScalar(val: Value, float_type: Type, pool: *InternPool) std.mem.Allocator.Error!Value {
    const storage: InternPool.Key.Float.Storage = switch (float_type.floatBits()) {
        16 => .{ .f16 = @tan(val.toFloat(f16, pool)) },
        32 => .{ .f32 = @tan(val.toFloat(f32, pool)) },
        64 => .{ .f64 = @tan(val.toFloat(f64, pool)) },
        80 => .{ .f80 = @tan(val.toFloat(f80, pool)) },
        128 => .{ .f128 = @tan(val.toFloat(f128, pool)) },
        else => unreachable,
    };
    return .fromIndex(try pool.internFloat(.{ .ty = float_type.index, .storage = storage }));
}

pub fn exp(val: Value, float_type: Type, arena: std.mem.Allocator, pool: *InternPool) std.mem.Allocator.Error!Value {
    if (float_type.zigTypeTag(pool) == .vector) {
        const result_data = try arena.alloc(InternPool.Index, float_type.vectorLen(pool));
        const scalar_ty = float_type.scalarType(pool);
        for (result_data, 0..) |*scalar, i| {
            const elem_val = try val.elemValue(pool, i);
            scalar.* = (try expScalar(elem_val, scalar_ty, pool)).index;
        }
        return .fromIndex(try pool.internAggregate(.{ .ty = float_type.index, .storage = .{ .elems = result_data } }));
    }
    return expScalar(val, float_type, pool);
}

pub fn expScalar(val: Value, float_type: Type, pool: *InternPool) std.mem.Allocator.Error!Value {
    const storage: InternPool.Key.Float.Storage = switch (float_type.floatBits()) {
        16 => .{ .f16 = @exp(val.toFloat(f16, pool)) },
        32 => .{ .f32 = @exp(val.toFloat(f32, pool)) },
        64 => .{ .f64 = @exp(val.toFloat(f64, pool)) },
        80 => .{ .f80 = @exp(val.toFloat(f80, pool)) },
        128 => .{ .f128 = @exp(val.toFloat(f128, pool)) },
        else => unreachable,
    };
    return .fromIndex(try pool.internFloat(.{ .ty = float_type.index, .storage = storage }));
}

pub fn exp2(val: Value, float_type: Type, arena: std.mem.Allocator, pool: *InternPool) std.mem.Allocator.Error!Value {
    if (float_type.zigTypeTag(pool) == .vector) {
        const result_data = try arena.alloc(InternPool.Index, float_type.vectorLen(pool));
        const scalar_ty = float_type.scalarType(pool);
        for (result_data, 0..) |*scalar, i| {
            const elem_val = try val.elemValue(pool, i);
            scalar.* = (try exp2Scalar(elem_val, scalar_ty, pool)).index;
        }
        return .fromIndex(try pool.internAggregate(.{ .ty = float_type.index, .storage = .{ .elems = result_data } }));
    }
    return exp2Scalar(val, float_type, pool);
}

pub fn exp2Scalar(val: Value, float_type: Type, pool: *InternPool) std.mem.Allocator.Error!Value {
    const storage: InternPool.Key.Float.Storage = switch (float_type.floatBits()) {
        16 => .{ .f16 = @exp2(val.toFloat(f16, pool)) },
        32 => .{ .f32 = @exp2(val.toFloat(f32, pool)) },
        64 => .{ .f64 = @exp2(val.toFloat(f64, pool)) },
        80 => .{ .f80 = @exp2(val.toFloat(f80, pool)) },
        128 => .{ .f128 = @exp2(val.toFloat(f128, pool)) },
        else => unreachable,
    };
    return .fromIndex(try pool.internFloat(.{ .ty = float_type.index, .storage = storage }));
}

pub fn log(val: Value, float_type: Type, arena: std.mem.Allocator, pool: *InternPool) std.mem.Allocator.Error!Value {
    if (float_type.zigTypeTag(pool) == .vector) {
        const result_data = try arena.alloc(InternPool.Index, float_type.vectorLen(pool));
        const scalar_ty = float_type.scalarType(pool);
        for (result_data, 0..) |*scalar, i| {
            const elem_val = try val.elemValue(pool, i);
            scalar.* = (try logScalar(elem_val, scalar_ty, pool)).index;
        }
        return .fromIndex(try pool.internAggregate(.{ .ty = float_type.index, .storage = .{ .elems = result_data } }));
    }
    return logScalar(val, float_type, pool);
}

pub fn logScalar(val: Value, float_type: Type, pool: *InternPool) std.mem.Allocator.Error!Value {
    const storage: InternPool.Key.Float.Storage = switch (float_type.floatBits()) {
        16 => .{ .f16 = @log(val.toFloat(f16, pool)) },
        32 => .{ .f32 = @log(val.toFloat(f32, pool)) },
        64 => .{ .f64 = @log(val.toFloat(f64, pool)) },
        80 => .{ .f80 = @log(val.toFloat(f80, pool)) },
        128 => .{ .f128 = @log(val.toFloat(f128, pool)) },
        else => unreachable,
    };
    return .fromIndex(try pool.internFloat(.{ .ty = float_type.index, .storage = storage }));
}

pub fn log2(val: Value, float_type: Type, arena: std.mem.Allocator, pool: *InternPool) std.mem.Allocator.Error!Value {
    if (float_type.zigTypeTag(pool) == .vector) {
        const result_data = try arena.alloc(InternPool.Index, float_type.vectorLen(pool));
        const scalar_ty = float_type.scalarType(pool);
        for (result_data, 0..) |*scalar, i| {
            const elem_val = try val.elemValue(pool, i);
            scalar.* = (try log2Scalar(elem_val, scalar_ty, pool)).index;
        }
        return .fromIndex(try pool.internAggregate(.{ .ty = float_type.index, .storage = .{ .elems = result_data } }));
    }
    return log2Scalar(val, float_type, pool);
}

pub fn log2Scalar(val: Value, float_type: Type, pool: *InternPool) std.mem.Allocator.Error!Value {
    const storage: InternPool.Key.Float.Storage = switch (float_type.floatBits()) {
        16 => .{ .f16 = @log2(val.toFloat(f16, pool)) },
        32 => .{ .f32 = @log2(val.toFloat(f32, pool)) },
        64 => .{ .f64 = @log2(val.toFloat(f64, pool)) },
        80 => .{ .f80 = @log2(val.toFloat(f80, pool)) },
        128 => .{ .f128 = @log2(val.toFloat(f128, pool)) },
        else => unreachable,
    };
    return .fromIndex(try pool.internFloat(.{ .ty = float_type.index, .storage = storage }));
}

pub fn log10(val: Value, float_type: Type, arena: std.mem.Allocator, pool: *InternPool) std.mem.Allocator.Error!Value {
    if (float_type.zigTypeTag(pool) == .vector) {
        const result_data = try arena.alloc(InternPool.Index, float_type.vectorLen(pool));
        const scalar_ty = float_type.scalarType(pool);
        for (result_data, 0..) |*scalar, i| {
            const elem_val = try val.elemValue(pool, i);
            scalar.* = (try log10Scalar(elem_val, scalar_ty, pool)).index;
        }
        return .fromIndex(try pool.internAggregate(.{ .ty = float_type.index, .storage = .{ .elems = result_data } }));
    }
    return log10Scalar(val, float_type, pool);
}

pub fn log10Scalar(val: Value, float_type: Type, pool: *InternPool) std.mem.Allocator.Error!Value {
    const storage: InternPool.Key.Float.Storage = switch (float_type.floatBits()) {
        16 => .{ .f16 = @log10(val.toFloat(f16, pool)) },
        32 => .{ .f32 = @log10(val.toFloat(f32, pool)) },
        64 => .{ .f64 = @log10(val.toFloat(f64, pool)) },
        80 => .{ .f80 = @log10(val.toFloat(f80, pool)) },
        128 => .{ .f128 = @log10(val.toFloat(f128, pool)) },
        else => unreachable,
    };
    return .fromIndex(try pool.internFloat(.{ .ty = float_type.index, .storage = storage }));
}

pub fn floor(val: Value, float_type: Type, arena: std.mem.Allocator, pool: *InternPool) std.mem.Allocator.Error!Value {
    if (float_type.zigTypeTag(pool) == .vector) {
        const result_data = try arena.alloc(InternPool.Index, float_type.vectorLen(pool));
        const scalar_ty = float_type.scalarType(pool);
        for (result_data, 0..) |*scalar, i| {
            const elem_val = try val.elemValue(pool, i);
            scalar.* = (try floorScalar(elem_val, scalar_ty, pool)).index;
        }
        return .fromIndex(try pool.internAggregate(.{ .ty = float_type.index, .storage = .{ .elems = result_data } }));
    }
    return floorScalar(val, float_type, pool);
}

pub fn floorScalar(val: Value, float_type: Type, pool: *InternPool) std.mem.Allocator.Error!Value {
    const storage: InternPool.Key.Float.Storage = switch (float_type.floatBits()) {
        16 => .{ .f16 = @floor(val.toFloat(f16, pool)) },
        32 => .{ .f32 = @floor(val.toFloat(f32, pool)) },
        64 => .{ .f64 = @floor(val.toFloat(f64, pool)) },
        80 => .{ .f80 = @floor(val.toFloat(f80, pool)) },
        128 => .{ .f128 = @floor(val.toFloat(f128, pool)) },
        else => unreachable,
    };
    return .fromIndex(try pool.internFloat(.{ .ty = float_type.index, .storage = storage }));
}

pub fn ceil(val: Value, float_type: Type, arena: std.mem.Allocator, pool: *InternPool) std.mem.Allocator.Error!Value {
    if (float_type.zigTypeTag(pool) == .vector) {
        const result_data = try arena.alloc(InternPool.Index, float_type.vectorLen(pool));
        const scalar_ty = float_type.scalarType(pool);
        for (result_data, 0..) |*scalar, i| {
            const elem_val = try val.elemValue(pool, i);
            scalar.* = (try ceilScalar(elem_val, scalar_ty, pool)).index;
        }
        return .fromIndex(try pool.internAggregate(.{ .ty = float_type.index, .storage = .{ .elems = result_data } }));
    }
    return ceilScalar(val, float_type, pool);
}

pub fn ceilScalar(val: Value, float_type: Type, pool: *InternPool) std.mem.Allocator.Error!Value {
    const storage: InternPool.Key.Float.Storage = switch (float_type.floatBits()) {
        16 => .{ .f16 = @ceil(val.toFloat(f16, pool)) },
        32 => .{ .f32 = @ceil(val.toFloat(f32, pool)) },
        64 => .{ .f64 = @ceil(val.toFloat(f64, pool)) },
        80 => .{ .f80 = @ceil(val.toFloat(f80, pool)) },
        128 => .{ .f128 = @ceil(val.toFloat(f128, pool)) },
        else => unreachable,
    };
    return .fromIndex(try pool.internFloat(.{ .ty = float_type.index, .storage = storage }));
}

pub fn round(val: Value, float_type: Type, arena: std.mem.Allocator, pool: *InternPool) std.mem.Allocator.Error!Value {
    if (float_type.zigTypeTag(pool) == .vector) {
        const result_data = try arena.alloc(InternPool.Index, float_type.vectorLen(pool));
        const scalar_ty = float_type.scalarType(pool);
        for (result_data, 0..) |*scalar, i| {
            const elem_val = try val.elemValue(pool, i);
            scalar.* = (try roundScalar(elem_val, scalar_ty, pool)).index;
        }
        return .fromIndex(try pool.internAggregate(.{ .ty = float_type.index, .storage = .{ .elems = result_data } }));
    }
    return roundScalar(val, float_type, pool);
}

pub fn roundScalar(val: Value, float_type: Type, pool: *InternPool) std.mem.Allocator.Error!Value {
    const storage: InternPool.Key.Float.Storage = switch (float_type.floatBits()) {
        16 => .{ .f16 = @round(val.toFloat(f16, pool)) },
        32 => .{ .f32 = @round(val.toFloat(f32, pool)) },
        64 => .{ .f64 = @round(val.toFloat(f64, pool)) },
        80 => .{ .f80 = @round(val.toFloat(f80, pool)) },
        128 => .{ .f128 = @round(val.toFloat(f128, pool)) },
        else => unreachable,
    };
    return .fromIndex(try pool.internFloat(.{ .ty = float_type.index, .storage = storage }));
}

pub fn trunc(val: Value, float_type: Type, arena: std.mem.Allocator, pool: *InternPool) std.mem.Allocator.Error!Value {
    if (float_type.zigTypeTag(pool) == .vector) {
        const result_data = try arena.alloc(InternPool.Index, float_type.vectorLen(pool));
        const scalar_ty = float_type.scalarType(pool);
        for (result_data, 0..) |*scalar, i| {
            const elem_val = try val.elemValue(pool, i);
            scalar.* = (try truncScalar(elem_val, scalar_ty, pool)).index;
        }
        return .fromIndex(try pool.internAggregate(.{ .ty = float_type.index, .storage = .{ .elems = result_data } }));
    }
    return truncScalar(val, float_type, pool);
}

pub fn truncScalar(val: Value, float_type: Type, pool: *InternPool) std.mem.Allocator.Error!Value {
    const storage: InternPool.Key.Float.Storage = switch (float_type.floatBits()) {
        16 => .{ .f16 = @trunc(val.toFloat(f16, pool)) },
        32 => .{ .f32 = @trunc(val.toFloat(f32, pool)) },
        64 => .{ .f64 = @trunc(val.toFloat(f64, pool)) },
        80 => .{ .f80 = @trunc(val.toFloat(f80, pool)) },
        128 => .{ .f128 = @trunc(val.toFloat(f128, pool)) },
        else => unreachable,
    };
    return .fromIndex(try pool.internFloat(.{ .ty = float_type.index, .storage = storage }));
}

/// The value as a `std.math.big.int.Const`, borrowing into `space` for the
/// `.u64`/`.i64` storage forms. Ports `Value.toBigInt` (the REPL stores no lazy
/// int, so it reads `int.storage.toBigInt` directly).
pub fn toBigInt(val: Value, space: *InternPool.Key.Int.Storage.BigIntSpace, pool: *const InternPool) std.math.big.int.Const {
    return pool.indexToKey(val.index).int.storage.toBigInt(space);
}

/// `@clz`/`@ctz`/`@popCount` of one integer value at `ty`'s width, via the same
/// `std.math.big.int.Const` methods. Port `Value.clz`/`ctz`/`popCount`.
pub fn clz(val: Value, ty: Type, pool: *const InternPool) u64 {
    var bigint_buf: InternPool.Key.Int.Storage.BigIntSpace = undefined;
    const bigint = val.toBigInt(&bigint_buf, pool);
    return bigint.clz(ty.intInfo(pool).?.bits);
}

pub fn ctz(val: Value, ty: Type, pool: *const InternPool) u64 {
    var bigint_buf: InternPool.Key.Int.Storage.BigIntSpace = undefined;
    const bigint = val.toBigInt(&bigint_buf, pool);
    return bigint.ctz(ty.intInfo(pool).?.bits);
}

pub fn popCount(val: Value, ty: Type, pool: *const InternPool) u64 {
    var bigint_buf: InternPool.Key.Int.Storage.BigIntSpace = undefined;
    const bigint = val.toBigInt(&bigint_buf, pool);
    return @intCast(bigint.popCount(ty.intInfo(pool).?.bits));
}

pub const void_value: Value = .{ .index = .void_value };
pub const bool_true: Value = .{ .index = .bool_true };
pub const bool_false: Value = .{ .index = .bool_false };
