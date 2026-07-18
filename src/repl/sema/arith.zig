const std = @import("std");
const builtin = @import("builtin");
const assert = std.debug.assert;
const Allocator = std.mem.Allocator;
const BigIntConst = std.math.big.int.Const;
const BigIntMutable = std.math.big.int.Mutable;
const Limb = std.math.big.Limb;

const InternPool = @import("InternPool.zig");
const Sema = @import("Sema.zig");
const Value = @import("Value.zig");
const Type = @import("Type.zig");
const BigIntSpace = InternPool.Key.Int.Storage.BigIntSpace;
const comptime_int_ty: Type = .fromIndex(.comptime_int_type);
const u1_ty: Type = .fromIndex(.u1_type);

pub fn incrementDefinedInt(sema: *Sema, ty: Type, prev_val: Value) !struct { overflow: bool, val: Value } {
    const pool = sema.intern_pool;
    assert(Value.typeOf(prev_val, pool).index == ty.index);
    assert(!prev_val.isUndef(pool));
    if (ty.index == .u0_type) {
        return .{ .overflow = true, .val = try comptimeIntAdd(sema, prev_val, .one_comptime_int) };
    }
    const res = try intAdd(sema, prev_val, try sema.intValue_u64(ty, 1), ty);
    return .{ .overflow = res.overflow, .val = res.val };
}

pub fn negateFloat(sema: *Sema, ty: Type, val: Value) !Value {
    const pool = sema.intern_pool;
    if (val.isUndef(pool)) return val;
    switch (ty.zigTypeTag(pool)) {
        .vector => {
            const scalar_ty = ty.childType(pool);
            const len = ty.vectorLen(pool);
            const result_elems = try sema.arena.alloc(InternPool.Index, len);
            for (result_elems, 0..) |*result_elem, elem_idx| {
                const elem = try val.elemValue(pool, elem_idx);
                if (elem.isUndef(pool)) {
                    result_elem.* = elem.index;
                } else {
                    result_elem.* = (try floatNeg(sema, elem, scalar_ty)).index;
                }
            }
            return sema.aggregateValue(ty, result_elems);
        },
        .float, .comptime_float => return floatNeg(sema, val, ty),
        else => unreachable,
    }
}

pub fn addMaybeWrap(sema: *Sema, ty: Type, lhs: Value, rhs: Value) !Value {
    const pool = sema.intern_pool;
    if (lhs.isUndef(pool)) return lhs;
    if (rhs.isUndef(pool)) return rhs;
    switch (ty.zigTypeTag(pool)) {
        .int, .comptime_int => return (try intAddWithOverflow(sema, lhs, rhs, ty)).wrapped_result,
        .float, .comptime_float => return floatAdd(sema, lhs, rhs, ty),
        else => unreachable,
    }
}

pub fn subMaybeWrap(sema: *Sema, ty: Type, lhs: Value, rhs: Value) !Value {
    const pool = sema.intern_pool;
    if (lhs.isUndef(pool)) return lhs;
    if (rhs.isUndef(pool)) return rhs;
    switch (ty.zigTypeTag(pool)) {
        .int, .comptime_int => return (try intSubWithOverflow(sema, lhs, rhs, ty)).wrapped_result,
        .float, .comptime_float => return floatSub(sema, lhs, rhs, ty),
        else => unreachable,
    }
}

pub fn mulMaybeWrap(sema: *Sema, ty: Type, lhs: Value, rhs: Value) !Value {
    const pool = sema.intern_pool;
    if (lhs.isUndef(pool)) return lhs;
    if (rhs.isUndef(pool)) return rhs;
    switch (ty.zigTypeTag(pool)) {
        .int, .comptime_int => return (try intMulWithOverflow(sema, lhs, rhs, ty)).wrapped_result,
        .float, .comptime_float => return floatMul(sema, lhs, rhs, ty),
        else => unreachable,
    }
}

pub fn addWithOverflow(sema: *Sema, ty: Type, lhs: Value, rhs: Value) !Value.OverflowArithmeticResult {
    const pool = sema.intern_pool;
    switch (ty.zigTypeTag(pool)) {
        .int, .comptime_int => return addWithOverflowScalar(sema, ty, lhs, rhs),
        .vector => {
            const scalar_ty = ty.childType(pool);
            const len = ty.vectorLen(pool);
            switch (scalar_ty.zigTypeTag(pool)) {
                .int, .comptime_int => {},
                else => unreachable,
            }
            const overflow_bits = try sema.arena.alloc(InternPool.Index, len);
            const wrapped_results = try sema.arena.alloc(InternPool.Index, len);
            for (overflow_bits, wrapped_results, 0..) |*ob, *wr, elem_idx| {
                const lhs_elem = try lhs.elemValue(pool, elem_idx);
                const rhs_elem = try rhs.elemValue(pool, elem_idx);
                const elem_result = try addWithOverflowScalar(sema, scalar_ty, lhs_elem, rhs_elem);
                ob.* = elem_result.overflow_bit.index;
                wr.* = elem_result.wrapped_result.index;
            }
            return .{
                .overflow_bit = try sema.aggregateValue(
                    try sema.vectorType(.{ .len = @intCast(overflow_bits.len), .child = .u1_type }),
                    overflow_bits,
                ),
                .wrapped_result = try sema.aggregateValue(ty, wrapped_results),
            };
        },
        else => unreachable,
    }
}
fn addWithOverflowScalar(sema: *Sema, ty: Type, lhs: Value, rhs: Value) !Value.OverflowArithmeticResult {
    const pool = sema.intern_pool;
    switch (ty.zigTypeTag(pool)) {
        .int, .comptime_int => {},
        else => unreachable,
    }
    if (lhs.isUndef(pool) or rhs.isUndef(pool)) return .{
        .overflow_bit = .undef_u1,
        .wrapped_result = try sema.undefValue(ty),
    };
    return intAddWithOverflow(sema, lhs, rhs, ty);
}

pub fn subWithOverflow(sema: *Sema, ty: Type, lhs: Value, rhs: Value) !Value.OverflowArithmeticResult {
    const pool = sema.intern_pool;
    switch (ty.zigTypeTag(pool)) {
        .int, .comptime_int => return subWithOverflowScalar(sema, ty, lhs, rhs),
        .vector => {
            const scalar_ty = ty.childType(pool);
            const len = ty.vectorLen(pool);
            switch (scalar_ty.zigTypeTag(pool)) {
                .int, .comptime_int => {},
                else => unreachable,
            }
            const overflow_bits = try sema.arena.alloc(InternPool.Index, len);
            const wrapped_results = try sema.arena.alloc(InternPool.Index, len);
            for (overflow_bits, wrapped_results, 0..) |*ob, *wr, elem_idx| {
                const lhs_elem = try lhs.elemValue(pool, elem_idx);
                const rhs_elem = try rhs.elemValue(pool, elem_idx);
                const elem_result = try subWithOverflowScalar(sema, scalar_ty, lhs_elem, rhs_elem);
                ob.* = elem_result.overflow_bit.index;
                wr.* = elem_result.wrapped_result.index;
            }
            return .{
                .overflow_bit = try sema.aggregateValue(
                    try sema.vectorType(.{ .len = @intCast(overflow_bits.len), .child = .u1_type }),
                    overflow_bits,
                ),
                .wrapped_result = try sema.aggregateValue(ty, wrapped_results),
            };
        },
        else => unreachable,
    }
}
fn subWithOverflowScalar(sema: *Sema, ty: Type, lhs: Value, rhs: Value) !Value.OverflowArithmeticResult {
    const pool = sema.intern_pool;
    switch (ty.zigTypeTag(pool)) {
        .int, .comptime_int => {},
        else => unreachable,
    }
    if (lhs.isUndef(pool) or rhs.isUndef(pool)) return .{
        .overflow_bit = .undef_u1,
        .wrapped_result = try sema.undefValue(ty),
    };
    return intSubWithOverflow(sema, lhs, rhs, ty);
}

pub fn mulWithOverflow(sema: *Sema, ty: Type, lhs: Value, rhs: Value) !Value.OverflowArithmeticResult {
    const pool = sema.intern_pool;
    switch (ty.zigTypeTag(pool)) {
        .int, .comptime_int => return mulWithOverflowScalar(sema, ty, lhs, rhs),
        .vector => {
            const scalar_ty = ty.childType(pool);
            const len = ty.vectorLen(pool);
            switch (scalar_ty.zigTypeTag(pool)) {
                .int, .comptime_int => {},
                else => unreachable,
            }
            const overflow_bits = try sema.arena.alloc(InternPool.Index, len);
            const wrapped_results = try sema.arena.alloc(InternPool.Index, len);
            for (overflow_bits, wrapped_results, 0..) |*ob, *wr, elem_idx| {
                const lhs_elem = try lhs.elemValue(pool, elem_idx);
                const rhs_elem = try rhs.elemValue(pool, elem_idx);
                const elem_result = try mulWithOverflowScalar(sema, scalar_ty, lhs_elem, rhs_elem);
                ob.* = elem_result.overflow_bit.index;
                wr.* = elem_result.wrapped_result.index;
            }
            return .{
                .overflow_bit = try sema.aggregateValue(
                    try sema.vectorType(.{ .len = @intCast(overflow_bits.len), .child = .u1_type }),
                    overflow_bits,
                ),
                .wrapped_result = try sema.aggregateValue(ty, wrapped_results),
            };
        },
        else => unreachable,
    }
}
fn mulWithOverflowScalar(sema: *Sema, ty: Type, lhs: Value, rhs: Value) !Value.OverflowArithmeticResult {
    const pool = sema.intern_pool;
    switch (ty.zigTypeTag(pool)) {
        .int, .comptime_int => {},
        else => unreachable,
    }
    if (lhs.isUndef(pool) or rhs.isUndef(pool)) return .{
        .overflow_bit = .undef_u1,
        .wrapped_result = try sema.undefValue(ty),
    };
    return intMulWithOverflow(sema, lhs, rhs, ty);
}

pub fn add(sema: *Sema, ty: Type, lhs_val: Value, rhs_val: Value) !Value {
    const pool = sema.intern_pool;
    switch (ty.zigTypeTag(pool)) {
        .int, .comptime_int => return addScalar(sema, ty, lhs_val, rhs_val, true),
        .float, .comptime_float => return addScalar(sema, ty, lhs_val, rhs_val, false),
        .vector => {
            const elem_ty = ty.childType(pool);
            const len = ty.vectorLen(pool);
            const is_int = switch (elem_ty.zigTypeTag(pool)) {
                .int, .comptime_int => true,
                .float, .comptime_float => false,
                else => unreachable,
            };
            const elem_vals = try sema.arena.alloc(InternPool.Index, len);
            for (elem_vals, 0..) |*result_elem, elem_idx| {
                const lhs_elem = try lhs_val.elemValue(pool, elem_idx);
                const rhs_elem = try rhs_val.elemValue(pool, elem_idx);
                result_elem.* = (try addScalar(sema, elem_ty, lhs_elem, rhs_elem, is_int)).index;
            }
            return sema.aggregateValue(ty, elem_vals);
        },
        else => unreachable,
    }
}
fn addScalar(sema: *Sema, ty: Type, lhs_val: Value, rhs_val: Value, is_int: bool) !Value {
    const pool = sema.intern_pool;
    if (is_int) {
        if (lhs_val.isUndef(pool)) return sema.failWithUseOfUndef();
        if (rhs_val.isUndef(pool)) return sema.failWithUseOfUndef();
        const res = try intAdd(sema, lhs_val, rhs_val, ty);
        if (res.overflow) return sema.failWithIntegerOverflow(ty, res.val);
        return res.val;
    } else {
        if (lhs_val.isUndef(pool)) return lhs_val;
        if (rhs_val.isUndef(pool)) return rhs_val;
        return floatAdd(sema, lhs_val, rhs_val, ty);
    }
}

pub fn addWrap(sema: *Sema, ty: Type, lhs_val: Value, rhs_val: Value) !Value {
    const pool = sema.intern_pool;
    switch (ty.zigTypeTag(pool)) {
        .vector => {
            const elem_ty = ty.childType(pool);
            const len = ty.vectorLen(pool);
            const elem_vals = try sema.arena.alloc(InternPool.Index, len);
            for (elem_vals, 0..) |*result_elem, elem_idx| {
                const lhs_elem = try lhs_val.elemValue(pool, elem_idx);
                const rhs_elem = try rhs_val.elemValue(pool, elem_idx);
                result_elem.* = (try addWrapScalar(sema, elem_ty, lhs_elem, rhs_elem)).index;
            }
            return sema.aggregateValue(ty, elem_vals);
        },
        else => return addWrapScalar(sema, ty, lhs_val, rhs_val),
    }
}
fn addWrapScalar(sema: *Sema, ty: Type, lhs_val: Value, rhs_val: Value) !Value {
    return (try addWithOverflowScalar(sema, ty, lhs_val, rhs_val)).wrapped_result;
}

pub fn addSat(sema: *Sema, ty: Type, lhs_val: Value, rhs_val: Value) !Value {
    const pool = sema.intern_pool;
    switch (ty.zigTypeTag(pool)) {
        .vector => {
            const elem_ty = ty.childType(pool);
            const len = ty.vectorLen(pool);
            const elem_vals = try sema.arena.alloc(InternPool.Index, len);
            for (elem_vals, 0..) |*result_elem, elem_idx| {
                const lhs_elem = try lhs_val.elemValue(pool, elem_idx);
                const rhs_elem = try rhs_val.elemValue(pool, elem_idx);
                result_elem.* = (try addSatScalar(sema, elem_ty, lhs_elem, rhs_elem)).index;
            }
            return sema.aggregateValue(ty, elem_vals);
        },
        else => return addSatScalar(sema, ty, lhs_val, rhs_val),
    }
}
fn addSatScalar(sema: *Sema, ty: Type, lhs_val: Value, rhs_val: Value) !Value {
    const pool = sema.intern_pool;
    const is_comptime_int = switch (ty.zigTypeTag(pool)) {
        .int => false,
        .comptime_int => true,
        else => unreachable,
    };
    if (lhs_val.isUndef(pool)) return lhs_val;
    if (rhs_val.isUndef(pool)) return rhs_val;
    if (is_comptime_int) {
        const res = try intAdd(sema, lhs_val, rhs_val, ty);
        assert(!res.overflow);
        return res.val;
    } else {
        return intAddSat(sema, lhs_val, rhs_val, ty);
    }
}

pub fn sub(sema: *Sema, ty: Type, lhs_val: Value, rhs_val: Value) !Value {
    const pool = sema.intern_pool;
    switch (ty.zigTypeTag(pool)) {
        .int, .comptime_int => return subScalar(sema, ty, lhs_val, rhs_val, true),
        .float, .comptime_float => return subScalar(sema, ty, lhs_val, rhs_val, false),
        .vector => {
            const elem_ty = ty.childType(pool);
            const len = ty.vectorLen(pool);
            const is_int = switch (elem_ty.zigTypeTag(pool)) {
                .int, .comptime_int => true,
                .float, .comptime_float => false,
                else => unreachable,
            };
            const elem_vals = try sema.arena.alloc(InternPool.Index, len);
            for (elem_vals, 0..) |*result_elem, elem_idx| {
                const lhs_elem = try lhs_val.elemValue(pool, elem_idx);
                const rhs_elem = try rhs_val.elemValue(pool, elem_idx);
                result_elem.* = (try subScalar(sema, elem_ty, lhs_elem, rhs_elem, is_int)).index;
            }
            return sema.aggregateValue(ty, elem_vals);
        },
        else => unreachable,
    }
}
fn subScalar(sema: *Sema, ty: Type, lhs_val: Value, rhs_val: Value, is_int: bool) !Value {
    const pool = sema.intern_pool;
    if (is_int) {
        if (lhs_val.isUndef(pool)) return sema.failWithUseOfUndef();
        if (rhs_val.isUndef(pool)) return sema.failWithUseOfUndef();
        const res = try intSub(sema, lhs_val, rhs_val, ty);
        if (res.overflow) return sema.failWithIntegerOverflow(ty, res.val);
        return res.val;
    } else {
        if (lhs_val.isUndef(pool)) return lhs_val;
        if (rhs_val.isUndef(pool)) return rhs_val;
        return floatSub(sema, lhs_val, rhs_val, ty);
    }
}

pub fn subWrap(sema: *Sema, ty: Type, lhs_val: Value, rhs_val: Value) !Value {
    const pool = sema.intern_pool;
    switch (ty.zigTypeTag(pool)) {
        .vector => {
            const elem_ty = ty.childType(pool);
            const len = ty.vectorLen(pool);
            const elem_vals = try sema.arena.alloc(InternPool.Index, len);
            for (elem_vals, 0..) |*result_elem, elem_idx| {
                const lhs_elem = try lhs_val.elemValue(pool, elem_idx);
                const rhs_elem = try rhs_val.elemValue(pool, elem_idx);
                result_elem.* = (try subWrapScalar(sema, elem_ty, lhs_elem, rhs_elem)).index;
            }
            return sema.aggregateValue(ty, elem_vals);
        },
        else => return subWrapScalar(sema, ty, lhs_val, rhs_val),
    }
}
fn subWrapScalar(sema: *Sema, ty: Type, lhs_val: Value, rhs_val: Value) !Value {
    const pool = sema.intern_pool;
    switch (ty.zigTypeTag(pool)) {
        .int, .comptime_int => {},
        else => unreachable,
    }
    if (lhs_val.isUndef(pool)) return lhs_val;
    if (rhs_val.isUndef(pool)) return rhs_val;
    const result = try intSubWithOverflow(sema, lhs_val, rhs_val, ty);
    return result.wrapped_result;
}

pub fn subSat(sema: *Sema, ty: Type, lhs_val: Value, rhs_val: Value) !Value {
    const pool = sema.intern_pool;
    switch (ty.zigTypeTag(pool)) {
        .vector => {
            const elem_ty = ty.childType(pool);
            const len = ty.vectorLen(pool);
            const elem_vals = try sema.arena.alloc(InternPool.Index, len);
            for (elem_vals, 0..) |*result_elem, elem_idx| {
                const lhs_elem = try lhs_val.elemValue(pool, elem_idx);
                const rhs_elem = try rhs_val.elemValue(pool, elem_idx);
                result_elem.* = (try subSatScalar(sema, elem_ty, lhs_elem, rhs_elem)).index;
            }
            return sema.aggregateValue(ty, elem_vals);
        },
        else => return subSatScalar(sema, ty, lhs_val, rhs_val),
    }
}
fn subSatScalar(sema: *Sema, ty: Type, lhs_val: Value, rhs_val: Value) !Value {
    const pool = sema.intern_pool;
    const is_comptime_int = switch (ty.zigTypeTag(pool)) {
        .int => false,
        .comptime_int => true,
        else => unreachable,
    };
    if (lhs_val.isUndef(pool)) return lhs_val;
    if (rhs_val.isUndef(pool)) return rhs_val;
    if (is_comptime_int) {
        const res = try intSub(sema, lhs_val, rhs_val, ty);
        assert(!res.overflow);
        return res.val;
    } else {
        return intSubSat(sema, lhs_val, rhs_val, ty);
    }
}

pub fn mul(sema: *Sema, ty: Type, lhs_val: Value, rhs_val: Value) !Value {
    const pool = sema.intern_pool;
    switch (ty.zigTypeTag(pool)) {
        .int, .comptime_int => return mulScalar(sema, ty, lhs_val, rhs_val, true),
        .float, .comptime_float => return mulScalar(sema, ty, lhs_val, rhs_val, false),
        .vector => {
            const elem_ty = ty.childType(pool);
            const len = ty.vectorLen(pool);
            const is_int = switch (elem_ty.zigTypeTag(pool)) {
                .int, .comptime_int => true,
                .float, .comptime_float => false,
                else => unreachable,
            };
            const elem_vals = try sema.arena.alloc(InternPool.Index, len);
            for (elem_vals, 0..) |*result_elem, elem_idx| {
                const lhs_elem = try lhs_val.elemValue(pool, elem_idx);
                const rhs_elem = try rhs_val.elemValue(pool, elem_idx);
                result_elem.* = (try mulScalar(sema, elem_ty, lhs_elem, rhs_elem, is_int)).index;
            }
            return sema.aggregateValue(ty, elem_vals);
        },
        else => unreachable,
    }
}
fn mulScalar(sema: *Sema, ty: Type, lhs_val: Value, rhs_val: Value, is_int: bool) !Value {
    const pool = sema.intern_pool;
    if (is_int) {
        if (lhs_val.isUndef(pool)) return sema.failWithUseOfUndef();
        if (rhs_val.isUndef(pool)) return sema.failWithUseOfUndef();
        const res = try intMul(sema, lhs_val, rhs_val, ty);
        if (res.overflow) return sema.failWithIntegerOverflow(ty, res.val);
        return res.val;
    } else {
        if (lhs_val.isUndef(pool)) return lhs_val;
        if (rhs_val.isUndef(pool)) return rhs_val;
        return floatMul(sema, lhs_val, rhs_val, ty);
    }
}

pub fn mulWrap(sema: *Sema, ty: Type, lhs_val: Value, rhs_val: Value) !Value {
    const pool = sema.intern_pool;
    switch (ty.zigTypeTag(pool)) {
        .vector => {
            const elem_ty = ty.childType(pool);
            const len = ty.vectorLen(pool);
            const elem_vals = try sema.arena.alloc(InternPool.Index, len);
            for (elem_vals, 0..) |*result_elem, elem_idx| {
                const lhs_elem = try lhs_val.elemValue(pool, elem_idx);
                const rhs_elem = try rhs_val.elemValue(pool, elem_idx);
                result_elem.* = (try mulWrapScalar(sema, elem_ty, lhs_elem, rhs_elem)).index;
            }
            return sema.aggregateValue(ty, elem_vals);
        },
        else => return mulWrapScalar(sema, ty, lhs_val, rhs_val),
    }
}
fn mulWrapScalar(sema: *Sema, ty: Type, lhs_val: Value, rhs_val: Value) !Value {
    const pool = sema.intern_pool;
    switch (ty.zigTypeTag(pool)) {
        .int, .comptime_int => {},
        else => unreachable,
    }
    if (lhs_val.isUndef(pool)) return lhs_val;
    if (rhs_val.isUndef(pool)) return rhs_val;
    const result = try intMulWithOverflow(sema, lhs_val, rhs_val, ty);
    return result.wrapped_result;
}

pub fn mulSat(sema: *Sema, ty: Type, lhs_val: Value, rhs_val: Value) !Value {
    const pool = sema.intern_pool;
    switch (ty.zigTypeTag(pool)) {
        .vector => {
            const elem_ty = ty.childType(pool);
            const len = ty.vectorLen(pool);
            const elem_vals = try sema.arena.alloc(InternPool.Index, len);
            for (elem_vals, 0..) |*result_elem, elem_idx| {
                const lhs_elem = try lhs_val.elemValue(pool, elem_idx);
                const rhs_elem = try rhs_val.elemValue(pool, elem_idx);
                result_elem.* = (try mulSatScalar(sema, elem_ty, lhs_elem, rhs_elem)).index;
            }
            return sema.aggregateValue(ty, elem_vals);
        },
        else => return mulSatScalar(sema, ty, lhs_val, rhs_val),
    }
}
fn mulSatScalar(sema: *Sema, ty: Type, lhs_val: Value, rhs_val: Value) !Value {
    const pool = sema.intern_pool;
    const is_comptime_int = switch (ty.zigTypeTag(pool)) {
        .int => false,
        .comptime_int => true,
        else => unreachable,
    };
    if (lhs_val.isUndef(pool)) return lhs_val;
    if (rhs_val.isUndef(pool)) return rhs_val;
    if (is_comptime_int) {
        const res = try intMul(sema, lhs_val, rhs_val, ty);
        assert(!res.overflow);
        return res.val;
    } else {
        return intMulSat(sema, lhs_val, rhs_val, ty);
    }
}

pub fn div(sema: *Sema, ty: Type, lhs_val: Value, rhs_val: Value, op: DivOp) !Value {
    const pool = sema.intern_pool;
    switch (ty.zigTypeTag(pool)) {
        .int, .comptime_int => return divScalar(sema, ty, lhs_val, rhs_val, op, true),
        .float, .comptime_float => return divScalar(sema, ty, lhs_val, rhs_val, op, false),
        .vector => {
            const elem_ty = ty.childType(pool);
            const len = ty.vectorLen(pool);
            const is_int = switch (elem_ty.zigTypeTag(pool)) {
                .int, .comptime_int => true,
                .float, .comptime_float => false,
                else => unreachable,
            };
            const elem_vals = try sema.arena.alloc(InternPool.Index, len);
            for (elem_vals, 0..) |*result_elem, elem_idx| {
                const lhs_elem = try lhs_val.elemValue(pool, elem_idx);
                const rhs_elem = try rhs_val.elemValue(pool, elem_idx);
                result_elem.* = (try divScalar(sema, elem_ty, lhs_elem, rhs_elem, op, is_int)).index;
            }
            return sema.aggregateValue(ty, elem_vals);
        },
        else => unreachable,
    }
}
fn divScalar(sema: *Sema, ty: Type, lhs_val: Value, rhs_val: Value, op: DivOp, is_int: bool) !Value {
    const pool = sema.intern_pool;
    if (is_int) {
        if (rhs_val.eqlScalarNum(.zero_comptime_int, pool)) return sema.failWithDivideByZero();

        if (lhs_val.isUndef(pool)) return sema.failWithUseOfUndef();
        if (rhs_val.isUndef(pool)) return sema.failWithUseOfUndef();

        switch (op) {
            .div, .div_trunc => {
                const res = try intDivTrunc(sema, lhs_val, rhs_val, ty);
                if (res.overflow) return sema.failWithIntegerOverflow(ty, res.val);
                return res.val;
            },
            .div_floor => {
                const res = try intDivFloor(sema, lhs_val, rhs_val, ty);
                if (res.overflow) return sema.failWithIntegerOverflow(ty, res.val);
                return res.val;
            },
            .div_ceil => {
                const res = try intDivCeil(sema, lhs_val, rhs_val, ty);
                if (res.overflow) return sema.failWithIntegerOverflow(ty, res.val);
                return res.val;
            },
            .div_exact => switch (try intDivExact(sema, lhs_val, rhs_val, ty)) {
                .remainder => {
                    return sema.fail(sema.block, sema.block.nodeOffset(.zero), "exact division produced remainder", .{});
                },
                .overflow => |val| return sema.failWithIntegerOverflow(ty, val),
                .success => |val| return val,
            },
        }
    } else {
        const allow_div_zero = switch (op) {
            .div, .div_trunc, .div_floor, .div_ceil => ty.index != .comptime_float_type,
            .div_exact => false,
        };
        if (!allow_div_zero) {
            if (rhs_val.eqlScalarNum(.zero_comptime_int, pool)) return sema.failWithDivideByZero();
        }

        const can_exhibit_ib = !allow_div_zero or op == .div_exact;
        if (can_exhibit_ib) {
            if (lhs_val.isUndef(pool)) return sema.failWithUseOfUndef();
            if (rhs_val.isUndef(pool)) return sema.failWithUseOfUndef();
        } else {
            if (lhs_val.isUndef(pool)) return lhs_val;
            if (rhs_val.isUndef(pool)) return rhs_val;
        }

        switch (op) {
            .div => return floatDiv(sema, lhs_val, rhs_val, ty),
            .div_trunc => return floatDivTrunc(sema, lhs_val, rhs_val, ty),
            .div_floor => return floatDivFloor(sema, lhs_val, rhs_val, ty),
            .div_ceil => return floatDivCeil(sema, lhs_val, rhs_val, ty),
            .div_exact => {
                if (!floatDivIsExact(sema, lhs_val, rhs_val, ty)) {
                    return sema.fail(sema.block, sema.block.nodeOffset(.zero), "exact division produced remainder", .{});
                }
                return floatDivTrunc(sema, lhs_val, rhs_val, ty);
            },
        }
    }
}

pub fn modRem(sema: *Sema, ty: Type, lhs_val: Value, rhs_val: Value, op: ModRemOp) !Value {
    const pool = sema.intern_pool;
    switch (ty.zigTypeTag(pool)) {
        .vector => {
            const elem_ty = ty.childType(pool);
            const len = ty.vectorLen(pool);
            const elem_vals = try sema.arena.alloc(InternPool.Index, len);
            for (elem_vals, 0..) |*result_elem, elem_idx| {
                const lhs_elem = try lhs_val.elemValue(pool, elem_idx);
                const rhs_elem = try rhs_val.elemValue(pool, elem_idx);
                result_elem.* = (try modRemScalar(sema, elem_ty, lhs_elem, rhs_elem, op)).index;
            }
            return sema.aggregateValue(ty, elem_vals);
        },
        else => return modRemScalar(sema, ty, lhs_val, rhs_val, op),
    }
}
fn modRemScalar(sema: *Sema, ty: Type, lhs_val: Value, rhs_val: Value, op: ModRemOp) !Value {
    const pool = sema.intern_pool;
    const is_int = switch (ty.zigTypeTag(pool)) {
        .int, .comptime_int => true,
        .float, .comptime_float => false,
        else => unreachable,
    };

    const allow_div_zero = !is_int;
    if (allow_div_zero) {
        if (lhs_val.isUndef(pool)) return lhs_val;
        if (rhs_val.isUndef(pool)) return rhs_val;
    } else {
        if (lhs_val.isUndef(pool)) return sema.failWithUseOfUndef();
        if (rhs_val.isUndef(pool)) return sema.failWithUseOfUndef();
        if (rhs_val.eqlScalarNum(.zero_comptime_int, pool)) return sema.failWithDivideByZero();
    }

    if (is_int) {
        switch (op) {
            .mod => return intMod(sema, lhs_val, rhs_val, ty),
            .rem => return intRem(sema, lhs_val, rhs_val, ty),
        }
    } else {
        switch (op) {
            .mod => return floatMod(sema, lhs_val, rhs_val, ty),
            .rem => return floatRem(sema, lhs_val, rhs_val, ty),
        }
    }
}

pub fn shl(sema: *Sema, lhs_ty: Type, lhs_val: Value, rhs_val: Value, op: ShlOp) !Value {
    const pool = sema.intern_pool;
    switch (lhs_ty.zigTypeTag(pool)) {
        .int, .comptime_int => return shlScalar(sema, lhs_ty, lhs_val, rhs_val, op),
        .vector => {
            const lhs_elem_ty = lhs_ty.childType(pool);
            const len = lhs_ty.vectorLen(pool);
            const elem_vals = try sema.arena.alloc(InternPool.Index, len);
            for (elem_vals, 0..) |*result_elem, elem_idx| {
                const lhs_elem = try lhs_val.elemValue(pool, elem_idx);
                const rhs_elem = try rhs_val.elemValue(pool, elem_idx);
                result_elem.* = (try shlScalar(sema, lhs_elem_ty, lhs_elem, rhs_elem, op)).index;
            }
            return sema.aggregateValue(lhs_ty, elem_vals);
        },
        else => unreachable,
    }
}
pub fn shlWithOverflow(sema: *Sema, lhs_ty: Type, lhs_val: Value, rhs_val: Value) !Value.OverflowArithmeticResult {
    const pool = sema.intern_pool;
    switch (lhs_ty.zigTypeTag(pool)) {
        .int, .comptime_int => return shlWithOverflowScalar(sema, lhs_ty, lhs_val, rhs_val),
        .vector => {
            const lhs_elem_ty = lhs_ty.childType(pool);
            const len = lhs_ty.vectorLen(pool);
            const overflow_bits = try sema.arena.alloc(InternPool.Index, len);
            const wrapped_results = try sema.arena.alloc(InternPool.Index, len);
            for (overflow_bits, wrapped_results, 0..) |*ob, *wr, elem_idx| {
                const lhs_elem = try lhs_val.elemValue(pool, elem_idx);
                const rhs_elem = try rhs_val.elemValue(pool, elem_idx);
                const elem_result = try shlWithOverflowScalar(sema, lhs_elem_ty, lhs_elem, rhs_elem);
                ob.* = elem_result.overflow_bit.index;
                wr.* = elem_result.wrapped_result.index;
            }
            return .{
                .overflow_bit = try sema.aggregateValue(try sema.vectorType(.{
                    .len = @intCast(overflow_bits.len),
                    .child = .u1_type,
                }), overflow_bits),
                .wrapped_result = try sema.aggregateValue(lhs_ty, wrapped_results),
            };
        },
        else => unreachable,
    }
}
fn shlScalar(sema: *Sema, lhs_ty: Type, lhs_val: Value, rhs_val: Value, op: ShlOp) !Value {
    const pool = sema.intern_pool;
    switch (op) {
        .shl, .shl_exact => {
            if (lhs_val.isUndef(pool)) return sema.failWithUseOfUndef();
            if (rhs_val.isUndef(pool)) return sema.failWithUseOfUndef();
        },
        .shl_sat => {
            if (lhs_val.isUndef(pool)) return lhs_val;
            if (rhs_val.isUndef(pool)) return rhs_val;
        },
    }
    switch (Value.order(rhs_val, .zero_comptime_int, pool)) {
        .gt => {},
        .eq => return lhs_val,
        .lt => return sema.failWithNegativeShiftAmount(rhs_val),
    }
    switch (lhs_ty.zigTypeTag(pool)) {
        .int => switch (op) {
            .shl => return intShl(sema, lhs_ty, lhs_val, rhs_val),
            .shl_sat => return intShlSat(sema, lhs_ty, lhs_val, rhs_val),
            .shl_exact => {
                const shifted = try intShlWithOverflow(sema, lhs_ty, lhs_val, rhs_val, false);
                if (shifted.overflow) {
                    return sema.failWithIntegerOverflow(lhs_ty, shifted.val);
                }
                return shifted.val;
            },
        },
        .comptime_int => return comptimeIntShl(sema, lhs_val, rhs_val),
        else => unreachable,
    }
}
fn shlWithOverflowScalar(sema: *Sema, lhs_ty: Type, lhs_val: Value, rhs_val: Value) !Value.OverflowArithmeticResult {
    const pool = sema.intern_pool;
    if (lhs_val.isUndef(pool)) return sema.failWithUseOfUndef();
    if (rhs_val.isUndef(pool)) return sema.failWithUseOfUndef();

    switch (Value.order(rhs_val, .zero_comptime_int, pool)) {
        .gt => {},
        .eq => return .{ .overflow_bit = .zero_u1, .wrapped_result = lhs_val },
        .lt => return sema.failWithNegativeShiftAmount(rhs_val),
    }
    switch (lhs_ty.zigTypeTag(pool)) {
        .int => {
            const result = try intShlWithOverflow(sema, lhs_ty, lhs_val, rhs_val, true);
            return .{
                .overflow_bit = try sema.intValue_u64(u1_ty, @intFromBool(result.overflow)),
                .wrapped_result = result.val,
            };
        },
        .comptime_int => return .{
            .overflow_bit = .zero_u1,
            .wrapped_result = try comptimeIntShl(sema, lhs_val, rhs_val),
        },
        else => unreachable,
    }
}

pub fn shr(sema: *Sema, lhs_ty: Type, rhs_ty: Type, lhs_val: Value, rhs_val: Value, op: ShrOp) !Value {
    const pool = sema.intern_pool;
    switch (lhs_ty.zigTypeTag(pool)) {
        .int, .comptime_int => return shrScalar(sema, lhs_ty, rhs_ty, lhs_val, rhs_val, op),
        .vector => {
            const lhs_elem_ty = lhs_ty.childType(pool);
            const rhs_elem_ty = rhs_ty.childType(pool);
            const len = lhs_ty.vectorLen(pool);
            const elem_vals = try sema.arena.alloc(InternPool.Index, len);
            for (elem_vals, 0..) |*result_elem, elem_idx| {
                const lhs_elem = try lhs_val.elemValue(pool, elem_idx);
                const rhs_elem = try rhs_val.elemValue(pool, elem_idx);
                result_elem.* = (try shrScalar(sema, lhs_elem_ty, rhs_elem_ty, lhs_elem, rhs_elem, op)).index;
            }
            return sema.aggregateValue(lhs_ty, elem_vals);
        },
        else => unreachable,
    }
}
fn shrScalar(sema: *Sema, lhs_ty: Type, rhs_ty: Type, lhs_val: Value, rhs_val: Value, op: ShrOp) !Value {
    const pool = sema.intern_pool;
    if (lhs_val.isUndef(pool)) return sema.failWithUseOfUndef();
    if (rhs_val.isUndef(pool)) return sema.failWithUseOfUndef();

    switch (Value.order(rhs_val, .zero_comptime_int, pool)) {
        .gt => {},
        .eq => return lhs_val,
        .lt => return sema.failWithNegativeShiftAmount(rhs_val),
    }
    return intShr(sema, lhs_ty, rhs_ty, lhs_val, rhs_val, op);
}

pub fn truncate(sema: *Sema, val: Value, ty: Type, dest_ty: Type, dest_signedness: std.lang.Signedness, dest_bits: u16) !Value {
    const pool = sema.intern_pool;
    if (val.isUndef(pool)) return sema.undefValue(dest_ty);
    switch (ty.zigTypeTag(pool)) {
        .int, .comptime_int => return intTruncate(sema, val, dest_ty, dest_signedness, dest_bits),
        .vector => {
            const dest_elem_ty = dest_ty.childType(pool);
            const len = ty.vectorLen(pool);
            const elem_vals = try sema.arena.alloc(InternPool.Index, len);
            for (elem_vals, 0..) |*result_elem, elem_idx| {
                const elem_val = try val.elemValue(pool, elem_idx);
                result_elem.* = if (elem_val.isUndef(pool))
                    (try sema.undefValue(dest_elem_ty)).index
                else
                    (try intTruncate(
                        sema,
                        elem_val,
                        dest_elem_ty,
                        dest_signedness,
                        dest_bits,
                    )).index;
            }
            return sema.aggregateValue(dest_ty, elem_vals);
        },
        else => unreachable,
    }
}

pub fn bitwiseNot(sema: *Sema, ty: Type, val: Value) !Value {
    const pool = sema.intern_pool;
    if (val.isUndef(pool)) return val;
    switch (ty.zigTypeTag(pool)) {
        .bool, .int, .comptime_int => return intBitwiseNot(sema, val, ty),
        .vector => {
            const elem_ty = ty.childType(pool);
            switch (elem_ty.zigTypeTag(pool)) {
                .bool, .int, .comptime_int => {},
                else => unreachable,
            }
            const len = ty.vectorLen(pool);
            const elem_vals = try sema.arena.alloc(InternPool.Index, len);
            for (elem_vals, 0..) |*result_elem, elem_idx| {
                const elem_val = try val.elemValue(pool, elem_idx);
                result_elem.* = if (elem_val.isUndef(pool))
                    elem_val.index
                else
                    (try intBitwiseNot(sema, elem_val, elem_ty)).index;
            }
            return sema.aggregateValue(ty, elem_vals);
        },
        else => unreachable,
    }
}

pub fn bitwiseBin(sema: *Sema, ty: Type, lhs_val: Value, rhs_val: Value, op: BitwiseBinOp) !Value {
    const pool = sema.intern_pool;
    switch (ty.zigTypeTag(pool)) {
        .vector => {
            const elem_ty = ty.childType(pool);
            switch (elem_ty.zigTypeTag(pool)) {
                .bool, .int, .comptime_int => {},
                else => unreachable,
            }
            const len = ty.vectorLen(pool);
            const elem_vals = try sema.arena.alloc(InternPool.Index, len);
            for (elem_vals, 0..) |*result_elem, elem_idx| {
                const lhs_elem = try lhs_val.elemValue(pool, elem_idx);
                const rhs_elem = try rhs_val.elemValue(pool, elem_idx);
                result_elem.* = (try bitwiseBinScalar(sema, elem_ty, lhs_elem, rhs_elem, op)).index;
            }
            return sema.aggregateValue(ty, elem_vals);
        },
        .bool, .int, .comptime_int => return bitwiseBinScalar(sema, ty, lhs_val, rhs_val, op),
        else => unreachable,
    }
}
fn bitwiseBinScalar(sema: *Sema, ty: Type, lhs_val: Value, rhs_val: Value, op: BitwiseBinOp) !Value {
    const pool = sema.intern_pool;
    if (op == .xor and (lhs_val.isUndef(pool) or rhs_val.isUndef(pool))) return sema.undefValue(ty);
    const def_lhs: Value, const def_rhs: Value = make_defined: {
        const lhs_undef = lhs_val.isUndef(pool);
        const rhs_undef = rhs_val.isUndef(pool);
        break :make_defined switch ((@as(u2, @intFromBool(lhs_undef)) << 1) | @intFromBool(rhs_undef)) {
            0b00 => .{ lhs_val, rhs_val },
            0b01 => .{ lhs_val, try intValueAa(sema, ty) },
            0b10 => .{ try intValueAa(sema, ty), rhs_val },
            0b11 => return sema.undefValue(ty),
        };
    };
    if (ty.index == .u0_type) return sema.intValue_u64(ty, 0);
    switch (op) {
        .@"and" => return intBitwiseAnd(sema, def_lhs, def_rhs, ty),
        .nand => return intBitwiseNand(sema, def_lhs, def_rhs, ty),
        .@"or" => return intBitwiseOr(sema, def_lhs, def_rhs, ty),
        .xor => return intBitwiseXor(sema, def_lhs, def_rhs, ty),
    }
}

pub fn floatAdd(sema: *Sema, lhs: Value, rhs: Value, ty: Type) !Value {
    const pool = sema.intern_pool;
    const storage: InternPool.Key.Float.Storage = switch (ty.floatBits()) {
        16 => .{ .f16 = lhs.toFloat(f16, pool) + rhs.toFloat(f16, pool) },
        32 => .{ .f32 = lhs.toFloat(f32, pool) + rhs.toFloat(f32, pool) },
        64 => .{ .f64 = lhs.toFloat(f64, pool) + rhs.toFloat(f64, pool) },
        80 => .{ .f80 = lhs.toFloat(f80, pool) + rhs.toFloat(f80, pool) },
        128 => .{ .f128 = lhs.toFloat(f128, pool) + rhs.toFloat(f128, pool) },
        else => unreachable,
    };
    return .fromIndex(try pool.internFloat(.{ .ty = ty.index, .storage = storage }));
}

pub fn floatSub(sema: *Sema, lhs: Value, rhs: Value, ty: Type) !Value {
    const pool = sema.intern_pool;
    const storage: InternPool.Key.Float.Storage = switch (ty.floatBits()) {
        16 => .{ .f16 = lhs.toFloat(f16, pool) - rhs.toFloat(f16, pool) },
        32 => .{ .f32 = lhs.toFloat(f32, pool) - rhs.toFloat(f32, pool) },
        64 => .{ .f64 = lhs.toFloat(f64, pool) - rhs.toFloat(f64, pool) },
        80 => .{ .f80 = lhs.toFloat(f80, pool) - rhs.toFloat(f80, pool) },
        128 => .{ .f128 = lhs.toFloat(f128, pool) - rhs.toFloat(f128, pool) },
        else => unreachable,
    };
    return .fromIndex(try pool.internFloat(.{ .ty = ty.index, .storage = storage }));
}

pub fn floatMul(sema: *Sema, lhs: Value, rhs: Value, ty: Type) !Value {
    const pool = sema.intern_pool;
    const storage: InternPool.Key.Float.Storage = switch (ty.floatBits()) {
        16 => .{ .f16 = lhs.toFloat(f16, pool) * rhs.toFloat(f16, pool) },
        32 => .{ .f32 = lhs.toFloat(f32, pool) * rhs.toFloat(f32, pool) },
        64 => .{ .f64 = lhs.toFloat(f64, pool) * rhs.toFloat(f64, pool) },
        80 => .{ .f80 = lhs.toFloat(f80, pool) * rhs.toFloat(f80, pool) },
        128 => .{ .f128 = lhs.toFloat(f128, pool) * rhs.toFloat(f128, pool) },
        else => unreachable,
    };
    return .fromIndex(try pool.internFloat(.{ .ty = ty.index, .storage = storage }));
}

pub fn floatDiv(sema: *Sema, lhs: Value, rhs: Value, ty: Type) !Value {
    const pool = sema.intern_pool;
    const storage: InternPool.Key.Float.Storage = switch (ty.floatBits()) {
        16 => .{ .f16 = lhs.toFloat(f16, pool) / rhs.toFloat(f16, pool) },
        32 => .{ .f32 = lhs.toFloat(f32, pool) / rhs.toFloat(f32, pool) },
        64 => .{ .f64 = lhs.toFloat(f64, pool) / rhs.toFloat(f64, pool) },
        80 => .{ .f80 = lhs.toFloat(f80, pool) / rhs.toFloat(f80, pool) },
        128 => .{ .f128 = lhs.toFloat(f128, pool) / rhs.toFloat(f128, pool) },
        else => unreachable,
    };
    return .fromIndex(try pool.internFloat(.{ .ty = ty.index, .storage = storage }));
}

pub fn floatDivTrunc(sema: *Sema, lhs: Value, rhs: Value, ty: Type) !Value {
    const pool = sema.intern_pool;
    const storage: InternPool.Key.Float.Storage = switch (ty.floatBits()) {
        16 => .{ .f16 = @divTrunc(lhs.toFloat(f16, pool), rhs.toFloat(f16, pool)) },
        32 => .{ .f32 = @divTrunc(lhs.toFloat(f32, pool), rhs.toFloat(f32, pool)) },
        64 => .{ .f64 = @divTrunc(lhs.toFloat(f64, pool), rhs.toFloat(f64, pool)) },
        80 => .{ .f80 = @divTrunc(lhs.toFloat(f80, pool), rhs.toFloat(f80, pool)) },
        128 => .{ .f128 = @divTrunc(lhs.toFloat(f128, pool), rhs.toFloat(f128, pool)) },
        else => unreachable,
    };
    return .fromIndex(try pool.internFloat(.{ .ty = ty.index, .storage = storage }));
}

pub fn floatDivFloor(sema: *Sema, lhs: Value, rhs: Value, ty: Type) !Value {
    const pool = sema.intern_pool;
    const storage: InternPool.Key.Float.Storage = switch (ty.floatBits()) {
        16 => .{ .f16 = @divFloor(lhs.toFloat(f16, pool), rhs.toFloat(f16, pool)) },
        32 => .{ .f32 = @divFloor(lhs.toFloat(f32, pool), rhs.toFloat(f32, pool)) },
        64 => .{ .f64 = @divFloor(lhs.toFloat(f64, pool), rhs.toFloat(f64, pool)) },
        80 => .{ .f80 = @divFloor(lhs.toFloat(f80, pool), rhs.toFloat(f80, pool)) },
        128 => .{ .f128 = @divFloor(lhs.toFloat(f128, pool), rhs.toFloat(f128, pool)) },
        else => unreachable,
    };
    return .fromIndex(try pool.internFloat(.{ .ty = ty.index, .storage = storage }));
}

pub fn floatDivCeil(sema: *Sema, lhs: Value, rhs: Value, ty: Type) !Value {
    const pool = sema.intern_pool;
    const storage: InternPool.Key.Float.Storage = switch (ty.floatBits()) {
        16 => .{ .f16 = @divCeil(lhs.toFloat(f16, pool), rhs.toFloat(f16, pool)) },
        32 => .{ .f32 = @divCeil(lhs.toFloat(f32, pool), rhs.toFloat(f32, pool)) },
        64 => .{ .f64 = @divCeil(lhs.toFloat(f64, pool), rhs.toFloat(f64, pool)) },
        80 => .{ .f80 = @divCeil(lhs.toFloat(f80, pool), rhs.toFloat(f80, pool)) },
        128 => .{ .f128 = @divCeil(lhs.toFloat(f128, pool), rhs.toFloat(f128, pool)) },
        else => unreachable,
    };
    return .fromIndex(try pool.internFloat(.{ .ty = ty.index, .storage = storage }));
}

pub fn floatDivIsExact(sema: *Sema, lhs: Value, rhs: Value, ty: Type) bool {
    const pool = sema.intern_pool;
    return switch (ty.floatBits()) {
        16 => @mod(lhs.toFloat(f16, pool), rhs.toFloat(f16, pool)) == 0,
        32 => @mod(lhs.toFloat(f32, pool), rhs.toFloat(f32, pool)) == 0,
        64 => @mod(lhs.toFloat(f64, pool), rhs.toFloat(f64, pool)) == 0,
        80 => @mod(lhs.toFloat(f80, pool), rhs.toFloat(f80, pool)) == 0,
        128 => @mod(lhs.toFloat(f128, pool), rhs.toFloat(f128, pool)) == 0,
        else => unreachable,
    };
}

pub fn floatNeg(sema: *Sema, val: Value, ty: Type) !Value {
    const pool = sema.intern_pool;
    const storage: InternPool.Key.Float.Storage = switch (ty.floatBits()) {
        16 => .{ .f16 = -val.toFloat(f16, pool) },
        32 => .{ .f32 = -val.toFloat(f32, pool) },
        64 => .{ .f64 = -val.toFloat(f64, pool) },
        80 => .{ .f80 = -val.toFloat(f80, pool) },
        128 => .{ .f128 = -val.toFloat(f128, pool) },
        else => unreachable,
    };
    return .fromIndex(try pool.internFloat(.{ .ty = ty.index, .storage = storage }));
}

pub fn floatMod(sema: *Sema, lhs: Value, rhs: Value, ty: Type) !Value {
    const pool = sema.intern_pool;
    const storage: InternPool.Key.Float.Storage = switch (ty.floatBits()) {
        16 => .{ .f16 = @mod(lhs.toFloat(f16, pool), rhs.toFloat(f16, pool)) },
        32 => .{ .f32 = @mod(lhs.toFloat(f32, pool), rhs.toFloat(f32, pool)) },
        64 => .{ .f64 = @mod(lhs.toFloat(f64, pool), rhs.toFloat(f64, pool)) },
        80 => .{ .f80 = @mod(lhs.toFloat(f80, pool), rhs.toFloat(f80, pool)) },
        128 => .{ .f128 = @mod(lhs.toFloat(f128, pool), rhs.toFloat(f128, pool)) },
        else => unreachable,
    };
    return .fromIndex(try pool.internFloat(.{ .ty = ty.index, .storage = storage }));
}

pub fn floatRem(sema: *Sema, lhs: Value, rhs: Value, ty: Type) !Value {
    const pool = sema.intern_pool;
    const storage: InternPool.Key.Float.Storage = switch (ty.floatBits()) {
        16 => .{ .f16 = @rem(lhs.toFloat(f16, pool), rhs.toFloat(f16, pool)) },
        32 => .{ .f32 = @rem(lhs.toFloat(f32, pool), rhs.toFloat(f32, pool)) },
        64 => .{ .f64 = @rem(lhs.toFloat(f64, pool), rhs.toFloat(f64, pool)) },
        80 => .{ .f80 = @rem(lhs.toFloat(f80, pool), rhs.toFloat(f80, pool)) },
        128 => .{ .f128 = @rem(lhs.toFloat(f128, pool), rhs.toFloat(f128, pool)) },
        else => unreachable,
    };
    return .fromIndex(try pool.internFloat(.{ .ty = ty.index, .storage = storage }));
}

fn intAdd(sema: *Sema, lhs: Value, rhs: Value, ty: Type) !struct { overflow: bool, val: Value } {
    const pool = sema.intern_pool;
    switch (ty.index) {
        .comptime_int_type => return .{ .overflow = false, .val = try comptimeIntAdd(sema, lhs, rhs) },
        else => {
            const res = try intAddWithOverflowInner(sema, lhs, rhs, ty);
            return switch (res.overflow_bit.toUnsignedInt(pool)) {
                0 => .{ .overflow = false, .val = res.wrapped_result },
                1 => .{ .overflow = true, .val = try comptimeIntAdd(sema, lhs, rhs) },
                else => unreachable,
            };
        },
    }
}
fn comptimeIntAdd(sema: *Sema, lhs: Value, rhs: Value) !Value {
    const pool = sema.intern_pool;
    var lhs_space: BigIntSpace = undefined;
    var rhs_space: BigIntSpace = undefined;
    const lhs_bigint = lhs.toBigInt(&lhs_space, pool);
    const rhs_bigint = rhs.toBigInt(&rhs_space, pool);
    const limbs = try sema.arena.alloc(Limb, @max(lhs_bigint.limbs.len, rhs_bigint.limbs.len) + 1);
    var result_bigint: BigIntMutable = .{ .limbs = limbs, .positive = undefined, .len = undefined };
    result_bigint.add(lhs_bigint, rhs_bigint);
    return sema.intValue_big(comptime_int_ty, result_bigint.toConst());
}
fn intAddWithOverflow(sema: *Sema, lhs: Value, rhs: Value, ty: Type) !Value.OverflowArithmeticResult {
    switch (ty.index) {
        .comptime_int_type => return .{ .overflow_bit = Value.zero_u1, .wrapped_result = try comptimeIntAdd(sema, lhs, rhs) },
        else => return intAddWithOverflowInner(sema, lhs, rhs, ty),
    }
}
fn intAddWithOverflowInner(sema: *Sema, lhs: Value, rhs: Value, ty: Type) !Value.OverflowArithmeticResult {
    assert(ty.index != .comptime_int_type);
    const pool = sema.intern_pool;
    const info = ty.intInfo(pool);
    var lhs_space: BigIntSpace = undefined;
    var rhs_space: BigIntSpace = undefined;
    const lhs_bigint = lhs.toBigInt(&lhs_space, pool);
    const rhs_bigint = rhs.toBigInt(&rhs_space, pool);
    const limbs = try sema.arena.alloc(Limb, std.math.big.int.calcTwosCompLimbCount(info.bits));
    var result_bigint: BigIntMutable = .{ .limbs = limbs, .positive = undefined, .len = undefined };
    const overflowed = result_bigint.addWrap(lhs_bigint, rhs_bigint, info.signedness, info.bits);
    return .{
        .overflow_bit = try sema.intValue_u64(u1_ty, @intFromBool(overflowed)),
        .wrapped_result = try sema.intValue_big(ty, result_bigint.toConst()),
    };
}
fn intAddSat(sema: *Sema, lhs: Value, rhs: Value, ty: Type) !Value {
    const pool = sema.intern_pool;
    const info = ty.intInfo(pool);
    var lhs_space: BigIntSpace = undefined;
    var rhs_space: BigIntSpace = undefined;
    const lhs_bigint = lhs.toBigInt(&lhs_space, pool);
    const rhs_bigint = rhs.toBigInt(&rhs_space, pool);
    const limbs = try sema.arena.alloc(Limb, std.math.big.int.calcTwosCompLimbCount(info.bits));
    var result_bigint: BigIntMutable = .{ .limbs = limbs, .positive = undefined, .len = undefined };
    result_bigint.addSat(lhs_bigint, rhs_bigint, info.signedness, info.bits);
    return sema.intValue_big(ty, result_bigint.toConst());
}
fn intSub(sema: *Sema, lhs: Value, rhs: Value, ty: Type) !struct { overflow: bool, val: Value } {
    const pool = sema.intern_pool;
    switch (ty.index) {
        .comptime_int_type => return .{ .overflow = false, .val = try comptimeIntSub(sema, lhs, rhs) },
        else => {
            const res = try intSubWithOverflowInner(sema, lhs, rhs, ty);
            return switch (res.overflow_bit.toUnsignedInt(pool)) {
                0 => .{ .overflow = false, .val = res.wrapped_result },
                1 => .{ .overflow = true, .val = try comptimeIntSub(sema, lhs, rhs) },
                else => unreachable,
            };
        },
    }
}
fn comptimeIntSub(sema: *Sema, lhs: Value, rhs: Value) !Value {
    const pool = sema.intern_pool;
    var lhs_space: BigIntSpace = undefined;
    var rhs_space: BigIntSpace = undefined;
    const lhs_bigint = lhs.toBigInt(&lhs_space, pool);
    const rhs_bigint = rhs.toBigInt(&rhs_space, pool);
    const limbs = try sema.arena.alloc(Limb, @max(lhs_bigint.limbs.len, rhs_bigint.limbs.len) + 1);
    var result_bigint: BigIntMutable = .{ .limbs = limbs, .positive = undefined, .len = undefined };
    result_bigint.sub(lhs_bigint, rhs_bigint);
    return sema.intValue_big(comptime_int_ty, result_bigint.toConst());
}
fn intSubWithOverflow(sema: *Sema, lhs: Value, rhs: Value, ty: Type) !Value.OverflowArithmeticResult {
    switch (ty.index) {
        .comptime_int_type => return .{ .overflow_bit = Value.zero_u1, .wrapped_result = try comptimeIntSub(sema, lhs, rhs) },
        else => return intSubWithOverflowInner(sema, lhs, rhs, ty),
    }
}
fn intSubWithOverflowInner(sema: *Sema, lhs: Value, rhs: Value, ty: Type) !Value.OverflowArithmeticResult {
    assert(ty.index != .comptime_int_type);
    const pool = sema.intern_pool;
    const info = ty.intInfo(pool);
    var lhs_space: BigIntSpace = undefined;
    var rhs_space: BigIntSpace = undefined;
    const lhs_bigint = lhs.toBigInt(&lhs_space, pool);
    const rhs_bigint = rhs.toBigInt(&rhs_space, pool);
    const limbs = try sema.arena.alloc(Limb, std.math.big.int.calcTwosCompLimbCount(info.bits));
    var result_bigint: BigIntMutable = .{ .limbs = limbs, .positive = undefined, .len = undefined };
    const overflowed = result_bigint.subWrap(lhs_bigint, rhs_bigint, info.signedness, info.bits);
    return .{
        .overflow_bit = try sema.intValue_u64(u1_ty, @intFromBool(overflowed)),
        .wrapped_result = try sema.intValue_big(ty, result_bigint.toConst()),
    };
}
fn intSubSat(sema: *Sema, lhs: Value, rhs: Value, ty: Type) !Value {
    const pool = sema.intern_pool;
    const info = ty.intInfo(pool);
    var lhs_space: BigIntSpace = undefined;
    var rhs_space: BigIntSpace = undefined;
    const lhs_bigint = lhs.toBigInt(&lhs_space, pool);
    const rhs_bigint = rhs.toBigInt(&rhs_space, pool);
    const limbs = try sema.arena.alloc(Limb, std.math.big.int.calcTwosCompLimbCount(info.bits));
    var result_bigint: BigIntMutable = .{ .limbs = limbs, .positive = undefined, .len = undefined };
    result_bigint.subSat(lhs_bigint, rhs_bigint, info.signedness, info.bits);
    return sema.intValue_big(ty, result_bigint.toConst());
}
fn intMul(sema: *Sema, lhs: Value, rhs: Value, ty: Type) !struct { overflow: bool, val: Value } {
    const pool = sema.intern_pool;
    switch (ty.index) {
        .comptime_int_type => return .{ .overflow = false, .val = try comptimeIntMul(sema, lhs, rhs) },
        else => {
            const res = try intMulWithOverflowInner(sema, lhs, rhs, ty);
            return switch (res.overflow_bit.toUnsignedInt(pool)) {
                0 => .{ .overflow = false, .val = res.wrapped_result },
                1 => .{ .overflow = true, .val = try comptimeIntMul(sema, lhs, rhs) },
                else => unreachable,
            };
        },
    }
}
fn comptimeIntMul(sema: *Sema, lhs: Value, rhs: Value) !Value {
    const pool = sema.intern_pool;
    var lhs_space: BigIntSpace = undefined;
    var rhs_space: BigIntSpace = undefined;
    const lhs_bigint = lhs.toBigInt(&lhs_space, pool);
    const rhs_bigint = rhs.toBigInt(&rhs_space, pool);
    const limbs = try sema.arena.alloc(Limb, lhs_bigint.limbs.len + rhs_bigint.limbs.len);
    var result_bigint: BigIntMutable = .{ .limbs = limbs, .positive = undefined, .len = undefined };
    const limbs_buffer = try sema.arena.alloc(Limb, std.math.big.int.calcMulLimbsBufferLen(lhs_bigint.limbs.len, rhs_bigint.limbs.len, 1));
    result_bigint.mul(lhs_bigint, rhs_bigint, limbs_buffer, sema.arena);
    return sema.intValue_big(comptime_int_ty, result_bigint.toConst());
}
fn intMulWithOverflow(sema: *Sema, lhs: Value, rhs: Value, ty: Type) !Value.OverflowArithmeticResult {
    switch (ty.index) {
        .comptime_int_type => return .{ .overflow_bit = Value.zero_u1, .wrapped_result = try comptimeIntMul(sema, lhs, rhs) },
        else => return intMulWithOverflowInner(sema, lhs, rhs, ty),
    }
}
fn intMulWithOverflowInner(sema: *Sema, lhs: Value, rhs: Value, ty: Type) !Value.OverflowArithmeticResult {
    const pool = sema.intern_pool;
    const info = ty.intInfo(pool);
    var lhs_space: BigIntSpace = undefined;
    var rhs_space: BigIntSpace = undefined;
    const lhs_bigint = lhs.toBigInt(&lhs_space, pool);
    const rhs_bigint = rhs.toBigInt(&rhs_space, pool);
    const limbs = try sema.arena.alloc(Limb, lhs_bigint.limbs.len + rhs_bigint.limbs.len);
    var result_bigint: BigIntMutable = .{ .limbs = limbs, .positive = undefined, .len = undefined };
    result_bigint.mulNoAlias(lhs_bigint, rhs_bigint, sema.arena);
    const overflowed = !result_bigint.toConst().fitsInTwosComp(info.signedness, info.bits);
    if (overflowed) result_bigint.truncate(result_bigint.toConst(), info.signedness, info.bits);
    return .{
        .overflow_bit = try sema.intValue_u64(u1_ty, @intFromBool(overflowed)),
        .wrapped_result = try sema.intValue_big(ty, result_bigint.toConst()),
    };
}
fn intMulSat(sema: *Sema, lhs: Value, rhs: Value, ty: Type) !Value {
    const pool = sema.intern_pool;
    const info = ty.intInfo(pool);
    var lhs_space: BigIntSpace = undefined;
    var rhs_space: BigIntSpace = undefined;
    const lhs_bigint = lhs.toBigInt(&lhs_space, pool);
    const rhs_bigint = rhs.toBigInt(&rhs_space, pool);
    const limbs = try sema.arena.alloc(Limb, lhs_bigint.limbs.len + rhs_bigint.limbs.len);
    var result_bigint: BigIntMutable = .{ .limbs = limbs, .positive = undefined, .len = undefined };
    result_bigint.mulNoAlias(lhs_bigint, rhs_bigint, sema.arena);
    result_bigint.saturate(result_bigint.toConst(), info.signedness, info.bits);
    return sema.intValue_big(ty, result_bigint.toConst());
}
fn intDivTrunc(sema: *Sema, lhs: Value, rhs: Value, ty: Type) !struct { overflow: bool, val: Value } {
    const result = intDivTruncInner(sema, lhs, rhs, ty) catch |err| switch (err) {
        error.Overflow => {
            const result = intDivTruncInner(sema, lhs, rhs, comptime_int_ty) catch |err1| switch (err1) {
                error.Overflow => unreachable,
                else => |e| return e,
            };
            return .{ .overflow = true, .val = result };
        },
        else => |e| return e,
    };
    return .{ .overflow = false, .val = result };
}
fn intDivTruncInner(sema: *Sema, lhs: Value, rhs: Value, ty: Type) !Value {
    const pool = sema.intern_pool;
    var lhs_space: BigIntSpace = undefined;
    var rhs_space: BigIntSpace = undefined;
    const lhs_bigint = lhs.toBigInt(&lhs_space, pool);
    const rhs_bigint = rhs.toBigInt(&rhs_space, pool);
    const limbs_q = try sema.arena.alloc(Limb, lhs_bigint.limbs.len);
    const limbs_r = try sema.arena.alloc(Limb, rhs_bigint.limbs.len);
    const limbs_buf = try sema.arena.alloc(Limb, std.math.big.int.calcDivLimbsBufferLen(lhs_bigint.limbs.len, rhs_bigint.limbs.len));
    var result_q: BigIntMutable = .{ .limbs = limbs_q, .positive = undefined, .len = undefined };
    var result_r: BigIntMutable = .{ .limbs = limbs_r, .positive = undefined, .len = undefined };
    result_q.divTrunc(&result_r, lhs_bigint, rhs_bigint, limbs_buf);
    if (ty.index != .comptime_int_type) {
        const info = ty.intInfo(pool);
        if (!result_q.toConst().fitsInTwosComp(info.signedness, info.bits)) return error.Overflow;
    }
    return sema.intValue_big(ty, result_q.toConst());
}
fn intDivExact(sema: *Sema, lhs: Value, rhs: Value, ty: Type) !union(enum) { remainder, overflow: Value, success: Value } {
    const pool = sema.intern_pool;
    var lhs_space: BigIntSpace = undefined;
    var rhs_space: BigIntSpace = undefined;
    const lhs_bigint = lhs.toBigInt(&lhs_space, pool);
    const rhs_bigint = rhs.toBigInt(&rhs_space, pool);
    const limbs_q = try sema.arena.alloc(Limb, lhs_bigint.limbs.len);
    const limbs_r = try sema.arena.alloc(Limb, rhs_bigint.limbs.len);
    const limbs_buf = try sema.arena.alloc(Limb, std.math.big.int.calcDivLimbsBufferLen(lhs_bigint.limbs.len, rhs_bigint.limbs.len));
    var result_q: BigIntMutable = .{ .limbs = limbs_q, .positive = undefined, .len = undefined };
    var result_r: BigIntMutable = .{ .limbs = limbs_r, .positive = undefined, .len = undefined };
    result_q.divTrunc(&result_r, lhs_bigint, rhs_bigint, limbs_buf);
    if (!result_r.toConst().eqlZero()) return .remainder;
    if (ty.index != .comptime_int_type) {
        const info = ty.intInfo(pool);
        if (!result_q.toConst().fitsInTwosComp(info.signedness, info.bits)) return .{ .overflow = try sema.intValue_big(comptime_int_ty, result_q.toConst()) };
    }
    return .{ .success = try sema.intValue_big(ty, result_q.toConst()) };
}
fn intDivFloor(sema: *Sema, lhs: Value, rhs: Value, ty: Type) !struct { overflow: bool, val: Value } {
    const result = intDivFloorInner(sema, lhs, rhs, ty) catch |err| switch (err) {
        error.Overflow => {
            const result = intDivFloorInner(sema, lhs, rhs, comptime_int_ty) catch |err1| switch (err1) {
                error.Overflow => unreachable,
                else => |e| return e,
            };
            return .{ .overflow = true, .val = result };
        },
        else => |e| return e,
    };
    return .{ .overflow = false, .val = result };
}
fn intDivFloorInner(sema: *Sema, lhs: Value, rhs: Value, ty: Type) !Value {
    const pool = sema.intern_pool;
    var lhs_space: BigIntSpace = undefined;
    var rhs_space: BigIntSpace = undefined;
    const lhs_bigint = lhs.toBigInt(&lhs_space, pool);
    const rhs_bigint = rhs.toBigInt(&rhs_space, pool);
    const limbs_q = try sema.arena.alloc(Limb, lhs_bigint.limbs.len);
    const limbs_r = try sema.arena.alloc(Limb, rhs_bigint.limbs.len);
    const limbs_buf = try sema.arena.alloc(Limb, std.math.big.int.calcDivLimbsBufferLen(lhs_bigint.limbs.len, rhs_bigint.limbs.len));
    var result_q: BigIntMutable = .{ .limbs = limbs_q, .positive = undefined, .len = undefined };
    var result_r: BigIntMutable = .{ .limbs = limbs_r, .positive = undefined, .len = undefined };
    result_q.divFloor(&result_r, lhs_bigint, rhs_bigint, limbs_buf);
    if (ty.index != .comptime_int_type) {
        const info = ty.intInfo(pool);
        if (!result_q.toConst().fitsInTwosComp(info.signedness, info.bits)) return error.Overflow;
    }
    return sema.intValue_big(ty, result_q.toConst());
}
fn intDivCeil(sema: *Sema, lhs: Value, rhs: Value, ty: Type) !struct { overflow: bool, val: Value } {
    const result = intDivCeilInner(sema, lhs, rhs, ty) catch |err| switch (err) {
        error.Overflow => {
            const result = intDivCeilInner(sema, lhs, rhs, comptime_int_ty) catch |err1| switch (err1) {
                error.Overflow => unreachable,
                else => |e| return e,
            };
            return .{ .overflow = true, .val = result };
        },
        else => |e| return e,
    };
    return .{ .overflow = false, .val = result };
}
fn intDivCeilInner(sema: *Sema, lhs: Value, rhs: Value, ty: Type) !Value {
    const pool = sema.intern_pool;
    var lhs_space: BigIntSpace = undefined;
    var rhs_space: BigIntSpace = undefined;
    const lhs_bigint = lhs.toBigInt(&lhs_space, pool);
    const rhs_bigint = rhs.toBigInt(&rhs_space, pool);
    const limbs_q = try sema.arena.alloc(Limb, lhs_bigint.limbs.len);
    const limbs_r = try sema.arena.alloc(Limb, rhs_bigint.limbs.len);
    const limbs_buf = try sema.arena.alloc(Limb, std.math.big.int.calcDivLimbsBufferLen(lhs_bigint.limbs.len, rhs_bigint.limbs.len));
    var result_q: BigIntMutable = .{ .limbs = limbs_q, .positive = undefined, .len = undefined };
    var result_r: BigIntMutable = .{ .limbs = limbs_r, .positive = undefined, .len = undefined };
    result_q.divCeil(&result_r, lhs_bigint, rhs_bigint, limbs_buf);
    if (ty.index != .comptime_int_type) {
        const info = ty.intInfo(pool);
        if (!result_q.toConst().fitsInTwosComp(info.signedness, info.bits)) return error.Overflow;
    }
    return sema.intValue_big(ty, result_q.toConst());
}
fn intMod(sema: *Sema, lhs: Value, rhs: Value, ty: Type) !Value {
    const pool = sema.intern_pool;
    var lhs_space: BigIntSpace = undefined;
    var rhs_space: BigIntSpace = undefined;
    const lhs_bigint = lhs.toBigInt(&lhs_space, pool);
    const rhs_bigint = rhs.toBigInt(&rhs_space, pool);
    const limbs_q = try sema.arena.alloc(Limb, lhs_bigint.limbs.len);
    const limbs_r = try sema.arena.alloc(Limb, rhs_bigint.limbs.len);
    const limbs_buf = try sema.arena.alloc(Limb, std.math.big.int.calcDivLimbsBufferLen(lhs_bigint.limbs.len, rhs_bigint.limbs.len));
    var result_q: BigIntMutable = .{ .limbs = limbs_q, .positive = undefined, .len = undefined };
    var result_r: BigIntMutable = .{ .limbs = limbs_r, .positive = undefined, .len = undefined };
    result_q.divFloor(&result_r, lhs_bigint, rhs_bigint, limbs_buf);
    return sema.intValue_big(ty, result_r.toConst());
}
fn intRem(sema: *Sema, lhs: Value, rhs: Value, ty: Type) !Value {
    const pool = sema.intern_pool;
    var lhs_space: BigIntSpace = undefined;
    var rhs_space: BigIntSpace = undefined;
    const lhs_bigint = lhs.toBigInt(&lhs_space, pool);
    const rhs_bigint = rhs.toBigInt(&rhs_space, pool);
    const limbs_q = try sema.arena.alloc(Limb, lhs_bigint.limbs.len);
    const limbs_r = try sema.arena.alloc(Limb, rhs_bigint.limbs.len);
    const limbs_buf = try sema.arena.alloc(Limb, std.math.big.int.calcDivLimbsBufferLen(lhs_bigint.limbs.len, rhs_bigint.limbs.len));
    var result_q: BigIntMutable = .{ .limbs = limbs_q, .positive = undefined, .len = undefined };
    var result_r: BigIntMutable = .{ .limbs = limbs_r, .positive = undefined, .len = undefined };
    result_q.divTrunc(&result_r, lhs_bigint, rhs_bigint, limbs_buf);
    return sema.intValue_big(ty, result_r.toConst());
}
fn intTruncate(sema: *Sema, val: Value, dest_ty: Type, dest_signedness: std.lang.Signedness, dest_bits: u16) !Value {
    const pool = sema.intern_pool;
    var val_space: BigIntSpace = undefined;
    const val_bigint = val.toBigInt(&val_space, pool);
    const limbs = try sema.arena.alloc(Limb, std.math.big.int.calcTwosCompLimbCount(dest_bits));
    var result_bigint: BigIntMutable = .{ .limbs = limbs, .positive = undefined, .len = undefined };
    result_bigint.truncate(val_bigint, dest_signedness, dest_bits);
    return sema.intValue_big(dest_ty, result_bigint.toConst());
}
fn intBitwiseNot(sema: *Sema, val: Value, ty: Type) !Value {
    const pool = sema.intern_pool;
    if (val.isUndef(pool)) return .fromIndex(try pool.get(.{ .undef = ty.index }));
    switch (ty.index) {
        .bool_type => return Value.makeBool(!val.toBool()),
        .u0_type => return val,
        else => {},
    }
    const info = ty.intInfo(pool);
    var val_space: BigIntSpace = undefined;
    const val_bigint = val.toBigInt(&val_space, pool);
    const limbs = try sema.arena.alloc(Limb, std.math.big.int.calcTwosCompLimbCount(info.bits));
    var result_bigint: BigIntMutable = .{ .limbs = limbs, .positive = undefined, .len = undefined };
    result_bigint.bitNotWrap(val_bigint, info.signedness, info.bits);
    return sema.intValue_big(ty, result_bigint.toConst());
}

pub fn byteSwap(sema: *Sema, val: Value, ty: Type) !Value {
    const pool = sema.intern_pool;
    if (pool.indexToKey(val.index) == .undef) return val;
    switch (ty.zigTypeTag(pool)) {
        .int => return intByteSwap(sema, val, ty),
        .vector => {
            const elem_ty = ty.childType(pool);
            const len = ty.vectorLen(pool);
            const elem_vals = try sema.arena.alloc(InternPool.Index, len);
            for (elem_vals, 0..) |*result_elem, elem_idx| {
                const elem_val = try val.elemValue(pool, elem_idx);
                result_elem.* = if (pool.indexToKey(elem_val.index) == .undef)
                    elem_val.index
                else
                    (try intByteSwap(sema, elem_val, elem_ty)).index;
            }
            return .{ .index = try pool.internAggregate(.{ .ty = ty.index, .storage = .{ .elems = elem_vals } }) };
        },
        else => unreachable,
    }
}

pub fn bitReverse(sema: *Sema, val: Value, ty: Type) !Value {
    const pool = sema.intern_pool;
    if (pool.indexToKey(val.index) == .undef) return val;
    switch (ty.zigTypeTag(pool)) {
        .int => return intBitReverse(sema, val, ty),
        .vector => {
            const elem_ty = ty.childType(pool);
            const len = ty.vectorLen(pool);
            const elem_vals = try sema.arena.alloc(InternPool.Index, len);
            for (elem_vals, 0..) |*result_elem, elem_idx| {
                const elem_val = try val.elemValue(pool, elem_idx);
                result_elem.* = if (pool.indexToKey(elem_val.index) == .undef)
                    elem_val.index
                else
                    (try intBitReverse(sema, elem_val, elem_ty)).index;
            }
            return .{ .index = try pool.internAggregate(.{ .ty = ty.index, .storage = .{ .elems = elem_vals } }) };
        },
        else => unreachable,
    }
}

fn intByteSwap(sema: *Sema, val: Value, ty: Type) !Value {
    const pool = sema.intern_pool;
    const info = ty.intInfo(pool);
    var val_space: BigIntSpace = undefined;
    const val_bigint = val.toBigInt(&val_space, pool);
    const limbs = try sema.arena.alloc(Limb, std.math.big.int.calcTwosCompLimbCount(info.bits));
    var result_bigint: BigIntMutable = .{ .limbs = limbs, .positive = undefined, .len = undefined };
    result_bigint.byteSwap(val_bigint, info.signedness, @divExact(info.bits, 8));
    return .{ .index = try pool.internIntValue(ty.index, result_bigint.toConst()) };
}

fn intBitReverse(sema: *Sema, val: Value, ty: Type) !Value {
    const pool = sema.intern_pool;
    const info = ty.intInfo(pool);
    var val_space: BigIntSpace = undefined;
    const val_bigint = val.toBigInt(&val_space, pool);
    const limbs = try sema.arena.alloc(Limb, std.math.big.int.calcTwosCompLimbCount(info.bits));
    var result_bigint: BigIntMutable = .{ .limbs = limbs, .positive = undefined, .len = undefined };
    result_bigint.bitReverse(val_bigint, info.signedness, info.bits);
    return .{ .index = try pool.internIntValue(ty.index, result_bigint.toConst()) };
}

fn intValueAa(sema: *Sema, ty: Type) !Value {
    const pool = sema.intern_pool;
    if (ty.index == .bool_type) return Value.bool_true;
    if (ty.index == .u0_type) return sema.intValue_u64(ty, 0);
    const info = ty.intInfo(pool);
    const buf = try sema.arena.alloc(u8, (info.bits + 7) / 8);
    @memset(buf, 0xAA);
    const limbs = try sema.arena.alloc(Limb, std.math.big.int.calcTwosCompLimbCount(info.bits));
    var result_bigint: BigIntMutable = .{ .limbs = limbs, .positive = undefined, .len = undefined };
    result_bigint.readTwosComplement(buf, info.bits, builtin.target.cpu.arch.endian(), info.signedness);
    return sema.intValue_big(ty, result_bigint.toConst());
}
fn intBitwiseAnd(sema: *Sema, lhs: Value, rhs: Value, ty: Type) !Value {
    const pool = sema.intern_pool;
    if (ty.index == .bool_type) return Value.makeBool(lhs.toBool() and rhs.toBool());
    var lhs_space: BigIntSpace = undefined;
    var rhs_space: BigIntSpace = undefined;
    const lhs_bigint = lhs.toBigInt(&lhs_space, pool);
    const rhs_bigint = rhs.toBigInt(&rhs_space, pool);
    const limbs = try sema.arena.alloc(Limb, @max(lhs_bigint.limbs.len, rhs_bigint.limbs.len) + 1);
    var result_bigint: BigIntMutable = .{ .limbs = limbs, .positive = undefined, .len = undefined };
    result_bigint.bitAnd(lhs_bigint, rhs_bigint);
    return sema.intValue_big(ty, result_bigint.toConst());
}
fn intBitwiseNand(sema: *Sema, lhs: Value, rhs: Value, ty: Type) !Value {
    const pool = sema.intern_pool;
    if (ty.index == .bool_type) return Value.makeBool(!(lhs.toBool() and rhs.toBool()));
    const info = ty.intInfo(pool);
    var lhs_space: BigIntSpace = undefined;
    var rhs_space: BigIntSpace = undefined;
    const lhs_bigint = lhs.toBigInt(&lhs_space, pool);
    const rhs_bigint = rhs.toBigInt(&rhs_space, pool);
    const limbs = try sema.arena.alloc(Limb, @max(@max(lhs_bigint.limbs.len, rhs_bigint.limbs.len) + 1, std.math.big.int.calcTwosCompLimbCount(info.bits)));
    var result_bigint: BigIntMutable = .{ .limbs = limbs, .positive = undefined, .len = undefined };
    result_bigint.bitAnd(lhs_bigint, rhs_bigint);
    result_bigint.bitNotWrap(result_bigint.toConst(), info.signedness, info.bits);
    return sema.intValue_big(ty, result_bigint.toConst());
}
fn intBitwiseOr(sema: *Sema, lhs: Value, rhs: Value, ty: Type) !Value {
    const pool = sema.intern_pool;
    if (ty.index == .bool_type) return Value.makeBool(lhs.toBool() or rhs.toBool());
    var lhs_space: BigIntSpace = undefined;
    var rhs_space: BigIntSpace = undefined;
    const lhs_bigint = lhs.toBigInt(&lhs_space, pool);
    const rhs_bigint = rhs.toBigInt(&rhs_space, pool);
    const limbs = try sema.arena.alloc(Limb, @max(lhs_bigint.limbs.len, rhs_bigint.limbs.len));
    var result_bigint: BigIntMutable = .{ .limbs = limbs, .positive = undefined, .len = undefined };
    result_bigint.bitOr(lhs_bigint, rhs_bigint);
    return sema.intValue_big(ty, result_bigint.toConst());
}
fn intBitwiseXor(sema: *Sema, lhs: Value, rhs: Value, ty: Type) !Value {
    const pool = sema.intern_pool;
    if (ty.index == .bool_type) return Value.makeBool(lhs.toBool() != rhs.toBool());
    var lhs_space: BigIntSpace = undefined;
    var rhs_space: BigIntSpace = undefined;
    const lhs_bigint = lhs.toBigInt(&lhs_space, pool);
    const rhs_bigint = rhs.toBigInt(&rhs_space, pool);
    const limbs = try sema.arena.alloc(Limb, @max(lhs_bigint.limbs.len, rhs_bigint.limbs.len) + 1);
    var result_bigint: BigIntMutable = .{ .limbs = limbs, .positive = undefined, .len = undefined };
    result_bigint.bitXor(lhs_bigint, rhs_bigint);
    return sema.intValue_big(ty, result_bigint.toConst());
}

pub const ShlOp = enum { shl, shl_sat, shl_exact };
pub const ShrOp = enum { shr, shr_exact };
pub const DivOp = enum { div, div_trunc, div_floor, div_ceil, div_exact };
pub const ModRemOp = enum { mod, rem };
pub const BitwiseBinOp = enum { @"and", nand, @"or", xor };

fn intShl(sema: *Sema, lhs_ty: Type, lhs: Value, rhs: Value) !Value {
    const pool = sema.intern_pool;
    const info = lhs_ty.intInfo(pool);
    var lhs_space: BigIntSpace = undefined;
    const lhs_bigint = lhs.toBigInt(&lhs_space, pool);
    const shift_amt: usize = @intCast(rhs.toUnsignedInt(pool));
    if (shift_amt >= info.bits) return sema.failWithTooLargeShiftAmount(lhs_ty, rhs);
    var result_bigint = try intShlInner(sema, lhs_bigint, shift_amt);
    result_bigint.truncate(result_bigint.toConst(), info.signedness, info.bits);
    return sema.intValue_big(lhs_ty, result_bigint.toConst());
}
fn intShlSat(sema: *Sema, lhs_ty: Type, lhs: Value, rhs: Value) !Value {
    const pool = sema.intern_pool;
    const info = lhs_ty.intInfo(pool);
    var lhs_space: BigIntSpace = undefined;
    const lhs_bigint = lhs.toBigInt(&lhs_space, pool);
    const shift_amt: usize = amt: {
        if (rhs.getUnsignedInt(pool)) |shift_amt_u64| {
            if (std.math.cast(usize, shift_amt_u64)) |shift_amt| break :amt shift_amt;
        }
        return if (lhs_bigint.eqlZero()) lhs else lhs_ty.maxIntScalar(sema, lhs_ty);
    };
    const limbs = try sema.arena.alloc(Limb, std.math.big.int.calcTwosCompLimbCount(info.bits));
    var result_bigint: BigIntMutable = .{ .limbs = limbs, .positive = undefined, .len = undefined };
    result_bigint.shiftLeftSat(lhs_bigint, shift_amt, info.signedness, info.bits);
    return sema.intValue_big(lhs_ty, result_bigint.toConst());
}
fn intShlWithOverflow(sema: *Sema, lhs_ty: Type, lhs: Value, rhs: Value, truncate_result: bool) !struct { overflow: bool, val: Value } {
    const pool = sema.intern_pool;
    const info = lhs_ty.intInfo(pool);
    var lhs_space: BigIntSpace = undefined;
    const lhs_bigint = lhs.toBigInt(&lhs_space, pool);
    const shift_amt: usize = @intCast(rhs.toUnsignedInt(pool));
    if (shift_amt >= info.bits) return sema.failWithTooLargeShiftAmount(lhs_ty, rhs);
    var result_bigint = try intShlInner(sema, lhs_bigint, shift_amt);
    const overflow = !result_bigint.toConst().fitsInTwosComp(info.signedness, info.bits);
    const result = result: {
        if (overflow) {
            if (truncate_result) {
                result_bigint.truncate(result_bigint.toConst(), info.signedness, info.bits);
            } else {
                break :result try sema.intValue_big(comptime_int_ty, result_bigint.toConst());
            }
        }
        break :result try sema.intValue_big(lhs_ty, result_bigint.toConst());
    };
    return .{ .overflow = overflow, .val = result };
}
fn comptimeIntShl(sema: *Sema, lhs: Value, rhs: Value) !Value {
    const pool = sema.intern_pool;
    var lhs_space: BigIntSpace = undefined;
    const lhs_bigint = lhs.toBigInt(&lhs_space, pool);
    if (rhs.getUnsignedInt(pool)) |shift_amt_u64| {
        if (std.math.cast(usize, shift_amt_u64)) |shift_amt| {
            const result_bigint = try intShlInner(sema, lhs_bigint, shift_amt);
            return sema.intValue_big(comptime_int_ty, result_bigint.toConst());
        }
    }
    return sema.failWithUnsupportedComptimeShiftAmount();
}
fn intShlInner(sema: *Sema, operand: BigIntConst, shift_amt: usize) !BigIntMutable {
    const limbs = try sema.arena.alloc(Limb, operand.limbs.len + (shift_amt / (@sizeOf(Limb) * 8)) + 1);
    var result: BigIntMutable = .{ .limbs = limbs, .positive = undefined, .len = undefined };
    result.shiftLeft(operand, shift_amt);
    return result;
}
fn intShr(sema: *Sema, lhs_ty: Type, rhs_ty: Type, lhs: Value, rhs: Value, op: ShrOp) !Value {
    const pool = sema.intern_pool;
    var lhs_space: BigIntSpace = undefined;
    const lhs_bigint = lhs.toBigInt(&lhs_space, pool);
    const shift_amt: usize = if (rhs_ty.index == .comptime_int_type) amt: {
        if (rhs.getUnsignedInt(pool)) |shift_amt_u64| {
            if (std.math.cast(usize, shift_amt_u64)) |shift_amt| break :amt shift_amt;
        }
        if (rhs.compareAllWithZero(.lt, pool)) {
            return sema.failWithNegativeShiftAmount(rhs);
        } else {
            return sema.failWithUnsupportedComptimeShiftAmount();
        }
    } else @intCast(rhs.toUnsignedInt(pool));
    if (lhs_ty.index != .comptime_int_type and shift_amt >= lhs_ty.intInfo(pool).bits) {
        return sema.failWithTooLargeShiftAmount(lhs_ty, rhs);
    }
    if (op == .shr_exact and lhs_bigint.ctz(shift_amt) < shift_amt) {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "exact shift shifted out 1 bits", .{});
    }
    const result_limbs = lhs_bigint.limbs.len -| (shift_amt / (@sizeOf(Limb) * 8));
    if (result_limbs == 0) {
        if (lhs_bigint.positive) {
            return sema.intValue_u64(lhs_ty, 0);
        } else {
            return sema.intValue_i64(lhs_ty, -1);
        }
    }
    const limbs = try sema.arena.alloc(Limb, result_limbs);
    var result_bigint: BigIntMutable = .{ .limbs = limbs, .positive = undefined, .len = undefined };
    result_bigint.shiftRight(lhs_bigint, shift_amt);
    return sema.intValue_big(lhs_ty, result_bigint.toConst());
}

const testing = std.testing;

const Env = struct {
    pool: InternPool,
    arena_state: std.heap.ArenaAllocator,
    buf: [512]u8 = undefined,
    w: std.Io.Writer = undefined,
    block: Sema.Block = .{},
    sema: Sema = undefined,

    fn setup(e: *Env, gpa: Allocator) !void {
        e.pool = try InternPool.init(gpa);
        e.arena_state = std.heap.ArenaAllocator.init(gpa);
        e.w = std.Io.Writer.fixed(&e.buf);
        e.sema = .{
            .gpa = gpa,
            .arena = e.arena_state.allocator(),
            .intern_pool = &e.pool,
            .zir = undefined,
            .writer = &e.w,
            .inst_map = .empty,
            .comptime_allocs = .empty,
            .namespace = null,
        };
        e.sema.block = &e.block;
    }
    fn deinit(e: *Env) void {
        e.arena_state.deinit();
        e.pool.deinit();
    }
    fn ci(e: *Env, x: i64) !Value {
        return e.sema.intValue_i64(comptime_int_ty, x);
    }
    fn cu(e: *Env, x: u64) !Value {
        return e.sema.intValue_u64(comptime_int_ty, x);
    }
    fn cw(e: *Env, ty: Type, x: u64) !Value {
        return e.sema.intValue_u64(ty, x);
    }
    fn diag(e: *Env) []const u8 {
        return e.w.buffered();
    }
    fn clearDiag(e: *Env) void {
        e.w.end = 0;
    }
};

fn expectDecimal(sema: *Sema, val: Value, expected: []const u8) !void {
    var space: BigIntSpace = undefined;
    const big = sema.intern_pool.indexToKey(val.index).int.storage.toBigInt(&space);
    const actual = try big.toStringAlloc(sema.gpa, 10, .lower);
    defer sema.gpa.free(actual);
    try testing.expectEqualStrings(expected, actual);
}

test "add: small positives" {
    var e: Env = undefined;
    try e.setup(testing.allocator);
    defer e.deinit();
    try expectDecimal(&e.sema, try add(&e.sema, comptime_int_ty, try e.ci(3), try e.ci(4)), "7");
}

test "add: multi-limb carry across the u64 boundary" {
    var e: Env = undefined;
    try e.setup(testing.allocator);
    defer e.deinit();
    try expectDecimal(&e.sema, try add(&e.sema, comptime_int_ty, try e.cu(std.math.maxInt(u64)), try e.cu(1)), "18446744073709551616");
}

test "sub: yields negative when rhs exceeds lhs" {
    var e: Env = undefined;
    try e.setup(testing.allocator);
    defer e.deinit();
    try expectDecimal(&e.sema, try sub(&e.sema, comptime_int_ty, try e.ci(3), try e.ci(5)), "-2");
}

test "mul: multi-limb result" {
    var e: Env = undefined;
    try e.setup(testing.allocator);
    defer e.deinit();
    const two_pow_32 = try e.cu(1 << 32);
    try expectDecimal(&e.sema, try mul(&e.sema, comptime_int_ty, two_pow_32, two_pow_32), "18446744073709551616");
}

test "negate (0 - x): flips sign of a non-zero value" {
    var e: Env = undefined;
    try e.setup(testing.allocator);
    defer e.deinit();
    try expectDecimal(&e.sema, try sub(&e.sema, comptime_int_ty, try e.ci(0), try e.ci(5)), "-5");
    try expectDecimal(&e.sema, try sub(&e.sema, comptime_int_ty, try e.ci(0), try e.ci(-3)), "3");
}

test "negate (0 - x): zero stays canonical positive" {
    var e: Env = undefined;
    try e.setup(testing.allocator);
    defer e.deinit();
    try expectDecimal(&e.sema, try sub(&e.sema, comptime_int_ty, try e.ci(0), try e.ci(0)), "0");
}

test "negate (0 - x): value wider than u64" {
    var e: Env = undefined;
    try e.setup(testing.allocator);
    defer e.deinit();
    const big = try add(&e.sema, comptime_int_ty, try e.cu(std.math.maxInt(u64)), try e.cu(1));
    try expectDecimal(&e.sema, try sub(&e.sema, comptime_int_ty, try e.ci(0), big), "-18446744073709551616");
}

test "divTrunc: positive operands" {
    var e: Env = undefined;
    try e.setup(testing.allocator);
    defer e.deinit();
    try expectDecimal(&e.sema, try div(&e.sema, comptime_int_ty, try e.ci(7), try e.ci(2), .div_trunc), "3");
}

test "divTrunc: negative dividend rounds toward zero" {
    var e: Env = undefined;
    try e.setup(testing.allocator);
    defer e.deinit();
    try expectDecimal(&e.sema, try div(&e.sema, comptime_int_ty, try e.ci(-7), try e.ci(2), .div_trunc), "-3");
}

test "divFloor: negative dividend rounds toward negative infinity" {
    var e: Env = undefined;
    try e.setup(testing.allocator);
    defer e.deinit();
    try expectDecimal(&e.sema, try div(&e.sema, comptime_int_ty, try e.ci(-7), try e.ci(2), .div_floor), "-4");
}

test "divExact: succeeds when the remainder is zero" {
    var e: Env = undefined;
    try e.setup(testing.allocator);
    defer e.deinit();
    try expectDecimal(&e.sema, try div(&e.sema, comptime_int_ty, try e.ci(6), try e.ci(2), .div_exact), "3");
}

test "divExact: errors when the remainder is non-zero" {
    var e: Env = undefined;
    try e.setup(testing.allocator);
    defer e.deinit();
    try testing.expectError(error.AnalysisFail, div(&e.sema, comptime_int_ty, try e.ci(7), try e.ci(2), .div_exact));
    try testing.expect(std.mem.indexOf(u8, e.diag(), "exact division produced remainder") != null);
}

test "mod and rem differ in sign for a negative dividend" {
    var e: Env = undefined;
    try e.setup(testing.allocator);
    defer e.deinit();
    try expectDecimal(&e.sema, try modRem(&e.sema, comptime_int_ty, try e.ci(-7), try e.ci(2), .mod), "1");
    try expectDecimal(&e.sema, try modRem(&e.sema, comptime_int_ty, try e.ci(-7), try e.ci(2), .rem), "-1");
}

test "shl: small" {
    var e: Env = undefined;
    try e.setup(testing.allocator);
    defer e.deinit();
    try expectDecimal(&e.sema, try shl(&e.sema, comptime_int_ty, try e.ci(1), try e.ci(4), .shl), "16");
}

test "shl: across the limb boundary" {
    var e: Env = undefined;
    try e.setup(testing.allocator);
    defer e.deinit();
    try expectDecimal(&e.sema, try shl(&e.sema, comptime_int_ty, try e.ci(1), try e.ci(64), .shl), "18446744073709551616");
}

test "shr: small" {
    var e: Env = undefined;
    try e.setup(testing.allocator);
    defer e.deinit();
    try expectDecimal(&e.sema, try shr(&e.sema, comptime_int_ty, comptime_int_ty, try e.ci(256), try e.ci(4), .shr), "16");
}

test "shift: rejects negative and too-large amounts" {
    var e: Env = undefined;
    try e.setup(testing.allocator);
    defer e.deinit();
    try testing.expectError(error.AnalysisFail, shl(&e.sema, comptime_int_ty, try e.ci(1), try e.ci(-1), .shl));
    try testing.expect(std.mem.indexOf(u8, e.diag(), "shift by negative amount") != null);
    e.clearDiag();
    const u8_ty: Type = .fromIndex(.u8_type);
    try testing.expectError(error.AnalysisFail, shl(&e.sema, u8_ty, try e.cw(u8_ty, 1), try e.ci(8), .shl));
    try testing.expect(std.mem.indexOf(u8, e.diag(), "too large for operand type") != null);
}

test "bitwise and on positives" {
    var e: Env = undefined;
    try e.setup(testing.allocator);
    defer e.deinit();
    try expectDecimal(&e.sema, try bitwiseBin(&e.sema, comptime_int_ty, try e.ci(12), try e.ci(10), .@"and"), "8");
}

test "bitwise or on positives" {
    var e: Env = undefined;
    try e.setup(testing.allocator);
    defer e.deinit();
    try expectDecimal(&e.sema, try bitwiseBin(&e.sema, comptime_int_ty, try e.ci(12), try e.ci(10), .@"or"), "14");
}

test "bitwise xor on positives" {
    var e: Env = undefined;
    try e.setup(testing.allocator);
    defer e.deinit();
    try expectDecimal(&e.sema, try bitwiseBin(&e.sema, comptime_int_ty, try e.ci(12), try e.ci(10), .xor), "6");
}

test "bitwise xor of a value with itself is zero" {
    var e: Env = undefined;
    try e.setup(testing.allocator);
    defer e.deinit();
    const twelve = try e.ci(12);
    try expectDecimal(&e.sema, try bitwiseBin(&e.sema, comptime_int_ty, twelve, twelve, .xor), "0");
}

test "all division ops reject a zero divisor" {
    var e: Env = undefined;
    try e.setup(testing.allocator);
    defer e.deinit();
    inline for (.{ .div, .div_trunc, .div_floor, .div_exact }) |op| {
        try testing.expectError(error.AnalysisFail, div(&e.sema, comptime_int_ty, try e.ci(1), try e.ci(0), op));
        e.clearDiag();
    }
    try testing.expectError(error.AnalysisFail, modRem(&e.sema, comptime_int_ty, try e.ci(1), try e.ci(0), .mod));
    e.clearDiag();
    try testing.expectError(error.AnalysisFail, modRem(&e.sema, comptime_int_ty, try e.ci(1), try e.ci(0), .rem));
}
