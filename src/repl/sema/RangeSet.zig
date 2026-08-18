const RangeSet = @This();

list: std.MultiArrayList(Range),

pub const Range = struct {
    first: Value,
    last: Value,
    src: LazySrcLoc,
};

pub const empty: RangeSet = .{ .list = .empty };

pub fn deinit(self: *RangeSet, allocator: Allocator) void {
    self.list.deinit(allocator);
    self.* = undefined;
}

pub fn ensureUnusedCapacity(set: *RangeSet, allocator: Allocator, additional_count: usize) Allocator.Error!void {
    return set.list.ensureUnusedCapacity(allocator, additional_count);
}

pub fn addAssumeCapacity(set: *RangeSet, new: Range, ty: Type, pool: *const InternPool) ?Range {
    assert(new.first.typeOf(pool).index == ty.index);
    assert(new.last.typeOf(pool).index == ty.index);
    assert(new.first.compareScalar(.lte, new.last, ty, pool));

    const idx = std.sort.lowerBound(Value, set.list.items(.last), @as(SearchCtx, .{
        .val = new.first,
        .pool = pool,
    }), compare);

    if (idx != set.list.len and // `new.first` is *not* greater than all `old.last`
        new.last.compareScalar(.gte, set.list.items(.first)[idx], ty, pool))
    {
        return set.list.get(idx); // `new` overlaps with existing range.
    }
    set.list.insertAssumeCapacity(idx, new);
    return null;
}

pub fn spans(
    set: *RangeSet,
    allocator: Allocator,
    first: Value,
    last: Value,
    ty: Type,
    pool: *const InternPool,
) Allocator.Error!bool {
    assert(first.typeOf(pool).index == ty.index);
    assert(last.typeOf(pool).index == ty.index);
    if (set.list.len == 0) return false;

    assert(std.sort.isSorted(Value, set.list.items(.first), @as(SortCtx, .{ .ty = ty, .pool = pool }), lessThan));
    assert(std.sort.isSorted(Value, set.list.items(.last), @as(SortCtx, .{ .ty = ty, .pool = pool }), lessThan));

    if (!set.list.items(.first)[0].eql(first, ty, pool) or
        !set.list.items(.last)[set.list.len - 1].eql(last, ty, pool))
    {
        return false;
    }

    const limbs = try allocator.alloc(
        math.big.Limb,
        math.big.int.calcTwosCompLimbCount(ty.intInfo(pool).bits),
    );
    defer allocator.free(limbs);
    var counter: math.big.int.Mutable = .init(limbs, 0);

    var space: InternPool.Key.Int.Storage.BigIntSpace = undefined;

    // look for gaps
    for (
        set.list.items(.first)[1..],
        set.list.items(.last)[0 .. set.list.len - 1],
    ) |cur_first, prev_last| {
        // prev_last + 1 == cur_first
        counter.copy(prev_last.toBigInt(&space, pool));
        counter.addScalar(counter.toConst(), 1);

        const cur_start_int = cur_first.toBigInt(&space, pool);
        if (!cur_start_int.eql(counter.toConst())) {
            return false;
        }
    }

    return true;
}

const SearchCtx = struct {
    val: Value,
    pool: *const InternPool,
};
fn compare(ctx: SearchCtx, other: Value) math.Order {
    return ctx.val.order(other, ctx.pool);
}

const SortCtx = struct {
    ty: Type,
    pool: *const InternPool,
};
fn lessThan(ctx: SortCtx, a: Value, b: Value) bool {
    return a.compareScalar(.lt, b, ctx.ty, ctx.pool);
}

const std = @import("std");
const math = std.math;
const assert = std.debug.assert;
const Allocator = std.mem.Allocator;

const InternPool = @import("InternPool.zig");
const Type = @import("Type.zig");
const Value = @import("Value.zig");
const LazySrcLoc = @import("ErrorMsg.zig").LazySrcLoc;
