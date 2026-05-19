//! Runtime-only port of the compiler's `src/Sema/arith.zig`. Each public
//! function takes plain `std.math.big.int.Const` operands plus the
//! InternPool, performs the operation with `std.math.big.int.Mutable`, and
//! interns the result. Callers (typically Sema's per-tag handlers) own the
//! type-check + Value-wrapping above this layer.
//!
//! Compiler reference: src/Sema/arith.zig in the Zig compiler tree.
//! Their `intAdd`/`intSub`/`intMul`/`intNegate` correspond directly to the
//! `internAdd`/`internSub`/`internMul`/`internNegate` helpers here. The
//! compiler's outer `add`/`sub`/etc. wrappers (which dispatch
//! scalar/vector/float, handle undef, and report overflow) live in the
//! caller until we need them.

const std = @import("std");
const assert = std.debug.assert;
const Allocator = std.mem.Allocator;
const BigIntConst = std.math.big.int.Const;
const BigIntMutable = std.math.big.int.Mutable;
const Limb = std.math.big.Limb;

const InternPool = @import("InternPool.zig");

/// `lhs + rhs` as a fresh `comptime_int` value in the pool. Workspace is sized
/// to the bound documented on `BigIntMutable.add`:
/// `@max(lhs.limbs.len, rhs.limbs.len) + 1` limbs.
pub fn internAdd(
    gpa: Allocator,
    intern_pool: *InternPool,
    lhs: BigIntConst,
    rhs: BigIntConst,
) Allocator.Error!InternPool.Index {
    assert(@intFromPtr(intern_pool) != 0);
    assert(lhs.limbs.len > 0);
    assert(rhs.limbs.len > 0);

    const workspace_len = @max(lhs.limbs.len, rhs.limbs.len) + 1;
    const workspace = try gpa.alloc(Limb, workspace_len);
    defer gpa.free(workspace);

    var mutable: BigIntMutable = .{
        .limbs = workspace,
        .len = undefined,
        .positive = undefined,
    };
    mutable.add(lhs, rhs);

    assert(mutable.len > 0);
    assert(mutable.len <= workspace_len);

    const idx = try intern_pool.internComptimeInt(mutable.toConst());
    assert(idx != .none);
    return idx;
}

/// `lhs - rhs` as a fresh `comptime_int` value in the pool. Workspace is
/// sized to the bound documented on `BigIntMutable.sub`:
/// `@max(lhs.limbs.len, rhs.limbs.len) + 1` limbs.
pub fn internSub(
    gpa: Allocator,
    intern_pool: *InternPool,
    lhs: BigIntConst,
    rhs: BigIntConst,
) Allocator.Error!InternPool.Index {
    assert(@intFromPtr(intern_pool) != 0);
    assert(lhs.limbs.len > 0);
    assert(rhs.limbs.len > 0);

    const workspace_len = @max(lhs.limbs.len, rhs.limbs.len) + 1;
    const workspace = try gpa.alloc(Limb, workspace_len);
    defer gpa.free(workspace);

    var mutable: BigIntMutable = .{
        .limbs = workspace,
        .len = undefined,
        .positive = undefined,
    };
    mutable.sub(lhs, rhs);

    assert(mutable.len > 0);
    assert(mutable.len <= workspace_len);

    const idx = try intern_pool.internComptimeInt(mutable.toConst());
    assert(idx != .none);
    return idx;
}

/// `lhs * rhs` as a fresh `comptime_int` value in the pool. Workspace is
/// sized to the bound documented on `BigIntMutable.mulNoAlias`:
/// `lhs.limbs.len + rhs.limbs.len` limbs. The fresh workspace cannot alias
/// either operand (both live in the pool's arena), so `mulNoAlias` is
/// strictly safe and avoids the extra temp buffer `mul` would need.
pub fn internMul(
    gpa: Allocator,
    intern_pool: *InternPool,
    lhs: BigIntConst,
    rhs: BigIntConst,
) Allocator.Error!InternPool.Index {
    assert(@intFromPtr(intern_pool) != 0);
    assert(lhs.limbs.len > 0);
    assert(rhs.limbs.len > 0);

    const workspace_len = lhs.limbs.len + rhs.limbs.len;
    const workspace = try gpa.alloc(Limb, workspace_len);
    defer gpa.free(workspace);

    var mutable: BigIntMutable = .{
        .limbs = workspace,
        .len = undefined,
        .positive = undefined,
    };
    // Workspace is gpa-allocated; lhs/rhs live in the pool's arena. The
    // `mulNoAlias` precondition (rma cannot alias a or b) is satisfied by
    // construction, so we can skip the extra temp buffer that `mul` needs.
    assert(@intFromPtr(workspace.ptr) != @intFromPtr(lhs.limbs.ptr));
    assert(@intFromPtr(workspace.ptr) != @intFromPtr(rhs.limbs.ptr));
    mutable.mulNoAlias(lhs, rhs, gpa);

    assert(mutable.len > 0);
    assert(mutable.len <= workspace_len);

    const idx = try intern_pool.internComptimeInt(mutable.toConst());
    assert(idx != .none);
    return idx;
}

/// `-operand` as a fresh `comptime_int` value in the pool. Allocation-free
/// in the steady state: `BigIntConst.negate` returns a sign-flipped view
/// over the operand's limbs, and `internComptimeInt` copies them into the
/// pool's arena. Zero is preserved as canonical positive zero, matching the
/// representation the rest of the pool uses for `Index.zero`.
pub fn internNegate(
    gpa: Allocator,
    intern_pool: *InternPool,
    operand: BigIntConst,
) Allocator.Error!InternPool.Index {
    _ = gpa;
    assert(@intFromPtr(intern_pool) != 0);
    assert(operand.limbs.len > 0);

    // operand.limbs may alias the pool's big_int_limbs buffer; InternPool's
    // aliasing guard handles the copy. negate is sign-only — magnitude
    // limbs are unchanged — so the result limb count equals the operand's.
    const operand_len = operand.limbs.len;

    const idx = if (operand.eqlZero())
        try intern_pool.internComptimeInt(operand)
    else
        try intern_pool.internComptimeInt(operand.negate());

    assert(idx != .none);
    var space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
    const stored = intern_pool.indexToKey(idx).int.storage.toBigInt(&space);
    assert(stored.limbs.len == operand_len);
    return idx;
}

pub const DivError = Allocator.Error || error{ DivisionByZero, DivisionNotExact };

/// `@divTrunc(lhs, rhs)`: integer division rounded toward zero. Quotient
/// shares sign of the mathematical quotient.
pub fn internDivTrunc(
    gpa: Allocator,
    intern_pool: *InternPool,
    lhs: BigIntConst,
    rhs: BigIntConst,
) DivError!InternPool.Index {
    const idx = (try computeDivPair(gpa, intern_pool, lhs, rhs, .trunc)).quotient;
    assert(idx != .none);
    return idx;
}

/// `@divFloor(lhs, rhs)`: integer division rounded toward -inf.
pub fn internDivFloor(
    gpa: Allocator,
    intern_pool: *InternPool,
    lhs: BigIntConst,
    rhs: BigIntConst,
) DivError!InternPool.Index {
    const idx = (try computeDivPair(gpa, intern_pool, lhs, rhs, .floor)).quotient;
    assert(idx != .none);
    return idx;
}

/// `@divExact(lhs, rhs)`: integer division asserting `rhs` evenly divides
/// `lhs`. The runtime equivalent of the compiler's safety check: if the
/// trunc-remainder is nonzero we return `error.DivisionNotExact`.
pub fn internDivExact(
    gpa: Allocator,
    intern_pool: *InternPool,
    lhs: BigIntConst,
    rhs: BigIntConst,
) DivError!InternPool.Index {
    const pair = try computeDivPair(gpa, intern_pool, lhs, rhs, .trunc);
    assert(pair.quotient != .none);
    assert(pair.remainder != .none);

    var space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
    const remainder = intern_pool.indexToKey(pair.remainder).int.storage.toBigInt(&space);
    if (!remainder.eqlZero()) return error.DivisionNotExact;
    return pair.quotient;
}

/// `@mod(lhs, rhs)`: modulo, result has sign of `rhs` (floor-mod).
pub fn internMod(
    gpa: Allocator,
    intern_pool: *InternPool,
    lhs: BigIntConst,
    rhs: BigIntConst,
) DivError!InternPool.Index {
    const idx = (try computeDivPair(gpa, intern_pool, lhs, rhs, .floor)).remainder;
    assert(idx != .none);
    return idx;
}

/// `@rem(lhs, rhs)`: remainder, result has sign of `lhs` (trunc-mod).
pub fn internRem(
    gpa: Allocator,
    intern_pool: *InternPool,
    lhs: BigIntConst,
    rhs: BigIntConst,
) DivError!InternPool.Index {
    const idx = (try computeDivPair(gpa, intern_pool, lhs, rhs, .trunc)).remainder;
    assert(idx != .none);
    return idx;
}

/// Bitwise binary kernels: three near-identical pairs of workspace alloc +
/// `BigIntMutable.bit*` + intern. The workspace bound `@max(lhs, rhs) + 1`
/// covers every sign combination the stdlib documents (bitAnd reaches
/// `@max + 1` for two negatives; bitOr / bitXor reach `@max + 1` for mixed
/// signs). One bound for all three keeps the shared kernel uniform.
pub fn internBitAnd(
    gpa: Allocator,
    intern_pool: *InternPool,
    lhs: BigIntConst,
    rhs: BigIntConst,
) Allocator.Error!InternPool.Index {
    return runBitwise(gpa, intern_pool, lhs, rhs, BigIntMutable.bitAnd);
}

pub fn internBitOr(
    gpa: Allocator,
    intern_pool: *InternPool,
    lhs: BigIntConst,
    rhs: BigIntConst,
) Allocator.Error!InternPool.Index {
    return runBitwise(gpa, intern_pool, lhs, rhs, BigIntMutable.bitOr);
}

pub fn internXor(
    gpa: Allocator,
    intern_pool: *InternPool,
    lhs: BigIntConst,
    rhs: BigIntConst,
) Allocator.Error!InternPool.Index {
    return runBitwise(gpa, intern_pool, lhs, rhs, BigIntMutable.bitXor);
}

fn runBitwise(
    gpa: Allocator,
    intern_pool: *InternPool,
    lhs: BigIntConst,
    rhs: BigIntConst,
    op: *const fn (*BigIntMutable, BigIntConst, BigIntConst) void,
) Allocator.Error!InternPool.Index {
    assert(@intFromPtr(intern_pool) != 0);
    assert(lhs.limbs.len > 0);
    assert(rhs.limbs.len > 0);

    const workspace_len = @max(lhs.limbs.len, rhs.limbs.len) + 1;
    const workspace = try gpa.alloc(Limb, workspace_len);
    defer gpa.free(workspace);

    var mutable: BigIntMutable = .{
        .limbs = workspace,
        .len = undefined,
        .positive = undefined,
    };
    op(&mutable, lhs, rhs);

    assert(mutable.len > 0);
    assert(mutable.len <= workspace_len);

    const idx = try intern_pool.internComptimeInt(mutable.toConst());
    assert(idx != .none);
    return idx;
}

/// Error set for the shift kernels. `ConvertError` is reused from
/// `std.math.big.int.Const` so a negative-shift surfaces as
/// `error.NegativeIntoUnsigned` and a shift-too-big-for-usize surfaces as
/// `error.TargetTooSmall` — the same names stdlib gives those conditions
/// when extracting via `BigIntConst.toInt`. `ShiftAmountTooLarge` is the
/// one project-specific addition: our soft cap on workspace size.
pub const ShiftError =
    Allocator.Error || std.math.big.int.Const.ConvertError || error{ShiftAmountTooLarge};

/// Cap on shift amounts. A comptime_int shift is mathematically defined
/// for any non-negative amount, but allocating workspace for a shift of
/// `usize.max` bits is absurd. The cap stays high enough that any
/// plausible numeric work fits (~2 MB of limbs).
pub const max_shift_bits: usize = 1 << 24;

/// `lhs << rhs`. Workspace sized to the bound on
/// `BigIntMutable.shiftLeft`: `a.limbs.len + ceil(shift / limb_bits)`.
pub fn internShl(
    gpa: Allocator,
    intern_pool: *InternPool,
    lhs: BigIntConst,
    rhs: BigIntConst,
) ShiftError!InternPool.Index {
    const shift = try shiftAmount(rhs);
    const limb_bits = @sizeOf(Limb) * 8;
    return runShift(gpa, intern_pool, lhs, shift, lhs.limbs.len + (shift / limb_bits) + 1, .left);
}

/// `lhs >> rhs`. Workspace cannot grow beyond `lhs.limbs.len`.
pub fn internShr(
    gpa: Allocator,
    intern_pool: *InternPool,
    lhs: BigIntConst,
    rhs: BigIntConst,
) ShiftError!InternPool.Index {
    const shift = try shiftAmount(rhs);
    return runShift(gpa, intern_pool, lhs, shift, lhs.limbs.len, .right);
}

fn shiftAmount(rhs: BigIntConst) ShiftError!usize {
    assert(rhs.limbs.len > 0);
    // Stdlib's `toInt` short-circuits negative-into-unsigned through
    // `TargetTooSmall` (its sign check happens before the explicit
    // `NegativeIntoUnsigned` arm), so pre-check the sign here so callers
    // see the more precise error name.
    if (!rhs.positive and !rhs.eqlZero()) return error.NegativeIntoUnsigned;
    const shift = try rhs.toInt(usize);
    if (shift > max_shift_bits) return error.ShiftAmountTooLarge;
    return shift;
}

fn runShift(
    gpa: Allocator,
    intern_pool: *InternPool,
    lhs: BigIntConst,
    shift: usize,
    workspace_len: usize,
    direction: enum { left, right },
) Allocator.Error!InternPool.Index {
    assert(@intFromPtr(intern_pool) != 0);
    assert(lhs.limbs.len > 0);

    const workspace = try gpa.alloc(Limb, workspace_len);
    defer gpa.free(workspace);

    var mutable: BigIntMutable = .{
        .limbs = workspace,
        .len = undefined,
        .positive = undefined,
    };
    switch (direction) {
        .left => mutable.shiftLeft(lhs, shift),
        .right => mutable.shiftRight(lhs, shift),
    }

    assert(mutable.len > 0);
    assert(mutable.len <= workspace_len);

    const idx = try intern_pool.internComptimeInt(mutable.toConst());
    assert(idx != .none);
    return idx;
}

/// Integer comparison. Result is a plain `bool` (no intern needed —
/// callers map to `Index.bool_true` / `Index.bool_false`). Sign and
/// magnitude are handled by `BigIntConst.order`; the `Order.compare`
/// helper translates that to the requested operator.
pub fn compareInt(
    lhs: BigIntConst,
    rhs: BigIntConst,
    op: std.math.CompareOperator,
) bool {
    assert(lhs.limbs.len > 0);
    assert(rhs.limbs.len > 0);
    return lhs.order(rhs).compare(op);
}

const DivKind = enum { trunc, floor };

const DivPair = struct {
    quotient: InternPool.Index,
    remainder: InternPool.Index,
};

const testing = std.testing;

fn constLimbs(slice: []std.math.big.Limb, positive: bool) BigIntConst {
    return .{ .limbs = slice, .positive = positive };
}

fn expectInternedDecimal(
    gpa: Allocator,
    intern_pool: *InternPool,
    idx: InternPool.Index,
    expected: []const u8,
) !void {
    var space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
    const stored = intern_pool.indexToKey(idx).int.storage.toBigInt(&space);
    const actual = try stored.toStringAlloc(gpa, 10, .lower);
    defer gpa.free(actual);
    try testing.expectEqualStrings(expected, actual);
}

test "internAdd: small positives" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    var a = [_]Limb{3};
    var b = [_]Limb{4};
    const idx = try internAdd(gpa, &pool, constLimbs(&a, true), constLimbs(&b, true));
    try expectInternedDecimal(gpa, &pool, idx, "7");
}

test "internAdd: multi-limb carry across u64 boundary" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    var a = [_]Limb{std.math.maxInt(Limb)};
    var b = [_]Limb{1};
    const idx = try internAdd(gpa, &pool, constLimbs(&a, true), constLimbs(&b, true));
    // 2^64 on 64-bit hosts (or 2^32 on 32-bit). Same result either way: the
    // value equals @sizeOf(Limb) bits worth of 2-power.
    var space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
    const stored = pool.indexToKey(idx).int.storage.toBigInt(&space);
    try testing.expect(stored.limbs.len >= 2);
    try testing.expect(stored.positive);
}

test "internSub: yields negative when rhs > lhs" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    var a = [_]Limb{3};
    var b = [_]Limb{5};
    const idx = try internSub(gpa, &pool, constLimbs(&a, true), constLimbs(&b, true));
    try expectInternedDecimal(gpa, &pool, idx, "-2");
}

test "internMul: multi-limb result" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    var a = [_]Limb{1_000_000};
    var b = [_]Limb{1_000_000};
    const idx = try internMul(gpa, &pool, constLimbs(&a, true), constLimbs(&b, true));
    try expectInternedDecimal(gpa, &pool, idx, "1000000000000");
}

test "internNegate: flips sign of non-zero" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    var v = [_]Limb{42};
    const idx = try internNegate(gpa, &pool, constLimbs(&v, true));
    try expectInternedDecimal(gpa, &pool, idx, "-42");
}

test "internNegate: zero stays positive (canonical representation)" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    var z = [_]Limb{0};
    const idx = try internNegate(gpa, &pool, constLimbs(&z, true));
    var space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
    const stored = pool.indexToKey(idx).int.storage.toBigInt(&space);
    try testing.expect(stored.positive);
    try testing.expectEqual(@as(usize, 1), stored.limbs.len);
    try testing.expectEqual(@as(Limb, 0), stored.limbs[0]);
}

test "internNegate: forwarding pool-aliased operand is safe" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    // Multi-limb value: forces the big-int path, otherwise the small-int
    // compressor packs it into an inline tag and the aliasing concern
    // (limbs borrowed from the pool's `extra` buffer) never arises.
    var big = [_]Limb{ 0, 1 }; // 2^@bitSizeOf(Limb)
    const big_idx = try pool.internIntValue(.u128_type, constLimbs(&big, true));

    // Drain `big_int_limbs` capacity so the next intern triggers a realloc
    // that would invalidate any aliased source pointer before its memcpy
    // ran.
    while (pool.big_int_limbs.items.len < pool.big_int_limbs.capacity) {
        try pool.big_int_limbs.append(pool.gpa, 0);
    }

    var space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
    const aliased = pool.indexToKey(big_idx).int.storage.toBigInt(&space);
    const neg_idx = try internNegate(gpa, &pool, aliased);
    var print_space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
    const stored = pool.indexToKey(neg_idx).int.storage.toBigInt(&print_space);
    try testing.expect(!stored.positive);
    try testing.expectEqual(@as(usize, 2), stored.limbs.len);
}

test "internDivTrunc: positive operands" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    var a = [_]Limb{7};
    var b = [_]Limb{2};
    const idx = try internDivTrunc(gpa, &pool, constLimbs(&a, true), constLimbs(&b, true));
    try expectInternedDecimal(gpa, &pool, idx, "3");
}

test "internDivTrunc: negative dividend rounds toward zero" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    var a = [_]Limb{7};
    var b = [_]Limb{2};
    const idx = try internDivTrunc(gpa, &pool, constLimbs(&a, false), constLimbs(&b, true));
    try expectInternedDecimal(gpa, &pool, idx, "-3");
}

test "internDivFloor: negative dividend rounds toward -inf" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    var a = [_]Limb{7};
    var b = [_]Limb{2};
    const idx = try internDivFloor(gpa, &pool, constLimbs(&a, false), constLimbs(&b, true));
    try expectInternedDecimal(gpa, &pool, idx, "-4");
}

test "internDivExact: succeeds when remainder is zero" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    var a = [_]Limb{10};
    var b = [_]Limb{2};
    const idx = try internDivExact(gpa, &pool, constLimbs(&a, true), constLimbs(&b, true));
    try expectInternedDecimal(gpa, &pool, idx, "5");
}

test "internDivExact: errors when remainder is non-zero" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    var a = [_]Limb{7};
    var b = [_]Limb{2};
    try testing.expectError(
        error.DivisionNotExact,
        internDivExact(gpa, &pool, constLimbs(&a, true), constLimbs(&b, true)),
    );
}

test "internMod and internRem differ in sign for negative dividend" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    var a = [_]Limb{7};
    var b = [_]Limb{2};
    // @mod: result has sign of divisor → +1
    const mod_idx = try internMod(gpa, &pool, constLimbs(&a, false), constLimbs(&b, true));
    try expectInternedDecimal(gpa, &pool, mod_idx, "1");
    // @rem: result has sign of dividend → -1
    const rem_idx = try internRem(gpa, &pool, constLimbs(&a, false), constLimbs(&b, true));
    try expectInternedDecimal(gpa, &pool, rem_idx, "-1");
}

test "internShl: small" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    var a = [_]Limb{1};
    var s = [_]Limb{5};
    const idx = try internShl(gpa, &pool, constLimbs(&a, true), constLimbs(&s, true));
    try expectInternedDecimal(gpa, &pool, idx, "32");
}

test "internShl: across limb boundary" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    var a = [_]Limb{1};
    var s = [_]Limb{128};
    const idx = try internShl(gpa, &pool, constLimbs(&a, true), constLimbs(&s, true));
    try expectInternedDecimal(gpa, &pool, idx, "340282366920938463463374607431768211456"); // 2^128
}

test "internShr: small" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    var a = [_]Limb{1024};
    var s = [_]Limb{3};
    const idx = try internShr(gpa, &pool, constLimbs(&a, true), constLimbs(&s, true));
    try expectInternedDecimal(gpa, &pool, idx, "128");
}

test "shift kernels surface stdlib ConvertError variants" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    var a = [_]Limb{1};
    var s = [_]Limb{2};
    // Negative shift -> stdlib's NegativeIntoUnsigned, propagated verbatim.
    try testing.expectError(
        error.NegativeIntoUnsigned,
        internShl(gpa, &pool, constLimbs(&a, true), constLimbs(&s, false)),
    );

    // Shift beyond our soft cap -> our one project-specific variant.
    var s_huge = [_]Limb{max_shift_bits + 1};
    try testing.expectError(
        error.ShiftAmountTooLarge,
        internShl(gpa, &pool, constLimbs(&a, true), constLimbs(&s_huge, true)),
    );
}

test "internBitAnd on positives" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    var a = [_]Limb{0b1100};
    var b = [_]Limb{0b1010};
    const idx = try internBitAnd(gpa, &pool, constLimbs(&a, true), constLimbs(&b, true));
    try expectInternedDecimal(gpa, &pool, idx, "8"); // 0b1000
}

test "internBitOr on positives" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    var a = [_]Limb{0b1100};
    var b = [_]Limb{0b1010};
    const idx = try internBitOr(gpa, &pool, constLimbs(&a, true), constLimbs(&b, true));
    try expectInternedDecimal(gpa, &pool, idx, "14"); // 0b1110
}

test "internXor on positives" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    var a = [_]Limb{0b1100};
    var b = [_]Limb{0b1010};
    const idx = try internXor(gpa, &pool, constLimbs(&a, true), constLimbs(&b, true));
    try expectInternedDecimal(gpa, &pool, idx, "6"); // 0b0110
}

test "internXor of a value with itself is zero" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    var a = [_]Limb{0xCAFE};
    var b = [_]Limb{0xCAFE};
    const idx = try internXor(gpa, &pool, constLimbs(&a, true), constLimbs(&b, true));
    try expectInternedDecimal(gpa, &pool, idx, "0");
}

test "compareInt covers all six operators on simple positives" {
    var three = [_]Limb{3};
    var five = [_]Limb{5};
    const a = constLimbs(&three, true);
    const b = constLimbs(&five, true);

    try testing.expect(compareInt(a, b, .lt));
    try testing.expect(compareInt(a, b, .lte));
    try testing.expect(!compareInt(a, b, .eq));
    try testing.expect(!compareInt(a, b, .gte));
    try testing.expect(!compareInt(a, b, .gt));
    try testing.expect(compareInt(a, b, .neq));
}

test "compareInt: equal values" {
    var seven = [_]Limb{7};
    var seven_again = [_]Limb{7};
    const a = constLimbs(&seven, true);
    const b = constLimbs(&seven_again, true);

    try testing.expect(compareInt(a, b, .eq));
    try testing.expect(compareInt(a, b, .lte));
    try testing.expect(compareInt(a, b, .gte));
    try testing.expect(!compareInt(a, b, .lt));
    try testing.expect(!compareInt(a, b, .gt));
    try testing.expect(!compareInt(a, b, .neq));
}

test "compareInt: sign matters when magnitudes match" {
    var seven_pos = [_]Limb{7};
    var seven_neg = [_]Limb{7};
    const pos = constLimbs(&seven_pos, true);
    const neg = constLimbs(&seven_neg, false);

    // -7 < +7
    try testing.expect(compareInt(neg, pos, .lt));
    try testing.expect(compareInt(pos, neg, .gt));
    try testing.expect(compareInt(neg, pos, .neq));
}

test "compareInt: signed zero is canonical positive zero" {
    var zero_a = [_]Limb{0};
    var zero_b = [_]Limb{0};
    const a = constLimbs(&zero_a, true);
    const b = constLimbs(&zero_b, true);

    try testing.expect(compareInt(a, b, .eq));
    try testing.expect(!compareInt(a, b, .lt));
    try testing.expect(!compareInt(a, b, .gt));
}

test "all division ops error on zero divisor" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    var a = [_]Limb{1};
    var z = [_]Limb{0};
    const lhs = constLimbs(&a, true);
    const rhs = constLimbs(&z, true);
    try testing.expectError(error.DivisionByZero, internDivTrunc(gpa, &pool, lhs, rhs));
    try testing.expectError(error.DivisionByZero, internDivFloor(gpa, &pool, lhs, rhs));
    try testing.expectError(error.DivisionByZero, internDivExact(gpa, &pool, lhs, rhs));
    try testing.expectError(error.DivisionByZero, internMod(gpa, &pool, lhs, rhs));
    try testing.expectError(error.DivisionByZero, internRem(gpa, &pool, lhs, rhs));
}

fn computeDivPair(
    gpa: Allocator,
    intern_pool: *InternPool,
    lhs: BigIntConst,
    rhs: BigIntConst,
    kind: DivKind,
) DivError!DivPair {
    assert(@intFromPtr(intern_pool) != 0);
    assert(lhs.limbs.len > 0);
    assert(rhs.limbs.len > 0);

    if (rhs.eqlZero()) return error.DivisionByZero;

    const q_limbs = lhs.limbs.len;
    const r_limbs = rhs.limbs.len;
    const tmp_limbs = std.math.big.int.calcDivLimbsBufferLen(lhs.limbs.len, rhs.limbs.len);
    const total = q_limbs + r_limbs + tmp_limbs;
    const all = try gpa.alloc(Limb, total);
    defer gpa.free(all);

    var quotient: BigIntMutable = .{
        .limbs = all[0..q_limbs],
        .len = undefined,
        .positive = undefined,
    };
    var remainder: BigIntMutable = .{
        .limbs = all[q_limbs..][0..r_limbs],
        .len = undefined,
        .positive = undefined,
    };
    const tmp_buffer = all[q_limbs + r_limbs ..];

    // The stdlib div kernel asserts q and r must not alias each other.
    // Pre-check here so a mis-slicing of `all` surfaces with a clearer
    // message than the assert deep inside std.math.big.int.div.
    assert(@intFromPtr(quotient.limbs.ptr) != @intFromPtr(remainder.limbs.ptr));
    assert(tmp_buffer.len == tmp_limbs);

    switch (kind) {
        .trunc => BigIntMutable.divTrunc(&quotient, &remainder, lhs, rhs, tmp_buffer),
        .floor => BigIntMutable.divFloor(&quotient, &remainder, lhs, rhs, tmp_buffer),
    }

    assert(quotient.len > 0);
    assert(quotient.len <= q_limbs);
    assert(remainder.len > 0);
    assert(remainder.len <= r_limbs);

    const q_idx = try intern_pool.internComptimeInt(quotient.toConst());
    const r_idx = try intern_pool.internComptimeInt(remainder.toConst());
    assert(q_idx != .none);
    assert(r_idx != .none);
    return .{ .quotient = q_idx, .remainder = r_idx };
}
