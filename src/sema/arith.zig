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
    const stored = intern_pool.get(idx).int_value.value;
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

    const remainder = intern_pool.get(pair.remainder).int_value.value;
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

const DivKind = enum { trunc, floor };

const DivPair = struct {
    quotient: InternPool.Index,
    remainder: InternPool.Index,
};

/// Shared worker for all five division ops. Allocates one combined
/// workspace sized per the bounds documented on `BigIntMutable.divTrunc` /
/// `BigIntMutable.divFloor`: `q` up to `lhs.limbs.len`, `r` up to
/// `rhs.limbs.len`, plus the temp buffer from `calcDivLimbsBufferLen`.
/// Both quotient and remainder are interned even when only one is wanted —
/// the pool has no GC and the redundant slot is cheap compared to the
/// per-call alloc.
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
