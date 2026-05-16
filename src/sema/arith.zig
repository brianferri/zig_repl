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
    const workspace = try gpa.alloc(Limb, @max(lhs.limbs.len, rhs.limbs.len) + 1);
    defer gpa.free(workspace);

    var mutable: BigIntMutable = .{
        .limbs = workspace,
        .len = undefined,
        .positive = undefined,
    };
    mutable.add(lhs, rhs);
    return intern_pool.internComptimeInt(mutable.toConst());
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
    const workspace = try gpa.alloc(Limb, @max(lhs.limbs.len, rhs.limbs.len) + 1);
    defer gpa.free(workspace);

    var mutable: BigIntMutable = .{
        .limbs = workspace,
        .len = undefined,
        .positive = undefined,
    };
    mutable.sub(lhs, rhs);
    return intern_pool.internComptimeInt(mutable.toConst());
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
    const workspace = try gpa.alloc(Limb, lhs.limbs.len + rhs.limbs.len);
    defer gpa.free(workspace);

    var mutable: BigIntMutable = .{
        .limbs = workspace,
        .len = undefined,
        .positive = undefined,
    };
    mutable.mulNoAlias(lhs, rhs, gpa);
    return intern_pool.internComptimeInt(mutable.toConst());
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
    if (operand.eqlZero()) return intern_pool.internComptimeInt(operand);
    return intern_pool.internComptimeInt(operand.negate());
}
