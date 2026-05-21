//! Runtime-only port of the compiler's `analyzeBodyInner` (Sema.zig). Drops
//! every `Block.is_comptime` branch, all `ComptimeReason`/`branch_quota`
//! machinery, and the per-thread analysis-graph bookkeeping
//! (`pt`/`owner`/`func_index`). Replaces the compiler's AIR backend with
//! direct interpretation against the InternPool.
//!
//! Reference: src/Sema.zig in the Zig compiler tree.
//! Handler arms land per ZIR-tag group; until a tag is explicitly handled
//! it surfaces a deterministic `unsupported_zir_inst: <tag>` diagnostic.
//! There is no silent fallback.

const std = @import("std");
const assert = std.debug.assert;
const Allocator = std.mem.Allocator;
const Zir = std.zig.Zir;
const BigIntMutable = std.math.big.int.Mutable;
const Limb = std.math.big.Limb;

const InternPool = @import("InternPool.zig");
const Value = @import("Value.zig");
const arith = @import("arith.zig");
const InputShape = @import("../front/InputShape.zig");

const Sema = @This();

pub const Error = Allocator.Error || std.Io.Writer.Error || error{
    AnalysisFail,
};

gpa: Allocator,
intern_pool: *InternPool,
zir: Zir,
writer: *std.Io.Writer,
/// Per-instruction Value results within the body currently being walked.
/// Cleared between bodies; not shared across REPL inputs.
results: std.AutoHashMapUnmanaged(Zir.Inst.Index, Value),
/// Backing storage for `alloc` / `alloc_mut` / `alloc_comptime_mut`.
/// Each alloc reserves a fresh entry whose `value` starts as a typed
/// undef. `store_node` writes into the entry; `load` reads it back.
/// `Key.ptr { base_addr = .comptime_alloc = idx }` is the only
/// interned reference to the entry, so the table lifetime exactly
/// matches one body evaluation. Mirrors the compiler's
/// `Sema.comptime_allocs: std.ArrayList(ComptimeAlloc)` field
/// (`src/Sema.zig`); `is_const` lets `store_node` reject writes
/// through a const pointer with the same error vocabulary the
/// compiler uses ("cannot assign to constant").
comptime_allocs: std.ArrayListUnmanaged(ComptimeAlloc),
/// Current lookup scope. `null` for test paths that don't construct
/// a session; REPL passes the session-root index so `evalDeclVal`
/// can resolve cross-line names via the parent chain.
namespace: ?InternPool.NamespaceIndex,

pub const ComptimeAlloc = struct {
    ty: InternPool.Index,
    val: Value,
    is_const: bool,
};

/// Walks the ZIR produced by AstGen for a single REPL line.
///
/// Two control-flow modes depending on what AstGen produced:
///
///   1. The line was wrapped as `const __repl_input = (<expr>);`.
///      `findReplInputBody` locates that decl and evaluates its
///      body. The result is the Value returned to the REPL prompt.
///   2. The line is a raw declaration (`const x = ...;` etc.).
///      `bindDecls` walks every top-level decl in the root struct,
///      evaluates the value bodies, and binds them into the session
///      namespace via `createNav` + `pub_decls.put`. Returns `null`
///      because declarations don't produce a value-to-print.
///
/// `namespace` is the session-root NamespaceIndex (or `null` for
/// test paths without session state -- `evalDeclVal` errors and
/// `bindDecls` is a no-op in that mode).
pub fn analyze(
    gpa: Allocator,
    intern_pool: *InternPool,
    zir: Zir,
    writer: *std.Io.Writer,
    namespace: ?InternPool.NamespaceIndex,
) Error!?Value {
    // Zir may carry compile-error items that the front-end Pipeline
    // classifies as non-actionable (see `front/ZirErrors.zig`).
    // Pipeline gates Sema entry via `hasZirErrors`; Sema itself
    // walks only the `__repl_input` body (or the namespace
    // bindDecls path) and is unaffected by the suppressed items, so
    // the stronger `!hasCompileErrors()` assertion has been
    // intentionally relaxed.
    assert(@intFromPtr(intern_pool) != 0);
    assert(zir.instructions.len > 0);

    var sema: Sema = .{
        .gpa = gpa,
        .intern_pool = intern_pool,
        .zir = zir,
        .writer = writer,
        .results = .empty,
        .comptime_allocs = .empty,
        .namespace = namespace,
    };
    defer sema.results.deinit(gpa);
    defer sema.comptime_allocs.deinit(gpa);

    if (findReplInputBody(zir)) |body| {
        return try sema.evalBody(body);
    }
    if (namespace != null) try sema.bindDecls();
    return null;
}

fn findReplInputBody(zir: Zir) ?[]const Zir.Inst.Index {
    for (zir.typeDecls(.main_struct_inst)) |decl_inst| {
        const unwrapped = zir.getDeclaration(decl_inst);
        if (unwrapped.name == .empty) continue;
        const name = zir.nullTerminatedString(unwrapped.name);
        if (std.mem.eql(u8, name, InputShape.expression_decl_name)) {
            return unwrapped.value_body;
        }
    }
    return null;
}

fn evalBody(sema: *Sema, body: []const Zir.Inst.Index) Error!Value {
    assert(body.len > 0);

    const tags = sema.zir.instructions.items(.tag);
    const datas = sema.zir.instructions.items(.data);

    for (body) |inst| {
        const tag = tags[@intFromEnum(inst)];
        switch (tag) {
            .break_inline, .@"break" => {
                const operand = datas[@intFromEnum(inst)].@"break".operand;
                return sema.resolveRef(operand);
            },
            .condbr, .condbr_inline => return sema.evalCondbr(inst),
            else => {
                if (try sema.evalInst(inst, tag)) |result| {
                    try sema.results.put(sema.gpa, inst, result);
                }
            },
        }
    }
    try sema.writer.writeAll("internal error: body did not terminate with break\n");
    return error.AnalysisFail;
}

fn evalInst(sema: *Sema, inst: Zir.Inst.Index, tag: Zir.Inst.Tag) Error!?Value {
    return switch (tag) {
        .int => sema.evalInt(inst),
        .int_big => sema.evalIntBig(inst),
        .float => sema.evalFloat(inst),
        .float128 => sema.evalFloat128(inst),
        .add,
        .add_unsafe,
        .sub,
        .mul,
        .div,
        .div_exact,
        .div_floor,
        .div_trunc,
        .mod,
        .rem,
        .addwrap,
        .subwrap,
        .mulwrap,
        .add_sat,
        .sub_sat,
        .mul_sat,
        => sema.evalBinaryArith(inst, tag),
        .bit_and, .bit_or, .xor => sema.evalBitwise(inst, tag),
        .shl, .shr, .shl_exact, .shr_exact, .shl_sat => sema.evalShift(inst, tag),
        .typeof_log2_int_type => sema.evalTypeofLog2IntType(inst),
        .as_node, .as_shift_operand => sema.evalAsNode(inst),
        .float_cast => sema.evalFloatCast(inst),
        .int_from_float => sema.evalIntFromFloat(inst),
        .float_from_int => sema.evalFloatFromInt(inst),
        .int_cast => sema.evalIntCast(inst),
        .truncate => sema.evalTruncate(inst),
        .bitcast => sema.evalBitCast(inst),
        .bool_not => sema.evalBoolNot(inst),
        .bool_br_and => sema.evalBoolBr(inst, .bool_br_and),
        .bool_br_or => sema.evalBoolBr(inst, .bool_br_or),
        .block, .block_inline => sema.evalBlock(inst),
        .cmp_lt => sema.evalComparison(inst, .lt),
        .cmp_lte => sema.evalComparison(inst, .lte),
        .cmp_eq => sema.evalComparison(inst, .eq),
        .cmp_gte => sema.evalComparison(inst, .gte),
        .cmp_gt => sema.evalComparison(inst, .gt),
        .cmp_neq => sema.evalComparison(inst, .neq),
        .negate, .negate_wrap => sema.evalNegate(inst, tag),
        .bit_not => sema.evalBitNot(inst),
        .ptr_type => sema.evalPtrType(inst),
        .alloc => sema.evalAlloc(inst, true),
        .alloc_mut, .alloc_comptime_mut => sema.evalAlloc(inst, false),
        .store_node => sema.evalStoreNode(inst),
        .load => sema.evalLoad(inst),
        .decl_val => sema.evalDeclVal(inst),
        .error_set_decl => sema.evalErrorSetDecl(inst),
        .error_value => sema.evalErrorValue(inst),
        .error_union_type => sema.evalErrorUnionType(inst),
        .err_union_code => sema.evalErrUnionCode(inst),
        .err_union_payload_unsafe => sema.evalErrUnionPayloadUnsafe(inst),
        .is_non_err => sema.evalIsNonErr(inst),
        .dbg_stmt => null,
        .ensure_result_used, .ensure_result_non_error => sema.evalPassthroughUnNode(inst),
        inline else => |unhandled| sema.reportUnsupportedTag(unhandled),
    };
}

fn evalInt(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const value: u64 = sema.zir.instructions.items(.data)[@intFromEnum(inst)].int;

    var limbs_buf: [std.math.big.int.calcLimbLen(@as(u64, std.math.maxInt(u64)))]Limb = undefined;
    var mutable: BigIntMutable = .{
        .limbs = &limbs_buf,
        .len = undefined,
        .positive = undefined,
    };
    mutable.set(value);

    const idx = try sema.intern_pool.internComptimeInt(mutable.toConst());
    return .{ .index = idx };
}

/// Arbitrary-precision integer literal. AstGen stores raw limb bytes
/// inline in `zir.string_bytes`, with `data.str.len` measured in limbs
/// (not bytes). Always positive: AstGen lowers `-N` as
/// `negate(int_big N)`, so negative-magnitude encoding is unnecessary.
///
/// Known waste: `zir.string_bytes` is `[]u8` (alignment 1), so the limb
/// bytes inside it may land at any offset. `std.math.big.Limb` is
/// `usize` and needs `@alignOf(usize)` alignment to read safely
/// (misaligned reads are UB on stricter architectures and trip Zig's
/// safety checks). The fix would be aligning the limb runs in
/// `string_bytes` upstream so we could reinterpret in place -- neither
/// AstGen nor the compiler's Sema do this yet. Until that lands we eat
/// one `gpa.alloc` + `@memcpy` per `int_big` instruction. Worth
/// revisiting if `int_big` ever shows up in REPL profiling.
///
/// Compiler reference: src/Sema.zig:zirIntBig in the Zig compiler tree
/// (carries the same TODO).
fn evalIntBig(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromPtr(sema) != 0);
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const str = sema.zir.instructions.items(.data)[@intFromEnum(inst)].str;
    const limb_count: u32 = str.len;
    assert(limb_count > 0);

    const byte_count = limb_count * @sizeOf(std.math.big.Limb);
    const start: u32 = @intFromEnum(str.start);
    assert(start + byte_count <= sema.zir.string_bytes.len);

    const limb_bytes = sema.zir.string_bytes[start..][0..byte_count];

    const limbs = try sema.gpa.alloc(std.math.big.Limb, limb_count);
    defer sema.gpa.free(limbs);
    @memcpy(std.mem.sliceAsBytes(limbs), limb_bytes);

    const value: std.math.big.int.Const = .{ .limbs = limbs, .positive = true };
    const idx = try sema.intern_pool.internComptimeInt(value);
    assert(idx != .none);
    return .{ .index = idx };
}

/// f64-width float literal. AstGen stashes the value directly in the
/// instruction's `float` union field; we widen it to f128 here so the
/// stored Key matches the pool's invariant that `comptime_float_type`
/// always uses `.f128` storage. Mirrors the compiler's zirFloat.
fn evalFloat(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const value: f64 = sema.zir.instructions.items(.data)[@intFromEnum(inst)].float;
    const idx = try sema.intern_pool.internFloat(.{
        .ty = .comptime_float_type,
        .storage = .{ .f128 = @floatCast(value) },
    });
    assert(idx != .none);
    return .{ .index = idx };
}

/// f128-width float literal. AstGen stores the value as a 4-u32-piece
/// `Zir.Inst.Float128` payload referenced by `pl_node`. Mirrors the
/// compiler's zirFloat128.
fn evalFloat128(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    const payload = sema.zir.extraData(Zir.Inst.Float128, pl_node.payload_index).data;

    const idx = try sema.intern_pool.internFloat(.{
        .ty = .comptime_float_type,
        .storage = .{ .f128 = payload.get() },
    });
    assert(idx != .none);
    return .{ .index = idx };
}

fn evalPassthroughUnNode(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const operand = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node.operand;
    return try sema.resolveRef(operand);
}

/// Binary arith dispatcher (`add/sub/mul/div(_*)?/mod/rem`). Picks int
/// vs float kernels by operand type. When one operand is `comptime_int`
/// and the other is `comptime_float`, the int side is promoted via
/// `BigIntConst.toFloat(f128, .nearest_even)` -- peer-type resolution as
/// the compiler does for these specific types. Fixed-width arithmetic
/// and full peer-type resolution land with their coercion handlers.
///
/// Compiler reference: src/Sema.zig:zirArithmetic ->
/// src/Sema/arith.zig:{add,sub,mul,divTrunc,divFloor,mod,rem}.
fn evalBinaryArith(sema: *Sema, inst: Zir.Inst.Index, tag: Zir.Inst.Tag) Error!?Value {
    assert(@intFromPtr(sema) != 0);
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    const bin = sema.zir.extraData(Zir.Inst.Bin, pl_node.payload_index).data;
    assert(bin.lhs != .none);
    assert(bin.rhs != .none);

    const op_name: []const u8 = @tagName(tag);
    assert(op_name.len > 0);

    const ip = sema.intern_pool;
    const lhs_value = try sema.resolveRef(bin.lhs);
    const rhs_value = try sema.resolveRef(bin.rhs);
    const lhs_key = ip.indexToKey(lhs_value.index);
    const rhs_key = ip.indexToKey(rhs_value.index);

    if (resolveNumericPairToInt(ip, lhs_key, rhs_key)) |triple| {
        return sema.evalBinaryArithInt(tag, triple.lhs, triple.rhs, triple.ty);
    }

    if (coerceNumericPairToFloat(lhs_key, rhs_key)) |pair| {
        return sema.evalBinaryArithFloat(tag, pair[0], pair[1]);
    }

    if ((lhs_key == .int or lhs_key == .float) and (rhs_key == .int or rhs_key == .float)) {
        try sema.writer.print("{s}: incompatible numeric operands\n", .{op_name});
    } else {
        try sema.writer.print("{s}: non-numeric or mismatched operands\n", .{op_name});
    }
    return error.AnalysisFail;
}

/// Peer-type resolution for two int operands. Returns the common int
/// type plus both operand Keys (unchanged -- the kernel does the bignum
/// arithmetic and re-fits afterwards), or `null` if the pair isn't a
/// resolvable int-int combination (mixed signedness with no winner, a
/// non-`.int_type` fixed-width like `usize` or `c_int`, or a non-int
/// operand).
///
/// Common-type rules -- `src/Sema.zig` `resolvePeerTypesInner` for the
/// `.fixed_int` strategy:
///   * Both comptime_int -> comptime_int.
///   * comptime_int + fixed-width int -> the fixed-width int (the
///     comptime side is range-checked when the kernel re-fits).
///   * Both fixed-width int, same signedness -> the wider one.
///   * Both fixed-width int, mixed signedness -> the signed type
///     IFF its bits strictly exceed the unsigned type's bits; else no
///     common type (conflict).
fn resolveNumericPairToInt(
    pool: *const InternPool,
    lhs_key: InternPool.Key,
    rhs_key: InternPool.Key,
) ?struct { ty: InternPool.Index, lhs: InternPool.Key.Int, rhs: InternPool.Key.Int } {
    if (lhs_key != .int or rhs_key != .int) return null;
    const lhs_int = lhs_key.int;
    const rhs_int = rhs_key.int;

    const lhs_is_cti = lhs_int.ty == .comptime_int_type;
    const rhs_is_cti = rhs_int.ty == .comptime_int_type;
    const lhs_info: ?std.lang.Type.Int = if (lhs_is_cti) null else intTypeInfo(pool, lhs_int.ty);
    const rhs_info: ?std.lang.Type.Int = if (rhs_is_cti) null else intTypeInfo(pool, rhs_int.ty);

    // Bail on int types we don't yet support as a peer target (usize,
    // c_int, etc. -- separate target-aware axis).
    if (!lhs_is_cti and lhs_info == null) return null;
    if (!rhs_is_cti and rhs_info == null) return null;

    if (lhs_is_cti and rhs_is_cti) {
        return .{ .ty = .comptime_int_type, .lhs = lhs_int, .rhs = rhs_int };
    }
    if (lhs_is_cti) return .{ .ty = rhs_int.ty, .lhs = lhs_int, .rhs = rhs_int };
    if (rhs_is_cti) return .{ .ty = lhs_int.ty, .lhs = lhs_int, .rhs = rhs_int };

    const li = lhs_info.?;
    const ri = rhs_info.?;
    if (li.signedness == ri.signedness) {
        const wider_ty = if (li.bits >= ri.bits) lhs_int.ty else rhs_int.ty;
        return .{ .ty = wider_ty, .lhs = lhs_int, .rhs = rhs_int };
    }

    // Mixed signedness. Signed wins IFF its bits strictly exceed the
    // unsigned width. Otherwise we hit the compiler's legacy-compat
    // branch (`any_comptime_known` is always true for us, since every
    // value reaching here is comptime-known): wider unsigned wins, or
    // if signed_bits >= unsigned_bits, the earlier operand wins. Since
    // we don't track source order, we use lhs as the fallback --
    // matches the compiler in practice.
    const signed_ty = if (li.signedness == .signed) lhs_int.ty else rhs_int.ty;
    const signed_bits = if (li.signedness == .signed) li.bits else ri.bits;
    const unsigned_ty = if (li.signedness == .signed) rhs_int.ty else lhs_int.ty;
    const unsigned_bits = if (li.signedness == .signed) ri.bits else li.bits;
    if (signed_bits > unsigned_bits) {
        return .{ .ty = signed_ty, .lhs = lhs_int, .rhs = rhs_int };
    }
    if (unsigned_bits > signed_bits) {
        return .{ .ty = unsigned_ty, .lhs = lhs_int, .rhs = rhs_int };
    }
    return .{ .ty = lhs_int.ty, .lhs = lhs_int, .rhs = rhs_int };
}

/// Pull `(signedness, bits)` for any Zig int type Index. Covers
/// `int_type` (uN/iN), `comptime_int`-rejected (returns null -- peer
/// resolution treats it separately), and the target-conditioned
/// family (`usize`, `isize`, `c_char` ... `c_ulonglong`) whose widths
/// come from `@typeInfo(T).int` against the host.
fn intTypeInfo(pool: *const InternPool, ty: InternPool.Index) ?std.lang.Type.Int {
    return switch (ty) {
        .usize_type => @typeInfo(usize).int,
        .isize_type => @typeInfo(isize).int,
        .c_char_type => @typeInfo(c_char).int,
        .c_short_type => @typeInfo(c_short).int,
        .c_ushort_type => @typeInfo(c_ushort).int,
        .c_int_type => @typeInfo(c_int).int,
        .c_uint_type => @typeInfo(c_uint).int,
        .c_long_type => @typeInfo(c_long).int,
        .c_ulong_type => @typeInfo(c_ulong).int,
        .c_longlong_type => @typeInfo(c_longlong).int,
        .c_ulonglong_type => @typeInfo(c_ulonglong).int,
        .comptime_int_type => null,
        else => switch (pool.indexToKey(ty)) {
            .int_type => |it| it,
            else => null,
        },
    };
}

/// Peer-type resolution for numeric operands when at least one side is
/// a float. Returns the two operands coerced to a common float type, or
/// `null` when the pair has no valid common float type (the dispatcher
/// then diagnoses; pairs the int-arith arm would handle also return
/// null here).
///
/// Common-type rules -- matched against the compiler's `resolvePeerTypes`
/// strategy lattice for the int/float subset:
///   * Both sides fixed-width float -> the wider one
///     (`f32 + f64` -> f64, etc.)
///   * Exactly one side is fixed-width float -> that fixed-width float.
///     Any int operand (comptime_int OR fixed-width int) coerces into it
///     via `BigIntConst.toFloat(f128, .nearest_even)` then narrowing.
///   * Otherwise, at least one side must be comptime_float -> common is
///     comptime_float. Fixed-width int operands are rejected here
///     (matches Zig: `@as(i32, 5) + 1.5` is "incompatible types").
fn coerceNumericPairToFloat(
    lhs_key: InternPool.Key,
    rhs_key: InternPool.Key,
) ?[2]InternPool.Key.Float {
    const lhs_fw: ?InternPool.Index = fixedWidthFloatType(lhs_key);
    const rhs_fw: ?InternPool.Index = fixedWidthFloatType(rhs_key);

    if (lhs_fw != null and rhs_fw != null) {
        const target = widerFloatType(lhs_fw.?, rhs_fw.?);
        return .{
            coerceToTargetFloat(lhs_key, target) orelse return null,
            coerceToTargetFloat(rhs_key, target) orelse return null,
        };
    }
    if (lhs_fw orelse rhs_fw) |target| {
        return .{
            coerceToTargetFloat(lhs_key, target) orelse return null,
            coerceToTargetFloat(rhs_key, target) orelse return null,
        };
    }

    const lhs_is_ctf = lhs_key == .float and lhs_key.float.ty == .comptime_float_type;
    const rhs_is_ctf = rhs_key == .float and rhs_key.float.ty == .comptime_float_type;
    if (!lhs_is_ctf and !rhs_is_ctf) return null;
    return .{
        coerceToTargetFloat(lhs_key, .comptime_float_type) orelse return null,
        coerceToTargetFloat(rhs_key, .comptime_float_type) orelse return null,
    };
}

fn fixedWidthFloatType(key: InternPool.Key) ?InternPool.Index {
    if (key != .float) return null;
    if (!isFixedWidthFloatType(key.float.ty)) return null;
    return key.float.ty;
}

fn widerFloatType(a: InternPool.Index, b: InternPool.Index) InternPool.Index {
    return if (floatTypeBits(a) >= floatTypeBits(b)) a else b;
}

fn floatTypeBits(ty: InternPool.Index) u16 {
    return switch (ty) {
        .f16_type => 16,
        .f32_type => 32,
        .f64_type => 64,
        .f80_type => 80,
        .f128_type => 128,
        else => unreachable,
    };
}

/// Coerce a numeric Key to a `Key.Float` at `target_ty`, or `null` if
/// the coercion is invalid for that target. The only invalid combo is
/// fixed-width int operand with comptime_float target -- Zig requires
/// an explicit cast there.
fn coerceToTargetFloat(
    key: InternPool.Key,
    target_ty: InternPool.Index,
) ?InternPool.Key.Float {
    return switch (key) {
        .float => coerceNumericToFloat(key, target_ty),
        .int => |int| blk: {
            if (target_ty == .comptime_float_type and int.ty != .comptime_int_type) break :blk null;
            break :blk coerceNumericToFloat(key, target_ty);
        },
        else => null,
    };
}

/// Widen a numeric Key (any int or any float) to f128, then narrow to
/// the storage variant for `target_ty`. Uses `BigIntConst.toFloat(f128,
/// .nearest_even)` for ints (IEEE-754 default) -- the same helper the
/// compiler's `Value.toFloat` calls. Callers must have ensured the
/// coercion is valid (see `coerceToTargetFloat`).
fn coerceNumericToFloat(
    key: InternPool.Key,
    target_ty: InternPool.Index,
) InternPool.Key.Float {
    assert(isFloatTypeIndex(target_ty));
    const widened: f128 = switch (key) {
        .float => |float| floatToF128(float),
        .int => |int| blk: {
            var space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
            const big = int.storage.toBigInt(&space);
            const rounded = big.toFloat(f128, .nearest_even);
            break :blk rounded[0];
        },
        else => unreachable,
    };
    return .{ .ty = target_ty, .storage = narrowF128ToFloatStorage(widened, target_ty) };
}

/// Int binary arith. The bignum kernel computes an exact comptime_int
/// result; if `dest_ty` is a fixed-width int, we then range-check via
/// `fitsInTwosComp` (matching the compiler's comptime overflow error)
/// and re-intern at the destination type.
fn evalBinaryArithInt(
    sema: *Sema,
    tag: Zir.Inst.Tag,
    lhs_int: InternPool.Key.Int,
    rhs_int: InternPool.Key.Int,
    dest_ty: InternPool.Index,
) Error!?Value {
    var lhs_space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
    var rhs_space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
    const lhs = lhs_int.storage.toBigInt(&lhs_space);
    const rhs = rhs_int.storage.toBigInt(&rhs_space);

    const ip = sema.intern_pool;
    const gpa = sema.gpa;

    // Wrap / sat tags carry destination-width semantics in stdlib's
    // `BigIntMutable.addWrap` family. For comptime_int destinations the
    // wrap/sat tags fall back to regular arith (matches `zig run`:
    // `200 +% 100` on two comptime_int operands is 300, not 44).
    const dest_info = intTypeInfo(ip, dest_ty);
    if (dest_info) |info| {
        if (wrapSatKernel(tag)) |kind| {
            return try sema.runIntWrapSat(kind, lhs, rhs, dest_ty, info);
        }
    }

    const tmp_idx = switch (tag) {
        .add, .add_unsafe => try arith.internAdd(gpa, ip, lhs, rhs),
        .sub => try arith.internSub(gpa, ip, lhs, rhs),
        .mul => try arith.internMul(gpa, ip, lhs, rhs),
        .addwrap, .add_sat => try arith.internAdd(gpa, ip, lhs, rhs),
        .subwrap, .sub_sat => try arith.internSub(gpa, ip, lhs, rhs),
        .mulwrap, .mul_sat => try arith.internMul(gpa, ip, lhs, rhs),
        .div, .div_trunc => try sema.unwrapDivResult(arith.internDivTrunc(gpa, ip, lhs, rhs), "/"),
        .div_exact => try sema.unwrapDivResult(arith.internDivExact(gpa, ip, lhs, rhs), "@divExact"),
        .div_floor => try sema.unwrapDivResult(arith.internDivFloor(gpa, ip, lhs, rhs), "@divFloor"),
        .mod => try sema.unwrapDivResult(arith.internMod(gpa, ip, lhs, rhs), "@mod"),
        .rem => try sema.unwrapDivResult(arith.internRem(gpa, ip, lhs, rhs), "@rem"),
        else => unreachable,
    };

    if (dest_ty == .comptime_int_type) return .{ .index = tmp_idx };
    return try sema.refitIntToFixedWidth(tmp_idx, dest_ty, @tagName(tag));
}

const WrapSatKind = enum {
    add_wrap,
    sub_wrap,
    mul_wrap,
    add_sat,
    sub_sat,
    mul_sat,
};

fn wrapSatKernel(tag: Zir.Inst.Tag) ?WrapSatKind {
    return switch (tag) {
        .addwrap => .add_wrap,
        .subwrap => .sub_wrap,
        .mulwrap => .mul_wrap,
        .add_sat => .add_sat,
        .sub_sat => .sub_sat,
        .mul_sat => .mul_sat,
        else => null,
    };
}

/// Run a wrap or saturating int kernel via stdlib's
/// `BigIntMutable.{addWrap, addSat, subWrap, subSat, mulWrap, mulSat}`.
/// The `mul_sat` case has no direct stdlib helper, so we mul first and
/// then `saturate` to the destination range.
fn runIntWrapSat(
    sema: *Sema,
    kind: WrapSatKind,
    lhs: std.math.big.int.Const,
    rhs: std.math.big.int.Const,
    dest_ty: InternPool.Index,
    dest_info: std.lang.Type.Int,
) Error!?Value {
    const limb_bits: usize = @bitSizeOf(std.math.big.Limb);
    // Worst-case `mul` output is `lhs.limbs.len + rhs.limbs.len`; add /
    // sub need `max + 1`. One worst-case buffer fits everything plus
    // one cushion limb for `saturate` to write its sentinel.
    const max_op_limbs = @max(lhs.limbs.len + rhs.limbs.len, @max(lhs.limbs.len, rhs.limbs.len) + 1);
    const dest_limbs = (@as(usize, dest_info.bits) + limb_bits - 1) / limb_bits + 1;
    const workspace = try sema.gpa.alloc(std.math.big.Limb, @max(max_op_limbs, dest_limbs));
    defer sema.gpa.free(workspace);

    var mutable: std.math.big.int.Mutable = .{
        .limbs = workspace,
        .len = undefined,
        .positive = undefined,
    };
    switch (kind) {
        .add_wrap => _ = mutable.addWrap(lhs, rhs, dest_info.signedness, dest_info.bits),
        .sub_wrap => _ = mutable.subWrap(lhs, rhs, dest_info.signedness, dest_info.bits),
        // Workspace is gpa-allocated; lhs/rhs live in the pool's arena,
        // so mulWrapNoAlias's no-alias precondition holds and the
        // separate temp buffer mulWrap would need is unnecessary.
        .mul_wrap => mutable.mulWrapNoAlias(lhs, rhs, dest_info.signedness, dest_info.bits, sema.gpa),
        .add_sat => mutable.addSat(lhs, rhs, dest_info.signedness, dest_info.bits),
        .sub_sat => mutable.subSat(lhs, rhs, dest_info.signedness, dest_info.bits),
        .mul_sat => {
            mutable.mulNoAlias(lhs, rhs, sema.gpa);
            const product = mutable.toConst();
            mutable.saturate(product, dest_info.signedness, dest_info.bits);
        },
    }
    const idx = try sema.intern_pool.internIntValue(dest_ty, mutable.toConst());
    return .{ .index = idx };
}

/// Re-intern a comptime_int result at the given fixed-width int type,
/// erroring if the value doesn't fit. Used by every fixed-width int
/// path (binary arith and the matching coercion in `@as`).
fn refitIntToFixedWidth(
    sema: *Sema,
    comptime_int_idx: InternPool.Index,
    dest_ty: InternPool.Index,
    op_name: []const u8,
) Error!Value {
    const dest_info = intTypeInfo(sema.intern_pool, dest_ty) orelse {
        try sema.writer.print("{s}: destination is not a supported int type\n", .{op_name});
        return error.AnalysisFail;
    };
    var space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
    const result_big = sema.intern_pool.indexToKey(comptime_int_idx).int.storage.toBigInt(&space);
    if (!result_big.fitsInTwosComp(dest_info.signedness, dest_info.bits)) {
        try sema.writer.print(
            "{s}: value does not fit in {c}{d}\n",
            .{ op_name, @as(u8, switch (dest_info.signedness) {
                .signed => 'i',
                .unsigned => 'u',
            }), dest_info.bits },
        );
        return error.AnalysisFail;
    }
    const idx = try sema.intern_pool.internIntValue(dest_ty, result_big);
    return .{ .index = idx };
}

/// Float binary arith for any width. The `inline else` switch on storage
/// instantiates the math in the operand's native float type (f16 .. f128),
/// so the same body covers comptime_float (always f128) and all the
/// fixed-width variants. Storage variants are guaranteed to match because
/// `ty` matches and the pool stores each ty as its corresponding variant.
fn evalBinaryArithFloat(
    sema: *Sema,
    tag: Zir.Inst.Tag,
    lhs_float: InternPool.Key.Float,
    rhs_float: InternPool.Key.Float,
) Error!?Value {
    assert(lhs_float.ty == rhs_float.ty);

    const StorageTag = @typeInfo(InternPool.Key.Float.Storage).@"union".tag_type.?;
    assert(@as(StorageTag, lhs_float.storage) == @as(StorageTag, rhs_float.storage));

    const ip = sema.intern_pool;
    switch (lhs_float.storage) {
        inline else => |lhs_v, storage_tag| {
            const FloatT = @TypeOf(lhs_v);
            const rhs_v = @field(rhs_float.storage, @tagName(storage_tag));
            const result: FloatT = try sema.computeFloatBin(FloatT, tag, lhs_v, rhs_v);
            const out_storage = @unionInit(InternPool.Key.Float.Storage, @tagName(storage_tag), result);
            const idx = try ip.internFloat(.{ .ty = lhs_float.ty, .storage = out_storage });
            return .{ .index = idx };
        },
    }
}

/// Compute the float result for a binary arith tag at a specific width.
/// Division-family ops share a single zero-check; `@divExact` adds a
/// remainder check. Diagnostics are written directly so the caller can
/// just propagate `AnalysisFail` via `try`.
fn computeFloatBin(
    sema: *Sema,
    comptime FloatT: type,
    tag: Zir.Inst.Tag,
    lhs: FloatT,
    rhs: FloatT,
) Error!FloatT {
    switch (tag) {
        .add => return lhs + rhs,
        .sub => return lhs - rhs,
        .mul => return lhs * rhs,
        else => {},
    }
    if (rhs == 0) {
        try sema.writer.print("error: {s}: division by zero\n", .{floatDivOpName(tag)});
        return error.AnalysisFail;
    }
    return switch (tag) {
        .div => lhs / rhs,
        .div_trunc => @divTrunc(lhs, rhs),
        .div_floor => @divFloor(lhs, rhs),
        .div_exact => blk: {
            if (@rem(lhs, rhs) != 0) {
                try sema.writer.print("error: @divExact: remainder is non-zero\n", .{});
                return error.AnalysisFail;
            }
            break :blk lhs / rhs;
        },
        .mod => @mod(lhs, rhs),
        .rem => @rem(lhs, rhs),
        else => unreachable,
    };
}

fn floatDivOpName(tag: Zir.Inst.Tag) []const u8 {
    return switch (tag) {
        .div => "/",
        .div_trunc => "@divTrunc",
        .div_floor => "@divFloor",
        .div_exact => "@divExact",
        .mod => "@mod",
        .rem => "@rem",
        else => unreachable,
    };
}

/// Translate an arith.DivError into either a successful Index or a written
/// runtime-style diagnostic + AnalysisFail.
fn unwrapDivResult(
    sema: *Sema,
    result: arith.DivError!InternPool.Index,
    op_name: []const u8,
) Error!InternPool.Index {
    assert(@intFromPtr(sema) != 0);
    assert(op_name.len > 0);

    const idx = result catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        error.DivisionByZero => {
            try sema.writer.print("error: {s}: division by zero\n", .{op_name});
            return error.AnalysisFail;
        },
        error.DivisionNotExact => {
            try sema.writer.print("error: {s}: remainder is non-zero\n", .{op_name});
            return error.AnalysisFail;
        },
    };
    assert(idx != .none);
    return idx;
}

const ShiftKernel = *const fn (
    std.mem.Allocator,
    *InternPool,
    std.math.big.int.Const,
    std.math.big.int.Const,
) arith.ShiftError!InternPool.Index;

/// `block` / `block_inline`: evaluate an inner ZIR body and yield the value
/// it breaks with. Sema's existing `evalBody` already does this -- `block`
/// here is just an `evalInst` arm that exposes the inner body's break
/// value as the instruction's own result.
///
/// Each `evalBody` call corresponds to one block scope; `break_inline`
/// inside the inner body terminates *that* call and returns the value
/// here. Labeled multi-level breaks need a return-signal mechanism we
/// haven't built yet; the single-target case suffices for `if`-as-value
/// and the bodies AstGen emits around comparison/shift sequences.
///
/// Compiler reference: src/Sema.zig:zirBlock / zirBlockInline.
fn evalBlock(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromPtr(sema) != 0);
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.Block, pl_node.payload_index);
    const body = sema.zir.bodySlice(extra.end, extra.data.body_len);
    return try sema.evalBody(body);
}

/// `condbr` / `condbr_inline`: resolve a bool condition, pick the then or
/// else body, recursively evalBody on the chosen one. The picked body
/// terminates with `break_inline` to its enclosing block, which exits the
/// recursive `evalBody` call here. Treated as a terminator by the outer
/// `evalBody` because it always transfers control -- never falls through.
///
/// Compiler reference: src/Sema.zig:zirCondbr.
fn evalCondbr(sema: *Sema, inst: Zir.Inst.Index) Error!Value {
    assert(@intFromPtr(sema) != 0);
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.CondBr, pl_node.payload_index);
    const condbr = extra.data;
    assert(condbr.condition != .none);

    const cond_value = try sema.resolveRef(condbr.condition);
    const cond_is_true = switch (cond_value.index) {
        .bool_true => true,
        .bool_false => false,
        else => {
            try sema.writer.writeAll("condbr: condition is not a bool\n");
            return error.AnalysisFail;
        },
    };

    const then_body_start = extra.end;
    const else_body_start = then_body_start + condbr.then_body_len;
    const body = if (cond_is_true)
        sema.zir.bodySlice(then_body_start, condbr.then_body_len)
    else
        sema.zir.bodySlice(else_body_start, condbr.else_body_len);

    return try sema.evalBody(body);
}

/// `!operand` (bool_not). Operand must be one of the two well-known bool
/// indices; we map directly to the opposite without going through Sema
/// type machinery.
fn evalBoolNot(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromPtr(sema) != 0);
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    assert(un_node.operand != .none);

    const operand = try sema.resolveRef(un_node.operand);
    return switch (operand.index) {
        .bool_true => .{ .index = .bool_false },
        .bool_false => .{ .index = .bool_true },
        else => {
            try sema.writer.writeAll("bool_not: operand is not a bool\n");
            return error.AnalysisFail;
        },
    };
}

/// Short-circuiting `and` / `or`. `lhs` is a bool Ref; the rhs is a ZIR
/// body the compiler emits to evaluate the right operand only when the
/// short-circuit doesn't fire. First nested-body path in Sema -- the body
/// is just a sub-sequence of `Zir.Inst.Index` and `evalBody` already does
/// the right thing. `tag` distinguishes the two variants directly via
/// `Zir.Inst.Tag` rather than a parallel local enum.
///
/// Compiler reference: src/Sema.zig:zirBoolBr.
fn evalBoolBr(sema: *Sema, inst: Zir.Inst.Index, tag: Zir.Inst.Tag) Error!?Value {
    assert(@intFromPtr(sema) != 0);
    assert(@intFromEnum(inst) < sema.zir.instructions.len);
    assert(tag == .bool_br_and or tag == .bool_br_or);

    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.BoolBr, pl_node.payload_index);
    const bool_br = extra.data;
    assert(bool_br.lhs != .none);

    const lhs_value = try sema.resolveRef(bool_br.lhs);
    const lhs_is_true = switch (lhs_value.index) {
        .bool_true => true,
        .bool_false => false,
        else => {
            try sema.writer.writeAll("bool_br: lhs is not a bool\n");
            return error.AnalysisFail;
        },
    };

    const short_circuited = switch (tag) {
        .bool_br_and => !lhs_is_true, // false and X -> false
        .bool_br_or => lhs_is_true, // true  or  X -> true
        else => unreachable,
    };
    if (short_circuited) return lhs_value;

    const body = sema.zir.bodySlice(extra.end, bool_br.body_len);
    return try sema.evalBody(body);
}

/// `typeof_log2_int_type`: returns the type whose values are valid as the
/// right-hand operand of `lhs << rhs` / `lhs >> rhs`. For `comptime_int`
/// operands this is `comptime_int` itself (the compiler's behavior); for
/// fixed-width int operands it is `unsigned(log2_ceil(bits))`.
///
/// Compiler reference: src/Sema.zig:zirTypeofLog2IntType -> log2IntType.
fn evalTypeofLog2IntType(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromPtr(sema) != 0);
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    assert(un_node.operand != .none);

    const operand = try sema.resolveRef(un_node.operand);
    const operand_type = Value.typeOf(operand, sema.intern_pool);

    if (operand_type.index == .comptime_int_type) {
        const idx = try sema.intern_pool.internTypeValue(.comptime_int_type);
        return .{ .index = idx };
    }

    const operand_type_key = sema.intern_pool.indexToKey(operand_type.index);
    if (operand_type_key == .int_type) {
        const bits = operand_type_key.int_type.bits;
        const log2_bits: u16 = if (bits == 0) 0 else std.math.log2_int_ceil(u16, bits);
        const log2_type = try sema.intern_pool.internIntType(.unsigned, log2_bits);
        const idx = try sema.intern_pool.internTypeValue(log2_type);
        return .{ .index = idx };
    }

    try sema.writer.writeAll("typeof_log2_int_type: non-integer operand not yet supported\n");
    return error.AnalysisFail;
}

/// `as_node` / `as_shift_operand`: coerce `operand` to `dest_type`.
/// Currently supported:
///   * identity (operand type == dest type) -- free passthrough.
///   * comptime_int -> any fixed-width int: range-checked via stdlib's
///     `BigIntConst.fitsInTwosComp`; failure raises a runtime-style
///     "value does not fit" diagnostic and returns AnalysisFail.
/// Other coercions (int widening / narrowing between fixed widths,
/// float, optional, error union, pointer) land alongside their
/// respective handlers.
///
/// Compiler reference: src/Sema.zig:zirAsNode -> analyzeAs.
fn evalAsNode(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromPtr(sema) != 0);
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    const as = sema.zir.extraData(Zir.Inst.As, pl_node.payload_index).data;
    assert(as.dest_type != .none);
    assert(as.operand != .none);

    const dest_type_index = try sema.resolveDestType(as.dest_type, "as");

    const operand_value = try sema.resolveRef(as.operand);
    return try sema.coerceValueToType(operand_value, dest_type_index, "@as");
}

/// Resolve a `Zir.Inst.Ref` that should identify a type. Accepts both
/// shapes the pool uses to represent "this value names a type":
///
///   * A `type_value` Key wrapping the target Index (the dynamic case
///     for synthesized types).
///   * A bare type Key whose own Index is the type slot --
///     `simple_type` / `int_type` / `ptr_type` / `anyframe_type`. Per
///     `Value.typeOf`, these surface a value of type `type`, so the
///     Index itself doubles as the type identifier.
///
/// Used by every cast builtin (`@as` / `@floatCast` / `@intCast` /
/// `@truncate` / `@bitCast` / `@intFromFloat` / `@floatFromInt`) to
/// unpack the destination-type operand into a single Index.
fn resolveDestType(
    sema: *Sema,
    ref: Zir.Inst.Ref,
    op_name: []const u8,
) Error!InternPool.Index {
    assert(ref != .none);
    const dest_value = try sema.resolveRef(ref);
    return switch (sema.intern_pool.indexToKey(dest_value.index)) {
        .type_value => |t| t,
        .simple_type,
        .int_type,
        .ptr_type,
        .anyframe_type,
        .error_set_type,
        .error_union_type,
        => dest_value.index,
        else => blk: {
            try sema.writer.print("{s}: destination is not a type\n", .{op_name});
            break :blk error.AnalysisFail;
        },
    };
}

/// `@floatCast(DestType, x)`: float-to-float width cast (widening or
/// narrowing). All widths are accepted; narrowing loses precision but
/// never errors. The pool's storage variant is selected by `DestType`.
///
/// Compiler reference: src/Sema.zig:zirFloatCast.
fn evalFloatCast(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    const bin = sema.zir.extraData(Zir.Inst.Bin, pl_node.payload_index).data;
    assert(bin.lhs != .none);
    assert(bin.rhs != .none);

    const dest_type_index = try sema.resolveDestType(bin.lhs, "@floatCast");
    if (!isFloatTypeIndex(dest_type_index)) {
        try sema.writer.writeAll("@floatCast: destination is not a float type\n");
        return error.AnalysisFail;
    }

    const operand_value = try sema.resolveRef(bin.rhs);
    const operand_key = sema.intern_pool.indexToKey(operand_value.index);
    if (operand_key != .float) {
        try sema.writer.writeAll("@floatCast: operand is not a float\n");
        return error.AnalysisFail;
    }
    const coerced = coerceNumericToFloat(operand_key, dest_type_index);
    const idx = try sema.intern_pool.internFloat(coerced);
    return .{ .index = idx };
}

/// `@intFromFloat(DestType, x)`: truncate `x` toward zero and re-tag as
/// `DestType`. NaN and infinities are rejected (the compiler does the
/// same at comptime). Fixed-width destinations get range-checked via
/// `BigIntConst.fitsInTwosComp`; `comptime_int` accepts anything finite.
///
/// Compiler reference: src/Sema.zig:zirIntFromFloat.
fn evalIntFromFloat(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    const bin = sema.zir.extraData(Zir.Inst.Bin, pl_node.payload_index).data;
    assert(bin.lhs != .none);
    assert(bin.rhs != .none);

    const dest_type_index = try sema.resolveDestType(bin.lhs, "@intFromFloat");

    const operand_value = try sema.resolveRef(bin.rhs);
    const operand_key = sema.intern_pool.indexToKey(operand_value.index);
    if (operand_key != .float) {
        try sema.writer.writeAll("@intFromFloat: operand is not a float\n");
        return error.AnalysisFail;
    }
    const operand_f128: f128 = floatToF128(operand_key.float);
    if (std.math.isNan(operand_f128)) {
        try sema.writer.writeAll("@intFromFloat: operand is NaN\n");
        return error.AnalysisFail;
    }
    if (!std.math.isFinite(operand_f128)) {
        try sema.writer.writeAll("@intFromFloat: operand is infinite\n");
        return error.AnalysisFail;
    }

    return try sema.materialiseIntFromFloat(operand_f128, dest_type_index);
}

/// Truncate a finite f128 toward zero and intern the result at the
/// requested destination type. `BigIntMutable.setFloat(.trunc)` writes
/// the integer part; `std.math.big.int.calcLimbLen` sizes the buffer to
/// exactly what this specific value needs (1-2 limbs for normal-sized
/// values, up to ~257 only for f128 near the max exponent -- matching
/// the compiler's `intFromFloatScalar`).
fn materialiseIntFromFloat(
    sema: *Sema,
    operand: f128,
    dest_type_index: InternPool.Index,
) Error!Value {
    const limbs = try sema.gpa.alloc(std.math.big.Limb, std.math.big.int.calcLimbLen(operand));
    defer sema.gpa.free(limbs);

    var mutable: std.math.big.int.Mutable = .{
        .limbs = limbs,
        .len = undefined,
        .positive = undefined,
    };
    _ = mutable.setFloat(operand, .trunc);
    const big = mutable.toConst();

    const dest_key = sema.intern_pool.indexToKey(dest_type_index);
    if (dest_key == .simple_type and dest_key.simple_type == .comptime_int) {
        const idx = try sema.intern_pool.internComptimeInt(big);
        return .{ .index = idx };
    }
    if (dest_key == .int_type) {
        const dest_int = dest_key.int_type;
        if (!big.fitsInTwosComp(dest_int.signedness, dest_int.bits)) {
            try sema.writer.print(
                "@intFromFloat: value does not fit in {c}{d}\n",
                .{ @as(u8, switch (dest_int.signedness) {
                    .signed => 'i',
                    .unsigned => 'u',
                }), dest_int.bits },
            );
            return error.AnalysisFail;
        }
        const idx = try sema.intern_pool.internIntValue(dest_type_index, big);
        return .{ .index = idx };
    }

    try sema.writer.writeAll("@intFromFloat: destination is not an int type\n");
    return error.AnalysisFail;
}

/// `@floatFromInt(DestType, x)`: integer-to-float conversion. The int is
/// rounded to nearest-even (IEEE-754 default) at the destination width.
/// Operands of any int type are accepted -- including comptime_int with
/// arbitrary magnitude -- because `BigIntConst.toFloat` handles the
/// rounding.
///
/// Compiler reference: src/Sema.zig:zirFloatFromInt.
fn evalFloatFromInt(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    const bin = sema.zir.extraData(Zir.Inst.Bin, pl_node.payload_index).data;
    assert(bin.lhs != .none);
    assert(bin.rhs != .none);

    const dest_type_index = try sema.resolveDestType(bin.lhs, "@floatFromInt");
    if (!isFloatTypeIndex(dest_type_index)) {
        try sema.writer.writeAll("@floatFromInt: destination is not a float type\n");
        return error.AnalysisFail;
    }

    const operand_value = try sema.resolveRef(bin.rhs);
    const operand_key = sema.intern_pool.indexToKey(operand_value.index);
    if (operand_key != .int) {
        try sema.writer.writeAll("@floatFromInt: operand is not an int\n");
        return error.AnalysisFail;
    }
    // `coerceNumericToFloat` accepts any int via the same widen+narrow
    // pipeline (rounding is f128 nearest-even, IEEE-754 default).
    const coerced = coerceNumericToFloat(operand_key, dest_type_index);
    const idx = try sema.intern_pool.internFloat(coerced);
    return .{ .index = idx };
}

/// `@intCast(x)`: cast int to int with range check. Destination type
/// from result-location; ZIR-side same `pl_node + Bin` shape as the
/// other casts.
///
/// Compiler reference: src/Sema.zig:zirIntCast.
fn evalIntCast(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    const bin = sema.zir.extraData(Zir.Inst.Bin, pl_node.payload_index).data;

    const dest_type_index = try sema.resolveDestType(bin.lhs, "@intCast");
    const operand_value = try sema.resolveRef(bin.rhs);
    const operand_key = sema.intern_pool.indexToKey(operand_value.index);
    if (operand_key != .int) {
        try sema.writer.writeAll("@intCast: operand is not an int\n");
        return error.AnalysisFail;
    }
    // comptime_int destination is identity at comptime.
    if (dest_type_index == .comptime_int_type) return operand_value;
    return try sema.refitIntToFixedWidth(operand_value.index, dest_type_index, "@intCast");
}

/// `@truncate(x)`: take low bits of operand, ignoring high. Destination
/// type must be an int strictly narrower than (or equal to) the source.
/// Uses stdlib's `BigIntMutable.truncate` for two's-complement
/// reduction.
///
/// Compiler reference: src/Sema.zig:zirTruncate.
fn evalTruncate(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    const bin = sema.zir.extraData(Zir.Inst.Bin, pl_node.payload_index).data;

    const dest_type_index = try sema.resolveDestType(bin.lhs, "@truncate");
    const dest_info = intTypeInfo(sema.intern_pool, dest_type_index) orelse {
        try sema.writer.writeAll("@truncate: destination is not a fixed-width int\n");
        return error.AnalysisFail;
    };

    const operand_value = try sema.resolveRef(bin.rhs);
    const operand_key = sema.intern_pool.indexToKey(operand_value.index);
    if (operand_key != .int) {
        try sema.writer.writeAll("@truncate: operand is not an int\n");
        return error.AnalysisFail;
    }

    var space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
    const operand_big = operand_key.int.storage.toBigInt(&space);

    const limb_bits: usize = @bitSizeOf(std.math.big.Limb);
    const workspace_limbs: usize = (@as(usize, dest_info.bits) + limb_bits - 1) / limb_bits + 1;
    const workspace = try sema.gpa.alloc(std.math.big.Limb, workspace_limbs);
    defer sema.gpa.free(workspace);

    var mutable: std.math.big.int.Mutable = .{
        .limbs = workspace,
        .len = undefined,
        .positive = undefined,
    };
    mutable.truncate(operand_big, dest_info.signedness, dest_info.bits);
    const idx = try sema.intern_pool.internIntValue(dest_type_index, mutable.toConst());
    return .{ .index = idx };
}

/// `@bitCast(x)`: reinterpret operand's bit pattern as another type of
/// the same size. We cover the numeric cases the REPL actually hits:
/// fixed-width int <-> fixed-width float of matching bit width.
///
/// Compiler reference: src/Sema.zig:zirBitCast.
fn evalBitCast(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    const bin = sema.zir.extraData(Zir.Inst.Bin, pl_node.payload_index).data;

    const dest_type_index = try sema.resolveDestType(bin.lhs, "@bitCast");
    const operand_value = try sema.resolveRef(bin.rhs);
    const operand_type = Value.typeOf(operand_value, sema.intern_pool);
    if (dest_type_index == operand_type.index) return operand_value;

    const operand_key = sema.intern_pool.indexToKey(operand_value.index);
    const operand_bits = numericBitSize(sema.intern_pool, operand_type.index);
    const dest_bits = numericBitSize(sema.intern_pool, dest_type_index);
    if (operand_bits == null or dest_bits == null) {
        try sema.writer.writeAll("@bitCast: operands must be fixed-width numeric types\n");
        return error.AnalysisFail;
    }
    if (operand_bits.? != dest_bits.?) {
        try sema.writer.print(
            "@bitCast: type sizes differ ({d} vs {d} bits)\n",
            .{ operand_bits.?, dest_bits.? },
        );
        return error.AnalysisFail;
    }

    return try sema.reinterpretBitCast(operand_key, dest_type_index, dest_bits.?);
}

/// Bit-width of a fixed-width numeric type, or `null` for comptime /
/// target-conditioned types we don't handle in `@bitCast` yet.
fn numericBitSize(pool: *const InternPool, ty: InternPool.Index) ?u16 {
    if (intTypeInfo(pool, ty)) |info| return info.bits;
    return switch (ty) {
        .f16_type => 16,
        .f32_type => 32,
        .f64_type => 64,
        .f80_type => 80,
        .f128_type => 128,
        else => null,
    };
}

/// Numeric `@bitCast` worker: route the operand bits through the dest
/// type's storage. Supports int <-> int (same bit width but different
/// signedness -- uses stdlib's `truncate` for two's-complement view)
/// and int <-> float of matching width (bit pattern reinterpret).
fn reinterpretBitCast(
    sema: *Sema,
    operand_key: InternPool.Key,
    dest_ty: InternPool.Index,
    bits: u16,
) Error!Value {
    const ip = sema.intern_pool;
    const dest_int = intTypeInfo(ip, dest_ty);

    switch (operand_key) {
        .int => |int| {
            if (dest_int) |info| {
                // Reinterpret same-width int: truncate gives the two's-
                // complement view at the destination signedness.
                var space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
                const big = int.storage.toBigInt(&space);
                const limb_bits: usize = @bitSizeOf(std.math.big.Limb);
                const workspace_limbs: usize = (@as(usize, info.bits) + limb_bits - 1) / limb_bits + 1;
                const workspace = try sema.gpa.alloc(std.math.big.Limb, workspace_limbs);
                defer sema.gpa.free(workspace);
                var mutable: std.math.big.int.Mutable = .{
                    .limbs = workspace,
                    .len = undefined,
                    .positive = undefined,
                };
                mutable.truncate(big, info.signedness, info.bits);
                const idx = try ip.internIntValue(dest_ty, mutable.toConst());
                return .{ .index = idx };
            }
            // int -> float of the same width.
            const bits_u128 = try intBitsAsU128(int, bits);
            return try sema.internBitsAsFloat(bits_u128, dest_ty);
        },
        .float => |float| {
            const bits_u128 = floatBitsAsU128(float);
            if (dest_int) |info| {
                return try sema.internBitsAsInt(bits_u128, dest_ty, info);
            }
            // float -> float of the same width: identity bit pattern.
            return try sema.internBitsAsFloat(bits_u128, dest_ty);
        },
        else => {
            try sema.writer.writeAll("@bitCast: operand kind not supported\n");
            return error.AnalysisFail;
        },
    }
}

/// Read an int value's `bits` low bits as a `u128`. Used by `@bitCast`
/// when forwarding an int's bit pattern into a same-width float.
fn intBitsAsU128(int: InternPool.Key.Int, bits: u16) Error!u128 {
    assert(bits > 0);
    assert(bits <= 128);
    var space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
    const big = int.storage.toBigInt(&space);
    // toInt(u128) sign-checks; we want the two's-complement view. The
    // limbs already hold the magnitude; flip the sign bit explicitly
    // for negative values to land at the right u128 pattern.
    if (big.positive) return big.toInt(u128) catch unreachable;
    const magnitude: u128 = big.toInt(u128) catch unreachable;
    const mask: u128 = if (bits == 128) ~@as(u128, 0) else (@as(u128, 1) << @intCast(bits)) - 1;
    return (~magnitude + 1) & mask;
}

fn floatBitsAsU128(float: InternPool.Key.Float) u128 {
    return switch (float.storage) {
        .f16 => |v| @as(u16, @bitCast(v)),
        .f32 => |v| @as(u32, @bitCast(v)),
        .f64 => |v| @as(u64, @bitCast(v)),
        .f80 => |v| @as(u80, @bitCast(v)),
        .f128 => |v| @as(u128, @bitCast(v)),
    };
}

fn internBitsAsFloat(sema: *Sema, bits: u128, dest_ty: InternPool.Index) Error!Value {
    const storage: InternPool.Key.Float.Storage = switch (dest_ty) {
        .f16_type => .{ .f16 = @bitCast(@as(u16, @intCast(bits))) },
        .f32_type => .{ .f32 = @bitCast(@as(u32, @intCast(bits))) },
        .f64_type => .{ .f64 = @bitCast(@as(u64, @intCast(bits))) },
        .f80_type => .{ .f80 = @bitCast(@as(u80, @intCast(bits))) },
        .f128_type => .{ .f128 = @bitCast(bits) },
        else => unreachable,
    };
    const idx = try sema.intern_pool.internFloat(.{ .ty = dest_ty, .storage = storage });
    return .{ .index = idx };
}

fn internBitsAsInt(
    sema: *Sema,
    bits: u128,
    dest_ty: InternPool.Index,
    dest_info: std.lang.Type.Int,
) Error!Value {
    var limbs_buf: [(128 + @bitSizeOf(std.math.big.Limb) - 1) / @bitSizeOf(std.math.big.Limb) + 1]std.math.big.Limb = undefined;
    var mutable: std.math.big.int.Mutable = .{
        .limbs = &limbs_buf,
        .len = undefined,
        .positive = undefined,
    };
    mutable.set(bits);
    var work_buf: [limbs_buf.len]std.math.big.Limb = undefined;
    var work: std.math.big.int.Mutable = .{
        .limbs = &work_buf,
        .len = undefined,
        .positive = undefined,
    };
    work.truncate(mutable.toConst(), dest_info.signedness, dest_info.bits);
    const idx = try sema.intern_pool.internIntValue(dest_ty, work.toConst());
    return .{ .index = idx };
}

fn isFixedWidthFloatType(ty: InternPool.Index) bool {
    return switch (ty) {
        .f16_type, .f32_type, .f64_type, .f80_type, .f128_type => true,
        else => false,
    };
}

/// True for every Zig float type: comptime_float, c_longdouble, and the
/// fixed-width family. Used by the cast builtins to gate destination
/// types.
fn isFloatTypeIndex(ty: InternPool.Index) bool {
    return ty == .comptime_float_type or ty == .c_longdouble_type or isFixedWidthFloatType(ty);
}

/// Widen a `Key.Float`'s storage to f128 (lossless for every input
/// width). The pool's read-side already normalises comptime_float to
/// f128 storage, so for that case this is just an unwrap; for fixed
/// widths this is `@floatCast`.
fn floatToF128(source: InternPool.Key.Float) f128 {
    return switch (source.storage) {
        inline else => |v| @as(f128, @floatCast(v)),
    };
}

/// Narrow (or pass through) an f128 to the storage variant matching
/// `dest_ty`. Caller must have checked `isFloatTypeIndex(dest_ty)`.
/// `c_longdouble_type` stores as f128 -- see InternPool's emitFloat for
/// the matching tag selection (the f80/f128 split is taken there).
fn narrowF128ToFloatStorage(value: f128, dest_ty: InternPool.Index) InternPool.Key.Float.Storage {
    return switch (dest_ty) {
        .f16_type => .{ .f16 = @floatCast(value) },
        .f32_type => .{ .f32 = @floatCast(value) },
        .f64_type => .{ .f64 = @floatCast(value) },
        .f80_type => .{ .f80 = @floatCast(value) },
        .f128_type => .{ .f128 = value },
        .comptime_float_type, .c_longdouble_type => .{ .f128 = value },
        else => unreachable,
    };
}

/// `shl / shr`. Same operand shape as the other binary ops, but `rhs` is a
/// shift amount that must fit in `usize` and be non-negative -- the kernel's
/// stdlib-named `ConvertError.NegativeIntoUnsigned` /
/// `ConvertError.TargetTooSmall` flow through here and become runtime-style
/// diagnostics + `AnalysisFail`.
///
/// `shl_exact` / `shr_exact` land alongside fixed-width int support -- the
/// "no bits lost" check is meaningful only when the operand has a width.
///
/// Compiler reference: src/Sema.zig:zirShl / zirShr.
/// `shl / shr / shl_exact / shr_exact / shl_sat`. Operand shape is
/// `pl_node + Bin`; LHS may be any int type, RHS is the pre-coerced
/// shift amount (typeof_log2_int_type). For fixed-width LHS, the
/// result is computed in arbitrary precision and re-fit; `_exact`
/// variants reject any bit-loss, `_sat` clamps via stdlib's
/// `shiftLeftSat`.
fn evalShift(
    sema: *Sema,
    inst: Zir.Inst.Index,
    tag: Zir.Inst.Tag,
) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    const bin = sema.zir.extraData(Zir.Inst.Bin, pl_node.payload_index).data;
    assert(bin.lhs != .none);
    assert(bin.rhs != .none);

    const op_name: []const u8 = @tagName(tag);
    const ip = sema.intern_pool;
    const lhs_value = try sema.resolveRef(bin.lhs);
    const rhs_value = try sema.resolveRef(bin.rhs);
    const lhs_key = ip.indexToKey(lhs_value.index);
    const rhs_key = ip.indexToKey(rhs_value.index);

    if (lhs_key != .int or rhs_key != .int) {
        try sema.writer.print("{s}: non-int operand\n", .{op_name});
        return error.AnalysisFail;
    }

    var lhs_space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
    var rhs_space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
    const lhs = lhs_key.int.storage.toBigInt(&lhs_space);
    const rhs = rhs_key.int.storage.toBigInt(&rhs_space);
    const dest_ty = lhs_key.int.ty;

    // shl_sat needs the destination signedness / bit count up front;
    // the bignum kernel handles the rest.
    if (tag == .shl_sat) {
        const dest_info = intTypeInfo(ip, dest_ty) orelse {
            try sema.writer.print("{s}: saturating shift requires a fixed-width int operand\n", .{op_name});
            return error.AnalysisFail;
        };
        const idx = try sema.runShlSat(lhs, rhs, dest_ty, dest_info, op_name);
        return .{ .index = idx };
    }

    const kernel: ShiftKernel = switch (tag) {
        .shl, .shl_exact => arith.internShl,
        .shr, .shr_exact => arith.internShr,
        else => unreachable,
    };
    const tmp_idx = kernel(sema.gpa, ip, lhs, rhs) catch |err|
        return sema.reportShiftAmountError(err, op_name);

    // `_exact`: confirm the inverse shift round-trips, i.e. no bits
    // were lost. Compares lhs against (result <<-> shift_amount).
    if (tag == .shl_exact or tag == .shr_exact) {
        try sema.checkShiftExact(tag, lhs, rhs, tmp_idx, op_name);
    }

    if (dest_ty == .comptime_int_type) return .{ .index = tmp_idx };
    return try sema.refitIntToFixedWidth(tmp_idx, dest_ty, op_name);
}

fn reportShiftAmountError(sema: *Sema, err: arith.ShiftError, op_name: []const u8) Error {
    switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        error.NegativeIntoUnsigned => {
            try sema.writer.print("error: {s}: shift amount is negative\n", .{op_name});
            return error.AnalysisFail;
        },
        error.TargetTooSmall => {
            try sema.writer.print("error: {s}: shift amount exceeds usize\n", .{op_name});
            return error.AnalysisFail;
        },
        error.ShiftAmountTooLarge => {
            try sema.writer.print(
                "error: {s}: shift amount exceeds {d} bits\n",
                .{ op_name, arith.max_shift_bits },
            );
            return error.AnalysisFail;
        },
    }
}

/// `_exact` shift safety: re-shift the result the opposite direction
/// and confirm it matches the original LHS bit-for-bit. Mirrors the
/// compiler's `zirShlExact` / `zirShrExact` post-checks.
fn checkShiftExact(
    sema: *Sema,
    tag: Zir.Inst.Tag,
    lhs: std.math.big.int.Const,
    rhs: std.math.big.int.Const,
    result_idx: InternPool.Index,
    op_name: []const u8,
) Error!void {
    assert(tag == .shl_exact or tag == .shr_exact);
    const ip = sema.intern_pool;
    var space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
    const result = ip.indexToKey(result_idx).int.storage.toBigInt(&space);

    const inverse_kernel: ShiftKernel = if (tag == .shl_exact) arith.internShr else arith.internShl;
    const round_trip = inverse_kernel(sema.gpa, ip, result, rhs) catch |err|
        return sema.reportShiftAmountError(err, op_name);

    var rt_space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
    const round_trip_big = ip.indexToKey(round_trip).int.storage.toBigInt(&rt_space);
    if (!round_trip_big.eql(lhs)) {
        try sema.writer.print("error: {s}: exact shift lost bits\n", .{op_name});
        return error.AnalysisFail;
    }
}

/// `shl_sat`: shift left and saturate to the destination width's
/// `[minInt, maxInt]` range via stdlib's `shiftLeftSat`. Buffer
/// sized for the worst-case bit-shift output, matching the compiler
/// in `Sema/arith.zig:shlSat`.
fn runShlSat(
    sema: *Sema,
    lhs: std.math.big.int.Const,
    rhs: std.math.big.int.Const,
    dest_ty: InternPool.Index,
    dest_info: std.lang.Type.Int,
    op_name: []const u8,
) Error!InternPool.Index {
    const shift_amount = arith.shiftAmount(rhs) catch |err|
        return sema.reportShiftAmountError(err, op_name);

    const limb_bits: usize = @bitSizeOf(std.math.big.Limb);
    const max_limbs: usize = (@as(usize, dest_info.bits) + limb_bits - 1) / limb_bits + 1;
    const workspace = try sema.gpa.alloc(std.math.big.Limb, max_limbs);
    defer sema.gpa.free(workspace);

    var mutable: std.math.big.int.Mutable = .{
        .limbs = workspace,
        .len = undefined,
        .positive = undefined,
    };
    mutable.shiftLeftSat(lhs, shift_amount, dest_info.signedness, dest_info.bits);
    return try sema.intern_pool.internIntValue(dest_ty, mutable.toConst());
}

/// `bit_and / bit_or / xor`. Uses the same `resolveNumericPairToInt`
/// peer resolution as the arith dispatcher -- so fixed-width int
/// operands work and the result is range-checked back into the dest
/// type. For comptime_int operands, the bignum result is canonical.
///
/// Compiler reference: src/Sema.zig:zirBitBinOp -> src/Sema/arith.zig.
fn evalBitwise(sema: *Sema, inst: Zir.Inst.Index, tag: Zir.Inst.Tag) Error!?Value {
    assert(@intFromPtr(sema) != 0);
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    const bin = sema.zir.extraData(Zir.Inst.Bin, pl_node.payload_index).data;
    assert(bin.lhs != .none);
    assert(bin.rhs != .none);

    const op_name: []const u8 = @tagName(tag);
    const ip = sema.intern_pool;
    const lhs_value = try sema.resolveRef(bin.lhs);
    const rhs_value = try sema.resolveRef(bin.rhs);
    const lhs_key = ip.indexToKey(lhs_value.index);
    const rhs_key = ip.indexToKey(rhs_value.index);

    const triple = resolveNumericPairToInt(ip, lhs_key, rhs_key) orelse {
        try sema.writer.print("{s}: non-int or incompatible operands\n", .{op_name});
        return error.AnalysisFail;
    };

    var lhs_space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
    var rhs_space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
    const lhs = triple.lhs.storage.toBigInt(&lhs_space);
    const rhs = triple.rhs.storage.toBigInt(&rhs_space);

    const gpa = sema.gpa;
    const tmp_idx = switch (tag) {
        .bit_and => try arith.internBitAnd(gpa, ip, lhs, rhs),
        .bit_or => try arith.internBitOr(gpa, ip, lhs, rhs),
        .xor => try arith.internXor(gpa, ip, lhs, rhs),
        else => unreachable,
    };
    if (triple.ty == .comptime_int_type) return .{ .index = tmp_idx };
    return try sema.refitIntToFixedWidth(tmp_idx, triple.ty, op_name);
}

/// `cmp_lt / cmp_lte / cmp_eq / cmp_gte / cmp_gt / cmp_neq`. Same operand
/// shape as `evalBinaryArith` (pl_node + Bin); int vs float kernels are
/// selected by the operand types, results map to the well-known
/// `Index.bool_true` / `Index.bool_false`.
///
/// Compiler reference: src/Sema.zig:zirCmp -> src/Sema/arith.zig:cmpScalar.
fn evalComparison(
    sema: *Sema,
    inst: Zir.Inst.Index,
    op: std.math.CompareOperator,
) Error!?Value {
    assert(@intFromPtr(sema) != 0);
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    const bin = sema.zir.extraData(Zir.Inst.Bin, pl_node.payload_index).data;
    assert(bin.lhs != .none);
    assert(bin.rhs != .none);

    const op_name: []const u8 = @tagName(op);
    const ip = sema.intern_pool;
    const lhs_value = try sema.resolveRef(bin.lhs);
    const rhs_value = try sema.resolveRef(bin.rhs);
    const lhs_key = ip.indexToKey(lhs_value.index);
    const rhs_key = ip.indexToKey(rhs_value.index);

    // Comparison doesn't need to re-fit, so it only cares that peer
    // resolution found a common int type -- the bignum values compare
    // exactly across signedness and width.
    if (resolveNumericPairToInt(ip, lhs_key, rhs_key)) |triple| {
        var lhs_space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
        var rhs_space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
        const lhs = triple.lhs.storage.toBigInt(&lhs_space);
        const rhs = triple.rhs.storage.toBigInt(&rhs_space);
        const result = arith.compareInt(lhs, rhs, op);
        return .{ .index = if (result) .bool_true else .bool_false };
    }

    if (coerceNumericPairToFloat(lhs_key, rhs_key)) |pair| {
        const result = compareFloatStorage(pair[0].storage, pair[1].storage, op);
        return .{ .index = if (result) .bool_true else .bool_false };
    }

    if ((lhs_key == .int or lhs_key == .float) and (rhs_key == .int or rhs_key == .float)) {
        try sema.writer.print("{s}: incompatible numeric operands\n", .{op_name});
    } else {
        try sema.writer.print("{s}: non-numeric or mismatched operands\n", .{op_name});
    }
    return error.AnalysisFail;
}

/// Compare two float storages of the same width. NaN comparisons follow
/// IEEE: any comparison with a NaN is false except `.neq`, which is true.
/// `std.math.order` doesn't totalise NaN, so the language operators are
/// used directly via an inline switch over the storage variant.
fn compareFloatStorage(
    lhs: InternPool.Key.Float.Storage,
    rhs: InternPool.Key.Float.Storage,
    op: std.math.CompareOperator,
) bool {
    const StorageTag = @typeInfo(InternPool.Key.Float.Storage).@"union".tag_type.?;
    assert(@as(StorageTag, lhs) == @as(StorageTag, rhs));
    switch (lhs) {
        inline else => |lhs_v, storage_tag| {
            const rhs_v = @field(rhs, @tagName(storage_tag));
            return switch (op) {
                .lt => lhs_v < rhs_v,
                .lte => lhs_v <= rhs_v,
                .eq => lhs_v == rhs_v,
                .gte => lhs_v >= rhs_v,
                .gt => lhs_v > rhs_v,
                .neq => lhs_v != rhs_v,
            };
        },
    }
}

/// `negate` / `negate_wrap`. AstGen lowers `-x` as `negate(x)`; constant-
/// folded literals like `-1` / `-1.5` come through as well-known Refs or
/// as a single signed literal and never reach here. `negate_wrap` is the
/// `-%x` form, valid only on fixed-width int operands.
///
/// Compiler reference: src/Sema.zig:zirNegate (~13858) /
/// src/Sema.zig:zirNegateWrap (~13896).
fn evalNegate(sema: *Sema, inst: Zir.Inst.Index, tag: Zir.Inst.Tag) Error!?Value {
    assert(tag == .negate or tag == .negate_wrap);
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    assert(un_node.operand != .none);

    const ip = sema.intern_pool;
    const operand_value = try sema.resolveRef(un_node.operand);
    const operand_key = ip.indexToKey(operand_value.index);
    const op_name: []const u8 = @tagName(tag);

    if (operand_key == .float) {
        if (tag == .negate_wrap) {
            try sema.writer.writeAll("negate_wrap: not valid on float operand\n");
            return error.AnalysisFail;
        }
        if (operand_key.float.ty != .comptime_float_type and !isFixedWidthFloatType(operand_key.float.ty)) {
            try sema.writer.writeAll("negate: float type not yet supported\n");
            return error.AnalysisFail;
        }
        const out_storage = switch (operand_key.float.storage) {
            inline else => |v, storage_tag| @unionInit(
                InternPool.Key.Float.Storage,
                @tagName(storage_tag),
                -v,
            ),
        };
        const idx = try ip.internFloat(.{ .ty = operand_key.float.ty, .storage = out_storage });
        return .{ .index = idx };
    }

    if (operand_key == .int) {
        if (operand_key.int.ty == .comptime_int_type) {
            // Wrap is meaningless at infinite precision: both forms reduce
            // to a plain negate of a comptime_int.
            var space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
            const operand = operand_key.int.storage.toBigInt(&space);
            const idx = try arith.internNegate(sema.gpa, ip, operand);
            return .{ .index = idx };
        }
        const dest_info = intTypeInfo(ip, operand_key.int.ty) orelse {
            try sema.writer.print("{s}: int type not yet supported\n", .{op_name});
            return error.AnalysisFail;
        };
        if (tag == .negate_wrap) {
            return try sema.runIntNegateWrap(operand_key.int, operand_key.int.ty, dest_info);
        }
        var space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
        const operand = operand_key.int.storage.toBigInt(&space);
        const tmp_idx = try arith.internNegate(sema.gpa, ip, operand);
        return try sema.refitIntToFixedWidth(tmp_idx, operand_key.int.ty, op_name);
    }

    try sema.writer.print("{s}: non-numeric operand\n", .{op_name});
    return error.AnalysisFail;
}

/// `ptr_type`: evaluate a `*T` / `*const T` / `[*]T` / `[]T` / `[*c]T`
/// type expression to an interned `Key.ptr_type` value. Sentinel,
/// align, address_space, and bit_range extensions trail the payload
/// via additional `Ref` slots in extra; Stage 2 handles only the
/// base case (none of the optional extensions). Compiler reference:
/// `src/Sema.zig:zirPtrType`.
fn evalPtrType(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const inst_data = sema.zir.instructions.items(.data)[@intFromEnum(inst)].ptr_type;
    if (inst_data.flags.has_sentinel) {
        try sema.writer.writeAll("ptr_type: sentinel-terminated pointers not yet supported\n");
        return error.AnalysisFail;
    }
    if (inst_data.flags.has_align or inst_data.flags.has_addrspace or inst_data.flags.has_bit_range) {
        try sema.writer.writeAll("ptr_type: align / address_space / bit_range not yet supported\n");
        return error.AnalysisFail;
    }

    const payload = sema.zir.extraData(Zir.Inst.PtrType, inst_data.payload_index).data;
    assert(payload.elem_type != .none);

    const elem_value = try sema.resolveRef(payload.elem_type);
    const child_ty: InternPool.Index = switch (sema.intern_pool.indexToKey(elem_value.index)) {
        .type_value => |t| t,
        .simple_type, .int_type, .anyframe_type, .ptr_type => elem_value.index,
        else => {
            try sema.writer.writeAll("ptr_type: element is not a type\n");
            return error.AnalysisFail;
        },
    };
    assert(child_ty != .none);

    const idx = try sema.intern_pool.internPtrType(.{
        .child = child_ty,
        .flags = .{
            .size = switch (inst_data.size) {
                .one => .one,
                .many => .many,
                .slice => .slice,
                .c => .c,
            },
            .is_const = !inst_data.flags.is_mutable,
            .is_volatile = inst_data.flags.is_volatile,
            .is_allowzero = inst_data.flags.is_allowzero,
            .address_space = .generic,
        },
    });
    return .{ .index = idx };
}

/// `alloc` / `alloc_mut` / `alloc_comptime_mut`: reserve a fresh
/// entry in `comptime_allocs`, initialise to a typed `undef`, and
/// return a `Key.ptr` whose `BaseAddr = .comptime_alloc = index`.
///
/// Compiler reference: src/Sema.zig:zirAlloc (~3723) /
/// src/Sema.zig:zirAllocMut (~3755) / analyzeComptimeAlloc (~33069).
/// The compiler distinguishes `alloc` (const) from `alloc_mut` via
/// the resulting pointer type's `is_const` flag -- not via a separate
/// runtime instruction. We do the same: both paths reach `evalAlloc`
/// with `is_const` set; the only behavioural difference is whether
/// `store_node` will accept writes through the resulting pointer.
/// Modelled as `bool` to match `std.lang.Type.Pointer.is_const`
/// and `Zir.Inst.alloc.is_const` rather than introduce a REPL-local
/// two-state enum.
fn evalAlloc(sema: *Sema, inst: Zir.Inst.Index, is_const: bool) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    assert(un_node.operand != .none);

    const child_ty = try sema.resolveDestType(un_node.operand, "alloc");

    const ip = sema.intern_pool;
    const undef_idx = try ip.get(.{ .undef = child_ty });
    const alloc_index: u32 = @intCast(sema.comptime_allocs.items.len);
    try sema.comptime_allocs.append(sema.gpa, .{
        .ty = child_ty,
        .val = .{ .index = undef_idx },
        .is_const = is_const,
    });

    const ptr_ty = try ip.internPtrType(.{
        .child = child_ty,
        .flags = .{ .size = .one, .is_const = is_const },
    });
    const ptr_idx = try ip.internPtr(.{
        .ty = ptr_ty,
        .base_addr = .{ .comptime_alloc = @enumFromInt(alloc_index) },
        .byte_offset = 0,
    });
    return .{ .index = ptr_idx };
}

/// `store_node ptr, value`: deref `ptr` to find its `comptime_alloc`
/// entry, coerce `value` to the entry's stored type, and overwrite.
/// Mirrors `storePtr2` -> `coerceExtra` -> `coerceInMemory` from the
/// compiler (`src/Sema.zig`). Writes through a `*const T` pointer
/// surface "cannot assign to constant" -- same vocabulary the
/// compiler uses.
fn evalStoreNode(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    const bin = sema.zir.extraData(Zir.Inst.Bin, pl_node.payload_index).data;
    assert(bin.lhs != .none);
    assert(bin.rhs != .none);

    const ip = sema.intern_pool;
    const ptr_value = try sema.resolveRef(bin.lhs);
    const ptr_key = ip.indexToKey(ptr_value.index);
    if (ptr_key != .ptr) {
        try sema.writer.writeAll("store: lhs is not a pointer\n");
        return error.AnalysisFail;
    }

    const ptr_ty_key = ip.indexToKey(ptr_key.ptr.ty);
    assert(ptr_ty_key == .ptr_type);
    if (ptr_ty_key.ptr_type.flags.is_const) {
        try sema.writer.writeAll("cannot assign to constant\n");
        return error.AnalysisFail;
    }

    const alloc = try sema.lookupComptimeAlloc(ptr_key.ptr, "store");
    const rhs_value = try sema.resolveRef(bin.rhs);
    const coerced = try sema.coerceValueToType(rhs_value, alloc.ty, "store");
    alloc.val = coerced;
    return .{ .index = .void_value };
}

/// `load ptr`: deref `ptr` to find its `comptime_alloc` entry and
/// return the entry's current value. Compiler reference:
/// src/Sema.zig:zirLoad (~15173) -> analyzeLoad (~30040) ->
/// pointerDeref (~33154).
fn evalLoad(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    assert(un_node.operand != .none);

    const ptr_value = try sema.resolveRef(un_node.operand);
    const ptr_key = sema.intern_pool.indexToKey(ptr_value.index);
    if (ptr_key != .ptr) {
        try sema.writer.writeAll("load: operand is not a pointer\n");
        return error.AnalysisFail;
    }
    const alloc = try sema.lookupComptimeAlloc(ptr_key.ptr, "load");
    return alloc.val;
}

/// Locate the `ComptimeAlloc` entry referenced by a `Key.Ptr`. Returns
/// a pointer into `comptime_allocs` so the caller can mutate `val`
/// (for store) or read it (for load) without copying. The `byte_offset`
/// is asserted to be zero -- field/element pointers (non-zero offsets)
/// arrive with Stage 4 aggregates.
fn lookupComptimeAlloc(
    sema: *Sema,
    ptr: InternPool.Key.Ptr,
    op_name: []const u8,
) Error!*ComptimeAlloc {
    assert(@intFromPtr(sema) != 0);
    assert(op_name.len > 0);

    if (ptr.byte_offset != 0) {
        try sema.writer.print("{s}: pointer offset not yet supported\n", .{op_name});
        return error.AnalysisFail;
    }
    const idx: u32 = @intFromEnum(ptr.base_addr.comptime_alloc);
    assert(idx < sema.comptime_allocs.items.len);
    return &sema.comptime_allocs.items[idx];
}

/// Coerce a Value to a destination type using the same paths
/// `evalAsNode` follows: identity, comptime_int -> fixed-width int,
/// any-numeric -> fixed-width float / comptime_float, `undef` re-tag.
/// Mirrors the compiler's `coerceExtra` -> `coerceInMemory` ->
/// `pt.getCoerced` chain.
fn coerceValueToType(
    sema: *Sema,
    value: Value,
    dest_ty: InternPool.Index,
    op_name: []const u8,
) Error!Value {
    assert(dest_ty != .none);
    assert(value.index != .none);

    const ip = sema.intern_pool;
    const value_type = Value.typeOf(value, ip);
    if (value_type.index == dest_ty) return value;

    const key = ip.indexToKey(value.index);

    if (key == .undef) {
        const idx = try ip.get(.{ .undef = dest_ty });
        return .{ .index = idx };
    }

    if (value_type.index == .comptime_int_type and intTypeInfo(ip, dest_ty) != null) {
        return try sema.refitIntToFixedWidth(value.index, dest_ty, op_name);
    }

    if (isFloatTypeIndex(dest_ty)) {
        if (coerceToTargetFloat(key, dest_ty)) |coerced| {
            const idx = try ip.internFloat(coerced);
            return .{ .index = idx };
        }
    }

    // Coercion into an error-union type: an error value becomes the
    // `.err` arm; any other value coerces to the payload type and
    // becomes the `.payload` arm. Same shape as the compiler's
    // `coerceExtra` error-union branch.
    if (ip.indexToKey(dest_ty) == .error_union_type) {
        return try sema.coerceToErrorUnion(value, dest_ty, op_name);
    }

    try sema.writer.print("{s}: cannot coerce value to destination type\n", .{op_name});
    return error.AnalysisFail;
}

fn coerceToErrorUnion(
    sema: *Sema,
    value: Value,
    dest_ty: InternPool.Index,
    op_name: []const u8,
) Error!Value {
    const ip = sema.intern_pool;
    const eu_type = ip.indexToKey(dest_ty).error_union_type;
    const value_key = ip.indexToKey(value.index);

    // An error value of any error-set type coerces in by name --
    // the compiler verifies the name is a member of the destination
    // error set. Stage 3 ships the name carry; set-membership
    // checking lands when error-union narrowing handlers do.
    if (value_key == .err) {
        const idx = try ip.internErrorUnion(.{
            .ty = dest_ty,
            .val = .{ .err_name = value_key.err.name },
        });
        return .{ .index = idx };
    }

    // Anything else: coerce to the payload type, then wrap.
    const payload_value = try sema.coerceValueToType(value, eu_type.payload_type, op_name);
    const idx = try ip.internErrorUnion(.{
        .ty = dest_ty,
        .val = .{ .payload = payload_value.index },
    });
    return .{ .index = idx };
}

/// `~x`: bitwise NOT. For comptime_int the identity `~x = -(x + 1)` is
/// applied at arbitrary precision via `addScalar` + sign flip. For
/// fixed-width int operands stdlib's `BigIntMutable.bitNotWrap` flips
/// the bits within the type's width and `refitIntToFixedWidth` re-
/// interns at the operand's type.
///
/// Compiler reference: src/Sema.zig:zirBitNot (~13302).
fn evalBitNot(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    assert(un_node.operand != .none);

    const ip = sema.intern_pool;
    const operand_value = try sema.resolveRef(un_node.operand);
    const operand_key = ip.indexToKey(operand_value.index);

    if (operand_key != .int) {
        try sema.writer.writeAll("bit_not: operand is not an int\n");
        return error.AnalysisFail;
    }

    if (operand_key.int.ty == .comptime_int_type) {
        return try sema.runComptimeIntBitNot(operand_key.int);
    }

    const dest_info = intTypeInfo(ip, operand_key.int.ty) orelse {
        try sema.writer.writeAll("bit_not: int type not yet supported\n");
        return error.AnalysisFail;
    };
    return try sema.runFixedWidthBitNot(operand_key.int, operand_key.int.ty, dest_info);
}

/// Compute `~x` on a `comptime_int` operand via the
/// `~x = -(x + 1)` identity. Workspace is one limb larger than the
/// operand because `addScalar` can carry.
fn runComptimeIntBitNot(sema: *Sema, operand_int: InternPool.Key.Int) Error!Value {
    assert(operand_int.ty == .comptime_int_type);
    var op_space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
    const operand_big = operand_int.storage.toBigInt(&op_space);

    const workspace_limbs = operand_big.limbs.len + 1;
    const workspace = try sema.gpa.alloc(std.math.big.Limb, workspace_limbs);
    defer sema.gpa.free(workspace);

    var mutable: std.math.big.int.Mutable = .{
        .limbs = workspace,
        .len = undefined,
        .positive = undefined,
    };
    mutable.addScalar(operand_big, 1);
    const plus_one = mutable.toConst();

    const idx = try sema.intern_pool.internComptimeInt(plus_one.negate());
    return .{ .index = idx };
}

/// Compute `~x` on a fixed-width int via stdlib's `bitNotWrap`. Buffer
/// sized to `calcTwosCompLimbCount(bits)` plus a one-limb cushion (the
/// stdlib helper internally adds before the wrap).
fn runFixedWidthBitNot(
    sema: *Sema,
    operand_int: InternPool.Key.Int,
    dest_ty: InternPool.Index,
    dest_info: std.lang.Type.Int,
) Error!Value {
    var op_space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
    const operand_big = operand_int.storage.toBigInt(&op_space);

    const limb_bits: usize = @bitSizeOf(std.math.big.Limb);
    const workspace_limbs: usize = (@as(usize, dest_info.bits) + limb_bits - 1) / limb_bits + 1;
    const workspace = try sema.gpa.alloc(std.math.big.Limb, workspace_limbs);
    defer sema.gpa.free(workspace);

    var mutable: std.math.big.int.Mutable = .{
        .limbs = workspace,
        .len = undefined,
        .positive = undefined,
    };
    mutable.bitNotWrap(operand_big, dest_info.signedness, dest_info.bits);
    const idx = try sema.intern_pool.internIntValue(dest_ty, mutable.toConst());
    return .{ .index = idx };
}

/// Compute `-%x` on a fixed-width int via stdlib's `subWrap(0, x, ...)`.
/// Wrap semantics: `-%@as(i8, -128)` is `-128` (overflow wraps).
fn runIntNegateWrap(
    sema: *Sema,
    operand_int: InternPool.Key.Int,
    dest_ty: InternPool.Index,
    dest_info: std.lang.Type.Int,
) Error!Value {
    var op_space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
    const operand_big = operand_int.storage.toBigInt(&op_space);

    const limb_bits: usize = @bitSizeOf(std.math.big.Limb);
    const workspace_limbs: usize = (@as(usize, dest_info.bits) + limb_bits - 1) / limb_bits + 1;
    const workspace = try sema.gpa.alloc(std.math.big.Limb, workspace_limbs);
    defer sema.gpa.free(workspace);

    var mutable: std.math.big.int.Mutable = .{
        .limbs = workspace,
        .len = undefined,
        .positive = undefined,
    };
    const zero: std.math.big.int.Const = .{ .limbs = &.{0}, .positive = true };
    _ = mutable.subWrap(zero, operand_big, dest_info.signedness, dest_info.bits);
    const idx = try sema.intern_pool.internIntValue(dest_ty, mutable.toConst());
    return .{ .index = idx };
}

fn resolveRef(sema: *Sema, ref: Zir.Inst.Ref) Error!Value {
    assert(ref != .none);

    if (ref.toIndex()) |inst_idx| {
        if (sema.results.get(inst_idx)) |value| return value;
        try sema.writer.print(
            "internal error: unresolved instruction ref %{d}\n",
            .{@intFromEnum(inst_idx)},
        );
        return error.AnalysisFail;
    }

    if (wellKnownRefToValue(ref)) |value| return value;
    if (try sema.internTypedWellKnownRef(ref)) |value| return value;
    try sema.writer.print("unsupported ZIR ref: {s}\n", .{@tagName(ref)});
    return error.AnalysisFail;
}

/// Refs the compiler hands out as pre-typed constants --
/// `zero_u8` / `one_u8` / `one_usize` / `undef_bool` / etc. We intern
/// them on demand rather than reserving well-known slots, since they
/// fold into the pool's normal int / undef storage with no special
/// shape. Mirrors the compiler's well-known table layout in
/// `src/InternPool.zig`.
fn internTypedWellKnownRef(sema: *Sema, ref: Zir.Inst.Ref) Error!?Value {
    const TypedInt = struct { ty: InternPool.Index, value: u64 };
    const typed_int: ?TypedInt = switch (ref) {
        .zero_usize => .{ .ty = .usize_type, .value = 0 },
        .zero_u1 => .{ .ty = .u1_type, .value = 0 },
        .zero_u8 => .{ .ty = .u8_type, .value = 0 },
        .one_usize => .{ .ty = .usize_type, .value = 1 },
        .one_u1 => .{ .ty = .u1_type, .value = 1 },
        .one_u8 => .{ .ty = .u8_type, .value = 1 },
        .four_u8 => .{ .ty = .u8_type, .value = 4 },
        else => null,
    };
    if (typed_int) |t| {
        const idx = try sema.intern_pool.internInt(.{
            .ty = t.ty,
            .storage = .{ .u64 = t.value },
        });
        return .{ .index = idx };
    }

    const undef_ty: ?InternPool.Index = switch (ref) {
        .undef_bool => .bool_type,
        .undef_usize => .usize_type,
        .undef_u1 => .u1_type,
        else => null,
    };
    if (undef_ty) |ty| {
        const idx = try sema.intern_pool.get(.{ .undef = ty });
        return .{ .index = idx };
    }
    return null;
}

/// Maps a static ZIR `Ref` to the corresponding interned Value.
///
/// The compiler does this in three lines (src/Sema.zig:resolveInst):
///
///     return @enumFromInt(@intFromEnum(zir_ref));
///
/// because its `Zir.Inst.Ref` and `InternPool.Index` are kept in
/// lock-step. A non-instruction Ref *is* the matching InternPool index,
/// by construction. Pure integer identity, no lookup.
///
/// Our parity is partial -- the type-prefix of `Index` through
/// `enum_literal_type` (positions 0..44) mirrors the compiler's
/// `Index` enum exactly, so we use the compiler's identity pattern
/// directly for that range. Positions beyond it diverge until further
/// compliance steps add the ptr/slice/vector wells and the typed
/// undef/int values; the reflection bridge below covers them by name.
/// Once the gap is closed, the reflection block disappears and only
/// the identity line remains.
fn wellKnownRefToValue(ref: Zir.Inst.Ref) ?Value {
    if (ref == .none) return null;
    if (ref.toIndex() != null) return null; // dynamic instruction ref

    const ref_int = @intFromEnum(ref);
    const identity_boundary = @intFromEnum(InternPool.Index.enum_literal_type);
    if (ref_int <= identity_boundary) {
        return Value{ .index = @enumFromInt(ref_int) };
    }

    inline for (@typeInfo(Zir.Inst.Ref).@"enum".fields) |field| {
        if (comptime std.mem.eql(u8, field.name, "none")) continue;
        if (comptime !@hasField(InternPool.Index, field.name)) continue;
        if (comptime field.value <= @intFromEnum(InternPool.Index.enum_literal_type)) continue;
        if (ref_int == field.value) {
            return Value{ .index = @field(InternPool.Index, field.name) };
        }
    }
    return null;
}

/// `decl_val`: read the value bound to a name in the current scope.
/// Walks `sema.namespace`'s parent chain via `pool.namespacePtr` ->
/// `Namespace.NameAdapter`, returning `nav.resolved.?.value` when
/// found. Surfaces a structured diagnostic when the name binds to a
/// non-value kind (test / comptime block / extern decl whose value
/// hasn't yet been resolved by linkage).
///
/// Compiler reference: `src/Sema.zig:zirDeclVal` (~5900) ->
/// `lookupIdentifier` (~5920) -> `analyzeNavVal`. The compiler's
/// `lookupIdentifier` asserts `unreachable` on a missing name
/// because AstGen pre-checks identifier resolution; our Sema-side
/// check is defense-in-depth -- the wrap-injection ensures session
/// names are in scope before AstGen runs, so a missing name would
/// be a structural bug in wrap-injection itself.
fn evalDeclVal(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const data = sema.zir.instructions.items(.data)[@intFromEnum(inst)].str_tok;
    const name_bytes = data.get(sema.zir);
    const name = try sema.intern_pool.getOrPutString(sema.gpa, name_bytes);

    const ns_idx = sema.namespace orelse {
        try sema.writer.print("decl_val '{s}': no namespace in scope\n", .{name_bytes});
        return error.AnalysisFail;
    };

    if (try sema.lookupName(ns_idx, name)) |nav_idx| {
        const nav = sema.intern_pool.getNav(nav_idx);
        const resolved = nav.resolved orelse {
            try sema.writer.print(
                "decl_val '{s}': binding recorded but value not resolved (test / comptime / extern)\n",
                .{name_bytes},
            );
            return error.AnalysisFail;
        };
        if (resolved.value == .none) {
            try sema.writer.print("decl_val '{s}': type resolved but value not yet\n", .{name_bytes});
            return error.AnalysisFail;
        }
        return Value{ .index = resolved.value };
    }

    try sema.writer.print("decl_val '{s}': not found in scope\n", .{name_bytes});
    return error.AnalysisFail;
}

/// Walk `ns_idx`'s parent chain and return the first Nav.Index whose
/// interned name equals `name`. Each per-namespace lookup goes
/// through `Namespace.lookupNav` (pub_decls then priv_decls);
/// bounded by `max_namespace_chain` so a malformed parent cycle
/// can't hang. Same shape as the compiler's `lookupIdentifier`
/// (`src/Sema.zig:5920`).
fn lookupName(
    sema: *Sema,
    ns_idx: InternPool.NamespaceIndex,
    name: InternPool.NullTerminatedString,
) Error!?InternPool.Nav.Index {
    assert(@intFromPtr(sema) != 0);

    var current: ?InternPool.NamespaceIndex = ns_idx;
    var depth: u32 = 0;
    while (current) |idx| : (depth += 1) {
        assert(depth < max_namespace_chain);
        const ns = sema.intern_pool.namespacePtr(idx);
        if (ns.lookupNav(sema.intern_pool, name)) |nav_idx| return nav_idx;
        current = ns.parent.unwrap();
    }
    return null;
}

const max_namespace_chain: u32 = 1024;

/// Walk every top-level decl in the input's main_struct_inst and
/// register each one in `sema.namespace`. Mirrors the compiler's
/// per-decl analysis loop in `Zcu.PerThread.analyzeFile` collapsed
/// to single-namespace eager evaluation. Idempotent against
/// wrap-injected predecessors: a name already bound in the namespace
/// is skipped (the injection appears in every line's ZIR so the user
/// can reference prior decls).
fn bindDecls(sema: *Sema) Error!void {
    assert(@intFromPtr(sema) != 0);
    assert(sema.namespace != null);

    const ns_idx = sema.namespace.?;
    for (sema.zir.typeDecls(.main_struct_inst)) |decl_inst| {
        try sema.bindOneDecl(ns_idx, decl_inst);
    }
}

fn bindOneDecl(
    sema: *Sema,
    ns_idx: InternPool.NamespaceIndex,
    decl_inst: Zir.Inst.Index,
) Error!void {
    const unwrapped = sema.zir.getDeclaration(decl_inst);
    if (unwrapped.kind == .@"comptime" or unwrapped.kind == .unnamed_test) {
        return sema.bindAnonymousDecl(ns_idx, decl_inst, unwrapped);
    }

    assert(unwrapped.name != .empty);
    const name_bytes = sema.zir.nullTerminatedString(unwrapped.name);

    // Skip the auto-generated REPL expression decl; `analyze`
    // already routes that through `evalBody` directly.
    if (std.mem.eql(u8, name_bytes, InputShape.expression_decl_name)) return;

    const name = try sema.intern_pool.getOrPutString(sema.gpa, name_bytes);

    // Skip wrap-injected predecessors: a name already in pub_decls
    // (or priv_decls) was bound by a prior REPL line and is being
    // re-emitted by wrap-injection so AstGen sees it in scope. The
    // user can't legally rebind it within a single input -- AstGen
    // would reject with "duplicate struct member name" first.
    if (try sema.lookupName(ns_idx, name)) |_| return;

    switch (unwrapped.kind) {
        .@"const", .@"var" => try sema.bindValueDecl(ns_idx, name, unwrapped),
        .@"test", .decltest => try sema.bindTestDecl(ns_idx, name, decl_inst, unwrapped),
        .@"comptime", .unnamed_test => unreachable, // routed above
    }
}

fn bindValueDecl(
    sema: *Sema,
    ns_idx: InternPool.NamespaceIndex,
    name: InternPool.NullTerminatedString,
    unwrapped: std.zig.Zir.Inst.Declaration.Unwrapped,
) Error!void {
    const value_body = unwrapped.value_body orelse {
        try sema.writer.print(
            "bindDecls '{s}': no value_body (extern decl, Stage 5/8)\n",
            .{sema.intern_pool.stringSlice(name)},
        );
        return error.AnalysisFail;
    };

    // Evaluate the value body first; if the decl has a type
    // annotation (`const x: T = ...`), AstGen emits a `type_body`
    // that resolves T, and we coerce the value to it. Otherwise we
    // keep the value's natural type (typically `comptime_int` /
    // `comptime_float` for unannotated literals).
    const raw_value = try sema.evalBody(value_body);
    const declared_type: ?InternPool.Index = if (unwrapped.type_body) |tb|
        (try sema.evalBody(tb)).index
    else
        null;
    const final_value = if (declared_type) |dest_ty|
        try sema.coerceValueToType(raw_value, dest_ty, "decl")
    else
        raw_value;
    const final_type = if (declared_type) |dest_ty|
        dest_ty
    else
        Value.typeOf(final_value, sema.intern_pool).index;

    const nav_idx = try sema.intern_pool.createNav(sema.gpa, name, name);
    sema.intern_pool.navPtr(nav_idx).resolved = .{
        .type = final_type,
        .@"align" = .none,
        .@"linksection" = .none,
        .@"addrspace" = .generic,
        .@"const" = unwrapped.kind == .@"const",
        .@"threadlocal" = unwrapped.is_threadlocal,
        .is_extern_decl = unwrapped.linkage == .@"extern",
        .value = final_value.index,
    };

    const ns = sema.intern_pool.namespacePtr(ns_idx);
    const ctx: InternPool.Namespace.NavNameContext = .{ .pool = sema.intern_pool };
    const target_map = if (unwrapped.is_pub) &ns.pub_decls else &ns.priv_decls;
    _ = try target_map.getOrPutContext(sema.gpa, nav_idx, ctx);
}

fn bindTestDecl(
    sema: *Sema,
    ns_idx: InternPool.NamespaceIndex,
    name: InternPool.NullTerminatedString,
    decl_inst: Zir.Inst.Index,
    unwrapped: std.zig.Zir.Inst.Declaration.Unwrapped,
) Error!void {
    _ = unwrapped;
    const nav_idx = try sema.intern_pool.createNav(sema.gpa, name, name);
    // Test bodies stay unevaluated until Stage 6 brings std.testing;
    // the Nav carries the name for `:test <name>` listing later.
    sema.intern_pool.navPtr(nav_idx).analysis = .{
        .namespace = ns_idx,
        .zir_index = decl_inst,
        .wanted = false,
    };
    try sema.intern_pool.namespacePtr(ns_idx).test_decls.append(sema.gpa, nav_idx);
}

fn bindAnonymousDecl(
    sema: *Sema,
    ns_idx: InternPool.NamespaceIndex,
    decl_inst: Zir.Inst.Index,
    unwrapped: std.zig.Zir.Inst.Declaration.Unwrapped,
) Error!void {
    switch (unwrapped.kind) {
        .@"comptime" => {
            const id = try sema.intern_pool.createComptimeUnit(sema.gpa, ns_idx, decl_inst);
            try sema.intern_pool.namespacePtr(ns_idx).comptime_decls.append(sema.gpa, id);
        },
        .unnamed_test => {
            // Stored alongside named tests; the namespace's test_decls
            // is name-blind so listing iterates Navs and reads the name
            // from each.
            const synthesized = try sema.intern_pool.getOrPutString(sema.gpa, "");
            const nav_idx = try sema.intern_pool.createNav(sema.gpa, synthesized, synthesized);
            sema.intern_pool.navPtr(nav_idx).analysis = .{
                .namespace = ns_idx,
                .zir_index = decl_inst,
                .wanted = false,
            };
            try sema.intern_pool.namespacePtr(ns_idx).test_decls.append(sema.gpa, nav_idx);
        },
        else => unreachable,
    }
}

/// `error_set_decl`: lower an `error{Foo, Bar}` literal. The
/// `pl_node` payload points at an `ErrorSetDecl { fields_len }`
/// followed by `fields_len` interned name handles in the Zir extra
/// arena. We intern each name into our pool's string table, then
/// `pool.internErrorSetType` sorts + dedupes the names so the
/// resulting `Index` is canonical for the set's membership.
///
/// Compiler reference: src/Sema.zig:zirErrorSetDecl (~2990).
fn evalErrorSetDecl(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.ErrorSetDecl, pl_node.payload_index);
    const fields_len = extra.data.fields_len;

    const names = try sema.gpa.alloc(InternPool.NullTerminatedString, fields_len);
    defer sema.gpa.free(names);

    var extra_index: u32 = @intCast(extra.end);
    for (names) |*slot| {
        const zir_name_idx: std.zig.Zir.NullTerminatedString = @enumFromInt(sema.zir.extra[extra_index]);
        const name_bytes = sema.zir.nullTerminatedString(zir_name_idx);
        slot.* = try sema.intern_pool.getOrPutString(sema.gpa, name_bytes);
        extra_index += 1;
    }

    const ty_idx = try sema.intern_pool.internErrorSetType(names);
    return .{ .index = ty_idx };
}

/// `error_value`: lower an `error.Foo` literal. The `str_tok` payload
/// is the error's identifier. We intern the name globally (shared
/// across all sets containing it), build a singleton `error{Foo}`
/// type for the most precise value type, and intern the `err` value
/// pointing at it. Mirrors compiler `zirErrorValue` (~7578).
fn evalErrorValue(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const data = sema.zir.instructions.items(.data)[@intFromEnum(inst)].str_tok;
    const name_bytes = data.get(sema.zir);
    const name = try sema.intern_pool.getOrPutString(sema.gpa, name_bytes);
    const ty_idx = try sema.intern_pool.singletonErrorSetType(name);
    const err_idx = try sema.intern_pool.internErr(.{ .ty = ty_idx, .name = name });
    return .{ .index = err_idx };
}

/// `error_union_type`: `pl_node + Bin` whose lhs is the error-set
/// type expression and rhs is the payload type expression. Both
/// must resolve to types; `resolveDestType` enforces this. Mirrors
/// the compiler's handler (`src/Sema.zig:zirErrorUnionType`).
fn evalErrorUnionType(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    const bin = sema.zir.extraData(Zir.Inst.Bin, pl_node.payload_index).data;
    assert(bin.lhs != .none);
    assert(bin.rhs != .none);

    const error_set = try sema.resolveDestType(bin.lhs, "error_union_type");
    const payload = try sema.resolveDestType(bin.rhs, "error_union_type");

    const ty_idx = try sema.intern_pool.internErrorUnionType(.{
        .error_set_type = error_set,
        .payload_type = payload,
    });
    return .{ .index = ty_idx };
}

/// `err_union_code operand`: extract the error code from an error
/// union value. The operand must be an `error_union` Key whose
/// variant is `.err_name`. The result is an `err` value of the
/// union's error-set type. Mirrors the compiler's
/// `zirErrUnionCode` / `analyzeErrUnionCode` (`src/Sema.zig:8247`).
/// On a `.payload` operand the compiler emits `unreachable_value`
/// at compile time; we surface a diagnostic since hitting it via
/// REPL input means the AstGen lowering guaranteed the wrong shape.
fn evalErrUnionCode(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    assert(un_node.operand != .none);

    const ip = sema.intern_pool;
    const operand_value = try sema.resolveRef(un_node.operand);
    const operand_key = ip.indexToKey(operand_value.index);
    if (operand_key != .error_union) {
        try sema.writer.print("err_union_code: operand is not an error union\n", .{});
        return error.AnalysisFail;
    }

    const eu_type = ip.indexToKey(operand_key.error_union.ty).error_union_type;
    switch (operand_key.error_union.val) {
        .err_name => |name| {
            const err_idx = try ip.internErr(.{ .ty = eu_type.error_set_type, .name = name });
            return .{ .index = err_idx };
        },
        .payload => {
            try sema.writer.print("err_union_code: operand carries a payload, not an error\n", .{});
            return error.AnalysisFail;
        },
    }
}

/// `err_union_payload_unsafe operand`: extract the payload from an
/// error union value, asserting the variant is `.payload`. "Unsafe"
/// in the compiler means "the runtime safety check was already done
/// by an earlier branch"; at REPL eval time we work with concrete
/// values and can surface a diagnostic if the variant is `.err_name`
/// rather than crashing. Mirrors `zirErrUnionPayload`
/// (`src/Sema.zig:8092`).
fn evalErrUnionPayloadUnsafe(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    assert(un_node.operand != .none);

    const operand_value = try sema.resolveRef(un_node.operand);
    const operand_key = sema.intern_pool.indexToKey(operand_value.index);
    if (operand_key != .error_union) {
        try sema.writer.print("err_union_payload: operand is not an error union\n", .{});
        return error.AnalysisFail;
    }

    switch (operand_key.error_union.val) {
        .payload => |payload_idx| return .{ .index = payload_idx },
        .err_name => {
            try sema.writer.print("err_union_payload: operand carries an error, not a payload\n", .{});
            return error.AnalysisFail;
        },
    }
}

/// `is_non_err operand`: boolean predicate, true IFF the union's
/// variant is `.payload`. Used by AstGen-lowered control flow
/// (`if (x) |v| ... else |e| ...` and friends). Mirrors
/// `zirIsNonErr` (`src/Sema.zig:17225`).
fn evalIsNonErr(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    assert(un_node.operand != .none);

    const operand_value = try sema.resolveRef(un_node.operand);
    const operand_key = sema.intern_pool.indexToKey(operand_value.index);
    if (operand_key != .error_union) {
        try sema.writer.print("is_non_err: operand is not an error union\n", .{});
        return error.AnalysisFail;
    }

    return switch (operand_key.error_union.val) {
        .payload => Value.bool_true,
        .err_name => Value.bool_false,
    };
}

fn reportUnsupportedTag(sema: *Sema, comptime tag: Zir.Inst.Tag) Error!?Value {
    try sema.writer.print("unsupported ZIR instruction: {s}\n", .{@tagName(tag)});
    return error.AnalysisFail;
}
