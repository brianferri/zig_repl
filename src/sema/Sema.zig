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

const Sema = @This();

pub const Error = Allocator.Error || std.Io.Writer.Error || error{
    AnalysisFail,
};

/// The REPL's `front/InputShape` wraps every expression line as
/// `const __repl_input = (<expr>);`, so Sema always looks for this decl in
/// the root struct to find the body to evaluate.
const repl_input_decl_name: []const u8 = "__repl_input";

gpa: Allocator,
intern_pool: *InternPool,
zir: Zir,
writer: *std.Io.Writer,
/// Per-instruction Value results within the body currently being walked.
/// Cleared between bodies; not shared across REPL inputs.
results: std.AutoHashMapUnmanaged(Zir.Inst.Index, Value),

/// Walks the ZIR produced by AstGen for a single REPL line and returns its
/// resulting Value, or null when there is no `__repl_input` decl (e.g. raw
/// declarations whose body shape we don't yet evaluate). Diagnostics for
/// unhandled tags are written to `writer`.
pub fn analyze(
    gpa: Allocator,
    intern_pool: *InternPool,
    zir: Zir,
    writer: *std.Io.Writer,
) Error!?Value {
    assert(!zir.hasCompileErrors());
    assert(@intFromPtr(intern_pool) != 0);
    assert(zir.instructions.len > 0);

    var sema: Sema = .{
        .gpa = gpa,
        .intern_pool = intern_pool,
        .zir = zir,
        .writer = writer,
        .results = .empty,
    };
    defer sema.results.deinit(gpa);

    const body = findReplInputBody(zir) orelse return null;
    return try sema.evalBody(body);
}

fn findReplInputBody(zir: Zir) ?[]const Zir.Inst.Index {
    for (zir.typeDecls(.main_struct_inst)) |decl_inst| {
        const unwrapped = zir.getDeclaration(decl_inst);
        if (unwrapped.name == .empty) continue;
        const name = zir.nullTerminatedString(unwrapped.name);
        if (std.mem.eql(u8, name, repl_input_decl_name)) {
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
        .sub,
        .mul,
        .div,
        .div_exact,
        .div_floor,
        .div_trunc,
        .mod,
        .rem,
        => sema.evalBinaryArith(inst, tag),
        .bit_and, .bit_or, .xor => sema.evalBitwise(inst, tag),
        .shl => sema.evalShift(inst, "shl", arith.internShl),
        .shr => sema.evalShift(inst, "shr", arith.internShr),
        .typeof_log2_int_type => sema.evalTypeofLog2IntType(inst),
        .as_node, .as_shift_operand => sema.evalAsNode(inst),
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
        .negate => sema.evalNegate(inst),
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
/// `string_bytes` upstream so we could reinterpret in place — neither
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
/// `BigIntConst.toFloat(f128, .nearest_even)` — peer-type resolution as
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

    const lhs_is_cti = lhs_key == .int and lhs_key.int.ty == .comptime_int_type;
    const rhs_is_cti = rhs_key == .int and rhs_key.int.ty == .comptime_int_type;
    const lhs_is_ctf = lhs_key == .float and lhs_key.float.ty == .comptime_float_type;
    const rhs_is_ctf = rhs_key == .float and rhs_key.float.ty == .comptime_float_type;

    if (lhs_is_cti and rhs_is_cti) {
        return sema.evalBinaryArithInt(tag, lhs_key.int, rhs_key.int);
    }
    if ((lhs_is_cti or lhs_is_ctf) and (rhs_is_cti or rhs_is_ctf)) {
        const lhs_f: InternPool.Key.Float = if (lhs_is_ctf) lhs_key.float else comptimeIntToComptimeFloat(lhs_key.int);
        const rhs_f: InternPool.Key.Float = if (rhs_is_ctf) rhs_key.float else comptimeIntToComptimeFloat(rhs_key.int);
        return sema.evalBinaryArithFloat(tag, lhs_f, rhs_f);
    }

    if ((lhs_key == .int or lhs_key == .float) and (rhs_key == .int or rhs_key == .float)) {
        try sema.writer.print("{s}: fixed-width numeric arithmetic not yet supported\n", .{op_name});
    } else {
        try sema.writer.print("{s}: non-numeric or mismatched operands\n", .{op_name});
    }
    return error.AnalysisFail;
}

/// Peer-type promotion `comptime_int -> comptime_float`. The pool stores
/// `comptime_float` as f128, so we round the big-int to f128 nearest-even
/// — IEEE-754 default — matching the compiler's behavior for the same
/// mixed-arithmetic case.
fn comptimeIntToComptimeFloat(int: InternPool.Key.Int) InternPool.Key.Float {
    assert(int.ty == .comptime_int_type);
    var space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
    const big = int.storage.toBigInt(&space);
    const promoted = big.toFloat(f128, .nearest_even);
    return .{
        .ty = .comptime_float_type,
        .storage = .{ .f128 = promoted[0] },
    };
}

fn evalBinaryArithInt(
    sema: *Sema,
    tag: Zir.Inst.Tag,
    lhs_int: InternPool.Key.Int,
    rhs_int: InternPool.Key.Int,
) Error!?Value {
    assert(lhs_int.ty == .comptime_int_type);
    assert(rhs_int.ty == .comptime_int_type);

    var lhs_space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
    var rhs_space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
    const lhs = lhs_int.storage.toBigInt(&lhs_space);
    const rhs = rhs_int.storage.toBigInt(&rhs_space);

    const ip = sema.intern_pool;
    const gpa = sema.gpa;
    const idx = switch (tag) {
        .add => try arith.internAdd(gpa, ip, lhs, rhs),
        .sub => try arith.internSub(gpa, ip, lhs, rhs),
        .mul => try arith.internMul(gpa, ip, lhs, rhs),
        // ZIR `div` is the generic `/` operator; for comptime_int operands
        // Zig defines it as truncation toward zero, so route to the same
        // kernel as `@divTrunc`. `div_exact` / `div_floor` are the
        // builtins with their own kernels.
        .div, .div_trunc => try sema.unwrapDivResult(arith.internDivTrunc(gpa, ip, lhs, rhs), "/"),
        .div_exact => try sema.unwrapDivResult(arith.internDivExact(gpa, ip, lhs, rhs), "@divExact"),
        .div_floor => try sema.unwrapDivResult(arith.internDivFloor(gpa, ip, lhs, rhs), "@divFloor"),
        .mod => try sema.unwrapDivResult(arith.internMod(gpa, ip, lhs, rhs), "@mod"),
        .rem => try sema.unwrapDivResult(arith.internRem(gpa, ip, lhs, rhs), "@rem"),
        else => unreachable,
    };
    return .{ .index = idx };
}

fn evalBinaryArithFloat(
    sema: *Sema,
    tag: Zir.Inst.Tag,
    lhs_float: InternPool.Key.Float,
    rhs_float: InternPool.Key.Float,
) Error!?Value {
    assert(lhs_float.ty == .comptime_float_type);
    assert(rhs_float.ty == .comptime_float_type);

    const lhs = lhs_float.storage.f128;
    const rhs = rhs_float.storage.f128;
    const ip = sema.intern_pool;
    const idx = switch (tag) {
        .add => try arith.internFloatAdd(ip, lhs, rhs),
        .sub => try arith.internFloatSub(ip, lhs, rhs),
        .mul => try arith.internFloatMul(ip, lhs, rhs),
        .div => try sema.unwrapDivResult(arith.internFloatDiv(ip, lhs, rhs), "/"),
        .div_exact => try sema.unwrapDivResult(arith.internFloatDivExact(ip, lhs, rhs), "@divExact"),
        .div_floor => try sema.unwrapDivResult(arith.internFloatDivFloor(ip, lhs, rhs), "@divFloor"),
        .div_trunc => try sema.unwrapDivResult(arith.internFloatDivTrunc(ip, lhs, rhs), "@divTrunc"),
        .mod => try sema.unwrapDivResult(arith.internFloatMod(ip, lhs, rhs), "@mod"),
        .rem => try sema.unwrapDivResult(arith.internFloatRem(ip, lhs, rhs), "@rem"),
        else => unreachable,
    };
    return .{ .index = idx };
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
/// it breaks with. Sema's existing `evalBody` already does this — `block`
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
/// `evalBody` because it always transfers control — never falls through.
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
/// short-circuit doesn't fire. First nested-body path in Sema — the body
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
///   * identity (operand type == dest type) — free passthrough.
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

    const dest_value = try sema.resolveRef(as.dest_type);
    const dest_key = sema.intern_pool.indexToKey(dest_value.index);
    // The destination may be either a `type_value` wrapping a type
    // (the dynamic case for synthesized types), or the bare type slot
    // itself when it came in via a well-known `Ref.X_type` (which Sema
    // treats as the value-of-type-type identifying that slot directly).
    const dest_type_index: InternPool.Index = switch (dest_key) {
        .type_value => |t| t,
        .simple_type, .int_type => dest_value.index,
        else => {
            try sema.writer.writeAll("as: destination is not a type\n");
            return error.AnalysisFail;
        },
    };

    const operand_value = try sema.resolveRef(as.operand);
    const operand_type = Value.typeOf(operand_value, sema.intern_pool);

    // Identity coercion is always safe.
    if (dest_type_index == operand_type.index) return operand_value;

    // comptime_int -> fixed-width int: range-check then re-intern with the
    // new type. The pool's aliasing guard handles the case where the
    // BigIntConst still references the operand's interned limbs.
    if (operand_type.index == .comptime_int_type) {
        const dest_key2 = sema.intern_pool.indexToKey(dest_type_index);
        if (dest_key2 == .int_type) {
            return try sema.coerceComptimeIntToFixedInt(
                operand_value,
                dest_type_index,
                dest_key2.int_type,
            );
        }
    }

    // comptime_float -> fixed-width float: narrow the stored f128 to the
    // destination width. f64 / f32 / f16 lose precision but never error
    // (the language permits the cast); f80 / f128 are lossless.
    if (operand_type.index == .comptime_float_type and isFixedWidthFloatType(dest_type_index)) {
        return try sema.coerceComptimeFloatToFixedFloat(operand_value, dest_type_index);
    }

    try sema.writer.writeAll("as: this coercion is not yet supported\n");
    return error.AnalysisFail;
}

fn isFixedWidthFloatType(ty: InternPool.Index) bool {
    return switch (ty) {
        .f16_type, .f32_type, .f64_type, .f80_type, .f128_type => true,
        else => false,
    };
}

fn coerceComptimeFloatToFixedFloat(
    sema: *Sema,
    operand_value: Value,
    dest_type_index: InternPool.Index,
) Error!Value {
    assert(dest_type_index != .none);
    assert(isFixedWidthFloatType(dest_type_index));

    const op_key = sema.intern_pool.indexToKey(operand_value.index);
    assert(op_key == .float);
    assert(op_key.float.ty == .comptime_float_type);

    const v: f128 = op_key.float.storage.f128;
    const storage: InternPool.Key.Float.Storage = switch (dest_type_index) {
        .f16_type => .{ .f16 = @floatCast(v) },
        .f32_type => .{ .f32 = @floatCast(v) },
        .f64_type => .{ .f64 = @floatCast(v) },
        .f80_type => .{ .f80 = @floatCast(v) },
        .f128_type => .{ .f128 = v },
        else => unreachable,
    };
    const idx = try sema.intern_pool.internFloat(.{
        .ty = dest_type_index,
        .storage = storage,
    });
    return .{ .index = idx };
}

fn coerceComptimeIntToFixedInt(
    sema: *Sema,
    operand_value: Value,
    dest_type_index: InternPool.Index,
    dest_int_type: std.builtin.Type.Int,
) Error!Value {
    assert(@intFromPtr(sema) != 0);
    assert(dest_type_index != .none);

    const op_key = sema.intern_pool.indexToKey(operand_value.index);
    assert(op_key == .int);
    assert(op_key.int.ty == .comptime_int_type);

    var space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
    const big = op_key.int.storage.toBigInt(&space);
    if (!big.fitsInTwosComp(dest_int_type.signedness, dest_int_type.bits)) {
        try sema.writer.print(
            "@as: value does not fit in {c}{d}\n",
            .{ @as(u8, switch (dest_int_type.signedness) {
                .signed => 'i',
                .unsigned => 'u',
            }), dest_int_type.bits },
        );
        return error.AnalysisFail;
    }

    const idx = try sema.intern_pool.internIntValue(dest_type_index, big);
    return .{ .index = idx };
}

/// `shl / shr`. Same operand shape as the other binary ops, but `rhs` is a
/// shift amount that must fit in `usize` and be non-negative — the kernel's
/// stdlib-named `ConvertError.NegativeIntoUnsigned` /
/// `ConvertError.TargetTooSmall` flow through here and become runtime-style
/// diagnostics + `AnalysisFail`.
///
/// `shl_exact` / `shr_exact` land alongside fixed-width int support — the
/// "no bits lost" check is meaningful only when the operand has a width.
///
/// Compiler reference: src/Sema.zig:zirShl / zirShr.
fn evalShift(
    sema: *Sema,
    inst: Zir.Inst.Index,
    op_name: []const u8,
    kernel: ShiftKernel,
) Error!?Value {
    assert(@intFromPtr(sema) != 0);
    assert(@intFromEnum(inst) < sema.zir.instructions.len);
    assert(op_name.len > 0);

    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    const bin = sema.zir.extraData(Zir.Inst.Bin, pl_node.payload_index).data;
    assert(bin.lhs != .none);
    assert(bin.rhs != .none);

    var lhs_space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
    var rhs_space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
    const lhs = try sema.resolveComptimeInt(bin.lhs, op_name, &lhs_space);
    const rhs = try sema.resolveComptimeInt(bin.rhs, op_name, &rhs_space);

    const idx = kernel(sema.gpa, sema.intern_pool, lhs, rhs) catch |err| switch (err) {
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
            try sema.writer.print("error: {s}: shift amount exceeds {d} bits\n", .{ op_name, arith.max_shift_bits });
            return error.AnalysisFail;
        },
    };
    return .{ .index = idx };
}

/// `bit_and / bit_or / xor`. Same operand shape as `evalBinaryArith`
/// (pl_node + Bin); routes to a per-op `arith.internBit*` kernel keyed
/// on the captured Zir.Inst.Tag.
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
    var lhs_space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
    var rhs_space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
    const lhs = try sema.resolveComptimeInt(bin.lhs, op_name, &lhs_space);
    const rhs = try sema.resolveComptimeInt(bin.rhs, op_name, &rhs_space);

    const ip = sema.intern_pool;
    const gpa = sema.gpa;
    const idx = switch (tag) {
        .bit_and => try arith.internBitAnd(gpa, ip, lhs, rhs),
        .bit_or => try arith.internBitOr(gpa, ip, lhs, rhs),
        .xor => try arith.internXor(gpa, ip, lhs, rhs),
        else => unreachable,
    };
    return .{ .index = idx };
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

    const lhs_is_cti = lhs_key == .int and lhs_key.int.ty == .comptime_int_type;
    const rhs_is_cti = rhs_key == .int and rhs_key.int.ty == .comptime_int_type;
    const lhs_is_ctf = lhs_key == .float and lhs_key.float.ty == .comptime_float_type;
    const rhs_is_ctf = rhs_key == .float and rhs_key.float.ty == .comptime_float_type;

    if (lhs_is_cti and rhs_is_cti) {
        var lhs_space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
        var rhs_space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
        const lhs = lhs_key.int.storage.toBigInt(&lhs_space);
        const rhs = rhs_key.int.storage.toBigInt(&rhs_space);
        const result = arith.compareInt(lhs, rhs, op);
        return .{ .index = if (result) .bool_true else .bool_false };
    }
    if ((lhs_is_cti or lhs_is_ctf) and (rhs_is_cti or rhs_is_ctf)) {
        const lhs_f: InternPool.Key.Float = if (lhs_is_ctf) lhs_key.float else comptimeIntToComptimeFloat(lhs_key.int);
        const rhs_f: InternPool.Key.Float = if (rhs_is_ctf) rhs_key.float else comptimeIntToComptimeFloat(rhs_key.int);
        const result = arith.compareFloat(lhs_f.storage.f128, rhs_f.storage.f128, op);
        return .{ .index = if (result) .bool_true else .bool_false };
    }

    if ((lhs_key == .int or lhs_key == .float) and (rhs_key == .int or rhs_key == .float)) {
        try sema.writer.print("{s}: fixed-width numeric comparison not yet supported\n", .{op_name});
    } else {
        try sema.writer.print("{s}: non-numeric or mismatched operands\n", .{op_name});
    }
    return error.AnalysisFail;
}

/// Compiler reference: src/Sema.zig:zirNegate -> src/Sema/arith.zig:negate.
/// AstGen lowers `-x` as `negate(x)`; constant-folded literals like `-1` /
/// `-1.5` instead come through as well-known Refs or as a single signed
/// literal and never reach here. Routes to the int or float kernel by
/// operand type.
fn evalNegate(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromPtr(sema) != 0);
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    assert(un_node.operand != .none);

    const ip = sema.intern_pool;
    const operand_value = try sema.resolveRef(un_node.operand);
    const operand_key = ip.indexToKey(operand_value.index);

    if (operand_key == .float) {
        if (operand_key.float.ty != .comptime_float_type) {
            try sema.writer.writeAll("negate: fixed-width float negation not yet supported\n");
            return error.AnalysisFail;
        }
        const idx = try arith.internFloatNegate(ip, operand_key.float.storage.f128);
        assert(idx != .none);
        return .{ .index = idx };
    }

    if (operand_key == .int) {
        if (operand_key.int.ty != .comptime_int_type) {
            try sema.writer.writeAll("negate: fixed-width int negation not yet supported\n");
            return error.AnalysisFail;
        }
        var space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
        const operand = operand_key.int.storage.toBigInt(&space);
        const idx = try arith.internNegate(sema.gpa, ip, operand);
        assert(idx != .none);
        return .{ .index = idx };
    }

    try sema.writer.writeAll("negate: non-numeric operand\n");
    return error.AnalysisFail;
}

/// Resolve a Ref and require it to be a `comptime_int` value. Reports the
/// op-specific diagnostic and returns `error.AnalysisFail` for any
/// non-integer or fixed-width-int operand until those land.
fn resolveComptimeInt(
    sema: *Sema,
    ref: Zir.Inst.Ref,
    op_name: []const u8,
    space: *InternPool.Key.Int.Storage.BigIntSpace,
) Error!std.math.big.int.Const {
    assert(@intFromPtr(sema) != 0);
    assert(ref != .none);
    assert(op_name.len > 0);

    const value = try sema.resolveRef(ref);
    assert(value.index != .none);

    const key = sema.intern_pool.indexToKey(value.index);
    if (key != .int) {
        try sema.writer.print("{s}: non-integer operand not yet supported\n", .{op_name});
        return error.AnalysisFail;
    }
    if (key.int.ty != .comptime_int_type) {
        try sema.writer.print("{s}: fixed-width int arithmetic not yet supported\n", .{op_name});
        return error.AnalysisFail;
    }
    const big = key.int.storage.toBigInt(space);
    assert(big.limbs.len > 0);
    return big;
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

    return wellKnownRefToValue(ref) orelse {
        try sema.writer.print("unsupported ZIR ref: {s}\n", .{@tagName(ref)});
        return error.AnalysisFail;
    };
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
/// Our parity is partial — the type-prefix of `Index` through
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

fn reportUnsupportedTag(sema: *Sema, comptime tag: Zir.Inst.Tag) Error!?Value {
    try sema.writer.print("unsupported ZIR instruction: {s}\n", .{@tagName(tag)});
    return error.AnalysisFail;
}
