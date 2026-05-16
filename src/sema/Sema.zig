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
    UnsupportedZirInst,
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
            else => {
                if (try sema.evalInst(inst, tag)) |result| {
                    try sema.results.put(sema.gpa, inst, result);
                }
            },
        }
    }
    try sema.writer.writeAll("internal error: body did not terminate with break\n");
    return error.UnsupportedZirInst;
}

fn evalInst(sema: *Sema, inst: Zir.Inst.Index, tag: Zir.Inst.Tag) Error!?Value {
    return switch (tag) {
        .int => sema.evalInt(inst),
        .add => sema.evalBinaryArith(inst, .add),
        .sub => sema.evalBinaryArith(inst, .sub),
        .mul => sema.evalBinaryArith(inst, .mul),
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

fn evalPassthroughUnNode(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const operand = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node.operand;
    return try sema.resolveRef(operand);
}

/// Integer add/sub/mul share the same operand shape (`pl_node` + `Bin`) and
/// the same comptime_int-only first cut. Each routes to the matching kernel
/// in `arith.zig`; fixed-width and float dispatch land with their coercion
/// handlers.
///
/// Compiler reference: src/Sema.zig:zirArithmetic ->
/// src/Sema/arith.zig:{add,sub,mul} -> {add,sub,mul}Scalar -> int{Add,Sub,Mul}.
const BinaryArithOp = enum { add, sub, mul };

fn evalBinaryArith(sema: *Sema, inst: Zir.Inst.Index, op: BinaryArithOp) Error!?Value {
    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    const bin = sema.zir.extraData(Zir.Inst.Bin, pl_node.payload_index).data;

    const op_name: []const u8 = @tagName(op);
    const lhs = try sema.resolveComptimeInt(bin.lhs, op_name);
    const rhs = try sema.resolveComptimeInt(bin.rhs, op_name);

    const idx = switch (op) {
        .add => try arith.internAdd(sema.gpa, sema.intern_pool, lhs, rhs),
        .sub => try arith.internSub(sema.gpa, sema.intern_pool, lhs, rhs),
        .mul => try arith.internMul(sema.gpa, sema.intern_pool, lhs, rhs),
    };
    return .{ .index = idx };
}

/// Compiler reference: src/Sema.zig:zirNegate -> src/Sema/arith.zig:negate.
/// AstGen lowers `-x` as `negate(x)`; constant-folded literals like `-1`
/// instead come through as `Ref.negative_one` and never reach here.
fn evalNegate(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    const operand = try sema.resolveComptimeInt(un_node.operand, "negate");
    const idx = try arith.internNegate(sema.gpa, sema.intern_pool, operand);
    return .{ .index = idx };
}

/// Resolve a Ref and require it to be a `comptime_int` value. Reports the
/// op-specific diagnostic and returns `error.UnsupportedZirInst` for any
/// non-integer or fixed-width-int operand until those land.
fn resolveComptimeInt(
    sema: *Sema,
    ref: Zir.Inst.Ref,
    op_name: []const u8,
) Error!std.math.big.int.Const {
    const value = try sema.resolveRef(ref);
    const key = sema.intern_pool.get(value.index);
    if (key != .int_value) {
        try sema.writer.print("{s}: non-integer operand not yet supported\n", .{op_name});
        return error.UnsupportedZirInst;
    }
    if (key.int_value.ty != .comptime_int_type) {
        try sema.writer.print("{s}: fixed-width int arithmetic not yet supported\n", .{op_name});
        return error.UnsupportedZirInst;
    }
    return key.int_value.value;
}

fn resolveRef(sema: *Sema, ref: Zir.Inst.Ref) Error!Value {
    assert(ref != .none);

    if (ref.toIndex()) |inst_idx| {
        if (sema.results.get(inst_idx)) |value| return value;
        try sema.writer.print(
            "internal error: unresolved instruction ref %{d}\n",
            .{@intFromEnum(inst_idx)},
        );
        return error.UnsupportedZirInst;
    }

    return wellKnownRefToValue(ref) orelse {
        try sema.writer.print("unsupported ZIR ref: {s}\n", .{@tagName(ref)});
        return error.UnsupportedZirInst;
    };
}

/// Maps a static ZIR `Ref` (one of the well-known constants) to the
/// corresponding interned Value. The full Ref→InternPool.Index identity
/// the compiler relies on requires Key variants we haven't ported yet
/// (ptr_type, vector_type, the convenience pointer/slice shapes); we map
/// only the variants reachable from currently-supported handlers.
fn wellKnownRefToValue(ref: Zir.Inst.Ref) ?Value {
    return switch (ref) {
        .zero => .{ .index = .zero },
        .one => .{ .index = .one },
        .negative_one => .{ .index = .negative_one },
        .void_value => .{ .index = .void_value },
        .bool_true => .{ .index = .bool_true },
        .bool_false => .{ .index = .bool_false },
        .null_value => .{ .index = .null_value },
        .undef => .{ .index = .undef },
        else => null,
    };
}

fn reportUnsupportedTag(sema: *Sema, comptime tag: Zir.Inst.Tag) Error!?Value {
    try sema.writer.print("unsupported ZIR instruction: {s}\n", .{@tagName(tag)});
    return error.UnsupportedZirInst;
}
