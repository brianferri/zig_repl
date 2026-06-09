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
const Type = @import("Type.zig");
const arith = @import("arith.zig");
const InputShape = @import("../front/InputShape.zig");
const Session = @import("../Session.zig");

const Sema = @This();

pub const Error = Allocator.Error || std.Io.Writer.Error || error{
    AnalysisFail,
    /// Non-local control transfer from `break` / `break_inline`.
    /// The break instruction's own ZIR index is stashed in
    /// `sema.comptime_break_inst`; the receiver (`resolveInlineBody`)
    /// reads the `Zir.Inst.Break` extra payload to recover the
    /// target block_inst and the operand ref. Mirrors the compiler
    /// at src/Sema.zig:1685 (`zirBreak` arm) +
    /// src/Sema.zig:1062 (`analyzeInlineBody`).
    ComptimeBreak,
    /// Non-local control transfer from `ret_node` / `ret_load` /
    /// `ret_implicit` (the `return X;` keyword inside a function
    /// body). The value being returned lives in `sema.return_value`.
    /// `evalCall` is the receiver: catches ComptimeReturn from the
    /// resolveInlineBody on the fn body and returns the value.
    /// Mirrors src/Zcu.zig:2816 CompileError.ComptimeReturn.
    ComptimeReturn,
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
/// Bump cursor for the modeled address space `@intFromPtr` draws from. Starts
/// above zero so no alloc lands on the null address; advanced per addressed
/// alloc, rounded up to the alloc's alignment. Synthetic -- see `evalIntFromPtr`.
comptime_address_cursor: u64 = 0x1000,
/// Current lookup scope. `null` for test paths that don't construct
/// a session; REPL passes the session-root index so `evalDeclVal`
/// can resolve cross-line names via the parent chain.
namespace: ?InternPool.NamespaceIndex,
/// Populated when returning `error.ComptimeBreak`. Used to
/// communicate the break instruction up the stack to find the
/// corresponding block. The receiver reads the break's
/// `Zir.Inst.Break` extra to get the target block_inst and
/// recovers the value via `resolveRef(operand)`. Mirrors the
/// compiler's `comptime_break_inst` field (src/Sema.zig:81).
comptime_break_inst: Zir.Inst.Index = undefined,
/// Backwards-branch quota, mirroring the compiler at
/// src/Sema.zig:77. Each `repeat` / `repeat_inline` increments
/// `branch_count`; when it exceeds `branch_quota`, Sema fails with
/// the same "evaluation exceeded N backwards branches" diagnostic
/// AstGen emits. The user-facing knob is `@setEvalBranchQuota`
/// (lands with broader builtin coverage).
branch_quota: u32 = default_branch_quota,
branch_count: u32 = 0,
/// Value carried by an in-flight `error.ComptimeReturn`. Set by
/// the `.ret_node` / `.ret_load` / `.ret_implicit` arms of
/// evalBody; consumed by `evalCall`'s catch. Garbage outside
/// that transfer.
return_value: Value = undefined,
/// Declared return type of the function whose body is being evaluated, or
/// `.none` at the top level. `evalCall` sets it around the body so the
/// `ret_type` instruction (which AstGen emits to reference a non-trivial
/// return type, e.g. `u23`) resolves to it. Mirrors `sema.fn_ret_ty` in
/// src/Sema.zig.
fn_ret_ty: InternPool.Index = .none,
/// Accumulator for the comptime-known provenance of the instruction currently
/// being evaluated: `resolveRef` ANDs in each operand it returns, and the eval
/// loop snapshots it per instruction (reset to `true` around each `evalInst`)
/// to fold into the result's `Value.is_comptime`. This is how runtime-ness
/// propagates -- an instruction with any runtime operand yields a runtime
/// value -- without every op having to thread it by hand.
operand_comptime: bool = true,
/// Read-only view of every previously-analysed line's ZIR. An entry is
/// callable as a fn body when a Func value's `source_zir_id` references
/// its index. Populated by the REPL driver; tests can leave this empty
/// since they don't exercise cross-line calls.
line_zir: []const Zir = &.{},
/// The id THIS analyze pass's ZIR will have if registered. Used
/// at evalFunc-intern time so the resulting Func's
/// `source_zir_id` resolves correctly on future cross-line
/// lookups. evalCall compares against `func.source_zir_id` to
/// decide whether to swap `sema.zir` for the body eval.
current_zir_id: u32 = 0,
/// Currently-active `Block`. Mirrors the compiler's
/// `block: *Block` parameter threaded through every handler in
/// `src/Sema.zig`; we keep it on Sema rather than in every
/// signature since the REPL has no nested fn definitions or
/// runtime-Block lowering that would require save/restore
/// across handler frames. When those land, the compiler's
/// threading pattern lifts here.
block: *Block = undefined,
/// Fully-qualified name of the declaration whose value body is being
/// evaluated, used to name a container type declared in it
/// (`const P = struct {...}` -> the struct is named after `P`'s fqn,
/// `repl.P`). Mirrors the compiler's `block.type_name_ctx`; our flat
/// REPL has one enclosing declaration at a time, so `bindValueDecl`
/// sets it around the value-body eval.
type_name_ctx: InternPool.NullTerminatedString = .empty,

pub const default_branch_quota: u32 = 1000;

/// Mirrors the compiler's `Sema.Block` (src/Sema.zig). Today
/// only `params` is populated -- the other compiler fields
/// (label, instructions, runtime_*, namespace overrides,
/// comptime_reason, etc.) land alongside their dependent
/// handlers. `params` accumulates `.param` / `.param_comptime`
/// instructions seen during body walking, drained by
/// `evalFunc` when the matching `.func` instruction lands.
pub const Block = struct {
    params: std.ArrayListUnmanaged(Param) = .empty,

    pub fn deinit(self: *Block, gpa: std.mem.Allocator) void {
        self.params.deinit(gpa);
    }

    /// Mirrors `Block.Param` in the compiler. `name` is omitted
    /// since fn types don't carry param names; bare-decl
    /// rendering will surface them via the AST source when
    /// needed.
    pub const Param = struct {
        ty: InternPool.Index,
        is_comptime: bool,
    };
};

pub const ComptimeAlloc = struct {
    val: Value,
    is_const: bool,
    /// A synthetic address in `Sema`'s modeled address space, assigned lazily
    /// on the first `@intFromPtr`, then stable for the slot. `null` until then.
    /// The compiler has no comptime address (it defers `@intFromPtr` of a
    /// comptime alloc to a runtime op); this is a REPL extension so alignment
    /// is observable -- see `evalIntFromPtr`.
    address: ?u64 = null,
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
///
/// Session-owned state (gpa, intern_pool, root_namespace,
/// line_zir) is read straight off `session`. Per-call inputs
/// (the ZIR to analyse + the diagnostic writer) are explicit
/// parameters. `current_zir_id` is derived as
/// `session.line_zir.items.len` -- the slot THIS pass's ZIR
/// will occupy once committed by the REPL driver after a
/// successful analyze.
pub fn analyze(session: *Session, zir: Zir, writer: *std.Io.Writer) Error!?Value {
    const gpa = session.gpa;
    const intern_pool = session.intern_pool;
    const namespace = session.root_namespace;
    // Zir may carry compile-error items that the front-end Pipeline
    // classifies as non-actionable (see `front/ZirErrors.zig`).
    // Pipeline gates Sema entry via `hasZirErrors`; Sema itself
    // walks only the `__repl_input` body (or the namespace
    // bindDecls path) and is unaffected by the suppressed items, so
    // the stronger `!hasCompileErrors()` assertion has been
    // intentionally relaxed.
    assert(zir.instructions.len > 0);

    var top_block: Block = .{};
    defer top_block.deinit(gpa);

    var sema: Sema = .{
        .gpa = gpa,
        .intern_pool = intern_pool,
        .zir = zir,
        .writer = writer,
        .results = .empty,
        .comptime_allocs = .empty,
        .namespace = namespace,
        .block = &top_block,
        .line_zir = session.line_zir.items,
        .current_zir_id = @intCast(session.line_zir.items.len),
    };
    defer sema.results.deinit(gpa);
    defer sema.comptime_allocs.deinit(gpa);

    // Seed the naming context with the root namespace's own name, so a
    // type declared at session scope (e.g. an anonymous `struct {...}` in
    // an expression, which never passes through `bindValueDecl`) still
    // qualifies under `repl`. Mirrors the compiler seeding a file block's
    // `type_name_ctx` to the file-root name.
    sema.type_name_ctx = try intern_pool.namespaceName(gpa, namespace);

    if (findReplInputBody(zir)) |bound| {
        return try sema.resolveInlineBody(bound.body, bound.decl_inst);
    }
    try sema.bindDecls();
    return null;
}

const ReplInputBody = struct {
    decl_inst: Zir.Inst.Index,
    body: []const Zir.Inst.Index,
};

fn findReplInputBody(zir: Zir) ?ReplInputBody {
    for (zir.typeDecls(.main_struct_inst)) |decl_inst| {
        const unwrapped = zir.getDeclaration(decl_inst);
        if (unwrapped.name == .empty) continue;
        const name = zir.nullTerminatedString(unwrapped.name);
        if (std.mem.eql(u8, name, InputShape.expression_decl_name)) {
            // AstGen's wrapping `break_inline` for the decl body
            // targets the declaration instruction itself.
            return .{ .decl_inst = decl_inst, .body = unwrapped.value_body orelse return null };
        }
    }
    return null;
}

/// Walk a ZIR body, evaluating each instruction. Mirrors the
/// compiler's `analyzeBodyInner` (`src/Sema.zig:1125`):
///
///   * `while (true)` -- no `i < body.len` upper bound. The only
///     exit is `return` from a terminator arm. AstGen guarantees
///     every body ends in a `noreturn`-class instruction
///     (`break_inline` / `condbr` / etc.), so the loop ALWAYS
///     terminates via a return.
///   * `assert(i < body.len)` at the top -- fast crash on
///     malformed input rather than UB from out-of-bounds indexing.
///   * `.repeat` / `.repeat_inline`: `i = 0; continue;` to restart
///     at the body's first instruction, gated by
///     `emitBackwardBranch` which enforces `branch_quota` exactly
///     as the compiler does (src/Sema.zig:1698).
fn evalBody(sema: *Sema, body: []const Zir.Inst.Index) Error!Value {
    assert(body.len > 0);

    const tags = sema.zir.instructions.items(.tag);

    var i: u32 = 0;
    while (true) {
        assert(i < body.len);
        const inst = body[i];
        const tag = tags[@intFromEnum(inst)];
        switch (tag) {
            .break_inline, .@"break" => {
                sema.comptime_break_inst = inst;
                return error.ComptimeBreak;
            },
            .condbr, .condbr_inline => return sema.evalCondbr(inst),
            .repeat, .repeat_inline => {
                try sema.emitBackwardBranch();
                i = 0;
                continue;
            },
            // `return X;` keyword inside a fn body. ret_node /
            // ret_load read un_node; ret_implicit reads un_tok
            // (no source-node offset since AstGen emits it
            // implicitly at fn-body end). All three stash the
            // resolved value in sema.return_value and raise
            // ComptimeReturn for evalCall's catch.
            .ret_node => {
                const operand = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node.operand;
                sema.return_value = try sema.resolveRef(operand);
                return error.ComptimeReturn;
            },
            .ret_implicit => {
                const operand = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_tok.operand;
                sema.return_value = try sema.resolveRef(operand);
                return error.ComptimeReturn;
            },
            .ret_load => {
                const operand = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node.operand;
                const ptr = try sema.resolveRef(operand);
                sema.return_value = try sema.loadValue(ptr);
                return error.ComptimeReturn;
            },
            // AstGen has already done the LIFO scheduling: defers are
            // emitted at the textual end of each block in reverse
            // declaration order via `genDefers` (AstGen.zig ~2986).
            // Errdefers share this tag -- they're distinguished only
            // by AstGen emitting their invocation only at error-exit
            // points (`genDefers(..., .normal_and_error)`). So Sema
            // just runs each defer body inline as it encounters the
            // instruction; no defer stack on our side. Mirrors
            // src/Sema.zig:1956 (the @"defer" arm in analyzeBodyInner).
            .@"defer" => {
                const defer_data = sema.zir.instructions.items(.data)[@intFromEnum(inst)].@"defer";
                const defer_body = sema.zir.bodySlice(defer_data.index, defer_data.len);
                // AstGen-emitted defer bodies are block expressions
                // terminated by `break_inline`, so evalBody MUST
                // raise. The two ComptimeBreak shapes (own
                // terminator vs further-out) match src/Sema.zig:1956.
                // A returned Value would require the body to end in
                // a condbr-as-terminator path AstGen never emits for
                // defers -- surface loudly if it ever does.
                if (sema.evalBody(defer_body)) |_| {
                    @panic("defer body returned a value -- unexpected AstGen shape");
                } else |err| switch (err) {
                    error.ComptimeBreak => {
                        if (sema.comptime_break_inst != defer_body[defer_body.len - 1]) {
                            return error.ComptimeBreak;
                        }
                    },
                    else => |e| return e,
                }
            },
            else => {
                // Snapshot operand provenance for this instruction only:
                // reset, evaluate (resolveRef ANDs in each operand it reads),
                // then fold the verdict into the result. Saved/restored so a
                // nested body's operands don't leak into the enclosing
                // instruction -- a compound op (block/loop) reads nothing
                // directly here, so its passed-through value keeps its own
                // provenance; a simple op inherits its operands'.
                const saved_oc = sema.operand_comptime;
                sema.operand_comptime = true;
                const maybe = sema.evalInst(inst, tag);
                const operands_comptime = sema.operand_comptime;
                sema.operand_comptime = saved_oc;
                if (try maybe) |result| {
                    var r = result;
                    r.is_comptime = r.is_comptime and operands_comptime;
                    try sema.results.put(sema.gpa, inst, r);
                }
            },
        }
        i += 1;
    }
}

/// Mirrors src/Sema.zig:emitBackwardBranch at src/Sema.zig:25436.
/// Increments `branch_count`; on overflow past `branch_quota`,
/// emits the same diagnostic AstGen does and aborts via
/// `error.AnalysisFail`. The limit will be raisable through
/// `@setEvalBranchQuota` once that builtin lands.
fn emitBackwardBranch(sema: *Sema) Error!void {
    sema.branch_count += 1;
    if (sema.branch_count > sema.branch_quota) {
        try sema.writer.print(
            "evaluation exceeded {d} backwards branches\n",
            .{sema.branch_quota},
        );
        try sema.writer.print(
            "use @setEvalBranchQuota() to raise the branch limit from {d}\n",
            .{sema.branch_quota},
        );
        return error.AnalysisFail;
    }
}

/// Walk `body`. If a `break_inline` / `@"break"` raises
/// `error.ComptimeBreak` and its `block_inst` matches `break_target`,
/// consume the transfer and return the break's operand resolved.
/// Otherwise re-raise so an outer receiver can handle it.
///
/// This is the runtime-only analog of the compiler's
/// `Sema.analyzeInlineBody` (src/Sema.zig:1062): the compiler
/// distinguishes "this body broke runtime-style" (returns null) from
/// "this body broke at comptime" (consumes via this path or
/// re-raises). With the comptime-coupling stripped, every body
/// resolves through this single path -- AstGen always emits
/// `break_inline` for the wrap, and `@"break"` raises the same error
/// because Sema is entirely comptime.
fn resolveInlineBody(
    sema: *Sema,
    body: []const Zir.Inst.Index,
    break_target: Zir.Inst.Index,
) Error!Value {
    if (sema.evalBody(body)) |val| {
        // A body normally terminates via `break` which raises
        // `error.ComptimeBreak` -- this `if` branch only fires when
        // a non-break terminator (e.g. `condbr`) returned a value
        // directly. Surface that value as the body's result.
        return val;
    } else |err| switch (err) {
        error.ComptimeBreak => {},
        else => |e| return e,
    }
    const datas = sema.zir.instructions.items(.data);
    const break_data = datas[@intFromEnum(sema.comptime_break_inst)].@"break";
    const extra = sema.zir.extraData(Zir.Inst.Break, break_data.payload_index);
    if (extra.data.block_inst != break_target) return error.ComptimeBreak;
    return try sema.resolveRef(break_data.operand);
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
        .mod_rem,
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
        .align_of => sema.evalAlignOf(inst),
        .size_of => sema.evalSizeOf(inst),
        .int_from_ptr => sema.evalIntFromPtr(inst),
        .alloc, .alloc_mut, .alloc_comptime_mut => sema.evalAlloc(inst),
        .make_ptr_const => sema.evalMakePtrConst(inst),
        .store_node => sema.evalStoreNode(inst),
        .struct_init_field_ptr => sema.evalStructInitFieldPtr(inst),
        .field_ptr_load => sema.evalFieldPtrLoad(inst),
        .opt_eu_base_ptr_init => sema.evalOptEuBasePtrInit(inst),
        .validate_ptr_struct_init => sema.evalValidatePtrStructInit(inst),
        .load => sema.evalLoad(inst),
        .decl_val => sema.evalDeclVal(inst),
        .decl_ref => sema.evalDeclRef(inst),
        .error_set_decl => sema.evalErrorSetDecl(inst),
        .error_value => sema.evalErrorValue(inst),
        .error_union_type => sema.evalErrorUnionType(inst),
        .err_union_code => sema.evalErrUnionCode(inst),
        .err_union_payload_unsafe => sema.evalErrUnionPayloadUnsafe(inst),
        .is_non_err => sema.evalIsNonErr(inst),
        .loop => sema.evalLoop(inst),
        .for_len => sema.evalForLen(inst),
        .switch_block,
        .switch_block_ref,
        .switch_block_err_union,
        => sema.evalSwitchBlock(inst),
        .param, .param_comptime => sema.evalParam(inst, tag),
        .param_anytype, .param_anytype_comptime => return sema.failAnytypeParam(),
        .func, .func_inferred, .func_fancy => sema.evalFunc(inst),
        .typeof => sema.evalTypeof(inst),
        .typeof_builtin => sema.evalTypeofBuiltin(inst),
        .ret_type => sema.evalRetType(),
        .call => sema.evalCall(inst, .direct),
        .field_call => sema.evalCall(inst, .field),
        .block_comptime => sema.evalBlockComptime(inst),
        .restore_err_ret_index_unconditional,
        .restore_err_ret_index_fn_entry,
        => null,
        .extended => sema.evalExtended(inst),
        // dbg_stmt / dbg_var_val / dbg_var_ptr are AstGen-emitted
        // debug breadcrumbs for line/local tracking. Tolerated as
        // no-ops here so we don't reject any function body that
        // declares a local. A future `:scope` extension can read
        // dbg_var_* via str_op to surface live local names.
        // validate_const is a runtime-safety guard the compiler
        // lowers to nothing in comptime context -- a no-op for us.
        .dbg_stmt, .dbg_var_val, .dbg_var_ptr, .validate_const => null,
        .ensure_result_used, .ensure_result_non_error => sema.evalPassthroughUnNode(inst),
        .int_type => sema.evalIntType(inst),
        .vector_type => sema.evalVectorType(inst),
        .optional_type => sema.evalOptionalType(inst),
        .optional_payload_safe, .optional_payload_unsafe => sema.evalOptionalPayload(inst),
        .array_type => sema.evalArrayType(inst),
        .array_init => sema.evalArrayInit(inst),
        .array_init_ref => sema.evalArrayInitRef(inst),
        .array_init_anon => sema.evalArrayInitAnon(inst),
        .array_init_elem_type => sema.evalArrayInitElemType(inst),
        .validate_array_init_result_ty => sema.evalValidateArrayInitResultTy(inst),
        .ref => sema.evalRef(inst),
        .elem_ptr_load => sema.evalElemPtrLoad(inst),
        .elem_val => sema.evalElemVal(inst),
        inline else => |unhandled| return sema.reportUnsupportedTag(unhandled),
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
    const bin = sema.binData(inst);
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
        // `%` is `@rem`, but Zig rejects it only when an operand is negative
        // AND the remainder is nonzero (mod/rem ambiguity); a negative operand
        // with a zero remainder is fine. Mirrors zirModRem. `.positive` is true
        // for zero, so `!positive` means strictly negative.
        .mod_rem => blk: {
            const rem_idx = try sema.unwrapDivResult(arith.internRem(gpa, ip, lhs, rhs), "%");
            if (!lhs.positive or !rhs.positive) {
                var rem_space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
                const rem_nonzero = !ip.indexToKey(rem_idx).int.storage.toBigInt(&rem_space).eqlZero();
                if (rem_nonzero) {
                    try sema.writer.writeAll("%: use @rem or @mod for negative operands\n");
                    return error.AnalysisFail;
                }
            }
            break :blk rem_idx;
        },
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
    // Worst-case `mul` output is `lhs.limbs.len + rhs.limbs.len`; add /
    // sub need `max + 1`. One worst-case buffer fits everything plus
    // one cushion limb for `saturate` to write its sentinel.
    const max_op_limbs = @max(lhs.limbs.len + rhs.limbs.len, @max(lhs.limbs.len, rhs.limbs.len) + 1);
    const dest_limbs = std.math.big.int.calcTwosCompLimbCount(dest_info.bits) + 1;
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

/// Whether `dst` can represent every value of `src` -- Zig's implicit
/// (runtime) int coercion rule. A signed dest needs a strictly wider bit
/// count than an unsigned source (the extra bit holds the sign); an unsigned
/// dest never accepts a signed source. Compiler reference:
/// `coerceInMemoryAllowedInts` in src/Sema.zig.
fn intCoercible(src: std.lang.Type.Int, dst: std.lang.Type.Int) bool {
    return switch (dst.signedness) {
        .unsigned => src.signedness == .unsigned and dst.bits >= src.bits,
        .signed => switch (src.signedness) {
            .signed => dst.bits >= src.bits,
            .unsigned => dst.bits > src.bits,
        },
    };
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
        // `%` is `@rem`, rejected only when an operand is negative AND the
        // remainder is nonzero -- the same mod/rem ambiguity rule the int
        // kernel applies (zirModRem governs both).
        .mod_rem => blk: {
            const r = @rem(lhs, rhs);
            if ((lhs < 0 or rhs < 0) and r != 0) {
                try sema.writer.writeAll("%: use @rem or @mod for negative operands\n");
                return error.AnalysisFail;
            }
            break :blk r;
        },
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
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.Block, pl_node.payload_index);
    const body = sema.zir.bodySlice(extra.end, extra.data.body_len);
    return try sema.resolveInlineBody(body, inst);
}

/// `condbr` / `condbr_inline`: resolve a bool condition, pick the then or
/// else body, recursively evalBody on the chosen one. The picked body
/// terminates with `break_inline` to its enclosing block, which exits the
/// recursive `evalBody` call here. Treated as a terminator by the outer
/// `evalBody` because it always transfers control -- never falls through.
///
/// Compiler reference: src/Sema.zig:zirCondbr.
fn evalCondbr(sema: *Sema, inst: Zir.Inst.Index) Error!Value {
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
    return try sema.resolveInlineBody(body, inst);
}

/// `typeof_log2_int_type`: returns the type whose values are valid as the
/// right-hand operand of `lhs << rhs` / `lhs >> rhs`. For `comptime_int`
/// operands this is `comptime_int` itself (the compiler's behavior); for
/// fixed-width int operands it is `unsigned(log2_ceil(bits))`.
///
/// Compiler reference: src/Sema.zig:zirTypeofLog2IntType -> log2IntType.
fn evalTypeofLog2IntType(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    assert(un_node.operand != .none);

    const operand = try sema.resolveRef(un_node.operand);
    const operand_type = Value.typeOf(operand, sema.intern_pool);

    if (operand_type.index == .comptime_int_type) {
        // A type used as a value is its own Index (a value of type `type`).
        return .{ .index = .comptime_int_type };
    }

    const operand_type_key = sema.intern_pool.indexToKey(operand_type.index);
    if (operand_type_key == .int_type) {
        const bits = operand_type_key.int_type.bits;
        const log2_bits: u16 = if (bits == 0) 0 else std.math.log2_int_ceil(u16, bits);
        const log2_type = try sema.intern_pool.internIntType(.unsigned, log2_bits);
        return .{ .index = log2_type };
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
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    const as = sema.zir.extraData(Zir.Inst.As, pl_node.payload_index).data;
    assert(as.dest_type != .none);
    assert(as.operand != .none);

    const dest_type_index = try sema.resolveDestType(as.dest_type, "as");

    const operand_value = try sema.resolveRef(as.operand);
    return try sema.coerceValueToType(operand_value, dest_type_index, "@as");
}

/// Resolve a `Zir.Inst.Ref` that should identify a type. A type used as a
/// value is its own Index -- a value of type `type` (per `Value.typeOf`), so
/// any Key that `Key.isType` accepts is itself the type identifier.
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
    const key = sema.intern_pool.indexToKey(dest_value.index);
    // A type used as a value is its own Index (per `Key.isType` /
    // `Value.typeOf`), so any type Key is itself the destination. Deriving
    // from `isType` keeps this in lockstep with that single type/value
    // partition rather than a hand-maintained accept-list.
    if (key.isType()) return dest_value.index;
    try sema.writer.print("{s}: destination is not a type\n", .{op_name});
    return error.AnalysisFail;
}

/// Decode the `Zir.Inst.Bin` payload (the `lhs` / `rhs` operand refs) of a
/// `pl_node` instruction -- the wire shape every binary-op and cast builtin
/// shares. Callers that require both operands present assert it themselves.
fn binData(sema: *Sema, inst: Zir.Inst.Index) Zir.Inst.Bin {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);
    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    return sema.zir.extraData(Zir.Inst.Bin, pl_node.payload_index).data;
}

/// `@floatCast(DestType, x)`: float-to-float width cast (widening or
/// narrowing). All widths are accepted; narrowing loses precision but
/// never errors. The pool's storage variant is selected by `DestType`.
///
/// Compiler reference: src/Sema.zig:zirFloatCast.
fn evalFloatCast(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const bin = sema.binData(inst);
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
    const bin = sema.binData(inst);
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
    const bin = sema.binData(inst);
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
    const bin = sema.binData(inst);

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
    const bin = sema.binData(inst);

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

    const workspace_limbs: usize = std.math.big.int.calcTwosCompLimbCount(dest_info.bits) + 1;
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
    const bin = sema.binData(inst);

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
                const workspace_limbs: usize = std.math.big.int.calcTwosCompLimbCount(info.bits) + 1;
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
    // Reinterpret as an unsigned `bits`-wide two's-complement value -- the
    // same `truncate(.unsigned, bits)` the int->bits paths use -- so a
    // negative value lands on its two's-complement pattern. Stack buffer, no
    // allocation; `bits <= 128` so the result fits `u128`.
    var buf: [std.math.big.int.calcTwosCompLimbCount(128) + 1]std.math.big.Limb = undefined;
    var pattern: std.math.big.int.Mutable = .{ .limbs = &buf, .len = undefined, .positive = undefined };
    pattern.truncate(big, .unsigned, bits);
    return pattern.toConst().toInt(u128) catch unreachable;
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
    var limbs_buf: [std.math.big.int.calcTwosCompLimbCount(128) + 1]std.math.big.Limb = undefined;
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
    const bin = sema.binData(inst);
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

    const max_limbs: usize = std.math.big.int.calcTwosCompLimbCount(dest_info.bits) + 1;
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
    const bin = sema.binData(inst);
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
    const bin = sema.binData(inst);
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
/// via additional `Ref` slots in extra; the current subset handles
/// only the base case (none of the optional extensions). Compiler reference:
/// `src/Sema.zig:zirPtrType`.
fn evalPtrType(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const inst_data = sema.zir.instructions.items(.data)[@intFromEnum(inst)].ptr_type;
    if (inst_data.flags.has_sentinel) {
        try sema.writer.writeAll("ptr_type: sentinel-terminated pointers not yet supported\n");
        return error.AnalysisFail;
    }
    if (inst_data.flags.has_addrspace or inst_data.flags.has_bit_range) {
        try sema.writer.writeAll("ptr_type: address_space / bit_range not yet supported\n");
        return error.AnalysisFail;
    }

    const extra = sema.zir.extraData(Zir.Inst.PtrType, inst_data.payload_index);
    const payload = extra.data;
    assert(payload.elem_type != .none);

    // The optional extensions trail the payload as `Ref` slots in `extra`,
    // in the order sentinel, align, addrspace, bit_range (zirPtrType). With
    // sentinel rejected above, the align ref -- when present -- is the first.
    const alignment: InternPool.Alignment = if (inst_data.flags.has_align)
        try sema.alignmentFromValue(try sema.resolveRef(@enumFromInt(sema.zir.extra[extra.end])), "ptr_type")
    else
        .none;

    const child_ty = try sema.resolveDestType(payload.elem_type, "ptr_type");
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
            .alignment = alignment,
            .is_const = !inst_data.flags.is_mutable,
            .is_volatile = inst_data.flags.is_volatile,
            .is_allowzero = inst_data.flags.is_allowzero,
            .address_space = .generic,
        },
    });
    return .{ .index = idx };
}

/// Convert an `align(N)` operand value to an `Alignment`. `N` is a comptime
/// integer; Zig requires it be a power of two (`validateAlign`), so a
/// non-power-of-two surfaces a diagnostic rather than corrupting the log2
/// encoding. Shared by pointer types (`*align(N) T`) and decl alignment
/// (`var x: T align(N)`).
fn alignmentFromValue(sema: *Sema, value: Value, op_name: []const u8) Error!InternPool.Alignment {
    const bytes = try sema.resolveUsizeInt(value, op_name);
    if (bytes == 0 or !std.math.isPowerOfTwo(bytes)) {
        try sema.writer.print("{s}: alignment '{d}' is not a power of two\n", .{ op_name, bytes });
        return error.AnalysisFail;
    }
    return InternPool.Alignment.fromByteUnits(bytes);
}

/// `@alignOf(T)`: the host ABI alignment of `T`, as a `comptime_int`. Mirrors
/// zirAlignOf -- only `noreturn` is rejected (uninstantiable); every other
/// modelled type yields its alignment (a comptime-only type yields 1).
fn evalAlignOf(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    const ty = try sema.resolveDestType(un_node.operand, "@alignOf");
    if (ty == .noreturn_type) {
        try sema.writer.writeAll("@alignOf: no align available for uninstantiable type 'noreturn'\n");
        return error.AnalysisFail;
    }
    const alignment = Type.fromIndex(ty).abiAlignment(sema.intern_pool) orelse {
        try sema.writer.writeAll("@alignOf: type not yet supported\n");
        return error.AnalysisFail;
    };
    const idx = try sema.intern_pool.internInt(.{
        .ty = .comptime_int_type,
        .storage = .{ .u64 = alignment.toByteUnits().? },
    });
    return .{ .index = idx };
}

/// `@sizeOf(T)`: the host ABI byte size of `T`, as a `comptime_int`. Mirrors
/// zirSizeOf -- `noreturn` is uninstantiable and comptime-only types have no
/// size, so both are rejected; `void` (one possible value) is `0`.
fn evalSizeOf(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    const ty = try sema.resolveDestType(un_node.operand, "@sizeOf");
    const key = sema.intern_pool.indexToKey(ty);
    // noreturn is uninstantiable; comptime-only types (and opaque) have no
    // runtime size. zirSizeOf rejects all of these before measuring; we reject
    // them rather than let `abiSize`'s 0 (the compiler's value for these
    // unsized simple types) masquerade as a real size.
    if (key == .simple_type) switch (key.simple_type) {
        .noreturn => {
            try sema.writer.writeAll("@sizeOf: no size available for uninstantiable type 'noreturn'\n");
            return error.AnalysisFail;
        },
        .comptime_int, .comptime_float, .type, .null, .undefined, .enum_literal, .anyopaque => {
            try sema.writer.print("@sizeOf: no size available for type '{s}'\n", .{@tagName(key.simple_type)});
            return error.AnalysisFail;
        },
        else => {},
    };
    const size = Type.fromIndex(ty).abiSize(sema.intern_pool) orelse {
        try sema.writer.writeAll("@sizeOf: type not yet supported\n");
        return error.AnalysisFail;
    };
    const idx = try sema.intern_pool.internInt(.{
        .ty = .comptime_int_type,
        .storage = .{ .u64 = size },
    });
    return .{ .index = idx };
}

/// `@intFromPtr(p)`: the pointer's address as `usize`.
///
/// Deliberate deviation from the compiler: `zirIntFromPtr` returns a comptime
/// value only for a pointer with a literal address (`@ptrFromInt`); a
/// comptime-alloc pointer has none, so the compiler defers to a runtime op
/// (codegen assigns the address). This evaluator has no runtime, so it assigns
/// the alloc a stable address in a modeled address space -- the bump cursor
/// rounded up to the pointer's alignment (explicit `align(N)`, else the
/// pointee's natural alignment). This makes alignment observable
/// (`@intFromPtr(&x) % @alignOf(T) == 0`). The address is REPL-synthetic: it
/// will not equal a real `zig run` address, so only the alignment invariant is
/// meaningful -- the address value itself is not comparable to the compiler.
fn evalIntFromPtr(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    const ptr = try sema.resolveRef(un_node.operand);
    const key = sema.intern_pool.indexToKey(ptr.index);
    if (key != .ptr) {
        try sema.writer.writeAll("@intFromPtr: operand is not a pointer\n");
        return error.AnalysisFail;
    }
    const p = key.ptr;
    const alloc_idx: u32 = switch (p.base_addr) {
        .comptime_alloc => |i| @intFromEnum(i),
        // A field pointer's address needs the field's byte offset within the
        // aggregate, which auto-layout structs don't expose here.
        .field => {
            try sema.writer.writeAll("@intFromPtr: address of a struct field not supported\n");
            return error.AnalysisFail;
        },
    };
    const ptr_ty = sema.intern_pool.indexToKey(p.ty).ptr_type;
    const natural: InternPool.Alignment = Type.fromIndex(ptr_ty.child).abiAlignment(sema.intern_pool) orelse .@"1";
    const align_bytes: u64 = ptr_ty.flags.alignment.toByteUnits() orelse natural.toByteUnits().?;

    const slot = &sema.comptime_allocs.items[alloc_idx];
    const base = slot.address orelse base: {
        const aligned = std.mem.alignForward(u64, sema.comptime_address_cursor, align_bytes);
        const size = Type.fromIndex(ptr_ty.child).abiSize(sema.intern_pool) orelse 1;
        sema.comptime_address_cursor = aligned + @max(size, 1);
        slot.address = aligned;
        break :base aligned;
    };

    const idx = try sema.intern_pool.internInt(.{
        .ty = .usize_type,
        .storage = .{ .u64 = base + p.byte_offset },
    });
    return .{ .index = idx };
}

/// `alloc` / `alloc_mut` / `alloc_comptime_mut`: reserve a fresh
/// entry in `comptime_allocs`, initialise to a typed `undef`, and
/// return a `Key.ptr` whose `BaseAddr = .comptime_alloc = index`.
///
/// All three start MUTABLE -- `alloc` is not const, despite naming a
/// `const` declaration. AstGen emits a separate `make_ptr_const` once a
/// `const`'s value is fully initialised (`evalMakePtrConst`); a `var` and the
/// for-loop index counter (an `alloc` that is incremented) never get one and
/// stay writable. Compiler reference: src/Sema.zig:zirAlloc / zirAllocMut /
/// analyzeComptimeAlloc, and Zir.zig's note that `alloc_mut` is "the same as
/// `alloc` except mutable, so make_ptr_const need not be used".
fn evalAlloc(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    assert(un_node.operand != .none);

    const child_ty = try sema.resolveDestType(un_node.operand, "alloc");
    const undef_idx = try sema.intern_pool.get(.{ .undef = child_ty });
    return try sema.pushComptimeAlloc(child_ty, .{ .index = undef_idx }, false, .none);
}

/// `make_ptr_const`: freeze an `alloc`'s pointer to `*const T` once the value
/// is fully initialised. AstGen emits it for a `const` local (an `alloc` is
/// mutable until then); it marks the comptime-alloc const so later stores are
/// rejected and returns a const-typed pointer to the same slot. Mirrors
/// zirMakePtrConst's "preserve the comptime alloc, just make the pointer
/// const" branch (the anon-decl promotion is a runtime-codegen optimisation
/// this comptime evaluator does not need).
fn evalMakePtrConst(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    const ptr = try sema.resolveRef(un_node.operand);
    const ip = sema.intern_pool;
    const p = ip.indexToKey(ptr.index).ptr;
    switch (p.base_addr) {
        .comptime_alloc => |idx| sema.comptime_allocs.items[@intFromEnum(idx)].is_const = true,
        // A field pointer freezes the aggregate it projects from.
        .field => |f| sema.comptime_allocs.items[@intFromEnum(ip.indexToKey(f.base).ptr.base_addr.comptime_alloc)].is_const = true,
    }
    const old = ip.indexToKey(p.ty).ptr_type;
    if (old.flags.is_const) return ptr;
    var flags = old.flags;
    flags.is_const = true;
    const const_ty = try ip.internPtrType(.{ .child = old.child, .sentinel = old.sentinel, .flags = flags });
    const const_ptr = try ip.internPtr(.{ .ty = const_ty, .base_addr = p.base_addr, .byte_offset = p.byte_offset });
    return .{ .index = const_ptr };
}

/// Append a comptime-alloc slot holding `val` (of type `child_ty`)
/// and return a single-item pointer to it (`*align(N) T` / `*const T` per
/// `is_const` and `alignment`). The one place that turns "a value needs an
/// address" into a slot + pointer: shared by `alloc` (undef slot) and the
/// ref-producing tags (`ref`, `decl_ref`, `array_init_ref`).
///
/// The slot is a *copy* of `val`, not the address of any pre-existing
/// storage. That is sound only because store-through-a-pointer
/// (`validate_deref` + deref-store) is unimplemented, so a `decl_ref`'s
/// `is_const = false` pointer can never be written through. When deref-store
/// lands, a mutable decl pointer must target the decl's real storage (a
/// `.nav`-style base address) -- writing through this copy would leave the
/// decl unchanged, a silent divergence from the compiler.
fn pushComptimeAlloc(
    sema: *Sema,
    child_ty: InternPool.Index,
    val: Value,
    is_const: bool,
    alignment: InternPool.Alignment,
) Error!Value {
    assert(child_ty != .none);
    assert(val.index != .none);

    const ip = sema.intern_pool;
    const alloc_index: u32 = @intCast(sema.comptime_allocs.items.len);
    try sema.comptime_allocs.append(sema.gpa, .{
        .val = val,
        .is_const = is_const,
    });

    const ptr_ty = try ip.internPtrType(.{
        .child = child_ty,
        .flags = .{ .size = .one, .is_const = is_const, .alignment = alignment },
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
    const bin = sema.binData(inst);
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

    const rhs_value = try sema.resolveRef(bin.rhs);
    switch (ptr_key.ptr.base_addr) {
        .comptime_alloc => {
            const alloc = try sema.lookupComptimeAlloc(ptr_key.ptr);
            const coerced = try sema.coerceValueToType(rhs_value, alloc.val.typeOf(ip).toIndex(), "store");
            alloc.val = coerced;
        },
        // Store into one field of a struct alloc: coerce to the field type
        // (the field pointer's child) and rebuild the alloc's aggregate.
        .field => |f| {
            const base = ip.indexToKey(f.base).ptr;
            const struct_ty = ip.indexToKey(base.ty).ptr_type.child;
            const coerced = try sema.coerceValueToType(rhs_value, ptr_ty_key.ptr_type.child, "store");
            const base_alloc = try sema.lookupComptimeAlloc(base);
            base_alloc.val = try sema.setStructField(base_alloc.val, struct_ty, @intCast(f.index), coerced);
        },
    }
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
    return try sema.loadValue(ptr_value);
}

/// Dereference a Key.ptr Value through its backing comptime_alloc
/// slot. Shared by `evalLoad` (ZIR `.load` arm) and the ptr-form
/// switch operand (`switch_block_ref`).
fn loadValue(sema: *Sema, ptr: Value) Error!Value {
    const ptr_key = sema.intern_pool.indexToKey(ptr.index);
    if (ptr_key != .ptr) {
        try sema.writer.writeAll("internal error: load through non-pointer value\n");
        return error.AnalysisFail;
    }
    const alloc = try sema.lookupComptimeAlloc(ptr_key.ptr);
    return alloc.val;
}

/// Locate the `ComptimeAlloc` entry referenced by a `Key.Ptr`. Returns
/// a pointer into `comptime_allocs` so the caller can mutate `val`
/// (for store) or read it (for load) without copying. The `byte_offset`
/// is asserted to be zero -- field/element pointers (non-zero offsets)
/// arrive with aggregates.
fn lookupComptimeAlloc(sema: *Sema, ptr: InternPool.Key.Ptr) Error!*ComptimeAlloc {
    if (ptr.byte_offset != 0) {
        try sema.writer.writeAll("comptime_alloc lookup: pointer offset not yet supported\n");
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

    if (try sema.coerceToFixedWidthInt(value, dest_ty, op_name)) |coerced| return coerced;
    if (try sema.coerceToFloat(value, dest_ty, op_name)) |coerced| return coerced;

    // Coercion into an error-union type: an error value becomes the
    // `.err` arm; any other value coerces to the payload type and
    // becomes the `.payload` arm. Same shape as the compiler's
    // `coerceExtra` error-union branch.
    if (ip.indexToKey(dest_ty) == .error_union_type) {
        return try sema.coerceToErrorUnion(value, dest_ty, op_name);
    }

    // Coercion into an optional type: `null` becomes the null optional;
    // any other value coerces to the child type and wraps as the
    // payload. Same shape as the compiler's `coerceExtra` optional arm.
    if (ip.indexToKey(dest_ty) == .opt_type) {
        return try sema.coerceToOptional(value, dest_ty, op_name);
    }

    try sema.writer.print("{s}: cannot coerce value to destination type\n", .{op_name});
    return error.AnalysisFail;
}

/// Coerce `value` to a fixed-width int `dest_ty`, or `null` if `dest_ty` isn't
/// one (caller falls through). A runtime value follows Zig's type-based rule
/// -- the dest must represent every value of the source type, so `u32 -> i32`
/// is rejected -- while a comptime-known value follows the value-fits rule
/// (`coerceExtra` keys on whether the value is known, src/Sema.zig);
/// `refitIntToFixedWidth` re-tags and reports out-of-range.
fn coerceToFixedWidthInt(sema: *Sema, value: Value, dest_ty: InternPool.Index, op_name: []const u8) Error!?Value {
    const ip = sema.intern_pool;
    if (ip.indexToKey(value.index) != .int) return null;
    const dst = intTypeInfo(ip, dest_ty) orelse return null;
    // A runtime int's type is fixed-width (`comptime_int` is comptime-only);
    // the `if` guards the rare edge of a `comptime_int` here marked runtime,
    // which then falls through to the value-fits path.
    if (!value.is_comptime) {
        const value_type = Value.typeOf(value, ip);
        if (intTypeInfo(ip, value_type.index)) |src| {
            if (!intCoercible(src, dst)) {
                try sema.writer.print("{s}: expected ", .{op_name});
                try Type.print(.fromIndex(dest_ty), ip, sema.writer);
                try sema.writer.writeAll(", found ");
                try Type.print(.fromIndex(value_type.index), ip, sema.writer);
                try sema.writer.writeByte('\n');
                return error.AnalysisFail;
            }
        }
    }
    var coerced = try sema.refitIntToFixedWidth(value.index, dest_ty, op_name);
    coerced.is_comptime = value.is_comptime;
    return coerced;
}

/// Coerce `value` to a float `dest_ty`, or `null` if `dest_ty` isn't a float
/// or the operand isn't a coercible number (caller falls through). A runtime
/// value widens to a wider-or-equal float; a narrowing or a runtime int needs
/// an explicit @floatCast / @floatFromInt. A comptime value coerces by value.
fn coerceToFloat(sema: *Sema, value: Value, dest_ty: InternPool.Index, op_name: []const u8) Error!?Value {
    if (!isFloatTypeIndex(dest_ty)) return null;
    const ip = sema.intern_pool;
    if (!value.is_comptime) {
        const value_type = Value.typeOf(value, ip);
        const widens = isFloatTypeIndex(value_type.index) and
            numericBitSize(ip, value_type.index).? <= numericBitSize(ip, dest_ty).?;
        if (!widens) {
            try sema.writer.print("{s}: a runtime value does not coerce to ", .{op_name});
            try Type.print(.fromIndex(dest_ty), ip, sema.writer);
            try sema.writer.writeAll(" (needs @floatCast or @floatFromInt)\n");
            return error.AnalysisFail;
        }
    }
    if (coerceToTargetFloat(ip.indexToKey(value.index), dest_ty)) |coerced| {
        const idx = try ip.internFloat(coerced);
        return .{ .index = idx, .is_comptime = value.is_comptime };
    }
    return null;
}

fn coerceToOptional(
    sema: *Sema,
    value: Value,
    dest_ty: InternPool.Index,
    op_name: []const u8,
) Error!Value {
    const ip = sema.intern_pool;
    if (value.index == .null_value) {
        const idx = try ip.internOpt(.{ .ty = dest_ty, .val = .none });
        return .{ .index = idx };
    }
    const child = ip.indexToKey(dest_ty).opt_type;
    const payload = try sema.coerceValueToType(value, child, op_name);
    const idx = try ip.internOpt(.{ .ty = dest_ty, .val = payload.index });
    return .{ .index = idx };
}

/// `int_type`: an arbitrary-width integer type (`u69`, `i420`, ...).
/// Well-known widths (`u8`, `i32`, `usize`, ...) arrive as pre-
/// interned `Inst.Ref` constants and never reach here; this handles
/// the rest. Compiler reference: src/Sema.zig:zirIntType (~7372).
fn evalIntType(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const int_type = sema.zir.instructions.items(.data)[@intFromEnum(inst)].int_type;
    const idx = try sema.intern_pool.internIntType(int_type.signedness, int_type.bit_count);
    return .{ .index = idx };
}

/// `array_type lhs, rhs`: `lhs` is the length operand, `rhs` the
/// element type. Builds `[len]child` with no sentinel (the
/// sentinel form is `array_type_sentinel`, a separate tag). Returns
/// the array-type Index, which doubles as the value-of-type-`type`.
/// Compiler reference: src/Sema.zig:zirArrayType (~7460).
fn evalArrayType(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const bin = sema.binData(inst);
    assert(bin.lhs != .none);
    assert(bin.rhs != .none);

    const len = try sema.resolveArrayLen(bin.lhs, "array_type");
    const child = try sema.resolveDestType(bin.rhs, "array_type");
    const array_ty = try sema.intern_pool.internArrayType(.{ .len = len, .child = child });
    return .{ .index = array_ty };
}

/// `vector_type lhs, rhs`: `lhs` is the lane count, `rhs` the element
/// type. The length is a u32 upstream, so a wider value is rejected.
/// The element type is restricted to concrete int/float/bool/pointer
/// via `isVectorElemType`. Compiler reference: src/Sema.zig:zirVectorType
/// (~7456).
fn evalVectorType(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const bin = sema.binData(inst);
    assert(bin.lhs != .none);
    assert(bin.rhs != .none);

    const len64 = try sema.resolveArrayLen(bin.lhs, "vector_type");
    const len = std.math.cast(u32, len64) orelse {
        try sema.writer.print("vector_type: length {d} exceeds u32\n", .{len64});
        return error.AnalysisFail;
    };
    const child = try sema.resolveDestType(bin.rhs, "vector_type");
    if (!isVectorElemType(sema.intern_pool, child)) {
        try sema.writer.writeAll(
            "vector_type: expected integer, float, bool, or pointer for the vector element type\n",
        );
        return error.AnalysisFail;
    }
    const vector_ty = try sema.intern_pool.internVectorType(.{ .len = len, .child = child });
    return .{ .index = vector_ty };
}

/// Predicate for `@Vector` element types -- concrete integer, float,
/// bool, or pointer. comptime_int / comptime_float are excluded: a
/// vector lane needs a fixed bit width. Mirrors the compiler's
/// `checkVectorElemType` (src/Sema.zig).
fn isVectorElemType(pool: *const InternPool, child: InternPool.Index) bool {
    return switch (pool.indexToKey(child)) {
        .int_type, .ptr_type => true,
        .simple_type => |st| switch (st) {
            .usize,
            .isize,
            .c_char,
            .c_short,
            .c_ushort,
            .c_int,
            .c_uint,
            .c_long,
            .c_ulong,
            .c_longlong,
            .c_ulonglong,
            .c_longdouble,
            .f16,
            .f32,
            .f64,
            .f80,
            .f128,
            .bool,
            => true,
            else => false,
        },
        else => false,
    };
}

/// `optional_type operand`: build `?child`. Compiler reference:
/// src/Sema.zig:zirOptionalType. The compiler also rejects opaque and
/// `null` element types; neither is constructible in the REPL yet
/// (opaque arrives with container decls), so that guard is
/// deferred rather than silently dropped.
fn evalOptionalType(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    const child = try sema.resolveDestType(un_node.operand, "optional_type");
    const opt_ty = try sema.intern_pool.internOptionalType(child);
    return .{ .index = opt_ty };
}

/// `optional_payload_safe` / `_unsafe` (`x.?`): unwrap an optional to
/// its payload. Both ZIR forms collapse here -- the safe variant's
/// runtime null check has no comptime analogue; a comptime-known
/// `null` is the "unable to unwrap null" compile error either way.
/// Compiler reference: src/Sema.zig:zirOptionalPayload (~8037). The
/// `_ptr` pointer-to-payload variants are not wired (they need an
/// offset into the optional's slot) and surface the unsupported-tag
/// diagnostic.
fn evalOptionalPayload(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    const operand = try sema.resolveRef(un_node.operand);
    const key = sema.intern_pool.indexToKey(operand.index);
    if (key != .opt) {
        try sema.writer.writeAll("optional unwrap: operand is not an optional\n");
        return error.AnalysisFail;
    }
    if (key.opt.val == .none) {
        try sema.writer.writeAll("unable to unwrap null\n");
        return error.AnalysisFail;
    }
    return .{ .index = key.opt.val };
}

/// `array_init`: build the aggregate value. `array_init_ref`: build
/// it and hand back a `*const [N]T` instead. AstGen emits the `_ref`
/// form when the result is indexed in place (`([_]T{...})[i]`) and
/// the value form when it's used directly. Both share
/// `buildArrayAggregate`. Compiler reference: src/Sema.zig:zirArrayInit
/// (~18826) -- the comptime slice that builds an aggregate Value.
fn evalArrayInit(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    return .{ .index = try sema.buildArrayAggregate(inst) };
}

fn evalArrayInitRef(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const agg = try sema.buildArrayAggregate(inst);
    return try sema.materializeConstPtr(.{ .index = agg });
}

/// `array_init_anon`: an anonymous tuple literal (`.{a, b, ...}`).
/// Unlike `array_init` there's no destination type -- the tuple type
/// is inferred from each operand's own type, and elements are not
/// coerced. The field values live in the aggregate; `elem_ptr_load`
/// then indexes it (AstGen emits a separate `ref` for that path).
/// Compiler reference: src/Sema.zig:zirArrayInitAnon (~19210).
///
/// Deviation: the compiler bakes the elements into the type
/// (`@TypeOf(.{1, 2.5})` is `struct { comptime comptime_int = 1, ... }`,
/// so `.{1,2.5}` and `.{1,3.5}` differ). We intern field types only and
/// keep values in the aggregate, deduping by type. Observable only via
/// `@TypeOf`/`@typeName`/type-equality, none of which we model yet.
fn evalArrayInitAnon(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.MultiOp, pl_node.payload_index);
    const operands = sema.zir.refSlice(extra.end, extra.data.operands_len);

    const ip = sema.intern_pool;
    const types = try sema.gpa.alloc(InternPool.Index, operands.len);
    defer sema.gpa.free(types);
    const values = try sema.gpa.alloc(InternPool.Index, operands.len);
    defer sema.gpa.free(values);

    for (operands, types, values) |operand, *ty, *val| {
        const elem = try sema.resolveRef(operand);
        ty.* = Value.typeOf(elem, ip).index;
        val.* = elem.index;
    }

    // Both interns copy into the pool, so the gpa buffers free safely.
    const tuple_ty = try ip.internTupleType(types);
    const agg = try ip.internAggregate(.{ .ty = tuple_ty, .storage = .{ .elems = values } });
    return .{ .index = agg };
}

/// Decode an `array_init[_ref]` MultiOp into an interned aggregate
/// Index. First operand is the array type; the rest are element
/// values coerced to the array's child type.
fn buildArrayAggregate(sema: *Sema, inst: Zir.Inst.Index) Error!InternPool.Index {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.MultiOp, pl_node.payload_index);
    const operands = sema.zir.refSlice(extra.end, extra.data.operands_len);
    assert(operands.len >= 1);

    const ip = sema.intern_pool;
    const array_ty = try sema.resolveDestType(operands[0], "array_init");
    const array_key = ip.indexToKey(array_ty);

    const elems = operands[1..];
    const buf = try sema.gpa.alloc(InternPool.Index, elems.len);
    defer sema.gpa.free(buf);
    for (elems, 0..) |elem_ref, i| {
        const elem = try sema.resolveRef(elem_ref);
        // Arrays/vectors share one child type; a tuple gives each
        // position its own field type (`array_ty.fieldType(i)` in the
        // compiler), which is where a void/non-void mismatch is caught.
        const elem_ty = try sema.arrayInitElemType(array_key, i, "array_init");
        const coerced = try sema.coerceValueToType(elem, elem_ty, "array_init");
        buf[i] = coerced.index;
    }

    return try ip.internAggregate(.{ .ty = array_ty, .storage = .{ .elems = buf } });
}

/// The element type at `index` for an array-initializable result type:
/// the shared child for arrays/vectors, or the positional field type for
/// a tuple. Mirrors the `is_tuple ? fieldType(i) : childType()` split in
/// src/Sema.zig:zirArrayInit / zirArrayInitElemType.
fn arrayInitElemType(
    sema: *Sema,
    key: InternPool.Key,
    index: usize,
    op_name: []const u8,
) Error!InternPool.Index {
    switch (key) {
        .array_type => |at| return at.child,
        .vector_type => |vt| return vt.child,
        .tuple_type => |tt| {
            if (index < tt.types.len) return tt.types[index];
            try sema.writer.print(
                "{s}: element {d} is out of range for a {d}-field tuple\n",
                .{ op_name, index, tt.types.len },
            );
            return error.AnalysisFail;
        },
        else => {
            try sema.writer.print("{s}: type does not support array-init syntax\n", .{op_name});
            return error.AnalysisFail;
        },
    }
}

/// `array_init_elem_type lhs, rhs`: given a result type (`lhs`) and an
/// element index (`rhs`, carried as the integer value of the Ref), yield
/// the element's expected type. AstGen emits one per element to supply a
/// result-type hint to each initializer expression.
/// Compiler reference: src/Sema.zig:zirArrayInitElemType.
fn evalArrayInitElemType(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const bin = sema.zir.instructions.items(.data)[@intFromEnum(inst)].bin;
    const indexable_ty = try sema.resolveDestType(bin.lhs, "array_init_elem_type");
    const index: usize = @intFromEnum(bin.rhs);
    const elem_ty = try sema.arrayInitElemType(
        sema.intern_pool.indexToKey(indexable_ty),
        index,
        "array_init_elem_type",
    );
    return .{ .index = elem_ty };
}

/// `validate_array_init_result_ty`: confirm the known result type accepts
/// array-init syntax and that the element count matches. The compiler
/// returns void; the real type checking happens element-by-element in
/// `array_init`. Compiler reference: src/Sema.zig:zirValidateArrayInitResultTy.
fn evalValidateArrayInitResultTy(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    const data = sema.zir.extraData(Zir.Inst.ArrayInit, pl_node.payload_index).data;
    const result_ty = try sema.resolveDestType(data.ty, "array init");
    const field_count: u64 = switch (sema.intern_pool.indexToKey(result_ty)) {
        .array_type => |at| at.len,
        .vector_type => |vt| vt.len,
        .tuple_type => |tt| tt.types.len,
        else => {
            try sema.writer.print("array init: type does not support array-init syntax\n", .{});
            return error.AnalysisFail;
        },
    };
    if (data.init_count != field_count) {
        try sema.writer.print(
            "array init: expected {d} elements, found {d}\n",
            .{ field_count, data.init_count },
        );
        return error.AnalysisFail;
    }
    return null;
}

/// `tuple_decl` (extended): a positional struct type, e.g.
/// `struct { i32, f128 }`. The `small` field is the field count; trailing
/// the `TupleDecl` payload are two Refs per field -- a type and a default
/// init. Only `comptime` fields take a default; we don't model those yet,
/// so a present init is rejected. Compiler reference: src/Sema.zig:zirTupleDecl.
fn evalTupleDecl(sema: *Sema, extended: Zir.Inst.Extended.InstData) Error!?Value {
    const fields_len = extended.small;
    const extra = sema.zir.extraData(Zir.Inst.TupleDecl, extended.operand);
    const refs = sema.zir.refSlice(extra.end, fields_len * 2);

    const types = try sema.gpa.alloc(InternPool.Index, fields_len);
    defer sema.gpa.free(types);
    for (types, 0..) |*ty, i| {
        const zir_field_ty = refs[i * 2];
        const zir_field_init = refs[i * 2 + 1];
        if (zir_field_init != .none) {
            try sema.writer.print(
                "tuple field {d}: comptime field defaults are not supported\n",
                .{i},
            );
            return error.AnalysisFail;
        }
        ty.* = try sema.resolveDestType(zir_field_ty, "tuple field type");
    }

    return .{ .index = try sema.intern_pool.internTupleType(types) };
}

/// `struct_decl` (extended): a named struct type (`struct { x: i32 }`).
/// Interns a nominal `struct_type` shell keyed on the declaration site;
/// the compiler likewise creates the type before resolving fields (its
/// `getDeclaredStructType` + lazy `resolveStructFieldTypes`), so the
/// field bodies are left in the ZIR and resolved on demand. The name
/// follows `name_strategy`: `.parent` borrows the enclosing
/// declaration's name (`const P = struct {...}` -> `P`); the rest have
/// no name to borrow, so a stable name is synthesized from the
/// declaration site. Compiler reference: src/Sema.zig:zirStructDecl,
/// setTypeName.
fn evalStructDecl(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const struct_decl = sema.zir.getStructDecl(inst);
    const name = switch (struct_decl.name_strategy) {
        // Named after the enclosing declaration: its fully-qualified
        // name is already `type_name_ctx` (the compiler's `.parent`).
        .parent => sema.type_name_ctx,
        // No declaration to borrow from: `<ctx>__struct_<N>`, the format
        // `setTypeName` uses for `.anon`. `.func` (generic-instantiation
        // naming) and `.dbg_var` fall here too.
        .anon, .func, .dbg_var => blk: {
            const ctx = sema.intern_pool.stringSlice(sema.type_name_ctx);
            const text = try std.fmt.allocPrint(sema.gpa, "{s}__struct_{d}", .{ ctx, @intFromEnum(inst) });
            defer sema.gpa.free(text);
            break :blk try sema.intern_pool.getOrPutString(sema.gpa, text);
        },
    };

    return .{ .index = try sema.intern_pool.internStructType(.{
        .source_zir_id = sema.current_zir_id,
        .decl_inst = inst,
        .name = name,
    }) };
}

/// Resolve a struct field by name to its index and type. Iterates the struct
/// decl's fields via the stdlib `iterateFields`, matching name bytes; the field
/// type is its type body evaluated in the struct's source ZIR (swapped in for a
/// cross-line struct, as `evalCall` does for functions). Returns null if no
/// field matches. Field types that reference the defining line's locals are out
/// of scope -- the swapped frame shares the session namespace but not that
/// line's per-instruction results.
fn structFieldByName(
    sema: *Sema,
    struct_ty: InternPool.Index,
    name: []const u8,
) Error!?struct { index: u32, ty: InternPool.Index } {
    const st = sema.intern_pool.indexToKey(struct_ty).struct_type;
    const saved_zir = sema.zir;
    const saved_id = sema.current_zir_id;
    if (st.source_zir_id != sema.current_zir_id) {
        if (st.source_zir_id >= sema.line_zir.len) {
            try sema.writer.writeAll("struct field: defining ZIR is no longer available\n");
            return error.AnalysisFail;
        }
        sema.zir = sema.line_zir[st.source_zir_id];
        sema.current_zir_id = st.source_zir_id;
    }
    defer {
        sema.zir = saved_zir;
        sema.current_zir_id = saved_id;
    }
    var it = sema.zir.getStructDecl(st.decl_inst).iterateFields();
    while (it.next()) |field| {
        if (std.mem.eql(u8, sema.zir.nullTerminatedString(field.name), name)) {
            const ty = (try sema.resolveInlineBody(field.type_body, st.decl_inst)).index;
            return .{ .index = field.idx, .ty = ty };
        }
    }
    return null;
}

/// A struct type's declared field count (read straight from its source ZIR's
/// `field_names`; no field bodies are evaluated).
fn structFieldCount(sema: *Sema, struct_ty: InternPool.Index) Error!u32 {
    const st = sema.intern_pool.indexToKey(struct_ty).struct_type;
    const zir = if (st.source_zir_id == sema.current_zir_id)
        sema.zir
    else if (st.source_zir_id < sema.line_zir.len)
        sema.line_zir[st.source_zir_id]
    else {
        try sema.writer.writeAll("struct field count: defining ZIR is no longer available\n");
        return error.AnalysisFail;
    };
    return @intCast(zir.getStructDecl(st.decl_inst).field_names.len);
}

/// `struct_init_field_ptr`: `&object.field`, the pointer each field value is
/// stored through during `.{ ... }` init. Resolves the field by name to its
/// index and builds a `.field` pointer into the struct alloc. Mirrors
/// zirStructInitFieldPtr -> fieldPtr -> structFieldPtrByIndex (the auto-layout
/// `.field` representation).
fn evalStructInitFieldPtr(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);
    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.Field, pl_node.payload_index).data;
    const name = sema.zir.nullTerminatedString(extra.field_name_start);
    const object_ptr = try sema.resolveRef(extra.lhs);
    const struct_ty = sema.intern_pool.indexToKey(sema.intern_pool.indexToKey(object_ptr.index).ptr.ty).ptr_type.child;
    const fld = (try sema.structFieldByName(struct_ty, name)) orelse {
        try sema.writer.print("struct init: no field named '{s}'\n", .{name});
        return error.AnalysisFail;
    };
    const field_ptr_ty = try sema.intern_pool.internPtrType(.{ .child = fld.ty, .flags = .{ .size = .one } });
    const field_ptr = try sema.intern_pool.internPtr(.{
        .ty = field_ptr_ty,
        .base_addr = .{ .field = .{ .base = object_ptr.index, .index = fld.index } },
        .byte_offset = 0,
    });
    return .{ .index = field_ptr };
}

/// `field_ptr_load`: read `object.field`. Resolves the field index by name and
/// returns the corresponding element of the struct alloc's aggregate value.
/// Mirrors zirFieldPtrLoad -> fieldPtrLoad.
fn evalFieldPtrLoad(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);
    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.Field, pl_node.payload_index).data;
    const name = sema.zir.nullTerminatedString(extra.field_name_start);
    const object_ptr = try sema.resolveRef(extra.lhs);
    const struct_ty = sema.intern_pool.indexToKey(sema.intern_pool.indexToKey(object_ptr.index).ptr.ty).ptr_type.child;
    const fld = (try sema.structFieldByName(struct_ty, name)) orelse {
        try sema.writer.print("field access: no field named '{s}'\n", .{name});
        return error.AnalysisFail;
    };
    const struct_val = try sema.loadValue(object_ptr);
    const agg = sema.intern_pool.indexToKey(struct_val.index).aggregate;
    return .{ .index = InternPool.aggregateElementAt(agg, fld.index) };
}

/// Write `elem` into field `index` of a struct alloc's value, returning the new
/// aggregate. An `undef` alloc materialises an all-`undef` aggregate of the
/// right arity first; an existing aggregate is copied with one element
/// replaced. Whole-aggregate read-modify-write -- the compiler mutates in place
/// via `MutableValue`, which this comptime-only evaluator does not model.
fn setStructField(
    sema: *Sema,
    old: Value,
    struct_ty: InternPool.Index,
    index: u32,
    elem: Value,
) Error!Value {
    const ip = sema.intern_pool;
    const count = try sema.structFieldCount(struct_ty);
    const elems = try sema.gpa.alloc(InternPool.Index, count);
    defer sema.gpa.free(elems);
    const old_key = ip.indexToKey(old.index);
    if (old_key == .aggregate) {
        for (elems, 0..) |*e, i| e.* = InternPool.aggregateElementAt(old_key.aggregate, i);
    } else {
        @memset(elems, .undef);
    }
    elems[index] = elem.index;
    return .{ .index = try ip.internAggregate(.{ .ty = struct_ty, .storage = .{ .elems = elems } }) };
}

/// `opt_eu_base_ptr_init`: strips the optional/error-union payload base before a
/// result-location init. For a plain struct/array the operand is already the
/// base, so this is the identity, mirroring `optEuBasePtrInit`'s non-opt/EU
/// path.
fn evalOptEuBasePtrInit(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);
    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    return try sema.resolveRef(un_node.operand);
}

/// `validate_ptr_struct_init`: after a `.{ ... }` init's explicit field stores,
/// every field not written must get its default value, or -- if it has none --
/// be a "missing field" error. The body is the list of `struct_init_field_ptr`
/// instructions (one per explicit field), whose names give the set that was
/// initialized. Mirrors zirValidatePtrStructInit -> validateStructInit.
fn evalValidatePtrStructInit(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);
    const datas = sema.zir.instructions.items(.data);
    const extra = sema.zir.extraData(Zir.Inst.Block, datas[@intFromEnum(inst)].pl_node.payload_index);
    const body = sema.zir.bodySlice(extra.end, extra.data.body_len);
    if (body.len == 0) return null; // no fields -> nothing to default or check

    const ip = sema.intern_pool;
    const first = sema.zir.extraData(Zir.Inst.Field, datas[@intFromEnum(body[0])].pl_node.payload_index).data;
    const object_ptr = try sema.resolveRef(first.lhs);
    const struct_ty = ip.indexToKey(ip.indexToKey(object_ptr.index).ptr.ty).ptr_type.child;

    // Names explicitly initialized -- byte slices into the current ZIR, valid
    // across the source-ZIR swap below (a different ZIR's string table).
    const stored = try sema.gpa.alloc([]const u8, body.len);
    defer sema.gpa.free(stored);
    for (body, stored) |field_ptr, *name| {
        const fp = sema.zir.extraData(Zir.Inst.Field, datas[@intFromEnum(field_ptr)].pl_node.payload_index).data;
        name.* = sema.zir.nullTerminatedString(fp.field_name_start);
    }

    const st = ip.indexToKey(struct_ty).struct_type;
    const saved_zir = sema.zir;
    const saved_id = sema.current_zir_id;
    if (st.source_zir_id != sema.current_zir_id) {
        if (st.source_zir_id >= sema.line_zir.len) {
            try sema.writer.writeAll("struct init: defining ZIR is no longer available\n");
            return error.AnalysisFail;
        }
        sema.zir = sema.line_zir[st.source_zir_id];
        sema.current_zir_id = st.source_zir_id;
    }
    defer {
        sema.zir = saved_zir;
        sema.current_zir_id = saved_id;
    }
    var it = sema.zir.getStructDecl(st.decl_inst).iterateFields();
    while (it.next()) |field| {
        const name = sema.zir.nullTerminatedString(field.name);
        if (sliceContainsName(stored, name)) continue;
        const default_body = field.default_body orelse {
            try sema.writer.print("missing struct field: {s}\n", .{name});
            return error.AnalysisFail;
        };
        const field_ty = (try sema.resolveInlineBody(field.type_body, st.decl_inst)).index;
        const raw = try sema.resolveInlineBody(default_body, st.decl_inst);
        const value = try sema.coerceValueToType(raw, field_ty, "struct field default");
        const alloc = try sema.lookupComptimeAlloc(ip.indexToKey(object_ptr.index).ptr);
        alloc.val = try sema.setStructField(alloc.val, struct_ty, field.idx, value);
    }
    return null;
}

fn sliceContainsName(names: []const []const u8, name: []const u8) bool {
    for (names) |n| if (std.mem.eql(u8, n, name)) return true;
    return false;
}

/// `ref operand`: materialise `operand`'s value into a fresh const
/// comptime-alloc slot and return a `*const T` to it. Compiler
/// reference: src/Sema.zig:zirRef (~3052) -> analyzeRef.
fn evalRef(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const un_tok = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_tok;
    assert(un_tok.operand != .none);

    const value = try sema.resolveRef(un_tok.operand);
    return try sema.materializeConstPtr(value);
}

/// Store `value` in a fresh const comptime-alloc slot and return a
/// `*const T` pointer to it. Shared by `ref` (pointer to an inline
/// value) and `array_init_ref` (pointer to a fresh aggregate) -- both
/// address a temporary, which the compiler also types `*const` at natural
/// alignment. `decl_ref` does NOT use this: a pointer to a binding carries
/// the decl's own constness and alignment.
fn materializeConstPtr(sema: *Sema, value: Value) Error!Value {
    const child_ty = Value.typeOf(value, sema.intern_pool).index;
    return try sema.pushComptimeAlloc(child_ty, value, true, .none);
}

/// `elem_ptr_load lhs, rhs`: load the aggregate behind pointer
/// `lhs`, then return element `rhs`. AstGen emits this for `a[i]`
/// in value position (the ptr-then-load fusion). Bounds are checked
/// against the aggregate type's element count -- an out-of-range
/// index is a comptime error here (we have no runtime panic path).
fn evalElemPtrLoad(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const bin = sema.binData(inst);
    assert(bin.lhs != .none);
    assert(bin.rhs != .none);

    const array_value = try sema.loadValue(try sema.resolveRef(bin.lhs));
    return try sema.aggregateElement(array_value, bin.rhs);
}

/// `elem_val`: `indexable[index]` by value (the `for (a) |x|` capture and
/// direct indexing of an aggregate value). Same element read as
/// `elem_ptr_load`, but the operand is the aggregate value rather than a
/// pointer to it -- if it does arrive as a pointer, load through it first.
fn evalElemVal(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const bin = sema.binData(inst);
    assert(bin.lhs != .none);
    assert(bin.rhs != .none);

    const lhs = try sema.resolveRef(bin.lhs);
    const array_value = if (sema.intern_pool.indexToKey(lhs.index) == .ptr)
        try sema.loadValue(lhs)
    else
        lhs;
    return try sema.aggregateElement(array_value, bin.rhs);
}

/// Read element `index_ref` of an aggregate value, with a bounds check.
/// Shared by `elem_ptr_load` and `elem_val`.
fn aggregateElement(sema: *Sema, array_value: Value, index_ref: Zir.Inst.Ref) Error!Value {
    const ip = sema.intern_pool;
    const agg_key = ip.indexToKey(array_value.index);
    if (agg_key != .aggregate) {
        try sema.writer.writeAll("elem access: operand is not an indexable aggregate\n");
        return error.AnalysisFail;
    }
    const index = try sema.resolveArrayLen(index_ref, "elem access");
    const count = ip.aggregateElementCount(agg_key.aggregate.ty);
    if (index >= count) {
        try sema.writer.print("index out of bounds: index {d}, len {d}\n", .{ index, count });
        return error.AnalysisFail;
    }
    return .{ .index = InternPool.aggregateElementAt(agg_key.aggregate, index) };
}

/// Resolve a ZIR ref to a `u64` array length or element index:
/// coerce to `usize`, then read the scalar. Lengths and indices are
/// comptime-known integers in every shape AstGen emits here.
fn resolveArrayLen(sema: *Sema, ref: Zir.Inst.Ref, op_name: []const u8) Error!u64 {
    assert(ref != .none);
    return sema.resolveUsizeInt(try sema.resolveRef(ref), op_name);
}

/// Coerce `value` to `usize` and read it as a `u64`. The comptime-known
/// integers that lengths, indices, and alignments are built from always fit.
/// Shared by `resolveArrayLen` (lengths / indices) and `alignmentFromValue`.
fn resolveUsizeInt(sema: *Sema, value: Value, op_name: []const u8) Error!u64 {
    const coerced = try sema.coerceValueToType(value, .usize_type, op_name);
    const key = sema.intern_pool.indexToKey(coerced.index);
    if (key != .int) {
        try sema.writer.print("{s}: expected an integer\n", .{op_name});
        return error.AnalysisFail;
    }
    var space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
    return key.int.storage.toBigInt(&space).toInt(u64) catch {
        try sema.writer.print("{s}: value out of usize range\n", .{op_name});
        return error.AnalysisFail;
    };
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
    // error set. The current subset carries the name only;
    // set-membership checking lands when error-union narrowing
    // handlers do.
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

    const workspace_limbs: usize = std.math.big.int.calcTwosCompLimbCount(dest_info.bits) + 1;
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

    const workspace_limbs: usize = std.math.big.int.calcTwosCompLimbCount(dest_info.bits) + 1;
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
        if (sema.results.get(inst_idx)) |value| {
            // Fold this operand's provenance into the in-flight instruction's
            // accumulator (see `operand_comptime`). Only instruction results
            // can be runtime; the well-known refs below are always comptime.
            sema.operand_comptime = sema.operand_comptime and value.is_comptime;
            return value;
        }
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
    const resolved = try sema.lookupDeclResolved(inst, "decl_val");
    return .{ .index = resolved.value };
}

/// `decl_ref name`: AstGen emits this (rather than `decl_val`) when the use
/// site needs a pointer -- e.g. `a[i]` takes `&a` first, or `&x`. The pointer
/// carries the binding's own constness and alignment (`var`/`const` and
/// `align(N)`), so `@TypeOf(&x)` matches the compiler. Compiler reference:
/// src/Sema.zig:zirDeclRef.
fn evalDeclRef(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const resolved = try sema.lookupDeclResolved(inst, "decl_ref");
    return try sema.pushComptimeAlloc(
        resolved.type,
        .{ .index = resolved.value },
        resolved.@"const",
        resolved.@"align",
    );
}

/// Resolve a `str_tok` decl name against the session namespace to its
/// resolved Nav. Shared by `decl_val` (reads `.value`) and `decl_ref` (also
/// reads `.@"const"` / `.@"align"` for the pointer type).
fn lookupDeclResolved(sema: *Sema, inst: Zir.Inst.Index, op_name: []const u8) Error!InternPool.Nav.Resolved {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const data = sema.zir.instructions.items(.data)[@intFromEnum(inst)].str_tok;
    const name_bytes = data.get(sema.zir);
    const name = try sema.intern_pool.getOrPutString(sema.gpa, name_bytes);

    const ns_idx = sema.namespace orelse {
        try sema.writer.print("{s} '{s}': no namespace in scope\n", .{ op_name, name_bytes });
        return error.AnalysisFail;
    };

    if (try sema.lookupName(ns_idx, name)) |nav_idx| {
        const nav = sema.intern_pool.getNav(nav_idx);
        const resolved = nav.resolved orelse {
            try sema.writer.print(
                "{s} '{s}': binding recorded but value not resolved (test / comptime / extern)\n",
                .{ op_name, name_bytes },
            );
            return error.AnalysisFail;
        };
        if (resolved.value == .none) {
            try sema.writer.print(
                "{s} '{s}': type resolved but value not yet\n",
                .{ op_name, name_bytes },
            );
            return error.AnalysisFail;
        }
        return resolved;
    }

    try sema.writer.print("{s} '{s}': not found in scope\n", .{ op_name, name_bytes });
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
        .@"const", .@"var" => try sema.bindValueDecl(ns_idx, name, decl_inst, unwrapped),
        .@"test", .decltest => try sema.bindTestDecl(ns_idx, name, decl_inst, unwrapped),
        .@"comptime", .unnamed_test => unreachable, // routed above
    }
}

fn bindValueDecl(
    sema: *Sema,
    ns_idx: InternPool.NamespaceIndex,
    name: InternPool.NullTerminatedString,
    decl_inst: Zir.Inst.Index,
    unwrapped: std.zig.Zir.Inst.Declaration.Unwrapped,
) Error!void {
    const value_body = unwrapped.value_body orelse {
        try sema.writer.print(
            "bindDecls '{s}': no value_body (extern decl)\n",
            .{sema.intern_pool.stringSlice(name)},
        );
        return error.AnalysisFail;
    };

    // Resolve the type annotation (`const x: T = ...`) before the
    // value: a result-located init (typed tuple/struct/array literal)
    // refers to the declaration instruction as its result type
    // (`array_init args[0]=%decl`, `array_init_elem_type lhs=%decl`),
    // so `%decl` must already resolve to T. Store it so `resolveRef`
    // finds it. Both bodies break to the declaration instruction.
    const declared_type: ?InternPool.Index = if (unwrapped.type_body) |tb| blk: {
        const t = (try sema.resolveInlineBody(tb, decl_inst)).index;
        try sema.results.put(sema.gpa, decl_inst, .{ .index = t });
        break :blk t;
    } else null;
    const fqn = try sema.intern_pool.fullyQualifiedName(sema.gpa, ns_idx, name);
    const prev_ctx = sema.type_name_ctx;
    sema.type_name_ctx = fqn;
    defer sema.type_name_ctx = prev_ctx;
    const raw_value = try sema.resolveInlineBody(value_body, decl_inst);
    const final_value = if (declared_type) |dest_ty|
        try sema.coerceValueToType(raw_value, dest_ty, "decl")
    else
        raw_value;
    const final_type = if (declared_type) |dest_ty|
        dest_ty
    else
        Value.typeOf(final_value, sema.intern_pool).index;

    // `var x: T align(N)`: the declared alignment, resolved from its body
    // (which breaks to the decl inst, like the type/value bodies). `.none`
    // means natural alignment.
    const declared_align: InternPool.Alignment = if (unwrapped.align_body) |ab|
        try sema.alignmentFromValue(try sema.resolveInlineBody(ab, decl_inst), "decl align")
    else
        .none;

    const nav_idx = try sema.intern_pool.createNav(sema.gpa, name, fqn);
    sema.intern_pool.navPtr(nav_idx).resolved = .{
        .type = final_type,
        .@"align" = declared_align,
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
    // Test bodies stay unevaluated until module loading brings std.testing;
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
    const bin = sema.binData(inst);
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

/// `loop`: read the `pl_node + Block` payload, extract the body
/// slice, delegate to `evalBody`. The body itself terminates via a
/// `break_inline` whose target is this loop instruction (returning
/// the loop's value) or via `repeat` (handled internally by
/// `evalBody`'s i=0 restart). Mirrors the compiler's `zirLoop`
/// (`src/Sema.zig:5102`).
fn evalLoop(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.Block, pl_node.payload_index);
    const body = sema.zir.bodySlice(extra.end, extra.data.body_len);
    return try sema.resolveInlineBody(body, inst);
}

/// `for_len`: the iteration count of a `for` loop -- the length shared by its
/// inputs. The `MultiOp` operands are pairs: `[start, end]` for a range,
/// `[indexable, .none]` for an array/slice (its element count). All inputs are
/// comptime-known here; mismatched lengths are rejected, as the compiler does.
/// The rest of the for loop desugars to primitives already handled (the `|i|`
/// capture is just a `load` of the index counter). Mirrors zirForLen.
fn evalForLen(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.MultiOp, pl_node.payload_index);
    const operands = sema.zir.refSlice(extra.end, extra.data.operands_len);
    const pairs: []const [2]Zir.Inst.Ref =
        @as([*]const [2]Zir.Inst.Ref, @ptrCast(operands.ptr))[0..@divExact(operands.len, 2)];

    var len: ?u64 = null;
    for (pairs) |pair| {
        if (pair[0] == .none) continue;
        const arg_len: u64 = if (pair[1] == .none) blk: {
            const obj = try sema.resolveRef(pair[0]);
            const key = sema.intern_pool.indexToKey(obj.index);
            if (key != .aggregate) {
                try sema.writer.writeAll("for: operand is not a range or indexable\n");
                return error.AnalysisFail;
            }
            break :blk sema.intern_pool.aggregateElementCount(key.aggregate.ty);
        } else blk: {
            const start = try sema.resolveUsizeInt(try sema.resolveRef(pair[0]), "for range start");
            const end = try sema.resolveUsizeInt(try sema.resolveRef(pair[1]), "for range end");
            if (end < start) {
                try sema.writer.writeAll("for: range end is before range start\n");
                return error.AnalysisFail;
            }
            break :blk end - start;
        };
        if (len) |existing| {
            if (existing != arg_len) {
                try sema.writer.writeAll("for: non-matching loop lengths\n");
                return error.AnalysisFail;
            }
        } else len = arg_len;
    }
    const idx = try sema.intern_pool.internInt(.{
        .ty = .usize_type,
        .storage = .{ .u64 = len orelse 0 },
    });
    return .{ .index = idx };
}

/// `switch_block` family: resolve the operand, walk cases via
/// stdlib's `zir.getSwitchBlock`, evaluate the matching prong body.
/// Handles all three tag flavors:
///
///   * `switch_block`     - direct operand.
///   * `switch_block_ref` - operand is a pointer; load through it
///                          first via `loadValue`.
///   * `switch_block_err_union` - operand is an error_union. On the
///                          `.payload` arm runs `non_err_case.body`;
///                          on the `.err_name` arm continues into
///                          case matching where items are
///                          `error_value` names.
///
/// Item kinds covered: `.body_len` (literal / computed item),
/// `.under` (wildcard), `.error_value` (matches err-union err_name).
/// `.enum_literal` items and prong captures land with enum
/// + capture machinery and surface a structured diagnostic.
///
/// Ranges (`range_infos`) use BigInt comparison after coercing both
/// endpoints to the operand type.
///
/// Compiler reference: src/Sema.zig:zirSwitchBlock ~9984.
fn evalSwitchBlock(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const tag = sema.zir.instructions.items(.tag)[@intFromEnum(inst)];
    const sw = sema.zir.getSwitchBlock(inst);

    var operand = try sema.resolveRef(sw.main_operand);
    if (tag == .switch_block_ref) {
        operand = try sema.loadValue(operand);
    }

    // `switch_block_err_union`: dispatch by the error_union's val
    // arm. `non_err_case.operand_is_ref` says the operand is a
    // *EU; the compiler defers the is-err check to runtime via
    // `analyzePtrIsNonErr` vs `analyzeIsNonErr`
    // (src/Sema.zig:9894), keeping the pointer through both
    // branches. We have no AIR to defer to, so the comptime path
    // must materialise the error_union Key now -- if the operand
    // is `Key.ptr`, the only way to reach the .val arm is through
    // the comptime_alloc slot.
    if (tag == .switch_block_err_union) {
        const non_err = sw.non_err_case orelse {
            try sema.writer.writeAll("switch_block_err_union: missing non_err_case\n");
            return error.AnalysisFail;
        };
        if (non_err.operand_is_ref) {
            operand = try sema.loadValue(operand);
        }
        const eu_key = sema.intern_pool.indexToKey(operand.index);
        if (eu_key != .error_union) {
            try sema.writer.writeAll("switch_block_err_union: operand is not an error_union\n");
            return error.AnalysisFail;
        }
        switch (eu_key.error_union.val) {
            .payload => {
                if (non_err.capture != .none) return sema.failSwitch("non-err payload capture");
                return try sema.resolveInlineBody(non_err.body, inst);
            },
            .err_name => {},
        }
    }

    // Either way, `error_value` items match the operand's error
    // name. Bare `Key.err` and the err arm of `Key.error_union`
    // both surface a name we can compare against the item's
    // interned name bytes.
    const operand_err_name: ?InternPool.NullTerminatedString =
        switch (sema.intern_pool.indexToKey(operand.index)) {
            .err => |e| e.name,
            .error_union => |eu| switch (eu.val) {
                .err_name => |n| n,
                .payload => null,
            },
            else => null,
        };

    const op: SwitchOperand = .{
        .value = operand,
        .ty = Value.typeOf(operand, sema.intern_pool).index,
        .err_name = operand_err_name,
    };

    var extra_index: usize = sw.end;
    var it = sw.iterateCases();
    while (it.next()) |case| {
        const prong_body = sema.zir.bodySlice(extra_index, case.prong_info.body_len);
        extra_index += case.prong_info.body_len;

        if (case.prong_info.capture != .none) return sema.failSwitch("prong capture");

        var matched = try sema.matchSwitchItems(inst, case.item_infos, op, &extra_index, false);
        matched = try sema.matchSwitchRanges(inst, case.range_infos, op, &extra_index, matched);

        if (matched) return try sema.resolveInlineBody(prong_body, inst);
    }

    if (sw.else_case) |else_case| {
        if (else_case.capture != .none) return sema.failSwitch("else capture");
        return try sema.resolveInlineBody(else_case.body, inst);
    }

    try sema.writer.writeAll("switch: no matching case and no else\n");
    return error.AnalysisFail;
}

/// The switch operand viewed three ways the case-matchers need: its value
/// (for equality against each item), its type (to coerce items/ranges to),
/// and its error name if any (to match `error_value` items).
const SwitchOperand = struct {
    value: Value,
    ty: InternPool.Index,
    err_name: ?InternPool.NullTerminatedString,
};

/// Match a case's scalar items against `op`, advancing `extra_index` past
/// every item body regardless of `matched` -- the cursor must pass them all,
/// only the comparison short-circuits. Returns whether any item (or an
/// earlier one, via `matched`) matched.
fn matchSwitchItems(
    sema: *Sema,
    inst: Zir.Inst.Index,
    item_infos: []const Zir.Inst.SwitchBlock.ItemInfo,
    op: SwitchOperand,
    extra_index: *usize,
    matched: bool,
) Error!bool {
    var hit = matched;
    for (item_infos) |item_info| {
        switch (item_info.unwrap()) {
            .body_len => |body_len| {
                const item_body = sema.zir.bodySlice(extra_index.*, body_len);
                extra_index.* += body_len;
                if (hit) continue;
                const item_raw = try sema.resolveInlineBody(item_body, inst);
                const item_coerced = try sema.coerceValueToType(item_raw, op.ty, "switch case");
                if (item_coerced.index == op.value.index) hit = true;
            },
            .under => hit = true,
            .error_value => |item_err_name| {
                // Item names live in zir.string_bytes; the operand's
                // error name lives in the intern pool. Compare bytes.
                if (op.err_name) |opn| {
                    const op_bytes = sema.intern_pool.stringSlice(opn);
                    const item_bytes = sema.zir.nullTerminatedString(item_err_name);
                    if (std.mem.eql(u8, op_bytes, item_bytes)) hit = true;
                }
            },
            .enum_literal => return sema.failSwitch("enum_literal switch items"),
        }
    }
    return hit;
}

/// Match a case's `lo...hi` ranges against `op`, advancing `extra_index`
/// past every endpoint body. Like `matchSwitchItems`, the cursor walks all
/// bodies even once matched.
fn matchSwitchRanges(
    sema: *Sema,
    inst: Zir.Inst.Index,
    range_infos: []const [2]Zir.Inst.SwitchBlock.ItemInfo,
    op: SwitchOperand,
    extra_index: *usize,
    matched: bool,
) Error!bool {
    var hit = matched;
    for (range_infos) |range_pair| {
        const lo_len = range_pair[0].bodyLen() orelse 0;
        const hi_len = range_pair[1].bodyLen() orelse 0;
        const lo_body = sema.zir.bodySlice(extra_index.*, lo_len);
        extra_index.* += lo_len;
        const hi_body = sema.zir.bodySlice(extra_index.*, hi_len);
        extra_index.* += hi_len;
        if (hit) continue;
        const lo_raw = try sema.resolveInlineBody(lo_body, inst);
        const hi_raw = try sema.resolveInlineBody(hi_body, inst);
        const lo_co = try sema.coerceValueToType(lo_raw, op.ty, "switch range");
        const hi_co = try sema.coerceValueToType(hi_raw, op.ty, "switch range");
        if (try integerInRange(sema, op.value, lo_co, hi_co)) hit = true;
    }
    return hit;
}

/// `lo <= x <= hi` over the integer-key BigInt representations.
/// Both endpoints have already been coerced to the operand type
/// upstream; this just runs the order comparison.
fn integerInRange(sema: *Sema, x: Value, lo: Value, hi: Value) Error!bool {
    const x_key = sema.intern_pool.indexToKey(x.index);
    const lo_key = sema.intern_pool.indexToKey(lo.index);
    const hi_key = sema.intern_pool.indexToKey(hi.index);
    if (x_key != .int or lo_key != .int or hi_key != .int) {
        try sema.writer.writeAll("switch range: non-integer endpoint\n");
        return error.AnalysisFail;
    }
    var x_space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
    var lo_space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
    var hi_space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
    const x_big = x_key.int.storage.toBigInt(&x_space);
    const lo_big = lo_key.int.storage.toBigInt(&lo_space);
    const hi_big = hi_key.int.storage.toBigInt(&hi_space);
    return x_big.order(lo_big) != .lt and x_big.order(hi_big) != .gt;
}

fn failSwitch(sema: *Sema, what: []const u8) Error {
    try sema.writer.print("unsupported switch construct: {s}\n", .{what});
    return error.AnalysisFail;
}

/// `.param` / `.param_comptime`: evaluate the param's type body
/// (break_target is the param inst itself, mirroring
/// src/Sema.zig:zirParam ~9031) and push onto `params`
/// for the enclosing `.func` to drain. `.is_generic` params
/// surface a structured diagnostic -- generics are unsupported.
fn evalParam(sema: *Sema, inst: Zir.Inst.Index, tag: Zir.Inst.Tag) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const pl_tok = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_tok;
    const extra = sema.zir.extraData(Zir.Inst.Param, pl_tok.payload_index);
    if (extra.data.type.is_generic) {
        try sema.writer.writeAll("generic parameter types not yet supported\n");
        return error.AnalysisFail;
    }
    const body = sema.zir.bodySlice(extra.end, extra.data.type.body_len);
    const ty_value = try sema.resolveInlineBody(body, inst);
    try sema.block.params.append(sema.gpa, .{
        .ty = ty_value.index,
        .is_comptime = tag == .param_comptime,
    });
    return null;
}

fn failAnytypeParam(sema: *Sema) Error {
    try sema.writer.writeAll("anytype parameters not yet supported\n");
    return error.AnalysisFail;
}

/// `ret_type`: the declared return type of the function whose body is being
/// evaluated. AstGen emits it to reference a non-trivial return type -- one
/// computed in a `ret_ty_body` (e.g. `u23`) rather than a pre-interned ref
/// like `i32` -- from within the body. `evalCall` sets `fn_ret_ty` around the
/// body, so it is never `.none` here.
fn evalRetType(sema: *Sema) Error!?Value {
    assert(sema.fn_ret_ty != .none);
    return .{ .index = sema.fn_ret_ty };
}

/// `.func` / `.func_inferred` / `.func_fancy`: build the Func
/// type from the drained `params` + the resolved return
/// type, intern both, return the Func value. Uses stdlib's
/// `getFnInfo` to abstract the three Inst layouts. Compiler
/// reference: src/Sema.zig:zirFunc ~8321 + funcCommon ~8896.
///
/// CC defaults to `.auto` here regardless of `func_fancy`'s
/// cc_ref / cc_body -- same minimal calling-convention storage
/// documented at the FuncType storage site (FFI widens). The inferred-
/// error-set flag (`.func_inferred`) is observed via `getFnInfo`
/// but doesn't affect the FuncType encoding today; it'll matter
/// when error-set inference moves out of the per-fn analysis.
/// Resolve a function's declared return type from its ZIR: a pre-interned
/// `ret_ty_ref` (e.g. `i32`), else a computed `ret_ty_body` (e.g. `u23`),
/// else `void`. `break_target` is the func inst the body breaks to. For a
/// generic signature the ref/body references an unbound param, so this is
/// meaningful only after `evalCall` binds the comptime args; at definition
/// time `evalFunc` stores the poison marker instead.
fn resolveDeclaredRetType(sema: *Sema, info: Zir.FnInfo, break_target: Zir.Inst.Index) Error!InternPool.Index {
    if (info.ret_ty_ref != .none) return (try sema.resolveRef(info.ret_ty_ref)).index;
    if (info.ret_ty_body.len > 0) return (try sema.resolveInlineBody(info.ret_ty_body, break_target)).index;
    return .void_type;
}

fn evalFunc(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const info = sema.zir.getFnInfo(inst);

    // A generic signature's return type depends on a comptime argument
    // (`fn make(comptime T: type) T`): its ref/body points at a param that
    // has no value until a call binds one. Store the poison marker now;
    // `evalCall` re-resolves the concrete type per instantiation. Mirrors
    // funcCommon (src/Sema.zig), which interns generic_poison_type here.
    const ret_ty: InternPool.Index = if (info.ret_ty_is_generic)
        .generic_poison_type
    else
        try sema.resolveDeclaredRetType(info, inst);

    const params = try sema.gpa.alloc(InternPool.Index, sema.block.params.items.len);
    defer sema.gpa.free(params);
    var comptime_bits: u32 = 0;
    for (sema.block.params.items, 0..) |pp, i| {
        params[i] = pp.ty;
        if (pp.is_comptime) comptime_bits |= @as(u32, 1) << @intCast(i);
    }
    sema.block.params.clearRetainingCapacity();

    const fn_ty = try sema.intern_pool.internFuncType(.{
        .param_types = params,
        .return_type = ret_ty,
        .comptime_bits = comptime_bits,
    });
    // No body -> this is a fn TYPE expression (`fn () void`),
    // not a fn declaration. Return the FuncType Index directly
    // as the type-of-type value. Mirrors the compiler's
    // funcCommon at src/Sema.zig:9004 which interns just the
    // FuncType when `has_body == false`.
    if (info.body.len == 0) return Value{ .index = fn_ty };

    const func_idx = try sema.intern_pool.internFunc(.{
        .source_zir_id = sema.current_zir_id,
        .ty = fn_ty,
        .uncoerced_ty = fn_ty,
        .zir_body_inst = inst,
    });
    return Value{ .index = func_idx };
}

/// `.call` / `.field_call`: invoke a comptime-resolvable function
/// value with args. Mirrors src/Sema.zig:zirCall ~6125 +
/// analyzeCall ~6539 for the comptime slice:
///
///   1. Resolve the callee Value; require Key.func.
///   2. Read args_len from Inst.Call's Flags.
///   3. Walk per-arg bodies (stride table at extra[end..],
///      first args_len entries are end-offsets) and evaluate
///      each via resolveInlineBody (break_target = call inst).
///   4. Coerce each arg to its FuncType param type.
///   5. Get fn body via getFnInfo; filter param_body for .param
///      tags to obtain the param inst indices.
///   6. Pre-populate sema.results so the fn body's references to
///      param insts resolve to the bound arg values.
///   7. Evaluate fn body via resolveInlineBody.
///   8. Remove the param-binding entries from results so other
///      callers of the same func get a clean slate.
///
/// `.field_call` (`a.foo(x)`) needs type-method resolution which
/// requires struct support; surfaces a structured diagnostic.
fn evalCall(sema: *Sema, inst: Zir.Inst.Index, comptime kind: enum { direct, field }) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    // Bound recursion as the compiler does: every call is a backward branch
    // against `branch_quota` (`analyzeCall` -> `emitBackwardBranch`), which
    // also catches runaway non-recursive evaluation. Raise via
    // `@setEvalBranchQuota` once that builtin lands.
    try sema.emitBackwardBranch();

    if (kind == .field) {
        try sema.writer.writeAll("field_call: method-call resolution requires struct support\n");
        return error.AnalysisFail;
    }

    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.Call, pl_node.payload_index);
    const args_len: u32 = extra.data.flags.args_len;

    const callee_value = try sema.resolveRef(extra.data.callee);
    const callee_key = sema.intern_pool.indexToKey(callee_value.index);
    if (callee_key != .func) {
        try sema.writer.writeAll("call: callee is not a function value\n");
        return error.AnalysisFail;
    }
    const func = callee_key.func;
    const func_ty = sema.intern_pool.indexToKey(func.ty).func_type;

    if (func_ty.param_types.len != args_len) {
        try sema.writer.print(
            "call: expected {d} args, got {d}\n",
            .{ func_ty.param_types.len, args_len },
        );
        return error.AnalysisFail;
    }

    // Walk arg bodies via the stride table. args_body[0..args_len]
    // holds end-offsets; arg N's body is args_body[start..end] where
    // start is `args_len` for N=0 or `args_body[N-1]` otherwise.
    const args_body: []const Zir.Inst.Index = @ptrCast(sema.zir.extra[extra.end..]);
    const arg_values = try sema.evalCallArgs(inst, func_ty, args_body);
    defer sema.gpa.free(arg_values);

    // Swap sema.zir to the func's source-ZIR snapshot when the
    // call crosses a REPL line boundary. The common same-line
    // case (current_zir_id == func.source_zir_id) skips the swap.
    // Restored via defer so subsequent instructions in the
    // caller's body see the caller's zir again.
    const caller_zir = sema.zir;
    if (func.source_zir_id != sema.current_zir_id) {
        if (func.source_zir_id >= sema.line_zir.len) {
            try sema.writer.writeAll("call: function's source ZIR is no longer available\n");
            return error.AnalysisFail;
        }
        sema.zir = sema.line_zir[func.source_zir_id];
    }
    defer sema.zir = caller_zir;

    // Extract the body + param insts via getFnInfo on the
    // possibly-swapped sema.zir.
    const info = sema.zir.getFnInfo(func.zir_body_inst);
    const param_insts = try sema.collectParamInsts(info, args_len);
    defer sema.gpa.free(param_insts);

    // Each call frame needs its own results map. The fn body's
    // intermediate instruction results (n - 1, the inner call's
    // return, etc.) share inst indices across recursive frames
    // because the body's ZIR is the same; without isolation the
    // inner frame's writes pollute the outer frame's reads.
    // Swap in a fresh empty map for the body eval; restore the
    // caller's map on exit. Param bindings go on the fresh map
    // so the body's references resolve to the bound args.
    const saved_results = sema.results;
    sema.results = .empty;
    defer {
        sema.results.deinit(sema.gpa);
        sema.results = saved_results;
    }
    for (param_insts, arg_values) |p_inst, val| {
        try sema.results.put(sema.gpa, p_inst, val);
    }

    // Expose the return type to the body's `ret_type` instruction; restore
    // the caller's on exit so nested calls each see their own. A generic
    // return was stored as the poison marker at definition (`evalFunc`); now
    // that the comptime args are bound, the param ref/body it points at
    // re-resolves to the concrete type for this instantiation.
    const saved_ret_ty = sema.fn_ret_ty;
    sema.fn_ret_ty = if (func_ty.return_type == .generic_poison_type)
        try sema.resolveDeclaredRetType(info, func.zir_body_inst)
    else
        func_ty.return_type;
    defer sema.fn_ret_ty = saved_ret_ty;

    // Fn body terminates via `return X;` (ret_node /
    // ret_implicit / ret_load) raising ComptimeReturn; catch it
    // and surface the stashed value. Bare resolveInlineBody
    // would propagate the error past the call site.
    if (sema.resolveInlineBody(info.body, func.zir_body_inst)) |val| {
        return val;
    } else |err| switch (err) {
        // Coerce the returned value to the declared return type -- the
        // coercion the compiler does in its `ret_node` handling against
        // `fn_ret_ty`, which AstGen leaves to Sema. Done here (rather than a
        // pushed/popped `fn_ret_ty` + per-ret-arm) since a call yields one
        // return value. A return derived from a runtime parameter coerces
        // type-based, so `fn (a: u32) i32 { return a; }` is rejected as the
        // compiler rejects it; a comptime-known return coerces value-based.
        error.ComptimeReturn => return try sema.coerceValueToType(sema.return_value, sema.fn_ret_ty, "return"),
        else => |e| return e,
    }
}

/// Resolve and coerce each call argument to its declared parameter type.
/// Returns a freshly allocated slice (caller frees). Each result's
/// `is_comptime` is seeded from the parameter's `comptime`-ness: a
/// non-`comptime` parameter is runtime inside the body even when the call
/// site passed a comptime argument, so coercions of it (and values derived
/// from it) follow Zig's runtime, type-based rule.
fn evalCallArgs(
    sema: *Sema,
    inst: Zir.Inst.Index,
    func_ty: InternPool.Key.FuncType,
    args_body: []const Zir.Inst.Index,
) Error![]Value {
    const args_len: u32 = @intCast(func_ty.param_types.len);
    const arg_values = try sema.gpa.alloc(Value, args_len);
    errdefer sema.gpa.free(arg_values);
    for (0..args_len) |i| {
        const start = if (i == 0) args_len else @intFromEnum(args_body[i - 1]);
        const end = @intFromEnum(args_body[i]);
        const arg_body = args_body[start..end];
        const raw = try sema.resolveInlineBody(arg_body, inst);
        arg_values[i] = try sema.coerceValueToType(raw, func_ty.param_types[i], "call arg");
        arg_values[i].is_comptime = func_ty.paramIsComptime(@intCast(i));
    }
    return arg_values;
}

/// Collect the function body's parameter instructions into a freshly
/// allocated slice (caller frees), one per argument in declaration order.
/// AstGen interleaves non-`param` insts in the param body; only the four
/// `param*` tags name a parameter binding.
fn collectParamInsts(sema: *Sema, info: Zir.FnInfo, args_len: u32) Error![]Zir.Inst.Index {
    const tags = sema.zir.instructions.items(.tag);
    const param_insts = try sema.gpa.alloc(Zir.Inst.Index, args_len);
    errdefer sema.gpa.free(param_insts);
    var pi: u32 = 0;
    for (info.param_body) |param_inst| {
        switch (tags[@intFromEnum(param_inst)]) {
            .param, .param_comptime, .param_anytype, .param_anytype_comptime => {
                if (pi >= args_len) break;
                param_insts[pi] = param_inst;
                pi += 1;
            },
            else => continue,
        }
    }
    assert(pi == args_len);
    return param_insts;
}

/// `.block_comptime`: identical to `.block` for our comptime-only
/// Sema, the only difference being the extra carries a `reason`
/// (`std.zig.SimpleComptimeReason`) we don't observe today.
/// Compiler reference: src/Sema.zig:1737 (zirBlockComptime) which
/// makes the child block's comptime status explicit; we always
/// run at comptime so the body resolves the same way as for
/// `.block`.
fn evalBlockComptime(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.BlockComptime, pl_node.payload_index);
    const body = sema.zir.bodySlice(extra.end, extra.data.body_len);
    return try sema.resolveInlineBody(body, inst);
}

/// `.typeof`: `@TypeOf(x)` single-arg form. Reads the operand,
/// returns its type as a type-of-type value. Mirrors
/// src/Sema.zig:zirTypeof ~16860.
fn evalTypeof(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    const operand = try sema.resolveRef(un_node.operand);
    return Value{ .index = Value.typeOf(operand, sema.intern_pool).index };
}

/// `.typeof_builtin`: `@TypeOf(...)` body-form -- AstGen wraps
/// the operand expression in an Inst.Block so the type-context
/// (`is_typeof`) can short-circuit certain analyses. Resolves
/// the body's break value via resolveInlineBody (break_target is
/// this inst), returns the resulting value's type. Mirrors
/// src/Sema.zig:zirTypeofBuiltin ~16869.
fn evalTypeofBuiltin(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.Block, pl_node.payload_index);
    const body = sema.zir.bodySlice(extra.end, extra.data.body_len);
    const operand = try sema.resolveInlineBody(body, inst);
    return Value{ .index = Value.typeOf(operand, sema.intern_pool).index };
}

/// Sub-dispatcher for the `.extended` ZIR tag. The data union arm
/// carries `(opcode, small, operand)`; each `Zir.Inst.Extended`
/// opcode names a distinct builtin / construct. Mirrors the
/// compiler's `.extended => ext: { switch (opcode) ... }` at
/// src/Sema.zig:1382. Implemented today:
///
///   * `dbg_empty_stmt`, `breakpoint`, `disable_instrumentation`,
///     `disable_intrinsics`, `branch_hint`, `set_float_mode`,
///     `restore_err_ret_index` -- no-ops at our level (no AIR, no
///     instrumentation, no error-return-trace machinery yet).
///   * `in_comptime` -- honest `false`; we have no comptime/runtime
///     bifurcation so the spec branch is the runtime one.
///   * `tuple_decl` -- a positional struct type (`struct { i32, f128 }`).
///   * `struct_decl` -- a named struct type (`struct { x: i32 }`).
///
/// Every other opcode surfaces a structured
/// "unsupported extended opcode: <name>" diagnostic; the `inline
/// else` expansion ensures stdlib adding a new Opcode variant
/// keeps compiling but routes through the same fallback.
fn evalExtended(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const extended = sema.zir.instructions.items(.data)[@intFromEnum(inst)].extended;
    switch (extended.opcode) {
        .dbg_empty_stmt,
        .breakpoint,
        .disable_instrumentation,
        .disable_intrinsics,
        .branch_hint,
        .set_float_mode,
        .restore_err_ret_index,
        => return null,

        .in_comptime => return Value.bool_false,

        .tuple_decl => return sema.evalTupleDecl(extended),
        .struct_decl => return sema.evalStructDecl(inst),

        // The result type for a compound assignment (`s += x`, `s -= x`): the
        // lhs's own type, against which the rhs is coerced before the arith +
        // store-back. Mirrors zirInplaceArithResultTy's non-pointer case;
        // pointer arithmetic (its `[*]T`/`[*c]T` special cases) is unsupported,
        // so a pointer lhs yields its own type and the following arith rejects it.
        .inplace_arith_result_ty => {
            const lhs = try sema.resolveRef(@enumFromInt(extended.operand));
            return Value{ .index = Value.typeOf(lhs, sema.intern_pool).index };
        },

        // Bridge into std.lang.* (CallingConvention, AtomicOrder,
        // AddressSpace, ...). Compiler reference:
        // src/Sema.zig:zirStdLangValue ~24709 + getStdLangType.
        // Full end-to-end requires the `std` module loader
        // -- without it we have no interned Type for the std.lang
        // container. Surface as a named diagnostic so the gap is
        // visible (vs the generic `inline else` fallback).
        .std_lang_value => {
            const small: std.zig.Zir.Inst.StdLangValue = @enumFromInt(extended.small);
            try sema.writer.print(
                "extended.std_lang_value(.{s}): std.lang access requires module loading\n",
                .{@tagName(small)},
            );
            return error.AnalysisFail;
        },

        inline else => |op| {
            try sema.writer.print("unsupported extended ZIR opcode: {s}\n", .{@tagName(op)});
            return error.AnalysisFail;
        },
    }
}

fn reportUnsupportedTag(sema: *Sema, comptime tag: Zir.Inst.Tag) Error {
    try sema.writer.print("unsupported ZIR instruction: {s}\n", .{@tagName(tag)});
    return error.AnalysisFail;
}
