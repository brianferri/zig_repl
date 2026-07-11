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
const render_value = @import("../render/Value.zig");
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
/// Scratch allocator freed at the end of this evaluation, mirroring the
/// compiler's `sema.arena` (freed at end-of-analysis). Backs short-lived
/// structures that outlive a single call but not the evaluation, such as an
/// `InMemoryCoercionResult`'s nested reason tree.
arena: Allocator,
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
/// Synthetic addresses handed out to `.nav` / `.uav` pointers, keyed by the
/// interned pointer value. Interned pointers dedup, so equal pointers reuse one
/// address -- `@intFromPtr(&x) == @intFromPtr(&x)` holds. (A `.comptime_alloc`
/// caches its address inline on the slot instead; those slots are not interned.)
synthetic_addresses: std.AutoHashMapUnmanaged(InternPool.Index, u64) = .empty,
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
/// The owning session, holding every lowered file (`session.files`) plus the
/// `@import` byte source and dedup table. A Func or container type carries a
/// `source_zir_id` (a `File.Index`); crossing into that file's ZIR reads it
/// from `session.files`. `null` in pure-Sema test paths (no session), which
/// never cross files or import.
session: ?*Session = null,
/// The `File.Index` of the file being analysed. A type or Func defined here
/// records it as its `source_zir_id`, so a later pass can swap `sema.zir` back
/// to this file (`evalCall` compares against `func.source_zir_id`).
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
/// The type `@This()` resolves to -- the innermost container whose member is
/// being evaluated. `.none` outside a container member. Mirrors the compiler's
/// `block.namespace.owner_type`: one slot, set around a member's evaluation
/// (`containerDeclByName`). Enclosing containers are reached through each container
/// type's `parent` field (the compiler's `Namespace.parent`), which `evalDeclVal`
/// walks -- so this being a single slot is faithful, not a nesting limit.
this_type: InternPool.Index = .none,

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
/// The ZIR to analyse is the file already appended at `file_index`
/// (`session.files`); the driver reserves that slot before calling so a module
/// loaded mid-analysis takes a later `File.Index` and never collides.
pub fn analyze(session: *Session, file_index: Session.Index, writer: *std.Io.Writer) Error!?Value {
    const gpa = session.gpa;
    const intern_pool = session.intern_pool;
    const namespace = session.root_namespace;
    const zir = session.files.items[file_index].zir.?;
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

    var arena_instance = std.heap.ArenaAllocator.init(gpa);
    defer arena_instance.deinit();

    var sema: Sema = .{
        .gpa = gpa,
        .arena = arena_instance.allocator(),
        .intern_pool = intern_pool,
        .zir = zir,
        .writer = writer,
        .results = .empty,
        .comptime_allocs = .empty,
        .namespace = namespace,
        .block = &top_block,
        .session = session,
        .current_zir_id = file_index,
    };
    defer sema.results.deinit(gpa);
    defer sema.comptime_allocs.deinit(gpa);
    defer sema.synthetic_addresses.deinit(gpa);

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
        .str => sema.evalStr(inst),
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
        .sqrt => sema.evalUnaryMath(inst, Value.sqrt),
        .sin => sema.evalUnaryMath(inst, Value.sin),
        .cos => sema.evalUnaryMath(inst, Value.cos),
        .tan => sema.evalUnaryMath(inst, Value.tan),
        .exp => sema.evalUnaryMath(inst, Value.exp),
        .exp2 => sema.evalUnaryMath(inst, Value.exp2),
        .log => sema.evalUnaryMath(inst, Value.log),
        .log2 => sema.evalUnaryMath(inst, Value.log2),
        .log10 => sema.evalUnaryMath(inst, Value.log10),
        .floor => sema.evalUnaryMath(inst, Value.floor),
        .ceil => sema.evalUnaryMath(inst, Value.ceil),
        .round => sema.evalUnaryMath(inst, Value.round),
        .trunc => sema.evalUnaryMath(inst, Value.trunc),
        .mul_add => sema.evalMulAdd(inst),
        .min => sema.evalMinMax(inst, .min),
        .max => sema.evalMinMax(inst, .max),
        .reduce => sema.evalReduce(inst),
        .abs => sema.evalAbs(inst),
        .bit_not => sema.evalBitNot(inst),
        .ptr_type => sema.evalPtrType(inst),
        .align_of => sema.evalAlignOf(inst),
        .size_of => sema.evalSizeOf(inst),
        .bit_size_of => sema.evalBitSizeOf(inst),
        .clz => sema.evalBitCount(inst, Value.clz),
        .ctz => sema.evalBitCount(inst, Value.ctz),
        .pop_count => sema.evalBitCount(inst, Value.popCount),
        .byte_swap => sema.evalByteSwap(inst),
        .bit_reverse => sema.evalBitReverse(inst),
        .int_from_ptr => sema.evalIntFromPtr(inst),
        .int_from_enum => sema.evalIntFromEnum(inst),
        .tag_name => sema.evalTagName(inst),
        .enum_from_int => sema.evalEnumFromInt(inst),
        .decl_literal => sema.evalDeclLiteral(inst, true),
        .decl_literal_no_coerce => sema.evalDeclLiteral(inst, false),
        .enum_literal => sema.evalEnumLiteral(inst),
        .int_from_bool => sema.evalIntFromBool(inst),
        .alloc, .alloc_mut, .alloc_comptime_mut => sema.evalAlloc(inst),
        .ret_ptr => sema.evalRetPtr(),
        .alloc_inferred, .alloc_inferred_comptime => sema.evalAllocInferred(true),
        .alloc_inferred_mut, .alloc_inferred_comptime_mut => sema.evalAllocInferred(false),
        .store_to_inferred_ptr => sema.evalStoreToInferredPtr(inst),
        .resolve_inferred_alloc => sema.evalResolveInferredAlloc(inst),
        .make_ptr_const => sema.evalMakePtrConst(inst),
        .store_node => sema.evalStoreNode(inst),
        .struct_init_field_ptr => sema.evalFieldPtr(inst, true),
        .field_ptr => sema.evalFieldPtr(inst, false),
        .field_ptr_named => sema.evalFieldPtrNamed(inst),
        .field_ptr_load => sema.evalFieldPtrLoad(inst),
        .field_ptr_named_load => sema.evalFieldPtrNamedLoad(inst),
        .has_field => sema.evalHasField(inst),
        .has_decl => sema.evalHasDecl(inst),
        .opt_eu_base_ptr_init => sema.evalOptEuBasePtrInit(inst),
        .validate_ptr_struct_init => sema.evalValidatePtrStructInit(inst),
        .validate_struct_init_ty => sema.evalValidateStructInitTy(inst, false),
        .validate_struct_init_result_ty => sema.evalValidateStructInitTy(inst, true),
        .struct_init_field_type => sema.evalStructInitFieldType(inst),
        .struct_init => sema.evalStructInit(inst, false),
        .struct_init_ref => sema.evalStructInit(inst, true),
        .struct_init_empty => sema.evalStructInitEmpty(inst),
        .deref => sema.evalDeref(inst),
        .ref_deref => sema.evalRefDeref(inst),
        .validate_ref_ty => sema.evalValidateRefTy(inst),
        .coerce_ptr_elem_ty => sema.evalCoercePtrElemTy(inst),
        .load => sema.evalLoad(inst),
        .decl_val => sema.evalDeclVal(inst),
        .decl_ref => sema.evalDeclRef(inst),
        .error_set_decl => sema.evalErrorSetDecl(inst),
        .error_value => sema.evalErrorValue(inst),
        .error_union_type => sema.evalErrorUnionType(inst),
        // Async never landed in the self-hosted compiler; every frame/async form
        // resolves to the same diagnostic (`failWithUseOfAsync`).
        .anyframe_type, .frame_type, .suspend_block, .@"resume" => sema.failUseOfAsync(),
        .err_union_code => sema.evalErrUnionCode(inst),
        .err_union_code_ptr => sema.evalErrUnionCodePtr(inst),
        .err_union_payload_unsafe => sema.evalErrUnionPayloadUnsafe(inst),
        .err_union_payload_unsafe_ptr => sema.evalErrUnionPayloadUnsafePtr(inst),
        .is_non_err => sema.evalIsNonErr(inst),
        .is_non_err_ptr => sema.evalIsNonErrPtr(inst),
        .ret_is_non_err => sema.evalRetIsNonErr(inst),
        .ensure_err_union_payload_void => sema.evalEnsureErrUnionPayloadVoid(inst),
        .@"try" => sema.evalTry(inst),
        .try_ptr => sema.evalTryPtr(inst),
        .loop => sema.evalLoop(inst),
        .for_len => sema.evalForLen(inst),
        .switch_block,
        .switch_block_ref,
        .switch_block_err_union,
        => sema.evalSwitchBlock(inst),
        .param, .param_comptime => sema.evalParam(inst, tag),
        .param_anytype, .param_anytype_comptime => sema.evalParamAnytype(tag),
        .func, .func_inferred, .func_fancy => sema.evalFunc(inst),
        .typeof => sema.evalTypeof(inst),
        .typeof_builtin => sema.evalTypeofBuiltin(inst),
        .ret_type => sema.evalRetType(),
        .call => sema.evalCall(inst, .direct),
        .field_call => sema.evalCall(inst, .field),
        .block_comptime => sema.evalBlockComptime(inst),
        // Error-return-trace bookkeeping: no runtime trace exists at comptime, so
        // save/restore are no-ops (the compiler also lowers them away comptime).
        .save_err_ret_index,
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
        .reify_int => sema.evalReifyInt(inst),
        .vector_type => sema.evalVectorType(inst),
        .optional_type => sema.evalOptionalType(inst),
        .optional_payload_safe, .optional_payload_unsafe => sema.evalOptionalPayload(inst),
        .optional_payload_safe_ptr, .optional_payload_unsafe_ptr => sema.evalOptionalPayloadPtr(inst),
        .is_non_null => sema.evalIsNonNull(inst),
        .array_type => sema.evalArrayType(inst),
        .array_type_sentinel => sema.evalArrayTypeSentinel(inst),
        .array_init => sema.evalArrayInit(inst),
        .array_init_ref => sema.evalArrayInitRef(inst),
        .array_init_anon => sema.evalArrayInitAnon(inst),
        .struct_init_anon => sema.evalStructInitAnon(inst),
        .struct_init_empty_result => sema.evalStructInitEmptyResult(inst, false),
        .struct_init_empty_ref_result => sema.evalStructInitEmptyResult(inst, true),
        .import => sema.evalImport(inst),
        .type_info => sema.evalTypeInfo(inst),
        .array_init_elem_type => sema.evalArrayInitElemType(inst),
        .elem_type => sema.evalElemType(inst),
        .splat_op_result_ty => sema.evalSplatOpResultType(inst),
        .splat => sema.evalSplat(inst),
        .shuffle => sema.evalShuffle(inst),
        .validate_array_init_ty => sema.evalValidateArrayInitTy(inst, false),
        .validate_array_init_result_ty => sema.evalValidateArrayInitTy(inst, true),
        .validate_array_init_ref_ty => sema.evalValidateArrayInitRefTy(inst),
        .ref => sema.evalRef(inst),
        .elem_ptr_load => sema.evalElemPtrLoad(inst),
        // `elem_ptr` is the for-loop by-ref capture (`for (&arr) |*e|`), `_node`
        // is `&arr[i]`; both take a pointer operand and project one element, so
        // they share a handler (the compiler differs only in a diagnostic).
        .elem_ptr, .elem_ptr_node => sema.evalElemPtrNode(inst),
        .elem_val => sema.evalElemVal(inst),
        .memcpy => sema.evalMemcpy(inst),
        .slice_start => sema.evalSliceStart(inst),
        .slice_end => sema.evalSliceEnd(inst),
        .slice_sentinel => sema.evalSliceSentinel(inst),
        .slice_sentinel_ty => sema.evalSliceSentinelTy(inst),
        .slice_length => sema.evalSliceLength(inst),
        .array_init_elem_ptr => sema.evalArrayInitElemPtr(inst),
        .validate_ptr_array_init => sema.evalValidatePtrArrayInit(inst),
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

/// `str "..."`: a string literal, `*const [N:0]u8`. Mirrors zirStr -> addStrLit.
fn evalStr(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const bytes = sema.zir.instructions.items(.data)[@intFromEnum(inst)].str.get(sema.zir);
    return try sema.internStringLiteral(bytes);
}

/// Build a string-literal value: a `[N:0]u8` array (each byte a `u8`, plus the
/// trailing 0 sentinel) behind a const pointer, `*const [N:0]u8`. Mirrors
/// `addStrLit` -> `uavRef`. The compiler uses the aggregate `bytes` storage; this
/// evaluator has only `elems` storage, so the bytes are interned one `u8` per slot
/// until a `bytes` flavor lands. Shared by `str` and `@tagName`.
fn internStringLiteral(sema: *Sema, bytes: []const u8) Error!Value {
    const ip = sema.intern_pool;
    const u8_zero = try ip.internInt(.{ .ty = .u8_type, .storage = .{ .u64 = 0 } });
    const array_ty = try ip.internArrayType(.{ .len = bytes.len, .child = .u8_type, .sentinel = u8_zero });

    const elems = try sema.gpa.alloc(InternPool.Index, bytes.len + 1);
    defer sema.gpa.free(elems);
    for (bytes, 0..) |b, i| elems[i] = try ip.internInt(.{ .ty = .u8_type, .storage = .{ .u64 = b } });
    elems[bytes.len] = u8_zero; // the sentinel slot

    const array_val = try ip.internAggregate(.{ .ty = array_ty, .storage = .{ .elems = elems } });
    return try sema.materializeConstPtr(.{ .index = array_val });
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
pub fn intValue_big(sema: *Sema, ty: Type, x: std.math.big.int.Const) Error!Value {
    return .fromIndex(try sema.intern_pool.internIntValue(ty.index, x));
}

pub fn intValue_u64(sema: *Sema, ty: Type, x: u64) Error!Value {
    return .fromIndex(try sema.intern_pool.internInt(.{ .ty = ty.index, .storage = .{ .u64 = x } }));
}

pub fn intValue_i64(sema: *Sema, ty: Type, x: i64) Error!Value {
    return .fromIndex(try sema.intern_pool.internInt(.{ .ty = ty.index, .storage = .{ .i64 = x } }));
}

pub fn undefValue(sema: *Sema, ty: Type) Error!Value {
    return .fromIndex(try sema.intern_pool.get(.{ .undef = ty.index }));
}

pub fn aggregateSplatValue(sema: *Sema, ty: Type, repeated_elem: Value) Error!Value {
    if (repeated_elem.isUndef(sema.intern_pool)) return sema.undefValue(ty);
    return .fromIndex(try sema.intern_pool.internAggregate(.{ .ty = ty.index, .storage = .{ .repeated_elem = repeated_elem.index } }));
}

pub fn aggregateValue(sema: *Sema, ty: Type, elems: []const InternPool.Index) Error!Value {
    return .fromIndex(try sema.intern_pool.internAggregate(.{ .ty = ty.index, .storage = .{ .elems = elems } }));
}

pub fn vectorType(sema: *Sema, info: InternPool.Key.VectorType) Error!Type {
    return .fromIndex(try sema.intern_pool.internVectorType(info));
}

/// Bits needed to represent `val` as an integer: twos-complement signed if
/// `sign`, else unsigned. Ports `intBitsForValue` (`src/Zcu/PerThread.zig`).
fn intBitsForValue(sema: *Sema, val: Value, sign: bool) u16 {
    switch (sema.intern_pool.indexToKey(val.index).int.storage) {
        .i64 => |x| {
            if (std.math.cast(u64, x)) |casted| return Type.smallestUnsignedBits(casted) + @intFromBool(sign);
            assert(sign);
            if (x == std.math.minInt(i64)) return 64;
            return Type.smallestUnsignedBits(@as(u64, @intCast(-(x + 1)))) + 1;
        },
        .u64 => |x| return Type.smallestUnsignedBits(x) + @intFromBool(sign),
        .big_int => |big| {
            if (big.positive) return @intCast(big.bitCountAbs() + @intFromBool(sign));
            if (big.eqlZero()) return 0;
            return @intCast(big.bitCountTwosComp());
        },
    }
}

/// Smallest int type holding the inclusive range `[min, max]`. Ports
/// `intFittingRange` (`src/Zcu/PerThread.zig`).
fn intFittingRange(sema: *Sema, min: Value, max: Value) Error!Type {
    const pool = sema.intern_pool;
    assert(!min.isUndef(pool));
    assert(!max.isUndef(pool));
    const sign = min.compareHetero(.lt, Value.zero_comptime_int, pool);
    const min_val_bits = sema.intBitsForValue(min, sign);
    const max_val_bits = sema.intBitsForValue(max, sign);
    return .fromIndex(try pool.internIntType(if (sign) .signed else .unsigned, @max(min_val_bits, max_val_bits)));
}

pub fn failWithUseOfUndef(sema: *Sema) Error {
    try sema.writer.writeAll("use of undefined value here causes illegal behavior\n");
    return error.AnalysisFail;
}

pub fn failWithDivideByZero(sema: *Sema) Error {
    try sema.writer.writeAll("division by zero here causes illegal behavior\n");
    return error.AnalysisFail;
}

pub fn failWithIntegerOverflow(sema: *Sema, ty: Type, val: Value) Error {
    try sema.writer.writeAll("overflow of integer type '");
    try Type.print(ty, sema.intern_pool, sema.writer);
    try sema.writer.writeAll("' with value '");
    try render_value.render(val, sema.intern_pool, sema.writer);
    try sema.writer.writeAll("'\n");
    return error.AnalysisFail;
}

pub fn failWithNegativeShiftAmount(sema: *Sema, shift_amt: Value) Error {
    try sema.writer.writeAll("shift by negative amount '");
    try render_value.render(shift_amt, sema.intern_pool, sema.writer);
    try sema.writer.writeAll("'\n");
    return error.AnalysisFail;
}

pub fn failWithTooLargeShiftAmount(sema: *Sema, ty: Type, shift_amt: Value) Error {
    try sema.writer.writeAll("shift amount '");
    try render_value.render(shift_amt, sema.intern_pool, sema.writer);
    try sema.writer.writeAll("' is too large for operand type '");
    try Type.print(ty, sema.intern_pool, sema.writer);
    try sema.writer.writeAll("'\n");
    return error.AnalysisFail;
}

pub fn failWithUnsupportedComptimeShiftAmount(sema: *Sema) Error {
    try sema.writer.writeAll("this implementation only supports comptime shift amounts of up to 2^64 - 1 bits\n");
    return error.AnalysisFail;
}

fn evalBinaryArith(sema: *Sema, inst: Zir.Inst.Index, tag: Zir.Inst.Tag) Error!?Value {
    const bin = sema.binData(inst);
    assert(bin.lhs != .none);
    assert(bin.rhs != .none);

    const op_name: []const u8 = @tagName(tag);
    const lhs_val = try sema.resolveRef(bin.lhs);
    const rhs_val = try sema.resolveRef(bin.rhs);

    const resolved_type = try sema.resolveArithPeerType(lhs_val, rhs_val, op_name);
    const lhs = try sema.coerceValueToType(lhs_val, resolved_type.index, op_name);
    const rhs = try sema.coerceValueToType(rhs_val, resolved_type.index, op_name);

    return switch (tag) {
        .add, .add_unsafe => try arith.add(sema, resolved_type, lhs, rhs),
        .addwrap => try arith.addWrap(sema, resolved_type, lhs, rhs),
        .add_sat => try arith.addSat(sema, resolved_type, lhs, rhs),
        .sub => try arith.sub(sema, resolved_type, lhs, rhs),
        .subwrap => try arith.subWrap(sema, resolved_type, lhs, rhs),
        .sub_sat => try arith.subSat(sema, resolved_type, lhs, rhs),
        .mul => try arith.mul(sema, resolved_type, lhs, rhs),
        .mulwrap => try arith.mulWrap(sema, resolved_type, lhs, rhs),
        .mul_sat => try arith.mulSat(sema, resolved_type, lhs, rhs),
        .div => try arith.div(sema, resolved_type, lhs, rhs, .div),
        .div_trunc => try arith.div(sema, resolved_type, lhs, rhs, .div_trunc),
        .div_floor => try arith.div(sema, resolved_type, lhs, rhs, .div_floor),
        .div_exact => try arith.div(sema, resolved_type, lhs, rhs, .div_exact),
        .mod => try arith.modRem(sema, resolved_type, lhs, rhs, .mod),
        .rem => try arith.modRem(sema, resolved_type, lhs, rhs, .rem),
        .mod_rem => try sema.evalModRem(resolved_type, lhs_val, rhs_val, lhs, rhs),
        else => unreachable,
    };
}

/// `%` (`mod_rem`): `@rem`, but rejected when an operand may be negative and the
/// remainder is nonzero -- the mod/rem ambiguity. Mirrors `zirModRem`; the
/// negativity check keys on each operand's *original* scalar type + value.
fn evalModRem(sema: *Sema, resolved_type: Type, lhs_orig: Value, rhs_orig: Value, lhs: Value, rhs: Value) Error!Value {
    const ip = sema.intern_pool;
    const lhs_ty = Value.typeOf(lhs_orig, ip);
    const rhs_ty = Value.typeOf(rhs_orig, ip);
    const lhs_maybe_negative = !isUnsignedIntType(lhs_ty.scalarType(ip), ip) and !lhs.compareAllWithZero(.gte, ip);
    const rhs_maybe_negative = !isUnsignedIntType(rhs_ty.scalarType(ip), ip) and !rhs.compareAllWithZero(.gte, ip);
    const result = try arith.modRem(sema, resolved_type, lhs, rhs, .rem);
    if (lhs_maybe_negative or rhs_maybe_negative) {
        if (!result.compareAllWithZero(.eq, ip)) {
            try sema.writer.writeAll("remainder division with '");
            try Type.print(lhs_ty, ip, sema.writer);
            try sema.writer.writeAll("' and '");
            try Type.print(rhs_ty, ip, sema.writer);
            try sema.writer.writeAll("': signed integers and floats must use @rem or @mod\n");
            return error.AnalysisFail;
        }
    }
    return result;
}

fn isUnsignedIntType(ty: Type, pool: *const InternPool) bool {
    return ty.zigTypeTag(pool) == .int and ty.intInfo(pool).?.signedness == .unsigned;
}

/// Peer-type resolution for a binary numeric op, producing the result type the
/// mid-layer operates on. Vectors resolve element-wise into a vector of the
/// element peer; scalars fall to `resolveScalarNumericPeer`.
fn resolveArithPeerType(sema: *Sema, lhs: Value, rhs: Value, op_name: []const u8) Error!Type {
    const ip = sema.intern_pool;
    const lt_key = ip.indexToKey(Value.typeOf(lhs, ip).index);
    const rt_key = ip.indexToKey(Value.typeOf(rhs, ip).index);
    if (lt_key == .vector_type or rt_key == .vector_type) {
        if (lt_key != .vector_type or rt_key != .vector_type) {
            try sema.writer.print("{s}: mixed scalar and vector operands\n", .{op_name});
            return error.AnalysisFail;
        }
        if (lt_key.vector_type.len != rt_key.vector_type.len) {
            try sema.writer.print("{s}: vector length mismatch\n", .{op_name});
            return error.AnalysisFail;
        }
        const lhs_agg = ip.indexToKey(lhs.index).aggregate;
        const rhs_agg = ip.indexToKey(rhs.index).aggregate;
        const elem_ty = try sema.resolveScalarNumericPeer(
            ip.indexToKey(InternPool.aggregateElementAt(lhs_agg, 0)),
            ip.indexToKey(InternPool.aggregateElementAt(rhs_agg, 0)),
            op_name,
        );
        return sema.vectorType(.{ .len = lt_key.vector_type.len, .child = elem_ty.index });
    }
    return sema.resolveScalarNumericPeer(ip.indexToKey(lhs.index), ip.indexToKey(rhs.index), op_name);
}

fn resolveScalarNumericPeer(sema: *Sema, lhs_key: InternPool.Key, rhs_key: InternPool.Key, op_name: []const u8) Error!Type {
    if (resolveNumericPairToInt(sema.intern_pool, lhs_key, rhs_key)) |triple| return .fromIndex(triple.ty);
    if (coerceNumericPairToFloat(lhs_key, rhs_key)) |pair| return .fromIndex(pair[0].ty);
    return sema.failNumericOperands(op_name, lhs_key, rhs_key);
}

/// The "not a workable numeric pair" error shared by numeric peer resolution
/// (`resolveScalarNumericPeer`) and comparison (`evalComparison`): two numeric
/// operands with no common type are "incompatible"; a non-numeric operand is
/// "non-numeric or mismatched".
fn failNumericOperands(sema: *Sema, op_name: []const u8, lhs_key: InternPool.Key, rhs_key: InternPool.Key) Error {
    if ((lhs_key == .int or lhs_key == .float) and (rhs_key == .int or rhs_key == .float)) {
        sema.writer.print("{s}: incompatible numeric operands\n", .{op_name}) catch |e| return e;
    } else {
        sema.writer.print("{s}: non-numeric or mismatched operands\n", .{op_name}) catch |e| return e;
    }
    return error.AnalysisFail;
}

/// Validate two operands for a lane-wise comparison: both must be vectors of the
/// same length -- a scalar operand is "mixed scalar and vector operands" and a
/// differing length is a "vector length mismatch". Returns the lane count + both
/// aggregates.
const VectorPair = struct { len: usize, lhs: InternPool.Key.Aggregate, rhs: InternPool.Key.Aggregate };
fn vectorBinaryOperands(sema: *Sema, lhs: Value, rhs: Value, op_name: []const u8) Error!VectorPair {
    const ip = sema.intern_pool;
    const lhs_vt = ip.indexToKey(Value.typeOf(lhs, ip).index).vector_type;
    const rhs_ty_key = ip.indexToKey(Value.typeOf(rhs, ip).index);
    if (rhs_ty_key != .vector_type) {
        try sema.writer.print("{s}: mixed scalar and vector operands\n", .{op_name});
        return error.AnalysisFail;
    }
    if (rhs_ty_key.vector_type.len != lhs_vt.len) {
        try sema.writer.print("{s}: vector length mismatch\n", .{op_name});
        return error.AnalysisFail;
    }
    return .{ .len = @intCast(lhs_vt.len), .lhs = ip.indexToKey(lhs.index).aggregate, .rhs = ip.indexToKey(rhs.index).aggregate };
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

    const ip = sema.intern_pool;
    const operand = try sema.resolveRef(un_node.operand);
    const operand_type = Value.typeOf(operand, ip).index;

    // A vector shift takes a `@Vector(N, log2)` amount -- the element's log2 type.
    if (ip.indexToKey(operand_type) == .vector_type) {
        const vt = ip.indexToKey(operand_type).vector_type;
        const elem_log2 = (try sema.log2IntType(vt.child)) orelse
            return sema.failLog2NonInt();
        return .{ .index = try ip.internVectorType(.{ .len = vt.len, .child = elem_log2 }) };
    }

    return .{ .index = (try sema.log2IntType(operand_type)) orelse return sema.failLog2NonInt() };
}

fn failLog2NonInt(sema: *Sema) Error {
    sema.writer.writeAll("typeof_log2_int_type: non-integer operand not yet supported\n") catch |e| return e;
    return error.AnalysisFail;
}

/// The type valid as a shift amount for a value of int type `int_ty`:
/// The type valid as a shift amount for a value of type `int_ty`: `comptime_int`
/// for a `comptime_int`, `unsigned(log2_ceil(bits))` for an int, and elementwise
/// for a vector. Null if `int_ty` is not a shiftable type. Ports the compiler's
/// `log2IntType`, which dispatches on `zigTypeTag` (so it never depends on
/// `intInfo` returning null to classify).
fn log2IntType(sema: *Sema, int_ty: InternPool.Index) Error!?InternPool.Index {
    const ip = sema.intern_pool;
    const operand = Type.fromIndex(int_ty);
    switch (operand.zigTypeTag(ip)) {
        .comptime_int => return .comptime_int_type,
        .int => {
            const bits = operand.intInfo(ip).?.bits;
            const log2_bits: u16 = if (bits == 0) 0 else std.math.log2_int_ceil(u16, bits);
            return try ip.internIntType(.unsigned, log2_bits);
        },
        .vector => {
            const log2_elem = (try sema.log2IntType(operand.childType(ip).toIndex())) orelse return null;
            return try ip.internVectorType(.{ .len = operand.vectorLen(ip), .child = log2_elem });
        },
        else => return null,
    }
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
    // Classify by `zigTypeTag` (like the compiler), then read the int info; this
    // covers every fixed-width int -- `intN`, `usize`/`isize`, and the `c_*` types.
    if (Type.fromIndex(dest_type_index).zigTypeTag(sema.intern_pool) == .int) {
        const dest_int = Type.fromIndex(dest_type_index).intInfo(sema.intern_pool).?;
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

    const ip = sema.intern_pool;
    const lhs_value = try sema.resolveRef(bin.lhs);
    const rhs_value = try sema.resolveRef(bin.rhs);
    const lhs_ty = Value.typeOf(lhs_value, ip);
    const rhs_ty = Value.typeOf(rhs_value, ip);

    return switch (tag) {
        .shl => try arith.shl(sema, lhs_ty, lhs_value, rhs_value, .shl),
        .shl_exact => try arith.shl(sema, lhs_ty, lhs_value, rhs_value, .shl_exact),
        .shl_sat => try arith.shl(sema, lhs_ty, lhs_value, rhs_value, .shl_sat),
        .shr => try arith.shr(sema, lhs_ty, rhs_ty, lhs_value, rhs_value, .shr),
        .shr_exact => try arith.shr(sema, lhs_ty, rhs_ty, lhs_value, rhs_value, .shr_exact),
        else => unreachable,
    };
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
    const lhs_value = try sema.resolveRef(bin.lhs);
    const rhs_value = try sema.resolveRef(bin.rhs);

    const resolved_type = try sema.resolveArithPeerType(lhs_value, rhs_value, op_name);
    const lhs = try sema.coerceValueToType(lhs_value, resolved_type.index, op_name);
    const rhs = try sema.coerceValueToType(rhs_value, resolved_type.index, op_name);

    return switch (tag) {
        .bit_and => try arith.bitwiseBin(sema, resolved_type, lhs, rhs, .@"and"),
        .bit_or => try arith.bitwiseBin(sema, resolved_type, lhs, rhs, .@"or"),
        .xor => try arith.bitwiseBin(sema, resolved_type, lhs, rhs, .xor),
        else => unreachable,
    };
}

/// A `bool` result as an interned Value -- the two well-known bool indices.
inline fn boolValue(b: bool) Value {
    return .{ .index = if (b) .bool_true else .bool_false };
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
    var lhs_value = try sema.resolveRef(bin.lhs);
    var rhs_value = try sema.resolveRef(bin.rhs);
    var lhs_key = ip.indexToKey(lhs_value.index);
    var rhs_key = ip.indexToKey(rhs_value.index);

    // A tagged union compared to an enum literal (`@typeInfo(T) == .int`)
    // compares its active tag, so stand the union in for its `enum_tag` before
    // the enum-literal peer resolution below. Mirrors `analyzeCmpUnionTag`,
    // including its guard: only a tagged union (`union(enum)` / `union(E)`) is
    // comparable to an enum literal -- a bare/extern/packed union is not, even
    // though this evaluator generates a tag enum for it internally.
    if (lhs_key == .un and rhs_key == .enum_literal) {
        if (try sema.cmpUnionTagNoValue(Value.typeOf(lhs_value, ip).index, rhs_key.enum_literal, op)) |v| return v;
        lhs_value = .{ .index = lhs_key.un.tag };
        lhs_key = ip.indexToKey(lhs_value.index);
    } else if (rhs_key == .un and lhs_key == .enum_literal) {
        if (try sema.cmpUnionTagNoValue(Value.typeOf(rhs_value, ip).index, lhs_key.enum_literal, op)) |v| return v;
        rhs_value = .{ .index = rhs_key.un.tag };
        rhs_key = ip.indexToKey(rhs_value.index);
    }

    // Null and optional comparisons. Mirrors `zirCmpEq`: a null literal against
    // an optional or C pointer reduces to an is-null test; a non-null operand
    // against null is an error; otherwise an optional operand pulls its peer up
    // to the optional type and the two compare by interned identity -- interning
    // is canonical, so `Value.eql` is `a.toIntern() == b.toIntern()`. Only
    // `==`/`!=` are defined (the compiler's `isSelfComparable`).
    {
        const lhs_ty = Value.typeOf(lhs_value, ip).index;
        const rhs_ty = Value.typeOf(rhs_value, ip).index;
        const lhs_null_lit = lhs_ty == .null_type;
        const rhs_null_lit = rhs_ty == .null_type;
        const lhs_is_opt = ip.indexToKey(lhs_ty) == .opt_type;
        const rhs_is_opt = ip.indexToKey(rhs_ty) == .opt_type;
        if (lhs_null_lit or rhs_null_lit or lhs_is_opt or rhs_is_opt) {
            if (op != .eq and op != .neq) {
                try sema.writer.print("operator {s} not allowed for optional type\n", .{op_name});
                return error.AnalysisFail;
            }
            if (lhs_null_lit and rhs_null_lit) return boolValue(op == .eq);
            if (lhs_null_lit or rhs_null_lit) {
                const other_ty = if (lhs_null_lit) rhs_ty else lhs_ty;
                const other_val = if (lhs_null_lit) rhs_value else lhs_value;
                const other_key = ip.indexToKey(other_ty);
                const nullable = other_key == .opt_type or
                    (other_key == .ptr_type and other_key.ptr_type.flags.size == .c);
                if (!nullable) {
                    try sema.writer.writeAll("comparison of '");
                    try Type.print(.fromIndex(other_ty), ip, sema.writer);
                    try sema.writer.writeAll("' with null\n");
                    return error.AnalysisFail;
                }
                const ov_key = ip.indexToKey(other_val.index);
                const is_null = ov_key == .opt and ov_key.opt.val == .none;
                return boolValue(if (op == .eq) is_null else !is_null);
            }
            // Both peer-coerced to the optional type, then compared by identity.
            const opt_ty = if (lhs_is_opt) lhs_ty else rhs_ty;
            const l = if (lhs_is_opt) lhs_value else try sema.coerceToOptional(lhs_value, opt_ty, op_name);
            const r = if (rhs_is_opt) rhs_value else try sema.coerceToOptional(rhs_value, opt_ty, op_name);
            return boolValue((l.index == r.index) == (op == .eq));
        }
    }

    // Peer resolution: an enum literal (`.foo`) coerces to the other operand's
    // enum type before the identity comparison (`e == .foo`).
    if (lhs_key == .enum_literal and rhs_key == .enum_tag) {
        lhs_value = try sema.coerceValueToType(lhs_value, rhs_key.enum_tag.ty, op_name);
        lhs_key = ip.indexToKey(lhs_value.index);
    } else if (rhs_key == .enum_literal and lhs_key == .enum_tag) {
        rhs_value = try sema.coerceValueToType(rhs_value, lhs_key.enum_tag.ty, op_name);
        rhs_key = ip.indexToKey(rhs_value.index);
    }

    // Vector operands compare lane-wise into a `@Vector(N, bool)` mask.
    if (ip.indexToKey(Value.typeOf(lhs_value, ip).index) == .vector_type)
        return try sema.evalVectorComparison(op, lhs_value, rhs_value, op_name);

    // Types, bools, and enum tags compare by interned identity: interning is
    // canonical, so equal values share an Index. Only `==`/`!=` are defined
    // (ordering is a type error). Mirrors zirCmpEq's `.type` branch and cmpScalar's
    // bool/enum paths. A type operand's own `.index` IS the type, so `==` is the
    // compiler's `Type.eql` on interned types.
    {
        const lhs_ty = Value.typeOf(lhs_value, ip).index;
        const rhs_ty = Value.typeOf(rhs_value, ip).index;
        const kind: ?[]const u8 = if (lhs_ty == .type_type and rhs_ty == .type_type)
            "type"
        else if (lhs_ty == .bool_type and rhs_ty == .bool_type)
            "bool"
        else if (lhs_key == .enum_tag and rhs_key == .enum_tag)
            "enum"
        else
            null;
        if (kind) |kind_name| {
            if (lhs_key == .enum_tag and lhs_key.enum_tag.ty != rhs_key.enum_tag.ty) {
                try sema.writer.print("{s}: enum operands have different types\n", .{op_name});
                return error.AnalysisFail;
            }
            const equal = lhs_value.index == rhs_value.index;
            return switch (op) {
                .eq => .{ .index = if (equal) .bool_true else .bool_false },
                .neq => .{ .index = if (equal) .bool_false else .bool_true },
                else => {
                    try sema.writer.print("{s}: operator not allowed for {s} operands\n", .{ op_name, kind_name });
                    return error.AnalysisFail;
                },
            };
        }
    }

    return sema.scalarCompare(op, lhs_value, rhs_value, op_name);
}

/// Compare two numeric scalars to a `bool`, shared by `evalComparison` and each
/// lane of `evalVectorComparison`. Any int/float pair compares by value through
/// `Value.compareHetero` -- ints order exactly, a float pair (or a mixed int/float
/// pair) orders as `f128`, and NaN is unordered. A non-numeric operand is a typed
/// error. Mirrors `cmpNumeric`'s comptime path (`src/Sema.zig`).
fn scalarCompare(sema: *Sema, op: std.math.CompareOperator, lhs: Value, rhs: Value, op_name: []const u8) Error!?Value {
    const ip = sema.intern_pool;
    const lhs_key = ip.indexToKey(lhs.index);
    const rhs_key = ip.indexToKey(rhs.index);
    if ((lhs_key == .int or lhs_key == .float) and (rhs_key == .int or rhs_key == .float)) {
        return boolValue(Value.compareHetero(lhs, op, rhs, ip));
    }
    return sema.failNumericOperands(op_name, lhs_key, rhs_key);
}

/// Lane-wise comparison of two `@Vector(N, T)` operands into a `@Vector(N, bool)`
/// mask: compare each `(lhs[i], rhs[i])` pair to a `bool`. Same operand rules as
/// `evalVectorArith` -- both must be vectors of the same length. Mirrors the
/// compiler's element-wise `cmp` on vectors.
fn evalVectorComparison(sema: *Sema, op: std.math.CompareOperator, lhs: Value, rhs: Value, op_name: []const u8) Error!?Value {
    const ip = sema.intern_pool;
    const vp = try sema.vectorBinaryOperands(lhs, rhs, op_name);
    const elems = try sema.gpa.alloc(InternPool.Index, vp.len);
    defer sema.gpa.free(elems);
    for (elems, 0..) |*e, i| {
        const l: Value = .{ .index = InternPool.aggregateElementAt(vp.lhs, i) };
        const r: Value = .{ .index = InternPool.aggregateElementAt(vp.rhs, i) };
        e.* = (try sema.scalarCompare(op, l, r, op_name) orelse return null).index;
    }
    // A comparison mask is always `@Vector(N, bool)`, whatever the operand type.
    const vec_ty = try ip.internVectorType(.{ .len = @intCast(vp.len), .child = .bool_type });
    return .{ .index = try ip.internAggregate(.{ .ty = vec_ty, .storage = .{ .elems = elems } }) };
}

/// `negate` / `negate_wrap`. AstGen lowers `-x` as `negate(x)`; constant-
/// folded literals like `-1` / `-1.5` come through as well-known Refs or
/// as a single signed literal and never reach here. `negate_wrap` is the
/// `-%x` form, valid only on fixed-width int operands.
///
/// Compiler reference: src/Sema.zig:zirNegate (~13858) /
/// src/Sema.zig:zirNegateWrap (~13896).
/// The `@sqrt`/`@sin`/.../`@trunc` unary float builtins. Each maps to a distinct
/// ZIR tag; the compiler funnels them through `zirUnaryMath` with the matching
/// `Value` fn. Rejects a non-float scalar type, then folds scalar or elementwise
/// (mirrors `Value.sqrt`'s scalar/vector split). The operand is comptime-known.
/// `@sqrt`/`@sin`/.../`@trunc`: a unary float builtin. Ports zirUnaryMath ->
/// unaryMath: reject a non-float scalar, then fold via `maybeConstantUnaryMath`
/// with the matching `Value` function (passed by the dispatch, as the compiler
/// passes `Value.sqrt` etc.).
fn evalUnaryMath(
    sema: *Sema,
    inst: Zir.Inst.Index,
    comptime eval: fn (Value, Type, std.mem.Allocator, *InternPool) std.mem.Allocator.Error!Value,
) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);
    const ip = sema.intern_pool;
    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    const operand = try sema.resolveRef(un_node.operand);
    const operand_ty = operand.typeOf(ip);
    switch (operand_ty.scalarType(ip).zigTypeTag(ip)) {
        .comptime_float, .float => {},
        else => {
            try sema.writer.writeAll("expected vector of floats or float type, found '");
            try Type.print(operand_ty, ip, sema.writer);
            try sema.writer.writeAll("'\n");
            return error.AnalysisFail;
        },
    }
    return try sema.maybeConstantUnaryMath(operand, operand_ty, eval);
}

fn checkNumericType(sema: *Sema, ty: Type) Error!void {
    const ip = sema.intern_pool;
    switch (ty.zigTypeTag(ip)) {
        .comptime_float, .float, .comptime_int, .int => {},
        .vector => switch (ty.childType(ip).zigTypeTag(ip)) {
            .comptime_float, .float, .comptime_int, .int => {},
            else => |t| {
                try sema.writer.print("expected number, found '{t}'\n", .{t});
                return error.AnalysisFail;
            },
        },
        else => {
            try sema.writer.writeAll("expected number, found '");
            try Type.print(ty, ip, sema.writer);
            try sema.writer.writeAll("'\n");
            return error.AnalysisFail;
        },
    }
}

/// `@min`/`@max`: fold two numeric operands, refining the result type to the
/// narrowest that holds it (`@max(u32, i64)` -> `u63`). Ports `analyzeMinMax`
/// (`src/Sema.zig`); every operand is comptime-known here, so only the runtime
/// path is dropped.
fn evalMinMax(sema: *Sema, inst: Zir.Inst.Index, comptime op: enum { min, max }) Error!?Value {
    const ip = sema.intern_pool;
    const bin = sema.binData(inst);
    const operands = [_]Value{ try sema.resolveRef(bin.lhs), try sema.resolveRef(bin.rhs) };
    const opFunc = switch (op) {
        .min => Value.numberMin,
        .max => Value.numberMax,
    };

    const vector_len: ?u64 = vec_len: {
        const first_ty = Value.typeOf(operands[0], ip);
        try sema.checkNumericType(first_ty);
        if (first_ty.zigTypeTag(ip) == .vector) {
            const vec_len = first_ty.vectorLen(ip);
            for (operands[1..]) |operand| {
                const operand_ty = Value.typeOf(operand, ip);
                try sema.checkNumericType(operand_ty);
                if (operand_ty.zigTypeTag(ip) != .vector) {
                    try sema.writer.writeAll("expected vector, found '");
                    try Type.print(operand_ty, ip, sema.writer);
                    try sema.writer.writeAll("'\n");
                    return error.AnalysisFail;
                }
                if (operand_ty.vectorLen(ip) != vec_len) {
                    try sema.writer.print("expected vector of length '{d}', found '", .{vec_len});
                    try Type.print(operand_ty, ip, sema.writer);
                    try sema.writer.writeAll("'\n");
                    return error.AnalysisFail;
                }
            }
            break :vec_len vec_len;
        } else {
            for (operands[1..]) |operand| {
                const operand_ty = Value.typeOf(operand, ip);
                try sema.checkNumericType(operand_ty);
                if (operand_ty.zigTypeTag(ip) == .vector) {
                    try sema.writer.writeAll("expected vector, found '");
                    try Type.print(first_ty, ip, sema.writer);
                    try sema.writer.writeAll("'\n");
                    return error.AnalysisFail;
                }
            }
            break :vec_len null;
        }
    };

    // The result scalar type, in "priority" order: float > comptime_float > int.
    const TypeStrat = union(enum) {
        float: Type,
        comptime_float,
        int: struct {
            all_comptime_int: bool,
            result_min: Value,
            result_max: Value,
            operand_min: Value,
            operand_max: Value,
        },
        none,
    };
    var cur_strat: TypeStrat = .none;
    for (operands) |operand| {
        const operand_scalar_ty = Value.typeOf(operand, ip).scalarType(ip);
        const want_strat: TypeStrat = switch (operand_scalar_ty.zigTypeTag(ip)) {
            .comptime_int => s: {
                if (operand.isUndef(ip)) break :s .none;
                break :s .{ .int = .{
                    .all_comptime_int = true,
                    .result_min = operand,
                    .result_max = operand,
                    .operand_min = operand,
                    .operand_max = operand,
                } };
            },
            .comptime_float => .comptime_float,
            .float => .{ .float = operand_scalar_ty },
            .int => s: {
                const min: Value, const max: Value = bounds: {
                    if (vector_len) |len| {
                        var min = try operand.elemValue(ip, 0);
                        var max = min;
                        for (1..@intCast(len)) |elem_idx| {
                            const elem_val = try operand.elemValue(ip, elem_idx);
                            min = Value.numberMin(min, elem_val, ip);
                            max = Value.numberMax(max, elem_val, ip);
                        }
                        if (!min.isUndef(ip) and !max.isUndef(ip)) break :bounds .{ min, max };
                    } else {
                        if (!operand.isUndef(ip)) break :bounds .{ operand, operand };
                    }
                    break :bounds .{
                        try operand_scalar_ty.minInt(sema, operand_scalar_ty),
                        try operand_scalar_ty.maxInt(sema, operand_scalar_ty),
                    };
                };
                break :s .{ .int = .{
                    .all_comptime_int = false,
                    .result_min = min,
                    .result_max = max,
                    .operand_min = min,
                    .operand_max = max,
                } };
            },
            else => unreachable,
        };
        if (@intFromEnum(want_strat) < @intFromEnum(cur_strat)) {
            cur_strat = want_strat;
        } else if (@intFromEnum(want_strat) == @intFromEnum(cur_strat)) {
            switch (cur_strat) {
                .none, .comptime_float => {},
                .float => |cur_float| {
                    const want_float = want_strat.float;
                    if (want_float.floatBits() > cur_float.floatBits() or
                        (want_float.floatBits() == cur_float.floatBits() and
                            cur_float.index == .c_longdouble_type and
                            want_float.index != .c_longdouble_type))
                    {
                        cur_strat = want_strat;
                    }
                },
                .int => |*cur_int| {
                    const want_int = want_strat.int;
                    if (!want_int.all_comptime_int) cur_int.all_comptime_int = false;
                    cur_int.result_min = opFunc(cur_int.result_min, want_int.result_min, ip);
                    cur_int.result_max = opFunc(cur_int.result_max, want_int.result_max, ip);
                    cur_int.operand_min = Value.numberMin(cur_int.operand_min, want_int.operand_min, ip);
                    cur_int.operand_max = Value.numberMax(cur_int.operand_max, want_int.operand_max, ip);
                },
            }
        }
    }

    const result_scalar_ty: Type = switch (cur_strat) {
        .float => |ty| ty,
        .comptime_float => .fromIndex(.comptime_float_type),
        .int => |int| if (int.all_comptime_int)
            .fromIndex(.comptime_int_type)
        else
            try sema.intFittingRange(int.result_min, int.result_max),
        .none => .fromIndex(.comptime_int_type),
    };
    const result_ty: Type = if (vector_len) |l|
        try sema.vectorType(.{ .len = @intCast(l), .child = result_scalar_ty.index })
    else
        result_scalar_ty;

    // We might have refined all the way down to a one-possible-value type.
    if (try result_ty.onePossibleValue(sema)) |opv| return opv;

    // Fold the comptime-known operands element-wise.
    const elems = try sema.arena.alloc(InternPool.Index, @intCast(vector_len orelse 1));
    var elems_populated = false;
    for (operands) |operand| {
        if (vector_len != null) {
            if (elems_populated) {
                for (elems, 0..) |*elem, elem_idx| {
                    const new_elem = try operand.elemValue(ip, elem_idx);
                    elem.* = opFunc(.{ .index = elem.* }, new_elem, ip).index;
                }
            } else {
                elems_populated = true;
                for (elems, 0..) |*elem_out, elem_idx| {
                    elem_out.* = (try operand.elemValue(ip, elem_idx)).index;
                }
            }
        } else {
            if (elems_populated) {
                elems[0] = opFunc(.{ .index = elems[0] }, operand, ip).index;
            } else {
                elems_populated = true;
                elems[0] = operand.index;
            }
        }
    }
    // Coerce each result element to the refined scalar type (always fits).
    for (elems) |*elem| {
        const ev: Value = .{ .index = elem.* };
        elem.* = if (ev.isUndef(ip))
            (try sema.undefValue(result_scalar_ty)).index
        else
            (try sema.coerceValueToType(ev, result_scalar_ty.index, @tagName(op))).index;
    }
    if (vector_len == null) return Value{ .index = elems[0] };
    return try sema.aggregateValue(result_ty, elems);
}

/// `@reduce(op, vec)`: fold a vector to a scalar with the `std.lang.ReduceOp`
/// operation. Mirrors `zirReduce` (`src/Sema.zig`); the accumulator folds through
/// the same arith / Value methods the compiler uses.
fn evalReduce(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    const bin = sema.binData(inst);
    const operation = try sema.resolveStdLangEnum(.ReduceOp, bin.lhs);
    const operand = try sema.resolveRef(bin.rhs);
    const operand_ty = operand.typeOf(ip);

    if (operand_ty.zigTypeTag(ip) != .vector) {
        try sema.writer.writeAll("expected vector, found '");
        try Type.print(operand_ty, ip, sema.writer);
        try sema.writer.writeAll("'\n");
        return error.AnalysisFail;
    }

    const scalar_ty = operand_ty.childType(ip);
    switch (operation) {
        .And, .Or, .Xor => switch (scalar_ty.zigTypeTag(ip)) {
            .int, .bool => {},
            else => return sema.failReduceOperand(operation, operand_ty, "integer or boolean"),
        },
        .Min, .Max, .Add, .Mul => switch (scalar_ty.zigTypeTag(ip)) {
            .int, .float => {},
            else => return sema.failReduceOperand(operation, operand_ty, "integer or float"),
        },
    }

    const vec_len = operand_ty.vectorLen(ip);
    if (vec_len == 0) {
        try sema.writer.writeAll("@reduce operation requires a vector with nonzero length\n");
        return error.AnalysisFail;
    }

    if (ip.indexToKey(operand.index) == .undef) return try sema.undefValue(scalar_ty);

    var accum: Value = try operand.elemValue(ip, 0);
    var i: u32 = 1;
    while (i < vec_len) : (i += 1) {
        const elem_val = try operand.elemValue(ip, i);
        accum = switch (operation) {
            .And => try arith.bitwiseBin(sema, scalar_ty, accum, elem_val, .@"and"),
            .Or => try arith.bitwiseBin(sema, scalar_ty, accum, elem_val, .@"or"),
            .Xor => try arith.bitwiseBin(sema, scalar_ty, accum, elem_val, .xor),
            .Min => Value.numberMin(accum, elem_val, ip),
            .Max => Value.numberMax(accum, elem_val, ip),
            .Add => try arith.addMaybeWrap(sema, scalar_ty, accum, elem_val),
            .Mul => try arith.mulMaybeWrap(sema, scalar_ty, accum, elem_val),
        };
    }
    return accum;
}

fn failReduceOperand(sema: *Sema, operation: std.lang.ReduceOp, operand_ty: Type, want: []const u8) Error {
    try sema.writer.print("@reduce operation '{s}' requires {s} operand; found '", .{ @tagName(operation), want });
    try Type.print(operand_ty, sema.intern_pool, sema.writer);
    try sema.writer.writeAll("'\n");
    return error.AnalysisFail;
}

/// `mul_add` (`@mulAdd(T, a, b, c)`): the fused multiply-add `a * b + c` at `T`'s
/// precision. Ports zirMulAdd: the result type is the addend's type and the
/// mulends coerce to it; reject a non-float scalar, pass undef through, then fold
/// via `Value.mulAdd`.
fn evalMulAdd(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    const extra = sema.zir.extraData(Zir.Inst.MulAdd, sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node.payload_index).data;
    const addend = try sema.resolveRef(extra.addend);
    const ty = addend.typeOf(ip);
    const mulend1 = try sema.coerceValueToType(try sema.resolveRef(extra.mulend1), ty.toIndex(), "@mulAdd");
    const mulend2 = try sema.coerceValueToType(try sema.resolveRef(extra.mulend2), ty.toIndex(), "@mulAdd");

    switch (ty.scalarType(ip).zigTypeTag(ip)) {
        .comptime_float, .float => {},
        else => {
            try sema.writer.writeAll("expected vector of floats or float type, found '");
            try Type.print(ty, ip, sema.writer);
            try sema.writer.writeAll("'\n");
            return error.AnalysisFail;
        },
    }

    if (ip.indexToKey(mulend1.index) == .undef or ip.indexToKey(mulend2.index) == .undef or ip.indexToKey(addend.index) == .undef)
        return .{ .index = try ip.get(.{ .undef = ty.toIndex() }) };
    return try Value.mulAdd(ty, mulend1, mulend2, addend, sema.arena, ip);
}

/// `abs` (`@abs(x)`). Ports zirAbs: a signed int narrows to the same-width
/// unsigned type (`toUnsigned`), an unsigned int is returned unchanged, and
/// float/comptime keep the operand type; then fold via `maybeConstantUnaryMath`
/// with `Value.abs`.
fn evalAbs(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    const operand = try sema.resolveRef(un_node.operand);
    const operand_ty = operand.typeOf(ip);
    const scalar_ty = operand_ty.scalarType(ip);

    const result_ty: Type = switch (scalar_ty.zigTypeTag(ip)) {
        .comptime_float, .float, .comptime_int => operand_ty,
        .int => if (scalar_ty.intInfo(ip).?.signedness == .signed) try operand_ty.toUnsigned(ip) else return operand,
        else => {
            try sema.writer.writeAll("expected integer, float, or vector of either integers or floats, found '");
            try Type.print(operand_ty, ip, sema.writer);
            try sema.writer.writeAll("'\n");
            return error.AnalysisFail;
        },
    };

    return try sema.maybeConstantUnaryMath(operand, result_ty, Value.abs);
}

/// Fold a unary math builtin over a comptime-known operand: a scalar directly, a
/// vector elementwise, and undef to undef of the result type. Ports
/// `maybeConstantUnaryMath` (the operand is always comptime-known here, so the
/// runtime `null` return collapses to always folding).
fn maybeConstantUnaryMath(
    sema: *Sema,
    operand: Value,
    result_ty: Type,
    comptime eval: fn (Value, Type, std.mem.Allocator, *InternPool) std.mem.Allocator.Error!Value,
) Error!Value {
    const ip = sema.intern_pool;
    switch (result_ty.zigTypeTag(ip)) {
        .vector => {
            const scalar_ty = result_ty.scalarType(ip);
            const vec_len = result_ty.vectorLen(ip);
            if (ip.indexToKey(operand.index) == .undef)
                return .{ .index = try ip.get(.{ .undef = result_ty.toIndex() }) };
            const elems = try sema.arena.alloc(InternPool.Index, vec_len);
            for (elems, 0..) |*elem, i| {
                elem.* = (try eval(try operand.elemValue(ip, i), scalar_ty, sema.arena, ip)).index;
            }
            return .{ .index = try ip.internAggregate(.{ .ty = result_ty.toIndex(), .storage = .{ .elems = elems } }) };
        },
        else => {
            if (ip.indexToKey(operand.index) == .undef)
                return .{ .index = try ip.get(.{ .undef = result_ty.toIndex() }) };
            return try eval(operand, result_ty, sema.arena, ip);
        },
    }
}

fn evalNegate(sema: *Sema, inst: Zir.Inst.Index, tag: Zir.Inst.Tag) Error!?Value {
    assert(tag == .negate or tag == .negate_wrap);
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    assert(un_node.operand != .none);

    const ip = sema.intern_pool;
    const operand = try sema.resolveRef(un_node.operand);
    const ty = Value.typeOf(operand, ip);
    const scalar_ty = ty.scalarType(ip);
    const scalar_tag = scalar_ty.zigTypeTag(ip);

    const numeric = switch (scalar_tag) {
        .int, .comptime_int, .float, .comptime_float => true,
        else => false,
    };
    if (!numeric or (tag == .negate and isUnsignedIntType(scalar_ty, ip))) {
        try sema.writer.writeAll("negation of type '");
        try Type.print(ty, ip, sema.writer);
        try sema.writer.writeAll("'\n");
        return error.AnalysisFail;
    }

    if (scalar_tag == .float or scalar_tag == .comptime_float) {
        return try arith.negateFloat(sema, ty, operand);
    }

    const zero_scalar = try sema.intValue_u64(scalar_ty, 0);
    const zero = if (ty.zigTypeTag(ip) == .vector) try sema.aggregateSplatValue(ty, zero_scalar) else zero_scalar;
    return switch (tag) {
        .negate => try arith.sub(sema, ty, zero, operand),
        .negate_wrap => try arith.subWrap(sema, ty, zero, operand),
        else => unreachable,
    };
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
    if (inst_data.flags.has_addrspace or inst_data.flags.has_bit_range) {
        try sema.writer.writeAll("ptr_type: address_space / bit_range not yet supported\n");
        return error.AnalysisFail;
    }

    const extra = sema.zir.extraData(Zir.Inst.PtrType, inst_data.payload_index);
    const payload = extra.data;
    assert(payload.elem_type != .none);

    const child_ty = try sema.resolveDestType(payload.elem_type, "ptr_type");
    assert(child_ty != .none);

    // The optional extensions trail the payload as `Ref` slots in `extra`, in the
    // order sentinel, align, addrspace, bit_range (zirPtrType). A cursor walks the
    // present ones; addrspace/bit_range are rejected above.
    var extra_i = extra.end;
    const sentinel: InternPool.Index = if (inst_data.flags.has_sentinel) blk: {
        const ref: Zir.Inst.Ref = @enumFromInt(sema.zir.extra[extra_i]);
        extra_i += 1;
        break :blk (try sema.coerceValueToType(try sema.resolveRef(ref), child_ty, "pointer sentinel")).index;
    } else .none;
    const alignment: InternPool.Alignment = if (inst_data.flags.has_align) blk: {
        const ref: Zir.Inst.Ref = @enumFromInt(sema.zir.extra[extra_i]);
        extra_i += 1;
        break :blk try sema.alignmentFromValue(try sema.resolveRef(ref), "ptr_type");
    } else .none;

    const idx = try sema.intern_pool.internPtrType(.{
        .child = child_ty,
        .sentinel = sentinel,
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

/// `bit_size_of` (`@bitSizeOf(T)`): the type's bit width as a `comptime_int`.
/// Mirrors zirBitSizeOf -- resolve the operand type, reject one with no bit
/// representation, then measure via `Type.bitSize`.
fn evalBitSizeOf(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);
    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    const ty = try sema.resolveDestType(un_node.operand, "@bitSizeOf");
    const bits = Type.fromIndex(ty).bitSize(sema.intern_pool) orelse {
        try sema.writer.writeAll("@bitSizeOf: no bit size available for type '");
        try Type.print(.fromIndex(ty), sema.intern_pool, sema.writer);
        try sema.writer.writeAll("'\n");
        return error.AnalysisFail;
    };
    const idx = try sema.intern_pool.internInt(.{
        .ty = .comptime_int_type,
        .storage = .{ .u64 = bits },
    });
    return .{ .index = idx };
}

/// `clz`/`ctz`/`pop_count` (`@clz`/`@ctz`/`@popCount`): count leading zeros,
/// trailing zeros, or set bits of a fixed-width integer (or vector of them). The
/// result scalar type is `smallestUnsignedInt(bits)` -- the narrowest unsigned
/// type holding the maximum count. Ports zirBitCount, folding via the same
/// `std.math.big.int.Const` methods `Value.clz`/`ctz`/`popCount` call; the REPL's
/// scalar-only `intInfo` takes a `scalarType` first. An undef operand yields undef.
fn evalBitCount(
    sema: *Sema,
    inst: Zir.Inst.Index,
    comptime comptimeOp: fn (Value, Type, *const InternPool) u64,
) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);
    const ip = sema.intern_pool;
    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    const operand = try sema.resolveRef(un_node.operand);
    const operand_ty = operand.typeOf(ip);
    _ = try sema.checkIntOrVector(operand);
    const bits = operand_ty.intInfo(ip).?.bits;

    const result_scalar_ty = Type.fromIndex(try ip.internIntType(.unsigned, Type.smallestUnsignedBits(bits)));
    switch (operand_ty.zigTypeTag(ip)) {
        .vector => {
            const vec_len = operand_ty.vectorLen(ip);
            const result_ty = try ip.internVectorType(.{ .len = vec_len, .child = result_scalar_ty.index });
            if (ip.indexToKey(operand.index) == .undef) return .{ .index = try ip.get(.{ .undef = result_ty }) };
            const elems = try sema.arena.alloc(InternPool.Index, vec_len);
            const scalar_ty = operand_ty.scalarType(ip);
            for (elems, 0..) |*elem, i| {
                const count = comptimeOp(try operand.elemValue(ip, i), scalar_ty, ip);
                elem.* = try ip.internInt(.{ .ty = result_scalar_ty.index, .storage = .{ .u64 = count } });
            }
            return .{ .index = try ip.internAggregate(.{ .ty = result_ty, .storage = .{ .elems = elems } }) };
        },
        .int => {
            if (ip.indexToKey(operand.index) == .undef) return .{ .index = try ip.get(.{ .undef = result_scalar_ty.index }) };
            const count = comptimeOp(operand, operand_ty, ip);
            return .{ .index = try ip.internInt(.{ .ty = result_scalar_ty.index, .storage = .{ .u64 = count } }) };
        },
        else => unreachable,
    }
}

/// `byte_swap`/`bit_reverse` (`@byteSwap`/`@bitReverse`): reverse the byte or bit
/// order of a fixed-width integer (or vector of them), keeping the operand type.
/// `@byteSwap` requires the width to be a multiple of 8. Mirrors zirByteSwap/
/// zirBitReverse -> `arith.byteSwap`/`bitReverse`, folding via the same
/// `std.math.big.int.Mutable` methods. An undef operand (or lane) stays undef.
/// The scalar int type of an int or vector-of-int operand, else an error. Ports
/// `checkIntOrVector`.
fn checkIntOrVector(sema: *Sema, operand: Value) Error!Type {
    const ip = sema.intern_pool;
    const operand_ty = operand.typeOf(ip);
    switch (operand_ty.zigTypeTag(ip)) {
        .int => return operand_ty,
        .vector => {
            const elem_ty = operand_ty.childType(ip);
            switch (elem_ty.zigTypeTag(ip)) {
                .int => return elem_ty,
                else => {
                    try sema.writer.writeAll("expected vector of integers; found vector of '");
                    try Type.print(elem_ty, ip, sema.writer);
                    try sema.writer.writeAll("'\n");
                    return error.AnalysisFail;
                },
            }
        },
        else => {
            try sema.writer.writeAll("expected integer or vector, found '");
            try Type.print(operand_ty, ip, sema.writer);
            try sema.writer.writeAll("'\n");
            return error.AnalysisFail;
        },
    }
}

/// `byte_swap` (`@byteSwap`). Ports zirByteSwap: the scalar width must be a byte
/// multiple; the fold is `byteSwap`.
fn evalByteSwap(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    const operand = try sema.resolveRef(un_node.operand);
    const operand_ty = operand.typeOf(ip);
    const scalar_ty = try sema.checkIntOrVector(operand);
    const bits = scalar_ty.intInfo(ip).?.bits;
    if (bits % 8 != 0) {
        try sema.writer.writeAll("@byteSwap requires the number of bits to be evenly divisible by 8, but '");
        try Type.print(scalar_ty, ip, sema.writer);
        try sema.writer.print("' has {d} bits\n", .{bits});
        return error.AnalysisFail;
    }
    return try sema.byteSwap(operand, operand_ty);
}

/// `bit_reverse` (`@bitReverse`). Ports zirBitReverse; the fold is `bitReverse`.
fn evalBitReverse(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    const operand = try sema.resolveRef(un_node.operand);
    const operand_ty = operand.typeOf(ip);
    _ = try sema.checkIntOrVector(operand);
    return try sema.bitReverse(operand, operand_ty);
}

/// Ports `arith.byteSwap`: a whole-operand undef stays undef; an int folds via
/// `intByteSwap`, a vector elementwise (an undef lane stays undef).
fn byteSwap(sema: *Sema, val: Value, ty: Type) Error!Value {
    const ip = sema.intern_pool;
    if (ip.indexToKey(val.index) == .undef) return val;
    switch (ty.zigTypeTag(ip)) {
        .int => return sema.intByteSwap(val, ty),
        .vector => {
            const elem_ty = ty.childType(ip);
            const len = ty.vectorLen(ip);
            const elem_vals = try sema.arena.alloc(InternPool.Index, len);
            for (elem_vals, 0..) |*result_elem, elem_idx| {
                const elem_val = try val.elemValue(ip, elem_idx);
                result_elem.* = if (ip.indexToKey(elem_val.index) == .undef)
                    elem_val.index
                else
                    (try sema.intByteSwap(elem_val, elem_ty)).index;
            }
            return .{ .index = try ip.internAggregate(.{ .ty = ty.index, .storage = .{ .elems = elem_vals } }) };
        },
        else => unreachable,
    }
}

/// Ports `arith.bitReverse`.
fn bitReverse(sema: *Sema, val: Value, ty: Type) Error!Value {
    const ip = sema.intern_pool;
    if (ip.indexToKey(val.index) == .undef) return val;
    switch (ty.zigTypeTag(ip)) {
        .int => return sema.intBitReverse(val, ty),
        .vector => {
            const elem_ty = ty.childType(ip);
            const len = ty.vectorLen(ip);
            const elem_vals = try sema.arena.alloc(InternPool.Index, len);
            for (elem_vals, 0..) |*result_elem, elem_idx| {
                const elem_val = try val.elemValue(ip, elem_idx);
                result_elem.* = if (ip.indexToKey(elem_val.index) == .undef)
                    elem_val.index
                else
                    (try sema.intBitReverse(elem_val, elem_ty)).index;
            }
            return .{ .index = try ip.internAggregate(.{ .ty = ty.index, .storage = .{ .elems = elem_vals } }) };
        },
        else => unreachable,
    }
}

/// Ports `arith.intByteSwap`: byte-swap one integer into a two's-complement
/// scratch, then re-intern at `ty`.
fn intByteSwap(sema: *Sema, val: Value, ty: Type) Error!Value {
    const ip = sema.intern_pool;
    const info = ty.intInfo(ip).?;
    var val_space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
    const val_bigint = val.toBigInt(&val_space, ip);
    const limbs = try sema.arena.alloc(std.math.big.Limb, std.math.big.int.calcTwosCompLimbCount(info.bits));
    var result_bigint: BigIntMutable = .{ .limbs = limbs, .positive = undefined, .len = undefined };
    result_bigint.byteSwap(val_bigint, info.signedness, @divExact(info.bits, 8));
    return .{ .index = try ip.internIntValue(ty.index, result_bigint.toConst()) };
}

/// Ports `arith.intBitReverse`.
fn intBitReverse(sema: *Sema, val: Value, ty: Type) Error!Value {
    const ip = sema.intern_pool;
    const info = ty.intInfo(ip).?;
    var val_space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
    const val_bigint = val.toBigInt(&val_space, ip);
    const limbs = try sema.arena.alloc(std.math.big.Limb, std.math.big.int.calcTwosCompLimbCount(info.bits));
    var result_bigint: BigIntMutable = .{ .limbs = limbs, .positive = undefined, .len = undefined };
    result_bigint.bitReverse(val_bigint, info.signedness, info.bits);
    return .{ .index = try ip.internIntValue(ty.index, result_bigint.toConst()) };
}

/// Reserve the next `size` bytes of the modeled address space at `align_bytes`
/// alignment and return the aligned base. Advances `comptime_address_cursor`.
/// The one place that hands out a synthetic address, shared by the pointer
/// bases that need one (`@intFromPtr` of a comptime alloc or a decl).
fn nextSyntheticAddress(sema: *Sema, align_bytes: u64, size: u64) u64 {
    const aligned = std.mem.alignForward(u64, sema.comptime_address_cursor, align_bytes);
    sema.comptime_address_cursor = aligned + @max(size, 1);
    return aligned;
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
/// will not equal a real `zig run` address, so the address value is not
/// comparable to the compiler -- but it IS stable per pointer (cached on the
/// alloc slot or in `synthetic_addresses`), so identity holds within a line
/// (`@intFromPtr(&x) == @intFromPtr(&x)`, distinct decls compare unequal).
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
    const ip = sema.intern_pool;
    const ptr_ty = ip.indexToKey(p.ty).ptr_type;
    const natural: InternPool.Alignment = Type.fromIndex(ptr_ty.child).abiAlignment(ip) orelse .@"1";
    const align_bytes: u64 = ptr_ty.flags.alignment.toByteUnits() orelse natural.toByteUnits().?;
    const size: u64 = Type.fromIndex(ptr_ty.child).abiSize(ip) orelse 1;

    const base: u64 = switch (p.base_addr) {
        .comptime_alloc => |i| blk: {
            const slot = &sema.comptime_allocs.items[@intFromEnum(i)];
            break :blk slot.address orelse addr: {
                const aligned = sema.nextSyntheticAddress(align_bytes, size);
                slot.address = aligned;
                break :addr aligned;
            };
        },
        // A decl (`.nav`) or anonymous-constant (`.uav`) pointer has no Sema
        // slot to cache on, so key the synthetic address on the interned pointer
        // itself. zig folds `@intFromPtr(&x) % align` through the known alignment
        // (a bare `@intFromPtr(&x)` is a comptime error there); synthesizing an
        // aligned address keeps that invariant, and caching per pointer keeps it
        // stable within the line so `@intFromPtr(&x) == @intFromPtr(&x)` holds.
        // These pointers carry byte_offset 0, so the pointer identity is the base
        // identity.
        .nav, .uav => sema.synthetic_addresses.get(ptr.index) orelse addr: {
            const aligned = sema.nextSyntheticAddress(align_bytes, size);
            try sema.synthetic_addresses.put(sema.gpa, ptr.index, aligned);
            break :addr aligned;
        },
        // A field/element pointer's address needs the byte offset within the
        // aggregate, which auto-layout aggregates don't expose here; a payload
        // pointer sits inside the optional's storage the same way.
        .field, .arr_elem, .opt_payload, .eu_payload => {
            try sema.writer.writeAll("@intFromPtr: address of an aggregate element is not supported\n");
            return error.AnalysisFail;
        },
    };

    const idx = try ip.internInt(.{
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

/// `ret_ptr`: the result pointer a function returns its value through when the
/// return type is result-located (a by-value aggregate). In a comptime block the
/// compiler's `zirRetPtr` allocates a comptime slot of the return type; the body
/// writes the return value into it and `ret_load` reads it back.
fn evalRetPtr(sema: *Sema) Error!?Value {
    const ret_ty = sema.fn_ret_ty;
    const undef_idx = try sema.intern_pool.get(.{ .undef = ret_ty });
    return try sema.pushComptimeAlloc(ret_ty, .{ .index = undef_idx }, false, .none);
}

/// `make_ptr_const`: freeze an `alloc`'s pointer to `*const T` once the value
/// is fully initialised. AstGen emits it for a `const` local (an `alloc` is
/// mutable until then); it marks the comptime-alloc const so later stores are
/// rejected and returns a const-typed pointer to the same slot. Mirrors
/// zirMakePtrConst's "preserve the comptime alloc, just make the pointer
/// const" branch (the anon-decl promotion is a runtime-codegen optimisation
/// this comptime evaluator does not need).
/// Mark the comptime alloc backing `ptr` as const so later stores through it are
/// rejected. Recurses through aggregate-element and optional-payload pointers to
/// the root alloc; a declaration (`.nav`) or anonymous constant (`.uav`) base is
/// already immutable, so freezing is a no-op there. The freeze side of
/// `make_ptr_const`.
fn freezeBacking(sema: *Sema, ptr: InternPool.Key.Ptr) void {
    const ip = sema.intern_pool;
    switch (ptr.base_addr) {
        .comptime_alloc => |idx| sema.comptime_allocs.items[@intFromEnum(idx)].is_const = true,
        .field, .arr_elem => |f| sema.freezeBacking(ip.indexToKey(f.base).ptr),
        .opt_payload, .eu_payload => |base| sema.freezeBacking(ip.indexToKey(base).ptr),
        .nav, .uav => {},
    }
}

fn evalMakePtrConst(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    const ptr = try sema.resolveRef(un_node.operand);
    const ip = sema.intern_pool;
    const p = ip.indexToKey(ptr.index).ptr;
    sema.freezeBacking(p);
    const old = ip.indexToKey(p.ty).ptr_type;
    if (old.flags.is_const) return ptr;
    var flags = old.flags;
    flags.is_const = true;
    const const_ty = try ip.internPtrType(.{ .child = old.child, .sentinel = old.sentinel, .flags = flags });
    const const_ptr = try ip.internPtr(.{ .ty = const_ty, .base_addr = p.base_addr, .byte_offset = p.byte_offset });
    return .{ .index = const_ptr };
}

/// Append a comptime-alloc slot holding `val` (of type `child_ty`) and return a
/// single-item pointer to it (`*align(N) T` / `*const T` per `is_const` and
/// `alignment`). The one place that turns "a value needs an address" into a
/// slot + pointer: shared by `alloc` (undef slot) and the const-ref tags
/// (`ref`, `array_init_ref`), whose pointers are read-only temporaries.
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

/// `alloc_inferred` / `alloc_inferred_mut` / `alloc_inferred_comptime[_mut]`: a
/// `var`/`const` whose type is inferred from its initializer (`var y = expr`).
/// The type is unknown here, so reserve a slot holding a poison placeholder and
/// return a pointer to it; `store_to_inferred_ptr` then fills the slot and fixes
/// the pointer's element type, and `resolve_inferred_alloc` returns the finished
/// pointer. Mirrors zirAllocInferred[Comptime] -- a comptime-only evaluator always
/// takes the compiler's comptime-inferred-alloc path. `_mut` variants are writable.
fn evalAllocInferred(sema: *Sema, comptime is_const: bool) Error!?Value {
    const placeholder = try sema.intern_pool.get(.{ .undef = .generic_poison_type });
    return try sema.pushComptimeAlloc(.generic_poison_type, .{ .index = placeholder }, is_const, .none);
}

/// `store_to_inferred_ptr lhs, rhs`: the single store that gives an inferred
/// alloc its type. Fill the reserved slot with `rhs` and rebuild the pointer with
/// `rhs`'s type as the element type, then bind that typed pointer as the alloc
/// instruction's result so `resolve_inferred_alloc` returns it. Mirrors
/// storeToInferredAllocComptime -- the comptime path: one store, value known, so
/// the element type is exactly the operand's type (no peer resolution needed).
fn evalStoreToInferredPtr(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    const bin = sema.zir.extraData(Zir.Inst.Bin, pl_node.payload_index).data;
    const ptr = try sema.resolveRef(bin.lhs);
    const operand = try sema.resolveRef(bin.rhs);

    const p = ip.indexToKey(ptr.index).ptr;
    const slot = try sema.lookupComptimeAlloc(p);
    slot.val = operand;

    const ptr_ty = try ip.internPtrType(.{
        .child = operand.typeOf(ip).toIndex(),
        .flags = .{ .size = .one, .is_const = slot.is_const },
    });
    const typed_ptr = try ip.internPtr(.{ .ty = ptr_ty, .base_addr = p.base_addr, .byte_offset = 0 });
    try sema.results.put(sema.gpa, bin.lhs.toIndex().?, .{ .index = typed_ptr });
    return .{ .index = .void_value };
}

/// `resolve_inferred_alloc operand`: the inferred alloc's type is already fixed by
/// its `store_to_inferred_ptr`, so return the retyped pointer bound there. Mirrors
/// zirResolveInferredAlloc's comptime arm ("the work was already done").
fn evalResolveInferredAlloc(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    return try sema.resolveRef(un_node.operand);
}

/// `deref ptr`: the `ptr.*` load. Mirrors `src/Sema.zig:zirDeref` --
/// `validateDeref` then `analyzeLoad`. AstGen folds the former standalone
/// `validate_deref` + `load` pair into this single instruction.
fn evalDeref(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);
    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    assert(un_node.operand != .none);
    const operand = try sema.resolveRef(un_node.operand);
    try sema.validateDeref(operand);
    return try sema.loadValue(operand);
}

/// `ref_deref ptr`: `ptr.*` in a reference context (`&ptr.*`). Mirrors
/// `zirRefDeref` -- validate, then a single-item pointer surfaces as itself and a
/// C pointer narrows to `.one`. Many/slice never reach here (`validateDeref`
/// rejects them).
fn evalRefDeref(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);
    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    assert(un_node.operand != .none);
    const ip = sema.intern_pool;
    const operand = try sema.resolveRef(un_node.operand);
    try sema.validateDeref(operand);
    const ptr_type = ip.indexToKey(operand.typeOf(ip).toIndex()).ptr_type;
    switch (ptr_type.flags.size) {
        .one => return operand,
        .c => {
            var flags = ptr_type.flags;
            flags.size = .one;
            flags.is_allowzero = false;
            const single_ptr_ty = try ip.internPtrType(.{ .child = ptr_type.child, .sentinel = ptr_type.sentinel, .flags = flags });
            return try sema.coerceValueToType(operand, single_ptr_ty, "@as");
        },
        .many, .slice => unreachable,
    }
}

/// Check that `operand` (a value) can be dereferenced. Mirrors
/// `src/Sema.zig:validateDeref`: rejects non-pointers, many/slice pointers
/// (which require index syntax), and the deref of an undefined pointer. The
/// compiler's one-possible-value exception to the undef check is omitted --
/// this evaluator has no OPV classifier, and an undef deref is a hard error
/// for every pointee it currently models.
fn validateDeref(sema: *Sema, operand: Value) Error!void {
    const ip = sema.intern_pool;
    const operand_ty = operand.typeOf(ip);
    const ty_key = ip.indexToKey(operand_ty.toIndex());
    if (ty_key != .ptr_type) {
        try sema.writer.writeAll("cannot dereference non-pointer type '");
        try operand_ty.print(ip, sema.writer);
        try sema.writer.writeAll("'\n");
        return error.AnalysisFail;
    }
    switch (ty_key.ptr_type.flags.size) {
        .one, .c => {},
        .many => {
            try sema.writer.writeAll("index syntax required for unknown-length pointer type '");
            try operand_ty.print(ip, sema.writer);
            try sema.writer.writeAll("'\n");
            return error.AnalysisFail;
        },
        .slice => {
            try sema.writer.writeAll("index syntax required for slice type '");
            try operand_ty.print(ip, sema.writer);
            try sema.writer.writeAll("'\n");
            return error.AnalysisFail;
        },
    }
    if (ip.indexToKey(operand.index) == .undef) {
        try sema.writer.writeAll("cannot dereference undefined value\n");
        return error.AnalysisFail;
    }
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
    // Coerce to the pointee type, then write it through the pointer. `.comptime_alloc`
    // coerces against the slot's current value type (a mutable alloc may have been
    // re-typed); every other base kind coerces against the pointer's child.
    const coerced = if (ptr_key.ptr.base_addr == .comptime_alloc)
        try sema.coerceValueToType(rhs_value, (try sema.lookupComptimeAlloc(ptr_key.ptr)).val.typeOf(ip).toIndex(), "store")
    else
        try sema.coerceValueToType(rhs_value, ptr_ty_key.ptr_type.child, "store");
    try sema.storePointee(ptr_key.ptr, coerced);
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

/// Dereference a Key.ptr Value through its backing storage: a comptime-alloc
/// slot, or a declaration's resolved value for a `.nav` base. Shared by
/// `evalLoad` (ZIR `.load` arm) and the ptr-form switch operand
/// (`switch_block_ref`).
fn loadValue(sema: *Sema, ptr: Value) Error!Value {
    const ip = sema.intern_pool;
    const ptr_key = ip.indexToKey(ptr.index);
    if (ptr_key != .ptr) {
        try sema.writer.writeAll("internal error: load through non-pointer value\n");
        return error.AnalysisFail;
    }
    switch (ptr_key.ptr.base_addr) {
        .nav => |nav| return .{ .index = ip.getNav(nav).resolved.?.value },
        // A `.uav` pointer carries its pointee inline (an anonymous constant).
        .uav => |uav| return .{ .index = uav.val },
        // A field/element pointer (`&l.a`, `&arr[i]`, or the intermediate in
        // `l.a.x` / `arr[i].f`): load the aggregate behind the base pointer, then
        // project the index. The base may itself be a nav, alloc, or another such
        // pointer, so recurse.
        .field, .arr_elem => |f| {
            const parent = try sema.loadValue(.{ .index = f.base });
            const parent_key = ip.indexToKey(parent.index);
            // A not-yet-initialised parent (mid array/struct init) projects to
            // `undef`. Mirrors the compiler's `loadComptimePtrInner`, whose every
            // level returns `.undef` when the value it projects from is `undef`
            // (src/Sema/comptime_ptr_access.zig).
            if (parent_key == .undef) return .{ .index = .undef };
            // A pointer whose pointee is itself an array reads that many consecutive
            // elements into a sub-array, not a single element -- the shape
            // `analyzeSlice` produces for `a[start..end]`. The compiler's `.arr_elem`
            // load gates this on the load type's element base matching the array's
            // (`load_one_ty == base_ty`), so `matrix[i]` (row element type differs)
            // still projects one row.
            if (ptr_key.ptr.base_addr == .arr_elem) sub_array: {
                const child_ty = ip.indexToKey(ptr_key.ptr.ty).ptr_type.child;
                const sub = indexableInfo(ip, child_ty) orelse break :sub_array;
                const agg = switch (parent_key) {
                    .aggregate => |agg| agg,
                    else => break :sub_array,
                };
                const parent_info = indexableInfo(ip, agg.ty) orelse break :sub_array;
                if (parent_info.child != sub.child) break :sub_array;
                // Aggregate storage includes the sentinel slot (`elems.len ==
                // lenIncludingSentinel`), so read that many -- the last element is
                // the sentinel, read from index `f.index + len` of the parent.
                const count = ip.aggregateElementCount(child_ty);
                const elems = try sema.arena.alloc(InternPool.Index, @intCast(count));
                for (elems, 0..) |*e, i| e.* = InternPool.aggregateElementAt(agg, f.index + @as(u64, @intCast(i)));
                return try sema.aggregateValue(Type.fromIndex(child_ty), elems);
            }
            return switch (parent_key) {
                // A union stores only the active field's payload, not a positional
                // slot per field; reading a field pointer checks the active tag,
                // mirroring `unionFieldPtr`'s comptime load.
                .un => try sema.loadUnionField(parent.index, @intCast(f.index)),
                .aggregate => |agg| .{ .index = InternPool.aggregateElementAt(agg, @intCast(f.index)) },
                else => unreachable, // an element/field ptr always projects one of the above
            };
        },
        // A pointer to an optional's payload (`p.?` as an lvalue): load the
        // optional behind `base`, then project its payload. Non-null is checked
        // where the pointer is formed (`analyzeOptionalPayloadPtr`).
        .opt_payload => |base| {
            const opt = try sema.loadValue(.{ .index = base });
            // A not-yet-initialised optional (a result `*?T` mid-init) projects to
            // `undef`, as the `.field`/`.arr_elem` arm above does.
            return switch (ip.indexToKey(opt.index)) {
                .undef => .{ .index = .undef },
                else => .{ .index = ip.indexToKey(opt.index).opt.val },
            };
        },
        // A pointer to an error union's payload (`err_union_payload_unsafe_ptr`,
        // the payload branch of a pointer-form `catch`/`try`): load the union
        // behind `base` and project its payload. The non-error case is checked
        // where the pointer is formed (`is_non_err_ptr`); a comptime-known error
        // reaching here means the wrong branch was taken.
        .eu_payload => |base| {
            const eu = try sema.loadValue(.{ .index = base });
            return switch (ip.indexToKey(eu.index)) {
                .undef => .{ .index = .undef },
                .error_union => |e| switch (e.val) {
                    .payload => |p| .{ .index = p },
                    .err_name => {
                        try sema.writer.writeAll("err_union_payload: operand carries an error, not a payload\n");
                        return error.AnalysisFail;
                    },
                },
                else => unreachable,
            };
        },
        else => {
            const alloc = try sema.lookupComptimeAlloc(ptr_key.ptr);
            return alloc.val;
        },
    }
}

/// Read field `index` of a union value, checking it is the active field. The
/// active field's index is the tag's position in the tag enum (`enumTagFieldIndex`
/// -- for a `union(E)` the tag may hold `E`'s explicit value, so resolve position
/// through the tag enum, not the raw integer). A validated union has matching
/// union/tag field order, so that position equals the union field index. An
/// inactive read is the compiler's "access of union field ... while field ... is
/// active" error. Shared by the field-pointer load and the direct field access.
fn loadUnionField(sema: *Sema, union_val: InternPool.Index, index: u32) Error!Value {
    const ip = sema.intern_pool;
    const uv = ip.indexToKey(union_val).un;
    const tag_ty = ip.indexToKey(uv.tag).enum_tag.ty;
    const active_index = (try sema.enumTagFieldIndex(tag_ty, .{ .index = uv.tag })).?;
    if (active_index == index) return .{ .index = uv.val };
    const accessed = (try sema.unionFieldNameAt(uv.ty, index)) orelse unreachable;
    const active_name = (try sema.unionFieldNameAt(uv.ty, active_index)) orelse unreachable;
    try sema.writer.print("access of union field '{s}' while field '{s}' is active\n", .{
        ip.stringSlice(accessed), ip.stringSlice(active_name),
    });
    return error.AnalysisFail;
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

/// The result of `coerceInMemoryAllowed`. Mirrors the compiler's
/// `InMemoryCoercionResult` (src/Sema.zig) variant-for-variant, including the
/// recursive `child` reason tree (allocated in `sema.arena`, like the compiler).
/// The compiler's `report` appends `LazySrcLoc`-anchored notes to a `Zcu.ErrorMsg`;
/// the REPL has neither, so its `report` writes the same note text to `sema.writer`
/// (the one bit that legitimately cannot port -- the note *sink*).
const InMemoryCoercionResult = union(enum) {
    ok: Strategy,
    no_match: Pair,
    int_not_coercible: Int,
    comptime_int_not_coercible: TypeValuePair,
    error_union_payload: PairAndChild,
    array_len: IntPair,
    array_sentinel: Sentinel,
    array_elem: PairAndChild,
    vector_len: IntPair,
    vector_elem: PairAndChild,
    optional_shape: Pair,
    optional_child: PairAndChild,
    from_anyerror,
    missing_error: []const InternPool.NullTerminatedString,
    fn_var_args: bool,
    fn_generic: bool,
    fn_param_count: IntPair,
    fn_param_noalias: IntPair,
    fn_param_comptime: ComptimeParam,
    fn_param: Param,
    fn_cc: CC,
    fn_return_type: PairAndChild,
    ptr_child: PairAndChild,
    ptr_addrspace: AddressSpace,
    ptr_sentinel: Sentinel,
    ptr_size: Size,
    ptr_const: Pair,
    ptr_volatile: Pair,
    ptr_allowzero: Pair,
    ptr_bit_range: BitRange,
    ptr_alignment: AlignPair,
    double_ptr_to_anyopaque: Pair,
    slice_to_anyopaque: Pair,

    const Strategy = enum { none, same_type, bit_cast, ptr_cast, error_cast };
    const Pair = struct { actual: Type, wanted: Type };
    const TypeValuePair = struct { actual: Value, wanted: Type };
    const PairAndChild = struct { child: *InMemoryCoercionResult, actual: Type, wanted: Type };
    const Param = struct { child: *InMemoryCoercionResult, actual: Type, wanted: Type, index: u64 };
    const ComptimeParam = struct { index: u64, wanted: bool };
    // `unreachable_value` indicates no sentinel.
    const Sentinel = struct { actual: Value, wanted: Value, ty: Type };
    const Int = struct {
        actual_signedness: std.lang.Signedness,
        wanted_signedness: std.lang.Signedness,
        actual_bits: u16,
        wanted_bits: u16,
    };
    const IntPair = struct { actual: u64, wanted: u64 };
    const AlignPair = struct { actual: InternPool.Alignment, wanted: InternPool.Alignment };
    const Size = struct { actual: std.lang.Type.Pointer.Size, wanted: std.lang.Type.Pointer.Size };
    const AddressSpace = struct { actual: std.lang.AddressSpace, wanted: std.lang.AddressSpace };
    const CC = struct { actual: std.lang.CallingConvention, wanted: std.lang.CallingConvention };
    const BitRange = struct { actual_host: u16, wanted_host: u16, actual_offset: u16, wanted_offset: u16 };

    fn dupe(child: *const InMemoryCoercionResult, arena: Allocator) !*InMemoryCoercionResult {
        const res = try arena.create(InMemoryCoercionResult);
        res.* = child.*;
        return res;
    }

    /// Write the reason chain as diagnostic notes to `sema.writer`, mirroring the
    /// compiler's `report`. Type/value formatting goes through `Type.print` /
    /// `render_value.render` instead of the compiler's `{f}` value formatters; the
    /// `no_match` case's "declared here" notes are `LazySrcLoc`-only, so they are
    /// omitted (the caller's message already names the two types).
    fn report(res: *const InMemoryCoercionResult, sema: *Sema) Error!void {
        const ip = sema.intern_pool;
        const w = sema.writer;
        var cur = res;
        while (true) switch (cur.*) {
            .ok => unreachable,
            .no_match => break,
            .int_not_coercible => |int| {
                try w.print("{s} {d}-bit int cannot represent all possible {s} {d}-bit values\n", .{
                    @tagName(int.wanted_signedness), int.wanted_bits, @tagName(int.actual_signedness), int.actual_bits,
                });
                break;
            },
            .comptime_int_not_coercible => |int| {
                try w.writeAll("type '");
                try Type.print(int.wanted, ip, w);
                try w.writeAll("' cannot represent value '");
                try render_value.render(int.actual, ip, w);
                try w.writeAll("'\n");
                break;
            },
            .error_union_payload => |pair| {
                try noteTwoTypes(sema, "error union payload '", pair.actual, "' cannot cast into error union payload '", pair.wanted);
                cur = pair.child;
            },
            .array_len => |lens| {
                try w.print("array of length {d} cannot cast into an array of length {d}\n", .{ lens.actual, lens.wanted });
                break;
            },
            .array_sentinel => |sentinel| {
                try noteSentinel(sema, "source array cannot be guaranteed to maintain '", "destination array requires '", "array sentinel '", "' cannot cast into array sentinel '", sentinel);
                break;
            },
            .array_elem => |pair| {
                try noteTwoTypes(sema, "array element type '", pair.actual, "' cannot cast into array element type '", pair.wanted);
                cur = pair.child;
            },
            .vector_len => |lens| {
                try w.print("vector of length {d} cannot cast into a vector of length {d}\n", .{ lens.actual, lens.wanted });
                break;
            },
            .vector_elem => |pair| {
                try noteTwoTypes(sema, "vector element type '", pair.actual, "' cannot cast into vector element type '", pair.wanted);
                cur = pair.child;
            },
            .optional_shape => |pair| {
                try noteTwoTypes(sema, "optional type child '", pair.actual.optionalChild(ip), "' cannot cast into optional type child '", pair.wanted.optionalChild(ip));
                break;
            },
            .optional_child => |pair| {
                try noteTwoTypes(sema, "optional type child '", pair.actual, "' cannot cast into optional type child '", pair.wanted);
                cur = pair.child;
            },
            .from_anyerror => {
                try w.writeAll("global error set cannot cast into a smaller set\n");
                break;
            },
            .missing_error => |missing_errors| {
                for (missing_errors) |err| try w.print("'error.{s}' not a member of destination error set\n", .{ip.stringSlice(err)});
                break;
            },
            .fn_var_args => |wanted_var_args| {
                try w.writeAll(if (wanted_var_args) "non-variadic function cannot cast into a variadic function\n" else "variadic function cannot cast into a non-variadic function\n");
                break;
            },
            .fn_generic => |wanted_generic| {
                try w.writeAll(if (wanted_generic) "non-generic function cannot cast into a generic function\n" else "generic function cannot cast into a non-generic function\n");
                break;
            },
            .fn_param_count => |lens| {
                try w.print("function with {d} parameters cannot cast into a function with {d} parameters\n", .{ lens.actual, lens.wanted });
                break;
            },
            .fn_param_noalias => |param| {
                var index: u6 = 0;
                var actual_noalias = false;
                while (true) : (index += 1) {
                    const actual: u1 = @truncate(param.actual >> index);
                    const wanted: u1 = @truncate(param.wanted >> index);
                    if (actual != wanted) {
                        actual_noalias = actual == 1;
                        break;
                    }
                }
                if (!actual_noalias) {
                    try w.print("regular parameter {d} cannot cast into a noalias parameter\n", .{index});
                } else {
                    try w.print("noalias parameter {d} cannot cast into a regular parameter\n", .{index});
                }
                break;
            },
            .fn_param_comptime => |param| {
                if (param.wanted) {
                    try w.print("non-comptime parameter {d} cannot cast into a comptime parameter\n", .{param.index});
                } else {
                    try w.print("comptime parameter {d} cannot cast into a non-comptime parameter\n", .{param.index});
                }
                break;
            },
            .fn_param => |param| {
                try w.print("parameter {d} '", .{param.index});
                try Type.print(param.actual, ip, w);
                try w.writeAll("' cannot cast into '");
                try Type.print(param.wanted, ip, w);
                try w.writeAll("'\n");
                cur = param.child;
            },
            .fn_cc => |cc| {
                try w.print("calling convention '{s}' cannot cast into calling convention '{s}'\n", .{ @tagName(cc.actual), @tagName(cc.wanted) });
                break;
            },
            .fn_return_type => |pair| {
                try noteTwoTypes(sema, "return type '", pair.actual, "' cannot cast into return type '", pair.wanted);
                cur = pair.child;
            },
            .ptr_child => |pair| {
                try noteTwoTypes(sema, "pointer type child '", pair.actual, "' cannot cast into pointer type child '", pair.wanted);
                cur = pair.child;
            },
            .ptr_addrspace => |addr_space| {
                try w.print("address space '{s}' cannot cast into address space '{s}'\n", .{ @tagName(addr_space.actual), @tagName(addr_space.wanted) });
                break;
            },
            .ptr_sentinel => |sentinel| {
                try noteSentinel(sema, "", "destination pointer requires '", "pointer sentinel '", "' cannot cast into pointer sentinel '", sentinel);
                break;
            },
            .ptr_size => |size| {
                try w.print("a {s} cannot cast into a {s}\n", .{ pointerSizeString(size.actual), pointerSizeString(size.wanted) });
                break;
            },
            .ptr_const => |pair| {
                if (pair.actual.isConstPtr(ip) and !pair.wanted.isConstPtr(ip)) {
                    try w.writeAll("cast discards const qualifier\n");
                } else {
                    try noteTwoTypes(sema, "mutable '", pair.wanted, "' would allow illegal const pointers stored to type '", pair.actual);
                }
                break;
            },
            .ptr_volatile => |pair| {
                if (pair.actual.isVolatilePtr(ip) and !pair.wanted.isVolatilePtr(ip)) {
                    try w.writeAll("cast discards volatile qualifier\n");
                } else {
                    try noteTwoTypes(sema, "mutable '", pair.wanted, "' would allow illegal volatile pointers stored to type '", pair.actual);
                }
                break;
            },
            .ptr_allowzero => |pair| {
                const wanted_allow_zero = pair.wanted.ptrAllowsZero(ip);
                const actual_allow_zero = pair.actual.ptrAllowsZero(ip);
                if (actual_allow_zero and !wanted_allow_zero) {
                    try noteTwoTypes(sema, "'", pair.actual, "' could have null values which are illegal in type '", pair.wanted);
                } else {
                    try noteTwoTypes(sema, "mutable '", pair.wanted, "' would allow illegal null values stored to type '", pair.actual);
                }
                break;
            },
            .ptr_bit_range => |bit_range| {
                if (bit_range.actual_host != bit_range.wanted_host)
                    try w.print("pointer host size '{d}' cannot cast into pointer host size '{d}'\n", .{ bit_range.actual_host, bit_range.wanted_host });
                if (bit_range.actual_offset != bit_range.wanted_offset)
                    try w.print("pointer bit offset '{d}' cannot cast into pointer bit offset '{d}'\n", .{ bit_range.actual_offset, bit_range.wanted_offset });
                break;
            },
            .ptr_alignment => |pair| {
                try w.print("pointer alignment '{d}' cannot cast into pointer alignment '{d}'\n", .{ pair.actual.toByteUnits() orelse 0, pair.wanted.toByteUnits() orelse 0 });
                break;
            },
            .double_ptr_to_anyopaque => |pair| {
                try noteTwoTypes(sema, "cannot implicitly cast double pointer '", pair.actual, "' to anyopaque pointer '", pair.wanted);
                break;
            },
            .slice_to_anyopaque => |pair| {
                try noteTwoTypes(sema, "cannot implicitly cast slice '", pair.actual, "' to anyopaque pointer '", pair.wanted);
                try w.writeAll("consider using '.ptr'\n");
                break;
            },
        };
    }
};

/// A `report` note of the shape `<pre>TYPE<mid>TYPE'\n` (the two-type notes that
/// pepper `InMemoryCoercionResult.report`).
fn noteTwoTypes(sema: *Sema, pre: []const u8, a: Type, mid: []const u8, b: Type) Error!void {
    const w = sema.writer;
    try w.writeAll(pre);
    try Type.print(a, sema.intern_pool, w);
    try w.writeAll(mid);
    try Type.print(b, sema.intern_pool, w);
    try w.writeAll("'\n");
}

/// The sentinel-mismatch note shared by `array_sentinel` and `ptr_sentinel`
/// (`unreachable_value` means "no sentinel").
fn noteSentinel(sema: *Sema, missing_actual: []const u8, missing_wanted: []const u8, both_pre: []const u8, both_mid: []const u8, sentinel: InMemoryCoercionResult.Sentinel) Error!void {
    const ip = sema.intern_pool;
    const w = sema.writer;
    if (sentinel.wanted.index == .unreachable_value) {
        try w.writeAll(missing_actual);
        try render_value.render(sentinel.actual, ip, w);
        try w.writeAll("'\n");
    } else if (sentinel.actual.index == .unreachable_value) {
        try w.writeAll(missing_wanted);
        try render_value.render(sentinel.wanted, ip, w);
        try w.writeAll("'\n");
    } else {
        try w.writeAll(both_pre);
        try render_value.render(sentinel.actual, ip, w);
        try w.writeAll(both_mid);
        try render_value.render(sentinel.wanted, ip, w);
        try w.writeAll("'\n");
    }
}

fn pointerSizeString(size: std.lang.Type.Pointer.Size) []const u8 {
    return switch (size) {
        .one => "single pointer",
        .many => "many pointer",
        .c => "C pointer",
        .slice => "slice",
    };
}

/// If types `A` and `B` have identical representations in runtime memory, they are
/// "in-memory coercible" -- `A` coerces to `B`, and so do pointers (`*const A` ->
/// `*const B`). Mirrors the compiler's `coerceInMemoryAllowed`, arm for arm. The
/// REPL drops the `block`/`*_src` (no `LazySrcLoc`) and `target` (single host
/// target) parameters. `src_val` refines the comptime-int arm's diagnostic.
fn coerceInMemoryAllowed(sema: *Sema, dest_ty: Type, src_ty: Type, dest_is_mut: bool, src_val: ?Value) Error!InMemoryCoercionResult {
    const ip = sema.intern_pool;
    if (dest_ty.index == src_ty.index) return .{ .ok = .same_type };

    const dest_tag = dest_ty.zigTypeTag(ip);
    const src_tag = src_ty.zigTypeTag(ip);

    // Differently-named integers with the same number of bits.
    if (dest_tag == .int and src_tag == .int) {
        const dest_info = dest_ty.intInfo(ip).?;
        const src_info = src_ty.intInfo(ip).?;
        if (dest_info.signedness == src_info.signedness and dest_info.bits == src_info.bits) return .{ .ok = .bit_cast };
        if ((src_info.signedness == dest_info.signedness and dest_info.bits < src_info.bits) or
            (dest_info.signedness == .signed and src_info.signedness == .unsigned and dest_info.bits <= src_info.bits) or
            (dest_info.signedness == .unsigned and src_info.signedness == .signed))
        {
            return .{ .int_not_coercible = .{
                .actual_signedness = src_info.signedness,
                .wanted_signedness = dest_info.signedness,
                .actual_bits = src_info.bits,
                .wanted_bits = dest_info.bits,
            } };
        }
    }

    // Comptime int to regular int.
    if (dest_tag == .int and src_tag == .comptime_int) {
        if (src_val) |val| {
            if (!sema.intFitsInType(val, dest_ty)) {
                return .{ .comptime_int_not_coercible = .{ .wanted = dest_ty, .actual = val } };
            }
        }
    }

    // Differently-named floats with the same number of bits.
    if (dest_tag == .float and src_tag == .float) {
        if (dest_ty.floatBits() == src_ty.floatBits()) return .{ .ok = .bit_cast };
    }

    // Pointers / Pointer-like Optionals.
    if (dest_ty.isPtrAtRuntime(ip) and src_ty.isPtrAtRuntime(ip)) {
        return try sema.coerceInMemoryAllowedPtrs(dest_ty, src_ty, dest_is_mut);
    }

    // Slices.
    if (dest_ty.isSlice(ip) and src_ty.isSlice(ip)) {
        return try sema.coerceInMemoryAllowedPtrs(dest_ty, src_ty, dest_is_mut);
    }

    // Functions.
    if (dest_tag == .@"fn" and src_tag == .@"fn") {
        return try sema.coerceInMemoryAllowedFns(dest_ty, src_ty, dest_is_mut);
    }

    // Error Unions.
    if (dest_tag == .error_union and src_tag == .error_union) {
        const dest_payload = dest_ty.errorUnionPayload(ip);
        const src_payload = src_ty.errorUnionPayload(ip);
        const payload_strat = switch (try sema.coerceInMemoryAllowed(dest_payload, src_payload, dest_is_mut, null)) {
            .ok => |strat| strat,
            else => |payload_result| return .{ .error_union_payload = .{
                .child = try payload_result.dupe(sema.arena),
                .actual = src_payload,
                .wanted = dest_payload,
            } },
        };
        switch (try sema.coerceInMemoryAllowed(dest_ty.errorUnionSet(ip), src_ty.errorUnionSet(ip), dest_is_mut, null)) {
            .ok => {},
            else => |err_set_result| return err_set_result,
        }
        return switch (payload_strat) {
            .same_type => .{ .ok = .error_cast },
            else => .{ .ok = .none },
        };
    }

    // Error Sets.
    if (dest_tag == .error_set and src_tag == .error_set) {
        switch (try sema.coerceInMemoryAllowedErrorSets(dest_ty, src_ty)) {
            .ok => |strat| assert(strat == .error_cast),
            else => |result| return result,
        }
        if (dest_is_mut) {
            switch (try sema.coerceInMemoryAllowedErrorSets(src_ty, dest_ty)) {
                .ok => |strat| assert(strat == .error_cast),
                else => |result| return result,
            }
        }
        return .{ .ok = .error_cast };
    }

    // Arrays.
    if (dest_tag == .array and src_tag == .array) {
        const dest_info = dest_ty.arrayInfo(ip);
        const src_info = src_ty.arrayInfo(ip);
        if (dest_info.len != src_info.len) return .{ .array_len = .{ .actual = src_info.len, .wanted = dest_info.len } };
        const child = try sema.coerceInMemoryAllowed(dest_info.elem_type, src_info.elem_type, dest_is_mut, null);
        const child_strat = switch (child) {
            .ok => |strat| strat,
            .no_match => |no_match| return .{ .no_match = no_match },
            else => return .{ .array_elem = .{
                .child = try child.dupe(sema.arena),
                .actual = src_info.elem_type,
                .wanted = dest_info.elem_type,
            } },
        };
        // The compiler coerces the src sentinel to the dest element type before
        // comparing; interned sentinels of the same element type compare by identity.
        const ok_sent = (dest_info.sentinel == null and src_info.sentinel == null) or
            (src_info.sentinel != null and dest_info.sentinel != null and dest_info.sentinel.? == src_info.sentinel.?);
        if (!ok_sent) {
            return .{ .array_sentinel = .{
                .actual = if (src_info.sentinel) |s| .{ .index = s } else .{ .index = .unreachable_value },
                .wanted = if (dest_info.sentinel) |s| .{ .index = s } else .{ .index = .unreachable_value },
                .ty = dest_info.elem_type,
            } };
        }
        return .{ .ok = switch (child_strat) {
            .bit_cast => .bit_cast,
            else => .none,
        } };
    }

    // Vectors.
    if (dest_tag == .vector and src_tag == .vector) {
        const dest_len = dest_ty.vectorLen(ip);
        const src_len = src_ty.vectorLen(ip);
        if (dest_len != src_len) return .{ .vector_len = .{ .actual = src_len, .wanted = dest_len } };
        const dest_elem_ty = dest_ty.scalarType(ip);
        const src_elem_ty = src_ty.scalarType(ip);
        switch (try sema.coerceInMemoryAllowed(dest_elem_ty, src_elem_ty, dest_is_mut, null)) {
            .ok => |child_strat| return .{ .ok = switch (child_strat) {
                .bit_cast => .bit_cast,
                .ptr_cast => .ptr_cast,
                else => .none,
            } },
            else => |child_result| return .{ .vector_elem = .{
                .child = try child_result.dupe(sema.arena),
                .actual = src_elem_ty,
                .wanted = dest_elem_ty,
            } },
        }
    }

    // Optionals.
    if (dest_tag == .optional and src_tag == .optional) {
        if (dest_ty.isPtrAtRuntime(ip) or src_ty.isPtrAtRuntime(ip)) {
            return .{ .optional_shape = .{ .actual = src_ty, .wanted = dest_ty } };
        }
        const dest_child_type = dest_ty.optionalChild(ip);
        const src_child_type = src_ty.optionalChild(ip);
        const child = try sema.coerceInMemoryAllowed(dest_child_type, src_child_type, dest_is_mut, null);
        if (child != .ok) return .{ .optional_child = .{
            .child = try child.dupe(sema.arena),
            .actual = src_child_type,
            .wanted = dest_child_type,
        } };
        return .{ .ok = .none };
    }

    // Tuples (with in-memory-coercible fields). The REPL's `tuple_type` stores only
    // field types (no comptime markers), so every field is non-comptime -- the
    // compiler's `structFieldIsComptime` parity check is trivially satisfied.
    if (dest_ty.isTuple(ip) and src_ty.isTuple(ip)) tuple: {
        const dest_types = ip.indexToKey(dest_ty.index).tuple_type.types;
        const src_types = ip.indexToKey(src_ty.index).tuple_type.types;
        if (dest_types.len != src_types.len) break :tuple;
        for (dest_types, src_types) |dft, sft| {
            const field = try sema.coerceInMemoryAllowed(.fromIndex(dft), .fromIndex(sft), dest_is_mut, null);
            if (field != .ok) break :tuple;
        }
        return .{ .ok = .none };
    }

    return .{ .no_match = .{ .actual = dest_ty, .wanted = src_ty } };
}

/// Whether a `comptime_int` value fits in fixed-width int `ty`. Mirrors
/// `Value.intFitsInType` via `std.math.big.int`'s `fitsInTwosComp`.
fn intFitsInType(sema: *Sema, val: Value, ty: Type) bool {
    const info = ty.intInfo(sema.intern_pool).?;
    var space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
    const big = sema.intern_pool.indexToKey(val.index).int.storage.toBigInt(&space);
    return big.fitsInTwosComp(info.signedness, info.bits);
}

/// Pointer (and slice) in-memory coercion. Mirrors `coerceInMemoryAllowedPtrs`.
/// The REPL's no-layout pointer model carries no packed host-size/bit-offset, so
/// the compiler's `ptr_bit_range` check is a no-op here and is omitted.
fn coerceInMemoryAllowedPtrs(sema: *Sema, dest_ty: Type, src_ty: Type, dest_is_mut: bool) Error!InMemoryCoercionResult {
    const ip = sema.intern_pool;
    const dest_info = dest_ty.ptrInfo(ip);
    const src_info = src_ty.ptrInfo(ip);

    const ok_ptr_size = src_info.flags.size == dest_info.flags.size or src_info.flags.size == .c or dest_info.flags.size == .c;
    if (!ok_ptr_size) return .{ .ptr_size = .{ .actual = src_info.flags.size, .wanted = dest_info.flags.size } };

    const ok_const = src_info.flags.is_const == dest_info.flags.is_const or (!dest_is_mut and dest_info.flags.is_const);
    if (!ok_const) return .{ .ptr_const = .{ .actual = src_ty, .wanted = dest_ty } };

    const ok_volatile = src_info.flags.is_volatile == dest_info.flags.is_volatile or (!dest_is_mut and dest_info.flags.is_volatile);
    if (!ok_volatile) return .{ .ptr_volatile = .{ .actual = src_ty, .wanted = dest_ty } };

    const dest_allowzero = dest_ty.ptrAllowsZero(ip);
    const src_allowzero = src_ty.ptrAllowsZero(ip);
    const ok_allowzero = src_allowzero == dest_allowzero or (!dest_is_mut and dest_allowzero);
    if (!ok_allowzero) return .{ .ptr_allowzero = .{ .actual = src_ty, .wanted = dest_ty } };

    if (dest_info.flags.address_space != src_info.flags.address_space) {
        return .{ .ptr_addrspace = .{ .actual = src_info.flags.address_space, .wanted = dest_info.flags.address_space } };
    }

    const dest_child: Type = .fromIndex(dest_info.child);
    const src_child: Type = .fromIndex(src_info.child);
    const child = try sema.coerceInMemoryAllowed(dest_child, src_child, dest_is_mut or !dest_info.flags.is_const, null);
    if (child != .ok) allow: {
        // `*[n:s]T` -> `*[n]T` (dropping the sentinel) is allowed when immutable.
        if (!dest_is_mut and src_child.zigTypeTag(ip) == .array and dest_child.zigTypeTag(ip) == .array and
            src_child.arrayInfo(ip).len == dest_child.arrayInfo(ip).len and
            src_child.arrayInfo(ip).sentinel != null and dest_child.arrayInfo(ip).sentinel == null and
            .ok == try sema.coerceInMemoryAllowed(dest_child.childType(ip), src_child.childType(ip), !dest_info.flags.is_const, null))
        {
            break :allow;
        }
        return .{ .ptr_child = .{
            .child = try child.dupe(sema.arena),
            .actual = .fromIndex(src_info.child),
            .wanted = .fromIndex(dest_info.child),
        } };
    }

    const sentinel_ok = ok: {
        const ss = src_info.sentinel;
        const ds = dest_info.sentinel;
        if (ss == .none and ds == .none) break :ok true;
        if (ss != .none and ds != .none and ds == ss) break :ok true;
        if (src_info.flags.size == .c) break :ok true;
        if (!dest_is_mut and dest_info.sentinel == .none) break :ok true;
        break :ok false;
    };
    if (!sentinel_ok) {
        return .{ .ptr_sentinel = .{
            .actual = if (src_info.sentinel == .none) .{ .index = .unreachable_value } else .{ .index = src_info.sentinel },
            .wanted = if (dest_info.sentinel == .none) .{ .index = .unreachable_value } else .{ .index = dest_info.sentinel },
            .ty = .fromIndex(dest_info.child),
        } };
    }

    if (src_info.flags.alignment != .none or dest_info.flags.alignment != .none or dest_info.child != src_info.child) {
        const src_align = if (src_info.flags.alignment == .none) (src_child.abiAlignment(ip) orelse .none) else src_info.flags.alignment;
        const dest_align = if (dest_info.flags.alignment == .none) (dest_child.abiAlignment(ip) orelse .none) else dest_info.flags.alignment;
        if (dest_align.compare(if (dest_is_mut) .neq else .gt, src_align)) {
            return .{ .ptr_alignment = .{ .actual = src_align, .wanted = dest_align } };
        }
    }

    return .{ .ok = .ptr_cast };
}

/// Function-type in-memory coercion. Mirrors `coerceInMemoryAllowedFns`.
fn coerceInMemoryAllowedFns(sema: *Sema, dest_ty: Type, src_ty: Type, dest_is_mut: bool) Error!InMemoryCoercionResult {
    const ip = sema.intern_pool;
    const dest_info = ip.indexToKey(dest_ty.index).func_type;
    const src_info = ip.indexToKey(src_ty.index).func_type;

    if (dest_info.is_var_args != src_info.is_var_args) return .{ .fn_var_args = dest_info.is_var_args };

    const callconv_ok = callconvCoerceAllowed(src_info.cc, dest_info.cc) and
        (!dest_is_mut or callconvCoerceAllowed(dest_info.cc, src_info.cc));
    if (!callconv_ok) return .{ .fn_cc = .{ .actual = src_info.cc, .wanted = dest_info.cc } };

    const src_is_runtime = fnTypeHasRuntimeBits(src_ty, ip);
    const dest_is_runtime = fnTypeHasRuntimeBits(dest_ty, ip);
    if (src_is_runtime != dest_is_runtime) return .{ .fn_generic = !dest_is_runtime };

    if (!switch (src_info.return_type) {
        .generic_poison_type => true,
        .noreturn_type => !dest_is_mut,
        else => false,
    }) {
        const rt = try sema.coerceInMemoryAllowed(.fromIndex(dest_info.return_type), .fromIndex(src_info.return_type), dest_is_mut, null);
        if (rt != .ok) return .{ .fn_return_type = .{
            .child = try rt.dupe(sema.arena),
            .actual = .fromIndex(src_info.return_type),
            .wanted = .fromIndex(dest_info.return_type),
        } };
    }

    if (dest_info.param_types.len != src_info.param_types.len) {
        return .{ .fn_param_count = .{ .actual = src_info.param_types.len, .wanted = dest_info.param_types.len } };
    }
    if (dest_info.noalias_bits != src_info.noalias_bits) {
        return .{ .fn_param_noalias = .{ .actual = src_info.noalias_bits, .wanted = dest_info.noalias_bits } };
    }

    for (0..dest_info.param_types.len) |param_i| {
        const dest_param_ty: Type = .fromIndex(dest_info.param_types[param_i]);
        const src_param_ty: Type = .fromIndex(src_info.param_types[param_i]);

        comptime_param: {
            const src_is_comptime = src_info.paramIsComptime(@intCast(param_i));
            const dest_is_comptime = dest_info.paramIsComptime(@intCast(param_i));
            if (src_is_comptime == dest_is_comptime) break :comptime_param;
            if (!dest_is_mut and src_is_comptime and !dest_is_comptime and dest_param_ty.comptimeOnly(ip)) break :comptime_param;
            return .{ .fn_param_comptime = .{ .index = param_i, .wanted = dest_is_comptime } };
        }

        if (src_param_ty.index != .generic_poison_type and dest_param_ty.index != .generic_poison_type) {
            // Cast direction is reversed for parameters.
            const param = try sema.coerceInMemoryAllowed(src_param_ty, dest_param_ty, dest_is_mut, null);
            if (param != .ok) return .{ .fn_param = .{
                .child = try param.dupe(sema.arena),
                .actual = dest_param_ty,
                .wanted = src_param_ty,
                .index = param_i,
            } };
        }
    }

    return .{ .ok = .none };
}

/// Whether a function type has runtime bits (i.e. is not generic). Mirrors
/// `Type.fnHasRuntimeBits` using `comptimeOnly` for the param-class check.
fn fnTypeHasRuntimeBits(fn_ty: Type, pool: *const InternPool) bool {
    const info = pool.indexToKey(fn_ty.index).func_type;
    if (info.comptime_bits != 0) return false;
    for (info.param_types) |param_ty| {
        if (param_ty == .generic_poison_type) return false;
        if (Type.fromIndex(param_ty).comptimeOnly(pool)) return false;
    }
    if (info.return_type == .generic_poison_type) return false;
    return true;
}

/// Whether calling convention `src_cc` coerces to `dest_cc`. Copied verbatim from
/// the compiler's `callconvCoerceAllowed`; the host target is the single REPL target.
fn callconvCoerceAllowed(src_cc: std.lang.CallingConvention, dest_cc: std.lang.CallingConvention) bool {
    const target = &@import("builtin").target;
    const Tag = std.lang.CallingConvention.Tag;
    if (@as(Tag, src_cc) != @as(Tag, dest_cc)) return false;

    switch (src_cc) {
        inline else => |src_data, tag| {
            const dest_data = @field(dest_cc, @tagName(tag));
            if (@TypeOf(src_data) != void and @hasField(@TypeOf(src_data), "incoming_stack_alignment")) {
                const default_stack_align = target.stackAlignment();
                const src_stack_align = src_data.incoming_stack_alignment orelse default_stack_align;
                const dest_stack_align = dest_data.incoming_stack_alignment orelse default_stack_align;
                if (dest_stack_align < src_stack_align) return false;
            }
            switch (@TypeOf(src_data)) {
                void, std.lang.CallingConvention.CommonOptions => {},
                std.lang.CallingConvention.X86RegparmOptions => {
                    if (src_data.register_params != dest_data.register_params) return false;
                },
                std.lang.CallingConvention.ArcInterruptOptions => {
                    if (src_data.type != dest_data.type) return false;
                },
                std.lang.CallingConvention.ArmInterruptOptions => {
                    if (src_data.type != dest_data.type) return false;
                },
                std.lang.CallingConvention.MicroblazeInterruptOptions => {
                    if (src_data.type != dest_data.type) return false;
                },
                std.lang.CallingConvention.MipsInterruptOptions => {
                    if (src_data.mode != dest_data.mode) return false;
                },
                std.lang.CallingConvention.RiscvInterruptOptions => {
                    if (src_data.mode != dest_data.mode) return false;
                },
                std.lang.CallingConvention.ShInterruptOptions => {
                    if (src_data.save != dest_data.save) return false;
                },
                std.lang.CallingConvention.SpirvKernelOptions,
                std.lang.CallingConvention.SpirvFragmentOptions,
                std.lang.CallingConvention.SpirvMeshOptions,
                => {},
                else => comptime unreachable,
            }
        },
    }
    return true;
}

/// Error-set in-memory coercion. Mirrors `coerceInMemoryAllowedErrorSets` for the
/// error-set flavours the REPL models -- concrete named sets, `anyerror`, and the
/// `adhoc` marker. The REPL has no per-function inferred-error-set subsystem
/// (`fn_ret_ty_ies` / `inferred_error_set_type`), so those arms do not apply: an
/// `adhoc` destination accepts (as the compiler does, minus recording the set).
fn coerceInMemoryAllowedErrorSets(sema: *Sema, dest_ty: Type, src_ty: Type) Error!InMemoryCoercionResult {
    const ip = sema.intern_pool;
    if (dest_ty.index == .anyerror_type or dest_ty.index == .adhoc_inferred_error_set_type) return .{ .ok = .error_cast };
    const dest_names = ip.indexToKey(dest_ty.index).error_set_type.names;

    if (src_ty.index == .anyerror_type) return .from_anyerror;
    if (src_ty.index == .adhoc_inferred_error_set_type) return .{ .ok = .error_cast };
    const src_names = ip.indexToKey(src_ty.index).error_set_type.names;

    var missing_error_buf: std.ArrayListUnmanaged(InternPool.NullTerminatedString) = .empty;
    defer missing_error_buf.deinit(sema.gpa);
    for (src_names) |name| {
        if (std.mem.indexOfScalar(InternPool.NullTerminatedString, dest_names, name) == null) {
            try missing_error_buf.append(sema.gpa, name);
        }
    }
    if (missing_error_buf.items.len != 0) {
        return .{ .missing_error = try sema.arena.dupe(InternPool.NullTerminatedString, missing_error_buf.items) };
    }
    return .{ .ok = .error_cast };
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

    // Dispatch on the destination type, mirroring `coerceExtra`'s
    // `switch (dest_ty.zigTypeTag())`; each arm is that type's coercion (a helper,
    // as the compiler calls one per arm). Falling through the switch is the
    // compiler's "cannot coerce" tail.
    switch (ip.indexToKey(dest_ty)) {
        // `.int` arm: any fixed-width int type (`intN`, `usize`/`isize`, `c_*`).
        .int_type => if (try sema.coerceToFixedWidthInt(value, dest_ty, op_name)) |c| return c,
        .simple_type => |s| switch (s) {
            .usize, .isize, .c_char, .c_short, .c_ushort, .c_int, .c_uint, .c_long, .c_ulong, .c_longlong, .c_ulonglong => {
                if (try sema.coerceToFixedWidthInt(value, dest_ty, op_name)) |c| return c;
            },
            // `.float` arm: `fN`, `comptime_float`, `c_longdouble`.
            .f16, .f32, .f64, .f80, .f128, .comptime_float, .c_longdouble => {
                if (try sema.coerceToFloat(value, dest_ty, op_name)) |c| return c;
            },
            // A comptime-known fixed-width int coerces to `comptime_int` (every
            // value is comptime-known here, and `comptime_int` has no range
            // limit). Re-intern the same value with `comptime_int_type`. This is
            // what `a << b` needs: the shift amount coerces to `Log2Int` of a
            // `comptime_int` operand, which is `comptime_int` itself.
            .comptime_int => if (ip.indexToKey(value.index) == .int) {
                var space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
                const big = ip.indexToKey(value.index).int.storage.toBigInt(&space);
                return .{ .index = try ip.internIntValue(.comptime_int_type, big) };
            },
            else => {},
        },
        // `.error_union` arm: an error value becomes the `.err` arm; any other
        // value coerces to the payload type and becomes the `.payload` arm.
        .error_union_type => return try sema.coerceToErrorUnion(value, dest_ty, op_name),
        // `.optional` arm: `null` becomes the null optional; any other value
        // coerces to the child type and wraps as the payload.
        .opt_type => return try sema.coerceToOptional(value, dest_ty, op_name),
        // `.pointer` arm: a pointer to an array (`*const [N:0]u8`, e.g. a string
        // literal, or `&[_]T{...}`) coerces to a slice (`len = N`) or to a bare
        // many-pointer (`[*]T`, re-typed, no length).
        .ptr_type => |p| switch (p.flags.size) {
            .slice => if (try sema.coerceToSlice(value, dest_ty)) |c| return c,
            .many => if (try sema.coerceToManyPtr(value, dest_ty)) |c| return c,
            else => {},
        },
        // `.array` / `.vector` arms: an array coerces to a vector (and vice versa)
        // of the same length -- they share the comptime aggregate representation
        // (`coerceArrayLike`).
        .array_type, .vector_type => if (try sema.coerceArrayLike(value, dest_ty, op_name)) |c| return c,
        // `.enum` arm: an `enum_literal` (`.foo`) resolves to the dest enum's tag
        // of that name; an already-correct tag passes through.
        .enum_type => switch (ip.indexToKey(value.index)) {
            .enum_literal => |name| {
                if (try sema.enumTagByName(dest_ty, name)) |tag| return tag;
                return sema.failBadMemberAccess(dest_ty, name);
            },
            .enum_tag => |et| if (et.ty == dest_ty) return value,
            else => {},
        },
        // `.union` arm: an enum literal / tag of the union's tag enum initialises
        // the corresponding void-payload field (`const c: E = .foo`), as
        // `coerceEnumToUnion` does; an already-correct union value passes through.
        .union_type => switch (ip.indexToKey(value.index)) {
            .un => |u| if (u.ty == dest_ty) return value,
            .enum_literal, .enum_tag => return try sema.coerceEnumToUnion(value, dest_ty, op_name),
            else => {},
        },
        else => {},
    }

    try sema.writer.print("{s}: cannot coerce value to destination type\n", .{op_name});
    return error.AnalysisFail;
}

/// Coerce an enum literal or tag to a tagged union by initialising the field the
/// tag selects. Mirrors the compiler's `coerceEnumToUnion`: resolve the tag
/// against the union's tag enum, then -- for a field with a single possible value
/// (a void payload) -- build the union value; a field needing a real payload
/// cannot be initialised from a bare tag.
fn coerceEnumToUnion(sema: *Sema, value: Value, union_ty: InternPool.Index, op_name: []const u8) Error!Value {
    const ip = sema.intern_pool;
    const tag_enum = try sema.unionTagEnumType(union_ty);
    const enum_tag = try sema.coerceValueToType(value, tag_enum, op_name);
    const tag_idx = (try sema.enumTagFieldIndex(tag_enum, enum_tag)).?;
    const tag_name = (try sema.enumFieldName(tag_enum, tag_idx)).?;
    const field = (try sema.unionFieldByName(union_ty, tag_name)).?;
    if (field.ty == .void_type) {
        return .{ .index = try ip.internUnion(.{ .ty = union_ty, .tag = enum_tag.index, .val = .void_value }) };
    }
    if (try sema.isNoPossibleValue(field.ty)) {
        try sema.writer.print("{s}: cannot initialize union field with uninstantiable type\n", .{op_name});
        return error.AnalysisFail;
    }
    try sema.writer.print("{s}: cannot initialize union field '{s}' from a bare tag\n", .{ op_name, ip.stringSlice(tag_name) });
    return error.AnalysisFail;
}

/// Coerce a single-pointer-to-array value (`*const [N]T`) into `dest_ty` (a slice
/// `[]T`): a slice whose `ptr` is the array pointer re-typed to the slice's
/// many-pointer field type (`[*]T`) and whose `len` is the array length. Returns
/// null if `value` is not a pointer to an array (caller reports). Mirrors
/// coerceArrayPtrToSlice's comptime arm (getCoerced to `slicePtrFieldType`).
fn coerceToSlice(sema: *Sema, value: Value, dest_ty: InternPool.Index) Error!?Value {
    const ip = sema.intern_pool;
    if (ip.indexToKey(value.index) != .ptr) return null;
    const array_ptr = ip.indexToKey(value.index).ptr;
    const child = ip.indexToKey(array_ptr.ty).ptr_type.child;
    if (ip.indexToKey(child) != .array_type) return null;
    const array = ip.indexToKey(child).array_type;

    // The slice's ptr field type is a many-ptr (`[*]T`) carrying the slice's
    // constness. `&arr` coerced to `[]T` is `arr[0..arr.len]`, so its many-pointer
    // addresses `arr[0]` -- an `.arr_elem` base into the array pointer, exactly the
    // shape `slice_end` produces for `arr[0..]`. Keeping the two forms identical
    // lets element access and `@memcpy` treat every slice uniformly.
    const many_ptr_ty = try ip.internPtrType(.{
        .child = array.child,
        .flags = .{ .size = .many, .is_const = ip.indexToKey(dest_ty).ptr_type.flags.is_const },
    });
    const many_ptr = try ip.internPtr(.{
        .ty = many_ptr_ty,
        .base_addr = .{ .arr_elem = .{ .base = value.index, .index = 0 } },
        .byte_offset = 0,
    });
    const len_val = try ip.internInt(.{ .ty = .usize_type, .storage = .{ .u64 = array.len } });
    return .{ .index = try ip.get(.{ .slice = .{ .ty = dest_ty, .ptr = many_ptr, .len = len_val } }) };
}

/// Coerce a single-pointer-to-array value (`*const [N]T`) into `dest_ty` (a
/// many-pointer `[*]T`): re-tag the array pointer to the many-pointer type,
/// keeping the same base address (indexing then derefs it like a slice's ptr).
/// Returns null if `value` is not a pointer to an array. Mirrors
/// coerceArrayPtrToMany's comptime arm (getCoerced to the many-pointer type).
fn coerceToManyPtr(sema: *Sema, value: Value, dest_ty: InternPool.Index) Error!?Value {
    const ip = sema.intern_pool;
    if (ip.indexToKey(value.index) != .ptr) return null;
    const array_ptr = ip.indexToKey(value.index).ptr;
    const child = ip.indexToKey(array_ptr.ty).ptr_type.child;
    if (ip.indexToKey(child) != .array_type) return null;
    const retagged = try ip.internPtr(.{ .ty = dest_ty, .base_addr = array_ptr.base_addr, .byte_offset = array_ptr.byte_offset });
    return .{ .index = retagged };
}

/// Coerce an array or vector value to `dest_ty` (a vector or array) of the same
/// length: arrays and vectors share the comptime aggregate representation, so
/// re-tag the aggregate to `dest_ty`, coercing each element to the destination
/// element type (identity for the same element type, widening otherwise). Returns
/// null if `value` is not an aggregate or the lengths differ (caller reports).
/// Mirrors coerceArrayLike's comptime in-memory / element-by-element arms.
fn coerceArrayLike(sema: *Sema, value: Value, dest_ty: InternPool.Index, op_name: []const u8) Error!?Value {
    const ip = sema.intern_pool;
    if (ip.indexToKey(value.index) != .aggregate) return null;
    const src = indexableInfo(ip, Value.typeOf(value, ip).index) orelse return null;
    const dst = indexableInfo(ip, dest_ty).?; // dest is array/vector by the caller's switch
    if (src.len != dst.len) return null;

    const count: usize = @intCast(dst.len);
    const elems = try sema.gpa.alloc(InternPool.Index, count);
    defer sema.gpa.free(elems);
    const agg = ip.indexToKey(value.index).aggregate;
    for (elems, 0..) |*e, i| {
        const elem: Value = .{ .index = InternPool.aggregateElementAt(agg, i) };
        e.* = (try sema.coerceValueToType(elem, dst.child, op_name)).index;
    }
    return .{ .index = try ip.internAggregate(.{ .ty = dest_ty, .storage = .{ .elems = elems } }) };
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
                try sema.writer.writeAll("expected type '");
                try Type.print(.fromIndex(dest_ty), ip, sema.writer);
                try sema.writer.writeAll("', found '");
                try Type.print(.fromIndex(value_type.index), ip, sema.writer);
                try sema.writer.writeAll("'\n");
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

/// `@Int(signedness, bits)` (`reify_int`): reify an integer type from a
/// `std.lang.Signedness` and a bit width -- the inverse of `@typeInfo`'s `.int`
/// arm. Mirrors zirReifyInt.
fn evalReifyInt(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.Bin, pl_node.payload_index).data;
    const signedness = try sema.resolveStdLangEnum(.Signedness, extra.lhs);
    const bits: u16 = @intCast(try sema.resolveInt(try sema.resolveRef(extra.rhs), .u16_type, "int bit width"));
    if (bits == 0 and signedness == .signed) {
        try sema.writer.print("signed integer cannot have bit width 0\n", .{});
        return error.AnalysisFail;
    }
    return .{ .index = try sema.intern_pool.internIntType(signedness, bits) };
}

/// `@Tuple(types)` (`reify_tuple`): build a tuple type from a `[]const type`.
/// Mirrors zirReifyTuple. The REPL's tuple type carries only element types, so
/// `getTupleType`'s parallel `values` array (all `.none` upstream, for comptime
/// fields) has no analogue here.
fn evalReifyTuple(sema: *Sema, extended: Zir.Inst.Extended.InstData) Error!?Value {
    const ip = sema.intern_pool;
    const extra = sema.zir.extraData(Zir.Inst.UnNode, extended.operand).data;

    const types_uncoerced = try sema.resolveRef(extra.operand);
    const types_slice_val = try sema.coerceValueToType(types_uncoerced, try sema.sliceConstTypeTy(), "tuple field types");
    const types_array_val = try sema.derefSliceAsArray(types_slice_val);
    const array = ip.indexToKey(types_array_val.index).aggregate;
    const fields_len: u32 = @intCast(ip.indexToKey(array.ty).array_type.len);

    const field_types = try sema.gpa.alloc(InternPool.Index, fields_len);
    defer sema.gpa.free(field_types);
    for (field_types, 0..) |*field_ty, field_idx| {
        const field_ty_val = InternPool.aggregateElementAt(array, field_idx);
        if (ip.indexToKey(field_ty_val) == .undef) {
            try sema.writer.writeAll("use of undefined value here causes illegal behavior\n");
            return error.AnalysisFail;
        }
        try sema.validateTupleFieldType(field_ty_val);
        field_ty.* = field_ty_val;
    }
    return .{ .index = try ip.internTupleType(field_types) };
}

/// Dereference a comptime slice (or a pointer to an array) to its backing array
/// value. The compiler's `derefSliceAsArray` re-types the slice pointer as a
/// single pointer to the array and `pointerDeref`s it (and passes a pointer-to-
/// array straight through). A `&.{ ... }` literal -- every reification argument --
/// is `arr[0..arr.len]`, so its many-pointer is an `.arr_elem` into the array
/// pointer (the uniform slice shape); the backing array is behind that base. A
/// direct pointer-to-array (`.uav`/`.nav`) resolves straight through `loadValue`.
fn derefSliceAsArray(sema: *Sema, val: Value) Error!Value {
    const ip = sema.intern_pool;
    const array_ptr: InternPool.Index = switch (ip.indexToKey(val.index)) {
        .slice => |s| s.ptr,
        .ptr => val.index,
        else => {
            try sema.writer.writeAll("reify: expected a comptime array-backed slice\n");
            return error.AnalysisFail;
        },
    };
    switch (ip.indexToKey(array_ptr).ptr.base_addr) {
        .uav, .nav => return try sema.loadValue(.{ .index = array_ptr }),
        // A whole-array slice: `arr_elem{ array_ptr, 0 }`. Load the array behind it.
        .arr_elem => |ae| if (ae.index == 0) return try sema.loadValue(.{ .index = ae.base }),
        else => {},
    }
    try sema.writer.writeAll("reify: expected a comptime array-backed slice\n");
    return error.AnalysisFail;
}

/// Reject a tuple field type that cannot be embedded, as the compiler's
/// `validateTupleFieldType` does. Only `anyopaque` and `noreturn` are expressible
/// here (the REPL has no nominal opaque types).
fn validateTupleFieldType(sema: *Sema, field_ty: InternPool.Index) Error!void {
    if (field_ty == .anyopaque_type) {
        try sema.writer.writeAll("opaque types have unknown size and therefore cannot be directly embedded in tuples\n");
        return error.AnalysisFail;
    }
    if (field_ty == .noreturn_type) {
        try sema.writer.writeAll("tuple fields cannot be 'noreturn'\n");
        return error.AnalysisFail;
    }
}

/// `@Pointer(size, attrs, child, sentinel)` (`reify_pointer`): reify a pointer
/// type from a `Type.Pointer.Size`, a `Type.Pointer.Attributes`, the element
/// type, and an optional sentinel. Mirrors zirReifyPointer.
fn evalReifyPointer(sema: *Sema, extended: Zir.Inst.Extended.InstData) Error!?Value {
    const ip = sema.intern_pool;
    const extra = sema.zir.extraData(Zir.Inst.ReifyPointer, extended.operand).data;

    const size_ty = try sema.getStdLangType(.@"Type.Pointer.Size");
    const attrs_ty = try sema.getStdLangType(.@"Type.Pointer.Attributes");

    const size_val = try sema.coerceValueToType(try sema.resolveRef(extra.size), size_ty, "pointer size");
    const size = try sema.interpretStdLangEnum(std.lang.Type.Pointer.Size, size_ty, size_val, "pointer size");

    // Read the `Attributes` aggregate field by field (the REPL's stand-in for
    // `interpretStdLangType` on a struct): const, volatile, allowzero, then the
    // optional address space and alignment.
    const attrs_val = try sema.coerceValueToType(try sema.resolveRef(extra.attrs), attrs_ty, "pointer attributes");
    const attrs = ip.indexToKey(attrs_val.index).aggregate;
    const is_const = InternPool.aggregateElementAt(attrs, 0) == .bool_true;
    const is_volatile = InternPool.aggregateElementAt(attrs, 1) == .bool_true;
    const is_allowzero = InternPool.aggregateElementAt(attrs, 2) == .bool_true;
    const addrspace_opt = ip.indexToKey(InternPool.aggregateElementAt(attrs, 3)).opt.val;
    const align_opt = ip.indexToKey(InternPool.aggregateElementAt(attrs, 4)).opt.val;

    const address_space: std.lang.AddressSpace = if (addrspace_opt != .none)
        try sema.interpretStdLangEnum(std.lang.AddressSpace, try sema.getStdLangType(.AddressSpace), .{ .index = addrspace_opt }, "address space")
    else
        .generic;
    const alignment: InternPool.Alignment = if (align_opt != .none)
        try sema.alignmentFromValue(.{ .index = align_opt }, "pointer alignment")
    else
        .none;

    const elem_ty = try sema.resolveDestType(extra.elem_ty, "pointer child");
    if (elem_ty == .noreturn_type) {
        try sema.writer.writeAll("pointer to noreturn not allowed\n");
        return error.AnalysisFail;
    }
    if (elem_ty == .null_type) {
        try sema.writer.writeAll("cannot reify pointer to '@TypeOf(null)'\n");
        return error.AnalysisFail;
    }
    if (elem_ty == .anyopaque_type and size != .one) {
        try sema.writer.writeAll("indexable pointer to opaque type not allowed\n");
        return error.AnalysisFail;
    }
    if (ip.indexToKey(elem_ty) == .func_type and size != .one) {
        try sema.writer.writeAll("function pointers must be single pointers\n");
        return error.AnalysisFail;
    }

    const sentinel_ty = try ip.internOptionalType(elem_ty);
    const sentinel_val = try sema.coerceValueToType(try sema.resolveRef(extra.sentinel), sentinel_ty, "pointer sentinel");
    const opt_sentinel = ip.indexToKey(sentinel_val.index).opt.val;
    if (opt_sentinel != .none) switch (size) {
        .many, .slice => {},
        .one, .c => {
            try sema.writer.writeAll("sentinels are only allowed on slices and unknown-length pointers\n");
            return error.AnalysisFail;
        },
    };

    return .{ .index = try ip.internPtrType(.{
        .child = elem_ty,
        .sentinel = opt_sentinel,
        .flags = .{
            .size = size,
            .is_const = is_const,
            .is_volatile = is_volatile,
            .is_allowzero = is_allowzero,
            .address_space = address_space,
            .alignment = alignment,
        },
    }) };
}

/// `reify_pointer_sentinel_ty`: the type `@Pointer`'s sentinel argument coerces
/// to -- `?child`, or `?noreturn` when the child (opaque or `@TypeOf(null)`)
/// cannot be an optional's payload. Mirrors zirReifyPointerSentinelTy.
fn evalReifyPointerSentinelTy(sema: *Sema, extended: Zir.Inst.Extended.InstData) Error!?Value {
    const ip = sema.intern_pool;
    const extra = sema.zir.extraData(Zir.Inst.UnNode, extended.operand).data;
    const elem_ty = try sema.resolveDestType(extra.operand, "pointer child");
    const child = if (elem_ty == .anyopaque_type or elem_ty == .null_type) .noreturn_type else elem_ty;
    return .{ .index = try ip.internOptionalType(child) };
}

/// `reify_slice_arg_ty`: the array-pointer type a reification slice argument
/// coerces to -- `*const [len]out`, `len` from the operand slice's length. Mirrors
/// zirReifySliceArgTy. The `@Fn` parameter-attributes and `@Struct` field-type /
/// field-attributes mappings are modelled; `@Union`'s land with `reify_union`.
fn evalReifySliceArgTy(sema: *Sema, extended: Zir.Inst.Extended.InstData) Error!?Value {
    const ip = sema.intern_pool;
    const extra = sema.zir.extraData(Zir.Inst.UnNode, extended.operand).data;
    const info: Zir.Inst.ReifySliceArgInfo = @enumFromInt(extended.small);
    const in_scalar_ty: InternPool.Index, const out_scalar_ty: InternPool.Index = switch (info) {
        .type_to_fn_param_attrs => .{ .type_type, try sema.getStdLangType(.@"Type.Fn.ParamAttributes") },
        .string_to_struct_field_type => .{ try sema.sliceConstU8Ty(), .type_type },
        .string_to_struct_field_attrs => .{ try sema.sliceConstU8Ty(), try sema.getStdLangType(.@"Type.Struct.FieldAttributes") },
        .string_to_union_field_type => .{ try sema.sliceConstU8Ty(), .type_type },
        .string_to_union_field_attrs => .{ try sema.sliceConstU8Ty(), try sema.getStdLangType(.@"Type.Union.FieldAttributes") },
    };
    const operand_ty = try ip.internPtrType(.{ .child = in_scalar_ty, .flags = .{ .size = .slice, .is_const = true } });
    const operand_val = try sema.coerceValueToType(try sema.resolveRef(extra.operand), operand_ty, "reify slice argument");
    const len = try sema.resolveUsizeInt(.{ .index = ip.indexToKey(operand_val.index).slice.len }, "reify slice argument length");
    const arr_ty = try ip.internArrayType(.{ .len = len, .child = out_scalar_ty });
    return .{ .index = try ip.internPtrType(.{ .child = arr_ty, .flags = .{ .size = .one, .is_const = true } }) };
}

/// Read a resolved `std.lang.CallingConvention` union value as the native enum --
/// the calling-convention inverse of `callConvValue`. Only payload-free tags are
/// modelled (the arch tags carry `CommonOptions`), matching the forward direction.
fn interpretCallConv(sema: *Sema, val: Value) Error!std.lang.CallingConvention {
    const ip = sema.intern_pool;
    const un = ip.indexToKey(val.index).un;
    const tag_enum = ip.indexToKey(un.tag).enum_tag.ty;
    const idx = (try sema.enumTagFieldIndex(tag_enum, .{ .index = un.tag })).?;
    const name = ip.stringSlice((try sema.enumFieldName(tag_enum, idx)).?);
    const tag = std.meta.stringToEnum(std.meta.Tag(std.lang.CallingConvention), name) orelse {
        try sema.writer.print("calling convention: unknown variant '{s}'\n", .{name});
        return error.AnalysisFail;
    };
    switch (tag) {
        inline else => |t| {
            if (@FieldType(std.lang.CallingConvention, @tagName(t)) != void) {
                try sema.writer.print("calling convention '{s}' is not modelled\n", .{@tagName(t)});
                return error.AnalysisFail;
            }
            return @unionInit(std.lang.CallingConvention, @tagName(t), {});
        },
    }
}

/// `@Fn(param_types, param_attrs, return_type, attrs)` (`reify_fn`): reify a
/// function type from its parameter types, per-parameter attributes, return type,
/// and function attributes (calling convention, varargs). Mirrors zirReifyFn; the
/// comptime-only evaluator omits the runtime-representability checks
/// (checkParamType / checkReturnTypeAndCallConv).
fn evalReifyFn(sema: *Sema, extended: Zir.Inst.Extended.InstData) Error!?Value {
    const ip = sema.intern_pool;
    const extra = sema.zir.extraData(Zir.Inst.ReifyFn, extended.operand).data;

    const param_types_slice = try sema.coerceValueToType(try sema.resolveRef(extra.param_types), try sema.sliceConstTypeTy(), "fn parameter types");
    const param_types_arr = ip.indexToKey((try sema.derefSliceAsArray(param_types_slice)).index).aggregate;
    const params_len: u32 = @intCast(ip.indexToKey(param_types_arr.ty).array_type.len);

    const param_attrs_arr = ip.indexToKey((try sema.derefSliceAsArray(try sema.resolveRef(extra.param_attrs))).index).aggregate;

    const ret_ty = try sema.resolveDestType(extra.ret_ty, "fn return type");

    const fn_attrs_val = try sema.coerceValueToType(try sema.resolveRef(extra.fn_attrs), try sema.getStdLangType(.@"Type.Fn.Attributes"), "fn attributes");
    const fn_attrs = ip.indexToKey(fn_attrs_val.index).aggregate;
    const cc = try sema.interpretCallConv(.{ .index = InternPool.aggregateElementAt(fn_attrs, 0) });
    const varargs = InternPool.aggregateElementAt(fn_attrs, 1) == .bool_true;

    var noalias_bits: u32 = 0;
    const param_types = try sema.gpa.alloc(InternPool.Index, params_len);
    defer sema.gpa.free(param_types);
    for (param_types, 0..) |*param_ty, param_idx| {
        param_ty.* = InternPool.aggregateElementAt(param_types_arr, param_idx);
        const param_attr = ip.indexToKey(InternPool.aggregateElementAt(param_attrs_arr, param_idx)).aggregate;
        if (InternPool.aggregateElementAt(param_attr, 0) == .bool_true) {
            if (param_idx > 31) {
                try sema.writer.writeAll("this compiler implementation only supports 'noalias' on the first 32 parameters\n");
                return error.AnalysisFail;
            }
            noalias_bits |= @as(u32, 1) << @intCast(param_idx);
        }
    }

    return .{ .index = try ip.internFuncType(.{
        .param_types = param_types,
        .noalias_bits = noalias_bits,
        .return_type = ret_ty,
        .cc = cc,
        .is_var_args = varargs,
    }) };
}

/// The `[]const []const u8` slice type an `@Enum`/`@Struct`/`@Union` field-name
/// argument coerces to (AstGen's `.slice_const_slice_const_u8_type`). The compiler
/// reserves it as a well-known index; the REPL interns it on demand. The element is
/// `[]const u8` with no sentinel, matching the primitive AstGen coerces against.
fn sliceOfStringTy(sema: *Sema) Error!InternPool.Index {
    return try sema.intern_pool.internPtrType(.{ .child = try sema.sliceConstU8Ty(), .flags = .{ .size = .slice, .is_const = true } });
}

/// The `[]const u8` slice type -- a reification string element (a field name), and
/// the `in_scalar_ty` of the string-to-field reify slice-argument mappings.
fn sliceConstU8Ty(sema: *Sema) Error!InternPool.Index {
    return try sema.intern_pool.internPtrType(.{ .child = .u8_type, .flags = .{ .size = .slice, .is_const = true } });
}

/// Read a comptime `[]const u8` slice value into an interned name handle. Mirrors
/// the compiler's `sliceToIpString`: the slice's backing `[N:0]u8` array holds one
/// interned `u8` per byte, which are collected and interned as a string.
fn sliceToIpString(sema: *Sema, slice_val: Value) Error!InternPool.NullTerminatedString {
    const ip = sema.intern_pool;
    const arr = try sema.derefSliceAsArray(slice_val);
    const agg = ip.indexToKey(arr.index).aggregate;
    const len: usize = @intCast(ip.indexToKey(agg.ty).array_type.len);
    const buf = try sema.gpa.alloc(u8, len);
    defer sema.gpa.free(buf);
    // The compiler's `Value.toIpString` reads `bytes` aggregate storage directly;
    // this evaluator has only `elems` storage (one `u8` per slot, as
    // `internStringLiteral` builds), so the bytes are read back one slot at a time.
    // An undef byte is rejected here, as the compiler's `toIpString` checks.
    for (buf, 0..) |*b, i| b.* = @intCast(sema.intAsI128(InternPool.aggregateElementAt(agg, i)) orelse {
        try sema.writer.writeAll("use of undefined value here causes illegal behavior\n");
        return error.AnalysisFail;
    });
    return try ip.getOrPutString(sema.gpa, buf);
}

/// `reify_enum_value_slice_ty`: the array-pointer type `@Enum`'s field-values
/// argument coerces to -- `*const [len]tag_ty`, `len` from the field-names slice's
/// length. Mirrors zirReifyEnumValueSliceTy.
fn evalReifyEnumValueSliceTy(sema: *Sema, extended: Zir.Inst.Extended.InstData) Error!?Value {
    const ip = sema.intern_pool;
    const extra = sema.zir.extraData(Zir.Inst.BinNode, extended.operand).data;
    const int_tag_ty = try sema.resolveDestType(extra.lhs, "enum tag type");
    const names_slice = try sema.coerceValueToType(try sema.resolveRef(extra.rhs), try sema.sliceOfStringTy(), "enum field names");
    const len = try sema.resolveUsizeInt(.{ .index = ip.indexToKey(names_slice.index).slice.len }, "enum field names length");
    const arr_ty = try ip.internArrayType(.{ .len = len, .child = int_tag_ty });
    return .{ .index = try ip.internPtrType(.{ .child = arr_ty, .flags = .{ .size = .one, .is_const = true } }) };
}

/// `@Enum(tag_ty, mode, field_names, field_values)` (`reify_enum`): reify an enum
/// type from its integer tag type, exhaustive/non-exhaustive mode, field names, and
/// per-field values. Mirrors zirReifyEnum: a reified enum's identity is its reify
/// instruction plus a `type_hash` over its inputs (dedup-stable), and it gets an
/// empty namespace. Field storage is filled eagerly from the arguments (there is no
/// ZIR to resolve lazily).
fn evalReifyEnum(sema: *Sema, extended: Zir.Inst.Extended.InstData, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    const name_strategy: Zir.Inst.NameStrategy = @enumFromInt(extended.small);
    const extra = sema.zir.extraData(Zir.Inst.ReifyEnum, extended.operand).data;

    const tag_ty = try sema.resolveDestType(extra.tag_ty, "enum tag type");

    const enum_mode_ty = try sema.getStdLangType(.@"Type.Enum.Mode");
    const mode_val = try sema.coerceValueToType(try sema.resolveRef(extra.mode), enum_mode_ty, "enum mode");
    const nonexhaustive = switch (try sema.interpretStdLangEnum(std.lang.Type.Enum.Mode, enum_mode_ty, mode_val, "enum mode")) {
        .exhaustive => false,
        .nonexhaustive => true,
    };

    const names_slice = try sema.coerceValueToType(try sema.resolveRef(extra.field_names), try sema.sliceOfStringTy(), "enum field names");
    const names_agg = ip.indexToKey((try sema.derefSliceAsArray(names_slice)).index).aggregate;
    const fields_len: u32 = @intCast(ip.indexToKey(names_agg.ty).array_type.len);

    const values_ty = try ip.internPtrType(.{
        .child = try ip.internArrayType(.{ .len = fields_len, .child = tag_ty }),
        .flags = .{ .size = .one, .is_const = true },
    });
    const values_slice = try sema.coerceValueToType(try sema.resolveRef(extra.field_values), values_ty, "enum field values");
    const values_arr = try sema.derefSliceAsArray(values_slice);
    const values_agg = ip.indexToKey(values_arr.index).aggregate;

    const names = try sema.gpa.alloc(InternPool.NullTerminatedString, fields_len);
    defer sema.gpa.free(names);
    for (names, 0..) |*n, i| n.* = try sema.sliceToIpString(.{ .index = InternPool.aggregateElementAt(names_agg, i) });
    const values = try sema.gpa.alloc(InternPool.Index, fields_len);
    defer sema.gpa.free(values);
    for (values, 0..) |*v, i| {
        v.* = InternPool.aggregateElementAt(values_agg, i);
        // Reject undefined field values, as the compiler's `anyUndef` check does;
        // field names are checked in `sliceToIpString`.
        if (ip.indexToKey(v.*) == .undef) {
            try sema.writer.writeAll("use of undefined value here causes illegal behavior\n");
            return error.AnalysisFail;
        }
    }

    // The dedup key is the reify instruction plus a hash over the inputs (Sema
    // computes it so the InternPool Key stays simple). Field names are hashed
    // individually because distinct slice values can intern to the same string.
    var hasher = std.hash.Wyhash.init(0);
    std.hash.autoHash(&hasher, tag_ty);
    std.hash.autoHash(&hasher, nonexhaustive);
    std.hash.autoHash(&hasher, fields_len);
    std.hash.autoHash(&hasher, values_arr.index); // dedup-stable interned aggregate
    for (names) |n| std.hash.autoHash(&hasher, n);

    const name = switch (name_strategy) {
        .parent => sema.type_name_ctx,
        .anon, .func, .dbg_var => blk: {
            const ctx = ip.stringSlice(sema.type_name_ctx);
            const text = try std.fmt.allocPrint(sema.gpa, "{s}__enum_{d}", .{ ctx, @intFromEnum(inst) });
            defer sema.gpa.free(text);
            break :blk try ip.getOrPutString(sema.gpa, text);
        },
    };

    const enum_ty = try ip.internEnumType(.{
        .name = name,
        .id = .{ .reified = .{ .source_zir_id = sema.current_zir_id, .decl_inst = inst, .type_hash = hasher.final() } },
        .parent = sema.this_type,
    });
    try ip.setEnumFields(enum_ty, tag_ty, nonexhaustive, names, values);
    return .{ .index = enum_ty };
}

/// `@Struct(layout, backing_ty, field_names, field_types, field_attrs)`
/// (`reify_struct`): reify a struct type from its layout, optional packed backing
/// integer, field names/types, and per-field attributes (comptime, alignment,
/// default). Mirrors zirReifyStruct. Fields are stored eagerly from the arguments:
/// a reified struct cannot be self-referential (its field types are already-interned
/// values), so no lazy resolution is needed. The runtime layout (offsets, size) is
/// not modelled.
fn evalReifyStruct(sema: *Sema, extended: Zir.Inst.Extended.InstData, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    const name_strategy: Zir.Inst.NameStrategy = @enumFromInt(extended.small);
    const extra = sema.zir.extraData(Zir.Inst.ReifyStruct, extended.operand).data;

    const layout_ty = try sema.getStdLangType(.@"Type.ContainerLayout");
    const layout_val = try sema.coerceValueToType(try sema.resolveRef(extra.layout), layout_ty, "struct layout");
    const layout = try sema.interpretStdLangEnum(std.lang.Type.ContainerLayout, layout_ty, layout_val, "struct layout");

    // backing_ty is `?type`: null unless a packed struct declares a backing integer.
    const backing_val = try sema.coerceValueToType(try sema.resolveRef(extra.backing_ty), try ip.internOptionalType(.type_type), "struct backing integer type");
    if (ip.indexToKey(backing_val.index) == .undef) {
        try sema.writer.writeAll("use of undefined value here causes illegal behavior\n");
        return error.AnalysisFail;
    }
    const backing_int = ip.indexToKey(backing_val.index).opt.val;
    if (backing_int != .none and layout != .@"packed") {
        try sema.writer.writeAll("non-packed struct does not support backing integer type\n");
        return error.AnalysisFail;
    }

    const names_slice = try sema.coerceValueToType(try sema.resolveRef(extra.field_names), try sema.sliceOfStringTy(), "struct field names");
    const names_agg = ip.indexToKey((try sema.derefSliceAsArray(names_slice)).index).aggregate;
    const fields_len: u32 = @intCast(ip.indexToKey(names_agg.ty).array_type.len);

    const field_types_ty = try ip.internPtrType(.{
        .child = try ip.internArrayType(.{ .len = fields_len, .child = .type_type }),
        .flags = .{ .size = .one, .is_const = true },
    });
    const types_arr = try sema.derefSliceAsArray(try sema.coerceValueToType(try sema.resolveRef(extra.field_types), field_types_ty, "struct field types"));
    const types_agg = ip.indexToKey(types_arr.index).aggregate;

    const attrs_scalar_ty = try sema.getStdLangType(.@"Type.Struct.FieldAttributes");
    const field_attrs_ty = try ip.internPtrType(.{
        .child = try ip.internArrayType(.{ .len = fields_len, .child = attrs_scalar_ty }),
        .flags = .{ .size = .one, .is_const = true },
    });
    const attrs_agg = ip.indexToKey((try sema.derefSliceAsArray(try sema.coerceValueToType(try sema.resolveRef(extra.field_attrs), field_attrs_ty, "struct field attributes"))).index).aggregate;

    const names = try sema.gpa.alloc(InternPool.NullTerminatedString, fields_len);
    defer sema.gpa.free(names);
    const types = try sema.gpa.alloc(InternPool.Index, fields_len);
    defer sema.gpa.free(types);
    const defaults = try sema.gpa.alloc(InternPool.Index, fields_len);
    defer sema.gpa.free(defaults);
    @memset(defaults, .none);
    const aligns = try sema.gpa.alloc(InternPool.Index, fields_len);
    defer sema.gpa.free(aligns);
    @memset(aligns, .none);
    const comptime_words = try sema.gpa.alloc(u32, (fields_len + 31) / 32);
    defer sema.gpa.free(comptime_words);
    @memset(comptime_words, 0);
    var any_defaults = false;
    var any_aligns = false;
    var any_comptime = false;

    // The dedup hash mirrors the compiler's: layout, the backing-int value, the
    // (dedup-stable) field-type array, then per-field name/attributes.
    var hasher = std.hash.Wyhash.init(0);
    std.hash.autoHash(&hasher, layout);
    std.hash.autoHash(&hasher, backing_val.index);
    std.hash.autoHash(&hasher, types_arr.index);

    for (names, types, 0..) |*name_out, *type_out, i| {
        name_out.* = try sema.sliceToIpString(.{ .index = InternPool.aggregateElementAt(names_agg, i) });
        type_out.* = InternPool.aggregateElementAt(types_agg, i);
        if (ip.indexToKey(type_out.*) == .undef) {
            try sema.writer.writeAll("use of undefined value here causes illegal behavior\n");
            return error.AnalysisFail;
        }
        // Field attributes are `.{ comptime: bool, align: ?usize, default_value_ptr:
        // ?*const anyopaque }` (the order `@typeInfo`'s struct arm emits).
        const attr_elem = InternPool.aggregateElementAt(attrs_agg, i);
        if (ip.indexToKey(attr_elem) == .undef) {
            try sema.writer.writeAll("use of undefined value here causes illegal behavior\n");
            return error.AnalysisFail;
        }
        const attr = ip.indexToKey(attr_elem).aggregate;
        const comptime_elem = InternPool.aggregateElementAt(attr, 0);
        const align_elem = InternPool.aggregateElementAt(attr, 1);
        const align_opt = ip.indexToKey(align_elem).opt.val;
        const default_ptr = ip.indexToKey(InternPool.aggregateElementAt(attr, 2)).opt.val;

        const field_default: InternPool.Index = if (default_ptr == .none) .none else (try sema.loadValue(.{ .index = default_ptr })).index;
        if (field_default != .none) {
            defaults[i] = field_default;
            any_defaults = true;
        }

        if (comptime_elem == .bool_true) {
            if (field_default == .none) {
                try sema.writer.writeAll("comptime field without default initialization value\n");
                return error.AnalysisFail;
            }
            if (layout != .auto) {
                try sema.writer.writeAll("non-auto struct fields cannot be marked comptime\n");
                return error.AnalysisFail;
            }
            comptime_words[i / 32] |= @as(u32, 1) << @intCast(i % 32);
            any_comptime = true;
        }

        if (align_opt != .none) {
            if (layout == .@"packed") {
                try sema.writer.writeAll("packed struct fields cannot be aligned\n");
                return error.AnalysisFail;
            }
            aligns[i] = align_opt;
            any_aligns = true;
        }

        std.hash.autoHash(&hasher, name_out.*);
        std.hash.autoHash(&hasher, comptime_elem);
        std.hash.autoHash(&hasher, align_elem);
        std.hash.autoHash(&hasher, field_default);
    }

    const name = switch (name_strategy) {
        .parent => sema.type_name_ctx,
        .anon, .func, .dbg_var => blk: {
            const ctx = ip.stringSlice(sema.type_name_ctx);
            const text = try std.fmt.allocPrint(sema.gpa, "{s}__struct_{d}", .{ ctx, @intFromEnum(inst) });
            defer sema.gpa.free(text);
            break :blk try ip.getOrPutString(sema.gpa, text);
        },
    };

    const struct_ty = try ip.internStructType(.{
        .name = name,
        .id = .{ .reified = .{ .source_zir_id = sema.current_zir_id, .decl_inst = inst, .type_hash = hasher.final() } },
        .parent = sema.this_type,
    });
    try ip.setStructFields(
        struct_ty,
        layout,
        backing_int,
        names,
        types,
        if (any_defaults) defaults else &.{},
        if (any_aligns) aligns else &.{},
        if (any_comptime) comptime_words else &.{},
    );
    return .{ .index = struct_ty };
}

/// `@Union(layout, arg_ty, field_names, field_types, field_attrs)` (`reify_union`):
/// reify a union type from its layout, optional tag/backing type, field names/types,
/// and per-field attributes (alignment only). Mirrors zirReifyUnion. Fields are
/// stored eagerly from the arguments (like `@Struct`). `arg_ty` is the explicit tag
/// enum for an `.auto` union; for a `.packed` union it is a backing integer (not a
/// tag), and for `.extern` it is rejected. The runtime layout is not modelled.
fn evalReifyUnion(sema: *Sema, extended: Zir.Inst.Extended.InstData, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    const name_strategy: Zir.Inst.NameStrategy = @enumFromInt(extended.small);
    const extra = sema.zir.extraData(Zir.Inst.ReifyUnion, extended.operand).data;

    const layout_ty = try sema.getStdLangType(.@"Type.ContainerLayout");
    const layout_val = try sema.coerceValueToType(try sema.resolveRef(extra.layout), layout_ty, "union layout");
    const layout = try sema.interpretStdLangEnum(std.lang.Type.ContainerLayout, layout_ty, layout_val, "union layout");

    // arg_ty is `?type`: for `.auto` it is the explicit tag enum; for `.packed` a
    // backing integer (not modelled as a tag); for `.extern` it is not allowed.
    const arg_val = try sema.coerceValueToType(try sema.resolveRef(extra.arg_ty), try ip.internOptionalType(.type_type), "union tag/backing type");
    if (ip.indexToKey(arg_val.index) == .undef) {
        try sema.writer.writeAll("use of undefined value here causes illegal behavior\n");
        return error.AnalysisFail;
    }
    // `arg_ty` is the tag enum for an `.auto` union and the backing integer for a
    // `.packed` one, matching how `zirReifyUnion` splits `explicit_tag_ty` from
    // `explicit_packed_backing_type`.
    const arg_ty = ip.indexToKey(arg_val.index).opt.val;
    var tag_type: InternPool.Index = .none;
    var backing_int: InternPool.Index = .none;
    if (arg_ty != .none) switch (layout) {
        .@"extern" => {
            try sema.writer.writeAll("extern union does not support enum tag type\n");
            return error.AnalysisFail;
        },
        .@"packed" => backing_int = arg_ty,
        .auto => tag_type = arg_ty,
    };

    const names_slice = try sema.coerceValueToType(try sema.resolveRef(extra.field_names), try sema.sliceOfStringTy(), "union field names");
    const names_agg = ip.indexToKey((try sema.derefSliceAsArray(names_slice)).index).aggregate;
    const fields_len: u32 = @intCast(ip.indexToKey(names_agg.ty).array_type.len);

    const field_types_ty = try ip.internPtrType(.{
        .child = try ip.internArrayType(.{ .len = fields_len, .child = .type_type }),
        .flags = .{ .size = .one, .is_const = true },
    });
    const types_arr = try sema.derefSliceAsArray(try sema.coerceValueToType(try sema.resolveRef(extra.field_types), field_types_ty, "union field types"));
    const types_agg = ip.indexToKey(types_arr.index).aggregate;

    const attrs_scalar_ty = try sema.getStdLangType(.@"Type.Union.FieldAttributes");
    const field_attrs_ty = try ip.internPtrType(.{
        .child = try ip.internArrayType(.{ .len = fields_len, .child = attrs_scalar_ty }),
        .flags = .{ .size = .one, .is_const = true },
    });
    const attrs_arr = try sema.derefSliceAsArray(try sema.coerceValueToType(try sema.resolveRef(extra.field_attrs), field_attrs_ty, "union field attributes"));
    const attrs_agg = ip.indexToKey(attrs_arr.index).aggregate;

    const names = try sema.gpa.alloc(InternPool.NullTerminatedString, fields_len);
    defer sema.gpa.free(names);
    const types = try sema.gpa.alloc(InternPool.Index, fields_len);
    defer sema.gpa.free(types);
    const aligns = try sema.gpa.alloc(InternPool.Index, fields_len);
    defer sema.gpa.free(aligns);
    @memset(aligns, .none);
    var any_aligns = false;

    // The dedup hash mirrors the compiler's: layout, the arg-type value, the
    // (dedup-stable) field-type and field-attribute arrays, then per-field name.
    // Field attributes hash wholesale -- a union field's only attribute is its
    // alignment, a value the InternPool already deduplicated.
    var hasher = std.hash.Wyhash.init(0);
    std.hash.autoHash(&hasher, layout);
    std.hash.autoHash(&hasher, arg_val.index);
    std.hash.autoHash(&hasher, types_arr.index);
    std.hash.autoHash(&hasher, attrs_arr.index);

    for (names, types, 0..) |*name_out, *type_out, i| {
        name_out.* = try sema.sliceToIpString(.{ .index = InternPool.aggregateElementAt(names_agg, i) });
        type_out.* = InternPool.aggregateElementAt(types_agg, i);
        if (ip.indexToKey(type_out.*) == .undef) {
            try sema.writer.writeAll("use of undefined value here causes illegal behavior\n");
            return error.AnalysisFail;
        }
        // A union field's attributes are `.{ align: ?usize }`.
        const attr_elem = InternPool.aggregateElementAt(attrs_agg, i);
        if (ip.indexToKey(attr_elem) == .undef) {
            try sema.writer.writeAll("use of undefined value here causes illegal behavior\n");
            return error.AnalysisFail;
        }
        const align_opt = ip.indexToKey(InternPool.aggregateElementAt(ip.indexToKey(attr_elem).aggregate, 0)).opt.val;
        if (align_opt != .none) {
            if (layout == .@"packed") {
                try sema.writer.writeAll("packed union fields cannot be aligned\n");
                return error.AnalysisFail;
            }
            aligns[i] = align_opt;
            any_aligns = true;
        }
        std.hash.autoHash(&hasher, name_out.*);
    }

    const name = switch (name_strategy) {
        .parent => sema.type_name_ctx,
        .anon, .func, .dbg_var => blk: {
            const ctx = ip.stringSlice(sema.type_name_ctx);
            const text = try std.fmt.allocPrint(sema.gpa, "{s}__union_{d}", .{ ctx, @intFromEnum(inst) });
            defer sema.gpa.free(text);
            break :blk try ip.getOrPutString(sema.gpa, text);
        },
    };

    const union_ty = try ip.internUnionType(.{
        .name = name,
        .id = .{ .reified = .{ .source_zir_id = sema.current_zir_id, .decl_inst = inst, .type_hash = hasher.final() } },
        .parent = sema.this_type,
    });
    try ip.setUnionFields(union_ty, layout, tag_type, backing_int, names, types, if (any_aligns) aligns else &.{});
    return .{ .index = union_ty };
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

/// `array_type_sentinel` (`[N:S]T`): `array_type` plus a sentinel terminator `S`
/// coerced to the element type. Mirrors zirArrayTypeSentinel (resolve len + elem,
/// coerce the sentinel, build the array type). The opaque-element and
/// comptime-var-sentinel guards have no REPL analogue; the sentinel is always
/// comptime-known here, and `coerceValueToType` rejects one that will not fit the
/// element type. Compiler reference: src/Sema.zig:zirArrayTypeSentinel (~7490).
fn evalArrayTypeSentinel(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);
    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.ArrayTypeSentinel, pl_node.payload_index).data;
    const len = try sema.resolveArrayLen(extra.len, "array_type");
    const elem_type = try sema.resolveDestType(extra.elem_type, "array_type");
    const uncasted_sentinel = try sema.resolveRef(extra.sentinel);
    const sentinel = try sema.coerceValueToType(uncasted_sentinel, elem_type, "array sentinel");
    // resolveConstDefinedValue: the sentinel must be a defined comptime value.
    if (sema.intern_pool.indexToKey(sentinel.index) == .undef) {
        try sema.writer.writeAll("use of undefined value here causes illegal behavior\n");
        return error.AnalysisFail;
    }
    const array_ty = try sema.intern_pool.internArrayType(.{
        .len = len,
        .sentinel = sentinel.index,
        .child = elem_type,
    });
    try sema.checkSentinelType(elem_type);
    return .{ .index = array_ty };
}

/// A sentinel's element type must be self-comparable, so the terminator can be
/// tested for. Mirrors the compiler's `checkSentinelType` (an array/struct/slice
/// element cannot carry a sentinel). Always the equality form (`==`).
fn checkSentinelType(sema: *Sema, elem_type: InternPool.Index) Error!void {
    if (!Type.fromIndex(elem_type).isSelfComparable(sema.intern_pool, true)) {
        try sema.writer.writeAll("non-scalar sentinel type '");
        try Type.print(.fromIndex(elem_type), sema.intern_pool, sema.writer);
        try sema.writer.writeAll("'\n");
        return error.AnalysisFail;
    }
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

/// `@select(T, pred, a, b)` (extended): a lane-wise blend of two vectors by a
/// bool mask -- `pred[i] ? a[i] : b[i]`. The length comes from `pred` (a
/// `@Vector(N, bool)`); `a`/`b` coerce to `@Vector(N, T)`. Mirrors zirSelect's
/// comptime arm. Compiler reference: src/Sema.zig:zirSelect (~23127).
fn evalSelect(sema: *Sema, extended: Zir.Inst.Extended.InstData) Error!?Value {
    const ip = sema.intern_pool;
    const extra = sema.zir.extraData(Zir.Inst.Select, extended.operand).data;

    const elem_ty = try sema.resolveDestType(extra.elem_type, "@select");
    if (!isVectorElemType(ip, elem_ty)) {
        try sema.writer.writeAll("@select: expected integer, float, bool, or pointer for the element type\n");
        return error.AnalysisFail;
    }
    const pred = try sema.resolveRef(extra.pred);
    const pred_info = indexableInfo(ip, Value.typeOf(pred, ip).index) orelse {
        try sema.writer.writeAll("@select: expected vector or array for the predicate\n");
        return error.AnalysisFail;
    };
    const vec_len = pred_info.len;

    // Coerce `a`/`b` to `@Vector(vec_len, elem_ty)` (they may arrive as arrays).
    const vec_ty = try ip.internVectorType(.{ .len = @intCast(vec_len), .child = elem_ty });
    const a_agg = ip.indexToKey((try sema.coerceValueToType(try sema.resolveRef(extra.a), vec_ty, "@select")).index).aggregate;
    const b_agg = ip.indexToKey((try sema.coerceValueToType(try sema.resolveRef(extra.b), vec_ty, "@select")).index).aggregate;
    const pred_agg = ip.indexToKey(pred.index).aggregate;

    const elems = try sema.gpa.alloc(InternPool.Index, @intCast(vec_len));
    defer sema.gpa.free(elems);
    for (elems, 0..) |*e, i| {
        const chosen = if (InternPool.aggregateElementAt(pred_agg, i) == .bool_true) a_agg else b_agg;
        e.* = InternPool.aggregateElementAt(chosen, i);
    }
    return .{ .index = try ip.internAggregate(.{ .ty = vec_ty, .storage = .{ .elems = elems } }) };
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
/// Compiler reference: src/Sema.zig:zirOptionalPayload (~8037). The `_ptr`
/// pointer-to-payload variants are `evalOptionalPayloadPtr`.
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

/// `optional_payload_safe_ptr` / `_unsafe_ptr` (`p.?` in an lvalue context, e.g.
/// `p.?.field`): given a pointer to an optional (`*?T`), yield a pointer to its
/// payload (`*T`). Mirrors `src/Sema.zig:analyzeOptionalPayloadPtr`'s comptime
/// path -- deref the pointer, reject a `null`, then form a `.opt_payload` pointer
/// (the child pointer type keeps the source pointer's flags, child = payload).
/// The safe/unsafe distinction is a runtime null-check with no comptime analogue.
fn evalOptionalPayloadPtr(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);
    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    return try sema.optPayloadPtr(try sema.resolveRef(un_node.operand), false);
}

/// Given a pointer to an optional (`*?T`), yield a pointer to its payload (`*T`) as
/// an `.opt_payload` projection keeping the source pointer's flags. When
/// `initializing` (a result-location `*?T` about to be written), the payload is
/// being created, so skip the null check; otherwise (`p.?`) a `null` is an error.
fn optPayloadPtr(sema: *Sema, optional_ptr: Value, comptime initializing: bool) Error!Value {
    const ip = sema.intern_pool;
    const ptr_type = ip.indexToKey(optional_ptr.typeOf(ip).toIndex()).ptr_type;
    const opt_key = ip.indexToKey(ptr_type.child);
    if (opt_key != .opt_type) {
        try sema.writer.writeAll("optional unwrap: pointer child is not an optional\n");
        return error.AnalysisFail;
    }
    if (!initializing) {
        const opt_val = try sema.loadValue(optional_ptr);
        if (ip.indexToKey(opt_val.index).opt.val == .none) {
            try sema.writer.writeAll("unable to unwrap null\n");
            return error.AnalysisFail;
        }
    }
    const child_ptr_ty = try ip.internPtrType(.{ .child = opt_key.opt_type, .sentinel = ptr_type.sentinel, .flags = ptr_type.flags });
    return .{ .index = try ip.internPtr(.{
        .ty = child_ptr_ty,
        .base_addr = .{ .opt_payload = optional_ptr.index },
        .byte_offset = 0,
    }) };
}

/// `is_non_null` (`if (opt) |v|`, `orelse`): the comptime null test that
/// feeds the following `condbr`. Mirrors `zirIsNonNull` ->
/// `analyzeIsNull(invert_logic = true)`: the operand is always a
/// comptime-known value here, so the answer is `makeBool(!isNull)`, where
/// `isNull` is `opt.val == .none` (Value.isNull's `.opt` arm).
/// `checkNullableType` rejects a non-optional operand.
/// Compiler reference: src/Sema.zig:zirIsNonNull (~17416).
fn evalIsNonNull(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);
    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    return try sema.isNonNullVal(try sema.resolveRef(un_node.operand));
}

/// `is_non_null_ptr` (`if (p.*) |v|`): the same null test on a pointer to an
/// optional (`*?T`) -- load it, then test. Mirrors `zirIsNonNullPtr`.
fn evalIsNonNullPtr(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);
    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    return try sema.isNonNullVal(try sema.loadValue(try sema.resolveRef(un_node.operand)));
}

/// The non-null predicate on an optional value. Mirrors `analyzeIsNull`.
fn isNonNullVal(sema: *Sema, operand: Value) Error!Value {
    const ip = sema.intern_pool;
    const key = ip.indexToKey(operand.index);
    if (key != .opt) {
        try sema.writer.writeAll("expected optional type, found '");
        try Type.print(operand.typeOf(ip), ip, sema.writer);
        try sema.writer.writeAll("'\n");
        return error.AnalysisFail;
    }
    return .{ .index = if (key.opt.val == .none) .bool_false else .bool_true };
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

/// `struct_init_anon` (`.{ .a = 1, .b = 2 }`): a NAMED anonymous struct. Unlike
/// the compiler -- which bakes an anon struct as a real struct type with inline
/// fields -- this evaluator gives it a `struct_type` whose `decl_inst` is the
/// `struct_init_anon` instruction itself (the reified `ContainerType.zir_index`
/// analogue); the field names/types are re-resolved from that instruction's items
/// on demand, exactly as a declared struct re-resolves from its `struct_decl`.
/// The field values live in the aggregate (the `tuple_type` deviation, so
/// `.{ .a = 1 }` and `.{ .a = 2 }` are NOT distinct types). Compiler reference:
/// src/Sema.zig:zirStructInitAnon -> structInitAnon.
fn evalStructInitAnon(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);
    const ip = sema.intern_pool;
    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.StructInitAnon, pl_node.payload_index);

    const values = try sema.gpa.alloc(InternPool.Index, extra.data.fields_len);
    defer sema.gpa.free(values);
    var extra_index = extra.end;
    for (values) |*val| {
        const item = sema.zir.extraData(Zir.Inst.StructInitAnon.Item, extra_index);
        extra_index = item.end;
        val.* = (try sema.resolveRef(item.data.init)).index;
    }

    const ctx = ip.stringSlice(sema.type_name_ctx);
    const name_text = try std.fmt.allocPrint(sema.gpa, "{s}__struct_{d}", .{ ctx, @intFromEnum(inst) });
    defer sema.gpa.free(name_text);
    const struct_ty = try ip.internStructType(.{
        .name = try ip.getOrPutString(sema.gpa, name_text),
        .id = .{ .declared = .{ .source_zir_id = sema.current_zir_id, .decl_inst = inst } },
        .parent = sema.this_type,
    });
    return .{ .index = try ip.internAggregate(.{ .ty = struct_ty, .storage = .{ .elems = values } }) };
}

/// `@import("path")`: resolve a module or file to its container type. Mirrors
/// the compiler's resolution (src/Zcu/PerThread.zig:doImport), which maps exactly
/// three names to distinct built-in modules -- `std`, `root`, `builtin` -- and
/// treats every other string as a module dependency or a relative `.zig`/`.zon`
/// file. `std` loads its root file; `root` and `builtin` are not backed yet. A
/// relative `.zig` path resolves against the importing file's directory; a bare
/// unknown name gets the compiler's "no module named" wording (`ModuleNotFound`).
fn evalImport(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const inst_data = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_tok;
    const extra = sema.zir.extraData(Zir.Inst.Import, inst_data.payload_index).data;
    return .{ .index = try sema.importPath(sema.zir.nullTerminatedString(extra.path)) };
}

/// Resolve an import string to its container type, the way `@import` does --
/// reused by builtins that reach into std (e.g. `getStdLangType`) so they go
/// through import semantics rather than a raw file load.
fn importPath(sema: *Sema, path: []const u8) Error!InternPool.Index {
    // `std` resolves to its root file; `builtin` is generated for the native target;
    // `root` (the compilation's own root file) has no REPL equivalent.
    if (std.mem.eql(u8, path, "std")) return sema.loadModuleFile("std.zig");
    if (std.mem.eql(u8, path, "root")) return sema.failUnloadedModule(path);
    if (std.mem.eql(u8, path, "builtin")) return sema.loadBuiltinModule("builtin");

    // Any other string is a relative file (a named module dependency would need
    // an import graph the REPL has no equivalent of). Resolve it against the
    // importing file, mirroring `Compilation.Path.upJoin`: join the importer's
    // sub-path, "..", and the import, then canonicalise -- the ".." cancels the
    // importer's own filename.
    if (std.mem.endsWith(u8, path, ".zig")) {
        const importer = sema.importerSubPath() orelse {
            try sema.writer.print("no module named '{s}' available\n", .{path});
            return error.AnalysisFail;
        };
        // Anchor at "/" so the join is absolute for canonicalisation; the leading
        // slash is stripped to yield a path relative to the source root.
        const anchored = try std.fs.path.resolvePosix(sema.gpa, &.{ "/", importer, "..", path });
        defer sema.gpa.free(anchored);
        return sema.loadModuleFile(anchored[1..]);
    }

    try sema.writer.print("no module named '{s}' available\n", .{path});
    return error.AnalysisFail;
}

fn failUnloadedModule(sema: *Sema, path: []const u8) Error {
    try sema.writer.print("@import(\"{s}\"): module loading is not supported\n", .{path});
    return error.AnalysisFail;
}

/// The sub-path (relative to the source root) of the file being analysed, or
/// null when the current file is a REPL line -- a line has no path to resolve a
/// relative import against.
fn importerSubPath(sema: *Sema) ?[]const u8 {
    const session = sema.session orelse return null;
    if (sema.current_zir_id >= session.files.items.len) return null;
    return session.files.items[sema.current_zir_id].sub_file_path;
}

/// Return the file-root container type of the module at canonical path
/// `canonical` (relative to the source root), reading and lowering its source on
/// first use. The file-root struct (`main_struct_inst`) becomes a `struct_type`
/// whose `source_zir_id` is the new file's `File.Index`, so its decls -- and its
/// own relative imports -- resolve lazily through `enterSourceZir`/
/// `importerSubPath`, exactly like a declared container. Mirrors the compiler's
/// `import_table` dedup plus `fileRootType`.
fn loadModuleFile(sema: *Sema, canonical: []const u8) Error!InternPool.Index {
    const session = sema.session orelse return sema.failUnloadedModule(canonical);
    if (session.import_table.get(canonical)) |idx| return session.files.items[idx].root_type;
    const source = session.module_source orelse return sema.failUnloadedModule(canonical);

    const bytes = source.read(sema.gpa, canonical) catch |err| {
        try sema.writer.print("@import(\"{s}\"): {s}\n", .{ canonical, @errorName(err) });
        return error.AnalysisFail;
    };
    defer sema.gpa.free(bytes);
    return sema.lowerModule(canonical, bytes);
}

/// Lower a module's source `bytes` (from a provider file or generated in-process,
/// like `builtin`) into its file-root container type, appending the file and
/// recording it in the `import_table`. Callers dedup via `import_table` first. The
/// file-root struct's identity mirrors `loadModuleFile` (a declared container keyed
/// on the new `File.Index`), so its decls and relative imports resolve lazily.
fn lowerModule(sema: *Sema, canonical: []const u8, bytes: [:0]const u8) Error!InternPool.Index {
    const session = sema.session.?;
    // The Ast references `bytes` and AstGen reads the Ast, so both live only
    // through lowering; the resulting Zir is what the session retains.
    var tree = try std.zig.Ast.parse(sema.gpa, bytes, .zig);
    defer tree.deinit(sema.gpa);
    var zir = try std.zig.AstGen.generate(sema.gpa, tree);
    if (zir.hasCompileErrors()) {
        zir.deinit(sema.gpa);
        try sema.writer.print("@import(\"{s}\"): source did not compile\n", .{canonical});
        return error.AnalysisFail;
    }

    // Append the file. Its `sub_file_path` is the owned canonical path and is
    // reused as the `import_table` key (no second allocation), so the whole
    // entry frees together in Session.deinit.
    const sub_path = sema.gpa.dupe(u8, canonical) catch |err| {
        zir.deinit(sema.gpa);
        return err;
    };
    session.files.append(sema.gpa, .{ .zir = zir, .sub_file_path = sub_path }) catch |err| {
        zir.deinit(sema.gpa);
        sema.gpa.free(sub_path);
        return err;
    };
    const file_index: Session.Index = @intCast(session.files.items.len - 1);
    try session.import_table.put(sema.gpa, sub_path, file_index);

    const root_type = try sema.intern_pool.internStructType(.{
        .name = try sema.moduleTypeName(canonical),
        .id = .{ .declared = .{ .source_zir_id = file_index, .decl_inst = .main_struct_inst } },
        .parent = .none,
    });
    session.files.items[file_index].root_type = root_type;
    return root_type;
}

/// The `builtin` module, generated for the native target. The compiler emits it
/// per compilation (`src/Builtin.zig`); the REPL evaluates native code, so
/// `sema/Builtin.zig` serializes the REPL's own `@import("builtin").target` into
/// the same expanded-literal shape -- enough for the target-dependent decls the
/// REPL reaches (calling conventions: `CallingConvention.c` is
/// `builtin.target.cCallingConvention()`).
fn loadBuiltinModule(sema: *Sema, canonical: []const u8) Error!InternPool.Index {
    const session = sema.session orelse return sema.failUnloadedModule(canonical);
    if (session.import_table.get(canonical)) |idx| return session.files.items[idx].root_type;
    if (session.module_source == null) return sema.failUnloadedModule(canonical);

    const bytes = try @import("Builtin.zig").generate(sema.gpa);
    defer sema.gpa.free(bytes);
    return sema.lowerModule(canonical, bytes);
}

/// Resolve a type declared in `std.lang` (a dotted `path` like "Type" or
/// "Type.Int"), reached as `@import("std").lang` then walked by name. Mirrors the
/// compiler's `getStdLangType` (which navigates the analyzed program's std
/// namespace). Requires a frontend-injected module source.
/// The compiler's `Zcu.StdLangDecl`: each tag *is* a `std.lang` access path
/// (`@"Type.Pointer.Size"` -> `std.lang.Type.Pointer.Size`), and its `access`
/// derives that path by splitting `@tagName` on the last `.`. Two deviations from
/// the compiler's enum: we carry only the type-kind decls (the func/string/panic
/// entries drive `getStdLangValue`, which the missing runtime/panic layer never
/// reaches), and `getStdLangType` re-walks the path per call rather than reading a
/// memoized `EnumArray` (we have no persistent `Zcu` to memoize into). Parents
/// still precede children, as `access` requires.
const StdLangDecl = enum {
    Signedness,
    AddressSpace,
    CallingConvention,
    CallModifier,
    AtomicOrder,
    AtomicRmwOp,
    ReduceOp,
    FloatMode,
    PrefetchOptions,
    ExportOptions,
    ExternOptions,
    BranchHint,
    Type,
    @"Type.Fn",
    @"Type.Fn.ParamAttributes",
    @"Type.Fn.Attributes",
    @"Type.Int",
    @"Type.Float",
    @"Type.Pointer",
    @"Type.Pointer.Size",
    @"Type.Pointer.Attributes",
    @"Type.Array",
    @"Type.Vector",
    @"Type.Optional",
    @"Type.ErrorUnion",
    @"Type.ErrorSet",
    @"Type.Enum",
    @"Type.Enum.Mode",
    @"Type.Union",
    @"Type.Union.FieldAttributes",
    @"Type.Struct",
    @"Type.Struct.FieldAttributes",
    @"Type.ContainerLayout",
    @"Type.Spirv",
    @"assembly.Clobbers",
};

fn getStdLangType(sema: *Sema, decl: StdLangDecl) Error!InternPool.Index {
    var container = try sema.resolveDeclType(try sema.importPath("std"), "lang");
    var it = std.mem.tokenizeScalar(u8, @tagName(decl), '.');
    while (it.next()) |seg| container = try sema.resolveDeclType(container, seg);
    return container;
}

fn resolveDeclType(sema: *Sema, container_ty: InternPool.Index, name: []const u8) Error!InternPool.Index {
    const name_nts = try sema.intern_pool.getOrPutString(sema.gpa, name);
    const v = (try sema.containerDeclByName(container_ty, name_nts)) orelse {
        try sema.writer.print("std.lang: missing declaration '{s}'\n", .{name});
        return error.AnalysisFail;
    };
    return v.index;
}

/// Resolve `ref` to a value of the named `std.lang` enum and return it as the
/// native enum `E` -- the inverse of the `@typeInfo` arms' enum construction, and
/// what the reification builtins read their categorical arguments through. Coerce
/// to the enum type, read the active field's name, map it to `E`. Mirrors the
/// compiler's `resolveStdLangEnum`; `std.meta.stringToEnum` stands in for its
/// native tag lookup.
fn resolveStdLangEnum(sema: *Sema, comptime decl: StdLangDecl, ref: Zir.Inst.Ref) Error!@field(std.lang, @tagName(decl)) {
    const E = @field(std.lang, @tagName(decl));
    const enum_ty = try sema.getStdLangType(decl);
    const val = try sema.coerceValueToType(try sema.resolveRef(ref), enum_ty, @tagName(decl));
    return sema.interpretStdLangEnum(E, enum_ty, val, @tagName(decl));
}

/// Read an already-resolved `std.lang` enum `val` (of type `enum_ty`) as the
/// native enum `E` -- the enum case of the compiler's `Value.interpret`: read the
/// active tag's name and map it. `ctx` names the argument for diagnostics.
fn interpretStdLangEnum(sema: *Sema, comptime E: type, enum_ty: InternPool.Index, val: Value, ctx: []const u8) Error!E {
    const idx = (try sema.enumTagFieldIndex(enum_ty, val)).?;
    const name = sema.intern_pool.stringSlice((try sema.enumFieldName(enum_ty, idx)).?);
    return std.meta.stringToEnum(E, name) orelse {
        try sema.writer.print("{s}: unknown variant '{s}'\n", .{ ctx, name });
        return error.AnalysisFail;
    };
}

/// `std_lang_value` (extended): the `std.lang` type a builtin coerces a
/// categorical argument against -- e.g. `@Int(.unsigned, _)` resolves `.unsigned`
/// against the `Signedness` this yields. `small` selects which. Mirrors
/// zirStdLangValue: most variants return the type via `getStdLangType`; the two
/// calling-convention *values* resolve directly (`.c` is a target-dependent
/// declaration, `.@"inline"` a payload-free tag).
fn evalStdLangValue(sema: *Sema, extended: Zir.Inst.Extended.InstData) Error!?Value {
    const value: Zir.Inst.StdLangValue = @enumFromInt(extended.small);
    const std_lang_type: StdLangDecl = switch (value) {
        .atomic_order => .AtomicOrder,
        .atomic_rmw_op => .AtomicRmwOp,
        .calling_convention => .CallingConvention,
        .address_space => .AddressSpace,
        .float_mode => .FloatMode,
        .signedness => .Signedness,
        .reduce_op => .ReduceOp,
        .call_modifier => .CallModifier,
        .prefetch_options => .PrefetchOptions,
        .export_options => .ExportOptions,
        .extern_options => .ExternOptions,
        .branch_hint => .BranchHint,
        .clobbers => .@"assembly.Clobbers",
        .pointer_size => .@"Type.Pointer.Size",
        .pointer_attributes => .@"Type.Pointer.Attributes",
        .fn_attributes => .@"Type.Fn.Attributes",
        .container_layout => .@"Type.ContainerLayout",
        .enum_mode => .@"Type.Enum.Mode",
        .spirv_type_options => .@"Type.Spirv",

        // Values are handled here: `.c` is a target-dependent declaration,
        // `.@"inline"` a payload-free tag -- resolved directly, not as types.
        .calling_convention_c => {
            const cc_ty = try sema.getStdLangType(.CallingConvention);
            const name = try sema.intern_pool.getOrPutString(sema.gpa, "c");
            return (try sema.containerDeclByName(cc_ty, name)) orelse {
                try sema.writer.print("std.lang is corrupt: CallingConvention.c\n", .{});
                return error.AnalysisFail;
            };
        },
        .calling_convention_inline => return .{ .index = try sema.callConvValue(.@"inline") },
    };
    return .{ .index = try sema.getStdLangType(std_lang_type) };
}

/// `@typeInfo(T)`: build the `std.lang.Type` union value describing `T`. Mirrors
/// zirTypeInfo -- resolve `std.lang.Type`, then produce a union whose active tag
/// is the type category and whose payload is the matching info struct. Requires
/// `std` to be loadable (the result type lives there).
fn evalTypeInfo(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    const ty = (try sema.resolveRef(un_node.operand)).index;

    const type_info_ty = try sema.getStdLangType(.Type);
    const tag_enum = try sema.unionTagEnumType(type_info_ty);

    if (Type.fromIndex(ty).zigTypeTag(ip) == .int) {
        const it = Type.fromIndex(ty).intInfo(ip).?;
        const int_info_ty = try sema.getStdLangType(.@"Type.Int");
        const signedness_ty = try sema.getStdLangType(.Signedness);
        const sign_idx = (try sema.enumFieldIndex(signedness_ty, try ip.getOrPutString(sema.gpa, @tagName(it.signedness)))).?;
        const sign_val = (try sema.enumValueFieldIndex(signedness_ty, sign_idx)).?;
        const bits_val = try ip.internInt(.{ .ty = .u16_type, .storage = .{ .u64 = it.bits } });
        var elems = [_]InternPool.Index{ sign_val.index, bits_val };
        const payload = try ip.internAggregate(.{ .ty = int_info_ty, .storage = .{ .elems = &elems } });
        return try sema.typeInfoUnion(type_info_ty, tag_enum, "int", payload);
    }

    switch (ip.indexToKey(ty)) {
        .simple_type => |s| switch (s) {
            // `Type.Float{ bits }`, like the int arm but a single field.
            .f16, .f32, .f64, .f80, .f128 => {
                const bits: u16 = switch (s) {
                    .f16 => 16,
                    .f32 => 32,
                    .f64 => 64,
                    .f80 => 80,
                    .f128 => 128,
                    else => unreachable,
                };
                const float_info_ty = try sema.getStdLangType(.@"Type.Float");
                var elems = [_]InternPool.Index{try ip.internInt(.{ .ty = .u16_type, .storage = .{ .u64 = bits } })};
                const payload = try ip.internAggregate(.{ .ty = float_info_ty, .storage = .{ .elems = &elems } });
                return try sema.typeInfoUnion(type_info_ty, tag_enum, "float", payload);
            },
            // Payload-free categories: the tag name is the simple type's name and
            // the union payload is `void`. Mirrors zirTypeInfo's trivial arm.
            .void, .bool, .type, .noreturn, .comptime_int, .comptime_float, .undefined, .null, .enum_literal => {
                return try sema.typeInfoUnion(type_info_ty, tag_enum, @tagName(s), .void_value);
            },
            // `anyerror` is the open error set: `error_names` is null.
            .anyerror => return try sema.typeInfoErrorSet(null),
            else => return sema.failTypeInfoUnsupported(ty),
        },
        // `Type.Optional{ child: type }`.
        .opt_type => |child| {
            const opt_ty = try sema.getStdLangType(.@"Type.Optional");
            var elems = [_]InternPool.Index{child};
            return try sema.typeInfoUnion(type_info_ty, tag_enum, "optional", try ip.internAggregate(.{ .ty = opt_ty, .storage = .{ .elems = &elems } }));
        },
        // `Type.Vector{ len: comptime_int, child: type }`.
        .vector_type => |vec| {
            const vec_ty = try sema.getStdLangType(.@"Type.Vector");
            var elems = [_]InternPool.Index{
                try ip.internInt(.{ .ty = .comptime_int_type, .storage = .{ .u64 = vec.len } }),
                vec.child,
            };
            return try sema.typeInfoUnion(type_info_ty, tag_enum, "vector", try ip.internAggregate(.{ .ty = vec_ty, .storage = .{ .elems = &elems } }));
        },
        // `Type.Array{ len: comptime_int, child: type, sentinel: ?*const anyopaque }`.
        .array_type => |arr| {
            const array_ty = try sema.getStdLangType(.@"Type.Array");
            var elems = [_]InternPool.Index{
                try ip.internInt(.{ .ty = .comptime_int_type, .storage = .{ .u64 = arr.len } }),
                arr.child,
                try sema.optRefValue(arr.sentinel),
            };
            return try sema.typeInfoUnion(type_info_ty, tag_enum, "array", try ip.internAggregate(.{ .ty = array_ty, .storage = .{ .elems = &elems } }));
        },
        // `Type.Pointer{ size, attrs, child, sentinel_ptr }`, `attrs` being
        // `Attributes{ const, volatile, allowzero, addrspace: ?AddressSpace, align: ?usize }`.
        .ptr_type => |p| {
            const pointer_ty = try sema.getStdLangType(.@"Type.Pointer");
            const size_ty = try sema.getStdLangType(.@"Type.Pointer.Size");
            const attrs_ty = try sema.getStdLangType(.@"Type.Pointer.Attributes");
            const addrspace_ty = try sema.getStdLangType(.AddressSpace);

            const opt_addrspace = try ip.internOpt(.{
                .ty = try ip.internOptionalType(addrspace_ty),
                .val = (try sema.enumValueFieldIndex(addrspace_ty, @intFromEnum(p.flags.address_space))).?.index,
            });
            const opt_align = try ip.internOpt(.{
                .ty = try ip.internOptionalType(.usize_type),
                .val = if (p.flags.alignment.toByteUnits()) |bytes|
                    try ip.internInt(.{ .ty = .usize_type, .storage = .{ .u64 = bytes } })
                else
                    .none,
            });
            var attr_elems = [_]InternPool.Index{
                if (p.flags.is_const) .bool_true else .bool_false,
                if (p.flags.is_volatile) .bool_true else .bool_false,
                if (p.flags.is_allowzero) .bool_true else .bool_false,
                opt_addrspace,
                opt_align,
            };
            var elems = [_]InternPool.Index{
                (try sema.enumValueFieldIndex(size_ty, @intFromEnum(p.flags.size))).?.index,
                try ip.internAggregate(.{ .ty = attrs_ty, .storage = .{ .elems = &attr_elems } }),
                p.child,
                try sema.optRefValue(p.sentinel),
            };
            return try sema.typeInfoUnion(type_info_ty, tag_enum, "pointer", try ip.internAggregate(.{ .ty = pointer_ty, .storage = .{ .elems = &elems } }));
        },
        // `Type.ErrorUnion{ error_set: type, payload: type }`.
        .error_union_type => |eu| {
            const eu_ty = try sema.getStdLangType(.@"Type.ErrorUnion");
            var elems = [_]InternPool.Index{ eu.error_set_type, eu.payload_type };
            return try sema.typeInfoUnion(type_info_ty, tag_enum, "error_union", try ip.internAggregate(.{ .ty = eu_ty, .storage = .{ .elems = &elems } }));
        },
        // `Type.ErrorSet{ error_names: ?[]const [:0]const u8 }` -- a named set.
        .error_set_type => return try sema.typeInfoErrorSet(ty),
        // `Type.Enum{ tag_type, mode, field_names, field_values, decl_names }`.
        .enum_type => {
            const enum_std_ty = try sema.getStdLangType(.@"Type.Enum");
            const mode_ty = try sema.getStdLangType(.@"Type.Enum.Mode");

            // Read the field names and values through the field accessors (which
            // walk declared and generated-union-tag enums alike); a value is the
            // tag's integer re-typed to `comptime_int`.
            const count = try sema.enumFieldCount(ty);
            const names = try sema.gpa.alloc(InternPool.NullTerminatedString, count);
            defer sema.gpa.free(names);
            const values = try sema.gpa.alloc(InternPool.Index, count);
            defer sema.gpa.free(values);
            for (names, values, 0..) |*name, *value, i| {
                name.* = (try sema.enumFieldName(ty, @intCast(i))).?;
                const tag = (try sema.enumValueFieldIndex(ty, @intCast(i))).?;
                const tag_int = ip.indexToKey(tag.index).enum_tag.int;
                value.* = try ip.internInt(.{ .ty = .comptime_int_type, .storage = .{ .i64 = @intCast(sema.intAsI128(tag_int).?) } });
            }
            const field_names_val = try sema.internStringSlice(names);
            const field_values_val = try sema.internConstSlice(.comptime_int_type, values);
            const decl_names_val = try sema.typeInfoDecls(ty);

            const mode_name = if (try sema.enumNonexhaustive(ty)) "nonexhaustive" else "exhaustive";
            const mode_idx = (try sema.enumFieldIndex(mode_ty, try ip.getOrPutString(sema.gpa, mode_name))).?;
            const mode_val = (try sema.enumValueFieldIndex(mode_ty, mode_idx)).?;

            var elems = [_]InternPool.Index{ try sema.enumIntTagTypeOf(ty), mode_val.index, field_names_val, field_values_val, decl_names_val };
            return try sema.typeInfoUnion(type_info_ty, tag_enum, "enum", try ip.internAggregate(.{ .ty = enum_std_ty, .storage = .{ .elems = &elems } }));
        },
        // `Type.Union{ layout, tag_type: ?type, backing_integer: ?type,
        // field_names, field_types, field_attrs, decl_names }`.
        .union_type => {
            const union_std_ty = try sema.getStdLangType(.@"Type.Union");
            const attrs_ty = try sema.getStdLangType(.@"Type.Union.FieldAttributes");
            const layout_ty = try sema.getStdLangType(.@"Type.ContainerLayout");

            // Names by position, type and explicit alignment by name -- composing the
            // existing field accessors, as the enum arm composes its own.
            const count = try sema.unionFieldCount(ty);
            const names = try sema.gpa.alloc(InternPool.NullTerminatedString, count);
            defer sema.gpa.free(names);
            const types = try sema.gpa.alloc(InternPool.Index, count);
            defer sema.gpa.free(types);
            const attrs = try sema.gpa.alloc(InternPool.Index, count);
            defer sema.gpa.free(attrs);
            for (names, types, attrs, 0..) |*name, *field_ty, *attr, i| {
                name.* = (try sema.unionFieldNameAt(ty, @intCast(i))).?;
                const f = (try sema.unionFieldByName(ty, name.*)).?;
                field_ty.* = f.ty;
                var attr_elems = [_]InternPool.Index{try sema.alignOptValue(f.align_bytes)};
                attr.* = try ip.internAggregate(.{ .ty = attrs_ty, .storage = .{ .elems = &attr_elems } });
            }
            const field_names_val = try sema.internStringSlice(names);
            const field_types_val = try sema.internConstSlice(.type_type, types);
            const field_attrs_val = try sema.internConstSlice(attrs_ty, attrs);
            const decl_names_val = try sema.typeInfoDecls(ty);

            // A reified union stores its layout and (for a packed union) its backing
            // integer; a declared one has neither modelled, so it reports `.auto` and
            // a null backing integer. The inferred backing of a packed union with no
            // explicit backing needs layout resolution, which is not modelled.
            const uf = ip.unionFields(ty);
            const layout = if (uf) |f| f.layout else .auto;
            const layout_val = (try sema.enumValueFieldIndex(layout_ty, @intFromEnum(layout))).?;
            const tag_type_val = try sema.optTypeValue(if (try sema.unionIsTagged(ty)) try sema.unionTagEnumType(ty) else .none);
            const backing_integer_val = try sema.optTypeValue(if (uf) |f| f.backing_int else .none);

            var elems = [_]InternPool.Index{ layout_val.index, tag_type_val, backing_integer_val, field_names_val, field_types_val, field_attrs_val, decl_names_val };
            return try sema.typeInfoUnion(type_info_ty, tag_enum, "union", try ip.internAggregate(.{ .ty = union_std_ty, .storage = .{ .elems = &elems } }));
        },
        // `Type.Struct{ is_tuple, layout, backing_integer: ?type, field_names,
        // field_types, field_attrs, decl_names }`. A `.struct_type` is never a
        // tuple (tuples are the `.tuple_type` Key), so `is_tuple` is false.
        // A tuple reflects as a `Type.Struct` too (`is_tuple = true`), as the
        // compiler's `.@"struct"` arm folds `tuple_type` in: positional field
        // names, its element types, and no declarations.
        .struct_type, .tuple_type => {
            const struct_std_ty = try sema.getStdLangType(.@"Type.Struct");
            const attrs_ty = try sema.getStdLangType(.@"Type.Struct.FieldAttributes");
            const layout_ty = try sema.getStdLangType(.@"Type.ContainerLayout");
            // A tuple's element-type list borrows `pool.extra`; interning in the
            // loop below can grow and reallocate it, so take a stable copy.
            const tuple_types: ?[]const InternPool.Index = switch (ip.indexToKey(ty)) {
                .tuple_type => |tt| try sema.gpa.dupe(InternPool.Index, tt.types),
                else => null,
            };
            defer if (tuple_types) |t| sema.gpa.free(t);

            // Struct fields resolve by position/name through the field accessors;
            // a tuple's come straight off its element-type list. The REPL's tuple
            // type carries no comptime field values, so every tuple field is
            // runtime (no default, not comptime).
            const count = if (tuple_types) |t| @as(u32, @intCast(t.len)) else try sema.structFieldCount(ty);
            const names = try sema.gpa.alloc(InternPool.NullTerminatedString, count);
            defer sema.gpa.free(names);
            const types = try sema.gpa.alloc(InternPool.Index, count);
            defer sema.gpa.free(types);
            const attrs = try sema.gpa.alloc(InternPool.Index, count);
            defer sema.gpa.free(attrs);
            for (names, types, attrs, 0..) |*name, *field_ty, *attr, i| {
                var is_comptime = false;
                var align_bytes: ?u64 = null;
                var default: InternPool.Index = .none;
                if (tuple_types) |t| {
                    var buf: [16]u8 = undefined;
                    name.* = try ip.getOrPutString(sema.gpa, std.fmt.bufPrint(&buf, "{d}", .{i}) catch unreachable);
                    field_ty.* = t[i];
                } else {
                    name.* = (try sema.structFieldNameAt(ty, @intCast(i))).?;
                    const f = (try sema.structFieldByName(ty, name.*)).?;
                    field_ty.* = f.ty;
                    is_comptime = f.is_comptime;
                    align_bytes = f.align_bytes;
                    default = try sema.structFieldDefault(ty, name.*);
                }
                var attr_elems = [_]InternPool.Index{
                    if (is_comptime) .bool_true else .bool_false,
                    try sema.alignOptValue(align_bytes),
                    try sema.optRefValue(default),
                };
                attr.* = try ip.internAggregate(.{ .ty = attrs_ty, .storage = .{ .elems = &attr_elems } });
            }
            const field_names_val = try sema.internStringSlice(names);
            const field_types_val = try sema.internConstSlice(.type_type, types);
            const field_attrs_val = try sema.internConstSlice(attrs_ty, attrs);
            const decl_names_val = if (tuple_types != null) try sema.internStringSlice(&.{}) else try sema.typeInfoDecls(ty);

            // A reified struct stores its layout and packed backing integer; a
            // declared struct (or a tuple) has none modelled, so it reports `.auto`
            // and a null backing integer.
            const sf: ?InternPool.StructFields = if (tuple_types == null) ip.structFields(ty) else null;
            const layout = if (sf) |f| f.layout else .auto;
            const layout_val = (try sema.enumValueFieldIndex(layout_ty, @intFromEnum(layout))).?;
            const backing_integer_val = try sema.optTypeValue(if (sf) |f| f.backing_int else .none);

            var elems = [_]InternPool.Index{ if (tuple_types != null) .bool_true else .bool_false, layout_val.index, backing_integer_val, field_names_val, field_types_val, field_attrs_val, decl_names_val };
            return try sema.typeInfoUnion(type_info_ty, tag_enum, "struct", try ip.internAggregate(.{ .ty = struct_std_ty, .storage = .{ .elems = &elems } }));
        },
        // `Type.Fn{ attrs: Attributes{ callconv, varargs }, is_generic,
        // return_type: ?type, param_types: []const ?type, param_attrs }`. A generic
        // parameter/return is `generic_poison_type`, exposed as a null element.
        .func_type => |ft| {
            // `ft.param_types` borrows `extra`; the interning below can grow and
            // reallocate it, so take a stable copy before touching the pool.
            const param_types = try sema.gpa.dupe(InternPool.Index, ft.param_types);
            defer sema.gpa.free(param_types);
            const fn_std_ty = try sema.getStdLangType(.@"Type.Fn");
            const param_attrs_ty = try sema.getStdLangType(.@"Type.Fn.ParamAttributes");
            const fn_attr_ty = try sema.getStdLangType(.@"Type.Fn.Attributes");
            const opt_type_child = try ip.internOptionalType(.type_type);

            var func_is_generic = ft.return_type == .generic_poison_type;
            const param_type_vals = try sema.gpa.alloc(InternPool.Index, param_types.len);
            defer sema.gpa.free(param_type_vals);
            const param_attr_vals = try sema.gpa.alloc(InternPool.Index, param_types.len);
            defer sema.gpa.free(param_attr_vals);
            for (param_type_vals, param_attr_vals, 0..) |*pt_val, *pa_val, i| {
                const param_ty = param_types[i];
                const is_generic = param_ty == .generic_poison_type;
                // Per-parameter flag masks cap at 32 params (the compiler's `u5`).
                const narrow = std.math.cast(u5, i);
                const is_comptime = if (narrow) |n| ft.paramIsComptime(n) else false;
                const is_noalias = if (narrow) |n| ft.paramIsNoalias(n) else false;
                if (is_generic or is_comptime) func_is_generic = true;
                pt_val.* = try sema.optTypeValue(if (is_generic) .none else param_ty);
                var pa_elems = [_]InternPool.Index{if (is_noalias) .bool_true else .bool_false};
                pa_val.* = try ip.internAggregate(.{ .ty = param_attrs_ty, .storage = .{ .elems = &pa_elems } });
            }
            const param_types_val = try sema.internConstSlice(opt_type_child, param_type_vals);
            const param_attrs_val = try sema.internConstSlice(param_attrs_ty, param_attr_vals);
            const return_type_val = try sema.optTypeValue(if (ft.return_type == .generic_poison_type) .none else ft.return_type);

            var attr_elems = [_]InternPool.Index{
                try sema.callConvValue(ft.cc),
                if (ft.is_var_args) .bool_true else .bool_false,
            };
            const attrs_val = try ip.internAggregate(.{ .ty = fn_attr_ty, .storage = .{ .elems = &attr_elems } });

            var elems = [_]InternPool.Index{ attrs_val, if (func_is_generic) .bool_true else .bool_false, return_type_val, param_types_val, param_attrs_val };
            return try sema.typeInfoUnion(type_info_ty, tag_enum, "fn", try ip.internAggregate(.{ .ty = fn_std_ty, .storage = .{ .elems = &elems } }));
        },
        else => return sema.failTypeInfoUnsupported(ty),
    }
}

/// A pointer of type `ptr_ty` addressing the anonymous constant `val` -- the
/// compiler's `uav` base. The pointee is carried inline, so the pointer is self-
/// contained. Shared by every const-pointer-to-a-value construction.
fn uavPtr(sema: *Sema, ptr_ty: InternPool.Index, val: InternPool.Index) Error!InternPool.Index {
    return try sema.intern_pool.internPtr(.{
        .ty = ptr_ty,
        .base_addr = .{ .uav = .{ .val = val, .orig_ty = ptr_ty } },
        .byte_offset = 0,
    });
}

/// Build a `?*const anyopaque` value pointing at `val` (a sentinel), or null when
/// `val` is `.none`. Mirrors the compiler's `optRefValue`: `@typeInfo`'s array
/// and pointer sentinels are exposed as an opaque const pointer to the value.
fn optRefValue(sema: *Sema, val: InternPool.Index) Error!InternPool.Index {
    const ip = sema.intern_pool;
    const ptr_ty = try ip.internPtrType(.{ .child = .anyopaque_type, .flags = .{ .size = .one, .is_const = true } });
    const opt_ty = try ip.internOptionalType(ptr_ty);
    const payload: InternPool.Index = if (val == .none) .none else try sema.uavPtr(ptr_ty, val);
    return try ip.internOpt(.{ .ty = opt_ty, .val = payload });
}

/// Build a `[]const child` slice value from `elems`: an array behind a `uav`
/// many-pointer, all const. The homogeneous-list shape `@typeInfo` uses for its
/// name/value/type slices. Mirrors zirTypeInfo's repeated inline `v:` blocks.
fn internConstSlice(sema: *Sema, child: InternPool.Index, elems: []const InternPool.Index) Error!InternPool.Index {
    const ip = sema.intern_pool;
    const array_ty = try ip.internArrayType(.{ .len = elems.len, .child = child });
    const array_val = try ip.internAggregate(.{ .ty = array_ty, .storage = .{ .elems = elems } });
    const slice_ty = try ip.internPtrType(.{ .child = child, .flags = .{ .size = .slice, .is_const = true } });
    const manyptr_ty = try ip.internPtrType(.{ .child = child, .flags = .{ .size = .many, .is_const = true } });
    const ptr = try sema.uavPtr(manyptr_ty, array_val);
    return try ip.get(.{ .slice = .{ .ty = slice_ty, .ptr = ptr, .len = try ip.internInt(.{ .ty = .usize_type, .storage = .{ .u64 = elems.len } }) } });
}

/// The interned `[:0]const u8` type -- the element of `@typeInfo`'s name lists.
fn sliceConstU8SentinelTy(sema: *Sema) Error!InternPool.Index {
    const ip = sema.intern_pool;
    const u8_zero = try ip.internInt(.{ .ty = .u8_type, .storage = .{ .u64 = 0 } });
    return try ip.internPtrType(.{ .child = .u8_type, .sentinel = u8_zero, .flags = .{ .size = .slice, .is_const = true } });
}

/// `[]const type` -- the type a reification builtin coerces its type-list argument
/// to. The compiler reserves this as a well-known InternPool index; the REPL
/// interns it on demand, as it does the other slice types.
fn sliceConstTypeTy(sema: *Sema) Error!InternPool.Index {
    return try sema.intern_pool.internPtrType(.{ .child = .type_type, .flags = .{ .size = .slice, .is_const = true } });
}

/// Build a `[]const [:0]const u8` slice value from interned name handles (each a
/// `[:0]const u8` slice over an interned `[N:0]u8`). `names` must be stable across
/// interning -- callers reading from the `extra` arena (error sets) re-derive
/// per element instead of passing a view here.
fn internStringSlice(sema: *Sema, names: []const InternPool.NullTerminatedString) Error!InternPool.Index {
    const ip = sema.intern_pool;
    const slice_u8_ty = try sema.sliceConstU8SentinelTy();
    const vals = try sema.gpa.alloc(InternPool.Index, names.len);
    defer sema.gpa.free(vals);
    for (vals, names) |*v, name| {
        const str_val = try sema.internStringLiteral(ip.stringSlice(name));
        v.* = (try sema.coerceToSlice(str_val, slice_u8_ty)).?.index;
    }
    return try sema.internConstSlice(slice_u8_ty, vals);
}

/// The `decl_names: []const [:0]const u8` list of a container's public
/// declarations, in source order. Mirrors `typeInfoDecls` -> `typeInfoNamespaceDecls`:
/// the compiler reads a populated `namespace.pub_decls`; this evaluator scans the
/// container's decl ZIR (as `containerDeclByName` does), keeping the public,
/// named ones (a `comptime`/test block has an empty name).
fn typeInfoDecls(sema: *Sema, container_ty: InternPool.Index) Error!InternPool.Index {
    const ip = sema.intern_pool;
    const ns = sema.containerNamespace(container_ty) orelse return try sema.internStringSlice(&.{});
    var names: std.ArrayListUnmanaged(InternPool.NullTerminatedString) = .empty;
    defer names.deinit(sema.gpa);
    {
        const frame = try sema.enterSourceZir(ns.source_zir_id, "type info decls");
        defer frame.restore(sema);
        for (sema.zir.typeDecls(ns.decl_inst)) |decl_inst| {
            const unwrapped = sema.zir.getDeclaration(decl_inst);
            if (unwrapped.name == .empty or !unwrapped.is_pub) continue;
            try names.append(sema.gpa, try ip.getOrPutString(sema.gpa, sema.zir.nullTerminatedString(unwrapped.name)));
        }
    }
    return try sema.internStringSlice(names.items);
}

/// Build the `.error_set` arm of `std.lang.Type`: a `Type.ErrorSet{ error_names:
/// ?[]const [:0]const u8 }`. `err_ty` is null for `anyerror` (the open error set,
/// so `error_names` is null) and the `error_set_type` index otherwise -- its
/// members, ordered, become the names (empty for `error{}`). Mirrors zirTypeInfo's
/// `.error_set` arm: each name becomes a `[:0]const u8` slice pointing at an
/// interned `[N:0]u8`, collected into a `[]const [:0]const u8` held behind an
/// optional. The compiler's `resolveInferredErrorSetTy` split is a runtime
/// concern; a comptime evaluator has the resolved set in hand.
fn typeInfoErrorSet(sema: *Sema, err_ty: ?InternPool.Index) Error!?Value {
    const ip = sema.intern_pool;
    const type_info_ty = try sema.getStdLangType(.Type);
    const tag_enum = try sema.unionTagEnumType(type_info_ty);
    const error_set_ty = try sema.getStdLangType(.@"Type.ErrorSet");

    const slice_u8_ty = try sema.sliceConstU8SentinelTy();
    const slice_errors_ty = try ip.internPtrType(.{ .child = slice_u8_ty, .flags = .{ .size = .slice, .is_const = true } });
    const opt_slice_errors_ty = try ip.internOptionalType(slice_errors_ty);

    // `err_ty` is null for `anyerror` (the open set), else the `error_set_type`
    // whose members are the names. `error_set_type.names` views the `extra` arena
    // that each interning below reallocates, so it is re-derived per element --
    // mirroring the compiler's `names.get(ip)[i]`.
    const errors_payload: InternPool.Index = if (err_ty) |t| payload: {
        const count = ip.indexToKey(t).error_set_type.names.len;
        const vals = try sema.gpa.alloc(InternPool.Index, count);
        defer sema.gpa.free(vals);
        for (vals, 0..) |*v, i| {
            const name = ip.indexToKey(t).error_set_type.names[i];
            const str_val = try sema.internStringLiteral(ip.stringSlice(name));
            v.* = (try sema.coerceToSlice(str_val, slice_u8_ty)).?.index;
        }
        break :payload try sema.internConstSlice(slice_u8_ty, vals);
    } else .none;

    const errors_val = try ip.internOpt(.{ .ty = opt_slice_errors_ty, .val = errors_payload });
    var elems = [_]InternPool.Index{errors_val};
    return try sema.typeInfoUnion(type_info_ty, tag_enum, "error_set", try ip.internAggregate(.{ .ty = error_set_ty, .storage = .{ .elems = &elems } }));
}

fn failTypeInfoUnsupported(sema: *Sema, ty: InternPool.Index) Error {
    sema.writer.writeAll("@typeInfo: unsupported type '") catch |e| return e;
    Type.print(.fromIndex(ty), sema.intern_pool, sema.writer) catch |e| return e;
    sema.writer.writeAll("'\n") catch |e| return e;
    return error.AnalysisFail;
}

/// Assemble a `std.lang.Type` union value: the field named `tag_name` active,
/// with `payload`. Mirrors zirTypeInfo's `internUnion` tail.
fn typeInfoUnion(sema: *Sema, type_info_ty: InternPool.Index, tag_enum: InternPool.Index, tag_name: []const u8, payload: InternPool.Index) Error!?Value {
    const tag_idx = (try sema.enumFieldIndex(tag_enum, try sema.intern_pool.getOrPutString(sema.gpa, tag_name))).?;
    const tag = (try sema.enumValueFieldIndex(tag_enum, tag_idx)).?;
    return .{ .index = try sema.intern_pool.internUnion(.{ .ty = type_info_ty, .tag = tag.index, .val = payload }) };
}

/// Render the file-root type name into `writer`: the sub-path with its extension
/// stripped and path separators turned into dots (`lang/assembly.zig` ->
/// `lang.assembly`, `std.zig` -> `std`). Mirrors `Zcu.File.renderFullyQualifiedName`.
fn renderModuleName(sub_path: []const u8, writer: *std.Io.Writer) std.Io.Writer.Error!void {
    const ext = std.fs.path.extension(sub_path);
    const noext = sub_path[0 .. sub_path.len - ext.len];
    for (noext) |byte| switch (byte) {
        '/', '\\' => try writer.writeByte('.'),
        else => try writer.writeByte(byte),
    };
}

/// Intern the file-root type name, mirroring `Zcu.File.internFullyQualifiedName`:
/// pre-size the buffer to the stripped length (`fullyQualifiedNameLen`), render
/// into it, then intern. The bytes must be assembled before interning because
/// the string pool is content-addressed.
fn moduleTypeName(sema: *Sema, sub_path: []const u8) Error!InternPool.NullTerminatedString {
    const ext = std.fs.path.extension(sub_path);
    const buf = try sema.gpa.alloc(u8, sub_path.len - ext.len);
    defer sema.gpa.free(buf);
    var writer: std.Io.Writer = .fixed(buf);
    renderModuleName(sub_path, &writer) catch unreachable; // buffer is exactly sized
    return sema.intern_pool.getOrPutString(sema.gpa, writer.buffered());
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
    // A sentinel-terminated array stores the sentinel as its final element:
    // `elems.len == lenIncludingSentinel` and `elems[len] == sentinel`.
    const sentinel: InternPool.Index = switch (array_key) {
        .array_type => |at| at.sentinel,
        else => .none,
    };
    const buf = try sema.gpa.alloc(InternPool.Index, elems.len + @intFromBool(sentinel != .none));
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
    if (sentinel != .none) buf[elems.len] = sentinel;

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

/// `elem_type`: the pointee type of a pointer type -- the result-location type
/// for a value stored through an element pointer (`e.* = @intCast(i)` in a
/// by-ref `for` capture). Mirrors zirElemType: peel any optional/error-union
/// wrapper, then take the pointer's child. Compiler reference:
/// src/Sema.zig:zirElemType (~7411).
fn evalElemType(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);
    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    const ptr_ty = sema.optEuBaseType(try sema.resolveDestType(un_node.operand, "elem_type"));
    return .{ .index = sema.intern_pool.indexToKey(ptr_ty).ptr_type.child };
}

/// `splat_op_result_ty` (`@splat`'s operand type): the element type of the
/// array/vector result location, used to type the scalar being broadcast.
/// Mirrors zirSplatOpResultType. Compiler reference: src/Sema.zig (~7441).
fn evalSplatOpResultType(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);
    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    const ty = sema.optEuBaseType(try sema.resolveDestType(un_node.operand, "@splat"));
    return .{ .index = (try sema.expectArrayOrVector(ty)).child };
}

/// `splat` (`@splat(x)`): broadcast a scalar to every lane of the array/vector
/// result type. Coerce the scalar to the element type and intern an aggregate
/// with `repeated_elem` storage (a sentinel array keeps its terminator). Mirrors
/// zirSplat -> the `splat` / `aggregateSplatValue` comptime path.
fn evalSplat(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    const bin = sema.binData(inst);
    const dest_ty = sema.optEuBaseType(try sema.resolveDestType(bin.lhs, "@splat"));
    const info = try sema.expectArrayOrVector(dest_ty);
    const scalar = try sema.coerceValueToType(try sema.resolveRef(bin.rhs), info.child, "@splat");

    const dest_key = ip.indexToKey(dest_ty);
    const sentinel = if (dest_key == .array_type) dest_key.array_type.sentinel else .none;
    if (sentinel == .none)
        return .{ .index = try ip.internAggregate(.{ .ty = dest_ty, .storage = .{ .repeated_elem = scalar.index } }) };

    // A sentinel array stores the scalar in each data slot, then the sentinel.
    const count: usize = @intCast(ip.aggregateElementCount(dest_ty));
    const elems = try sema.gpa.alloc(InternPool.Index, count);
    defer sema.gpa.free(elems);
    @memset(elems, scalar.index);
    elems[count - 1] = sentinel;
    return .{ .index = try ip.internAggregate(.{ .ty = dest_ty, .storage = .{ .elems = elems } }) };
}

/// `@shuffle(T, a, b, mask)`: build a `@Vector(mask_len, T)` by picking a lane
/// per mask element -- a non-negative `mask[i]` selects `a[mask[i]]`, a negative
/// one selects `b[~mask[i]]` (so `-1`->`b[0]`, `-2`->`b[1]`, ...). Out-of-range
/// indices are rejected. Mirrors zirShuffle -> analyzeShuffle's comptime arm.
/// Compiler reference: src/Sema.zig:zirShuffle (~22932).
fn evalShuffle(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.Shuffle, pl_node.payload_index).data;

    const elem_ty = try sema.resolveDestType(extra.elem_type, "@shuffle");
    if (!isVectorElemType(ip, elem_ty)) {
        try sema.writer.writeAll("@shuffle: expected integer, float, bool, or pointer for the element type\n");
        return error.AnalysisFail;
    }
    const mask = try sema.resolveRef(extra.mask);
    const mask_len = (indexableInfo(ip, Value.typeOf(mask, ip).index) orelse {
        try sema.writer.writeAll("@shuffle: expected vector or array for the mask\n");
        return error.AnalysisFail;
    }).len;
    const av = try sema.resolveRef(extra.a);
    const bv = try sema.resolveRef(extra.b);
    const a_len = (indexableInfo(ip, Value.typeOf(av, ip).index) orelse return sema.failShuffleOperand(elem_ty)).len;
    const b_len = (indexableInfo(ip, Value.typeOf(bv, ip).index) orelse return sema.failShuffleOperand(elem_ty)).len;

    const mask_agg = ip.indexToKey(mask.index).aggregate;
    const a_agg = ip.indexToKey(av.index).aggregate;
    const b_agg = ip.indexToKey(bv.index).aggregate;

    const elems = try sema.gpa.alloc(InternPool.Index, @intCast(mask_len));
    defer sema.gpa.free(elems);
    for (elems, 0..) |*e, i| {
        const raw = sema.intAsI128(InternPool.aggregateElementAt(mask_agg, i)) orelse {
            try sema.writer.writeAll("@shuffle: mask element is not a comptime integer\n");
            return error.AnalysisFail;
        };
        // A non-negative index selects `a`; a negative one selects `b` at `~raw`.
        const from_agg, const idx, const len = if (raw >= 0)
            .{ a_agg, @as(u64, @intCast(raw)), a_len }
        else
            .{ b_agg, @as(u64, @intCast(~raw)), b_len };
        if (idx >= len) {
            try sema.writer.print("mask element at index '{d}' selects out-of-bounds index\n", .{i});
            return error.AnalysisFail;
        }
        e.* = InternPool.aggregateElementAt(from_agg, idx);
    }
    const result_ty = try ip.internVectorType(.{ .len = @intCast(mask_len), .child = elem_ty });
    return .{ .index = try ip.internAggregate(.{ .ty = result_ty, .storage = .{ .elems = elems } }) };
}

fn failShuffleOperand(sema: *Sema, elem_ty: InternPool.Index) Error {
    sema.writer.writeAll("@shuffle: expected a vector of '") catch |e| return e;
    Type.print(.fromIndex(elem_ty), sema.intern_pool, sema.writer) catch |e| return e;
    sema.writer.writeAll("'\n") catch |e| return e;
    return error.AnalysisFail;
}

/// The `{len, child}` of an array/vector type, or the compiler's "expected array
/// or vector type, found '{f}'" error otherwise. Shared by the `@splat` handlers.
fn expectArrayOrVector(sema: *Sema, ty: InternPool.Index) Error!IndexableInfo {
    return indexableInfo(sema.intern_pool, ty) orelse {
        try sema.writer.writeAll("expected array or vector type, found '");
        try Type.print(.fromIndex(ty), sema.intern_pool, sema.writer);
        try sema.writer.writeAll("'\n");
        return error.AnalysisFail;
    };
}

/// `validate_array_init_ty` (`[N]T{...}`) / `validate_array_init_result_ty`
/// (`.{...}` with a known result type): confirm the type accepts array-init
/// syntax and that the element count matches. Validation only -- the per-element
/// type checking happens in `array_init`. The `_result_ty` form peels an
/// optional/error-union wrapper first (`is_result_ty`). Compiler reference:
/// src/Sema.zig:zirValidateArrayInitTy -> validateArrayInitTy.
fn evalValidateArrayInitTy(sema: *Sema, inst: Zir.Inst.Index, comptime is_result_ty: bool) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    const data = sema.zir.extraData(Zir.Inst.ArrayInit, pl_node.payload_index).data;
    const ty = try sema.resolveDestType(data.ty, "array init");
    const arr_ty = if (is_result_ty) sema.optEuBaseType(ty) else ty;
    try sema.validateArrayInitTy(data.init_count, arr_ty);
    return null;
}

/// The type-tag switch of `validateArrayInitTy`, mirrored arm-for-arm: an array
/// or vector requires an exact element count; a tuple allows AT MOST its field
/// count (trailing defaulted fields may be omitted); anything else does not
/// support array-init syntax.
fn validateArrayInitTy(sema: *Sema, init_count: u32, ty: InternPool.Index) Error!void {
    const ip = sema.intern_pool;
    switch (ip.indexToKey(ty)) {
        .array_type => |at| if (init_count != at.len) {
            try sema.writer.print("expected {d} array elements; found {d}\n", .{ at.len, init_count });
            return error.AnalysisFail;
        },
        .vector_type => |vt| if (init_count != vt.len) {
            try sema.writer.print("expected {d} vector elements; found {d}\n", .{ vt.len, init_count });
            return error.AnalysisFail;
        },
        // The compiler allows FEWER than the field count (trailing comptime-
        // defaulted fields may be omitted) and catches a genuine shortfall later
        // in struct-init. This evaluator models no comptime tuple defaults, so
        // every field is required -- an exact count, checked here.
        .tuple_type => |tt| if (init_count != tt.types.len) {
            try sema.writer.print("expected {d} tuple fields; found {d}\n", .{ tt.types.len, init_count });
            return error.AnalysisFail;
        },
        else => {
            try sema.writer.writeAll("type '");
            try Type.print(.fromIndex(ty), ip, sema.writer);
            try sema.writer.writeAll("' does not support array initialization syntax\n");
            return error.AnalysisFail;
        },
    }
}

/// `validate_array_init_ref_ty`: the array type a `&.{ ... }` init should build,
/// derived from the result pointer type -- `[elem_count]child` for a slice or
/// many-pointer result, otherwise the pointer's child type. Mirrors
/// zirValidateArrayInitRefTy.
fn evalValidateArrayInitRefTy(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.ArrayInitRefTy, pl_node.payload_index).data;
    const maybe_wrapped_ptr_ty = try sema.resolveDestType(extra.ptr_ty, "array init");
    if (maybe_wrapped_ptr_ty == .generic_poison_type) return .{ .index = .generic_poison_type };
    const ptr_ty = sema.optEuBaseType(maybe_wrapped_ptr_ty);
    assert(ip.indexToKey(ptr_ty) == .ptr_type); // validated by a previous instruction
    switch (ip.indexToKey(ptr_ty)) {
        .ptr_type => |ptr_type| switch (ptr_type.flags.size) {
            // Use an array of the correct length for a slice or many-pointer result.
            .slice, .many => return .{ .index = try ip.internArrayType(.{
                .len = extra.elem_count,
                .child = ptr_type.child,
                .sentinel = ptr_type.sentinel,
            }) },
            else => {},
        },
        else => {},
    }
    // Otherwise, we just want the pointer child type.
    const ret_ty = ip.indexToKey(ptr_ty).ptr_type.child;
    if (ret_ty == .anyopaque_type) return .{ .index = .generic_poison_type };
    const arr_ty = sema.optEuBaseType(ret_ty);
    try sema.validateArrayInitTy(extra.elem_count, arr_ty);
    return .{ .index = ret_ty };
}

/// `validate_ref_ty` (`&expr` with a known result type): checks the
/// result-location type is a pointer, so `&expr` -- which always yields a
/// pointer -- can satisfy it. Validation only (no value). Mirrors
/// `zirValidateRefTy`: peel any optional/error-union wrapper
/// (`optEuBaseType`, so `?*T`/`E!*T` targets pass) then require a
/// `ptr_type`. Compiler reference: src/Sema.zig:zirValidateRefTy (~4239).
fn evalValidateRefTy(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const un_tok = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_tok;
    const ty_operand = try sema.resolveDestType(un_tok.operand, "address-of");
    if (sema.intern_pool.indexToKey(sema.optEuBaseType(ty_operand)) != .ptr_type) {
        try sema.writer.writeAll("expected type '");
        try Type.print(.fromIndex(ty_operand), sema.intern_pool, sema.writer);
        try sema.writer.writeAll("', found pointer\n");
        return error.AnalysisFail;
    }
    return null;
}

/// `coerce_ptr_elem_ty lhs, rhs`: coerce a value (`rhs`) to what the
/// result pointer type (`lhs`) expects to point at -- for `&[_]T{...}` /
/// `&.{...}` bound to a `[]T`/`[*]T` target, an array of the pointer's
/// element type sized to the value's length. Mirrors `zirCoercePtrElemTy`:
/// a slice/many target coerces to `[N]elem`; a single (`.one`) target
/// coerces to `elem` (unless it's `*[1]T` from `&T`, left as-is); a C
/// pointer is left uncoerced. Compiler reference:
/// src/Sema.zig:zirCoercePtrElemTy (~4140).
fn evalCoercePtrElemTy(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const bin = sema.binData(inst);
    assert(bin.lhs != .none);
    assert(bin.rhs != .none);

    const ip = sema.intern_pool;
    const uncoerced = try sema.resolveRef(bin.rhs);
    const ptr_ty = ip.indexToKey(sema.optEuBaseType(try sema.resolveDestType(bin.lhs, "coerce_ptr_elem_ty"))).ptr_type;
    const elem_ty = ptr_ty.child;
    const val_ty = Value.typeOf(uncoerced, ip).index;
    switch (ptr_ty.flags.size) {
        .one => {
            // `*[1]T` initialised from `&T`: the pointer already matches, so
            // coercing the element would be wrong. Otherwise coerce to `T`.
            if (ip.indexToKey(elem_ty) == .array_type and ip.indexToKey(elem_ty).array_type.child == val_ty) {
                return uncoerced;
            }
            return try sema.coerceValueToType(uncoerced, elem_ty, "coerce_ptr_elem_ty");
        },
        .slice, .many => {
            const len = switch (ip.indexToKey(val_ty)) {
                .array_type => |at| at.len,
                .vector_type => |vt| vt.len,
                .tuple_type => |tt| tt.types.len,
                else => {
                    try sema.writer.writeAll("expected array of '");
                    try Type.print(.fromIndex(elem_ty), ip, sema.writer);
                    try sema.writer.writeAll("', found '");
                    try Type.print(.fromIndex(val_ty), ip, sema.writer);
                    try sema.writer.writeAll("'\n");
                    return error.AnalysisFail;
                },
            };
            const want_ty = try ip.internArrayType(.{ .len = len, .child = elem_ty, .sentinel = ptr_ty.sentinel });
            return try sema.coerceValueToType(uncoerced, want_ty, "coerce_ptr_elem_ty");
        },
        .c => return uncoerced,
    }
}

/// Peel any optional (`?T`) or error-union (`E!T`) wrapper off a type,
/// returning the innermost base. Mirrors `Type.optEuBaseType`, which the
/// result-location handlers use so `?*T` / `E![]T` targets are treated by
/// their pointer/array base.
fn optEuBaseType(sema: *Sema, ty: InternPool.Index) InternPool.Index {
    var cur = ty;
    while (true) switch (sema.intern_pool.indexToKey(cur)) {
        .opt_type => |child| cur = child,
        .error_union_type => |eu| cur = eu.payload_type,
        else => return cur,
    };
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

    // Resolve captured outer values now, while the defining scope is live; a
    // `closure_get` in a field/decl body reads them later (`evalClosureGet`).
    const captures = try sema.resolveCaptures(struct_decl.captures);
    defer sema.gpa.free(captures);

    return .{
        .index = try sema.intern_pool.internStructType(.{
            .name = name,
            .id = .{ .declared = .{
                .source_zir_id = sema.current_zir_id,
                .decl_inst = inst,
                .captures = captures,
            } },
            // The container being evaluated is the enclosing one; record it so an
            // unqualified decl reference resolves outward (the compiler's namespace parent).
            .parent = sema.this_type,
        }),
    };
}

/// `enum_decl` (extended): a named enum type (`enum { a, b }`). Interns a nominal
/// `enum_type` shell keyed on the declaration site, like `evalStructDecl`; field
/// names, the integer tag type, and per-field values are resolved on demand from
/// the decl's ZIR (`enumFieldByName`). Mirrors src/Sema.zig:zirEnumDecl ->
/// getDeclaredEnumType (identity only, lazy field resolution).
fn evalEnumDecl(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const enum_decl = sema.zir.getEnumDecl(inst);
    const name = switch (enum_decl.name_strategy) {
        .parent => sema.type_name_ctx,
        .anon, .func, .dbg_var => blk: {
            const ctx = sema.intern_pool.stringSlice(sema.type_name_ctx);
            const text = try std.fmt.allocPrint(sema.gpa, "{s}__enum_{d}", .{ ctx, @intFromEnum(inst) });
            defer sema.gpa.free(text);
            break :blk try sema.intern_pool.getOrPutString(sema.gpa, text);
        },
    };

    const captures = try sema.resolveCaptures(enum_decl.captures);
    defer sema.gpa.free(captures);

    return .{ .index = try sema.intern_pool.internEnumType(.{
        .name = name,
        .id = .{ .declared = .{
            .source_zir_id = sema.current_zir_id,
            .decl_inst = inst,
            .captures = captures,
        } },
        .parent = sema.this_type,
    }) };
}

/// `union_decl` (extended): a named union type (`union(enum) { a: u8, b: u16 }`).
/// Interns a nominal `union_type` shell, like `evalEnumDecl`; field names and
/// types resolve on demand from the decl's ZIR. Mirrors zirUnionDecl ->
/// getDeclaredUnionType.
fn evalUnionDecl(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const union_decl = sema.zir.getUnionDecl(inst);
    const name = switch (union_decl.name_strategy) {
        .parent => sema.type_name_ctx,
        .anon, .func, .dbg_var => blk: {
            const ctx = sema.intern_pool.stringSlice(sema.type_name_ctx);
            const text = try std.fmt.allocPrint(sema.gpa, "{s}__union_{d}", .{ ctx, @intFromEnum(inst) });
            defer sema.gpa.free(text);
            break :blk try sema.intern_pool.getOrPutString(sema.gpa, text);
        },
    };

    const captures = try sema.resolveCaptures(union_decl.captures);
    defer sema.gpa.free(captures);

    return .{ .index = try sema.intern_pool.internUnionType(.{
        .name = name,
        .id = .{ .declared = .{
            .source_zir_id = sema.current_zir_id,
            .decl_inst = inst,
            .captures = captures,
        } },
        .parent = sema.this_type,
    }) };
}

/// Resolve a struct decl's ZIR captures to their comptime values in the current
/// scope. Mirrors `Sema.getCaptures`, reduced to the kinds a comptime evaluator
/// produces: a captured local is an `.instruction` (its value) or an
/// `.instruction_load` (load through its alloc); `.nested` indexes the enclosing
/// container's already-resolved captures (`this_type`). Returns a fresh slice the
/// caller frees; `internStructType` copies it into the pool.
fn resolveCaptures(sema: *Sema, zir_captures: []const Zir.Inst.Capture) Error![]const InternPool.Index {
    if (zir_captures.len == 0) return &.{};
    const caps = try sema.gpa.alloc(InternPool.Index, zir_captures.len);
    errdefer sema.gpa.free(caps);
    for (zir_captures, caps) |zc, *c| {
        c.* = switch (zc.unwrap()) {
            .instruction => |i| (try sema.resolveRef(i.toRef())).index,
            .instruction_load => |i| (try sema.loadValue(try sema.resolveRef(i.toRef()))).index,
            .nested => |idx| sema.intern_pool.indexToKey(sema.this_type).struct_type.id.captures()[idx],
            .decl_val, .decl_ref => {
                try sema.writer.writeAll("closure capture: decl captures are not supported\n");
                return error.AnalysisFail;
            },
        };
    }
    return caps;
}

/// A saved `(zir, current_zir_id)` pair, put back by `restore`. The compiler
/// keeps one persistent `Zir` per file and never swaps; the REPL retains each
/// line's ZIR separately, so a struct or function defined on an earlier line is
/// inspected by temporarily viewing its source ZIR, then restoring the caller's.
const ZirFrame = struct {
    zir: Zir,
    id: u32,

    fn restore(frame: ZirFrame, sema: *Sema) void {
        sema.zir = frame.zir;
        sema.current_zir_id = frame.id;
    }
};

/// View the ZIR of the file that defined `source_zir_id` (a no-op when it is the
/// current file), returning the previous frame; the caller `defer`s `.restore`.
/// `ctx` names the operation for the diagnostic when that file's ZIR is no longer
/// available -- a REPL-only failure (a tombstoned failed line), since the
/// compiler never discards a live file's ZIR.
fn enterSourceZir(sema: *Sema, source_zir_id: u32, ctx: []const u8) Error!ZirFrame {
    const frame: ZirFrame = .{ .zir = sema.zir, .id = sema.current_zir_id };
    if (source_zir_id != sema.current_zir_id) {
        const session = sema.session orelse return sema.failZirUnavailable(ctx);
        if (source_zir_id >= session.files.items.len) return sema.failZirUnavailable(ctx);
        sema.zir = session.files.items[source_zir_id].zir orelse return sema.failZirUnavailable(ctx);
        sema.current_zir_id = source_zir_id;
    }
    return frame;
}

fn failZirUnavailable(sema: *Sema, ctx: []const u8) Error {
    try sema.writer.print("{s}: defining ZIR is no longer available\n", .{ctx});
    return error.AnalysisFail;
}

/// A container's resolution context: its source ZIR frame, the `this_type` that
/// `@This()` resolves to while inside, and the `decl_inst` its field/decl bodies
/// hang off. Restored together. Everything the field and decl accessors need to
/// read a nominal container's ZIR, in one place.
const ContainerFrame = struct {
    zir: ZirFrame,
    saved_this: InternPool.Index,
    decl_inst: Zir.Inst.Index,

    fn restore(cf: ContainerFrame, sema: *Sema) void {
        sema.this_type = cf.saved_this;
        cf.zir.restore(sema);
    }
};

/// Enter a nominal container's resolution context. A generated tag enum has no
/// ZIR of its own -- it resolves in its owner union's context (the compiler's
/// `owner_union`), so the owner is unwrapped here rather than at each call site.
fn enterContainer(sema: *Sema, container_ty: InternPool.Index, ctx: []const u8) Error!ContainerFrame {
    const owner = switch (sema.intern_pool.indexToKey(container_ty)) {
        .enum_type => |et| if (et.id.generatedUnion() != .none) et.id.generatedUnion() else container_ty,
        else => container_ty,
    };
    const ns = sema.containerNamespace(owner).?;
    const zir = try sema.enterSourceZir(ns.source_zir_id, ctx);
    const saved_this = sema.this_type;
    sema.this_type = owner;
    return .{ .zir = zir, .saved_this = saved_this, .decl_inst = ns.decl_inst };
}

/// The compiler's `failWithBadStructFieldAccess` diagnostic: a field lookup that
/// misses names both the field and the struct. Shared by every field-access site
/// (`field_ptr`, field loads, struct init) so the wording is one message keyed on
/// the struct -- not a per-syntax context string. Mirrors src/Sema.zig.
fn failBadStructFieldAccess(sema: *Sema, struct_ty: InternPool.Index, name: InternPool.NullTerminatedString) Error {
    const ip = sema.intern_pool;
    const st_name = ip.stringSlice(ip.indexToKey(struct_ty).struct_type.name);
    sema.writer.print("no field named '{s}' in struct '{s}'\n", .{ ip.stringSlice(name), st_name }) catch |e| return e;
    return error.AnalysisFail;
}

/// The union counterpart of `failBadStructFieldAccess`: a field lookup that misses
/// on a union value/type. Mirrors the compiler's separate
/// `failWithBadUnionFieldAccess` ("... in union '{f}'").
fn failBadUnionFieldAccess(sema: *Sema, union_ty: InternPool.Index, name: InternPool.NullTerminatedString) Error {
    const ip = sema.intern_pool;
    const un_name = ip.stringSlice(ip.indexToKey(union_ty).union_type.name);
    sema.writer.print("no field named '{s}' in union '{s}'\n", .{ ip.stringSlice(name), un_name }) catch |e| return e;
    return error.AnalysisFail;
}

/// The compiler's `failWithBadMemberAccess` diagnostic: a namespace/tag lookup
/// that misses names the container kind, the container, and the member. Used for
/// `T.member`, the static `T.decl()` call, and a missing enum tag (`E.z`).
/// Mirrors src/Sema.zig (kw_name + type name).
fn failBadMemberAccess(sema: *Sema, container_ty: InternPool.Index, name: InternPool.NullTerminatedString) Error {
    const ip = sema.intern_pool;
    const key = ip.indexToKey(container_ty);
    const kw: []const u8, const ct_name: InternPool.NullTerminatedString = switch (key) {
        .struct_type => |st| .{ "struct", st.name },
        .enum_type => |et| .{ "enum", et.name },
        .union_type => |ut| .{ "union", ut.name },
        // A non-container type reaches here only through a field call on a type
        // that carries no namespace (`u8.foo()`); name it via its printed form.
        else => {
            sema.writer.print("type '", .{}) catch |e| return e;
            Type.print(.fromIndex(container_ty), ip, sema.writer) catch |e| return e;
            sema.writer.print("' has no member named '{s}'\n", .{ip.stringSlice(name)}) catch |e| return e;
            return error.AnalysisFail;
        },
    };
    sema.writer.print("{s} '{s}' has no member named '{s}'\n", .{ kw, ip.stringSlice(ct_name), ip.stringSlice(name) }) catch |e| return e;
    return error.AnalysisFail;
}

/// A resolved container field. `index`/`ty` serve every caller. The reflection
/// attributes (`is_comptime`, explicit `align_bytes` or null) come free from the
/// same ZIR field the by-name lookup already visits. The field's default value is
/// deliberately absent: the compiler resolves defaults in a pass (`field_defaults`
/// via `ensureStructDefaultsResolved`) separate from field types and reads them
/// only for aggregate init and `@typeInfo`, never during field access -- see
/// `structFieldDefault`. Void-typed and align-less fields leave the rest at rest.
pub const FieldInfo = struct {
    index: u32,
    ty: InternPool.Index,
    is_comptime: bool = false,
    align_bytes: ?u64 = null,
};

/// Field `i`'s `comptime` bit from a reified struct's stored `comptime_bits`
/// (empty when no field is comptime, LSB-first within each u32).
fn structFieldIsComptime(f: InternPool.StructFields, i: usize) bool {
    if (f.comptime_bits.len == 0) return false;
    return f.comptime_bits[i / 32] >> @intCast(i % 32) & 1 != 0;
}

/// Field `i`'s explicit alignment (bytes) from a reified struct's stored `aligns`,
/// or null for the natural alignment (no `aligns` slice, or a `.none` entry).
fn structFieldAlign(sema: *Sema, f: InternPool.StructFields, i: usize) ?u64 {
    if (f.aligns.len == 0 or f.aligns[i] == .none) return null;
    return @intCast(sema.intAsI128(f.aligns[i]).?);
}

/// Resolve a struct field by name to its index and type. Iterates the struct
/// decl's fields via the stdlib `iterateFields`, matching name bytes; the field
/// type is its type body evaluated in the struct's source ZIR (swapped in for a
/// cross-line struct, as `evalCall` does for functions). Returns null if no
/// field matches. Field types that reference the defining line's locals are out
/// of scope -- the swapped frame shares the session namespace but not that
/// line's per-instruction results.
pub fn structFieldByName(
    sema: *Sema,
    struct_ty: InternPool.Index,
    name: InternPool.NullTerminatedString,
) Error!?FieldInfo {
    const ip = sema.intern_pool;
    // A reified struct has no ZIR; its fields are read from storage.
    if (ip.structFields(struct_ty)) |f| {
        for (f.names, 0..) |n, i| {
            if (n != name) continue;
            return .{
                .index = @intCast(i),
                .ty = f.types[i],
                .is_comptime = structFieldIsComptime(f, i),
                .align_bytes = structFieldAlign(sema, f, i),
            };
        }
        return null;
    }
    // Intern each ZIR field name as we scan and compare interned handles against
    // the (already interned) query -- the compiler resolves struct fields lazily
    // too (`resolveStructFieldTypes` interns each ZIR name), and `getOrPutString`
    // dedups so repeated resolution is stable. `this_type` is the struct, so a
    // `closure_get` (a captured outer type) in a field body resolves.
    const cf = try sema.enterContainer(struct_ty, "struct field");
    defer cf.restore(sema);
    // An anonymous struct (`.{ .a = 1 }`) has no `struct_decl`; its fields live in
    // the owning `struct_init_anon` instruction's items.
    if (sema.zir.instructions.items(.tag)[@intFromEnum(cf.decl_inst)] == .struct_init_anon)
        return try sema.anonStructFieldByName(cf.decl_inst, name);
    var it = sema.zir.getStructDecl(cf.decl_inst).iterateFields();
    while (it.next()) |field| {
        if ((try ip.getOrPutString(sema.gpa, sema.zir.nullTerminatedString(field.name))) == name) {
            return .{
                .index = field.idx,
                .ty = (try sema.resolveInlineBody(field.type_body, cf.decl_inst)).index,
                .is_comptime = field.is_comptime,
                .align_bytes = try sema.fieldAlignBytes(field.align_body, cf.decl_inst),
            };
        }
    }
    return null;
}

/// A struct field's declared default value, coerced to the field type, or `.none`
/// if it has none. Mirrors the compiler's `field_defaults` (populated by
/// `ensureStructDefaultsResolved`): a resolution pass separate from field types,
/// consulted only by aggregate init and `@typeInfo`. Field access must not run it
/// -- a default like `= .auto` resolves against the field type, not the accessing
/// scope, so evaluating it off the access path would misbind. An anonymous struct
/// has no declared defaults (its values come from the init), so it yields `.none`.
pub fn structFieldDefault(
    sema: *Sema,
    struct_ty: InternPool.Index,
    name: InternPool.NullTerminatedString,
) Error!InternPool.Index {
    const ip = sema.intern_pool;
    // A reified struct has no ZIR; its defaults are stored (`.none` if none).
    if (ip.structFields(struct_ty)) |f| {
        for (f.names, 0..) |n, i| {
            if (n != name) continue;
            return if (f.defaults.len == 0) .none else f.defaults[i];
        }
        return .none;
    }
    const cf = try sema.enterContainer(struct_ty, "struct field default");
    defer cf.restore(sema);
    if (sema.zir.instructions.items(.tag)[@intFromEnum(cf.decl_inst)] == .struct_init_anon) return .none;
    var it = sema.zir.getStructDecl(cf.decl_inst).iterateFields();
    while (it.next()) |field| {
        if ((try ip.getOrPutString(sema.gpa, sema.zir.nullTerminatedString(field.name))) != name) continue;
        const body = field.default_body orelse return .none;
        const ty = (try sema.resolveInlineBody(field.type_body, cf.decl_inst)).index;
        // AstGen compiles the default with `coerced_ty = decl_inst.toRef()`, so a
        // decl literal in it (`= .foo`) takes its result type from the field's
        // decl inst; bind that to the resolved field type before evaluating, then
        // restore. Mirrors the compiler's inst_map put/remove around the init body.
        try sema.results.put(sema.gpa, cf.decl_inst, .{ .index = ty });
        const raw = sema.resolveInlineBody(body, cf.decl_inst);
        _ = sema.results.remove(cf.decl_inst);
        return (try sema.coerceValueToType(try raw, ty, "field default")).index;
    }
    return .none;
}

/// The index of an anonymous struct's field `name` (matching the
/// `struct_init_anon` items), or null. Name-based only -- no init evaluation --
/// so it works cross-line (a field's type/value comes from the stored aggregate,
/// not from re-resolving its init, which is out of scope after the ZIR swap). The
/// `FieldInfo.ty` is `.none`; callers that need the field type read it from the
/// aggregate element (`fieldTypeFromValue`).
fn anonStructFieldByName(sema: *Sema, decl_inst: Zir.Inst.Index, name: InternPool.NullTerminatedString) Error!?FieldInfo {
    const ip = sema.intern_pool;
    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(decl_inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.StructInitAnon, pl_node.payload_index);
    var extra_index = extra.end;
    var i: u32 = 0;
    while (i < extra.data.fields_len) : (i += 1) {
        const item = sema.zir.extraData(Zir.Inst.StructInitAnon.Item, extra_index);
        extra_index = item.end;
        if ((try ip.getOrPutString(sema.gpa, sema.zir.nullTerminatedString(item.data.field_name))) == name)
            return .{ .index = i, .ty = .none };
    }
    return null;
}

/// Resolve a union field by name to its index and type. Mirrors `structFieldByName`
/// over the union decl's fields (`getUnionDecl().iterateFields()`); a field with no
/// type body is `void`. Returns null if no field matches.
pub fn unionFieldByName(
    sema: *Sema,
    union_ty: InternPool.Index,
    name: InternPool.NullTerminatedString,
) Error!?FieldInfo {
    const ip = sema.intern_pool;
    // A reified union has no ZIR; its fields are read from storage.
    if (ip.unionFields(union_ty)) |f| {
        for (f.names, 0..) |n, i| {
            if (n != name) continue;
            return .{
                .index = @intCast(i),
                .ty = f.types[i],
                .align_bytes = if (f.aligns.len == 0 or f.aligns[i] == .none) null else @intCast(sema.intAsI128(f.aligns[i]).?),
            };
        }
        return null;
    }
    const cf = try sema.enterContainer(union_ty, "union field");
    defer cf.restore(sema);
    var it = sema.zir.getUnionDecl(cf.decl_inst).iterateFields();
    while (it.next()) |field| {
        if ((try ip.getOrPutString(sema.gpa, sema.zir.nullTerminatedString(field.name))) == name) {
            const ty = if (field.type_body) |body|
                (try sema.resolveInlineBody(body, cf.decl_inst)).index
            else
                .void_type;
            return .{
                .index = field.idx,
                .ty = ty,
                .align_bytes = try sema.fieldAlignBytes(field.align_body, cf.decl_inst),
            };
        }
    }
    return null;
}

/// A field's explicit `align(N)` in bytes, or null when it has no alignment body.
/// The `field.align_body` an iterator yields for struct and union fields; mirrors
/// the compiler's `explicitFieldAlignment` collapsing to null when unspecified.
fn fieldAlignBytes(sema: *Sema, align_body: ?[]const Zir.Inst.Index, decl_inst: Zir.Inst.Index) Error!?u64 {
    const body = align_body orelse return null;
    return try sema.resolveUsizeInt(try sema.resolveInlineBody(body, decl_inst), "field alignment");
}

/// An explicit field alignment as an interned `?usize` -- `null` when unspecified,
/// else the byte count. The `@"align"` field of `@typeInfo`'s `FieldAttributes`.
fn alignOptValue(sema: *Sema, align_bytes: ?u64) Error!InternPool.Index {
    const ip = sema.intern_pool;
    const opt_usize = try ip.internOptionalType(.usize_type);
    return try ip.internOpt(.{
        .ty = opt_usize,
        .val = if (align_bytes) |bytes| try ip.internInt(.{ .ty = .usize_type, .storage = .{ .u64 = bytes } }) else .none,
    });
}

/// A `?type` value -- `null` for `.none`, else the type. `@typeInfo`'s optional
/// `tag_type` / `backing_integer` container fields.
fn optTypeValue(sema: *Sema, val: InternPool.Index) Error!InternPool.Index {
    const ip = sema.intern_pool;
    return try ip.internOpt(.{ .ty = try ip.internOptionalType(.type_type), .val = val });
}

/// A `std.lang.CallingConvention` union value for `cc` (`@typeInfo`'s
/// `Fn.Attributes.callconv`). Payload-free conventions -- `.auto` and friends,
/// the ones a comptime-only function carries -- build from the active tag with a
/// void payload; the arch-specific payload-bearing conventions have no comptime
/// instances here and are not modelled. A focused stand-in for the compiler's
/// general `Value.uninterpret(cc, ...)`.
fn callConvValue(sema: *Sema, cc: std.lang.CallingConvention) Error!InternPool.Index {
    const ip = sema.intern_pool;
    const cc_ty = try sema.getStdLangType(.CallingConvention);
    const tag_enum = try sema.unionTagEnumType(cc_ty);
    switch (cc) {
        inline else => |payload, tag| {
            if (@TypeOf(payload) != void) {
                try sema.writer.print("@typeInfo: calling convention '{s}' is not modelled\n", .{@tagName(tag)});
                return error.AnalysisFail;
            }
            const idx = (try sema.enumFieldIndex(tag_enum, try ip.getOrPutString(sema.gpa, @tagName(tag)))).?;
            const tag_val = (try sema.enumValueFieldIndex(tag_enum, idx)).?;
            return try ip.internUnion(.{ .ty = cc_ty, .tag = tag_val.index, .val = .void_value });
        },
    }
}

/// The interned name of a struct's field at `index`, mirroring `unionFieldNameAt`
/// -- lets `@typeInfo`'s struct arm iterate by position while `structFieldByName`
/// supplies each field's type and attributes.
pub fn structFieldNameAt(sema: *Sema, struct_ty: InternPool.Index, index: u32) Error!?InternPool.NullTerminatedString {
    const ip = sema.intern_pool;
    // A reified struct has no ZIR; its field names are stored.
    if (ip.structFields(struct_ty)) |f| return if (index < f.names.len) f.names[index] else null;
    const cf = try sema.enterContainer(struct_ty, "struct field name");
    defer cf.restore(sema);
    var it = sema.zir.getStructDecl(cf.decl_inst).iterateFields();
    while (it.next()) |field| {
        if (field.idx == index)
            return try ip.getOrPutString(sema.gpa, sema.zir.nullTerminatedString(field.name));
    }
    return null;
}

/// A union type's declared field count, read from its source ZIR.
pub fn unionFieldCount(sema: *Sema, union_ty: InternPool.Index) Error!u32 {
    // A reified union has no ZIR; its field count comes from stored fields.
    if (sema.intern_pool.unionFields(union_ty)) |f| return @intCast(f.names.len);
    const cf = try sema.enterContainer(union_ty, "union field count");
    defer cf.restore(sema);
    return @intCast(sema.zir.getUnionDecl(cf.decl_inst).field_names.len);
}

/// The interned name of a union's field at `index`, for the active-field
/// diagnostic (the compiler's `enumFieldName(active_index)`). Returns null if the
/// index is out of range.
pub fn unionFieldNameAt(sema: *Sema, union_ty: InternPool.Index, index: u32) Error!?InternPool.NullTerminatedString {
    const ip = sema.intern_pool;
    // A reified union has no ZIR; its field names are stored.
    if (ip.unionFields(union_ty)) |f| return if (index < f.names.len) f.names[index] else null;
    const cf = try sema.enterContainer(union_ty, "union field name");
    defer cf.restore(sema);
    var it = sema.zir.getUnionDecl(cf.decl_inst).iterateFields();
    while (it.next()) |field| {
        if (field.idx == index)
            return try ip.getOrPutString(sema.gpa, sema.zir.nullTerminatedString(field.name));
    }
    return null;
}

/// The union's auto-generated tag enum: an `enum_type` whose identity is the
/// union index alone (`generated_union`) and whose fields are the union's,
/// resolved through that back-reference. Mirrors the compiler's
/// `generated_union_tag` container: `owner_union` set, `zir_index`/`captures`
/// empty. Every auto-layout union has one, and its tag values drive the
/// active-field check.
fn failUntaggedUnionCmp(sema: *Sema) Error {
    sema.writer.writeAll("comparison of union and enum literal is only valid for tagged union types\n") catch |e| return e;
    return error.AnalysisFail;
}

/// The union half of `analyzeCmpUnionTag`: reject a comparison against an
/// untagged union, and when the literal names a field whose type has no possible
/// value -- so that tag can never be active -- short-circuit to the static
/// result (`==` false, `!=` true). Returns null to fall through to the
/// active-tag comparison; only `==`/`!=` short-circuit.
fn cmpUnionTagNoValue(sema: *Sema, union_ty: InternPool.Index, tag_name: InternPool.NullTerminatedString, op: std.math.CompareOperator) Error!?Value {
    if (!try sema.unionIsTagged(union_ty)) return sema.failUntaggedUnionCmp();
    if (op != .eq and op != .neq) return null;
    const field = (try sema.unionFieldByName(union_ty, tag_name)) orelse return null;
    if (!try sema.isNoPossibleValue(field.ty)) return null;
    return .{ .index = if (op == .eq) .bool_false else .bool_true };
}

/// Whether a value of `ty` cannot exist -- `Type.classify(zcu) == .no_possible_value`.
/// The NPV determination is layout-independent (it depends only on field types,
/// which this evaluator resolves), so it is ported in full, unlike the
/// one/comptime distinctions `classify` draws from resolved byte sizes.
/// Exhaustive per the compiler's NPV list: `noreturn`; `anyopaque` (and any
/// opaque type, which this evaluator does not model); `[n]T` with `n != 0` of an
/// NPV `T`; a tuple/struct with a (non-comptime) NPV field; a union all of whose
/// fields are NPV. An optional or error union of an NPV type is NOT NPV -- it
/// still holds `null` / an error. An enum's backing is always an integer, so an
/// enum is never NPV (the compiler's `noreturn`-backed enum cannot be formed).
pub fn isNoPossibleValue(sema: *Sema, ty: InternPool.Index) Error!bool {
    const ip = sema.intern_pool;
    return switch (ip.indexToKey(ty)) {
        .simple_type => |s| s == .noreturn or s == .anyopaque,
        // A zero-length array without a sentinel has one value; otherwise it is
        // NPV iff its element is (mirrors classify's array arm).
        .array_type => |arr| arr.len != 0 and arr.sentinel == .none and try sema.isNoPossibleValue(arr.child),
        .tuple_type => |tup| {
            for (tup.types) |field_ty| if (try sema.isNoPossibleValue(field_ty)) return true;
            return false;
        },
        .struct_type => try sema.structHasNpvField(ty),
        .union_type => try sema.unionAllFieldsNpv(ty),
        else => false,
    };
}

/// A struct is NPV if any of its fields has an NPV type (a comptime field cannot,
/// as it holds a concrete value). Reads each field type through `structFieldByName`.
fn structHasNpvField(sema: *Sema, struct_ty: InternPool.Index) Error!bool {
    const count = try sema.structFieldCount(struct_ty);
    var i: u32 = 0;
    while (i < count) : (i += 1) {
        const name = (try sema.structFieldNameAt(struct_ty, i)).?;
        if (try sema.isNoPossibleValue((try sema.structFieldByName(struct_ty, name)).?.ty)) return true;
    }
    return false;
}

/// A union is NPV iff every field has an NPV type (no tag can ever be active --
/// the compiler's `possible_tags == 0`). Reads each field type through
/// `unionFieldByName`.
fn unionAllFieldsNpv(sema: *Sema, union_ty: InternPool.Index) Error!bool {
    const count = try sema.unionFieldCount(union_ty);
    if (count == 0) return false;
    var i: u32 = 0;
    while (i < count) : (i += 1) {
        const name = (try sema.unionFieldNameAt(union_ty, i)).?;
        if (!try sema.isNoPossibleValue((try sema.unionFieldByName(union_ty, name)).?.ty)) return false;
    }
    return true;
}

pub fn unionTagEnumType(sema: *Sema, union_ty: InternPool.Index) Error!InternPool.Index {
    const ip = sema.intern_pool;
    // A reified union with an explicit tag enum uses it; an untagged one gets a
    // generated tag enum keyed on the union (auto-numbered), like a declared bare
    // union -- so its values still carry a tag.
    if (ip.unionFields(union_ty)) |f| {
        if (f.tag_type != .none) return f.tag_type;
        return try ip.internEnumType(.{
            .name = ip.indexToKey(union_ty).union_type.name,
            .id = .{ .generated_union_tag = union_ty },
        });
    }
    const ut = ip.indexToKey(union_ty).union_type;
    // `this_type` is the union, so a `closure_get` (a captured `E` / `T`) in the
    // tag-type body resolves.
    const cf = try sema.enterContainer(union_ty, "union tag type");
    defer cf.restore(sema);
    const decl = sema.zir.getUnionDecl(cf.decl_inst);
    // `union(E)`: the tag is the existing enum `E` (the `arg_type_body`), which
    // must be an enum. `union(enum)` / `union(enum(T))` / bare `union` generate a
    // tag enum keyed on the union (its int type resolved in `generatedTagLookup`).
    if (decl.kind == .tagged_explicit) {
        const ty = (try sema.resolveInlineBody(decl.arg_type_body.?, cf.decl_inst)).index;
        if (ip.indexToKey(ty) != .enum_type) {
            try sema.writer.writeAll("expected enum tag type, found '");
            try Type.print(.fromIndex(ty), ip, sema.writer);
            try sema.writer.writeAll("'\n");
            return error.AnalysisFail;
        }
        return ty;
    }
    return try ip.internEnumType(.{
        // A generated tag enum's identity is the owner union alone; field
        // resolution goes through it. `name` still prints the tag type's name.
        .name = ut.name,
        .id = .{ .generated_union_tag = union_ty },
    });
}

/// An enum type's declared field count, read from its source ZIR. A union's
/// generated tag enum defers to the union's field count.
fn enumFieldCount(sema: *Sema, enum_ty: InternPool.Index) Error!u32 {
    const et = sema.intern_pool.indexToKey(enum_ty).enum_type;
    if (et.id.generatedUnion() != .none) return try sema.unionFieldCount(et.id.generatedUnion());
    // A reified enum has no ZIR; its field count comes from stored fields.
    if (sema.intern_pool.enumFields(enum_ty)) |f| return @intCast(f.names.len);
    const cf = try sema.enterContainer(enum_ty, "enum field count");
    defer cf.restore(sema);
    return @intCast(sema.zir.getEnumDecl(cf.decl_inst).field_names.len);
}

/// The integer tag type of an auto-numbered enum with `field_count` fields: the
/// smallest unsigned int that can hold `field_count - 1`, the compiler's default
/// enum tag type. The fallback when no explicit `enum(T)` backing int is given.
fn enumIntTagType(sema: *Sema, field_count: u32) Error!InternPool.Index {
    const bits: u16 = if (field_count <= 1) 0 else @intCast(64 - @clz(@as(u64, field_count - 1)));
    return try sema.intern_pool.internIntType(.unsigned, bits);
}

/// How to select an enum tag: by field name (`E.b`) or by integer value
/// (`@enumFromInt`). Both walk the same field iteration, so one helper serves both.
const EnumMatch = union(enum) { name: InternPool.NullTerminatedString, value: i128, index: u32 };

/// The result of an enum lookup: the `enum_tag` value, its interned field name
/// (so `@tagName` needs no second scan), and its field position. The position is
/// the compiler's `enumTagFieldIndex` -- the union active-field check compares it
/// to the accessed field index.
const EnumMatchResult = struct { tag: Value, name: InternPool.NullTerminatedString, index: u32 };

/// Resolve an enum tag by name or by integer value, returning its `enum_tag` and
/// interned name. Walks the decl's fields in order, assigning each its value: an
/// explicit `= expr` body, else one past the previous (0 for the first). The tag
/// type is an explicit `enum(T)` body, else the auto smallest-unsigned. Returns
/// null if nothing matches. `this_type` is set so a value body may use `@This()`.
///
/// This is the shared walk backing the compiler-shaped accessors below
/// (`enumFieldIndex` / `enumTagFieldIndex` / `enumFieldName` / `enumValueFieldIndex`),
/// analogous to the compiler indexing into a `LoadedEnumType`'s resolved arrays --
/// this evaluator has no such cached type, so it re-walks the ZIR.
fn enumFieldScan(sema: *Sema, enum_ty: InternPool.Index, match: EnumMatch) Error!?EnumMatchResult {
    const ip = sema.intern_pool;
    const et = ip.indexToKey(enum_ty).enum_type;
    // A union's generated tag enum has no enum ZIR: its fields are the union's,
    // auto-numbered from 0 with no explicit values or tag type.
    if (et.id.generatedUnion() != .none) return try sema.generatedTagScan(enum_ty, match);

    const fields = try sema.resolveEnumFields(enum_ty);
    for (fields.names, 0..) |field_name, pos| {
        // An auto-numbered enum stores no values; the tag value is the field index.
        const cur: i128 = if (fields.values.len == 0) @intCast(pos) else sema.intAsI128(fields.values[pos]).?;
        if (try sema.matchEnumField(enum_ty, fields.int_tag_type, match, field_name, @intCast(pos), cur)) |m| return m;
    }
    return null;
}

/// Resolve a declared enum's fields from its ZIR into the InternPool once, then
/// return the stored view. The tag type and each field's name and (auto or
/// explicit) value are read in the enum's own ZIR frame; subsequent calls read the
/// cache. Mirrors the compiler resolving `LoadedEnumType`'s fields lazily.
fn resolveEnumFields(sema: *Sema, enum_ty: InternPool.Index) Error!InternPool.EnumFields {
    const ip = sema.intern_pool;
    if (ip.enumFields(enum_ty)) |f| return f;

    const tag_ty = try sema.enumIntTagTypeOf(enum_ty);
    const cf = try sema.enterContainer(enum_ty, "enum field");
    defer cf.restore(sema);
    const decl = sema.zir.getEnumDecl(cf.decl_inst);
    // The compiler stores field values only for an enum that needs them -- an
    // explicit tag type or a non-exhaustive enum; an auto-numbered enum's value is
    // its field index (see `enumValueFieldIndex`). Zig rejects explicit values
    // without an explicit tag type, so `tag_type_body` captures every valued enum.
    const have_values = decl.nonexhaustive or decl.tag_type_body != null;

    var names: std.ArrayListUnmanaged(InternPool.NullTerminatedString) = .empty;
    defer names.deinit(sema.gpa);
    var values: std.ArrayListUnmanaged(InternPool.Index) = .empty;
    defer values.deinit(sema.gpa);

    var it = decl.iterateFields();
    var next_auto: i128 = 0;
    while (it.next()) |field| {
        try names.append(sema.gpa, try ip.getOrPutString(sema.gpa, sema.zir.nullTerminatedString(field.name)));
        if (!have_values) continue;
        const cur: i128 = if (field.value_body) |body| blk: {
            const raw = try sema.resolveInlineBody(body, cf.decl_inst);
            break :blk sema.intAsI128(raw.index) orelse {
                try sema.writer.writeAll("enum: tag value is not an integer\n");
                return error.AnalysisFail;
            };
        } else next_auto;
        next_auto = cur + 1;
        try values.append(sema.gpa, try sema.enumTagIntValue(tag_ty, cur));
    }
    try ip.setEnumFields(enum_ty, tag_ty, decl.nonexhaustive, names.items, values.items);
    return ip.enumFields(enum_ty).?;
}

/// `enumFieldScan` for a union's generated tag enum: the fields are the union's,
/// auto-numbered from 0. The int tag type is `union(enum(T))`'s explicit `T`, else
/// the auto smallest-unsigned. Mirrors the compiler treating the generated tag as
/// an ordinary auto enum whose int mode is explicit only for `tagged_enum_explicit`.
fn generatedTagScan(sema: *Sema, enum_ty: InternPool.Index, match: EnumMatch) Error!?EnumMatchResult {
    const ip = sema.intern_pool;
    const tag_ty = try sema.enumIntTagTypeOf(enum_ty);
    // A reified union has no ZIR; its generated tag reads the union's stored fields.
    // A generated tag enum is auto-numbered, so each tag value equals its position.
    const owner = ip.indexToKey(enum_ty).enum_type.id.generatedUnion();
    if (ip.unionFields(owner)) |f| {
        for (f.names, 0..) |field_name, idx| {
            if (try sema.matchEnumField(enum_ty, tag_ty, match, field_name, @intCast(idx), @intCast(idx))) |m| return m;
        }
        return null;
    }
    // `enterContainer` unwraps the generated tag enum to its owner union: the
    // union's ZIR frame, and the union as `this_type` so a `closure_get` in an
    // explicit `union(enum(T))` tag resolves.
    const cf = try sema.enterContainer(enum_ty, "union tag field");
    defer cf.restore(sema);
    const decl = sema.zir.getUnionDecl(cf.decl_inst);
    var it = decl.iterateFields();
    while (it.next()) |field| {
        const field_name = try ip.getOrPutString(sema.gpa, sema.zir.nullTerminatedString(field.name));
        if (try sema.matchEnumField(enum_ty, tag_ty, match, field_name, field.idx, field.idx)) |m| return m;
    }
    return null;
}

/// The integer tag type of an enum -- an explicit `enum(T)` backing (or a
/// `union(enum(T))`'s explicit `T` for a generated tag enum), else the auto
/// smallest-unsigned. Mirrors `LoadedEnumType.int_tag_type`, and is the single
/// source `enumFieldScan`/`generatedTagScan` draw the tag type from for coercion.
pub fn enumIntTagTypeOf(sema: *Sema, enum_ty: InternPool.Index) Error!InternPool.Index {
    const et = sema.intern_pool.indexToKey(enum_ty).enum_type;
    // A reified enum has no ZIR; its tag type is stored. (A declared enum's fields
    // are not yet resolved when this is called during resolution, so it reads ZIR.)
    if (sema.intern_pool.enumFields(enum_ty)) |f| return f.int_tag_type;
    // The generated tag enum of a reified union is auto-numbered (the union has no
    // ZIR, and a reified union carries no explicit int tag type).
    const gu = et.id.generatedUnion();
    if (gu != .none and sema.intern_pool.unionFields(gu) != null) {
        return try sema.enumIntTagType(try sema.unionFieldCount(gu));
    }
    const cf = try sema.enterContainer(enum_ty, "enum tag type");
    defer cf.restore(sema);
    // A generated tag enum reads its explicit `T` from the owner union's decl;
    // a declared enum reads its `enum(T)` backing from its own.
    if (et.id.generatedUnion() != .none) {
        const decl = sema.zir.getUnionDecl(cf.decl_inst);
        return if (decl.kind == .tagged_enum_explicit)
            (try sema.resolveInlineBody(decl.arg_type_body.?, cf.decl_inst)).index
        else
            try sema.enumIntTagType(@intCast(decl.field_names.len));
    }
    const decl = sema.zir.getEnumDecl(cf.decl_inst);
    return if (decl.tag_type_body) |body|
        (try sema.resolveInlineBody(body, cf.decl_inst)).index
    else
        try sema.enumIntTagType(@intCast(decl.field_names.len));
}

/// Whether an enum is non-exhaustive (has a `_` field). A union's generated tag
/// enum is always exhaustive. Mirrors `LoadedEnumType.nonexhaustive`.
fn enumNonexhaustive(sema: *Sema, enum_ty: InternPool.Index) Error!bool {
    const et = sema.intern_pool.indexToKey(enum_ty).enum_type;
    if (et.id.generatedUnion() != .none) return false;
    // A reified enum has no ZIR; its mode is stored.
    if (sema.intern_pool.enumFields(enum_ty)) |f| return f.nonexhaustive;
    const cf = try sema.enterContainer(enum_ty, "enum mode");
    defer cf.restore(sema);
    return sema.zir.getEnumDecl(cf.decl_inst).nonexhaustive;
}

/// If `(field_name, value)` matches `match`, build the `enum_tag` result. The
/// value is coerced to `tag_ty`, whose range check rejects an out-of-range tag as
/// the compiler's field-value coercion does. Shared by declared and generated
/// enum field iteration.
fn matchEnumField(
    sema: *Sema,
    enum_ty: InternPool.Index,
    tag_ty: InternPool.Index,
    match: EnumMatch,
    field_name: InternPool.NullTerminatedString,
    field_index: u32,
    value: i128,
) Error!?EnumMatchResult {
    const ip = sema.intern_pool;
    const matched = switch (match) {
        .name => |n| field_name == n,
        .value => |v| value == v,
        .index => |i| field_index == i,
    };
    if (!matched) return null;
    const int = try sema.enumTagIntValue(tag_ty, value);
    return .{
        .tag = .{ .index = try ip.internEnumTag(.{ .ty = enum_ty, .int = int }) },
        .name = field_name,
        .index = field_index,
    };
}

/// The interned integer value `value` as an enum's `tag_ty` -- the `int` an
/// `enum_tag` holds. Shared by `matchEnumField` and `resolveEnumFields`.
fn enumTagIntValue(sema: *Sema, tag_ty: InternPool.Index, value: i128) Error!InternPool.Index {
    const i64v = std.math.cast(i64, value) orelse {
        try sema.writer.writeAll("enum: tag value out of supported range\n");
        return error.AnalysisFail;
    };
    const raw = try sema.intern_pool.internInt(.{ .ty = .comptime_int_type, .storage = .{ .i64 = i64v } });
    return (try sema.coerceValueToType(.{ .index = raw }, tag_ty, "enum tag")).index;
}

/// The field index of `name`, or null if the enum has no such field. Mirrors the
/// compiler's `Type.enumFieldIndex` / `LoadedEnumType.nameIndex`.
fn enumFieldIndex(sema: *Sema, enum_ty: InternPool.Index, name: InternPool.NullTerminatedString) Error!?u32 {
    return if (try sema.enumFieldScan(enum_ty, .{ .name = name })) |m| m.index else null;
}

/// The field index whose tag value is `tag` (an `enum_tag` or bare `int` value),
/// or null if none. Mirrors `Type.enumTagFieldIndex` / `LoadedEnumType.tagValueIndex`.
fn enumTagFieldIndex(sema: *Sema, enum_ty: InternPool.Index, tag: Value) Error!?u32 {
    const int = switch (sema.intern_pool.indexToKey(tag.index)) {
        .enum_tag => |et| et.int,
        .int => tag.index,
        else => unreachable,
    };
    return if (try sema.enumFieldScan(enum_ty, .{ .value = sema.intAsI128(int).? })) |m| m.index else null;
}

/// The name of field `index`. Mirrors `Type.enumFieldName`.
fn enumFieldName(sema: *Sema, enum_ty: InternPool.Index, index: u32) Error!?InternPool.NullTerminatedString {
    return if (try sema.enumFieldScan(enum_ty, .{ .index = index })) |m| m.name else null;
}

/// The `enum_tag` value of field `index`. Mirrors `pt.enumValueFieldIndex`.
pub fn enumValueFieldIndex(sema: *Sema, enum_ty: InternPool.Index, index: u32) Error!?Value {
    return if (try sema.enumFieldScan(enum_ty, .{ .index = index })) |m| m.tag else null;
}

/// The `enum_tag` value of the field named `name` (`E.b`, `.b`), or null. Combines
/// `enumFieldIndex` + `enumValueFieldIndex`; kept as one call for the common lookup.
fn enumTagByName(sema: *Sema, enum_ty: InternPool.Index, name: InternPool.NullTerminatedString) Error!?Value {
    return if (try sema.enumFieldScan(enum_ty, .{ .name = name })) |m| m.tag else null;
}

/// The integer value of an `int` Key as `i128`, or null if it is not an integer
/// or does not fit. Used to read explicit enum tag values and `@enumFromInt` args.
fn intAsI128(sema: *Sema, index: InternPool.Index) ?i128 {
    const key = sema.intern_pool.indexToKey(index);
    if (key != .int) return null;
    return switch (key.int.storage) {
        .u64 => |v| @as(i128, v),
        .i64 => |v| @as(i128, v),
        .big_int => |b| b.toInt(i128) catch null,
    };
}

/// `enum_from_int lhs, rhs`: `@enumFromInt(n)` -- the enum tag whose integer value
/// is `n`. `lhs` is the destination enum type, `rhs` the integer. A value with no
/// matching tag is rejected as the compiler's `enumHasInt` check does. Mirrors
/// zirEnumFromInt's exhaustive comptime arm.
fn evalEnumFromInt(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    const bin = sema.zir.extraData(Zir.Inst.Bin, pl_node.payload_index).data;
    const dest_ty = (try sema.resolveRef(bin.lhs)).index;
    if (ip.indexToKey(dest_ty) != .enum_type) {
        try sema.writer.writeAll("@enumFromInt: destination is not an enum\n");
        return error.AnalysisFail;
    }
    const operand = try sema.resolveRef(bin.rhs);
    const value = sema.intAsI128(operand.index) orelse {
        try sema.writer.writeAll("@enumFromInt: operand is not an integer\n");
        return error.AnalysisFail;
    };
    // Mirror `intToEnum`: the value must name a field (`tagValueIndex`), then take
    // that field's canonical tag (`enumValueFieldIndex`).
    if (try sema.enumTagFieldIndex(dest_ty, operand)) |field_index|
        return (try sema.enumValueFieldIndex(dest_ty, field_index)).?;
    const name = ip.stringSlice(ip.indexToKey(dest_ty).enum_type.name);
    try sema.writer.print("enum '{s}' has no tag with value '{d}'\n", .{ name, value });
    return error.AnalysisFail;
}

/// `int_from_bool` (`@intFromBool(b)`): `false` -> `0`, `true` -> `1`, as `u1`.
/// Mirrors zirIntFromBool.
fn evalIntFromBool(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const operand = try sema.resolveRef(sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node.operand);
    const u1_type = try sema.intern_pool.get(.{ .int_type = .{ .signedness = .unsigned, .bits = 1 } });
    return .{ .index = try sema.intern_pool.internInt(.{
        .ty = u1_type,
        .storage = .{ .u64 = @intFromBool(operand.index == .bool_true) },
    }) };
}

/// `enum_literal` (`.foo`): a standalone literal carrying only the name (type
/// `enum_literal_type`); it coerces to a concrete enum/union on use, e.g. in
/// `e == .foo`. Mirrors zirEnumLiteral.
fn evalEnumLiteral(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const bytes = sema.zir.instructions.items(.data)[@intFromEnum(inst)].str_tok.get(sema.zir);
    const name = try sema.intern_pool.getOrPutString(sema.gpa, bytes);
    return .{ .index = try sema.intern_pool.get(.{ .enum_literal = name }) };
}

/// `decl_literal` / `decl_literal_no_coerce`: `.name` resolved against the known
/// result type (`const e: E = .b`) -- a declaration if the type has one by that
/// name, otherwise an enum/union tag. `decl_literal` then coerces the member to
/// the result type (so a union tag becomes the union value). A bare literal with
/// no result type is an `enum_literal` value (see `evalEnumLiteral`).
fn evalDeclLiteral(sema: *Sema, inst: Zir.Inst.Index, comptime do_coerce: bool) Error!?Value {
    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.Field, pl_node.payload_index).data;
    const name = try sema.intern_pool.getOrPutString(sema.gpa, sema.zir.nullTerminatedString(extra.field_name_start));
    const orig_ty = (try sema.resolveRef(extra.lhs)).index;
    return try sema.analyzeDeclLiteral(orig_ty, name, do_coerce);
}

/// Resolve `.name` against the result type `orig_ty`, then (for `decl_literal`)
/// coerce the member to it. Mirrors zirDeclLiteral -> analyzeDeclLiteral: peel any
/// error-union / optional / single-pointer wrapper; a generic-poison, enum-literal,
/// or error-set result type degrades to a plain `enum_literal` value.
fn analyzeDeclLiteral(sema: *Sema, orig_ty: InternPool.Index, name: InternPool.NullTerminatedString, comptime do_coerce: bool) Error!Value {
    const ip = sema.intern_pool;
    if (orig_ty == .generic_poison_type) return .{ .index = try ip.get(.{ .enum_literal = name }) };
    var ty = orig_ty;
    while (true) switch (ip.indexToKey(ty)) {
        .error_union_type => |eu| ty = eu.payload_type,
        .opt_type => |child| ty = child,
        .ptr_type => |p| if (p.flags.size == .one) {
            ty = p.child;
        } else break,
        .error_set_type => return .{ .index = try ip.get(.{ .enum_literal = name }) },
        .simple_type => |s| if (s == .enum_literal) return .{ .index = try ip.get(.{ .enum_literal = name }) } else break,
        else => break,
    };
    const uncoerced = try sema.fieldValOnType(ty, name);
    return if (do_coerce) try sema.coerceValueToType(uncoerced, orig_ty, "decl literal") else uncoerced;
}

/// Type-level member access `T.name`: a namespace declaration takes precedence,
/// then an enum tag or a union's tag-enum value. Mirrors the `.type` case of the
/// compiler's `fieldVal` (union/enum/struct arms).
fn fieldValOnType(sema: *Sema, ty: InternPool.Index, name: InternPool.NullTerminatedString) Error!Value {
    switch (sema.intern_pool.indexToKey(ty)) {
        .enum_type => {
            if (try sema.containerDeclByName(ty, name)) |v| return v;
            if (try sema.enumTagByName(ty, name)) |v| return v;
            return sema.failBadMemberAccess(ty, name);
        },
        .union_type => {
            if (try sema.containerDeclByName(ty, name)) |v| return v;
            if (try sema.enumTagByName(try sema.unionTagEnumType(ty), name)) |v| return v;
            return sema.failBadMemberAccess(ty, name);
        },
        .struct_type => {
            if (try sema.containerDeclByName(ty, name)) |v| return v;
            return sema.failBadMemberAccess(ty, name);
        },
        else => {
            try sema.writer.writeAll("decl literal: result type is not a container with members\n");
            return error.AnalysisFail;
        },
    }
}

/// `int_from_enum operand`: the integer tag of an enum value. Mirrors
/// zirIntFromEnum's comptime arm -- returns the `enum_tag`'s stored int (already
/// typed as the enum's integer tag type).
fn evalIntFromEnum(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    const operand = try sema.resolveRef(un_node.operand);
    const key = sema.intern_pool.indexToKey(operand.index);
    if (key != .enum_tag) {
        try sema.writer.writeAll("@intFromEnum: operand is not an enum value\n");
        return error.AnalysisFail;
    }
    return .{ .index = key.enum_tag.int };
}

/// `tag_name operand`: `@tagName(e)` -- the name of an enum value's tag as a
/// `*const [N:0]u8` string literal. Finds the tag by its integer value, then
/// builds the string from the field name. Mirrors zirTagName's comptime arm,
/// which returns `addNullTerminatedStrLit(field_name)`.
fn evalTagName(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    const operand = try sema.resolveRef(un_node.operand);
    // Mirrors zirTagName's operand switch: an enum tag names itself; a union names
    // its active field via its tag, but only if the union is tagged.
    const tag: InternPool.Key.EnumTag = switch (ip.indexToKey(operand.index)) {
        .enum_tag => |et| et,
        .un => |uv| blk: {
            if (!try sema.unionIsTagged(uv.ty)) {
                try sema.writer.writeAll("union '");
                try Type.print(.fromIndex(uv.ty), ip, sema.writer);
                try sema.writer.writeAll("' is untagged\n");
                return error.AnalysisFail;
            }
            break :blk ip.indexToKey(uv.tag).enum_tag;
        },
        else => {
            try sema.writer.writeAll("expected enum or union; found '");
            try Type.print(operand.typeOf(ip), ip, sema.writer);
            try sema.writer.writeAll("'\n");
            return error.AnalysisFail;
        },
    };
    // A valid enum_tag always names one of its type's fields: value -> index -> name.
    const field_index = (try sema.enumTagFieldIndex(tag.ty, .{ .index = tag.int })).?;
    const name = (try sema.enumFieldName(tag.ty, field_index)).?;
    return try sema.internStringLiteral(ip.stringSlice(name));
}

/// Whether a union is tagged (`union(enum)` / `union(T)` / `union(enum(T))`), so
/// its active field is a first-class enum tag reachable by `@tagName`/`switch`.
/// Read from the union decl's ZIR `kind`, mirroring `unionTagType != null`
/// (`tag_usage == .tagged`). Auto/extern/packed unions are untagged.
fn unionIsTagged(sema: *Sema, union_ty: InternPool.Index) Error!bool {
    // A reified union has no ZIR; it is tagged iff it stores an explicit tag enum.
    if (sema.intern_pool.unionFields(union_ty)) |f| return f.tag_type != .none;
    const ut = sema.intern_pool.indexToKey(union_ty).union_type;
    const frame = try sema.enterSourceZir(ut.id.sourceZirId(), "union kind");
    defer frame.restore(sema);
    return switch (sema.zir.getUnionDecl(ut.id.declInst()).kind) {
        .tagged_explicit, .tagged_enum, .tagged_enum_explicit => true,
        .auto, .@"extern", .@"packed", .packed_explicit => false,
    };
}

/// A struct type's declared field count (read straight from its source ZIR's
/// `field_names`; no field bodies are evaluated).
pub fn structFieldCount(sema: *Sema, struct_ty: InternPool.Index) Error!u32 {
    // A reified struct has no ZIR; its field count comes from stored fields.
    if (sema.intern_pool.structFields(struct_ty)) |f| return @intCast(f.names.len);
    const st = sema.intern_pool.indexToKey(struct_ty).struct_type;
    const decl_inst = st.id.declInst();
    const frame = try sema.enterSourceZir(st.id.sourceZirId(), "struct field count");
    defer frame.restore(sema);
    const zir = sema.zir;
    // An anonymous struct stores its field count on the `struct_init_anon` item.
    if (zir.instructions.items(.tag)[@intFromEnum(decl_inst)] == .struct_init_anon) {
        const pl_node = zir.instructions.items(.data)[@intFromEnum(decl_inst)].pl_node;
        return zir.extraData(Zir.Inst.StructInitAnon, pl_node.payload_index).data.fields_len;
    }
    return @intCast(zir.getStructDecl(decl_inst).field_names.len);
}

/// `field_ptr` (`&object.field`, and the intermediate in a chain like `l.a.x`)
/// and `struct_init_field_ptr` (the pointer each field is stored through during
/// `.{ ... }` init): both resolve the field by name and build the auto-layout
/// `.field` projection into `object_ptr`. The compiler routes both through
/// `fieldPtr`, differing in an `initializing` flag: a pointer to a union field is
/// only valid for the active field unless it is being initialized, so a
/// non-initializing pointer to an inactive field is rejected here (as
/// `unionFieldPtr`'s comptime branch does). The field pointer inherits the parent
/// pointer's constness. Mirrors zirFieldPtr / zirStructInitFieldPtr.
fn evalFieldPtr(sema: *Sema, inst: Zir.Inst.Index, comptime initializing: bool) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);
    const ip = sema.intern_pool;
    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.Field, pl_node.payload_index).data;
    const name = try ip.getOrPutString(sema.gpa, sema.zir.nullTerminatedString(extra.field_name_start));
    const object_ptr = try sema.resolveRef(extra.lhs);
    return sema.fieldPtr(object_ptr, name, initializing);
}

/// `&object.name` shared by `field_ptr` / `struct_init_field_ptr` (name from ZIR)
/// and `field_ptr_named` (`&@field(object, "name")` / an `@field` lvalue, name
/// from a comptime string). Mirrors the compiler's shared `fieldPtr`. `object_ptr`
/// is the resolved operand pointer; `initializing` skips the active-field check on
/// a union field being written.
fn fieldPtr(sema: *Sema, object_ptr: Value, name: InternPool.NullTerminatedString, comptime initializing: bool) Error!?Value {
    const ip = sema.intern_pool;
    const parent_ty = ip.indexToKey(object_ptr.index).ptr.ty;
    const object_ty = ip.indexToKey(parent_ty).ptr_type.child;
    // Zig dereferences a single pointer during field lookup: `p.field` where `p`
    // is a `*T` (so the operand is `*const *T`) reads the field on `T`. Mirrors
    // `fieldPtr`'s `is_pointer_to` / `inner_ty` -- load the operand to the inner
    // pointer and use that as the field-pointer base; a non-pointer container is
    // unchanged (`inner_ty == object_ty`, `base_ptr == object_ptr`).
    const is_pointer_to = ip.indexToKey(object_ty) == .ptr_type and
        ip.indexToKey(object_ty).ptr_type.flags.size == .one;
    const container_ty = if (is_pointer_to) ip.indexToKey(object_ty).ptr_type.child else object_ty;
    const base_ptr = if (is_pointer_to) try sema.loadValue(object_ptr) else object_ptr;
    const attr_ptr_ty = if (is_pointer_to) object_ty else parent_ty;

    // Namespace decl access on a type (`&S.decl`, e.g. the intermediate `S.A` in
    // `S.A.y`): the operand points at a type value. Resolve the decl in that type's
    // namespace and return a pointer to it. Mirrors fieldPtr's `.type` arm, whose
    // `namespaceLookupRef` yields a `decl_ref`.
    if (container_ty == .type_type) {
        const container = try sema.loadValue(base_ptr);
        if (try sema.containerDeclByName(container.index, name)) |decl_val|
            return try sema.materializeConstPtr(decl_val);
        return sema.failBadMemberAccess(container.index, name);
    }

    // `.array` / `.pointer` (slice) fieldPtr arms: `arr.len`, `slice.len`/`.ptr`
    // taken by pointer. These fields are computed values, not `.field` projections,
    // so return a `*const` to the value (the compiler's `uavRef` / field ptr).
    switch (ip.indexToKey(container_ty)) {
        .array_type => |at| {
            if (name.eqlSlice("len", ip))
                return try sema.materializeConstPtr(.{ .index = try ip.internInt(.{ .ty = .usize_type, .storage = .{ .u64 = at.len } }) });
            return sema.failNoMember(container_ty, name);
        },
        .ptr_type => |ptr_ty| if (ptr_ty.flags.size == .slice) {
            const s = ip.indexToKey((try sema.loadValue(base_ptr)).index).slice;
            if (name.eqlSlice("len", ip)) return try sema.materializeConstPtr(.{ .index = s.len });
            if (name.eqlSlice("ptr", ip)) return try sema.materializeConstPtr(.{ .index = s.ptr });
            return sema.failNoMember(container_ty, name);
        },
        else => {},
    }

    const fld: FieldInfo = switch (ip.indexToKey(container_ty)) {
        .union_type => blk: {
            const f = (try sema.unionFieldByName(container_ty, name)) orelse
                return sema.failBadUnionFieldAccess(container_ty, name);
            // Reading a pointer to an inactive union field is illegal; the
            // compiler checks the active tag at the pointer op unless the field
            // is being initialized. The union value is comptime-known here.
            if (!initializing) _ = try sema.loadUnionField((try sema.loadValue(base_ptr)).index, f.index);
            break :blk f;
        },
        .struct_type => (try sema.structFieldByName(container_ty, name)) orelse
            return sema.failBadStructFieldAccess(container_ty, name),
        // A by-pointer field access on a non-aggregate, non-type operand. Mirrors
        // fieldPtr's fallthrough "type '{f}' does not support field access".
        else => {
            try sema.writer.writeAll("type '");
            try Type.print(.fromIndex(container_ty), ip, sema.writer);
            try sema.writer.writeAll("' does not support field access\n");
            return error.AnalysisFail;
        },
    };
    // An anonymous struct's field carries no ZIR-resolvable type (`.none`); read
    // it from the stored aggregate element instead.
    const field_ty = if (fld.ty != .none) fld.ty else blk: {
        const agg = ip.indexToKey((try sema.loadValue(base_ptr)).index).aggregate;
        break :blk Value.typeOf(.{ .index = InternPool.aggregateElementAt(agg, fld.index) }, ip).index;
    };
    const field_ptr_ty = try ip.internPtrType(.{
        .child = field_ty,
        .flags = .{ .size = .one, .is_const = ip.indexToKey(attr_ptr_ty).ptr_type.flags.is_const },
    });
    return .{ .index = try ip.internPtr(.{
        .ty = field_ptr_ty,
        .base_addr = .{ .field = .{ .base = base_ptr.index, .index = fld.index } },
        .byte_offset = 0,
    }) };
}

/// The container a type is declared in (`.none` at the top level), the REPL's
/// stand-in for `Namespace.parent`. Read from the container type's `parent` field.
fn containerParent(sema: *Sema, container_ty: InternPool.Index) InternPool.Index {
    return switch (sema.intern_pool.indexToKey(container_ty)) {
        .struct_type => |st| st.parent,
        .enum_type => |et| et.parent,
        .union_type => |ut| ut.parent,
        else => .none,
    };
}

/// Look up a member declaration by name in a container type's namespace (`P.id`)
/// and return its evaluated value. Iterates the container decl's declarations in
/// its source ZIR (swapped in for a cross-line type, as `structFieldByName`
/// does), matching by name. Returns null if no declaration matches. Unnamed
/// members (`comptime` blocks, tests) are skipped. Works for any nominal
/// container -- struct, union, or enum -- since all share a decl namespace (the
/// compiler's namespace lookup is container-kind agnostic).
/// The ZIR coordinates of a container type's namespace (`struct`/`union`/`enum`),
/// or null for a non-container. Shared by the decl-lookup walkers so the
/// container-kind switch lives in one place.
const ContainerNamespace = struct { source_zir_id: u32, decl_inst: Zir.Inst.Index };
fn containerNamespace(sema: *Sema, container_ty: InternPool.Index) ?ContainerNamespace {
    return switch (sema.intern_pool.indexToKey(container_ty)) {
        // A reified struct has an empty namespace (no source decls).
        .struct_type => |st| switch (st.id) {
            .declared => |d| .{ .source_zir_id = d.source_zir_id, .decl_inst = d.decl_inst },
            else => null,
        },
        // A reified union has an empty namespace (no source decls).
        .union_type => |ut| switch (ut.id) {
            .declared => |d| .{ .source_zir_id = d.source_zir_id, .decl_inst = d.decl_inst },
            else => null,
        },
        // A generated tag enum resolves through the owner union's namespace; a
        // reified enum has an empty namespace (no source decls).
        .enum_type => |et| switch (et.id) {
            .declared => |d| .{ .source_zir_id = d.source_zir_id, .decl_inst = d.decl_inst },
            .generated_union_tag => |owner| sema.containerNamespace(owner),
            .reified => null,
        },
        else => null,
    };
}

fn containerDeclByName(sema: *Sema, container_ty: InternPool.Index, name: InternPool.NullTerminatedString) Error!?Value {
    const ns = sema.containerNamespace(container_ty) orelse return null;
    // Decls are not stored on the type; intern each decl name as we scan and
    // compare interned handles against the query, as the compiler's namespace
    // lookup does.
    const frame = try sema.enterSourceZir(ns.source_zir_id, "container decl");
    defer frame.restore(sema);
    for (sema.zir.typeDecls(ns.decl_inst)) |decl_inst| {
        const unwrapped = sema.zir.getDeclaration(decl_inst);
        if (unwrapped.name == .empty) continue;
        if ((try sema.intern_pool.getOrPutString(sema.gpa, sema.zir.nullTerminatedString(unwrapped.name))) != name) continue;
        const value_body = unwrapped.value_body orelse return null;
        // Evaluate the member with this container as `@This()` (e.g. a method's
        // `self: @This()` parameter type resolves to it).
        const saved_this = sema.this_type;
        sema.this_type = container_ty;
        defer sema.this_type = saved_this;
        // A member function collects its parameters into `block.params`, which
        // the enclosing evaluation may itself be filling (a parameter type that
        // calls another function, `fn use(b: dep(u8))`). Give this member a fresh
        // list so its `func` drains only its own params; restore the caller's.
        const saved_params = sema.block.params;
        sema.block.params = .empty;
        defer {
            sema.block.params.deinit(sema.gpa);
            sema.block.params = saved_params;
        }
        // `results` is keyed by bare instruction index, so a decl body in another
        // file collides with the caller's in-flight instructions at the same index.
        // Evaluate it against a fresh map, as `evalCall` does for a function body.
        const saved_results = sema.results;
        sema.results = .empty;
        defer {
            sema.results.deinit(sema.gpa);
            sema.results = saved_results;
        }
        // Resolve the type annotation (`const x: T = ...`) before the value and
        // bind it to the declaration instruction, then coerce, exactly as
        // `bindValueDecl` does: a result-located init -- a `decl_literal` like
        // `.gnu`, whose `coerced_ty` AstGen sets to `decl_inst.toRef()` -- reads
        // `%decl` for its type. Both bodies break to the declaration instruction.
        const declared_type: ?InternPool.Index = if (unwrapped.type_body) |tb| blk: {
            const t = (try sema.resolveInlineBody(tb, decl_inst)).index;
            try sema.results.put(sema.gpa, decl_inst, .{ .index = t });
            break :blk t;
        } else null;
        const raw_value = try sema.resolveInlineBody(value_body, decl_inst);
        return if (declared_type) |dest_ty|
            try sema.coerceValueToType(raw_value, dest_ty, "decl")
        else
            raw_value;
    }
    return null;
}

/// `field_ptr_load`: read `object.field` -- a struct field when `object` is a
/// struct value, or a member declaration when it is a struct type (the split
/// below). Mirrors zirFieldPtrLoad -> fieldPtrLoad.
fn evalFieldPtrLoad(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);
    const ip = sema.intern_pool;
    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.Field, pl_node.payload_index).data;
    // Intern the field name once (as `zirFieldVal` does), then reuse the handle for
    // every arm below -- the `len` check, the namespace lookups, and diagnostics.
    const name = try ip.getOrPutString(sema.gpa, sema.zir.nullTerminatedString(extra.field_name_start));
    const object = try sema.loadValue(try sema.resolveRef(extra.lhs));
    return sema.fieldPtrLoad(object, name);
}

/// `object.name` read shared by `field_ptr_load` (name from ZIR) and
/// `field_ptr_named_load` (`@field`, name from a comptime string). Mirrors the
/// compiler's `fieldPtrLoad`, which both `zirFieldPtrLoad` and
/// `zirFieldPtrNamedLoad` call. `object` is the already-loaded operand value.
fn fieldPtrLoad(sema: *Sema, object: Value, name: InternPool.NullTerminatedString) Error!?Value {
    const ip = sema.intern_pool;

    // Mirror fieldVal, which switches on the object's type tag. A *type* used as a
    // value (`S.decl`, `E.tag`) is the `.type` arm: resolve the name in the type's
    // namespace. We look decls/tags up from the type's ZIR rather than a persistent
    // Namespace (no Zcu).
    switch (ip.indexToKey(object.index)) {
        .struct_type, .union_type => {
            if (try sema.containerDeclByName(object.index, name)) |v| return v;
            return sema.failBadMemberAccess(object.index, name);
        },
        .enum_type => {
            if (try sema.enumTagByName(object.index, name)) |v| return v;
            return sema.failBadMemberAccess(object.index, name);
        },
        else => {},
    }

    // Otherwise `object` is a data value; dispatch on its (inner) type, auto-
    // dereferencing a single pointer to the aggregate it addresses -- as fieldVal
    // does for a single-pointer-to-array/struct. A string literal is a
    // `*const [N:0]u8`, and `ref`-before-field nests one more pointer, so follow
    // the chain.
    var inner = object;
    while (ip.indexToKey(inner.index) == .ptr) inner = try sema.loadValue(inner);
    const inner_ty = inner.typeOf(ip).toIndex();
    switch (ip.indexToKey(inner_ty)) {
        // `.array` arm: only `len` (the array length as a `usize`).
        .array_type => |at| {
            if (name.eqlSlice("len", ip))
                return .{ .index = try ip.internInt(.{ .ty = .usize_type, .storage = .{ .u64 = at.len } }) };
            return sema.failNoMember(inner_ty, name);
        },
        // `.@"struct"` arm: the named field of a struct value.
        .struct_type => {
            const fld = (try sema.structFieldByName(inner_ty, name)) orelse
                return sema.failBadStructFieldAccess(inner_ty, name);
            return .{ .index = InternPool.aggregateElementAt(ip.indexToKey(inner.index).aggregate, fld.index) };
        },
        // `.@"union"` arm: the accessed field must be the active one, mirroring
        // unionFieldVal's `active_index == field_index` check.
        .union_type => {
            const fld = (try sema.unionFieldByName(inner_ty, name)) orelse
                return sema.failBadUnionFieldAccess(inner_ty, name);
            return try sema.loadUnionField(inner.index, fld.index);
        },
        // `.pointer` arm (a slice): `.len` / `.ptr` read from the slice value.
        .ptr_type => |ptr_ty| {
            if (ptr_ty.flags.size == .slice) {
                const s = ip.indexToKey(inner.index).slice;
                if (name.eqlSlice("len", ip)) return .{ .index = s.len };
                if (name.eqlSlice("ptr", ip)) return .{ .index = s.ptr };
            }
            return sema.failNoMember(inner_ty, name);
        },
        else => return sema.failNoMember(inner_ty, name),
    }
}

/// The compiler's `"no member named '{f}' in '{f}'"` diagnostic for a field
/// access on a type that has no such member (an array without `len`/`ptr`, or a
/// non-aggregate). Mirrors fieldVal's array/else arms.
fn failNoMember(sema: *Sema, ty: InternPool.Index, name: InternPool.NullTerminatedString) Error {
    sema.writer.print("no member named '{s}' in '", .{sema.intern_pool.stringSlice(name)}) catch |e| return e;
    Type.print(.fromIndex(ty), sema.intern_pool, sema.writer) catch |e| return e;
    sema.writer.writeAll("'\n") catch |e| return e;
    return error.AnalysisFail;
}

/// `field_ptr_named_load` (`@field(object, "name")`): the same read as
/// `field_ptr_load`, but the field name is a comptime string operand rather than
/// a ZIR-encoded name. Mirrors zirFieldPtrNamedLoad -> fieldPtrLoad.
fn evalFieldPtrNamedLoad(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);
    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.FieldNamed, pl_node.payload_index).data;
    const field_name = try sema.resolveConstStringIntern(extra.field_name);
    const object = try sema.loadValue(try sema.resolveRef(extra.lhs));
    return sema.fieldPtrLoad(object, field_name);
}

/// `field_ptr_named` (`&@field(object, "name")`, or `@field(...) = v`): the
/// pointer form of `@field`, name from a comptime string. Mirrors
/// zirFieldPtrNamed -> fieldPtr.
fn evalFieldPtrNamed(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);
    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.FieldNamed, pl_node.payload_index).data;
    const field_name = try sema.resolveConstStringIntern(extra.field_name);
    const object_ptr = try sema.resolveRef(extra.lhs);
    return sema.fieldPtr(object_ptr, field_name, false);
}

/// Resolve a comptime string operand -- the name arg of `@field` / `@hasField` /
/// `@hasDecl` -- to an interned name. The operand is a comptime `[]const u8`: a
/// string literal (`*const [N:0]u8`) or a slice of one. Unwrap to the backing
/// `u8` aggregate, a start offset, and a length (as `aggregateElement` does),
/// then read each byte. Mirrors the compiler's `resolveConstStringIntern`, which
/// coerces the operand to `[]const u8` and interns its bytes.
fn resolveConstStringIntern(sema: *Sema, ref: Zir.Inst.Ref) Error!InternPool.NullTerminatedString {
    const ip = sema.intern_pool;
    var agg = try sema.resolveRef(ref);
    var start: u64 = 0;
    var slice_len: ?u64 = null;
    if (ip.indexToKey(agg.index) == .slice) {
        const s = ip.indexToKey(agg.index).slice;
        slice_len = try sema.resolveUsizeInt(.{ .index = s.len }, "string len");
        const ptr = ip.indexToKey(s.ptr).ptr;
        if (ptr.base_addr == .arr_elem) {
            start = ptr.base_addr.arr_elem.index;
            agg = .{ .index = ptr.base_addr.arr_elem.base };
        } else {
            agg = .{ .index = s.ptr };
        }
    }
    while (ip.indexToKey(agg.index) == .ptr) agg = try sema.loadValue(agg);
    const key = ip.indexToKey(agg.index);
    const arr = if (key == .aggregate) ip.indexToKey(key.aggregate.ty) else key;
    if (key != .aggregate or arr != .array_type or arr.array_type.child != .u8_type) {
        try sema.writer.writeAll("expected a comptime string\n");
        return error.AnalysisFail;
    }
    const len: usize = @intCast(slice_len orelse arr.array_type.len);
    const bytes = try sema.gpa.alloc(u8, len);
    defer sema.gpa.free(bytes);
    for (bytes, 0..) |*b, i| {
        const elem = InternPool.aggregateElementAt(key.aggregate, start + i);
        b.* = @intCast(ip.indexToKey(elem).int.storage.u64);
    }
    return try ip.getOrPutString(sema.gpa, bytes);
}

/// `has_field` (`@hasField(T, "name")`): whether type `T` has a field named
/// `name`. Mirrors zirHasField's type-tag switch: struct/union/enum by field or
/// tag name, tuple by numeric index, array `len`, slice `ptr`/`len`. A type that
/// has no fields at all is the compiler's "does not support '@hasField'" error.
fn evalHasField(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    const bin = sema.zir.extraData(Zir.Inst.Bin, pl_node.payload_index).data;
    const ty = try sema.resolveDestType(bin.lhs, "@hasField");
    const field_name = try sema.resolveConstStringIntern(bin.rhs);
    // The REPL's `*FieldByName` / `enumTagByName` are the lazy-from-ZIR analogue of
    // the compiler's `nameIndex` (a field is a field, never a decl). A non-slice
    // pointer, and every non-container type, fall through the switch to the fail --
    // matching zirHasField, where only a slice pointer is answerable.
    const has_field = hf: {
        switch (ip.indexToKey(ty)) {
            .ptr_type => |ptr_type| switch (ptr_type.flags.size) {
                .slice => {
                    if (field_name.eqlSlice("ptr", ip)) break :hf true;
                    if (field_name.eqlSlice("len", ip)) break :hf true;
                    break :hf false;
                },
                else => {},
            },
            .tuple_type => |tuple| {
                const field_index = field_name.toUnsigned(ip) orelse break :hf false;
                break :hf field_index < tuple.types.len;
            },
            .struct_type => break :hf (try sema.structFieldByName(ty, field_name)) != null,
            .union_type => break :hf (try sema.unionFieldByName(ty, field_name)) != null,
            .enum_type => break :hf (try sema.enumTagByName(ty, field_name)) != null,
            .array_type => break :hf field_name.eqlSlice("len", ip),
            else => {},
        }
        try sema.writer.writeAll("type '");
        try Type.print(.fromIndex(ty), ip, sema.writer);
        try sema.writer.writeAll("' does not support '@hasField'\n");
        return error.AnalysisFail;
    };
    return .{ .index = if (has_field) .bool_true else .bool_false };
}

/// `has_decl` (`@hasDecl(T, "name")`): whether container type `T` declares a
/// member named `name`. Mirrors zirHasDecl -> a namespace lookup; the REPL's
/// single-file model has no visibility restriction, so a present name is
/// accessible. Scans decl names without evaluating them (as `lookupInNamespace`
/// does), so a decl whose body would fail still counts as present.
fn evalHasDecl(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    const bin = sema.zir.extraData(Zir.Inst.Bin, pl_node.payload_index).data;
    const container_type = try sema.resolveDestType(bin.lhs, "@hasDecl");
    const decl_name = try sema.resolveConstStringIntern(bin.rhs);
    // checkNamespaceType: `@hasDecl` requires a container (the REPL has no opaque).
    // A non-namespace type is a compile error, not a `false` result.
    if (sema.containerNamespace(container_type) == null) {
        try sema.writer.writeAll("expected struct, enum, union, or opaque; found '");
        try Type.print(.fromIndex(container_type), sema.intern_pool, sema.writer);
        try sema.writer.writeAll("'\n");
        return error.AnalysisFail;
    }
    // getNamespace + lookupInNamespace; `.accessible` is always true in the REPL's
    // single-file model, so a present name is the answer.
    return .{ .index = if (try sema.containerHasDecl(container_type, decl_name)) .bool_true else .bool_false };
}

/// Whether container type `container_ty` declares a member named `name`, by
/// scanning decl names only (no value evaluation). Mirrors the compiler's
/// namespace name lookup; the value-resolving counterpart is `containerDeclByName`.
fn containerHasDecl(sema: *Sema, container_ty: InternPool.Index, name: InternPool.NullTerminatedString) Error!bool {
    const ns = sema.containerNamespace(container_ty) orelse return false;
    const frame = try sema.enterSourceZir(ns.source_zir_id, "container decl");
    defer frame.restore(sema);
    for (sema.zir.typeDecls(ns.decl_inst)) |decl_inst| {
        const unwrapped = sema.zir.getDeclaration(decl_inst);
        if (unwrapped.name == .empty) continue;
        if ((try sema.intern_pool.getOrPutString(sema.gpa, sema.zir.nullTerminatedString(unwrapped.name))) == name) return true;
    }
    return false;
}

/// Write `elem` into slot `index` of an aggregate alloc's value (a struct field
/// or an array element), returning the new aggregate. An `undef` alloc
/// materialises an all-`undef` aggregate of the right arity first; an existing
/// aggregate is copied with one element replaced. Whole-aggregate read-modify-
/// write -- the compiler mutates in place via `MutableValue`, which this
/// comptime-only evaluator does not model.
fn setAggregateElement(
    sema: *Sema,
    old: Value,
    agg_ty: InternPool.Index,
    index: u32,
    elem: Value,
) Error!Value {
    const ip = sema.intern_pool;
    // A struct doesn't store its field count in the type (resolved from ZIR); an
    // array/vector/tuple does (`aggregateElementCount`).
    const count = if (ip.indexToKey(agg_ty) == .struct_type)
        try sema.structFieldCount(agg_ty)
    else
        @as(u32, @intCast(ip.aggregateElementCount(agg_ty)));
    const elems = try sema.gpa.alloc(InternPool.Index, count);
    defer sema.gpa.free(elems);
    const old_key = ip.indexToKey(old.index);
    if (old_key == .aggregate) {
        for (elems, 0..) |*e, i| e.* = InternPool.aggregateElementAt(old_key.aggregate, i);
    } else {
        @memset(elems, .undef);
    }
    elems[index] = elem.index;
    return .{ .index = try ip.internAggregate(.{ .ty = agg_ty, .storage = .{ .elems = elems } }) };
}

/// Store `value` into the slot addressed by an element/field pointer, rebuilding
/// the enclosing aggregate. The base may itself be an element/field pointer
/// (`outer[i][j]`, `s.a.b`), so recurse until the backing comptime alloc is
/// reached and update its value. Whole-aggregate read-modify-write, the recursive
/// analogue of `setStructField` -- the compiler mutates in place via
/// `MutableValue` / `beginComptimePtrMutation`, which this evaluator does not model.
fn storeElement(sema: *Sema, ptr: InternPool.Key.Ptr, value: Value) Error!void {
    const ip = sema.intern_pool;
    const f = switch (ptr.base_addr) {
        .field, .arr_elem => |f| f,
        else => unreachable, // only element/field pointers reach here
    };
    const base_ptr = ip.indexToKey(f.base).ptr;
    const agg_ty = ip.indexToKey(base_ptr.ty).ptr_type.child;
    // A union stores only the active field's payload, so a store through
    // `&u.field` makes that field active -- a fresh `.un` with the field's tag --
    // rather than a positional slot update. Mirrors `evalUnionInit`'s tag lookup.
    if (ip.indexToKey(agg_ty) == .union_type) {
        const tag_enum = try sema.unionTagEnumType(agg_ty);
        const tag = (try sema.enumValueFieldIndex(tag_enum, @intCast(f.index))).?;
        const new_union = Value{ .index = try ip.internUnion(.{ .ty = agg_ty, .tag = tag.index, .val = value.index }) };
        try sema.storePointee(base_ptr, new_union);
        return;
    }
    // A store through a pointer-to-array writes the value's consecutive elements as
    // a sub-array of the parent -- the counterpart of `loadValue`'s sub-array read,
    // and the REPL analog of storing a `[len]T` through `storePtrVal`. The same
    // `load_one_ty == base_ty` gate keeps a `*T` element pointer a single-slot write.
    if (ptr.base_addr == .arr_elem) sub_array: {
        const child_ty = ip.indexToKey(ptr.ty).ptr_type.child;
        const sub = indexableInfo(ip, child_ty) orelse break :sub_array;
        const parent_info = indexableInfo(ip, agg_ty) orelse break :sub_array;
        if (parent_info.child != sub.child) break :sub_array;
        var parent = try sema.loadValue(.{ .index = f.base });
        const count = ip.aggregateElementCount(child_ty);
        var i: u64 = 0;
        while (i < count) : (i += 1) {
            const elem = try sema.aggregateElementByIndex(value, i);
            parent = try sema.setAggregateElement(parent, agg_ty, @intCast(f.index + i), elem);
        }
        try sema.storePointee(base_ptr, parent);
        return;
    }
    const parent = try sema.loadValue(.{ .index = f.base });
    const new_parent = try sema.setAggregateElement(parent, agg_ty, @intCast(f.index), value);
    try sema.storePointee(base_ptr, new_parent);
}

/// Write `value` as the entire pointee of `ptr`, rebuilding every enclosing
/// aggregate or optional up to the backing comptime alloc. The store-tail shared
/// by `store_node`, `storeElement`, and the optional-payload store: a field/array
/// pointer rebuilds its aggregate (`storeElement`), an optional-payload pointer
/// rebuilds the optional around the new payload and stores it back through the
/// base, and an alloc pointer updates the slot. A declaration pointer is runtime
/// storage this evaluator cannot mutate.
fn storePointee(sema: *Sema, ptr: InternPool.Key.Ptr, value: Value) Error!void {
    const ip = sema.intern_pool;
    switch (ptr.base_addr) {
        .comptime_alloc => (try sema.lookupComptimeAlloc(ptr)).val = value,
        .field, .arr_elem => try sema.storeElement(ptr, value),
        .opt_payload => |base| {
            // Take the optional's type from the base pointer, not the current value:
            // an initializing store writes into an `undef` optional that carries none.
            const opt_ty = ip.indexToKey(ip.indexToKey(base).ptr.ty).ptr_type.child;
            const new_opt = Value{ .index = try ip.internOpt(.{ .ty = opt_ty, .val = value.index }) };
            try sema.storePointee(ip.indexToKey(base).ptr, new_opt);
        },
        .eu_payload => |base| {
            // Rebuild the error union as a non-error carrying the new payload, then
            // store it back through the base. The union type comes from the base
            // pointer (an initializing store writes into an `undef` union).
            const eu_ty = ip.indexToKey(ip.indexToKey(base).ptr.ty).ptr_type.child;
            const new_eu = Value{ .index = try ip.internErrorUnion(.{ .ty = eu_ty, .val = .{ .payload = value.index } }) };
            try sema.storePointee(ip.indexToKey(base).ptr, new_eu);
        },
        .nav, .uav => {
            try sema.writer.writeAll("unable to evaluate comptime expression: store through a pointer to a declaration\n");
            return error.AnalysisFail;
        },
    }
}

/// `opt_eu_base_ptr_init`: project a result-location pointer down to the payload
/// base it will initialize. A `*?T`/`*E!T` (or nested `*?E!T`) becomes a `*T`, so
/// the following `struct_init_field_ptr` sees the struct/union, not the wrapper.
/// Mirrors `optEuBasePtrInit`'s loop; a plain struct/array is already the base and
/// falls straight out. Both projections initialize (skip the null/error check).
fn evalOptEuBasePtrInit(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);
    const ip = sema.intern_pool;
    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    var base_ptr = try sema.resolveRef(un_node.operand);
    while (true) switch (ip.indexToKey(ip.indexToKey(base_ptr.typeOf(ip).toIndex()).ptr_type.child)) {
        .opt_type => base_ptr = try sema.optPayloadPtr(base_ptr, true),
        .error_union_type => base_ptr = try sema.errUnionPayloadPtr(base_ptr, true),
        else => break,
    };
    return base_ptr;
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

    // A union's single field-pointer store already set the active tag, so there is
    // nothing to default; more than one initializer is the "multiple active fields"
    // error. Mirrors `validateUnionInit`.
    if (ip.indexToKey(struct_ty) == .union_type) {
        if (body.len != 1) {
            try sema.writer.writeAll("cannot initialize multiple union fields at once; unions can only have one active field\n");
            return error.AnalysisFail;
        }
        return null;
    }

    // The interned names explicitly initialized, to test each declared field
    // against by handle. Interned from the current ZIR before the swap below.
    const stored = try sema.gpa.alloc(InternPool.NullTerminatedString, body.len);
    defer sema.gpa.free(stored);
    for (body, stored) |field_ptr, *n| {
        const fp = sema.zir.extraData(Zir.Inst.Field, datas[@intFromEnum(field_ptr)].pl_node.payload_index).data;
        n.* = try ip.getOrPutString(sema.gpa, sema.zir.nullTerminatedString(fp.field_name_start));
    }

    // Fill each declared field the init omitted with its default, as
    // `finishStructInit` does.
    const count = try sema.structFieldCount(struct_ty);
    var i: u32 = 0;
    while (i < count) : (i += 1) {
        const name = (try sema.structFieldNameAt(struct_ty, i)).?;
        if (std.mem.indexOfScalar(InternPool.NullTerminatedString, stored, name) != null) continue;
        const default = try sema.structFieldDefault(struct_ty, name);
        if (default == .none) {
            try sema.writer.print("missing struct field: {s}\n", .{ip.stringSlice(name)});
            return error.AnalysisFail;
        }
        const alloc = try sema.lookupComptimeAlloc(ip.indexToKey(object_ptr.index).ptr);
        alloc.val = try sema.setAggregateElement(alloc.val, struct_ty, i, .{ .index = default });
    }
    return null;
}

/// `validate_struct_init_ty` / `validate_struct_init_result_ty`: check that the
/// named type accepts `T{ ... }` init syntax; the following `struct_init` builds
/// the value. Returns void. Mirrors zirValidateStructInitTy -- a struct or union
/// passes (the same ZIR drives `T{ .a = x }` for both). The result-ty form peels
/// optional/error-union wrappers first, so `@as(?S, .{...})` validates against `S`.
fn evalValidateStructInitTy(sema: *Sema, inst: Zir.Inst.Index, comptime is_result_ty: bool) Error!?Value {
    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    const ty = (try sema.resolveRef(un_node.operand)).index;
    const struct_ty = if (is_result_ty) Type.fromIndex(ty).optEuBaseType(sema.intern_pool).index else ty;
    switch (sema.intern_pool.indexToKey(struct_ty)) {
        .struct_type, .union_type => return null,
        else => {
            try sema.writer.writeAll("struct init: type does not support struct initialization syntax\n");
            return error.AnalysisFail;
        },
    }
}

/// `struct_init_field_type`: the type of `container_type`'s field `name`, used
/// to coerce that field's init expression. Mirrors zirStructInitFieldType, which
/// peels optional/error-union wrappers off `container_type` before resolving the
/// field against the payload struct or union.
fn evalStructInitFieldType(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const datas = sema.zir.instructions.items(.data);
    const ft = sema.zir.extraData(Zir.Inst.FieldType, datas[@intFromEnum(inst)].pl_node.payload_index).data;
    const container_ty = Type.fromIndex((try sema.resolveRef(ft.container_type)).index).optEuBaseType(sema.intern_pool).index;
    const name = try sema.intern_pool.getOrPutString(sema.gpa, sema.zir.nullTerminatedString(ft.name_start));
    const field_ty = switch (sema.intern_pool.indexToKey(container_ty)) {
        .struct_type => ((try sema.structFieldByName(container_ty, name)) orelse
            return sema.failBadStructFieldAccess(container_ty, name)).ty,
        .union_type => ((try sema.unionFieldByName(container_ty, name)) orelse
            return sema.failBadUnionFieldAccess(container_ty, name)).ty,
        else => {
            try sema.writer.writeAll("struct init: initializer type is not a struct or union\n");
            return error.AnalysisFail;
        },
    };
    return .{ .index = field_ty };
}

/// `struct_init`: `T{ .a = x, .b = y }` -- explicit-type struct initialization,
/// returning the value directly. Each item pairs a `struct_init_field_type`
/// instruction (naming the container type and field) with an init expression;
/// the struct type is read from the first item. Fields left unwritten take their
/// declared default, or are a missing-field error. Mirrors zirStructInit's
/// struct arm + finishStructInit; the union arm builds a union value from the
/// single initialized field. `struct_init_ref` (`is_ref`) is `struct_init` +
/// `ref`: a pointer to the fresh value. The `.{ ... }` result-location form goes
/// through `validate_ptr_struct_init`.
fn evalStructInit(sema: *Sema, inst: Zir.Inst.Index, comptime is_ref: bool) Error!?Value {
    const ip = sema.intern_pool;
    const datas = sema.zir.instructions.items(.data);
    const extra = sema.zir.extraData(Zir.Inst.StructInit, datas[@intFromEnum(inst)].pl_node.payload_index);

    const first = sema.zir.extraData(Zir.Inst.StructInit.Item, extra.end).data;
    const first_ft = sema.zir.extraData(Zir.Inst.FieldType, datas[@intFromEnum(first.field_type)].pl_node.payload_index).data;
    // The result type may wrap the container in `?`/`E!` (from `@as(?S, .{...})`);
    // build against the peeled base and coerce the finished value back at the end.
    const result_ty = (try sema.resolveRef(first_ft.container_type)).index;
    const struct_ty = Type.fromIndex(result_ty).optEuBaseType(ip).index;
    switch (ip.indexToKey(struct_ty)) {
        .struct_type => {},
        .union_type => return try sema.evalUnionInit(struct_ty, result_ty, inst, is_ref),
        else => {
            try sema.writer.writeAll("struct init: initializer type is not a struct or union\n");
            return error.AnalysisFail;
        },
    }

    const count = try sema.structFieldCount(struct_ty);
    const elems = try sema.gpa.alloc(InternPool.Index, count);
    defer sema.gpa.free(elems);
    @memset(elems, .none); // .none marks a field not yet written

    // Bind each explicitly-written field to its coerced init value. The inits
    // are resolved in the caller's ZIR; field names/types come from the struct's
    // source ZIR (`structFieldByName` swaps to it internally).
    var extra_index = extra.end;
    for (0..extra.data.fields_len) |_| {
        const item = sema.zir.extraData(Zir.Inst.StructInit.Item, extra_index);
        extra_index = item.end;
        const ft = sema.zir.extraData(Zir.Inst.FieldType, datas[@intFromEnum(item.data.field_type)].pl_node.payload_index).data;
        const name = try ip.getOrPutString(sema.gpa, sema.zir.nullTerminatedString(ft.name_start));
        const field = (try sema.structFieldByName(struct_ty, name)) orelse
            return sema.failBadStructFieldAccess(struct_ty, name);
        const raw = try sema.resolveRef(item.data.init);
        elems[field.index] = (try sema.coerceValueToType(raw, field.ty, "struct field")).index;
    }

    return try sema.finishStructInit(struct_ty, result_ty, elems, is_ref);
}

/// `struct_init`'s union arm: `U{ .a = x }` builds a union value. A union init
/// names exactly one field; the tag is that field's `enum_tag` in the union's tag
/// enum (looked up by name, so a `union(E)` uses `E`'s value for the field), the
/// payload the coerced init. Mirrors zirStructInit's union branch: unionFieldIndex
/// -> enumValueFieldIndex tag -> internUnion.
fn evalUnionInit(sema: *Sema, union_ty: InternPool.Index, result_ty: InternPool.Index, inst: Zir.Inst.Index, comptime is_ref: bool) Error!Value {
    const ip = sema.intern_pool;
    const datas = sema.zir.instructions.items(.data);
    const extra = sema.zir.extraData(Zir.Inst.StructInit, datas[@intFromEnum(inst)].pl_node.payload_index);
    if (extra.data.fields_len != 1) {
        try sema.writer.writeAll("union initialization expects exactly one field\n");
        return error.AnalysisFail;
    }

    const item = sema.zir.extraData(Zir.Inst.StructInit.Item, extra.end).data;
    const ft = sema.zir.extraData(Zir.Inst.FieldType, datas[@intFromEnum(item.field_type)].pl_node.payload_index).data;
    const name = try ip.getOrPutString(sema.gpa, sema.zir.nullTerminatedString(ft.name_start));
    const field = (try sema.unionFieldByName(union_ty, name)) orelse
        return sema.failBadUnionFieldAccess(union_ty, name);

    const raw = try sema.resolveRef(item.init);
    const val = (try sema.coerceValueToType(raw, field.ty, "union field")).index;

    const tag_enum = try sema.unionTagEnumType(union_ty);
    const tag_index = (try sema.enumFieldIndex(tag_enum, name)) orelse
        return sema.failBadMemberAccess(tag_enum, name);
    // A `union(E)` requires its fields to match `E`'s in order and count; the
    // active-field check reads the tag's position, so a mismatch would misreport
    // it. Mirrors the compiler's union/tag field-order validation.
    if (tag_index != field.index) {
        try sema.writer.writeAll("union field order does not match tag enum field order\n");
        return error.AnalysisFail;
    }
    if ((try sema.enumFieldCount(tag_enum)) != try sema.unionFieldCount(union_ty)) {
        try sema.writer.writeAll("enum field missing from union\n");
        return error.AnalysisFail;
    }
    const tag = (try sema.enumValueFieldIndex(tag_enum, tag_index)).?;
    const value: Value = .{ .index = try ip.internUnion(.{ .ty = union_ty, .tag = tag.index, .val = val }) };
    const final = if (result_ty == union_ty) value else try sema.coerceValueToType(value, result_ty, "union init");
    return if (is_ref) try sema.materializeConstPtr(final) else final;
}

/// `struct_init_empty`: `T{}` -- every field takes its default. Just the
/// zero-explicit-field case of `struct_init`. Mirrors zirStructInitEmpty's
/// struct arm (array/vector/union arms not built here).
fn evalStructInitEmpty(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    const struct_ty = (try sema.resolveRef(un_node.operand)).index;
    if (sema.intern_pool.indexToKey(struct_ty) != .struct_type) {
        try sema.writer.writeAll("struct init: type does not support struct initialization syntax\n");
        return error.AnalysisFail;
    }
    return try sema.structInitEmpty(struct_ty);
}

/// The value of `T{}` for a struct: every field takes its declared default (or a
/// missing-field error). Mirrors the compiler's `structInitEmpty`; shared by the
/// typed (`struct_init_empty`) and result-typed (`struct_init_empty_result`)
/// forms.
fn structInitEmpty(sema: *Sema, struct_ty: InternPool.Index) Error!Value {
    const count = try sema.structFieldCount(struct_ty);
    const elems = try sema.gpa.alloc(InternPool.Index, count);
    defer sema.gpa.free(elems);
    @memset(elems, .none);
    return try sema.finishStructInit(struct_ty, struct_ty, elems, false);
}

/// `struct_init_empty_result` / `struct_init_empty_ref_result`: `.{}` whose type
/// comes from the surrounding result type. An untyped (generic-poison) operand --
/// `.{}` bound to an `anytype` parameter -- is the empty tuple; a concrete struct
/// fills its defaults. The result type may wrap the container in `?`/`E!` (from
/// `@as(?S, .{})`), so build against the peeled base and coerce back. Mirrors
/// zirStructInitEmptyResult; the `is_ref` variant returns a `*const` to the value.
fn evalStructInitEmptyResult(sema: *Sema, inst: Zir.Inst.Index, comptime is_ref: bool) Error!?Value {
    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    const init_ty = try sema.resolveDestType(un_node.operand, "struct init");
    if (init_ty == .generic_poison_type) {
        const empty: Value = .{ .index = .empty_tuple };
        return if (is_ref) try sema.materializeConstPtr(empty) else empty;
    }
    const obj_ty = Type.fromIndex(init_ty).optEuBaseType(sema.intern_pool).index;
    const base: Value = switch (sema.intern_pool.indexToKey(obj_ty)) {
        .struct_type, .tuple_type => try sema.structInitEmpty(obj_ty),
        .array_type, .vector_type => try sema.arrayInitEmpty(obj_ty),
        .union_type => {
            try sema.writer.writeAll("union initializer must initialize one field\n");
            return error.AnalysisFail;
        },
        else => {
            try sema.writer.writeAll("struct init: type does not support struct initialization syntax\n");
            return error.AnalysisFail;
        },
    };
    const value = if (init_ty == obj_ty) base else try sema.coerceValueToType(base, init_ty, "struct init");
    return if (is_ref) try sema.materializeConstPtr(value) else value;
}

/// The value of `T{}` for an array or vector: valid only at length 0, yielding the
/// empty aggregate. Mirrors the compiler's `arrayInitEmpty`.
fn arrayInitEmpty(sema: *Sema, obj_ty: InternPool.Index) Error!Value {
    const key = sema.intern_pool.indexToKey(obj_ty);
    const arr_len = switch (key) {
        .array_type => |at| at.len,
        .vector_type => |vt| vt.len,
        else => unreachable,
    };
    if (arr_len != 0) {
        try sema.writer.print("expected {d} {s} elements; found 0\n", .{ arr_len, if (key == .array_type) "array" else "vector" });
        return error.AnalysisFail;
    }
    return .{ .index = try sema.intern_pool.internAggregate(.{ .ty = obj_ty, .storage = .{ .elems = &.{} } }) };
}

/// Complete a struct init: fill each unwritten field (`elems[i] == .none`) from
/// its declared default -- evaluated in the struct's source ZIR -- or report a
/// missing-field error, then intern the aggregate. The value is built at the
/// peeled `struct_ty` and coerced to `result_ty` -- identical unless the result
/// type wraps the struct in `?`/`E!`, where the coercion re-wraps it. `is_ref`
/// returns a `*const` pointer to the finished (wrapped) value. The
/// finishStructInit analog shared by both the explicit-field and empty forms.
fn finishStructInit(sema: *Sema, struct_ty: InternPool.Index, result_ty: InternPool.Index, elems: []InternPool.Index, comptime is_ref: bool) Error!Value {
    const ip = sema.intern_pool;
    // Each unwritten field takes its declared default, resolved by the same pass
    // `@typeInfo` uses (`structFieldDefault`), kept off the field-access path.
    for (elems, 0..) |*elem, i| {
        if (elem.* != .none) continue;
        const name = (try sema.structFieldNameAt(struct_ty, @intCast(i))).?;
        const default = try sema.structFieldDefault(struct_ty, name);
        if (default == .none) {
            try sema.writer.print("missing struct field: {s}\n", .{ip.stringSlice(name)});
            return error.AnalysisFail;
        }
        elem.* = default;
    }

    const value: Value = .{ .index = try ip.internAggregate(.{ .ty = struct_ty, .storage = .{ .elems = elems } }) };
    const final = if (result_ty == struct_ty) value else try sema.coerceValueToType(value, result_ty, "struct init");
    return if (is_ref) try sema.materializeConstPtr(final) else final;
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

/// Give a constant value an address as a `*const T` -- `&"str"`, `&[_]T{...}`,
/// `ref` (a pointer to an inline temporary), the namespace-access intermediate
/// in `S.A.y`. The compiler types these `*const` at natural alignment too;
/// `decl_ref` does NOT use this (a pointer to a binding carries the decl's own
/// constness and alignment). The pointee is already interned, so bake it into a
/// `.uav` (anonymous-decl) pointer rather than an ephemeral `comptime_allocs`
/// slot: unlike a `.comptime_alloc` pointer, a uav survives past the line that
/// created it, since `comptime_allocs` is reset each analysis. Mirrors the
/// compiler storing an unnamed constant as an anon decl.
fn materializeConstPtr(sema: *Sema, value: Value) Error!Value {
    const ip = sema.intern_pool;
    const ptr_ty = try ip.internPtrType(.{
        .child = Value.typeOf(value, ip).index,
        .flags = .{ .size = .one, .is_const = true },
    });
    return .{ .index = try sema.uavPtr(ptr_ty, value.index) };
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

/// `elem_ptr_node lhs, rhs`: a pointer to element `rhs` of the array behind `lhs`
/// (`&arr[i]`, and the pointer AstGen forms for `arr[i].f`). Builds an `.arr_elem`
/// projection, as the compiler's `elemPtr` does. Mirrors zirElemPtrNode -> elemPtr.
fn evalElemPtrNode(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const bin = sema.binData(inst);
    const array_ptr = try sema.resolveRef(bin.lhs);
    const index = try sema.resolveArrayLen(bin.rhs, "elem ptr");
    return try sema.elemPtr(array_ptr, index);
}

/// `array_init_elem_ptr`: the pointer to element `index` (an immediate) of the
/// array being initialized by a `.{ ... }` result-location init; each is a
/// `store_node` target. Mirrors zirArrayInitElemPtr -> elemPtrArray.
fn evalArrayInitElemPtr(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const datas = sema.zir.instructions.items(.data);
    const extra = sema.zir.extraData(Zir.Inst.ElemPtrImm, datas[@intFromEnum(inst)].pl_node.payload_index).data;
    const array_ptr = try sema.resolveRef(extra.ptr);
    return try sema.elemPtr(array_ptr, extra.index);
}

/// Build a single-element pointer to element `index` of the array behind
/// `array_ptr` (an `.arr_elem` projection into the no-layout aggregate). Shared by
/// `elem_ptr_node` (`&a[i]`) and `array_init_elem_ptr` (a `.{...}` store target).
/// Mirrors the compiler's `elemPtrArray`.
fn elemPtr(sema: *Sema, array_ptr: Value, index: u64) Error!Value {
    const ip = sema.intern_pool;
    const parent_ty = ip.indexToKey(array_ptr.index).ptr.ty;
    const child_ty = ip.indexToKey(parent_ty).ptr_type.child;
    // A pointer to a slice indexes the slice's backing array (`elemPtrSlice`).
    if (ip.indexToKey(child_ty) == .ptr_type and ip.indexToKey(child_ty).ptr_type.flags.size == .slice) {
        return try sema.elemPtrSlice(array_ptr, index, child_ty);
    }
    // A vector indexes exactly like an array (`@Vector(N, T)` inits and indexes
    // through the same `array_init_elem_ptr` / `elem_ptr` ZIR), so accept both.
    const elems = indexableInfo(ip, child_ty) orelse {
        try sema.writer.writeAll("elem ptr: operand is not an array pointer\n");
        return error.AnalysisFail;
    };
    if (index >= elems.len) {
        try sema.writer.print("index {d} outside array of length {d}\n", .{ index, elems.len });
        return error.AnalysisFail;
    }
    const elem_ptr_ty = try ip.internPtrType(.{
        .child = elems.child,
        .flags = .{ .size = .one, .is_const = ip.indexToKey(parent_ty).ptr_type.flags.is_const },
    });
    return .{ .index = try ip.internPtr(.{
        .ty = elem_ptr_ty,
        .base_addr = .{ .arr_elem = .{ .base = array_ptr.index, .index = @intCast(index) } },
        .byte_offset = 0,
    }) };
}

/// Build a single-element pointer to element `index` of the slice behind
/// `slice_ptr` (whose pointee type is `slice_ty`). The slice's `ptr` field is a
/// many-pointer into a backing array; the element pointer is an `.arr_elem` into
/// that array at `start + index`, where `start` is the sub-slice offset the many-
/// pointer already carries (`a[start..]`). Mirrors the compiler's `elemPtrSlice` /
/// `Value.ptrElem`. Bounds-checks against the slice's own `len`.
fn elemPtrSlice(sema: *Sema, slice_ptr: Value, index: u64, slice_ty: InternPool.Index) Error!Value {
    const ip = sema.intern_pool;
    const slice_val = try sema.loadValue(slice_ptr);
    const s = ip.indexToKey(slice_val.index).slice;
    const len = try sema.resolveUsizeInt(.{ .index = s.len }, "slice index");
    if (index >= len) {
        try sema.writer.print("index {d} outside slice of length {d}\n", .{ index, len });
        return error.AnalysisFail;
    }
    const many = ip.indexToKey(s.ptr).ptr;
    const base: InternPool.Index, const start: u64 = if (many.base_addr == .arr_elem)
        .{ many.base_addr.arr_elem.base, many.base_addr.arr_elem.index }
    else
        .{ s.ptr, 0 };
    const elem_ptr_ty = try ip.internPtrType(.{
        .child = ip.indexToKey(slice_ty).ptr_type.child,
        .flags = .{ .size = .one, .is_const = ip.indexToKey(slice_ty).ptr_type.flags.is_const },
    });
    return .{ .index = try ip.internPtr(.{
        .ty = elem_ptr_ty,
        .base_addr = .{ .arr_elem = .{ .base = base, .index = start + index } },
        .byte_offset = 0,
    }) };
}

/// The element count and element type of an indexable homogeneous type -- an
/// array or a vector, which share `{len, child}` and index identically. Null for
/// anything else. Lets the element-access paths treat `@Vector(N, T)` as `[N]T`.
const IndexableInfo = struct { len: u64, child: InternPool.Index };
fn indexableInfo(ip: *const InternPool, ty: InternPool.Index) ?IndexableInfo {
    return switch (ip.indexToKey(ty)) {
        .array_type => |at| .{ .len = at.len, .child = at.child },
        .vector_type => |vt| .{ .len = vt.len, .child = vt.child },
        else => null,
    };
}

/// `validate_ptr_array_init`: after a `.{ ... }` array init's element stores,
/// check the number of initialized elements equals the array length. The body is
/// the list of `array_init_elem_ptr` instructions. Mirrors zirValidatePtrArrayInit's
/// array arm (sentinel handling deferred).
fn evalValidatePtrArrayInit(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    const datas = sema.zir.instructions.items(.data);
    const extra = sema.zir.extraData(Zir.Inst.Block, datas[@intFromEnum(inst)].pl_node.payload_index);
    const body = sema.zir.bodySlice(extra.end, extra.data.body_len);
    if (body.len == 0) return null;
    const first = sema.zir.extraData(Zir.Inst.ElemPtrImm, datas[@intFromEnum(body[0])].pl_node.payload_index).data;
    const array_ptr = try sema.resolveRef(first.ptr);
    const array_ty = ip.indexToKey(ip.indexToKey(array_ptr.index).ptr.ty).ptr_type.child;
    // The init target is an array or a vector (both use `array_init_elem_ptr`).
    const array_len = (indexableInfo(ip, array_ty) orelse return null).len;
    if (body.len != array_len) {
        try sema.writer.print("expected {d} array elements; found {d}\n", .{ array_len, body.len });
        return error.AnalysisFail;
    }
    return null;
}

/// The comptime slice handler all four `slice_*` ZIR tags feed. Ports
/// `analyzeSlice` (`src/Sema.zig`): `ptr_ptr` is the (double) pointer AstGen
/// produces -- a `*[N]T`, or a pointer to a slice/many-ptr loaded first. `end` is
/// null for `a[start..]` (slice to the operand's length); `by_length` means the
/// second operand is a length, so the end is `start + it`. Every operand is
/// comptime-known, so the runtime ptr-arithmetic and safety-check machinery drops.
fn analyzeSlice(sema: *Sema, ptr_ptr: Value, start: u64, end_opt: ?u64, sentinel_opt: ?Value, by_length: bool) Error!?Value {
    const ip = sema.intern_pool;
    const ptr_ptr_child = ip.indexToKey(ip.indexToKey(ptr_ptr.index).ptr.ty).ptr_type.child;

    // Resolve the operand to a backing pointer + start offset + length + element type.
    var backing: InternPool.Index = undefined;
    var base_offset: u64 = undefined;
    var len: u64 = undefined;
    var elem_ty: InternPool.Index = undefined;
    var is_const: bool = undefined;
    var ptr_sentinel: InternPool.Index = .none;
    // The out-of-bounds message names the operand as an array or a slice, matching
    // the compiler's two `analyzeSlice` diagnostics.
    var operand_is_slice = false;
    switch (ip.indexToKey(ptr_ptr_child)) {
        // `*[N]T`: slice the array directly.
        .array_type => |arr| {
            backing = ptr_ptr.index;
            base_offset = 0;
            len = arr.len;
            elem_ty = arr.child;
            is_const = ip.indexToKey(ip.indexToKey(ptr_ptr.index).ptr.ty).ptr_type.flags.is_const;
            ptr_sentinel = arr.sentinel;
        },
        .ptr_type => |inner| switch (inner.flags.size) {
            // `&*[N]T` (a string literal, `&[_]T{...}`): load to the `*[N]T`, slice that.
            .one => {
                const arr = ip.indexToKey(inner.child).array_type;
                backing = (try sema.loadValue(ptr_ptr)).index;
                base_offset = 0;
                len = arr.len;
                elem_ty = arr.child;
                is_const = inner.flags.is_const;
                ptr_sentinel = arr.sentinel;
            },
            // `&[]T`: load the slice and re-slice into the same backing.
            .slice => {
                operand_is_slice = true;
                const s = ip.indexToKey((try sema.loadValue(ptr_ptr)).index).slice;
                len = try sema.resolveUsizeInt(.{ .index = s.len }, "slice len");
                const sptr = ip.indexToKey(s.ptr).ptr;
                if (sptr.base_addr == .arr_elem) {
                    backing = sptr.base_addr.arr_elem.base;
                    base_offset = sptr.base_addr.arr_elem.index;
                } else {
                    backing = s.ptr;
                    base_offset = 0;
                }
                const s_ptr_ty = ip.indexToKey(s.ty).ptr_type;
                elem_ty = s_ptr_ty.child;
                is_const = s_ptr_ty.flags.is_const;
                ptr_sentinel = s_ptr_ty.sentinel;
            },
            else => return sema.failSliceNotArrayPtr(),
        },
        else => return sema.failSliceNotArrayPtr(),
    }

    // `a[start..]` slices to the length; `a[start..][0..n]` (by_length) ends at start+n.
    const end: u64 = if (end_opt) |e| (if (by_length) start + e else e) else len;
    // end_is_len (without the sentinel) makes a slice to the end inherit the sentinel.
    const end_is_len = end == len;

    if (start > end) {
        try sema.writer.print("start index {d} is larger than end index {d}\n", .{ start, end });
        return error.AnalysisFail;
    }
    if (end > len + @intFromBool(ptr_sentinel != .none)) {
        // The printed length excludes the sentinel; a `" +1 (sentinel)"` suffix
        // notes it is admissible as the end index when the operand is terminated.
        const sentinel_label: []const u8 = if (ptr_sentinel != .none) " +1 (sentinel)" else "";
        const kind: []const u8 = if (operand_is_slice) "slice" else "array";
        try sema.writer.print("end index {d} out of bounds for {s} of length {d}{s}\n", .{ end, kind, len, sentinel_label });
        return error.AnalysisFail;
    }

    // Result sentinel: an explicit `:S`, else inherited when slicing to the end of a
    // sentinel-terminated operand.
    const sentinel: InternPool.Index = s: {
        if (sentinel_opt) |provided| {
            try sema.checkSentinelType(elem_ty);
            const casted = try sema.coerceValueToType(provided, elem_ty, "slice sentinel");
            // The sentinel sits at index `end` of the backing; verify it matches.
            const actual = try sema.aggregateElementByIndex(try sema.loadValue(.{ .index = backing }), base_offset + end);
            if (actual.index != casted.index) {
                try sema.writer.writeAll("value in memory does not match slice sentinel\n");
                return error.AnalysisFail;
            }
            break :s casted.index;
        }
        break :s if (end_is_len) ptr_sentinel else .none;
    };

    // The new length is comptime-known (always, here), so the result is a pointer
    // to an array of that length -- `*[end-start]T` -- rather than a slice. This is
    // the `opt_new_len_val` branch of the compiler's `analyzeSlice`: it coerces the
    // advanced pointer to `*[new_len]elem_ty` and returns that.
    const result_array_ty = try ip.internArrayType(.{ .len = end - start, .child = elem_ty, .sentinel = sentinel });
    const result_ptr_ty = try ip.internPtrType(.{ .child = result_array_ty, .flags = .{ .size = .one, .is_const = is_const } });
    return .{ .index = try ip.internPtr(.{
        .ty = result_ptr_ty,
        .base_addr = .{ .arr_elem = .{ .base = backing, .index = base_offset + start } },
        .byte_offset = 0,
    }) };
}

fn failSliceNotArrayPtr(sema: *Sema) Error {
    try sema.writer.writeAll("slice: operand is not an array pointer\n");
    return error.AnalysisFail;
}

fn evalSliceStart(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const datas = sema.zir.instructions.items(.data);
    const extra = sema.zir.extraData(Zir.Inst.SliceStart, datas[@intFromEnum(inst)].pl_node.payload_index).data;
    const operand = try sema.resolveRef(extra.lhs);
    const start = try sema.resolveArrayLen(extra.start, "slice start");
    return sema.analyzeSlice(operand, start, null, null, false);
}

fn evalSliceEnd(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const datas = sema.zir.instructions.items(.data);
    const extra = sema.zir.extraData(Zir.Inst.SliceEnd, datas[@intFromEnum(inst)].pl_node.payload_index).data;
    const operand = try sema.resolveRef(extra.lhs);
    const start = try sema.resolveArrayLen(extra.start, "slice start");
    const end = try sema.resolveArrayLen(extra.end, "slice end");
    return sema.analyzeSlice(operand, start, end, null, false);
}

fn evalSliceSentinel(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const datas = sema.zir.instructions.items(.data);
    const extra = sema.zir.extraData(Zir.Inst.SliceSentinel, datas[@intFromEnum(inst)].pl_node.payload_index).data;
    const operand = try sema.resolveRef(extra.lhs);
    const start = try sema.resolveArrayLen(extra.start, "slice start");
    // `a[start.. :s]` carries no end (slices to the length); `a[start..end :s]` does.
    const end = if (extra.end == .none) null else try sema.resolveArrayLen(extra.end, "slice end");
    const sentinel = try sema.resolveRef(extra.sentinel);
    return sema.analyzeSlice(operand, start, end, sentinel, false);
}

fn evalSliceLength(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const datas = sema.zir.instructions.items(.data);
    const extra = sema.zir.extraData(Zir.Inst.SliceLength, datas[@intFromEnum(inst)].pl_node.payload_index).data;
    const operand = try sema.resolveRef(extra.lhs);
    const start = try sema.resolveArrayLen(extra.start, "slice start");
    const length = try sema.resolveArrayLen(extra.len, "slice length");
    const sentinel = if (extra.sentinel == .none) null else try sema.resolveRef(extra.sentinel);
    return sema.analyzeSlice(operand, start, length, sentinel, true);
}

/// `slice_sentinel_ty operand`: the element type a `a[start..end :s]` sentinel is
/// coerced to -- AstGen emits it as the `coerced_ty` result type of the sentinel
/// expression. The operand is the lvalue (a double pointer if it was already a
/// pointer), so peel one pointer, then take the element type per operand kind.
/// Mirrors zirSliceSentinelTy.
fn evalSliceSentinelTy(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    const datas = sema.zir.instructions.items(.data);
    const operand = try sema.resolveRef(datas[@intFromEnum(inst)].un_node.operand);
    const lhs_ptr_ty = operand.typeOf(ip);
    const lhs_ty = switch (ip.indexToKey(lhs_ptr_ty.index)) {
        .ptr_type => |pt| pt.child,
        else => {
            try sema.writer.writeAll("expected pointer, found '");
            try Type.print(lhs_ptr_ty, ip, sema.writer);
            try sema.writer.writeAll("'\n");
            return error.AnalysisFail;
        },
    };
    const sentinel_ty: InternPool.Index = switch (ip.indexToKey(lhs_ty)) {
        .array_type => |at| at.child,
        .ptr_type => |pt| switch (pt.flags.size) {
            .many, .c, .slice => pt.child,
            .one => switch (ip.indexToKey(pt.child)) {
                .array_type => |at| at.child,
                else => {
                    try sema.writer.writeAll("slice of single-item pointer cannot have sentinel\n");
                    return error.AnalysisFail;
                },
            },
        },
        else => {
            try sema.writer.writeAll("slice of non-array type '");
            try Type.print(Type.fromIndex(lhs_ty), ip, sema.writer);
            try sema.writer.writeAll("'\n");
            return error.AnalysisFail;
        },
    };
    return .{ .index = sentinel_ty };
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
    return sema.aggregateElementByIndex(array_value, try sema.resolveArrayLen(index_ref, "elem access"));
}

/// Read element `index` of an aggregate or slice value, with a bounds check.
fn aggregateElementByIndex(sema: *Sema, array_value: Value, index: u64) Error!Value {
    const ip = sema.intern_pool;
    // A slice indexes through its `ptr` into the array; its own `len` bounds it
    // (the array behind `ptr` may be longer). Unwrap to the array pointer first. A
    // sub-slice (`a[start..end]`) carries its start in the many-pointer's
    // `.arr_elem` base, so index reads land at `array[start + i]`.
    var agg = array_value;
    var slice_len: ?u64 = null;
    var start_offset: u64 = 0;
    if (ip.indexToKey(agg.index) == .slice) {
        const s = ip.indexToKey(agg.index).slice;
        slice_len = try sema.resolveUsizeInt(.{ .index = s.len }, "slice len");
        const ptr = ip.indexToKey(s.ptr).ptr;
        if (ptr.base_addr == .arr_elem) {
            start_offset = ptr.base_addr.arr_elem.index;
            agg = .{ .index = ptr.base_addr.arr_elem.base };
        } else {
            agg = .{ .index = s.ptr };
        }
    }
    // Deref a pointer operand to the aggregate it addresses. A string literal is a
    // `*const [N:0]u8`, and taking its address (`ref` before an index) nests one
    // more pointer, so follow the chain -- the compiler's elem access auto-derefs
    // a single-pointer-to-array the same way.
    while (ip.indexToKey(agg.index) == .ptr) agg = try sema.loadValue(agg);
    const agg_key = ip.indexToKey(agg.index);
    if (agg_key != .aggregate) {
        try sema.writer.writeAll("elem access: operand is not an indexable aggregate\n");
        return error.AnalysisFail;
    }
    const count = slice_len orelse ip.aggregateElementCount(agg_key.aggregate.ty);
    if (index >= count) {
        try sema.writer.print("index {d} outside array of length {d}\n", .{ index, count });
        return error.AnalysisFail;
    }
    return .{ .index = InternPool.aggregateElementAt(agg_key.aggregate, start_offset + index) };
}

/// A `@memcpy` operand must be an indexable pointer -- a slice, many/C pointer, or
/// pointer to an array. Mirrors `checkMemOperand`; returns the operand's type, or
/// null (with no diagnostic) so the caller emits the "not an indexable pointer"
/// error against the specific operand.
fn memOperandType(sema: *Sema, value: Value) ?Type {
    const ip = sema.intern_pool;
    const ty = value.typeOf(ip);
    switch (ip.indexToKey(ty.index)) {
        .ptr_type => |ptr_type| switch (ptr_type.flags.size) {
            .slice, .many, .c => return ty,
            .one => if (ip.indexToKey(ptr_type.child) == .array_type) return ty,
        },
        else => {},
    }
    return null;
}

fn failMemOperand(sema: *Sema, ty: Type) Error {
    try sema.writer.writeAll("@memcpy: type '");
    try Type.print(ty, sema.intern_pool, sema.writer);
    try sema.writer.writeAll("' is not an indexable pointer; operand must be a slice, a many pointer or a pointer to an array\n");
    return error.AnalysisFail;
}

/// The element count of a `@memcpy` operand, or null for many/C pointers (which
/// carry no length). Mirrors `indexablePtrLenOrNone`: a slice's own `len`, or a
/// pointer-to-array's array length.
fn indexableMemLen(sema: *Sema, value: Value) Error!?u64 {
    const ip = sema.intern_pool;
    switch (ip.indexToKey(value.index)) {
        .slice => |s| return try sema.resolveUsizeInt(.{ .index = s.len }, "@memcpy length"),
        .ptr => |p| return switch (ip.indexToKey(ip.indexToKey(p.ty).ptr_type.child)) {
            .array_type => |at| at.len,
            else => null, // many / C pointer
        },
        else => return null,
    }
}

/// The backing aggregate a `@memcpy` operand addresses, as `(pointer-to-backing,
/// start index)`. A slice indexes `backing[start..]` via its many-pointer's
/// `arr_elem` base; a sub-range pointer-to-array (`a[start..end]`) carries the same
/// `arr_elem` base directly; a whole-array pointer (`&a`) addresses it at offset 0.
fn memBacking(sema: *Sema, value: Value) struct { ptr: InternPool.Index, start: u64 } {
    const ip = sema.intern_pool;
    switch (ip.indexToKey(value.index)) {
        .slice => |s| {
            const many = ip.indexToKey(s.ptr).ptr;
            return switch (many.base_addr) {
                .arr_elem => |ae| .{ .ptr = ae.base, .start = ae.index },
                else => .{ .ptr = s.ptr, .start = 0 },
            };
        },
        .ptr => |p| return switch (p.base_addr) {
            .arr_elem => |ae| .{ .ptr = ae.base, .start = ae.index },
            else => .{ .ptr = value.index, .start = 0 },
        },
        else => unreachable,
    }
}

/// Whether two `@memcpy` operands alias over `elem_count` elements. Mirrors
/// `Value.doPointersOverlap`'s comptime-only branch -- compare the backing storage
/// identity and the element-index distance. The compiler's other branch keys on
/// byte offsets, which collapse to element indices in the REPL's no-layout model,
/// so this single comparison covers both.
fn doPointersOverlap(sema: *Sema, a: Value, b: Value, elem_count: u64) bool {
    const a_back = sema.memBacking(a);
    const b_back = sema.memBacking(b);
    if (a_back.ptr != b_back.ptr) return false;
    const diff = if (a_back.start >= b_back.start) a_back.start - b_back.start else b_back.start - a_back.start;
    return diff < elem_count;
}

/// `memcpy` (`@memcpy(dest, src)`): copy `src`'s elements into `dest`. Mirrors
/// zirMemcpy's comptime path -- indexable-operand + element-coercion + const-dest +
/// matching-length + aliasing checks, then the single `[len]elem` array load/store
/// (`pointerDeref` + `storePtrVal`). Returns void.
fn evalMemcpy(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    const bin = sema.binData(inst);
    const dest = try sema.resolveRef(bin.lhs);
    const src = try sema.resolveRef(bin.rhs);

    const dest_ty = sema.memOperandType(dest) orelse return sema.failMemOperand(dest.typeOf(ip));
    const src_ty = sema.memOperandType(src) orelse return sema.failMemOperand(src.typeOf(ip));

    if (dest_ty.isConstPtr(ip)) {
        try sema.writer.writeAll("@memcpy: cannot copy to constant pointer\n");
        return error.AnalysisFail;
    }

    const dest_elem = dest_ty.indexableElem(ip);
    const src_elem = src_ty.indexableElem(ip);
    const imc = try sema.coerceInMemoryAllowed(dest_elem, src_elem, false, null);
    if (imc != .ok) {
        try sema.writer.writeAll("@memcpy: pointer element type '");
        try Type.print(src_elem, ip, sema.writer);
        try sema.writer.writeAll("' cannot coerce into element type '");
        try Type.print(dest_elem, ip, sema.writer);
        try sema.writer.writeAll("'\n");
        try imc.report(sema);
        return error.AnalysisFail;
    }

    const dest_len = try sema.indexableMemLen(dest);
    const src_len = try sema.indexableMemLen(src);
    if (dest_len == null and src_len == null) {
        try sema.writer.writeAll("@memcpy: unknown copy length\n");
        return error.AnalysisFail;
    }
    if (dest_len != null and src_len != null and dest_len.? != src_len.?) {
        try sema.writer.print("@memcpy: non-matching copy lengths {d} and {d}\n", .{ dest_len.?, src_len.? });
        return error.AnalysisFail;
    }
    const len = dest_len orelse src_len.?;
    if (len == 0) return null;

    // A zero-bit element type (e.g. `void`, `u0`) copies nothing and cannot alias,
    // so it is done here -- before the aliasing check, as zirMemcpy's `zero_bit`
    // block returns early. A comptime-only element still copies. `abiSize == 0`
    // stands in for the compiler's `hasRuntimeBits`.
    if (!src_elem.comptimeOnly(ip) and (src_elem.abiSize(ip) orelse 0) == 0) return null;

    if (sema.doPointersOverlap(dest, src, len)) {
        try sema.writer.writeAll("@memcpy: arguments alias\n");
        return error.AnalysisFail;
    }

    // Copy as one array load and one array store, as zirMemcpy does: upgrade each
    // operand's backing pointer to `*[len]elem` and move the `[len]elem` value
    // whole. `loadValue`/`storePointee` handle the pointer-to-array projection --
    // `pointerDeref` and `storePtrVal` in the compiler.
    const src_back = sema.memBacking(src);
    const dest_back = sema.memBacking(dest);
    const src_arr_ptr = try ip.internPtr(.{
        .ty = try ip.internPtrType(.{
            .child = try ip.internArrayType(.{ .len = len, .child = src_elem.index }),
            .flags = .{ .size = .one, .is_const = true },
        }),
        .base_addr = .{ .arr_elem = .{ .base = src_back.ptr, .index = src_back.start } },
        .byte_offset = 0,
    });
    const array_val = try sema.loadValue(.{ .index = src_arr_ptr });
    const dest_arr_ptr: InternPool.Key.Ptr = .{
        .ty = try ip.internPtrType(.{
            .child = try ip.internArrayType(.{ .len = len, .child = dest_elem.index }),
            .flags = .{ .size = .one, .is_const = false },
        }),
        .base_addr = .{ .arr_elem = .{ .base = dest_back.ptr, .index = dest_back.start } },
        .byte_offset = 0,
    };
    try sema.storePointee(dest_arr_ptr, array_val);
    return null;
}

/// Resolve a ZIR ref to a `u64` array length or element index:
/// coerce to `usize`, then read the scalar. Lengths and indices are
/// comptime-known integers in every shape AstGen emits here.
fn resolveArrayLen(sema: *Sema, ref: Zir.Inst.Ref, op_name: []const u8) Error!u64 {
    assert(ref != .none);
    return sema.resolveUsizeInt(try sema.resolveRef(ref), op_name);
}

/// Coerce `value` to the integer type `ty` and read it as a `u64`. Mirrors the
/// compiler's `resolveInt`; `resolveUsizeInt` is the `.usize_type` case.
fn resolveInt(sema: *Sema, value: Value, ty: InternPool.Index, op_name: []const u8) Error!u64 {
    const coerced = try sema.coerceValueToType(value, ty, op_name);
    const key = sema.intern_pool.indexToKey(coerced.index);
    if (key != .int) {
        try sema.writer.print("{s}: expected an integer\n", .{op_name});
        return error.AnalysisFail;
    }
    var space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
    return key.int.storage.toBigInt(&space).toInt(u64) catch {
        try sema.writer.print("{s}: value out of range\n", .{op_name});
        return error.AnalysisFail;
    };
}

/// Coerce `value` to `usize` and read it as a `u64`. The comptime-known integers
/// that lengths, indices, and alignments are built from always fit. Shared by
/// `resolveArrayLen` (lengths / indices) and `alignmentFromValue`.
fn resolveUsizeInt(sema: *Sema, value: Value, op_name: []const u8) Error!u64 {
    return sema.resolveInt(value, .usize_type, op_name);
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
    try sema.writer.print("unsupported ZIR ref: {s}\n", .{@tagName(ref)});
    return error.AnalysisFail;
}

/// Maps a static ZIR `Ref` to the corresponding interned Value.
///
/// The compiler does this in three lines (src/Sema.zig:resolveInst):
///
///     return @enumFromInt(@intFromEnum(zir_ref));
///
/// because its `Zir.Inst.Ref` and `InternPool.Index` are kept in
/// lock-step. A non-instruction Ref *is* the matching InternPool index,
/// by construction. Pure integer identity, no lookup. The REPL's
/// well-known `Index` set mirrors the compiler's `static_keys` in the
/// same order, so every static ref's integer value is its `Index`.
fn wellKnownRefToValue(ref: Zir.Inst.Ref) ?Value {
    if (ref != .none and ref.toIndex() == null) {
        return .{ .index = @enumFromInt(@intFromEnum(ref)) };
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
    // `lookupIdentifier` walks the namespace chain innermost-first: a struct
    // member's body resolves a bare sibling name (`fn total() { return sum2(); }`)
    // against the enclosing struct before the outer (file / session) scope, so an
    // inner decl shadows a same-named outer one. Mirror that order: `this_type`
    // (the enclosing container, set around member evaluation) first, session next.
    if (sema.this_type != .none) {
        const name = try sema.intern_pool.getOrPutString(sema.gpa, sema.zir.instructions.items(.data)[@intFromEnum(inst)].str_tok.get(sema.zir));
        // Walk the enclosing-container chain (`this_type` -> its `parent` -> ...),
        // as `lookupIdentifier` walks `namespace.parent`, before the session scope.
        var container = sema.this_type;
        while (container != .none) : (container = sema.containerParent(container)) {
            if (try sema.containerDeclByName(container, name)) |val| return val;
        }
    }
    if (try sema.lookupDecl(inst, "decl_val")) |found| {
        return .{ .index = found.resolved.value };
    }
    const name = sema.zir.instructions.items(.data)[@intFromEnum(inst)].str_tok.get(sema.zir);
    try sema.writer.print("decl_val '{s}': not found in scope\n", .{name});
    return error.AnalysisFail;
}

/// `decl_ref name`: AstGen emits this (rather than `decl_val`) when the use
/// site needs a pointer -- e.g. `a[i]` takes `&a` first, or `&x`. The pointer
/// carries the binding's own constness and alignment (`var`/`const` and
/// `align(N)`), so `@TypeOf(&x)` matches the compiler. Compiler reference:
/// src/Sema.zig:zirDeclRef.
fn evalDeclRef(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    // Same innermost-first resolution as `evalDeclVal`: a bare sibling name binds
    // in the enclosing container before the session scope (`zirDeclRef` and
    // `zirDeclVal` share one `lookupIdentifier`). A sibling decl has no Nav, so a
    // pointer to it materialises a const slot holding its comptime value -- the
    // comptime analog of the compiler's `analyzeNavRef` decl pointer.
    if (sema.this_type != .none) {
        const name = try sema.intern_pool.getOrPutString(sema.gpa, sema.zir.instructions.items(.data)[@intFromEnum(inst)].str_tok.get(sema.zir));
        var container = sema.this_type;
        while (container != .none) : (container = sema.containerParent(container)) {
            if (try sema.containerDeclByName(container, name)) |val| return try sema.materializeConstPtr(val);
        }
    }
    const found = (try sema.lookupDecl(inst, "decl_ref")) orelse {
        const name = sema.zir.instructions.items(.data)[@intFromEnum(inst)].str_tok.get(sema.zir);
        try sema.writer.print("decl_ref '{s}': not found in scope\n", .{name});
        return error.AnalysisFail;
    };
    const ip = sema.intern_pool;
    const ptr_ty = try ip.internPtrType(.{
        .child = found.resolved.type,
        .flags = .{ .size = .one, .is_const = found.resolved.@"const", .alignment = found.resolved.@"align" },
    });
    const ptr_idx = try ip.internPtr(.{
        .ty = ptr_ty,
        .base_addr = .{ .nav = found.nav },
        .byte_offset = 0,
    });
    return .{ .index = ptr_idx };
}

/// Resolve a `str_tok` decl name against the session namespace to its
/// resolved Nav. Shared by `decl_val` (reads `.value`) and `decl_ref` (also
/// reads `.@"const"` / `.@"align"` for the pointer type).
const DeclLookup = struct {
    nav: InternPool.Nav.Index,
    resolved: InternPool.Nav.Resolved,
};

fn lookupDecl(sema: *Sema, inst: Zir.Inst.Index, op_name: []const u8) Error!?DeclLookup {
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
        return .{ .nav = nav_idx, .resolved = resolved };
    }

    // Not a session binding. The caller decides whether to fall back (e.g. to
    // an enclosing struct's declarations) or to report it unresolved.
    return null;
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
    return try sema.errUnionCodeVal(try sema.resolveRef(un_node.operand));
}

/// `err_union_code_ptr operand`: the error code from a pointer to an error union
/// (`*E!T`) -- load it, then extract. Mirrors `zirErrUnionCodePtr`
/// (`analyzeLoad` -> `analyzeErrUnionCode`).
fn evalErrUnionCodePtr(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);
    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    assert(un_node.operand != .none);
    return try sema.errUnionCodeVal(try sema.loadValue(try sema.resolveRef(un_node.operand)));
}

/// The error code of an error-union value whose active variant is `.err_name`,
/// as an `err` of the union's error-set type. Mirrors `analyzeErrUnionCode`.
fn errUnionCodeVal(sema: *Sema, operand_value: Value) Error!Value {
    const ip = sema.intern_pool;
    const operand_key = ip.indexToKey(operand_value.index);
    if (operand_key != .error_union) {
        try sema.writer.print("err_union_code: operand is not an error union\n", .{});
        return error.AnalysisFail;
    }
    const eu_type = ip.indexToKey(operand_key.error_union.ty).error_union_type;
    switch (operand_key.error_union.val) {
        .err_name => |name| return .{ .index = try ip.internErr(.{ .ty = eu_type.error_set_type, .name = name }) },
        .payload => {
            try sema.writer.print("err_union_code: operand carries a payload, not an error\n", .{});
            return error.AnalysisFail;
        },
    }
}

/// `err_union_payload_unsafe_ptr operand`: given a pointer to an error union
/// (`*E!T`), yield a pointer to its payload (`*T`) as an `.eu_payload` projection
/// keeping the source pointer's flags. Mirrors `analyzeErrUnionPayloadPtr`'s
/// comptime path (`initializing = false`, so a comptime-known error is rejected).
fn evalErrUnionPayloadUnsafePtr(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);
    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    assert(un_node.operand != .none);
    return try sema.errUnionPayloadPtr(try sema.resolveRef(un_node.operand), false);
}

/// Given a pointer to an error union (`*E!T`), form a pointer to its payload
/// (`*T`) as an `.eu_payload` projection keeping the source pointer's flags. When
/// `initializing` (a result-location `*E!T` about to be written), the payload is
/// being created, so skip the error check; otherwise a comptime-known error is the
/// "caught unreachable"/error-return-trace case. The `optPayloadPtr` analog for
/// error unions -- mirrors `analyzeErrUnionPayloadPtr`.
fn errUnionPayloadPtr(sema: *Sema, eu_ptr: Value, comptime initializing: bool) Error!Value {
    const ip = sema.intern_pool;
    const ptr_type = ip.indexToKey(eu_ptr.typeOf(ip).toIndex()).ptr_type;
    const eu_key = ip.indexToKey(ptr_type.child);
    if (eu_key != .error_union_type) {
        try sema.writer.writeAll("err_union_payload: pointer child is not an error union\n");
        return error.AnalysisFail;
    }
    if (!initializing) {
        const eu_val = try sema.loadValue(eu_ptr);
        if (ip.indexToKey(eu_val.index).error_union.val == .err_name) {
            try sema.writer.writeAll("err_union_payload: operand carries an error, not a payload\n");
            return error.AnalysisFail;
        }
    }
    const child_ptr_ty = try ip.internPtrType(.{ .child = eu_key.error_union_type.payload_type, .sentinel = ptr_type.sentinel, .flags = ptr_type.flags });
    return .{ .index = try ip.internPtr(.{
        .ty = child_ptr_ty,
        .base_addr = .{ .eu_payload = eu_ptr.index },
        .byte_offset = 0,
    }) };
}

/// `try operand` (`try x`): if `x` is a payload, yield it; if an error, run the
/// error branch `body` (a `ret_node` that propagates the error out of the
/// enclosing function). Mirrors `zirTry`: the operand is comptime-known, so the
/// branch is chosen directly rather than emitted as runtime control flow.
fn evalTry(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);
    const ip = sema.intern_pool;
    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.Try, pl_node.payload_index);
    const body = sema.zir.bodySlice(extra.end, extra.data.body_len);
    const err_union = try sema.resolveRef(extra.data.operand);
    const key = ip.indexToKey(err_union.index);
    if (key != .error_union) {
        try sema.writer.writeAll("expected error union type\n");
        return error.AnalysisFail;
    }
    return switch (key.error_union.val) {
        .payload => |p| .{ .index = p },
        // The body is noreturn (it returns the error); running it propagates
        // `error.ComptimeReturn`/`ComptimeBreak` up to the call boundary.
        .err_name => try sema.evalBody(body),
    };
}

/// `try_ptr operand` (`try p.*` on an addressable error union): the pointer form
/// of `try`. Load the union behind `operand` (`*E!T`); on a payload yield a `*T`
/// (`eu_payload` projection), on an error run the error branch. Mirrors `zirTryPtr`.
fn evalTryPtr(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);
    const ip = sema.intern_pool;
    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.Try, pl_node.payload_index);
    const body = sema.zir.bodySlice(extra.end, extra.data.body_len);
    const operand = try sema.resolveRef(extra.data.operand);
    const err_union = try sema.loadValue(operand);
    const key = ip.indexToKey(err_union.index);
    if (key != .error_union) {
        try sema.writer.writeAll("expected error union type\n");
        return error.AnalysisFail;
    }
    return switch (key.error_union.val) {
        .payload => try sema.errUnionPayloadPtr(operand, false),
        .err_name => try sema.evalBody(body),
    };
}

/// `ensure_err_union_payload_void operand`: reject a discarded non-void error-union
/// payload (`errfn();` without capturing the payload). Returns void. Mirrors
/// `zirEnsureErrUnionPayloadVoid`; the operand may be the union or a pointer to it.
fn evalEnsureErrUnionPayloadVoid(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);
    const ip = sema.intern_pool;
    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    const operand = try sema.resolveRef(un_node.operand);
    const operand_ty = operand.typeOf(ip);
    const eu_ty = if (operand_ty.zigTypeTag(ip) == .pointer) operand_ty.childType(ip) else operand_ty;
    if (eu_ty.zigTypeTag(ip) != .error_union) return null;
    const payload_tag = eu_ty.errorUnionPayload(ip).zigTypeTag(ip);
    if (payload_tag != .void and payload_tag != .noreturn) {
        try sema.writer.writeAll("error union payload is ignored\n");
        return error.AnalysisFail;
    }
    return null;
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
    return try sema.isNonErrVal(try sema.resolveRef(un_node.operand));
}

/// `ret_is_non_err operand`: the same non-error predicate as `is_non_err`, emitted
/// where a `return`-position `try`/`catch` needs it. Mirrors `zirRetIsNonErr`.
fn evalRetIsNonErr(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);
    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    assert(un_node.operand != .none);
    return try sema.isNonErrVal(try sema.resolveRef(un_node.operand));
}

/// `is_non_err_ptr operand`: the non-error predicate on a pointer to an error
/// union (`*E!T`) -- load it, then test. Mirrors `zirIsNonErrPtr`
/// (`analyzeLoad` -> `analyzeIsNonErr`).
fn evalIsNonErrPtr(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);
    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    assert(un_node.operand != .none);
    return try sema.isNonErrVal(try sema.loadValue(try sema.resolveRef(un_node.operand)));
}

/// The non-error predicate on an error-union value: `true` iff the variant is
/// `.payload`. Mirrors `analyzeIsNonErr` (the operand is comptime-known here).
fn isNonErrVal(sema: *Sema, operand_value: Value) Error!Value {
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
            // The indexable's element count: an array/vector/tuple aggregate, a
            // slice's `len`, or a pointer to any of those (`for (&arr)`), which
            // auto-derefs. Mirrors the compiler resolving each input's length.
            var obj = try sema.resolveRef(pair[0]);
            const ip = sema.intern_pool;
            if (ip.indexToKey(obj.index) == .slice)
                break :blk try sema.resolveUsizeInt(.{ .index = ip.indexToKey(obj.index).slice.len }, "for slice len");
            while (ip.indexToKey(obj.index) == .ptr) obj = try sema.loadValue(obj);
            const key = ip.indexToKey(obj.index);
            if (key != .aggregate) {
                try sema.writer.writeAll("for: operand is not a range or indexable\n");
                return error.AnalysisFail;
            }
            break :blk ip.aggregateElementCount(key.aggregate.ty);
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

    // A tagged union switches on its active tag; the operand's payload is what a
    // prong capture (`.a => |v|`) binds. Mirrors `switchCond` coercing a union to
    // its tag enum, with an untagged union rejected. The tag is already an
    // `enum_tag`, so the enum-literal matching below is unchanged.
    var cond = operand;
    var union_operand: ?InternPool.Key.Union = null;
    if (sema.intern_pool.indexToKey(operand.index) == .un) {
        const uv = sema.intern_pool.indexToKey(operand.index).un;
        if (!try sema.unionIsTagged(uv.ty)) {
            try sema.writer.writeAll("switch on union with no attached enum\n");
            return error.AnalysisFail;
        }
        cond = .{ .index = uv.tag };
        union_operand = uv;
    }

    const op: SwitchOperand = .{
        .value = cond,
        .ty = Value.typeOf(cond, sema.intern_pool).index,
        .err_name = operand_err_name,
    };

    try sema.validateSwitchBlock(inst, op.ty, sw);

    var extra_index: usize = sw.end;
    var it = sw.iterateCases();
    while (it.next()) |case| {
        const prong_body = sema.zir.bodySlice(extra_index, case.prong_info.body_len);
        extra_index += case.prong_info.body_len;

        var matched = try sema.matchSwitchItems(inst, case.item_infos, op, &extra_index, false);
        matched = try sema.matchSwitchRanges(inst, case.range_infos, op, &extra_index, matched);

        if (matched) {
            // `|_, tag|` binds the tag as a second capture; not modeled (the tag
            // enum is auto-generated). Reject cleanly rather than leave its
            // placeholder unbound.
            if (case.prong_info.has_tag_capture) return sema.failSwitch("tag capture");
            if (case.prong_info.capture != .none) {
                // A multi-item capture (`.a, .b => |v|`) is valid only if the
                // fields' types peer-resolve; we model the identical-type case and
                // reject differing types rather than the compiler's peer type.
                if (union_operand) |uv| {
                    if (case.item_infos.len > 1 and
                        (try sema.uniformUnionCaptureType(uv.ty, case.item_infos)) == null)
                        return sema.failSwitch("capture group across differing field types");
                }
                const payload: ?Value = if (union_operand) |uv| .{ .index = uv.val } else null;
                try sema.bindSwitchCapture(inst, sw, case.prong_info.capture, payload);
            }
            return try sema.resolveInlineBody(prong_body, inst);
        }
    }

    if (sw.else_case) |else_case| {
        if (else_case.capture != .none) return sema.failSwitch("else capture");
        return try sema.resolveInlineBody(else_case.body, inst);
    }

    try sema.writer.writeAll("switch: no matching case and no else\n");
    return error.AnalysisFail;
}

/// The subset of `zigTypeTag` that `validateSwitchBlock`'s exhaustiveness switch
/// distinguishes, computed from an InternPool key -- this evaluator has no
/// `zigTypeTag`. `usize`/`isize`/`c_*` are fixed-width ints, so they map to `.int`
/// like the compiler (not a separate "needs else" group). `.other` stands for the
/// compiler's `else => "switch on type"`.
const SwitchTypeTag = enum { @"enum", error_set, int, comptime_int, bool, void, @"fn", enum_literal, type, other };
fn switchTypeTag(ip: *const InternPool, ty: InternPool.Index) SwitchTypeTag {
    return switch (ip.indexToKey(ty)) {
        .enum_type => .@"enum",
        .error_set_type, .error_union_type => .error_set,
        .int_type => .int,
        .func_type => .@"fn",
        .simple_type => |s| switch (s) {
            .anyerror => .error_set,
            .comptime_int => .comptime_int,
            .bool => .bool,
            .void => .void,
            .type => .type,
            .enum_literal => .enum_literal,
            .usize, .isize, .c_char, .c_short, .c_ushort, .c_int, .c_uint => .int,
            .c_long, .c_ulong, .c_longlong, .c_ulonglong => .int,
            else => .other,
        },
        else => .other,
    };
}

/// Whether an error-set item type is `anyerror` (directly or as an error union's
/// set), which -- being unbounded -- can only be exhausted by an `else`.
fn isAnyerrorSet(ip: *const InternPool, item_ty: InternPool.Index) bool {
    const set_ty = switch (ip.indexToKey(item_ty)) {
        .error_union_type => |eu| eu.error_set_type,
        else => item_ty,
    };
    return set_ty == .anyerror_type;
}

/// The compiler's "else prong required when switching on type '{f}'" for a type
/// whose domain cannot be enumerated; a no-op when an `else` is present.
fn requireSwitchElse(sema: *Sema, item_ty: InternPool.Index, has_else: bool) Error!void {
    if (has_else) return;
    try sema.writer.writeAll("else prong required when switching on type '");
    try Type.print(.fromIndex(item_ty), sema.intern_pool, sema.writer);
    try sema.writer.writeAll("'\n");
    return error.AnalysisFail;
}
/// Miniature of the compiler's `RangeSet`: `i128` integer intervals with overlap
/// (duplicate) and full-range spanning tests; `[lo, hi]` inclusive.
const SwitchRangeSet = struct {
    ranges: std.ArrayListUnmanaged([2]i128) = .empty,

    fn deinit(set: *SwitchRangeSet, gpa: std.mem.Allocator) void {
        set.ranges.deinit(gpa);
    }

    /// Add `[lo, hi]`; returns true if it overlaps an existing range (a duplicate
    /// switch value), mirroring `RangeSet.addAssumeCapacity`.
    fn add(set: *SwitchRangeSet, gpa: std.mem.Allocator, lo: i128, hi: i128) Error!bool {
        for (set.ranges.items) |r| {
            if (hi >= r[0] and lo <= r[1]) return true;
        }
        try set.ranges.append(gpa, .{ lo, hi });
        return false;
    }

    /// Whether the ranges exactly cover `[min, max]` with no gaps. Ranges never
    /// overlap (`add` rejects that), so sort and check strict adjacency, mirroring
    /// `RangeSet.spans`.
    fn spans(set: *SwitchRangeSet, min: i128, max: i128) bool {
        const items = set.ranges.items;
        if (items.len == 0) return false;
        std.mem.sort([2]i128, items, {}, struct {
            fn lt(_: void, a: [2]i128, b: [2]i128) bool {
                return a[0] < b[0];
            }
        }.lt);
        if (items[0][0] != min or items[items.len - 1][1] != max) return false;
        for (items[1..], items[0 .. items.len - 1]) |cur, prev| {
            if (prev[1] + 1 != cur[0]) return false;
        }
        return true;
    }
};

/// The `[min, max]` of a fixed-width int type as `i128`, or null when the operand
/// is a target-width/`c_*` int (unbounded here) so a no-`else` switch can never
/// span it -- matching the compiler routing those through the `.int` arm.
fn intTypeBounds(ip: *const InternPool, item_ty: InternPool.Index) ?[2]i128 {
    const key = ip.indexToKey(item_ty);
    if (key != .int_type) return null;
    const it = key.int_type;
    if (it.bits == 0) return .{ 0, 0 };
    const wide = if (it.signedness == .unsigned) it.bits > 127 else it.bits > 128;
    if (wide) return null;
    return if (it.signedness == .unsigned)
        .{ 0, (@as(i128, 1) << @intCast(it.bits)) - 1 }
    else
        .{ -(@as(i128, 1) << @intCast(it.bits - 1)), (@as(i128, 1) << @intCast(it.bits - 1)) - 1 };
}

/// Mark enum field `index` as seen; returns true if it was already seen (a
/// duplicate). Mirrors writing `seen_enum_fields[field_index]`.
fn markSwitchEnumField(seen: []bool, index: u32) bool {
    if (index >= seen.len) return false;
    if (seen[index]) return true;
    seen[index] = true;
    return false;
}

/// Record a resolved (computed) case item value against the collector for its
/// type, returning true on a duplicate. Mirrors `validateSwitchItemOrRange`'s
/// per-type arms; `type_tag` selects the collector as the compiler's `zigTypeTag`
/// switch does.
fn validateSwitchItemValue(
    sema: *Sema,
    type_tag: SwitchTypeTag,
    val: Value,
    seen_enum_fields: []bool,
    seen_errors: *std.AutoHashMapUnmanaged(InternPool.NullTerminatedString, void),
    seen_sparse: *std.AutoHashMapUnmanaged(InternPool.Index, void),
    range_set: *SwitchRangeSet,
    true_seen: *bool,
    false_seen: *bool,
    void_seen: *bool,
) Error!bool {
    const ip = sema.intern_pool;
    switch (type_tag) {
        .@"enum" => {
            const tag_ty = ip.indexToKey(val.index).enum_tag.ty;
            const field_index = (try sema.enumTagFieldIndex(tag_ty, val)).?;
            return markSwitchEnumField(seen_enum_fields, field_index);
        },
        .error_set => return (try seen_errors.getOrPut(sema.gpa, ip.indexToKey(val.index).err.name)).found_existing,
        .int, .comptime_int => {
            const v = sema.intAsI128(val.index).?;
            return try range_set.add(sema.gpa, v, v);
        },
        .bool => {
            switch (ip.indexToKey(val.index).simple_value) {
                .true => {
                    if (true_seen.*) return true;
                    true_seen.* = true;
                },
                .false => {
                    if (false_seen.*) return true;
                    false_seen.* = true;
                },
                else => {},
            }
            return false;
        },
        .void => {
            if (void_seen.*) return true;
            void_seen.* = true;
            return false;
        },
        .enum_literal, .@"fn", .type => return (try seen_sparse.getOrPut(sema.gpa, val.index)).found_existing,
        .other => unreachable,
    }
}

/// Mirror of the compiler's `validateSwitchBlock`: reject a non-switchable operand
/// ("switch on type '{f}'"), collect every case's items/ranges into the same
/// per-type sets the compiler keeps (`seen_enum_fields`, `seen_errors`,
/// `seen_sparse_values`, a `range_set`, and true/false/void seen), rejecting a
/// duplicate item ("duplicate switch value"), a stray range on a non-int, and a
/// `_` prong, then check exhaustiveness per `item_ty`'s tag: all values handled or
/// an `else` ("switch must handle all possibilities"), an unbounded domain needs
/// an else ("else prong required when switching on type '{f}'"), and a
/// fully-covered switch's else is redundant ("unreachable else prong; all cases
/// already handled").
///
/// REPL deltas: no source locations, so duplicate/coverage errors are single-line
/// without the compiler's "previous value here" / per-field notes; and `_` is
/// always rejected since the evaluator does not model non-exhaustive enums.
fn validateSwitchBlock(sema: *Sema, inst: Zir.Inst.Index, item_ty: InternPool.Index, sw: Zir.UnwrappedSwitchBlock) Error!void {
    const ip = sema.intern_pool;
    const gpa = sema.gpa;
    const has_else = sw.else_case != null;

    const type_tag = switchTypeTag(ip, item_ty);
    if (type_tag == .other) {
        try sema.writer.writeAll("switch on type '");
        try Type.print(.fromIndex(item_ty), ip, sema.writer);
        try sema.writer.writeAll("'\n");
        return error.AnalysisFail;
    }

    var seen_enum_fields: []bool = &.{};
    if (type_tag == .@"enum") {
        seen_enum_fields = try gpa.alloc(bool, try sema.enumFieldCount(item_ty));
        @memset(seen_enum_fields, false);
    }
    defer gpa.free(seen_enum_fields);
    var seen_errors: std.AutoHashMapUnmanaged(InternPool.NullTerminatedString, void) = .empty;
    defer seen_errors.deinit(gpa);
    var seen_sparse: std.AutoHashMapUnmanaged(InternPool.Index, void) = .empty;
    defer seen_sparse.deinit(gpa);
    var range_set: SwitchRangeSet = .{};
    defer range_set.deinit(gpa);
    var true_seen = false;
    var false_seen = false;
    var void_seen = false;
    var saw_range = false;

    // Collect and duplicate-check every item/range, walking the same cursor the
    // matcher does (prong body, then item bodies, then range bodies).
    var extra_index: usize = sw.end;
    var it = sw.iterateCases();
    while (it.next()) |case| {
        extra_index += case.prong_info.body_len;
        for (case.item_infos) |item_info| {
            const dup = switch (item_info.unwrap()) {
                .under => {
                    try sema.writer.writeAll("'_' prong only allowed when switching on non-exhaustive enums\n");
                    return error.AnalysisFail;
                },
                .enum_literal => |n| blk: {
                    const name = try ip.getOrPutString(gpa, sema.zir.nullTerminatedString(n));
                    if (ip.indexToKey(item_ty) != .enum_type) return sema.failBadMemberAccess(item_ty, name);
                    const field_index = (try sema.enumFieldIndex(item_ty, name)) orelse
                        return sema.failBadMemberAccess(item_ty, name);
                    break :blk markSwitchEnumField(seen_enum_fields, field_index);
                },
                .error_value => |n| blk: {
                    const name = try ip.getOrPutString(gpa, sema.zir.nullTerminatedString(n));
                    break :blk (try seen_errors.getOrPut(gpa, name)).found_existing;
                },
                .body_len => |len| blk: {
                    const raw = try sema.resolveInlineBody(sema.zir.bodySlice(extra_index, len), inst);
                    extra_index += len;
                    const val = try sema.coerceValueToType(raw, item_ty, "switch case");
                    break :blk try validateSwitchItemValue(sema, type_tag, val, seen_enum_fields, &seen_errors, &seen_sparse, &range_set, &true_seen, &false_seen, &void_seen);
                },
            };
            if (dup) {
                try sema.writer.writeAll("duplicate switch value\n");
                return error.AnalysisFail;
            }
        }
        for (case.range_infos) |range_pair| {
            saw_range = true;
            const lo_len = range_pair[0].bodyLen() orelse 0;
            const hi_len = range_pair[1].bodyLen() orelse 0;
            // A range only spans for integers, whose endpoints are always computed
            // (`body_len`); on any other type the ranges-not-allowed check below
            // rejects it, so skip resolving the endpoints (they may be bodyless).
            if (type_tag == .int or type_tag == .comptime_int) {
                const lo = try sema.coerceValueToType(try sema.resolveInlineBody(sema.zir.bodySlice(extra_index, lo_len), inst), item_ty, "switch range");
                const hi = try sema.coerceValueToType(try sema.resolveInlineBody(sema.zir.bodySlice(extra_index + lo_len, hi_len), inst), item_ty, "switch range");
                if (try range_set.add(gpa, sema.intAsI128(lo.index).?, sema.intAsI128(hi.index).?)) {
                    try sema.writer.writeAll("duplicate switch value\n");
                    return error.AnalysisFail;
                }
            }
            extra_index += lo_len + hi_len;
        }
    }

    // Ranges are only meaningful for integers (validateSwitchBlock 11366).
    if (saw_range and type_tag != .int and type_tag != .comptime_int) {
        try sema.writer.writeAll("ranges not allowed when switching on type '");
        try Type.print(.fromIndex(item_ty), ip, sema.writer);
        try sema.writer.writeAll("'\n");
        return error.AnalysisFail;
    }

    // Exhaustiveness per type tag (validateSwitchBlock 11390).
    const all_handled = switch (type_tag) {
        .@"enum" => for (seen_enum_fields) |f| {
            if (!f) break false;
        } else true,
        .bool => true_seen and false_seen,
        .void => void_seen,
        .int => if (intTypeBounds(ip, item_ty)) |b| range_set.spans(b[0], b[1]) else false,
        .error_set => blk: {
            if (isAnyerrorSet(ip, item_ty)) return sema.requireSwitchElse(item_ty, has_else);
            const set_ty = switch (ip.indexToKey(item_ty)) {
                .error_union_type => |eu| eu.error_set_type,
                else => item_ty,
            };
            break :blk for (ip.indexToKey(set_ty).error_set_type.names) |set_name| {
                if (!seen_errors.contains(set_name)) break false;
            } else true;
        },
        .comptime_int, .enum_literal, .@"fn", .type => return sema.requireSwitchElse(item_ty, has_else),
        .other => unreachable,
    };
    if (has_else) {
        if (all_handled) {
            try sema.writer.writeAll("unreachable else prong; all cases already handled\n");
            return error.AnalysisFail;
        }
    } else if (!all_handled) {
        try sema.writer.writeAll("switch must handle all possibilities\n");
        return error.AnalysisFail;
    }
}

/// Bind a matched prong's capture (`|v|`) to the instruction the prong body reads
/// it through. AstGen uses the `switch_block` instruction itself as the first
/// (payload) capture ref, falling back to a separate placeholder only for a
/// second (tag) capture; so the capture inst is `payload_capture_placeholder`
/// Bind a matched prong's capture (`|v|`) to the instruction the prong body reads
/// it through. AstGen uses the `switch_block` instruction itself as the first
/// (payload) capture ref, falling back to a separate placeholder only for a
/// second (tag) capture; so the capture inst is `payload_capture_placeholder`
/// when present, else the switch inst. Only a tagged union's payload capture is
/// modeled: `by_val` binds the active payload, `by_ref` a `*const` to it.
fn bindSwitchCapture(
    sema: *Sema,
    inst: Zir.Inst.Index,
    sw: Zir.UnwrappedSwitchBlock,
    capture: Zir.Inst.SwitchBlock.ProngInfo.Capture,
    union_payload: ?Value,
) Error!void {
    const payload = union_payload orelse return sema.failSwitch("prong capture");
    const capture_inst = sw.payload_capture_placeholder.unwrap() orelse inst;
    const cap: Value = switch (capture) {
        .none => unreachable,
        .by_val => payload,
        .by_ref => try sema.materializeConstPtr(payload),
    };
    try sema.results.put(sema.gpa, capture_inst, cap);
}

/// The shared field type of a multi-item union capture prong (`.a, .b => |v|`),
/// or null if the fields' types differ (or an item is not a field literal). The
/// compiler peer-resolves them; we model only the identical-type case, so a
/// differing group is rejected by the caller ("capture group with incompatible
/// types" territory) rather than mis-typed.
fn uniformUnionCaptureType(
    sema: *Sema,
    union_ty: InternPool.Index,
    item_infos: []const Zir.Inst.SwitchBlock.ItemInfo,
) Error!?InternPool.Index {
    const ip = sema.intern_pool;
    var common: ?InternPool.Index = null;
    for (item_infos) |item_info| {
        const name_idx = switch (item_info.unwrap()) {
            .enum_literal => |n| n,
            else => return null,
        };
        const name = try ip.getOrPutString(sema.gpa, sema.zir.nullTerminatedString(name_idx));
        const fld = (try sema.unionFieldByName(union_ty, name)) orelse return null;
        if (common) |c| {
            if (c != fld.ty) return null;
        } else common = fld.ty;
    }
    return common;
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
                // The operand's error name is an interned handle; intern the ZIR
                // item name and compare handles (interned-name equality).
                if (op.err_name) |opn| {
                    const item = try sema.intern_pool.getOrPutString(sema.gpa, sema.zir.nullTerminatedString(item_err_name));
                    if (item == opn) hit = true;
                }
            },
            // A `.tag` prong on an enum switch. The compiler resolves each item via
            // `analyzeDeclLiteral` against the operand type (`resolveSwitchItem`);
            // `enumTagByName` is that same tag lookup. Compare by identity -- interned
            // tags are canonical. Like the other item kinds, an item in a prong the
            // operand never reaches is not evaluated (the evaluator returns on the
            // first matching prong), so a bad tag there is not caught, unlike the
            // compiler's whole-switch validation.
            .enum_literal => |name_idx| {
                if (hit) continue;
                if (sema.intern_pool.indexToKey(op.ty) != .enum_type) {
                    return sema.failSwitch("enum-literal case on a non-enum operand");
                }
                const name = try sema.intern_pool.getOrPutString(sema.gpa, sema.zir.nullTerminatedString(name_idx));
                const tag = (try sema.enumTagByName(op.ty, name)) orelse
                    return sema.failBadMemberAccess(op.ty, name);
                if (tag.index == op.value.index) hit = true;
            },
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

/// `.param` / `.param_comptime`: evaluate the param's type body (break_target
/// is the param inst itself, mirroring src/Sema.zig:zirParam ~9031) and push
/// onto `params` for the enclosing `.func` to drain. A `.is_generic` param --
/// its type depends on a prior comptime param (`x: T`) -- can't be resolved
/// until a call binds one, so it stores `generic_poison_type` and `evalCall`
/// re-resolves it per instantiation, exactly as the generic return type is.
fn evalParam(sema: *Sema, inst: Zir.Inst.Index, tag: Zir.Inst.Tag) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const pl_tok = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_tok;
    const extra = sema.zir.extraData(Zir.Inst.Param, pl_tok.payload_index);
    const ty: InternPool.Index = if (extra.data.type.is_generic)
        .generic_poison_type
    else
        try sema.resolveParamType(inst);
    try sema.block.params.append(sema.gpa, .{
        .ty = ty,
        .is_comptime = tag == .param_comptime,
    });
    return null;
}

/// Re-resolve a generic parameter's declared type at call time. Its type body
/// references prior comptime params, which are bound in `results` by the time
/// this runs, so `resolveInlineBody` yields the concrete type for this
/// instantiation. The parameter analogue of `resolveDeclaredRetType`.
fn resolveParamType(sema: *Sema, param_inst: Zir.Inst.Index) Error!InternPool.Index {
    const pl_tok = sema.zir.instructions.items(.data)[@intFromEnum(param_inst)].pl_tok;
    const extra = sema.zir.extraData(Zir.Inst.Param, pl_tok.payload_index);
    const body = sema.zir.bodySlice(extra.end, extra.data.type.body_len);
    return (try sema.resolveInlineBody(body, param_inst)).index;
}

/// `.param_anytype` / `.param_anytype_comptime`: an `anytype` parameter has no
/// declared type -- its type is the argument's, bound per call. Store the poison
/// marker like a generic param; `evalCall` resolves it to the argument's own
/// type at the call site. Mirrors `src/Sema.zig:zirParamAnytype`.
fn evalParamAnytype(sema: *Sema, tag: Zir.Inst.Tag) Error!?Value {
    try sema.block.params.append(sema.gpa, .{
        .ty = .generic_poison_type,
        .is_comptime = tag == .param_anytype_comptime,
    });
    return null;
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

/// Read `noalias_bits` and `is_var_args` from a `func_fancy` instruction. They
/// trail the optional cc / return-type fields in its `extra` (per the compiler's
/// `zirFuncFancy`), which `getFnInfo` does not surface; a plain `func` /
/// `func_inferred` has neither. `noalias_bits` is indexed by parameter position.
fn funcFancyExtras(sema: *Sema, inst: Zir.Inst.Index, tag: Zir.Inst.Tag) struct { noalias_bits: u32, is_var_args: bool } {
    if (tag != .func_fancy) return .{ .noalias_bits = 0, .is_var_args = false };
    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.FuncFancy, pl_node.payload_index);
    const bits = extra.data.bits;
    var extra_index = extra.end;
    if (bits.has_cc_body) {
        extra_index += 1 + sema.zir.extra[extra_index];
    } else if (bits.has_cc_ref) {
        extra_index += 1;
    }
    if (bits.has_ret_ty_body) {
        extra_index += 1 + sema.zir.extra[extra_index];
    } else if (bits.has_ret_ty_ref) {
        extra_index += 1;
    }
    return .{
        .noalias_bits = if (bits.has_any_noalias) sema.zir.extra[extra_index] else 0,
        .is_var_args = bits.is_var_args,
    };
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

    const tag = sema.zir.instructions.items(.tag)[@intFromEnum(inst)];
    const fancy = sema.funcFancyExtras(inst, tag);
    const fn_ty = try sema.intern_pool.internFuncType(.{
        .param_types = params,
        .return_type = ret_ty,
        .comptime_bits = comptime_bits,
        .noalias_bits = fancy.noalias_bits,
        .is_var_args = fancy.is_var_args,
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
        // The container being analysed when the function is declared is where
        // its body resolves bare sibling names; a call restores it (see the
        // body-eval `this_type` below).
        .parent = sema.this_type,
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
/// `.field_call` (`obj.f(x)`) resolves `f` in the object: a struct-type object
/// (`P.decl(x)`) calls the namespace declaration; a struct-value object
/// (`p.method(x)`) binds the value as the method's first argument.
fn evalCall(sema: *Sema, inst: Zir.Inst.Index, comptime kind: enum { direct, field }) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    // Bound recursion as the compiler does: every call is a backward branch
    // against `branch_quota` (`analyzeCall` -> `emitBackwardBranch`), which
    // also catches runaway non-recursive evaluation. Raise via
    // `@setEvalBranchQuota` once that builtin lands.
    try sema.emitBackwardBranch();

    // Resolve the callee, an optional bound receiver, and the argument bodies.
    // A direct call reads the callee ref. A field call (`obj.f(...)`) resolves
    // `f` in the object: a struct-type object (`P.decl(x)`) calls the
    // declaration with no receiver; a struct-value object (`p.method(x)`) binds
    // the value as the method's first argument.
    // `enclosing_ty` is the struct whose declaration is being called, or `.none`
    // for a direct call whose namespace is not named at the call site. It becomes
    // `@This()` / the bare-sibling-name namespace for the callee's body.
    const callee_value: Value, const self_val: ?Value, const explicit_len: u32, const args_body: []const Zir.Inst.Index, const enclosing_ty: InternPool.Index = switch (kind) {
        .direct => blk: {
            const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
            const extra = sema.zir.extraData(Zir.Inst.Call, pl_node.payload_index);
            break :blk .{
                try sema.resolveRef(extra.data.callee),
                null,
                extra.data.flags.args_len,
                @ptrCast(sema.zir.extra[extra.end..]),
                .none,
            };
        },
        .field => blk: {
            const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
            const extra = sema.zir.extraData(Zir.Inst.FieldCall, pl_node.payload_index);
            const name = try sema.intern_pool.getOrPutString(sema.gpa, sema.zir.nullTerminatedString(extra.data.field_name_start));
            const object_ptr = try sema.resolveRef(extra.data.obj_ptr);
            const object = try sema.loadValue(object_ptr);
            const args_slice: []const Zir.Inst.Index = @ptrCast(sema.zir.extra[extra.end..]);
            // Mirror `fieldCallBind`: a type object (`T.decl(x)`) resolves the
            // declaration in T's namespace with no receiver; a value object
            // (`v.method(x)`) binds the value and resolves the method in its type's
            // namespace. `containerDeclByName` (the REPL's `getNamespace` lookup)
            // returns null for a type without one -- e.g. an enum, as in
            // `std.Target.Os.Tag.defaultVersionRange(...)`, or the value's type in
            // `builtin.target.cCallingConvention()`.
            const is_type = object.typeOf(sema.intern_pool).toIndex() == .type_type;
            const lookup_ty = if (is_type) object.index else object.typeOf(sema.intern_pool).toIndex();
            const callee = (try sema.containerDeclByName(lookup_ty, name)) orelse
                return sema.failBadMemberAccess(lookup_ty, name);
            // Bind the value method's receiver from `m`'s first parameter, as
            // `fieldCallBind` does: a `*T` receiver -- a single/C pointer to the
            // value's type -- or an `anytype` first parameter takes the object
            // pointer (so the method reads or mutates through it); a by-value `T`
            // takes the loaded value.
            const self: ?Value = if (is_type) null else self: {
                const callee_func = sema.intern_pool.indexToKey(callee.index);
                if (callee_func != .func) break :self object;
                const first_params = sema.intern_pool.indexToKey(callee_func.func.ty).func_type.param_types;
                if (first_params.len == 0) break :self object;
                if (first_params[0] == .generic_poison_type) break :self object_ptr;
                const p0 = sema.intern_pool.indexToKey(first_params[0]);
                if (p0 == .ptr_type and
                    (p0.ptr_type.flags.size == .one or p0.ptr_type.flags.size == .c) and
                    p0.ptr_type.child == lookup_ty)
                    break :self object_ptr;
                break :self object;
            };
            break :blk .{ callee, self, extra.data.flags.args_len, args_slice, lookup_ty };
        },
    };

    const callee_key = sema.intern_pool.indexToKey(callee_value.index);
    if (callee_key != .func) {
        try sema.writer.writeAll("call: callee is not a function value\n");
        return error.AnalysisFail;
    }
    const func = callee_key.func;
    var func_ty = sema.intern_pool.indexToKey(func.ty).func_type;
    // `param_types` borrows the pool's `extra`; evaluating the arguments below
    // interns values that can reallocate it. Copy onto stable storage and rebind
    // so every later read (the param loop, `paramIsComptime`) is safe. The other
    // `func_ty` fields are copied scalars, unaffected by reallocation.
    const param_types = try sema.gpa.dupe(InternPool.Index, func_ty.param_types);
    defer sema.gpa.free(param_types);
    func_ty.param_types = param_types;

    const args_len = explicit_len + @as(u32, @intFromBool(self_val != null));
    if (func_ty.param_types.len != args_len) {
        try sema.writer.print(
            "expected {d} argument(s), found {d}\n",
            .{ func_ty.param_types.len, args_len },
        );
        return error.AnalysisFail;
    }
    const raw_args = try sema.evalCallArgs(inst, self_val, explicit_len, args_body, func_ty.param_types);
    defer sema.gpa.free(raw_args);

    // The callee's body sees its container as `@This()` and resolves bare
    // sibling-declaration names (`fn total() { return sum2(...); }`) against it.
    // Args above were evaluated in the caller's scope, so this is set only now.
    // Prefer the function's own definition container over the call site: a
    // function reached through a re-export (`std.Target.x86.featureSet`) resolves
    // its body's names where it was declared, not where it was named. Falls back
    // to the call-site container for a function with no stored parent (a REPL
    // top-level `fn`, whose siblings resolve through the session namespace).
    const saved_this = sema.this_type;
    sema.this_type = if (func.parent != .none) func.parent else enclosing_ty;
    defer sema.this_type = saved_this;

    // View the func's source-ZIR snapshot for the body eval, crossing a REPL line
    // boundary when the call does (a no-op for a same-line call). Moving
    // current_zir_id too is not incidental: a struct/func declared in the body
    // records `(source_zir_id, decl_inst)` -- the REPL's analog of the compiler's
    // `TrackedInst{ file, inst }` from `block.trackZir` -- so it must capture the
    // callee's line (the block's file scope during the call), not the caller's,
    // or its decl is later read from the wrong ZIR. Restored on return.
    const frame = try sema.enterSourceZir(func.source_zir_id, "call");
    defer frame.restore(sema);

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
    // Bind params in declaration order, coercing each argument to its parameter
    // type. A poison marker means the type was unknown at definition: a generic
    // param re-resolves its type body against the now-bound comptime params; an
    // `anytype` param (no type body) takes the argument's own type.
    const param_tags = sema.zir.instructions.items(.tag);
    for (param_insts, raw_args, 0..) |p_inst, raw, i| {
        const declared = func_ty.param_types[i];
        const param_ty = if (declared != .generic_poison_type)
            declared
        else switch (param_tags[@intFromEnum(p_inst)]) {
            .param_anytype, .param_anytype_comptime => raw.typeOf(sema.intern_pool).toIndex(),
            else => try sema.resolveParamType(p_inst),
        };
        var val = try sema.coerceValueToType(raw, param_ty, "call arg");
        val.is_comptime = func_ty.paramIsComptime(@intCast(i));
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

/// Resolve each call argument to a raw (uncoerced) Value in the caller's scope.
/// Returns a freshly allocated slice (caller frees). A bound `self_val` (a
/// method call's receiver) is prepended as the first argument; the remaining
/// `explicit_len` come from `args_body`. Coercion to the parameter type happens
/// in `evalCall` once the callee's ZIR is in scope, because a generic
/// parameter's type is only known there, per instantiation.
///
/// Before each argument body runs, the call instruction is bound to that
/// argument's parameter type, so a result-type-dependent expression -- a
/// `decl_literal` like `.tag`, whose type ref AstGen points at the call -- reads
/// it. Mirrors `analyzeArg` (src/Sema.zig) mapping `call_inst` to the parameter
/// type. A generic parameter's type is the poison marker here; the argument then
/// yields its own natural type, resolved against the concrete type in `evalCall`.
fn evalCallArgs(
    sema: *Sema,
    inst: Zir.Inst.Index,
    self_val: ?Value,
    explicit_len: u32,
    args_body: []const Zir.Inst.Index,
    param_types: []const InternPool.Index,
) Error![]Value {
    const base: u32 = @intFromBool(self_val != null);
    const arg_values = try sema.gpa.alloc(Value, base + explicit_len);
    errdefer sema.gpa.free(arg_values);
    if (self_val) |s| arg_values[0] = s;
    for (0..explicit_len) |i| {
        const start = if (i == 0) explicit_len else @intFromEnum(args_body[i - 1]);
        const end = @intFromEnum(args_body[i]);
        const param_idx = base + i;
        const param_ty: InternPool.Index = if (param_idx < param_types.len) param_types[param_idx] else .generic_poison_type;
        try sema.results.put(sema.gpa, inst, .{ .index = param_ty });
        arg_values[param_idx] = try sema.resolveInlineBody(args_body[start..end], inst);
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

/// `typeof_peer`: `@TypeOf(a, b, ...)` -- the peer-resolved type of several
/// operands. AstGen puts the operand expressions in a body (evaluated for its
/// instruction results) followed by their refs. Mirrors `src/Sema.zig`
/// zirTypeofPeer: run the body, then fold peer resolution across the operands.
/// `@This()` (extended `this`): the enclosing container type. Mirrors zirThis,
/// which returns the block namespace's owner type; here it is the struct set by
/// `containerDeclByName` around a member's evaluation.
fn evalThis(sema: *Sema) Error!?Value {
    if (sema.this_type == .none) {
        try sema.writer.writeAll("@This(): no enclosing container\n");
        return error.AnalysisFail;
    }
    return Value{ .index = sema.this_type };
}

/// `closure_get` (extended): the value of capture `small` of the container being
/// evaluated -- `this_type`, the compiler's `block.namespace.owner_type`. The
/// capture's comptime value was resolved when the type was declared
/// (`resolveCaptures`) and stored on the type. Mirrors zirClosureGet's comptime
/// arm; the runtime/nav arms do not arise in a comptime evaluator.
fn evalClosureGet(sema: *Sema, extended: Zir.Inst.Extended.InstData) Error!?Value {
    if (sema.this_type == .none) {
        try sema.writer.writeAll("closure_get: no enclosing container\n");
        return error.AnalysisFail;
    }
    const captures = switch (sema.intern_pool.indexToKey(sema.this_type)) {
        .struct_type => |st| st.id.captures(),
        .union_type => |ut| ut.id.captures(),
        .enum_type => |et| et.id.captures(),
        else => unreachable,
    };
    assert(extended.small < captures.len);
    return Value{ .index = captures[extended.small] };
}

fn evalTypeofPeer(sema: *Sema, extended: Zir.Inst.Extended.InstData, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    const extra = sema.zir.extraData(Zir.Inst.TypeOfPeer, extended.operand);
    const body = sema.zir.bodySlice(extra.data.body_index, extra.data.body_len);
    // Evaluate the operand expressions; the body's break value is unused (we
    // read the operands by ref below, as the compiler does).
    _ = try sema.resolveInlineBody(body, inst);

    const args = sema.zir.refSlice(extra.end, extended.small);
    assert(args.len > 0);

    var acc = try sema.resolveRef(args[0]);
    for (args[1..]) |arg_ref| {
        acc = try sema.peerResolvePair(acc, try sema.resolveRef(arg_ref));
    }
    return Value{ .index = Value.typeOf(acc, ip).index };
}

/// Peer-resolve two operands and return whichever one carries the peer type
/// (the peer type is always one of the operand types for the cases modeled).
/// Same type wins trivially; a mixed int pair resolves through the shared
/// `resolveNumericPairToInt` rule, a pair involving a float through
/// `coerceNumericPairToFloat` (whose coerced values carry the common type).
/// Other mixes surface a diagnostic.
fn peerResolvePair(sema: *Sema, a: Value, b: Value) Error!Value {
    const ip = sema.intern_pool;
    const a_key = ip.indexToKey(a.index);
    const b_key = ip.indexToKey(b.index);
    const a_ty = Value.typeOf(a, ip).index;
    if (a_ty == Value.typeOf(b, ip).index) return a;
    if (resolveNumericPairToInt(ip, a_key, b_key)) |peer| {
        return if (a_ty == peer.ty) a else b;
    }
    if (coerceNumericPairToFloat(a_key, b_key)) |pair| {
        return if (a_ty == pair[0].ty) a else b;
    }
    try sema.writer.writeAll("@TypeOf: no peer type for the given operands\n");
    return error.AnalysisFail;
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

        .select => return sema.evalSelect(extended),
        .reify_tuple => return sema.evalReifyTuple(extended),
        .reify_pointer => return sema.evalReifyPointer(extended),
        .reify_pointer_sentinel_ty => return sema.evalReifyPointerSentinelTy(extended),
        .reify_slice_arg_ty => return sema.evalReifySliceArgTy(extended),
        .reify_fn => return sema.evalReifyFn(extended),
        .reify_enum_value_slice_ty => return sema.evalReifyEnumValueSliceTy(extended),
        .reify_enum => return sema.evalReifyEnum(extended, inst),
        .reify_struct => return sema.evalReifyStruct(extended, inst),
        .reify_union => return sema.evalReifyUnion(extended, inst),
        .tuple_decl => return sema.evalTupleDecl(extended),
        .enum_decl => return sema.evalEnumDecl(inst),
        .union_decl => return sema.evalUnionDecl(inst),
        .struct_decl => return sema.evalStructDecl(inst),
        .typeof_peer => return sema.evalTypeofPeer(extended, inst),
        .this => return sema.evalThis(),
        .closure_get => return sema.evalClosureGet(extended),

        // The result type for a compound assignment (`s += x`, `s -= x`): the
        // lhs's own type, against which the rhs is coerced before the arith +
        // store-back. Mirrors zirInplaceArithResultTy's non-pointer case;
        // pointer arithmetic (its `[*]T`/`[*c]T` special cases) is unsupported,
        // so a pointer lhs yields its own type and the following arith rejects it.
        .inplace_arith_result_ty => {
            const lhs = try sema.resolveRef(@enumFromInt(extended.operand));
            return Value{ .index = Value.typeOf(lhs, sema.intern_pool).index };
        },

        .std_lang_value => return sema.evalStdLangValue(extended),

        // `@frame()` -- another async form, rejected like the frame ZIR tags.
        .frame => return sema.failUseOfAsync(),

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

/// Reject an async/frame operation (`anyframe`, `anyframe->T`, `@Frame`, `suspend`,
/// `resume`, `@frame`) with the self-hosted compiler's own diagnostic. Async was
/// never implemented in the self-hosted compiler; each of these ZIR forms resolves
/// to `failWithUseOfAsync`, so the REPL mirrors that rather than the type build the
/// dead code past `if (true)` in `zirAnyframeType` would suggest.
fn failUseOfAsync(sema: *Sema) Error!?Value {
    try sema.writer.writeAll("async has not been implemented in the self-hosted compiler yet\n");
    return error.AnalysisFail;
}

const testing = std.testing;

fn opvTestSema(gpa: std.mem.Allocator, pool: *InternPool, arena: *std.heap.ArenaAllocator, w: *std.Io.Writer) Sema {
    return .{
        .gpa = gpa,
        .arena = arena.allocator(),
        .intern_pool = pool,
        .zir = undefined,
        .writer = w,
        .results = .empty,
        .comptime_allocs = .empty,
        .namespace = null,
    };
}

fn opvNames(sema: *Sema, names: []const []const u8) ![]InternPool.NullTerminatedString {
    const out = try sema.arena.alloc(InternPool.NullTerminatedString, names.len);
    for (names, out) |n, *h| h.* = try sema.intern_pool.getOrPutString(sema.gpa, n);
    return out;
}

/// A reified enum whose fields are `names`; `hash` keeps its identity distinct.
fn opvEnum(sema: *Sema, hash: u64, names: []const []const u8) !Type {
    const pool = sema.intern_pool;
    const handles = try opvNames(sema, names);
    const tag_ty = try sema.enumIntTagType(@intCast(names.len));
    const enum_ty = try pool.internEnumType(.{
        .name = try pool.getOrPutString(sema.gpa, "E"),
        .id = .{ .reified = .{ .source_zir_id = 0, .decl_inst = @enumFromInt(0), .type_hash = hash } },
    });
    try pool.setEnumFields(enum_ty, tag_ty, false, handles, &.{});
    return .fromIndex(enum_ty);
}

fn opvStruct(sema: *Sema, hash: u64, names: []const []const u8, types: []const InternPool.Index) !Type {
    const pool = sema.intern_pool;
    const handles = try opvNames(sema, names);
    const struct_ty = try pool.internStructType(.{
        .name = try pool.getOrPutString(sema.gpa, "S"),
        .id = .{ .reified = .{ .source_zir_id = 0, .decl_inst = @enumFromInt(0), .type_hash = hash } },
    });
    try pool.setStructFields(struct_ty, .auto, .none, handles, types, &.{}, &.{}, &.{});
    return .fromIndex(struct_ty);
}

fn opvUnion(sema: *Sema, hash: u64, tag_hash: u64, names: []const []const u8, types: []const InternPool.Index) !Type {
    const pool = sema.intern_pool;
    const tag_enum = try opvEnum(sema, tag_hash, names);
    const handles = try opvNames(sema, names);
    const union_ty = try pool.internUnionType(.{
        .name = try pool.getOrPutString(sema.gpa, "U"),
        .id = .{ .reified = .{ .source_zir_id = 0, .decl_inst = @enumFromInt(0), .type_hash = hash } },
    });
    try pool.setUnionFields(union_ty, .auto, tag_enum.index, .none, handles, types, &.{});
    return .fromIndex(union_ty);
}

test "onePossibleValue: every type-kind branch" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();
    var arena_state = std.heap.ArenaAllocator.init(gpa);
    defer arena_state.deinit();
    var buf: [512]u8 = undefined;
    var w = std.Io.Writer.fixed(&buf);
    var sema = opvTestSema(gpa, &pool, &arena_state, &w);
    const s = &sema;

    const expectOpv = struct {
        fn f(se: *Sema, ty: Type, has: bool) !void {
            try testing.expectEqual(has, (try ty.onePossibleValue(se)) != null);
        }
    }.f;

    // int: only a 0-bit int is OPV.
    try expectOpv(s, .fromIndex(.u0_type), true);
    try expectOpv(s, .fromIndex(.u8_type), false);
    // simple: void is OPV; bool / type / comptime_int are not.
    try expectOpv(s, .fromIndex(.void_type), true);
    try expectOpv(s, .fromIndex(.bool_type), false);
    try expectOpv(s, .fromIndex(.type_type), false);
    try expectOpv(s, .fromIndex(.comptime_int_type), false);
    // array: element-driven; a zero-length array is OPV.
    try expectOpv(s, .fromIndex(try pool.internArrayType(.{ .len = 3, .child = .u0_type })), true);
    try expectOpv(s, .fromIndex(try pool.internArrayType(.{ .len = 3, .child = .u8_type })), false);
    try expectOpv(s, .fromIndex(try pool.internArrayType(.{ .len = 0, .child = .u8_type })), true);
    // vector.
    try expectOpv(s, .fromIndex(try pool.internVectorType(.{ .len = 3, .child = .u0_type })), true);
    try expectOpv(s, .fromIndex(try pool.internVectorType(.{ .len = 3, .child = .u8_type })), false);
    // optional: `?noreturn` is OPV (only null); `?u8` is not.
    try expectOpv(s, .fromIndex(try pool.internOptionalType(.noreturn_type)), true);
    try expectOpv(s, .fromIndex(try pool.internOptionalType(.u8_type)), false);
    // tuple: OPV iff every field is.
    try expectOpv(s, .fromIndex(try pool.internTupleType(&.{ .u0_type, .void_type })), true);
    try expectOpv(s, .fromIndex(try pool.internTupleType(&.{.u8_type})), false);
    // enum: OPV iff it has a single tag.
    try expectOpv(s, try opvEnum(s, 0x1001, &.{"only"}), true);
    try expectOpv(s, try opvEnum(s, 0x1002, &.{ "a", "b" }), false);
    // struct: OPV iff every field is.
    try expectOpv(s, try opvStruct(s, 0x2001, &.{ "x", "y" }, &.{ .u0_type, .void_type }), true);
    try expectOpv(s, try opvStruct(s, 0x2002, &.{"x"}, &.{.u8_type}), false);
    // union: OPV iff exactly one field is inhabitable and it is OPV.
    try expectOpv(s, try opvUnion(s, 0x3001, 0x4001, &.{"x"}, &.{.u0_type}), true);
    try expectOpv(s, try opvUnion(s, 0x3002, 0x4002, &.{"x"}, &.{.u8_type}), false);
    try expectOpv(s, try opvUnion(s, 0x3003, 0x4003, &.{ "a", "b" }, &.{ .u0_type, .u0_type }), false);
}
