const std = @import("std");
const assert = std.debug.assert;
const Allocator = std.mem.Allocator;
const Zir = std.zig.Zir;
const BigIntMutable = std.math.big.int.Mutable;
const Limb = std.math.big.Limb;

const InternPool = @import("InternPool.zig");
const Value = @import("Value.zig");
const MutableValue = @import("MutableValue.zig").MutableValue;
const comptime_ptr_access = @import("comptime_ptr_access.zig");
const runtime = @import("../io/root.zig");
const reinterpret = @import("reinterpret.zig");
const Type = @import("Type.zig");
const render_value = @import("../render/Value.zig");
const arith = @import("arith.zig");
const RangeSet = @import("RangeSet.zig");
const InputShape = @import("../front/InputShape.zig");
const Session = @import("../Session.zig");

const Sema = @This();

pub const Error = Allocator.Error || std.Io.Writer.Error || error{
    AnalysisFail,
    ComptimeBreak,
    ComptimeReturn,
    NotCoercible,
};

gpa: Allocator,
arena: Allocator,
intern_pool: *InternPool,
zir: Zir,
writer: *std.Io.Writer,
err: ?*ErrorMsg = null,
inst_map: std.AutoHashMapUnmanaged(Zir.Inst.Index, Value),
comptime_allocs: std.ArrayListUnmanaged(ComptimeAlloc),
comptime_address_cursor: u64 = 0x1000,
synthetic_addresses: std.AutoHashMapUnmanaged(InternPool.Index, u64) = .empty,
comptime_break_inst: Zir.Inst.Index = undefined,
branch_quota: u32 = default_branch_quota,
branch_count: u32 = 0,
return_value: Value = undefined,
fn_ret_ty: InternPool.Index = .none,
operand_comptime: bool = true,
session: ?*Session = null,
current_zir_id: u32 = 0,
/// The declaration currently being analyzed, the compiler's `sema.owner`. A function created
/// while resolving a declaration records it as its owner nav.
owner_nav: InternPool.Nav.Index.Optional = .none,
block: *Block = undefined,

pub const default_branch_quota: u32 = 1000;

pub const LazySrcLoc = @import("ErrorMsg.zig").LazySrcLoc;
pub const ErrorMsg = @import("ErrorMsg.zig").ErrorMsg;

pub const Block = struct {
    params: std.ArrayListUnmanaged(Param) = .empty,
    src_base_inst: Zir.Inst.Index = undefined,
    namespace: ?InternPool.NamespaceIndex = null,
    type_name_ctx: InternPool.NullTerminatedString = .empty,
    /// Set for the block of an inline/comptime call so a comptime scope propagates into the callee
    /// and diagnostics can walk back to the call site. Reduced from the compiler's `Block.Inlining`:
    /// the AIR-return and generic-instantiation fields have no analog in a comptime-only interpreter.
    inlining: ?*Inlining = null,
    comptime_reason: ?BlockComptimeReason = null,

    pub fn deinit(self: *Block, gpa: std.mem.Allocator) void {
        self.params.deinit(gpa);
    }

    pub fn isComptime(block: Block) bool {
        return block.comptime_reason != null;
    }

    /// This `Block` indicates that an inline call is happening, so a comptime scope is inherited from
    /// the call site and diagnostics can attribute the comptime requirement to the caller.
    pub const Inlining = struct {
        call_block: *Block,
        call_src: LazySrcLoc,
    };

    fn explainWhyBlockIsComptime(start_block: *Block, sema: *Sema, err_msg: *ErrorMsg) Allocator.Error!*Block {
        var block = start_block;
        while (true) {
            switch (block.comptime_reason.?) {
                .inlining_parent => {
                    const inlining = block.inlining.?;
                    try sema.errNote(inlining.call_src, err_msg, "called at comptime from here", .{});
                    block = inlining.call_block;
                },
                .reason => |r| {
                    try r.r.explain(sema, r.src, err_msg);
                    return block;
                },
            }
        }
    }

    pub fn src(block: Block, offset: LazySrcLoc.Offset) LazySrcLoc {
        return .{ .base_node_inst = block.src_base_inst, .offset = offset };
    }

    pub fn nodeOffset(block: Block, node_offset: std.zig.Ast.Node.Offset) LazySrcLoc {
        return block.src(LazySrcLoc.Offset.nodeOffset(node_offset));
    }

    pub fn builtinCallArgSrc(block: Block, builtin_call_node: std.zig.Ast.Node.Offset, arg_index: u32) LazySrcLoc {
        return block.src(.{ .node_offset_builtin_call_arg = .{
            .builtin_call_node = builtin_call_node,
            .arg_index = arg_index,
        } });
    }

    pub const Param = struct {
        ty: InternPool.Index,
        is_comptime: bool,
    };
};

/// Represents the reason we are resolving a value or evaluating code at comptime.
/// Most reasons are represented by a `std.zig.SimpleComptimeReason`, which provides a plain message.
const ComptimeReason = union(enum) {
    /// Evaluating at comptime for a reason in the `std.zig.SimpleComptimeReason` enum.
    simple: std.zig.SimpleComptimeReason,

    /// Evaluating at comptime because of a comptime-only type. This field is separate so that
    /// the type in question can be included in the error message.
    /// The format string looks like "foo '{f}' bar", where "{f}" is the comptime-only type.
    /// We will then explain why this type is comptime-only.
    comptime_only: struct {
        ty: Type,
        msg: enum {
            union_init,
            struct_init,
            tuple_init,
        },
    },

    /// Like `comptime_only`, but for a parameter type.
    /// Includes a "parameter type declared here" note.
    comptime_only_param_ty: struct {
        ty: Type,
        param_ty_src: LazySrcLoc,
    },

    /// Like `comptime_only`, but for a return type.
    /// Includes a "return type declared here" note.
    comptime_only_ret_ty: struct {
        ty: Type,
        is_generic_inst: bool,
        ret_ty_src: LazySrcLoc,
    },

    /// Evaluating at comptime because we're evaluating an argument to a parameter marked `comptime`.
    comptime_param: struct {
        comptime_src: LazySrcLoc,
    },

    fn explain(reason: ComptimeReason, sema: *Sema, src: LazySrcLoc, err_msg: *ErrorMsg) Allocator.Error!void {
        const ip = sema.intern_pool;
        switch (reason) {
            .simple => |simple| {
                try sema.errNote(src, err_msg, "{s}", .{simple.message()});
            },
            .comptime_only => |co| {
                const pre, const post = switch (co.msg) {
                    .union_init => .{ "initializer of comptime-only union", "must be comptime-known" },
                    .struct_init => .{ "initializer of comptime-only struct", "must be comptime-known" },
                    .tuple_init => .{ "initializer of comptime-only tuple", "must be comptime-known" },
                };
                try sema.errNote(src, err_msg, "{s} '{f}' {s}", .{ pre, co.ty.fmt(ip), post });
                try sema.explainWhyTypeIsComptime(err_msg, src, co.ty);
            },
            .comptime_only_param_ty => |co| {
                try sema.errNote(src, err_msg, "argument to parameter with comptime-only type '{f}' must be comptime-known", .{co.ty.fmt(ip)});
                try sema.errNote(co.param_ty_src, err_msg, "parameter type declared here", .{});
                try sema.explainWhyTypeIsComptime(err_msg, src, co.ty);
            },
            .comptime_only_ret_ty => |co| {
                const function_with: []const u8 = if (co.is_generic_inst) "generic function instantiated with" else "function with";
                try sema.errNote(src, err_msg, "call to {s} comptime-only return type '{f}' is evaluated at comptime", .{ function_with, co.ty.fmt(ip) });
                try sema.errNote(co.ret_ty_src, err_msg, "return type declared here", .{});
                try sema.explainWhyTypeIsComptime(err_msg, src, co.ty);
            },
            .comptime_param => |cp| {
                try sema.errNote(src, err_msg, "argument to comptime parameter must be comptime-known", .{});
                try sema.errNote(cp.comptime_src, err_msg, "parameter declared comptime here", .{});
            },
        }
    }
};

/// Represents the reason a `Block` is being evaluated at comptime.
const BlockComptimeReason = union(enum) {
    /// This block inherits being comptime-only from the `inlining` call site.
    inlining_parent,

    /// Comptime evaluation began somewhere in the current function for a given `ComptimeReason`.
    reason: struct {
        /// The source location which this reason originates from. `r` is reported here.
        src: LazySrcLoc,
        r: ComptimeReason,
    },
};

pub const ComptimeAlloc = struct {
    val: MutableValue,
    is_const: bool,
    /// The alignment of this allocation. `.none` means naturally aligned.
    alignment: InternPool.Alignment = .none,
    address: ?u64 = null,
};

pub fn getComptimeAlloc(sema: *Sema, idx: InternPool.Key.ComptimeAllocIndex) *ComptimeAlloc {
    return &sema.comptime_allocs.items[@backingInt(idx)];
}

pub fn analyze(session: *Session, file_index: Session.Index, writer: *std.Io.Writer) Error!?Value {
    const gpa = session.gpa;
    const intern_pool = session.intern_pool;
    const namespace = session.root_namespace;
    const zir = session.files.items[file_index].zir.?;
    assert(zir.instructions.len > 0);

    var top_block: Block = .{ .namespace = namespace };
    defer top_block.deinit(gpa);

    var arena_instance = std.heap.ArenaAllocator.init(gpa);
    defer arena_instance.deinit();

    var sema: Sema = .{
        .gpa = gpa,
        .arena = arena_instance.allocator(),
        .intern_pool = intern_pool,
        .zir = zir,
        .writer = writer,
        .inst_map = .empty,
        .comptime_allocs = .empty,
        .block = &top_block,
        .session = session,
        .current_zir_id = file_index,
    };
    defer sema.inst_map.deinit(gpa);
    defer sema.comptime_allocs.deinit(gpa);
    defer sema.synthetic_addresses.deinit(gpa);

    sema.block.type_name_ctx = try intern_pool.namespaceName(gpa, namespace);

    try runtime.install(&sema);

    if (findReplInputBody(zir)) |bound| {
        top_block.src_base_inst = bound.decl_inst;
        return try sema.evalReplExpression(bound.body, bound.decl_inst);
    }
    const ns_idx = sema.block.namespace.?;
    const comptime_start = intern_pool.namespacePtr(ns_idx).comptime_decls.items.len;
    try sema.bindDecls();
    // Analyze the container-scope `comptime {}` blocks bound this pass. Re-read the namespace pointer per
    // iteration: analyzing a block may intern a new type and reallocate the namespace list.
    var cu_i = comptime_start;
    while (cu_i < intern_pool.namespacePtr(ns_idx).comptime_decls.items.len) : (cu_i += 1) {
        try sema.analyzeComptimeUnit(intern_pool.namespacePtr(ns_idx).comptime_decls.items[cu_i]);
    }
    return null;
}

/// Evaluate the wrapper function an expression input lowers to, and read its single result local. The
/// wrapper is a runtime function body (see `InputShape`), so comptime-required operands carry their
/// `block_comptime` and evaluate with the real comptime/runtime boundary; `__repl_value` holds the
/// user expression's value, uncoerced.
fn evalReplExpression(sema: *Sema, value_body: []const Zir.Inst.Index, decl_inst: Zir.Inst.Index) Error!?Value {
    _ = decl_inst;
    // Read the body straight off the wrapper's `func` ZIR instruction, without evaluating the value
    // body: that would intern a function value and grow the pool on every eval.
    const func_inst = replWrapperFunc(sema.zir, value_body) orelse return null;
    const info = sema.zir.getFnInfo(func_inst);

    const saved_ret_ty = sema.fn_ret_ty;
    sema.fn_ret_ty = .void_type;
    defer sema.fn_ret_ty = saved_ret_ty;

    // The wrapper's `void` body ends in a return, which surfaces as `ComptimeReturn`.
    if (sema.resolveInlineBody(info.body, func_inst)) |_| {} else |err| switch (err) {
        error.ComptimeReturn => {},
        else => |e| return e,
    }

    return sema.replExpressionValue(info.body);
}

fn replWrapperFunc(zir: Zir, value_body: []const Zir.Inst.Index) ?Zir.Inst.Index {
    const tags = zir.instructions.items(.tag);
    for (value_body) |inst| {
        switch (tags[@backingInt(inst)]) {
            .func, .func_inferred, .func_fancy => return inst,
            else => {},
        }
    }
    return null;
}

/// Read the value bound to `__repl_value` in the evaluated wrapper body. AstGen lowers the local as a
/// `dbg_var_val` (rvalue) or, when the initializer needs a result location, a `dbg_var_ptr`.
fn replExpressionValue(sema: *Sema, body: []const Zir.Inst.Index) Error!?Value {
    const tags = sema.zir.instructions.items(.tag);
    const datas = sema.zir.instructions.items(.data);
    for (body) |inst| {
        const tag = tags[@backingInt(inst)];
        switch (tag) {
            .dbg_var_val, .dbg_var_ptr => {
                const str_op = datas[@backingInt(inst)].str_op;
                if (!std.mem.eql(u8, sema.zir.nullTerminatedString(str_op.str), InputShape.expression_value_name)) continue;
                const bound = try sema.resolveInst(str_op.operand);
                const result = if (tag == .dbg_var_ptr) try sema.loadValue(bound) else bound;
                return sema.snapshotComptimeBacking(result);
            },
            else => {},
        }
    }
    return null;
}

/// A comptime alloc is freed when analysis ends, so a result pointing into one is snapshotted while it is still live.
fn snapshotComptimeBacking(sema: *Sema, value: Value) Value {
    const ip = sema.intern_pool;
    if (!value.canMutateComptimeVarState(ip)) return value;
    switch (ip.indexToKey(value.index)) {
        .ptr => |p| {
            const ptr_ty = ip.indexToKey(p.ty).ptr_type;
            if (ptr_ty.flags.size != .one or ip.indexToKey(ptr_ty.child) != .array_type) return value;
            const loaded = sema.loadValue(value) catch return value;
            return .{ .index = sema.uavPtr(p.ty, loaded.index) catch return value };
        },
        .slice => |s| {
            const slice_ptr_ty = ip.indexToKey(s.ty).ptr_type;
            const elem = slice_ptr_ty.child;
            const len = sema.resolveUsizeInt(.{ .index = s.len }) catch return value;
            const elems = sema.arena.alloc(InternPool.Index, len) catch return value;
            for (elems, 0..) |*e, i| {
                const elem_ptr = Value.fromIndex(s.ptr).ptrElem(i, ip) catch return value;
                e.* = (sema.loadValue(elem_ptr) catch return value).index;
            }
            const arr_ty = ip.internArrayType(.{ .len = len, .child = elem }) catch return value;
            const arr_val = sema.aggregateValue(.fromIndex(arr_ty), elems) catch return value;
            const many_ty = ip.internPtrType(.{ .child = elem, .flags = .{ .size = .many, .is_const = slice_ptr_ty.flags.is_const } }) catch return value;
            const many_ptr = sema.uavPtr(many_ty, arr_val.index) catch return value;
            return .{ .index = ip.get(.{ .slice = .{ .ty = s.ty, .ptr = many_ptr, .len = s.len } }) catch return value };
        },
        else => return value,
    }
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
            return .{ .decl_inst = decl_inst, .body = unwrapped.value_body orelse return null };
        }
    }
    return null;
}

fn evalBody(sema: *Sema, body: []const Zir.Inst.Index) Error!Value {
    assert(body.len > 0);

    const tags = sema.zir.instructions.items(.tag);

    var i: u32 = 0;
    while (true) {
        assert(i < body.len);
        const inst = body[i];
        const tag = tags[@backingInt(inst)];
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
            .ret_node => {
                const operand = sema.zir.instructions.items(.data)[@backingInt(inst)].un_node.operand;
                sema.return_value = try sema.resolveInst(operand);
                return error.ComptimeReturn;
            },
            .ret_implicit => {
                const operand = sema.zir.instructions.items(.data)[@backingInt(inst)].un_tok.operand;
                sema.return_value = try sema.resolveInst(operand);
                return error.ComptimeReturn;
            },
            .ret_load => {
                const operand = sema.zir.instructions.items(.data)[@backingInt(inst)].un_node.operand;
                const ptr = try sema.resolveInst(operand);
                sema.return_value = try sema.loadValue(ptr);
                return error.ComptimeReturn;
            },
            .ret_err_value => {
                // `return error.Foo`: build the single-error value and return it, mirroring the
                // compiler's `zirRetErrValue`.
                const ip = sema.intern_pool;
                const str_tok = sema.zir.instructions.items(.data)[@backingInt(inst)].str_tok;
                const err_name = try ip.getOrPutString(sema.gpa, str_tok.get(sema.zir), .no_embedded_nulls);
                _ = try ip.getErrorValue(err_name);
                const error_set_type = try ip.singletonErrorSetType(err_name);
                sema.return_value = .{ .index = try ip.internErr(.{ .ty = error_set_type, .name = err_name }) };
                return error.ComptimeReturn;
            },
            .@"defer" => {
                const defer_data = sema.zir.instructions.items(.data)[@backingInt(inst)].@"defer";
                const defer_body = sema.zir.bodySlice(defer_data.index, defer_data.len);
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
                const saved_oc = sema.operand_comptime;
                sema.operand_comptime = true;
                const maybe = sema.evalInst(inst, tag);
                const operands_comptime = sema.operand_comptime;
                sema.operand_comptime = saved_oc;
                if (try maybe) |result| {
                    var r = result;
                    r.is_comptime = r.is_comptime and operands_comptime;
                    try sema.inst_map.put(sema.gpa, inst, r);
                }
            },
        }
        i += 1;
    }
}

fn emitBackwardBranch(sema: *Sema) Error!void {
    sema.branch_count += 1;
    if (sema.branch_count > sema.branch_quota) {
        const src = sema.block.nodeOffset(.zero);
        const msg = msg: {
            const msg = try sema.errMsg(src, "evaluation exceeded {d} backwards branches", .{sema.branch_quota});
            errdefer msg.destroy(sema.gpa);
            try sema.errNote(src, msg, "use @setEvalBranchQuota() to raise the branch limit from {d}", .{sema.branch_quota});
            break :msg msg;
        };
        return sema.failWithOwnedErrorMsg(sema.block, msg);
    }
}

pub fn resolveInlineBody(
    sema: *Sema,
    body: []const Zir.Inst.Index,
    break_target: Zir.Inst.Index,
) Error!Value {
    if (sema.evalBody(body)) |val| {
        return val;
    } else |err| switch (err) {
        error.ComptimeBreak => {},
        else => |e| return e,
    }
    const datas = sema.zir.instructions.items(.data);
    const break_data = datas[@backingInt(sema.comptime_break_inst)].@"break";
    const extra = sema.zir.extraData(Zir.Inst.Break, break_data.payload_index);
    if (extra.data.block_inst != break_target) return error.ComptimeBreak;
    return try sema.resolveInst(break_data.operand);
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
        .div_ceil,
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
        .array_cat => sema.evalArrayCat(inst),
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
        .cmp_lt => sema.evalCmp(inst, .lt),
        .cmp_lte => sema.evalCmp(inst, .lte),
        .cmp_eq => sema.evalCmpEq(inst, .eq),
        .cmp_gte => sema.evalCmp(inst, .gte),
        .cmp_gt => sema.evalCmp(inst, .gt),
        .cmp_neq => sema.evalCmpEq(inst, .neq),
        .negate => sema.evalNegate(inst),
        .negate_wrap => sema.evalNegateWrap(inst),
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
        .backing_int => sema.evalBackingInt(inst),
        .from_backing_int_arg_ty => sema.evalFromBackingIntArgTy(inst),
        .from_backing_int => sema.evalFromBackingInt(inst),
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
        .@"unreachable" => sema.evalUnreachable(inst),
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
        .save_err_ret_index,
        .restore_err_ret_index_unconditional,
        .restore_err_ret_index_fn_entry,
        => null,
        .extended => sema.evalExtended(inst),
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
        .offset_of => sema.evalOffsetOf(inst),
        .bit_offset_of => sema.evalBitOffsetOf(inst),
        .ptr_from_int => sema.evalPtrFromInt(inst),
        .ptr_cast => sema.evalPtrCast(inst),
        .array_init_elem_type => sema.evalArrayInitElemType(inst),
        .elem_type => sema.evalElemType(inst),
        .indexable_ptr_elem_type => sema.evalIndexablePtrElemType(inst),
        .splat_op_result_ty => sema.evalSplatOpResultType(inst),
        .splat => sema.evalSplat(inst),
        .shuffle => sema.evalShuffle(inst),
        .validate_array_init_ty => sema.evalValidateArrayInitTy(inst, false),
        .validate_array_init_result_ty => sema.evalValidateArrayInitTy(inst, true),
        .validate_array_init_ref_ty => sema.evalValidateArrayInitRefTy(inst),
        .ref => sema.evalRef(inst),
        .elem_ptr_load => sema.evalElemPtrLoad(inst),
        .elem_ptr, .elem_ptr_node => sema.evalElemPtrNode(inst),
        .elem_val => sema.evalElemVal(inst),
        .memcpy => sema.evalMemcpy(inst),
        .memset => sema.evalMemset(inst),
        .compile_error => sema.evalCompileError(inst),
        .set_eval_branch_quota => sema.evalSetEvalBranchQuota(inst),
        .set_runtime_safety => sema.evalSetRuntimeSafety(inst),
        .type_name => sema.evalTypeName(inst),
        .error_name => sema.evalErrorName(inst),
        .union_init => sema.evalUnionInit(inst),
        .field_type_ref => sema.evalFieldTypeRef(inst),
        .merge_error_sets => sema.evalMergeErrorSets(inst),
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
    const value: u64 = sema.zir.instructions.items(.data)[@backingInt(inst)].int;

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

fn evalStr(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const bytes = sema.zir.instructions.items(.data)[@backingInt(inst)].str.get(sema.zir);
    return try sema.internStringLiteral(bytes);
}

fn internStringLiteral(sema: *Sema, bytes: []const u8) Error!Value {
    const ip = sema.intern_pool;
    const string = try ip.getOrPutString(sema.gpa, bytes, .maybe_embedded_nulls);
    const array_ty = try ip.internArrayType(.{ .len = bytes.len, .child = .u8_type, .sentinel = .zero_u8 });
    const array_val = try ip.internAggregate(.{ .ty = array_ty, .storage = .{ .bytes = string } });
    return try sema.materializeConstPtr(.{ .index = array_val });
}

fn evalIntBig(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@backingInt(inst) < sema.zir.instructions.len);

    const str = sema.zir.instructions.items(.data)[@backingInt(inst)].str;
    const limb_count: u32 = str.len;
    assert(limb_count > 0);

    const byte_count = limb_count * @sizeOf(std.math.big.Limb);
    const start: u32 = @backingInt(str.start);
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

fn evalFloat(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@backingInt(inst) < sema.zir.instructions.len);

    const value: f64 = sema.zir.instructions.items(.data)[@backingInt(inst)].float;
    const idx = try sema.intern_pool.internFloat(.{
        .ty = .comptime_float_type,
        .storage = .{ .f128 = @floatCast(value) },
    });
    assert(idx != .none);
    return .{ .index = idx };
}

fn evalFloat128(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@backingInt(inst) < sema.zir.instructions.len);

    const pl_node = sema.zir.instructions.items(.data)[@backingInt(inst)].pl_node;
    const payload = sema.zir.extraData(Zir.Inst.Float128, pl_node.payload_index).data;

    const idx = try sema.intern_pool.internFloat(.{
        .ty = .comptime_float_type,
        .storage = .{ .f128 = payload.get() },
    });
    assert(idx != .none);
    return .{ .index = idx };
}

fn evalPassthroughUnNode(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const operand = sema.zir.instructions.items(.data)[@backingInt(inst)].un_node.operand;
    return try sema.resolveInst(operand);
}

pub fn intValue_big(sema: *Sema, ty: Type, x: std.math.big.int.Const) Error!Value {
    return .fromIndex(try sema.intern_pool.internIntValue(ty.index, x));
}

pub fn intValue_u64(sema: *Sema, ty: Type, x: u64) Error!Value {
    return .fromIndex(try sema.intern_pool.internInt(.{ .ty = ty.index, .storage = .{ .u64 = x } }));
}

pub fn floatValue(sema: *Sema, ty: Type, x: anytype) Error!Value {
    const storage: InternPool.Key.Float.Storage = switch (ty.floatBits()) {
        16 => .{ .f16 = @as(f16, @floatCast(x)) },
        32 => .{ .f32 = @as(f32, @floatCast(x)) },
        64 => .{ .f64 = @as(f64, @floatCast(x)) },
        80 => .{ .f80 = @as(f80, @floatCast(x)) },
        128 => .{ .f128 = @as(f128, @floatCast(x)) },
        else => unreachable,
    };
    return .fromIndex(try sema.intern_pool.get(.{ .float = .{ .ty = ty.index, .storage = storage } }));
}

pub fn ptrIntValue(sema: *Sema, ty: Type, x: u64) Error!Value {
    assert(ty.zigTypeTag(sema.intern_pool) == .pointer and !ty.isSlice(sema.intern_pool));
    assert(x != 0 or ty.isAllowzeroPtr(sema.intern_pool));
    return .fromIndex(try sema.intern_pool.internPtr(.{
        .ty = ty.index,
        .base_addr = .int,
        .byte_offset = x,
    }));
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

fn splat(sema: *Sema, ty: Type, val: Value) Error!Value {
    if (ty.zigTypeTag(sema.intern_pool) != .vector) return val;
    return sema.aggregateSplatValue(ty, val);
}

fn compareAll(sema: *Sema, lhs: Value, op: std.math.CompareOperator, rhs: Value, ty: Type) Error!bool {
    const ip = sema.intern_pool;
    if (ty.zigTypeTag(ip) == .vector) {
        var i: usize = 0;
        while (i < ty.vectorLen(ip)) : (i += 1) {
            const lhs_elem = try lhs.elemValue(ip, i);
            const rhs_elem = try rhs.elemValue(ip, i);
            if (!lhs_elem.compareScalar(op, rhs_elem, ty.scalarType(ip), ip)) return false;
        }
        return true;
    }
    return lhs.compareScalar(op, rhs, ty, ip);
}

fn overflowArithmeticTupleType(sema: *Sema, ty: Type) Error!Type {
    const ip = sema.intern_pool;
    const ov_ty: Type = if (ty.zigTypeTag(ip) == .vector)
        try sema.vectorType(.{ .len = ty.vectorLen(ip), .child = .u1_type })
    else
        .fromIndex(.u1_type);
    return .fromIndex(try ip.internTupleType(&.{ ty.index, ov_ty.index }, &.{ .none, .none }));
}

pub fn aggregateValue(sema: *Sema, ty: Type, elems: []const InternPool.Index) Error!Value {
    for (elems) |elem| {
        if (!Value.fromIndex(elem).isUndef(sema.intern_pool)) break;
    } else if (elems.len > 0) {
        return sema.undefValue(ty);
    }
    return .fromIndex(try sema.intern_pool.internAggregate(.{ .ty = ty.index, .storage = .{ .elems = elems } }));
}

pub fn bitpackValue(sema: *Sema, ty: Type, backing_int_val: Value) Error!Value {
    assert(backing_int_val.typeOf(sema.intern_pool).index == ty.bitpackBackingInt(sema.intern_pool).index);
    return .fromIndex(try sema.intern_pool.internBitpack(.{ .ty = ty.index, .backing_int_val = backing_int_val.index }));
}

pub fn vectorType(sema: *Sema, info: InternPool.Key.VectorType) Error!Type {
    return .fromIndex(try sema.intern_pool.internVectorType(info));
}

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

fn intFittingRange(sema: *Sema, min: Value, max: Value) Error!Type {
    const pool = sema.intern_pool;
    assert(!min.isUndef(pool));
    assert(!max.isUndef(pool));
    const sign = min.compareHetero(.lt, Value.zero_comptime_int, pool);
    const min_val_bits = sema.intBitsForValue(min, sign);
    const max_val_bits = sema.intBitsForValue(max, sign);
    return .fromIndex(try pool.internIntType(if (sign) .signed else .unsigned, @max(min_val_bits, max_val_bits)));
}

fn errMsg(sema: *Sema, src: LazySrcLoc, comptime format: []const u8, args: anytype) Allocator.Error!*ErrorMsg {
    assert(src.offset != .unneeded);
    const em = try ErrorMsg.create(sema.gpa, src, format, args);
    em.file = sema.current_zir_id;
    return em;
}

fn errNote(sema: *Sema, src: LazySrcLoc, parent: *ErrorMsg, comptime format: []const u8, args: anytype) Allocator.Error!void {
    const msg = try std.fmt.allocPrint(sema.gpa, format, args);
    errdefer sema.gpa.free(msg);
    parent.notes = try sema.gpa.realloc(parent.notes, parent.notes.len + 1);
    parent.notes[parent.notes.len - 1] = .{ .src_loc = src, .msg = msg };
}

fn failWithOwnedErrorMsg(sema: *Sema, block: ?*Block, em: *ErrorMsg) Error {
    @branchHint(.cold);
    _ = block;
    if (sema.session) |session| {
        if (session.failed_analysis != null) {
            sema.err = null;
            em.destroy(sema.gpa);
        } else {
            sema.err = em;
            session.failed_analysis = em;
        }
    } else {
        sema.writer.print("{s}\n", .{em.msg}) catch {};
        em.destroy(sema.gpa);
    }
    return error.AnalysisFail;
}

pub fn fail(sema: *Sema, block: *Block, src: LazySrcLoc, comptime format: []const u8, args: anytype) Error {
    const err_msg = try sema.errMsg(src, format, args);
    return sema.failWithOwnedErrorMsg(block, err_msg);
}

fn failWithNeededComptime(
    sema: *Sema,
    block: *Block,
    src: LazySrcLoc,
    /// `null` may be passed only if `block.isComptime()`. It indicates that the reason for the value
    /// being comptime-resolved is that the block is being comptime-evaluated.
    reason: ?ComptimeReason,
) Error {
    const msg, const fail_block = msg: {
        const msg = try sema.errMsg(src, "unable to resolve comptime value", .{});
        errdefer msg.destroy(sema.gpa);
        const fail_block = if (reason) |r| b: {
            try r.explain(sema, src, msg);
            break :b block;
        } else b: {
            break :b try block.explainWhyBlockIsComptime(sema, msg);
        };
        break :msg .{ msg, fail_block };
    };
    return sema.failWithOwnedErrorMsg(fail_block, msg);
}

/// Emit notes explaining why `ty` is comptime-only. `ty` is a comptime-only type reached from a
/// "needs comptime" diagnostic. Struct/union/tuple field notes attach to `src`,
/// as the REPL's `LazySrcLoc` has no container-field offset.
fn explainWhyTypeIsComptime(sema: *Sema, msg: *ErrorMsg, src: LazySrcLoc, ty: Type) Allocator.Error!void {
    const ip = sema.intern_pool;
    assert(ty.comptimeOnly(ip));
    switch (ty.zigTypeTag(ip)) {
        .bool,
        .int,
        .float,
        .error_set,
        .frame,
        .@"anyframe",
        .void,
        .@"enum",
        .@"opaque",
        .spirv,
        .pointer,
        => unreachable, // not comptime-only

        .comptime_float,
        .comptime_int,
        .enum_literal,
        .noreturn,
        .undefined,
        .null,
        => return, // no explanation needed

        .array, .vector => try sema.explainWhyTypeIsComptime(msg, src, ty.childType(ip)),
        .optional => try sema.explainWhyTypeIsComptime(msg, src, ty.optionalChild(ip)),
        .error_union => try sema.explainWhyTypeIsComptime(msg, src, ty.errorUnionPayload(ip)),

        .@"fn" => try sema.errNote(src, msg, "use '*const {f}' for a function pointer type", .{ty.fmt(ip)}),
        .type => try sema.errNote(src, msg, "types are not available at runtime", .{}),

        .@"struct" => if (!ty.isTuple(ip)) {
            const struct_type = ip.loadStructType(ty.index);
            for (0..struct_type.field_types.len) |i| {
                const field_ty: Type = .fromIndex(struct_type.field_types[i]);
                if (!field_ty.comptimeOnly(ip)) continue;
                try sema.errNote(src, msg, "struct requires comptime because of this field", .{});
                return sema.explainWhyTypeIsComptime(msg, src, field_ty);
            }
            unreachable;
        } else {
            const tuple = ip.indexToKey(ty.index).tuple_type;
            for (tuple.types, tuple.values) |field_ty_ip, field_val_ip| {
                if (field_val_ip != .none) continue;
                const field_ty: Type = .fromIndex(field_ty_ip);
                if (!field_ty.comptimeOnly(ip)) continue;
                try sema.errNote(src, msg, "tuple requires comptime because of field of type '{f}'", .{field_ty.fmt(ip)});
                return sema.explainWhyTypeIsComptime(msg, src, field_ty);
            }
            unreachable;
        },

        .@"union" => {
            const union_obj = ip.unionFields(ty.index);
            for (0..union_obj.field_types.len) |i| {
                const field_ty: Type = .fromIndex(union_obj.field_types[i]);
                if (!field_ty.comptimeOnly(ip)) continue;
                try sema.errNote(src, msg, "union requires comptime because of this field", .{});
                return sema.explainWhyTypeIsComptime(msg, src, field_ty);
            }
            unreachable;
        },
    }
}

fn srcNodeOffset(sema: *Sema, inst: Zir.Inst.Index) std.zig.Ast.Node.Offset {
    const tag = sema.zir.instructions.items(.tag)[@backingInt(inst)];
    const data = sema.zir.instructions.items(.data)[@backingInt(inst)];
    return switch (Zir.Inst.Tag.data_tags[@backingInt(tag)]) {
        .pl_node => data.pl_node.src_node,
        .un_node => data.un_node.src_node,
        .node => data.node,
        else => .zero,
    };
}

pub fn failWithUseOfUndef(sema: *Sema) Error {
    return sema.fail(sema.block, sema.block.nodeOffset(.zero), "use of undefined value here causes illegal behavior", .{});
}

pub fn failWithDivideByZero(sema: *Sema) Error {
    return sema.fail(sema.block, sema.block.nodeOffset(.zero), "division by zero here causes illegal behavior", .{});
}

pub fn failWithIntegerOverflow(sema: *Sema, ty: Type, val: Value) Error {
    return sema.fail(sema.block, sema.block.nodeOffset(.zero), "overflow of integer type '{f}' with value '{f}'", .{ ty.fmt(sema.intern_pool), render_value.fmt(val, sema.intern_pool) });
}

pub fn failWithNegativeShiftAmount(sema: *Sema, shift_amt: Value) Error {
    return sema.fail(sema.block, sema.block.nodeOffset(.zero), "shift by negative amount '{f}'", .{render_value.fmt(shift_amt, sema.intern_pool)});
}

pub fn failWithTooLargeShiftAmount(sema: *Sema, ty: Type, shift_amt: Value) Error {
    return sema.fail(sema.block, sema.block.nodeOffset(.zero), "shift amount '{f}' is too large for operand type '{f}'", .{ render_value.fmt(shift_amt, sema.intern_pool), ty.fmt(sema.intern_pool) });
}

pub fn failWithUnsupportedComptimeShiftAmount(sema: *Sema) Error {
    return sema.fail(sema.block, sema.block.nodeOffset(.zero), "this implementation only supports comptime shift amounts of up to 2^64 - 1 bits", .{});
}

fn evalBinaryArith(sema: *Sema, inst: Zir.Inst.Index, tag: Zir.Inst.Tag) Error!?Value {
    const bin = sema.binData(inst);
    assert(bin.lhs != .none);
    assert(bin.rhs != .none);

    const lhs_val = try sema.resolveInst(bin.lhs);
    const rhs_val = try sema.resolveInst(bin.rhs);

    try sema.checkVectorizableBinaryOperands(Value.typeOf(lhs_val, sema.intern_pool), Value.typeOf(rhs_val, sema.intern_pool));
    switch (tag) {
        .div, .div_trunc, .div_floor, .div_ceil, .div_exact, .mod, .rem, .mod_rem => try sema.checkInvalidPtrIntArithmetic(Value.typeOf(lhs_val, sema.intern_pool)),
        else => {},
    }
    const resolved_type = try sema.resolvePeerTypes(&.{ lhs_val, rhs_val });
    const lhs = try sema.coerceValueToType(lhs_val, resolved_type.index);
    const rhs = try sema.coerceValueToType(rhs_val, resolved_type.index);

    const pool = sema.intern_pool;
    const scalar_tag = resolved_type.scalarType(pool).zigTypeTag(pool);
    try sema.checkArithmeticOp(scalar_tag, Value.typeOf(lhs_val, pool).zigTypeTag(pool), Value.typeOf(rhs_val, pool).zigTypeTag(pool), tag);

    // If it makes a difference whether the operands coerce to ints or floats before dividing, error;
    // if `lhs % rhs` is zero it does not matter (compiler: `zirDiv`).
    if (tag == .div) {
        const lhs_ty = Value.typeOf(lhs_val, pool);
        const rhs_ty = Value.typeOf(rhs_val, pool);
        if ((lhs_ty.zigTypeTag(pool) == .comptime_float and rhs_ty.zigTypeTag(pool) == .comptime_int) or
            (lhs_ty.zigTypeTag(pool) == .comptime_int and rhs_ty.zigTypeTag(pool) == .comptime_float))
        {
            const rem = arith.modRem(sema, resolved_type, lhs, rhs, .rem) catch unreachable;
            if (!rem.compareAllWithZero(.eq, pool)) {
                return sema.fail(sema.block, sema.block.nodeOffset(.zero), "ambiguous coercion of division operands '{f}' and '{f}'; non-zero remainder '{f}'", .{ lhs_ty.fmt(pool), rhs_ty.fmt(pool), render_value.fmt(rem, pool) });
            }
        }
    }

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
        .div_ceil => try arith.div(sema, resolved_type, lhs, rhs, .div_ceil),
        .div_exact => try arith.div(sema, resolved_type, lhs, rhs, .div_exact),
        .mod => try arith.modRem(sema, resolved_type, lhs, rhs, .mod),
        .rem => try arith.modRem(sema, resolved_type, lhs, rhs, .rem),
        .mod_rem => try sema.evalModRem(resolved_type, lhs_val, rhs_val, lhs, rhs),
        else => unreachable,
    };
}

fn evalModRem(sema: *Sema, resolved_type: Type, lhs_orig: Value, rhs_orig: Value, lhs: Value, rhs: Value) Error!Value {
    const ip = sema.intern_pool;
    const lhs_ty = Value.typeOf(lhs_orig, ip);
    const rhs_ty = Value.typeOf(rhs_orig, ip);
    const lhs_maybe_negative = !lhs_ty.scalarType(ip).isUnsignedInt(ip) and !lhs.compareAllWithZero(.gte, ip);
    const rhs_maybe_negative = !rhs_ty.scalarType(ip).isUnsignedInt(ip) and !rhs.compareAllWithZero(.gte, ip);
    const result = try arith.modRem(sema, resolved_type, lhs, rhs, .rem);
    if (lhs_maybe_negative or rhs_maybe_negative) {
        if (!result.compareAllWithZero(.eq, ip)) {
            return sema.fail(sema.block, sema.block.nodeOffset(.zero), "remainder division with '{f}' and '{f}': signed integers and floats must use @rem or @mod", .{ lhs_ty.fmt(ip), rhs_ty.fmt(ip) });
        }
    }
    return result;
}

/// The strategy chosen for peer type resolution, mirroring the compiler's PeerResolveStrategy.
const PeerResolveStrategy = enum {
    unknown,
    error_set,
    error_union,
    nullable,
    optional,
    array,
    vector,
    c_ptr,
    ptr,
    func,
    enum_or_union,
    comptime_int,
    comptime_float,
    fixed_int,
    fixed_float,
    tuple,
    exact,

    fn merge(a: PeerResolveStrategy, b: PeerResolveStrategy, reason_peer: *usize, b_peer_idx: usize) PeerResolveStrategy {
        const s0_is_a = @backingInt(a) <= @backingInt(b);
        const s0 = if (s0_is_a) a else b;
        const s1 = if (s0_is_a) b else a;

        const ReasonMethod = enum { all_s0, all_s1, either };

        const reason_method: ReasonMethod, const strat: PeerResolveStrategy = switch (s0) {
            .unknown => .{ .all_s1, s1 },
            .error_set => switch (s1) {
                .error_set => .{ .either, .error_set },
                else => .{ .all_s0, .error_union },
            },
            .error_union => switch (s1) {
                .error_union => .{ .either, .error_union },
                else => .{ .all_s0, .error_union },
            },
            .nullable => switch (s1) {
                .nullable => .{ .either, .nullable },
                .c_ptr => .{ .all_s1, .c_ptr },
                else => .{ .all_s0, .optional },
            },
            .optional => switch (s1) {
                .optional => .{ .either, .optional },
                .c_ptr => .{ .all_s1, .c_ptr },
                else => .{ .all_s0, .optional },
            },
            .array => switch (s1) {
                .array => .{ .either, .array },
                .vector => .{ .all_s1, .vector },
                else => .{ .all_s0, .array },
            },
            .vector => switch (s1) {
                .vector => .{ .either, .vector },
                else => .{ .all_s0, .vector },
            },
            .c_ptr => switch (s1) {
                .c_ptr => .{ .either, .c_ptr },
                else => .{ .all_s0, .c_ptr },
            },
            .ptr => switch (s1) {
                .ptr => .{ .either, .ptr },
                else => .{ .all_s0, .ptr },
            },
            .func => switch (s1) {
                .func => .{ .either, .func },
                else => .{ .all_s1, s1 },
            },
            .enum_or_union => switch (s1) {
                .enum_or_union => .{ .either, .enum_or_union },
                else => .{ .all_s0, .enum_or_union },
            },
            .comptime_int => switch (s1) {
                .comptime_int => .{ .either, .comptime_int },
                else => .{ .all_s1, s1 },
            },
            .comptime_float => switch (s1) {
                .comptime_float => .{ .either, .comptime_float },
                else => .{ .all_s1, s1 },
            },
            .fixed_int => switch (s1) {
                .fixed_int => .{ .either, .fixed_int },
                else => .{ .all_s1, s1 },
            },
            .fixed_float => switch (s1) {
                .fixed_float => .{ .either, .fixed_float },
                else => .{ .all_s1, s1 },
            },
            .tuple => switch (s1) {
                .exact => .{ .all_s1, .exact },
                else => .{ .all_s0, .tuple },
            },
            .exact => .{ .all_s0, .exact },
        };

        switch (reason_method) {
            .all_s0 => if (!s0_is_a) {
                reason_peer.* = b_peer_idx;
            },
            .all_s1 => if (s0_is_a) {
                reason_peer.* = b_peer_idx;
            },
            .either => {
                reason_peer.* = @min(reason_peer.*, b_peer_idx);
            },
        }

        return strat;
    }

    fn select(ty: Type, pool: *const InternPool) PeerResolveStrategy {
        return switch (ty.zigTypeTag(pool)) {
            .type, .void, .bool, .@"opaque", .spirv, .frame, .@"anyframe" => .exact,
            .noreturn, .undefined => .unknown,
            .null => .nullable,
            .comptime_int => .comptime_int,
            .int => .fixed_int,
            .comptime_float => .comptime_float,
            .float => .fixed_float,
            .pointer => if (ty.ptrInfo(pool).flags.size == .c) .c_ptr else .ptr,
            .array => .array,
            .vector => .vector,
            .optional => .optional,
            .error_set => .error_set,
            .error_union => .error_union,
            .enum_literal, .@"enum", .@"union" => .enum_or_union,
            .@"struct" => if (ty.isTuple(pool)) .tuple else .exact,
            .@"fn" => .func,
        };
    }
};

/// The outcome of peer type resolution, mirroring the compiler's PeerResolveResult.
const PeerResolveResult = union(enum) {
    success: Type,
    conflict: struct {
        peer_idx_a: usize,
        peer_idx_b: usize,
    },
    field_error: struct {
        field_name: InternPool.NullTerminatedString,
        field_types: []Type,
        sub_result: *PeerResolveResult,
    },

    /// Report a conflict as a REPL diagnostic. The compiler additionally attaches per-candidate source
    /// notes via a PeerTypeCandidateSrc; the REPL has no per-peer source surface here, so it reports the
    /// conflicting types (and the field chain) without those notes.
    fn report(result: PeerResolveResult, sema: *Sema, peer_tys_in: []const Type) Error!*ErrorMsg {
        const ip = sema.intern_pool;
        const src = sema.block.nodeOffset(.zero);
        var opt_msg: ?*ErrorMsg = null;
        errdefer if (opt_msg) |msg| msg.destroy(sema.gpa);

        var peer_tys = peer_tys_in;
        var cur = result;
        while (true) {
            var conflict_idx: [2]usize = undefined;
            switch (cur) {
                .success => unreachable,
                .conflict => |conflict| {
                    conflict_idx = .{ conflict.peer_idx_a, conflict.peer_idx_b };
                },
                .field_error => |field_error| {
                    const fmt = "struct field '{s}' has conflicting types";
                    const args = .{ip.stringSlice(field_error.field_name)};
                    if (opt_msg) |msg| {
                        try sema.errNote(src, msg, fmt, args);
                    } else {
                        opt_msg = try sema.errMsg(src, fmt, args);
                    }
                    cur = field_error.sub_result.*;
                    peer_tys = field_error.field_types;
                    continue;
                },
            }

            if (conflict_idx[1] < conflict_idx[0]) std.mem.swap(usize, &conflict_idx[0], &conflict_idx[1]);
            const conflict_tys: [2]Type = .{ peer_tys[conflict_idx[0]], peer_tys[conflict_idx[1]] };
            const fmt = "incompatible types: '{f}' and '{f}'";
            const args = .{ conflict_tys[0].fmt(ip), conflict_tys[1].fmt(ip) };
            if (opt_msg) |msg| {
                try sema.errNote(src, msg, fmt, args);
            } else {
                opt_msg = try sema.errMsg(src, fmt, args);
            }
            break;
        }
        return opt_msg.?;
    }
};

const ArrayLike = struct {
    len: u64,
    /// `noreturn` indicates that this type is `struct{}` so can coerce to anything.
    elem_ty: Type,
};

fn typeIsArrayLike(sema: *Sema, ty: Type) ?ArrayLike {
    const ip = sema.intern_pool;
    return switch (ty.zigTypeTag(ip)) {
        .array => .{ .len = ty.arrayLen(ip), .elem_ty = ty.childType(ip) },
        .@"struct" => {
            if (!ty.isTuple(ip)) return null;
            const field_count = sema.structFieldCount(ty.index) catch return null;
            if (field_count == 0) return .{ .len = 0, .elem_ty = .fromIndex(.noreturn_type) };
            const elem_ty = ty.fieldType(0, ip);
            for (1..field_count) |i| {
                if (ty.fieldType(i, ip).index != elem_ty.index) return null;
            }
            return .{ .len = field_count, .elem_ty = elem_ty };
        },
        else => null,
    };
}

fn maybeMergeErrorSets(sema: *Sema, e0: Type, e1: Type) Error!Type {
    // e0 -> e1
    if (.ok == try sema.coerceInMemoryAllowedErrorSets(e1, e0)) return e1;
    // e1 -> e0
    if (.ok == try sema.coerceInMemoryAllowedErrorSets(e0, e1)) return e0;
    return sema.errorSetMerge(e0.index, e1.index);
}

fn resolvePairInMemoryCoercible(sema: *Sema, ty_a: Type, ty_b: Type) Error!?Type {
    // ty_b -> ty_a
    if (.ok == try sema.coerceInMemoryAllowed(ty_a, ty_b, false, null)) return ty_a;
    // ty_a -> ty_b
    if (.ok == try sema.coerceInMemoryAllowed(ty_b, ty_a, false, null)) return ty_b;
    return null;
}

/// Resolve the common type of a set of peer values, mirroring the compiler's resolvePeerTypes.
fn resolvePeerTypes(sema: *Sema, instructions: []const Value) Error!Type {
    const ip = sema.intern_pool;
    switch (instructions.len) {
        0 => return .fromIndex(.noreturn_type),
        1 => return Value.typeOf(instructions[0], ip),
        else => {},
    }

    // Fast path: everything the same type.
    same_type: {
        const ty = Value.typeOf(instructions[0], ip);
        for (instructions[1..]) |inst| {
            if (Value.typeOf(inst, ip).index != ty.index) break :same_type;
        }
        return ty;
    }

    const peer_tys = try sema.arena.alloc(?Type, instructions.len);
    const peer_vals = try sema.arena.alloc(?Value, instructions.len);
    for (instructions, peer_tys, peer_vals) |inst, *ty, *val| {
        ty.* = Value.typeOf(inst, ip);
        val.* = if (inst.is_comptime) inst else null;
    }

    switch (try sema.resolvePeerTypesInner(peer_tys, peer_vals)) {
        .success => |ty| return ty,
        else => |result| {
            const buf_tys = try sema.arena.alloc(Type, instructions.len);
            for (buf_tys, instructions) |*ty, inst| ty.* = Value.typeOf(inst, ip);
            const msg = try result.report(sema, buf_tys);
            return sema.failWithOwnedErrorMsg(sema.block, msg);
        },
    }
}

fn defaultAddressSpace(context: enum { global_constant, global_mutable, local, function }) std.lang.AddressSpace {
    if (context == .function and @import("builtin").target.cpu.arch == .avr) return .flash;
    return .generic;
}

fn resolvePeerTypesInner(sema: *Sema, peer_tys: []?Type, peer_vals: []?Value) Error!PeerResolveResult {
    const ip = sema.intern_pool;

    var strat_reason: usize = 0;
    var s: PeerResolveStrategy = .unknown;
    for (peer_tys, 0..) |opt_ty, i| {
        const ty = opt_ty orelse continue;
        s = s.merge(PeerResolveStrategy.select(ty, ip), &strat_reason, i);
    }

    if (s == .unknown) {
        s = .exact;
    } else {
        for (peer_tys) |*ty_ptr| {
            const ty = ty_ptr.* orelse continue;
            switch (ty.zigTypeTag(ip)) {
                .noreturn, .undefined => ty_ptr.* = null,
                else => {},
            }
        }
    }

    switch (s) {
        .unknown => unreachable,

        .error_set => {
            var final_set: ?Type = null;
            for (peer_tys, 0..) |opt_ty, i| {
                const ty = opt_ty orelse continue;
                if (ty.zigTypeTag(ip) != .error_set) return .{ .conflict = .{ .peer_idx_a = strat_reason, .peer_idx_b = i } };
                if (final_set) |cur_set| {
                    final_set = try sema.maybeMergeErrorSets(cur_set, ty);
                } else {
                    final_set = ty;
                }
            }
            return .{ .success = final_set.? };
        },

        .error_union => {
            var final_set: ?Type = null;
            for (peer_tys, peer_vals) |*ty_ptr, *val_ptr| {
                const ty = ty_ptr.* orelse continue;
                const set_ty = switch (ty.zigTypeTag(ip)) {
                    .error_set => blk: {
                        ty_ptr.* = null;
                        val_ptr.* = null;
                        break :blk ty;
                    },
                    .error_union => blk: {
                        const set_ty = ty.errorUnionSet(ip);
                        ty_ptr.* = ty.errorUnionPayload(ip);
                        if (val_ptr.*) |eu_val| switch (ip.indexToKey(eu_val.index)) {
                            .error_union => |eu| switch (eu.val) {
                                .payload => |payload_ip| val_ptr.* = Value.fromIndex(payload_ip),
                                .err_name => val_ptr.* = null,
                            },
                            .undef => val_ptr.* = Value.fromIndex(try ip.get(.{ .undef = ty_ptr.*.?.index })),
                            else => unreachable,
                        };
                        break :blk set_ty;
                    },
                    else => continue,
                };
                if (final_set) |cur_set| {
                    final_set = try sema.maybeMergeErrorSets(cur_set, set_ty);
                } else {
                    final_set = set_ty;
                }
            }
            assert(final_set != null);
            const final_payload = switch (try sema.resolvePeerTypesInner(peer_tys, peer_vals)) {
                .success => |ty| ty,
                else => |result| return result,
            };
            return .{ .success = .fromIndex(try ip.internErrorUnionType(.{ .error_set_type = final_set.?.index, .payload_type = final_payload.index })) };
        },

        .nullable => {
            for (peer_tys, 0..) |opt_ty, i| {
                const ty = opt_ty orelse continue;
                if (ty.index != .null_type) return .{ .conflict = .{ .peer_idx_a = strat_reason, .peer_idx_b = i } };
            }
            return .{ .success = .fromIndex(.null_type) };
        },

        .optional => {
            for (peer_tys, peer_vals) |*ty_ptr, *val_ptr| {
                const ty = ty_ptr.* orelse continue;
                switch (ty.zigTypeTag(ip)) {
                    .null => {
                        ty_ptr.* = null;
                        val_ptr.* = null;
                    },
                    .optional => {
                        ty_ptr.* = ty.optionalChild(ip);
                        if (val_ptr.*) |opt_val| {
                            if (!opt_val.isUndef(ip)) {
                                const ov = ip.indexToKey(opt_val.index).opt.val;
                                val_ptr.* = if (ov == .none) null else Value.fromIndex(ov);
                            } else val_ptr.* = null;
                        }
                    },
                    else => {},
                }
            }
            const child_ty = switch (try sema.resolvePeerTypesInner(peer_tys, peer_vals)) {
                .success => |ty| ty,
                else => |result| return result,
            };
            return .{ .success = .fromIndex(try ip.internOptionalType(child_ty.index)) };
        },

        .array => {
            var opt_first_idx: ?usize = null;
            var opt_first_arr_idx: ?usize = null;
            var len: u64 = undefined;
            var sentinel: ?Value = undefined;
            var elem_ty: Type = undefined;

            for (peer_tys, 0..) |*ty_ptr, i| {
                const ty = ty_ptr.* orelse continue;

                if (!ty.isArrayOrVector(ip)) {
                    const arr_like = sema.typeIsArrayLike(ty) orelse return .{ .conflict = .{ .peer_idx_a = strat_reason, .peer_idx_b = i } };
                    if (opt_first_idx) |first_idx| {
                        if (arr_like.len != len) return .{ .conflict = .{ .peer_idx_a = first_idx, .peer_idx_b = i } };
                    } else {
                        opt_first_idx = i;
                        len = arr_like.len;
                    }
                    sentinel = null;
                    continue;
                }

                const first_arr_idx = opt_first_arr_idx orelse {
                    if (opt_first_idx == null) {
                        opt_first_idx = i;
                        len = ty.arrayLen(ip);
                        sentinel = ty.sentinel(ip);
                    }
                    opt_first_arr_idx = i;
                    elem_ty = ty.childType(ip);
                    continue;
                };

                if (ty.arrayLen(ip) != len) return .{ .conflict = .{ .peer_idx_a = first_arr_idx, .peer_idx_b = i } };

                const peer_elem_ty = ty.childType(ip);
                if (peer_elem_ty.index != elem_ty.index) coerce: {
                    if (.ok == try sema.coerceInMemoryAllowed(elem_ty, peer_elem_ty, false, null)) break :coerce;
                    if (.ok == try sema.coerceInMemoryAllowed(peer_elem_ty, elem_ty, false, null)) {
                        elem_ty = peer_elem_ty;
                        break :coerce;
                    }
                    return .{ .conflict = .{ .peer_idx_a = first_arr_idx, .peer_idx_b = i } };
                }

                if (sentinel) |cur_sent| {
                    if (ty.sentinel(ip)) |peer_sent| {
                        if (peer_sent.index != cur_sent.index) sentinel = null;
                    } else {
                        sentinel = null;
                    }
                }
            }

            assert(opt_first_arr_idx != null);
            return .{ .success = .fromIndex(try ip.internArrayType(.{
                .len = len,
                .child = elem_ty.index,
                .sentinel = if (sentinel) |sent_val| sent_val.index else .none,
            })) };
        },

        .vector => {
            var len: ?u64 = null;
            var first_idx: usize = undefined;
            for (peer_tys, peer_vals, 0..) |*ty_ptr, *val_ptr, i| {
                const ty = ty_ptr.* orelse continue;
                if (!ty.isArrayOrVector(ip)) {
                    const arr_like = sema.typeIsArrayLike(ty) orelse return .{ .conflict = .{ .peer_idx_a = strat_reason, .peer_idx_b = i } };
                    if (len) |expect_len| {
                        if (arr_like.len != expect_len) return .{ .conflict = .{ .peer_idx_a = first_idx, .peer_idx_b = i } };
                    } else {
                        len = arr_like.len;
                        first_idx = i;
                    }
                    ty_ptr.* = null;
                    val_ptr.* = null;
                    continue;
                }
                if (len) |expect_len| {
                    if (ty.arrayLen(ip) != expect_len) return .{ .conflict = .{ .peer_idx_a = first_idx, .peer_idx_b = i } };
                } else {
                    len = ty.arrayLen(ip);
                    first_idx = i;
                }
                ty_ptr.* = ty.childType(ip);
                val_ptr.* = null;
            }
            const child_ty = switch (try sema.resolvePeerTypesInner(peer_tys, peer_vals)) {
                .success => |ty| ty,
                else => |result| return result,
            };
            return .{ .success = try sema.vectorType(.{ .len = @intCast(len.?), .child = child_ty.index }) };
        },

        .c_ptr => {
            const target = @import("builtin").target;
            var opt_ptr_info: ?InternPool.Key.PtrType = null;
            var first_idx: usize = undefined;
            for (peer_tys, peer_vals, 0..) |opt_ty, opt_val, i| {
                const ty = opt_ty orelse continue;
                switch (ty.zigTypeTag(ip)) {
                    .comptime_int => continue,
                    .int => {
                        if (opt_val != null) {
                            continue;
                        } else {
                            if (ty.intInfo(ip).bits <= target.ptrBitWidth()) continue;
                        }
                    },
                    .null => continue,
                    else => {},
                }
                if (!ty.isPtrAtRuntime(ip)) return .{ .conflict = .{ .peer_idx_a = strat_reason, .peer_idx_b = i } };
                const peer_info = ty.ptrInfo(ip);
                var ptr_info = opt_ptr_info orelse {
                    opt_ptr_info = peer_info;
                    opt_ptr_info.?.flags.size = .c;
                    first_idx = i;
                    continue;
                };
                ptr_info.child = ((try sema.resolvePairInMemoryCoercible(.fromIndex(ptr_info.child), .fromIndex(peer_info.child))) orelse {
                    return .{ .conflict = .{ .peer_idx_a = first_idx, .peer_idx_b = i } };
                }).index;
                if (ptr_info.sentinel != .none and peer_info.sentinel != .none) {
                    const peer_sent = try ip.getCoerced(ptr_info.sentinel, ptr_info.child);
                    const ptr_sent = try ip.getCoerced(peer_info.sentinel, ptr_info.child);
                    ptr_info.sentinel = if (ptr_sent == peer_sent) ptr_sent else .none;
                } else {
                    ptr_info.sentinel = .none;
                }
                ptr_info.flags.alignment = a: {
                    if (ptr_info.flags.alignment == .none and peer_info.flags.alignment == .none) break :a .none;
                    const cur_align = switch (ptr_info.flags.alignment) {
                        .none => Type.fromIndex(ptr_info.child).abiAlignment(ip),
                        else => ptr_info.flags.alignment,
                    };
                    const new_align = switch (peer_info.flags.alignment) {
                        .none => Type.fromIndex(peer_info.child).abiAlignment(ip),
                        else => peer_info.flags.alignment,
                    };
                    break :a .minStrict(cur_align, new_align);
                };
                if (ptr_info.flags.address_space != peer_info.flags.address_space) return .{ .conflict = .{ .peer_idx_a = first_idx, .peer_idx_b = i } };
                if (ptr_info.packed_offset.bit_offset != peer_info.packed_offset.bit_offset or
                    ptr_info.packed_offset.host_size != peer_info.packed_offset.host_size) return .{ .conflict = .{ .peer_idx_a = first_idx, .peer_idx_b = i } };
                ptr_info.flags.is_const = ptr_info.flags.is_const or peer_info.flags.is_const;
                ptr_info.flags.is_volatile = ptr_info.flags.is_volatile or peer_info.flags.is_volatile;
                opt_ptr_info = ptr_info;
            }
            return .{ .success = .fromIndex(try ip.internPtrType(opt_ptr_info.?)) };
        },

        .ptr => {
            var opt_slice_idx: ?usize = null;
            var opt_ptr_info: ?InternPool.Key.PtrType = null;
            var first_idx: usize = undefined;
            var other_idx: usize = undefined;

            for (peer_tys, 0..) |opt_ty, i| {
                const ty = opt_ty orelse continue;
                const peer_info: InternPool.Key.PtrType = switch (ty.zigTypeTag(ip)) {
                    .pointer => ty.ptrInfo(ip),
                    .@"fn" => .{ .child = ty.index, .flags = .{ .address_space = defaultAddressSpace(.global_constant) } },
                    else => return .{ .conflict = .{ .peer_idx_a = strat_reason, .peer_idx_b = i } },
                };
                switch (peer_info.flags.size) {
                    .one, .many => {},
                    .slice => opt_slice_idx = i,
                    .c => return .{ .conflict = .{ .peer_idx_a = strat_reason, .peer_idx_b = i } },
                }

                var ptr_info = opt_ptr_info orelse {
                    opt_ptr_info = peer_info;
                    first_idx = i;
                    continue;
                };
                other_idx = i;
                const generic_err: PeerResolveResult = .{ .conflict = .{ .peer_idx_a = first_idx, .peer_idx_b = i } };

                ptr_info.flags.alignment = a: {
                    if (ptr_info.flags.alignment == .none and peer_info.flags.alignment == .none) break :a .none;
                    const cur_align = switch (ptr_info.flags.alignment) {
                        .none => Type.fromIndex(ptr_info.child).abiAlignment(ip),
                        else => ptr_info.flags.alignment,
                    };
                    const new_align = switch (peer_info.flags.alignment) {
                        .none => Type.fromIndex(peer_info.child).abiAlignment(ip),
                        else => peer_info.flags.alignment,
                    };
                    break :a .minStrict(cur_align, new_align);
                };
                if (ptr_info.flags.address_space != peer_info.flags.address_space) return generic_err;
                if (ptr_info.packed_offset.bit_offset != peer_info.packed_offset.bit_offset or
                    ptr_info.packed_offset.host_size != peer_info.packed_offset.host_size) return generic_err;
                ptr_info.flags.is_const = ptr_info.flags.is_const or peer_info.flags.is_const;
                ptr_info.flags.is_volatile = ptr_info.flags.is_volatile or peer_info.flags.is_volatile;
                ptr_info.flags.is_allowzero = ptr_info.flags.is_allowzero or peer_info.flags.is_allowzero;

                const peer_sentinel: InternPool.Index = switch (peer_info.flags.size) {
                    .one => switch (ip.indexToKey(peer_info.child)) {
                        .array_type => |array_type| array_type.sentinel,
                        else => .none,
                    },
                    .many, .slice => peer_info.sentinel,
                    .c => unreachable,
                };
                const cur_sentinel: InternPool.Index = switch (ptr_info.flags.size) {
                    .one => switch (ip.indexToKey(ptr_info.child)) {
                        .array_type => |array_type| array_type.sentinel,
                        else => .none,
                    },
                    .many, .slice => ptr_info.sentinel,
                    .c => unreachable,
                };

                const peer_pointee_array = sema.typeIsArrayLike(.fromIndex(peer_info.child));
                const cur_pointee_array = sema.typeIsArrayLike(.fromIndex(ptr_info.child));

                good: {
                    switch (peer_info.flags.size) {
                        .one => switch (ptr_info.flags.size) {
                            .one => {
                                if (try sema.resolvePairInMemoryCoercible(.fromIndex(ptr_info.child), .fromIndex(peer_info.child))) |pointee| {
                                    ptr_info.child = pointee.index;
                                    break :good;
                                }
                                const cur_arr = cur_pointee_array orelse return generic_err;
                                const peer_arr = peer_pointee_array orelse return generic_err;
                                if (try sema.resolvePairInMemoryCoercible(cur_arr.elem_ty, peer_arr.elem_ty)) |elem_ty| {
                                    if (cur_arr.len == peer_arr.len) {
                                        ptr_info.child = try ip.internArrayType(.{ .len = cur_arr.len, .child = elem_ty.index });
                                        break :good;
                                    }
                                    ptr_info.flags.size = .slice;
                                    ptr_info.child = elem_ty.index;
                                    break :good;
                                }
                                if (peer_arr.elem_ty.index == .noreturn_type) {
                                    ptr_info.flags.size = .slice;
                                    ptr_info.child = cur_arr.elem_ty.index;
                                    break :good;
                                }
                                if (cur_arr.elem_ty.index == .noreturn_type) {
                                    ptr_info.flags.size = .slice;
                                    ptr_info.child = peer_arr.elem_ty.index;
                                    break :good;
                                }
                                return generic_err;
                            },
                            .many => {
                                const arr = peer_pointee_array orelse return generic_err;
                                if (try sema.resolvePairInMemoryCoercible(.fromIndex(ptr_info.child), arr.elem_ty)) |pointee| {
                                    ptr_info.child = pointee.index;
                                    break :good;
                                }
                                if (arr.elem_ty.index == .noreturn_type) break :good;
                                return generic_err;
                            },
                            .slice => {
                                const arr = peer_pointee_array orelse return generic_err;
                                if (try sema.resolvePairInMemoryCoercible(.fromIndex(ptr_info.child), arr.elem_ty)) |pointee| {
                                    ptr_info.child = pointee.index;
                                    break :good;
                                }
                                if (arr.elem_ty.index == .noreturn_type) break :good;
                                return generic_err;
                            },
                            .c => unreachable,
                        },
                        .many => switch (ptr_info.flags.size) {
                            .one => {
                                const arr = cur_pointee_array orelse return generic_err;
                                if (try sema.resolvePairInMemoryCoercible(arr.elem_ty, .fromIndex(peer_info.child))) |pointee| {
                                    ptr_info.flags.size = .many;
                                    ptr_info.child = pointee.index;
                                    break :good;
                                }
                                if (arr.elem_ty.index == .noreturn_type) {
                                    ptr_info.flags.size = .many;
                                    ptr_info.child = peer_info.child;
                                    break :good;
                                }
                                return generic_err;
                            },
                            .many => {
                                if (try sema.resolvePairInMemoryCoercible(.fromIndex(ptr_info.child), .fromIndex(peer_info.child))) |pointee| {
                                    ptr_info.child = pointee.index;
                                    break :good;
                                }
                                return generic_err;
                            },
                            .slice => {
                                if (opt_slice_idx) |slice_idx| return .{ .conflict = .{ .peer_idx_a = slice_idx, .peer_idx_b = i } };
                                if (try sema.resolvePairInMemoryCoercible(.fromIndex(ptr_info.child), .fromIndex(peer_info.child))) |pointee| {
                                    ptr_info.flags.size = .many;
                                    ptr_info.child = pointee.index;
                                    break :good;
                                }
                                return generic_err;
                            },
                            .c => unreachable,
                        },
                        .slice => switch (ptr_info.flags.size) {
                            .one => {
                                const arr = cur_pointee_array orelse return generic_err;
                                if (try sema.resolvePairInMemoryCoercible(arr.elem_ty, .fromIndex(peer_info.child))) |pointee| {
                                    ptr_info.flags.size = .slice;
                                    ptr_info.child = pointee.index;
                                    break :good;
                                }
                                if (arr.elem_ty.index == .noreturn_type) {
                                    ptr_info.flags.size = .slice;
                                    ptr_info.child = peer_info.child;
                                    break :good;
                                }
                                return generic_err;
                            },
                            .many => return generic_err,
                            .slice => {
                                if (try sema.resolvePairInMemoryCoercible(.fromIndex(ptr_info.child), .fromIndex(peer_info.child))) |pointee| {
                                    ptr_info.child = pointee.index;
                                    break :good;
                                }
                                return generic_err;
                            },
                            .c => unreachable,
                        },
                        .c => unreachable,
                    }
                }

                const sentinel_ty = switch (ptr_info.flags.size) {
                    .one => switch (ip.indexToKey(ptr_info.child)) {
                        .array_type => |array_type| array_type.child,
                        else => ptr_info.child,
                    },
                    .many, .slice, .c => ptr_info.child,
                };

                sentinel: {
                    no_sentinel: {
                        if (peer_sentinel == .none) break :no_sentinel;
                        if (cur_sentinel == .none) break :no_sentinel;
                        const peer_sent_coerced = try ip.getCoerced(peer_sentinel, sentinel_ty);
                        const cur_sent_coerced = try ip.getCoerced(cur_sentinel, sentinel_ty);
                        if (peer_sent_coerced != cur_sent_coerced) break :no_sentinel;
                        if (ptr_info.flags.size == .one) switch (ip.indexToKey(ptr_info.child)) {
                            .array_type => |array_type| ptr_info.child = try ip.internArrayType(.{ .len = array_type.len, .child = array_type.child, .sentinel = cur_sent_coerced }),
                            else => unreachable,
                        } else {
                            ptr_info.sentinel = cur_sent_coerced;
                        }
                        break :sentinel;
                    }
                    ptr_info.sentinel = .none;
                    if (ptr_info.flags.size == .one) switch (ip.indexToKey(ptr_info.child)) {
                        .array_type => |array_type| ptr_info.child = try ip.internArrayType(.{ .len = array_type.len, .child = array_type.child, .sentinel = .none }),
                        else => {},
                    };
                }

                opt_ptr_info = ptr_info;
            }

            const pointee = opt_ptr_info.?.child;
            switch (pointee) {
                .noreturn_type => return .{ .conflict = .{ .peer_idx_a = first_idx, .peer_idx_b = other_idx } },
                else => switch (ip.indexToKey(pointee)) {
                    .array_type => |array_type| if (array_type.child == .noreturn_type) return .{ .conflict = .{ .peer_idx_a = first_idx, .peer_idx_b = other_idx } },
                    else => {},
                },
            }
            return .{ .success = .fromIndex(try ip.internPtrType(opt_ptr_info.?)) };
        },

        .func => {
            var opt_cur_ty: ?Type = null;
            var first_idx: usize = undefined;
            for (peer_tys, 0..) |opt_ty, i| {
                const ty = opt_ty orelse continue;
                const cur_ty = opt_cur_ty orelse {
                    opt_cur_ty = ty;
                    first_idx = i;
                    continue;
                };
                if (ty.zigTypeTag(ip) != .@"fn") return .{ .conflict = .{ .peer_idx_a = strat_reason, .peer_idx_b = i } };
                if (.ok == try sema.coerceInMemoryAllowedFns(cur_ty, ty, false)) continue;
                if (.ok == try sema.coerceInMemoryAllowedFns(ty, cur_ty, false)) {
                    opt_cur_ty = ty;
                    continue;
                }
                return .{ .conflict = .{ .peer_idx_a = first_idx, .peer_idx_b = i } };
            }
            return .{ .success = opt_cur_ty.? };
        },

        .enum_or_union => {
            var opt_cur_ty: ?Type = null;
            var cur_ty_idx: usize = undefined;
            for (peer_tys, 0..) |opt_ty, i| {
                const ty = opt_ty orelse continue;
                switch (ty.zigTypeTag(ip)) {
                    .enum_literal, .@"enum", .@"union" => {},
                    else => return .{ .conflict = .{ .peer_idx_a = strat_reason, .peer_idx_b = i } },
                }
                const cur_ty = opt_cur_ty orelse {
                    opt_cur_ty = ty;
                    cur_ty_idx = i;
                    continue;
                };
                const generic_err: PeerResolveResult = .{ .conflict = .{ .peer_idx_a = cur_ty_idx, .peer_idx_b = i } };
                switch (cur_ty.zigTypeTag(ip)) {
                    .enum_literal => {
                        opt_cur_ty = ty;
                        cur_ty_idx = i;
                    },
                    .@"enum" => switch (ty.zigTypeTag(ip)) {
                        .enum_literal => {},
                        .@"enum" => if (ty.index != cur_ty.index) return generic_err,
                        .@"union" => {
                            if (ty.unionTagTypeHypothetical(ip).index != cur_ty.index) return generic_err;
                            opt_cur_ty = ty;
                            cur_ty_idx = i;
                        },
                        else => unreachable,
                    },
                    .@"union" => switch (ty.zigTypeTag(ip)) {
                        .enum_literal => {},
                        .@"enum" => if (ty.index != cur_ty.unionTagTypeHypothetical(ip).index) return generic_err,
                        .@"union" => if (ty.index != cur_ty.index) return generic_err,
                        else => unreachable,
                    },
                    else => unreachable,
                }
            }
            return .{ .success = opt_cur_ty.? };
        },

        .comptime_int => {
            for (peer_tys, 0..) |opt_ty, i| {
                const ty = opt_ty orelse continue;
                switch (ty.zigTypeTag(ip)) {
                    .comptime_int => {},
                    else => return .{ .conflict = .{ .peer_idx_a = strat_reason, .peer_idx_b = i } },
                }
            }
            return .{ .success = .fromIndex(.comptime_int_type) };
        },

        .comptime_float => {
            for (peer_tys, 0..) |opt_ty, i| {
                const ty = opt_ty orelse continue;
                switch (ty.zigTypeTag(ip)) {
                    .comptime_int, .comptime_float => {},
                    else => return .{ .conflict = .{ .peer_idx_a = strat_reason, .peer_idx_b = i } },
                }
            }
            return .{ .success = .fromIndex(.comptime_float_type) };
        },

        .fixed_int => {
            var idx_unsigned: ?usize = null;
            var idx_signed: ?usize = null;
            var any_comptime_known = false;

            for (peer_tys, peer_vals, 0..) |opt_ty, *ptr_opt_val, i| {
                const ty = opt_ty orelse continue;
                const opt_val = ptr_opt_val.*;
                switch (ty.zigTypeTag(ip)) {
                    .comptime_int => {
                        if (opt_val == null or opt_val.?.isUndef(ip)) return .{ .conflict = .{ .peer_idx_a = strat_reason, .peer_idx_b = i } };
                        any_comptime_known = true;
                        continue;
                    },
                    .int => {},
                    else => return .{ .conflict = .{ .peer_idx_a = strat_reason, .peer_idx_b = i } },
                }
                if (opt_val != null) any_comptime_known = true;
                const info = ty.intInfo(ip);
                const idx_ptr = switch (info.signedness) {
                    .unsigned => &idx_unsigned,
                    .signed => &idx_signed,
                };
                const largest_idx = idx_ptr.* orelse {
                    idx_ptr.* = i;
                    continue;
                };
                const cur_info = peer_tys[largest_idx].?.intInfo(ip);
                if (info.bits > cur_info.bits) idx_ptr.* = i;
            }

            if (idx_signed == null) return .{ .success = peer_tys[idx_unsigned.?].? };
            if (idx_unsigned == null) return .{ .success = peer_tys[idx_signed.?].? };

            const unsigned_info = peer_tys[idx_unsigned.?].?.intInfo(ip);
            const signed_info = peer_tys[idx_signed.?].?.intInfo(ip);
            if (signed_info.bits > unsigned_info.bits) return .{ .success = peer_tys[idx_signed.?].? };

            // Legacy compatibility: comptime-known values get coerced down to the smallest fitting type.
            if (any_comptime_known) {
                if (unsigned_info.bits > signed_info.bits) return .{ .success = peer_tys[idx_unsigned.?].? };
                const idx = @min(idx_unsigned.?, idx_signed.?);
                return .{ .success = peer_tys[idx].? };
            }
            return .{ .conflict = .{ .peer_idx_a = idx_unsigned.?, .peer_idx_b = idx_signed.? } };
        },

        .fixed_float => {
            var opt_cur_ty: ?Type = null;
            for (peer_tys, 0..) |opt_ty, i| {
                const ty = opt_ty orelse continue;
                switch (ty.zigTypeTag(ip)) {
                    .comptime_float, .comptime_int, .int => {},
                    .float => {
                        if (opt_cur_ty) |cur_ty| {
                            if (cur_ty.index != ty.index) {
                                const bits = @max(cur_ty.floatBits(), ty.floatBits());
                                opt_cur_ty = switch (bits) {
                                    16 => .fromIndex(.f16_type),
                                    32 => .fromIndex(.f32_type),
                                    64 => .fromIndex(.f64_type),
                                    80 => .fromIndex(.f80_type),
                                    128 => .fromIndex(.f128_type),
                                    else => unreachable,
                                };
                            }
                        } else {
                            opt_cur_ty = ty;
                        }
                    },
                    else => return .{ .conflict = .{ .peer_idx_a = strat_reason, .peer_idx_b = i } },
                }
            }
            const cur_ty = opt_cur_ty.?;
            for (peer_tys, peer_vals, 0..) |opt_ty, opt_val, i| {
                const ty = opt_ty orelse continue;
                switch (ty.zigTypeTag(ip)) {
                    .comptime_float, .comptime_int, .float => {},
                    .int => {
                        if (opt_val != null) continue;
                        const int_info = ty.intInfo(ip);
                        const int_precision = int_info.bits - @intFromBool(int_info.signedness == .signed);
                        if (int_precision > cur_ty.floatSignificandBits()) return .{ .conflict = .{ .peer_idx_a = strat_reason, .peer_idx_b = i } };
                    },
                    else => unreachable,
                }
            }
            return .{ .success = cur_ty };
        },

        .tuple => {
            var opt_first_idx: ?usize = null;
            var field_count: usize = undefined;
            for (peer_tys, 0..) |opt_ty, i| {
                const ty = opt_ty orelse continue;
                if (!ty.isTuple(ip)) return .{ .conflict = .{ .peer_idx_a = strat_reason, .peer_idx_b = i } };
                const first_idx = opt_first_idx orelse {
                    opt_first_idx = i;
                    field_count = try sema.structFieldCount(ty.index);
                    continue;
                };
                if (try sema.structFieldCount(ty.index) != field_count) return .{ .conflict = .{ .peer_idx_a = first_idx, .peer_idx_b = i } };
            }
            assert(opt_first_idx != null);

            const field_types = try sema.arena.alloc(InternPool.Index, field_count);
            const field_vals = try sema.arena.alloc(InternPool.Index, field_count);
            const sub_peer_tys = try sema.arena.alloc(?Type, peer_tys.len);
            const sub_peer_vals = try sema.arena.alloc(?Value, peer_vals.len);

            for (field_types, field_vals, 0..) |*field_ty, *field_val, field_index| {
                for (peer_tys, peer_vals, sub_peer_tys, sub_peer_vals) |opt_ty, opt_val, *peer_field_ty, *peer_field_val| {
                    const ty = opt_ty orelse {
                        peer_field_ty.* = null;
                        peer_field_val.* = null;
                        continue;
                    };
                    peer_field_ty.* = ty.fieldType(field_index, ip);
                    peer_field_val.* = if (opt_val) |val| try val.fieldValue(field_index, ip) else null;
                }
                field_ty.* = switch (try sema.resolvePeerTypesInner(sub_peer_tys, sub_peer_vals)) {
                    .success => |ty| ty.index,
                    else => |result| {
                        const result_buf = try sema.arena.create(PeerResolveResult);
                        result_buf.* = result;
                        const field_name = try ip.getOrPutStringFmt(sema.gpa, "{d}", .{field_index}, .no_embedded_nulls);

                        // The error needs the field types, but the recursive call may have clobbered
                        // sub_peer_tys, so recompute them; already-resolved peers are left undefined.
                        const peer_field_tys = try sema.arena.alloc(Type, peer_tys.len);
                        for (peer_tys, peer_field_tys) |opt_ty, *peer_field_ty| {
                            const ty = opt_ty orelse continue;
                            peer_field_ty.* = ty.fieldType(field_index, ip);
                        }

                        return .{ .field_error = .{
                            .field_name = field_name,
                            .field_types = peer_field_tys,
                            .sub_result = result_buf,
                        } };
                    },
                };

                var comptime_val: ?Value = null;
                for (peer_tys) |opt_ty| {
                    const struct_ty = opt_ty orelse continue;
                    const uncoerced_field_val = (try struct_ty.structFieldValueComptime(sema, field_index)) orelse {
                        comptime_val = null;
                        break;
                    };
                    const coerced_val = sema.coerceExtra(uncoerced_field_val, field_ty.*, false) catch |err| switch (err) {
                        error.NotCoercible => {
                            comptime_val = null;
                            break;
                        },
                        else => |e| return e,
                    };
                    const existing = comptime_val orelse {
                        comptime_val = coerced_val;
                        continue;
                    };
                    if (coerced_val.index != existing.index) {
                        comptime_val = null;
                        break;
                    }
                }
                field_val.* = if (comptime_val) |v| v.index else .none;
            }

            return .{ .success = .fromIndex(try ip.internTupleType(field_types, field_vals)) };
        },

        .exact => {
            var expect_ty: ?Type = null;
            var first_idx: usize = undefined;
            for (peer_tys, 0..) |opt_ty, i| {
                const ty = opt_ty orelse continue;
                if (expect_ty) |expect| {
                    if (ty.index != expect.index) return .{ .conflict = .{ .peer_idx_a = first_idx, .peer_idx_b = i } };
                } else {
                    expect_ty = ty;
                    first_idx = i;
                }
            }
            return .{ .success = expect_ty.? };
        },
    }
}

/// The compiler's checkVectorizableBinaryOperands: arithmetic rejects a vector paired with a scalar,
/// or two vectors of differing length, before peer resolution runs.
fn checkInvalidPtrIntArithmetic(sema: *Sema, ty: Type) Error!void {
    const ip = sema.intern_pool;
    switch (ty.zigTypeTag(ip)) {
        .pointer => switch (ty.ptrInfo(ip).flags.size) {
            .one, .slice => return,
            .many, .c => return sema.failWithInvalidPtrArithmetic("pointer-integer", "addition and subtraction"),
        },
        else => return,
    }
}

fn failWithInvalidPtrArithmetic(sema: *Sema, arithmetic: []const u8, supports: []const u8) Error {
    const src = sema.block.nodeOffset(.zero);
    const msg = msg: {
        const msg = try sema.errMsg(src, "invalid {s} arithmetic operator", .{arithmetic});
        errdefer msg.destroy(sema.gpa);
        try sema.errNote(src, msg, "{s} arithmetic only supports {s}", .{ arithmetic, supports });
        break :msg msg;
    };
    return sema.failWithOwnedErrorMsg(sema.block, msg);
}

fn checkVectorizableBinaryOperands(sema: *Sema, lhs_ty: Type, rhs_ty: Type) Error!void {
    const ip = sema.intern_pool;
    const lhs_tag = lhs_ty.zigTypeTag(ip);
    const rhs_tag = rhs_ty.zigTypeTag(ip);
    if (lhs_tag != .vector and rhs_tag != .vector) return;

    const lhs_is_vector = switch (lhs_tag) {
        .vector, .array => true,
        else => false,
    };
    const rhs_is_vector = switch (rhs_tag) {
        .vector, .array => true,
        else => false,
    };
    const src = sema.block.nodeOffset(.zero);
    if (lhs_is_vector and rhs_is_vector) {
        if (lhs_ty.arrayLen(ip) != rhs_ty.arrayLen(ip)) {
            return sema.fail(sema.block, src, "vector length mismatch", .{});
        }
    } else {
        return sema.fail(sema.block, src, "mixed scalar and vector operands: '{f}' and '{f}'", .{ lhs_ty.fmt(ip), rhs_ty.fmt(ip) });
    }
}

fn refitIntToFixedWidth(sema: *Sema, comptime_int_idx: InternPool.Index, dest_ty: InternPool.Index) Error!Value {
    const ip = sema.intern_pool;
    const dest_info = Type.fromIndex(dest_ty).intInfo(ip);
    var space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
    const result_big = ip.indexToKey(comptime_int_idx).int.storage.toBigInt(&space);
    if (!result_big.fitsInTwosComp(dest_info.signedness, dest_info.bits)) {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "type '{f}' cannot represent integer value '{f}'", .{ Type.fromIndex(dest_ty).fmt(ip), render_value.fmt(.{ .index = comptime_int_idx }, ip) });
    }
    const idx = try sema.intern_pool.internIntValue(dest_ty, result_big);
    return .{ .index = idx };
}

fn evalBlock(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@backingInt(inst) < sema.zir.instructions.len);

    const pl_node = sema.zir.instructions.items(.data)[@backingInt(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.Block, pl_node.payload_index);
    const body = sema.zir.bodySlice(extra.end, extra.data.body_len);
    return try sema.resolveInlineBody(body, inst);
}

fn evalCondbr(sema: *Sema, inst: Zir.Inst.Index) Error!Value {
    assert(@backingInt(inst) < sema.zir.instructions.len);

    const pl_node = sema.zir.instructions.items(.data)[@backingInt(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.CondBr, pl_node.payload_index);
    const condbr = extra.data;
    assert(condbr.condition != .none);

    const cond = try sema.coerceValueToType(try sema.resolveInst(condbr.condition), .bool_type);
    const cond_is_true = cond.toBool();

    const then_body_start = extra.end;
    const else_body_start = then_body_start + condbr.then_body_len;
    const body = if (cond_is_true)
        sema.zir.bodySlice(then_body_start, condbr.then_body_len)
    else
        sema.zir.bodySlice(else_body_start, condbr.else_body_len);

    return try sema.evalBody(body);
}

fn evalBoolNot(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@backingInt(inst) < sema.zir.instructions.len);
    const ip = sema.intern_pool;
    const un_node = sema.zir.instructions.items(.data)[@backingInt(inst)].un_node;
    assert(un_node.operand != .none);
    const src = sema.block.nodeOffset(un_node.src_node);
    const uncasted_operand = try sema.resolveInst(un_node.operand);
    const uncasted_ty = uncasted_operand.typeOf(ip);
    if (uncasted_ty.zigTypeTag(ip) == .vector) {
        if (uncasted_ty.scalarType(ip).zigTypeTag(ip) != .bool)
            return sema.fail(sema.block, src, "boolean not operation on type '{f}'", .{uncasted_ty.fmt(ip)});
        return try arith.bitwiseNot(sema, uncasted_ty, uncasted_operand);
    }
    const operand = try sema.coerceValueToType(uncasted_operand, .bool_type);
    if (operand.isUndef(ip)) return .{ .index = .undef_bool };
    return if (operand.toBool()) .{ .index = .bool_false } else .{ .index = .bool_true };
}

fn evalBoolBr(sema: *Sema, inst: Zir.Inst.Index, tag: Zir.Inst.Tag) Error!?Value {
    assert(@backingInt(inst) < sema.zir.instructions.len);
    assert(tag == .bool_br_and or tag == .bool_br_or);

    const pl_node = sema.zir.instructions.items(.data)[@backingInt(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.BoolBr, pl_node.payload_index);
    const bool_br = extra.data;
    assert(bool_br.lhs != .none);

    const lhs = try sema.coerceValueToType(try sema.resolveInst(bool_br.lhs), .bool_type);
    const lhs_is_true = lhs.toBool();

    const short_circuited = switch (tag) {
        .bool_br_and => !lhs_is_true,
        .bool_br_or => lhs_is_true,
        else => unreachable,
    };
    if (short_circuited) return lhs;

    const body = sema.zir.bodySlice(extra.end, bool_br.body_len);
    return try sema.resolveInlineBody(body, inst);
}

fn evalTypeofLog2IntType(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@backingInt(inst) < sema.zir.instructions.len);

    const un_node = sema.zir.instructions.items(.data)[@backingInt(inst)].un_node;
    assert(un_node.operand != .none);

    const ip = sema.intern_pool;
    // A type query yields a comptime-known result whatever the operand's runtime-ness;
    // the compiler returns `Air.internedToRef` unconditionally, so keep the operand's
    // value from tainting this result's comptime flag.
    const saved_operand_comptime = sema.operand_comptime;
    const operand = try sema.resolveInst(un_node.operand);
    sema.operand_comptime = saved_operand_comptime;
    const operand_type = Value.typeOf(operand, ip).index;

    return .{ .index = try sema.log2IntType(operand_type) };
}

fn log2IntType(sema: *Sema, int_ty: InternPool.Index) Error!InternPool.Index {
    const ip = sema.intern_pool;
    const operand = Type.fromIndex(int_ty);
    switch (operand.zigTypeTag(ip)) {
        .comptime_int => return .comptime_int_type,
        .int => {
            const bits = operand.intInfo(ip).bits;
            const log2_bits: u16 = if (bits == 0) 0 else std.math.log2_int_ceil(u16, bits);
            return try ip.internIntType(.unsigned, log2_bits);
        },
        .vector => {
            const log2_elem = try sema.log2IntType(operand.childType(ip).toIndex());
            return try ip.internVectorType(.{ .len = operand.vectorLen(ip), .child = log2_elem });
        },
        else => {},
    }
    return sema.fail(sema.block, sema.block.nodeOffset(.zero), "bit shifting operation expected integer type, found '{f}'", .{operand.fmt(ip)});
}

fn checkIntType(sema: *Sema, src: LazySrcLoc, ty: Type) Error!bool {
    const ip = sema.intern_pool;
    switch (ty.zigTypeTag(ip)) {
        .comptime_int => return true,
        .int => return false,
        else => return sema.fail(sema.block, src, "expected integer type, found '{f}'", .{ty.fmt(ip)}),
    }
}

fn checkFloatType(sema: *Sema, ty_src: LazySrcLoc, ty: Type) Error!void {
    switch (ty.zigTypeTag(sema.intern_pool)) {
        .comptime_int, .comptime_float, .float => {},
        else => return sema.fail(sema.block, ty_src, "expected float type, found '{f}'", .{ty.fmt(sema.intern_pool)}),
    }
}

fn checkIntOrVectorAllowComptime(sema: *Sema, operand_ty: Type, operand_src: LazySrcLoc) Error!Type {
    const ip = sema.intern_pool;
    switch (operand_ty.zigTypeTag(ip)) {
        .int, .comptime_int => return operand_ty,
        .vector => {
            const elem_ty = operand_ty.childType(ip);
            switch (elem_ty.zigTypeTag(ip)) {
                .int, .comptime_int => return elem_ty,
                else => return sema.fail(sema.block, operand_src, "expected vector of integers; found vector of '{f}'", .{elem_ty.fmt(ip)}),
            }
        },
        else => return sema.fail(sema.block, operand_src, "expected integer or vector, found '{f}'", .{operand_ty.fmt(ip)}),
    }
}

/// The compiler additionally attaches `Type.Comparison` dedupe placeholder notes to disambiguate
/// same-named types; that formatting subsystem is not modelled here, so the message stands alone.
fn typeMismatchErrMsg(sema: *Sema, src: LazySrcLoc, expected: Type, found: Type) Error!*ErrorMsg {
    const ip = sema.intern_pool;
    return sema.errMsg(src, "expected type '{f}', found '{f}'", .{ expected.fmt(ip), found.fmt(ip) });
}

fn addFieldErrNote(sema: *Sema, container_ty: InternPool.Index, field_index: u32, parent: *ErrorMsg, comptime format: []const u8, args: anytype) Error!void {
    @branchHint(.cold);
    const id: InternPool.Key.ContainerType = switch (sema.intern_pool.indexToKey(container_ty)) {
        .struct_type => |st| st,
        .union_type => |ut| ut,
        .enum_type => |et| et,
        else => return,
    };
    // A generated union-tag enum has no fields of its own; tag field `i` is the owning union's field `i`.
    const field_src: LazySrcLoc = switch (id) {
        .declared => |d| .{ .base_node_inst = d.decl_inst, .offset = .{ .container_field_name = field_index } },
        .reified => |r| .{ .base_node_inst = r.decl_inst, .offset = .{ .container_field_name = field_index } },
        .generated_union_tag => |owner_union| return sema.addFieldErrNote(owner_union, field_index, parent, format, args),
    };
    try sema.errNote(field_src, parent, format, args);
}

pub fn addDeclaredHereNote(sema: *Sema, parent: *ErrorMsg, decl_ty: Type) Error!void {
    const category = switch (decl_ty.zigTypeTag(sema.intern_pool)) {
        .@"union" => "union",
        .@"struct" => "struct",
        .@"enum" => "enum",
        .@"opaque" => "opaque",
        else => return,
    };
    try sema.errNote(sema.containerTypeSrc(decl_ty.index), parent, "{s} declared here", .{category});
}

fn failWithExpectedOptionalType(sema: *Sema, src: LazySrcLoc, non_optional_ty: Type) Error {
    const ip = sema.intern_pool;
    return sema.failWithOwnedErrorMsg(sema.block, msg: {
        const msg = try sema.errMsg(src, "expected optional type, found '{f}'", .{non_optional_ty.fmt(ip)});
        errdefer msg.destroy(sema.gpa);
        if (non_optional_ty.zigTypeTag(ip) == .error_union) {
            try sema.errNote(src, msg, "consider using 'try', 'catch', or 'if'", .{});
        }
        try sema.addDeclaredHereNote(msg, non_optional_ty);
        break :msg msg;
    });
}

fn failWithStructInitNotSupported(sema: *Sema, src: LazySrcLoc, ty: Type) Error {
    return sema.fail(sema.block, src, "type '{f}' does not support struct initialization syntax", .{ty.fmt(sema.intern_pool)});
}

fn failWithArrayInitNotSupported(sema: *Sema, src: LazySrcLoc, ty: Type) Error {
    return sema.fail(sema.block, src, "type '{f}' does not support array initialization syntax", .{ty.fmt(sema.intern_pool)});
}

fn failWithTypeMismatch(sema: *Sema, src: LazySrcLoc, expected: Type, found: Type) Error {
    return sema.failWithOwnedErrorMsg(sema.block, msg: {
        const msg = try sema.typeMismatchErrMsg(src, expected, found);
        errdefer msg.destroy(sema.gpa);
        try sema.addDeclaredHereNote(msg, expected);
        try sema.addDeclaredHereNote(msg, found);
        break :msg msg;
    });
}

fn evalAsNode(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@backingInt(inst) < sema.zir.instructions.len);

    const pl_node = sema.zir.instructions.items(.data)[@backingInt(inst)].pl_node;
    const as = sema.zir.extraData(Zir.Inst.As, pl_node.payload_index).data;
    assert(as.dest_type != .none);
    assert(as.operand != .none);

    const dest_type_index = try sema.resolveDestType(as.dest_type);

    const operand_value = try sema.resolveInst(as.operand);
    return try sema.coerceValueToType(operand_value, dest_type_index);
}

fn resolveDestType(
    sema: *Sema,
    ref: Zir.Inst.Ref,
) Error!InternPool.Index {
    assert(ref != .none);
    const dest_value = try sema.resolveInst(ref);
    const key = sema.intern_pool.indexToKey(dest_value.index);
    if (key.isType()) return dest_value.index;
    return sema.fail(sema.block, sema.block.nodeOffset(.zero), "expected type 'type', found '{f}'", .{dest_value.typeOf(sema.intern_pool).fmt(sema.intern_pool)});
}

fn binData(sema: *Sema, inst: Zir.Inst.Index) Zir.Inst.Bin {
    assert(@backingInt(inst) < sema.zir.instructions.len);
    const pl_node = sema.zir.instructions.items(.data)[@backingInt(inst)].pl_node;
    return sema.zir.extraData(Zir.Inst.Bin, pl_node.payload_index).data;
}

fn evalFloatCast(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    const pl_node = sema.zir.instructions.items(.data)[@backingInt(inst)].pl_node;
    const src = sema.block.nodeOffset(pl_node.src_node);
    const operand_src = sema.block.builtinCallArgSrc(pl_node.src_node, 0);
    const extra = sema.zir.extraData(Zir.Inst.Bin, pl_node.payload_index).data;

    const dest_ty: Type = .fromIndex(try sema.resolveDestType(extra.lhs));
    const dest_scalar_ty = dest_ty.scalarType(ip);
    const operand = try sema.resolveInst(extra.rhs);
    const operand_ty = operand.typeOf(ip);
    const operand_scalar_ty = operand_ty.scalarType(ip);

    try sema.checkVectorizableBinaryOperands(dest_ty, operand_ty);
    const is_vector = dest_ty.zigTypeTag(ip) == .vector;

    switch (dest_scalar_ty.zigTypeTag(ip)) {
        .comptime_float, .float => {},
        else => return sema.fail(sema.block, src, "expected float or vector type, found '{f}'", .{dest_ty.fmt(ip)}),
    }
    switch (operand_scalar_ty.zigTypeTag(ip)) {
        .comptime_float, .float, .comptime_int => {},
        else => return sema.fail(sema.block, operand_src, "expected float or vector type, found '{f}'", .{operand_ty.fmt(ip)}),
    }

    if (!is_vector) {
        return try operand.floatCast(dest_ty, ip);
    }
    const vec_len = operand_ty.vectorLen(ip);
    const new_elems = try sema.arena.alloc(InternPool.Index, vec_len);
    for (new_elems, 0..) |*new_elem, i| {
        const old_elem = try operand.elemValue(ip, i);
        new_elem.* = (try old_elem.floatCast(dest_scalar_ty, ip)).index;
    }
    return try sema.aggregateValue(dest_ty, new_elems);
}

fn evalIntFromFloat(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    const pl_node = sema.zir.instructions.items(.data)[@backingInt(inst)].pl_node;
    const src = sema.block.nodeOffset(pl_node.src_node);
    const operand_src = sema.block.builtinCallArgSrc(pl_node.src_node, 0);
    const extra = sema.zir.extraData(Zir.Inst.Bin, pl_node.payload_index).data;
    const dest_ty: Type = .fromIndex(try sema.resolveDestType(extra.lhs));
    const operand = try sema.resolveInst(extra.rhs);
    const operand_ty = operand.typeOf(ip);

    try sema.checkVectorizableBinaryOperands(dest_ty, operand_ty);

    const dest_scalar_ty = dest_ty.scalarType(ip);
    const operand_scalar_ty = operand_ty.scalarType(ip);

    switch (dest_scalar_ty.zigTypeTag(ip)) {
        .comptime_int, .int => {},
        else => return sema.fail(sema.block, src, "expected integer result type, found '{f}'", .{dest_scalar_ty.fmt(ip)}),
    }
    try sema.checkFloatType(operand_src, operand_scalar_ty);

    return try sema.intFromFloat(operand, operand_ty, dest_ty, .truncate);
}

const IntFromFloatMode = enum { exact, truncate, round, floor, ceil };

fn intFromFloat(sema: *Sema, val: Value, float_ty: Type, int_ty: Type, mode: IntFromFloatMode) Error!Value {
    const ip = sema.intern_pool;
    if (float_ty.zigTypeTag(ip) == .vector) {
        const result_data = try sema.arena.alloc(InternPool.Index, float_ty.vectorLen(ip));
        for (result_data, 0..) |*scalar, elem_idx| {
            const elem_val = try val.elemValue(ip, elem_idx);
            scalar.* = (try sema.intFromFloatScalar(elem_val, int_ty.scalarType(ip), mode)).index;
        }
        return sema.aggregateValue(int_ty, result_data);
    }
    return sema.intFromFloatScalar(val, int_ty, mode);
}

fn intFromFloatScalar(sema: *Sema, val: Value, int_ty: Type, mode: IntFromFloatMode) Error!Value {
    const ip = sema.intern_pool;
    if (val.isUndef(ip)) return sema.failWithUseOfUndef();

    var float = val.toFloat(f128, ip);
    switch (mode) {
        .round => float = @round(float),
        .floor => float = @floor(float),
        .ceil => float = @ceil(float),
        .truncate, .exact => {},
    }

    if (std.math.isNan(float)) {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "float value NaN cannot be stored in integer type '{f}'", .{int_ty.fmt(ip)});
    }
    if (std.math.isInf(float)) {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "float value Inf cannot be stored in integer type '{f}'", .{int_ty.fmt(ip)});
    }

    var big_int: std.math.big.int.Mutable = .{
        .limbs = try sema.arena.alloc(std.math.big.Limb, std.math.big.int.calcLimbLen(float)),
        .len = undefined,
        .positive = undefined,
    };
    switch (big_int.setFloat(float, .trunc)) {
        .inexact => switch (mode) {
            .exact => return sema.fail(sema.block, sema.block.nodeOffset(.zero), "fractional component prevents float value '{f}' from coercion to type '{f}'", .{ render_value.fmt(val, ip), int_ty.fmt(ip) }),
            .truncate, .round, .floor, .ceil => {},
        },
        .exact => {},
    }
    const cti_result: Value = .{ .index = try ip.internComptimeInt(big_int.toConst()) };
    if (int_ty.index == .comptime_int_type) return cti_result;

    const int_info = int_ty.intInfo(ip);
    if (!big_int.toConst().fitsInTwosComp(int_info.signedness, int_info.bits)) {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "float value '{f}' cannot be stored in integer type '{f}'", .{ render_value.fmt(val, ip), int_ty.fmt(ip) });
    }
    return .{ .index = try ip.getCoerced(cti_result.index, int_ty.index) };
}

fn evalFloatFromInt(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    const pl_node = sema.zir.instructions.items(.data)[@backingInt(inst)].pl_node;
    const src = sema.block.nodeOffset(pl_node.src_node);
    const operand_src = sema.block.builtinCallArgSrc(pl_node.src_node, 0);
    const extra = sema.zir.extraData(Zir.Inst.Bin, pl_node.payload_index).data;
    const dest_ty: Type = .fromIndex(try sema.resolveDestType(extra.lhs));
    const operand = try sema.resolveInst(extra.rhs);
    const operand_ty = operand.typeOf(ip);

    try sema.checkVectorizableBinaryOperands(dest_ty, operand_ty);

    const dest_scalar_ty = dest_ty.scalarType(ip);
    const operand_scalar_ty = operand_ty.scalarType(ip);

    switch (dest_scalar_ty.zigTypeTag(ip)) {
        .comptime_float, .float => {},
        else => return sema.fail(sema.block, src, "expected float result type, found '{f}'", .{dest_scalar_ty.fmt(ip)}),
    }
    _ = try sema.checkIntType(operand_src, operand_scalar_ty);

    if (operand.isUndef(ip)) return try sema.undefValue(dest_ty);
    if (dest_ty.zigTypeTag(ip) != .vector) {
        return try sema.floatValue(dest_ty, operand.toFloat(f128, ip));
    }
    const dest_elems = try sema.arena.alloc(InternPool.Index, dest_ty.vectorLen(ip));
    for (dest_elems, 0..) |*out_elem, elem_idx| {
        const orig_elem = try operand.elemValue(ip, elem_idx);
        const casted_elem = if (orig_elem.isUndef(ip))
            try sema.undefValue(dest_scalar_ty)
        else
            try sema.floatValue(dest_scalar_ty, orig_elem.toFloat(f128, ip));
        out_elem.* = casted_elem.index;
    }
    return try sema.aggregateValue(dest_ty, dest_elems);
}

fn intCast(sema: *Sema, dest_ty: Type, dest_ty_src: LazySrcLoc, operand: Value, operand_src: LazySrcLoc) Error!Value {
    const ip = sema.intern_pool;
    const operand_ty = operand.typeOf(ip);
    const dest_scalar_ty = try sema.checkIntOrVectorAllowComptime(dest_ty, dest_ty_src);
    _ = try sema.checkIntOrVectorAllowComptime(operand_ty, operand_src);

    if (operand.is_comptime) {
        return sema.coerceValueToType(operand, dest_ty.index);
    } else if (dest_scalar_ty.zigTypeTag(ip) == .comptime_int) {
        return sema.fail(sema.block, operand_src, "unable to cast runtime value to 'comptime_int'", .{});
    }
    // The compiler emits an AIR `int_cast` for a runtime operand; with no AIR layer, the interpreter
    // holds the value and performs the width refit directly (the runtime cast truncates instead of
    // raising a comptime range error).
    return sema.refitIntToFixedWidth(operand.index, dest_ty.index);
}

fn evalIntCast(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const pl_node = sema.zir.instructions.items(.data)[@backingInt(inst)].pl_node;
    const src = sema.block.nodeOffset(pl_node.src_node);
    const operand_src = sema.block.builtinCallArgSrc(pl_node.src_node, 0);
    const extra = sema.zir.extraData(Zir.Inst.Bin, pl_node.payload_index).data;
    const dest_ty: Type = .fromIndex(try sema.resolveDestType(extra.lhs));
    const operand = try sema.resolveInst(extra.rhs);
    return try sema.intCast(dest_ty, src, operand, operand_src);
}

fn evalTruncate(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    const pl_node = sema.zir.instructions.items(.data)[@backingInt(inst)].pl_node;
    const src = sema.block.nodeOffset(pl_node.src_node);
    const operand_src = sema.block.builtinCallArgSrc(pl_node.src_node, 0);
    const extra = sema.zir.extraData(Zir.Inst.Bin, pl_node.payload_index).data;
    const dest_ty: Type = .fromIndex(try sema.resolveDestType(extra.lhs));
    const dest_scalar_ty = try sema.checkIntOrVectorAllowComptime(dest_ty, src);
    const operand = try sema.resolveInst(extra.rhs);
    const operand_ty = operand.typeOf(ip);
    const operand_scalar_ty = try sema.checkIntOrVectorAllowComptime(operand_ty, operand_src);

    const operand_is_vector = operand_ty.zigTypeTag(ip) == .vector;
    const dest_is_vector = dest_ty.zigTypeTag(ip) == .vector;
    if (operand_is_vector != dest_is_vector) {
        return sema.failWithTypeMismatch(operand_src, dest_ty, operand_ty);
    }

    if (dest_scalar_ty.zigTypeTag(ip) == .comptime_int) {
        return try sema.coerceValueToType(operand, dest_ty.index);
    }

    if (try dest_ty.onePossibleValue(sema)) |opv| return opv;

    const dest_info = dest_scalar_ty.intInfo(ip);

    if (operand_scalar_ty.zigTypeTag(ip) != .comptime_int) {
        const operand_info = operand_ty.intInfo(ip);
        if (operand_info.signedness != dest_info.signedness) {
            return sema.fail(sema.block, operand_src, "expected {s} integer type, found '{f}'", .{ @tagName(dest_info.signedness), operand_ty.fmt(ip) });
        }
        if (dest_info.bits >= operand_info.bits) {
            return try sema.coerceValueToType(operand, dest_ty.index);
        }
    }

    return try arith.truncate(sema, operand, operand_ty, dest_ty, dest_info.signedness, dest_info.bits);
}

fn evalBitCast(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    const pl_node = sema.zir.instructions.items(.data)[@backingInt(inst)].pl_node;
    const src = sema.block.nodeOffset(pl_node.src_node);
    const operand_src = sema.block.builtinCallArgSrc(pl_node.src_node, 0);
    const extra = sema.zir.extraData(Zir.Inst.Bin, pl_node.payload_index).data;

    const dest_ty: Type = .fromIndex(try sema.resolveDestType(extra.lhs));
    const operand = try sema.resolveInst(extra.rhs);
    const operand_ty = operand.typeOf(ip);

    // Check for pointers before `hasBitRepresentation` so slices get a better message.
    switch (dest_ty.scalarType(ip).zigTypeTag(ip)) {
        .pointer, .optional => return sema.failWithOwnedErrorMsg(sema.block, msg: {
            const msg = try sema.errMsg(src, "cannot @bitCast to '{f}'", .{dest_ty.fmt(ip)});
            errdefer msg.destroy(sema.gpa);
            switch (operand_ty.zigTypeTag(ip)) {
                .int, .comptime_int => try sema.errNote(src, msg, "use @ptrFromInt to cast from '{f}'", .{operand_ty.fmt(ip)}),
                .pointer => try sema.errNote(src, msg, "use @ptrCast to cast from '{f}'", .{operand_ty.fmt(ip)}),
                else => {},
            }
            break :msg msg;
        }),
        .array => switch (dest_ty.arrayBase(ip)[0].zigTypeTag(ip)) {
            .pointer, .optional => return sema.fail(sema.block, src, "cannot @bitCast to '{f}'", .{dest_ty.fmt(ip)}),
            else => {},
        },
        else => {},
    }
    if (!dest_ty.hasBitRepresentation(ip)) {
        return sema.fail(sema.block, src, "cannot @bitCast to '{f}'", .{dest_ty.fmt(ip)});
    }

    switch (operand_ty.scalarType(ip).zigTypeTag(ip)) {
        .pointer, .optional => return sema.failWithOwnedErrorMsg(sema.block, msg: {
            const msg = try sema.errMsg(operand_src, "cannot @bitCast from '{f}'", .{operand_ty.fmt(ip)});
            errdefer msg.destroy(sema.gpa);
            switch (dest_ty.zigTypeTag(ip)) {
                .int, .comptime_int => try sema.errNote(operand_src, msg, "use @intFromPtr to cast to '{f}'", .{dest_ty.fmt(ip)}),
                .pointer => try sema.errNote(operand_src, msg, "use @ptrCast to cast to '{f}'", .{dest_ty.fmt(ip)}),
                else => {},
            }
            break :msg msg;
        }),
        .array => switch (operand_ty.arrayBase(ip)[0].zigTypeTag(ip)) {
            .pointer, .optional => return sema.fail(sema.block, operand_src, "cannot @bitCast from '{f}'", .{dest_ty.fmt(ip)}),
            else => {},
        },
        else => {},
    }
    if (!operand_ty.hasBitRepresentation(ip)) {
        return sema.fail(sema.block, operand_src, "cannot @bitCast from '{f}'", .{operand_ty.fmt(ip)});
    }

    return try sema.bitCast(dest_ty, operand, src);
}

fn bitCast(sema: *Sema, dest_ty: Type, operand: Value, src: LazySrcLoc) Error!Value {
    const ip = sema.intern_pool;
    try sema.ensureLayoutResolved(dest_ty.index);
    const dest_bits = dest_ty.bitSize(ip);
    const operand_ty = Value.typeOf(operand, ip);
    const old_bits = operand_ty.bitSize(ip);
    if (old_bits != dest_bits)
        return sema.fail(sema.block, src, "@bitCast size mismatch: destination type '{f}' has {d} bits but source type '{f}' has {d} bits", .{ dest_ty.fmt(ip), dest_bits, operand_ty.fmt(ip), old_bits });
    return try sema.bitCastVal(operand, dest_ty);
}

fn bitCastVal(sema: *Sema, val: Value, dest_ty: Type) Error!Value {
    const ip = sema.intern_pool;
    const bit_size = dest_ty.bitSize(ip);
    assert(Value.typeOf(val, ip).bitSize(ip) == bit_size);
    if (val.isUndef(ip)) return .fromIndex(try ip.get(.{ .undef = dest_ty.index }));
    const buf = try sema.gpa.alloc(u8, @intCast((bit_size + 7) / 8));
    defer sema.gpa.free(buf);
    @memset(buf, 0);
    val.writeToPackedMemory(ip, buf, 0);
    return try Value.readFromPackedMemory(dest_ty, ip, buf, 0);
}

fn evalShift(
    sema: *Sema,
    inst: Zir.Inst.Index,
    tag: Zir.Inst.Tag,
) Error!?Value {
    const bin = sema.binData(inst);
    assert(bin.lhs != .none);
    assert(bin.rhs != .none);

    const ip = sema.intern_pool;
    const lhs_value = try sema.resolveInst(bin.lhs);
    const rhs_value = try sema.resolveInst(bin.rhs);
    const lhs_ty = Value.typeOf(lhs_value, ip);
    const rhs_ty = Value.typeOf(rhs_value, ip);

    // `<<` and `@shlExact` validate their operands when the `typeof_log2_int_type`
    // for the rhs coercion is evaluated; `<<|` gets no such coercion, so both its
    // operands are only checked here (src/Sema.zig zirShl).
    if (tag == .shl_sat) {
        _ = try sema.log2IntType(lhs_ty.index);
        _ = try sema.checkIntType(sema.block.nodeOffset(.zero), rhs_ty.scalarType(ip));
    }

    return switch (tag) {
        .shl => try arith.shl(sema, lhs_ty, lhs_value, rhs_value, .shl),
        .shl_exact => try arith.shl(sema, lhs_ty, lhs_value, rhs_value, .shl_exact),
        .shl_sat => try arith.shl(sema, lhs_ty, lhs_value, rhs_value, .shl_sat),
        .shr => try arith.shr(sema, lhs_ty, rhs_ty, lhs_value, rhs_value, .shr),
        .shr_exact => try arith.shr(sema, lhs_ty, rhs_ty, lhs_value, rhs_value, .shr_exact),
        else => unreachable,
    };
}

fn checkArithmeticOp(sema: *Sema, scalar_tag: std.lang.TypeId, lhs_zig_ty_tag: std.lang.TypeId, rhs_zig_ty_tag: std.lang.TypeId, tag: Zir.Inst.Tag) Error!void {
    const is_int = scalar_tag == .int or scalar_tag == .comptime_int;
    const is_float = scalar_tag == .float or scalar_tag == .comptime_float;
    if (!is_int and !(is_float and floatOpAllowed(tag))) {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "invalid operands to binary expression: '{s}' and '{s}'", .{
            @tagName(lhs_zig_ty_tag), @tagName(rhs_zig_ty_tag),
        });
    }
}

fn floatOpAllowed(tag: Zir.Inst.Tag) bool {
    return switch (tag) {
        .add, .add_unsafe, .sub, .mul, .div, .div_exact, .div_trunc, .div_floor, .div_ceil, .mod, .rem, .mod_rem => true,
        else => false,
    };
}

fn evalBitwise(sema: *Sema, inst: Zir.Inst.Index, tag: Zir.Inst.Tag) Error!?Value {
    const bin = sema.binData(inst);
    assert(bin.lhs != .none);
    assert(bin.rhs != .none);

    const lhs_value = try sema.resolveInst(bin.lhs);
    const rhs_value = try sema.resolveInst(bin.rhs);

    try sema.checkVectorizableBinaryOperands(Value.typeOf(lhs_value, sema.intern_pool), Value.typeOf(rhs_value, sema.intern_pool));
    const resolved_type = try sema.resolvePeerTypes(&.{ lhs_value, rhs_value });
    const lhs = try sema.coerceValueToType(lhs_value, resolved_type.index);
    const rhs = try sema.coerceValueToType(rhs_value, resolved_type.index);

    const pool = sema.intern_pool;
    const scalar_tag = resolved_type.scalarType(pool).zigTypeTag(pool);
    const is_int_or_bool = scalar_tag == .int or scalar_tag == .comptime_int or scalar_tag == .bool;
    if (!is_int_or_bool) {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "invalid operands to binary bitwise expression: '{s}' and '{s}'", .{
            @tagName(Value.typeOf(lhs_value, pool).zigTypeTag(pool)),
            @tagName(Value.typeOf(rhs_value, pool).zigTypeTag(pool)),
        });
    }

    return switch (tag) {
        .bit_and => try arith.bitwiseBin(sema, resolved_type, lhs, rhs, .@"and"),
        .bit_or => try arith.bitwiseBin(sema, resolved_type, lhs, rhs, .@"or"),
        .xor => try arith.bitwiseBin(sema, resolved_type, lhs, rhs, .xor),
        else => unreachable,
    };
}

inline fn boolValue(b: bool) Value {
    return .{ .index = if (b) .bool_true else .bool_false };
}

fn compareOperatorName(comp: std.math.CompareOperator) []const u8 {
    return switch (comp) {
        .lt => "<",
        .lte => "<=",
        .eq => "==",
        .gte => ">=",
        .gt => ">",
        .neq => "!=",
    };
}

fn analyzeIsNull(sema: *Sema, operand: Value, invert: bool) Error!Value {
    const ip = sema.intern_pool;
    if (operand.isUndef(ip)) return .{ .index = try ip.get(.{ .undef = .bool_type }) };
    // `Value.isNull` covers both an optional payload and a C pointer's null address (`base_addr .int`,
    // `byte_offset 0`), so a null `[*c]T` compares equal to `null` like the compiler.
    const is_null = operand.isNull(ip);
    return boolValue(is_null != invert);
}

fn analyzeCmpUnionTag(sema: *Sema, un: Value, tag: Value, op: std.math.CompareOperator) Error!?Value {
    const ip = sema.intern_pool;
    const union_ty = un.typeOf(ip);
    try sema.ensureLayoutResolved(union_ty.index);
    if (ip.unionFields(union_ty.index).tag_usage != .tagged) {
        return sema.failWithOwnedErrorMsg(sema.block, msg: {
            const msg = try sema.errMsg(sema.block.nodeOffset(.zero), "comparison of union and enum literal is only valid for tagged union types", .{});
            errdefer msg.destroy(sema.gpa);
            try sema.errNote(sema.containerTypeSrc(union_ty.index), msg, "union '{f}' is not a tagged union", .{union_ty.fmt(ip)});
            break :msg msg;
        });
    }
    // The REPL carries the tag enum on the tag value (`enum_tag_type` stays `.none`), so coerce the
    // enum operand to the active tag's type and compare the tags.
    const union_tag = un.unionTag(ip).?;
    const coerced_tag = try sema.coerceValueToType(tag, union_tag.typeOf(ip).index);
    return sema.cmpSelf(union_tag, coerced_tag, op);
}

fn evalCmpEq(sema: *Sema, inst: Zir.Inst.Index, op: std.math.CompareOperator) Error!?Value {
    const ip = sema.intern_pool;
    const bin = sema.binData(inst);
    const src = sema.block.nodeOffset(sema.srcNodeOffset(inst));
    const lhs = try sema.resolveInst(bin.lhs);
    const rhs = try sema.resolveInst(bin.rhs);
    const lhs_ty = lhs.typeOf(ip);
    const rhs_ty = rhs.typeOf(ip);
    const lhs_ty_tag = lhs_ty.zigTypeTag(ip);
    const rhs_ty_tag = rhs_ty.zigTypeTag(ip);

    if (lhs_ty_tag == .null and rhs_ty_tag == .null) return boolValue(op == .eq);
    if (lhs_ty_tag == .null and (rhs_ty_tag == .optional or rhs_ty.isCPtr(ip))) return try sema.analyzeIsNull(rhs, op == .neq);
    if (rhs_ty_tag == .null and (lhs_ty_tag == .optional or lhs_ty.isCPtr(ip))) return try sema.analyzeIsNull(lhs, op == .neq);
    if (lhs_ty_tag == .null or rhs_ty_tag == .null) {
        const non_null_type = if (lhs_ty_tag == .null) rhs_ty else lhs_ty;
        return sema.fail(sema.block, src, "comparison of '{f}' with null", .{non_null_type.fmt(ip)});
    }

    if (lhs_ty_tag == .@"union" and (rhs_ty_tag == .enum_literal or rhs_ty_tag == .@"enum")) return sema.analyzeCmpUnionTag(lhs, rhs, op);
    if (rhs_ty_tag == .@"union" and (lhs_ty_tag == .enum_literal or lhs_ty_tag == .@"enum")) return sema.analyzeCmpUnionTag(rhs, lhs, op);

    if (lhs_ty_tag == .error_set and rhs_ty_tag == .error_set) {
        if (lhs.isUndef(ip) or rhs.isUndef(ip)) return .{ .index = .undef_bool };
        return boolValue((ip.indexToKey(lhs.index).err.name == ip.indexToKey(rhs.index).err.name) == (op == .eq));
    }

    if (lhs_ty_tag == .type and rhs_ty_tag == .type) {
        return boolValue((lhs.index == rhs.index) == (op == .eq));
    }

    return sema.analyzeCmp(lhs, rhs, op, true);
}

fn evalCmp(sema: *Sema, inst: Zir.Inst.Index, op: std.math.CompareOperator) Error!?Value {
    const bin = sema.binData(inst);
    const lhs = try sema.resolveInst(bin.lhs);
    const rhs = try sema.resolveInst(bin.rhs);
    return sema.analyzeCmp(lhs, rhs, op, false);
}

fn analyzeCmp(sema: *Sema, lhs: Value, rhs: Value, op: std.math.CompareOperator, is_equality_cmp: bool) Error!?Value {
    const ip = sema.intern_pool;
    const src = sema.block.nodeOffset(.zero);
    const lhs_ty = lhs.typeOf(ip);
    const rhs_ty = rhs.typeOf(ip);
    if (lhs_ty.zigTypeTag(ip) != .optional and rhs_ty.zigTypeTag(ip) != .optional) {
        try sema.checkVectorizableBinaryOperands(lhs_ty, rhs_ty);
    }

    if (lhs_ty.zigTypeTag(ip) == .vector and rhs_ty.zigTypeTag(ip) == .vector) {
        return try sema.cmpVector(lhs, rhs, op);
    }
    if (lhs_ty.isNumeric(ip) and rhs_ty.isNumeric(ip)) {
        return try sema.cmpNumeric(lhs, rhs, op);
    }
    // The compiler routes the unwrapped error code through `cmpSelf`; the REPL's error values carry
    // their set type, so a cross-set `eql` would fail the type assert -- errors compare by name.
    if (is_equality_cmp and lhs_ty.zigTypeTag(ip) == .error_union and rhs_ty.zigTypeTag(ip) == .error_set) {
        if (lhs.errorUnionIsPayload(ip)) return boolValue(false);
        const code = try sema.analyzeErrUnionCode(lhs);
        if (code.isUndef(ip) or rhs.isUndef(ip)) return .{ .index = .undef_bool };
        return boolValue((ip.indexToKey(code.index).err.name == ip.indexToKey(rhs.index).err.name) == (op == .eq));
    }
    if (is_equality_cmp and lhs_ty.zigTypeTag(ip) == .error_set and rhs_ty.zigTypeTag(ip) == .error_union) {
        if (rhs.errorUnionIsPayload(ip)) return boolValue(false);
        const code = try sema.analyzeErrUnionCode(rhs);
        if (lhs.isUndef(ip) or code.isUndef(ip)) return .{ .index = .undef_bool };
        return boolValue((ip.indexToKey(lhs.index).err.name == ip.indexToKey(code.index).err.name) == (op == .eq));
    }

    const resolved_type = try sema.resolvePeerTypes(&.{ lhs, rhs });
    if (!resolved_type.isSelfComparable(ip, is_equality_cmp)) {
        return sema.fail(sema.block, src, "operator {s} not allowed for type '{f}'", .{ compareOperatorName(op), resolved_type.fmt(ip) });
    }
    const casted_lhs = try sema.coerceValueToType(lhs, resolved_type.index);
    const casted_rhs = try sema.coerceValueToType(rhs, resolved_type.index);
    return sema.cmpSelf(casted_lhs, casted_rhs, op);
}

fn cmpSelf(sema: *Sema, casted_lhs: Value, casted_rhs: Value, op: std.math.CompareOperator) Error!?Value {
    const ip = sema.intern_pool;
    if (casted_lhs.isUndef(ip) or casted_rhs.isUndef(ip)) return .{ .index = .undef_bool };
    const resolved_type = casted_lhs.typeOf(ip);
    return boolValue(casted_lhs.compareScalar(op, casted_rhs, resolved_type, ip));
}

fn analyzeErrUnionCode(sema: *Sema, operand: Value) Error!Value {
    const ip = sema.intern_pool;
    const operand_ty = Value.typeOf(operand, ip);
    if (operand_ty.zigTypeTag(ip) != .error_union) {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "expected error union type, found '{f}'", .{operand_ty.fmt(ip)});
    }
    const result_ty = operand_ty.errorUnionSet(ip);
    switch (ip.indexToKey(operand.index).error_union.val) {
        .payload => return .{ .index = .unreachable_value },
        .err_name => |name| return .{ .index = try ip.internErr(.{ .ty = result_ty.index, .name = name }) },
    }
}

fn cmpNumeric(sema: *Sema, uncasted_lhs: Value, uncasted_rhs: Value, op: std.math.CompareOperator) Error!Value {
    const ip = sema.intern_pool;
    const lhs_ty = uncasted_lhs.typeOf(ip);
    const rhs_ty = uncasted_rhs.typeOf(ip);
    assert(lhs_ty.isNumeric(ip));
    assert(rhs_ty.isNumeric(ip));
    const lhs_ty_tag = lhs_ty.zigTypeTag(ip);
    const rhs_ty_tag = rhs_ty.zigTypeTag(ip);

    // One exception to heterogeneous comparison: comptime_float coerces to the fixed-width float.
    const lhs = if (lhs_ty_tag == .comptime_float and rhs_ty_tag == .float)
        try sema.coerceValueToType(uncasted_lhs, rhs_ty.index)
    else
        uncasted_lhs;
    const rhs = if (lhs_ty_tag == .float and rhs_ty_tag == .comptime_float)
        try sema.coerceValueToType(uncasted_rhs, lhs_ty.index)
    else
        uncasted_rhs;

    // The comparison depends on both values, so the result is undef if either is undef.
    if (lhs.isUndef(ip) or rhs.isUndef(ip)) return .{ .index = .undef_bool };

    return boolValue(Value.compareHetero(lhs, op, rhs, ip));
}

fn cmpVector(sema: *Sema, lhs: Value, rhs: Value, op: std.math.CompareOperator) Error!Value {
    const ip = sema.intern_pool;
    const lhs_ty = lhs.typeOf(ip);
    assert(lhs_ty.zigTypeTag(ip) == .vector);
    assert(rhs.typeOf(ip).zigTypeTag(ip) == .vector);
    try sema.checkVectorizableBinaryOperands(lhs_ty, rhs.typeOf(ip));

    const len = lhs_ty.vectorLen(ip);
    const result_ty = try sema.vectorType(.{ .len = @intCast(len), .child = .bool_type });
    const elems = try sema.gpa.alloc(InternPool.Index, @intCast(len));
    defer sema.gpa.free(elems);
    var i: usize = 0;
    while (i < len) : (i += 1) {
        const l = try lhs.elemValue(ip, i);
        const r = try rhs.elemValue(ip, i);
        elems[i] = (try sema.cmpNumeric(l, r, op)).index;
    }
    return sema.aggregateValue(result_ty, elems);
}

fn evalUnaryMath(
    sema: *Sema,
    inst: Zir.Inst.Index,
    comptime eval: fn (Value, Type, std.mem.Allocator, *InternPool) std.mem.Allocator.Error!Value,
) Error!?Value {
    const un_node = sema.zir.instructions.items(.data)[@backingInt(inst)].un_node;
    const operand = try sema.resolveInst(un_node.operand);
    const operand_src = sema.block.builtinCallArgSrc(un_node.src_node, 0);
    return sema.unaryMath(operand_src, operand, eval);
}

fn unaryMath(
    sema: *Sema,
    operand_src: LazySrcLoc,
    operand: Value,
    comptime eval: fn (Value, Type, std.mem.Allocator, *InternPool) std.mem.Allocator.Error!Value,
) Error!?Value {
    const ip = sema.intern_pool;
    const operand_ty = operand.typeOf(ip);
    switch (operand_ty.scalarType(ip).zigTypeTag(ip)) {
        .comptime_float, .float => {},
        else => return sema.fail(sema.block, operand_src, "expected vector of floats or float type, found '{f}'", .{operand_ty.fmt(ip)}),
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
                return sema.fail(sema.block, sema.block.nodeOffset(.zero), "expected number, found '{t}'", .{t});
            },
        },
        else => {
            return sema.fail(sema.block, sema.block.nodeOffset(.zero), "expected number, found '{f}'", .{ty.fmt(ip)});
        },
    }
}

const MinMax = enum { min, max };

fn evalMinMax(sema: *Sema, inst: Zir.Inst.Index, comptime op: MinMax) Error!?Value {
    const bin = sema.binData(inst);
    const operands = [_]Value{ try sema.resolveInst(bin.lhs), try sema.resolveInst(bin.rhs) };
    return try sema.analyzeMinMax(&operands, op);
}

fn analyzeMinMax(sema: *Sema, operands: []const Value, comptime op: MinMax) Error!Value {
    const ip = sema.intern_pool;
    const opFunc = switch (op) {
        .min => Value.numberMin,
        .max => Value.numberMax,
    };

    if (operands.len == 1) {
        try sema.checkNumericType(Value.typeOf(operands[0], ip));
        return operands[0];
    }

    const vector_len: ?u64 = vec_len: {
        const first_ty = Value.typeOf(operands[0], ip);
        try sema.checkNumericType(first_ty);
        if (first_ty.zigTypeTag(ip) == .vector) {
            const vec_len = first_ty.vectorLen(ip);
            for (operands[1..]) |operand| {
                const operand_ty = Value.typeOf(operand, ip);
                try sema.checkNumericType(operand_ty);
                if (operand_ty.zigTypeTag(ip) != .vector) {
                    return sema.fail(sema.block, sema.block.nodeOffset(.zero), "expected vector, found '{f}'", .{operand_ty.fmt(ip)});
                }
                if (operand_ty.vectorLen(ip) != vec_len) {
                    return sema.fail(sema.block, sema.block.nodeOffset(.zero), "expected vector of length '{d}', found '{f}'", .{ vec_len, operand_ty.fmt(ip) });
                }
            }
            break :vec_len vec_len;
        } else {
            for (operands[1..]) |operand| {
                const operand_ty = Value.typeOf(operand, ip);
                try sema.checkNumericType(operand_ty);
                if (operand_ty.zigTypeTag(ip) == .vector) {
                    return sema.fail(sema.block, sema.block.nodeOffset(.zero), "expected vector, found '{f}'", .{first_ty.fmt(ip)});
                }
            }
            break :vec_len null;
        }
    };

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
        if (@backingInt(want_strat) < @backingInt(cur_strat)) {
            cur_strat = want_strat;
        } else if (@backingInt(want_strat) == @backingInt(cur_strat)) {
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

    if (try result_ty.onePossibleValue(sema)) |opv| return opv;

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
    for (elems) |*elem| {
        const ev: Value = .{ .index = elem.* };
        elem.* = if (ev.isUndef(ip))
            (try sema.undefValue(result_scalar_ty)).index
        else
            (try sema.coerceValueToType(ev, result_scalar_ty.index)).index;
    }
    if (vector_len == null) return Value{ .index = elems[0] };
    return try sema.aggregateValue(result_ty, elems);
}

fn evalMinMaxMulti(sema: *Sema, extended: Zir.Inst.Extended.InstData, comptime op: MinMax) Error!?Value {
    const extra = sema.zir.extraData(Zir.Inst.NodeMultiOp, extended.operand);
    const operand_refs = sema.zir.refSlice(extra.end, extended.small);
    const operands = try sema.arena.alloc(Value, operand_refs.len);
    for (operand_refs, operands) |ref, *v| v.* = try sema.resolveInst(ref);
    return try sema.analyzeMinMax(operands, op);
}

fn evalReduce(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    const bin = sema.binData(inst);
    const operation = try sema.resolveStdLangEnum(.ReduceOp, bin.lhs);
    const operand = try sema.resolveInst(bin.rhs);
    const operand_ty = operand.typeOf(ip);

    if (operand_ty.zigTypeTag(ip) != .vector) {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "expected vector, found '{f}'", .{operand_ty.fmt(ip)});
    }

    const scalar_ty = operand_ty.childType(ip);
    switch (operation) {
        .And, .Or, .Xor => switch (scalar_ty.zigTypeTag(ip)) {
            .int, .bool => {},
            else => return sema.fail(sema.block, sema.block.nodeOffset(.zero), "@reduce operation '{s}' requires integer or boolean operand; found '{f}'", .{ @tagName(operation), operand_ty.fmt(ip) }),
        },
        .Min, .Max, .Add, .Mul => switch (scalar_ty.zigTypeTag(ip)) {
            .int, .float => {},
            else => return sema.fail(sema.block, sema.block.nodeOffset(.zero), "@reduce operation '{s}' requires integer or float operand; found '{f}'", .{ @tagName(operation), operand_ty.fmt(ip) }),
        },
    }

    const vec_len = operand_ty.vectorLen(ip);
    if (vec_len == 0) {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "@reduce operation requires a vector with nonzero length", .{});
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

fn evalMulAdd(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    const extra = sema.zir.extraData(Zir.Inst.MulAdd, sema.zir.instructions.items(.data)[@backingInt(inst)].pl_node.payload_index).data;
    const addend = try sema.resolveInst(extra.addend);
    const ty = addend.typeOf(ip);
    const mulend1 = try sema.coerceValueToType(try sema.resolveInst(extra.mulend1), ty.toIndex());
    const mulend2 = try sema.coerceValueToType(try sema.resolveInst(extra.mulend2), ty.toIndex());

    switch (ty.scalarType(ip).zigTypeTag(ip)) {
        .comptime_float, .float => {},
        else => {
            return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "expected vector of floats or float type, found '{f}'", .{ty.fmt(ip)});
        },
    }

    if (ip.indexToKey(mulend1.index) == .undef or ip.indexToKey(mulend2.index) == .undef or ip.indexToKey(addend.index) == .undef)
        return .{ .index = try ip.get(.{ .undef = ty.toIndex() }) };
    return try Value.mulAdd(ty, mulend1, mulend2, addend, sema.arena, ip);
}

fn evalAbs(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    const un_node = sema.zir.instructions.items(.data)[@backingInt(inst)].un_node;
    const operand = try sema.resolveInst(un_node.operand);
    const operand_ty = operand.typeOf(ip);
    const scalar_ty = operand_ty.scalarType(ip);

    const result_ty: Type = switch (scalar_ty.zigTypeTag(ip)) {
        .comptime_float, .float, .comptime_int => operand_ty,
        .int => if (scalar_ty.isSignedInt(ip)) try operand_ty.toUnsigned(ip) else return operand,
        else => {
            return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "expected integer, float, or vector of either integers or floats, found '{f}'", .{operand_ty.fmt(ip)});
        },
    };

    return try sema.maybeConstantUnaryMath(operand, result_ty, Value.abs);
}

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

fn evalNegate(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    const inst_data = sema.zir.instructions.items(.data)[@backingInt(inst)].un_node;
    const src = sema.block.nodeOffset(inst_data.src_node);

    const rhs = try sema.resolveInst(inst_data.operand);
    const rhs_ty = rhs.typeOf(ip);
    const rhs_scalar_ty = rhs_ty.scalarType(ip);

    if (rhs_scalar_ty.isUnsignedInt(ip) or switch (rhs_scalar_ty.zigTypeTag(ip)) {
        .int, .comptime_int, .float, .comptime_float => false,
        else => true,
    }) {
        return sema.fail(sema.block, src, "negation of type '{f}'", .{rhs_ty.fmt(ip)});
    }

    if (rhs_scalar_ty.isAnyFloat()) {
        // Handle float negation here to ensure negative zero is represented in the bits.
        return try arith.negateFloat(sema, rhs_ty, rhs);
    }

    const lhs = try sema.splat(rhs_ty, try sema.intValue_u64(rhs_scalar_ty, 0));
    return try arith.sub(sema, rhs_ty, lhs, rhs);
}

fn evalNegateWrap(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    const inst_data = sema.zir.instructions.items(.data)[@backingInt(inst)].un_node;
    const src = sema.block.nodeOffset(inst_data.src_node);

    const rhs = try sema.resolveInst(inst_data.operand);
    const rhs_ty = rhs.typeOf(ip);
    const rhs_scalar_ty = rhs_ty.scalarType(ip);

    switch (rhs_scalar_ty.zigTypeTag(ip)) {
        .int, .comptime_int, .float, .comptime_float => {},
        else => return sema.fail(sema.block, src, "negation of type '{f}'", .{rhs_ty.fmt(ip)}),
    }

    const lhs = try sema.splat(rhs_ty, try sema.intValue_u64(rhs_scalar_ty, 0));
    return try arith.subWrap(sema, rhs_ty, lhs, rhs);
}

fn evalPtrType(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@backingInt(inst) < sema.zir.instructions.len);

    const inst_data = sema.zir.instructions.items(.data)[@backingInt(inst)].ptr_type;
    if (inst_data.flags.has_addrspace or inst_data.flags.has_bit_range) {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "ptr_type: address_space / bit_range not yet supported", .{});
    }

    const extra = sema.zir.extraData(Zir.Inst.PtrType, inst_data.payload_index);
    const payload = extra.data;
    assert(payload.elem_type != .none);

    const child_ty = try sema.resolveDestType(payload.elem_type);
    assert(child_ty != .none);
    if (Type.fromIndex(child_ty).zigTypeTag(sema.intern_pool) == .noreturn) {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "pointer to noreturn not allowed", .{});
    }

    var extra_i = extra.end;
    const sentinel: InternPool.Index = if (inst_data.flags.has_sentinel) blk: {
        const ref: Zir.Inst.Ref = @fromBackingInt(@intCast(sema.zir.extra[extra_i]));
        extra_i += 1;
        break :blk (try sema.coerceValueToType(try sema.resolveInst(ref), child_ty)).index;
    } else .none;
    const alignment: InternPool.Alignment = if (inst_data.flags.has_align) blk: {
        const ref: Zir.Inst.Ref = @fromBackingInt(@intCast(sema.zir.extra[extra_i]));
        extra_i += 1;
        break :blk try sema.alignmentFromValue(try sema.resolveInst(ref));
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

fn validateAlign(sema: *Sema, src: LazySrcLoc, alignment: u64) Error!InternPool.Alignment {
    if (alignment == 0) return sema.fail(sema.block, src, "alignment must be >= 1", .{});
    if (!std.math.isPowerOfTwo(alignment)) {
        return sema.fail(sema.block, src, "alignment value '{d}' is not a power of two", .{alignment});
    }
    return InternPool.Alignment.fromByteUnits(alignment);
}

fn alignmentFromValue(sema: *Sema, value: Value) Error!InternPool.Alignment {
    const bytes = try sema.resolveUsizeInt(value);
    if (bytes == 0 or !std.math.isPowerOfTwo(bytes)) {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "alignment '{d}' is not a power of two", .{bytes});
    }
    return InternPool.Alignment.fromByteUnits(bytes);
}

const SortByAlignDesc = struct {
    aligns: []const InternPool.Alignment,
    fn lessThan(ctx: SortByAlignDesc, a: InternPool.RuntimeOrder, b: InternPool.RuntimeOrder) bool {
        assert(a != .unresolved);
        assert(b != .unresolved);
        if (a == .omitted) return false;
        if (b == .omitted) return true;
        return ctx.aligns[@backingInt(a)].compare(.gt, ctx.aligns[@backingInt(b)]);
    }
};

fn resolveStructLayout(sema: *Sema, struct_ty: InternPool.Index) Error!void {
    const ip = sema.intern_pool;
    assert(ip.indexToKey(struct_ty) == .struct_type);
    if (ip.structLayoutResolved(struct_ty)) return;

    if (ip.indexToKey(struct_ty).struct_type == .declared) {
        // The field count stored at type creation is authoritative; structFieldCount re-derives from
        // ZIR and misreads the main_struct_inst sentinel (index 0) of a namespace/module root.
        const count: u32 = @intCast(ip.loadStructType(struct_ty).field_types.len);
        const names = try sema.arena.alloc(InternPool.NullTerminatedString, count);
        const types = try sema.arena.alloc(InternPool.Index, count);
        const aligns = try sema.arena.alloc(InternPool.Alignment, count);
        const comptime_bits = try sema.arena.alloc(u32, (count + 31) / 32);
        @memset(comptime_bits, 0);
        var i: u32 = 0;
        while (i < count) : (i += 1) {
            const name = (try sema.structFieldNameAt(struct_ty, i)).?;
            const field = (try sema.structFieldByName(struct_ty, name)).?;
            names[i] = name;
            types[i] = field.ty;
            aligns[i] = if (field.align_bytes) |a| .fromByteUnits(a) else .none;
            if (field.is_comptime) comptime_bits[i / 32] |= @as(u32, 1) << @intCast(i % 32);
        }
        try ip.fillDeclaredStructFields(struct_ty, names, types, aligns, comptime_bits);
    }

    const saved_field_types = blk: {
        const f = ip.loadStructType(struct_ty);
        break :blk try sema.arena.dupe(InternPool.Index, f.field_types);
    };
    for (saved_field_types) |field_ty| try sema.ensureLayoutResolved(field_ty);

    if (ip.loadStructType(struct_ty).layout == .@"packed") {
        const backing = backing: {
            if (ip.indexToKey(struct_ty).struct_type == .declared) {
                var block: Block = undefined;
                const cf = try sema.enterContainer(&block, struct_ty, "packed struct backing integer");
                defer cf.restore(sema);
                if (sema.zir.getStructDecl(cf.decl_inst).backing_int_type_body) |body| {
                    break :backing (try sema.resolveInlineBody(body, cf.decl_inst)).index;
                }
            }
            var total_bits: u16 = 0;
            for (ip.loadStructType(struct_ty).field_types) |field_ty| total_bits += @intCast(Type.fromIndex(field_ty).bitSize(ip));
            break :backing try ip.internIntType(.unsigned, total_bits);
        };
        ip.setStructPackedBackingInt(struct_ty, backing);
        const backing_ty: Type = .fromIndex(backing);
        ip.setStructLayout(struct_ty, &.{}, &.{}, @intCast(backing_ty.abiSize(ip)), backing_ty.abiAlignment(ip), backing_ty.classify(ip));
        return;
    }

    const f = ip.loadStructType(struct_ty);
    const fields_len: u32 = @intCast(f.field_types.len);
    const resolved_aligns = try sema.arena.alloc(InternPool.Alignment, fields_len);
    const runtime_order = try sema.arena.alloc(InternPool.RuntimeOrder, fields_len);
    const offsets = try sema.arena.alloc(u32, fields_len);
    var struct_align: InternPool.Alignment = .@"1";
    var has_runtime = false;
    var has_comptime = false;
    var has_npv = false;
    for (f.field_types, resolved_aligns, runtime_order, 0..) |field_ty, *field_align, *order, idx| {
        const explicit_align = f.field_aligns.getOrNone(idx);
        field_align.* = if (explicit_align != .none)
            explicit_align
        else
            Type.fromIndex(field_ty).abiAlignment(ip);
        if (structFieldIsComptime(f, idx)) {
            order.* = .omitted;
            continue;
        }
        order.* = @fromBackingInt(@intCast(idx));
        struct_align = struct_align.maxStrict(field_align.*);
        switch (Type.fromIndex(field_ty).classify(ip)) {
            .one_possible_value => {},
            .no_possible_value => has_npv = true,
            .runtime => has_runtime = true,
            .fully_comptime => has_comptime = true,
            .partially_comptime => {
                has_runtime = true;
                has_comptime = true;
            },
        }
    }
    const class: InternPool.TypeClass = if (has_npv)
        .no_possible_value
    else if (has_comptime)
        (if (has_runtime) .partially_comptime else .fully_comptime)
    else if (has_runtime) .runtime else .one_possible_value;

    if (f.layout == .auto) {
        std.mem.sortUnstable(InternPool.RuntimeOrder, runtime_order, SortByAlignDesc{ .aligns = resolved_aligns }, SortByAlignDesc.lessThan);
    }
    var cur_offset: u64 = 0;
    const order_len: u32 = switch (f.layout) {
        .auto => @intCast(std.mem.sliceTo(runtime_order, .omitted).len),
        .@"extern" => fields_len,
        .@"packed" => unreachable,
    };
    for (0..order_len) |k| {
        const field_idx: u32 = switch (f.layout) {
            .auto => runtime_order[k].toInt().?,
            .@"extern" => @intCast(k),
            .@"packed" => unreachable,
        };
        const offset = resolved_aligns[field_idx].forward(cur_offset);
        offsets[field_idx] = @truncate(offset);
        cur_offset = offset + Type.fromIndex(f.field_types[field_idx]).abiSize(ip);
    }
    const size: u32 = if (class == .no_possible_value) 0 else @intCast(struct_align.forward(cur_offset));
    ip.setStructLayout(struct_ty, runtime_order, offsets, size, struct_align, class);
}

fn resolveUnionFields(sema: *Sema, union_ty: InternPool.Index) Error!void {
    const ip = sema.intern_pool;
    if (ip.indexToKey(union_ty).union_type != .declared) return;
    const count = try sema.unionFieldCount(union_ty);
    const names = try sema.arena.alloc(InternPool.NullTerminatedString, count);
    const types = try sema.arena.alloc(InternPool.Index, count);
    const aligns = try sema.arena.alloc(InternPool.Alignment, count);
    var i: u32 = 0;
    while (i < count) : (i += 1) {
        const name = (try sema.unionFieldNameAt(union_ty, i)).?;
        const field = (try sema.unionFieldByName(union_ty, name)).?;
        names[i] = name;
        types[i] = field.ty;
        aligns[i] = if (field.align_bytes) |a| .fromByteUnits(a) else .none;
    }
    try ip.fillDeclaredUnionFields(union_ty, names, types, aligns);
}

fn resolveUnionLayout(sema: *Sema, union_ty: InternPool.Index) Error!void {
    const ip = sema.intern_pool;
    assert(ip.indexToKey(union_ty) == .union_type);
    if (ip.unionLayoutResolved(union_ty)) return;
    try sema.resolveUnionFields(union_ty);

    const saved_field_types = blk: {
        const f = ip.unionFields(union_ty);
        break :blk try sema.arena.dupe(InternPool.Index, f.field_types);
    };
    for (saved_field_types) |field_ty| try sema.ensureLayoutResolved(field_ty);

    if (ip.unionFields(union_ty).layout == .@"packed") {
        const uf = ip.unionFields(union_ty);
        // Every field of a packed union must have the same bit width; the backing integer is that
        // width. The first field sets it and the rest must agree.
        const first_field_bits = Type.fromIndex(uf.field_types[0]).bitSize(ip);
        for (uf.field_types[1..]) |field_ty| {
            if (Type.fromIndex(field_ty).bitSize(ip) != first_field_bits) {
                return sema.fail(sema.block, sema.block.nodeOffset(.zero), "field bit width does not match earlier field", .{});
            }
        }
        const backing_int_bits = std.math.cast(u16, first_field_bits) orelse
            return sema.fail(sema.block, sema.block.nodeOffset(.zero), "packed union bit width '{d}' exceeds maximum bit width of 65535", .{first_field_bits});
        const backing = try ip.internIntType(.unsigned, backing_int_bits);
        ip.setUnionPackedBackingInt(union_ty, backing);
        const backing_ty: Type = .fromIndex(backing);
        ip.setUnionLayout(union_ty, @intCast(backing_ty.abiSize(ip)), backing_ty.abiAlignment(ip), backing_ty.classify(ip), false);
        return;
    }

    const tag_usage = ip.unionFields(union_ty).tag_usage;
    const enum_tag_ty: InternPool.Index = if (tag_usage != .none) try sema.unionTagEnumType(union_ty) else .none;
    if (tag_usage != .none) {
        try sema.ensureLayoutResolved(enum_tag_ty);
        // Persist the resolved tag enum on the type so a tagged union's tag can be read from the type,
        // not only recovered from a value. A declared union's tag enum is generated
        // lazily above, so this is the first point it is knowable.
        ip.setUnionEnumTagType(union_ty, enum_tag_ty);
    }

    const f = ip.unionFields(union_ty);
    var payload_align: InternPool.Alignment = .@"1";
    var payload_size: u64 = 0;
    var possible_tags: u32 = 0;
    var payload_has_comptime = false;
    for (f.field_types, 0..) |field_ty, idx| {
        const explicit_align = f.field_aligns.getOrNone(idx);
        const field_align: InternPool.Alignment = if (explicit_align != .none)
            explicit_align
        else
            Type.fromIndex(field_ty).abiAlignment(ip);
        payload_align = payload_align.maxStrict(field_align);
        payload_size = @max(payload_size, Type.fromIndex(field_ty).abiSize(ip));
        switch (Type.fromIndex(field_ty).classify(ip)) {
            .no_possible_value => {},
            .one_possible_value, .runtime => possible_tags += 1,
            .partially_comptime, .fully_comptime => {
                possible_tags += 1;
                payload_has_comptime = true;
            },
        }
    }
    const has_runtime_tag = switch (possible_tags) {
        0, 1 => false,
        else => tag_usage != .none and !payload_has_comptime,
    };
    const class: InternPool.TypeClass = class: {
        if (possible_tags == 0) break :class .no_possible_value;
        if (payload_has_comptime) break :class if (payload_size > 0) .partially_comptime else .fully_comptime;
        break :class if (has_runtime_tag or payload_size > 0) .runtime else .one_possible_value;
    };
    const size: u64, const alignment: InternPool.Alignment = layout: {
        if (!has_runtime_tag) break :layout .{ payload_align.forward(payload_size), payload_align };
        const tag_align = Type.fromIndex(enum_tag_ty).abiAlignment(ip);
        const tag_size = Type.fromIndex(enum_tag_ty).abiSize(ip);
        const alignment = tag_align.maxStrict(payload_align);
        break :layout .{ alignment.forward(tag_size + payload_size), alignment };
    };
    ip.setUnionLayout(union_ty, @intCast(size), alignment, class, has_runtime_tag);
}

pub fn ensureLayoutResolved(sema: *Sema, ty: InternPool.Index) Error!void {
    const ip = sema.intern_pool;
    switch (ip.indexToKey(ty)) {
        .int_type, .ptr_type, .anyframe_type, .simple_type, .error_set_type, .opaque_type => {},
        .array_type => |arr| return sema.ensureLayoutResolved(arr.child),
        .vector_type => |vec| return sema.ensureLayoutResolved(vec.child),
        .opt_type => |child| return sema.ensureLayoutResolved(child),
        .error_union_type => |eu| return sema.ensureLayoutResolved(eu.payload_type),
        .tuple_type => |tuple| for (tuple.types) |field_ty| try sema.ensureLayoutResolved(field_ty),
        .func_type => |ft| {
            for (ft.param_types) |param_ty| try sema.ensureLayoutResolved(param_ty);
            try sema.ensureLayoutResolved(ft.return_type);
        },
        .enum_type => {},
        .struct_type => try sema.resolveStructLayout(ty),
        .union_type => try sema.resolveUnionLayout(ty),
        .simple_value, .enum_literal, .int, .float, .undef, .ptr, .slice, .err, .error_union, .func, .@"extern", .opt, .aggregate, .enum_tag, .un, .bitpack => unreachable,
    }
}

fn evalAlignOf(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    const un_node = sema.zir.instructions.items(.data)[@backingInt(inst)].un_node;
    const operand_src = sema.block.builtinCallArgSrc(un_node.src_node, 0);
    const ty: Type = .fromIndex(try sema.resolveDestType(un_node.operand));
    try sema.ensureLayoutResolved(ty.index);
    if (ty.isNoReturn(ip)) {
        return sema.fail(sema.block, operand_src, "no align available for uninstantiable type '{f}'", .{ty.fmt(ip)});
    }
    return .{ .index = try ip.internInt(.{ .ty = .comptime_int_type, .storage = .{ .u64 = ty.abiAlignment(ip).toByteUnits().? } }) };
}

fn evalSizeOf(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    const un_node = sema.zir.instructions.items(.data)[@backingInt(inst)].un_node;
    const operand_src = sema.block.builtinCallArgSrc(un_node.src_node, 0);
    const ty: Type = .fromIndex(try sema.resolveDestType(un_node.operand));
    try sema.ensureLayoutResolved(ty.index);
    switch (ty.classify(ip)) {
        .no_possible_value => return sema.fail(sema.block, operand_src, "no size available for uninstantiable type '{f}'", .{ty.fmt(ip)}),
        .partially_comptime, .fully_comptime => return sema.fail(sema.block, operand_src, "no size available for comptime-only type '{f}'", .{ty.fmt(ip)}),
        .one_possible_value => {
            assert(ty.abiSize(ip) == 0);
            return .{ .index = .zero };
        },
        .runtime => return .{ .index = try ip.internInt(.{ .ty = .comptime_int_type, .storage = .{ .u64 = ty.abiSize(ip) } }) },
    }
}

fn evalOffsetOf(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@backingInt(inst) < sema.zir.instructions.len);
    const ip = sema.intern_pool;
    const pl_node = sema.zir.instructions.items(.data)[@backingInt(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.Bin, pl_node.payload_index).data;
    const ty = try sema.resolveDestType(extra.lhs);
    const field_name = try sema.resolveConstStringIntern(extra.rhs);
    if (Type.fromIndex(ty).zigTypeTag(ip) != .@"struct") {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "expected struct type, found '{f}'", .{Type.fromIndex(ty).fmt(ip)});
    }
    try sema.ensureLayoutResolved(ty);
    const field = (try sema.structFieldByName(ty, field_name)) orelse return sema.failNoMember(ty, field_name);
    if (field.is_comptime) {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "no offset available for comptime field", .{});
    }
    const offset = Type.fromIndex(ty).structFieldOffset(ip, field.index);
    return .{ .index = try ip.internInt(.{ .ty = .comptime_int_type, .storage = .{ .u64 = offset } }) };
}

fn evalBitOffsetOf(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@backingInt(inst) < sema.zir.instructions.len);
    const ip = sema.intern_pool;
    const pl_node = sema.zir.instructions.items(.data)[@backingInt(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.Bin, pl_node.payload_index).data;
    const ty = try sema.resolveDestType(extra.lhs);
    const field_name = try sema.resolveConstStringIntern(extra.rhs);
    if (Type.fromIndex(ty).zigTypeTag(ip) != .@"struct") {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "expected struct type, found '{f}'", .{Type.fromIndex(ty).fmt(ip)});
    }
    try sema.ensureLayoutResolved(ty);
    const field = (try sema.structFieldByName(ty, field_name)) orelse return sema.failNoMember(ty, field_name);
    if (field.is_comptime) {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "no offset available for comptime field", .{});
    }
    const bit_offset: u64 = switch (Type.fromIndex(ty).containerLayout(ip)) {
        .@"packed" => blk: {
            var bit_sum: u64 = 0;
            var preceding: u32 = 0;
            while (preceding < field.index) : (preceding += 1) {
                const pname = (try sema.structFieldNameAt(ty, preceding)).?;
                const pf = (try sema.structFieldByName(ty, pname)).?;
                bit_sum += Type.fromIndex(pf.ty).bitSize(ip);
            }
            break :blk bit_sum;
        },
        else => Type.fromIndex(ty).structFieldOffset(ip, field.index) * 8,
    };
    return .{ .index = try ip.internInt(.{ .ty = .comptime_int_type, .storage = .{ .u64 = bit_offset } }) };
}

fn checkPtrType(sema: *Sema, ty: Type, allow_slice: bool) Error!void {
    const ip = sema.intern_pool;
    switch (ty.zigTypeTag(ip)) {
        .pointer => if (allow_slice or !ty.isSlice(ip)) return,
        .optional => if (ty.childType(ip).zigTypeTag(ip) == .pointer) return,
        else => {},
    }
    return sema.fail(sema.block, sema.block.nodeOffset(.zero), "expected pointer type, found '{f}'", .{ty.fmt(ip)});
}

/// The fn-pointer address mask (`fnPtrMaskOrNull`) is not modeled, so alignment is checked against the
/// raw address; for data pointers the compiler's mask is a no-op.
fn ptrFromIntVal(sema: *Sema, operand_val: Value, ptr_ty: Type, ptr_align: InternPool.Alignment) Error!Value {
    const ip = sema.intern_pool;
    if (operand_val.isUndef(ip)) {
        if (ptr_ty.ptrAllowsZero(ip) and ptr_align == .@"1") return .fromIndex(try ip.get(.{ .undef = ptr_ty.index }));
        return sema.failWithUseOfUndef();
    }
    const addr = operand_val.toUnsignedInt(ip);
    if (!ptr_ty.ptrAllowsZero(ip) and addr == 0)
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "pointer type '{f}' does not allow address zero", .{ptr_ty.fmt(ip)});
    if (addr != 0 and ptr_align != .none) {
        if (!ptr_align.check(addr))
            return sema.fail(sema.block, sema.block.nodeOffset(.zero), "pointer type '{f}' requires aligned address", .{ptr_ty.fmt(ip)});
    }
    return switch (ptr_ty.zigTypeTag(ip)) {
        .optional => .fromIndex(try ip.get(.{ .opt = .{
            .ty = ptr_ty.index,
            .val = if (addr == 0) .none else try ip.internPtr(.{ .ty = ptr_ty.childType(ip).index, .base_addr = .int, .byte_offset = addr }),
        } })),
        .pointer => .fromIndex(try ip.internPtr(.{ .ty = ptr_ty.index, .base_addr = .int, .byte_offset = addr })),
        else => unreachable,
    };
}

fn evalPtrFromInt(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@backingInt(inst) < sema.zir.instructions.len);
    const ip = sema.intern_pool;
    const pl_node = sema.zir.instructions.items(.data)[@backingInt(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.Bin, pl_node.payload_index).data;
    const operand = try sema.resolveInst(extra.rhs);
    const uncoerced_operand_ty = operand.typeOf(ip);
    const dest_ty = try sema.resolveDestType(extra.lhs);
    try sema.checkVectorizableBinaryOperands(Type.fromIndex(dest_ty), uncoerced_operand_ty);

    const is_vector = Type.fromIndex(dest_ty).zigTypeTag(ip) == .vector;
    const operand_ty: InternPool.Index = if (is_vector)
        try ip.internVectorType(.{ .child = .usize_type, .len = Type.fromIndex(dest_ty).vectorLen(ip) })
    else
        .usize_type;
    const operand_coerced = try sema.coerceValueToType(operand, operand_ty);

    const ptr_ty = Type.fromIndex(dest_ty).scalarType(ip);
    try sema.checkPtrType(ptr_ty, true);
    const elem_ty = ptr_ty.nullablePtrElem(ip);
    try sema.ensureLayoutResolved(elem_ty.index);
    const ptr_align = ptr_ty.ptrAlignment(ip);

    if (ptr_ty.isSlice(ip))
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "integer cannot be converted to slice type '{f}'", .{ptr_ty.fmt(ip)});

    if (!is_vector) return try sema.ptrFromIntVal(operand_coerced, ptr_ty, ptr_align);

    const len = Type.fromIndex(dest_ty).vectorLen(ip);
    const new_elems = try sema.arena.alloc(InternPool.Index, len);
    for (new_elems, 0..) |*new_elem, elem_idx| {
        const elem = try operand_coerced.elemValue(ip, elem_idx);
        new_elem.* = (try sema.ptrFromIntVal(elem, ptr_ty, ptr_align)).index;
    }
    return try sema.aggregateValue(Type.fromIndex(dest_ty), new_elems);
}

fn checkPtrOperand(sema: *Sema, ty: Type) Error!void {
    const ip = sema.intern_pool;
    switch (ty.zigTypeTag(ip)) {
        .pointer => return,
        .@"fn" => return sema.failWithOwnedErrorMsg(sema.block, msg: {
            const msg = try sema.errMsg(sema.block.nodeOffset(.zero), "expected pointer, found '{f}'", .{ty.fmt(ip)});
            errdefer msg.destroy(sema.gpa);
            try sema.errNote(sema.block.nodeOffset(.zero), msg, "use '&' to obtain a function pointer", .{});
            break :msg msg;
        }),
        .optional => if (ty.childType(ip).zigTypeTag(ip) == .pointer) return,
        else => {},
    }
    return sema.fail(sema.block, sema.block.nodeOffset(.zero), "expected pointer type, found '{f}'", .{ty.fmt(ip)});
}

fn evalPtrCast(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const pl_node = sema.zir.instructions.items(.data)[@backingInt(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.Bin, pl_node.payload_index).data;
    const dest_ty = try sema.resolveDestType(extra.lhs);
    const operand = try sema.resolveInst(extra.rhs);
    return try sema.ptrCastFull(.{ .ptr_cast = true }, operand, Type.fromIndex(dest_ty), "@ptrCast");
}

fn evalPtrCastFull(sema: *Sema, extended: Zir.Inst.Extended.InstData) Error!?Value {
    const flags: std.zig.Zir.Inst.FullPtrCastFlags = @bitCast(@as(u5, @truncate(extended.small)));
    const extra = sema.zir.extraData(Zir.Inst.BinNode, extended.operand).data;
    const operand = try sema.resolveInst(extra.rhs);
    const dest_ty = try sema.resolveDestType(extra.lhs);
    return try sema.ptrCastFull(flags, operand, Type.fromIndex(dest_ty), flags.needResultTypeBuiltinName());
}

fn evalPtrCastNoDest(sema: *Sema, extended: Zir.Inst.Extended.InstData) Error!?Value {
    const ip = sema.intern_pool;
    const flags: std.zig.Zir.Inst.FullPtrCastFlags = @bitCast(@as(u5, @truncate(extended.small)));
    const extra = sema.zir.extraData(Zir.Inst.UnNode, extended.operand).data;
    const operand = try sema.resolveInst(extra.operand);
    const operand_ty = operand.typeOf(ip);
    try sema.checkPtrOperand(operand_ty);

    var ptr_info = operand_ty.ptrInfo(ip);
    if (flags.const_cast) ptr_info.flags.is_const = false;
    if (flags.volatile_cast) ptr_info.flags.is_volatile = false;

    const dest_ty = blk: {
        const dest_ptr = try ip.internPtrType(ptr_info);
        if (operand_ty.zigTypeTag(ip) == .optional) break :blk try ip.internOptionalType(dest_ptr);
        break :blk dest_ptr;
    };
    return .{ .index = try ip.getCoerced(operand.index, dest_ty) };
}

fn evalFieldParentPtr(sema: *Sema, extended: Zir.Inst.Extended.InstData) Error!?Value {
    const ip = sema.intern_pool;
    const extra = sema.zir.extraData(Zir.Inst.FieldParentPtr, extended.operand).data;
    const flags: std.zig.Zir.Inst.FullPtrCastFlags = @bitCast(@as(u5, @truncate(extended.small)));
    assert(!flags.ptr_cast);
    const inst_src = sema.block.nodeOffset(extra.src_node);
    const field_ptr_src = sema.block.builtinCallArgSrc(extra.src_node, 1);

    var maybe_opt_parent_ptr_ty = Type.fromIndex(try sema.resolveDestType(extra.parent_ptr_type));
    // `.remove_eu`: an error-union result-type hint is stripped to its payload, as the compiler's
    // `resolveDestType` does, so `const p: E!*P = @fieldParentPtr(...)` resolves the parent pointer type.
    if (maybe_opt_parent_ptr_ty.zigTypeTag(ip) == .error_union) maybe_opt_parent_ptr_ty = maybe_opt_parent_ptr_ty.errorUnionPayload(ip);
    try sema.checkPtrType(maybe_opt_parent_ptr_ty, true);
    const parent_ptr_ty = switch (maybe_opt_parent_ptr_ty.zigTypeTag(ip)) {
        .optional => maybe_opt_parent_ptr_ty.optionalChild(ip),
        .pointer => maybe_opt_parent_ptr_ty,
        else => unreachable,
    };
    const parent_ptr_info = parent_ptr_ty.ptrInfo(ip);
    if (parent_ptr_info.flags.size != .one) {
        return sema.fail(sema.block, inst_src, "expected single pointer type, found '{f}'", .{parent_ptr_ty.fmt(ip)});
    }
    const parent_ty = Type.fromIndex(parent_ptr_info.child);
    try sema.ensureLayoutResolved(parent_ty.index);
    switch (parent_ty.zigTypeTag(ip)) {
        .@"struct", .@"union" => {},
        else => return sema.fail(sema.block, inst_src, "expected pointer to struct or union type, found '{f}'", .{parent_ptr_ty.fmt(ip)}),
    }

    const field_name = try sema.resolveConstStringIntern(extra.field_name);
    const field_index = switch (parent_ty.zigTypeTag(ip)) {
        .@"struct" => if (parent_ty.isTuple(ip)) blk: {
            if (field_name.eqlSlice("len", ip)) {
                return sema.fail(sema.block, inst_src, "cannot get @fieldParentPtr of 'len' field of tuple", .{});
            }
            break :blk try sema.tupleFieldIndex(parent_ty.index, field_name);
        } else ((try sema.structFieldByName(parent_ty.index, field_name)) orelse return sema.failBadStructFieldAccess(parent_ty.index, field_name)).index,
        .@"union" => ((try sema.unionFieldByName(parent_ty.index, field_name)) orelse return sema.failBadUnionFieldAccess(parent_ty.index, field_name)).index,
        else => unreachable,
    };
    if (parent_ty.zigTypeTag(ip) == .@"struct" and parent_ty.structFieldIsComptime(field_index, ip)) {
        return sema.fail(sema.block, inst_src, "cannot get @fieldParentPtr of a comptime field", .{});
    }

    const field_ptr = try sema.resolveInst(extra.field_ptr);
    const field_ptr_ty = field_ptr.typeOf(ip);
    try sema.checkPtrOperand(field_ptr_ty);

    const hypothetical_field_ptr_ty = try parent_ptr_ty.fieldPtrType(field_index, ip);
    const casted_field_ptr = try sema.ptrCastFull(flags, field_ptr, hypothetical_field_ptr_ty, "@fieldParentPtr");

    const unaligned_parent_ptr_ty = Type.fromIndex(try ip.internPtrType(info: {
        var info = parent_ptr_info;
        info.flags.alignment = hypothetical_field_ptr_ty.ptrAlignment(ip);
        break :info info;
    }));

    // The field pointer is always comptime-known here (no runtime AIR layer to defer to), so the
    // compiler's runtime `field_parent_ptr` AIR branch is absent.
    const field_ptr_val = casted_field_ptr;
    const unaligned_parent_ptr: Value = switch (parent_ty.containerLayout(ip)) {
        .@"packed" => .{ .index = try ip.getCoerced(field_ptr_val.index, unaligned_parent_ptr_ty.index) },
        .@"extern" => switch (parent_ty.zigTypeTag(ip)) {
            .@"struct" => try sema.ptrSubtract(field_ptr_src, field_ptr_val, parent_ty.structFieldOffset(ip, field_index), unaligned_parent_ptr_ty),
            .@"union" => .{ .index = try ip.getCoerced(field_ptr_val.index, unaligned_parent_ptr_ty.index) },
            else => unreachable,
        },
        .auto => result: {
            const opt_field: ?InternPool.Key.Ptr.BaseAddr.BaseIndex = opt_field: {
                const ptr = switch (ip.indexToKey(field_ptr_val.index)) {
                    .ptr => |ptr| ptr,
                    else => break :opt_field null,
                };
                if (ptr.byte_offset != 0) break :opt_field null;
                break :opt_field switch (ptr.base_addr) {
                    .field => |field| field,
                    else => null,
                };
            };

            const field = opt_field orelse {
                return sema.fail(sema.block, field_ptr_src, "pointer value not based on parent struct", .{});
            };

            if ((Value{ .index = field.base }).typeOf(ip).childType(ip).index != parent_ty.index) {
                return sema.fail(sema.block, field_ptr_src, "pointer value not based on parent struct", .{});
            }
            if (field.index != field_index) {
                return sema.fail(sema.block, inst_src, "field '{f}' has index '{d}' but pointer value is index '{d}' of struct '{f}'", .{ field_name.fmt(ip), field_index, field.index, parent_ty.fmt(ip) });
            }
            break :result .{ .index = try ip.getCoerced(field.base, unaligned_parent_ptr_ty.index) };
        },
    };

    // If the hypothetical field pointer has lower alignment than the parent pointer, an `@alignCast` is
    // required; otherwise coerce directly. A field pointer can never increase alignment.
    const field_align = hypothetical_field_ptr_ty.ptrAlignment(ip);
    const parent_align = parent_ptr_ty.ptrAlignment(ip);
    assert(!field_align.compare(.gt, parent_align));
    if (field_align.compare(.eq, parent_align)) {
        return try sema.coerceValueToType(unaligned_parent_ptr, maybe_opt_parent_ptr_ty.index);
    }
    if (flags.align_cast) {
        return try sema.ptrCastFull(flags, unaligned_parent_ptr, maybe_opt_parent_ptr_ty, "@fieldParentPtr");
    }
    return sema.failWithOwnedErrorMsg(sema.block, msg: {
        const msg = try sema.errMsg(inst_src, "@fieldParentPtr increases pointer alignment", .{});
        errdefer msg.destroy(sema.gpa);
        try sema.errNote(inst_src, msg, "parent pointer type '{f}' has alignment '{d}'", .{ parent_ptr_ty.fmt(ip), @backingInt(parent_ptr_ty.abiAlignment(ip)) });
        if (parent_ty.isTuple(ip)) {
            try sema.errNote(field_ptr_src, msg, "tuple field '{d}' limits alignment to '{d}'", .{ field_index, @backingInt(field_ptr_ty.ptrAlignment(ip)) });
        } else {
            try sema.errNote(sema.containerTypeSrc(parent_ty.index), msg, "{s} field '{f}' limits alignment to '{d}'", .{ @tagName(parent_ty.zigTypeTag(ip)), field_name.fmt(ip), @backingInt(field_ptr_ty.ptrAlignment(ip)) });
        }
        try sema.errNote(inst_src, msg, "use @alignCast to assert pointer alignment", .{});
        break :msg msg;
    });
}

/// A copy of `ptr_val` with `byte_subtract` removed from its byte offset, retyped to `new_ty`. Mirrors
/// the compiler's `ptrSubtract`.
fn ptrSubtract(sema: *Sema, src: LazySrcLoc, ptr_val: Value, byte_subtract: u64, new_ty: Type) Error!Value {
    const ip = sema.intern_pool;
    if (byte_subtract == 0) return .{ .index = try ip.getCoerced(ptr_val.index, new_ty.index) };
    const ptr = switch (ip.indexToKey(ptr_val.index)) {
        .undef => return sema.failWithUseOfUndef(),
        .ptr => |ptr| ptr,
        else => unreachable,
    };
    if (ptr.byte_offset < byte_subtract) {
        return sema.failWithOwnedErrorMsg(sema.block, msg: {
            const msg = try sema.errMsg(src, "pointer computation here causes illegal behavior", .{});
            errdefer msg.destroy(sema.gpa);
            try sema.errNote(src, msg, "resulting pointer exceeds bounds of containing value which may trigger overflow", .{});
            break :msg msg;
        });
    }
    return .{ .index = try ip.internPtr(.{
        .ty = new_ty.index,
        .base_addr = ptr.base_addr,
        .byte_offset = ptr.byte_offset - byte_subtract,
    }) };
}

fn ptrCastFull(
    sema: *Sema,
    flags: std.zig.Zir.Inst.FullPtrCastFlags,
    operand: Value,
    dest_ty: Type,
    operation: []const u8,
) Error!Value {
    const ip = sema.intern_pool;
    const operand_ty = operand.typeOf(ip);

    try sema.checkPtrType(dest_ty, true);
    try sema.checkPtrOperand(operand_ty);

    const src_info = operand_ty.ptrInfo(ip);
    const dest_info = dest_ty.ptrInfo(ip);

    try sema.ensureLayoutResolved(src_info.child);
    try sema.ensureLayoutResolved(dest_info.child);

    const DestSliceLen = union(enum) { undef, constant: u64 };
    // The operand is always comptime-known in the REPL, so a slice's length is always
    // known here; the compiler's runtime-slice length variants are the absent runtime layer.
    const dest_slice_len: ?DestSliceLen = len: {
        switch (dest_info.flags.size) {
            .slice => {},
            .many, .c, .one => break :len null,
        }
        const src_elem_ty: Type, const src_len: u64 = switch (src_info.flags.size) {
            .one => src: {
                const true_child: Type = .fromIndex(src_info.child);
                break :src switch (true_child.zigTypeTag(ip)) {
                    .array => .{ true_child.childType(ip), true_child.arrayLen(ip) },
                    else => .{ true_child, 1 },
                };
            },
            .slice => src: {
                if (operand.isUndef(ip)) break :len .undef;
                const slice_val: Value = switch (operand_ty.zigTypeTag(ip)) {
                    .optional => switch (ip.indexToKey(operand.index).opt.val) {
                        .none => break :len .undef,
                        else => |payload| .{ .index = payload },
                    },
                    .pointer => operand,
                    else => unreachable,
                };
                const slice_len: Value = .{ .index = ip.indexToKey(slice_val.index).slice.len };
                if (slice_len.isUndef(ip)) break :len .undef;
                break :src .{ .fromIndex(src_info.child), slice_len.toUnsignedInt(ip) };
            },
            .many, .c => {
                return sema.fail(sema.block, sema.block.nodeOffset(.zero), "cannot infer length of slice from {s}", .{pointerSizeString(src_info.flags.size)});
            },
        };
        const dest_elem_ty: Type = .fromIndex(dest_info.child);
        if (dest_elem_ty.index == src_elem_ty.index) {
            break :len .{ .constant = src_len };
        }
        if (!src_elem_ty.comptimeOnly(ip) and !dest_elem_ty.comptimeOnly(ip)) {
            if (src_elem_ty.zigTypeTag(ip) == .@"opaque") {
                return sema.fail(sema.block, sema.block.nodeOffset(.zero), "cannot infer length of slice of '{f}' from pointer to opaque type '{f}' with unknown size", .{ dest_elem_ty.fmt(ip), src_elem_ty.fmt(ip) });
            }
            const src_elem_size = src_elem_ty.abiSize(ip);
            const dest_elem_size = dest_elem_ty.abiSize(ip);
            if (dest_elem_size == 0) {
                return sema.fail(sema.block, sema.block.nodeOffset(.zero), "cannot infer length of slice of zero-bit '{f}' from '{f}'", .{ dest_elem_ty.fmt(ip), operand_ty.fmt(ip) });
            }
            const bytes = src_len * src_elem_size;
            const dest_len = std.math.divExact(u64, bytes, dest_elem_size) catch {
                return sema.fail(sema.block, sema.block.nodeOffset(.zero), "type '{f}' does not divide exactly into destination elements", .{Type.fromIndex(src_info.child).fmt(ip)});
            };
            break :len .{ .constant = dest_len };
        }
        // Comptime-only element types can be "restructured", consistent with comptime loads/stores.
        const dest_base_ty: Type, const dest_base_per_elem: u64 = dest_elem_ty.arrayBase(ip);
        const src_base_ty: Type, const src_base_per_elem: u64 = src_elem_ty.arrayBase(ip);
        if (dest_base_ty.index != src_base_ty.index) {
            return sema.fail(sema.block, sema.block.nodeOffset(.zero), "cannot infer length of comptime-only '{f}' from incompatible '{f}'", .{ dest_ty.fmt(ip), operand_ty.fmt(ip) });
        }
        const base_len = src_len * src_base_per_elem;
        const dest_len = std.math.divExact(u64, base_len, dest_base_per_elem) catch {
            return sema.fail(sema.block, sema.block.nodeOffset(.zero), "type '{f}' does not divide exactly into destination elements", .{src_elem_ty.fmt(ip)});
        };
        break :len .{ .constant = dest_len };
    };

    // The checking logic here must stay in sync with coerceInMemoryAllowedPtrs.
    if (!flags.ptr_cast) {
        const is_array_ptr_to_slice = b: {
            if (dest_info.flags.size != .slice) break :b false;
            if (src_info.flags.size != .one) break :b false;
            const src_pointer_child: Type = .fromIndex(src_info.child);
            if (src_pointer_child.zigTypeTag(ip) != .array) break :b false;
            break :b src_pointer_child.childType(ip).index == dest_info.child;
        };

        check_size: {
            if (src_info.flags.size == dest_info.flags.size) break :check_size;
            if (is_array_ptr_to_slice) break :check_size;
            if (src_info.flags.size == .c) break :check_size;
            if (dest_info.flags.size == .c) break :check_size;
            return sema.failWithOwnedErrorMsg(sema.block, msg: {
                const msg = try sema.errMsg(sema.block.nodeOffset(.zero), "cannot implicitly convert {s} to {s}", .{ pointerSizeString(src_info.flags.size), pointerSizeString(dest_info.flags.size) });
                errdefer msg.destroy(sema.gpa);
                if (dest_info.flags.size == .many and
                    (src_info.flags.size == .slice or
                        (src_info.flags.size == .one and Type.fromIndex(src_info.child).zigTypeTag(ip) == .array)))
                {
                    try sema.errNote(sema.block.nodeOffset(.zero), msg, "use 'ptr' field to convert slice to many pointer", .{});
                } else {
                    try sema.errNote(sema.block.nodeOffset(.zero), msg, "use @ptrCast to change pointer size", .{});
                }
                break :msg msg;
            });
        }

        check_child: {
            const src_child: Type = if (dest_info.flags.size == .slice and src_info.flags.size == .one)
                Type.fromIndex(src_info.child).childType(ip)
            else
                .fromIndex(src_info.child);
            const dest_child: Type = .fromIndex(dest_info.child);
            if (.ok == try sema.coerceInMemoryAllowed(dest_child, src_child, !dest_info.flags.is_const, null)) break :check_child;
            return sema.failWithOwnedErrorMsg(sema.block, msg: {
                const msg = try sema.errMsg(sema.block.nodeOffset(.zero), "pointer element type '{f}' cannot coerce into element type '{f}'", .{ src_child.fmt(ip), dest_child.fmt(ip) });
                errdefer msg.destroy(sema.gpa);
                try sema.errNote(sema.block.nodeOffset(.zero), msg, "use @ptrCast to cast pointer element type", .{});
                break :msg msg;
            });
        }

        check_sent: {
            if (dest_info.sentinel == .none) break :check_sent;
            if (src_info.flags.size == .c) break :check_sent;
            if (src_info.sentinel != .none) {
                const coerced_sent = try ip.getCoerced(src_info.sentinel, dest_info.child);
                if (dest_info.sentinel == coerced_sent) break :check_sent;
            }
            if (is_array_ptr_to_slice) {
                const arr_ty: Type = .fromIndex(src_info.child);
                if (arr_ty.sentinel(ip)) |src_sentinel| {
                    const coerced_sent = try ip.getCoerced(src_sentinel.index, dest_info.child);
                    if (dest_info.sentinel == coerced_sent) break :check_sent;
                }
            }
            return sema.failWithOwnedErrorMsg(sema.block, msg: {
                const msg = if (src_info.sentinel == .none)
                    try sema.errMsg(sema.block.nodeOffset(.zero), "destination pointer requires a sentinel", .{})
                else
                    try sema.errMsg(sema.block.nodeOffset(.zero), "pointer sentinel cannot coerce into destination pointer sentinel", .{});
                errdefer msg.destroy(sema.gpa);
                try sema.errNote(sema.block.nodeOffset(.zero), msg, "use @ptrCast to cast pointer sentinel", .{});
                break :msg msg;
            });
        }

        if (src_info.packed_offset.host_size != dest_info.packed_offset.host_size) {
            return sema.failWithOwnedErrorMsg(sema.block, msg: {
                const msg = try sema.errMsg(sema.block.nodeOffset(.zero), "pointer host size '{d}' cannot coerce into pointer host size '{d}'", .{ src_info.packed_offset.host_size, dest_info.packed_offset.host_size });
                errdefer msg.destroy(sema.gpa);
                try sema.errNote(sema.block.nodeOffset(.zero), msg, "use @ptrCast to cast pointer host size", .{});
                break :msg msg;
            });
        }

        if (src_info.packed_offset.bit_offset != dest_info.packed_offset.bit_offset) {
            return sema.failWithOwnedErrorMsg(sema.block, msg: {
                const msg = try sema.errMsg(sema.block.nodeOffset(.zero), "pointer bit offset '{d}' cannot coerce into pointer bit offset '{d}'", .{ src_info.packed_offset.bit_offset, dest_info.packed_offset.bit_offset });
                errdefer msg.destroy(sema.gpa);
                try sema.errNote(sema.block.nodeOffset(.zero), msg, "use @ptrCast to cast pointer bit offset", .{});
                break :msg msg;
            });
        }

        check_allowzero: {
            const src_allows_zero = operand_ty.ptrAllowsZero(ip);
            const dest_allows_zero = dest_ty.ptrAllowsZero(ip);
            if (!src_allows_zero) break :check_allowzero;
            if (dest_allows_zero) break :check_allowzero;
            return sema.failWithOwnedErrorMsg(sema.block, msg: {
                const msg = try sema.errMsg(sema.block.nodeOffset(.zero), "'{f}' could have null values which are illegal in type '{f}'", .{ operand_ty.fmt(ip), dest_ty.fmt(ip) });
                errdefer msg.destroy(sema.gpa);
                try sema.errNote(sema.block.nodeOffset(.zero), msg, "use @ptrCast to assert the pointer is not null", .{});
                break :msg msg;
            });
        }
    }

    const src_align = if (src_info.flags.alignment != .none)
        src_info.flags.alignment
    else
        Type.fromIndex(src_info.child).abiAlignment(ip);
    const dest_align = if (dest_info.flags.alignment != .none)
        dest_info.flags.alignment
    else
        Type.fromIndex(dest_info.child).abiAlignment(ip);

    if (!flags.align_cast) {
        if (dest_align.compare(.gt, src_align)) {
            return sema.failWithOwnedErrorMsg(sema.block, msg: {
                const msg = try sema.errMsg(sema.block.nodeOffset(.zero), "{s} increases pointer alignment", .{operation});
                errdefer msg.destroy(sema.gpa);
                try sema.errNote(sema.block.nodeOffset(.zero), msg, "'{f}' has alignment '{d}'", .{ operand_ty.fmt(ip), src_align.toByteUnits() orelse 0 });
                try sema.errNote(sema.block.nodeOffset(.zero), msg, "'{f}' has alignment '{d}'", .{ dest_ty.fmt(ip), dest_align.toByteUnits() orelse 0 });
                try sema.errNote(sema.block.nodeOffset(.zero), msg, "use @alignCast to assert pointer alignment", .{});
                break :msg msg;
            });
        }
    }

    // `@addrSpaceCast` (which would set `addrspace_cast`) is not among these builtins, so the
    // address space must match; the compiler's `else` branch validating a real cast is unreachable here.
    if (!flags.addrspace_cast) {
        if (src_info.flags.address_space != dest_info.flags.address_space) {
            return sema.failWithOwnedErrorMsg(sema.block, msg: {
                const msg = try sema.errMsg(sema.block.nodeOffset(.zero), "{s} changes pointer address space", .{operation});
                errdefer msg.destroy(sema.gpa);
                try sema.errNote(sema.block.nodeOffset(.zero), msg, "'{f}' has address space '{s}'", .{ operand_ty.fmt(ip), @tagName(src_info.flags.address_space) });
                try sema.errNote(sema.block.nodeOffset(.zero), msg, "'{f}' has address space '{s}'", .{ dest_ty.fmt(ip), @tagName(dest_info.flags.address_space) });
                try sema.errNote(sema.block.nodeOffset(.zero), msg, "use @addrSpaceCast to cast pointer address space", .{});
                break :msg msg;
            });
        }
    }

    if (!flags.const_cast) {
        if (src_info.flags.is_const and !dest_info.flags.is_const) {
            return sema.failWithOwnedErrorMsg(sema.block, msg: {
                const msg = try sema.errMsg(sema.block.nodeOffset(.zero), "{s} discards const qualifier", .{operation});
                errdefer msg.destroy(sema.gpa);
                try sema.errNote(sema.block.nodeOffset(.zero), msg, "use @constCast to discard const qualifier", .{});
                break :msg msg;
            });
        }
    }

    if (!flags.volatile_cast) {
        if (src_info.flags.is_volatile and !dest_info.flags.is_volatile) {
            return sema.failWithOwnedErrorMsg(sema.block, msg: {
                const msg = try sema.errMsg(sema.block.nodeOffset(.zero), "{s} discards volatile qualifier", .{operation});
                errdefer msg.destroy(sema.gpa);
                try sema.errNote(sema.block.nodeOffset(.zero), msg, "use @volatileCast to discard volatile qualifier", .{});
                break :msg msg;
            });
        }
    }

    if (operand.isUndef(ip)) {
        if (!dest_ty.ptrAllowsZero(ip)) return sema.failWithUseOfUndef();
        return .fromIndex(try ip.get(.{ .undef = dest_ty.index }));
    }
    if (operand.isNull(ip)) {
        if (!dest_ty.ptrAllowsZero(ip)) {
            return sema.fail(sema.block, sema.block.nodeOffset(.zero), "null pointer casted to type '{f}'", .{dest_ty.fmt(ip)});
        }
        if (dest_ty.zigTypeTag(ip) == .optional) {
            return .fromIndex(try ip.internOpt(.{ .ty = dest_ty.index, .val = .none }));
        }
        return .fromIndex(try ip.internPtr(.{ .ty = dest_ty.index, .base_addr = .int, .byte_offset = 0 }));
    }

    const ptr_val: Value = switch (src_info.flags.size) {
        .slice => .{ .index = ip.indexToKey(operand.index).slice.ptr },
        .one, .many, .c => operand,
    };

    if (dest_align.compare(.gt, src_align)) {
        if (ptr_val.getUnsignedInt(ip)) |addr| {
            if (!dest_align.check(addr)) {
                return sema.fail(sema.block, sema.block.nodeOffset(.zero), "pointer address 0x{X} is not aligned to {d} bytes", .{ addr, dest_align.toByteUnits().? });
            }
        }
    }

    if (dest_info.flags.size == .slice) {
        const len_val: Value = switch (dest_slice_len.?) {
            .undef => try sema.undefValue(.fromIndex(.usize_type)),
            .constant => |n| try sema.intValue_u64(.fromIndex(.usize_type), n),
        };
        const dest_is_optional = dest_ty.zigTypeTag(ip) == .optional;
        const slice_ty = if (dest_is_optional) dest_ty.optionalChild(ip) else dest_ty;
        const slice_val = try ip.get(.{ .slice = .{
            .ty = slice_ty.index,
            .ptr = try ip.getCoerced(ptr_val.index, try ip.slicePtrType(slice_ty.index)),
            .len = len_val.index,
        } });
        if (!dest_is_optional) return .fromIndex(slice_val);
        return .fromIndex(try ip.internOpt(.{ .ty = dest_ty.index, .val = slice_val }));
    } else {
        return .fromIndex(try ip.getCoerced(ptr_val.index, dest_ty.index));
    }
}

fn evalBitSizeOf(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@backingInt(inst) < sema.zir.instructions.len);
    const un_node = sema.zir.instructions.items(.data)[@backingInt(inst)].un_node;
    const ty = try sema.resolveDestType(un_node.operand);
    const operand_ty = Type.fromIndex(ty);
    if (!operand_ty.hasBitRepresentation(sema.intern_pool) and
        operand_ty.zigTypeTag(sema.intern_pool) != .error_set and
        operand_ty.zigTypeTag(sema.intern_pool) != .@"enum")
    {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "no bit size available for type '{f}'", .{operand_ty.fmt(sema.intern_pool)});
    }
    try sema.ensureLayoutResolved(ty);
    const bits = operand_ty.bitSize(sema.intern_pool);
    const idx = try sema.intern_pool.internInt(.{
        .ty = .comptime_int_type,
        .storage = .{ .u64 = bits },
    });
    return .{ .index = idx };
}

fn evalBitCount(
    sema: *Sema,
    inst: Zir.Inst.Index,
    comptime comptimeOp: fn (Value, Type, *const InternPool) u64,
) Error!?Value {
    assert(@backingInt(inst) < sema.zir.instructions.len);
    const ip = sema.intern_pool;
    const un_node = sema.zir.instructions.items(.data)[@backingInt(inst)].un_node;
    const operand = try sema.resolveInst(un_node.operand);
    const operand_ty = operand.typeOf(ip);
    _ = try sema.checkIntOrVector(operand);
    const bits = operand_ty.intInfo(ip).bits;

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
                    return sema.fail(sema.block, sema.block.nodeOffset(.zero), "expected vector of integers; found vector of '{f}'", .{elem_ty.fmt(ip)});
                },
            }
        },
        else => {
            return sema.fail(sema.block, sema.block.nodeOffset(.zero), "expected integer or vector, found '{f}'", .{operand_ty.fmt(ip)});
        },
    }
}

fn evalByteSwap(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    const un_node = sema.zir.instructions.items(.data)[@backingInt(inst)].un_node;
    const operand = try sema.resolveInst(un_node.operand);
    const operand_ty = operand.typeOf(ip);
    const scalar_ty = try sema.checkIntOrVector(operand);
    const bits = scalar_ty.intInfo(ip).bits;
    if (bits % 8 != 0) {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "@byteSwap requires the number of bits to be evenly divisible by 8, but '{f}' has {d} bits", .{ scalar_ty.fmt(ip), bits });
    }
    return try arith.byteSwap(sema, operand, operand_ty);
}

fn evalBitReverse(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    const un_node = sema.zir.instructions.items(.data)[@backingInt(inst)].un_node;
    const operand = try sema.resolveInst(un_node.operand);
    const operand_ty = operand.typeOf(ip);
    _ = try sema.checkIntOrVector(operand);
    return try arith.bitReverse(sema, operand, operand_ty);
}

fn nextSyntheticAddress(sema: *Sema, align_bytes: u64, size: u64) u64 {
    const aligned = std.mem.alignForward(u64, sema.comptime_address_cursor, align_bytes);
    sema.comptime_address_cursor = aligned + @max(size, 1);
    return aligned;
}

fn evalIntFromPtr(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@backingInt(inst) < sema.zir.instructions.len);

    const un_node = sema.zir.instructions.items(.data)[@backingInt(inst)].un_node;
    const ptr = try sema.resolveInst(un_node.operand);
    const key = sema.intern_pool.indexToKey(ptr.index);
    if (key != .ptr) {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "@intFromPtr: operand is not a pointer", .{});
    }
    const p = key.ptr;
    const ip = sema.intern_pool;
    const ptr_ty = ip.indexToKey(p.ty).ptr_type;
    try sema.ensureLayoutResolved(ptr_ty.child);
    const natural: InternPool.Alignment = Type.fromIndex(ptr_ty.child).abiAlignment(ip);
    const align_bytes: u64 = ptr_ty.flags.alignment.toByteUnits() orelse natural.toByteUnits().?;
    const size: u64 = Type.fromIndex(ptr_ty.child).abiSize(ip);

    const base: u64 = switch (p.base_addr) {
        .comptime_alloc => |i| blk: {
            const slot = &sema.comptime_allocs.items[@backingInt(i)];
            break :blk slot.address orelse addr: {
                const aligned = sema.nextSyntheticAddress(align_bytes, size);
                slot.address = aligned;
                break :addr aligned;
            };
        },
        .nav, .uav => sema.synthetic_addresses.get(ptr.index) orelse addr: {
            const aligned = sema.nextSyntheticAddress(align_bytes, size);
            try sema.synthetic_addresses.put(sema.gpa, ptr.index, aligned);
            break :addr aligned;
        },
        .int => 0,
        .field, .arr_elem, .opt_payload, .eu_payload, .comptime_field => {
            return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "@intFromPtr: address of an aggregate element is not supported", .{});
        },
    };

    const idx = try ip.internInt(.{
        .ty = .usize_type,
        .storage = .{ .u64 = base + p.byte_offset },
    });
    return .{ .index = idx };
}

fn evalAlloc(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@backingInt(inst) < sema.zir.instructions.len);

    const un_node = sema.zir.instructions.items(.data)[@backingInt(inst)].un_node;
    assert(un_node.operand != .none);

    const child_ty = try sema.resolveDestType(un_node.operand);
    const undef_idx = try sema.intern_pool.get(.{ .undef = child_ty });
    return try sema.pushComptimeAlloc(child_ty, .{ .index = undef_idx }, false, .none);
}

fn evalRetPtr(sema: *Sema) Error!?Value {
    const ret_ty = sema.fn_ret_ty;
    const undef_idx = try sema.intern_pool.get(.{ .undef = ret_ty });
    return try sema.pushComptimeAlloc(ret_ty, .{ .index = undef_idx }, false, .none);
}

fn freezeBacking(sema: *Sema, ptr: InternPool.Key.Ptr) void {
    const ip = sema.intern_pool;
    switch (ptr.base_addr) {
        .comptime_alloc => |idx| sema.comptime_allocs.items[@backingInt(idx)].is_const = true,
        .field, .arr_elem => |f| sema.freezeBacking(ip.indexToKey(f.base).ptr),
        .opt_payload, .eu_payload => |base| sema.freezeBacking(ip.indexToKey(base).ptr),
        .nav, .uav, .comptime_field, .int => {},
    }
}

fn evalMakePtrConst(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@backingInt(inst) < sema.zir.instructions.len);

    const un_node = sema.zir.instructions.items(.data)[@backingInt(inst)].un_node;
    const ptr = try sema.resolveInst(un_node.operand);
    const ip = sema.intern_pool;
    const p = ip.indexToKey(ptr.index).ptr;
    const old = ip.indexToKey(p.ty).ptr_type;
    if (p.base_addr == .comptime_alloc) try sema.fillComptimeAllocFields(p, old.child);
    sema.freezeBacking(p);

    var flags = old.flags;
    flags.is_const = true;
    const const_ty = try ip.internPtrType(.{ .child = old.child, .sentinel = old.sentinel, .flags = flags });

    // A frozen comptime alloc whose value does not reference comptime-mutable memory is promoted to an
    // anonymous decl (uav), so the const pointer names a stable, self-contained value -- mirrors
    // zirMakePtrConst. A value that can still mutate comptime-var state keeps its comptime_alloc base.
    if (p.base_addr == .comptime_alloc and p.byte_offset == 0) {
        const alloc = try sema.lookupComptimeAlloc(p);
        const alloc_val = try alloc.val.intern(ip, sema.arena);
        if (!alloc_val.canMutateComptimeVarState(ip))
            return .{ .index = try sema.uavPtr(const_ty, alloc_val.index) };
    }

    if (old.flags.is_const) return ptr;
    const const_ptr = try ip.internPtr(.{ .ty = const_ty, .base_addr = p.base_addr, .byte_offset = p.byte_offset });
    return .{ .index = const_ptr };
}

// A comptime field is addressed by a standalone comptime_field pointer, so its element store is a no-op;
// fill comptime fields from their type defaults when the comptime-known alloc is finalized, mirroring the
// compiler resolving the comptime fields of such an alloc.
fn fillComptimeAllocFields(sema: *Sema, alloc_ptr: InternPool.Key.Ptr, agg_ty: InternPool.Index) Error!void {
    const ip = sema.intern_pool;
    const key = ip.indexToKey(agg_ty);
    const count: u32 = switch (key) {
        .tuple_type => |t| @intCast(t.types.len),
        .struct_type => count: {
            try sema.ensureLayoutResolved(agg_ty);
            break :count try sema.structFieldCount(agg_ty);
        },
        else => return,
    };
    const ty: Type = .fromIndex(agg_ty);
    var i: u32 = 0;
    while (i < count) : (i += 1) {
        if (!ty.structFieldIsComptime(i, ip)) continue;
        const default = (try ty.structFieldValueComptime(sema, i)).?;
        const alloc = try sema.lookupComptimeAlloc(alloc_ptr);
        const cur = try alloc.val.intern(ip, sema.arena);
        alloc.val = .{ .interned = (try sema.setAggregateElement(cur, agg_ty, i, default)).index };
    }
}

pub fn pushComptimeAlloc(
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
        .val = .{ .interned = val.index },
        .is_const = is_const,
        .alignment = alignment,
    });

    const ptr_ty = try ip.internPtrType(.{
        .child = child_ty,
        .flags = .{ .size = .one, .is_const = is_const, .alignment = alignment },
    });
    const ptr_idx = try ip.internPtr(.{
        .ty = ptr_ty,
        .base_addr = .{ .comptime_alloc = @fromBackingInt(@intCast(alloc_index)) },
        .byte_offset = 0,
    });
    return .{ .index = ptr_idx };
}

fn evalAllocInferred(sema: *Sema, comptime is_const: bool) Error!?Value {
    const placeholder = try sema.intern_pool.get(.{ .undef = .generic_poison_type });
    return try sema.pushComptimeAlloc(.generic_poison_type, .{ .index = placeholder }, is_const, .none);
}

fn evalStoreToInferredPtr(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    const pl_node = sema.zir.instructions.items(.data)[@backingInt(inst)].pl_node;
    const bin = sema.zir.extraData(Zir.Inst.Bin, pl_node.payload_index).data;
    const ptr = try sema.resolveInst(bin.lhs);
    const operand = try sema.resolveInst(bin.rhs);

    const p = ip.indexToKey(ptr.index).ptr;
    const slot = try sema.lookupComptimeAlloc(p);
    slot.val = .{ .interned = operand.index };

    const ptr_ty = try ip.internPtrType(.{
        .child = operand.typeOf(ip).toIndex(),
        .flags = .{ .size = .one, .is_const = slot.is_const },
    });
    const typed_ptr = try ip.internPtr(.{ .ty = ptr_ty, .base_addr = p.base_addr, .byte_offset = 0 });
    try sema.inst_map.put(sema.gpa, bin.lhs.toIndex().?, .{ .index = typed_ptr });
    return .{ .index = .void_value };
}

fn evalResolveInferredAlloc(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const un_node = sema.zir.instructions.items(.data)[@backingInt(inst)].un_node;
    return try sema.resolveInst(un_node.operand);
}

fn evalDeref(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@backingInt(inst) < sema.zir.instructions.len);
    const un_node = sema.zir.instructions.items(.data)[@backingInt(inst)].un_node;
    assert(un_node.operand != .none);
    const operand = try sema.resolveInst(un_node.operand);
    try sema.validateDeref(operand);
    return try sema.loadValue(operand);
}

fn evalRefDeref(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@backingInt(inst) < sema.zir.instructions.len);
    const un_node = sema.zir.instructions.items(.data)[@backingInt(inst)].un_node;
    assert(un_node.operand != .none);
    const ip = sema.intern_pool;
    const operand = try sema.resolveInst(un_node.operand);
    try sema.validateDeref(operand);
    const ptr_type = ip.indexToKey(operand.typeOf(ip).toIndex()).ptr_type;
    switch (ptr_type.flags.size) {
        .one => return operand,
        .c => {
            var flags = ptr_type.flags;
            flags.size = .one;
            flags.is_allowzero = false;
            const single_ptr_ty = try ip.internPtrType(.{ .child = ptr_type.child, .sentinel = ptr_type.sentinel, .flags = flags });
            return try sema.coerceValueToType(operand, single_ptr_ty);
        },
        .many, .slice => unreachable,
    }
}

fn validateDeref(sema: *Sema, operand: Value) Error!void {
    const ip = sema.intern_pool;
    const operand_ty = operand.typeOf(ip);
    const ty_key = ip.indexToKey(operand_ty.toIndex());
    if (ty_key != .ptr_type) {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "cannot dereference non-pointer type '{f}'", .{operand_ty.fmt(ip)});
    }
    switch (ty_key.ptr_type.flags.size) {
        .one, .c => {},
        .many => {
            return sema.fail(sema.block, sema.block.nodeOffset(.zero), "index syntax required for unknown-length pointer type '{f}'", .{operand_ty.fmt(ip)});
        },
        .slice => {
            return sema.fail(sema.block, sema.block.nodeOffset(.zero), "index syntax required for slice type '{f}'", .{operand_ty.fmt(ip)});
        },
    }
    if (ip.indexToKey(operand.index) == .undef) {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "cannot dereference undefined value", .{});
    }
}

fn evalStoreNode(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const bin = sema.binData(inst);
    assert(bin.lhs != .none);
    assert(bin.rhs != .none);

    const ip = sema.intern_pool;
    const ptr_value = try sema.resolveInst(bin.lhs);
    const ptr_key = ip.indexToKey(ptr_value.index);
    if (ptr_key != .ptr) {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "store: lhs is not a pointer", .{});
    }

    const ptr_ty_key = ip.indexToKey(ptr_key.ptr.ty);
    assert(ptr_ty_key == .ptr_type);
    if (ptr_ty_key.ptr_type.flags.is_const) {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "cannot assign to constant", .{});
    }

    const rhs_value = try sema.resolveInst(bin.rhs);
    // Coerce to the pointer's element type and store through the comptime pointer engine, which
    // navigates the pointer (including byte offsets into extern aggregates) to its sub-location.
    const coerced = try sema.coerceValueToType(rhs_value, ptr_ty_key.ptr_type.child);
    try sema.storePtrVal(ptr_value, coerced);
    return .{ .index = .void_value };
}

fn evalLoad(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@backingInt(inst) < sema.zir.instructions.len);

    const un_node = sema.zir.instructions.items(.data)[@backingInt(inst)].un_node;
    assert(un_node.operand != .none);

    const ptr_value = try sema.resolveInst(un_node.operand);
    return try sema.loadValue(ptr_value);
}

fn loadValue(sema: *Sema, ptr: Value) Error!Value {
    const ip = sema.intern_pool;
    if (ip.indexToKey(ptr.index) != .ptr) {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "internal error: load through non-pointer value", .{});
    }
    const src = sema.block.nodeOffset(.zero);
    const ptr_ty = ptr.typeOf(ip);
    // Where the compiler emits an AIR load of runtime memory, the runtime layer retargets the pointer
    // onto a copy of the mutable global's value; the reused comptime load then navigates it and the
    // loaded value is marked runtime. Its error results flow through the same arms as a comptime load.
    var is_runtime = false;
    var result = try comptime_ptr_access.loadComptimePtr(sema, ptr);
    if (result == .runtime_load) {
        if (try runtime.retargetLoad(sema, ptr)) |rt_ptr| {
            result = try comptime_ptr_access.loadComptimePtr(sema, rt_ptr);
            is_runtime = true;
        }
    }
    switch (result) {
        .success => |mv| {
            const val = try mv.intern(ip, sema.arena);
            return if (is_runtime) .{ .index = val.index, .is_comptime = false } else val;
        },
        .runtime_load => return sema.fail(sema.block, src, "unable to evaluate comptime expression: load requires runtime memory", .{}),
        .undef => return sema.failWithUseOfUndef(),
        .err_payload => |err_name| return sema.fail(sema.block, src, "attempt to unwrap error: {f}", .{err_name.fmt(ip)}),
        .null_payload => return sema.fail(sema.block, src, "attempt to use null value", .{}),
        .inactive_union_field => return sema.fail(sema.block, src, "access of inactive union field", .{}),
        .needed_well_defined => |ty| return sema.fail(sema.block, src, "comptime dereference requires '{f}' to have a well-defined layout", .{ty.fmt(ip)}),
        .out_of_bounds => |ty| return sema.fail(sema.block, src, "dereference of '{f}' exceeds bounds of containing decl of type '{f}'", .{ ptr_ty.fmt(ip), ty.fmt(ip) }),
        .exceeds_host_size => return sema.fail(sema.block, src, "bit-pointer target exceeds host size", .{}),
    }
}

fn loadUnionField(sema: *Sema, union_val: InternPool.Index, index: u32) Error!Value {
    const ip = sema.intern_pool;
    const uv = ip.indexToKey(union_val).un;
    const tag_ty = ip.indexToKey(uv.tag).enum_tag.ty;
    const active_index = (try sema.enumTagFieldIndex(tag_ty, .{ .index = uv.tag })).?;
    if (active_index == index) return .{ .index = uv.val };
    const accessed = (try sema.unionFieldNameAt(uv.ty, index)) orelse unreachable;
    const active_name = (try sema.unionFieldNameAt(uv.ty, active_index)) orelse unreachable;
    return sema.fail(sema.block, sema.block.nodeOffset(.zero), "access of union field '{s}' while field '{s}' is active", .{
        ip.stringSlice(accessed), ip.stringSlice(active_name),
    });
}

fn lookupComptimeAlloc(sema: *Sema, ptr: InternPool.Key.Ptr) Error!*ComptimeAlloc {
    if (ptr.byte_offset != 0) {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "comptime_alloc lookup: pointer offset not yet supported", .{});
    }
    const idx: u32 = @backingInt(ptr.base_addr.comptime_alloc);
    assert(idx < sema.comptime_allocs.items.len);
    return &sema.comptime_allocs.items[idx];
}

pub const castMemory = reinterpret.castMemory;
pub const spliceMemory = reinterpret.spliceMemory;

pub const InMemoryCoercionResult = union(enum) {
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

    fn report(res: *const InMemoryCoercionResult, sema: *Sema, src: LazySrcLoc, msg: *ErrorMsg) Error!void {
        const ip = sema.intern_pool;
        var cur = res;
        while (true) switch (cur.*) {
            .ok => unreachable,
            .no_match => break,
            .int_not_coercible => |int| {
                try sema.errNote(src, msg, "{s} {d}-bit int cannot represent all possible {s} {d}-bit values", .{
                    @tagName(int.wanted_signedness), int.wanted_bits, @tagName(int.actual_signedness), int.actual_bits,
                });
                break;
            },
            .comptime_int_not_coercible => |int| {
                try sema.errNote(src, msg, "type '{f}' cannot represent value '{f}'", .{ int.wanted.fmt(ip), render_value.fmt(int.actual, ip) });
                break;
            },
            .error_union_payload => |pair| {
                try noteTwoTypes(sema, src, msg, "error union payload '", pair.actual, "' cannot cast into error union payload '", pair.wanted);
                cur = pair.child;
            },
            .array_len => |lens| {
                try sema.errNote(src, msg, "array of length {d} cannot cast into an array of length {d}", .{ lens.actual, lens.wanted });
                break;
            },
            .array_sentinel => |sentinel| {
                try noteSentinel(sema, src, msg, "source array cannot be guaranteed to maintain '", "destination array requires '", "array sentinel '", "' cannot cast into array sentinel '", sentinel);
                break;
            },
            .array_elem => |pair| {
                try noteTwoTypes(sema, src, msg, "array element type '", pair.actual, "' cannot cast into array element type '", pair.wanted);
                cur = pair.child;
            },
            .vector_len => |lens| {
                try sema.errNote(src, msg, "vector of length {d} cannot cast into a vector of length {d}", .{ lens.actual, lens.wanted });
                break;
            },
            .vector_elem => |pair| {
                try noteTwoTypes(sema, src, msg, "vector element type '", pair.actual, "' cannot cast into vector element type '", pair.wanted);
                cur = pair.child;
            },
            .optional_shape => |pair| {
                try noteTwoTypes(sema, src, msg, "optional type child '", pair.actual.optionalChild(ip), "' cannot cast into optional type child '", pair.wanted.optionalChild(ip));
                break;
            },
            .optional_child => |pair| {
                try noteTwoTypes(sema, src, msg, "optional type child '", pair.actual, "' cannot cast into optional type child '", pair.wanted);
                cur = pair.child;
            },
            .from_anyerror => {
                try sema.errNote(src, msg, "global error set cannot cast into a smaller set", .{});
                break;
            },
            .missing_error => |missing_errors| {
                for (missing_errors) |err| try sema.errNote(src, msg, "'error.{s}' not a member of destination error set", .{ip.stringSlice(err)});
                break;
            },
            .fn_var_args => |wanted_var_args| {
                if (wanted_var_args) {
                    try sema.errNote(src, msg, "non-variadic function cannot cast into a variadic function", .{});
                } else {
                    try sema.errNote(src, msg, "variadic function cannot cast into a non-variadic function", .{});
                }
                break;
            },
            .fn_generic => |wanted_generic| {
                if (wanted_generic) {
                    try sema.errNote(src, msg, "non-generic function cannot cast into a generic function", .{});
                } else {
                    try sema.errNote(src, msg, "generic function cannot cast into a non-generic function", .{});
                }
                break;
            },
            .fn_param_count => |lens| {
                try sema.errNote(src, msg, "function with {d} parameters cannot cast into a function with {d} parameters", .{ lens.actual, lens.wanted });
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
                    try sema.errNote(src, msg, "regular parameter {d} cannot cast into a noalias parameter", .{index});
                } else {
                    try sema.errNote(src, msg, "noalias parameter {d} cannot cast into a regular parameter", .{index});
                }
                break;
            },
            .fn_param_comptime => |param| {
                if (param.wanted) {
                    try sema.errNote(src, msg, "non-comptime parameter {d} cannot cast into a comptime parameter", .{param.index});
                } else {
                    try sema.errNote(src, msg, "comptime parameter {d} cannot cast into a non-comptime parameter", .{param.index});
                }
                break;
            },
            .fn_param => |param| {
                try sema.errNote(src, msg, "parameter {d} '{f}' cannot cast into '{f}'", .{ param.index, param.actual.fmt(ip), param.wanted.fmt(ip) });
                cur = param.child;
            },
            .fn_cc => |cc| {
                try sema.errNote(src, msg, "calling convention '{s}' cannot cast into calling convention '{s}'", .{ @tagName(cc.actual), @tagName(cc.wanted) });
                break;
            },
            .fn_return_type => |pair| {
                try noteTwoTypes(sema, src, msg, "return type '", pair.actual, "' cannot cast into return type '", pair.wanted);
                cur = pair.child;
            },
            .ptr_child => |pair| {
                try noteTwoTypes(sema, src, msg, "pointer type child '", pair.actual, "' cannot cast into pointer type child '", pair.wanted);
                cur = pair.child;
            },
            .ptr_addrspace => |addr_space| {
                try sema.errNote(src, msg, "address space '{s}' cannot cast into address space '{s}'", .{ @tagName(addr_space.actual), @tagName(addr_space.wanted) });
                break;
            },
            .ptr_sentinel => |sentinel| {
                try noteSentinel(sema, src, msg, "", "destination pointer requires '", "pointer sentinel '", "' cannot cast into pointer sentinel '", sentinel);
                break;
            },
            .ptr_size => |size| {
                try sema.errNote(src, msg, "a {s} cannot cast into a {s}", .{ pointerSizeString(size.actual), pointerSizeString(size.wanted) });
                break;
            },
            .ptr_const => |pair| {
                if (pair.actual.isConstPtr(ip) and !pair.wanted.isConstPtr(ip)) {
                    try sema.errNote(src, msg, "cast discards const qualifier", .{});
                } else {
                    try noteTwoTypes(sema, src, msg, "mutable '", pair.wanted, "' would allow illegal const pointers stored to type '", pair.actual);
                }
                break;
            },
            .ptr_volatile => |pair| {
                if (pair.actual.isVolatilePtr(ip) and !pair.wanted.isVolatilePtr(ip)) {
                    try sema.errNote(src, msg, "cast discards volatile qualifier", .{});
                } else {
                    try noteTwoTypes(sema, src, msg, "mutable '", pair.wanted, "' would allow illegal volatile pointers stored to type '", pair.actual);
                }
                break;
            },
            .ptr_allowzero => |pair| {
                const wanted_allow_zero = pair.wanted.ptrAllowsZero(ip);
                const actual_allow_zero = pair.actual.ptrAllowsZero(ip);
                if (actual_allow_zero and !wanted_allow_zero) {
                    try noteTwoTypes(sema, src, msg, "'", pair.actual, "' could have null values which are illegal in type '", pair.wanted);
                } else {
                    try noteTwoTypes(sema, src, msg, "mutable '", pair.wanted, "' would allow illegal null values stored to type '", pair.actual);
                }
                break;
            },
            .ptr_bit_range => |bit_range| {
                if (bit_range.actual_host != bit_range.wanted_host)
                    try sema.errNote(src, msg, "pointer host size '{d}' cannot cast into pointer host size '{d}'", .{ bit_range.actual_host, bit_range.wanted_host });
                if (bit_range.actual_offset != bit_range.wanted_offset)
                    try sema.errNote(src, msg, "pointer bit offset '{d}' cannot cast into pointer bit offset '{d}'", .{ bit_range.actual_offset, bit_range.wanted_offset });
                break;
            },
            .ptr_alignment => |pair| {
                try sema.errNote(src, msg, "pointer alignment '{d}' cannot cast into pointer alignment '{d}'", .{ pair.actual.toByteUnits() orelse 0, pair.wanted.toByteUnits() orelse 0 });
                break;
            },
            .double_ptr_to_anyopaque => |pair| {
                try noteTwoTypes(sema, src, msg, "cannot implicitly cast double pointer '", pair.actual, "' to anyopaque pointer '", pair.wanted);
                break;
            },
            .slice_to_anyopaque => |pair| {
                try noteTwoTypes(sema, src, msg, "cannot implicitly cast slice '", pair.actual, "' to anyopaque pointer '", pair.wanted);
                try sema.errNote(src, msg, "consider using '.ptr'", .{});
                break;
            },
        };
    }
};

fn noteTwoTypes(sema: *Sema, src: LazySrcLoc, msg: *ErrorMsg, pre: []const u8, a: Type, mid: []const u8, b: Type) Error!void {
    const ip = sema.intern_pool;
    try sema.errNote(src, msg, "{s}{f}{s}{f}'", .{ pre, a.fmt(ip), mid, b.fmt(ip) });
}

fn noteSentinel(sema: *Sema, src: LazySrcLoc, msg: *ErrorMsg, missing_actual: []const u8, missing_wanted: []const u8, both_pre: []const u8, both_mid: []const u8, sentinel: InMemoryCoercionResult.Sentinel) Error!void {
    const ip = sema.intern_pool;
    if (sentinel.wanted.index == .unreachable_value) {
        try sema.errNote(src, msg, "{s}{f}'", .{ missing_actual, render_value.fmt(sentinel.actual, ip) });
    } else if (sentinel.actual.index == .unreachable_value) {
        try sema.errNote(src, msg, "{s}{f}'", .{ missing_wanted, render_value.fmt(sentinel.wanted, ip) });
    } else {
        try sema.errNote(src, msg, "{s}{f}{s}{f}'", .{ both_pre, render_value.fmt(sentinel.actual, ip), both_mid, render_value.fmt(sentinel.wanted, ip) });
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

pub fn coerceInMemoryAllowed(sema: *Sema, dest_ty: Type, src_ty: Type, dest_is_mut: bool, src_val: ?Value) Error!InMemoryCoercionResult {
    const ip = sema.intern_pool;
    if (dest_ty.index == src_ty.index) return .{ .ok = .same_type };

    const dest_tag = dest_ty.zigTypeTag(ip);
    const src_tag = src_ty.zigTypeTag(ip);

    if (dest_tag == .int and src_tag == .int) {
        const dest_info = dest_ty.intInfo(ip);
        const src_info = src_ty.intInfo(ip);
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

    if (dest_tag == .int and src_tag == .comptime_int) {
        if (src_val) |val| {
            if (!sema.intFitsInType(val, dest_ty)) {
                return .{ .comptime_int_not_coercible = .{ .wanted = dest_ty, .actual = val } };
            }
        }
    }

    if (dest_tag == .float and src_tag == .float) {
        if (dest_ty.floatBits() == src_ty.floatBits()) return .{ .ok = .bit_cast };
    }

    if (dest_ty.isPtrAtRuntime(ip) and src_ty.isPtrAtRuntime(ip)) {
        return try sema.coerceInMemoryAllowedPtrs(dest_ty, src_ty, dest_is_mut);
    }

    if (dest_ty.isSlice(ip) and src_ty.isSlice(ip)) {
        return try sema.coerceInMemoryAllowedPtrs(dest_ty, src_ty, dest_is_mut);
    }

    if (dest_tag == .@"fn" and src_tag == .@"fn") {
        return try sema.coerceInMemoryAllowedFns(dest_ty, src_ty, dest_is_mut);
    }

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

fn intFitsInType(sema: *Sema, val: Value, ty: Type) bool {
    const info = ty.intInfo(sema.intern_pool);
    var space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
    const big = sema.intern_pool.indexToKey(val.index).int.storage.toBigInt(&space);
    return big.fitsInTwosComp(info.signedness, info.bits);
}

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
        try sema.ensureLayoutResolved(src_info.child);
        try sema.ensureLayoutResolved(dest_info.child);
        const src_align = if (src_info.flags.alignment == .none) src_child.abiAlignment(ip) else src_info.flags.alignment;
        const dest_align = if (dest_info.flags.alignment == .none) dest_child.abiAlignment(ip) else dest_info.flags.alignment;
        if (dest_align.compare(if (dest_is_mut) .neq else .gt, src_align)) {
            return .{ .ptr_alignment = .{ .actual = src_align, .wanted = dest_align } };
        }
    }

    return .{ .ok = .ptr_cast };
}

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

pub fn coerceValueToType(sema: *Sema, value: Value, dest_ty: InternPool.Index) Error!Value {
    return sema.coerceExtra(value, dest_ty, true);
}

fn checkPtrAttributes(sema: *Sema, dest_ty: Type, inst_ty: Type, in_memory_result: *InMemoryCoercionResult) bool {
    const ip = sema.intern_pool;
    const dest_info = dest_ty.ptrInfo(ip);
    const inst_info = inst_ty.ptrInfo(ip);
    const inst_child: Type = .fromIndex(inst_info.child);
    const len0 = (inst_child.zigTypeTag(ip) == .array and (inst_child.arrayLenIncludingSentinel(ip) == 0 or
        (inst_child.arrayLen(ip) == 0 and dest_info.sentinel == .none and dest_info.flags.size != .c and dest_info.flags.size != .many))) or
        (inst_child.isTuple(ip) and ip.indexToKey(inst_child.index).tuple_type.types.len == 0);

    const ok_const = (!inst_info.flags.is_const or dest_info.flags.is_const) or len0;
    const ok_volatile = !inst_info.flags.is_volatile or dest_info.flags.is_volatile;
    if (!ok_const) {
        in_memory_result.* = .{ .ptr_const = .{ .actual = inst_ty, .wanted = dest_ty } };
        return false;
    }
    if (!ok_volatile) {
        in_memory_result.* = .{ .ptr_volatile = .{ .actual = inst_ty, .wanted = dest_ty } };
        return false;
    }

    if (dest_info.flags.address_space != inst_info.flags.address_space) {
        in_memory_result.* = .{ .ptr_addrspace = .{ .actual = inst_info.flags.address_space, .wanted = dest_info.flags.address_space } };
        return false;
    }

    if (inst_info.packed_offset.host_size != dest_info.packed_offset.host_size or
        inst_info.packed_offset.bit_offset != dest_info.packed_offset.bit_offset)
    {
        in_memory_result.* = .{ .ptr_bit_range = .{
            .actual_host = inst_info.packed_offset.host_size,
            .wanted_host = dest_info.packed_offset.host_size,
            .actual_offset = inst_info.packed_offset.bit_offset,
            .wanted_offset = dest_info.packed_offset.bit_offset,
        } };
        return false;
    }

    if (inst_info.flags.alignment == .none and dest_info.flags.alignment == .none) return true;
    if (len0) return true;

    const inst_align = if (inst_info.flags.alignment != .none)
        inst_info.flags.alignment
    else
        inst_child.abiAlignment(ip);

    const dest_align = if (dest_info.flags.alignment != .none)
        dest_info.flags.alignment
    else
        Type.fromIndex(dest_info.child).abiAlignment(ip);

    if (dest_align.compare(.gt, inst_align)) {
        in_memory_result.* = .{ .ptr_alignment = .{ .actual = inst_align, .wanted = dest_align } };
        return false;
    }
    return true;
}

fn coerceExtra(
    sema: *Sema,
    value: Value,
    dest_ty: InternPool.Index,
    report_err: bool,
) Error!Value {
    assert(dest_ty != .none);
    assert(value.index != .none);

    const ip = sema.intern_pool;
    const value_type = Value.typeOf(value, ip);
    if (value_type.index == dest_ty) return value;

    // The interpreter produces `undefined` as the untyped literal (`undefined_type`),
    // so coerce the bare literal to any destination here.
    // A concretely-typed undefined value instead flows through the per-arm checks below (e.g. a `[*c]const T`
    // undefined still fails a const-discarding pointer coercion).
    if (value_type.index == .undefined_type) return .{ .index = try ip.get(.{ .undef = dest_ty }) };

    // In-memory-coercible types re-type the value directly (e.g. `*[n:s]T` -> `*[n]T`, error-set
    // widening, distinct-but-layout-identical types). The REPL only ever holds comptime values, so
    // the compiler's runtime bit_cast/ptr_cast branch collapses to `getCoerced`.
    switch (try sema.coerceInMemoryAllowed(.fromIndex(dest_ty), value_type, false, value)) {
        .ok => return .{ .index = try ip.getCoerced(value.index, dest_ty) },
        else => {},
    }

    switch (ip.indexToKey(dest_ty)) {
        .int_type => if (try sema.coerceToFixedWidthInt(value, dest_ty)) |c| return c,
        .simple_type => |s| switch (s) {
            .usize, .isize, .c_char, .c_short, .c_ushort, .c_int, .c_uint, .c_long, .c_ulong, .c_longlong, .c_ulonglong => {
                if (try sema.coerceToFixedWidthInt(value, dest_ty)) |c| return c;
            },
            .f16, .f32, .f64, .f80, .f128, .comptime_float, .c_longdouble => {
                if (try sema.coerceToFloat(value, dest_ty)) |c| return c;
            },
            .comptime_int => if (ip.indexToKey(value.index) == .int) {
                var space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
                const big = ip.indexToKey(value.index).int.storage.toBigInt(&space);
                return .{ .index = try ip.internIntValue(.comptime_int_type, big) };
            },
            .anyerror => return try sema.coerceToErrorSet(value, dest_ty),
            else => {},
        },
        .error_set_type => return try sema.coerceToErrorSet(value, dest_ty),
        .error_union_type => return try sema.coerceToErrorUnion(value, dest_ty),
        .opt_type => return try sema.coerceToOptional(value, dest_ty),
        .ptr_type => |p| {
            // `*T`/`[*]T` -> `*anyopaque`/`[*]anyopaque`: coerce the pointer, not the pointee
            // (the compiler's to_anyopaque -> coerceCompatiblePtrs). Reject a double-pointer source;
            // a slice destination falls through to the slice coercion below.
            if (p.child == .anyopaque_type and p.flags.size != .slice) {
                const val_ty = Value.typeOf(value, ip);
                if (val_ty.zigTypeTag(ip) == .pointer and !val_ty.isSlice(ip)) {
                    const src_child = ip.indexToKey(val_ty.index).ptr_type.child;
                    if (ip.indexToKey(src_child) != .ptr_type and !Type.fromIndex(src_child).isPtrLikeOptional(ip))
                        return .{ .index = try ip.getCoerced(value.index, dest_ty) };
                }
            }
            switch (p.flags.size) {
                .slice => if (try sema.coerceToSlice(value, dest_ty)) |c| return c,
                // *[N]T to [*]T
                .many => if (try sema.coerceToManyPtr(value, dest_ty)) |c| return c,
                // *[N]T to [*c]T
                .c => if (try sema.coerceToManyPtr(value, dest_ty)) |c| return c,
                // A function value coerces to a pointer-to-function (`fn(...)` -> `*const fn(...)`) by
                // taking its address, like `&f` -- the coercion that builds a vtable of method pointers.
                .one => if (ip.indexToKey(p.child) == .func_type and ip.indexToKey(value.index) == .func)
                    return try sema.materializeConstPtr(value),
            }

            // coercion from a C pointer: a `[*c]T` source retypes to any non-slice pointer whose element
            // type matches (compiler: src_c_ptr).
            const src_ty = Value.typeOf(value, ip);
            if (src_ty.isCPtr(ip)) c_src: {
                if (p.flags.size == .slice) break :c_src;
                var in_memory_result: InMemoryCoercionResult = .{ .ok = .none };
                if (!sema.checkPtrAttributes(.fromIndex(dest_ty), src_ty, &in_memory_result)) break :c_src;
                switch (try sema.coerceInMemoryAllowed(.fromIndex(p.child), src_ty.childType(ip), !p.flags.is_const, null)) {
                    .ok => {},
                    else => break :c_src,
                }
                return .{ .index = try ip.getCoerced(value.index, dest_ty) };
            }

            // A C pointer destination also accepts a null, integer, or pointer source
            // (compiler: coerceExtra's `.c => switch (inst_ty.zigTypeTag(zcu))`).
            if (p.flags.size == .c) switch (src_ty.zigTypeTag(ip)) {
                .null => return .{ .index = try ip.internPtr(.{ .ty = dest_ty, .base_addr = .int, .byte_offset = 0 }) },
                .comptime_int, .int => {
                    const addr = try sema.resolveInt(value, .usize_type);
                    return .{ .index = try ip.internPtr(.{ .ty = dest_ty, .base_addr = .int, .byte_offset = addr }) };
                },
                .pointer => {
                    var in_memory_result: InMemoryCoercionResult = .{ .ok = .none };
                    if (sema.checkPtrAttributes(.fromIndex(dest_ty), src_ty, &in_memory_result))
                        return .{ .index = try ip.getCoerced(value.index, dest_ty) };
                },
                else => {},
            };
        },
        .array_type, .vector_type => {
            // The compiler dispatches an array/vector destination by source shape: an array/vector
            // source coerces element-wise (coerceArrayLike), a tuple source through coerceTupleToArray.
            if (Type.fromIndex(Value.typeOf(value, ip).index).isTuple(ip))
                return try sema.coerceTupleToArray(value, dest_ty);
            if (try sema.coerceArrayLike(value, dest_ty)) |c| return c;
        },
        .enum_type => switch (ip.indexToKey(value.index)) {
            .enum_literal => |name| {
                if (try sema.enumTagByName(dest_ty, name)) |tag| return tag;
                return sema.failBadMemberAccess(dest_ty, name);
            },
            .enum_tag => |et| if (et.ty == dest_ty) return value,
            .un => {
                // union to its own tag type; the REPL carries the tag enum on the tag value.
                if (ip.unionFields(value.typeOf(ip).index).tag_usage == .tagged) {
                    const tag = value.unionTag(ip).?;
                    if (tag.typeOf(ip).index == dest_ty) return tag;
                }
            },
            else => {},
        },
        .union_type => switch (ip.indexToKey(value.index)) {
            .un => |u| if (u.ty == dest_ty) return value,
            .enum_literal, .enum_tag => return try sema.coerceEnumToUnion(value, dest_ty),
            else => {},
        },
        else => {},
    }

    if (!report_err) return error.NotCoercible;
    return sema.fail(sema.block, sema.block.nodeOffset(.zero), "expected type '{f}', found '{f}'", .{ Type.fromIndex(dest_ty).fmt(ip), value_type.fmt(ip) });
}

fn coerceEnumToUnion(sema: *Sema, value: Value, union_ty: InternPool.Index) Error!Value {
    const ip = sema.intern_pool;
    const tag_enum = try sema.unionTagEnumType(union_ty);
    const enum_tag = try sema.coerceValueToType(value, tag_enum);
    const tag_idx = (try sema.enumTagFieldIndex(tag_enum, enum_tag)).?;
    const tag_name = (try sema.enumFieldName(tag_enum, tag_idx)).?;
    const field = (try sema.unionFieldByName(union_ty, tag_name)).?;
    if (field.ty == .void_type) {
        return .{ .index = try ip.internUnion(.{ .ty = union_ty, .tag = enum_tag.index, .val = .void_value }) };
    }
    if (try sema.isNoPossibleValue(field.ty)) {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "cannot initialize union field with uninstantiable type", .{});
    }
    return sema.fail(sema.block, sema.block.nodeOffset(.zero), "cannot initialize union field '{s}' from a bare tag", .{ip.stringSlice(tag_name)});
}

fn coerceToErrorSet(sema: *Sema, value: Value, dest_ty: InternPool.Index) Error!Value {
    const ip = sema.intern_pool;
    const key = ip.indexToKey(value.index);
    if (key != .err) {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "expected type '{f}', found '{f}'", .{ Type.fromIndex(dest_ty).fmt(ip), Value.typeOf(value, ip).fmt(ip) });
    }
    const imc = try sema.coerceInMemoryAllowedErrorSets(Type.fromIndex(dest_ty), Value.typeOf(value, ip));
    if (imc != .ok) {
        const src = sema.block.nodeOffset(.zero);
        const msg = msg: {
            const msg = try sema.errMsg(src, "expected type '{f}', found '{f}'", .{ Type.fromIndex(dest_ty).fmt(ip), Value.typeOf(value, ip).fmt(ip) });
            errdefer msg.destroy(sema.gpa);
            try imc.report(sema, src, msg);
            break :msg msg;
        };
        return sema.failWithOwnedErrorMsg(sema.block, msg);
    }
    return .{ .index = try ip.internErr(.{ .ty = dest_ty, .name = key.err.name }) };
}

fn coerceToSlice(sema: *Sema, value: Value, dest_ty: InternPool.Index) Error!?Value {
    const ip = sema.intern_pool;
    if (ip.indexToKey(value.index) != .ptr) return null;
    const array_ptr = ip.indexToKey(value.index).ptr;
    const child = ip.indexToKey(array_ptr.ty).ptr_type.child;
    if (ip.indexToKey(child) != .array_type) return null;
    const array = ip.indexToKey(child).array_type;

    const many_ptr = try ip.getCoerced(value.index, try ip.slicePtrType(dest_ty));
    const len_val = try ip.internInt(.{ .ty = .usize_type, .storage = .{ .u64 = array.len } });
    return .{ .index = try ip.get(.{ .slice = .{ .ty = dest_ty, .ptr = many_ptr, .len = len_val } }) };
}

fn coerceToManyPtr(sema: *Sema, value: Value, dest_ty: InternPool.Index) Error!?Value {
    const ip = sema.intern_pool;
    if (ip.indexToKey(value.index) != .ptr) return null;
    const array_ptr = ip.indexToKey(value.index).ptr;
    const child = ip.indexToKey(array_ptr.ty).ptr_type.child;
    if (ip.indexToKey(child) != .array_type) return null;
    const retagged = try ip.internPtr(.{ .ty = dest_ty, .base_addr = array_ptr.base_addr, .byte_offset = array_ptr.byte_offset });
    return .{ .index = retagged };
}

fn coerceArrayLike(sema: *Sema, value: Value, dest_ty: InternPool.Index) Error!?Value {
    const ip = sema.intern_pool;
    if (ip.indexToKey(value.index) != .aggregate) return null;
    const value_ty = Value.typeOf(value, ip);
    switch (value_ty.zigTypeTag(ip)) {
        .array, .vector => {},
        else => return null,
    }
    const dest = Type.fromIndex(dest_ty);
    if (value_ty.arrayLen(ip) != dest.arrayLen(ip)) return null;
    const dst_child = dest.childType(ip).index;

    const count: usize = @intCast(dest.arrayLen(ip));
    const elems = try sema.gpa.alloc(InternPool.Index, count);
    defer sema.gpa.free(elems);
    const agg = ip.indexToKey(value.index).aggregate;
    for (elems, 0..) |*e, i| {
        const elem: Value = .{ .index = try ip.aggregateElementAt(agg, i) };
        e.* = (try sema.coerceValueToType(elem, dst_child)).index;
    }
    return .{ .index = try ip.internAggregate(.{ .ty = dest_ty, .storage = .{ .elems = elems } }) };
}

/// The comptime value of tuple field `field_index`, with the tuple's bounds validated. Mirrors the
/// compiler's tupleField; the compiler's runtime path collapses here because a tuple value is always
/// comptime-known.
fn tupleField(sema: *Sema, tuple: Value, field_index: u32) Error!Value {
    const ip = sema.intern_pool;
    const tuple_ty = Value.typeOf(tuple, ip);
    const field_count = try sema.structFieldCount(tuple_ty.index);

    if (field_count == 0) {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "indexing into empty tuple is not allowed", .{});
    }

    if (field_index >= field_count) {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "index {d} outside tuple of length {d}", .{ field_index, field_count });
    }

    const field_ty = tuple_ty.fieldType(field_index, ip);

    if (try tuple_ty.structFieldValueComptime(sema, field_index)) |default_value| {
        return default_value; // comptime field
    }

    if (tuple.isUndef(ip)) return .{ .index = try ip.get(.{ .undef = field_ty.index }) };
    return try tuple.fieldValue(field_index, ip);
}

/// Coerce a tuple to an array/vector of matching length by coercing each element to the destination
/// element type (compiler: coerceTupleToArray). The REPL stores an array sentinel as a trailing
/// aggregate element (its storage convention; the compiler leaves it implied by the type).
fn coerceTupleToArray(sema: *Sema, value: Value, dest_ty: InternPool.Index) Error!Value {
    const ip = sema.intern_pool;
    const inst_len = ip.aggregateElementCount(Value.typeOf(value, ip).index);
    const dest_key = ip.indexToKey(dest_ty);
    const dest_len = switch (dest_key) {
        .array_type => |at| at.len,
        .vector_type => |vt| vt.len,
        else => unreachable,
    };
    if (dest_len != inst_len) {
        const src = sema.block.nodeOffset(.zero);
        const msg = msg: {
            const msg = try sema.errMsg(src, "expected type '{f}', found '{f}'", .{ Type.fromIndex(dest_ty).fmt(ip), Value.typeOf(value, ip).fmt(ip) });
            errdefer msg.destroy(sema.gpa);
            try sema.errNote(src, msg, "destination has length {d}", .{dest_len});
            try sema.errNote(src, msg, "source has length {d}", .{inst_len});
            break :msg msg;
        };
        return sema.failWithOwnedErrorMsg(sema.block, msg);
    }
    const dest_elem_ty = switch (dest_key) {
        .array_type => |at| at.child,
        .vector_type => |vt| vt.child,
        else => unreachable,
    };
    const elems = try sema.gpa.alloc(InternPool.Index, @intCast(dest_len));
    defer sema.gpa.free(elems);
    for (0..@intCast(dest_len)) |i| {
        const elem_val = try sema.tupleField(value, @intCast(i));
        elems[i] = (try sema.coerceValueToType(elem_val, dest_elem_ty)).index;
    }
    return .{ .index = try ip.internAggregate(.{ .ty = dest_ty, .storage = .{ .elems = elems } }) };
}

fn coerceToFixedWidthInt(sema: *Sema, value: Value, dest_ty: InternPool.Index) Error!?Value {
    const ip = sema.intern_pool;
    const dest = Type.fromIndex(dest_ty);
    // An undefined value carries no bits to check against the destination, so it coerces to undefined of
    // the destination (compiler: coerceExtra's per-arm `undefValue` for a numeric destination).
    if (value.isUndef(ip)) return try sema.undefValue(dest);
    // A comptime-known float coerces to an integer type when it has no fractional part; otherwise it is
    // an error (compiler: coerceExtra's int-dest / float-source arm, via `intFromFloat(.exact)`).
    if (ip.indexToKey(value.index) == .float and value.is_comptime) {
        return try sema.intFromFloat(value, Value.typeOf(value, ip), dest, .exact);
    }
    if (ip.indexToKey(value.index) != .int) return null;
    if (!value.is_comptime) {
        // integer widening: a runtime value re-types only when it cannot lose bits -- same signedness and
        // no narrower, or an unsigned into a strictly wider signed (compiler: coerceExtra's int-cast arm).
        const dst_info = dest.intInfo(ip);
        const src_info = Value.typeOf(value, ip).intInfo(ip);
        const widens = (src_info.signedness == dst_info.signedness and dst_info.bits >= src_info.bits) or
            (dst_info.signedness == .signed and dst_info.bits > src_info.bits);
        if (!widens) {
            return sema.fail(sema.block, sema.block.nodeOffset(.zero), "expected type '{f}', found '{f}'", .{ dest.fmt(ip), Value.typeOf(value, ip).fmt(ip) });
        }
    }
    var coerced = try sema.refitIntToFixedWidth(value.index, dest_ty);
    coerced.is_comptime = value.is_comptime;
    return coerced;
}

fn coerceToFloat(sema: *Sema, value: Value, dest_ty: InternPool.Index) Error!?Value {
    const ip = sema.intern_pool;
    const dest = Type.fromIndex(dest_ty);
    if (value.isUndef(ip)) return try sema.undefValue(dest);
    const value_type = Value.typeOf(value, ip);
    switch (value_type.zigTypeTag(ip)) {
        // A `comptime_float` always coerces (it carries full precision; the narrowing rounds).
        .comptime_float => {
            const result_val = try value.floatCast(dest, ip);
            return .{ .index = result_val.index, .is_comptime = value.is_comptime };
        },
        .float => {
            if (!value.is_comptime) {
                // A runtime float re-types only by widening (compiler: fpext requires no bit loss).
                if (dest.floatBits() < value_type.floatBits()) return null;
                const result_val = try value.floatCast(dest, ip);
                return .{ .index = result_val.index, .is_comptime = false };
            }
            const result_val = try value.floatCast(dest, ip);
            // The value coerces only if it survives a round-trip back to the source type unchanged.
            if (!value.eql(try result_val.floatCast(value_type, ip), value_type, ip)) {
                return sema.fail(sema.block, sema.block.nodeOffset(.zero), "type '{f}' cannot represent float value '{f}'", .{ dest.fmt(ip), render_value.fmt(value, ip) });
            }
            return .{ .index = result_val.index, .is_comptime = true };
        },
        .int, .comptime_int => {
            if (!value.is_comptime) {
                // A runtime integer becomes a float only when its precision fits the significand
                // (compiler: float_from_int); otherwise this is not a coercion.
                const int_info = value_type.intInfo(ip);
                const int_precision = int_info.bits - @intFromBool(int_info.signedness == .signed);
                if (int_precision > dest.floatSignificandBits()) return null;
                const result_val = try sema.floatValue(dest, value.toFloat(f128, ip));
                return .{ .index = result_val.index, .is_comptime = false };
            }
            const result_val = try sema.floatValue(dest, value.toFloat(f128, ip));
            var buffer: InternPool.Key.Int.Storage.BigIntSpace = undefined;
            const operand_big_int = value.toBigInt(&buffer, ip);
            // The integer coerces only if the float represents it exactly (round-trip through big-int).
            const fits = switch (ip.indexToKey(result_val.index).float.storage) {
                inline else => |x| fits: {
                    if (!std.math.isFinite(x)) break :fits false;
                    var result_big_int: std.math.big.int.Mutable = .{
                        .limbs = try sema.arena.alloc(std.math.big.Limb, std.math.big.int.calcLimbLen(x)),
                        .len = undefined,
                        .positive = undefined,
                    };
                    switch (result_big_int.setFloat(x, .nearest_even)) {
                        .inexact => break :fits false,
                        .exact => {},
                    }
                    break :fits result_big_int.toConst().eql(operand_big_int);
                },
            };
            if (!fits) {
                return sema.fail(sema.block, sema.block.nodeOffset(.zero), "type '{f}' cannot represent integer value '{f}'", .{ dest.fmt(ip), render_value.fmt(value, ip) });
            }
            return .{ .index = result_val.index, .is_comptime = true };
        },
        else => return null,
    }
}

fn coerceToOptional(
    sema: *Sema,
    value: Value,
    dest_ty: InternPool.Index,
) Error!Value {
    const ip = sema.intern_pool;
    const dest = Type.fromIndex(dest_ty);
    // Undefined sets the optional's presence bit to undefined too (compiler: coerceExtra's optional arm).
    if (value.isUndef(ip)) return (try dest.onePossibleValue(sema)) orelse try sema.undefValue(dest);
    if (value.index == .null_value) {
        const idx = try ip.internOpt(.{ .ty = dest_ty, .val = .none });
        return .{ .index = idx };
    }
    const child = ip.indexToKey(dest_ty).opt_type;
    const payload = try sema.coerceValueToType(value, child);
    const idx = try ip.internOpt(.{ .ty = dest_ty, .val = payload.index });
    return .{ .index = idx };
}

fn evalIntType(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@backingInt(inst) < sema.zir.instructions.len);

    const int_type = sema.zir.instructions.items(.data)[@backingInt(inst)].int_type;
    const idx = try sema.intern_pool.internIntType(int_type.signedness, int_type.bit_count);
    return .{ .index = idx };
}

fn evalReifyInt(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const pl_node = sema.zir.instructions.items(.data)[@backingInt(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.Bin, pl_node.payload_index).data;
    const signedness = try sema.resolveStdLangEnum(.Signedness, extra.lhs);
    const bits: u16 = @intCast(try sema.resolveInt(try sema.resolveInst(extra.rhs), .u16_type));
    if (bits == 0 and signedness == .signed) {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "signed integer cannot have bit width 0", .{});
    }
    return .{ .index = try sema.intern_pool.internIntType(signedness, bits) };
}

fn evalReifyTuple(sema: *Sema, extended: Zir.Inst.Extended.InstData) Error!?Value {
    const ip = sema.intern_pool;
    const extra = sema.zir.extraData(Zir.Inst.UnNode, extended.operand).data;

    const types_uncoerced = try sema.resolveInst(extra.operand);
    const types_slice_val = try sema.coerceValueToType(types_uncoerced, try sema.sliceConstTypeTy());
    const types_array_val = try sema.derefSliceAsArray(types_slice_val);
    const array = ip.indexToKey(types_array_val.index).aggregate;
    const fields_len: u32 = @intCast(ip.indexToKey(array.ty).array_type.len);

    const field_types = try sema.gpa.alloc(InternPool.Index, fields_len);
    defer sema.gpa.free(field_types);
    for (field_types, 0..) |*field_ty, field_idx| {
        const field_ty_val = try ip.aggregateElementAt(array, field_idx);
        if (ip.indexToKey(field_ty_val) == .undef) {
            return sema.fail(sema.block, sema.block.nodeOffset(.zero), "use of undefined value here causes illegal behavior", .{});
        }
        try sema.validateTupleFieldType(field_ty_val);
        field_ty.* = field_ty_val;
    }
    const field_vals = try sema.gpa.alloc(InternPool.Index, fields_len);
    defer sema.gpa.free(field_vals);
    @memset(field_vals, .none);
    return .{ .index = try ip.internTupleType(field_types, field_vals) };
}

fn derefSliceAsArray(sema: *Sema, val: Value) Error!Value {
    const ip = sema.intern_pool;
    const slice_ty = val.typeOf(ip);
    assert(slice_ty.zigTypeTag(ip) == .pointer);
    switch (slice_ty.ptrInfo(ip).flags.size) {
        .slice => {},
        .one => return sema.loadValue(val),
        .many, .c => unreachable,
    }
    const slice = switch (ip.indexToKey(val.index)) {
        .undef => return sema.failWithUseOfUndef(),
        .slice => |slice| slice,
        else => unreachable,
    };
    const elem_ty = Type.fromIndex(slice.ty).childType(ip);
    const len = try sema.resolveUsizeInt(.{ .index = slice.len });
    const array_ty = try ip.internArrayType(.{ .child = elem_ty.index, .len = len });
    const ptr_ty = try ip.internPtrType(p: {
        var p = Type.fromIndex(slice.ty).ptrInfo(ip);
        p.flags.size = .one;
        p.child = array_ty;
        p.sentinel = .none;
        break :p p;
    });
    const casted_ptr = try ip.getCoerced(slice.ptr, ptr_ty);
    return sema.loadValue(.{ .index = casted_ptr });
}

fn validateTupleFieldType(sema: *Sema, field_ty: InternPool.Index) Error!void {
    if (field_ty == .anyopaque_type) {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "opaque types have unknown size and therefore cannot be directly embedded in tuples", .{});
    }
    if (field_ty == .noreturn_type) {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "tuple fields cannot be 'noreturn'", .{});
    }
}

fn evalReifyPointer(sema: *Sema, extended: Zir.Inst.Extended.InstData) Error!?Value {
    const ip = sema.intern_pool;
    const extra = sema.zir.extraData(Zir.Inst.ReifyPointer, extended.operand).data;

    const size_ty = try sema.getStdLangType(.@"Type.Pointer.Size");
    const attrs_ty = try sema.getStdLangType(.@"Type.Pointer.Attributes");

    const size_val = try sema.coerceValueToType(try sema.resolveInst(extra.size), size_ty);
    const size = try sema.interpretStdLangEnum(std.lang.Type.Pointer.Size, size_ty, size_val, "pointer size");

    const attrs_val = try sema.coerceValueToType(try sema.resolveInst(extra.attrs), attrs_ty);
    const attrs = try sema.interpretStdLangType(std.lang.Type.Pointer.Attributes, attrs_val);
    const is_const = attrs.@"const";
    const is_volatile = attrs.@"volatile";
    const is_allowzero = attrs.@"allowzero";
    const address_space: std.lang.AddressSpace = attrs.@"addrspace" orelse .generic;
    const alignment: InternPool.Alignment = if (attrs.@"align") |bytes|
        try sema.validateAlign(sema.block.nodeOffset(.zero), bytes)
    else
        .none;

    const elem_ty = try sema.resolveDestType(extra.elem_ty);
    switch (Type.fromIndex(elem_ty).zigTypeTag(ip)) {
        .noreturn => return sema.fail(sema.block, sema.block.nodeOffset(.zero), "pointer to noreturn not allowed", .{}),
        // This needs to be disallowed, because the sentinel parameter would otherwise have type
        // `?@TypeOf(null)`, which is not a valid type because you cannot differentiate between
        // constructing the "inner" null value and the "outer" null value.
        .null => return sema.fail(sema.block, sema.block.nodeOffset(.zero), "cannot reify pointer to '@TypeOf(null)'", .{}),
        .@"fn" => switch (size) {
            .one => {},
            .many, .c, .slice => return sema.fail(sema.block, sema.block.nodeOffset(.zero), "function pointers must be single pointers", .{}),
        },
        .@"opaque" => switch (size) {
            .one => {},
            .many, .c, .slice => return sema.fail(sema.block, sema.block.nodeOffset(.zero), "indexable pointer to opaque type '{f}' not allowed", .{Type.fromIndex(elem_ty).fmt(ip)}),
        },
        else => {},
    }

    const sentinel_ty = try ip.internOptionalType(elem_ty);
    const sentinel_val = try sema.coerceValueToType(try sema.resolveInst(extra.sentinel), sentinel_ty);
    const opt_sentinel = ip.indexToKey(sentinel_val.index).opt.val;
    if (opt_sentinel != .none) {
        switch (size) {
            .many, .slice => {},
            .one, .c => return sema.fail(sema.block, sema.block.nodeOffset(.zero), "sentinels are only allowed on slices and unknown-length pointers", .{}),
        }
        try sema.checkSentinelType(elem_ty);
    }

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

fn evalReifyPointerSentinelTy(sema: *Sema, extended: Zir.Inst.Extended.InstData) Error!?Value {
    const ip = sema.intern_pool;
    const extra = sema.zir.extraData(Zir.Inst.UnNode, extended.operand).data;
    const elem_ty = try sema.resolveDestType(extra.operand);
    return .{
        .index = switch (Type.fromIndex(elem_ty).zigTypeTag(ip)) {
            else => try ip.internOptionalType(elem_ty),
            // These types cannot be the child of an optional. To allow reifying pointers to them still,
            // we treat the "sentinel" argument to `@Pointer` as `?noreturn` instead of `?T`.
            .@"opaque", .null => .optional_noreturn_type,
        },
    };
}

fn evalReifySliceArgTy(sema: *Sema, extended: Zir.Inst.Extended.InstData) Error!?Value {
    const ip = sema.intern_pool;
    const extra = sema.zir.extraData(Zir.Inst.UnNode, extended.operand).data;
    const info: Zir.Inst.ReifySliceArgInfo = @fromBackingInt(@intCast(extended.small));
    const in_scalar_ty: InternPool.Index, const out_scalar_ty: InternPool.Index = switch (info) {
        .type_to_fn_param_attrs => .{ .type_type, try sema.getStdLangType(.@"Type.Fn.ParamAttributes") },
        .string_to_struct_field_type => .{ try sema.sliceConstU8Ty(), .type_type },
        .string_to_struct_field_attrs => .{ try sema.sliceConstU8Ty(), try sema.getStdLangType(.@"Type.Struct.FieldAttributes") },
        .string_to_union_field_type => .{ try sema.sliceConstU8Ty(), .type_type },
        .string_to_union_field_attrs => .{ try sema.sliceConstU8Ty(), try sema.getStdLangType(.@"Type.Union.FieldAttributes") },
    };
    const operand_ty = try ip.internPtrType(.{ .child = in_scalar_ty, .flags = .{ .size = .slice, .is_const = true } });
    const operand_val = try sema.coerceValueToType(try sema.resolveInst(extra.operand), operand_ty);
    const len_val: Value = .fromIndex(ip.indexToKey(operand_val.index).slice.len);
    if (len_val.isUndef(ip)) return sema.failWithUseOfUndef();
    const len = try sema.resolveUsizeInt(len_val);
    const arr_ty = try ip.internArrayType(.{ .len = len, .child = out_scalar_ty });
    return .{ .index = try ip.internPtrType(.{ .child = arr_ty, .flags = .{ .size = .one, .is_const = true } }) };
}

const calling_conventions_supporting_var_args = [_]std.lang.CallingConvention.Tag{
    .x86_16_cdecl,
    .x86_64_sysv,
    .x86_64_x32,
    .x86_64_win,
    .x86_sysv,
    .x86_win,
    .aarch64_aapcs,
    .aarch64_aapcs_darwin,
    .aarch64_aapcs_win,
    .aarch64_vfabi,
    .aarch64_vfabi_sve,
    .alpha_osf,
    .arm_aapcs,
    .arm_aapcs_vfp,
    .microblaze_std,
    .mips64_n64,
    .mips64_n32,
    .mips_o32,
    .riscv64_lp64,
    .riscv64_lp64_v,
    .riscv32_ilp32,
    .riscv32_ilp32_v,
    .sparc64_sysv,
    .sparc_sysv,
    .powerpc64_elf,
    .powerpc64_elf_altivec,
    .powerpc64_elf_v2,
    .powerpc_sysv,
    .powerpc_sysv_altivec,
    .powerpc_aix,
    .powerpc_aix_altivec,
    .wasm_mvp,
    .arc_sysv,
    .avr_gnu,
    .bpf_std,
    .csky_sysv,
    .hexagon_sysv,
    .hexagon_sysv_hvx,
    .hppa_elf,
    .hppa64_elf,
    .kvx_lp64,
    .kvx_ilp32,
    .lanai_sysv,
    .loongarch64_lp64,
    .loongarch32_ilp32,
    .m68k_sysv,
    .m68k_gnu,
    .m68k_rtd,
    .m88k_sysv,
    .msp430_eabi,
    .or1k_sysv,
    .s390x_sysv,
    .s390x_sysv_vx,
    .sh_gnu,
    .sh_renesas,
    .ve_sysv,
    .xcore_xs1,
    .xcore_xs2,
    .xtensa_call0,
    .xtensa_windowed,
};

fn callConvSupportsVarArgs(cc: std.lang.CallingConvention.Tag) bool {
    return for (calling_conventions_supporting_var_args) |supported_cc| {
        if (cc == supported_cc) return true;
    } else false;
}

fn checkCallConvSupportsVarArgs(sema: *Sema, cc: std.lang.CallingConvention.Tag) Error!void {
    if (!callConvSupportsVarArgs(cc)) {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "variadic function does not support '{s}' calling convention", .{@tagName(cc)});
    }
}

// Ported from Sema.checkParamType. The option-carrying interrupt calling conventions (x86_64_interrupt,
// arm_interrupt, ...) are rejected earlier by `interpretCallConv`, so only the option-free avr_interrupt and
// avr_signal reach this switch; the comptime/generic-parameter and vulkan/opengl address-space branches do
// not apply to `@Fn` reification (concrete parameter types, native target).
fn checkParamType(sema: *Sema, param_ty: Type, param_is_noalias: bool, cc: std.lang.CallingConvention.Tag) Error!void {
    const ip = sema.intern_pool;
    if (!param_ty.isValidParamType(ip)) {
        const opaque_str: []const u8 = if (param_ty.zigTypeTag(ip) == .@"opaque") "opaque " else "";
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "parameter of {s}type '{f}' not allowed", .{ opaque_str, param_ty.fmt(ip) });
    }
    switch (cc) {
        .avr_interrupt, .avr_signal => return sema.fail(sema.block, sema.block.nodeOffset(.zero), "parameters are not allowed with '{s}' calling convention", .{@tagName(cc)}),
        else => {},
    }
    if (param_is_noalias and !param_ty.isGenericPoison() and !param_ty.isPtrAtRuntime(ip) and !param_ty.isSliceAtRuntime(ip)) {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "non-pointer parameter declared noalias", .{});
    }
}

// Ported from Sema.checkReturnTypeAndCallConv. incoming-stack-alignment does not apply here (option-carrying
// calling conventions are rejected by `interpretCallConv`), so of the interrupt calling conventions only the
// option-free avr_interrupt and avr_signal reach the switch.
fn checkReturnTypeAndCallConv(sema: *Sema, bare_ret_ty: Type, opt_varargs: bool, inferred_error_set: bool, cc: std.lang.CallingConvention.Tag) Error!void {
    const ip = sema.intern_pool;
    if (opt_varargs) {
        try sema.checkCallConvSupportsVarArgs(cc);
    }
    if (inferred_error_set and !bare_ret_ty.isGenericPoison()) {
        try sema.validateErrorUnionPayloadType(bare_ret_ty);
    }
    const ies_ret_ty_prefix: []const u8 = if (inferred_error_set) "!" else "";
    if (!bare_ret_ty.isValidReturnType(ip)) {
        const opaque_str: []const u8 = if (bare_ret_ty.zigTypeTag(ip) == .@"opaque") "opaque " else "";
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "{s}return type '{s}{f}' not allowed", .{ opaque_str, ies_ret_ty_prefix, bare_ret_ty.fmt(ip) });
    }
    switch (cc) {
        .avr_interrupt, .avr_signal => {
            const ret_ok = switch (bare_ret_ty.index) {
                .void_type, .noreturn_type => true,
                else => false,
            };
            if (!ret_ok) {
                return sema.fail(sema.block, sema.block.nodeOffset(.zero), "function with calling convention '{s}' must return 'void' or 'noreturn'", .{@tagName(cc)});
            }
        },
        else => {},
    }
}

fn interpretCallConv(sema: *Sema, val: Value) Error!std.lang.CallingConvention {
    return sema.interpretStdLangType(std.lang.CallingConvention, val);
}

fn interpretStdLangType(sema: *Sema, comptime T: type, val: Value) Error!T {
    return val.interpret(T, sema.intern_pool) catch |err| switch (err) {
        error.OutOfMemory => |e| return e,
        error.UndefinedValue => return sema.failWithUseOfUndef(),
        error.TypeMismatch => @panic("std.lang is corrupt"),
    };
}

fn uninterpretStdLangType(sema: *Sema, val: anytype, ty: Type) Error!Value {
    return Value.uninterpret(val, ty, sema);
}

fn evalReifyFn(sema: *Sema, extended: Zir.Inst.Extended.InstData) Error!?Value {
    const ip = sema.intern_pool;
    const extra = sema.zir.extraData(Zir.Inst.ReifyFn, extended.operand).data;

    const param_types_slice = try sema.coerceValueToType(try sema.resolveInst(extra.param_types), try sema.sliceConstTypeTy());
    const param_types_arr = ip.indexToKey((try sema.derefSliceAsArray(param_types_slice)).index).aggregate;
    const params_len: u32 = @intCast(ip.indexToKey(param_types_arr.ty).array_type.len);

    const param_attrs_arr = ip.indexToKey((try sema.derefSliceAsArray(try sema.resolveInst(extra.param_attrs))).index).aggregate;

    const ret_ty = try sema.resolveDestType(extra.ret_ty);

    const fn_attrs_val = try sema.coerceValueToType(try sema.resolveInst(extra.fn_attrs), try sema.getStdLangType(.@"Type.Fn.Attributes"));
    const fn_attrs = ip.indexToKey(fn_attrs_val.index).aggregate;
    const cc = try sema.interpretCallConv(.{ .index = try ip.aggregateElementAt(fn_attrs, 0) });
    const varargs = try ip.aggregateElementAt(fn_attrs, 1) == .bool_true;

    var noalias_bits: u32 = 0;
    const param_types = try sema.gpa.alloc(InternPool.Index, params_len);
    defer sema.gpa.free(param_types);
    for (param_types, 0..) |*param_ty, param_idx| {
        param_ty.* = try ip.aggregateElementAt(param_types_arr, param_idx);
        const param_attr = ip.indexToKey(try ip.aggregateElementAt(param_attrs_arr, param_idx)).aggregate;
        const param_is_noalias = try ip.aggregateElementAt(param_attr, 0) == .bool_true;
        try sema.checkParamType(.fromIndex(param_ty.*), param_is_noalias, std.meta.activeTag(cc));
        if (param_is_noalias) {
            if (param_idx > 31) {
                return sema.fail(sema.block, sema.block.nodeOffset(.zero), "this compiler implementation only supports 'noalias' on the first 32 parameters", .{});
            }
            noalias_bits |= @as(u32, 1) << @intCast(param_idx);
        }
    }

    try sema.checkReturnTypeAndCallConv(.fromIndex(ret_ty), varargs, false, std.meta.activeTag(cc));

    return .{ .index = try ip.internFuncType(.{
        .param_types = param_types,
        .noalias_bits = noalias_bits,
        .return_type = ret_ty,
        .cc = cc,
        .is_var_args = varargs,
    }) };
}

fn sliceOfStringTy(sema: *Sema) Error!InternPool.Index {
    return try sema.intern_pool.internPtrType(.{ .child = try sema.sliceConstU8Ty(), .flags = .{ .size = .slice, .is_const = true } });
}

fn sliceConstU8Ty(sema: *Sema) Error!InternPool.Index {
    return try sema.intern_pool.internPtrType(.{ .child = .u8_type, .flags = .{ .size = .slice, .is_const = true } });
}

fn sliceToIpString(sema: *Sema, slice_val: Value) Error!InternPool.NullTerminatedString {
    const ip = sema.intern_pool;
    const arr = try sema.derefSliceAsArray(slice_val);
    const agg = ip.indexToKey(arr.index).aggregate;
    const len: usize = @intCast(ip.indexToKey(agg.ty).array_type.len);
    const buf = try sema.gpa.alloc(u8, len);
    defer sema.gpa.free(buf);
    for (buf, 0..) |*b, i| b.* = @intCast(sema.intAsI128(try ip.aggregateElementAt(agg, i)) orelse {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "use of undefined value here causes illegal behavior", .{});
    });
    return try ip.getOrPutString(sema.gpa, buf, .no_embedded_nulls);
}

fn evalReifyEnumValueSliceTy(sema: *Sema, extended: Zir.Inst.Extended.InstData) Error!?Value {
    const ip = sema.intern_pool;
    const extra = sema.zir.extraData(Zir.Inst.BinNode, extended.operand).data;
    const int_tag_ty = try sema.resolveDestType(extra.lhs);
    const names_slice = try sema.coerceValueToType(try sema.resolveInst(extra.rhs), try sema.sliceOfStringTy());
    const len_val: Value = .fromIndex(ip.indexToKey(names_slice.index).slice.len);
    if (len_val.isUndef(ip)) return sema.failWithUseOfUndef();
    const len = try sema.resolveUsizeInt(len_val);
    const arr_ty = try ip.internArrayType(.{ .len = len, .child = int_tag_ty });
    return .{ .index = try ip.internPtrType(.{ .child = arr_ty, .flags = .{ .size = .one, .is_const = true } }) };
}

fn evalReifyEnum(sema: *Sema, extended: Zir.Inst.Extended.InstData, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    const name_strategy: Zir.Inst.NameStrategy = @fromBackingInt(@intCast(extended.small));
    const extra = sema.zir.extraData(Zir.Inst.ReifyEnum, extended.operand).data;

    // Reify diagnostics anchor per argument on the reify instruction (base node = `inst`), matching
    // the compiler's `@Enum(tag_ty, mode, names, values)` argument layout.
    const field_names_src: LazySrcLoc = .{ .base_node_inst = inst, .offset = .{ .node_offset_builtin_call_arg = .{ .builtin_call_node = .zero, .arg_index = 2 } } };
    const field_values_src: LazySrcLoc = .{ .base_node_inst = inst, .offset = .{ .node_offset_builtin_call_arg = .{ .builtin_call_node = .zero, .arg_index = 3 } } };

    const tag_ty = try sema.resolveDestType(extra.tag_ty);

    const enum_mode_ty = try sema.getStdLangType(.@"Type.Enum.Mode");
    const mode_val = try sema.coerceValueToType(try sema.resolveInst(extra.mode), enum_mode_ty);
    const nonexhaustive = switch (try sema.interpretStdLangEnum(std.lang.Type.Enum.Mode, enum_mode_ty, mode_val, "enum mode")) {
        .exhaustive => false,
        .nonexhaustive => true,
    };

    const names_slice = try sema.coerceValueToType(try sema.resolveInst(extra.field_names), try sema.sliceOfStringTy());
    const names_agg = ip.indexToKey((try sema.derefSliceAsArray(names_slice)).index).aggregate;
    const fields_len: u32 = @intCast(ip.indexToKey(names_agg.ty).array_type.len);

    const values_ty = try ip.internPtrType(.{
        .child = try ip.internArrayType(.{ .len = fields_len, .child = tag_ty }),
        .flags = .{ .size = .one, .is_const = true },
    });
    const values_slice = try sema.coerceValueToType(try sema.resolveInst(extra.field_values), values_ty);
    const values_arr = try sema.derefSliceAsArray(values_slice);
    const values_agg = ip.indexToKey(values_arr.index).aggregate;

    const names = try sema.gpa.alloc(InternPool.NullTerminatedString, fields_len);
    defer sema.gpa.free(names);
    for (names, 0..) |*n, i| n.* = try sema.sliceToIpString(.{ .index = try ip.aggregateElementAt(names_agg, i) });
    const values = try sema.gpa.alloc(InternPool.Index, fields_len);
    defer sema.gpa.free(values);
    for (values, 0..) |*v, i| {
        v.* = try ip.aggregateElementAt(values_agg, i);
        if (ip.indexToKey(v.*) == .undef) {
            return sema.fail(sema.block, field_values_src, "use of undefined value here causes illegal behavior", .{});
        }
    }

    var hasher = std.hash.Wyhash.init(0);
    std.hash.autoHash(&hasher, tag_ty);
    std.hash.autoHash(&hasher, nonexhaustive);
    std.hash.autoHash(&hasher, fields_len);
    std.hash.autoHash(&hasher, values_arr.index);
    for (names) |n| std.hash.autoHash(&hasher, n);

    const name = switch (name_strategy) {
        .parent => sema.block.type_name_ctx,
        .anon, .func, .dbg_var => blk: {
            const ctx = ip.stringSlice(sema.block.type_name_ctx);
            const text = try std.fmt.allocPrint(sema.gpa, "{s}__enum_{d}", .{ ctx, @backingInt(inst) });
            defer sema.gpa.free(text);
            break :blk try ip.getOrPutString(sema.gpa, text, .no_embedded_nulls);
        },
    };

    const enum_ty = try ip.getReifiedEnumType(.{
        .name = name,
        .id = .{ .reified = .{ .source_zir_id = sema.current_zir_id, .decl_inst = inst, .type_hash = hasher.final() } },
        .int_tag_type = tag_ty,
        .nonexhaustive = nonexhaustive,
        .names = names,
        .values = values,
    });
    const fields = ip.loadEnumType(enum_ty);
    fields.field_name_map.get(ip).clearRetainingCapacity();
    for (names, 0..) |field_name, field_index| {
        if (ip.addFieldName(names, fields.field_name_map, field_name)) |prev_field_index| {
            return sema.failWithOwnedErrorMsg(sema.block, msg: {
                const msg = try sema.errMsg(field_names_src, "duplicate enum field '{f}' at index '{d}'", .{ field_name.fmt(ip), field_index });
                errdefer msg.destroy(sema.gpa);
                try sema.errNote(field_names_src, msg, "previous field at index '{d}'", .{prev_field_index});
                break :msg msg;
            });
        }
    }
    if (fields.field_value_map.unwrap()) |value_map| {
        value_map.get(ip).clearRetainingCapacity();
        for (values, 0..) |field_value, field_index| {
            if (ip.addFieldTagValue(values, value_map, field_value)) |prev_field_index| {
                return sema.failWithOwnedErrorMsg(sema.block, msg: {
                    const msg = try sema.errMsg(field_values_src, "enum tag value '{f}' for field '{f}' already taken", .{ render_value.fmt(.{ .index = field_value }, ip), names[field_index].fmt(ip) });
                    errdefer msg.destroy(sema.gpa);
                    try sema.errNote(field_values_src, msg, "previous occurrence in field '{f}'", .{names[prev_field_index].fmt(ip)});
                    break :msg msg;
                });
            }
        }
    }
    return .{ .index = enum_ty };
}

fn evalReifyStruct(sema: *Sema, extended: Zir.Inst.Extended.InstData, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    const name_strategy: Zir.Inst.NameStrategy = @fromBackingInt(@intCast(extended.small));
    const extra = sema.zir.extraData(Zir.Inst.ReifyStruct, extended.operand).data;

    // A reify instruction is `extended`, so its diagnostics anchor per argument on the reify
    // instruction itself (base node = `inst`), matching the compiler's `@Struct` arg layout.
    const backing_ty_src: LazySrcLoc = .{ .base_node_inst = inst, .offset = .{ .node_offset_builtin_call_arg = .{ .builtin_call_node = .zero, .arg_index = 1 } } };
    const field_names_src: LazySrcLoc = .{ .base_node_inst = inst, .offset = .{ .node_offset_builtin_call_arg = .{ .builtin_call_node = .zero, .arg_index = 2 } } };
    const field_types_src: LazySrcLoc = .{ .base_node_inst = inst, .offset = .{ .node_offset_builtin_call_arg = .{ .builtin_call_node = .zero, .arg_index = 3 } } };
    const field_attrs_src: LazySrcLoc = .{ .base_node_inst = inst, .offset = .{ .node_offset_builtin_call_arg = .{ .builtin_call_node = .zero, .arg_index = 4 } } };

    const layout_ty = try sema.getStdLangType(.@"Type.ContainerLayout");
    const layout_val = try sema.coerceValueToType(try sema.resolveInst(extra.layout), layout_ty);
    const layout = try sema.interpretStdLangEnum(std.lang.Type.ContainerLayout, layout_ty, layout_val, "struct layout");

    const backing_val = try sema.coerceValueToType(try sema.resolveInst(extra.backing_ty), try ip.internOptionalType(.type_type));
    if (ip.indexToKey(backing_val.index) == .undef) {
        return sema.fail(sema.block, backing_ty_src, "use of undefined value here causes illegal behavior", .{});
    }
    const backing_int = ip.indexToKey(backing_val.index).opt.val;
    if (backing_int != .none and layout != .@"packed") {
        return sema.fail(sema.block, backing_ty_src, "non-packed struct does not support backing integer type", .{});
    }

    const names_slice = try sema.coerceValueToType(try sema.resolveInst(extra.field_names), try sema.sliceOfStringTy());
    const names_agg = ip.indexToKey((try sema.derefSliceAsArray(names_slice)).index).aggregate;
    const fields_len: u32 = @intCast(ip.indexToKey(names_agg.ty).array_type.len);

    const field_types_ty = try ip.internPtrType(.{
        .child = try ip.internArrayType(.{ .len = fields_len, .child = .type_type }),
        .flags = .{ .size = .one, .is_const = true },
    });
    const types_arr = try sema.derefSliceAsArray(try sema.coerceValueToType(try sema.resolveInst(extra.field_types), field_types_ty));
    const types_agg = ip.indexToKey(types_arr.index).aggregate;

    const attrs_scalar_ty = try sema.getStdLangType(.@"Type.Struct.FieldAttributes");
    const field_attrs_ty = try ip.internPtrType(.{
        .child = try ip.internArrayType(.{ .len = fields_len, .child = attrs_scalar_ty }),
        .flags = .{ .size = .one, .is_const = true },
    });
    const attrs_agg = ip.indexToKey((try sema.derefSliceAsArray(try sema.coerceValueToType(try sema.resolveInst(extra.field_attrs), field_attrs_ty))).index).aggregate;

    const names = try sema.gpa.alloc(InternPool.NullTerminatedString, fields_len);
    defer sema.gpa.free(names);
    const types = try sema.gpa.alloc(InternPool.Index, fields_len);
    defer sema.gpa.free(types);
    const defaults = try sema.gpa.alloc(InternPool.Index, fields_len);
    defer sema.gpa.free(defaults);
    @memset(defaults, .none);
    const aligns = try sema.gpa.alloc(InternPool.Alignment, fields_len);
    defer sema.gpa.free(aligns);
    @memset(aligns, .none);
    const comptime_words = try sema.gpa.alloc(u32, (fields_len + 31) / 32);
    defer sema.gpa.free(comptime_words);
    @memset(comptime_words, 0);
    var any_defaults = false;
    var any_aligns = false;
    var any_comptime = false;

    var hasher = std.hash.Wyhash.init(0);
    std.hash.autoHash(&hasher, layout);
    std.hash.autoHash(&hasher, backing_val.index);
    std.hash.autoHash(&hasher, types_arr.index);

    for (names, types, 0..) |*name_out, *type_out, i| {
        name_out.* = try sema.sliceToIpString(.{ .index = try ip.aggregateElementAt(names_agg, i) });
        type_out.* = try ip.aggregateElementAt(types_agg, i);
        if (ip.indexToKey(type_out.*) == .undef) {
            return sema.fail(sema.block, field_types_src, "use of undefined value here causes illegal behavior", .{});
        }
        const attr_elem = try ip.aggregateElementAt(attrs_agg, i);
        if (ip.indexToKey(attr_elem) == .undef) {
            return sema.fail(sema.block, field_attrs_src, "use of undefined value here causes illegal behavior", .{});
        }
        const StructFieldAttributes = std.lang.Type.Struct.FieldAttributes;
        const attr_v: Value = .fromIndex(attr_elem);
        const comptime_elem = (try attr_v.fieldValue(comptime std.meta.fieldIndex(StructFieldAttributes, "comptime").?, ip)).index;
        const align_opt = ip.indexToKey((try attr_v.fieldValue(comptime std.meta.fieldIndex(StructFieldAttributes, "align").?, ip)).index).opt.val;
        const default_ptr = ip.indexToKey((try attr_v.fieldValue(comptime std.meta.fieldIndex(StructFieldAttributes, "default_value_ptr").?, ip)).index).opt.val;

        // `default_value_ptr` is typed `*const anyopaque`; re-type it to a pointer to the field type
        // before loading, so the deref reinterprets from the pointee rather than the opaque type.
        const field_default: InternPool.Index = if (default_ptr == .none) .none else d: {
            const field_ptr_ty = try ip.internPtrType(.{ .child = type_out.*, .flags = .{ .size = .one, .is_const = true } });
            break :d (try sema.loadValue(.{ .index = try ip.getCoerced(default_ptr, field_ptr_ty) })).index;
        };
        if (field_default != .none) {
            defaults[i] = field_default;
            any_defaults = true;
        }

        if (comptime_elem == .bool_true) {
            if (field_default == .none) {
                return sema.fail(sema.block, field_attrs_src, "comptime field without default initialization value", .{});
            }
            if (layout != .auto) {
                return sema.fail(sema.block, field_attrs_src, "non-auto struct fields cannot be marked comptime", .{});
            }
            comptime_words[i / 32] |= @as(u32, 1) << @intCast(i % 32);
            any_comptime = true;
        }

        if (align_opt != .none) {
            if (layout == .@"packed") {
                return sema.fail(sema.block, field_attrs_src, "packed struct fields cannot be aligned", .{});
            }
            aligns[i] = try sema.alignmentFromValue(.{ .index = align_opt });
            any_aligns = true;
        }

        std.hash.autoHash(&hasher, name_out.*);
        std.hash.autoHash(&hasher, comptime_elem);
        std.hash.autoHash(&hasher, align_opt);
        std.hash.autoHash(&hasher, field_default);
    }

    const name = switch (name_strategy) {
        .parent => sema.block.type_name_ctx,
        .anon, .func, .dbg_var => blk: {
            const ctx = ip.stringSlice(sema.block.type_name_ctx);
            const text = try std.fmt.allocPrint(sema.gpa, "{s}__struct_{d}", .{ ctx, @backingInt(inst) });
            defer sema.gpa.free(text);
            break :blk try ip.getOrPutString(sema.gpa, text, .no_embedded_nulls);
        },
    };

    const struct_ty = try ip.getReifiedStructType(.{
        .name = name,
        .id = .{ .reified = .{ .source_zir_id = sema.current_zir_id, .decl_inst = inst, .type_hash = hasher.final() } },
        .layout = layout,
        .backing_int = backing_int,
        .names = names,
        .types = types,
        .defaults = if (any_defaults) defaults else &.{},
        .aligns = if (any_aligns) aligns else &.{},
        .comptime_bits = if (any_comptime) comptime_words else &.{},
    });
    const fields = ip.loadStructType(struct_ty);
    fields.field_name_map.get(ip).clearRetainingCapacity();
    for (names, 0..) |field_name, field_index| {
        if (ip.addFieldName(names, fields.field_name_map, field_name)) |prev_field_index| {
            return sema.failWithOwnedErrorMsg(sema.block, msg: {
                const msg = try sema.errMsg(field_names_src, "duplicate struct field '{f}' at index '{d}'", .{ field_name.fmt(ip), field_index });
                errdefer msg.destroy(sema.gpa);
                try sema.errNote(field_names_src, msg, "previous field at index '{d}'", .{prev_field_index});
                break :msg msg;
            });
        }
    }
    return .{ .index = struct_ty };
}

fn evalReifyUnion(sema: *Sema, extended: Zir.Inst.Extended.InstData, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    const name_strategy: Zir.Inst.NameStrategy = @fromBackingInt(@intCast(extended.small));
    const extra = sema.zir.extraData(Zir.Inst.ReifyUnion, extended.operand).data;

    // Reify diagnostics anchor per argument on the reify instruction (base node = `inst`), matching
    // the compiler's `@Union(layout, tag_ty, names, types, aligns)` argument layout.
    const arg_ty_src: LazySrcLoc = .{ .base_node_inst = inst, .offset = .{ .node_offset_builtin_call_arg = .{ .builtin_call_node = .zero, .arg_index = 1 } } };
    const field_names_src: LazySrcLoc = .{ .base_node_inst = inst, .offset = .{ .node_offset_builtin_call_arg = .{ .builtin_call_node = .zero, .arg_index = 2 } } };
    const field_types_src: LazySrcLoc = .{ .base_node_inst = inst, .offset = .{ .node_offset_builtin_call_arg = .{ .builtin_call_node = .zero, .arg_index = 3 } } };
    const field_attrs_src: LazySrcLoc = .{ .base_node_inst = inst, .offset = .{ .node_offset_builtin_call_arg = .{ .builtin_call_node = .zero, .arg_index = 4 } } };

    const layout_ty = try sema.getStdLangType(.@"Type.ContainerLayout");
    const layout_val = try sema.coerceValueToType(try sema.resolveInst(extra.layout), layout_ty);
    const layout = try sema.interpretStdLangEnum(std.lang.Type.ContainerLayout, layout_ty, layout_val, "union layout");

    const arg_val = try sema.coerceValueToType(try sema.resolveInst(extra.arg_ty), try ip.internOptionalType(.type_type));
    if (ip.indexToKey(arg_val.index) == .undef) {
        return sema.fail(sema.block, arg_ty_src, "use of undefined value here causes illegal behavior", .{});
    }
    const arg_ty = ip.indexToKey(arg_val.index).opt.val;
    var tag_type: InternPool.Index = .none;
    var backing_int: InternPool.Index = .none;
    if (arg_ty != .none) switch (layout) {
        .@"extern" => {
            return sema.fail(sema.block, arg_ty_src, "extern union does not support enum tag type", .{});
        },
        .@"packed" => backing_int = arg_ty,
        .auto => tag_type = arg_ty,
    };

    const names_slice = try sema.coerceValueToType(try sema.resolveInst(extra.field_names), try sema.sliceOfStringTy());
    const names_agg = ip.indexToKey((try sema.derefSliceAsArray(names_slice)).index).aggregate;
    const fields_len: u32 = @intCast(ip.indexToKey(names_agg.ty).array_type.len);

    const field_types_ty = try ip.internPtrType(.{
        .child = try ip.internArrayType(.{ .len = fields_len, .child = .type_type }),
        .flags = .{ .size = .one, .is_const = true },
    });
    const types_arr = try sema.derefSliceAsArray(try sema.coerceValueToType(try sema.resolveInst(extra.field_types), field_types_ty));
    const types_agg = ip.indexToKey(types_arr.index).aggregate;

    const attrs_scalar_ty = try sema.getStdLangType(.@"Type.Union.FieldAttributes");
    const field_attrs_ty = try ip.internPtrType(.{
        .child = try ip.internArrayType(.{ .len = fields_len, .child = attrs_scalar_ty }),
        .flags = .{ .size = .one, .is_const = true },
    });
    const attrs_arr = try sema.derefSliceAsArray(try sema.coerceValueToType(try sema.resolveInst(extra.field_attrs), field_attrs_ty));
    const attrs_agg = ip.indexToKey(attrs_arr.index).aggregate;

    const names = try sema.gpa.alloc(InternPool.NullTerminatedString, fields_len);
    defer sema.gpa.free(names);
    const types = try sema.gpa.alloc(InternPool.Index, fields_len);
    defer sema.gpa.free(types);
    const aligns = try sema.gpa.alloc(InternPool.Alignment, fields_len);
    defer sema.gpa.free(aligns);
    @memset(aligns, .none);
    var any_aligns = false;

    var hasher = std.hash.Wyhash.init(0);
    std.hash.autoHash(&hasher, layout);
    std.hash.autoHash(&hasher, arg_val.index);
    std.hash.autoHash(&hasher, types_arr.index);
    std.hash.autoHash(&hasher, attrs_arr.index);

    for (names, types, 0..) |*name_out, *type_out, i| {
        name_out.* = try sema.sliceToIpString(.{ .index = try ip.aggregateElementAt(names_agg, i) });
        type_out.* = try ip.aggregateElementAt(types_agg, i);
        if (ip.indexToKey(type_out.*) == .undef) {
            return sema.fail(sema.block, field_types_src, "use of undefined value here causes illegal behavior", .{});
        }
        const attr_elem = try ip.aggregateElementAt(attrs_agg, i);
        if (ip.indexToKey(attr_elem) == .undef) {
            return sema.fail(sema.block, field_attrs_src, "use of undefined value here causes illegal behavior", .{});
        }
        const align_opt = ip.indexToKey((try Value.fromIndex(attr_elem).fieldValue(comptime std.meta.fieldIndex(std.lang.Type.Union.FieldAttributes, "align").?, ip)).index).opt.val;
        if (align_opt != .none) {
            if (layout == .@"packed") {
                return sema.fail(sema.block, field_attrs_src, "packed union fields cannot be aligned", .{});
            }
            aligns[i] = try sema.alignmentFromValue(.{ .index = align_opt });
            any_aligns = true;
        }
        std.hash.autoHash(&hasher, name_out.*);
    }

    const name = switch (name_strategy) {
        .parent => sema.block.type_name_ctx,
        .anon, .func, .dbg_var => blk: {
            const ctx = ip.stringSlice(sema.block.type_name_ctx);
            const text = try std.fmt.allocPrint(sema.gpa, "{s}__union_{d}", .{ ctx, @backingInt(inst) });
            defer sema.gpa.free(text);
            break :blk try ip.getOrPutString(sema.gpa, text, .no_embedded_nulls);
        },
    };

    const tag_usage: InternPool.UnionFields.TagUsage = if (tag_type != .none)
        .tagged
    else switch (layout) {
        .auto => .safety,
        .@"extern", .@"packed" => .none,
    };

    const union_ty = try ip.getReifiedUnionType(.{
        .name = name,
        .id = .{ .reified = .{ .source_zir_id = sema.current_zir_id, .decl_inst = inst, .type_hash = hasher.final() } },
        .layout = layout,
        .tag_usage = tag_usage,
        .enum_tag_type = tag_type,
        .backing_int = backing_int,
        .names = names,
        .types = types,
        .aligns = if (any_aligns) aligns else &.{},
    });
    const fields = ip.unionFields(union_ty);
    fields.field_name_map.get(ip).clearRetainingCapacity();
    for (names, 0..) |field_name, field_index| {
        if (ip.addFieldName(names, fields.field_name_map, field_name)) |prev_field_index| {
            return sema.failWithOwnedErrorMsg(sema.block, msg: {
                const msg = try sema.errMsg(field_names_src, "duplicate union field '{f}' at index '{d}'", .{ field_name.fmt(ip), field_index });
                errdefer msg.destroy(sema.gpa);
                try sema.errNote(field_names_src, msg, "previous field at index '{d}'", .{prev_field_index});
                break :msg msg;
            });
        }
    }
    return .{ .index = union_ty };
}

fn evalArrayType(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const bin = sema.binData(inst);
    assert(bin.lhs != .none);
    assert(bin.rhs != .none);

    const len = try sema.resolveArrayLen(bin.lhs);
    const child = try sema.resolveDestType(bin.rhs);
    const array_ty = try sema.intern_pool.internArrayType(.{ .len = len, .child = child });
    return .{ .index = array_ty };
}

fn evalArrayTypeSentinel(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@backingInt(inst) < sema.zir.instructions.len);
    const pl_node = sema.zir.instructions.items(.data)[@backingInt(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.ArrayTypeSentinel, pl_node.payload_index).data;
    const len = try sema.resolveArrayLen(extra.len);
    const elem_type = try sema.resolveDestType(extra.elem_type);
    const uncasted_sentinel = try sema.resolveInst(extra.sentinel);
    const sentinel = try sema.coerceValueToType(uncasted_sentinel, elem_type);
    if (sema.intern_pool.indexToKey(sentinel.index) == .undef) {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "use of undefined value here causes illegal behavior", .{});
    }
    const array_ty = try sema.intern_pool.internArrayType(.{
        .len = len,
        .sentinel = sentinel.index,
        .child = elem_type,
    });
    try sema.checkSentinelType(elem_type);
    return .{ .index = array_ty };
}

fn checkSentinelType(sema: *Sema, elem_type: InternPool.Index) Error!void {
    if (!Type.fromIndex(elem_type).isSelfComparable(sema.intern_pool, true)) {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "non-scalar sentinel type '{f}'", .{Type.fromIndex(elem_type).fmt(sema.intern_pool)});
    }
}

fn evalVectorType(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const bin = sema.binData(inst);
    assert(bin.lhs != .none);
    assert(bin.rhs != .none);

    const len64 = try sema.resolveArrayLen(bin.lhs);
    const len = std.math.cast(u32, len64) orelse {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "vector_type: length {d} exceeds u32", .{len64});
    };
    const child = try sema.resolveDestType(bin.rhs);
    if (!isVectorElemType(sema.intern_pool, child)) {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "expected integer, float, bool, or pointer for the vector element type; found '{f}'", .{Type.fromIndex(child).fmt(sema.intern_pool)});
    }
    const vector_ty = try sema.intern_pool.internVectorType(.{ .len = len, .child = child });
    return .{ .index = vector_ty };
}

fn evalSelect(sema: *Sema, extended: Zir.Inst.Extended.InstData) Error!?Value {
    const ip = sema.intern_pool;
    const extra = sema.zir.extraData(Zir.Inst.Select, extended.operand).data;

    const elem_ty = try sema.resolveDestType(extra.elem_type);
    if (!isVectorElemType(ip, elem_ty)) {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "@select: expected integer, float, bool, or pointer for the element type", .{});
    }
    const pred = try sema.resolveInst(extra.pred);
    const pred_ty = Value.typeOf(pred, ip);
    switch (pred_ty.zigTypeTag(ip)) {
        .array, .vector => {},
        else => return sema.fail(sema.block, sema.block.nodeOffset(.zero), "@select: expected vector or array for the predicate", .{}),
    }
    const vec_len = pred_ty.arrayLen(ip);

    const vec_ty = try ip.internVectorType(.{ .len = @intCast(vec_len), .child = elem_ty });
    const a_agg = ip.indexToKey((try sema.coerceValueToType(try sema.resolveInst(extra.a), vec_ty)).index).aggregate;
    const b_agg = ip.indexToKey((try sema.coerceValueToType(try sema.resolveInst(extra.b), vec_ty)).index).aggregate;
    const pred_agg = ip.indexToKey(pred.index).aggregate;

    const elems = try sema.gpa.alloc(InternPool.Index, @intCast(vec_len));
    defer sema.gpa.free(elems);
    for (elems, 0..) |*e, i| {
        const chosen = if (try ip.aggregateElementAt(pred_agg, i) == .bool_true) a_agg else b_agg;
        e.* = try ip.aggregateElementAt(chosen, i);
    }
    return .{ .index = try ip.internAggregate(.{ .ty = vec_ty, .storage = .{ .elems = elems } }) };
}

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

fn evalOptionalType(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@backingInt(inst) < sema.zir.instructions.len);

    const un_node = sema.zir.instructions.items(.data)[@backingInt(inst)].un_node;
    const child = try sema.resolveDestType(un_node.operand);
    const opt_ty = try sema.intern_pool.internOptionalType(child);
    return .{ .index = opt_ty };
}

fn evalOptionalPayload(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@backingInt(inst) < sema.zir.instructions.len);

    const un_node = sema.zir.instructions.items(.data)[@backingInt(inst)].un_node;
    const operand = try sema.resolveInst(un_node.operand);
    const key = sema.intern_pool.indexToKey(operand.index);
    if (key != .opt) {
        return sema.failWithExpectedOptionalType(sema.block.nodeOffset(sema.srcNodeOffset(inst)), operand.typeOf(sema.intern_pool));
    }
    if (key.opt.val == .none) {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "unable to unwrap null", .{});
    }
    return .{ .index = key.opt.val };
}

fn evalOptionalPayloadPtr(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@backingInt(inst) < sema.zir.instructions.len);
    const un_node = sema.zir.instructions.items(.data)[@backingInt(inst)].un_node;
    return try sema.optPayloadPtr(try sema.resolveInst(un_node.operand), false);
}

fn optPayloadPtr(sema: *Sema, optional_ptr: Value, comptime initializing: bool) Error!Value {
    const ip = sema.intern_pool;
    const ptr_type = ip.indexToKey(optional_ptr.typeOf(ip).toIndex()).ptr_type;
    const opt_key = ip.indexToKey(ptr_type.child);
    if (opt_key != .opt_type) {
        return sema.failWithExpectedOptionalType(sema.block.nodeOffset(.zero), .fromIndex(ptr_type.child));
    }
    if (!initializing) {
        const opt_val = try sema.loadValue(optional_ptr);
        if (ip.indexToKey(opt_val.index).opt.val == .none) {
            return sema.fail(sema.block, sema.block.nodeOffset(.zero), "unable to unwrap null", .{});
        }
    } else {
        // Set the optional to non-null at comptime before returning the payload pointer, so stores
        // into the payload have somewhere to land. Use the payload's OPV if it has one, else undef.
        const child_type: Type = .fromIndex(opt_key.opt_type);
        const payload_val = (try child_type.onePossibleValue(sema)) orelse try sema.undefValue(child_type);
        const opt_val: Value = .fromIndex(try ip.internOpt(.{ .ty = ptr_type.child, .val = payload_val.index }));
        try sema.storePtrVal(optional_ptr, opt_val);
    }
    const child_ptr_ty = try ip.internPtrType(.{ .child = opt_key.opt_type, .sentinel = ptr_type.sentinel, .flags = ptr_type.flags });
    return .{ .index = try ip.internPtr(.{
        .ty = child_ptr_ty,
        .base_addr = .{ .opt_payload = optional_ptr.index },
        .byte_offset = 0,
    }) };
}

fn evalIsNonNull(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@backingInt(inst) < sema.zir.instructions.len);
    const un_node = sema.zir.instructions.items(.data)[@backingInt(inst)].un_node;
    return try sema.isNonNullVal(try sema.resolveInst(un_node.operand));
}

fn evalIsNonNullPtr(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@backingInt(inst) < sema.zir.instructions.len);
    const un_node = sema.zir.instructions.items(.data)[@backingInt(inst)].un_node;
    return try sema.isNonNullVal(try sema.loadValue(try sema.resolveInst(un_node.operand)));
}

fn isNonNullVal(sema: *Sema, operand: Value) Error!Value {
    const ip = sema.intern_pool;
    const key = ip.indexToKey(operand.index);
    if (key != .opt) {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "expected optional type, found '{f}'", .{operand.typeOf(ip).fmt(ip)});
    }
    return .{ .index = if (key.opt.val == .none) .bool_false else .bool_true };
}

fn evalArrayInit(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    return .{ .index = try sema.buildArrayAggregate(inst) };
}

fn evalArrayInitRef(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const agg = try sema.buildArrayAggregate(inst);
    return try sema.materializeConstPtr(.{ .index = agg });
}

fn evalArrayInitAnon(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@backingInt(inst) < sema.zir.instructions.len);
    const pl_node = sema.zir.instructions.items(.data)[@backingInt(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.MultiOp, pl_node.payload_index);
    const operands = sema.zir.refSlice(extra.end, extra.data.operands_len);
    return .{ .index = try sema.arrayInitAnon(operands) };
}

/// Build an anonymous tuple aggregate from the operand values -- used for `array_init_anon` and
/// when `array_init`'s result type is generic (`anytype`). Mirrors the compiler's `arrayInitAnon`.
fn arrayInitAnon(sema: *Sema, operands: []const Zir.Inst.Ref) Error!InternPool.Index {
    const ip = sema.intern_pool;
    const types = try sema.gpa.alloc(InternPool.Index, operands.len);
    defer sema.gpa.free(types);
    const values = try sema.gpa.alloc(InternPool.Index, operands.len);
    defer sema.gpa.free(values);
    const field_vals = try sema.gpa.alloc(InternPool.Index, operands.len);
    defer sema.gpa.free(field_vals);

    for (operands, types, values, field_vals) |operand, *ty, *val, *fv| {
        const elem = try sema.resolveInst(operand);
        ty.* = Value.typeOf(elem, ip).index;
        val.* = elem.index;
        // A field whose value is comptime-known is a comptime field of the tuple type.
        fv.* = if (elem.is_comptime) elem.index else .none;
    }

    const tuple_ty = try ip.internTupleType(types, field_vals);
    return try ip.internAggregate(.{ .ty = tuple_ty, .storage = .{ .elems = values } });
}

const ArrayCatInfo = struct { elem_type: Type, sentinel: InternPool.Index, len: u64, array: Value };

fn getArrayCatInfo(sema: *Sema, operand: Value) Error!?ArrayCatInfo {
    const ip = sema.intern_pool;
    const operand_ty = operand.typeOf(ip);
    switch (operand_ty.zigTypeTag(ip)) {
        .array => {
            const ai = operand_ty.arrayInfo(ip);
            return .{ .elem_type = ai.elem_type, .sentinel = ai.sentinel orelse .none, .len = ai.len, .array = operand };
        },
        .pointer => {
            const ptr_info = ip.indexToKey(operand_ty.index).ptr_type;
            switch (ptr_info.flags.size) {
                .slice => {
                    // A comptime-known slice supplies its length from the value; index its backing array.
                    const arr = try sema.derefSliceAsArray(operand);
                    const len = try sema.resolveUsizeInt(.{ .index = ip.indexToKey(operand.index).slice.len });
                    return .{ .elem_type = .fromIndex(ptr_info.child), .sentinel = ptr_info.sentinel, .len = len, .array = arr };
                },
                .one => {
                    if (Type.fromIndex(ptr_info.child).zigTypeTag(ip) == .array) {
                        const ai = Type.fromIndex(ptr_info.child).arrayInfo(ip);
                        return .{ .elem_type = ai.elem_type, .sentinel = ai.sentinel orelse .none, .len = ai.len, .array = try sema.loadValue(operand) };
                    }
                },
                .c, .many => {},
            }
        },
        else => {},
    }
    return null;
}

fn evalArrayCat(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    const bin = sema.binData(inst);
    const lhs = try sema.resolveInst(bin.lhs);
    const rhs = try sema.resolveInst(bin.rhs);
    const lhs_ty = lhs.typeOf(ip);
    const rhs_ty = rhs.typeOf(ip);
    const src = sema.block.nodeOffset(sema.srcNodeOffset(inst));

    if (lhs_ty.isTuple(ip) and rhs_ty.isTuple(ip)) return try sema.analyzeTupleCat(lhs, rhs);

    const lhs_info = (try sema.getArrayCatInfo(lhs)) orelse
        return sema.fail(sema.block, src, "expected indexable; found '{f}'", .{lhs_ty.fmt(ip)});
    const rhs_info = (try sema.getArrayCatInfo(rhs)) orelse
        return sema.fail(sema.block, src, "expected indexable; found '{f}'", .{rhs_ty.fmt(ip)});

    if (lhs_info.elem_type.index != rhs_info.elem_type.index) {
        return sema.fail(sema.block, src, "array concatenation requires matching element types, found '{f}' and '{f}'", .{ lhs_info.elem_type.fmt(ip), rhs_info.elem_type.fmt(ip) });
    }
    const elem_ty = lhs_info.elem_type;

    // With a sentinel mismatch the result has no sentinel; otherwise use whichever operand supplies one.
    const sentinel: InternPool.Index = blk: {
        if (lhs_info.sentinel != .none and rhs_info.sentinel != .none)
            break :blk if (lhs_info.sentinel == rhs_info.sentinel) lhs_info.sentinel else .none;
        if (lhs_info.sentinel != .none) break :blk lhs_info.sentinel;
        break :blk rhs_info.sentinel;
    };

    const result_len = lhs_info.len + rhs_info.len;
    const result_ty = try ip.internArrayType(.{ .len = result_len, .child = elem_ty.index, .sentinel = sentinel });

    const elems = try sema.gpa.alloc(InternPool.Index, @intCast(result_len));
    defer sema.gpa.free(elems);
    const lhs_agg = ip.indexToKey(lhs_info.array.index).aggregate;
    const rhs_agg = ip.indexToKey(rhs_info.array.index).aggregate;
    var i: u64 = 0;
    while (i < lhs_info.len) : (i += 1) elems[@intCast(i)] = try ip.aggregateElementAt(lhs_agg, i);
    while (i < result_len) : (i += 1) elems[@intCast(i)] = try ip.aggregateElementAt(rhs_agg, i - lhs_info.len);

    const agg: Value = .{ .index = try ip.internAggregate(.{ .ty = result_ty, .storage = .{ .elems = elems } }) };
    // Concatenating pointer operands (e.g. string literals) yields a pointer to the result, like a literal.
    if (lhs_ty.zigTypeTag(ip) == .pointer or rhs_ty.zigTypeTag(ip) == .pointer)
        return try sema.materializeConstPtr(agg);
    return agg;
}

fn analyzeTupleCat(sema: *Sema, lhs: Value, rhs: Value) Error!Value {
    const ip = sema.intern_pool;
    const lhs_tuple = ip.indexToKey(lhs.typeOf(ip).index).tuple_type;
    const rhs_tuple = ip.indexToKey(rhs.typeOf(ip).index).tuple_type;
    const total = lhs_tuple.types.len + rhs_tuple.types.len;

    const types = try sema.gpa.alloc(InternPool.Index, total);
    defer sema.gpa.free(types);
    const values = try sema.gpa.alloc(InternPool.Index, total);
    defer sema.gpa.free(values);

    const lhs_agg = ip.indexToKey(lhs.index).aggregate;
    const rhs_agg = ip.indexToKey(rhs.index).aggregate;
    for (lhs_tuple.types, 0..) |t, i| {
        types[i] = t;
        values[i] = try ip.aggregateElementAt(lhs_agg, i);
    }
    for (rhs_tuple.types, 0..) |t, i| {
        types[lhs_tuple.types.len + i] = t;
        values[lhs_tuple.types.len + i] = try ip.aggregateElementAt(rhs_agg, i);
    }

    const field_vals = try sema.gpa.alloc(InternPool.Index, total);
    defer sema.gpa.free(field_vals);
    @memset(field_vals, .none);
    const tuple_ty = try ip.internTupleType(types, field_vals);
    return .{ .index = try ip.internAggregate(.{ .ty = tuple_ty, .storage = .{ .elems = values } }) };
}

fn evalStructInitAnon(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@backingInt(inst) < sema.zir.instructions.len);
    const ip = sema.intern_pool;
    const pl_node = sema.zir.instructions.items(.data)[@backingInt(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.StructInitAnon, pl_node.payload_index);

    const fields_len = extra.data.fields_len;
    const types = try sema.gpa.alloc(InternPool.Index, fields_len);
    defer sema.gpa.free(types);
    const values = try sema.gpa.alloc(InternPool.Index, fields_len);
    defer sema.gpa.free(values);
    const names = try sema.gpa.alloc(InternPool.NullTerminatedString, fields_len);
    defer sema.gpa.free(names);

    var extra_index = extra.end;
    for (types, values, names) |*field_ty, *field_val, *field_name| {
        const item = sema.zir.extraData(Zir.Inst.StructInitAnon.Item, extra_index);
        extra_index = item.end;
        field_name.* = try ip.getOrPutString(sema.gpa, sema.zir.nullTerminatedString(item.data.field_name), .no_embedded_nulls);
        const init = try sema.resolveInst(item.data.init);
        field_val.* = init.index;
        field_ty.* = init.typeOf(ip).index;
    }

    // The compiler treats anon struct types as reified: fields are stored eagerly, and every
    // comptime-known field is a comptime field with its value as the default. The REPL is
    // comptime-only, so every field value is known and every field is comptime.
    const comptime_words = try sema.gpa.alloc(u32, (fields_len + 31) / 32);
    defer sema.gpa.free(comptime_words);
    @memset(comptime_words, 0);
    var i: u32 = 0;
    while (i < fields_len) : (i += 1) comptime_words[i / 32] |= @as(u32, 1) << @intCast(i % 32);

    var hasher = std.hash.Wyhash.init(0);
    hasher.update(std.mem.sliceAsBytes(types));
    hasher.update(std.mem.sliceAsBytes(values));
    hasher.update(std.mem.sliceAsBytes(names));

    const ctx = ip.stringSlice(sema.block.type_name_ctx);
    const name_text = try std.fmt.allocPrint(sema.gpa, "{s}__struct_{d}", .{ ctx, @backingInt(inst) });
    defer sema.gpa.free(name_text);
    const struct_ty = try ip.getReifiedStructType(.{
        .name = try ip.getOrPutString(sema.gpa, name_text, .no_embedded_nulls),
        .id = .{ .reified = .{ .source_zir_id = sema.current_zir_id, .decl_inst = inst, .type_hash = hasher.final() } },
        .layout = .auto,
        .backing_int = .none,
        .names = names,
        .types = types,
        .defaults = values,
        .aligns = &.{},
        .comptime_bits = comptime_words,
    });
    const fields = ip.loadStructType(struct_ty);
    fields.field_name_map.get(ip).clearRetainingCapacity();
    for (names, 0..) |field_name, field_index| {
        if (ip.addFieldName(names, fields.field_name_map, field_name)) |prev_field_index| {
            return sema.failWithOwnedErrorMsg(sema.block, msg: {
                const src = sema.block.nodeOffset(sema.srcNodeOffset(inst));
                const msg = try sema.errMsg(src, "duplicate struct field '{f}' at index '{d}'", .{ field_name.fmt(ip), field_index });
                errdefer msg.destroy(sema.gpa);
                try sema.errNote(src, msg, "previous field at index '{d}'", .{prev_field_index});
                break :msg msg;
            });
        }
    }
    return .{ .index = try ip.internAggregate(.{ .ty = struct_ty, .storage = .{ .elems = values } }) };
}

fn evalImport(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const inst_data = sema.zir.instructions.items(.data)[@backingInt(inst)].pl_tok;
    const extra = sema.zir.extraData(Zir.Inst.Import, inst_data.payload_index).data;
    return .{ .index = try sema.importPath(sema.zir.nullTerminatedString(extra.path)) };
}

fn importPath(sema: *Sema, path: []const u8) Error!InternPool.Index {
    if (std.mem.eql(u8, path, "std")) return sema.loadModuleFile("std.zig");
    if (std.mem.eql(u8, path, "root")) return sema.rootModuleType();
    if (std.mem.eql(u8, path, "builtin")) return sema.loadBuiltinModule("builtin");

    if (std.mem.endsWith(u8, path, ".zig")) {
        // A REPL line has no path of its own; anchor its relative imports at the
        // source root, so the prompt resolves project files as the main module would.
        const importer = sema.importerSubPath() orelse "";
        const anchored = try std.fs.path.resolvePosix(sema.gpa, &.{ "/", importer, "..", path });
        defer sema.gpa.free(anchored);
        return sema.loadModuleFile(anchored[1..]);
    }

    return sema.fail(sema.block, sema.block.nodeOffset(.zero), "no module named '{s}' available", .{path});
}

fn failUnloadedModule(sema: *Sema, path: []const u8) Error {
    return sema.fail(sema.block, sema.block.nodeOffset(.zero), "@import(\"{s}\"): module loading is not supported", .{path});
}

fn rootModuleType(sema: *Sema) Error!InternPool.Index {
    const session = sema.session orelse return sema.failUnloadedModule("root");
    if (session.root_file) |file_index| return session.files.items[file_index].root_type;
    const file_index: Session.Index = @intCast(session.files.items.len);
    try session.files.append(sema.gpa, .{ .zir = null, .tree = null, .wrapped = null, .sub_file_path = null });
    const ty = switch (try sema.intern_pool.getDeclaredStructType(
        try sema.intern_pool.getOrPutString(sema.gpa, "root", .no_embedded_nulls),
        .{ .declared = .{ .source_zir_id = file_index, .decl_inst = .main_struct_inst } },
        0,
        .auto,
        false,
        false,
    )) {
        .existing => |e| e,
        .wip => |wip| wip.index,
    };
    sema.intern_pool.setNamespace(ty, session.root_namespace);
    session.files.items[file_index].root_type = ty;
    session.root_file = file_index;
    return ty;
}

fn importerSubPath(sema: *Sema) ?[]const u8 {
    const session = sema.session orelse return null;
    if (sema.current_zir_id >= session.files.items.len) return null;
    return session.files.items[sema.current_zir_id].sub_file_path;
}

fn loadModuleFile(sema: *Sema, canonical: []const u8) Error!InternPool.Index {
    const session = sema.session orelse return sema.failUnloadedModule(canonical);
    if (session.import_table.get(canonical)) |idx| return session.files.items[idx].root_type;
    const source = session.module_source orelse return sema.failUnloadedModule(canonical);

    const bytes = source.read(sema.gpa, canonical) catch |err| {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "@import(\"{s}\"): {s}", .{ canonical, @errorName(err) });
    };
    defer sema.gpa.free(bytes);
    return sema.lowerModule(canonical, bytes);
}

pub fn lowerModule(sema: *Sema, canonical: []const u8, bytes: [:0]const u8) Error!InternPool.Index {
    const session = sema.session.?;
    var tree = try std.zig.Ast.parse(sema.gpa, bytes, .{ .mode = .zig });
    defer tree.deinit(sema.gpa);
    var zir = try std.zig.AstGen.generate(sema.gpa, tree);
    if (zir.hasCompileErrors()) {
        zir.deinit(sema.gpa);
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "@import(\"{s}\"): source did not compile", .{canonical});
    }

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

    // A file whose root is a struct-with-fields (e.g. std/Target.zig) needs its field count set here,
    // just like any other struct decl; a namespace-only file's root simply has zero fields.
    const root_decl = zir.getStructDecl(.main_struct_inst);
    var any_field_aligns = false;
    var any_comptime_fields = false;
    var it = root_decl.iterateFields();
    while (it.next()) |field| {
        if (field.align_body != null) any_field_aligns = true;
        if (field.is_comptime) any_comptime_fields = true;
    }

    const root_type = switch (try sema.intern_pool.getDeclaredStructType(
        try sema.moduleTypeName(canonical),
        .{ .declared = .{ .source_zir_id = file_index, .decl_inst = .main_struct_inst } },
        @intCast(root_decl.field_names.len),
        .auto,
        any_field_aligns,
        any_comptime_fields,
    )) {
        .existing => |e| e,
        .wip => |wip| wip.index,
    };
    const root_ns = try sema.intern_pool.createNamespace(sema.gpa, .{
        .parent = .none,
        .owner_type = root_type,
        .file_scope = sema.namespaceFileScope(file_index),
    });
    sema.intern_pool.setNamespace(root_type, root_ns);
    session.files.items[file_index].root_type = root_type;
    return root_type;
}

fn loadBuiltinModule(sema: *Sema, canonical: []const u8) Error!InternPool.Index {
    const session = sema.session orelse return sema.failUnloadedModule(canonical);
    if (session.import_table.get(canonical)) |idx| return session.files.items[idx].root_type;
    if (session.module_source == null) return sema.failUnloadedModule(canonical);

    const bytes = try @import("Builtin.zig").generate(sema.gpa);
    defer sema.gpa.free(bytes);
    return sema.lowerModule(canonical, bytes);
}

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
    const name_nts = try sema.intern_pool.getOrPutString(sema.gpa, name, .no_embedded_nulls);
    const v = (try sema.containerDeclByName(container_ty, name_nts)) orelse {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "std.lang: missing declaration '{s}'", .{name});
    };
    return v.index;
}

fn resolveStdLangEnum(sema: *Sema, comptime decl: StdLangDecl, ref: Zir.Inst.Ref) Error!@field(std.lang, @tagName(decl)) {
    const E = @field(std.lang, @tagName(decl));
    const enum_ty = try sema.getStdLangType(decl);
    const val = try sema.coerceValueToType(try sema.resolveInst(ref), enum_ty);
    return sema.interpretStdLangEnum(E, enum_ty, val, @tagName(decl));
}

fn interpretStdLangEnum(sema: *Sema, comptime E: type, enum_ty: InternPool.Index, val: Value, ctx: []const u8) Error!E {
    const idx = (try sema.enumTagFieldIndex(enum_ty, val)).?;
    const name = sema.intern_pool.stringSlice((try sema.enumFieldName(enum_ty, idx)).?);
    return std.meta.stringToEnum(E, name) orelse {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "{s}: unknown variant '{s}'", .{ ctx, name });
    };
}

fn evalStdLangValue(sema: *Sema, extended: Zir.Inst.Extended.InstData) Error!?Value {
    const value: Zir.Inst.StdLangValue = @fromBackingInt(@intCast(extended.small));
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

        .calling_convention_c => {
            const cc_ty = try sema.getStdLangType(.CallingConvention);
            const name = try sema.intern_pool.getOrPutString(sema.gpa, "c", .no_embedded_nulls);
            return (try sema.containerDeclByName(cc_ty, name)) orelse {
                return sema.fail(sema.block, sema.block.nodeOffset(.zero), "std.lang is corrupt: CallingConvention.c", .{});
            };
        },
        .calling_convention_inline => return try sema.uninterpretStdLangType(@as(std.lang.CallingConvention, .@"inline"), .fromIndex(try sema.getStdLangType(.CallingConvention))),
    };
    return .{ .index = try sema.getStdLangType(std_lang_type) };
}

fn evalTypeInfo(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    const un_node = sema.zir.instructions.items(.data)[@backingInt(inst)].un_node;
    const ty = (try sema.resolveInst(un_node.operand)).index;

    const type_info_ty = try sema.getStdLangType(.Type);
    const tag_enum = try sema.unionTagEnumType(type_info_ty);

    if (Type.fromIndex(ty).zigTypeTag(ip) == .int) {
        const it = Type.fromIndex(ty).intInfo(ip);
        const int_info_ty = try sema.getStdLangType(.@"Type.Int");
        const signedness_ty = try sema.getStdLangType(.Signedness);
        const sign_idx = (try sema.enumFieldIndex(signedness_ty, try ip.getOrPutString(sema.gpa, @tagName(it.signedness), .no_embedded_nulls))).?;
        const sign_val = (try sema.enumValueFieldIndex(signedness_ty, sign_idx)).?;
        const bits_val = try ip.internInt(.{ .ty = .u16_type, .storage = .{ .u64 = it.bits } });
        var elems = [_]InternPool.Index{ sign_val.index, bits_val };
        const payload = try ip.internAggregate(.{ .ty = int_info_ty, .storage = .{ .elems = &elems } });
        return try sema.typeInfoUnion(type_info_ty, tag_enum, "int", payload);
    }

    switch (ip.indexToKey(ty)) {
        .simple_type => |s| switch (s) {
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
            .void, .bool, .type, .noreturn, .comptime_int, .comptime_float, .undefined, .null, .enum_literal => {
                return try sema.typeInfoUnion(type_info_ty, tag_enum, @tagName(s), .void_value);
            },
            .anyerror => return try sema.typeInfoErrorSet(null),
            else => return sema.failTypeInfoUnsupported(ty),
        },
        .opt_type => |child| {
            const opt_ty = try sema.getStdLangType(.@"Type.Optional");
            var elems = [_]InternPool.Index{child};
            return try sema.typeInfoUnion(type_info_ty, tag_enum, "optional", try ip.internAggregate(.{ .ty = opt_ty, .storage = .{ .elems = &elems } }));
        },
        .vector_type => |vec| {
            const vec_ty = try sema.getStdLangType(.@"Type.Vector");
            var elems = [_]InternPool.Index{
                try ip.internInt(.{ .ty = .comptime_int_type, .storage = .{ .u64 = vec.len } }),
                vec.child,
            };
            return try sema.typeInfoUnion(type_info_ty, tag_enum, "vector", try ip.internAggregate(.{ .ty = vec_ty, .storage = .{ .elems = &elems } }));
        },
        .array_type => |arr| {
            const array_ty = try sema.getStdLangType(.@"Type.Array");
            var elems = [_]InternPool.Index{
                try ip.internInt(.{ .ty = .comptime_int_type, .storage = .{ .u64 = arr.len } }),
                arr.child,
                try sema.optRefValue(arr.sentinel),
            };
            return try sema.typeInfoUnion(type_info_ty, tag_enum, "array", try ip.internAggregate(.{ .ty = array_ty, .storage = .{ .elems = &elems } }));
        },
        .ptr_type => |p| {
            const pointer_ty = try sema.getStdLangType(.@"Type.Pointer");
            const size_ty = try sema.getStdLangType(.@"Type.Pointer.Size");
            const attrs_ty = try sema.getStdLangType(.@"Type.Pointer.Attributes");
            const addrspace_ty = try sema.getStdLangType(.AddressSpace);

            const opt_addrspace = try ip.internOpt(.{
                .ty = try ip.internOptionalType(addrspace_ty),
                .val = (try sema.enumValueFieldIndex(addrspace_ty, @backingInt(p.flags.address_space))).?.index,
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
                (try sema.enumValueFieldIndex(size_ty, @backingInt(p.flags.size))).?.index,
                try ip.internAggregate(.{ .ty = attrs_ty, .storage = .{ .elems = &attr_elems } }),
                p.child,
                try sema.optRefValue(p.sentinel),
            };
            return try sema.typeInfoUnion(type_info_ty, tag_enum, "pointer", try ip.internAggregate(.{ .ty = pointer_ty, .storage = .{ .elems = &elems } }));
        },
        .error_union_type => |eu| {
            const eu_ty = try sema.getStdLangType(.@"Type.ErrorUnion");
            var elems = [_]InternPool.Index{ eu.error_set_type, eu.payload_type };
            return try sema.typeInfoUnion(type_info_ty, tag_enum, "error_union", try ip.internAggregate(.{ .ty = eu_ty, .storage = .{ .elems = &elems } }));
        },
        .error_set_type => return try sema.typeInfoErrorSet(ty),
        .enum_type => {
            const enum_std_ty = try sema.getStdLangType(.@"Type.Enum");
            const mode_ty = try sema.getStdLangType(.@"Type.Enum.Mode");

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
            const mode_idx = (try sema.enumFieldIndex(mode_ty, try ip.getOrPutString(sema.gpa, mode_name, .no_embedded_nulls))).?;
            const mode_val = (try sema.enumValueFieldIndex(mode_ty, mode_idx)).?;

            var elems = [_]InternPool.Index{ try sema.enumIntTagTypeOf(ty), mode_val.index, field_names_val, field_values_val, decl_names_val };
            return try sema.typeInfoUnion(type_info_ty, tag_enum, "enum", try ip.internAggregate(.{ .ty = enum_std_ty, .storage = .{ .elems = &elems } }));
        },
        .union_type => {
            const union_std_ty = try sema.getStdLangType(.@"Type.Union");
            const attrs_ty = try sema.getStdLangType(.@"Type.Union.FieldAttributes");
            const layout_ty = try sema.getStdLangType(.@"Type.ContainerLayout");

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

            try sema.resolveUnionFields(ty);
            const uf = ip.unionFields(ty);
            const layout_val = (try sema.enumValueFieldIndex(layout_ty, @backingInt(uf.layout))).?;
            const tag_type_val = try sema.optTypeValue(switch (uf.tag_usage) {
                .tagged => try sema.unionTagEnumType(ty),
                .none, .safety => .none,
            });
            const backing_integer_val = try sema.optTypeValue(uf.packed_backing_int_type);

            var elems = [_]InternPool.Index{ layout_val.index, tag_type_val, backing_integer_val, field_names_val, field_types_val, field_attrs_val, decl_names_val };
            return try sema.typeInfoUnion(type_info_ty, tag_enum, "union", try ip.internAggregate(.{ .ty = union_std_ty, .storage = .{ .elems = &elems } }));
        },
        .struct_type, .tuple_type => {
            const struct_std_ty = try sema.getStdLangType(.@"Type.Struct");
            const attrs_ty = try sema.getStdLangType(.@"Type.Struct.FieldAttributes");
            const layout_ty = try sema.getStdLangType(.@"Type.ContainerLayout");
            const tuple_types: ?[]const InternPool.Index = switch (ip.indexToKey(ty)) {
                .tuple_type => |tt| try sema.gpa.dupe(InternPool.Index, tt.types),
                else => null,
            };
            defer if (tuple_types) |t| sema.gpa.free(t);

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
                    name.* = try ip.getOrPutString(sema.gpa, std.fmt.bufPrint(&buf, "{d}", .{i}) catch unreachable, .no_embedded_nulls);
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

            const sf: ?InternPool.LoadedStructType = if (tuple_types == null and ip.indexToKey(ty).struct_type == .reified) ip.loadStructType(ty) else null;
            const layout = if (sf) |f| f.layout else .auto;
            const layout_val = (try sema.enumValueFieldIndex(layout_ty, @backingInt(layout))).?;
            const backing_integer_val = try sema.optTypeValue(if (sf) |f| f.packed_backing_int_type else .none);

            var elems = [_]InternPool.Index{ if (tuple_types != null) .bool_true else .bool_false, layout_val.index, backing_integer_val, field_names_val, field_types_val, field_attrs_val, decl_names_val };
            return try sema.typeInfoUnion(type_info_ty, tag_enum, "struct", try ip.internAggregate(.{ .ty = struct_std_ty, .storage = .{ .elems = &elems } }));
        },
        .func_type => |ft| {
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
                (try sema.uninterpretStdLangType(ft.cc, .fromIndex(try sema.getStdLangType(.CallingConvention)))).index,
                if (ft.is_var_args) .bool_true else .bool_false,
            };
            const attrs_val = try ip.internAggregate(.{ .ty = fn_attr_ty, .storage = .{ .elems = &attr_elems } });

            var elems = [_]InternPool.Index{ attrs_val, if (func_is_generic) .bool_true else .bool_false, return_type_val, param_types_val, param_attrs_val };
            return try sema.typeInfoUnion(type_info_ty, tag_enum, "fn", try ip.internAggregate(.{ .ty = fn_std_ty, .storage = .{ .elems = &elems } }));
        },
        else => return sema.failTypeInfoUnsupported(ty),
    }
}

fn uavPtr(sema: *Sema, ptr_ty: InternPool.Index, val: InternPool.Index) Error!InternPool.Index {
    return try sema.intern_pool.internPtr(.{
        .ty = ptr_ty,
        .base_addr = .{ .uav = .{ .val = val, .orig_ty = ptr_ty } },
        .byte_offset = 0,
    });
}

fn optRefValue(sema: *Sema, val: InternPool.Index) Error!InternPool.Index {
    const ip = sema.intern_pool;
    const ptr_ty = try ip.internPtrType(.{ .child = .anyopaque_type, .flags = .{ .size = .one, .is_const = true } });
    const opt_ty = try ip.internOptionalType(ptr_ty);
    const payload: InternPool.Index = if (val == .none) .none else try sema.uavPtr(ptr_ty, val);
    return try ip.internOpt(.{ .ty = opt_ty, .val = payload });
}

fn internConstSlice(sema: *Sema, child: InternPool.Index, elems: []const InternPool.Index) Error!InternPool.Index {
    const ip = sema.intern_pool;
    const array_ty = try ip.internArrayType(.{ .len = elems.len, .child = child });
    const array_val = try ip.internAggregate(.{ .ty = array_ty, .storage = .{ .elems = elems } });
    const slice_ty = try ip.internPtrType(.{ .child = child, .flags = .{ .size = .slice, .is_const = true } });
    const manyptr_ty = try ip.internPtrType(.{ .child = child, .flags = .{ .size = .many, .is_const = true } });
    const ptr = try sema.uavPtr(manyptr_ty, array_val);
    return try ip.get(.{ .slice = .{ .ty = slice_ty, .ptr = ptr, .len = try ip.internInt(.{ .ty = .usize_type, .storage = .{ .u64 = elems.len } }) } });
}

fn sliceConstU8SentinelTy(sema: *Sema) Error!InternPool.Index {
    const ip = sema.intern_pool;
    const u8_zero = try ip.internInt(.{ .ty = .u8_type, .storage = .{ .u64 = 0 } });
    return try ip.internPtrType(.{ .child = .u8_type, .sentinel = u8_zero, .flags = .{ .size = .slice, .is_const = true } });
}

fn sliceConstTypeTy(sema: *Sema) Error!InternPool.Index {
    return try sema.intern_pool.internPtrType(.{ .child = .type_type, .flags = .{ .size = .slice, .is_const = true } });
}

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
            try names.append(sema.gpa, try ip.getOrPutString(sema.gpa, sema.zir.nullTerminatedString(unwrapped.name), .no_embedded_nulls));
        }
    }
    return try sema.internStringSlice(names.items);
}

fn typeInfoErrorSet(sema: *Sema, err_ty: ?InternPool.Index) Error!?Value {
    const ip = sema.intern_pool;
    const type_info_ty = try sema.getStdLangType(.Type);
    const tag_enum = try sema.unionTagEnumType(type_info_ty);
    const error_set_ty = try sema.getStdLangType(.@"Type.ErrorSet");

    const slice_u8_ty = try sema.sliceConstU8SentinelTy();
    const slice_errors_ty = try ip.internPtrType(.{ .child = slice_u8_ty, .flags = .{ .size = .slice, .is_const = true } });
    const opt_slice_errors_ty = try ip.internOptionalType(slice_errors_ty);

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
    return sema.fail(sema.block, sema.block.nodeOffset(.zero), "@typeInfo: unsupported type '{f}'", .{Type.fromIndex(ty).fmt(sema.intern_pool)});
}

fn typeInfoUnion(sema: *Sema, type_info_ty: InternPool.Index, tag_enum: InternPool.Index, tag_name: []const u8, payload: InternPool.Index) Error!?Value {
    const tag_idx = (try sema.enumFieldIndex(tag_enum, try sema.intern_pool.getOrPutString(sema.gpa, tag_name, .no_embedded_nulls))).?;
    const tag = (try sema.enumValueFieldIndex(tag_enum, tag_idx)).?;
    return .{ .index = try sema.intern_pool.internUnion(.{ .ty = type_info_ty, .tag = tag.index, .val = payload }) };
}

fn renderModuleName(sub_path: []const u8, writer: *std.Io.Writer) std.Io.Writer.Error!void {
    const ext = std.fs.path.extension(sub_path);
    const noext = sub_path[0 .. sub_path.len - ext.len];
    for (noext) |byte| switch (byte) {
        '/', '\\' => try writer.writeByte('.'),
        else => try writer.writeByte(byte),
    };
}

fn moduleTypeName(sema: *Sema, sub_path: []const u8) Error!InternPool.NullTerminatedString {
    const ext = std.fs.path.extension(sub_path);
    const buf = try sema.gpa.alloc(u8, sub_path.len - ext.len);
    defer sema.gpa.free(buf);
    var writer: std.Io.Writer = .fixed(buf);
    renderModuleName(sub_path, &writer) catch unreachable;
    return sema.intern_pool.getOrPutString(sema.gpa, writer.buffered(), .no_embedded_nulls);
}

fn buildArrayAggregate(sema: *Sema, inst: Zir.Inst.Index) Error!InternPool.Index {
    assert(@backingInt(inst) < sema.zir.instructions.len);

    const pl_node = sema.zir.instructions.items(.data)[@backingInt(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.MultiOp, pl_node.payload_index);
    const operands = sema.zir.refSlice(extra.end, extra.data.operands_len);
    assert(operands.len >= 1);

    const ip = sema.intern_pool;
    const result_ty = try sema.resolveDestType(operands[0]);
    // A generic (`anytype`) result type is unknown; build an anonymous tuple of the elements, as
    // the compiler's zirArrayInit does (`resolveTypeOrPoison ... orelse arrayInitAnon(args[1..])`).
    if (result_ty == .generic_poison_type) return try sema.arrayInitAnon(operands[1..]);
    // Peel an optional/error-union result type (`?[N]T`, `E![N]T`) to the array it wraps; the wrapping
    // happens at the coercion of the built aggregate.
    const array_ty = sema.optEuBaseType(result_ty);
    const array_key = ip.indexToKey(array_ty);

    const elems = operands[1..];
    const buf = try sema.gpa.alloc(InternPool.Index, elems.len);
    defer sema.gpa.free(buf);
    for (elems, 0..) |elem_ref, i| {
        const elem = try sema.resolveInst(elem_ref);
        const elem_ty = try sema.arrayInitElemType(array_key, i);
        const coerced = try sema.coerceValueToType(elem, elem_ty);
        buf[i] = coerced.index;
    }

    return try ip.internAggregate(.{ .ty = array_ty, .storage = .{ .elems = buf } });
}

fn arrayInitElemType(
    sema: *Sema,
    key: InternPool.Key,
    index: usize,
) Error!InternPool.Index {
    switch (key) {
        .array_type => |at| return at.child,
        .vector_type => |vt| return vt.child,
        .tuple_type => |tt| {
            if (index < tt.types.len) return tt.types[index];
            return sema.fail(sema.block, sema.block.nodeOffset(.zero), "element {d} is out of range for a {d}-field tuple", .{ index, tt.types.len });
        },
        else => {
            return sema.fail(sema.block, sema.block.nodeOffset(.zero), "type does not support array-init syntax", .{});
        },
    }
}

fn evalArrayInitElemType(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@backingInt(inst) < sema.zir.instructions.len);

    const bin = sema.zir.instructions.items(.data)[@backingInt(inst)].bin;
    const maybe_wrapped = try sema.resolveDestType(bin.lhs);
    // A generic (`anytype`) aggregate has a generic element type; the element resolves on coercion.
    if (maybe_wrapped == .generic_poison_type) return .{ .index = .generic_poison_type };
    // Peel an optional/error-union result type (`?[N]T`, `E![N]T`) to the aggregate it wraps.
    const indexable_ty = sema.optEuBaseType(maybe_wrapped);
    const index: usize = @backingInt(bin.rhs);
    const elem_ty = try sema.arrayInitElemType(
        sema.intern_pool.indexToKey(indexable_ty),
        index,
    );
    return .{ .index = elem_ty };
}

fn evalElemType(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@backingInt(inst) < sema.zir.instructions.len);
    const un_node = sema.zir.instructions.items(.data)[@backingInt(inst)].un_node;
    const ptr_ty = sema.optEuBaseType(try sema.resolveDestType(un_node.operand));
    return .{ .index = sema.intern_pool.indexToKey(ptr_ty).ptr_type.child };
}

fn evalIndexablePtrElemType(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@backingInt(inst) < sema.zir.instructions.len);
    const ip = sema.intern_pool;
    const un_node = sema.zir.instructions.items(.data)[@backingInt(inst)].un_node;
    const ptr_ty = Type.fromIndex(try sema.resolveDestType(un_node.operand));
    const ptr_child = Type.fromIndex(ip.indexToKey(ptr_ty.index).ptr_type.child);
    const elem_ty = switch (ip.indexToKey(ptr_ty.index).ptr_type.flags.size) {
        .slice, .many, .c => ptr_child,
        .one => ptr_child.childType(ip),
    };
    return .{ .index = elem_ty.index };
}

fn evalSplatOpResultType(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@backingInt(inst) < sema.zir.instructions.len);
    const ip = sema.intern_pool;
    const un_node = sema.zir.instructions.items(.data)[@backingInt(inst)].un_node;
    const ty = Type.fromIndex(sema.optEuBaseType(try sema.resolveDestType(un_node.operand)));
    switch (ty.zigTypeTag(ip)) {
        .array, .vector => {},
        else => return sema.fail(sema.block, sema.block.nodeOffset(.zero), "expected array or vector type, found '{f}'", .{ty.fmt(ip)}),
    }
    return .{ .index = ty.childType(ip).index };
}

fn evalSplat(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    const bin = sema.binData(inst);
    const dest_ty = sema.optEuBaseType(try sema.resolveDestType(bin.lhs));
    const dest = Type.fromIndex(dest_ty);
    switch (dest.zigTypeTag(ip)) {
        .array, .vector => {},
        else => return sema.fail(sema.block, sema.block.nodeOffset(.zero), "expected array or vector type, found '{f}'", .{dest.fmt(ip)}),
    }
    const scalar = try sema.coerceValueToType(try sema.resolveInst(bin.rhs), dest.childType(ip).index);
    return .{ .index = try ip.internAggregate(.{ .ty = dest_ty, .storage = .{ .repeated_elem = scalar.index } }) };
}

fn evalShuffle(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    const pl_node = sema.zir.instructions.items(.data)[@backingInt(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.Shuffle, pl_node.payload_index).data;

    const elem_ty = try sema.resolveDestType(extra.elem_type);
    if (!isVectorElemType(ip, elem_ty)) {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "@shuffle: expected integer, float, bool, or pointer for the element type", .{});
    }
    const mask = try sema.resolveInst(extra.mask);
    const mask_ty = Value.typeOf(mask, ip);
    switch (mask_ty.zigTypeTag(ip)) {
        .array, .vector => {},
        else => return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "@shuffle: expected vector or array for the mask", .{}),
    }
    const mask_len = mask_ty.arrayLen(ip);
    const av = try sema.resolveInst(extra.a);
    const bv = try sema.resolveInst(extra.b);
    const a_ty = Value.typeOf(av, ip);
    const b_ty = Value.typeOf(bv, ip);
    switch (a_ty.zigTypeTag(ip)) {
        .array, .vector => {},
        else => return sema.failShuffleOperand(elem_ty),
    }
    switch (b_ty.zigTypeTag(ip)) {
        .array, .vector => {},
        else => return sema.failShuffleOperand(elem_ty),
    }
    const a_len = a_ty.arrayLen(ip);
    const b_len = b_ty.arrayLen(ip);

    const mask_agg = ip.indexToKey(mask.index).aggregate;
    const a_agg = ip.indexToKey(av.index).aggregate;
    const b_agg = ip.indexToKey(bv.index).aggregate;

    const elems = try sema.gpa.alloc(InternPool.Index, @intCast(mask_len));
    defer sema.gpa.free(elems);
    for (elems, 0..) |*e, i| {
        const raw = sema.intAsI128(try ip.aggregateElementAt(mask_agg, i)) orelse {
            return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "@shuffle: mask element is not a comptime integer", .{});
        };
        const from_agg, const idx, const len = if (raw >= 0)
            .{ a_agg, @as(u64, @intCast(raw)), a_len }
        else
            .{ b_agg, @as(u64, @intCast(~raw)), b_len };
        if (idx >= len) {
            return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "mask element at index '{d}' selects out-of-bounds index", .{i});
        }
        e.* = try ip.aggregateElementAt(from_agg, idx);
    }
    const result_ty = try ip.internVectorType(.{ .len = @intCast(mask_len), .child = elem_ty });
    return .{ .index = try ip.internAggregate(.{ .ty = result_ty, .storage = .{ .elems = elems } }) };
}

fn failShuffleOperand(sema: *Sema, elem_ty: InternPool.Index) Error {
    return sema.fail(sema.block, sema.block.nodeOffset(.zero), "@shuffle: expected a vector of '{f}'", .{Type.fromIndex(elem_ty).fmt(sema.intern_pool)});
}

fn evalValidateArrayInitTy(sema: *Sema, inst: Zir.Inst.Index, comptime is_result_ty: bool) Error!?Value {
    assert(@backingInt(inst) < sema.zir.instructions.len);

    const pl_node = sema.zir.instructions.items(.data)[@backingInt(inst)].pl_node;
    const data = sema.zir.extraData(Zir.Inst.ArrayInit, pl_node.payload_index).data;
    const ty = try sema.resolveDestType(data.ty);
    // A generic (`anytype`) result type is not known yet; the init proceeds anonymously.
    if (ty == .generic_poison_type) return null;
    const arr_ty = if (is_result_ty) sema.optEuBaseType(ty) else ty;
    try sema.validateArrayInitTy(data.init_count, arr_ty);
    return null;
}

fn validateArrayInitTy(sema: *Sema, init_count: u32, ty: InternPool.Index) Error!void {
    const ip = sema.intern_pool;
    switch (ip.indexToKey(ty)) {
        .array_type => |at| if (init_count != at.len) {
            return sema.fail(sema.block, sema.block.nodeOffset(.zero), "expected {d} array elements; found {d}", .{ at.len, init_count });
        },
        .vector_type => |vt| if (init_count != vt.len) {
            return sema.fail(sema.block, sema.block.nodeOffset(.zero), "expected {d} vector elements; found {d}", .{ vt.len, init_count });
        },
        .tuple_type => |tt| if (init_count != tt.types.len) {
            return sema.fail(sema.block, sema.block.nodeOffset(.zero), "expected {d} tuple fields; found {d}", .{ tt.types.len, init_count });
        },
        else => {
            return sema.fail(sema.block, sema.block.nodeOffset(.zero), "type '{f}' does not support array initialization syntax", .{Type.fromIndex(ty).fmt(ip)});
        },
    }
}

fn evalValidateArrayInitRefTy(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    const pl_node = sema.zir.instructions.items(.data)[@backingInt(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.ArrayInitRefTy, pl_node.payload_index).data;
    const maybe_wrapped_ptr_ty = try sema.resolveDestType(extra.ptr_ty);
    if (maybe_wrapped_ptr_ty == .generic_poison_type) return .{ .index = .generic_poison_type };
    const ptr_ty = sema.optEuBaseType(maybe_wrapped_ptr_ty);
    assert(ip.indexToKey(ptr_ty) == .ptr_type);
    switch (ip.indexToKey(ptr_ty)) {
        .ptr_type => |ptr_type| switch (ptr_type.flags.size) {
            .slice, .many => return .{ .index = try ip.internArrayType(.{
                .len = extra.elem_count,
                .child = ptr_type.child,
                .sentinel = ptr_type.sentinel,
            }) },
            else => {},
        },
        else => {},
    }
    const ret_ty = ip.indexToKey(ptr_ty).ptr_type.child;
    if (ret_ty == .anyopaque_type) return .{ .index = .generic_poison_type };
    const arr_ty = sema.optEuBaseType(ret_ty);
    try sema.validateArrayInitTy(extra.elem_count, arr_ty);
    return .{ .index = ret_ty };
}

fn evalValidateRefTy(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@backingInt(inst) < sema.zir.instructions.len);

    const un_tok = sema.zir.instructions.items(.data)[@backingInt(inst)].un_tok;
    const ty_operand = try sema.resolveDestType(un_tok.operand);
    if (sema.intern_pool.indexToKey(sema.optEuBaseType(ty_operand)) != .ptr_type) {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "expected type '{f}', found pointer", .{Type.fromIndex(ty_operand).fmt(sema.intern_pool)});
    }
    return null;
}

fn evalCoercePtrElemTy(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const bin = sema.binData(inst);
    assert(bin.lhs != .none);
    assert(bin.rhs != .none);

    const ip = sema.intern_pool;
    const uncoerced = try sema.resolveInst(bin.rhs);
    const ptr_ty = ip.indexToKey(sema.optEuBaseType(try sema.resolveDestType(bin.lhs))).ptr_type;
    const elem_ty = ptr_ty.child;
    const val_ty = Value.typeOf(uncoerced, ip).index;
    switch (ptr_ty.flags.size) {
        .one => {
            if (ip.indexToKey(elem_ty) == .array_type and ip.indexToKey(elem_ty).array_type.child == val_ty) {
                // Initializing a `*[1]T` with a reference to a `T` -- no coercion.
                return uncoerced;
            }
            // A destination element of `anyopaque` does not coerce the value; the pointer coerces instead.
            if (elem_ty == .anyopaque_type) return uncoerced;
            return try sema.coerceValueToType(uncoerced, elem_ty);
        },
        .slice, .many => {
            const len = switch (ip.indexToKey(val_ty)) {
                .array_type => |at| at.len,
                .vector_type => |vt| vt.len,
                .tuple_type => |tt| tt.types.len,
                else => {
                    return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "expected array of '{f}', found '{f}'", .{ Type.fromIndex(elem_ty).fmt(ip), Type.fromIndex(val_ty).fmt(ip) });
                },
            };
            const want_ty = try ip.internArrayType(.{ .len = len, .child = elem_ty, .sentinel = ptr_ty.sentinel });
            return try sema.coerceValueToType(uncoerced, want_ty);
        },
        .c => return uncoerced,
    }
}

fn optEuBaseType(sema: *Sema, ty: InternPool.Index) InternPool.Index {
    var cur = ty;
    while (true) switch (sema.intern_pool.indexToKey(cur)) {
        .opt_type => |child| cur = child,
        .error_union_type => |eu| cur = eu.payload_type,
        else => return cur,
    };
}

fn evalTupleDecl(sema: *Sema, extended: Zir.Inst.Extended.InstData) Error!?Value {
    const fields_len = extended.small;
    const extra = sema.zir.extraData(Zir.Inst.TupleDecl, extended.operand);
    const refs = sema.zir.refSlice(extra.end, fields_len * 2);

    const types = try sema.gpa.alloc(InternPool.Index, fields_len);
    defer sema.gpa.free(types);
    const vals = try sema.gpa.alloc(InternPool.Index, fields_len);
    defer sema.gpa.free(vals);
    for (types, vals, 0..) |*ty, *val, i| {
        const zir_field_ty = refs[i * 2];
        const zir_field_init = refs[i * 2 + 1];
        const field_type = try sema.resolveDestType(zir_field_ty);
        ty.* = field_type;
        val.* = if (zir_field_init != .none)
            (try sema.coerceValueToType(try sema.resolveInst(zir_field_init), field_type)).index
        else
            .none;
    }

    return .{ .index = try sema.intern_pool.internTupleType(types, vals) };
}

fn evalStructDecl(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@backingInt(inst) < sema.zir.instructions.len);

    const struct_decl = sema.zir.getStructDecl(inst);
    const name = switch (struct_decl.name_strategy) {
        .parent => sema.block.type_name_ctx,
        .anon, .func, .dbg_var => blk: {
            const ctx = sema.intern_pool.stringSlice(sema.block.type_name_ctx);
            const text = try std.fmt.allocPrint(sema.gpa, "{s}__struct_{d}", .{ ctx, @backingInt(inst) });
            defer sema.gpa.free(text);
            break :blk try sema.intern_pool.getOrPutString(sema.gpa, text, .no_embedded_nulls);
        },
    };

    const captures = try sema.resolveCaptures(struct_decl.captures);
    defer sema.gpa.free(captures);

    var any_field_aligns = false;
    var any_comptime_fields = false;
    var it = struct_decl.iterateFields();
    while (it.next()) |field| {
        if (field.align_body != null) any_field_aligns = true;
        if (field.is_comptime) any_comptime_fields = true;
    }

    const result = try sema.intern_pool.getDeclaredStructType(name, .{ .declared = .{
        .source_zir_id = sema.current_zir_id,
        .decl_inst = inst,
        .captures = captures,
    } }, @intCast(struct_decl.field_names.len), struct_decl.layout, any_field_aligns, any_comptime_fields);
    switch (result) {
        .existing => |ty| return .{ .index = ty },
        .wip => |wip| {
            const new_namespace_index = try sema.intern_pool.createNamespace(sema.gpa, .{
                .parent = .init(sema.block.namespace),
                .owner_type = wip.index,
                .file_scope = sema.namespaceFileScope(sema.current_zir_id),
            });
            sema.intern_pool.setNamespace(wip.index, new_namespace_index);
            return .{ .index = wip.index };
        },
    }
}

fn evalEnumDecl(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@backingInt(inst) < sema.zir.instructions.len);

    const enum_decl = sema.zir.getEnumDecl(inst);
    const name = switch (enum_decl.name_strategy) {
        .parent => sema.block.type_name_ctx,
        .anon, .func, .dbg_var => blk: {
            const ctx = sema.intern_pool.stringSlice(sema.block.type_name_ctx);
            const text = try std.fmt.allocPrint(sema.gpa, "{s}__enum_{d}", .{ ctx, @backingInt(inst) });
            defer sema.gpa.free(text);
            break :blk try sema.intern_pool.getOrPutString(sema.gpa, text, .no_embedded_nulls);
        },
    };

    const captures = try sema.resolveCaptures(enum_decl.captures);
    defer sema.gpa.free(captures);

    const result = try sema.intern_pool.getDeclaredEnumType(
        name,
        .{ .declared = .{
            .source_zir_id = sema.current_zir_id,
            .decl_inst = inst,
            .captures = captures,
        } },
        @intCast(enum_decl.field_names.len),
        enum_decl.nonexhaustive or enum_decl.tag_type_body != null,
        if (enum_decl.tag_type_body != null) .explicit else .auto,
    );
    switch (result) {
        .existing => |enum_ty| {
            return .{ .index = enum_ty };
        },
        .wip => |wip| {
            const new_namespace_index = try sema.intern_pool.createNamespace(sema.gpa, .{
                .parent = .init(sema.block.namespace),
                .owner_type = wip.index,
                .file_scope = sema.namespaceFileScope(sema.current_zir_id),
            });
            sema.intern_pool.setNamespace(wip.index, new_namespace_index);
            _ = try sema.resolveEnumFields(wip.index);
            return .{ .index = wip.index };
        },
    }
}

fn evalUnionDecl(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@backingInt(inst) < sema.zir.instructions.len);

    const union_decl = sema.zir.getUnionDecl(inst);
    const name = switch (union_decl.name_strategy) {
        .parent => sema.block.type_name_ctx,
        .anon, .func, .dbg_var => blk: {
            const ctx = sema.intern_pool.stringSlice(sema.block.type_name_ctx);
            const text = try std.fmt.allocPrint(sema.gpa, "{s}__union_{d}", .{ ctx, @backingInt(inst) });
            defer sema.gpa.free(text);
            break :blk try sema.intern_pool.getOrPutString(sema.gpa, text, .no_embedded_nulls);
        },
    };

    const captures = try sema.resolveCaptures(union_decl.captures);
    defer sema.gpa.free(captures);

    const layout: std.lang.Type.ContainerLayout = switch (union_decl.kind) {
        .auto, .tagged_explicit, .tagged_enum, .tagged_enum_explicit => .auto,
        .@"extern" => .@"extern",
        .@"packed", .packed_explicit => .@"packed",
    };

    const tag_usage: InternPool.UnionFields.TagUsage = switch (union_decl.kind) {
        .auto => .safety,
        .tagged_explicit, .tagged_enum, .tagged_enum_explicit => .tagged,
        .@"extern", .@"packed", .packed_explicit => .none,
    };

    const result = try sema.intern_pool.getDeclaredUnionType(
        name,
        .{ .declared = .{
            .source_zir_id = sema.current_zir_id,
            .decl_inst = inst,
            .captures = captures,
        } },
        @intCast(union_decl.field_names.len),
        layout,
        union_decl.field_align_body_lens != null,
        tag_usage,
    );
    const union_ty = switch (result) {
        .existing => |ty| ty,
        .wip => |wip| blk: {
            const new_namespace_index = try sema.intern_pool.createNamespace(sema.gpa, .{
                .parent = .init(sema.block.namespace),
                .owner_type = wip.index,
                .file_scope = sema.namespaceFileScope(sema.current_zir_id),
            });
            sema.intern_pool.setNamespace(wip.index, new_namespace_index);
            break :blk wip.index;
        },
    };
    return .{ .index = union_ty };
}

fn evalOpaqueDecl(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const opaque_decl = sema.zir.getOpaqueDecl(inst);
    const name = switch (opaque_decl.name_strategy) {
        .parent => sema.block.type_name_ctx,
        .anon, .func, .dbg_var => blk: {
            const ctx = sema.intern_pool.stringSlice(sema.block.type_name_ctx);
            const text = try std.fmt.allocPrint(sema.gpa, "{s}__opaque_{d}", .{ ctx, @backingInt(inst) });
            defer sema.gpa.free(text);
            break :blk try sema.intern_pool.getOrPutString(sema.gpa, text, .no_embedded_nulls);
        },
    };

    const captures = try sema.resolveCaptures(opaque_decl.captures);
    defer sema.gpa.free(captures);

    const result = try sema.intern_pool.getDeclaredOpaqueType(
        name,
        .{ .declared = .{
            .source_zir_id = sema.current_zir_id,
            .decl_inst = inst,
            .captures = captures,
        } },
    );
    switch (result) {
        .existing => |ty| return .{ .index = ty },
        .wip => |wip| {
            const new_namespace_index = try sema.intern_pool.createNamespace(sema.gpa, .{
                .parent = .init(sema.block.namespace),
                .owner_type = wip.index,
                .file_scope = sema.namespaceFileScope(sema.current_zir_id),
            });
            sema.intern_pool.setNamespace(wip.index, new_namespace_index);
            return .{ .index = wip.index };
        },
    }
}

fn resolveCaptures(sema: *Sema, zir_captures: []const Zir.Inst.Capture) Error![]const InternPool.Index {
    if (zir_captures.len == 0) return &.{};
    // The REPL session root is a typeless namespace (owner_type == .none), unlike the
    // compiler's file root which is a struct; a type declared directly there has no
    // enclosing captures to inherit.
    const parent_ty = sema.intern_pool.namespacePtr(sema.block.namespace.?).owner_type;
    const parent_captures: []const InternPool.Index = if (parent_ty != .none)
        sema.intern_pool.indexToKey(parent_ty).struct_type.captures()
    else
        &.{};
    const caps = try sema.gpa.alloc(InternPool.Index, zir_captures.len);
    errdefer sema.gpa.free(caps);
    for (zir_captures, caps) |zc, *c| {
        c.* = switch (zc.unwrap()) {
            .instruction => |i| (try sema.resolveInst(i.toRef())).index,
            .instruction_load => |i| (try sema.loadValue(try sema.resolveInst(i.toRef()))).index,
            .nested => |idx| parent_captures[idx],
            // A nested container capturing an enclosing decl (`decl_val`/`decl_ref`): the compiler
            // captures the nav lazily; the REPL resolves the enclosing name eagerly, like every other
            // capture arm, mirroring `lookupIdentifier` -> `nav_val`/`nav_ref`.
            inline .decl_val, .decl_ref => |str, tag| capture: {
                const name = try sema.intern_pool.getOrPutString(sema.gpa, sema.zir.nullTerminatedString(str), .no_embedded_nulls);
                const nav = (try sema.lookupName(sema.block.namespace.?, name)) orelse
                    return sema.fail(sema.block, sema.block.nodeOffset(.zero), "closure capture: '{f}' not found in scope", .{name.fmt(sema.intern_pool)});
                break :capture switch (tag) {
                    .decl_val => (try sema.analyzeNavVal(nav)).index,
                    .decl_ref => (try sema.analyzeNavRef(nav)).index,
                    else => comptime unreachable,
                };
            },
        };
    }
    return caps;
}

const ZirFrame = struct {
    zir: Zir,
    id: u32,

    fn restore(frame: ZirFrame, sema: *Sema) void {
        sema.zir = frame.zir;
        sema.current_zir_id = frame.id;
    }
};

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
    return sema.fail(sema.block, sema.block.nodeOffset(.zero), "{s}: defining ZIR is no longer available", .{ctx});
}

const ContainerFrame = struct {
    zir: ZirFrame,
    prev_block: *Block,
    decl_inst: Zir.Inst.Index,
    old_inst_map: std.AutoHashMapUnmanaged(Zir.Inst.Index, Value),

    fn restore(cf: ContainerFrame, sema: *Sema) void {
        sema.block.deinit(sema.gpa);
        sema.inst_map.deinit(sema.gpa);
        sema.inst_map = cf.old_inst_map;
        sema.block = cf.prev_block;
        cf.zir.restore(sema);
    }
};

fn enterContainer(sema: *Sema, block: *Block, container_ty: InternPool.Index, ctx: []const u8) Error!ContainerFrame {
    const owner = switch (sema.intern_pool.indexToKey(container_ty)) {
        .enum_type => |et| if (et.generatedUnion() != .none) et.generatedUnion() else container_ty,
        else => container_ty,
    };
    const ns = sema.containerNamespace(owner).?;
    const zir = try sema.enterSourceZir(ns.source_zir_id, ctx);
    block.* = .{
        .namespace = sema.getNamespaceIndex(owner),
        .src_base_inst = ns.decl_inst,
        .type_name_ctx = sema.block.type_name_ctx,
    };
    const prev_block = sema.block;
    sema.block = block;
    const old_inst_map = sema.inst_map;
    sema.inst_map = .empty;
    return .{ .zir = zir, .prev_block = prev_block, .decl_inst = ns.decl_inst, .old_inst_map = old_inst_map };
}

fn containerTypeSrc(sema: *Sema, container_ty: InternPool.Index) LazySrcLoc {
    const id: InternPool.Key.ContainerType = switch (sema.intern_pool.indexToKey(container_ty)) {
        .struct_type => |st| st,
        .union_type => |ut| ut,
        .enum_type => |et| et,
        .opaque_type => |ot| ot,
        else => return sema.block.nodeOffset(.zero),
    };
    // A generated union-tag enum has no source of its own; it resolves through the owning union.
    return switch (id) {
        .declared => |d| .{ .base_node_inst = d.decl_inst, .offset = .{ .node_offset = .zero } },
        .reified => |r| .{ .base_node_inst = r.decl_inst, .offset = .{ .node_offset = .zero } },
        .generated_union_tag => |owner_union| sema.containerTypeSrc(owner_union),
    };
}

fn failBadStructFieldAccess(sema: *Sema, struct_ty: InternPool.Index, name: InternPool.NullTerminatedString) Error {
    const ip = sema.intern_pool;
    const st_name = ip.stringSlice(ip.typeName(struct_ty));
    const msg = msg: {
        const msg = try sema.errMsg(sema.block.nodeOffset(.zero), "no field named '{s}' in struct '{s}'", .{ ip.stringSlice(name), st_name });
        errdefer msg.destroy(sema.gpa);
        try sema.errNote(sema.containerTypeSrc(struct_ty), msg, "struct declared here", .{});
        break :msg msg;
    };
    return sema.failWithOwnedErrorMsg(sema.block, msg);
}

fn failBadUnionFieldAccess(sema: *Sema, union_ty: InternPool.Index, name: InternPool.NullTerminatedString) Error {
    const ip = sema.intern_pool;
    const un_name = ip.stringSlice(ip.typeName(union_ty));
    const msg = msg: {
        const msg = try sema.errMsg(sema.block.nodeOffset(.zero), "no field named '{s}' in union '{s}'", .{ ip.stringSlice(name), un_name });
        errdefer msg.destroy(sema.gpa);
        try sema.errNote(sema.containerTypeSrc(union_ty), msg, "union declared here", .{});
        break :msg msg;
    };
    return sema.failWithOwnedErrorMsg(sema.block, msg);
}

fn failBadMemberAccess(sema: *Sema, container_ty: InternPool.Index, name: InternPool.NullTerminatedString) Error {
    const ip = sema.intern_pool;
    const src = sema.block.nodeOffset(.zero);
    const key = ip.indexToKey(container_ty);
    const kw_name: []const u8 = switch (key) {
        .struct_type => "struct",
        .enum_type => "enum",
        .union_type => "union",
        else => return sema.fail(sema.block, src, "type '{f}' has no member named '{s}'", .{ Type.fromIndex(container_ty).fmt(ip), ip.stringSlice(name) }),
    };
    const decl_inst: ?Zir.Inst.Index = switch (key) {
        .struct_type => |st| st.declInst(),
        .union_type => |ut| ut.declInst(),
        .enum_type => |et| switch (et) {
            .generated_union_tag => null,
            else => et.declInst(),
        },
        else => unreachable,
    };
    if (decl_inst) |di| if (di == .main_struct_inst) {
        return sema.fail(sema.block, src, "root source file struct '{f}' has no member named '{s}'", .{ Type.fromIndex(container_ty).fmt(ip), ip.stringSlice(name) });
    };
    return sema.fail(sema.block, src, "{s} '{f}' has no member named '{s}'", .{ kw_name, Type.fromIndex(container_ty).fmt(ip), ip.stringSlice(name) });
}

pub const FieldInfo = struct {
    index: u32,
    ty: InternPool.Index,
    is_comptime: bool = false,
    align_bytes: ?u64 = null,
};

fn structFieldIsComptime(f: InternPool.LoadedStructType, i: usize) bool {
    if (f.field_is_comptime_bits.len == 0) return false;
    return f.field_is_comptime_bits[i / 32] >> @intCast(i % 32) & 1 != 0;
}

fn structFieldAlign(f: InternPool.LoadedStructType, i: usize) ?u64 {
    const a = f.field_aligns.getOrNone(i);
    if (a == .none) return null;
    return a.toByteUnits().?;
}

pub fn structFieldByName(
    sema: *Sema,
    struct_ty: InternPool.Index,
    name: InternPool.NullTerminatedString,
) Error!?FieldInfo {
    const ip = sema.intern_pool;
    switch (ip.indexToKey(struct_ty).struct_type) {
        .reified => {
            const f = ip.loadStructType(struct_ty);
            const i = f.nameIndex(ip, name) orelse return null;
            return .{
                .index = i,
                .ty = f.field_types[i],
                .is_comptime = structFieldIsComptime(f, i),
                .align_bytes = structFieldAlign(f, i),
            };
        },
        .declared => {},
        .generated_union_tag => unreachable,
    }
    var block: Block = undefined;
    const cf = try sema.enterContainer(&block, struct_ty, "struct field");
    defer cf.restore(sema);
    if (sema.zir.instructions.items(.tag)[@backingInt(cf.decl_inst)] == .struct_init_anon)
        return try sema.anonStructFieldByName(cf.decl_inst, name);
    var it = sema.zir.getStructDecl(cf.decl_inst).iterateFields();
    while (it.next()) |field| {
        if ((try ip.getOrPutString(sema.gpa, sema.zir.nullTerminatedString(field.name), .no_embedded_nulls)) == name) {
            return .{
                .index = field.idx,
                .ty = (try sema.coerceValueToType(try sema.resolveInlineBody(field.type_body, cf.decl_inst), .type_type)).index,
                .is_comptime = field.is_comptime,
                .align_bytes = try sema.fieldAlignBytes(field.align_body, cf.decl_inst),
            };
        }
    }
    return null;
}

pub fn structFieldDefault(
    sema: *Sema,
    struct_ty: InternPool.Index,
    name: InternPool.NullTerminatedString,
) Error!InternPool.Index {
    const ip = sema.intern_pool;
    switch (ip.indexToKey(struct_ty).struct_type) {
        .reified => {
            const f = ip.loadStructType(struct_ty);
            const i = f.nameIndex(ip, name) orelse return .none;
            return if (f.field_defaults.len == 0) .none else f.field_defaults[i];
        },
        .declared => {},
        .generated_union_tag => unreachable,
    }
    var block: Block = undefined;
    const cf = try sema.enterContainer(&block, struct_ty, "struct field default");
    defer cf.restore(sema);
    if (sema.zir.instructions.items(.tag)[@backingInt(cf.decl_inst)] == .struct_init_anon) return .none;
    var it = sema.zir.getStructDecl(cf.decl_inst).iterateFields();
    while (it.next()) |field| {
        if ((try ip.getOrPutString(sema.gpa, sema.zir.nullTerminatedString(field.name), .no_embedded_nulls)) != name) continue;
        const body = field.default_body orelse return .none;
        const ty = (try sema.coerceValueToType(try sema.resolveInlineBody(field.type_body, cf.decl_inst), .type_type)).index;
        try sema.inst_map.put(sema.gpa, cf.decl_inst, .{ .index = ty });
        const raw = sema.resolveInlineBody(body, cf.decl_inst);
        _ = sema.inst_map.remove(cf.decl_inst);
        return (try sema.coerceValueToType(try raw, ty)).index;
    }
    return .none;
}

fn anonStructFieldByName(sema: *Sema, decl_inst: Zir.Inst.Index, name: InternPool.NullTerminatedString) Error!?FieldInfo {
    const ip = sema.intern_pool;
    const pl_node = sema.zir.instructions.items(.data)[@backingInt(decl_inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.StructInitAnon, pl_node.payload_index);
    var extra_index = extra.end;
    var i: u32 = 0;
    while (i < extra.data.fields_len) : (i += 1) {
        const item = sema.zir.extraData(Zir.Inst.StructInitAnon.Item, extra_index);
        extra_index = item.end;
        if ((try ip.getOrPutString(sema.gpa, sema.zir.nullTerminatedString(item.data.field_name), .no_embedded_nulls)) == name)
            return .{ .index = i, .ty = .none };
    }
    return null;
}

pub fn unionFieldByName(
    sema: *Sema,
    union_ty: InternPool.Index,
    name: InternPool.NullTerminatedString,
) Error!?FieldInfo {
    const ip = sema.intern_pool;
    switch (ip.indexToKey(union_ty).union_type) {
        .reified => {
            const f = ip.unionFields(union_ty);
            for (f.field_names, 0..) |n, i| {
                if (n != name) continue;
                return .{
                    .index = @intCast(i),
                    .ty = f.field_types[i],
                    .align_bytes = blk: {
                        const a = f.field_aligns.getOrNone(i);
                        break :blk if (a == .none) null else a.toByteUnits().?;
                    },
                };
            }
            return null;
        },
        .declared => {},
        .generated_union_tag => unreachable,
    }
    var block: Block = undefined;
    const cf = try sema.enterContainer(&block, union_ty, "union field");
    defer cf.restore(sema);
    var it = sema.zir.getUnionDecl(cf.decl_inst).iterateFields();
    while (it.next()) |field| {
        if ((try ip.getOrPutString(sema.gpa, sema.zir.nullTerminatedString(field.name), .no_embedded_nulls)) == name) {
            const ty = if (field.type_body) |body|
                (try sema.coerceValueToType(try sema.resolveInlineBody(body, cf.decl_inst), .type_type)).index
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

fn fieldAlignBytes(sema: *Sema, align_body: ?[]const Zir.Inst.Index, decl_inst: Zir.Inst.Index) Error!?u64 {
    const body = align_body orelse return null;
    return try sema.resolveUsizeInt(try sema.resolveInlineBody(body, decl_inst));
}

fn alignOptValue(sema: *Sema, align_bytes: ?u64) Error!InternPool.Index {
    const ip = sema.intern_pool;
    const opt_usize = try ip.internOptionalType(.usize_type);
    return try ip.internOpt(.{
        .ty = opt_usize,
        .val = if (align_bytes) |bytes| try ip.internInt(.{ .ty = .usize_type, .storage = .{ .u64 = bytes } }) else .none,
    });
}

fn optTypeValue(sema: *Sema, val: InternPool.Index) Error!InternPool.Index {
    const ip = sema.intern_pool;
    return try ip.internOpt(.{ .ty = try ip.internOptionalType(.type_type), .val = val });
}

pub fn structFieldNameAt(sema: *Sema, struct_ty: InternPool.Index, index: u32) Error!?InternPool.NullTerminatedString {
    const ip = sema.intern_pool;
    switch (ip.indexToKey(struct_ty).struct_type) {
        .reified => {
            const f = ip.loadStructType(struct_ty);
            return if (index < f.field_names.len) f.field_names[index] else null;
        },
        .declared => {},
        .generated_union_tag => unreachable,
    }
    var block: Block = undefined;
    const cf = try sema.enterContainer(&block, struct_ty, "struct field name");
    defer cf.restore(sema);
    if (sema.zir.instructions.items(.tag)[@backingInt(cf.decl_inst)] == .struct_init_anon) {
        const pl_node = sema.zir.instructions.items(.data)[@backingInt(cf.decl_inst)].pl_node;
        const extra = sema.zir.extraData(Zir.Inst.StructInitAnon, pl_node.payload_index);
        var extra_index = extra.end;
        var i: u32 = 0;
        while (i < extra.data.fields_len) : (i += 1) {
            const item = sema.zir.extraData(Zir.Inst.StructInitAnon.Item, extra_index);
            extra_index = item.end;
            if (i == index) return try ip.getOrPutString(sema.gpa, sema.zir.nullTerminatedString(item.data.field_name), .no_embedded_nulls);
        }
        return null;
    }
    var it = sema.zir.getStructDecl(cf.decl_inst).iterateFields();
    while (it.next()) |field| {
        if (field.idx == index)
            return try ip.getOrPutString(sema.gpa, sema.zir.nullTerminatedString(field.name), .no_embedded_nulls);
    }
    return null;
}

pub fn unionFieldCount(sema: *Sema, union_ty: InternPool.Index) Error!u32 {
    switch (sema.intern_pool.indexToKey(union_ty).union_type) {
        .reified => return @intCast(sema.intern_pool.unionFields(union_ty).field_names.len),
        .declared => {},
        .generated_union_tag => unreachable,
    }
    var block: Block = undefined;
    const cf = try sema.enterContainer(&block, union_ty, "union field count");
    defer cf.restore(sema);
    return @intCast(sema.zir.getUnionDecl(cf.decl_inst).field_names.len);
}

pub fn unionFieldNameAt(sema: *Sema, union_ty: InternPool.Index, index: u32) Error!?InternPool.NullTerminatedString {
    const ip = sema.intern_pool;
    switch (ip.indexToKey(union_ty).union_type) {
        .reified => {
            const f = ip.unionFields(union_ty);
            return if (index < f.field_names.len) f.field_names[index] else null;
        },
        .declared => {},
        .generated_union_tag => unreachable,
    }
    var block: Block = undefined;
    const cf = try sema.enterContainer(&block, union_ty, "union field name");
    defer cf.restore(sema);
    var it = sema.zir.getUnionDecl(cf.decl_inst).iterateFields();
    while (it.next()) |field| {
        if (field.idx == index)
            return try ip.getOrPutString(sema.gpa, sema.zir.nullTerminatedString(field.name), .no_embedded_nulls);
    }
    return null;
}

pub fn isNoPossibleValue(sema: *Sema, ty: InternPool.Index) Error!bool {
    const ip = sema.intern_pool;
    return switch (ip.indexToKey(ty)) {
        .simple_type => |s| s == .noreturn or s == .anyopaque,
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

fn structHasNpvField(sema: *Sema, struct_ty: InternPool.Index) Error!bool {
    const count = try sema.structFieldCount(struct_ty);
    var i: u32 = 0;
    while (i < count) : (i += 1) {
        const name = (try sema.structFieldNameAt(struct_ty, i)).?;
        if (try sema.isNoPossibleValue((try sema.structFieldByName(struct_ty, name)).?.ty)) return true;
    }
    return false;
}

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
    switch (ip.indexToKey(union_ty).union_type) {
        .reified => {
            const f = ip.unionFields(union_ty);
            if (f.enum_tag_type != .none) return f.enum_tag_type;
        },
        .declared => {
            var block: Block = undefined;
            const cf = try sema.enterContainer(&block, union_ty, "union tag type");
            defer cf.restore(sema);
            const decl = sema.zir.getUnionDecl(cf.decl_inst);
            if (decl.kind == .tagged_explicit) {
                const ty = (try sema.resolveInlineBody(decl.arg_type_body.?, cf.decl_inst)).index;
                if (ip.indexToKey(ty) != .enum_type) {
                    return sema.fail(sema.block, sema.block.nodeOffset(.zero), "expected enum tag type, found '{f}'", .{Type.fromIndex(ty).fmt(ip)});
                }
                return ty;
            }
        },
        .generated_union_tag => unreachable,
    }
    const fields_len = try sema.unionFieldCount(union_ty);
    const result = try ip.getDeclaredEnumType(ip.typeName(union_ty), .{ .generated_union_tag = union_ty }, fields_len, false, .auto);
    switch (result) {
        .existing => |tag| return tag,
        .wip => |wip| {
            _ = try sema.resolveGeneratedTagFields(wip.index, union_ty);
            return wip.index;
        },
    }
}

fn enumFieldCount(sema: *Sema, enum_ty: InternPool.Index) Error!u32 {
    switch (sema.intern_pool.indexToKey(enum_ty).enum_type) {
        .generated_union_tag => |u| return try sema.unionFieldCount(u),
        .reified => return @intCast(sema.intern_pool.loadEnumType(enum_ty).field_names.len),
        .declared => {},
    }
    var block: Block = undefined;
    const cf = try sema.enterContainer(&block, enum_ty, "enum field count");
    defer cf.restore(sema);
    return @intCast(sema.zir.getEnumDecl(cf.decl_inst).field_names.len);
}

fn enumIntTagType(sema: *Sema, field_count: u32) Error!InternPool.Index {
    const bits: u16 = if (field_count <= 1) 0 else @intCast(64 - @clz(@as(u64, field_count - 1)));
    return try sema.intern_pool.internIntType(.unsigned, bits);
}

const EnumMatch = union(enum) { name: InternPool.NullTerminatedString, value: i128, index: u32 };

const EnumMatchResult = struct { tag: Value, name: InternPool.NullTerminatedString, index: u32 };

fn enumFieldScan(sema: *Sema, enum_ty: InternPool.Index, match: EnumMatch) Error!?EnumMatchResult {
    const ip = sema.intern_pool;
    const fields = ip.loadEnumType(enum_ty);
    if (match == .name) {
        const pos = fields.nameIndex(ip, match.name) orelse return null;
        const cur: i128 = if (fields.field_values.len == 0) @intCast(pos) else sema.intAsI128(fields.field_values[pos]).?;
        return try sema.matchEnumField(enum_ty, fields.int_tag_type, match, fields.field_names[pos], @intCast(pos), cur);
    }
    for (fields.field_names, 0..) |field_name, pos| {
        const cur: i128 = if (fields.field_values.len == 0) @intCast(pos) else sema.intAsI128(fields.field_values[pos]).?;
        if (try sema.matchEnumField(enum_ty, fields.int_tag_type, match, field_name, @intCast(pos), cur)) |m| return m;
    }
    return null;
}

fn resolveEnumFields(sema: *Sema, enum_ty: InternPool.Index) Error!InternPool.LoadedEnumType {
    const ip = sema.intern_pool;
    assert(ip.indexToKey(enum_ty).enum_type == .declared);

    const tag_ty = try sema.enumIntTagTypeOf(enum_ty);
    var block: Block = undefined;
    const cf = try sema.enterContainer(&block, enum_ty, "enum field");
    defer cf.restore(sema);
    const decl = sema.zir.getEnumDecl(cf.decl_inst);
    const have_values = decl.nonexhaustive or decl.tag_type_body != null;

    var names: std.ArrayListUnmanaged(InternPool.NullTerminatedString) = .empty;
    defer names.deinit(sema.gpa);
    var values: std.ArrayListUnmanaged(InternPool.Index) = .empty;
    defer values.deinit(sema.gpa);

    var it = decl.iterateFields();
    var next_auto: i128 = 0;
    while (it.next()) |field| {
        try names.append(sema.gpa, try ip.getOrPutString(sema.gpa, sema.zir.nullTerminatedString(field.name), .no_embedded_nulls));
        if (!have_values) continue;
        const cur: i128 = if (field.value_body) |body| blk: {
            const raw = try sema.resolveInlineBody(body, cf.decl_inst);
            // Coerce to the tag type as the compiler does, so an out-of-range or fractional value reports the
            // coercion error.
            const coerced = try sema.coerceValueToType(raw, tag_ty);
            break :blk sema.intAsI128(coerced.index).?;
        } else next_auto;
        next_auto = cur + 1;
        try values.append(sema.gpa, try sema.enumTagIntValue(tag_ty, cur));
    }
    try ip.setEnumFields(enum_ty, tag_ty, decl.nonexhaustive, names.items, values.items);
    const fields = ip.loadEnumType(enum_ty);
    fields.field_name_map.get(ip).clearRetainingCapacity();
    for (names.items) |field_name| assert(ip.addFieldName(names.items, fields.field_name_map, field_name) == null);
    if (fields.field_value_map.unwrap()) |value_map| {
        value_map.get(ip).clearRetainingCapacity();
        for (values.items, 0..) |field_value, field_index| {
            if (ip.addFieldTagValue(values.items, value_map, field_value)) |prev_field_index| {
                return sema.failWithOwnedErrorMsg(sema.block, msg: {
                    const src = sema.block.nodeOffset(.zero);
                    const msg = try sema.errMsg(src, "enum tag value '{f}' for field '{f}' already taken", .{ render_value.fmt(.{ .index = field_value }, ip), names.items[field_index].fmt(ip) });
                    errdefer msg.destroy(sema.gpa);
                    try sema.errNote(src, msg, "previous occurrence in field '{f}'", .{names.items[prev_field_index].fmt(ip)});
                    break :msg msg;
                });
            }
        }
    }
    return ip.loadEnumType(enum_ty);
}

fn resolveGeneratedTagFields(sema: *Sema, enum_ty: InternPool.Index, union_ty: InternPool.Index) Error!InternPool.LoadedEnumType {
    const ip = sema.intern_pool;
    const tag_ty = try sema.enumIntTagTypeOf(enum_ty);

    const count = try sema.unionFieldCount(union_ty);
    const names = try sema.arena.alloc(InternPool.NullTerminatedString, count);
    for (names, 0..) |*n, i| n.* = (try sema.unionFieldNameAt(union_ty, @intCast(i))).?;

    try ip.setEnumFields(enum_ty, tag_ty, false, names, &.{});
    const fields = ip.loadEnumType(enum_ty);
    fields.field_name_map.get(ip).clearRetainingCapacity();
    for (names) |field_name| assert(ip.addFieldName(names, fields.field_name_map, field_name) == null);
    return fields;
}

pub fn enumIntTagTypeOf(sema: *Sema, enum_ty: InternPool.Index) Error!InternPool.Index {
    switch (sema.intern_pool.indexToKey(enum_ty).enum_type) {
        .reified => return sema.intern_pool.loadEnumType(enum_ty).int_tag_type,
        .generated_union_tag => |gu| {
            if (sema.intern_pool.indexToKey(gu).union_type == .reified) {
                return try sema.enumIntTagType(try sema.unionFieldCount(gu));
            }
            var block: Block = undefined;
            const cf = try sema.enterContainer(&block, enum_ty, "enum tag type");
            defer cf.restore(sema);
            const decl = sema.zir.getUnionDecl(cf.decl_inst);
            return if (decl.kind == .tagged_enum_explicit)
                (try sema.resolveInlineBody(decl.arg_type_body.?, cf.decl_inst)).index
            else
                try sema.enumIntTagType(@intCast(decl.field_names.len));
        },
        .declared => {
            var block: Block = undefined;
            const cf = try sema.enterContainer(&block, enum_ty, "enum tag type");
            defer cf.restore(sema);
            const decl = sema.zir.getEnumDecl(cf.decl_inst);
            return if (decl.tag_type_body) |body|
                (try sema.resolveInlineBody(body, cf.decl_inst)).index
            else
                try sema.enumIntTagType(@intCast(decl.field_names.len));
        },
    }
}

fn enumNonexhaustive(sema: *Sema, enum_ty: InternPool.Index) Error!bool {
    switch (sema.intern_pool.indexToKey(enum_ty).enum_type) {
        .generated_union_tag => return false,
        .reified => return sema.intern_pool.loadEnumType(enum_ty).nonexhaustive,
        .declared => {},
    }
    var block: Block = undefined;
    const cf = try sema.enterContainer(&block, enum_ty, "enum mode");
    defer cf.restore(sema);
    return sema.zir.getEnumDecl(cf.decl_inst).nonexhaustive;
}

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

fn enumTagIntValue(sema: *Sema, tag_ty: InternPool.Index, value: i128) Error!InternPool.Index {
    var limbs_buf: [std.math.big.int.calcLimbLen(@as(i128, std.math.minInt(i128)))]Limb = undefined;
    var mutable: BigIntMutable = .{ .limbs = &limbs_buf, .len = undefined, .positive = undefined };
    mutable.set(value);
    const raw = try sema.intern_pool.internComptimeInt(mutable.toConst());
    return (try sema.coerceValueToType(.{ .index = raw }, tag_ty)).index;
}

fn enumFieldIndex(sema: *Sema, enum_ty: InternPool.Index, name: InternPool.NullTerminatedString) Error!?u32 {
    return if (try sema.enumFieldScan(enum_ty, .{ .name = name })) |m| m.index else null;
}

pub fn enumTagFieldIndex(sema: *Sema, enum_ty: InternPool.Index, tag: Value) Error!?u32 {
    const int = switch (sema.intern_pool.indexToKey(tag.index)) {
        .enum_tag => |et| et.int,
        .int => tag.index,
        else => unreachable,
    };
    return if (try sema.enumFieldScan(enum_ty, .{ .value = sema.intAsI128(int).? })) |m| m.index else null;
}

fn enumFieldName(sema: *Sema, enum_ty: InternPool.Index, index: u32) Error!?InternPool.NullTerminatedString {
    return if (try sema.enumFieldScan(enum_ty, .{ .index = index })) |m| m.name else null;
}

pub fn enumValueFieldIndex(sema: *Sema, enum_ty: InternPool.Index, index: u32) Error!?Value {
    return if (try sema.enumFieldScan(enum_ty, .{ .index = index })) |m| m.tag else null;
}

fn enumTagByName(sema: *Sema, enum_ty: InternPool.Index, name: InternPool.NullTerminatedString) Error!?Value {
    return if (try sema.enumFieldScan(enum_ty, .{ .name = name })) |m| m.tag else null;
}

fn intAsI128(sema: *Sema, index: InternPool.Index) ?i128 {
    const key = sema.intern_pool.indexToKey(index);
    if (key != .int) return null;
    return switch (key.int.storage) {
        .u64 => |v| @as(i128, v),
        .i64 => |v| @as(i128, v),
        .big_int => |b| b.toInt(i128) catch null,
    };
}

fn enumHasInt(sema: *Sema, enum_ty: InternPool.Index, int: Value) Error!bool {
    const ip = sema.intern_pool;
    const fields = try sema.resolveEnumFields(enum_ty);
    assert(!fields.nonexhaustive);
    const int_tag_ty = fields.int_tag_type;
    if (!sema.intFitsInType(int, Type.fromIndex(int_tag_ty))) return false;
    const int_coerced = try sema.coerceValueToType(int, int_tag_ty);
    return fields.tagValueIndex(ip, int_coerced.index) != null;
}

fn evalEnumFromInt(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    const pl_node = sema.zir.instructions.items(.data)[@backingInt(inst)].pl_node;
    const bin = sema.zir.extraData(Zir.Inst.Bin, pl_node.payload_index).data;
    const dest_ty = (try sema.resolveInst(bin.lhs)).index;
    if (ip.indexToKey(dest_ty) != .enum_type) {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "@enumFromInt: destination is not an enum", .{});
    }
    const operand = try sema.resolveInst(bin.rhs);
    if (ip.indexToKey(operand.index) == .undef) {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "use of undefined value here causes illegal behavior", .{});
    }
    if (sema.intAsI128(operand.index) == null) {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "@enumFromInt: operand is not an integer", .{});
    }
    const int_tag_ty = try sema.enumIntTagTypeOf(dest_ty);
    if (try sema.enumNonexhaustive(dest_ty)) {
        if (!sema.intFitsInType(operand, Type.fromIndex(int_tag_ty))) {
            return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "int value '{f}' out of range of non-exhaustive enum '{f}'", .{ render_value.fmt(operand, ip), Type.fromIndex(dest_ty).fmt(ip) });
        }
    } else if (!try sema.enumHasInt(dest_ty, operand)) {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "enum '{f}' has no tag with value '{f}'", .{ Type.fromIndex(dest_ty).fmt(ip), render_value.fmt(operand, ip) });
    }
    const int_coerced = try sema.coerceValueToType(operand, int_tag_ty);
    return .{ .index = try ip.internEnumTag(.{ .ty = dest_ty, .int = int_coerced.index }) };
}

fn evalIntFromBool(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const operand = try sema.resolveInst(sema.zir.instructions.items(.data)[@backingInt(inst)].un_node.operand);
    const u1_type = try sema.intern_pool.get(.{ .int_type = .{ .signedness = .unsigned, .bits = 1 } });
    return .{ .index = try sema.intern_pool.internInt(.{
        .ty = u1_type,
        .storage = .{ .u64 = @intFromBool(operand.index == .bool_true) },
    }) };
}

fn evalEnumLiteral(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const bytes = sema.zir.instructions.items(.data)[@backingInt(inst)].str_tok.get(sema.zir);
    const name = try sema.intern_pool.getOrPutString(sema.gpa, bytes, .no_embedded_nulls);
    return .{ .index = try sema.intern_pool.get(.{ .enum_literal = name }) };
}

fn evalDeclLiteral(sema: *Sema, inst: Zir.Inst.Index, comptime do_coerce: bool) Error!?Value {
    const pl_node = sema.zir.instructions.items(.data)[@backingInt(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.Field, pl_node.payload_index).data;
    const name = try sema.intern_pool.getOrPutString(sema.gpa, sema.zir.nullTerminatedString(extra.field_name_start), .no_embedded_nulls);
    const orig_ty = (try sema.resolveInst(extra.lhs)).index;
    return try sema.analyzeDeclLiteral(orig_ty, name, do_coerce);
}

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
    return if (do_coerce) try sema.coerceValueToType(uncoerced, orig_ty) else uncoerced;
}

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
        .struct_type, .opaque_type => {
            if (try sema.containerDeclByName(ty, name)) |v| return v;
            return sema.failBadMemberAccess(ty, name);
        },
        else => {
            return sema.fail(sema.block, sema.block.nodeOffset(.zero), "type '{f}' has no members", .{Type.fromIndex(ty).fmt(sema.intern_pool)});
        },
    }
}

fn evalIntFromEnum(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const un_node = sema.zir.instructions.items(.data)[@backingInt(inst)].un_node;
    const operand = try sema.resolveInst(un_node.operand);
    const key = sema.intern_pool.indexToKey(operand.index);
    if (key != .enum_tag) {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "@intFromEnum: operand is not an enum value", .{});
    }
    return .{ .index = key.enum_tag.int };
}

/// `@backingInt`: the integer backing an enum tag, a tagged union's active tag, or a packed
/// aggregate. Mirrors the compiler's `zirBackingInt`; the runtime `bit_cast` path is replaced by the
/// comptime-known `Value.backingInt`, and `unionToTag` by its comptime path `Value.unionTag`.
fn evalBackingInt(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    const un_node = sema.zir.instructions.items(.data)[@backingInt(inst)].un_node;
    const operand_src = sema.block.builtinCallArgSrc(un_node.src_node, 0);
    const operand = try sema.resolveInst(un_node.operand);
    const operand_ty = operand.typeOf(ip);
    try sema.ensureLayoutResolved(operand_ty.index);
    const int_backed: Value = ref: switch (operand_ty.zigTypeTag(ip)) {
        .@"enum" => operand,
        .@"union" => {
            const union_obj = ip.unionFields(operand_ty.index);
            if (union_obj.tag_usage == .tagged) break :ref operand.unionTag(ip).?;
            if (union_obj.layout == .@"packed") break :ref operand;
            return sema.failWithOwnedErrorMsg(sema.block, msg: {
                const msg = try sema.errMsg(operand_src, "non-packed union '{f}' does not have a backing integer", .{operand_ty.fmt(ip)});
                errdefer msg.destroy(sema.gpa);
                try sema.errNote(operand_src, msg, "untagged union '{f}' does not have an enum tag with a backing integer", .{operand_ty.fmt(ip)});
                try sema.errNote(sema.containerTypeSrc(operand_ty.index), msg, "union declared here", .{});
                break :msg msg;
            });
        },
        .@"struct" => {
            if (operand_ty.containerLayout(ip) != .@"packed") {
                return sema.fail(sema.block, operand_src, "non-packed struct '{f}' does not have a backing integer", .{operand_ty.fmt(ip)});
            }
            break :ref operand;
        },
        else => return sema.fail(sema.block, operand_src, "expected enum, tagged union, packed union or packed struct, found '{f}'", .{operand_ty.fmt(ip)}),
    };
    const backing_int_ty = int_backed.typeOf(ip).backingIntType(ip);
    if (int_backed.isUndef(ip)) return try sema.undefValue(backing_int_ty);
    return int_backed.backingInt(ip);
}

/// The result-location arg type for `@fromBackingInt`: validate the destination is an enum or packed
/// aggregate and yield its backing integer type, so the operand coerces to it. Mirrors the compiler's
/// `zirFromBackingIntArgTy`; the ambiguous-inferred-backing-int rejection needs a struct/union backing
/// mode the REPL does not track and is left off.
fn evalFromBackingIntArgTy(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    const un_node = sema.zir.instructions.items(.data)[@backingInt(inst)].un_node;
    const src = sema.block.nodeOffset(un_node.src_node);
    const dest_ty: Type = .fromIndex(try sema.resolveDestType(un_node.operand));
    try sema.ensureLayoutResolved(dest_ty.index);
    switch (dest_ty.zigTypeTag(ip)) {
        .@"enum" => {},
        .@"struct", .@"union" => if (dest_ty.containerLayout(ip) != .@"packed")
            return sema.fail(sema.block, src, "non-packed {s} '{f}' does not have a backing integer", .{ @tagName(dest_ty.zigTypeTag(ip)), dest_ty.fmt(ip) }),
        else => return sema.fail(sema.block, src, "expected enum, packed union or packed struct, found '{f}'", .{dest_ty.fmt(ip)}),
    }
    return .{ .index = dest_ty.backingIntType(ip).index };
}

/// `@fromBackingInt`: build an enum tag or packed aggregate from its backing integer, the inverse of
/// `@backingInt`. Mirrors the compiler's `zirFromBackingInt` comptime path.
fn evalFromBackingInt(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    const pl_node = sema.zir.instructions.items(.data)[@backingInt(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.Bin, pl_node.payload_index).data;
    const src = sema.block.nodeOffset(pl_node.src_node);
    const dest_ty: Type = .fromIndex(try sema.resolveDestType(extra.lhs));
    try sema.ensureLayoutResolved(dest_ty.index);
    const operand = try sema.resolveInst(extra.rhs);
    const backing_int = try sema.coerceValueToType(operand, dest_ty.backingIntType(ip).index);

    if (dest_ty.zigTypeTag(ip) != .@"enum") {
        if (backing_int.isUndef(ip)) return try sema.undefValue(dest_ty);
        return try sema.bitpackValue(dest_ty, backing_int);
    }
    const enum_obj = ip.loadEnumType(dest_ty.index);
    if (backing_int.isUndef(ip)) {
        if (enum_obj.nonexhaustive) return try sema.undefValue(dest_ty);
        return sema.failWithUseOfUndef();
    }
    if (!enum_obj.nonexhaustive and enum_obj.tagValueIndex(ip, backing_int.index) == null) {
        return sema.fail(sema.block, src, "enum '{f}' has no tag with value '{f}'", .{ dest_ty.fmt(ip), render_value.fmt(backing_int, ip) });
    }
    return .{ .index = try ip.internEnumTag(.{ .ty = dest_ty.index, .int = backing_int.index }) };
}

fn evalTagName(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    const un_node = sema.zir.instructions.items(.data)[@backingInt(inst)].un_node;
    const operand_src = sema.block.builtinCallArgSrc(un_node.src_node, 0);
    const src = sema.block.nodeOffset(un_node.src_node);
    const operand = try sema.resolveInst(un_node.operand);
    const operand_ty = operand.typeOf(ip);
    const enum_ty: Type = switch (operand_ty.zigTypeTag(ip)) {
        .enum_literal => {
            const tag_name = ip.indexToKey(operand.index).enum_literal;
            return try sema.internStringLiteral(ip.stringSlice(tag_name));
        },
        .@"enum" => operand_ty,
        .@"union" => blk: {
            try sema.ensureLayoutResolved(operand_ty.index);
            if (ip.unionFields(operand_ty.index).tag_usage != .tagged)
                return sema.fail(sema.block, src, "union '{f}' is untagged", .{operand_ty.fmt(ip)});
            break :blk operand_ty.unionTagTypeHypothetical(ip);
        },
        else => return sema.fail(sema.block, operand_src, "expected enum or union; found '{f}'", .{operand_ty.fmt(ip)}),
    };
    if (operand.isUndef(ip)) return sema.failWithUseOfUndef();
    const casted_operand = try sema.coerceValueToType(operand, enum_ty.index);
    const field_index = (try sema.enumTagFieldIndex(enum_ty.index, casted_operand)) orelse {
        return sema.failWithOwnedErrorMsg(sema.block, msg: {
            const msg = try sema.errMsg(src, "no field with value '{f}' in enum '{f}'", .{ render_value.fmt(casted_operand, ip), enum_ty.fmt(ip) });
            errdefer msg.destroy(sema.gpa);
            try sema.errNote(sema.containerTypeSrc(enum_ty.index), msg, "declared here", .{});
            break :msg msg;
        });
    };
    const field_name = (try sema.enumFieldName(enum_ty.index, field_index)).?;
    return try sema.internStringLiteral(ip.stringSlice(field_name));
}

pub fn structFieldCount(sema: *Sema, struct_ty: InternPool.Index) Error!u32 {
    const key = sema.intern_pool.indexToKey(struct_ty);
    if (key == .tuple_type) return @intCast(key.tuple_type.types.len);
    switch (key.struct_type) {
        .reified => return @intCast(sema.intern_pool.loadStructType(struct_ty).field_names.len),
        .declared => {},
        .generated_union_tag => unreachable,
    }
    const st = sema.intern_pool.indexToKey(struct_ty).struct_type;
    const decl_inst = st.declInst();
    const frame = try sema.enterSourceZir(st.sourceZirId(), "struct field count");
    defer frame.restore(sema);
    const zir = sema.zir;
    if (zir.instructions.items(.tag)[@backingInt(decl_inst)] == .struct_init_anon) {
        const pl_node = zir.instructions.items(.data)[@backingInt(decl_inst)].pl_node;
        return zir.extraData(Zir.Inst.StructInitAnon, pl_node.payload_index).data.fields_len;
    }
    return @intCast(zir.getStructDecl(decl_inst).field_names.len);
}

fn evalFieldPtr(sema: *Sema, inst: Zir.Inst.Index, comptime initializing: bool) Error!?Value {
    assert(@backingInt(inst) < sema.zir.instructions.len);
    const ip = sema.intern_pool;
    const pl_node = sema.zir.instructions.items(.data)[@backingInt(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.Field, pl_node.payload_index).data;
    const name = try ip.getOrPutString(sema.gpa, sema.zir.nullTerminatedString(extra.field_name_start), .no_embedded_nulls);
    const object_ptr = try sema.resolveInst(extra.lhs);
    return sema.fieldPtr(object_ptr, name, initializing);
}

fn fieldPtr(sema: *Sema, object_ptr: Value, name: InternPool.NullTerminatedString, comptime initializing: bool) Error!?Value {
    const ip = sema.intern_pool;
    const parent_ty = ip.indexToKey(object_ptr.index).ptr.ty;
    const object_ty = ip.indexToKey(parent_ty).ptr_type.child;
    const is_pointer_to = ip.indexToKey(object_ty) == .ptr_type and
        ip.indexToKey(object_ty).ptr_type.flags.size == .one;
    const container_ty = if (is_pointer_to) ip.indexToKey(object_ty).ptr_type.child else object_ty;
    const base_ptr = if (is_pointer_to) try sema.loadValue(object_ptr) else object_ptr;

    if (container_ty == .type_type) {
        const container = try sema.loadValue(base_ptr);
        const ns = sema.getNamespaceIndex(container.index) orelse return sema.failBadMemberAccess(container.index, name);
        const nav = (try sema.namespaceLookup(ns, name)) orelse return sema.failBadMemberAccess(container.index, name);
        return try sema.analyzeNavRef(nav);
    }

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

    switch (ip.indexToKey(container_ty)) {
        .union_type => {
            try sema.ensureLayoutResolved(container_ty);
            return try sema.unionFieldPtr(base_ptr, name, .fromIndex(container_ty), initializing);
        },
        .struct_type => {
            const f = (try sema.structFieldByName(container_ty, name)) orelse
                return sema.failBadStructFieldAccess(container_ty, name);
            try sema.ensureLayoutResolved(container_ty);
            return try sema.structFieldPtrByIndex(base_ptr, f.index, .fromIndex(container_ty));
        },
        else => {
            return sema.fail(sema.block, sema.block.nodeOffset(.zero), "type '{f}' does not support field access", .{Type.fromIndex(container_ty).fmt(ip)});
        },
    }
}

const ContainerNamespace = struct { source_zir_id: u32, decl_inst: Zir.Inst.Index };
fn containerNamespace(sema: *Sema, container_ty: InternPool.Index) ?ContainerNamespace {
    return switch (sema.intern_pool.indexToKey(container_ty)) {
        .struct_type => |st| switch (st) {
            .declared => |d| .{ .source_zir_id = d.source_zir_id, .decl_inst = d.decl_inst },
            .reified, .generated_union_tag => null,
        },
        .union_type => |ut| switch (ut) {
            .declared => |d| .{ .source_zir_id = d.source_zir_id, .decl_inst = d.decl_inst },
            .reified, .generated_union_tag => null,
        },
        .enum_type => |et| switch (et) {
            .declared => |d| .{ .source_zir_id = d.source_zir_id, .decl_inst = d.decl_inst },
            .generated_union_tag => |owner| sema.containerNamespace(owner),
            .reified => null,
        },
        .opaque_type => |ot| switch (ot) {
            .declared => |d| .{ .source_zir_id = d.source_zir_id, .decl_inst = d.decl_inst },
            .reified, .generated_union_tag => null,
        },
        .simple_type,
        .simple_value,
        .enum_literal,
        .int_type,
        .anyframe_type,
        .int,
        .float,
        .undef,
        .ptr_type,
        .ptr,
        .slice,
        .error_set_type,
        .err,
        .error_union_type,
        .error_union,
        .func_type,
        .func,
        .@"extern",
        .array_type,
        .vector_type,
        .opt_type,
        .opt,
        .tuple_type,
        .aggregate,
        .enum_tag,
        .un,
        .bitpack,
        => null,
    };
}

/// Populate a namespace's decls from its owner type's ZIR on first access, the way the compiler's
/// `ensureNamespaceUpToDate` re-scans a stale namespace. `generation` 0 marks a never-scanned
/// namespace; reified and generated-union-tag namespaces carry no ZIR decls and stay empty.
fn ensureNamespaceUpToDate(sema: *Sema, ns: InternPool.NamespaceIndex) Error!void {
    const ns_ptr = sema.intern_pool.namespacePtr(ns);
    if (ns_ptr.generation != 0) return;
    ns_ptr.generation = 1;
    // The root namespace's decls are bound directly (bindDecls), not scanned from ZIR.
    if (ns_ptr.owner_type == .none) return;
    if (sema.containerNamespace(ns_ptr.owner_type) == null) return;
    try sema.scanNamespace(ns, ns_ptr.owner_type);
}

fn getNamespaceIndex(sema: *Sema, ty: InternPool.Index) ?InternPool.NamespaceIndex {
    return sema.intern_pool.typeNamespace(ty).unwrap();
}

fn namespaceFileScope(sema: *Sema, source_zir_id: u32) InternPool.OptionalFileIndex {
    const session = sema.session orelse return .none;
    if (source_zir_id >= session.files.items.len) return .none;
    if (session.files.items[source_zir_id].sub_file_path == null) return .none;
    return InternPool.OptionalFileIndex.init(@fromBackingInt(@intCast(source_zir_id)));
}

fn scanNamespace(sema: *Sema, ns: InternPool.NamespaceIndex, ty: InternPool.Index) Error!void {
    const ip = sema.intern_pool;
    const cn = sema.containerNamespace(ty).?;
    const frame = try sema.enterSourceZir(cn.source_zir_id, "scan namespace");
    defer frame.restore(sema);
    for (sema.zir.typeDecls(cn.decl_inst)) |decl_inst| {
        const unwrapped = sema.zir.getDeclaration(decl_inst);
        if (unwrapped.kind != .@"const" and unwrapped.kind != .@"var") continue;
        const name = try ip.getOrPutString(sema.gpa, sema.zir.nullTerminatedString(unwrapped.name), .no_embedded_nulls);
        const fqn = try ip.fullyQualifiedName(sema.gpa, ns, name);
        const nav = try ip.createNav(sema.gpa, name, fqn);
        ip.navPtr(nav).analysis = .{ .namespace = ns, .zir_index = decl_inst, .wanted = false };
        const ns_ptr = ip.namespacePtr(ns);
        const ctx: InternPool.Namespace.NavNameContext = .{ .pool = ip };
        const target = if (unwrapped.is_pub) &ns_ptr.pub_decls else &ns_ptr.priv_decls;
        _ = try target.getOrPutContext(sema.gpa, nav, ctx);
    }
}

fn analyzeNavVal(sema: *Sema, nav_idx: InternPool.Nav.Index) Error!Value {
    const ip = sema.intern_pool;
    // A `var` read is a runtime load (compiler: `analyzeNavRefInner(false)` + `analyzeLoad`), so it is
    // not comptime-known; a `const` read is. This gates use of a mutable global in comptime positions.
    if (ip.getNav(nav_idx).resolved) |r| return .{ .index = r.value, .is_comptime = r.@"const" };
    const analysis = ip.getNav(nav_idx).analysis.?;
    const container_ty = ip.namespacePtr(analysis.namespace).owner_type;
    const cn = sema.containerNamespace(container_ty).?;
    const frame = try sema.enterSourceZir(cn.source_zir_id, "analyze nav");
    defer frame.restore(sema);
    const decl_inst = analysis.zir_index;
    const unwrapped = sema.zir.getDeclaration(decl_inst);

    var block: Block = .{
        .namespace = analysis.namespace,
        .src_base_inst = decl_inst,
        .type_name_ctx = ip.getNav(nav_idx).fqn,
    };
    // A container declaration's type and value are comptime-known (AstGen lowers their bodies in a
    // comptime scope), so a comptime-required operand within them folds without a `block_comptime`.
    block.comptime_reason = .{ .reason = .{ .src = block.nodeOffset(.zero), .r = .{ .simple = .container_var_init } } };
    const prev_block = sema.block;
    sema.block = &block;
    defer {
        block.deinit(sema.gpa);
        sema.block = prev_block;
    }
    const prev_owner_nav = sema.owner_nav;
    sema.owner_nav = nav_idx.toOptional();
    defer sema.owner_nav = prev_owner_nav;
    const old_inst_map = sema.inst_map;
    sema.inst_map = .empty;
    defer {
        sema.inst_map.deinit(sema.gpa);
        sema.inst_map = old_inst_map;
    }
    const declared_type: ?InternPool.Index = if (unwrapped.type_body) |tb| blk: {
        const t = (try sema.coerceValueToType(try sema.resolveInlineBody(tb, decl_inst), .type_type)).index;
        try sema.inst_map.put(sema.gpa, decl_inst, .{ .index = t });
        break :blk t;
    } else null;

    if (unwrapped.linkage == .@"extern") {
        // An extern decl has no value body; the linker supplies its value at runtime. Mirror the
        // compiler's nav resolution and mint an extern symbol from the declared type, which the
        // comptime layer only ever holds. It can only be executed on the (deferred) runtime path.
        const nav_ty = declared_type.?;
        const ext = try ip.getExtern(.{ .ty = nav_ty, .owner_nav = nav_idx });
        ip.navPtr(nav_idx).resolved = .{
            .type = nav_ty,
            .@"align" = .none,
            .@"linksection" = .none,
            .@"addrspace" = .generic,
            .@"const" = unwrapped.kind == .@"const",
            .@"threadlocal" = unwrapped.is_threadlocal,
            .is_extern_decl = true,
            .value = ext,
        };
        return .{ .index = ext };
    }

    const value_body = unwrapped.value_body orelse
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "decl '{s}': no value_body", .{ip.stringSlice(ip.getNav(nav_idx).name)});
    const raw_value = try sema.resolveInlineBody(value_body, decl_inst);
    const value = if (declared_type) |dest_ty| try sema.coerceValueToType(raw_value, dest_ty) else raw_value;

    ip.navPtr(nav_idx).resolved = .{
        .type = declared_type orelse Value.typeOf(value, ip).index,
        .@"align" = .none,
        .@"linksection" = .none,
        .@"addrspace" = .generic,
        .@"const" = unwrapped.kind == .@"const",
        .@"threadlocal" = unwrapped.is_threadlocal,
        .is_extern_decl = unwrapped.linkage == .@"extern",
        .value = value.index,
    };
    return .{ .index = value.index, .is_comptime = unwrapped.kind == .@"const" };
}

pub fn containerDeclByName(sema: *Sema, container_ty: InternPool.Index, name: InternPool.NullTerminatedString) Error!?Value {
    const ns = sema.getNamespaceIndex(container_ty) orelse return null;
    const nav = (try sema.namespaceLookup(ns, name)) orelse return null;
    return try sema.analyzeNavVal(nav);
}

/// A pointer to a declaration's storage. Its constness follows the declaration (a `var` yields a
/// mutable pointer), unlike materializing an anonymous const value.
fn analyzeNavRef(sema: *Sema, nav_index: InternPool.Nav.Index) Error!Value {
    return sema.analyzeNavRefInner(nav_index, true);
}

/// Reference the `Nav` at the given index, ensuring it is resolved. `is_ref` is `true` when the
/// pointer is used directly and `false` when it will be immediately loaded (a `decl_val`).
///
/// The following pieces have no analog in this comptime-only layer:
///   - `ensureNavResolved(.type/.fully)`: there is no type-only nav resolution, so both kinds map to
///     `analyzeNavVal` (full) and `is_ref` cannot reduce the work.
///   - the `is_runtime` path (threadlocal / dll-import / pcrel extern) emits a runtime pointer (AIR).
///   - `maybeQueueFuncBodyAnalysis`: there is no separate function-body analysis queue.
fn analyzeNavRefInner(sema: *Sema, orig_nav_index: InternPool.Nav.Index, is_ref: bool) Error!Value {
    const ip = sema.intern_pool;
    _ = try sema.analyzeNavVal(orig_nav_index);

    const nav_index = nav: {
        const orig_nav = ip.getNav(orig_nav_index);
        if (orig_nav.resolved.?.is_extern_decl or ip.zigTypeTag(orig_nav.resolved.?.type) == .@"fn") {
            const orig_nav_value = switch (is_ref) {
                false => orig_nav.resolved.?.value,
                true => orig_val: {
                    _ = try sema.analyzeNavVal(orig_nav_index);
                    break :orig_val ip.getNav(orig_nav_index).resolved.?.value;
                },
            };
            switch (ip.indexToKey(orig_nav_value)) {
                .func => |f| if (f.owner_nav.unwrap()) |owner| break :nav owner,
                .@"extern" => |e| break :nav e.owner_nav,
                else => {},
            }
        }
        break :nav orig_nav_index;
    };

    const nav_resolved = ip.getNav(nav_index).resolved.?;
    const ptr_ty = try ip.internPtrType(.{
        .child = nav_resolved.type,
        .flags = .{
            .size = .one,
            .alignment = nav_resolved.@"align",
            .is_const = nav_resolved.@"const",
            .address_space = nav_resolved.@"addrspace",
        },
    });
    return .{ .index = try ip.internPtr(.{
        .ty = ptr_ty,
        .base_addr = .{ .nav = nav_index },
        .byte_offset = 0,
    }) };
}

fn evalFieldPtrLoad(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@backingInt(inst) < sema.zir.instructions.len);
    const ip = sema.intern_pool;
    const pl_node = sema.zir.instructions.items(.data)[@backingInt(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.Field, pl_node.payload_index).data;
    const name = try ip.getOrPutString(sema.gpa, sema.zir.nullTerminatedString(extra.field_name_start), .no_embedded_nulls);
    const object = try sema.loadValue(try sema.resolveInst(extra.lhs));
    return sema.fieldPtrLoad(object, name);
}

fn fieldPtrLoad(sema: *Sema, object: Value, name: InternPool.NullTerminatedString) Error!?Value {
    const ip = sema.intern_pool;

    switch (ip.indexToKey(object.index)) {
        .struct_type, .union_type, .enum_type, .opaque_type => return try sema.fieldValOnType(object.index, name),
        // `E.name` on an error set type yields `error.name`; `anyerror.name` mints a new global error.
        .error_set_type => |err_set| {
            if (err_set.nameIndex(ip, name) == null)
                return sema.fail(sema.block, sema.block.nodeOffset(.zero), "no error named '{s}' in '{f}'", .{ ip.stringSlice(name), Type.fromIndex(object.index).fmt(ip) });
            return .{ .index = try ip.internErr(.{ .ty = object.index, .name = name }) };
        },
        .simple_type => |s| if (s == .anyerror) {
            _ = try ip.getErrorValue(name);
            const set = try ip.singletonErrorSetType(name);
            return .{ .index = try ip.internErr(.{ .ty = set, .name = name }) };
        },
        .simple_value,
        .enum_literal,
        .int_type,
        .anyframe_type,
        .int,
        .float,
        .undef,
        .ptr_type,
        .ptr,
        .slice,
        .err,
        .error_union_type,
        .error_union,
        .func_type,
        .func,
        .@"extern",
        .array_type,
        .vector_type,
        .opt_type,
        .opt,
        .tuple_type,
        .aggregate,
        .enum_tag,
        .un,
        .bitpack,
        => {},
    }

    var inner = object;
    while (ip.indexToKey(inner.index) == .ptr) inner = try sema.loadValue(inner);
    const inner_ty = inner.typeOf(ip).toIndex();
    switch (ip.indexToKey(inner_ty)) {
        .array_type => |at| {
            if (name.eqlSlice("len", ip))
                return .{ .index = try ip.internInt(.{ .ty = .usize_type, .storage = .{ .u64 = at.len } }) };
            return sema.failNoMember(inner_ty, name);
        },
        .tuple_type => |tuple| {
            if (name.eqlSlice("len", ip))
                return .{ .index = try ip.internInt(.{ .ty = .usize_type, .storage = .{ .u64 = tuple.types.len } }) };
            const field_index = try sema.tupleFieldIndex(inner_ty, name);
            return .{ .index = try ip.aggregateElementAt(ip.indexToKey(inner.index).aggregate, field_index) };
        },
        .struct_type => {
            const fld = (try sema.structFieldByName(inner_ty, name)) orelse
                return sema.failBadStructFieldAccess(inner_ty, name);
            // A comptime field's value comes from the type's default, never the aggregate storage
            // (compiler: structFieldVal reads `field_defaults` directly, after resolving layout). A
            // mutable alloc never stores its comptime fields, so reading the slot would surface `undefined`.
            try sema.ensureLayoutResolved(inner_ty);
            if (Type.fromIndex(inner_ty).structFieldIsComptime(fld.index, ip)) {
                return (try Type.fromIndex(inner_ty).structFieldValueComptime(sema, fld.index)).?;
            }
            switch (ip.indexToKey(inner.index)) {
                .undef => return .{ .index = try ip.get(.{ .undef = fld.ty }) },
                .aggregate => |agg| return .{ .index = try ip.aggregateElementAt(agg, fld.index) },
                .bitpack => |bp| {
                    const struct_ty: Type = .fromIndex(inner_ty);
                    var field_bit_offset: u16 = 0;
                    var preceding: u32 = 0;
                    while (preceding < fld.index) : (preceding += 1) {
                        const pname = (try sema.structFieldNameAt(inner_ty, preceding)).?;
                        const pf = (try sema.structFieldByName(inner_ty, pname)).?;
                        field_bit_offset += @intCast(Type.fromIndex(pf.ty).bitSize(ip));
                    }
                    const buf = try sema.gpa.alloc(u8, @intCast((struct_ty.bitSize(ip) + 7) / 8));
                    defer sema.gpa.free(buf);
                    @memset(buf, 0);
                    Value.fromIndex(bp.backing_int_val).writeToPackedMemory(ip, buf, 0);
                    return try Value.readFromPackedMemory(Type.fromIndex(fld.ty), ip, buf, field_bit_offset);
                },
                else => unreachable,
            }
        },
        .union_type => {
            const fld = (try sema.unionFieldByName(inner_ty, name)) orelse
                return sema.failBadUnionFieldAccess(inner_ty, name);
            if (inner.isUndef(ip)) return sema.failWithUseOfUndef();
            // A packed union stores its value as a `.bitpack` backing integer with no active-tag
            // notion -- any field reinterprets the bits (bit offset 0), like a packed struct field.
            if (ip.indexToKey(inner.index) == .bitpack) return try inner.fieldValue(fld.index, ip);
            return try sema.loadUnionField(inner.index, fld.index);
        },
        .ptr_type => |ptr_ty| {
            if (ptr_ty.flags.size == .slice) {
                const s = ip.indexToKey(inner.index).slice;
                if (name.eqlSlice("len", ip)) return .{ .index = s.len };
                if (name.eqlSlice("ptr", ip)) return .{ .index = s.ptr };
            }
            return sema.failNoMember(inner_ty, name);
        },
        .simple_type,
        .simple_value,
        .enum_literal,
        .int_type,
        .anyframe_type,
        .int,
        .float,
        .undef,
        .ptr,
        .slice,
        .error_set_type,
        .err,
        .error_union_type,
        .error_union,
        .func_type,
        .func,
        .@"extern",
        .vector_type,
        .opt_type,
        .opt,
        .enum_type,
        .opaque_type,
        .aggregate,
        .enum_tag,
        .un,
        .bitpack,
        => return sema.failNoMember(inner_ty, name),
    }
}

fn failNoMember(sema: *Sema, ty: InternPool.Index, name: InternPool.NullTerminatedString) Error {
    return sema.fail(sema.block, sema.block.nodeOffset(.zero), "no member named '{s}' in '{f}'", .{ sema.intern_pool.stringSlice(name), Type.fromIndex(ty).fmt(sema.intern_pool) });
}

/// The numeric index of a tuple field named `field_name` (e.g. `@"0"`); errors otherwise.
/// `.len` is handled by the caller. Mirrors the compiler's `tupleFieldIndex`.
fn tupleFieldIndex(sema: *Sema, tuple_ty: InternPool.Index, field_name: InternPool.NullTerminatedString) Error!u32 {
    const ip = sema.intern_pool;
    assert(!field_name.eqlSlice("len", ip));
    if (field_name.toUnsigned(ip)) |field_index| {
        if (field_index < ip.indexToKey(tuple_ty).tuple_type.types.len) return field_index;
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "index '{s}' out of bounds of tuple '{f}'", .{ ip.stringSlice(field_name), Type.fromIndex(tuple_ty).fmt(ip) });
    }
    return sema.fail(sema.block, sema.block.nodeOffset(.zero), "no field named '{s}' in tuple '{f}'", .{ ip.stringSlice(field_name), Type.fromIndex(tuple_ty).fmt(ip) });
}

fn evalFieldPtrNamedLoad(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@backingInt(inst) < sema.zir.instructions.len);
    const pl_node = sema.zir.instructions.items(.data)[@backingInt(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.FieldNamed, pl_node.payload_index).data;
    const field_name = try sema.resolveConstStringIntern(extra.field_name);
    const object = try sema.loadValue(try sema.resolveInst(extra.lhs));
    return sema.fieldPtrLoad(object, field_name);
}

fn evalFieldPtrNamed(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@backingInt(inst) < sema.zir.instructions.len);
    const pl_node = sema.zir.instructions.items(.data)[@backingInt(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.FieldNamed, pl_node.payload_index).data;
    const field_name = try sema.resolveConstStringIntern(extra.field_name);
    const object_ptr = try sema.resolveInst(extra.lhs);
    return sema.fieldPtr(object_ptr, field_name, false);
}

fn resolveConstStringIntern(sema: *Sema, ref: Zir.Inst.Ref) Error!InternPool.NullTerminatedString {
    const ip = sema.intern_pool;
    var agg = try sema.resolveInst(ref);
    if (ip.indexToKey(agg.index) == .slice or ip.indexToKey(agg.index) == .ptr) {
        agg = try sema.derefSliceAsArray(agg);
    }
    const key = ip.indexToKey(agg.index);
    const arr = if (key == .aggregate) ip.indexToKey(key.aggregate.ty) else key;
    if (key != .aggregate or arr != .array_type or arr.array_type.child != .u8_type) {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "expected a comptime string", .{});
    }
    const len: usize = @intCast(arr.array_type.len);
    const bytes = try sema.gpa.alloc(u8, len);
    defer sema.gpa.free(bytes);
    for (bytes, 0..) |*b, i| {
        const elem = try ip.aggregateElementAt(key.aggregate, i);
        b.* = @intCast(ip.indexToKey(elem).int.storage.u64);
    }
    return try ip.getOrPutString(sema.gpa, bytes, .no_embedded_nulls);
}

fn evalCompileError(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const un_node = sema.zir.instructions.items(.data)[@backingInt(inst)].un_node;
    const msg = try sema.resolveConstStringIntern(un_node.operand);
    return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "{s}", .{sema.intern_pool.stringSlice(msg)});
}

fn evalSetEvalBranchQuota(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const un_node = sema.zir.instructions.items(.data)[@backingInt(inst)].un_node;
    const quota = try sema.resolveInt(try sema.resolveInst(un_node.operand), .u32_type);
    sema.branch_quota = @max(sema.branch_quota, @as(u32, @intCast(quota)));
    return null;
}

fn evalSetRuntimeSafety(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const un_node = sema.zir.instructions.items(.data)[@backingInt(inst)].un_node;
    _ = try sema.coerceValueToType(try sema.resolveInst(un_node.operand), .bool_type);
    return null;
}

fn evalTypeName(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const un_node = sema.zir.instructions.items(.data)[@backingInt(inst)].un_node;
    const ty = try sema.resolveDestType(un_node.operand);
    var name: std.Io.Writer.Allocating = .init(sema.gpa);
    defer name.deinit();
    try Type.print(Type.fromIndex(ty), sema.intern_pool, &name.writer);
    return try sema.internStringLiteral(name.written());
}

fn evalErrorName(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    const un_node = sema.zir.instructions.items(.data)[@backingInt(inst)].un_node;
    const operand = try sema.coerceValueToType(try sema.resolveInst(un_node.operand), .anyerror_type);
    const name = ip.indexToKey(operand.index).err.name;
    return try sema.internStringLiteral(ip.stringSlice(name));
}

fn evalUnionInit(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    const pl_node = sema.zir.instructions.items(.data)[@backingInt(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.UnionInit, pl_node.payload_index).data;
    const union_ty = try sema.resolveDestType(extra.union_type);
    if (ip.indexToKey(union_ty) != .union_type) {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "@unionInit: expected union type, found '{f}'", .{Type.fromIndex(union_ty).fmt(ip)});
    }
    const field_name = try sema.resolveConstStringIntern(extra.field_name);
    const field = (try sema.unionFieldByName(union_ty, field_name)) orelse
        return sema.failBadUnionFieldAccess(union_ty, field_name);
    const payload = try sema.coerceValueToType(try sema.resolveInst(extra.init), field.ty);
    try sema.resolveUnionFields(union_ty);
    if (ip.unionFields(union_ty).layout == .@"packed") {
        return try sema.bitCast(.fromIndex(union_ty), payload, sema.block.nodeOffset(sema.srcNodeOffset(inst)));
    }
    const tag_enum = try sema.unionTagEnumType(union_ty);
    const tag_val = (try sema.enumValueFieldIndex(tag_enum, field.index)).?;
    return .{ .index = try ip.internUnion(.{ .ty = union_ty, .tag = tag_val.index, .val = payload.index }) };
}

fn evalFieldTypeRef(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    const pl_node = sema.zir.instructions.items(.data)[@backingInt(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.FieldTypeRef, pl_node.payload_index).data;
    const aggregate_ty = sema.optEuBaseType(try sema.resolveDestType(extra.container_type));
    const field_name = try sema.resolveConstStringIntern(extra.field_name);
    const field_ty: InternPool.Index = switch (ip.indexToKey(aggregate_ty)) {
        .struct_type => ((try sema.structFieldByName(aggregate_ty, field_name)) orelse
            return sema.failBadMemberAccess(aggregate_ty, field_name)).ty,
        .tuple_type => |tuple| ty: {
            const idx = std.fmt.parseInt(u32, ip.stringSlice(field_name), 10) catch
                return sema.failBadMemberAccess(aggregate_ty, field_name);
            if (idx >= tuple.types.len) return sema.failBadMemberAccess(aggregate_ty, field_name);
            break :ty tuple.types[idx];
        },
        .union_type => ((try sema.unionFieldByName(aggregate_ty, field_name)) orelse
            return sema.failBadUnionFieldAccess(aggregate_ty, field_name)).ty,
        else => return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "expected struct or union; found '{f}'", .{Type.fromIndex(aggregate_ty).fmt(ip)}),
    };
    return .{ .index = field_ty };
}

fn evalMergeErrorSets(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    const bin = sema.binData(inst);
    const lhs = try sema.resolveInst(bin.lhs);
    const rhs = try sema.resolveInst(bin.rhs);
    if (Value.typeOf(lhs, ip).index == .bool_type and Value.typeOf(rhs, ip).index == .bool_type) {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "expected error set type, found 'bool' ('||' merges error sets; 'or' performs boolean OR)", .{});
    }
    const lhs_ty = try sema.resolveDestType(bin.lhs);
    const rhs_ty = try sema.resolveDestType(bin.rhs);
    inline for (.{ lhs_ty, rhs_ty }) |ty| {
        if (Type.fromIndex(ty).zigTypeTag(ip) != .error_set) {
            return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "expected error set type, found '{f}'", .{Type.fromIndex(ty).fmt(ip)});
        }
    }
    if (lhs_ty == .anyerror_type or rhs_ty == .anyerror_type) return .{ .index = .anyerror_type };
    return .{ .index = (try sema.errorSetMerge(lhs_ty, rhs_ty)).index };
}

fn errorSetMerge(sema: *Sema, lhs_ty: InternPool.Index, rhs_ty: InternPool.Index) Error!Type {
    const ip = sema.intern_pool;
    const lhs_names = ip.indexToKey(lhs_ty).error_set_type.names;
    const rhs_names = ip.indexToKey(rhs_ty).error_set_type.names;
    const buf = try sema.arena.alloc(InternPool.NullTerminatedString, lhs_names.len + rhs_names.len);
    @memcpy(buf[0..lhs_names.len], lhs_names);
    var n = lhs_names.len;
    for (rhs_names) |name| {
        if (std.mem.indexOfScalar(InternPool.NullTerminatedString, buf[0..n], name) == null) {
            buf[n] = name;
            n += 1;
        }
    }
    return .fromIndex(try ip.internErrorSetType(buf[0..n]));
}

fn evalHasField(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    const pl_node = sema.zir.instructions.items(.data)[@backingInt(inst)].pl_node;
    const bin = sema.zir.extraData(Zir.Inst.Bin, pl_node.payload_index).data;
    const ty_src = sema.block.builtinCallArgSrc(pl_node.src_node, 0);
    const ty = try sema.resolveDestType(bin.lhs);
    const field_name = try sema.resolveConstStringIntern(bin.rhs);
    try sema.ensureLayoutResolved(ty);
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
            .struct_type => break :hf ip.loadStructType(ty).nameIndex(ip, field_name) != null,
            // The compiler queries the tag enum's names; the REPL's union carries its field names
            // directly (its `enum_tag_type` stays `.none`), so query them.
            .union_type => break :hf (try sema.unionFieldByName(ty, field_name)) != null,
            .enum_type => break :hf ip.loadEnumType(ty).nameIndex(ip, field_name) != null,
            .array_type => break :hf field_name.eqlSlice("len", ip),
            else => {},
        }
        return sema.fail(sema.block, ty_src, "type '{f}' does not support '@hasField'", .{Type.fromIndex(ty).fmt(ip)});
    };
    return .{ .index = if (has_field) .bool_true else .bool_false };
}

fn evalHasDecl(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const pl_node = sema.zir.instructions.items(.data)[@backingInt(inst)].pl_node;
    const bin = sema.zir.extraData(Zir.Inst.Bin, pl_node.payload_index).data;
    const container_type = try sema.resolveDestType(bin.lhs);
    const decl_name = try sema.resolveConstStringIntern(bin.rhs);
    if (sema.containerNamespace(container_type) == null) {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "expected struct, enum, union, or opaque; found '{f}'", .{Type.fromIndex(container_type).fmt(sema.intern_pool)});
    }
    // Resolve through the namespace's decls, not by re-walking one defining ZIR: the root
    // namespace's decls are bound across many line files (its own ZIR is absent), and a
    // regular container's decls are scanned lazily on lookup. A private decl is only a hit
    // from within its own file, matching the compiler's accessibility check.
    const namespace = sema.getNamespaceIndex(container_type) orelse return .{ .index = .bool_false };
    if (try sema.lookupInNamespace(namespace, decl_name)) |lookup| {
        if (lookup.accessible) return .{ .index = .bool_true };
    }
    return .{ .index = .bool_false };
}

fn setAggregateElement(
    sema: *Sema,
    old: Value,
    agg_ty: InternPool.Index,
    index: u32,
    elem: Value,
) Error!Value {
    const ip = sema.intern_pool;
    const count = if (ip.indexToKey(agg_ty) == .struct_type)
        try sema.structFieldCount(agg_ty)
    else
        @as(u32, @intCast(ip.aggregateElementCount(agg_ty)));
    const elems = try sema.gpa.alloc(InternPool.Index, count);
    defer sema.gpa.free(elems);
    const old_key = ip.indexToKey(old.index);
    if (old_key == .aggregate) {
        for (elems, 0..) |*e, i| e.* = try ip.aggregateElementAt(old_key.aggregate, i);
    } else {
        @memset(elems, .undef);
    }
    elems[index] = elem.index;
    return .{ .index = try ip.internAggregate(.{ .ty = agg_ty, .storage = .{ .elems = elems } }) };
}

pub fn storePtrVal(sema: *Sema, ptr: Value, value: Value) Error!void {
    const ip = sema.intern_pool;
    const src = sema.block.nodeOffset(.zero);
    const ptr_ty = ptr.typeOf(ip);
    // Where the compiler emits an AIR store to runtime memory, the runtime layer retargets the pointer
    // onto an alloc-backed copy of the mutable global's value; the reused comptime store mutates it and
    // `writeBack` persists the result. Its error results flow through the same arms as a comptime store.
    var target: ?runtime.StoreTarget = null;
    var result = try comptime_ptr_access.storeComptimePtr(sema, ptr, value);
    if (result == .runtime_store) {
        if (try runtime.retargetStore(sema, ptr)) |t| {
            target = t;
            result = try comptime_ptr_access.storeComptimePtr(sema, t.ptr, value);
        }
    }
    switch (result) {
        .success => {
            if (target) |t| try runtime.writeBack(sema, t);
        },
        .runtime_store => return sema.fail(sema.block, src, "unable to evaluate comptime expression: store requires runtime memory", .{}),
        .comptime_field_mismatch => return sema.fail(sema.block, src, "value stored in comptime field does not match the default value of the field", .{}),
        .undef => return sema.failWithUseOfUndef(),
        .err_payload => |err_name| return sema.fail(sema.block, src, "attempt to unwrap error: {f}", .{err_name.fmt(ip)}),
        .null_payload => return sema.fail(sema.block, src, "attempt to use null value", .{}),
        .inactive_union_field => return sema.fail(sema.block, src, "access of inactive union field", .{}),
        .needed_well_defined => |ty| return sema.fail(sema.block, src, "comptime dereference requires '{f}' to have a well-defined layout", .{ty.fmt(ip)}),
        .out_of_bounds => |ty| return sema.fail(sema.block, src, "dereference of '{f}' exceeds bounds of containing decl of type '{f}'", .{ ptr_ty.fmt(ip), ty.fmt(ip) }),
        .exceeds_host_size => return sema.fail(sema.block, src, "bit-pointer target exceeds host size", .{}),
    }
}

fn evalOptEuBasePtrInit(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@backingInt(inst) < sema.zir.instructions.len);
    const ip = sema.intern_pool;
    const un_node = sema.zir.instructions.items(.data)[@backingInt(inst)].un_node;
    var base_ptr = try sema.resolveInst(un_node.operand);
    while (true) switch (ip.indexToKey(ip.indexToKey(base_ptr.typeOf(ip).toIndex()).ptr_type.child)) {
        .opt_type => base_ptr = try sema.optPayloadPtr(base_ptr, true),
        .error_union_type => base_ptr = try sema.errUnionPayloadPtr(base_ptr, true),
        else => break,
    };
    return base_ptr;
}

fn evalValidatePtrStructInit(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@backingInt(inst) < sema.zir.instructions.len);
    const datas = sema.zir.instructions.items(.data);
    const extra = sema.zir.extraData(Zir.Inst.Block, datas[@backingInt(inst)].pl_node.payload_index);
    const body = sema.zir.bodySlice(extra.end, extra.data.body_len);
    if (body.len == 0) return null;

    const ip = sema.intern_pool;
    const first = sema.zir.extraData(Zir.Inst.Field, datas[@backingInt(body[0])].pl_node.payload_index).data;
    const object_ptr = try sema.resolveInst(first.lhs);
    const struct_ty = ip.indexToKey(ip.indexToKey(object_ptr.index).ptr.ty).ptr_type.child;

    if (ip.indexToKey(struct_ty) == .union_type) {
        if (body.len != 1) {
            return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "cannot initialize multiple union fields at once; unions can only have one active field", .{});
        }
        return null;
    }

    const stored = try sema.gpa.alloc(InternPool.NullTerminatedString, body.len);
    defer sema.gpa.free(stored);
    for (body, stored) |field_ptr, *n| {
        const fp = sema.zir.extraData(Zir.Inst.Field, datas[@backingInt(field_ptr)].pl_node.payload_index).data;
        n.* = try ip.getOrPutString(sema.gpa, sema.zir.nullTerminatedString(fp.field_name_start), .no_embedded_nulls);
    }

    const count = try sema.structFieldCount(struct_ty);
    var i: u32 = 0;
    while (i < count) : (i += 1) {
        const name = (try sema.structFieldNameAt(struct_ty, i)).?;
        if (std.mem.indexOfScalar(InternPool.NullTerminatedString, stored, name) != null) continue;
        const default = try sema.structFieldDefault(struct_ty, name);
        if (default == .none) {
            return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "missing struct field: {s}", .{ip.stringSlice(name)});
        }
        // Store the default through the field pointer, not by poking the alloc directly: the
        // init target may be a field of an aggregate (a nested init), whose base is not a
        // comptime_alloc. Mirrors the compiler's storePtr2 in validateStructInit.
        const default_field_ptr = try sema.structFieldPtrByIndex(object_ptr, i, .fromIndex(struct_ty));
        try sema.storePtrVal(default_field_ptr, .{ .index = default });
    }
    // A comptime field is addressed by a standalone `comptime_field` pointer, so the stores above never
    // reach the alloc's storage for it. Fill those slots from their type defaults so a whole-value load
    // carries them, matching the compiler's guarantee that a struct value is complete.
    const obj_ptr = ip.indexToKey(object_ptr.index).ptr;
    if (obj_ptr.base_addr == .comptime_alloc and obj_ptr.byte_offset == 0)
        try sema.fillComptimeAllocFields(obj_ptr, struct_ty);
    return null;
}

fn evalValidateStructInitTy(sema: *Sema, inst: Zir.Inst.Index, comptime is_result_ty: bool) Error!?Value {
    const un_node = sema.zir.instructions.items(.data)[@backingInt(inst)].un_node;
    const ty = try sema.resolveDestType(un_node.operand);
    const struct_ty = if (is_result_ty) Type.fromIndex(ty).optEuBaseType(sema.intern_pool).index else ty;
    switch (sema.intern_pool.indexToKey(struct_ty)) {
        .struct_type, .union_type => return null,
        else => {
            return sema.failWithStructInitNotSupported(sema.block.nodeOffset(sema.srcNodeOffset(inst)), .fromIndex(struct_ty));
        },
    }
}

fn evalStructInitFieldType(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const datas = sema.zir.instructions.items(.data);
    const ft = sema.zir.extraData(Zir.Inst.FieldType, datas[@backingInt(inst)].pl_node.payload_index).data;
    const container_ty = Type.fromIndex((try sema.resolveInst(ft.container_type)).index).optEuBaseType(sema.intern_pool).index;
    const name = try sema.intern_pool.getOrPutString(sema.gpa, sema.zir.nullTerminatedString(ft.name_start), .no_embedded_nulls);
    const field_ty = switch (sema.intern_pool.indexToKey(container_ty)) {
        .struct_type => ((try sema.structFieldByName(container_ty, name)) orelse
            return sema.failBadStructFieldAccess(container_ty, name)).ty,
        .union_type => ((try sema.unionFieldByName(container_ty, name)) orelse
            return sema.failBadUnionFieldAccess(container_ty, name)).ty,
        else => {
            return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "struct init: initializer type is not a struct or union", .{});
        },
    };
    return .{ .index = field_ty };
}

fn failWithInvalidComptimeFieldStore(sema: *Sema, init_src: LazySrcLoc, container_ty: InternPool.Index, field_index: usize) Error {
    return sema.failWithOwnedErrorMsg(sema.block, msg: {
        const msg = try sema.errMsg(init_src, "value stored in comptime field does not match the default value of the field", .{});
        errdefer msg.destroy(sema.gpa);
        const struct_type = switch (sema.intern_pool.indexToKey(container_ty)) {
            .struct_type => |st| st,
            else => break :msg msg,
        };
        try sema.errNote(.{
            .base_node_inst = struct_type.declInst(),
            .offset = .{ .container_field_value = @intCast(field_index) },
        }, msg, "default value set here", .{});
        break :msg msg;
    });
}

fn evalStructInit(sema: *Sema, inst: Zir.Inst.Index, comptime is_ref: bool) Error!?Value {
    const ip = sema.intern_pool;
    const datas = sema.zir.instructions.items(.data);
    const extra = sema.zir.extraData(Zir.Inst.StructInit, datas[@backingInt(inst)].pl_node.payload_index);

    const first = sema.zir.extraData(Zir.Inst.StructInit.Item, extra.end).data;
    const first_ft = sema.zir.extraData(Zir.Inst.FieldType, datas[@backingInt(first.field_type)].pl_node.payload_index).data;
    const result_ty = (try sema.resolveInst(first_ft.container_type)).index;
    const struct_ty = Type.fromIndex(result_ty).optEuBaseType(ip).index;
    switch (ip.indexToKey(struct_ty)) {
        .struct_type => {},
        .union_type => return try sema.evalStructInitUnion(struct_ty, result_ty, inst, is_ref),
        else => {
            return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "struct init: initializer type is not a struct or union", .{});
        },
    }

    const count = try sema.structFieldCount(struct_ty);
    try sema.ensureLayoutResolved(struct_ty);
    const elems = try sema.gpa.alloc(InternPool.Index, count);
    defer sema.gpa.free(elems);
    @memset(elems, .none);

    var extra_index = extra.end;
    for (0..extra.data.fields_len) |_| {
        const item = sema.zir.extraData(Zir.Inst.StructInit.Item, extra_index);
        extra_index = item.end;
        const ft = sema.zir.extraData(Zir.Inst.FieldType, datas[@backingInt(item.data.field_type)].pl_node.payload_index).data;
        const name = try ip.getOrPutString(sema.gpa, sema.zir.nullTerminatedString(ft.name_start), .no_embedded_nulls);
        const field = (try sema.structFieldByName(struct_ty, name)) orelse
            return sema.failBadStructFieldAccess(struct_ty, name);
        const raw = try sema.resolveInst(item.data.init);
        const coerced = try sema.coerceValueToType(raw, field.ty);
        elems[field.index] = coerced.index;
        // A value stored into a comptime field must equal the field's comptime default. In the
        // comptime-only interpreter every init value is known, so the compiler's runtime
        // `failWithNeededComptime` branch never applies; interned identity is the compiler's `eql`.
        if (Type.fromIndex(struct_ty).structFieldIsComptime(field.index, ip)) {
            const default_value = (try Type.fromIndex(struct_ty).structFieldValueComptime(sema, field.index)).?;
            if (!coerced.eql(default_value, Type.fromIndex(struct_ty).fieldType(field.index, ip), ip))
                return sema.failWithInvalidComptimeFieldStore(sema.block.nodeOffset(sema.srcNodeOffset(inst)), struct_ty, field.index);
        }
    }

    return try sema.finishStructInit(struct_ty, result_ty, elems, is_ref);
}

fn evalStructInitUnion(sema: *Sema, union_ty: InternPool.Index, result_ty: InternPool.Index, inst: Zir.Inst.Index, comptime is_ref: bool) Error!Value {
    const ip = sema.intern_pool;
    const datas = sema.zir.instructions.items(.data);
    const extra = sema.zir.extraData(Zir.Inst.StructInit, datas[@backingInt(inst)].pl_node.payload_index);
    if (extra.data.fields_len != 1) {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "union initialization expects exactly one field", .{});
    }

    const item = sema.zir.extraData(Zir.Inst.StructInit.Item, extra.end).data;
    const ft = sema.zir.extraData(Zir.Inst.FieldType, datas[@backingInt(item.field_type)].pl_node.payload_index).data;
    const name = try ip.getOrPutString(sema.gpa, sema.zir.nullTerminatedString(ft.name_start), .no_embedded_nulls);
    const field = (try sema.unionFieldByName(union_ty, name)) orelse
        return sema.failBadUnionFieldAccess(union_ty, name);

    const raw = try sema.resolveInst(item.init);
    const val = (try sema.coerceValueToType(raw, field.ty)).index;

    if (Type.fromIndex(union_ty).containerLayout(ip) == .@"packed") {
        const union_val = try sema.bitCast(.fromIndex(union_ty), Value.fromIndex(val), sema.block.nodeOffset(sema.srcNodeOffset(inst)));
        const final = if (result_ty == union_ty) union_val else try sema.coerceValueToType(union_val, result_ty);
        return if (is_ref) try sema.materializeConstPtr(final) else final;
    }

    const tag_enum = try sema.unionTagEnumType(union_ty);
    const tag_index = (try sema.enumFieldIndex(tag_enum, name)) orelse
        return sema.failBadMemberAccess(tag_enum, name);
    if (tag_index != field.index) {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "union field order does not match tag enum field order", .{});
    }
    if ((try sema.enumFieldCount(tag_enum)) != try sema.unionFieldCount(union_ty)) {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "enum field missing from union", .{});
    }
    const tag = (try sema.enumValueFieldIndex(tag_enum, tag_index)).?;
    const value: Value = .{ .index = try ip.internUnion(.{ .ty = union_ty, .tag = tag.index, .val = val }) };
    const final = if (result_ty == union_ty) value else try sema.coerceValueToType(value, result_ty);
    return if (is_ref) try sema.materializeConstPtr(final) else final;
}

fn evalStructInitEmpty(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const un_node = sema.zir.instructions.items(.data)[@backingInt(inst)].un_node;
    const obj_ty = (try sema.coerceValueToType(try sema.resolveInst(un_node.operand), .type_type)).index;
    try sema.ensureLayoutResolved(obj_ty);
    return switch (sema.intern_pool.indexToKey(obj_ty)) {
        .struct_type, .tuple_type => try sema.structInitEmpty(obj_ty),
        .array_type, .vector_type => try sema.arrayInitEmpty(obj_ty),
        .union_type => sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "union initializer must initialize one field", .{}),
        else => sema.failWithArrayInitNotSupported(sema.block.nodeOffset(sema.srcNodeOffset(inst)), .fromIndex(obj_ty)),
    };
}

fn structInitEmpty(sema: *Sema, struct_ty: InternPool.Index) Error!Value {
    const count = try sema.structFieldCount(struct_ty);
    const elems = try sema.gpa.alloc(InternPool.Index, count);
    defer sema.gpa.free(elems);
    @memset(elems, .none);
    return try sema.finishStructInit(struct_ty, struct_ty, elems, false);
}

fn evalStructInitEmptyResult(sema: *Sema, inst: Zir.Inst.Index, comptime is_ref: bool) Error!?Value {
    const ip = sema.intern_pool;
    const un_node = sema.zir.instructions.items(.data)[@backingInt(inst)].un_node;
    // Generic poison means an untyped anonymous empty init.
    const ty_operand = try sema.resolveDestType(un_node.operand);
    if (ty_operand == .generic_poison_type) {
        const empty: Value = .{ .index = .empty_tuple };
        return if (is_ref) try sema.materializeConstPtr(empty) else empty;
    }
    // For `&.{}` the operand is the pointer result type; the init itself is the pointee,
    // a zero-length array for a slice/many-ptr (carrying its sentinel) or the child type
    // for a single/C pointer.
    const init_ty = if (is_ref) blk: {
        const ptr_ty = sema.optEuBaseType(ty_operand);
        const ptr_info = ip.indexToKey(ptr_ty).ptr_type;
        switch (ptr_info.flags.size) {
            .slice, .many => break :blk try ip.internArrayType(.{
                .len = 0,
                .child = ptr_info.child,
                .sentinel = ptr_info.sentinel,
            }),
            .one, .c => {
                if (ptr_info.child == .anyopaque_type) {
                    return try sema.materializeConstPtr(.{ .index = .empty_tuple });
                }
                break :blk ptr_info.child;
            },
        }
    } else ty_operand;
    const obj_ty = sema.optEuBaseType(init_ty);
    const base: Value = switch (ip.indexToKey(obj_ty)) {
        .struct_type, .tuple_type => try sema.structInitEmpty(obj_ty),
        .array_type, .vector_type => try sema.arrayInitEmpty(obj_ty),
        .union_type => {
            return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "union initializer must initialize one field", .{});
        },
        else => {
            return sema.failWithArrayInitNotSupported(sema.block.nodeOffset(sema.srcNodeOffset(inst)), .fromIndex(obj_ty));
        },
    };
    const value = if (init_ty == obj_ty) base else try sema.coerceValueToType(base, init_ty);
    return if (is_ref) try sema.materializeConstPtr(value) else value;
}

fn arrayInitEmpty(sema: *Sema, obj_ty: InternPool.Index) Error!Value {
    const key = sema.intern_pool.indexToKey(obj_ty);
    const arr_len = switch (key) {
        .array_type => |at| at.len,
        .vector_type => |vt| vt.len,
        else => unreachable,
    };
    if (arr_len != 0) {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "expected {d} {s} elements; found 0", .{ arr_len, if (key == .array_type) "array" else "vector" });
    }
    return .{ .index = try sema.intern_pool.internAggregate(.{ .ty = obj_ty, .storage = .{ .elems = &.{} } }) };
}

fn finishStructInit(sema: *Sema, struct_ty: InternPool.Index, result_ty: InternPool.Index, elems: []InternPool.Index, comptime is_ref: bool) Error!Value {
    const ip = sema.intern_pool;
    for (elems, 0..) |*elem, i| {
        if (elem.* != .none) continue;
        const name = (try sema.structFieldNameAt(struct_ty, @intCast(i))).?;
        const default = try sema.structFieldDefault(struct_ty, name);
        if (default == .none) {
            return sema.fail(sema.block, sema.block.nodeOffset(.zero), "missing struct field: {s}", .{ip.stringSlice(name)});
        }
        elem.* = default;
    }

    const value: Value = switch (Type.fromIndex(struct_ty).containerLayout(ip)) {
        .auto, .@"extern" => .{ .index = try ip.internAggregate(.{ .ty = struct_ty, .storage = .{ .elems = elems } }) },
        .@"packed" => blk: {
            try sema.ensureLayoutResolved(struct_ty);
            const packed_ty: Type = .fromIndex(struct_ty);
            const buf = try sema.gpa.alloc(u8, @intCast((packed_ty.bitSize(ip) + 7) / 8));
            defer sema.gpa.free(buf);
            @memset(buf, 0);

            var bit_offset: u16 = 0;
            for (elems) |elem| {
                const field_val = Value.fromIndex(elem);
                field_val.writeToPackedMemory(ip, buf, bit_offset);
                bit_offset += @intCast(field_val.typeOf(ip).bitSize(ip));
            }
            assert(bit_offset == packed_ty.bitSize(ip));
            break :blk try Value.readFromPackedMemory(packed_ty, ip, buf, 0);
        },
    };
    const final = if (result_ty == struct_ty) value else try sema.coerceValueToType(value, result_ty);
    return if (is_ref) try sema.materializeConstPtr(final) else final;
}

fn evalRef(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@backingInt(inst) < sema.zir.instructions.len);

    const un_tok = sema.zir.instructions.items(.data)[@backingInt(inst)].un_tok;
    assert(un_tok.operand != .none);

    const value = try sema.resolveInst(un_tok.operand);
    return try sema.materializeConstPtr(value);
}

fn materializeConstPtr(sema: *Sema, value: Value) Error!Value {
    const ip = sema.intern_pool;
    const ptr_ty = try ip.internPtrType(.{
        .child = Value.typeOf(value, ip).index,
        .flags = .{ .size = .one, .is_const = true },
    });
    return .{ .index = try sema.uavPtr(ptr_ty, value.index) };
}

fn evalElemPtrLoad(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const bin = sema.binData(inst);
    assert(bin.lhs != .none);
    assert(bin.rhs != .none);

    const indexable = try sema.loadValue(try sema.resolveInst(bin.lhs));
    return try sema.elemVal(indexable, bin.rhs);
}

fn evalElemPtrNode(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const bin = sema.binData(inst);
    const array_ptr = try sema.resolveInst(bin.lhs);
    const index = try sema.resolveArrayLen(bin.rhs);
    return try sema.elemPtr(array_ptr, index);
}

fn evalArrayInitElemPtr(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const datas = sema.zir.instructions.items(.data);
    const extra = sema.zir.extraData(Zir.Inst.ElemPtrImm, datas[@backingInt(inst)].pl_node.payload_index).data;
    const array_ptr = try sema.resolveInst(extra.ptr);
    return try sema.elemPtr(array_ptr, extra.index);
}

fn unionFieldPtr(sema: *Sema, union_ptr: Value, field_name: InternPool.NullTerminatedString, union_ty: Type, comptime initializing: bool) Error!Value {
    const ip = sema.intern_pool;
    ip.assertLayoutResolved(union_ty.index);
    const field = (try sema.unionFieldByName(union_ty.index, field_name)) orelse
        return sema.failBadUnionFieldAccess(union_ty.index, field_name);

    if (initializing and Type.fromIndex(field.ty).classify(ip) == .no_possible_value) {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "cannot initialize union field with uninstantiable type '{f}'", .{Type.fromIndex(field.ty).fmt(ip)});
    }

    switch (union_ty.containerLayout(ip)) {
        .auto => if (initializing) {
            const field_ty: Type = .fromIndex(field.ty);
            const payload_val = (try field_ty.onePossibleValue(sema)) orelse try sema.undefValue(field_ty);
            const tag_enum = try sema.unionTagEnumType(union_ty.index);
            const field_tag = (try sema.enumValueFieldIndex(tag_enum, field.index)).?;
            const new_union_val: Value = .fromIndex(try ip.internUnion(.{ .ty = union_ty.index, .tag = field_tag.index, .val = payload_val.index }));
            try sema.storePtrVal(union_ptr, new_union_val);
        } else {
            const union_val = try sema.loadValue(union_ptr);
            if (union_val.isUndef(ip)) return sema.failWithUseOfUndef();
            _ = try sema.loadUnionField(union_val.index, field.index);
        },
        .@"packed", .@"extern" => {},
    }
    return try union_ptr.ptrField(field.index, ip);
}

fn structFieldPtrByIndex(sema: *Sema, struct_ptr: Value, field_index: u32, struct_ty: Type) Error!Value {
    const ip = sema.intern_pool;
    ip.assertLayoutResolved(struct_ty.index);
    const struct_ptr_ty = struct_ptr.typeOf(ip);
    if (struct_ty.structFieldIsComptime(field_index, ip)) {
        const field_ptr_ty = try struct_ptr_ty.fieldPtrType(field_index, ip);
        // A declared struct resolves its field defaults lazily, so the comptime field value is fetched
        // through `structFieldValueComptime`; the compiler reads its eagerly-reified `field_defaults`.
        const comptime_val = (try struct_ty.structFieldValueComptime(sema, field_index)).?;
        return .{ .index = try ip.internPtr(.{
            .ty = field_ptr_ty.index,
            .base_addr = .{ .comptime_field = comptime_val.index },
            .byte_offset = 0,
        }) };
    }
    return try struct_ptr.ptrField(field_index, ip);
}

fn tupleElemPtr(sema: *Sema, tuple_ptr: Value, index: u64) Error!Value {
    const ip = sema.intern_pool;
    const tuple_ptr_ty = tuple_ptr.typeOf(ip);
    assert(tuple_ptr_ty.isSinglePointer(ip));
    const tuple_ty = tuple_ptr_ty.childType(ip);
    assert(tuple_ty.isTuple(ip));

    const field_count = ip.indexToKey(tuple_ty.index).tuple_type.types.len;
    if (field_count == 0) {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "indexing into empty tuple is not allowed", .{});
    }
    if (index >= field_count) {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "index {d} outside tuple of length {d}", .{ index, field_count });
    }

    return try sema.structFieldPtrByIndex(tuple_ptr, @intCast(index), tuple_ty);
}

fn elemPtr(sema: *Sema, array_ptr: Value, index: u64) Error!Value {
    const ip = sema.intern_pool;
    const indexable_ptr_ty = array_ptr.typeOf(ip);
    const indexable_ty = switch (indexable_ptr_ty.zigTypeTag(ip)) {
        .pointer => indexable_ptr_ty.childType(ip),
        else => return sema.fail(sema.block, sema.block.nodeOffset(.zero), "expected pointer, found '{f}'", .{indexable_ptr_ty.fmt(ip)}),
    };
    try sema.checkIndexable(indexable_ty);
    try sema.ensureLayoutResolved(indexable_ty.index);
    return switch (indexable_ty.zigTypeTag(ip)) {
        .vector => try sema.elemPtrVector(array_ptr, index),
        .array => try sema.elemPtrArray(array_ptr, index),
        .@"struct" => try sema.tupleElemPtr(array_ptr, index),
        else => e: {
            const indexable = try sema.loadValue(array_ptr);
            try sema.ensureLayoutResolved(indexable.typeOf(ip).childType(ip).index);
            break :e try sema.elemPtrOneLayerOnly(indexable, index);
        },
    };
}

/// Asserts `indexable` is an indexable pointer whose child type has its layout already resolved.
fn elemPtrOneLayerOnly(sema: *Sema, indexable: Value, index: u64) Error!Value {
    const ip = sema.intern_pool;
    const indexable_ty = indexable.typeOf(ip);
    assert(indexable_ty.isIndexable(ip));
    assert(indexable_ty.zigTypeTag(ip) == .pointer);
    const child_ty = indexable_ty.childType(ip);
    return switch (indexable_ty.ptrInfo(ip).flags.size) {
        .slice => try sema.elemPtrSlice(indexable, index),
        .many, .c => try indexable.ptrElem(index, ip),
        .one => switch (child_ty.zigTypeTag(ip)) {
            .vector => try sema.elemPtrVector(indexable, index),
            .array => try sema.elemPtrArray(indexable, index),
            .@"struct" => try sema.tupleElemPtr(indexable, index),
            else => unreachable, // guaranteed by checkIndexable
        },
    };
}

fn elemPtrArray(sema: *Sema, array_ptr: Value, index: u64) Error!Value {
    const ip = sema.intern_pool;
    const array_ty = array_ptr.typeOf(ip).childType(ip).index;
    const at = ip.indexToKey(array_ty).array_type;
    const array_sent = at.sentinel != .none;
    const array_len_s = at.len + @intFromBool(array_sent);
    if (array_len_s == 0) {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "cannot index into empty array", .{});
    }
    if (index >= array_len_s) {
        const sentinel_label: []const u8 = if (array_sent) " +1 (sentinel)" else "";
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "index {d} outside array of length {d}{s}", .{ index, at.len, sentinel_label });
    }
    return try array_ptr.ptrElem(index, ip);
}

fn elemPtrVector(sema: *Sema, array_ptr: Value, index: u64) Error!Value {
    const ip = sema.intern_pool;
    const parent_ty = array_ptr.typeOf(ip).index;
    const vector_ptr_info = ip.indexToKey(parent_ty).ptr_type;
    const vt = ip.indexToKey(vector_ptr_info.child).vector_type;
    if (vt.len == 0) {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "cannot index into empty vector", .{});
    }
    if (index >= vt.len) {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "index {d} outside vector of length {d}", .{ index, vt.len });
    }
    const elem_ptr_ty = try ip.internPtrType(.{
        .child = vt.child,
        .flags = .{
            .size = .one,
            .alignment = vector_ptr_info.flags.alignment,
            .is_const = vector_ptr_info.flags.is_const,
            .is_volatile = vector_ptr_info.flags.is_volatile,
            .is_allowzero = vector_ptr_info.flags.is_allowzero,
            .address_space = vector_ptr_info.flags.address_space,
            .vector_index = @fromBackingInt(@intCast(index)),
        },
        .packed_offset = .{
            .host_size = @intCast(vt.len),
            .bit_offset = 0,
        },
    });
    return .{ .index = try ip.getCoerced(array_ptr.index, elem_ptr_ty) };
}

fn elemPtrSlice(sema: *Sema, slice_val: Value, index: u64) Error!Value {
    const ip = sema.intern_pool;
    const slice_ty = slice_val.typeOf(ip).index;
    const slice_sent = ip.indexToKey(slice_ty).ptr_type.sentinel != .none;
    try sema.ensureLayoutResolved(ip.indexToKey(slice_ty).ptr_type.child);
    const s = ip.indexToKey(slice_val.index).slice;
    const len = try sema.resolveUsizeInt(.{ .index = s.len });
    const len_s = len + @intFromBool(slice_sent);
    if (len_s == 0) {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "cannot index into empty slice", .{});
    }
    if (index >= len_s) {
        const sentinel_label: []const u8 = if (slice_sent) " +1 (sentinel)" else "";
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "index {d} outside slice of length {d}{s}", .{ index, len, sentinel_label });
    }
    return try slice_val.ptrElem(index, ip);
}

fn evalValidatePtrArrayInit(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    const datas = sema.zir.instructions.items(.data);
    const extra = sema.zir.extraData(Zir.Inst.Block, datas[@backingInt(inst)].pl_node.payload_index);
    const body = sema.zir.bodySlice(extra.end, extra.data.body_len);
    if (body.len == 0) return null;
    const first = sema.zir.extraData(Zir.Inst.ElemPtrImm, datas[@backingInt(body[0])].pl_node.payload_index).data;
    const array_ptr = try sema.resolveInst(first.ptr);
    const array_ty = ip.indexToKey(ip.indexToKey(array_ptr.index).ptr.ty).ptr_type.child;
    switch (Type.fromIndex(array_ty).zigTypeTag(ip)) {
        .array, .vector => {},
        else => return null,
    }
    const array_len = Type.fromIndex(array_ty).arrayLen(ip);
    if (body.len != array_len) {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "expected {d} array elements; found {d}", .{ array_len, body.len });
    }
    return null;
}

fn analyzeSlice(sema: *Sema, ptr_ptr: Value, start: u64, end_opt: ?u64, sentinel_opt: ?Value, by_length: bool) Error!?Value {
    const ip = sema.intern_pool;
    // Slice expressions operate on a pointer to the sliced object; for a non-array operand it is a
    // double pointer. Mirrors the compiler's `analyzeSlice`; the runtime `analyzeSlicePtr` +
    // `analyzePtrArithmetic` pipeline is replaced by the comptime element-pointer path (`ptrElem`).
    const ptr_ptr_ty = ptr_ptr.typeOf(ip);
    const ptr_ptr_child_ty: Type = switch (ip.indexToKey(ptr_ptr_ty.index)) {
        .ptr_type => |pt| .fromIndex(pt.child),
        else => return sema.fail(sema.block, sema.block.nodeOffset(.zero), "expected pointer, found '{f}'", .{ptr_ptr_ty.fmt(ip)}),
    };

    var array_ty = ptr_ptr_child_ty;
    var slice_ty = ptr_ptr_ty;
    var ptr_or_slice = ptr_ptr;
    var elem_ty: InternPool.Index = undefined;
    var ptr_sentinel: InternPool.Index = .none;
    switch (ptr_ptr_child_ty.zigTypeTag(ip)) {
        .array => {
            const arr = ip.indexToKey(ptr_ptr_child_ty.index).array_type;
            ptr_sentinel = arr.sentinel;
            elem_ty = arr.child;
        },
        .pointer => {
            const inner = ip.indexToKey(ptr_ptr_child_ty.index).ptr_type;
            switch (inner.flags.size) {
                .one => {
                    ptr_or_slice = try sema.loadValue(ptr_ptr);
                    switch (ip.indexToKey(inner.child)) {
                        .array_type => |arr| {
                            ptr_sentinel = arr.sentinel;
                            slice_ty = ptr_ptr_child_ty;
                            array_ty = .fromIndex(inner.child);
                            elem_ty = arr.child;
                        },
                        // Slice of a single-item pointer to a non-array: `(&x)[0..1]` yields `*[1]T` ->
                        // `[]T`. Bounds must be [0..0], [0..1], or [1..1].
                        else => {
                            if (end_opt == null) {
                                return sema.fail(sema.block, sema.block.nodeOffset(.zero), "slice of single-item pointer must be bounded", .{});
                            }
                            const bound = if (by_length) start + end_opt.? else end_opt.?;
                            if (start != bound) {
                                if (start != 0 or bound != 1) {
                                    return sema.fail(sema.block, sema.block.nodeOffset(.zero), "slice of single-item pointer must have bounds [0..0], [0..1], or [1..1]", .{});
                                }
                            } else if (bound > 1) {
                                return sema.fail(sema.block, sema.block.nodeOffset(.zero), "end index {d} out of bounds for slice of single-item pointer", .{bound});
                            }
                            array_ty = .fromIndex(try ip.internArrayType(.{ .len = 1, .child = inner.child }));
                            slice_ty = .fromIndex(try ip.internPtrType(.{ .child = array_ty.index, .flags = .{
                                .alignment = inner.flags.alignment,
                                .is_const = inner.flags.is_const,
                                .is_allowzero = inner.flags.is_allowzero,
                                .is_volatile = inner.flags.is_volatile,
                                .address_space = inner.flags.address_space,
                            } }));
                            elem_ty = inner.child;
                            // A single-item pointer cannot be indexed, so reinterpret it as a many-item
                            // pointer, as the compiler coerces to `[*]T` before the slice arithmetic.
                            ptr_or_slice = .fromIndex(try ip.getCoerced(ptr_or_slice.index, try ip.internPtrType(.{ .child = inner.child, .flags = .{ .size = .many, .is_const = inner.flags.is_const } })));
                        },
                    }
                },
                .many, .c => {
                    ptr_or_slice = try sema.loadValue(ptr_ptr);
                    slice_ty = ptr_ptr_child_ty;
                    array_ty = ptr_ptr_child_ty;
                    elem_ty = inner.child;
                    ptr_sentinel = inner.sentinel;
                },
                .slice => {
                    ptr_or_slice = try sema.loadValue(ptr_ptr);
                    slice_ty = ptr_ptr_child_ty;
                    array_ty = ptr_ptr_child_ty;
                    elem_ty = inner.child;
                    ptr_sentinel = inner.sentinel;
                },
            }
        },
        else => return sema.fail(sema.block, sema.block.nodeOffset(.zero), "slice of non-array type '{f}'", .{ptr_ptr_child_ty.fmt(ip)}),
    }

    if (!Type.fromIndex(elem_ty).comptimeOnly(ip)) try sema.ensureLayoutResolved(elem_ty);

    // Length of the underlying object: an array carries it in its type, a comptime-known slice in its
    // value, a many-item/C pointer is unbounded. The compiler branches array vs slice at each use; with
    // no runtime AIR both collapse into one comptime length here.
    const maybe_len: ?u64 = if (array_ty.zigTypeTag(ip) == .array)
        array_ty.arrayLen(ip)
    else if (slice_ty.isSlice(ip))
        try sema.resolveUsizeInt(.{ .index = ip.indexToKey(ptr_or_slice.index).slice.len })
    else
        null;

    // Slicing an unbounded many-item pointer to its end (`p[start..]`) yields a many-item pointer.
    if (maybe_len == null and end_opt == null) {
        const elem_ptr = try ptr_or_slice.ptrElem(start, ip);
        return .{ .index = try ip.getCoerced(elem_ptr.index, ptr_ptr_child_ty.index) };
    }

    const end: u64 = if (end_opt) |e| (if (by_length) start + e else e) else maybe_len.?;
    const end_is_len = if (maybe_len) |l| end == l else false;

    if (start > end) {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "start index {d} is larger than end index {d}", .{ start, end });
    }
    if (maybe_len) |l| {
        if (end > l + @intFromBool(ptr_sentinel != .none)) {
            const sentinel_label: []const u8 = if (ptr_sentinel != .none) " +1 (sentinel)" else "";
            const kind: []const u8 = if (slice_ty.isSlice(ip)) "slice" else "array";
            return sema.fail(sema.block, sema.block.nodeOffset(.zero), "end index {d} out of bounds for {s} of length {d}{s}", .{ end, kind, l, sentinel_label });
        }
    }

    const sentinel: InternPool.Index = s: {
        if (sentinel_opt) |provided| {
            try sema.checkSentinelType(elem_ty);
            const casted = try sema.coerceValueToType(provided, elem_ty);
            const actual = try sema.loadValue(try ptr_or_slice.ptrElem(end, ip));
            if (actual.index != casted.index) {
                return sema.fail(sema.block, sema.block.nodeOffset(.zero), "value in memory does not match slice sentinel", .{});
            }
            break :s casted.index;
        }
        break :s if (end_is_len) ptr_sentinel else .none;
    };

    // The sub-array pointer is the pointer to element `start`, re-typed to the sub-array type (the
    // compiler's `analyzePtrArithmetic` + `getCoerced`).
    const result_array_ty = try ip.internArrayType(.{ .len = end - start, .child = elem_ty, .sentinel = sentinel });
    const is_const = ip.indexToKey(slice_ty.index).ptr_type.flags.is_const;
    const result_ptr_ty = try ip.internPtrType(.{ .child = result_array_ty, .flags = .{ .size = .one, .is_const = is_const } });
    const elem_ptr = try ptr_or_slice.ptrElem(start, ip);
    return .{ .index = try ip.getCoerced(elem_ptr.index, result_ptr_ty) };
}

fn evalSliceStart(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const datas = sema.zir.instructions.items(.data);
    const extra = sema.zir.extraData(Zir.Inst.SliceStart, datas[@backingInt(inst)].pl_node.payload_index).data;
    const operand = try sema.resolveInst(extra.lhs);
    const start = try sema.resolveArrayLen(extra.start);
    return sema.analyzeSlice(operand, start, null, null, false);
}

fn evalSliceEnd(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const datas = sema.zir.instructions.items(.data);
    const extra = sema.zir.extraData(Zir.Inst.SliceEnd, datas[@backingInt(inst)].pl_node.payload_index).data;
    const operand = try sema.resolveInst(extra.lhs);
    const start = try sema.resolveArrayLen(extra.start);
    const end = try sema.resolveArrayLen(extra.end);
    return sema.analyzeSlice(operand, start, end, null, false);
}

fn evalSliceSentinel(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const datas = sema.zir.instructions.items(.data);
    const extra = sema.zir.extraData(Zir.Inst.SliceSentinel, datas[@backingInt(inst)].pl_node.payload_index).data;
    const operand = try sema.resolveInst(extra.lhs);
    const start = try sema.resolveArrayLen(extra.start);
    const end = if (extra.end == .none) null else try sema.resolveArrayLen(extra.end);
    const sentinel = try sema.resolveInst(extra.sentinel);
    return sema.analyzeSlice(operand, start, end, sentinel, false);
}

fn evalSliceLength(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const datas = sema.zir.instructions.items(.data);
    const extra = sema.zir.extraData(Zir.Inst.SliceLength, datas[@backingInt(inst)].pl_node.payload_index).data;
    const operand = try sema.resolveInst(extra.lhs);
    const start = try sema.resolveArrayLen(extra.start);
    const length = try sema.resolveArrayLen(extra.len);
    const sentinel = if (extra.sentinel == .none) null else try sema.resolveInst(extra.sentinel);
    return sema.analyzeSlice(operand, start, length, sentinel, true);
}

fn evalSliceSentinelTy(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    const datas = sema.zir.instructions.items(.data);
    const operand = try sema.resolveInst(datas[@backingInt(inst)].un_node.operand);
    const lhs_ptr_ty = operand.typeOf(ip);
    const lhs_ty = switch (ip.indexToKey(lhs_ptr_ty.index)) {
        .ptr_type => |pt| pt.child,
        else => {
            return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "expected pointer, found '{f}'", .{lhs_ptr_ty.fmt(ip)});
        },
    };
    const sentinel_ty: InternPool.Index = switch (ip.indexToKey(lhs_ty)) {
        .array_type => |at| at.child,
        .ptr_type => |pt| switch (pt.flags.size) {
            .many, .c, .slice => pt.child,
            .one => switch (ip.indexToKey(pt.child)) {
                .array_type => |at| at.child,
                else => {
                    return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "slice of single-item pointer cannot have sentinel", .{});
                },
            },
        },
        else => {
            return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "slice of non-array type '{f}'", .{Type.fromIndex(lhs_ty).fmt(ip)});
        },
    };
    return .{ .index = sentinel_ty };
}

fn evalElemVal(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const bin = sema.binData(inst);
    assert(bin.lhs != .none);
    assert(bin.rhs != .none);

    return try sema.elemVal(try sema.resolveInst(bin.lhs), bin.rhs);
}

fn checkIndexable(sema: *Sema, ty: Type) Error!void {
    const ip = sema.intern_pool;
    if (!ty.isIndexable(ip)) {
        const src = sema.block.nodeOffset(.zero);
        const msg = msg: {
            const msg = try sema.errMsg(src, "type '{f}' does not support indexing", .{ty.fmt(ip)});
            errdefer msg.destroy(sema.gpa);
            try sema.errNote(src, msg, "operand must be an array, slice, tuple, or vector", .{});
            try sema.addDeclaredHereNote(msg, ty);
            break :msg msg;
        };
        return sema.failWithOwnedErrorMsg(sema.block, msg);
    }
}

fn elemVal(sema: *Sema, indexable: Value, index_ref: Zir.Inst.Ref) Error!Value {
    const ip = sema.intern_pool;
    const indexable_ty = indexable.typeOf(ip);
    try sema.checkIndexable(indexable_ty);
    const index = try sema.resolveArrayLen(index_ref);

    switch (indexable_ty.zigTypeTag(ip)) {
        .pointer => {
            const child_ty = indexable_ty.childType(ip);
            try sema.ensureLayoutResolved(child_ty.index);
            switch (indexable_ty.ptrInfo(ip).flags.size) {
                .slice => return try sema.elemValSlice(indexable, index),
                .many, .c => {
                    const elem_ptr = try indexable.ptrElem(index, ip);
                    return try sema.loadValue(elem_ptr);
                },
                .one => {
                    arr_sent: {
                        if (child_ty.zigTypeTag(ip) != .array) break :arr_sent;
                        const s = child_ty.sentinel(ip) orelse break :arr_sent;
                        if (index != child_ty.arrayLen(ip)) break :arr_sent;
                        return s;
                    }
                    const elem_ptr = try sema.elemPtr(indexable, index);
                    return try sema.loadValue(elem_ptr);
                },
            }
        },
        .array, .vector => return try sema.elemValArray(indexable, index),
        .@"struct" => return try sema.tupleField(indexable, @intCast(index)),
        else => unreachable,
    }
}

fn elemValArray(sema: *Sema, array: Value, index: u64) Error!Value {
    const ip = sema.intern_pool;
    const array_ty = array.typeOf(ip);
    const array_sent = array_ty.sentinel(ip);
    const array_len = array_ty.arrayLen(ip);
    const array_len_s = array_len + @intFromBool(array_sent != null);
    const elem_ty = array_ty.childType(ip);

    if (array_len_s == 0) {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "indexing into empty array is not allowed", .{});
    }
    if (array_sent) |s| {
        if (index == array_len) return s;
    }
    if (index >= array_len_s) {
        const sentinel_label: []const u8 = if (array_sent != null) " +1 (sentinel)" else "";
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "index {d} outside array of length {d}{s}", .{ index, array_len, sentinel_label });
    }
    if (array.isUndef(ip)) return try sema.undefValue(elem_ty);
    return try array.elemValue(ip, @intCast(index));
}

fn elemValSlice(sema: *Sema, slice: Value, index: u64) Error!Value {
    const ip = sema.intern_pool;
    const slice_ty = slice.typeOf(ip);
    const slice_sent = slice_ty.sentinel(ip) != null;
    const slice_len = try sema.resolveUsizeInt(.{ .index = ip.indexToKey(slice.index).slice.len });
    const slice_len_s = slice_len + @intFromBool(slice_sent);
    if (slice_len_s == 0) {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "indexing into empty slice is not allowed", .{});
    }
    if (index >= slice_len_s) {
        const sentinel_label: []const u8 = if (slice_sent) " +1 (sentinel)" else "";
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "index {d} outside slice of length {d}{s}", .{ index, slice_len, sentinel_label });
    }
    const elem_ptr = try slice.ptrElem(index, ip);
    return try sema.loadValue(elem_ptr);
}

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
    return sema.fail(sema.block, sema.block.nodeOffset(.zero), "@memcpy: type '{f}' is not an indexable pointer; operand must be a slice, a many pointer or a pointer to an array", .{ty.fmt(sema.intern_pool)});
}

fn indexableMemLen(sema: *Sema, value: Value) Error!?u64 {
    const ip = sema.intern_pool;
    switch (ip.indexToKey(value.index)) {
        .slice => |s| return try sema.resolveUsizeInt(.{ .index = s.len }),
        .ptr => |p| return switch (ip.indexToKey(ip.indexToKey(p.ty).ptr_type.child)) {
            .array_type => |at| at.len,
            else => null,
        },
        else => return null,
    }
}

fn evalMemcpy(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    const bin = sema.binData(inst);
    const dest = try sema.resolveInst(bin.lhs);
    const src = try sema.resolveInst(bin.rhs);

    const dest_ty = sema.memOperandType(dest) orelse return sema.failMemOperand(dest.typeOf(ip));
    const src_ty = sema.memOperandType(src) orelse return sema.failMemOperand(src.typeOf(ip));

    if (dest_ty.isConstPtr(ip)) {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "@memcpy: cannot copy to constant pointer", .{});
    }

    const dest_elem = dest_ty.indexableElem(ip);
    const src_elem = src_ty.indexableElem(ip);
    const imc = try sema.coerceInMemoryAllowed(dest_elem, src_elem, false, null);
    if (imc != .ok) {
        const err_src = sema.block.nodeOffset(sema.srcNodeOffset(inst));
        const msg = msg: {
            const msg = try sema.errMsg(err_src, "@memcpy: pointer element type '{f}' cannot coerce into element type '{f}'", .{ src_elem.fmt(ip), dest_elem.fmt(ip) });
            errdefer msg.destroy(sema.gpa);
            try imc.report(sema, err_src, msg);
            break :msg msg;
        };
        return sema.failWithOwnedErrorMsg(sema.block, msg);
    }

    const dest_len = try sema.indexableMemLen(dest);
    const src_len = try sema.indexableMemLen(src);
    if (dest_len == null and src_len == null) {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "@memcpy: unknown copy length", .{});
    }
    if (dest_len != null and src_len != null and dest_len.? != src_len.?) {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "@memcpy: non-matching copy lengths {d} and {d}", .{ dest_len.?, src_len.? });
    }
    const len = dest_len orelse src_len.?;
    if (len == 0) return null;

    if (!src_elem.comptimeOnly(ip)) {
        try sema.ensureLayoutResolved(src_elem.index);
        if (src_elem.abiSize(ip) == 0) return null;
    }

    const raw_dest_ptr: Value = if (dest_ty.isSlice(ip)) .{ .index = ip.indexToKey(dest.index).slice.ptr } else dest;
    const raw_src_ptr: Value = if (src_ty.isSlice(ip)) .{ .index = ip.indexToKey(src.index).slice.ptr } else src;

    if (Value.doPointersOverlap(raw_src_ptr, raw_dest_ptr, len, ip)) {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "@memcpy: arguments alias", .{});
    }

    // @memcpy as a single array load and store.
    const array_ty = try ip.internArrayType(.{ .len = len, .child = dest_elem.index });
    const dest_array_ptr_ty = try ip.internPtrType(info: {
        var info = dest_ty.ptrInfo(ip);
        info.flags.size = .one;
        info.child = array_ty;
        info.sentinel = .none;
        break :info info;
    });
    const src_array_ptr_ty = try ip.internPtrType(info: {
        var info = src_ty.ptrInfo(ip);
        info.flags.size = .one;
        info.child = array_ty;
        info.sentinel = .none;
        break :info info;
    });
    const coerced_dest_ptr: Value = .{ .index = try ip.getCoerced(raw_dest_ptr.index, dest_array_ptr_ty) };
    const coerced_src_ptr: Value = .{ .index = try ip.getCoerced(raw_src_ptr.index, src_array_ptr_ty) };
    const array_val = try sema.loadValue(coerced_src_ptr);
    try sema.storePtrVal(coerced_dest_ptr, array_val);
    return null;
}

fn evalMemset(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    const bin = sema.binData(inst);
    const dest = try sema.resolveInst(bin.lhs);
    const uncoerced_elem = try sema.resolveInst(bin.rhs);

    const dest_ty = sema.memOperandType(dest) orelse return sema.failMemOperand(dest.typeOf(ip));
    if (dest_ty.isConstPtr(ip)) {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "cannot memset constant pointer", .{});
    }

    const dest_elem = dest_ty.indexableElem(ip);
    const elem = try sema.coerceValueToType(uncoerced_elem, dest_elem.index);

    const len = (try sema.indexableMemLen(dest)) orelse {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "unknown @memset length", .{});
    };
    if (len == 0) return null;

    try sema.ensureLayoutResolved(dest_elem.index);
    const array_ty = try ip.internArrayType(.{ .len = len, .child = dest_elem.index });
    const array_val = try sema.aggregateSplatValue(.fromIndex(array_ty), elem);
    const array_ptr_ty = try ip.internPtrType(info: {
        var info = dest_ty.ptrInfo(ip);
        info.flags.size = .one;
        info.child = array_ty;
        break :info info;
    });
    const raw_ptr: Value = if (dest_ty.isSlice(ip)) .{ .index = ip.indexToKey(dest.index).slice.ptr } else dest;
    const array_ptr_val: Value = .{ .index = try ip.getCoerced(raw_ptr.index, array_ptr_ty) };
    try sema.storePtrVal(array_ptr_val, array_val);
    return null;
}

fn resolveArrayLen(sema: *Sema, ref: Zir.Inst.Ref) Error!u64 {
    assert(ref != .none);
    return sema.resolveUsizeInt(try sema.resolveInst(ref));
}

fn resolveInt(sema: *Sema, value: Value, ty: InternPool.Index) Error!u64 {
    const coerced = try sema.coerceValueToType(value, ty);
    const key = sema.intern_pool.indexToKey(coerced.index);
    if (key != .int) {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "expected an integer", .{});
    }
    var space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
    return key.int.storage.toBigInt(&space).toInt(u64) catch {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "value out of range", .{});
    };
}

fn resolveUsizeInt(sema: *Sema, value: Value) Error!u64 {
    return sema.resolveInt(value, .usize_type);
}

fn coerceToErrorUnion(
    sema: *Sema,
    value: Value,
    dest_ty: InternPool.Index,
) Error!Value {
    const ip = sema.intern_pool;
    const eu_type = ip.indexToKey(dest_ty).error_union_type;
    const value_key = ip.indexToKey(value.index);

    if (value_key == .err) {
        // Enforce that the error is a member of the destination's error set before wrapping it, as the
        // compiler's `wrapErrorUnionSet` does by coercing to `dest.errorUnionSet()` first.
        const coerced = try sema.coerceValueToType(value, eu_type.error_set_type);
        const idx = try ip.internErrorUnion(.{
            .ty = dest_ty,
            .val = .{ .err_name = ip.indexToKey(coerced.index).err.name },
        });
        return .{ .index = idx };
    }

    const payload_value = try sema.coerceValueToType(value, eu_type.payload_type);
    const idx = try ip.internErrorUnion(.{
        .ty = dest_ty,
        .val = .{ .payload = payload_value.index },
    });
    return .{ .index = idx };
}

fn evalBitNot(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@backingInt(inst) < sema.zir.instructions.len);

    const ip = sema.intern_pool;
    const un_node = sema.zir.instructions.items(.data)[@backingInt(inst)].un_node;
    assert(un_node.operand != .none);

    const operand = try sema.resolveInst(un_node.operand);
    const operand_ty = Value.typeOf(operand, ip);
    const scalar_ty = operand_ty.scalarType(ip);
    const scalar_tag = scalar_ty.zigTypeTag(ip);

    if (scalar_tag != .int and scalar_tag != .bool)
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "bitwise not operation on type '{f}'", .{operand_ty.fmt(ip)});

    return try arith.bitwiseNot(sema, operand_ty, operand);
}

fn resolveInst(sema: *Sema, ref: Zir.Inst.Ref) Error!Value {
    assert(ref != .none);

    if (ref.toIndex()) |inst_idx| {
        if (sema.inst_map.get(inst_idx)) |value| {
            sema.operand_comptime = sema.operand_comptime and value.is_comptime;
            return value;
        }
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst_idx)), "internal error: unresolved instruction ref %{d}", .{@backingInt(inst_idx)});
    }

    if (wellKnownRefToValue(ref)) |value| return value;
    return sema.fail(sema.block, sema.block.nodeOffset(.zero), "unsupported ZIR ref: {s}", .{@tagName(ref)});
}

fn wellKnownRefToValue(ref: Zir.Inst.Ref) ?Value {
    if (ref != .none and ref.toIndex() == null) {
        return .{ .index = @fromBackingInt(@intCast(@backingInt(ref))) };
    }
    return null;
}

fn evalDeclVal(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    // Container decls resolve as lazy Navs via the namespace-parent walk; the typeless
    // session root's decls are eager-bound and served by `lookupDecl` below.
    if (sema.block.namespace) |start_ns| if (ip.namespacePtr(start_ns).owner_type != .none) {
        const name = try ip.getOrPutString(sema.gpa, sema.zir.instructions.items(.data)[@backingInt(inst)].str_tok.get(sema.zir), .no_embedded_nulls);
        var ns_opt: ?InternPool.NamespaceIndex = start_ns;
        while (ns_opt) |ns| {
            if (try sema.lookupInNamespace(ns, name)) |lookup| return try sema.analyzeNavVal(lookup.nav);
            ns_opt = ip.namespacePtr(ns).parent.unwrap();
        }
    };
    if (try sema.lookupDecl(inst)) |found| {
        return .{ .index = found.resolved.value };
    }
    const name = sema.zir.instructions.items(.data)[@backingInt(inst)].str_tok.get(sema.zir);
    return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "decl_val '{s}': not found in scope", .{name});
}

fn evalDeclRef(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    if (sema.block.namespace) |start_ns| if (ip.namespacePtr(start_ns).owner_type != .none) {
        const name = try ip.getOrPutString(sema.gpa, sema.zir.instructions.items(.data)[@backingInt(inst)].str_tok.get(sema.zir), .no_embedded_nulls);
        var ns_opt: ?InternPool.NamespaceIndex = start_ns;
        while (ns_opt) |ns| {
            if (try sema.lookupInNamespace(ns, name)) |lookup| return try sema.analyzeNavRef(lookup.nav);
            ns_opt = ip.namespacePtr(ns).parent.unwrap();
        }
    };
    const found = (try sema.lookupDecl(inst)) orelse {
        const name = sema.zir.instructions.items(.data)[@backingInt(inst)].str_tok.get(sema.zir);
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "decl_ref '{s}': not found in scope", .{name});
    };
    return try sema.analyzeNavRef(found.nav);
}

const DeclLookup = struct {
    nav: InternPool.Nav.Index,
    resolved: InternPool.Nav.Resolved,
};

fn lookupDecl(sema: *Sema, inst: Zir.Inst.Index) Error!?DeclLookup {
    assert(@backingInt(inst) < sema.zir.instructions.len);

    const data = sema.zir.instructions.items(.data)[@backingInt(inst)].str_tok;
    const name_bytes = data.get(sema.zir);
    const name = try sema.intern_pool.getOrPutString(sema.gpa, name_bytes, .no_embedded_nulls);

    const ns_idx = sema.block.namespace orelse {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "no namespace in scope for '{s}'", .{name_bytes});
    };

    if (try sema.lookupName(ns_idx, name)) |nav_idx| {
        const nav = sema.intern_pool.getNav(nav_idx);
        const resolved = nav.resolved orelse {
            return sema.fail(sema.block, sema.block.nodeOffset(.zero), "binding '{s}' recorded but value not resolved (test / comptime / extern)", .{name_bytes});
        };
        if (resolved.value == .none) {
            return sema.fail(sema.block, sema.block.nodeOffset(.zero), "binding '{s}' type resolved but value not yet", .{name_bytes});
        }
        return .{ .nav = nav_idx, .resolved = resolved };
    }

    return null;
}

fn lookupName(
    sema: *Sema,
    ns_idx: InternPool.NamespaceIndex,
    name: InternPool.NullTerminatedString,
) Error!?InternPool.Nav.Index {
    var current: ?InternPool.NamespaceIndex = ns_idx;
    var depth: u32 = 0;
    while (current) |idx| : (depth += 1) {
        assert(depth < max_namespace_chain);
        if (try sema.lookupInNamespace(idx, name)) |lookup| return lookup.nav;
        current = sema.intern_pool.namespacePtr(idx).parent.unwrap();
    }
    return null;
}

fn lookupInNamespace(
    sema: *Sema,
    namespace_index: InternPool.NamespaceIndex,
    ident_name: InternPool.NullTerminatedString,
) Error!?struct {
    nav: InternPool.Nav.Index,
    accessible: bool,
} {
    const ip = sema.intern_pool;
    try sema.ensureNamespaceUpToDate(namespace_index);
    const namespace = ip.namespacePtr(namespace_index);
    const adapter: InternPool.Namespace.NameAdapter = .{ .pool = ip };
    const src_file = if (sema.block.namespace) |cur| ip.namespacePtr(cur).file_scope else .none;
    if (namespace.pub_decls.getKeyAdapted(ident_name, adapter)) |nav_index| {
        return .{ .nav = nav_index, .accessible = true };
    } else if (namespace.priv_decls.getKeyAdapted(ident_name, adapter)) |nav_index| {
        return .{ .nav = nav_index, .accessible = src_file == namespace.file_scope };
    }
    return null;
}

fn namespaceLookup(
    sema: *Sema,
    namespace: InternPool.NamespaceIndex,
    decl_name: InternPool.NullTerminatedString,
) Error!?InternPool.Nav.Index {
    if (try sema.lookupInNamespace(namespace, decl_name)) |lookup| {
        if (!lookup.accessible) {
            const msg = try sema.errMsg(sema.block.nodeOffset(.zero), "'{f}' is not marked 'pub'", .{decl_name.fmt(sema.intern_pool)});
            return sema.failWithOwnedErrorMsg(sema.block, msg);
        }
        return lookup.nav;
    }
    return null;
}

const max_namespace_chain: u32 = 1024;

fn bindDecls(sema: *Sema) Error!void {
    assert(sema.block.namespace != null);

    const ns_idx = sema.block.namespace.?;
    for (sema.zir.typeDecls(.main_struct_inst)) |decl_inst| {
        try sema.bindOneDecl(ns_idx, decl_inst);
    }
}

fn bindOneDecl(
    sema: *Sema,
    ns_idx: InternPool.NamespaceIndex,
    decl_inst: Zir.Inst.Index,
) Error!void {
    sema.block.src_base_inst = decl_inst;
    const unwrapped = sema.zir.getDeclaration(decl_inst);
    if (unwrapped.kind == .@"comptime" or unwrapped.kind == .unnamed_test) {
        return sema.bindAnonymousDecl(ns_idx, decl_inst, unwrapped);
    }

    assert(unwrapped.name != .empty);
    const name_bytes = sema.zir.nullTerminatedString(unwrapped.name);

    if (std.mem.eql(u8, name_bytes, InputShape.expression_decl_name)) return;

    const name = try sema.intern_pool.getOrPutString(sema.gpa, name_bytes, .no_embedded_nulls);

    if (try sema.lookupName(ns_idx, name)) |_| return;

    switch (unwrapped.kind) {
        .@"const", .@"var" => try sema.bindValueDecl(ns_idx, name, decl_inst, unwrapped),
        .@"test", .decltest => try sema.bindTestDecl(ns_idx, name, decl_inst, unwrapped),
        .@"comptime", .unnamed_test => unreachable,
    }
}

fn bindValueDecl(
    sema: *Sema,
    ns_idx: InternPool.NamespaceIndex,
    name: InternPool.NullTerminatedString,
    decl_inst: Zir.Inst.Index,
    unwrapped: std.zig.Zir.Inst.Declaration.Unwrapped,
) Error!void {
    const declared_type: ?InternPool.Index = if (unwrapped.type_body) |tb| blk: {
        const t = (try sema.coerceValueToType(try sema.resolveInlineBody(tb, decl_inst), .type_type)).index;
        try sema.inst_map.put(sema.gpa, decl_inst, .{ .index = t });
        break :blk t;
    } else null;
    const fqn = try sema.intern_pool.fullyQualifiedName(sema.gpa, ns_idx, name);
    const prev_ctx = sema.block.type_name_ctx;
    sema.block.type_name_ctx = fqn;
    defer sema.block.type_name_ctx = prev_ctx;

    const nav_idx = try sema.intern_pool.createNav(sema.gpa, name, fqn);
    const prev_owner_nav = sema.owner_nav;
    sema.owner_nav = nav_idx.toOptional();
    defer sema.owner_nav = prev_owner_nav;

    // An extern decl has no value body; the linker supplies its value at runtime. Mint an extern
    // symbol from the declared type (see analyzeNavVal); otherwise evaluate the value body.
    const final_type: InternPool.Index, const final_value: Value = if (unwrapped.linkage == .@"extern") ext: {
        const nav_ty = declared_type.?;
        break :ext .{ nav_ty, .{ .index = try sema.intern_pool.getExtern(.{ .ty = nav_ty, .owner_nav = nav_idx }) } };
    } else val: {
        const value_body = unwrapped.value_body orelse
            return sema.fail(sema.block, sema.block.nodeOffset(.zero), "bindDecls '{s}': no value_body", .{sema.intern_pool.stringSlice(name)});
        const raw_value = try sema.resolveInlineBody(value_body, decl_inst);
        const fv = if (declared_type) |dest_ty|
            try sema.coerceValueToType(raw_value, dest_ty)
        else
            raw_value;
        const ft = if (declared_type) |dest_ty| dest_ty else Value.typeOf(fv, sema.intern_pool).index;
        break :val .{ ft, fv };
    };

    const declared_align: InternPool.Alignment = if (unwrapped.align_body) |ab|
        try sema.alignmentFromValue(try sema.resolveInlineBody(ab, decl_inst))
    else
        .none;

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
            const synthesized = try sema.intern_pool.getOrPutString(sema.gpa, "", .no_embedded_nulls);
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

fn analyzeComptimeUnit(sema: *Sema, cu_id: InternPool.ComptimeUnit.Id) Error!void {
    const unit = sema.intern_pool.getComptimeUnit(cu_id);
    const decl_inst = unit.zir_index;
    const zir_decl = sema.zir.getDeclaration(decl_inst);
    assert(zir_decl.kind == .@"comptime");
    const value_body = zir_decl.value_body.?;

    const parent_block = sema.block;
    var block: Block = .{
        .namespace = unit.namespace,
        .src_base_inst = decl_inst,
        .type_name_ctx = parent_block.type_name_ctx,
        .comptime_reason = .{ .reason = .{
            .src = .{ .base_node_inst = decl_inst, .offset = LazySrcLoc.Offset.nodeOffset(.zero) },
            .r = .{ .simple = .comptime_keyword },
        } },
    };
    defer block.deinit(sema.gpa);
    sema.block = &block;
    defer sema.block = parent_block;

    _ = try sema.resolveInlineBody(value_body, decl_inst);
}

fn evalErrorSetDecl(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@backingInt(inst) < sema.zir.instructions.len);

    const pl_node = sema.zir.instructions.items(.data)[@backingInt(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.ErrorSetDecl, pl_node.payload_index);
    const fields_len = extra.data.fields_len;

    const names = try sema.gpa.alloc(InternPool.NullTerminatedString, fields_len);
    defer sema.gpa.free(names);

    var extra_index: u32 = @intCast(extra.end);
    for (names) |*slot| {
        const zir_name_idx: std.zig.Zir.NullTerminatedString = @fromBackingInt(@intCast(sema.zir.extra[extra_index]));
        const name_bytes = sema.zir.nullTerminatedString(zir_name_idx);
        slot.* = try sema.intern_pool.getOrPutString(sema.gpa, name_bytes, .no_embedded_nulls);
        extra_index += 1;
    }

    const ty_idx = try sema.intern_pool.internErrorSetType(names);
    return .{ .index = ty_idx };
}

fn evalErrorValue(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@backingInt(inst) < sema.zir.instructions.len);

    const data = sema.zir.instructions.items(.data)[@backingInt(inst)].str_tok;
    const name_bytes = data.get(sema.zir);
    const name = try sema.intern_pool.getOrPutString(sema.gpa, name_bytes, .no_embedded_nulls);
    const ty_idx = try sema.intern_pool.singletonErrorSetType(name);
    const err_idx = try sema.intern_pool.internErr(.{ .ty = ty_idx, .name = name });
    return .{ .index = err_idx };
}

fn evalErrorUnionType(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const bin = sema.binData(inst);
    assert(bin.lhs != .none);
    assert(bin.rhs != .none);

    const error_set = try sema.resolveDestType(bin.lhs);
    const payload = try sema.resolveDestType(bin.rhs);

    const ty_idx = try sema.intern_pool.internErrorUnionType(.{
        .error_set_type = error_set,
        .payload_type = payload,
    });
    return .{ .index = ty_idx };
}

fn evalErrUnionCode(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@backingInt(inst) < sema.zir.instructions.len);
    const un_node = sema.zir.instructions.items(.data)[@backingInt(inst)].un_node;
    assert(un_node.operand != .none);
    return try sema.errUnionCodeVal(try sema.resolveInst(un_node.operand));
}

fn evalErrUnionCodePtr(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@backingInt(inst) < sema.zir.instructions.len);
    const un_node = sema.zir.instructions.items(.data)[@backingInt(inst)].un_node;
    assert(un_node.operand != .none);
    return try sema.errUnionCodeVal(try sema.loadValue(try sema.resolveInst(un_node.operand)));
}

fn errUnionCodeVal(sema: *Sema, operand_value: Value) Error!Value {
    const ip = sema.intern_pool;
    const operand_key = ip.indexToKey(operand_value.index);
    if (operand_key != .error_union) {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "err_union_code: operand is not an error union", .{});
    }
    const eu_type = ip.indexToKey(operand_key.error_union.ty).error_union_type;
    switch (operand_key.error_union.val) {
        .err_name => |name| return .{ .index = try ip.internErr(.{ .ty = eu_type.error_set_type, .name = name }) },
        .payload => {
            return sema.fail(sema.block, sema.block.nodeOffset(.zero), "err_union_code: operand carries a payload, not an error", .{});
        },
    }
}

fn evalErrUnionPayloadUnsafePtr(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@backingInt(inst) < sema.zir.instructions.len);
    const un_node = sema.zir.instructions.items(.data)[@backingInt(inst)].un_node;
    assert(un_node.operand != .none);
    return try sema.errUnionPayloadPtr(try sema.resolveInst(un_node.operand), false);
}

fn errUnionPayloadPtr(sema: *Sema, eu_ptr: Value, comptime initializing: bool) Error!Value {
    const ip = sema.intern_pool;
    const ptr_type = ip.indexToKey(eu_ptr.typeOf(ip).toIndex()).ptr_type;
    const eu_key = ip.indexToKey(ptr_type.child);
    if (eu_key != .error_union_type) {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "err_union_payload: pointer child is not an error union", .{});
    }
    if (!initializing) {
        const eu_val = try sema.loadValue(eu_ptr);
        if (ip.indexToKey(eu_val.index).error_union.val == .err_name) {
            return sema.fail(sema.block, sema.block.nodeOffset(.zero), "err_union_payload: operand carries an error, not a payload", .{});
        }
    } else {
        // Set the error union to non-error at comptime before returning the payload pointer, so stores
        // into the payload have somewhere to land. Use the payload's OPV if it has one, else undef.
        const payload_type: Type = .fromIndex(eu_key.error_union_type.payload_type);
        const payload_val = (try payload_type.onePossibleValue(sema)) orelse try sema.undefValue(payload_type);
        const eu_val: Value = .fromIndex(try ip.internErrorUnion(.{ .ty = ptr_type.child, .val = .{ .payload = payload_val.index } }));
        try sema.storePtrVal(eu_ptr, eu_val);
    }
    const child_ptr_ty = try ip.internPtrType(.{ .child = eu_key.error_union_type.payload_type, .sentinel = ptr_type.sentinel, .flags = ptr_type.flags });
    return .{ .index = try ip.internPtr(.{
        .ty = child_ptr_ty,
        .base_addr = .{ .eu_payload = eu_ptr.index },
        .byte_offset = 0,
    }) };
}

fn evalTry(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@backingInt(inst) < sema.zir.instructions.len);
    const ip = sema.intern_pool;
    const pl_node = sema.zir.instructions.items(.data)[@backingInt(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.Try, pl_node.payload_index);
    const body = sema.zir.bodySlice(extra.end, extra.data.body_len);
    const err_union = try sema.resolveInst(extra.data.operand);
    const key = ip.indexToKey(err_union.index);
    if (key != .error_union) {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "expected error union type", .{});
    }
    return switch (key.error_union.val) {
        .payload => |p| .{ .index = p },
        .err_name => try sema.evalBody(body),
    };
}

fn evalTryPtr(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@backingInt(inst) < sema.zir.instructions.len);
    const ip = sema.intern_pool;
    const pl_node = sema.zir.instructions.items(.data)[@backingInt(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.Try, pl_node.payload_index);
    const body = sema.zir.bodySlice(extra.end, extra.data.body_len);
    const operand = try sema.resolveInst(extra.data.operand);
    const err_union = try sema.loadValue(operand);
    const key = ip.indexToKey(err_union.index);
    if (key != .error_union) {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "expected error union type", .{});
    }
    return switch (key.error_union.val) {
        .payload => try sema.errUnionPayloadPtr(operand, false),
        .err_name => try sema.evalBody(body),
    };
}

fn evalUnreachable(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const inst_data = sema.zir.instructions.items(.data)[@backingInt(inst)].@"unreachable";
    const src = sema.block.nodeOffset(inst_data.src_node);
    // Every body evaluates at comptime here, so reaching `unreachable` is always a
    // compile error; the compiler's runtime path instead lowers a trap.
    return sema.fail(sema.block, src, "reached unreachable code", .{});
}

fn evalEnsureErrUnionPayloadVoid(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@backingInt(inst) < sema.zir.instructions.len);
    const ip = sema.intern_pool;
    const un_node = sema.zir.instructions.items(.data)[@backingInt(inst)].un_node;
    const operand = try sema.resolveInst(un_node.operand);
    const operand_ty = operand.typeOf(ip);
    const eu_ty = if (operand_ty.zigTypeTag(ip) == .pointer) operand_ty.childType(ip) else operand_ty;
    if (eu_ty.zigTypeTag(ip) != .error_union) return null;
    const payload_tag = eu_ty.errorUnionPayload(ip).zigTypeTag(ip);
    if (payload_tag != .void and payload_tag != .noreturn) {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "error union payload is ignored", .{});
    }
    return null;
}

fn evalErrUnionPayloadUnsafe(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@backingInt(inst) < sema.zir.instructions.len);

    const un_node = sema.zir.instructions.items(.data)[@backingInt(inst)].un_node;
    assert(un_node.operand != .none);

    const ip = sema.intern_pool;
    const operand = try sema.resolveInst(un_node.operand);
    const err_union_ty = operand.typeOf(ip);
    if (err_union_ty.zigTypeTag(ip) != .error_union) {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "expected error union type, found '{f}'", .{err_union_ty.fmt(ip)});
    }
    // The compiler unwinds a comptime error return trace here; the REPL has no such trace.
    if (operand.getErrorName(ip).unwrap()) |name| {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "caught unexpected error '{s}'", .{ip.stringSlice(name)});
    }
    return .{ .index = ip.indexToKey(operand.index).error_union.val.payload };
}

fn evalIsNonErr(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@backingInt(inst) < sema.zir.instructions.len);
    const un_node = sema.zir.instructions.items(.data)[@backingInt(inst)].un_node;
    assert(un_node.operand != .none);
    return try sema.resolveIsNonErrVal(try sema.resolveInst(un_node.operand));
}

fn evalRetIsNonErr(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@backingInt(inst) < sema.zir.instructions.len);
    const un_node = sema.zir.instructions.items(.data)[@backingInt(inst)].un_node;
    assert(un_node.operand != .none);
    return try sema.resolveIsNonErrVal(try sema.resolveInst(un_node.operand));
}

fn evalIsNonErrPtr(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@backingInt(inst) < sema.zir.instructions.len);
    const un_node = sema.zir.instructions.items(.data)[@backingInt(inst)].un_node;
    assert(un_node.operand != .none);
    return try sema.resolveIsNonErrVal(try sema.loadValue(try sema.resolveInst(un_node.operand)));
}

fn resolveIsNonErrFromType(sema: *Sema, operand_ty: Type) Error!?Value {
    const ip = sema.intern_pool;
    const ot = operand_ty.zigTypeTag(ip);
    if (ot != .error_set and ot != .error_union) return Value.bool_true;
    if (ot == .error_set) return Value.bool_false;
    assert(ot == .error_union);

    const payload_ty = operand_ty.errorUnionPayload(ip);
    // The compiler asserts the payload layout is already resolved before `classify` reads its class; the
    // REPL resolves lazily, so ensure it here.
    try sema.ensureLayoutResolved(payload_ty.index);
    if (payload_ty.classify(ip) == .no_possible_value) {
        return Value.bool_false;
    }
    // The REPL never mints an inferred error set, so `resolveErrSetIsEmpty` reduces to `errorSetIsEmpty`.
    if (operand_ty.errorUnionSet(ip).errorSetIsEmpty(ip)) {
        return Value.bool_true;
    }
    return null;
}

fn resolveIsNonErrVal(sema: *Sema, operand: Value) Error!Value {
    const ip = sema.intern_pool;
    if (try sema.resolveIsNonErrFromType(operand.typeOf(ip))) |res| {
        return res;
    }
    assert(operand.typeOf(ip).zigTypeTag(ip) == .error_union);
    if (operand.isUndef(ip)) return .{ .index = .undef_bool };
    return Value.makeBool(operand.getErrorName(ip) == .none);
}

fn evalLoop(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@backingInt(inst) < sema.zir.instructions.len);

    const pl_node = sema.zir.instructions.items(.data)[@backingInt(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.Block, pl_node.payload_index);
    const body = sema.zir.bodySlice(extra.end, extra.data.body_len);
    return try sema.resolveInlineBody(body, inst);
}

fn evalForLen(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@backingInt(inst) < sema.zir.instructions.len);

    const pl_node = sema.zir.instructions.items(.data)[@backingInt(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.MultiOp, pl_node.payload_index);
    const operands = sema.zir.refSlice(extra.end, extra.data.operands_len);
    const pairs: []const [2]Zir.Inst.Ref =
        @as([*]const [2]Zir.Inst.Ref, @ptrCast(operands.ptr))[0..@divExact(operands.len, 2)];

    var len: ?u64 = null;
    for (pairs) |pair| {
        if (pair[0] == .none) continue;
        const arg_len: u64 = if (pair[1] == .none) blk: {
            const obj = try sema.resolveInst(pair[0]);
            const ip = sema.intern_pool;
            if (ip.indexToKey(obj.index) == .slice)
                break :blk try sema.resolveUsizeInt(.{ .index = ip.indexToKey(obj.index).slice.len });
            // Length is a property of the operand's type, not its (possibly undefined) value;
            // a pointer operand (`&array`) iterates its pointee.
            var operand_ty = obj.typeOf(ip).toIndex();
            while (ip.indexToKey(operand_ty) == .ptr_type) operand_ty = ip.indexToKey(operand_ty).ptr_type.child;
            switch (ip.indexToKey(operand_ty)) {
                .array_type, .vector_type, .tuple_type => break :blk ip.aggregateElementCount(operand_ty),
                else => {
                    const object_ty = obj.typeOf(ip);
                    const src = sema.block.nodeOffset(sema.srcNodeOffset(inst));
                    return sema.failWithOwnedErrorMsg(sema.block, msg: {
                        const msg = try sema.errMsg(src, "type '{f}' is not indexable and not a range", .{object_ty.fmt(ip)});
                        errdefer msg.destroy(sema.gpa);
                        try sema.errNote(src, msg, "for loop operand must be a range, array, slice, tuple, or vector", .{});
                        if (object_ty.zigTypeTag(ip) == .error_union) {
                            try sema.errNote(src, msg, "consider using 'try', 'catch', or 'if'", .{});
                        }
                        break :msg msg;
                    });
                },
            }
        } else blk: {
            const range_start = try sema.resolveInst(pair[0]);
            const range_end = try sema.resolveInst(pair[1]);
            // The length is `end - start`, so a descending range underflows usize and reports an integer
            // overflow; a `start` of 0 skips the subtraction. Mirrors the compiler's `zirForLen`.
            if (try sema.resolveUsizeInt(range_start) == 0) break :blk try sema.resolveUsizeInt(range_end);
            break :blk try sema.resolveUsizeInt(try arith.sub(sema, .fromIndex(.usize_type), range_end, range_start));
        };
        if (len) |existing| {
            if (existing != arg_len) {
                return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "non-matching for loop lengths", .{});
            }
        } else len = arg_len;
    }
    const idx = try sema.intern_pool.internInt(.{
        .ty = .usize_type,
        .storage = .{ .u64 = len orelse 0 },
    });
    return .{ .index = idx };
}

fn evalSwitchBlock(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@backingInt(inst) < sema.zir.instructions.len);

    const tag = sema.zir.instructions.items(.tag)[@backingInt(inst)];
    const sw = sema.zir.getSwitchBlock(inst);

    var operand = try sema.resolveInst(sw.main_operand);
    if (tag == .switch_block_ref) {
        operand = try sema.loadValue(operand);
    }

    if (tag == .switch_block_err_union) {
        const non_err = sw.non_err_case orelse {
            return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "switch_block_err_union: missing non_err_case", .{});
        };
        if (non_err.operand_is_ref) {
            operand = try sema.loadValue(operand);
        }
        const eu_key = sema.intern_pool.indexToKey(operand.index);
        if (eu_key != .error_union) {
            return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "switch_block_err_union: operand is not an error_union", .{});
        }
        switch (eu_key.error_union.val) {
            .payload => |payload_idx| {
                if (non_err.capture != .none) try sema.bindSwitchCapture(inst, sw, non_err.capture, .{ .index = payload_idx });
                return try sema.resolveInlineBody(non_err.body, inst);
            },
            .err_name => {},
        }
    }

    const operand_err_name: ?InternPool.NullTerminatedString =
        switch (sema.intern_pool.indexToKey(operand.index)) {
            .err => |e| e.name,
            .error_union => |eu| switch (eu.val) {
                .err_name => |n| n,
                .payload => null,
            },
            else => null,
        };

    var cond = operand;
    var union_operand: ?InternPool.Key.Union = null;
    if (sema.intern_pool.indexToKey(operand.index) == .un) {
        const uv = sema.intern_pool.indexToKey(operand.index).un;
        try sema.resolveUnionFields(uv.ty);
        if (sema.intern_pool.unionFields(uv.ty).tag_usage != .tagged) {
            return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "switch on union with no attached enum", .{});
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
            if (case.prong_info.has_tag_capture) return sema.failSwitch("tag capture");
            if (case.prong_info.capture != .none) {
                if (union_operand) |uv| {
                    if (case.item_infos.len > 1 and
                        (try sema.uniformUnionCaptureType(uv.ty, case.item_infos)) == null)
                        return sema.failSwitch("capture group across differing field types");
                }
                // A union capture binds the active field payload; a scalar switch binds the operand.
                const capture_val: Value = if (union_operand) |uv| .{ .index = uv.val } else operand;
                try sema.bindSwitchCapture(inst, sw, case.prong_info.capture, capture_val);
            }
            return try sema.resolveInlineBody(prong_body, inst);
        }
    }

    if (sw.else_case) |else_case| {
        if (else_case.has_tag_capture) return sema.failSwitch("tag capture");
        if (else_case.capture != .none) {
            const capture_val: Value = if (union_operand) |uv| .{ .index = uv.val } else operand;
            try sema.bindSwitchCapture(inst, sw, else_case.capture, capture_val);
        }
        return try sema.resolveInlineBody(else_case.body, inst);
    }

    return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "switch: no matching case and no else", .{});
}

fn isAnyerrorSet(ip: *const InternPool, item_ty: InternPool.Index) bool {
    const set_ty = switch (ip.indexToKey(item_ty)) {
        .error_union_type => |eu| eu.error_set_type,
        else => item_ty,
    };
    return set_ty == .anyerror_type;
}

fn requireSwitchElse(sema: *Sema, item_ty: InternPool.Index, has_else: bool) Error!void {
    if (has_else) return;
    return sema.fail(sema.block, sema.block.nodeOffset(.zero), "else prong required when switching on type '{f}'", .{Type.fromIndex(item_ty).fmt(sema.intern_pool)});
}
fn validateSwitchItemOrRange(
    sema: *Sema,
    item_src: LazySrcLoc,
    val: Value,
    opt_last_val: ?Value,
    item_ty: InternPool.Index,
    seen_enum_fields: []?LazySrcLoc,
    seen_errors: *std.AutoHashMapUnmanaged(InternPool.NullTerminatedString, LazySrcLoc),
    seen_sparse: *std.AutoHashMapUnmanaged(InternPool.Index, LazySrcLoc),
    range_set: *RangeSet,
    true_src: *?LazySrcLoc,
    false_src: *?LazySrcLoc,
    void_src: *?LazySrcLoc,
) Error!void {
    const ip = sema.intern_pool;
    const maybe_prev_src: ?LazySrcLoc = switch (Type.fromIndex(item_ty).zigTypeTag(ip)) {
        .@"enum" => blk: {
            const tag_ty = ip.indexToKey(val.index).enum_tag.ty;
            const field_index = (try sema.enumTagFieldIndex(tag_ty, val)).?;
            const prev = seen_enum_fields[field_index];
            seen_enum_fields[field_index] = item_src;
            break :blk prev;
        },
        .error_set => blk: {
            const gop = try seen_errors.getOrPut(sema.gpa, ip.indexToKey(val.index).err.name);
            const prev: ?LazySrcLoc = if (gop.found_existing) gop.value_ptr.* else null;
            gop.value_ptr.* = item_src;
            break :blk prev;
        },
        .int, .comptime_int => {
            const ty = Type.fromIndex(item_ty);
            const first_val = val;
            const last_val: Value = last_val: {
                const last_val = opt_last_val orelse break :last_val val;
                if (first_val.compareScalar(.gt, last_val, ty, ip)) {
                    return sema.fail(sema.block, item_src, "range start value is greater than the end value", .{});
                }
                break :last_val last_val;
            };
            if (range_set.addAssumeCapacity(.{ .first = first_val, .last = last_val, .src = item_src }, ty, ip)) |prev_range| {
                const overlap_start = first_val.numberMax(prev_range.first, ip);
                const overlap_end = last_val.numberMin(prev_range.last, ip);
                if (overlap_start.eql(overlap_end, ty, ip)) {
                    return sema.failWithOwnedErrorMsg(sema.block, msg: {
                        const msg = try sema.errMsg(item_src, "duplicate switch value '{f}'", .{render_value.fmt(overlap_start, ip)});
                        errdefer msg.destroy(sema.gpa);
                        if (prev_range.first.eql(prev_range.last, ty, ip)) {
                            try sema.errNote(prev_range.src, msg, "previous value here", .{});
                        } else {
                            try sema.errNote(prev_range.src, msg, "previous value inside range here", .{});
                        }
                        break :msg msg;
                    });
                }
                assert(!prev_range.first.eql(prev_range.last, ty, ip));
                return sema.failWithOwnedErrorMsg(sema.block, msg: {
                    const msg = try sema.errMsg(item_src, "duplicate switch ranges", .{});
                    errdefer msg.destroy(sema.gpa);
                    if (first_val.eql(prev_range.first, ty, ip) and last_val.eql(prev_range.last, ty, ip)) {
                        try sema.errNote(prev_range.src, msg, "previous range here", .{});
                    } else {
                        try sema.errNote(prev_range.src, msg, "overlaps with previous range here", .{});
                        try sema.errNote(prev_range.src, msg, "ranges overlap from '{f}' to '{f}'", .{ render_value.fmt(overlap_start, ip), render_value.fmt(overlap_end, ip) });
                    }
                    break :msg msg;
                });
            }
            return;
        },
        .bool => switch (ip.indexToKey(val.index).simple_value) {
            .true => blk: {
                const prev = true_src.*;
                true_src.* = item_src;
                break :blk prev;
            },
            .false => blk: {
                const prev = false_src.*;
                false_src.* = item_src;
                break :blk prev;
            },
            else => null,
        },
        .void => blk: {
            const prev = void_src.*;
            void_src.* = item_src;
            break :blk prev;
        },
        .enum_literal, .@"fn", .type => blk: {
            const gop = try seen_sparse.getOrPut(sema.gpa, val.index);
            const prev: ?LazySrcLoc = if (gop.found_existing) gop.value_ptr.* else null;
            gop.value_ptr.* = item_src;
            break :blk prev;
        },
        else => unreachable,
    };
    const prev_src = maybe_prev_src orelse return;
    return sema.failWithOwnedErrorMsg(sema.block, msg: {
        const msg = try sema.errMsg(item_src, "duplicate switch value '{f}'", .{render_value.fmt(val, ip)});
        errdefer msg.destroy(sema.gpa);
        try sema.errNote(prev_src, msg, "previous value here", .{});
        if (Type.fromIndex(item_ty).zigTypeTag(ip) == .type) {
            try sema.addDeclaredHereNote(msg, .fromIndex(val.index));
        } else {
            try sema.addDeclaredHereNote(msg, .fromIndex(item_ty));
        }
        break :msg msg;
    });
}

fn validateSwitchBlock(sema: *Sema, inst: Zir.Inst.Index, unresolved_item_ty: InternPool.Index, sw: Zir.UnwrappedSwitchBlock) Error!void {
    const ip = sema.intern_pool;
    const gpa = sema.gpa;
    const has_else = sw.else_case != null;
    const operand_src = sema.block.src(.{ .node_offset_switch_operand = sema.srcNodeOffset(inst) });
    const else_prong_src = sema.block.src(.{ .node_offset_switch_else_prong = sema.srcNodeOffset(inst) });

    // A caught error (`catch |e| switch (e)`) keeps its error-union type here, whereas the compiler
    // switches on the error set. Resolve to the error set so the item type matches the compiler's; a
    // direct error-union operand is routed through `switch_block_err_union`, never reaching this point.
    const item_ty = switch (ip.indexToKey(unresolved_item_ty)) {
        .error_union_type => |eu| eu.error_set_type,
        else => unresolved_item_ty,
    };

    const item_type_tag = Type.fromIndex(item_ty).zigTypeTag(ip);
    switch (item_type_tag) {
        .@"enum", .error_set, .int, .comptime_int, .type, .enum_literal, .@"fn", .bool, .void => {},
        .optional => return sema.failWithOwnedErrorMsg(sema.block, msg: {
            const msg = try sema.errMsg(operand_src, "switch on optional type '{f}'", .{Type.fromIndex(item_ty).fmt(ip)});
            errdefer msg.destroy(gpa);
            try sema.errNote(operand_src, msg, "consider using '.?', 'orelse', or 'if'", .{});
            break :msg msg;
        }),
        else => return sema.fail(sema.block, operand_src, "switch on type '{f}'", .{Type.fromIndex(item_ty).fmt(ip)}),
    }

    var seen_enum_fields: []?LazySrcLoc = &.{};
    if (item_type_tag == .@"enum") {
        seen_enum_fields = try gpa.alloc(?LazySrcLoc, try sema.enumFieldCount(item_ty));
        @memset(seen_enum_fields, null);
    }
    defer gpa.free(seen_enum_fields);
    var seen_errors: std.AutoHashMapUnmanaged(InternPool.NullTerminatedString, LazySrcLoc) = .empty;
    defer seen_errors.deinit(gpa);
    var seen_sparse: std.AutoHashMapUnmanaged(InternPool.Index, LazySrcLoc) = .empty;
    defer seen_sparse.deinit(gpa);
    var range_set: RangeSet = .empty;
    defer range_set.deinit(gpa);
    if (item_type_tag == .int or item_type_tag == .comptime_int) {
        try range_set.ensureUnusedCapacity(gpa, sw.totalItemsLen());
    }
    var true_src: ?LazySrcLoc = null;
    var false_src: ?LazySrcLoc = null;
    var void_src: ?LazySrcLoc = null;
    var saw_range = false;

    const switch_node_offset = sema.srcNodeOffset(inst);
    var extra_index: usize = sw.end;
    var it = sw.iterateCases();
    while (it.next()) |case| {
        extra_index += case.prong_info.body_len;
        for (case.item_infos, 0..) |item_info, item_i| {
            const item_src = sema.block.src(.{ .switch_case_item = .{
                .switch_node_offset = switch_node_offset,
                .case_idx = case.index,
                .item_idx = .{ .kind = .single, .value = @intCast(item_i) },
            } });
            switch (item_info.unwrap()) {
                .under => {
                    return sema.failWithOwnedErrorMsg(sema.block, msg: {
                        const msg = try sema.errMsg(sema.block.nodeOffset(switch_node_offset), "'_' prong only allowed when switching on non-exhaustive enums", .{});
                        errdefer msg.destroy(gpa);
                        try sema.errNote(item_src, msg, "'_' prong here", .{});
                        try sema.errNote(sema.block.nodeOffset(switch_node_offset), msg, "consider using 'else'", .{});
                        break :msg msg;
                    });
                },
                .enum_literal => |n| {
                    const name = try ip.getOrPutString(gpa, sema.zir.nullTerminatedString(n), .no_embedded_nulls);
                    const uncoerced = try sema.analyzeDeclLiteral(item_ty, name, false);
                    const val = try sema.coerceValueToType(uncoerced, item_ty);
                    try sema.validateSwitchItemOrRange(item_src, val, null, item_ty, seen_enum_fields, &seen_errors, &seen_sparse, &range_set, &true_src, &false_src, &void_src);
                },
                .error_value => |n| {
                    const name = try ip.getOrPutString(gpa, sema.zir.nullTerminatedString(n), .no_embedded_nulls);
                    const err_ty = try ip.singletonErrorSetType(name);
                    const val: Value = .{ .index = try ip.internErr(.{ .ty = err_ty, .name = name }) };
                    try sema.validateSwitchItemOrRange(item_src, val, null, item_ty, seen_enum_fields, &seen_errors, &seen_sparse, &range_set, &true_src, &false_src, &void_src);
                },
                .body_len => |len| {
                    const raw = try sema.resolveInlineBody(sema.zir.bodySlice(extra_index, len), inst);
                    extra_index += len;
                    const val = try sema.coerceValueToType(raw, item_ty);
                    try sema.validateSwitchItemOrRange(item_src, val, null, item_ty, seen_enum_fields, &seen_errors, &seen_sparse, &range_set, &true_src, &false_src, &void_src);
                },
            }
        }
        for (case.range_infos, 0..) |range_pair, range_i| {
            saw_range = true;
            const range_src = sema.block.src(.{ .switch_case_item = .{
                .switch_node_offset = switch_node_offset,
                .case_idx = case.index,
                .item_idx = .{ .kind = .range, .value = @intCast(range_i) },
            } });
            const lo_len = range_pair[0].bodyLen() orelse 0;
            const hi_len = range_pair[1].bodyLen() orelse 0;
            if (item_type_tag == .int or item_type_tag == .comptime_int) {
                const lo = try sema.coerceValueToType(try sema.resolveInlineBody(sema.zir.bodySlice(extra_index, lo_len), inst), item_ty);
                const hi = try sema.coerceValueToType(try sema.resolveInlineBody(sema.zir.bodySlice(extra_index + lo_len, hi_len), inst), item_ty);
                try sema.validateSwitchItemOrRange(range_src, lo, hi, item_ty, seen_enum_fields, &seen_errors, &seen_sparse, &range_set, &true_src, &false_src, &void_src);
            }
            extra_index += lo_len + hi_len;
        }
    }

    if (saw_range and item_type_tag != .int and item_type_tag != .comptime_int) {
        return sema.fail(sema.block, sema.block.src(.{ .node_offset_switch_range = switch_node_offset }), "ranges not allowed when switching on type '{f}'", .{Type.fromIndex(item_ty).fmt(ip)});
    }

    const switch_src = sema.block.nodeOffset(switch_node_offset);
    switch (item_type_tag) {
        .@"enum" => {
            const all_tags_handled = for (seen_enum_fields) |seen_src| {
                if (seen_src == null) break false;
            } else true;

            if (has_else) {
                if (all_tags_handled) {
                    return sema.fail(sema.block, else_prong_src, "unreachable else prong; all cases already handled", .{});
                }
            } else if (!all_tags_handled) {
                return sema.failWithOwnedErrorMsg(sema.block, msg: {
                    const msg = try sema.errMsg(switch_src, "switch must handle all possibilities", .{});
                    errdefer msg.destroy(gpa);
                    for (seen_enum_fields, 0..) |seen_src, i| {
                        if (seen_src != null) continue;
                        const field_name = (try sema.enumFieldName(item_ty, @intCast(i))).?;
                        try sema.addFieldErrNote(item_ty, @intCast(i), msg, "unhandled enumeration value: '{f}'", .{field_name.fmt(ip)});
                    }
                    try sema.errNote(sema.containerTypeSrc(item_ty), msg, "enum '{f}' declared here", .{Type.fromIndex(item_ty).fmt(ip)});
                    break :msg msg;
                });
            }
        },
        .error_set => {
            if (isAnyerrorSet(ip, item_ty)) return sema.requireSwitchElse(item_ty, has_else);
            const set_ty = switch (ip.indexToKey(item_ty)) {
                .error_union_type => |eu| eu.error_set_type,
                else => item_ty,
            };
            const error_names = ip.indexToKey(set_ty).error_set_type.names;
            var maybe_msg: ?*ErrorMsg = null;
            errdefer if (maybe_msg) |msg| msg.destroy(gpa);

            var seen_errors_from_set: u32 = 0;
            for (error_names) |error_name| {
                if (seen_errors.contains(error_name)) {
                    seen_errors_from_set += 1;
                } else if (!has_else) {
                    const msg = maybe_msg orelse blk: {
                        maybe_msg = try sema.errMsg(switch_src, "switch must handle all possibilities", .{});
                        break :blk maybe_msg.?;
                    };
                    try sema.errNote(switch_src, msg, "unhandled error value: 'error.{f}'", .{error_name.fmt(ip)});
                }
            }

            if (maybe_msg) |msg| {
                maybe_msg = null;
                try sema.addDeclaredHereNote(msg, .fromIndex(item_ty));
                return sema.failWithOwnedErrorMsg(sema.block, msg);
            }

            if (has_else and seen_errors_from_set == error_names.len) {
                return sema.fail(sema.block, else_prong_src, "unreachable else prong; all cases already handled", .{});
            }
        },
        .int => check_range: {
            const int_ty = Type.fromIndex(item_ty);
            const min_int = try int_ty.minInt(sema, int_ty);
            const max_int = try int_ty.maxInt(sema, int_ty);
            if (try range_set.spans(sema.arena, min_int, max_int, int_ty, ip)) {
                if (has_else) {
                    return sema.fail(sema.block, else_prong_src, "unreachable else prong; all cases already handled", .{});
                }
                break :check_range;
            }
            if (!has_else) {
                return sema.fail(sema.block, switch_src, "switch must handle all possibilities", .{});
            }
        },
        .comptime_int, .enum_literal, .@"fn", .type => return sema.requireSwitchElse(item_ty, has_else),
        .bool, .void => {
            const all_values_handled = switch (item_type_tag) {
                .bool => true_src != null and false_src != null,
                .void => void_src != null,
                else => unreachable,
            };
            if (has_else) {
                if (all_values_handled) {
                    return sema.fail(sema.block, else_prong_src, "unreachable else prong; all cases already handled", .{});
                }
            } else if (!all_values_handled) {
                return sema.fail(sema.block, switch_src, "switch must handle all possibilities", .{});
            }
        },
        else => unreachable,
    }
}

fn bindSwitchCapture(
    sema: *Sema,
    inst: Zir.Inst.Index,
    sw: Zir.UnwrappedSwitchBlock,
    capture: Zir.Inst.SwitchBlock.ProngInfo.Capture,
    capture_val: Value,
) Error!void {
    const capture_inst = sw.payload_capture_placeholder.unwrap() orelse inst;
    const cap: Value = switch (capture) {
        .none => unreachable,
        .by_val => capture_val,
        .by_ref => try sema.materializeConstPtr(capture_val),
    };
    try sema.inst_map.put(sema.gpa, capture_inst, cap);
}

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
        const name = try ip.getOrPutString(sema.gpa, sema.zir.nullTerminatedString(name_idx), .no_embedded_nulls);
        const fld = (try sema.unionFieldByName(union_ty, name)) orelse return null;
        if (common) |c| {
            if (c != fld.ty) return null;
        } else common = fld.ty;
    }
    return common;
}

const SwitchOperand = struct {
    value: Value,
    ty: InternPool.Index,
    err_name: ?InternPool.NullTerminatedString,
};

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
                const item_coerced = try sema.coerceValueToType(item_raw, op.ty);
                if (item_coerced.index == op.value.index) hit = true;
            },
            .under => hit = true,
            .error_value => |item_err_name| {
                if (op.err_name) |opn| {
                    const item = try sema.intern_pool.getOrPutString(sema.gpa, sema.zir.nullTerminatedString(item_err_name), .no_embedded_nulls);
                    if (item == opn) hit = true;
                }
            },
            .enum_literal => |name_idx| {
                if (hit) continue;
                const name = try sema.intern_pool.getOrPutString(sema.gpa, sema.zir.nullTerminatedString(name_idx), .no_embedded_nulls);
                // `.Name` resolves against a field or a pub decl of the enum (a decl literal); the
                // compiler resolves a switch item through analyzeDeclLiteral, then coerces.
                const uncoerced = try sema.analyzeDeclLiteral(op.ty, name, false);
                const tag = try sema.coerceValueToType(uncoerced, op.ty);
                if (tag.index == op.value.index) hit = true;
            },
        }
    }
    return hit;
}

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
        const lo_co = try sema.coerceValueToType(lo_raw, op.ty);
        const hi_co = try sema.coerceValueToType(hi_raw, op.ty);
        if (try integerInRange(sema, op.value, lo_co, hi_co)) hit = true;
    }
    return hit;
}

fn integerInRange(sema: *Sema, x: Value, lo: Value, hi: Value) Error!bool {
    const x_key = sema.intern_pool.indexToKey(x.index);
    const lo_key = sema.intern_pool.indexToKey(lo.index);
    const hi_key = sema.intern_pool.indexToKey(hi.index);
    if (x_key != .int or lo_key != .int or hi_key != .int) {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "switch range: non-integer endpoint", .{});
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
    return sema.fail(sema.block, sema.block.nodeOffset(.zero), "unsupported switch construct: {s}", .{what});
}

fn evalParam(sema: *Sema, inst: Zir.Inst.Index, tag: Zir.Inst.Tag) Error!?Value {
    assert(@backingInt(inst) < sema.zir.instructions.len);

    const pl_tok = sema.zir.instructions.items(.data)[@backingInt(inst)].pl_tok;
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

fn resolveParamType(sema: *Sema, param_inst: Zir.Inst.Index) Error!InternPool.Index {
    const pl_tok = sema.zir.instructions.items(.data)[@backingInt(param_inst)].pl_tok;
    const extra = sema.zir.extraData(Zir.Inst.Param, pl_tok.payload_index);
    const body = sema.zir.bodySlice(extra.end, extra.data.type.body_len);
    return (try sema.coerceValueToType(try sema.resolveInlineBody(body, param_inst), .type_type)).index;
}

fn evalParamAnytype(sema: *Sema, tag: Zir.Inst.Tag) Error!?Value {
    try sema.block.params.append(sema.gpa, .{
        .ty = .generic_poison_type,
        .is_comptime = tag == .param_anytype_comptime,
    });
    return null;
}

fn evalRetType(sema: *Sema) Error!?Value {
    assert(sema.fn_ret_ty != .none);
    return .{ .index = sema.fn_ret_ty };
}

fn validateErrorUnionPayloadType(sema: *Sema, payload_ty: Type) Error!void {
    const ip = sema.intern_pool;
    if (payload_ty.zigTypeTag(ip) == .@"opaque") {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "error union with payload of opaque type '{f}' not allowed", .{payload_ty.fmt(ip)});
    } else if (payload_ty.zigTypeTag(ip) == .error_set) {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "error union with payload of error set type '{f}' not allowed", .{payload_ty.fmt(ip)});
    }
}

fn resolveDeclaredRetType(sema: *Sema, info: Zir.FnInfo, break_target: Zir.Inst.Index) Error!InternPool.Index {
    if (info.ret_ty_ref != .none) return (try sema.coerceValueToType(try sema.resolveInst(info.ret_ty_ref), .type_type)).index;
    if (info.ret_ty_body.len > 0) return (try sema.coerceValueToType(try sema.resolveInlineBody(info.ret_ty_body, break_target), .type_type)).index;
    return .void_type;
}

fn funcFancyExtras(sema: *Sema, inst: Zir.Inst.Index, tag: Zir.Inst.Tag) Error!struct { noalias_bits: u32, is_var_args: bool, cc: std.lang.CallingConvention } {
    if (tag != .func_fancy) return .{ .noalias_bits = 0, .is_var_args = false, .cc = .auto };
    const pl_node = sema.zir.instructions.items(.data)[@backingInt(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.FuncFancy, pl_node.payload_index);
    const bits = extra.data.bits;
    var extra_index = extra.end;

    const cc: std.lang.CallingConvention = if (bits.has_cc_body) blk: {
        const body_len = sema.zir.extra[extra_index];
        extra_index += 1;
        const body = sema.zir.bodySlice(extra_index, body_len);
        extra_index += body.len;
        const cc_ty = try sema.getStdLangType(.CallingConvention);
        break :blk try sema.interpretCallConv(try sema.coerceValueToType(try sema.resolveInlineBody(body, inst), cc_ty));
    } else if (bits.has_cc_ref) blk: {
        const cc_ref: Zir.Inst.Ref = @fromBackingInt(@intCast(sema.zir.extra[extra_index]));
        extra_index += 1;
        const cc_ty = try sema.getStdLangType(.CallingConvention);
        break :blk try sema.interpretCallConv(try sema.coerceValueToType(try sema.resolveInst(cc_ref), cc_ty));
    } else
        // The compiler defaults an exported decl to target.cCallingConvention(); that needs
        // export-linkage resolution and a concrete target ABI, neither present in the comptime REPL.
        .auto;

    if (bits.has_ret_ty_body) {
        extra_index += 1 + sema.zir.extra[extra_index];
    } else if (bits.has_ret_ty_ref) {
        extra_index += 1;
    }
    return .{
        .noalias_bits = if (bits.has_any_noalias) sema.zir.extra[extra_index] else 0,
        .is_var_args = bits.is_var_args,
        .cc = cc,
    };
}

fn evalFunc(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@backingInt(inst) < sema.zir.instructions.len);

    const info = sema.zir.getFnInfo(inst);

    const tag = sema.zir.instructions.items(.tag)[@backingInt(inst)];
    const fancy = try sema.funcFancyExtras(inst, tag);
    const cc_tag = std.meta.activeTag(fancy.cc);

    const bare_ret_ty: InternPool.Index = if (info.ret_ty_is_generic)
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

    for (params, 0..) |param_ty, i| {
        try sema.checkParamType(.fromIndex(param_ty), (fancy.noalias_bits >> @intCast(i)) & 1 != 0, cc_tag);
    }
    if (!info.ret_ty_is_generic) {
        try sema.checkReturnTypeAndCallConv(.fromIndex(bare_ret_ty), fancy.is_var_args, info.inferred_error_set, cc_tag);
    }

    // A `!T` return carries the adhoc inferred error set; the REPL never mints an inferred error set type.
    const ret_ty: InternPool.Index = if (info.inferred_error_set and !info.ret_ty_is_generic)
        try sema.intern_pool.internErrorUnionType(.{ .error_set_type = .adhoc_inferred_error_set_type, .payload_type = bare_ret_ty })
    else
        bare_ret_ty;

    const fn_ty = try sema.intern_pool.internFuncType(.{
        .param_types = params,
        .return_type = ret_ty,
        .comptime_bits = comptime_bits,
        .noalias_bits = fancy.noalias_bits,
        .is_var_args = fancy.is_var_args,
        .cc = fancy.cc,
    });
    if (info.body.len == 0) return Value{ .index = fn_ty };

    const func_idx = try sema.intern_pool.internFunc(.{
        .source_zir_id = sema.current_zir_id,
        .ty = fn_ty,
        .uncoerced_ty = fn_ty,
        .zir_body_inst = inst,
        .parent = if (sema.block.namespace) |ns| sema.intern_pool.namespacePtr(ns).owner_type else .none,
        .owner_nav = sema.owner_nav,
    });
    return Value{ .index = func_idx };
}

const ResolvedFieldCallee = union(enum) {
    /// The LHS of the call was an actual field with this value.
    direct: Value,
    /// This is a method call, with the function and first argument given.
    method: struct {
        func_inst: Value,
        arg0_inst: Value,
    },
};

/// Port of the compiler's `finishFieldCallBind` (src/Sema.zig): the callee is the field's value. A
/// comptime field short-circuits to its comptime-known value; any other field is reached through its
/// pointer.
fn finishFieldCallBind(sema: *Sema, object_ptr: Value, field_index: u32, concrete_ty: Type) Error!ResolvedFieldCallee {
    const ip = sema.intern_pool;
    if (concrete_ty.zigTypeTag(ip) == .@"struct") {
        if (concrete_ty.structFieldIsComptime(field_index, ip)) {
            const default_val = (try concrete_ty.structFieldValueComptime(sema, field_index)).?;
            return .{ .direct = default_val };
        }
    }
    const field_ptr = try sema.structFieldPtrByIndex(object_ptr, field_index, concrete_ty);
    return .{ .direct = try sema.loadValue(field_ptr) };
}

/// Port of the compiler's `fieldCallBind` (src/Sema.zig): resolve the callee of `a.b(args)` from a
/// pointer to `a`. `b` is either an actual field holding a value (`.direct`, no receiver) or a member
/// function bound with `a` as its first argument (`.method`).
fn fieldCallBind(sema: *Sema, raw_ptr: Value, field_name: InternPool.NullTerminatedString) Error!ResolvedFieldCallee {
    const ip = sema.intern_pool;
    const raw_ptr_ty = raw_ptr.typeOf(ip);
    const inner_ty = if (raw_ptr_ty.zigTypeTag(ip) == .pointer and (raw_ptr_ty.ptrInfo(ip).flags.size == .one or raw_ptr_ty.ptrInfo(ip).flags.size == .c))
        raw_ptr_ty.childType(ip)
    else
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "expected single pointer, found '{f}'", .{raw_ptr_ty.fmt(ip)});

    // Optionally dereference a second pointer to get the concrete type.
    const is_double_ptr = inner_ty.zigTypeTag(ip) == .pointer and inner_ty.ptrInfo(ip).flags.size == .one;
    const concrete_ty = if (is_double_ptr) inner_ty.childType(ip) else inner_ty;
    try sema.ensureLayoutResolved(concrete_ty.toIndex());
    const object_ptr = if (is_double_ptr) try sema.loadValue(raw_ptr) else raw_ptr;

    find_field: {
        switch (concrete_ty.zigTypeTag(ip)) {
            .@"struct" => {
                if (ip.indexToKey(concrete_ty.toIndex()) == .struct_type) {
                    const field = (try sema.structFieldByName(concrete_ty.toIndex(), field_name)) orelse break :find_field;
                    return try sema.finishFieldCallBind(object_ptr, field.index, concrete_ty);
                }
                // The REPL models a tuple as its own key and reaches elements by index, so a tuple
                // exposes no by-name callable field to bind; fall through to the decl lookup.
                break :find_field;
            },
            .@"union" => {
                if ((try sema.unionFieldByName(concrete_ty.toIndex(), field_name)) == null) break :find_field;
                const field_ptr = try sema.unionFieldPtr(object_ptr, field_name, concrete_ty, false);
                return .{ .direct = try sema.loadValue(field_ptr) };
            },
            .type => {
                const namespace = try sema.loadValue(object_ptr);
                return .{ .direct = (try sema.containerDeclByName(namespace.toIndex(), field_name)) orelse
                    return sema.failBadMemberAccess(namespace.toIndex(), field_name) };
            },
            else => {},
        }
    }

    // If we get here, we need to look for a decl in the struct type instead.
    const found_nav = found_nav: {
        const namespace = sema.getNamespaceIndex(concrete_ty.toIndex()) orelse
            break :found_nav null;
        const nav_index = (try sema.namespaceLookup(namespace, field_name)) orelse
            break :found_nav null;

        const decl_val = try sema.analyzeNavVal(nav_index);
        const decl_type = decl_val.typeOf(ip);
        if (ip.indexToKey(decl_type.toIndex()) == .func_type) f: {
            const func_type = ip.indexToKey(decl_type.toIndex()).func_type;
            if (func_type.param_types.len == 0) break :f;

            const first_param_type: Type = .fromIndex(func_type.param_types[0]);
            if (first_param_type.toIndex() == .generic_poison_type or
                (first_param_type.zigTypeTag(ip) == .pointer and
                    (first_param_type.ptrInfo(ip).flags.size == .one or
                        first_param_type.ptrInfo(ip).flags.size == .c) and
                    first_param_type.childType(ip).toIndex() == concrete_ty.toIndex()))
            {
                return .{ .method = .{ .func_inst = decl_val, .arg0_inst = object_ptr } };
            } else if (first_param_type.toIndex() == concrete_ty.toIndex()) {
                const deref = try sema.loadValue(object_ptr);
                return .{ .method = .{ .func_inst = decl_val, .arg0_inst = deref } };
            } else if (first_param_type.zigTypeTag(ip) == .optional) {
                const child = first_param_type.optionalChild(ip);
                if (child.toIndex() == concrete_ty.toIndex()) {
                    const deref = try sema.loadValue(object_ptr);
                    return .{ .method = .{ .func_inst = decl_val, .arg0_inst = deref } };
                } else if (child.zigTypeTag(ip) == .pointer and
                    child.ptrInfo(ip).flags.size == .one and
                    child.childType(ip).toIndex() == concrete_ty.toIndex())
                {
                    return .{ .method = .{ .func_inst = decl_val, .arg0_inst = object_ptr } };
                }
            } else if (first_param_type.zigTypeTag(ip) == .error_union and
                first_param_type.errorUnionPayload(ip).toIndex() == concrete_ty.toIndex())
            {
                const deref = try sema.loadValue(object_ptr);
                return .{ .method = .{ .func_inst = decl_val, .arg0_inst = deref } };
            }
        }
        break :found_nav nav_index;
    };
    _ = found_nav;
    // The compiler emits a richer "no field or member function" error with notes; the REPL reports
    // its standard member-access diagnostic.
    return sema.failBadMemberAccess(concrete_ty.toIndex(), field_name);
}

fn checkCallArgumentCount(sema: *Sema, func_src: LazySrcLoc, func_ty: InternPool.Key.FuncType, total_args: u32, member_fn: bool) Error!void {
    const fn_params_len = func_ty.param_types.len;
    if (func_ty.is_var_args) {
        assert(callConvSupportsVarArgs(std.meta.activeTag(func_ty.cc)));
        if (total_args >= fn_params_len) return;
    } else if (fn_params_len == total_args) {
        return;
    }

    const member_str = if (member_fn) "member function " else "";
    const variadic_str = if (func_ty.is_var_args) "at least " else "";
    const args_len = total_args - @intFromBool(member_fn);
    return sema.fail(sema.block, func_src, "{s}expected {s}{d} argument(s), found {d}", .{
        member_str,
        variadic_str,
        fn_params_len - @intFromBool(member_fn),
        args_len,
    });
}

fn evalCall(sema: *Sema, inst: Zir.Inst.Index, comptime kind: enum { direct, field }) Error!?Value {
    assert(@backingInt(inst) < sema.zir.instructions.len);

    try sema.emitBackwardBranch();

    const callee_value: Value, const self_val: ?Value, const explicit_len: u32, const args_body: []const Zir.Inst.Index, const enclosing_ty: InternPool.Index = switch (kind) {
        .direct => blk: {
            const pl_node = sema.zir.instructions.items(.data)[@backingInt(inst)].pl_node;
            const extra = sema.zir.extraData(Zir.Inst.Call, pl_node.payload_index);
            break :blk .{
                try sema.resolveInst(extra.data.callee),
                null,
                extra.data.flags.args_len,
                @ptrCast(sema.zir.extra[extra.end..]),
                .none,
            };
        },
        .field => blk: {
            const pl_node = sema.zir.instructions.items(.data)[@backingInt(inst)].pl_node;
            const extra = sema.zir.extraData(Zir.Inst.FieldCall, pl_node.payload_index);
            const name = try sema.intern_pool.getOrPutString(sema.gpa, sema.zir.nullTerminatedString(extra.data.field_name_start), .no_embedded_nulls);
            const object_ptr = try sema.resolveInst(extra.data.obj_ptr);
            const args_slice: []const Zir.Inst.Index = @ptrCast(sema.zir.extra[extra.end..]);
            const callee: Value, const self: ?Value = switch (try sema.fieldCallBind(object_ptr, name)) {
                .direct => |func_inst| .{ func_inst, null },
                .method => |method| .{ method.func_inst, method.arg0_inst },
            };
            // The call namespace comes from the resolved function's parent; the receiver's concrete
            // type is the fallback when that function has none.
            const enclosing_ty = enc: {
                const object = try sema.loadValue(object_ptr);
                const object_ty = object.typeOf(sema.intern_pool);
                if (object_ty.toIndex() == .type_type) break :enc object.index;
                break :enc if (object_ty.isSinglePointer(sema.intern_pool)) object_ty.childType(sema.intern_pool).toIndex() else object_ty.toIndex();
            };
            break :blk .{ callee, self, extra.data.flags.args_len, args_slice, enclosing_ty };
        },
    };

    // A callee may be a pointer to a function -- a stored `*const fn(...)` or a vtable entry.
    // Dereference to the function value it points to before calling.
    var callee_resolved = callee_value;
    while (sema.intern_pool.indexToKey(callee_resolved.index) == .ptr) callee_resolved = try sema.loadValue(callee_resolved);
    const callee_key = sema.intern_pool.indexToKey(callee_resolved.index);
    if (callee_key == .@"extern") {
        if (try runtime.callIntrinsic(sema, callee_key.@"extern", explicit_len, args_body, inst)) |result| return result;
    }
    if (callee_key != .func) {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "call: callee is not a function value", .{});
    }
    const func = callee_key.func;
    var func_ty = sema.intern_pool.indexToKey(func.ty).func_type;
    const param_types = try sema.gpa.dupe(InternPool.Index, func_ty.param_types);
    defer sema.gpa.free(param_types);
    func_ty.param_types = param_types;

    const args_len = explicit_len + @as(u32, @intFromBool(self_val != null));
    try sema.checkCallArgumentCount(sema.block.nodeOffset(sema.srcNodeOffset(inst)), func_ty, args_len, self_val != null);
    const target_ty = if (func.parent != .none) func.parent else enclosing_ty;
    var call_block: Block = .{
        .namespace = if (target_ty != .none) sema.getNamespaceIndex(target_ty) else sema.block.namespace,
        .src_base_inst = sema.block.src_base_inst,
        .type_name_ctx = sema.block.type_name_ctx,
    };
    const caller_block = sema.block;
    defer call_block.deinit(sema.gpa);

    // The call must be comptime-evaluated -- so its arguments are comptime-known -- when the callee is
    // `inline` (compiler: `early_known_inline` propagates comptime args) or its return type is a
    // non-generic comptime-only type (compiler: enters a comptime scope). Mirrors the pre-argument
    // comptime-scope setup at ../zig/src/Sema.zig ~6716-6740.
    const early_known_inline = func_ty.cc == .@"inline";
    const saved_caller_comptime = caller_block.comptime_reason;
    defer caller_block.comptime_reason = saved_caller_comptime;
    if (!caller_block.isComptime() and !early_known_inline and
        func_ty.return_type != .generic_poison_type and
        Type.fromIndex(func_ty.return_type).comptimeOnly(sema.intern_pool))
    {
        const call_src = caller_block.nodeOffset(sema.srcNodeOffset(inst));
        caller_block.comptime_reason = .{ .reason = .{ .src = call_src, .r = .{ .comptime_only_ret_ty = .{
            .ty = Type.fromIndex(func_ty.return_type),
            .is_generic_inst = false,
            .ret_ty_src = call_src,
        } } } };
    }

    // A call inside a comptime scope is an inline call: the callee inherits the comptime scope, so its
    // parameters and everything computed from them are comptime-known, and diagnostics can attribute
    // the requirement back to the call site.
    var inlining: Block.Inlining = .{
        .call_block = caller_block,
        .call_src = caller_block.nodeOffset(sema.srcNodeOffset(inst)),
    };
    if (caller_block.isComptime()) {
        call_block.inlining = &inlining;
        call_block.comptime_reason = .inlining_parent;
    }

    // The fn info, param instructions, and param-type ZIR all live in the callee's ZIR.
    const info, const param_insts, const callee_param_tags = fetch: {
        const info_frame = try sema.enterSourceZir(func.source_zir_id, "call");
        defer info_frame.restore(sema);
        const fi = sema.zir.getFnInfo(func.zir_body_inst);
        break :fetch .{ fi, try sema.collectParamInsts(fi, args_len), sema.zir.instructions.items(.tag) };
    };
    defer sema.gpa.free(param_insts);

    // Evaluate arguments and bind parameters in lockstep, like the compiler's call loop: a generic
    // parameter's type is evaluated in the callee frame with the already-bound earlier parameters,
    // so a later argument can use that resolved type as its result location.
    var generic_inst_map: std.AutoHashMapUnmanaged(Zir.Inst.Index, Value) = .empty;
    errdefer generic_inst_map.deinit(sema.gpa);
    const base: u32 = @intFromBool(self_val != null);
    for (0..args_len) |arg_idx_usize| {
        const arg_idx: u32 = @intCast(arg_idx_usize);
        const p_inst = param_insts[arg_idx];
        const declared = func_ty.param_types[arg_idx];
        const param_ty: InternPool.Index = if (declared != .generic_poison_type)
            declared
        else switch (callee_param_tags[@backingInt(p_inst)]) {
            .param_anytype, .param_anytype_comptime => .generic_poison_type,
            else => blk: {
                const tframe = try sema.enterSourceZir(func.source_zir_id, "call param type");
                const saved_im = sema.inst_map;
                sema.inst_map = generic_inst_map;
                sema.block = &call_block;
                defer {
                    generic_inst_map = sema.inst_map;
                    sema.inst_map = saved_im;
                    sema.block = caller_block;
                    tframe.restore(sema);
                }
                break :blk try sema.resolveParamType(p_inst);
            },
        };

        const raw: Value = if (self_val != null and arg_idx == 0)
            self_val.?
        else raw: {
            const i = arg_idx - base;
            const start = if (i == 0) explicit_len else @backingInt(args_body[i - 1]);
            const end = @backingInt(args_body[i]);
            try sema.inst_map.put(sema.gpa, inst, .{ .index = param_ty });
            break :raw try sema.resolveInlineBody(args_body[start..end], inst);
        };

        const final_ty = if (param_ty == .generic_poison_type) raw.typeOf(sema.intern_pool).toIndex() else param_ty;
        var val = try sema.coerceValueToType(raw, final_ty);
        // An inline call (in a comptime scope) makes every parameter comptime-known. Otherwise a
        // comptime-only argument (e.g. comptime_int, type) is still comptime-known even for a
        // non-`comptime` parameter, matching the compiler's `declared or arg_ty.comptimeOnly`.
        val.is_comptime = caller_block.isComptime() or early_known_inline or func_ty.paramIsComptime(@intCast(arg_idx)) or Type.fromIndex(final_ty).comptimeOnly(sema.intern_pool);
        try generic_inst_map.put(sema.gpa, p_inst, val);
    }

    sema.block = &call_block;
    defer sema.block = caller_block;

    const frame = try sema.enterSourceZir(func.source_zir_id, "call");
    defer frame.restore(sema);

    const old_inst_map = sema.inst_map;
    sema.inst_map = generic_inst_map;
    generic_inst_map = .empty;
    defer {
        sema.inst_map.deinit(sema.gpa);
        sema.inst_map = old_inst_map;
    }

    const saved_ret_ty = sema.fn_ret_ty;
    sema.fn_ret_ty = if (func_ty.return_type == .generic_poison_type)
        try sema.resolveDeclaredRetType(info, func.zir_body_inst)
    else
        func_ty.return_type;
    defer sema.fn_ret_ty = saved_ret_ty;

    if (sema.resolveInlineBody(info.body, func.zir_body_inst)) |val| {
        return val;
    } else |err| switch (err) {
        error.ComptimeReturn => return try sema.coerceValueToType(sema.return_value, sema.fn_ret_ty),
        else => |e| return e,
    }
}

fn collectParamInsts(sema: *Sema, info: Zir.FnInfo, args_len: u32) Error![]Zir.Inst.Index {
    const tags = sema.zir.instructions.items(.tag);
    const param_insts = try sema.gpa.alloc(Zir.Inst.Index, args_len);
    errdefer sema.gpa.free(param_insts);
    var pi: u32 = 0;
    for (info.param_body) |param_inst| {
        switch (tags[@backingInt(param_inst)]) {
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

fn evalBlockComptime(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@backingInt(inst) < sema.zir.instructions.len);

    const pl_node = sema.zir.instructions.items(.data)[@backingInt(inst)].pl_node;
    const src = sema.block.nodeOffset(pl_node.src_node);
    const extra = sema.zir.extraData(Zir.Inst.BlockComptime, pl_node.payload_index);
    const body = sema.zir.bodySlice(extra.end, extra.data.body_len);

    const parent_block = sema.block;
    var child_block: Block = .{
        .namespace = parent_block.namespace,
        .src_base_inst = parent_block.src_base_inst,
        .type_name_ctx = parent_block.type_name_ctx,
        .inlining = parent_block.inlining,
        .comptime_reason = .{ .reason = .{ .src = src, .r = .{ .simple = extra.data.reason } } },
    };
    defer child_block.deinit(sema.gpa);
    sema.block = &child_block;
    defer sema.block = parent_block;

    const result = try sema.resolveInlineBody(body, inst);

    // Only check for the result being comptime-known in the outermost `block_comptime`, so AstGen may
    // safely elide redundant `block_comptime`. `is_comptime` is the REPL's comptime-known analog.
    if (!parent_block.isComptime() and !result.is_comptime) {
        return sema.failWithNeededComptime(&child_block, src, null);
    }
    return result;
}

fn evalTypeof(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@backingInt(inst) < sema.zir.instructions.len);

    const un_node = sema.zir.instructions.items(.data)[@backingInt(inst)].un_node;
    // The type is comptime-known even when the operand is a runtime value; the compiler
    // returns `Air.internedToRef(operand_ty)` unconditionally, so the operand must not
    // taint this result's comptime flag.
    const saved_operand_comptime = sema.operand_comptime;
    const operand = try sema.resolveInst(un_node.operand);
    sema.operand_comptime = saved_operand_comptime;
    return Value{ .index = Value.typeOf(operand, sema.intern_pool).index };
}

fn evalThis(sema: *Sema) Error!?Value {
    const ns = sema.block.namespace orelse
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "@This(): no enclosing container", .{});
    return Value{ .index = sema.intern_pool.namespacePtr(ns).owner_type };
}

fn evalClosureGet(sema: *Sema, extended: Zir.Inst.Extended.InstData) Error!?Value {
    const ns = sema.block.namespace orelse
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "closure_get: no enclosing container", .{});
    const captures = switch (sema.intern_pool.indexToKey(sema.intern_pool.namespacePtr(ns).owner_type)) {
        .struct_type => |st| st.captures(),
        .union_type => |ut| ut.captures(),
        .enum_type => |et| et.captures(),
        else => unreachable,
    };
    assert(extended.small < captures.len);
    return Value{ .index = captures[extended.small] };
}

fn evalOverflowArithmetic(sema: *Sema, extended: Zir.Inst.Extended.InstData, opcode: Zir.Inst.Extended) Error!?Value {
    const ip = sema.intern_pool;
    const extra = sema.zir.extraData(Zir.Inst.BinNode, extended.operand).data;
    const uncasted_lhs = try sema.resolveInst(extra.lhs);
    const uncasted_rhs = try sema.resolveInst(extra.rhs);
    const lhs_ty = Value.typeOf(uncasted_lhs, ip);
    const rhs_ty = Value.typeOf(uncasted_rhs, ip);

    try sema.checkVectorizableBinaryOperands(lhs_ty, rhs_ty);
    const dest_ty = if (opcode == .shl_with_overflow)
        lhs_ty
    else
        try sema.resolvePeerTypes(&.{ uncasted_lhs, uncasted_rhs });
    const rhs_dest_ty: Type = if (opcode == .shl_with_overflow)
        .fromIndex(try sema.log2IntType(lhs_ty.index))
    else
        dest_ty;

    const lhs = try sema.coerceValueToType(uncasted_lhs, dest_ty.index);
    const rhs = try sema.coerceValueToType(uncasted_rhs, rhs_dest_ty.index);

    if (dest_ty.scalarType(ip).zigTypeTag(ip) != .int) {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "expected vector of integers or integer tag type, found '{f}'", .{dest_ty.fmt(ip)});
    }

    const tuple_ty = try sema.overflowArithmeticTupleType(dest_ty);
    const overflow_ty: Type = .fromIndex(ip.indexToKey(tuple_ty.index).tuple_type.types[1]);
    const zero_overflow = try sema.splat(overflow_ty, Value.zero_u1);
    const undef: Value = .{ .index = .undef };

    var wrapped: Value = undefined;
    var overflow_bit: Value = undefined;
    switch (opcode) {
        .add_with_overflow => {
            if (!lhs.isUndef(ip) and lhs.compareAllWithZero(.eq, ip)) {
                wrapped = rhs;
                overflow_bit = zero_overflow;
            } else if (!rhs.isUndef(ip) and rhs.compareAllWithZero(.eq, ip)) {
                wrapped = lhs;
                overflow_bit = zero_overflow;
            } else if (lhs.isUndef(ip) or rhs.isUndef(ip)) {
                wrapped = undef;
                overflow_bit = undef;
            } else {
                const r = try arith.addWithOverflow(sema, dest_ty, lhs, rhs);
                wrapped = r.wrapped_result;
                overflow_bit = r.overflow_bit;
            }
        },
        .sub_with_overflow => {
            if (rhs.isUndef(ip)) {
                wrapped = undef;
                overflow_bit = undef;
            } else if (rhs.compareAllWithZero(.eq, ip)) {
                wrapped = lhs;
                overflow_bit = zero_overflow;
            } else if (lhs.isUndef(ip)) {
                wrapped = undef;
                overflow_bit = undef;
            } else {
                const r = try arith.subWithOverflow(sema, dest_ty, lhs, rhs);
                wrapped = r.wrapped_result;
                overflow_bit = r.overflow_bit;
            }
        },
        .mul_with_overflow => {
            // If either operand is one, the result is the other and no overflow occurred. i1 is excluded
            // because '1' is not a legal signed-i1 value.
            const dest_scalar_int = dest_ty.scalarType(ip).intInfo(ip);
            const one_matters = !(dest_scalar_int.bits == 1 and dest_scalar_int.signedness == .signed);
            const vec_one: ?Value = if (one_matters) try sema.splat(dest_ty, try sema.intValue_u64(dest_ty.scalarType(ip), 1)) else null;
            const lhs_is_one = if (vec_one) |one| !lhs.isUndef(ip) and try sema.compareAll(lhs, .eq, one, dest_ty) else false;
            const rhs_is_one = if (vec_one) |one| !rhs.isUndef(ip) and try sema.compareAll(rhs, .eq, one, dest_ty) else false;
            if (!lhs.isUndef(ip) and lhs.compareAllWithZero(.eq, ip)) {
                wrapped = lhs;
                overflow_bit = zero_overflow;
            } else if (!rhs.isUndef(ip) and rhs.compareAllWithZero(.eq, ip)) {
                wrapped = rhs;
                overflow_bit = zero_overflow;
            } else if (lhs_is_one) {
                wrapped = rhs;
                overflow_bit = zero_overflow;
            } else if (rhs_is_one) {
                wrapped = lhs;
                overflow_bit = zero_overflow;
            } else if (lhs.isUndef(ip) or rhs.isUndef(ip)) {
                wrapped = undef;
                overflow_bit = undef;
            } else {
                const r = try arith.mulWithOverflow(sema, dest_ty, lhs, rhs);
                wrapped = r.wrapped_result;
                overflow_bit = r.overflow_bit;
            }
        },
        .shl_with_overflow => {
            const r = try arith.shlWithOverflow(sema, lhs_ty, lhs, rhs);
            wrapped = r.wrapped_result;
            overflow_bit = r.overflow_bit;
        },
        else => unreachable,
    }

    return try sema.aggregateValue(tuple_ty, &.{ wrapped.index, overflow_bit.index });
}

fn evalTypeofPeer(sema: *Sema, extended: Zir.Inst.Extended.InstData, inst: Zir.Inst.Index) Error!?Value {
    const extra = sema.zir.extraData(Zir.Inst.TypeOfPeer, extended.operand);
    const body = sema.zir.bodySlice(extra.data.body_index, extra.data.body_len);
    // The compiler evaluates the operand body in an `is_typeof` block whose runtime side
    // is discarded and returns `Air.internedToRef(result_type)`; the peer type is
    // comptime-known, so keep the operands' runtime-ness from tainting it.
    const saved_operand_comptime = sema.operand_comptime;
    _ = try sema.resolveInlineBody(body, inst);

    const args = sema.zir.refSlice(extra.end, extended.small);
    assert(args.len > 0);

    const insts = try sema.arena.alloc(Value, args.len);
    for (insts, args) |*v, arg_ref| v.* = try sema.resolveInst(arg_ref);
    sema.operand_comptime = saved_operand_comptime;
    const ty = try sema.resolvePeerTypes(insts);
    return Value{ .index = ty.index };
}

fn evalTypeofBuiltin(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@backingInt(inst) < sema.zir.instructions.len);

    const pl_node = sema.zir.instructions.items(.data)[@backingInt(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.Block, pl_node.payload_index);
    const body = sema.zir.bodySlice(extra.end, extra.data.body_len);
    // The compiler evaluates the operand body in an `is_typeof` block whose runtime side
    // is discarded and returns `Air.internedToRef(operand_ty)`; the type is comptime-known,
    // so keep the operand's runtime-ness from tainting this result's comptime flag.
    const saved_operand_comptime = sema.operand_comptime;
    const operand = try sema.resolveInlineBody(body, inst);
    sema.operand_comptime = saved_operand_comptime;
    return Value{ .index = Value.typeOf(operand, sema.intern_pool).index };
}

fn evalIntFromError(sema: *Sema, extended: Zir.Inst.Extended.InstData) Error!?Value {
    const ip = sema.intern_pool;
    const extra = sema.zir.extraData(Zir.Inst.UnNode, extended.operand).data;
    const operand = try sema.coerceValueToType(try sema.resolveInst(extra.operand), .anyerror_type);
    const err_int_ty = Type.fromIndex(try ip.errorIntType());
    if (operand.isUndef(ip)) return try sema.undefValue(err_int_ty);
    const err_name = ip.indexToKey(operand.index).err.name;
    return try sema.intValue_u64(err_int_ty, try ip.getErrorValue(err_name));
}

fn evalErrorFromInt(sema: *Sema, extended: Zir.Inst.Extended.InstData) Error!?Value {
    const ip = sema.intern_pool;
    const extra = sema.zir.extraData(Zir.Inst.UnNode, extended.operand).data;
    const err_int_ty = Type.fromIndex(try ip.errorIntType());
    const operand = try sema.coerceValueToType(try sema.resolveInst(extra.operand), err_int_ty.index);
    const int = operand.toUnsignedInt(ip);
    if (int == 0 or int > ip.global_error_set.count()) {
        return sema.fail(sema.block, sema.block.nodeOffset(extra.node), "integer value '{d}' represents no error", .{int});
    }
    const name = ip.global_error_set.keys()[@intCast(int - 1)];
    return .fromIndex(try ip.internErr(.{ .ty = .anyerror_type, .name = name }));
}

fn evalErrorCast(sema: *Sema, extended: Zir.Inst.Extended.InstData) Error!?Value {
    const ip = sema.intern_pool;
    const extra = sema.zir.extraData(Zir.Inst.BinNode, extended.operand).data;
    const src = sema.block.nodeOffset(extra.node);

    var dest_ty = Type.fromIndex(try sema.resolveDestType(extra.lhs));
    if (dest_ty.zigTypeTag(ip) == .optional) dest_ty = dest_ty.optionalChild(ip);
    const operand = try sema.resolveInst(extra.rhs);
    const operand_ty = Value.typeOf(operand, ip);

    const dest_tag = dest_ty.zigTypeTag(ip);
    const operand_tag = operand_ty.zigTypeTag(ip);

    if (dest_tag != .error_set and dest_tag != .error_union) {
        return sema.fail(sema.block, src, "expected error set or error union type, found '{s}'", .{@tagName(dest_tag)});
    }
    if (operand_tag != .error_set and operand_tag != .error_union) {
        return sema.fail(sema.block, src, "expected error set or error union type, found '{s}'", .{@tagName(operand_tag)});
    }
    if (dest_tag == .error_set and operand_tag == .error_union) {
        return sema.fail(sema.block, src, "cannot cast an error union type to error set", .{});
    }
    if (dest_tag == .error_union and operand_tag == .error_union and
        dest_ty.errorUnionPayload(ip).index != operand_ty.errorUnionPayload(ip).index)
    {
        const msg = try sema.errMsg(src, "payload types of error unions must match", .{});
        try sema.errNote(src, msg, "destination payload is '{f}'", .{dest_ty.errorUnionPayload(ip).fmt(ip)});
        try sema.errNote(src, msg, "operand payload is '{f}'", .{operand_ty.errorUnionPayload(ip).fmt(ip)});
        return sema.failWithOwnedErrorMsg(sema.block, msg);
    }

    const dest_err_ty = switch (dest_tag) {
        .error_union => dest_ty.errorUnionSet(ip),
        .error_set => dest_ty,
        else => unreachable,
    };
    const operand_err_ty = switch (operand_tag) {
        .error_union => operand_ty.errorUnionSet(ip),
        .error_set => operand_ty,
        else => unreachable,
    };

    const result: enum {
        disjoint,
        superset,
        overlap,
    } = if (operand_err_ty.errorSetIsEmpty(ip)) res: {
        break :res .disjoint;
    } else check: switch (dest_err_ty.index) {
        .anyerror_type => .superset,
        .adhoc_inferred_error_set_type => .superset,
        else => |err_set_ty| switch (ip.indexToKey(err_set_ty)) {
            .error_set_type => |dest| {
                if (dest.names.len == 0) break :check .disjoint;
                if (operand_err_ty.isAnyError(ip)) break :check .overlap;
                var dest_has_all = true;
                var dest_has_any = false;
                for (operand_err_ty.errorSetNames(ip)) |operand_err_name| {
                    if (dest.nameIndex(ip, operand_err_name) != null) {
                        dest_has_any = true;
                    } else {
                        dest_has_all = false;
                    }
                }
                if (!dest_has_any) break :check .disjoint;
                if (dest_has_all) break :check .superset;
                break :check .overlap;
            },
            else => unreachable,
        },
    };

    if (result == .disjoint and !(operand_tag == .error_union and dest_tag == .error_union)) {
        return sema.fail(sema.block, src, "error sets '{f}' and '{f}' have no common errors", .{
            operand_err_ty.fmt(ip), dest_err_ty.fmt(ip),
        });
    }

    const err_name: InternPool.NullTerminatedString = switch (ip.indexToKey(operand.index)) {
        .err => |err| err.name,
        .error_union => |eu| switch (eu.val) {
            .err_name => |name| name,
            .payload => |payload_val| {
                assert(dest_tag == .error_union);
                return try sema.coerceToErrorUnion(.{ .index = payload_val }, dest_ty.index);
            },
        },
        else => unreachable,
    };

    if (result != .superset and !dest_err_ty.errorSetHasField(err_name, ip)) {
        return sema.fail(sema.block, src, "'error.{f}' not a member of error set '{f}'", .{
            err_name.fmt(ip), dest_err_ty.fmt(ip),
        });
    }

    return switch (dest_tag) {
        .error_set => .{ .index = try ip.internErr(.{ .ty = dest_ty.index, .name = err_name }) },
        .error_union => .{ .index = try ip.internErrorUnion(.{ .ty = dest_ty.index, .val = .{ .err_name = err_name } }) },
        else => unreachable,
    };
}

fn evalExtended(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@backingInt(inst) < sema.zir.instructions.len);

    const extended = sema.zir.instructions.items(.data)[@backingInt(inst)].extended;
    switch (extended.opcode) {
        .dbg_empty_stmt,
        .breakpoint,
        .disable_instrumentation,
        .disable_intrinsics,
        .branch_hint,
        .set_float_mode,
        .restore_err_ret_index,
        => return null,

        // `@inComptime()` is always true: the interpreter evaluates everything at comptime (it folds,
        // it does not emit runtime code), so std code that branches on `@inComptime` must take its
        // comptime path -- the only one the interpreter can execute. This is distinct from the
        // `block.isComptime()` coercion axis, which governs runtime-narrowing rejection and inline calls.
        .in_comptime => return Value.bool_true,

        .select => return sema.evalSelect(extended),
        .add_with_overflow,
        .sub_with_overflow,
        .mul_with_overflow,
        .shl_with_overflow,
        => return sema.evalOverflowArithmetic(extended, extended.opcode),
        .min_multi => return sema.evalMinMaxMulti(extended, .min),
        .max_multi => return sema.evalMinMaxMulti(extended, .max),
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
        .opaque_decl => return sema.evalOpaqueDecl(inst),
        .typeof_peer => return sema.evalTypeofPeer(extended, inst),
        .this => return sema.evalThis(),
        .closure_get => return sema.evalClosureGet(extended),
        .int_from_error => return sema.evalIntFromError(extended),
        .error_from_int => return sema.evalErrorFromInt(extended),
        .error_cast => return sema.evalErrorCast(extended),
        .ptr_cast_full => return sema.evalPtrCastFull(extended),
        .ptr_cast_no_dest => return sema.evalPtrCastNoDest(extended),
        .field_parent_ptr => return sema.evalFieldParentPtr(extended),

        .inplace_arith_result_ty => {
            const lhs = try sema.resolveInst(@fromBackingInt(@intCast(extended.operand)));
            return Value{ .index = Value.typeOf(lhs, sema.intern_pool).index };
        },

        .std_lang_value => return sema.evalStdLangValue(extended),

        .frame => return sema.failUseOfAsync(),

        inline else => |op| {
            return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "unsupported extended ZIR opcode: {s}", .{@tagName(op)});
        },
    }
}

fn reportUnsupportedTag(sema: *Sema, comptime tag: Zir.Inst.Tag) Error {
    return sema.fail(sema.block, sema.block.nodeOffset(.zero), "unsupported ZIR instruction: {s}", .{@tagName(tag)});
}

fn failUseOfAsync(sema: *Sema) Error!?Value {
    return sema.fail(sema.block, sema.block.nodeOffset(.zero), "async has not been implemented in the self-hosted compiler yet", .{});
}

const testing = std.testing;

fn opvTestSema(gpa: std.mem.Allocator, pool: *InternPool, arena: *std.heap.ArenaAllocator, w: *std.Io.Writer) Sema {
    return .{
        .gpa = gpa,
        .arena = arena.allocator(),
        .intern_pool = pool,
        .zir = undefined,
        .writer = w,
        .inst_map = .empty,
        .comptime_allocs = .empty,
    };
}

fn opvNames(sema: *Sema, names: []const []const u8) ![]InternPool.NullTerminatedString {
    const out = try sema.arena.alloc(InternPool.NullTerminatedString, names.len);
    for (names, out) |n, *h| h.* = try sema.intern_pool.getOrPutString(sema.gpa, n, .no_embedded_nulls);
    return out;
}

fn opvEnum(sema: *Sema, hash: u64, names: []const []const u8) !Type {
    const pool = sema.intern_pool;
    const handles = try opvNames(sema, names);
    const tag_ty = try sema.enumIntTagType(@intCast(names.len));
    const enum_ty = try pool.getReifiedEnumType(.{
        .name = try pool.getOrPutString(sema.gpa, "E", .no_embedded_nulls),
        .id = .{ .reified = .{ .source_zir_id = 0, .decl_inst = @fromBackingInt(@intCast(0)), .type_hash = hash } },
        .int_tag_type = tag_ty,
        .nonexhaustive = false,
        .names = handles,
        .values = &.{},
    });
    const f = pool.loadEnumType(enum_ty);
    f.field_name_map.get(pool).clearRetainingCapacity();
    for (handles) |name| assert(pool.addFieldName(handles, f.field_name_map, name) == null);
    return .fromIndex(enum_ty);
}

fn opvStruct(sema: *Sema, hash: u64, names: []const []const u8, types: []const InternPool.Index) !Type {
    const pool = sema.intern_pool;
    const handles = try opvNames(sema, names);
    const struct_ty = try pool.getReifiedStructType(.{
        .name = try pool.getOrPutString(sema.gpa, "S", .no_embedded_nulls),
        .id = .{ .reified = .{ .source_zir_id = 0, .decl_inst = @fromBackingInt(@intCast(0)), .type_hash = hash } },
        .layout = .auto,
        .backing_int = .none,
        .names = handles,
        .types = types,
        .defaults = &.{},
        .aligns = &.{},
        .comptime_bits = &.{},
    });
    const f = pool.loadStructType(struct_ty);
    f.field_name_map.get(pool).clearRetainingCapacity();
    for (handles) |name| assert(pool.addFieldName(handles, f.field_name_map, name) == null);
    return .fromIndex(struct_ty);
}

fn opvUnion(sema: *Sema, hash: u64, tag_hash: u64, names: []const []const u8, types: []const InternPool.Index) !Type {
    const pool = sema.intern_pool;
    const tag_enum = try opvEnum(sema, tag_hash, names);
    const handles = try opvNames(sema, names);
    const union_ty = try pool.getReifiedUnionType(.{
        .name = try pool.getOrPutString(sema.gpa, "U", .no_embedded_nulls),
        .id = .{ .reified = .{ .source_zir_id = 0, .decl_inst = @fromBackingInt(@intCast(0)), .type_hash = hash } },
        .layout = .auto,
        .tag_usage = .tagged,
        .enum_tag_type = tag_enum.index,
        .backing_int = .none,
        .names = handles,
        .types = types,
        .aligns = &.{},
    });
    const f = pool.unionFields(union_ty);
    f.field_name_map.get(pool).clearRetainingCapacity();
    for (handles) |name| assert(pool.addFieldName(handles, f.field_name_map, name) == null);
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

    try expectOpv(s, .fromIndex(.u0_type), true);
    try expectOpv(s, .fromIndex(.u8_type), false);
    try expectOpv(s, .fromIndex(.void_type), true);
    try expectOpv(s, .fromIndex(.bool_type), false);
    try expectOpv(s, .fromIndex(.type_type), false);
    try expectOpv(s, .fromIndex(.comptime_int_type), false);
    try expectOpv(s, .fromIndex(try pool.internArrayType(.{ .len = 3, .child = .u0_type })), true);
    try expectOpv(s, .fromIndex(try pool.internArrayType(.{ .len = 3, .child = .u8_type })), false);
    try expectOpv(s, .fromIndex(try pool.internArrayType(.{ .len = 0, .child = .u8_type })), true);
    try expectOpv(s, .fromIndex(try pool.internVectorType(.{ .len = 3, .child = .u0_type })), true);
    try expectOpv(s, .fromIndex(try pool.internVectorType(.{ .len = 3, .child = .u8_type })), false);
    try expectOpv(s, .fromIndex(try pool.internOptionalType(.noreturn_type)), true);
    try expectOpv(s, .fromIndex(try pool.internOptionalType(.u8_type)), false);
    try expectOpv(s, .fromIndex(try pool.internTupleType(&.{ .u0_type, .void_type }, &.{ .none, .none })), true);
    try expectOpv(s, .fromIndex(try pool.internTupleType(&.{.u8_type}, &.{.none})), false);
    try expectOpv(s, try opvEnum(s, 0x1001, &.{"only"}), true);
    try expectOpv(s, try opvEnum(s, 0x1002, &.{ "a", "b" }), false);
    try expectOpv(s, try opvStruct(s, 0x2001, &.{ "x", "y" }, &.{ .u0_type, .void_type }), true);
    try expectOpv(s, try opvStruct(s, 0x2002, &.{"x"}, &.{.u8_type}), false);
    try expectOpv(s, try opvUnion(s, 0x3001, 0x4001, &.{"x"}, &.{.u0_type}), true);
    try expectOpv(s, try opvUnion(s, 0x3002, 0x4002, &.{"x"}, &.{.u8_type}), false);
    try expectOpv(s, try opvUnion(s, 0x3003, 0x4003, &.{ "a", "b" }, &.{ .u0_type, .u0_type }), false);
}
