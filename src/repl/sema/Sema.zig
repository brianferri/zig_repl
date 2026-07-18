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
namespace: ?InternPool.NamespaceIndex,
comptime_break_inst: Zir.Inst.Index = undefined,
branch_quota: u32 = default_branch_quota,
branch_count: u32 = 0,
return_value: Value = undefined,
fn_ret_ty: InternPool.Index = .none,
operand_comptime: bool = true,
session: ?*Session = null,
current_zir_id: u32 = 0,
block: *Block = undefined,
type_name_ctx: InternPool.NullTerminatedString = .empty,
this_type: InternPool.Index = .none,

pub const default_branch_quota: u32 = 1000;

pub const LazySrcLoc = @import("ErrorMsg.zig").LazySrcLoc;
pub const ErrorMsg = @import("ErrorMsg.zig").ErrorMsg;

pub const Block = struct {
    params: std.ArrayListUnmanaged(Param) = .empty,
    src_base_inst: Zir.Inst.Index = undefined,

    pub fn deinit(self: *Block, gpa: std.mem.Allocator) void {
        self.params.deinit(gpa);
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

pub const ComptimeAlloc = struct {
    val: Value,
    is_const: bool,
    address: ?u64 = null,
};

pub fn analyze(session: *Session, file_index: Session.Index, writer: *std.Io.Writer) Error!?Value {
    const gpa = session.gpa;
    const intern_pool = session.intern_pool;
    const namespace = session.root_namespace;
    const zir = session.files.items[file_index].zir.?;
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
        .inst_map = .empty,
        .comptime_allocs = .empty,
        .namespace = namespace,
        .block = &top_block,
        .session = session,
        .current_zir_id = file_index,
    };
    defer sema.inst_map.deinit(gpa);
    defer sema.comptime_allocs.deinit(gpa);
    defer sema.synthetic_addresses.deinit(gpa);

    sema.type_name_ctx = try intern_pool.namespaceName(gpa, namespace);

    if (findReplInputBody(zir)) |bound| {
        top_block.src_base_inst = bound.decl_inst;
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
            .ret_node => {
                const operand = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node.operand;
                sema.return_value = try sema.resolveInst(operand);
                return error.ComptimeReturn;
            },
            .ret_implicit => {
                const operand = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_tok.operand;
                sema.return_value = try sema.resolveInst(operand);
                return error.ComptimeReturn;
            },
            .ret_load => {
                const operand = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node.operand;
                const ptr = try sema.resolveInst(operand);
                sema.return_value = try sema.loadValue(ptr);
                return error.ComptimeReturn;
            },
            .@"defer" => {
                const defer_data = sema.zir.instructions.items(.data)[@intFromEnum(inst)].@"defer";
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

fn resolveInlineBody(
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
    const break_data = datas[@intFromEnum(sema.comptime_break_inst)].@"break";
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
        .elem_ptr, .elem_ptr_node => sema.evalElemPtrNode(inst),
        .elem_val => sema.evalElemVal(inst),
        .memcpy => sema.evalMemcpy(inst),
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

fn evalStr(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const bytes = sema.zir.instructions.items(.data)[@intFromEnum(inst)].str.get(sema.zir);
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
    return try sema.resolveInst(operand);
}

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

fn splat(sema: *Sema, ty: Type, val: Value) Error!Value {
    if (ty.zigTypeTag(sema.intern_pool) != .vector) return val;
    return sema.aggregateSplatValue(ty, val);
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

fn srcNodeOffset(sema: *Sema, inst: Zir.Inst.Index) std.zig.Ast.Node.Offset {
    const tag = sema.zir.instructions.items(.tag)[@intFromEnum(inst)];
    const data = sema.zir.instructions.items(.data)[@intFromEnum(inst)];
    return switch (Zir.Inst.Tag.data_tags[@intFromEnum(tag)]) {
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

    const op_name: []const u8 = @tagName(tag);
    const lhs_val = try sema.resolveInst(bin.lhs);
    const rhs_val = try sema.resolveInst(bin.rhs);

    const resolved_type = try sema.resolveArithPeerType(lhs_val, rhs_val, op_name);
    const lhs = try sema.coerceValueToType(lhs_val, resolved_type.index, op_name);
    const rhs = try sema.coerceValueToType(rhs_val, resolved_type.index, op_name);

    const pool = sema.intern_pool;
    const scalar_tag = resolved_type.scalarType(pool).zigTypeTag(pool);
    try sema.checkArithmeticOp(scalar_tag, Value.typeOf(lhs_val, pool).zigTypeTag(pool), Value.typeOf(rhs_val, pool).zigTypeTag(pool), tag);

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

fn evalModRem(sema: *Sema, resolved_type: Type, lhs_orig: Value, rhs_orig: Value, lhs: Value, rhs: Value) Error!Value {
    const ip = sema.intern_pool;
    const lhs_ty = Value.typeOf(lhs_orig, ip);
    const rhs_ty = Value.typeOf(rhs_orig, ip);
    const lhs_maybe_negative = !isUnsignedIntType(lhs_ty.scalarType(ip), ip) and !lhs.compareAllWithZero(.gte, ip);
    const rhs_maybe_negative = !isUnsignedIntType(rhs_ty.scalarType(ip), ip) and !rhs.compareAllWithZero(.gte, ip);
    const result = try arith.modRem(sema, resolved_type, lhs, rhs, .rem);
    if (lhs_maybe_negative or rhs_maybe_negative) {
        if (!result.compareAllWithZero(.eq, ip)) {
            return sema.fail(sema.block, sema.block.nodeOffset(.zero), "remainder division with '{f}' and '{f}': signed integers and floats must use @rem or @mod", .{ lhs_ty.fmt(ip), rhs_ty.fmt(ip) });
        }
    }
    return result;
}

fn isUnsignedIntType(ty: Type, pool: *const InternPool) bool {
    return ty.zigTypeTag(pool) == .int and ty.intInfo(pool).signedness == .unsigned;
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
        const s0_is_a = @intFromEnum(a) <= @intFromEnum(b);
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
                    else => |result| return result,
                };

                var comptime_val: ?Value = null;
                for (peer_tys) |opt_ty| {
                    const struct_ty = opt_ty orelse continue;
                    const uncoerced_field_val = (try struct_ty.structFieldValueComptime(sema, field_index)) orelse {
                        comptime_val = null;
                        break;
                    };
                    const coerced_val = sema.coerceExtra(uncoerced_field_val, field_ty.*, "peer", false) catch |err| switch (err) {
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

fn resolveArithPeerType(sema: *Sema, lhs: Value, rhs: Value, op_name: []const u8) Error!Type {
    _ = op_name;
    const ip = sema.intern_pool;
    try sema.checkVectorizableBinaryOperands(Value.typeOf(lhs, ip), Value.typeOf(rhs, ip));
    return sema.resolvePeerTypes(&.{ lhs, rhs });
}

fn failNumericOperands(sema: *Sema, op_name: []const u8, lhs_key: InternPool.Key, rhs_key: InternPool.Key) Error {
    const src = sema.block.nodeOffset(.zero);
    if ((lhs_key == .int or lhs_key == .float) and (rhs_key == .int or rhs_key == .float)) {
        return sema.fail(sema.block, src, "{s}: incompatible numeric operands", .{op_name});
    }
    return sema.fail(sema.block, src, "{s}: non-numeric or mismatched operands", .{op_name});
}

const VectorPair = struct { len: usize, lhs: InternPool.Key.Aggregate, rhs: InternPool.Key.Aggregate };
fn vectorBinaryOperands(sema: *Sema, lhs: Value, rhs: Value, op_name: []const u8) Error!VectorPair {
    const ip = sema.intern_pool;
    const lhs_vt = ip.indexToKey(Value.typeOf(lhs, ip).index).vector_type;
    const rhs_ty_key = ip.indexToKey(Value.typeOf(rhs, ip).index);
    if (rhs_ty_key != .vector_type) {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "{s}: mixed scalar and vector operands", .{op_name});
    }
    if (rhs_ty_key.vector_type.len != lhs_vt.len) {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "{s}: vector length mismatch", .{op_name});
    }
    return .{ .len = @intCast(lhs_vt.len), .lhs = ip.indexToKey(lhs.index).aggregate, .rhs = ip.indexToKey(rhs.index).aggregate };
}

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

fn refitIntToFixedWidth(
    sema: *Sema,
    comptime_int_idx: InternPool.Index,
    dest_ty: InternPool.Index,
    op_name: []const u8,
) Error!Value {
    const dest_info = intTypeInfo(sema.intern_pool, dest_ty) orelse {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "{s}: destination is not a supported int type", .{op_name});
    };
    var space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
    const result_big = sema.intern_pool.indexToKey(comptime_int_idx).int.storage.toBigInt(&space);
    if (!result_big.fitsInTwosComp(dest_info.signedness, dest_info.bits)) {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "{s}: value does not fit in {c}{d}", .{
            op_name,
            @as(u8, switch (dest_info.signedness) {
                .signed => 'i',
                .unsigned => 'u',
            }),
            dest_info.bits,
        });
    }
    const idx = try sema.intern_pool.internIntValue(dest_ty, result_big);
    return .{ .index = idx };
}

fn intCoercible(src: std.lang.Type.Int, dst: std.lang.Type.Int) bool {
    return switch (dst.signedness) {
        .unsigned => src.signedness == .unsigned and dst.bits >= src.bits,
        .signed => switch (src.signedness) {
            .signed => dst.bits >= src.bits,
            .unsigned => dst.bits > src.bits,
        },
    };
}

fn evalBlock(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.Block, pl_node.payload_index);
    const body = sema.zir.bodySlice(extra.end, extra.data.body_len);
    return try sema.resolveInlineBody(body, inst);
}

fn evalCondbr(sema: *Sema, inst: Zir.Inst.Index) Error!Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.CondBr, pl_node.payload_index);
    const condbr = extra.data;
    assert(condbr.condition != .none);

    const cond_value = try sema.resolveInst(condbr.condition);
    const cond_is_true = switch (cond_value.index) {
        .bool_true => true,
        .bool_false => false,
        else => {
            return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "condbr: condition is not a bool", .{});
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

fn evalBoolNot(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    assert(un_node.operand != .none);

    const operand = try sema.resolveInst(un_node.operand);
    return switch (operand.index) {
        .bool_true => .{ .index = .bool_false },
        .bool_false => .{ .index = .bool_true },
        else => {
            return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "bool_not: operand is not a bool", .{});
        },
    };
}

fn evalBoolBr(sema: *Sema, inst: Zir.Inst.Index, tag: Zir.Inst.Tag) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);
    assert(tag == .bool_br_and or tag == .bool_br_or);

    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.BoolBr, pl_node.payload_index);
    const bool_br = extra.data;
    assert(bool_br.lhs != .none);

    const lhs_value = try sema.resolveInst(bool_br.lhs);
    const lhs_is_true = switch (lhs_value.index) {
        .bool_true => true,
        .bool_false => false,
        else => {
            return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "bool_br: lhs is not a bool", .{});
        },
    };

    const short_circuited = switch (tag) {
        .bool_br_and => !lhs_is_true,
        .bool_br_or => lhs_is_true,
        else => unreachable,
    };
    if (short_circuited) return lhs_value;

    const body = sema.zir.bodySlice(extra.end, bool_br.body_len);
    return try sema.resolveInlineBody(body, inst);
}

fn evalTypeofLog2IntType(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    assert(un_node.operand != .none);

    const ip = sema.intern_pool;
    const operand = try sema.resolveInst(un_node.operand);
    const operand_type = Value.typeOf(operand, ip).index;

    if (ip.indexToKey(operand_type) == .vector_type) {
        const vt = ip.indexToKey(operand_type).vector_type;
        const elem_log2 = (try sema.log2IntType(vt.child)) orelse
            return sema.failLog2NonInt();
        return .{ .index = try ip.internVectorType(.{ .len = vt.len, .child = elem_log2 }) };
    }

    return .{ .index = (try sema.log2IntType(operand_type)) orelse return sema.failLog2NonInt() };
}

fn failLog2NonInt(sema: *Sema) Error {
    return sema.fail(sema.block, sema.block.nodeOffset(.zero), "typeof_log2_int_type: non-integer operand not yet supported", .{});
}

fn log2IntType(sema: *Sema, int_ty: InternPool.Index) Error!?InternPool.Index {
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
            const log2_elem = (try sema.log2IntType(operand.childType(ip).toIndex())) orelse return null;
            return try ip.internVectorType(.{ .len = operand.vectorLen(ip), .child = log2_elem });
        },
        else => return null,
    }
}

fn evalAsNode(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    const as = sema.zir.extraData(Zir.Inst.As, pl_node.payload_index).data;
    assert(as.dest_type != .none);
    assert(as.operand != .none);

    const dest_type_index = try sema.resolveDestType(as.dest_type, "as");

    const operand_value = try sema.resolveInst(as.operand);
    return try sema.coerceValueToType(operand_value, dest_type_index, "@as");
}

fn resolveDestType(
    sema: *Sema,
    ref: Zir.Inst.Ref,
    op_name: []const u8,
) Error!InternPool.Index {
    assert(ref != .none);
    const dest_value = try sema.resolveInst(ref);
    const key = sema.intern_pool.indexToKey(dest_value.index);
    if (key.isType()) return dest_value.index;
    return sema.fail(sema.block, sema.block.nodeOffset(.zero), "{s}: destination is not a type", .{op_name});
}

fn binData(sema: *Sema, inst: Zir.Inst.Index) Zir.Inst.Bin {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);
    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    return sema.zir.extraData(Zir.Inst.Bin, pl_node.payload_index).data;
}

fn evalFloatCast(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const bin = sema.binData(inst);
    assert(bin.lhs != .none);
    assert(bin.rhs != .none);

    const dest_type_index = try sema.resolveDestType(bin.lhs, "@floatCast");
    if (!isFloatTypeIndex(dest_type_index)) {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "@floatCast: destination is not a float type", .{});
    }

    const operand_value = try sema.resolveInst(bin.rhs);
    const operand_key = sema.intern_pool.indexToKey(operand_value.index);
    if (operand_key != .float) {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "@floatCast: operand is not a float", .{});
    }
    const coerced = coerceNumericToFloat(operand_key, dest_type_index);
    const idx = try sema.intern_pool.internFloat(coerced);
    return .{ .index = idx };
}

fn evalIntFromFloat(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const bin = sema.binData(inst);
    assert(bin.lhs != .none);
    assert(bin.rhs != .none);

    const dest_type_index = try sema.resolveDestType(bin.lhs, "@intFromFloat");

    const operand_value = try sema.resolveInst(bin.rhs);
    const operand_key = sema.intern_pool.indexToKey(operand_value.index);
    if (operand_key != .float) {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "@intFromFloat: operand is not a float", .{});
    }
    const operand_f128: f128 = floatToF128(operand_key.float);
    if (std.math.isNan(operand_f128)) {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "@intFromFloat: operand is NaN", .{});
    }
    if (!std.math.isFinite(operand_f128)) {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "@intFromFloat: operand is infinite", .{});
    }

    return try sema.materialiseIntFromFloat(operand_f128, dest_type_index);
}

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
    if (Type.fromIndex(dest_type_index).zigTypeTag(sema.intern_pool) == .int) {
        const dest_int = Type.fromIndex(dest_type_index).intInfo(sema.intern_pool);
        if (!big.fitsInTwosComp(dest_int.signedness, dest_int.bits)) {
            return sema.fail(sema.block, sema.block.nodeOffset(.zero), "@intFromFloat: value does not fit in {c}{d}", .{
                @as(u8, switch (dest_int.signedness) {
                    .signed => 'i',
                    .unsigned => 'u',
                }),
                dest_int.bits,
            });
        }
        const idx = try sema.intern_pool.internIntValue(dest_type_index, big);
        return .{ .index = idx };
    }

    return sema.fail(sema.block, sema.block.nodeOffset(.zero), "@intFromFloat: destination is not an int type", .{});
}

fn evalFloatFromInt(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const bin = sema.binData(inst);
    assert(bin.lhs != .none);
    assert(bin.rhs != .none);

    const dest_type_index = try sema.resolveDestType(bin.lhs, "@floatFromInt");
    if (!isFloatTypeIndex(dest_type_index)) {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "@floatFromInt: destination is not a float type", .{});
    }

    const operand_value = try sema.resolveInst(bin.rhs);
    const operand_key = sema.intern_pool.indexToKey(operand_value.index);
    if (operand_key != .int) {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "@floatFromInt: operand is not an int", .{});
    }
    const coerced = coerceNumericToFloat(operand_key, dest_type_index);
    const idx = try sema.intern_pool.internFloat(coerced);
    return .{ .index = idx };
}

fn evalIntCast(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const bin = sema.binData(inst);

    const dest_type_index = try sema.resolveDestType(bin.lhs, "@intCast");
    const operand_value = try sema.resolveInst(bin.rhs);
    const operand_key = sema.intern_pool.indexToKey(operand_value.index);
    if (operand_key != .int) {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "@intCast: operand is not an int", .{});
    }
    if (dest_type_index == .comptime_int_type) return operand_value;
    return try sema.refitIntToFixedWidth(operand_value.index, dest_type_index, "@intCast");
}

fn evalTruncate(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const bin = sema.binData(inst);

    const dest_type_index = try sema.resolveDestType(bin.lhs, "@truncate");
    const dest_info = intTypeInfo(sema.intern_pool, dest_type_index) orelse {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "@truncate: destination is not a fixed-width int", .{});
    };

    const operand_value = try sema.resolveInst(bin.rhs);
    const operand_key = sema.intern_pool.indexToKey(operand_value.index);
    if (operand_key != .int) {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "@truncate: operand is not an int", .{});
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

fn evalBitCast(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    const bin = sema.binData(inst);
    const src = sema.block.nodeOffset(sema.srcNodeOffset(inst));

    const dest_ty: Type = .fromIndex(try sema.resolveDestType(bin.lhs, "@bitCast"));
    const operand = try sema.resolveInst(bin.rhs);
    const operand_ty = Value.typeOf(operand, ip);

    switch (dest_ty.scalarType(ip).zigTypeTag(ip)) {
        .pointer, .optional => return sema.fail(sema.block, src, "cannot @bitCast to '{f}'", .{dest_ty.fmt(ip)}),
        else => {},
    }
    if (!dest_ty.hasBitRepresentation(ip))
        return sema.fail(sema.block, src, "cannot @bitCast to '{f}'", .{dest_ty.fmt(ip)});
    switch (operand_ty.scalarType(ip).zigTypeTag(ip)) {
        .pointer, .optional => return sema.fail(sema.block, src, "cannot @bitCast from '{f}'", .{operand_ty.fmt(ip)}),
        else => {},
    }
    if (!operand_ty.hasBitRepresentation(ip))
        return sema.fail(sema.block, src, "cannot @bitCast from '{f}'", .{operand_ty.fmt(ip)});

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

fn isFixedWidthFloatType(ty: InternPool.Index) bool {
    return switch (ty) {
        .f16_type, .f32_type, .f64_type, .f80_type, .f128_type => true,
        else => false,
    };
}

fn isFloatTypeIndex(ty: InternPool.Index) bool {
    return ty == .comptime_float_type or ty == .c_longdouble_type or isFixedWidthFloatType(ty);
}

fn floatToF128(source: InternPool.Key.Float) f128 {
    return switch (source.storage) {
        inline else => |v| @as(f128, @floatCast(v)),
    };
}

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
        .add, .add_unsafe, .sub, .mul, .div, .div_exact, .div_trunc, .div_floor, .mod, .rem, .mod_rem => true,
        else => false,
    };
}

fn evalBitwise(sema: *Sema, inst: Zir.Inst.Index, tag: Zir.Inst.Tag) Error!?Value {
    const bin = sema.binData(inst);
    assert(bin.lhs != .none);
    assert(bin.rhs != .none);

    const op_name: []const u8 = @tagName(tag);
    const lhs_value = try sema.resolveInst(bin.lhs);
    const rhs_value = try sema.resolveInst(bin.rhs);

    const resolved_type = try sema.resolveArithPeerType(lhs_value, rhs_value, op_name);
    const lhs = try sema.coerceValueToType(lhs_value, resolved_type.index, op_name);
    const rhs = try sema.coerceValueToType(rhs_value, resolved_type.index, op_name);

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
    var lhs_value = try sema.resolveInst(bin.lhs);
    var rhs_value = try sema.resolveInst(bin.rhs);
    var lhs_key = ip.indexToKey(lhs_value.index);
    var rhs_key = ip.indexToKey(rhs_value.index);

    if (lhs_key == .un and (rhs_key == .enum_literal or rhs_key == .enum_tag)) {
        const tag_name = switch (rhs_key) {
            .enum_literal => |n| n,
            .enum_tag => |et| (try sema.enumFieldName(et.ty, (try sema.enumTagFieldIndex(et.ty, rhs_value)).?)).?,
            else => unreachable,
        };
        if (try sema.cmpUnionTagNoValue(Value.typeOf(lhs_value, ip).index, tag_name, op)) |v| return v;
        lhs_value = .{ .index = lhs_key.un.tag };
        lhs_key = ip.indexToKey(lhs_value.index);
    } else if (rhs_key == .un and (lhs_key == .enum_literal or lhs_key == .enum_tag)) {
        const tag_name = switch (lhs_key) {
            .enum_literal => |n| n,
            .enum_tag => |et| (try sema.enumFieldName(et.ty, (try sema.enumTagFieldIndex(et.ty, lhs_value)).?)).?,
            else => unreachable,
        };
        if (try sema.cmpUnionTagNoValue(Value.typeOf(rhs_value, ip).index, tag_name, op)) |v| return v;
        rhs_value = .{ .index = rhs_key.un.tag };
        rhs_key = ip.indexToKey(rhs_value.index);
    }

    {
        const lhs_ty = Value.typeOf(lhs_value, ip).index;
        const rhs_ty = Value.typeOf(rhs_value, ip).index;
        const lhs_null_lit = lhs_ty == .null_type;
        const rhs_null_lit = rhs_ty == .null_type;
        const lhs_is_opt = ip.indexToKey(lhs_ty) == .opt_type;
        const rhs_is_opt = ip.indexToKey(rhs_ty) == .opt_type;
        if (lhs_null_lit or rhs_null_lit or lhs_is_opt or rhs_is_opt) {
            if (op != .eq and op != .neq) {
                return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "operator {s} not allowed for optional type", .{op_name});
            }
            if (lhs_null_lit and rhs_null_lit) return boolValue(op == .eq);
            if (lhs_null_lit or rhs_null_lit) {
                const other_ty = if (lhs_null_lit) rhs_ty else lhs_ty;
                const other_val = if (lhs_null_lit) rhs_value else lhs_value;
                const other_key = ip.indexToKey(other_ty);
                const nullable = other_key == .opt_type or
                    (other_key == .ptr_type and other_key.ptr_type.flags.size == .c);
                if (!nullable) {
                    return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "comparison of '{f}' with null", .{Type.fromIndex(other_ty).fmt(ip)});
                }
                const ov_key = ip.indexToKey(other_val.index);
                const is_null = ov_key == .opt and ov_key.opt.val == .none;
                return boolValue(if (op == .eq) is_null else !is_null);
            }
            const opt_ty = if (lhs_is_opt) lhs_ty else rhs_ty;
            const l = if (lhs_is_opt) lhs_value else try sema.coerceToOptional(lhs_value, opt_ty, op_name);
            const r = if (rhs_is_opt) rhs_value else try sema.coerceToOptional(rhs_value, opt_ty, op_name);
            return boolValue((l.index == r.index) == (op == .eq));
        }
    }

    {
        const lhs_ty_tag = Value.typeOf(lhs_value, ip).zigTypeTag(ip);
        const rhs_ty_tag = Value.typeOf(rhs_value, ip).zigTypeTag(ip);

        // error_union == error_set (either order), equality only: a payload is never an error, so the
        // result is bool_false regardless of the operator; otherwise unwrap the error code and let the
        // error_set fold below compare it. Compiler analyzeCmp is_equality_cmp arms (errorUnionIsPayload
        // -> analyzeErrUnionCode -> cmpSelf).
        if (op == .eq or op == .neq) {
            if (lhs_ty_tag == .error_union and rhs_ty_tag == .error_set) {
                if (lhs_value.errorUnionIsPayload(ip)) return boolValue(false);
                lhs_value = try sema.analyzeErrUnionCode(lhs_value);
                lhs_key = ip.indexToKey(lhs_value.index);
            } else if (lhs_ty_tag == .error_set and rhs_ty_tag == .error_union) {
                if (rhs_value.errorUnionIsPayload(ip)) return boolValue(false);
                rhs_value = try sema.analyzeErrUnionCode(rhs_value);
                rhs_key = ip.indexToKey(rhs_value.index);
            }
        }

        // error_set == error_set: fold on the interned error names (compiler zirCmpEq error_set arm).
        if (Value.typeOf(lhs_value, ip).zigTypeTag(ip) == .error_set and Value.typeOf(rhs_value, ip).zigTypeTag(ip) == .error_set) {
            if (op != .eq and op != .neq) {
                return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "{s}: operator not allowed for error set operands", .{op_name});
            }
            if (lhs_value.isUndef(ip) or rhs_value.isUndef(ip)) return .{ .index = try ip.get(.{ .undef = .bool_type }) };
            return boolValue((lhs_key.err.name == rhs_key.err.name) == (op == .eq));
        }
    }

    if (lhs_key == .enum_literal and rhs_key == .enum_tag) {
        lhs_value = try sema.coerceValueToType(lhs_value, rhs_key.enum_tag.ty, op_name);
        lhs_key = ip.indexToKey(lhs_value.index);
    } else if (rhs_key == .enum_literal and lhs_key == .enum_tag) {
        rhs_value = try sema.coerceValueToType(rhs_value, lhs_key.enum_tag.ty, op_name);
        rhs_key = ip.indexToKey(rhs_value.index);
    }

    if (ip.indexToKey(Value.typeOf(lhs_value, ip).index) == .vector_type)
        return try sema.evalVectorComparison(op, lhs_value, rhs_value, op_name);

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
                return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "{s}: enum operands have different types", .{op_name});
            }
            const equal = lhs_value.index == rhs_value.index;
            return switch (op) {
                .eq => .{ .index = if (equal) .bool_true else .bool_false },
                .neq => .{ .index = if (equal) .bool_false else .bool_true },
                else => {
                    return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "{s}: operator not allowed for {s} operands", .{ op_name, kind_name });
                },
            };
        }
    }

    return sema.scalarCompare(op, lhs_value, rhs_value, op_name);
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

fn scalarCompare(sema: *Sema, op: std.math.CompareOperator, lhs: Value, rhs: Value, op_name: []const u8) Error!?Value {
    const ip = sema.intern_pool;
    const lhs_key = ip.indexToKey(lhs.index);
    const rhs_key = ip.indexToKey(rhs.index);
    if ((lhs_key == .int or lhs_key == .float) and (rhs_key == .int or rhs_key == .float)) {
        return boolValue(Value.compareHetero(lhs, op, rhs, ip));
    }
    return sema.failNumericOperands(op_name, lhs_key, rhs_key);
}

fn evalVectorComparison(sema: *Sema, op: std.math.CompareOperator, lhs: Value, rhs: Value, op_name: []const u8) Error!?Value {
    const ip = sema.intern_pool;
    const vp = try sema.vectorBinaryOperands(lhs, rhs, op_name);
    const elems = try sema.gpa.alloc(InternPool.Index, vp.len);
    defer sema.gpa.free(elems);
    for (elems, 0..) |*e, i| {
        const l: Value = .{ .index = try ip.aggregateElementAt(vp.lhs, i) };
        const r: Value = .{ .index = try ip.aggregateElementAt(vp.rhs, i) };
        e.* = (try sema.scalarCompare(op, l, r, op_name) orelse return null).index;
    }
    const vec_ty = try ip.internVectorType(.{ .len = @intCast(vp.len), .child = .bool_type });
    return .{ .index = try ip.internAggregate(.{ .ty = vec_ty, .storage = .{ .elems = elems } }) };
}

fn evalUnaryMath(
    sema: *Sema,
    inst: Zir.Inst.Index,
    comptime eval: fn (Value, Type, std.mem.Allocator, *InternPool) std.mem.Allocator.Error!Value,
) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);
    const ip = sema.intern_pool;
    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    const operand = try sema.resolveInst(un_node.operand);
    const operand_ty = operand.typeOf(ip);
    switch (operand_ty.scalarType(ip).zigTypeTag(ip)) {
        .comptime_float, .float => {},
        else => {
            return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "expected vector of floats or float type, found '{f}'", .{operand_ty.fmt(ip)});
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
            (try sema.coerceValueToType(ev, result_scalar_ty.index, @tagName(op))).index;
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
            else => return sema.failReduceOperand(operation, operand_ty, "integer or boolean"),
        },
        .Min, .Max, .Add, .Mul => switch (scalar_ty.zigTypeTag(ip)) {
            .int, .float => {},
            else => return sema.failReduceOperand(operation, operand_ty, "integer or float"),
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

fn failReduceOperand(sema: *Sema, operation: std.lang.ReduceOp, operand_ty: Type, want: []const u8) Error {
    return sema.fail(sema.block, sema.block.nodeOffset(.zero), "@reduce operation '{s}' requires {s} operand; found '{f}'", .{ @tagName(operation), want, operand_ty.fmt(sema.intern_pool) });
}

fn evalMulAdd(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    const extra = sema.zir.extraData(Zir.Inst.MulAdd, sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node.payload_index).data;
    const addend = try sema.resolveInst(extra.addend);
    const ty = addend.typeOf(ip);
    const mulend1 = try sema.coerceValueToType(try sema.resolveInst(extra.mulend1), ty.toIndex(), "@mulAdd");
    const mulend2 = try sema.coerceValueToType(try sema.resolveInst(extra.mulend2), ty.toIndex(), "@mulAdd");

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
    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    const operand = try sema.resolveInst(un_node.operand);
    const operand_ty = operand.typeOf(ip);
    const scalar_ty = operand_ty.scalarType(ip);

    const result_ty: Type = switch (scalar_ty.zigTypeTag(ip)) {
        .comptime_float, .float, .comptime_int => operand_ty,
        .int => if (scalar_ty.intInfo(ip).signedness == .signed) try operand_ty.toUnsigned(ip) else return operand,
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

fn evalNegate(sema: *Sema, inst: Zir.Inst.Index, tag: Zir.Inst.Tag) Error!?Value {
    assert(tag == .negate or tag == .negate_wrap);
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    assert(un_node.operand != .none);

    const ip = sema.intern_pool;
    const operand = try sema.resolveInst(un_node.operand);
    const ty = Value.typeOf(operand, ip);
    const scalar_ty = ty.scalarType(ip);
    const scalar_tag = scalar_ty.zigTypeTag(ip);

    const numeric = switch (scalar_tag) {
        .int, .comptime_int, .float, .comptime_float => true,
        else => false,
    };
    if (!numeric or (tag == .negate and isUnsignedIntType(scalar_ty, ip))) {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "negation of type '{f}'", .{ty.fmt(ip)});
    }

    if (scalar_tag == .float or scalar_tag == .comptime_float) {
        return try arith.negateFloat(sema, ty, operand);
    }

    const zero_scalar = try sema.intValue_u64(scalar_ty, 0);
    const zero = try sema.splat(ty, zero_scalar);
    return switch (tag) {
        .negate => try arith.sub(sema, ty, zero, operand),
        .negate_wrap => try arith.subWrap(sema, ty, zero, operand),
        else => unreachable,
    };
}

fn evalPtrType(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const inst_data = sema.zir.instructions.items(.data)[@intFromEnum(inst)].ptr_type;
    if (inst_data.flags.has_addrspace or inst_data.flags.has_bit_range) {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "ptr_type: address_space / bit_range not yet supported", .{});
    }

    const extra = sema.zir.extraData(Zir.Inst.PtrType, inst_data.payload_index);
    const payload = extra.data;
    assert(payload.elem_type != .none);

    const child_ty = try sema.resolveDestType(payload.elem_type, "ptr_type");
    assert(child_ty != .none);

    var extra_i = extra.end;
    const sentinel: InternPool.Index = if (inst_data.flags.has_sentinel) blk: {
        const ref: Zir.Inst.Ref = @enumFromInt(sema.zir.extra[extra_i]);
        extra_i += 1;
        break :blk (try sema.coerceValueToType(try sema.resolveInst(ref), child_ty, "pointer sentinel")).index;
    } else .none;
    const alignment: InternPool.Alignment = if (inst_data.flags.has_align) blk: {
        const ref: Zir.Inst.Ref = @enumFromInt(sema.zir.extra[extra_i]);
        extra_i += 1;
        break :blk try sema.alignmentFromValue(try sema.resolveInst(ref), "ptr_type");
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

fn alignmentFromValue(sema: *Sema, value: Value, op_name: []const u8) Error!InternPool.Alignment {
    const bytes = try sema.resolveUsizeInt(value, op_name);
    if (bytes == 0 or !std.math.isPowerOfTwo(bytes)) {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "{s}: alignment '{d}' is not a power of two", .{ op_name, bytes });
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
        return ctx.aligns[@intFromEnum(a)].compare(.gt, ctx.aligns[@intFromEnum(b)]);
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
                const cf = try sema.enterContainer(struct_ty, "packed struct backing integer");
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
        order.* = @enumFromInt(idx);
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
        var max_bits: u16 = 0;
        for (uf.field_types) |field_ty| max_bits = @max(max_bits, @as(u16, @intCast(Type.fromIndex(field_ty).bitSize(ip))));
        const backing = try ip.internIntType(.unsigned, max_bits);
        ip.setUnionPackedBackingInt(union_ty, backing);
        const backing_ty: Type = .fromIndex(backing);
        ip.setUnionLayout(union_ty, @intCast(backing_ty.abiSize(ip)), backing_ty.abiAlignment(ip), backing_ty.classify(ip), false);
        return;
    }

    const tag_usage = ip.unionFields(union_ty).tag_usage;
    const enum_tag_ty: InternPool.Index = if (tag_usage != .none) try sema.unionTagEnumType(union_ty) else .none;
    if (tag_usage != .none) try sema.ensureLayoutResolved(enum_tag_ty);

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
        .simple_value, .enum_literal, .int, .float, .undef, .ptr, .slice, .err, .error_union, .func, .opt, .aggregate, .enum_tag, .un, .bitpack => unreachable,
    }
}

fn evalAlignOf(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    const ty = try sema.resolveDestType(un_node.operand, "@alignOf");
    if (ty == .noreturn_type) {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "@alignOf: no align available for uninstantiable type 'noreturn'", .{});
    }
    try sema.ensureLayoutResolved(ty);
    const alignment = Type.fromIndex(ty).abiAlignment(sema.intern_pool);
    const idx = try sema.intern_pool.internInt(.{
        .ty = .comptime_int_type,
        .storage = .{ .u64 = alignment.toByteUnits().? },
    });
    return .{ .index = idx };
}

fn evalSizeOf(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    const ty = try sema.resolveDestType(un_node.operand, "@sizeOf");
    try sema.ensureLayoutResolved(ty);
    const key = sema.intern_pool.indexToKey(ty);
    if (key == .opaque_type) {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "@sizeOf: no size available for opaque type", .{});
    }
    if (key == .simple_type) switch (key.simple_type) {
        .noreturn => {
            return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "@sizeOf: no size available for uninstantiable type 'noreturn'", .{});
        },
        .comptime_int, .comptime_float, .type, .null, .undefined, .enum_literal, .anyopaque => {
            return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "@sizeOf: no size available for type '{s}'", .{@tagName(key.simple_type)});
        },
        else => {},
    };
    const size = Type.fromIndex(ty).abiSize(sema.intern_pool);
    const idx = try sema.intern_pool.internInt(.{
        .ty = .comptime_int_type,
        .storage = .{ .u64 = size },
    });
    return .{ .index = idx };
}

fn evalOffsetOf(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);
    const ip = sema.intern_pool;
    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.Bin, pl_node.payload_index).data;
    const ty = try sema.resolveDestType(extra.lhs, "@offsetOf");
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

fn evalBitSizeOf(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);
    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    const ty = try sema.resolveDestType(un_node.operand, "@bitSizeOf");
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
    assert(@intFromEnum(inst) < sema.zir.instructions.len);
    const ip = sema.intern_pool;
    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
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
    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
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
    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
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
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
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
            const slot = &sema.comptime_allocs.items[@intFromEnum(i)];
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
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    assert(un_node.operand != .none);

    const child_ty = try sema.resolveDestType(un_node.operand, "alloc");
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
        .comptime_alloc => |idx| sema.comptime_allocs.items[@intFromEnum(idx)].is_const = true,
        .field, .arr_elem => |f| sema.freezeBacking(ip.indexToKey(f.base).ptr),
        .opt_payload, .eu_payload => |base| sema.freezeBacking(ip.indexToKey(base).ptr),
        .nav, .uav, .comptime_field, .int => {},
    }
}

fn evalMakePtrConst(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
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
        if (!alloc.val.canMutateComptimeVarState(ip))
            return .{ .index = try sema.uavPtr(const_ty, alloc.val.index) };
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
        const default = ty.structFieldDefaultValue(i, ip).?;
        const alloc = try sema.lookupComptimeAlloc(alloc_ptr);
        alloc.val = try sema.setAggregateElement(alloc.val, agg_ty, i, default);
    }
}

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

fn evalAllocInferred(sema: *Sema, comptime is_const: bool) Error!?Value {
    const placeholder = try sema.intern_pool.get(.{ .undef = .generic_poison_type });
    return try sema.pushComptimeAlloc(.generic_poison_type, .{ .index = placeholder }, is_const, .none);
}

fn evalStoreToInferredPtr(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    const bin = sema.zir.extraData(Zir.Inst.Bin, pl_node.payload_index).data;
    const ptr = try sema.resolveInst(bin.lhs);
    const operand = try sema.resolveInst(bin.rhs);

    const p = ip.indexToKey(ptr.index).ptr;
    const slot = try sema.lookupComptimeAlloc(p);
    slot.val = operand;

    const ptr_ty = try ip.internPtrType(.{
        .child = operand.typeOf(ip).toIndex(),
        .flags = .{ .size = .one, .is_const = slot.is_const },
    });
    const typed_ptr = try ip.internPtr(.{ .ty = ptr_ty, .base_addr = p.base_addr, .byte_offset = 0 });
    try sema.inst_map.put(sema.gpa, bin.lhs.toIndex().?, .{ .index = typed_ptr });
    return .{ .index = .void_value };
}

fn evalResolveInferredAlloc(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    return try sema.resolveInst(un_node.operand);
}

fn evalDeref(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);
    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    assert(un_node.operand != .none);
    const operand = try sema.resolveInst(un_node.operand);
    try sema.validateDeref(operand);
    return try sema.loadValue(operand);
}

fn evalRefDeref(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);
    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
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
            return try sema.coerceValueToType(operand, single_ptr_ty, "@as");
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
    const coerced = if (ptr_key.ptr.base_addr == .comptime_alloc)
        try sema.coerceValueToType(rhs_value, (try sema.lookupComptimeAlloc(ptr_key.ptr)).val.typeOf(ip).toIndex(), "store")
    else
        try sema.coerceValueToType(rhs_value, ptr_ty_key.ptr_type.child, "store");
    try sema.storePointee(ptr_key.ptr, coerced);
    return .{ .index = .void_value };
}

fn evalLoad(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    assert(un_node.operand != .none);

    const ptr_value = try sema.resolveInst(un_node.operand);
    return try sema.loadValue(ptr_value);
}

fn loadValue(sema: *Sema, ptr: Value) Error!Value {
    const ip = sema.intern_pool;
    const ptr_key = ip.indexToKey(ptr.index);
    if (ptr_key != .ptr) {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "internal error: load through non-pointer value", .{});
    }
    switch (ptr_key.ptr.base_addr) {
        .nav => |nav| return .{ .index = ip.getNav(nav).resolved.?.value },
        .uav => |uav| return .{ .index = uav.val },
        .comptime_field => |val| return .{ .index = val },
        .field, .arr_elem => |f| {
            const parent = try sema.loadValue(.{ .index = f.base });
            const parent_key = ip.indexToKey(parent.index);
            if (parent_key == .undef) return .{ .index = .undef };
            if (ptr_key.ptr.base_addr == .arr_elem) sub_array: {
                const child_ty = ip.indexToKey(ptr_key.ptr.ty).ptr_type.child;
                const sub = indexableInfo(ip, child_ty) orelse break :sub_array;
                const agg = switch (parent_key) {
                    .aggregate => |agg| agg,
                    else => break :sub_array,
                };
                const parent_info = indexableInfo(ip, agg.ty) orelse break :sub_array;
                if (parent_info.child != sub.child) break :sub_array;
                const count = ip.aggregateElementCount(child_ty);
                const elems = try sema.arena.alloc(InternPool.Index, @intCast(count));
                for (elems, 0..) |*e, i| e.* = try ip.aggregateElementAt(agg, f.index + @as(u64, @intCast(i)));
                return try sema.aggregateValue(Type.fromIndex(child_ty), elems);
            }
            return switch (parent_key) {
                .un => try sema.loadUnionField(parent.index, @intCast(f.index)),
                .aggregate => |agg| .{ .index = try ip.aggregateElementAt(agg, @intCast(f.index)) },
                else => unreachable,
            };
        },
        .opt_payload => |base| {
            const opt = try sema.loadValue(.{ .index = base });
            return switch (ip.indexToKey(opt.index)) {
                .undef => .{ .index = .undef },
                else => .{ .index = ip.indexToKey(opt.index).opt.val },
            };
        },
        .eu_payload => |base| {
            const eu = try sema.loadValue(.{ .index = base });
            return switch (ip.indexToKey(eu.index)) {
                .undef => .{ .index = .undef },
                .error_union => |e| switch (e.val) {
                    .payload => |p| .{ .index = p },
                    .err_name => {
                        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "err_union_payload: operand carries an error, not a payload", .{});
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
    const idx: u32 = @intFromEnum(ptr.base_addr.comptime_alloc);
    assert(idx < sema.comptime_allocs.items.len);
    return &sema.comptime_allocs.items[idx];
}

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

fn coerceInMemoryAllowed(sema: *Sema, dest_ty: Type, src_ty: Type, dest_is_mut: bool, src_val: ?Value) Error!InMemoryCoercionResult {
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

fn coerceValueToType(sema: *Sema, value: Value, dest_ty: InternPool.Index, op_name: []const u8) Error!Value {
    return sema.coerceExtra(value, dest_ty, op_name, true);
}

fn coerceExtra(
    sema: *Sema,
    value: Value,
    dest_ty: InternPool.Index,
    op_name: []const u8,
    report_err: bool,
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

    switch (ip.indexToKey(dest_ty)) {
        .int_type => if (try sema.coerceToFixedWidthInt(value, dest_ty, op_name)) |c| return c,
        .simple_type => |s| switch (s) {
            .usize, .isize, .c_char, .c_short, .c_ushort, .c_int, .c_uint, .c_long, .c_ulong, .c_longlong, .c_ulonglong => {
                if (try sema.coerceToFixedWidthInt(value, dest_ty, op_name)) |c| return c;
            },
            .f16, .f32, .f64, .f80, .f128, .comptime_float, .c_longdouble => {
                if (try sema.coerceToFloat(value, dest_ty, op_name)) |c| return c;
            },
            .comptime_int => if (ip.indexToKey(value.index) == .int) {
                var space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
                const big = ip.indexToKey(value.index).int.storage.toBigInt(&space);
                return .{ .index = try ip.internIntValue(.comptime_int_type, big) };
            },
            .anyerror => return try sema.coerceToErrorSet(value, dest_ty, op_name),
            else => {},
        },
        .error_set_type => return try sema.coerceToErrorSet(value, dest_ty, op_name),
        .error_union_type => return try sema.coerceToErrorUnion(value, dest_ty, op_name),
        .opt_type => return try sema.coerceToOptional(value, dest_ty, op_name),
        .ptr_type => |p| switch (p.flags.size) {
            .slice => if (try sema.coerceToSlice(value, dest_ty)) |c| return c,
            .many => if (try sema.coerceToManyPtr(value, dest_ty)) |c| return c,
            // A function value coerces to a pointer-to-function (`fn(...)` -> `*const fn(...)`) by
            // taking its address, like `&f` -- the coercion that builds a vtable of method pointers.
            .one => if (ip.indexToKey(p.child) == .func_type and ip.indexToKey(value.index) == .func)
                return try sema.materializeConstPtr(value),
            .c => {},
        },
        .array_type, .vector_type => {
            // The compiler dispatches an array/vector destination by source shape: an array/vector
            // source coerces element-wise (coerceArrayLike), a tuple source through coerceTupleToArray.
            if (Type.fromIndex(Value.typeOf(value, ip).index).isTuple(ip))
                return try sema.coerceTupleToArray(value, dest_ty, op_name);
            if (try sema.coerceArrayLike(value, dest_ty, op_name)) |c| return c;
        },
        .enum_type => switch (ip.indexToKey(value.index)) {
            .enum_literal => |name| {
                if (try sema.enumTagByName(dest_ty, name)) |tag| return tag;
                return sema.failBadMemberAccess(dest_ty, name);
            },
            .enum_tag => |et| if (et.ty == dest_ty) return value,
            else => {},
        },
        .union_type => switch (ip.indexToKey(value.index)) {
            .un => |u| if (u.ty == dest_ty) return value,
            .enum_literal, .enum_tag => return try sema.coerceEnumToUnion(value, dest_ty, op_name),
            else => {},
        },
        else => {},
    }

    if (!report_err) return error.NotCoercible;
    return sema.fail(sema.block, sema.block.nodeOffset(.zero), "{s}: cannot coerce value to destination type", .{op_name});
}

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
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "{s}: cannot initialize union field with uninstantiable type", .{op_name});
    }
    return sema.fail(sema.block, sema.block.nodeOffset(.zero), "{s}: cannot initialize union field '{s}' from a bare tag", .{ op_name, ip.stringSlice(tag_name) });
}

fn coerceToErrorSet(sema: *Sema, value: Value, dest_ty: InternPool.Index, op_name: []const u8) Error!Value {
    const ip = sema.intern_pool;
    const key = ip.indexToKey(value.index);
    if (key != .err) {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "{s}: expected an error value", .{op_name});
    }
    const imc = try sema.coerceInMemoryAllowedErrorSets(Type.fromIndex(dest_ty), Value.typeOf(value, ip));
    if (imc != .ok) {
        const src = sema.block.nodeOffset(.zero);
        const msg = msg: {
            const msg = try sema.errMsg(src, "{s}: cannot coerce error set", .{op_name});
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

fn coerceToManyPtr(sema: *Sema, value: Value, dest_ty: InternPool.Index) Error!?Value {
    const ip = sema.intern_pool;
    if (ip.indexToKey(value.index) != .ptr) return null;
    const array_ptr = ip.indexToKey(value.index).ptr;
    const child = ip.indexToKey(array_ptr.ty).ptr_type.child;
    if (ip.indexToKey(child) != .array_type) return null;
    const retagged = try ip.internPtr(.{ .ty = dest_ty, .base_addr = array_ptr.base_addr, .byte_offset = array_ptr.byte_offset });
    return .{ .index = retagged };
}

fn coerceArrayLike(sema: *Sema, value: Value, dest_ty: InternPool.Index, op_name: []const u8) Error!?Value {
    const ip = sema.intern_pool;
    if (ip.indexToKey(value.index) != .aggregate) return null;
    const src = indexableInfo(ip, Value.typeOf(value, ip).index) orelse return null;
    const dst = indexableInfo(ip, dest_ty).?;
    if (src.len != dst.len) return null;

    const count: usize = @intCast(dst.len);
    const elems = try sema.gpa.alloc(InternPool.Index, count);
    defer sema.gpa.free(elems);
    const agg = ip.indexToKey(value.index).aggregate;
    for (elems, 0..) |*e, i| {
        const elem: Value = .{ .index = try ip.aggregateElementAt(agg, i) };
        e.* = (try sema.coerceValueToType(elem, dst.child, op_name)).index;
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
fn coerceTupleToArray(sema: *Sema, value: Value, dest_ty: InternPool.Index, op_name: []const u8) Error!Value {
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
            const msg = try sema.errMsg(src, "{s}: expected type '{f}', found '{f}'", .{ op_name, Type.fromIndex(dest_ty).fmt(ip), Value.typeOf(value, ip).fmt(ip) });
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
        elems[i] = (try sema.coerceValueToType(elem_val, dest_elem_ty, op_name)).index;
    }
    return .{ .index = try ip.internAggregate(.{ .ty = dest_ty, .storage = .{ .elems = elems } }) };
}

fn coerceToFixedWidthInt(sema: *Sema, value: Value, dest_ty: InternPool.Index, op_name: []const u8) Error!?Value {
    const ip = sema.intern_pool;
    if (ip.indexToKey(value.index) != .int) return null;
    const dst = intTypeInfo(ip, dest_ty) orelse return null;
    if (!value.is_comptime) {
        const value_type = Value.typeOf(value, ip);
        if (intTypeInfo(ip, value_type.index)) |src| {
            if (!intCoercible(src, dst)) {
                return sema.fail(sema.block, sema.block.nodeOffset(.zero), "expected type '{f}', found '{f}'", .{ Type.fromIndex(dest_ty).fmt(ip), Type.fromIndex(value_type.index).fmt(ip) });
            }
        }
    }
    var coerced = try sema.refitIntToFixedWidth(value.index, dest_ty, op_name);
    coerced.is_comptime = value.is_comptime;
    return coerced;
}

fn coerceToFloat(sema: *Sema, value: Value, dest_ty: InternPool.Index, op_name: []const u8) Error!?Value {
    if (!isFloatTypeIndex(dest_ty)) return null;
    const ip = sema.intern_pool;
    if (!value.is_comptime) {
        const value_type = Value.typeOf(value, ip);
        const widens = isFloatTypeIndex(value_type.index) and
            numericBitSize(ip, value_type.index).? <= numericBitSize(ip, dest_ty).?;
        if (!widens) {
            return sema.fail(sema.block, sema.block.nodeOffset(.zero), "{s}: a runtime value does not coerce to {f} (needs @floatCast or @floatFromInt)", .{ op_name, Type.fromIndex(dest_ty).fmt(ip) });
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

fn evalIntType(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const int_type = sema.zir.instructions.items(.data)[@intFromEnum(inst)].int_type;
    const idx = try sema.intern_pool.internIntType(int_type.signedness, int_type.bit_count);
    return .{ .index = idx };
}

fn evalReifyInt(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.Bin, pl_node.payload_index).data;
    const signedness = try sema.resolveStdLangEnum(.Signedness, extra.lhs);
    const bits: u16 = @intCast(try sema.resolveInt(try sema.resolveInst(extra.rhs), .u16_type, "int bit width"));
    if (bits == 0 and signedness == .signed) {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "signed integer cannot have bit width 0", .{});
    }
    return .{ .index = try sema.intern_pool.internIntType(signedness, bits) };
}

fn evalReifyTuple(sema: *Sema, extended: Zir.Inst.Extended.InstData) Error!?Value {
    const ip = sema.intern_pool;
    const extra = sema.zir.extraData(Zir.Inst.UnNode, extended.operand).data;

    const types_uncoerced = try sema.resolveInst(extra.operand);
    const types_slice_val = try sema.coerceValueToType(types_uncoerced, try sema.sliceConstTypeTy(), "tuple field types");
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
    const array_ptr: InternPool.Index = switch (ip.indexToKey(val.index)) {
        .slice => |s| s.ptr,
        .ptr => val.index,
        else => {
            return sema.fail(sema.block, sema.block.nodeOffset(.zero), "reify: expected a comptime array-backed slice", .{});
        },
    };
    switch (ip.indexToKey(array_ptr).ptr.base_addr) {
        .uav, .nav => return try sema.loadValue(.{ .index = array_ptr }),
        .arr_elem => |ae| if (ae.index == 0) return try sema.loadValue(.{ .index = ae.base }),
        else => {},
    }
    return sema.fail(sema.block, sema.block.nodeOffset(.zero), "reify: expected a comptime array-backed slice", .{});
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

    const size_val = try sema.coerceValueToType(try sema.resolveInst(extra.size), size_ty, "pointer size");
    const size = try sema.interpretStdLangEnum(std.lang.Type.Pointer.Size, size_ty, size_val, "pointer size");

    const attrs_val = try sema.coerceValueToType(try sema.resolveInst(extra.attrs), attrs_ty, "pointer attributes");
    const attrs = ip.indexToKey(attrs_val.index).aggregate;
    const is_const = try ip.aggregateElementAt(attrs, 0) == .bool_true;
    const is_volatile = try ip.aggregateElementAt(attrs, 1) == .bool_true;
    const is_allowzero = try ip.aggregateElementAt(attrs, 2) == .bool_true;
    const addrspace_opt = ip.indexToKey(try ip.aggregateElementAt(attrs, 3)).opt.val;
    const align_opt = ip.indexToKey(try ip.aggregateElementAt(attrs, 4)).opt.val;

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
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "pointer to noreturn not allowed", .{});
    }
    if (elem_ty == .null_type) {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "cannot reify pointer to '@TypeOf(null)'", .{});
    }
    if (elem_ty == .anyopaque_type and size != .one) {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "indexable pointer to opaque type not allowed", .{});
    }
    if (ip.indexToKey(elem_ty) == .func_type and size != .one) {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "function pointers must be single pointers", .{});
    }

    const sentinel_ty = try ip.internOptionalType(elem_ty);
    const sentinel_val = try sema.coerceValueToType(try sema.resolveInst(extra.sentinel), sentinel_ty, "pointer sentinel");
    const opt_sentinel = ip.indexToKey(sentinel_val.index).opt.val;
    if (opt_sentinel != .none) switch (size) {
        .many, .slice => {},
        .one, .c => {
            return sema.fail(sema.block, sema.block.nodeOffset(.zero), "sentinels are only allowed on slices and unknown-length pointers", .{});
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

fn evalReifyPointerSentinelTy(sema: *Sema, extended: Zir.Inst.Extended.InstData) Error!?Value {
    const ip = sema.intern_pool;
    const extra = sema.zir.extraData(Zir.Inst.UnNode, extended.operand).data;
    const elem_ty = try sema.resolveDestType(extra.operand, "pointer child");
    const child = if (elem_ty == .anyopaque_type or elem_ty == .null_type) .noreturn_type else elem_ty;
    return .{ .index = try ip.internOptionalType(child) };
}

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
    const operand_val = try sema.coerceValueToType(try sema.resolveInst(extra.operand), operand_ty, "reify slice argument");
    const len = try sema.resolveUsizeInt(.{ .index = ip.indexToKey(operand_val.index).slice.len }, "reify slice argument length");
    const arr_ty = try ip.internArrayType(.{ .len = len, .child = out_scalar_ty });
    return .{ .index = try ip.internPtrType(.{ .child = arr_ty, .flags = .{ .size = .one, .is_const = true } }) };
}

fn interpretCallConv(sema: *Sema, val: Value) Error!std.lang.CallingConvention {
    const ip = sema.intern_pool;
    const un = ip.indexToKey(val.index).un;
    const tag_enum = ip.indexToKey(un.tag).enum_tag.ty;
    const idx = (try sema.enumTagFieldIndex(tag_enum, .{ .index = un.tag })).?;
    const name = ip.stringSlice((try sema.enumFieldName(tag_enum, idx)).?);
    const tag = std.meta.stringToEnum(std.meta.Tag(std.lang.CallingConvention), name) orelse {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "calling convention: unknown variant '{s}'", .{name});
    };
    switch (tag) {
        inline else => |t| {
            if (@FieldType(std.lang.CallingConvention, @tagName(t)) != void) {
                return sema.fail(sema.block, sema.block.nodeOffset(.zero), "calling convention '{s}' is not modelled", .{@tagName(t)});
            }
            return @unionInit(std.lang.CallingConvention, @tagName(t), {});
        },
    }
}

fn evalReifyFn(sema: *Sema, extended: Zir.Inst.Extended.InstData) Error!?Value {
    const ip = sema.intern_pool;
    const extra = sema.zir.extraData(Zir.Inst.ReifyFn, extended.operand).data;

    const param_types_slice = try sema.coerceValueToType(try sema.resolveInst(extra.param_types), try sema.sliceConstTypeTy(), "fn parameter types");
    const param_types_arr = ip.indexToKey((try sema.derefSliceAsArray(param_types_slice)).index).aggregate;
    const params_len: u32 = @intCast(ip.indexToKey(param_types_arr.ty).array_type.len);

    const param_attrs_arr = ip.indexToKey((try sema.derefSliceAsArray(try sema.resolveInst(extra.param_attrs))).index).aggregate;

    const ret_ty = try sema.resolveDestType(extra.ret_ty, "fn return type");

    const fn_attrs_val = try sema.coerceValueToType(try sema.resolveInst(extra.fn_attrs), try sema.getStdLangType(.@"Type.Fn.Attributes"), "fn attributes");
    const fn_attrs = ip.indexToKey(fn_attrs_val.index).aggregate;
    const cc = try sema.interpretCallConv(.{ .index = try ip.aggregateElementAt(fn_attrs, 0) });
    const varargs = try ip.aggregateElementAt(fn_attrs, 1) == .bool_true;

    var noalias_bits: u32 = 0;
    const param_types = try sema.gpa.alloc(InternPool.Index, params_len);
    defer sema.gpa.free(param_types);
    for (param_types, 0..) |*param_ty, param_idx| {
        param_ty.* = try ip.aggregateElementAt(param_types_arr, param_idx);
        const param_attr = ip.indexToKey(try ip.aggregateElementAt(param_attrs_arr, param_idx)).aggregate;
        if (try ip.aggregateElementAt(param_attr, 0) == .bool_true) {
            if (param_idx > 31) {
                return sema.fail(sema.block, sema.block.nodeOffset(.zero), "this compiler implementation only supports 'noalias' on the first 32 parameters", .{});
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
    const int_tag_ty = try sema.resolveDestType(extra.lhs, "enum tag type");
    const names_slice = try sema.coerceValueToType(try sema.resolveInst(extra.rhs), try sema.sliceOfStringTy(), "enum field names");
    const len = try sema.resolveUsizeInt(.{ .index = ip.indexToKey(names_slice.index).slice.len }, "enum field names length");
    const arr_ty = try ip.internArrayType(.{ .len = len, .child = int_tag_ty });
    return .{ .index = try ip.internPtrType(.{ .child = arr_ty, .flags = .{ .size = .one, .is_const = true } }) };
}

fn evalReifyEnum(sema: *Sema, extended: Zir.Inst.Extended.InstData, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    const name_strategy: Zir.Inst.NameStrategy = @enumFromInt(extended.small);
    const extra = sema.zir.extraData(Zir.Inst.ReifyEnum, extended.operand).data;

    const tag_ty = try sema.resolveDestType(extra.tag_ty, "enum tag type");

    const enum_mode_ty = try sema.getStdLangType(.@"Type.Enum.Mode");
    const mode_val = try sema.coerceValueToType(try sema.resolveInst(extra.mode), enum_mode_ty, "enum mode");
    const nonexhaustive = switch (try sema.interpretStdLangEnum(std.lang.Type.Enum.Mode, enum_mode_ty, mode_val, "enum mode")) {
        .exhaustive => false,
        .nonexhaustive => true,
    };

    const names_slice = try sema.coerceValueToType(try sema.resolveInst(extra.field_names), try sema.sliceOfStringTy(), "enum field names");
    const names_agg = ip.indexToKey((try sema.derefSliceAsArray(names_slice)).index).aggregate;
    const fields_len: u32 = @intCast(ip.indexToKey(names_agg.ty).array_type.len);

    const values_ty = try ip.internPtrType(.{
        .child = try ip.internArrayType(.{ .len = fields_len, .child = tag_ty }),
        .flags = .{ .size = .one, .is_const = true },
    });
    const values_slice = try sema.coerceValueToType(try sema.resolveInst(extra.field_values), values_ty, "enum field values");
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
            return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "use of undefined value here causes illegal behavior", .{});
        }
    }

    var hasher = std.hash.Wyhash.init(0);
    std.hash.autoHash(&hasher, tag_ty);
    std.hash.autoHash(&hasher, nonexhaustive);
    std.hash.autoHash(&hasher, fields_len);
    std.hash.autoHash(&hasher, values_arr.index);
    for (names) |n| std.hash.autoHash(&hasher, n);

    const name = switch (name_strategy) {
        .parent => sema.type_name_ctx,
        .anon, .func, .dbg_var => blk: {
            const ctx = ip.stringSlice(sema.type_name_ctx);
            const text = try std.fmt.allocPrint(sema.gpa, "{s}__enum_{d}", .{ ctx, @intFromEnum(inst) });
            defer sema.gpa.free(text);
            break :blk try ip.getOrPutString(sema.gpa, text, .no_embedded_nulls);
        },
    };

    const enum_ty = try ip.getReifiedEnumType(.{
        .name = name,
        .id = .{ .reified = .{ .source_zir_id = sema.current_zir_id, .decl_inst = inst, .type_hash = hasher.final() } },
        .parent = sema.this_type,
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
                const src = sema.block.builtinCallArgSrc(sema.srcNodeOffset(inst), 2);
                const msg = try sema.errMsg(src, "duplicate enum field '{f}' at index '{d}'", .{ field_name.fmt(ip), field_index });
                errdefer msg.destroy(sema.gpa);
                try sema.errNote(src, msg, "previous field at index '{d}'", .{prev_field_index});
                break :msg msg;
            });
        }
    }
    if (fields.field_value_map.unwrap()) |value_map| {
        value_map.get(ip).clearRetainingCapacity();
        for (values, 0..) |field_value, field_index| {
            if (ip.addFieldTagValue(values, value_map, field_value)) |prev_field_index| {
                return sema.failWithOwnedErrorMsg(sema.block, msg: {
                    const src = sema.block.builtinCallArgSrc(sema.srcNodeOffset(inst), 3);
                    const msg = try sema.errMsg(src, "enum tag value '{f}' for field '{f}' already taken", .{ render_value.fmt(.{ .index = field_value }, ip), names[field_index].fmt(ip) });
                    errdefer msg.destroy(sema.gpa);
                    try sema.errNote(src, msg, "previous occurrence in field '{f}'", .{names[prev_field_index].fmt(ip)});
                    break :msg msg;
                });
            }
        }
    }
    return .{ .index = enum_ty };
}

fn evalReifyStruct(sema: *Sema, extended: Zir.Inst.Extended.InstData, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    const name_strategy: Zir.Inst.NameStrategy = @enumFromInt(extended.small);
    const extra = sema.zir.extraData(Zir.Inst.ReifyStruct, extended.operand).data;

    const layout_ty = try sema.getStdLangType(.@"Type.ContainerLayout");
    const layout_val = try sema.coerceValueToType(try sema.resolveInst(extra.layout), layout_ty, "struct layout");
    const layout = try sema.interpretStdLangEnum(std.lang.Type.ContainerLayout, layout_ty, layout_val, "struct layout");

    const backing_val = try sema.coerceValueToType(try sema.resolveInst(extra.backing_ty), try ip.internOptionalType(.type_type), "struct backing integer type");
    if (ip.indexToKey(backing_val.index) == .undef) {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "use of undefined value here causes illegal behavior", .{});
    }
    const backing_int = ip.indexToKey(backing_val.index).opt.val;
    if (backing_int != .none and layout != .@"packed") {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "non-packed struct does not support backing integer type", .{});
    }

    const names_slice = try sema.coerceValueToType(try sema.resolveInst(extra.field_names), try sema.sliceOfStringTy(), "struct field names");
    const names_agg = ip.indexToKey((try sema.derefSliceAsArray(names_slice)).index).aggregate;
    const fields_len: u32 = @intCast(ip.indexToKey(names_agg.ty).array_type.len);

    const field_types_ty = try ip.internPtrType(.{
        .child = try ip.internArrayType(.{ .len = fields_len, .child = .type_type }),
        .flags = .{ .size = .one, .is_const = true },
    });
    const types_arr = try sema.derefSliceAsArray(try sema.coerceValueToType(try sema.resolveInst(extra.field_types), field_types_ty, "struct field types"));
    const types_agg = ip.indexToKey(types_arr.index).aggregate;

    const attrs_scalar_ty = try sema.getStdLangType(.@"Type.Struct.FieldAttributes");
    const field_attrs_ty = try ip.internPtrType(.{
        .child = try ip.internArrayType(.{ .len = fields_len, .child = attrs_scalar_ty }),
        .flags = .{ .size = .one, .is_const = true },
    });
    const attrs_agg = ip.indexToKey((try sema.derefSliceAsArray(try sema.coerceValueToType(try sema.resolveInst(extra.field_attrs), field_attrs_ty, "struct field attributes"))).index).aggregate;

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
            return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "use of undefined value here causes illegal behavior", .{});
        }
        const attr_elem = try ip.aggregateElementAt(attrs_agg, i);
        if (ip.indexToKey(attr_elem) == .undef) {
            return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "use of undefined value here causes illegal behavior", .{});
        }
        const attr = ip.indexToKey(attr_elem).aggregate;
        const comptime_elem = try ip.aggregateElementAt(attr, 0);
        const align_elem = try ip.aggregateElementAt(attr, 1);
        const align_opt = ip.indexToKey(align_elem).opt.val;
        const default_ptr = ip.indexToKey(try ip.aggregateElementAt(attr, 2)).opt.val;

        const field_default: InternPool.Index = if (default_ptr == .none) .none else (try sema.loadValue(.{ .index = default_ptr })).index;
        if (field_default != .none) {
            defaults[i] = field_default;
            any_defaults = true;
        }

        if (comptime_elem == .bool_true) {
            if (field_default == .none) {
                return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "comptime field without default initialization value", .{});
            }
            if (layout != .auto) {
                return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "non-auto struct fields cannot be marked comptime", .{});
            }
            comptime_words[i / 32] |= @as(u32, 1) << @intCast(i % 32);
            any_comptime = true;
        }

        if (align_opt != .none) {
            if (layout == .@"packed") {
                return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "packed struct fields cannot be aligned", .{});
            }
            aligns[i] = .fromByteUnits(Value.fromIndex(align_opt).toUnsignedInt(ip));
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
            break :blk try ip.getOrPutString(sema.gpa, text, .no_embedded_nulls);
        },
    };

    const struct_ty = try ip.getReifiedStructType(.{
        .name = name,
        .id = .{ .reified = .{ .source_zir_id = sema.current_zir_id, .decl_inst = inst, .type_hash = hasher.final() } },
        .parent = sema.this_type,
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
                const src = sema.block.builtinCallArgSrc(sema.srcNodeOffset(inst), 2);
                const msg = try sema.errMsg(src, "duplicate struct field '{f}' at index '{d}", .{ field_name.fmt(ip), field_index });
                errdefer msg.destroy(sema.gpa);
                try sema.errNote(src, msg, "previous field at index '{d}'", .{prev_field_index});
                break :msg msg;
            });
        }
    }
    return .{ .index = struct_ty };
}

fn evalReifyUnion(sema: *Sema, extended: Zir.Inst.Extended.InstData, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    const name_strategy: Zir.Inst.NameStrategy = @enumFromInt(extended.small);
    const extra = sema.zir.extraData(Zir.Inst.ReifyUnion, extended.operand).data;

    const layout_ty = try sema.getStdLangType(.@"Type.ContainerLayout");
    const layout_val = try sema.coerceValueToType(try sema.resolveInst(extra.layout), layout_ty, "union layout");
    const layout = try sema.interpretStdLangEnum(std.lang.Type.ContainerLayout, layout_ty, layout_val, "union layout");

    const arg_val = try sema.coerceValueToType(try sema.resolveInst(extra.arg_ty), try ip.internOptionalType(.type_type), "union tag/backing type");
    if (ip.indexToKey(arg_val.index) == .undef) {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "use of undefined value here causes illegal behavior", .{});
    }
    const arg_ty = ip.indexToKey(arg_val.index).opt.val;
    var tag_type: InternPool.Index = .none;
    var backing_int: InternPool.Index = .none;
    if (arg_ty != .none) switch (layout) {
        .@"extern" => {
            return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "extern union does not support enum tag type", .{});
        },
        .@"packed" => backing_int = arg_ty,
        .auto => tag_type = arg_ty,
    };

    const names_slice = try sema.coerceValueToType(try sema.resolveInst(extra.field_names), try sema.sliceOfStringTy(), "union field names");
    const names_agg = ip.indexToKey((try sema.derefSliceAsArray(names_slice)).index).aggregate;
    const fields_len: u32 = @intCast(ip.indexToKey(names_agg.ty).array_type.len);

    const field_types_ty = try ip.internPtrType(.{
        .child = try ip.internArrayType(.{ .len = fields_len, .child = .type_type }),
        .flags = .{ .size = .one, .is_const = true },
    });
    const types_arr = try sema.derefSliceAsArray(try sema.coerceValueToType(try sema.resolveInst(extra.field_types), field_types_ty, "union field types"));
    const types_agg = ip.indexToKey(types_arr.index).aggregate;

    const attrs_scalar_ty = try sema.getStdLangType(.@"Type.Union.FieldAttributes");
    const field_attrs_ty = try ip.internPtrType(.{
        .child = try ip.internArrayType(.{ .len = fields_len, .child = attrs_scalar_ty }),
        .flags = .{ .size = .one, .is_const = true },
    });
    const attrs_arr = try sema.derefSliceAsArray(try sema.coerceValueToType(try sema.resolveInst(extra.field_attrs), field_attrs_ty, "union field attributes"));
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
            return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "use of undefined value here causes illegal behavior", .{});
        }
        const attr_elem = try ip.aggregateElementAt(attrs_agg, i);
        if (ip.indexToKey(attr_elem) == .undef) {
            return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "use of undefined value here causes illegal behavior", .{});
        }
        const align_opt = ip.indexToKey(try ip.aggregateElementAt(ip.indexToKey(attr_elem).aggregate, 0)).opt.val;
        if (align_opt != .none) {
            if (layout == .@"packed") {
                return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "packed union fields cannot be aligned", .{});
            }
            aligns[i] = .fromByteUnits(Value.fromIndex(align_opt).toUnsignedInt(ip));
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
        .parent = sema.this_type,
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
                const src = sema.block.builtinCallArgSrc(sema.srcNodeOffset(inst), 2);
                const msg = try sema.errMsg(src, "duplicate union field '{f}' at index '{d}", .{ field_name.fmt(ip), field_index });
                errdefer msg.destroy(sema.gpa);
                try sema.errNote(src, msg, "previous field at index '{d}'", .{prev_field_index});
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

    const len = try sema.resolveArrayLen(bin.lhs, "array_type");
    const child = try sema.resolveDestType(bin.rhs, "array_type");
    const array_ty = try sema.intern_pool.internArrayType(.{ .len = len, .child = child });
    return .{ .index = array_ty };
}

fn evalArrayTypeSentinel(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);
    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.ArrayTypeSentinel, pl_node.payload_index).data;
    const len = try sema.resolveArrayLen(extra.len, "array_type");
    const elem_type = try sema.resolveDestType(extra.elem_type, "array_type");
    const uncasted_sentinel = try sema.resolveInst(extra.sentinel);
    const sentinel = try sema.coerceValueToType(uncasted_sentinel, elem_type, "array sentinel");
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

    const len64 = try sema.resolveArrayLen(bin.lhs, "vector_type");
    const len = std.math.cast(u32, len64) orelse {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "vector_type: length {d} exceeds u32", .{len64});
    };
    const child = try sema.resolveDestType(bin.rhs, "vector_type");
    if (!isVectorElemType(sema.intern_pool, child)) {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "vector_type: expected integer, float, bool, or pointer for the vector element type", .{});
    }
    const vector_ty = try sema.intern_pool.internVectorType(.{ .len = len, .child = child });
    return .{ .index = vector_ty };
}

fn evalSelect(sema: *Sema, extended: Zir.Inst.Extended.InstData) Error!?Value {
    const ip = sema.intern_pool;
    const extra = sema.zir.extraData(Zir.Inst.Select, extended.operand).data;

    const elem_ty = try sema.resolveDestType(extra.elem_type, "@select");
    if (!isVectorElemType(ip, elem_ty)) {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "@select: expected integer, float, bool, or pointer for the element type", .{});
    }
    const pred = try sema.resolveInst(extra.pred);
    const pred_info = indexableInfo(ip, Value.typeOf(pred, ip).index) orelse {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "@select: expected vector or array for the predicate", .{});
    };
    const vec_len = pred_info.len;

    const vec_ty = try ip.internVectorType(.{ .len = @intCast(vec_len), .child = elem_ty });
    const a_agg = ip.indexToKey((try sema.coerceValueToType(try sema.resolveInst(extra.a), vec_ty, "@select")).index).aggregate;
    const b_agg = ip.indexToKey((try sema.coerceValueToType(try sema.resolveInst(extra.b), vec_ty, "@select")).index).aggregate;
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
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    const child = try sema.resolveDestType(un_node.operand, "optional_type");
    const opt_ty = try sema.intern_pool.internOptionalType(child);
    return .{ .index = opt_ty };
}

fn evalOptionalPayload(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    const operand = try sema.resolveInst(un_node.operand);
    const key = sema.intern_pool.indexToKey(operand.index);
    if (key != .opt) {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "optional unwrap: operand is not an optional", .{});
    }
    if (key.opt.val == .none) {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "unable to unwrap null", .{});
    }
    return .{ .index = key.opt.val };
}

fn evalOptionalPayloadPtr(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);
    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    return try sema.optPayloadPtr(try sema.resolveInst(un_node.operand), false);
}

fn optPayloadPtr(sema: *Sema, optional_ptr: Value, comptime initializing: bool) Error!Value {
    const ip = sema.intern_pool;
    const ptr_type = ip.indexToKey(optional_ptr.typeOf(ip).toIndex()).ptr_type;
    const opt_key = ip.indexToKey(ptr_type.child);
    if (opt_key != .opt_type) {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "optional unwrap: pointer child is not an optional", .{});
    }
    if (!initializing) {
        const opt_val = try sema.loadValue(optional_ptr);
        if (ip.indexToKey(opt_val.index).opt.val == .none) {
            return sema.fail(sema.block, sema.block.nodeOffset(.zero), "unable to unwrap null", .{});
        }
    }
    const child_ptr_ty = try ip.internPtrType(.{ .child = opt_key.opt_type, .sentinel = ptr_type.sentinel, .flags = ptr_type.flags });
    return .{ .index = try ip.internPtr(.{
        .ty = child_ptr_ty,
        .base_addr = .{ .opt_payload = optional_ptr.index },
        .byte_offset = 0,
    }) };
}

fn evalIsNonNull(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);
    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    return try sema.isNonNullVal(try sema.resolveInst(un_node.operand));
}

fn evalIsNonNullPtr(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);
    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
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
    assert(@intFromEnum(inst) < sema.zir.instructions.len);
    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
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
            if (ptr_info.flags.size == .one and Type.fromIndex(ptr_info.child).zigTypeTag(ip) == .array) {
                const ai = Type.fromIndex(ptr_info.child).arrayInfo(ip);
                return .{ .elem_type = ai.elem_type, .sentinel = ai.sentinel orelse .none, .len = ai.len, .array = try sema.loadValue(operand) };
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
    assert(@intFromEnum(inst) < sema.zir.instructions.len);
    const ip = sema.intern_pool;
    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
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

    const ctx = ip.stringSlice(sema.type_name_ctx);
    const name_text = try std.fmt.allocPrint(sema.gpa, "{s}__struct_{d}", .{ ctx, @intFromEnum(inst) });
    defer sema.gpa.free(name_text);
    const struct_ty = try ip.getReifiedStructType(.{
        .name = try ip.getOrPutString(sema.gpa, name_text, .no_embedded_nulls),
        .id = .{ .reified = .{ .source_zir_id = sema.current_zir_id, .decl_inst = inst, .type_hash = hasher.final() } },
        .parent = sema.this_type,
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
    const inst_data = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_tok;
    const extra = sema.zir.extraData(Zir.Inst.Import, inst_data.payload_index).data;
    return .{ .index = try sema.importPath(sema.zir.nullTerminatedString(extra.path)) };
}

fn importPath(sema: *Sema, path: []const u8) Error!InternPool.Index {
    if (std.mem.eql(u8, path, "std")) return sema.loadModuleFile("std.zig");
    if (std.mem.eql(u8, path, "root")) return sema.rootModuleType();
    if (std.mem.eql(u8, path, "builtin")) return sema.loadBuiltinModule("builtin");

    if (std.mem.endsWith(u8, path, ".zig")) {
        const importer = sema.importerSubPath() orelse {
            return sema.fail(sema.block, sema.block.nodeOffset(.zero), "no module named '{s}' available", .{path});
        };
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
    const ty = try sema.intern_pool.getDeclaredStructType(
        try sema.intern_pool.getOrPutString(sema.gpa, "root", .no_embedded_nulls),
        .{ .declared = .{ .source_zir_id = file_index, .decl_inst = .main_struct_inst } },
        .none,
        0,
        .auto,
        false,
        false,
    );
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

fn lowerModule(sema: *Sema, canonical: []const u8, bytes: [:0]const u8) Error!InternPool.Index {
    const session = sema.session.?;
    var tree = try std.zig.Ast.parse(sema.gpa, bytes, .zig);
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

    const root_type = try sema.intern_pool.getDeclaredStructType(
        try sema.moduleTypeName(canonical),
        .{ .declared = .{ .source_zir_id = file_index, .decl_inst = .main_struct_inst } },
        .none,
        @intCast(root_decl.field_names.len),
        .auto,
        any_field_aligns,
        any_comptime_fields,
    );
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
    const val = try sema.coerceValueToType(try sema.resolveInst(ref), enum_ty, @tagName(decl));
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

        .calling_convention_c => {
            const cc_ty = try sema.getStdLangType(.CallingConvention);
            const name = try sema.intern_pool.getOrPutString(sema.gpa, "c", .no_embedded_nulls);
            return (try sema.containerDeclByName(cc_ty, name)) orelse {
                return sema.fail(sema.block, sema.block.nodeOffset(.zero), "std.lang is corrupt: CallingConvention.c", .{});
            };
        },
        .calling_convention_inline => return .{ .index = try sema.callConvValue(.@"inline") },
    };
    return .{ .index = try sema.getStdLangType(std_lang_type) };
}

fn evalTypeInfo(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
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
            const layout_val = (try sema.enumValueFieldIndex(layout_ty, @intFromEnum(uf.layout))).?;
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
            const layout_val = (try sema.enumValueFieldIndex(layout_ty, @intFromEnum(layout))).?;
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
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.MultiOp, pl_node.payload_index);
    const operands = sema.zir.refSlice(extra.end, extra.data.operands_len);
    assert(operands.len >= 1);

    const ip = sema.intern_pool;
    const result_ty = try sema.resolveDestType(operands[0], "array_init");
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
        const elem_ty = try sema.arrayInitElemType(array_key, i, "array_init");
        const coerced = try sema.coerceValueToType(elem, elem_ty, "array_init");
        buf[i] = coerced.index;
    }

    return try ip.internAggregate(.{ .ty = array_ty, .storage = .{ .elems = buf } });
}

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
            return sema.fail(sema.block, sema.block.nodeOffset(.zero), "{s}: element {d} is out of range for a {d}-field tuple", .{ op_name, index, tt.types.len });
        },
        else => {
            return sema.fail(sema.block, sema.block.nodeOffset(.zero), "{s}: type does not support array-init syntax", .{op_name});
        },
    }
}

fn evalArrayInitElemType(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const bin = sema.zir.instructions.items(.data)[@intFromEnum(inst)].bin;
    const maybe_wrapped = try sema.resolveDestType(bin.lhs, "array_init_elem_type");
    // A generic (`anytype`) aggregate has a generic element type; the element resolves on coercion.
    if (maybe_wrapped == .generic_poison_type) return .{ .index = .generic_poison_type };
    // Peel an optional/error-union result type (`?[N]T`, `E![N]T`) to the aggregate it wraps.
    const indexable_ty = sema.optEuBaseType(maybe_wrapped);
    const index: usize = @intFromEnum(bin.rhs);
    const elem_ty = try sema.arrayInitElemType(
        sema.intern_pool.indexToKey(indexable_ty),
        index,
        "array_init_elem_type",
    );
    return .{ .index = elem_ty };
}

fn evalElemType(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);
    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    const ptr_ty = sema.optEuBaseType(try sema.resolveDestType(un_node.operand, "elem_type"));
    return .{ .index = sema.intern_pool.indexToKey(ptr_ty).ptr_type.child };
}

fn evalSplatOpResultType(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);
    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    const ty = sema.optEuBaseType(try sema.resolveDestType(un_node.operand, "@splat"));
    return .{ .index = (try sema.expectArrayOrVector(ty)).child };
}

fn evalSplat(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    const bin = sema.binData(inst);
    const dest_ty = sema.optEuBaseType(try sema.resolveDestType(bin.lhs, "@splat"));
    const info = try sema.expectArrayOrVector(dest_ty);
    const scalar = try sema.coerceValueToType(try sema.resolveInst(bin.rhs), info.child, "@splat");
    return .{ .index = try ip.internAggregate(.{ .ty = dest_ty, .storage = .{ .repeated_elem = scalar.index } }) };
}

fn evalShuffle(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.Shuffle, pl_node.payload_index).data;

    const elem_ty = try sema.resolveDestType(extra.elem_type, "@shuffle");
    if (!isVectorElemType(ip, elem_ty)) {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "@shuffle: expected integer, float, bool, or pointer for the element type", .{});
    }
    const mask = try sema.resolveInst(extra.mask);
    const mask_len = (indexableInfo(ip, Value.typeOf(mask, ip).index) orelse {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "@shuffle: expected vector or array for the mask", .{});
    }).len;
    const av = try sema.resolveInst(extra.a);
    const bv = try sema.resolveInst(extra.b);
    const a_len = (indexableInfo(ip, Value.typeOf(av, ip).index) orelse return sema.failShuffleOperand(elem_ty)).len;
    const b_len = (indexableInfo(ip, Value.typeOf(bv, ip).index) orelse return sema.failShuffleOperand(elem_ty)).len;

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

fn expectArrayOrVector(sema: *Sema, ty: InternPool.Index) Error!IndexableInfo {
    return indexableInfo(sema.intern_pool, ty) orelse {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "expected array or vector type, found '{f}'", .{Type.fromIndex(ty).fmt(sema.intern_pool)});
    };
}

fn evalValidateArrayInitTy(sema: *Sema, inst: Zir.Inst.Index, comptime is_result_ty: bool) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    const data = sema.zir.extraData(Zir.Inst.ArrayInit, pl_node.payload_index).data;
    const ty = try sema.resolveDestType(data.ty, "array init");
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
    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.ArrayInitRefTy, pl_node.payload_index).data;
    const maybe_wrapped_ptr_ty = try sema.resolveDestType(extra.ptr_ty, "array init");
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
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const un_tok = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_tok;
    const ty_operand = try sema.resolveDestType(un_tok.operand, "address-of");
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
    const ptr_ty = ip.indexToKey(sema.optEuBaseType(try sema.resolveDestType(bin.lhs, "coerce_ptr_elem_ty"))).ptr_type;
    const elem_ty = ptr_ty.child;
    const val_ty = Value.typeOf(uncoerced, ip).index;
    switch (ptr_ty.flags.size) {
        .one => {
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
                    return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "expected array of '{f}', found '{f}'", .{ Type.fromIndex(elem_ty).fmt(ip), Type.fromIndex(val_ty).fmt(ip) });
                },
            };
            const want_ty = try ip.internArrayType(.{ .len = len, .child = elem_ty, .sentinel = ptr_ty.sentinel });
            return try sema.coerceValueToType(uncoerced, want_ty, "coerce_ptr_elem_ty");
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
        const field_type = try sema.resolveDestType(zir_field_ty, "tuple field type");
        ty.* = field_type;
        val.* = if (zir_field_init != .none)
            (try sema.coerceValueToType(try sema.resolveInst(zir_field_init), field_type, "tuple field default")).index
        else
            .none;
    }

    return .{ .index = try sema.intern_pool.internTupleType(types, vals) };
}

fn evalStructDecl(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const struct_decl = sema.zir.getStructDecl(inst);
    const name = switch (struct_decl.name_strategy) {
        .parent => sema.type_name_ctx,
        .anon, .func, .dbg_var => blk: {
            const ctx = sema.intern_pool.stringSlice(sema.type_name_ctx);
            const text = try std.fmt.allocPrint(sema.gpa, "{s}__struct_{d}", .{ ctx, @intFromEnum(inst) });
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

    return .{
        .index = try sema.intern_pool.getDeclaredStructType(name, .{ .declared = .{
            .source_zir_id = sema.current_zir_id,
            .decl_inst = inst,
            .captures = captures,
        } }, sema.this_type, @intCast(struct_decl.field_names.len), struct_decl.layout, any_field_aligns, any_comptime_fields),
    };
}

fn evalEnumDecl(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const enum_decl = sema.zir.getEnumDecl(inst);
    const name = switch (enum_decl.name_strategy) {
        .parent => sema.type_name_ctx,
        .anon, .func, .dbg_var => blk: {
            const ctx = sema.intern_pool.stringSlice(sema.type_name_ctx);
            const text = try std.fmt.allocPrint(sema.gpa, "{s}__enum_{d}", .{ ctx, @intFromEnum(inst) });
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
        sema.this_type,
        @intCast(enum_decl.field_names.len),
        enum_decl.nonexhaustive or enum_decl.tag_type_body != null,
        if (enum_decl.tag_type_body != null) .explicit else .auto,
    );
    switch (result) {
        .existing => |enum_ty| return .{ .index = enum_ty },
        .wip => |wip| {
            _ = try sema.resolveEnumFields(wip.index);
            return .{ .index = wip.index };
        },
    }
}

fn evalUnionDecl(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const union_decl = sema.zir.getUnionDecl(inst);
    const name = switch (union_decl.name_strategy) {
        .parent => sema.type_name_ctx,
        .anon, .func, .dbg_var => blk: {
            const ctx = sema.intern_pool.stringSlice(sema.type_name_ctx);
            const text = try std.fmt.allocPrint(sema.gpa, "{s}__union_{d}", .{ ctx, @intFromEnum(inst) });
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
        sema.this_type,
        @intCast(union_decl.field_names.len),
        layout,
        union_decl.field_align_body_lens != null,
        tag_usage,
    );
    return .{ .index = switch (result) {
        .existing => |union_ty| union_ty,
        .wip => |wip| wip.index,
    } };
}

fn evalOpaqueDecl(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const opaque_decl = sema.zir.getOpaqueDecl(inst);
    const name = switch (opaque_decl.name_strategy) {
        .parent => sema.type_name_ctx,
        .anon, .func, .dbg_var => blk: {
            const ctx = sema.intern_pool.stringSlice(sema.type_name_ctx);
            const text = try std.fmt.allocPrint(sema.gpa, "{s}__opaque_{d}", .{ ctx, @intFromEnum(inst) });
            defer sema.gpa.free(text);
            break :blk try sema.intern_pool.getOrPutString(sema.gpa, text, .no_embedded_nulls);
        },
    };

    const captures = try sema.resolveCaptures(opaque_decl.captures);
    defer sema.gpa.free(captures);

    return .{ .index = try sema.intern_pool.getDeclaredOpaqueType(
        name,
        .{ .declared = .{
            .source_zir_id = sema.current_zir_id,
            .decl_inst = inst,
            .captures = captures,
        } },
        sema.this_type,
    ) };
}

fn resolveCaptures(sema: *Sema, zir_captures: []const Zir.Inst.Capture) Error![]const InternPool.Index {
    if (zir_captures.len == 0) return &.{};
    const caps = try sema.gpa.alloc(InternPool.Index, zir_captures.len);
    errdefer sema.gpa.free(caps);
    for (zir_captures, caps) |zc, *c| {
        c.* = switch (zc.unwrap()) {
            .instruction => |i| (try sema.resolveInst(i.toRef())).index,
            .instruction_load => |i| (try sema.loadValue(try sema.resolveInst(i.toRef()))).index,
            .nested => |idx| sema.intern_pool.indexToKey(sema.this_type).struct_type.captures()[idx],
            .decl_val, .decl_ref => {
                return sema.fail(sema.block, sema.block.nodeOffset(.zero), "closure capture: decl captures are not supported", .{});
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
    saved_this: InternPool.Index,
    decl_inst: Zir.Inst.Index,
    old_inst_map: std.AutoHashMapUnmanaged(Zir.Inst.Index, Value),

    fn restore(cf: ContainerFrame, sema: *Sema) void {
        sema.inst_map.deinit(sema.gpa);
        sema.inst_map = cf.old_inst_map;
        sema.this_type = cf.saved_this;
        cf.zir.restore(sema);
    }
};

fn enterContainer(sema: *Sema, container_ty: InternPool.Index, ctx: []const u8) Error!ContainerFrame {
    const owner = switch (sema.intern_pool.indexToKey(container_ty)) {
        .enum_type => |et| if (et.generatedUnion() != .none) et.generatedUnion() else container_ty,
        else => container_ty,
    };
    const ns = sema.containerNamespace(owner).?;
    const zir = try sema.enterSourceZir(ns.source_zir_id, ctx);
    const saved_this = sema.this_type;
    sema.this_type = owner;
    const old_inst_map = sema.inst_map;
    sema.inst_map = .empty;
    return .{ .zir = zir, .saved_this = saved_this, .decl_inst = ns.decl_inst, .old_inst_map = old_inst_map };
}

fn containerTypeSrc(sema: *Sema, container_ty: InternPool.Index) LazySrcLoc {
    const id: InternPool.Key.ContainerType = switch (sema.intern_pool.indexToKey(container_ty)) {
        .struct_type => |st| st,
        .union_type => |ut| ut,
        .enum_type => |et| et,
        else => return sema.block.nodeOffset(.zero),
    };
    return .{ .base_node_inst = id.declInst(), .offset = .{ .node_offset = .zero } };
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
    const cf = try sema.enterContainer(struct_ty, "struct field");
    defer cf.restore(sema);
    if (sema.zir.instructions.items(.tag)[@intFromEnum(cf.decl_inst)] == .struct_init_anon)
        return try sema.anonStructFieldByName(cf.decl_inst, name);
    var it = sema.zir.getStructDecl(cf.decl_inst).iterateFields();
    while (it.next()) |field| {
        if ((try ip.getOrPutString(sema.gpa, sema.zir.nullTerminatedString(field.name), .no_embedded_nulls)) == name) {
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
    const cf = try sema.enterContainer(struct_ty, "struct field default");
    defer cf.restore(sema);
    if (sema.zir.instructions.items(.tag)[@intFromEnum(cf.decl_inst)] == .struct_init_anon) return .none;
    var it = sema.zir.getStructDecl(cf.decl_inst).iterateFields();
    while (it.next()) |field| {
        if ((try ip.getOrPutString(sema.gpa, sema.zir.nullTerminatedString(field.name), .no_embedded_nulls)) != name) continue;
        const body = field.default_body orelse return .none;
        const ty = (try sema.resolveInlineBody(field.type_body, cf.decl_inst)).index;
        try sema.inst_map.put(sema.gpa, cf.decl_inst, .{ .index = ty });
        const raw = sema.resolveInlineBody(body, cf.decl_inst);
        _ = sema.inst_map.remove(cf.decl_inst);
        return (try sema.coerceValueToType(try raw, ty, "field default")).index;
    }
    return .none;
}

fn anonStructFieldByName(sema: *Sema, decl_inst: Zir.Inst.Index, name: InternPool.NullTerminatedString) Error!?FieldInfo {
    const ip = sema.intern_pool;
    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(decl_inst)].pl_node;
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
    const cf = try sema.enterContainer(union_ty, "union field");
    defer cf.restore(sema);
    var it = sema.zir.getUnionDecl(cf.decl_inst).iterateFields();
    while (it.next()) |field| {
        if ((try ip.getOrPutString(sema.gpa, sema.zir.nullTerminatedString(field.name), .no_embedded_nulls)) == name) {
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

fn fieldAlignBytes(sema: *Sema, align_body: ?[]const Zir.Inst.Index, decl_inst: Zir.Inst.Index) Error!?u64 {
    const body = align_body orelse return null;
    return try sema.resolveUsizeInt(try sema.resolveInlineBody(body, decl_inst), "field alignment");
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

fn callConvValue(sema: *Sema, cc: std.lang.CallingConvention) Error!InternPool.Index {
    const ip = sema.intern_pool;
    const cc_ty = try sema.getStdLangType(.CallingConvention);
    const tag_enum = try sema.unionTagEnumType(cc_ty);
    switch (cc) {
        inline else => |payload, tag| {
            if (@TypeOf(payload) != void) {
                return sema.fail(sema.block, sema.block.nodeOffset(.zero), "@typeInfo: calling convention '{s}' is not modelled", .{@tagName(tag)});
            }
            const idx = (try sema.enumFieldIndex(tag_enum, try ip.getOrPutString(sema.gpa, @tagName(tag), .no_embedded_nulls))).?;
            const tag_val = (try sema.enumValueFieldIndex(tag_enum, idx)).?;
            return try ip.internUnion(.{ .ty = cc_ty, .tag = tag_val.index, .val = .void_value });
        },
    }
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
    const cf = try sema.enterContainer(struct_ty, "struct field name");
    defer cf.restore(sema);
    if (sema.zir.instructions.items(.tag)[@intFromEnum(cf.decl_inst)] == .struct_init_anon) {
        const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(cf.decl_inst)].pl_node;
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
    const cf = try sema.enterContainer(union_ty, "union field count");
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
    const cf = try sema.enterContainer(union_ty, "union field name");
    defer cf.restore(sema);
    var it = sema.zir.getUnionDecl(cf.decl_inst).iterateFields();
    while (it.next()) |field| {
        if (field.idx == index)
            return try ip.getOrPutString(sema.gpa, sema.zir.nullTerminatedString(field.name), .no_embedded_nulls);
    }
    return null;
}

fn failUntaggedUnionCmp(sema: *Sema) Error {
    return sema.fail(sema.block, sema.block.nodeOffset(.zero), "comparison of union and enum literal is only valid for tagged union types", .{});
}

fn cmpUnionTagNoValue(sema: *Sema, union_ty: InternPool.Index, tag_name: InternPool.NullTerminatedString, op: std.math.CompareOperator) Error!?Value {
    try sema.resolveUnionFields(union_ty);
    if (sema.intern_pool.unionFields(union_ty).tag_usage != .tagged) return sema.failUntaggedUnionCmp();
    if (op != .eq and op != .neq) return null;
    const field = (try sema.unionFieldByName(union_ty, tag_name)) orelse return null;
    if (!try sema.isNoPossibleValue(field.ty)) return null;
    return .{ .index = if (op == .eq) .bool_false else .bool_true };
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
            const cf = try sema.enterContainer(union_ty, "union tag type");
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
    const result = try ip.getDeclaredEnumType(ip.typeName(union_ty), .{ .generated_union_tag = union_ty }, .none, fields_len, false, .auto);
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
    const cf = try sema.enterContainer(enum_ty, "enum field count");
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
    const cf = try sema.enterContainer(enum_ty, "enum field");
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
            break :blk sema.intAsI128(raw.index) orelse {
                return sema.fail(sema.block, sema.block.nodeOffset(.zero), "enum: tag value is not an integer", .{});
            };
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
            const cf = try sema.enterContainer(enum_ty, "enum tag type");
            defer cf.restore(sema);
            const decl = sema.zir.getUnionDecl(cf.decl_inst);
            return if (decl.kind == .tagged_enum_explicit)
                (try sema.resolveInlineBody(decl.arg_type_body.?, cf.decl_inst)).index
            else
                try sema.enumIntTagType(@intCast(decl.field_names.len));
        },
        .declared => {
            const cf = try sema.enterContainer(enum_ty, "enum tag type");
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
    const cf = try sema.enterContainer(enum_ty, "enum mode");
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
    const i64v = std.math.cast(i64, value) orelse {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "enum: tag value out of supported range", .{});
    };
    const raw = try sema.intern_pool.internInt(.{ .ty = .comptime_int_type, .storage = .{ .i64 = i64v } });
    return (try sema.coerceValueToType(.{ .index = raw }, tag_ty, "enum tag")).index;
}

fn enumFieldIndex(sema: *Sema, enum_ty: InternPool.Index, name: InternPool.NullTerminatedString) Error!?u32 {
    return if (try sema.enumFieldScan(enum_ty, .{ .name = name })) |m| m.index else null;
}

fn enumTagFieldIndex(sema: *Sema, enum_ty: InternPool.Index, tag: Value) Error!?u32 {
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
    const int_coerced = try sema.coerceValueToType(int, int_tag_ty, "enum tag");
    return fields.tagValueIndex(ip, int_coerced.index) != null;
}

fn evalEnumFromInt(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
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
    const int_coerced = try sema.coerceValueToType(operand, int_tag_ty, "enum tag");
    return .{ .index = try ip.internEnumTag(.{ .ty = dest_ty, .int = int_coerced.index }) };
}

fn evalIntFromBool(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const operand = try sema.resolveInst(sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node.operand);
    const u1_type = try sema.intern_pool.get(.{ .int_type = .{ .signedness = .unsigned, .bits = 1 } });
    return .{ .index = try sema.intern_pool.internInt(.{
        .ty = u1_type,
        .storage = .{ .u64 = @intFromBool(operand.index == .bool_true) },
    }) };
}

fn evalEnumLiteral(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const bytes = sema.zir.instructions.items(.data)[@intFromEnum(inst)].str_tok.get(sema.zir);
    const name = try sema.intern_pool.getOrPutString(sema.gpa, bytes, .no_embedded_nulls);
    return .{ .index = try sema.intern_pool.get(.{ .enum_literal = name }) };
}

fn evalDeclLiteral(sema: *Sema, inst: Zir.Inst.Index, comptime do_coerce: bool) Error!?Value {
    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
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
    return if (do_coerce) try sema.coerceValueToType(uncoerced, orig_ty, "decl literal") else uncoerced;
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
            return sema.fail(sema.block, sema.block.nodeOffset(.zero), "decl literal: result type is not a container with members", .{});
        },
    }
}

fn evalIntFromEnum(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    const operand = try sema.resolveInst(un_node.operand);
    const key = sema.intern_pool.indexToKey(operand.index);
    if (key != .enum_tag) {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "@intFromEnum: operand is not an enum value", .{});
    }
    return .{ .index = key.enum_tag.int };
}

fn evalTagName(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    const operand = try sema.resolveInst(un_node.operand);
    const tag: InternPool.Key.EnumTag = switch (ip.indexToKey(operand.index)) {
        .enum_tag => |et| et,
        .un => |uv| blk: {
            try sema.resolveUnionFields(uv.ty);
            if (ip.unionFields(uv.ty).tag_usage != .tagged) {
                return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "union '{f}' is untagged", .{Type.fromIndex(uv.ty).fmt(ip)});
            }
            break :blk ip.indexToKey(uv.tag).enum_tag;
        },
        else => {
            return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "expected enum or union; found '{f}'", .{operand.typeOf(ip).fmt(ip)});
        },
    };
    const field_index = (try sema.enumTagFieldIndex(tag.ty, .{ .index = tag.int })).?;
    const name = (try sema.enumFieldName(tag.ty, field_index)).?;
    return try sema.internStringLiteral(ip.stringSlice(name));
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
    if (zir.instructions.items(.tag)[@intFromEnum(decl_inst)] == .struct_init_anon) {
        const pl_node = zir.instructions.items(.data)[@intFromEnum(decl_inst)].pl_node;
        return zir.extraData(Zir.Inst.StructInitAnon, pl_node.payload_index).data.fields_len;
    }
    return @intCast(zir.getStructDecl(decl_inst).field_names.len);
}

fn evalFieldPtr(sema: *Sema, inst: Zir.Inst.Index, comptime initializing: bool) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);
    const ip = sema.intern_pool;
    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
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
        if (try sema.containerDeclByName(container.index, name)) |decl_val|
            return try sema.materializeConstPtr(decl_val);
        return sema.failBadMemberAccess(container.index, name);
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

fn getNamespaceIndex(sema: *Sema, ty: InternPool.Index) Error!?InternPool.NamespaceIndex {
    const ip = sema.intern_pool;
    if (ip.typeNamespace(ty).unwrap()) |ns| return ns;
    const cn = sema.containerNamespace(ty) orelse return null;
    const ns = try ip.createNamespace(sema.gpa, .none);
    const ns_ptr = ip.namespacePtr(ns);
    ns_ptr.owner_type = ty;
    ns_ptr.file_scope = sema.namespaceFileScope(cn.source_zir_id);
    ip.setNamespace(ty, ns);
    try sema.scanNamespace(ns, ty);
    return ns;
}

fn namespaceFileScope(sema: *Sema, source_zir_id: u32) InternPool.OptionalFileIndex {
    const session = sema.session orelse return .none;
    if (source_zir_id >= session.files.items.len) return .none;
    if (session.files.items[source_zir_id].sub_file_path == null) return .none;
    return InternPool.OptionalFileIndex.init(@enumFromInt(source_zir_id));
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
    if (ip.getNav(nav_idx).resolved) |r| return .{ .index = r.value };
    const analysis = ip.getNav(nav_idx).analysis.?;
    const container_ty = ip.namespacePtr(analysis.namespace).owner_type;
    const cn = sema.containerNamespace(container_ty).?;
    const frame = try sema.enterSourceZir(cn.source_zir_id, "analyze nav");
    defer frame.restore(sema);
    const decl_inst = analysis.zir_index;
    const unwrapped = sema.zir.getDeclaration(decl_inst);
    const value_body = unwrapped.value_body orelse
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "decl '{s}': no value_body (extern decl)", .{ip.stringSlice(ip.getNav(nav_idx).name)});

    const saved_namespace = sema.namespace;
    sema.namespace = analysis.namespace;
    defer sema.namespace = saved_namespace;
    const saved_this = sema.this_type;
    sema.this_type = container_ty;
    defer sema.this_type = saved_this;
    const saved_ctx = sema.type_name_ctx;
    sema.type_name_ctx = ip.getNav(nav_idx).fqn;
    defer sema.type_name_ctx = saved_ctx;
    const saved_params = sema.block.params;
    sema.block.params = .empty;
    defer {
        sema.block.params.deinit(sema.gpa);
        sema.block.params = saved_params;
    }
    const old_inst_map = sema.inst_map;
    sema.inst_map = .empty;
    defer {
        sema.inst_map.deinit(sema.gpa);
        sema.inst_map = old_inst_map;
    }
    const declared_type: ?InternPool.Index = if (unwrapped.type_body) |tb| blk: {
        const t = (try sema.resolveInlineBody(tb, decl_inst)).index;
        try sema.inst_map.put(sema.gpa, decl_inst, .{ .index = t });
        break :blk t;
    } else null;
    const raw_value = try sema.resolveInlineBody(value_body, decl_inst);
    const value = if (declared_type) |dest_ty| try sema.coerceValueToType(raw_value, dest_ty, "decl") else raw_value;

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
    return value;
}

fn containerDeclByName(sema: *Sema, container_ty: InternPool.Index, name: InternPool.NullTerminatedString) Error!?Value {
    const ns = (try sema.getNamespaceIndex(container_ty)) orelse return null;
    const nav = (try sema.namespaceLookup(ns, name)) orelse return null;
    return try sema.analyzeNavVal(nav);
}

fn containerDeclNav(sema: *Sema, container_ty: InternPool.Index, name: InternPool.NullTerminatedString) Error!?Value {
    const ns = (try sema.getNamespaceIndex(container_ty)) orelse return null;
    const lookup = sema.lookupInNamespace(ns, name) orelse return null;
    return try sema.analyzeNavVal(lookup.nav);
}

fn evalFieldPtrLoad(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);
    const ip = sema.intern_pool;
    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.Field, pl_node.payload_index).data;
    const name = try ip.getOrPutString(sema.gpa, sema.zir.nullTerminatedString(extra.field_name_start), .no_embedded_nulls);
    const object = try sema.loadValue(try sema.resolveInst(extra.lhs));
    return sema.fieldPtrLoad(object, name);
}

fn fieldPtrLoad(sema: *Sema, object: Value, name: InternPool.NullTerminatedString) Error!?Value {
    const ip = sema.intern_pool;

    switch (ip.indexToKey(object.index)) {
        .struct_type, .union_type, .enum_type, .opaque_type => return try sema.fieldValOnType(object.index, name),
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
    assert(@intFromEnum(inst) < sema.zir.instructions.len);
    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.FieldNamed, pl_node.payload_index).data;
    const field_name = try sema.resolveConstStringIntern(extra.field_name);
    const object = try sema.loadValue(try sema.resolveInst(extra.lhs));
    return sema.fieldPtrLoad(object, field_name);
}

fn evalFieldPtrNamed(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);
    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.FieldNamed, pl_node.payload_index).data;
    const field_name = try sema.resolveConstStringIntern(extra.field_name);
    const object_ptr = try sema.resolveInst(extra.lhs);
    return sema.fieldPtr(object_ptr, field_name, false);
}

fn resolveConstStringIntern(sema: *Sema, ref: Zir.Inst.Ref) Error!InternPool.NullTerminatedString {
    const ip = sema.intern_pool;
    var agg = try sema.resolveInst(ref);
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
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "expected a comptime string", .{});
    }
    const len: usize = @intCast(slice_len orelse arr.array_type.len);
    const bytes = try sema.gpa.alloc(u8, len);
    defer sema.gpa.free(bytes);
    for (bytes, 0..) |*b, i| {
        const elem = try ip.aggregateElementAt(key.aggregate, start + i);
        b.* = @intCast(ip.indexToKey(elem).int.storage.u64);
    }
    return try ip.getOrPutString(sema.gpa, bytes, .no_embedded_nulls);
}

fn evalCompileError(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    const msg = try sema.resolveConstStringIntern(un_node.operand);
    return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "{s}", .{sema.intern_pool.stringSlice(msg)});
}

fn evalSetEvalBranchQuota(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    const quota = try sema.resolveInt(try sema.resolveInst(un_node.operand), .u32_type, "@setEvalBranchQuota");
    sema.branch_quota = @max(sema.branch_quota, @as(u32, @intCast(quota)));
    return null;
}

fn evalSetRuntimeSafety(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    _ = try sema.coerceValueToType(try sema.resolveInst(un_node.operand), .bool_type, "@setRuntimeSafety");
    return null;
}

fn evalTypeName(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    const ty = try sema.resolveDestType(un_node.operand, "@typeName");
    var name: std.Io.Writer.Allocating = .init(sema.gpa);
    defer name.deinit();
    try Type.print(Type.fromIndex(ty), sema.intern_pool, &name.writer);
    return try sema.internStringLiteral(name.written());
}

fn evalErrorName(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    const operand = try sema.coerceValueToType(try sema.resolveInst(un_node.operand), .anyerror_type, "@errorName");
    const name = ip.indexToKey(operand.index).err.name;
    return try sema.internStringLiteral(ip.stringSlice(name));
}

fn evalUnionInit(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.UnionInit, pl_node.payload_index).data;
    const union_ty = try sema.resolveDestType(extra.union_type, "@unionInit");
    if (ip.indexToKey(union_ty) != .union_type) {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "@unionInit: expected union type, found '{f}'", .{Type.fromIndex(union_ty).fmt(ip)});
    }
    const field_name = try sema.resolveConstStringIntern(extra.field_name);
    const field = (try sema.unionFieldByName(union_ty, field_name)) orelse
        return sema.failBadUnionFieldAccess(union_ty, field_name);
    const payload = try sema.coerceValueToType(try sema.resolveInst(extra.init), field.ty, "@unionInit");
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
    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.FieldTypeRef, pl_node.payload_index).data;
    const aggregate_ty = sema.optEuBaseType(try sema.resolveDestType(extra.container_type, "field type"));
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
    const lhs_ty = try sema.resolveDestType(bin.lhs, "error set merge");
    const rhs_ty = try sema.resolveDestType(bin.rhs, "error set merge");
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
    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    const bin = sema.zir.extraData(Zir.Inst.Bin, pl_node.payload_index).data;
    const ty = try sema.resolveDestType(bin.lhs, "@hasField");
    const field_name = try sema.resolveConstStringIntern(bin.rhs);
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
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "type '{f}' does not support '@hasField'", .{Type.fromIndex(ty).fmt(ip)});
    };
    return .{ .index = if (has_field) .bool_true else .bool_false };
}

fn evalHasDecl(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    const bin = sema.zir.extraData(Zir.Inst.Bin, pl_node.payload_index).data;
    const container_type = try sema.resolveDestType(bin.lhs, "@hasDecl");
    const decl_name = try sema.resolveConstStringIntern(bin.rhs);
    if (sema.containerNamespace(container_type) == null) {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "expected struct, enum, union, or opaque; found '{f}'", .{Type.fromIndex(container_type).fmt(sema.intern_pool)});
    }
    return .{ .index = if (try sema.containerHasDecl(container_type, decl_name)) .bool_true else .bool_false };
}

fn containerHasDecl(sema: *Sema, container_ty: InternPool.Index, name: InternPool.NullTerminatedString) Error!bool {
    const ns = sema.containerNamespace(container_ty) orelse return false;
    const frame = try sema.enterSourceZir(ns.source_zir_id, "container decl");
    defer frame.restore(sema);
    for (sema.zir.typeDecls(ns.decl_inst)) |decl_inst| {
        const unwrapped = sema.zir.getDeclaration(decl_inst);
        if (unwrapped.name == .empty) continue;
        if ((try sema.intern_pool.getOrPutString(sema.gpa, sema.zir.nullTerminatedString(unwrapped.name), .no_embedded_nulls)) == name) return true;
    }
    return false;
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

fn storeElement(sema: *Sema, ptr: InternPool.Key.Ptr, value: Value) Error!void {
    const ip = sema.intern_pool;
    const f = switch (ptr.base_addr) {
        .field, .arr_elem => |f| f,
        else => unreachable,
    };
    const base_ptr = ip.indexToKey(f.base).ptr;
    const agg_ty = ip.indexToKey(base_ptr.ty).ptr_type.child;
    if (ip.indexToKey(agg_ty) == .union_type) {
        const tag_enum = try sema.unionTagEnumType(agg_ty);
        const tag = (try sema.enumValueFieldIndex(tag_enum, @intCast(f.index))).?;
        const new_union = Value{ .index = try ip.internUnion(.{ .ty = agg_ty, .tag = tag.index, .val = value.index }) };
        try sema.storePointee(base_ptr, new_union);
        return;
    }
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

fn storePointee(sema: *Sema, ptr: InternPool.Key.Ptr, value: Value) Error!void {
    const ip = sema.intern_pool;
    switch (ptr.base_addr) {
        .comptime_alloc => (try sema.lookupComptimeAlloc(ptr)).val = value,
        .comptime_field => |field_val| {
            if (value.index != field_val) {
                return sema.fail(sema.block, sema.block.nodeOffset(.zero), "value stored in comptime field does not match the comptime field value", .{});
            }
        },
        .field, .arr_elem => try sema.storeElement(ptr, value),
        .opt_payload => |base| {
            const opt_ty = ip.indexToKey(ip.indexToKey(base).ptr.ty).ptr_type.child;
            const new_opt = Value{ .index = try ip.internOpt(.{ .ty = opt_ty, .val = value.index }) };
            try sema.storePointee(ip.indexToKey(base).ptr, new_opt);
        },
        .eu_payload => |base| {
            const eu_ty = ip.indexToKey(ip.indexToKey(base).ptr.ty).ptr_type.child;
            const new_eu = Value{ .index = try ip.internErrorUnion(.{ .ty = eu_ty, .val = .{ .payload = value.index } }) };
            try sema.storePointee(ip.indexToKey(base).ptr, new_eu);
        },
        .nav, .uav => {
            return sema.fail(sema.block, sema.block.nodeOffset(.zero), "unable to evaluate comptime expression: store through a pointer to a declaration", .{});
        },
        .int => {
            return sema.fail(sema.block, sema.block.nodeOffset(.zero), "unable to evaluate comptime expression: store through an integer-address pointer", .{});
        },
    }
}

fn evalOptEuBasePtrInit(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);
    const ip = sema.intern_pool;
    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    var base_ptr = try sema.resolveInst(un_node.operand);
    while (true) switch (ip.indexToKey(ip.indexToKey(base_ptr.typeOf(ip).toIndex()).ptr_type.child)) {
        .opt_type => base_ptr = try sema.optPayloadPtr(base_ptr, true),
        .error_union_type => base_ptr = try sema.errUnionPayloadPtr(base_ptr, true),
        else => break,
    };
    return base_ptr;
}

fn evalValidatePtrStructInit(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);
    const datas = sema.zir.instructions.items(.data);
    const extra = sema.zir.extraData(Zir.Inst.Block, datas[@intFromEnum(inst)].pl_node.payload_index);
    const body = sema.zir.bodySlice(extra.end, extra.data.body_len);
    if (body.len == 0) return null;

    const ip = sema.intern_pool;
    const first = sema.zir.extraData(Zir.Inst.Field, datas[@intFromEnum(body[0])].pl_node.payload_index).data;
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
        const fp = sema.zir.extraData(Zir.Inst.Field, datas[@intFromEnum(field_ptr)].pl_node.payload_index).data;
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
        const alloc = try sema.lookupComptimeAlloc(ip.indexToKey(object_ptr.index).ptr);
        alloc.val = try sema.setAggregateElement(alloc.val, struct_ty, i, .{ .index = default });
    }
    return null;
}

fn evalValidateStructInitTy(sema: *Sema, inst: Zir.Inst.Index, comptime is_result_ty: bool) Error!?Value {
    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    const ty = try sema.resolveDestType(un_node.operand, "struct init");
    const struct_ty = if (is_result_ty) Type.fromIndex(ty).optEuBaseType(sema.intern_pool).index else ty;
    switch (sema.intern_pool.indexToKey(struct_ty)) {
        .struct_type, .union_type => return null,
        else => {
            return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "struct init: type does not support struct initialization syntax", .{});
        },
    }
}

fn evalStructInitFieldType(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const datas = sema.zir.instructions.items(.data);
    const ft = sema.zir.extraData(Zir.Inst.FieldType, datas[@intFromEnum(inst)].pl_node.payload_index).data;
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

fn evalStructInit(sema: *Sema, inst: Zir.Inst.Index, comptime is_ref: bool) Error!?Value {
    const ip = sema.intern_pool;
    const datas = sema.zir.instructions.items(.data);
    const extra = sema.zir.extraData(Zir.Inst.StructInit, datas[@intFromEnum(inst)].pl_node.payload_index);

    const first = sema.zir.extraData(Zir.Inst.StructInit.Item, extra.end).data;
    const first_ft = sema.zir.extraData(Zir.Inst.FieldType, datas[@intFromEnum(first.field_type)].pl_node.payload_index).data;
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
    const elems = try sema.gpa.alloc(InternPool.Index, count);
    defer sema.gpa.free(elems);
    @memset(elems, .none);

    var extra_index = extra.end;
    for (0..extra.data.fields_len) |_| {
        const item = sema.zir.extraData(Zir.Inst.StructInit.Item, extra_index);
        extra_index = item.end;
        const ft = sema.zir.extraData(Zir.Inst.FieldType, datas[@intFromEnum(item.data.field_type)].pl_node.payload_index).data;
        const name = try ip.getOrPutString(sema.gpa, sema.zir.nullTerminatedString(ft.name_start), .no_embedded_nulls);
        const field = (try sema.structFieldByName(struct_ty, name)) orelse
            return sema.failBadStructFieldAccess(struct_ty, name);
        const raw = try sema.resolveInst(item.data.init);
        elems[field.index] = (try sema.coerceValueToType(raw, field.ty, "struct field")).index;
    }

    return try sema.finishStructInit(struct_ty, result_ty, elems, is_ref);
}

fn evalStructInitUnion(sema: *Sema, union_ty: InternPool.Index, result_ty: InternPool.Index, inst: Zir.Inst.Index, comptime is_ref: bool) Error!Value {
    const ip = sema.intern_pool;
    const datas = sema.zir.instructions.items(.data);
    const extra = sema.zir.extraData(Zir.Inst.StructInit, datas[@intFromEnum(inst)].pl_node.payload_index);
    if (extra.data.fields_len != 1) {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "union initialization expects exactly one field", .{});
    }

    const item = sema.zir.extraData(Zir.Inst.StructInit.Item, extra.end).data;
    const ft = sema.zir.extraData(Zir.Inst.FieldType, datas[@intFromEnum(item.field_type)].pl_node.payload_index).data;
    const name = try ip.getOrPutString(sema.gpa, sema.zir.nullTerminatedString(ft.name_start), .no_embedded_nulls);
    const field = (try sema.unionFieldByName(union_ty, name)) orelse
        return sema.failBadUnionFieldAccess(union_ty, name);

    const raw = try sema.resolveInst(item.init);
    const val = (try sema.coerceValueToType(raw, field.ty, "union field")).index;

    if (Type.fromIndex(union_ty).containerLayout(ip) == .@"packed") {
        const union_val = try sema.bitCast(.fromIndex(union_ty), Value.fromIndex(val), sema.block.nodeOffset(sema.srcNodeOffset(inst)));
        const final = if (result_ty == union_ty) union_val else try sema.coerceValueToType(union_val, result_ty, "union init");
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
    const final = if (result_ty == union_ty) value else try sema.coerceValueToType(value, result_ty, "union init");
    return if (is_ref) try sema.materializeConstPtr(final) else final;
}

fn evalStructInitEmpty(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    const struct_ty = (try sema.resolveInst(un_node.operand)).index;
    if (sema.intern_pool.indexToKey(struct_ty) != .struct_type) {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "struct init: type does not support struct initialization syntax", .{});
    }
    return try sema.structInitEmpty(struct_ty);
}

fn structInitEmpty(sema: *Sema, struct_ty: InternPool.Index) Error!Value {
    const count = try sema.structFieldCount(struct_ty);
    const elems = try sema.gpa.alloc(InternPool.Index, count);
    defer sema.gpa.free(elems);
    @memset(elems, .none);
    return try sema.finishStructInit(struct_ty, struct_ty, elems, false);
}

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
            return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "union initializer must initialize one field", .{});
        },
        else => {
            return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "struct init: type does not support struct initialization syntax", .{});
        },
    };
    const value = if (init_ty == obj_ty) base else try sema.coerceValueToType(base, init_ty, "struct init");
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
    const final = if (result_ty == struct_ty) value else try sema.coerceValueToType(value, result_ty, "struct init");
    return if (is_ref) try sema.materializeConstPtr(final) else final;
}

fn evalRef(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const un_tok = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_tok;
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

    const array_value = try sema.loadValue(try sema.resolveInst(bin.lhs));
    return try sema.aggregateElement(array_value, bin.rhs);
}

fn evalElemPtrNode(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const bin = sema.binData(inst);
    const array_ptr = try sema.resolveInst(bin.lhs);
    const index = try sema.resolveArrayLen(bin.rhs, "elem ptr");
    return try sema.elemPtr(array_ptr, index);
}

fn evalArrayInitElemPtr(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const datas = sema.zir.instructions.items(.data);
    const extra = sema.zir.extraData(Zir.Inst.ElemPtrImm, datas[@intFromEnum(inst)].pl_node.payload_index).data;
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
        // Reading a union field asserts it is the active one; an initializing store sets the tag when the
        // field pointer is written (storeElement), so no tag store is needed here.
        .auto => if (!initializing) {
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
        return .{ .index = try ip.internPtr(.{
            .ty = field_ptr_ty.index,
            .base_addr = .{ .comptime_field = struct_ty.structFieldDefaultValue(field_index, ip).?.index },
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
    const parent_ty = ip.indexToKey(array_ptr.index).ptr.ty;
    const child_ty = ip.indexToKey(parent_ty).ptr_type.child;
    if (ip.indexToKey(child_ty) == .ptr_type and ip.indexToKey(child_ty).ptr_type.flags.size == .slice) {
        return try sema.elemPtrSlice(array_ptr, index, child_ty);
    }
    if (ip.indexToKey(child_ty) == .tuple_type) {
        return try sema.tupleElemPtr(array_ptr, index);
    }
    const elems = indexableInfo(ip, child_ty) orelse {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "elem ptr: operand is not an array pointer", .{});
    };
    if (index >= elems.len) {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "index {d} outside array of length {d}", .{ index, elems.len });
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

fn elemPtrSlice(sema: *Sema, slice_ptr: Value, index: u64, slice_ty: InternPool.Index) Error!Value {
    const ip = sema.intern_pool;
    const slice_val = try sema.loadValue(slice_ptr);
    const s = ip.indexToKey(slice_val.index).slice;
    const len = try sema.resolveUsizeInt(.{ .index = s.len }, "slice index");
    if (index >= len) {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "index {d} outside slice of length {d}", .{ index, len });
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

const IndexableInfo = struct { len: u64, child: InternPool.Index };
fn indexableInfo(ip: *const InternPool, ty: InternPool.Index) ?IndexableInfo {
    return switch (ip.indexToKey(ty)) {
        .array_type => |at| .{ .len = at.len, .child = at.child },
        .vector_type => |vt| .{ .len = vt.len, .child = vt.child },
        else => null,
    };
}

fn evalValidatePtrArrayInit(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    const datas = sema.zir.instructions.items(.data);
    const extra = sema.zir.extraData(Zir.Inst.Block, datas[@intFromEnum(inst)].pl_node.payload_index);
    const body = sema.zir.bodySlice(extra.end, extra.data.body_len);
    if (body.len == 0) return null;
    const first = sema.zir.extraData(Zir.Inst.ElemPtrImm, datas[@intFromEnum(body[0])].pl_node.payload_index).data;
    const array_ptr = try sema.resolveInst(first.ptr);
    const array_ty = ip.indexToKey(ip.indexToKey(array_ptr.index).ptr.ty).ptr_type.child;
    const array_len = (indexableInfo(ip, array_ty) orelse return null).len;
    if (body.len != array_len) {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "expected {d} array elements; found {d}", .{ array_len, body.len });
    }
    return null;
}

fn analyzeSlice(sema: *Sema, ptr_ptr: Value, start: u64, end_opt: ?u64, sentinel_opt: ?Value, by_length: bool) Error!?Value {
    const ip = sema.intern_pool;
    const ptr_ptr_child = ip.indexToKey(ip.indexToKey(ptr_ptr.index).ptr.ty).ptr_type.child;

    var backing: InternPool.Index = undefined;
    var base_offset: u64 = undefined;
    var len: u64 = undefined;
    var elem_ty: InternPool.Index = undefined;
    var is_const: bool = undefined;
    var ptr_sentinel: InternPool.Index = .none;
    var operand_is_slice = false;
    switch (ip.indexToKey(ptr_ptr_child)) {
        .array_type => |arr| {
            backing = ptr_ptr.index;
            base_offset = 0;
            len = arr.len;
            elem_ty = arr.child;
            is_const = ip.indexToKey(ip.indexToKey(ptr_ptr.index).ptr.ty).ptr_type.flags.is_const;
            ptr_sentinel = arr.sentinel;
        },
        .ptr_type => |inner| switch (inner.flags.size) {
            .one => {
                const arr = ip.indexToKey(inner.child).array_type;
                backing = (try sema.loadValue(ptr_ptr)).index;
                base_offset = 0;
                len = arr.len;
                elem_ty = arr.child;
                is_const = inner.flags.is_const;
                ptr_sentinel = arr.sentinel;
            },
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

    const end: u64 = if (end_opt) |e| (if (by_length) start + e else e) else len;
    const end_is_len = end == len;

    if (start > end) {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "start index {d} is larger than end index {d}", .{ start, end });
    }
    if (end > len + @intFromBool(ptr_sentinel != .none)) {
        const sentinel_label: []const u8 = if (ptr_sentinel != .none) " +1 (sentinel)" else "";
        const kind: []const u8 = if (operand_is_slice) "slice" else "array";
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "end index {d} out of bounds for {s} of length {d}{s}", .{ end, kind, len, sentinel_label });
    }

    const sentinel: InternPool.Index = s: {
        if (sentinel_opt) |provided| {
            try sema.checkSentinelType(elem_ty);
            const casted = try sema.coerceValueToType(provided, elem_ty, "slice sentinel");
            const actual = try sema.aggregateElementByIndex(try sema.loadValue(.{ .index = backing }), base_offset + end);
            if (actual.index != casted.index) {
                return sema.fail(sema.block, sema.block.nodeOffset(.zero), "value in memory does not match slice sentinel", .{});
            }
            break :s casted.index;
        }
        break :s if (end_is_len) ptr_sentinel else .none;
    };

    const result_array_ty = try ip.internArrayType(.{ .len = end - start, .child = elem_ty, .sentinel = sentinel });
    const result_ptr_ty = try ip.internPtrType(.{ .child = result_array_ty, .flags = .{ .size = .one, .is_const = is_const } });
    return .{ .index = try ip.internPtr(.{
        .ty = result_ptr_ty,
        .base_addr = .{ .arr_elem = .{ .base = backing, .index = base_offset + start } },
        .byte_offset = 0,
    }) };
}

fn failSliceNotArrayPtr(sema: *Sema) Error {
    return sema.fail(sema.block, sema.block.nodeOffset(.zero), "slice: operand is not an array pointer", .{});
}

fn evalSliceStart(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const datas = sema.zir.instructions.items(.data);
    const extra = sema.zir.extraData(Zir.Inst.SliceStart, datas[@intFromEnum(inst)].pl_node.payload_index).data;
    const operand = try sema.resolveInst(extra.lhs);
    const start = try sema.resolveArrayLen(extra.start, "slice start");
    return sema.analyzeSlice(operand, start, null, null, false);
}

fn evalSliceEnd(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const datas = sema.zir.instructions.items(.data);
    const extra = sema.zir.extraData(Zir.Inst.SliceEnd, datas[@intFromEnum(inst)].pl_node.payload_index).data;
    const operand = try sema.resolveInst(extra.lhs);
    const start = try sema.resolveArrayLen(extra.start, "slice start");
    const end = try sema.resolveArrayLen(extra.end, "slice end");
    return sema.analyzeSlice(operand, start, end, null, false);
}

fn evalSliceSentinel(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const datas = sema.zir.instructions.items(.data);
    const extra = sema.zir.extraData(Zir.Inst.SliceSentinel, datas[@intFromEnum(inst)].pl_node.payload_index).data;
    const operand = try sema.resolveInst(extra.lhs);
    const start = try sema.resolveArrayLen(extra.start, "slice start");
    const end = if (extra.end == .none) null else try sema.resolveArrayLen(extra.end, "slice end");
    const sentinel = try sema.resolveInst(extra.sentinel);
    return sema.analyzeSlice(operand, start, end, sentinel, false);
}

fn evalSliceLength(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const datas = sema.zir.instructions.items(.data);
    const extra = sema.zir.extraData(Zir.Inst.SliceLength, datas[@intFromEnum(inst)].pl_node.payload_index).data;
    const operand = try sema.resolveInst(extra.lhs);
    const start = try sema.resolveArrayLen(extra.start, "slice start");
    const length = try sema.resolveArrayLen(extra.len, "slice length");
    const sentinel = if (extra.sentinel == .none) null else try sema.resolveInst(extra.sentinel);
    return sema.analyzeSlice(operand, start, length, sentinel, true);
}

fn evalSliceSentinelTy(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    const ip = sema.intern_pool;
    const datas = sema.zir.instructions.items(.data);
    const operand = try sema.resolveInst(datas[@intFromEnum(inst)].un_node.operand);
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

    const lhs = try sema.resolveInst(bin.lhs);
    const array_value = if (sema.intern_pool.indexToKey(lhs.index) == .ptr)
        try sema.loadValue(lhs)
    else
        lhs;
    return try sema.aggregateElement(array_value, bin.rhs);
}

fn aggregateElement(sema: *Sema, array_value: Value, index_ref: Zir.Inst.Ref) Error!Value {
    return sema.aggregateElementByIndex(array_value, try sema.resolveArrayLen(index_ref, "elem access"));
}

fn aggregateElementByIndex(sema: *Sema, array_value: Value, index: u64) Error!Value {
    const ip = sema.intern_pool;
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
    while (ip.indexToKey(agg.index) == .ptr) agg = try sema.loadValue(agg);
    const agg_key = ip.indexToKey(agg.index);
    if (agg_key != .aggregate) {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "elem access: operand is not an indexable aggregate", .{});
    }
    const array_ty = agg_key.aggregate.ty;
    const count = slice_len orelse switch (ip.indexToKey(array_ty)) {
        .array_type => |at| at.lenIncludingSentinel(),
        else => ip.aggregateElementCount(array_ty),
    };
    if (index >= count) {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "index {d} outside array of length {d}", .{ index, count });
    }
    const logical_index = start_offset + index;
    if (slice_len == null) switch (ip.indexToKey(array_ty)) {
        .array_type => |at| if (at.sentinel != .none and logical_index == at.len) return .{ .index = at.sentinel },
        else => {},
    };
    return .{ .index = try ip.aggregateElementAt(agg_key.aggregate, logical_index) };
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
        .slice => |s| return try sema.resolveUsizeInt(.{ .index = s.len }, "@memcpy length"),
        .ptr => |p| return switch (ip.indexToKey(ip.indexToKey(p.ty).ptr_type.child)) {
            .array_type => |at| at.len,
            else => null,
        },
        else => return null,
    }
}

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

fn doPointersOverlap(sema: *Sema, a: Value, b: Value, elem_count: u64) bool {
    const a_back = sema.memBacking(a);
    const b_back = sema.memBacking(b);
    if (a_back.ptr != b_back.ptr) return false;
    const diff = if (a_back.start >= b_back.start) a_back.start - b_back.start else b_back.start - a_back.start;
    return diff < elem_count;
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

    if (sema.doPointersOverlap(dest, src, len)) {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "@memcpy: arguments alias", .{});
    }

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

fn resolveArrayLen(sema: *Sema, ref: Zir.Inst.Ref, op_name: []const u8) Error!u64 {
    assert(ref != .none);
    return sema.resolveUsizeInt(try sema.resolveInst(ref), op_name);
}

fn resolveInt(sema: *Sema, value: Value, ty: InternPool.Index, op_name: []const u8) Error!u64 {
    const coerced = try sema.coerceValueToType(value, ty, op_name);
    const key = sema.intern_pool.indexToKey(coerced.index);
    if (key != .int) {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "{s}: expected an integer", .{op_name});
    }
    var space: InternPool.Key.Int.Storage.BigIntSpace = undefined;
    return key.int.storage.toBigInt(&space).toInt(u64) catch {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "{s}: value out of range", .{op_name});
    };
}

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

    if (value_key == .err) {
        const idx = try ip.internErrorUnion(.{
            .ty = dest_ty,
            .val = .{ .err_name = value_key.err.name },
        });
        return .{ .index = idx };
    }

    const payload_value = try sema.coerceValueToType(value, eu_type.payload_type, op_name);
    const idx = try ip.internErrorUnion(.{
        .ty = dest_ty,
        .val = .{ .payload = payload_value.index },
    });
    return .{ .index = idx };
}

fn evalBitNot(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const ip = sema.intern_pool;
    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
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
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst_idx)), "internal error: unresolved instruction ref %{d}", .{@intFromEnum(inst_idx)});
    }

    if (wellKnownRefToValue(ref)) |value| return value;
    return sema.fail(sema.block, sema.block.nodeOffset(.zero), "unsupported ZIR ref: {s}", .{@tagName(ref)});
}

fn wellKnownRefToValue(ref: Zir.Inst.Ref) ?Value {
    if (ref != .none and ref.toIndex() == null) {
        return .{ .index = @enumFromInt(@intFromEnum(ref)) };
    }
    return null;
}

fn evalDeclVal(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    if (sema.this_type != .none) {
        const name = try sema.intern_pool.getOrPutString(sema.gpa, sema.zir.instructions.items(.data)[@intFromEnum(inst)].str_tok.get(sema.zir), .no_embedded_nulls);
        var container = sema.this_type;
        while (container != .none) : (container = sema.intern_pool.typeParent(container)) {
            if (try sema.containerDeclNav(container, name)) |val| return val;
        }
    }
    if (try sema.lookupDecl(inst, "decl_val")) |found| {
        return .{ .index = found.resolved.value };
    }
    const name = sema.zir.instructions.items(.data)[@intFromEnum(inst)].str_tok.get(sema.zir);
    return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "decl_val '{s}': not found in scope", .{name});
}

fn evalDeclRef(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    if (sema.this_type != .none) {
        const name = try sema.intern_pool.getOrPutString(sema.gpa, sema.zir.instructions.items(.data)[@intFromEnum(inst)].str_tok.get(sema.zir), .no_embedded_nulls);
        var container = sema.this_type;
        while (container != .none) : (container = sema.intern_pool.typeParent(container)) {
            if (try sema.containerDeclNav(container, name)) |val| return try sema.materializeConstPtr(val);
        }
    }
    const found = (try sema.lookupDecl(inst, "decl_ref")) orelse {
        const name = sema.zir.instructions.items(.data)[@intFromEnum(inst)].str_tok.get(sema.zir);
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "decl_ref '{s}': not found in scope", .{name});
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

const DeclLookup = struct {
    nav: InternPool.Nav.Index,
    resolved: InternPool.Nav.Resolved,
};

fn lookupDecl(sema: *Sema, inst: Zir.Inst.Index, op_name: []const u8) Error!?DeclLookup {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const data = sema.zir.instructions.items(.data)[@intFromEnum(inst)].str_tok;
    const name_bytes = data.get(sema.zir);
    const name = try sema.intern_pool.getOrPutString(sema.gpa, name_bytes, .no_embedded_nulls);

    const ns_idx = sema.namespace orelse {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "{s} '{s}': no namespace in scope", .{ op_name, name_bytes });
    };

    if (try sema.lookupName(ns_idx, name)) |nav_idx| {
        const nav = sema.intern_pool.getNav(nav_idx);
        const resolved = nav.resolved orelse {
            return sema.fail(sema.block, sema.block.nodeOffset(.zero), "{s} '{s}': binding recorded but value not resolved (test / comptime / extern)", .{ op_name, name_bytes });
        };
        if (resolved.value == .none) {
            return sema.fail(sema.block, sema.block.nodeOffset(.zero), "{s} '{s}': type resolved but value not yet", .{ op_name, name_bytes });
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
        if (sema.lookupInNamespace(idx, name)) |lookup| return lookup.nav;
        current = sema.intern_pool.namespacePtr(idx).parent.unwrap();
    }
    return null;
}

fn lookupInNamespace(
    sema: *Sema,
    namespace_index: InternPool.NamespaceIndex,
    ident_name: InternPool.NullTerminatedString,
) ?struct {
    nav: InternPool.Nav.Index,
    accessible: bool,
} {
    const ip = sema.intern_pool;
    const namespace = ip.namespacePtr(namespace_index);
    const adapter: InternPool.Namespace.NameAdapter = .{ .pool = ip };
    const src_file = if (sema.namespace) |cur| ip.namespacePtr(cur).file_scope else .none;
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
    if (sema.lookupInNamespace(namespace, decl_name)) |lookup| {
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
    const value_body = unwrapped.value_body orelse {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "bindDecls '{s}': no value_body (extern decl)", .{sema.intern_pool.stringSlice(name)});
    };

    const declared_type: ?InternPool.Index = if (unwrapped.type_body) |tb| blk: {
        const t = (try sema.resolveInlineBody(tb, decl_inst)).index;
        try sema.inst_map.put(sema.gpa, decl_inst, .{ .index = t });
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
        slot.* = try sema.intern_pool.getOrPutString(sema.gpa, name_bytes, .no_embedded_nulls);
        extra_index += 1;
    }

    const ty_idx = try sema.intern_pool.internErrorSetType(names);
    return .{ .index = ty_idx };
}

fn evalErrorValue(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const data = sema.zir.instructions.items(.data)[@intFromEnum(inst)].str_tok;
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

    const error_set = try sema.resolveDestType(bin.lhs, "error_union_type");
    const payload = try sema.resolveDestType(bin.rhs, "error_union_type");

    const ty_idx = try sema.intern_pool.internErrorUnionType(.{
        .error_set_type = error_set,
        .payload_type = payload,
    });
    return .{ .index = ty_idx };
}

fn evalErrUnionCode(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);
    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    assert(un_node.operand != .none);
    return try sema.errUnionCodeVal(try sema.resolveInst(un_node.operand));
}

fn evalErrUnionCodePtr(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);
    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
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
    assert(@intFromEnum(inst) < sema.zir.instructions.len);
    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
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
    }
    const child_ptr_ty = try ip.internPtrType(.{ .child = eu_key.error_union_type.payload_type, .sentinel = ptr_type.sentinel, .flags = ptr_type.flags });
    return .{ .index = try ip.internPtr(.{
        .ty = child_ptr_ty,
        .base_addr = .{ .eu_payload = eu_ptr.index },
        .byte_offset = 0,
    }) };
}

fn evalTry(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);
    const ip = sema.intern_pool;
    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
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
    assert(@intFromEnum(inst) < sema.zir.instructions.len);
    const ip = sema.intern_pool;
    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
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

fn evalEnsureErrUnionPayloadVoid(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);
    const ip = sema.intern_pool;
    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
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
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    assert(un_node.operand != .none);

    const operand_value = try sema.resolveInst(un_node.operand);
    const operand_key = sema.intern_pool.indexToKey(operand_value.index);
    if (operand_key != .error_union) {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "err_union_payload: operand is not an error union", .{});
    }

    switch (operand_key.error_union.val) {
        .payload => |payload_idx| return .{ .index = payload_idx },
        .err_name => {
            return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "err_union_payload: operand carries an error, not a payload", .{});
        },
    }
}

fn evalIsNonErr(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);
    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    assert(un_node.operand != .none);
    return try sema.isNonErrVal(try sema.resolveInst(un_node.operand));
}

fn evalRetIsNonErr(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);
    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    assert(un_node.operand != .none);
    return try sema.isNonErrVal(try sema.resolveInst(un_node.operand));
}

fn evalIsNonErrPtr(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);
    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    assert(un_node.operand != .none);
    return try sema.isNonErrVal(try sema.loadValue(try sema.resolveInst(un_node.operand)));
}

fn isNonErrVal(sema: *Sema, operand_value: Value) Error!Value {
    const operand_key = sema.intern_pool.indexToKey(operand_value.index);
    if (operand_key != .error_union) {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "is_non_err: operand is not an error union", .{});
    }
    return switch (operand_key.error_union.val) {
        .payload => Value.bool_true,
        .err_name => Value.bool_false,
    };
}

fn evalLoop(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.Block, pl_node.payload_index);
    const body = sema.zir.bodySlice(extra.end, extra.data.body_len);
    return try sema.resolveInlineBody(body, inst);
}

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
            var obj = try sema.resolveInst(pair[0]);
            const ip = sema.intern_pool;
            if (ip.indexToKey(obj.index) == .slice)
                break :blk try sema.resolveUsizeInt(.{ .index = ip.indexToKey(obj.index).slice.len }, "for slice len");
            while (ip.indexToKey(obj.index) == .ptr) obj = try sema.loadValue(obj);
            const key = ip.indexToKey(obj.index);
            if (key != .aggregate) {
                return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "for: operand is not a range or indexable", .{});
            }
            break :blk ip.aggregateElementCount(key.aggregate.ty);
        } else blk: {
            const start = try sema.resolveUsizeInt(try sema.resolveInst(pair[0]), "for range start");
            const end = try sema.resolveUsizeInt(try sema.resolveInst(pair[1]), "for range end");
            if (end < start) {
                return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "for: range end is before range start", .{});
            }
            break :blk end - start;
        };
        if (len) |existing| {
            if (existing != arg_len) {
                return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "for: non-matching loop lengths", .{});
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
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const tag = sema.zir.instructions.items(.tag)[@intFromEnum(inst)];
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
            .payload => {
                if (non_err.capture != .none) return sema.failSwitch("non-err payload capture");
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

    return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "switch: no matching case and no else", .{});
}

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
const SwitchRangeSet = struct {
    ranges: std.ArrayListUnmanaged([2]i128) = .empty,

    fn deinit(set: *SwitchRangeSet, gpa: std.mem.Allocator) void {
        set.ranges.deinit(gpa);
    }

    fn add(set: *SwitchRangeSet, gpa: std.mem.Allocator, lo: i128, hi: i128) Error!bool {
        for (set.ranges.items) |r| {
            if (hi >= r[0] and lo <= r[1]) return true;
        }
        try set.ranges.append(gpa, .{ lo, hi });
        return false;
    }

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

fn markSwitchEnumField(seen: []bool, index: u32) bool {
    if (index >= seen.len) return false;
    if (seen[index]) return true;
    seen[index] = true;
    return false;
}

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

fn validateSwitchBlock(sema: *Sema, inst: Zir.Inst.Index, item_ty: InternPool.Index, sw: Zir.UnwrappedSwitchBlock) Error!void {
    const ip = sema.intern_pool;
    const gpa = sema.gpa;
    const has_else = sw.else_case != null;

    const type_tag = switchTypeTag(ip, item_ty);
    if (type_tag == .other) {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "switch on type '{f}'", .{Type.fromIndex(item_ty).fmt(ip)});
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

    var extra_index: usize = sw.end;
    var it = sw.iterateCases();
    while (it.next()) |case| {
        extra_index += case.prong_info.body_len;
        for (case.item_infos) |item_info| {
            const dup = switch (item_info.unwrap()) {
                .under => {
                    return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "'_' prong only allowed when switching on non-exhaustive enums", .{});
                },
                .enum_literal => |n| blk: {
                    const name = try ip.getOrPutString(gpa, sema.zir.nullTerminatedString(n), .no_embedded_nulls);
                    if (ip.indexToKey(item_ty) != .enum_type) return sema.failBadMemberAccess(item_ty, name);
                    const field_index = (try sema.enumFieldIndex(item_ty, name)) orelse
                        return sema.failBadMemberAccess(item_ty, name);
                    break :blk markSwitchEnumField(seen_enum_fields, field_index);
                },
                .error_value => |n| blk: {
                    const name = try ip.getOrPutString(gpa, sema.zir.nullTerminatedString(n), .no_embedded_nulls);
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
                return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "duplicate switch value", .{});
            }
        }
        for (case.range_infos) |range_pair| {
            saw_range = true;
            const lo_len = range_pair[0].bodyLen() orelse 0;
            const hi_len = range_pair[1].bodyLen() orelse 0;
            if (type_tag == .int or type_tag == .comptime_int) {
                const lo = try sema.coerceValueToType(try sema.resolveInlineBody(sema.zir.bodySlice(extra_index, lo_len), inst), item_ty, "switch range");
                const hi = try sema.coerceValueToType(try sema.resolveInlineBody(sema.zir.bodySlice(extra_index + lo_len, hi_len), inst), item_ty, "switch range");
                if (try range_set.add(gpa, sema.intAsI128(lo.index).?, sema.intAsI128(hi.index).?)) {
                    return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "duplicate switch value", .{});
                }
            }
            extra_index += lo_len + hi_len;
        }
    }

    if (saw_range and type_tag != .int and type_tag != .comptime_int) {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "ranges not allowed when switching on type '{f}'", .{Type.fromIndex(item_ty).fmt(ip)});
    }

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
            return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "unreachable else prong; all cases already handled", .{});
        }
    } else if (!all_handled) {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "switch must handle all possibilities", .{});
    }
}

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
                const item_coerced = try sema.coerceValueToType(item_raw, op.ty, "switch case");
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
                if (sema.intern_pool.indexToKey(op.ty) != .enum_type) {
                    return sema.failSwitch("enum-literal case on a non-enum operand");
                }
                const name = try sema.intern_pool.getOrPutString(sema.gpa, sema.zir.nullTerminatedString(name_idx), .no_embedded_nulls);
                const tag = (try sema.enumTagByName(op.ty, name)) orelse
                    return sema.failBadMemberAccess(op.ty, name);
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
        const lo_co = try sema.coerceValueToType(lo_raw, op.ty, "switch range");
        const hi_co = try sema.coerceValueToType(hi_raw, op.ty, "switch range");
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

fn resolveParamType(sema: *Sema, param_inst: Zir.Inst.Index) Error!InternPool.Index {
    const pl_tok = sema.zir.instructions.items(.data)[@intFromEnum(param_inst)].pl_tok;
    const extra = sema.zir.extraData(Zir.Inst.Param, pl_tok.payload_index);
    const body = sema.zir.bodySlice(extra.end, extra.data.type.body_len);
    return (try sema.resolveInlineBody(body, param_inst)).index;
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

fn resolveDeclaredRetType(sema: *Sema, info: Zir.FnInfo, break_target: Zir.Inst.Index) Error!InternPool.Index {
    if (info.ret_ty_ref != .none) return (try sema.resolveInst(info.ret_ty_ref)).index;
    if (info.ret_ty_body.len > 0) return (try sema.resolveInlineBody(info.ret_ty_body, break_target)).index;
    return .void_type;
}

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
    if (info.body.len == 0) return Value{ .index = fn_ty };

    const func_idx = try sema.intern_pool.internFunc(.{
        .source_zir_id = sema.current_zir_id,
        .ty = fn_ty,
        .uncoerced_ty = fn_ty,
        .zir_body_inst = inst,
        .parent = sema.this_type,
    });
    return Value{ .index = func_idx };
}

fn evalCall(sema: *Sema, inst: Zir.Inst.Index, comptime kind: enum { direct, field }) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    try sema.emitBackwardBranch();

    const callee_value: Value, const self_val: ?Value, const explicit_len: u32, const args_body: []const Zir.Inst.Index, const enclosing_ty: InternPool.Index = switch (kind) {
        .direct => blk: {
            const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
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
            const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
            const extra = sema.zir.extraData(Zir.Inst.FieldCall, pl_node.payload_index);
            const name = try sema.intern_pool.getOrPutString(sema.gpa, sema.zir.nullTerminatedString(extra.data.field_name_start), .no_embedded_nulls);
            const object_ptr = try sema.resolveInst(extra.data.obj_ptr);
            const object = try sema.loadValue(object_ptr);
            const args_slice: []const Zir.Inst.Index = @ptrCast(sema.zir.extra[extra.end..]);
            const is_type = object.typeOf(sema.intern_pool).toIndex() == .type_type;
            const lookup_ty = if (is_type) object.index else object.typeOf(sema.intern_pool).toIndex();
            const callee = (try sema.containerDeclByName(lookup_ty, name)) orelse
                return sema.failBadMemberAccess(lookup_ty, name);
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

    // A callee may be a pointer to a function -- a stored `*const fn(...)` or a vtable entry.
    // Dereference to the function value it points to before calling.
    var callee_resolved = callee_value;
    while (sema.intern_pool.indexToKey(callee_resolved.index) == .ptr) callee_resolved = try sema.loadValue(callee_resolved);
    const callee_key = sema.intern_pool.indexToKey(callee_resolved.index);
    if (callee_key != .func) {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "call: callee is not a function value", .{});
    }
    const func = callee_key.func;
    var func_ty = sema.intern_pool.indexToKey(func.ty).func_type;
    const param_types = try sema.gpa.dupe(InternPool.Index, func_ty.param_types);
    defer sema.gpa.free(param_types);
    func_ty.param_types = param_types;

    const args_len = explicit_len + @as(u32, @intFromBool(self_val != null));
    if (func_ty.param_types.len != args_len) {
        return sema.fail(sema.block, sema.block.nodeOffset(sema.srcNodeOffset(inst)), "expected {d} argument(s), found {d}", .{ func_ty.param_types.len, args_len });
    }
    const raw_args = try sema.evalCallArgs(inst, self_val, explicit_len, args_body, func_ty.param_types);
    defer sema.gpa.free(raw_args);

    const saved_this = sema.this_type;
    sema.this_type = if (func.parent != .none) func.parent else enclosing_ty;
    defer sema.this_type = saved_this;

    const frame = try sema.enterSourceZir(func.source_zir_id, "call");
    defer frame.restore(sema);

    const info = sema.zir.getFnInfo(func.zir_body_inst);
    const param_insts = try sema.collectParamInsts(info, args_len);
    defer sema.gpa.free(param_insts);

    const old_inst_map = sema.inst_map;
    sema.inst_map = .empty;
    defer {
        sema.inst_map.deinit(sema.gpa);
        sema.inst_map = old_inst_map;
    }
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
        try sema.inst_map.put(sema.gpa, p_inst, val);
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
        error.ComptimeReturn => return try sema.coerceValueToType(sema.return_value, sema.fn_ret_ty, "return"),
        else => |e| return e,
    }
}

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
        try sema.inst_map.put(sema.gpa, inst, .{ .index = param_ty });
        arg_values[param_idx] = try sema.resolveInlineBody(args_body[start..end], inst);
    }
    return arg_values;
}

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

fn evalBlockComptime(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.BlockComptime, pl_node.payload_index);
    const body = sema.zir.bodySlice(extra.end, extra.data.body_len);
    return try sema.resolveInlineBody(body, inst);
}

fn evalTypeof(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const un_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].un_node;
    const operand = try sema.resolveInst(un_node.operand);
    return Value{ .index = Value.typeOf(operand, sema.intern_pool).index };
}

fn evalThis(sema: *Sema) Error!?Value {
    if (sema.this_type == .none) {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "@This(): no enclosing container", .{});
    }
    return Value{ .index = sema.this_type };
}

fn evalClosureGet(sema: *Sema, extended: Zir.Inst.Extended.InstData) Error!?Value {
    if (sema.this_type == .none) {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "closure_get: no enclosing container", .{});
    }
    const captures = switch (sema.intern_pool.indexToKey(sema.this_type)) {
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

    const op_name = switch (opcode) {
        .add_with_overflow => "@addWithOverflow",
        .sub_with_overflow => "@subWithOverflow",
        .mul_with_overflow => "@mulWithOverflow",
        .shl_with_overflow => "@shlWithOverflow",
        else => unreachable,
    };

    const dest_ty = if (opcode == .shl_with_overflow)
        lhs_ty
    else
        try sema.resolveArithPeerType(uncasted_lhs, uncasted_rhs, op_name);
    const rhs_dest_ty: Type = if (opcode == .shl_with_overflow)
        .fromIndex((try sema.log2IntType(lhs_ty.index)).?)
    else
        dest_ty;

    const lhs = try sema.coerceValueToType(uncasted_lhs, dest_ty.index, op_name);
    const rhs = try sema.coerceValueToType(uncasted_rhs, rhs_dest_ty.index, op_name);

    if (dest_ty.scalarType(ip).zigTypeTag(ip) != .int) {
        return sema.fail(sema.block, sema.block.nodeOffset(.zero), "{s}: expected vector of integers or integer tag type, found '{f}'", .{ op_name, dest_ty.fmt(ip) });
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
            if (!lhs.isUndef(ip) and lhs.compareAllWithZero(.eq, ip)) {
                wrapped = lhs;
                overflow_bit = zero_overflow;
            } else if (!rhs.isUndef(ip) and rhs.compareAllWithZero(.eq, ip)) {
                wrapped = rhs;
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
    _ = try sema.resolveInlineBody(body, inst);

    const args = sema.zir.refSlice(extra.end, extended.small);
    assert(args.len > 0);

    const insts = try sema.arena.alloc(Value, args.len);
    for (insts, args) |*v, arg_ref| v.* = try sema.resolveInst(arg_ref);
    const ty = try sema.resolvePeerTypes(insts);
    return Value{ .index = ty.index };
}

fn evalTypeofBuiltin(sema: *Sema, inst: Zir.Inst.Index) Error!?Value {
    assert(@intFromEnum(inst) < sema.zir.instructions.len);

    const pl_node = sema.zir.instructions.items(.data)[@intFromEnum(inst)].pl_node;
    const extra = sema.zir.extraData(Zir.Inst.Block, pl_node.payload_index);
    const body = sema.zir.bodySlice(extra.end, extra.data.body_len);
    const operand = try sema.resolveInlineBody(body, inst);
    return Value{ .index = Value.typeOf(operand, sema.intern_pool).index };
}

fn evalIntFromError(sema: *Sema, extended: Zir.Inst.Extended.InstData) Error!?Value {
    const ip = sema.intern_pool;
    const extra = sema.zir.extraData(Zir.Inst.UnNode, extended.operand).data;
    const operand = try sema.coerceValueToType(try sema.resolveInst(extra.operand), .anyerror_type, "@intFromError");
    const err_int_ty = Type.fromIndex(try ip.errorIntType());
    if (operand.isUndef(ip)) return try sema.undefValue(err_int_ty);
    const err_name = ip.indexToKey(operand.index).err.name;
    return try sema.intValue_u64(err_int_ty, try ip.getErrorValue(err_name));
}

fn evalErrorFromInt(sema: *Sema, extended: Zir.Inst.Extended.InstData) Error!?Value {
    const ip = sema.intern_pool;
    const extra = sema.zir.extraData(Zir.Inst.UnNode, extended.operand).data;
    const err_int_ty = Type.fromIndex(try ip.errorIntType());
    const operand = try sema.coerceValueToType(try sema.resolveInst(extra.operand), err_int_ty.index, "@errorFromInt");
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

    var dest_ty = Type.fromIndex(try sema.resolveDestType(extra.lhs, "@errorCast"));
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
                return try sema.coerceToErrorUnion(.{ .index = payload_val }, dest_ty.index, "@errorCast");
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

        .inplace_arith_result_ty => {
            const lhs = try sema.resolveInst(@enumFromInt(extended.operand));
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
        .namespace = null,
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
        .id = .{ .reified = .{ .source_zir_id = 0, .decl_inst = @enumFromInt(0), .type_hash = hash } },
        .parent = .none,
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
        .id = .{ .reified = .{ .source_zir_id = 0, .decl_inst = @enumFromInt(0), .type_hash = hash } },
        .parent = .none,
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
        .id = .{ .reified = .{ .source_zir_id = 0, .decl_inst = @enumFromInt(0), .type_hash = hash } },
        .parent = .none,
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
