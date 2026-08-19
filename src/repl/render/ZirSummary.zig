//! Renders one ZIR instruction's operand/value summary, shared by `:dump` and the web explorer.

const std = @import("std");
const Zir = std.zig.Zir;

pub fn write(
    zir: Zir,
    tag: Zir.Inst.Tag,
    data: Zir.Inst.Data,
    stdout: *std.Io.Writer,
) !void {
    switch (tag) {
        .add,
        .add_sat,
        .add_unsafe,
        .addwrap,
        .array_cat,
        .array_type,
        .bit_and,
        .bitcast,
        .bit_offset_of,
        .bit_or,
        .cmp_eq,
        .cmp_gt,
        .cmp_gte,
        .cmp_lt,
        .cmp_lte,
        .cmp_neq,
        .coerce_ptr_elem_ty,
        .div,
        .div_ceil,
        .div_exact,
        .div_floor,
        .div_trunc,
        .elem_ptr,
        .elem_ptr_load,
        .elem_ptr_node,
        .elem_val,
        .enum_from_int,
        .error_union_type,
        .float_cast,
        .float_from_int,
        .from_backing_int,
        .has_decl,
        .has_field,
        .int_cast,
        .int_from_float,
        .max,
        .memcpy,
        .memmove,
        .memset,
        .merge_error_sets,
        .min,
        .mod,
        .mod_rem,
        .mul,
        .mul_sat,
        .mulwrap,
        .offset_of,
        .ptr_cast,
        .ptr_from_int,
        .reduce,
        .reify_int,
        .rem,
        .shl,
        .shl_exact,
        .shl_sat,
        .shr,
        .shr_exact,
        .splat,
        .store_node,
        .store_to_inferred_ptr,
        .sub,
        .sub_sat,
        .subwrap,
        .truncate,
        .vector_type,
        .xor,
        => try writeBin(zir, data, stdout),

        .as_node, .as_shift_operand => try writeAs(zir, data, stdout),
        .condbr, .condbr_inline => try writeCondBr(zir, data, stdout),
        .@"try", .try_ptr => try writeTry(zir, data, stdout),
        .bool_br_and, .bool_br_or => try writeBoolBr(zir, data, stdout),
        .call => try writeCall(zir, data, stdout, .direct),
        .field_call => try writeCall(zir, data, stdout, .field),

        .block,
        .block_inline,
        .loop,
        .suspend_block,
        .typeof_builtin,
        .validate_ptr_array_init,
        .validate_ptr_struct_init,
        => try stdout.print(" src_node={d}", .{@backingInt(data.pl_node.src_node)}),

        .block_comptime => try writeBlockComptime(zir, data, stdout),

        .array_init,
        .array_init_anon,
        .array_init_elem_ptr,
        .array_init_ref,
        .array_type_sentinel,
        .atomic_load,
        .atomic_rmw,
        .atomic_store,
        .builtin_call,
        .decl_literal,
        .decl_literal_no_coerce,
        .error_set_decl,
        .@"export",
        .field_ptr,
        .field_ptr_load,
        .field_ptr_named,
        .field_ptr_named_load,
        .field_type_ref,
        .float128,
        .for_len,
        .func,
        .func_fancy,
        .func_inferred,
        .mul_add,
        .shuffle,
        .slice_end,
        .slice_length,
        .slice_sentinel,
        .slice_start,
        .struct_init,
        .struct_init_anon,
        .struct_init_field_ptr,
        .struct_init_field_type,
        .struct_init_ref,
        .switch_block,
        .switch_block_err_union,
        .switch_block_ref,
        .union_init,
        .validate_array_init_ref_ty,
        .validate_array_init_result_ty,
        .validate_array_init_ty,
        .validate_destructure,
        => try stdout.print(" payload={d} src_node={d}", .{ data.pl_node.payload_index, @backingInt(data.pl_node.src_node) }),

        .abs,
        .align_of,
        .alloc,
        .alloc_comptime_mut,
        .alloc_mut,
        .anyframe_type,
        .backing_int,
        .bit_not,
        .bit_reverse,
        .bit_size_of,
        .bool_not,
        .byte_swap,
        .ceil,
        .check_comptime_control_flow,
        .clz,
        .compile_error,
        .cos,
        .ctz,
        .elem_type,
        .embed_file,
        .ensure_err_union_payload_void,
        .ensure_result_non_error,
        .ensure_result_used,
        .error_name,
        .err_union_code,
        .err_union_code_ptr,
        .err_union_payload_unsafe,
        .err_union_payload_unsafe_ptr,
        .exp,
        .exp2,
        .floor,
        .frame_type,
        .from_backing_int_arg_ty,
        .indexable_ptr_elem_type,
        .indexable_ptr_len,
        .int_from_bool,
        .int_from_enum,
        .int_from_ptr,
        .is_non_err,
        .is_non_err_ptr,
        .is_non_null,
        .is_non_null_ptr,
        .load,
        .log,
        .log10,
        .log2,
        .make_ptr_const,
        .negate,
        .negate_wrap,
        .opt_eu_base_ptr_init,
        .optional_payload_safe,
        .optional_payload_safe_ptr,
        .optional_payload_unsafe,
        .optional_payload_unsafe_ptr,
        .optional_type,
        .panic,
        .pop_count,
        .resolve_inferred_alloc,
        .restore_err_ret_index_fn_entry,
        .restore_err_ret_index_unconditional,
        .@"resume",
        .ret_is_non_err,
        .ret_load,
        .ret_node,
        .round,
        .set_eval_branch_quota,
        .set_runtime_safety,
        .sin,
        .size_of,
        .slice_sentinel_ty,
        .splat_op_result_ty,
        .sqrt,
        .struct_init_empty,
        .struct_init_empty_ref_result,
        .struct_init_empty_result,
        .deref,
        .ref_deref,
        .tag_name,
        .tan,
        .trunc,
        .type_info,
        .type_name,
        .typeof,
        .typeof_log2_int_type,
        .validate_const,
        .validate_struct_init_result_ty,
        .validate_struct_init_ty,
        => {
            try stdout.writeAll(" operand=");
            try writeRef(stdout, data.un_node.operand);
            try stdout.print(" src_node={d}", .{@backingInt(data.un_node.src_node)});
        },

        .ref,
        .ret_implicit,
        .validate_ref_ty,
        => {
            try stdout.writeAll(" operand=");
            try writeRef(stdout, data.un_tok.operand);
            try stdout.print(" src_tok={d}", .{@backingInt(data.un_tok.src_tok)});
        },

        .import,
        .param,
        .param_comptime,
        => try stdout.print(" payload={d} src_tok={d}", .{ data.pl_tok.payload_index, @backingInt(data.pl_tok.src_tok) }),

        .alloc_inferred,
        .alloc_inferred_comptime,
        .alloc_inferred_comptime_mut,
        .alloc_inferred_mut,
        .repeat,
        .repeat_inline,
        .ret_ptr,
        .ret_type,
        .trap,
        => try stdout.print(" src_node={d}", .{@backingInt(data.node)}),

        .decl_ref,
        .decl_val,
        .enum_literal,
        .error_value,
        .param_anytype,
        .param_anytype_comptime,
        .ret_err_value,
        => try stdout.print(" \"{s}\" src_tok={d}", .{ data.str_tok.get(zir), @backingInt(data.str_tok.src_tok) }),

        .dbg_var_ptr,
        .dbg_var_val,
        => {
            try stdout.print(" \"{s}\" operand=", .{data.str_op.getStr(zir)});
            try writeRef(stdout, data.str_op.operand);
        },

        .int_big,
        .str,
        => try stdout.print(" \"{s}\"", .{data.str.get(zir)}),

        .@"break",
        .break_inline,
        .switch_continue,
        => {
            const e = zir.extraData(Zir.Inst.Break, data.@"break".payload_index);
            try stdout.writeAll(" operand=");
            try writeRef(stdout, data.@"break".operand);
            try stdout.print(" target=%{d}", .{@backingInt(e.data.block_inst)});
        },

        .@"unreachable" => try stdout.print(" src_node={d}", .{@backingInt(data.@"unreachable".src_node)}),

        .@"defer" => try stdout.print(" index={d} len={d}", .{ data.@"defer".index, data.@"defer".len }),

        .save_err_ret_index => {
            try stdout.writeAll(" operand=");
            try writeRef(stdout, data.save_err_ret_index.operand);
        },
        .ptr_type => try stdout.print(" size={s} payload={d}", .{ @tagName(data.ptr_type.size), data.ptr_type.payload_index }),
        .int_type => try stdout.print(" {s}{d}", .{ if (data.int_type.signedness == .signed) "i" else "u", data.int_type.bit_count }),
        .int => try stdout.print(" {d}", .{data.int}),
        .float => try stdout.print(" {d}", .{data.float}),
        .extended => try stdout.print(" opcode={s} small={d} operand={d}", .{ @tagName(data.extended.opcode), data.extended.small, data.extended.operand }),
        .elem_val_imm => {
            try stdout.writeAll(" operand=");
            try writeRef(stdout, data.elem_val_imm.operand);
            try stdout.print(" idx={d}", .{data.elem_val_imm.idx});
        },
        .declaration => try stdout.print(" payload={d} src_node={d}", .{ data.declaration.payload_index, @backingInt(data.declaration.src_node) }),
        .dbg_stmt => try stdout.print(" line={d} col={d}", .{ data.dbg_stmt.line, data.dbg_stmt.column }),
        .array_init_elem_type => {
            try stdout.writeAll(" lhs=");
            try writeRef(stdout, data.bin.lhs);
            try stdout.writeAll(" rhs=");
            try writeRef(stdout, data.bin.rhs);
        },
    }
}

fn writeBin(zir: Zir, data: Zir.Inst.Data, stdout: *std.Io.Writer) !void {
    const e = zir.extraData(Zir.Inst.Bin, data.pl_node.payload_index).data;
    try stdout.writeAll(" lhs=");
    try writeRef(stdout, e.lhs);
    try stdout.writeAll(" rhs=");
    try writeRef(stdout, e.rhs);
}

fn writeAs(zir: Zir, data: Zir.Inst.Data, stdout: *std.Io.Writer) !void {
    const e = zir.extraData(Zir.Inst.As, data.pl_node.payload_index).data;
    try stdout.writeAll(" dest_type=");
    try writeRef(stdout, e.dest_type);
    try stdout.writeAll(" operand=");
    try writeRef(stdout, e.operand);
}

fn writeCondBr(zir: Zir, data: Zir.Inst.Data, stdout: *std.Io.Writer) !void {
    const e = zir.extraData(Zir.Inst.CondBr, data.pl_node.payload_index).data;
    try stdout.writeAll(" condition=");
    try writeRef(stdout, e.condition);
}

fn writeTry(zir: Zir, data: Zir.Inst.Data, stdout: *std.Io.Writer) !void {
    const e = zir.extraData(Zir.Inst.Try, data.pl_node.payload_index).data;
    try stdout.writeAll(" operand=");
    try writeRef(stdout, e.operand);
}

fn writeBoolBr(zir: Zir, data: Zir.Inst.Data, stdout: *std.Io.Writer) !void {
    const e = zir.extraData(Zir.Inst.BoolBr, data.pl_node.payload_index).data;
    try stdout.writeAll(" lhs=");
    try writeRef(stdout, e.lhs);
}

fn writeBlockComptime(zir: Zir, data: Zir.Inst.Data, stdout: *std.Io.Writer) !void {
    const e = zir.extraData(Zir.Inst.BlockComptime, data.pl_node.payload_index).data;
    try stdout.print(" reason={s}", .{@tagName(e.reason)});
}

fn writeCall(
    zir: Zir,
    data: Zir.Inst.Data,
    stdout: *std.Io.Writer,
    comptime kind: enum { direct, field },
) !void {
    switch (kind) {
        .direct => {
            const e = zir.extraData(Zir.Inst.Call, data.pl_node.payload_index).data;
            const modifier: std.lang.CallModifier = @fromBackingInt(@intCast(e.flags.packed_modifier));
            try stdout.print(" modifier=.{s} callee=", .{@tagName(modifier)});
            try writeRef(stdout, e.callee);
            try stdout.print(" args_len={d}", .{@as(u32, e.flags.args_len)});
        },
        .field => {
            const e = zir.extraData(Zir.Inst.FieldCall, data.pl_node.payload_index).data;
            const modifier: std.lang.CallModifier = @fromBackingInt(@intCast(e.flags.packed_modifier));
            const name = zir.nullTerminatedString(e.field_name_start);
            try stdout.print(" modifier=.{s} obj_ptr=", .{@tagName(modifier)});
            try writeRef(stdout, e.obj_ptr);
            try stdout.print(" field=\"{s}\" args_len={d}", .{ name, @as(u32, e.flags.args_len) });
        },
    }
}

/// Renders an instruction index as `%N`; a well-known ref under its stdlib tag name.
fn writeRef(stdout: *std.Io.Writer, ref: Zir.Inst.Ref) !void {
    if (ref == .none) {
        try stdout.writeAll(".none");
    } else if (ref.toIndex()) |idx| {
        try stdout.print("%{d}", .{@backingInt(idx)});
    } else {
        try stdout.writeAll(@tagName(ref));
    }
}
