//! `:dump <expr>` -- diagnostic dump of AST + ZIR for any input.
//!
//! Used to investigate what AstGen actually emits when implementing
//! new Sema handlers. The per-instruction summary dispatches over
//! `Zir.Inst.Tag` exhaustively -- if stdlib adds a new tag the
//! switch will fail to compile, forcing this file to be updated in
//! lockstep. Per-arm formats match the data union layout in
//! `std/zig/Zir.zig:Inst.Data` so the dump shape is stable across
//! stdlib bumps as long as the arms themselves do not change.
//!
//! The ZIR section is rendered as a tree: we start at each
//! top-level declaration via `zir.typeDecls(.main_struct_inst)`,
//! print its metadata, and recurse into its body slices
//! (`type_body`, `align_body`, `linksection_body`, `addrspace_body`,
//! `value_body`). Body-bearing instructions inside the bodies
//! recurse further -- the body shape per tag mirrors
//! `src/print_zir.zig`'s `writeBlock`/`writeCondBr`/`writeTry`/
//! `writeBoolBr`/`writeFunc`/`writeDefer` helpers in the compiler.
//!
//! Stdlib has no built-in tree-printer; the canonical Zig idiom
//! is a `indent: u32` field on the writer plus
//! `stream.splatByteAll(' ', indent)` before each line. We follow
//! that pattern.
//!
//! Compiler reference: src/print_zir.zig.

const std = @import("std");
const assert = std.debug.assert;

const Session = @import("../Session.zig");
const Spec = @import("Spec.zig");
const Pipeline = @import("../front/Pipeline.zig");
const Diagnostic = @import("../render/Diagnostic.zig");

const Ast = std.zig.Ast;
const Zir = std.zig.Zir;

pub const spec: Spec = .{
    .name = "dump",
    .summary = "Dump AST + ZIR for an expression: :dump <expr>",
    .run = run,
};

fn run(session: *Session, argument: []const u8, stdout: *std.Io.Writer) anyerror!void {
    assert(@intFromPtr(session) != 0);
    assert(@intFromPtr(stdout) != 0);

    const trimmed = std.mem.trim(u8, argument, " \t");
    if (trimmed.len == 0) {
        try stdout.writeAll("usage: :dump <expression>\n");
        return;
    }

    var result = Pipeline.runWithInjection(
        session.gpa,
        trimmed,
        &session.intern_pool,
        .init(session.root_namespace),
    ) catch |err| {
        try stdout.print("front-end failed: {s}\n", .{@errorName(err)});
        return;
    };
    defer result.deinit(session.gpa);

    try dumpSource(result, stdout);
    if (result.hasParseErrors()) {
        try Diagnostic.renderParseErrors(result.tree, result.userView(), stdout);
        return;
    }
    try dumpAst(result.tree, stdout);
    try dumpZir(result.zir, stdout);
}

fn dumpSource(result: Pipeline.Result, stdout: *std.Io.Writer) !void {
    try stdout.print("source (wrapped, {d} bytes):\n  ", .{result.wrapped.text.len});
    try stdout.writeAll(result.wrapped.text);
    try stdout.writeAll("\n");
}

fn dumpAst(tree: Ast, stdout: *std.Io.Writer) !void {
    const root_decls = tree.rootDecls();
    try stdout.print("\nast (root_decls: {d}):\n", .{root_decls.len});
    for (root_decls, 0..) |node, i| {
        const tag = tree.nodeTag(node);
        var idx_buf: [16]u8 = undefined;
        const idx_str = std.fmt.bufPrint(&idx_buf, "[{d}]", .{i}) catch unreachable;
        if (astDeclName(tree, node, tag)) |n| {
            try stdout.print("  {s:<5}{s:<22} {s}\n", .{ idx_str, @tagName(tag), n });
        } else {
            try stdout.print("  {s:<5}{s}\n", .{ idx_str, @tagName(tag) });
        }
    }
}

/// Identifier carried by a top-level decl AST node, when the tag's
/// grammar specifies one. Returns null for decls without a
/// user-visible name (test, comptime block).
fn astDeclName(tree: Ast, node: Ast.Node.Index, tag: Ast.Node.Tag) ?[]const u8 {
    return switch (tag) {
        .simple_var_decl,
        .global_var_decl,
        .local_var_decl,
        .aligned_var_decl,
        => name: {
            // For `const X = ...;` the main token is `const` / `var`;
            // the identifier follows.
            const main_token = tree.nodeMainToken(node);
            break :name tree.tokenSlice(main_token + 1);
        },
        else => null,
    };
}

fn dumpZir(zir: Zir, stdout: *std.Io.Writer) !void {
    try stdout.print("\nzir ({d} instructions, {d} extra words, {d} string bytes):\n", .{
        zir.instructions.len,
        zir.extra.len,
        zir.string_bytes.len,
    });

    var dumper: Dumper = .{ .zir = zir, .stdout = stdout };
    const decl_insts = zir.typeDecls(.main_struct_inst);
    for (decl_insts) |decl_inst| try dumper.declaration(decl_inst);
}

/// Tree-walking dumper. `indent` tracks the current column for the
/// leading whitespace of every line written.
const Dumper = struct {
    zir: Zir,
    stdout: *std.Io.Writer,
    indent: u32 = 0,

    fn body(self: *Dumper, slice: []const Zir.Inst.Index) anyerror!void {
        for (slice) |inst| try self.instruction(inst);
    }

    /// Print one instruction line with its per-arm data summary,
    /// then recurse into any body slices the instruction owns.
    fn instruction(self: *Dumper, inst: Zir.Inst.Index) anyerror!void {
        try self.stdout.splatByteAll(' ', self.indent);
        const idx: u32 = @intFromEnum(inst);
        const tag = self.zir.instructions.items(.tag)[idx];
        const data = self.zir.instructions.items(.data)[idx];

        var idx_buf: [16]u8 = undefined;
        const idx_str = std.fmt.bufPrint(&idx_buf, "%{d}", .{idx}) catch unreachable;
        try self.stdout.print("{s:<6}{s:<22}", .{ idx_str, @tagName(tag) });
        try writeDataSummary(self.zir, tag, data, self.stdout);
        try self.stdout.writeAll("\n");

        try self.recurseBodies(inst, tag, data);
    }

    /// Walk a labelled body slice nested one indent step deeper.
    /// Skips empty bodies so the listing stays compact.
    fn section(self: *Dumper, label: []const u8, slice: []const Zir.Inst.Index) anyerror!void {
        if (slice.len == 0) return;
        try self.stdout.splatByteAll(' ', self.indent + 2);
        try self.stdout.print("{s}:\n", .{label});
        self.indent += 4;
        defer self.indent -= 4;
        try self.body(slice);
    }

    /// Top-level declaration entry: prints `decl <name>` metadata,
    /// then recurses into every body the declaration carries.
    fn declaration(self: *Dumper, decl_inst: Zir.Inst.Index) anyerror!void {
        try self.stdout.splatByteAll(' ', self.indent);
        const u = self.zir.getDeclaration(decl_inst);
        const name = if (u.name == .empty)
            "<unnamed>"
        else
            self.zir.nullTerminatedString(u.name);
        try self.stdout.print(
            "decl %{d} {s}  kind={s}  linkage={s}  pub={}\n",
            .{ @intFromEnum(decl_inst), name, @tagName(u.kind), @tagName(u.linkage), u.is_pub },
        );
        self.indent += 2;
        defer self.indent -= 2;
        if (u.type_body) |b| try self.section("type_body", b);
        if (u.align_body) |b| try self.section("align_body", b);
        if (u.linksection_body) |b| try self.section("linksection_body", b);
        if (u.addrspace_body) |b| try self.section("addrspace_body", b);
        if (u.value_body) |b| try self.section("value_body", b);
    }

    /// Per-tag body-slice descent. Covers the body-bearing payload
    /// shapes (`Block`, `BlockComptime`, `CondBr`, `Try`, `BoolBr`,
    /// `Defer`, `Func`, `FuncFancy`). Tags whose payload also carries
    /// a body but whose accessor is more involved
    /// (`switch_block` family, the `extended` opcodes that hold
    /// `struct_decl`/`union_decl`/`enum_decl`/`opaque_decl` bodies)
    /// render flat for now -- their summary still names the payload
    /// index, so a follow-up can extend this switch without changing
    /// any call sites.
    fn recurseBodies(
        self: *Dumper,
        inst: Zir.Inst.Index,
        tag: Zir.Inst.Tag,
        data: Zir.Inst.Data,
    ) anyerror!void {
        switch (tag) {
            .block, .block_inline, .loop, .suspend_block => {
                const e = self.zir.extraData(Zir.Inst.Block, data.pl_node.payload_index);
                try self.section("body", self.zir.bodySlice(e.end, e.data.body_len));
            },
            .block_comptime => {
                const e = self.zir.extraData(Zir.Inst.BlockComptime, data.pl_node.payload_index);
                try self.section("body", self.zir.bodySlice(e.end, e.data.body_len));
            },
            .condbr, .condbr_inline => {
                const e = self.zir.extraData(Zir.Inst.CondBr, data.pl_node.payload_index);
                const then_body = self.zir.bodySlice(e.end, e.data.then_body_len);
                const else_body = self.zir.bodySlice(e.end + e.data.then_body_len, e.data.else_body_len);
                try self.section("then", then_body);
                try self.section("else", else_body);
            },
            .@"try", .try_ptr => {
                const e = self.zir.extraData(Zir.Inst.Try, data.pl_node.payload_index);
                try self.section("body", self.zir.bodySlice(e.end, e.data.body_len));
            },
            .bool_br_and, .bool_br_or => {
                const e = self.zir.extraData(Zir.Inst.BoolBr, data.pl_node.payload_index);
                try self.section("rhs", self.zir.bodySlice(e.end, e.data.body_len));
            },
            .@"defer" => {
                try self.section("body", self.zir.bodySlice(data.@"defer".index, data.@"defer".len));
            },
            .func, .func_inferred, .func_fancy => {
                const info = self.zir.getFnInfo(inst);
                try self.section("param_body", info.param_body);
                try self.section("ret_ty_body", info.ret_ty_body);
                try self.section("body", info.body);
            },
            else => {},
        }
    }
};

/// Per-tag data summary. The switch is exhaustive over
/// `Zir.Inst.Tag`: adding a new tag in stdlib without updating
/// this switch is a compile error, by design.
///
/// Tag -> data-arm mapping mirrors the dispatch in
/// `src/print_zir.zig:writeInstToStream` so the categorisation
/// matches the compiler exactly.
fn writeDataSummary(
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
        .array_init,
        .array_init_anon,
        .array_init_elem_ptr,
        .array_init_ref,
        .array_type,
        .array_type_sentinel,
        .as_node,
        .as_shift_operand,
        .atomic_load,
        .atomic_rmw,
        .atomic_store,
        .bit_and,
        .bitcast,
        .bit_offset_of,
        .bit_or,
        .block,
        .block_comptime,
        .block_inline,
        .bool_br_and,
        .bool_br_or,
        .builtin_call,
        .call,
        .cmp_eq,
        .cmp_gt,
        .cmp_gte,
        .cmp_lt,
        .cmp_lte,
        .cmp_neq,
        .coerce_ptr_elem_ty,
        .condbr,
        .condbr_inline,
        .decl_literal,
        .decl_literal_no_coerce,
        .div,
        .div_exact,
        .div_floor,
        .div_trunc,
        .elem_ptr,
        .elem_ptr_load,
        .elem_ptr_node,
        .elem_val,
        .enum_from_int,
        .error_set_decl,
        .error_union_type,
        .@"export",
        .field_call,
        .field_ptr,
        .field_ptr_load,
        .field_ptr_named,
        .field_ptr_named_load,
        .field_type_ref,
        .float128,
        .float_cast,
        .float_from_int,
        .for_len,
        .func,
        .func_fancy,
        .func_inferred,
        .has_decl,
        .has_field,
        .int_cast,
        .int_from_float,
        .loop,
        .max,
        .memcpy,
        .memmove,
        .memset,
        .merge_error_sets,
        .min,
        .mod,
        .mod_rem,
        .mul,
        .mul_add,
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
        .shuffle,
        .slice_end,
        .slice_length,
        .slice_sentinel,
        .slice_start,
        .splat,
        .store_node,
        .store_to_inferred_ptr,
        .struct_init,
        .struct_init_anon,
        .struct_init_field_ptr,
        .struct_init_field_type,
        .struct_init_ref,
        .sub,
        .sub_sat,
        .subwrap,
        .suspend_block,
        .switch_block,
        .switch_block_err_union,
        .switch_block_ref,
        .truncate,
        .@"try",
        .try_ptr,
        .typeof_builtin,
        .union_init,
        .validate_array_init_ref_ty,
        .validate_array_init_result_ty,
        .validate_array_init_ty,
        .validate_destructure,
        .validate_ptr_array_init,
        .validate_ptr_struct_init,
        .vector_type,
        .xor,
        => try stdout.print(" payload={d} src_node={d}", .{ data.pl_node.payload_index, @intFromEnum(data.pl_node.src_node) }),

        .abs,
        .align_of,
        .alloc,
        .alloc_comptime_mut,
        .alloc_mut,
        .anyframe_type,
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
        .tag_name,
        .tan,
        .trunc,
        .type_info,
        .type_name,
        .typeof,
        .typeof_log2_int_type,
        .validate_const,
        .validate_deref,
        .validate_struct_init_result_ty,
        .validate_struct_init_ty,
        => try stdout.print(" operand={s} src_node={d}", .{ refLabel(data.un_node.operand), @intFromEnum(data.un_node.src_node) }),

        .ref,
        .ret_implicit,
        .validate_ref_ty,
        => try stdout.print(" operand={s} src_tok={d}", .{ refLabel(data.un_tok.operand), @intFromEnum(data.un_tok.src_tok) }),

        .import,
        .param,
        .param_comptime,
        => try stdout.print(" payload={d} src_tok={d}", .{ data.pl_tok.payload_index, @intFromEnum(data.pl_tok.src_tok) }),

        .alloc_inferred,
        .alloc_inferred_comptime,
        .alloc_inferred_comptime_mut,
        .alloc_inferred_mut,
        .repeat,
        .repeat_inline,
        .ret_ptr,
        .ret_type,
        .trap,
        => try stdout.print(" src_node={d}", .{@intFromEnum(data.node)}),

        .decl_ref,
        .decl_val,
        .enum_literal,
        .error_value,
        .param_anytype,
        .param_anytype_comptime,
        .ret_err_value,
        => try stdout.print(" \"{s}\" src_tok={d}", .{ data.str_tok.get(zir), @intFromEnum(data.str_tok.src_tok) }),

        .dbg_var_ptr,
        .dbg_var_val,
        => try stdout.print(" \"{s}\" operand={s}", .{ data.str_op.getStr(zir), refLabel(data.str_op.operand) }),

        .int_big,
        .str,
        => try stdout.print(" \"{s}\"", .{data.str.get(zir)}),

        .@"break",
        .break_inline,
        .switch_continue,
        => try stdout.print(" operand={s} payload={d}", .{ refLabel(data.@"break".operand), data.@"break".payload_index }),

        .@"unreachable"
        => try stdout.print(" src_node={d}", .{@intFromEnum(data.@"unreachable".src_node)}),

        .@"defer"
        => try stdout.print(" index={d} len={d}", .{ data.@"defer".index, data.@"defer".len }),

        .save_err_ret_index => try stdout.print(" operand={s}", .{refLabel(data.save_err_ret_index.operand)}),
        .ptr_type => try stdout.print(" size={s} payload={d}", .{ @tagName(data.ptr_type.size), data.ptr_type.payload_index }),
        .int_type => try stdout.print(" {s}{d}", .{ if (data.int_type.signedness == .signed) "i" else "u", data.int_type.bit_count }),
        .int => try stdout.print(" {d}", .{data.int}),
        .float => try stdout.print(" {d}", .{data.float}),
        .extended => try stdout.print(" opcode={s} small={d} operand={d}", .{ @tagName(data.extended.opcode), data.extended.small, data.extended.operand }),
        .elem_val_imm => try stdout.print(" operand={s} idx={d}", .{ refLabel(data.elem_val_imm.operand), data.elem_val_imm.idx }),
        .declaration => try stdout.print(" payload={d} src_node={d}", .{ data.declaration.payload_index, @intFromEnum(data.declaration.src_node) }),
        .dbg_stmt => try stdout.print(" line={d} col={d}", .{ data.dbg_stmt.line, data.dbg_stmt.column }),
        .array_init_elem_type => try stdout.print(" lhs={s} rhs={s}", .{ refLabel(data.bin.lhs), refLabel(data.bin.rhs) }),
    }
}

/// Render a `Zir.Inst.Ref` as the same `%N` shorthand used in the
/// `zir` listing. Well-known refs print under their stdlib tag name
/// (e.g. `bool_true`, `u32_type`).
fn refLabel(ref: Zir.Inst.Ref) []const u8 {
    if (ref == .none) return ".none";
    if (ref.toIndex()) |idx| {
        var buf: [16]u8 = undefined;
        return std.fmt.bufPrint(&buf, "%{d}", .{@intFromEnum(idx)}) catch unreachable;
    }
    return @tagName(ref);
}
