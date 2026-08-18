const std = @import("std");
const Allocator = std.mem.Allocator;
const assert = std.debug.assert;
const Zir = std.zig.Zir;
const Ast = std.zig.Ast;

pub const LazySrcLoc = struct {
    base_node_inst: Zir.Inst.Index,
    offset: Offset,

    pub const Offset = union(enum) {
        unneeded,
        node_offset: Ast.Node.Offset,
        node_offset_main_token: Ast.Node.Offset,
        node_offset_builtin_call_arg: struct {
            builtin_call_node: Ast.Node.Offset,
            arg_index: u32,
        },
        node_offset_bin_lhs: Ast.Node.Offset,
        node_offset_bin_rhs: Ast.Node.Offset,
        /// The name of the container field at this index, relative to the base container-declaration node.
        container_field_name: u32,
        /// The value (default) expression of the container field at this index, relative to the base
        /// container-declaration node.
        container_field_value: u32,
        /// The operand (condition) of a `switch`, relative to the switch node.
        node_offset_switch_operand: Ast.Node.Offset,
        /// The `else` prong of a `switch`, relative to the switch node.
        node_offset_switch_else_prong: Ast.Node.Offset,
        /// The first range item of a `switch`, relative to the switch node.
        node_offset_switch_range: Ast.Node.Offset,
        /// The value of an item in a specific case of a `switch`.
        switch_case_item: SwitchItem,
        /// The "first" value of a range item in a specific case of a `switch`.
        switch_case_item_range_first: SwitchItem,
        /// The "last" value of a range item in a specific case of a `switch`.
        switch_case_item_range_last: SwitchItem,

        pub const SwitchItem = struct {
            switch_node_offset: Ast.Node.Offset,
            case_idx: Zir.UnwrappedSwitchBlock.Case.Index,
            item_idx: Index,

            pub const Index = packed struct(u32) {
                kind: enum(u1) { single, range },
                value: u31,
            };
        };

        pub fn nodeOffset(node_offset: Ast.Node.Offset) Offset {
            return .{ .node_offset = node_offset };
        }
    };

    pub fn resolveBaseNode(base_node_inst: Zir.Inst.Index, zir: Zir) Ast.Node.Index {
        if (base_node_inst == .main_struct_inst) return .root;
        if (@backingInt(base_node_inst) >= zir.instructions.len) return .root;
        const inst = zir.instructions.get(@backingInt(base_node_inst));
        return switch (inst.tag) {
            .declaration => inst.data.declaration.src_node,
            .struct_init, .struct_init_ref => zir.extraData(Zir.Inst.StructInit, inst.data.pl_node.payload_index).data.abs_node,
            .struct_init_anon => zir.extraData(Zir.Inst.StructInitAnon, inst.data.pl_node.payload_index).data.abs_node,
            .extended => switch (inst.data.extended.opcode) {
                .struct_decl => zir.getStructDecl(base_node_inst).src_node,
                .union_decl => zir.getUnionDecl(base_node_inst).src_node,
                .enum_decl => zir.getEnumDecl(base_node_inst).src_node,
                .opaque_decl => zir.getOpaqueDecl(base_node_inst).src_node,
                .reify_enum => zir.extraData(Zir.Inst.ReifyEnum, inst.data.extended.operand).data.node,
                .reify_struct => zir.extraData(Zir.Inst.ReifyStruct, inst.data.extended.operand).data.node,
                .reify_union => zir.extraData(Zir.Inst.ReifyUnion, inst.data.extended.operand).data.node,
                .reify_spirv_type => zir.extraData(Zir.Inst.ReifySpirvType, inst.data.extended.operand).data.node,
                else => .root,
            },
            else => .root,
        };
    }

    pub fn resolveNode(src_loc: LazySrcLoc, zir: Zir, tree: Ast) Ast.Node.Index {
        const base = resolveBaseNode(src_loc.base_node_inst, zir);
        return switch (src_loc.offset) {
            .unneeded => unreachable,
            .node_offset,
            .node_offset_main_token,
            .node_offset_bin_lhs,
            .node_offset_bin_rhs,
            => |off| off.toAbsolute(base),
            .node_offset_builtin_call_arg => |arg| {
                var buf: [2]Ast.Node.Index = undefined;
                const params = tree.builtinCallParams(&buf, arg.builtin_call_node.toAbsolute(base)).?;
                return params[arg.arg_index];
            },
            .container_field_value, .container_field_name => |field_idx| {
                const want_name = src_loc.offset == .container_field_name;
                var buf: [2]Ast.Node.Index = undefined;
                const container_decl = tree.fullContainerDecl(&buf, base) orelse {
                    // A reification builtin: field names are arg 2; values are `@Enum` arg 3, `@Struct`/`@Union` arg 4.
                    if (tree.builtinCallParams(&buf, base)) |args| {
                        const builtin_name = tree.tokenSlice(tree.firstToken(base));
                        const arg_index: ?usize = if (want_name)
                            2
                        else if (std.mem.eql(u8, builtin_name, "@Enum"))
                            3
                        else if (std.mem.eql(u8, builtin_name, "@Struct") or std.mem.eql(u8, builtin_name, "@Union"))
                            4
                        else
                            null;
                        if (arg_index) |i| if (args.len > i) return args[i];
                    }
                    return base;
                };
                var cur_field_idx: u32 = 0;
                for (container_decl.ast.members) |member_node| {
                    const field = tree.fullContainerField(member_node) orelse continue;
                    if (cur_field_idx < field_idx) {
                        cur_field_idx += 1;
                        continue;
                    }
                    if (want_name) return member_node;
                    return field.ast.value_expr.unwrap() orelse member_node;
                }
                return base;
            },
            .node_offset_switch_operand => |node_off| {
                const switch_node = node_off.toAbsolute(base);
                const condition, _ = tree.nodeData(switch_node).node_and_extra;
                return condition;
            },
            .node_offset_switch_else_prong => |node_off| {
                const switch_node = node_off.toAbsolute(base);
                _, const extra_index = tree.nodeData(switch_node).node_and_extra;
                const case_nodes = tree.extraDataSlice(tree.extraData(extra_index, Ast.Node.SubRange), Ast.Node.Index);
                for (case_nodes) |case_node| {
                    const case = tree.fullSwitchCase(case_node).?;
                    if (case.ast.values.len == 0) return case_node;
                } else unreachable;
            },
            .node_offset_switch_range => |node_off| {
                const switch_node = node_off.toAbsolute(base);
                _, const extra_index = tree.nodeData(switch_node).node_and_extra;
                const case_nodes = tree.extraDataSlice(tree.extraData(extra_index, Ast.Node.SubRange), Ast.Node.Index);
                for (case_nodes) |case_node| {
                    const case = tree.fullSwitchCase(case_node).?;
                    for (case.ast.values) |item_node| {
                        if (tree.nodeTag(item_node) == .switch_range) return item_node;
                    }
                }
                unreachable;
            },
            .switch_case_item,
            .switch_case_item_range_first,
            .switch_case_item_range_last,
            => |item| {
                const switch_node = item.switch_node_offset.toAbsolute(base);
                _, const extra_index = tree.nodeData(switch_node).node_and_extra;
                const case_nodes = tree.extraDataSlice(tree.extraData(extra_index, Ast.Node.SubRange), Ast.Node.Index);

                var multi_i: u32 = 0;
                var scalar_i: u32 = 0;
                const case: Ast.full.SwitchCase = case: for (case_nodes) |case_node| {
                    const case = tree.fullSwitchCase(case_node).?;
                    if (case.ast.values.len == 0) continue;
                    const is_multi = case.ast.values.len != 1 or tree.nodeTag(case.ast.values[0]) == .switch_range;
                    switch (item.case_idx.kind) {
                        .scalar => if (!is_multi and item.case_idx.value == scalar_i) break :case case,
                        .multi => if (is_multi and item.case_idx.value == multi_i) break :case case,
                    }
                    if (is_multi) {
                        multi_i += 1;
                    } else {
                        scalar_i += 1;
                    }
                } else unreachable;

                switch (item.item_idx.kind) {
                    .single => {
                        var item_i: u32 = 0;
                        for (case.ast.values) |item_node| {
                            if (tree.nodeTag(item_node) == .switch_range) continue;
                            if (item_i != item.item_idx.value) {
                                item_i += 1;
                                continue;
                            }
                            return item_node;
                        } else unreachable;
                    },
                    .range => {
                        var range_i: u32 = 0;
                        for (case.ast.values) |item_node| {
                            if (tree.nodeTag(item_node) != .switch_range) continue;
                            if (range_i != item.item_idx.value) {
                                range_i += 1;
                                continue;
                            }
                            const first, const last = tree.nodeData(item_node).node_and_node;
                            return switch (src_loc.offset) {
                                .switch_case_item => item_node,
                                .switch_case_item_range_first => first,
                                .switch_case_item_range_last => last,
                                else => unreachable,
                            };
                        } else unreachable;
                    },
                }
            },
        };
    }
};

pub const ErrorMsg = struct {
    src_loc: LazySrcLoc,
    msg: []const u8,
    notes: []ErrorMsg = &.{},
    file: u32 = 0,

    pub fn create(gpa: Allocator, src_loc: LazySrcLoc, comptime format: []const u8, args: anytype) !*ErrorMsg {
        assert(src_loc.offset != .unneeded);
        const err_msg = try gpa.create(ErrorMsg);
        errdefer gpa.destroy(err_msg);
        err_msg.* = try ErrorMsg.init(gpa, src_loc, format, args);
        return err_msg;
    }

    pub fn init(gpa: Allocator, src_loc: LazySrcLoc, comptime format: []const u8, args: anytype) !ErrorMsg {
        return .{
            .src_loc = src_loc,
            .msg = try std.fmt.allocPrint(gpa, format, args),
        };
    }

    pub fn destroy(err_msg: *ErrorMsg, gpa: Allocator) void {
        err_msg.deinit(gpa);
        gpa.destroy(err_msg);
    }

    pub fn deinit(err_msg: *ErrorMsg, gpa: Allocator) void {
        for (err_msg.notes) |*note| note.deinit(gpa);
        gpa.free(err_msg.notes);
        gpa.free(err_msg.msg);
        err_msg.* = undefined;
    }
};
