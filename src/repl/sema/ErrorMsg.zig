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

        pub fn nodeOffset(node_offset: Ast.Node.Offset) Offset {
            return .{ .node_offset = node_offset };
        }
    };

    pub fn resolveBaseNode(base_node_inst: Zir.Inst.Index, zir: Zir) Ast.Node.Index {
        if (base_node_inst == .main_struct_inst) return .root;
        if (@intFromEnum(base_node_inst) >= zir.instructions.len) return .root;
        const inst = zir.instructions.get(@intFromEnum(base_node_inst));
        return switch (inst.tag) {
            .declaration => inst.data.declaration.src_node,
            .struct_init, .struct_init_ref => zir.extraData(Zir.Inst.StructInit, inst.data.pl_node.payload_index).data.abs_node,
            .struct_init_anon => zir.extraData(Zir.Inst.StructInitAnon, inst.data.pl_node.payload_index).data.abs_node,
            .extended => switch (inst.data.extended.opcode) {
                .struct_decl => zir.getStructDecl(base_node_inst).src_node,
                .union_decl => zir.getUnionDecl(base_node_inst).src_node,
                .enum_decl => zir.getEnumDecl(base_node_inst).src_node,
                .opaque_decl => zir.getOpaqueDecl(base_node_inst).src_node,
                else => .root,
            },
            else => .root,
        };
    }

    pub fn resolveNode(src_loc: LazySrcLoc, zir: Zir) Ast.Node.Index {
        const base = resolveBaseNode(src_loc.base_node_inst, zir);
        return switch (src_loc.offset) {
            .unneeded => unreachable,
            .node_offset,
            .node_offset_main_token,
            .node_offset_bin_lhs,
            .node_offset_bin_rhs,
            => |off| off.toAbsolute(base),
            .node_offset_builtin_call_arg => |arg| arg.builtin_call_node.toAbsolute(base),
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
