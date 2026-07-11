//! Structured analysis errors and their source locations, shared between the
//! analyzer (which produces them) and the session (which holds them for the
//! driver to render). Mirrors `Zcu.ErrorMsg` and `Zcu.LazySrcLoc`, which live
//! together in the compiler's `Zcu`; the REPL keeps them in a leaf module so
//! `Session` can own an `*ErrorMsg` without importing the analyzer.

const std = @import("std");
const Allocator = std.mem.Allocator;
const assert = std.debug.assert;
const Zir = std.zig.Zir;
const Ast = std.zig.Ast;

/// Mirrors `Zcu.LazySrcLoc`. `base_node_inst` is the instruction whose
/// declaration node the `offset` is measured against. The compiler uses a
/// cross-file `InternPool.TrackedInst.Index`; the REPL is single-file, so a
/// plain `Zir.Inst.Index` suffices (the one field that legitimately does not
/// port). The driver, which holds the AST, turns the resolved node into a span.
pub const LazySrcLoc = struct {
    base_node_inst: Zir.Inst.Index,
    offset: Offset,

    /// Mirrors `Zcu.LazySrcLoc.Offset`. Only the variants the REPL currently
    /// constructs are listed; adding a new source-location kind trips the
    /// exhaustive switch in `resolveNode`, which is where its AST navigation is
    /// added.
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

    /// The declaration node the `offset` is relative to. Mirrors
    /// `Zcu.resolveBaseNode`'s `.declaration` arm; the base is always a
    /// declaration instruction (the block's `src_base_inst`), single-file, so
    /// the compiler's `TrackedInst`/multi-tag resolution collapses to one read.
    pub fn resolveBaseNode(base_node_inst: Zir.Inst.Index, zir: Zir) Ast.Node.Index {
        return zir.instructions.items(.data)[@intFromEnum(base_node_inst)].declaration.src_node;
    }

    /// The absolute AST node the caret anchors on: the base declaration node with
    /// `offset` applied. Mirrors the node `Zcu.SrcLoc.span` resolves before taking
    /// a byte span; the driver applies `tree.nodeToSpan` to the result. The
    /// builtin-call-arg / bin-operand navigation `span` performs with the tree is
    /// not yet modeled -- those resolve to the enclosing call / operator node.
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

/// Mirrors `Zcu.ErrorMsg`: a message anchored at a source location, with
/// sub-notes. The `reference_trace_root` field the compiler carries has no REPL
/// analog (no cross-unit reference tracing). Allocated with `gpa` (message and
/// notes included) so it outlives the analyzer's arena, exactly as the compiler
/// keeps `failed_analysis` entries alive past a `Sema`.
pub const ErrorMsg = struct {
    src_loc: LazySrcLoc,
    msg: []const u8,
    notes: []ErrorMsg = &.{},

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
