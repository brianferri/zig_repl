//! Source-mapped structured view of one input's lowering for the web explorer: JSON `{ source, ast, zir }`,
//! each node/instruction bound to its source byte range by AST node identity, not overlapping spans.

const std = @import("std");
const Ast = std.zig.Ast;
const Zir = std.zig.Zir;
const Json = std.json.Stringify;

const repl = @import("repl");
const Pipeline = repl.front.Pipeline;
const Session = repl.Session;
const eval = repl.eval;
const InputShape = repl.front.InputShape;
const ZirWalk = repl.front.ZirWalk;
const ZirSummary = repl.render.ZirSummary;

const UserView = Pipeline.UserView;

/// Shift applied to a segment's ids and spans when several segments share one outline.
const Offset = struct {
    /// Shifts the segment's AST node ids (and the ZIR `node` refs into them) past the previous segment's.
    id: u32 = 0,
    /// Shifts the segment's spans to its place in the full source.
    byte: u32 = 0,
};

const Segment = struct {
    result: *const Pipeline.Result,
    off: Offset,
};

/// Outlines `source` as JSON `{ source, ast, zir }`; the arrays are empty on a front-end failure.
/// Declarations + a trailing expression can't share one parse (a container rejects a bare expression), so
/// they run as two segments and merge -- the declarations bind so the expression run resolves them, and
/// the expression segment is shifted past them in id and byte space.
pub fn writeJson(session: *Session, source: []const u8, w: *std.Io.Writer) !void {
    const split = InputShape.splitTrailingExpr(session.gpa, source) catch null;
    if (split) |s| {
        var decls = Pipeline.runWithInjection(session.gpa, s.decls, session.intern_pool, .init(session.root_namespace)) catch return emitEmpty(w, null);
        defer decls.deinit(session.gpa);
        // Bind the declarations so the expression run's ZIR resolves their
        // names; a failed bind still emits both ASTs.
        _ = eval.run(session, s.decls, w) catch {};
        var expr = Pipeline.runWithInjection(session.gpa, s.expr, session.intern_pool, .init(session.root_namespace)) catch return emitEmpty(w, null);
        defer expr.deinit(session.gpa);
        const expr_off: Offset = .{
            .id = @intCast(decls.tree.nodes.len),
            .byte = @intCast(@intFromPtr(s.expr.ptr) - @intFromPtr(source.ptr)),
        };
        try emitOutline(session.gpa, w, source, &.{
            .{ .result = &decls, .off = .{} },
            .{ .result = &expr, .off = expr_off },
        });
        return;
    }

    var result = Pipeline.runWithInjection(session.gpa, source, session.intern_pool, .init(session.root_namespace)) catch return emitEmpty(w, null);
    defer result.deinit(session.gpa);
    try emitOutline(session.gpa, w, source, &.{.{ .result = &result, .off = .{} }});
}

/// Emit an empty `{ source, ast, zir }` outline, optionally carrying an
/// `error` field for a front-end failure that produced no nodes.
pub fn emitEmpty(w: *std.Io.Writer, message: ?[]const u8) !void {
    const Empty = struct {
        source: []const u8 = "",
        ast: []const u32 = &[_]u32{},
        zir: []const u32 = &[_]u32{},
        @"error": ?[]const u8 = null,
    };
    var json: Json = .{ .writer = w, .options = .{ .emit_null_optional_fields = false } };
    try json.write(Empty{ .@"error" = message });
}

/// Emits the merged `{ source, ast, zir }`. Nodes mapping into injected/prelude bytes are dropped; the
/// rest are shifted by the segment's `off`.
fn emitOutline(gpa: std.mem.Allocator, w: *std.Io.Writer, source: []const u8, segments: []const Segment) !void {
    var json: Json = .{ .writer = w, .options = .{ .emit_null_optional_fields = false } };
    try json.beginObject();
    try json.objectField("source");
    try json.write(source);

    try json.objectField("ast");
    try json.beginArray();
    for (segments) |seg| {
        if (seg.result.hasParseErrors()) continue;
        const tree = seg.result.tree;
        const view = seg.result.userView();
        for (tree.rootDecls()) |decl| {
            try emitAstNode(&json, tree, view, outlineNode(tree, decl), seg.off);
        }
    }
    try json.endArray();

    try json.objectField("zir");
    try json.beginArray();
    for (segments) |seg| {
        if (seg.result.hasParseErrors() or seg.result.hasZirErrors()) continue;
        const zir = seg.result.zir;
        const view = seg.result.userView();
        var scratch: std.Io.Writer.Allocating = .init(gpa);
        defer scratch.deinit();
        var sink: ZirSink = .{ .json = &json, .zir = zir, .scratch = &scratch, .id_offset = seg.off.id };
        const datas = zir.instructions.items(.data);
        // Skip injected-prelude decls (their node maps into hidden bytes), but always walk the expression
        // wrapper -- its own node is injected, yet its body holds the user expression.
        for (zir.typeDecls(.main_struct_inst)) |decl_inst| {
            const decl_node = datas[@backingInt(decl_inst)].declaration.src_node;
            if (!isWrapperDecl(seg.result.tree, decl_node) and
                view.translate(seg.result.tree.nodeToSpan(decl_node)) == null) continue;
            try ZirWalk.walkDecl(ZirSink, zir, decl_inst, &sink);
        }
    }
    try json.endArray();

    try json.endObject();
}

/// For an expression input (wrapped in a function whose local binds `( EXPR )`), dives to that initializer
/// and unwraps the parens to EXPR; any other declaration is its own node.
fn outlineNode(tree: Ast, decl: Ast.Node.Index) Ast.Node.Index {
    if (tree.nodeTag(decl) != .fn_decl or !isWrapperDecl(tree, decl)) return decl;
    const body = tree.nodeData(decl).node_and_node[1];
    const first_stmt = switch (tree.nodeTag(body)) {
        .block_two, .block_two_semicolon => tree.nodeData(body).opt_node_and_opt_node[0].unwrap() orelse return decl,
        else => return decl,
    };
    if (tree.nodeTag(first_stmt) != .simple_var_decl) return decl;
    const init = tree.nodeData(first_stmt).opt_node_and_opt_node[1].unwrap() orelse return decl;
    if (tree.nodeTag(init) == .grouped_expression) {
        return tree.nodeData(init).node_and_token[0];
    }
    return init;
}

fn isWrapperDecl(tree: Ast, decl: Ast.Node.Index) bool {
    const name = tree.tokenSlice(tree.nodeMainToken(decl) + 1);
    return std.mem.eql(u8, name, InputShape.expression_decl_name);
}

/// A node mapping into the injected wrap, not the user's text, drops out with its subtree.
fn emitAstNode(json: *Json, tree: Ast, view: UserView, node: Ast.Node.Index, off: Offset) anyerror!void {
    const span = view.translate(tree.nodeToSpan(node)) orelse return;
    try json.beginObject();
    try json.objectField("id");
    try json.write(@backingInt(node) + off.id);
    try json.objectField("label");
    try json.write(@tagName(tree.nodeTag(node)));
    try json.objectField("lo");
    try json.write(span.start + off.byte);
    try json.objectField("hi");
    try json.write(span.end + off.byte);
    try json.objectField("children");
    try json.beginArray();
    try emitChildren(json, tree, view, node, off);
    try json.endArray();
    try json.endObject();
}

/// The AST has no generic child iterator, so children are read per tag from the slots its grammar fills;
/// an unhandled tag is a leaf. `fn_proto` is left a leaf on purpose -- its parameter names are tokens,
/// not nodes.
fn emitChildren(json: *Json, tree: Ast, view: UserView, node: Ast.Node.Index, off: Offset) anyerror!void {
    switch (tree.nodeTag(node)) {
        .mul,
        .div,
        .mod,
        .mul_wrap,
        .mul_sat,
        .add,
        .sub,
        .add_wrap,
        .sub_wrap,
        .add_sat,
        .sub_sat,
        .shl,
        .shl_sat,
        .shr,
        .bit_and,
        .bit_xor,
        .bit_or,
        .bool_and,
        .bool_or,
        .equal_equal,
        .bang_equal,
        .less_than,
        .greater_than,
        .less_or_equal,
        .greater_or_equal,
        => {
            const lhs, const rhs = tree.nodeData(node).node_and_node;
            try emitAstNode(json, tree, view, lhs, off);
            try emitAstNode(json, tree, view, rhs, off);
        },

        .negation,
        .negation_wrap,
        .bit_not,
        .bool_not,
        .address_of,
        .optional_type,
        => try emitAstNode(json, tree, view, tree.nodeData(node).node, off),

        .grouped_expression => try emitAstNode(json, tree, view, tree.nodeData(node).node_and_token[0], off),

        .fn_decl => {
            const proto, const body = tree.nodeData(node).node_and_node;
            try emitAstNode(json, tree, view, proto, off);
            try emitAstNode(json, tree, view, body, off);
        },

        .block,
        .block_semicolon,
        .block_two,
        .block_two_semicolon,
        => {
            var buf: [2]Ast.Node.Index = undefined;
            for (tree.blockStatements(&buf, node).?) |stmt| try emitAstNode(json, tree, view, stmt, off);
        },

        .call,
        .call_comma,
        .call_one,
        .call_one_comma,
        => {
            var buf: [1]Ast.Node.Index = undefined;
            const c = tree.fullCall(&buf, node).?;
            try emitAstNode(json, tree, view, c.ast.fn_expr, off);
            for (c.ast.params) |arg| try emitAstNode(json, tree, view, arg, off);
        },

        .@"return" => {
            if (tree.nodeData(node).opt_node.unwrap()) |operand| try emitAstNode(json, tree, view, operand, off);
        },

        .simple_var_decl => {
            if (tree.nodeData(node).opt_node_and_opt_node[1].unwrap()) |init| {
                try emitAstNode(json, tree, view, init, off);
            }
        },

        else => {},
    }
}

/// `ZirWalk` sink emitting the instruction tree as JSON. A section header has no `detail`/`node`; an
/// instruction carries its summary (`detail`) and the AST node it lowered from (`node`, when its shape
/// resolves one).
const ZirSink = struct {
    json: *Json,
    zir: Zir,
    scratch: *std.Io.Writer.Allocating,
    /// Shift for the `node` refs so they key into this segment's AST ids (see `Offset`).
    id_offset: u32 = 0,

    // Declarations are elided so their bodies surface as top-level sections (hides the `__repl_input` wrapper).
    pub fn openDeclaration(self: *ZirSink, decl_inst: Zir.Inst.Index, base: Ast.Node.Index) !void {
        _ = self;
        _ = decl_inst;
        _ = base;
    }

    pub fn closeDeclaration(self: *ZirSink) !void {
        _ = self;
    }

    pub fn openSection(self: *ZirSink, label: []const u8) !void {
        try self.open(label, null, null);
    }

    pub fn closeSection(self: *ZirSink) !void {
        try self.close();
    }

    pub fn openInstruction(
        self: *ZirSink,
        inst: Zir.Inst.Index,
        tag: Zir.Inst.Tag,
        data: Zir.Inst.Data,
        base: Ast.Node.Index,
    ) !void {
        _ = inst;
        self.scratch.clearRetainingCapacity();
        ZirSummary.write(self.zir, tag, data, &self.scratch.writer) catch {};
        const detail = std.mem.trim(u8, self.scratch.written(), " ");
        const node = instNode(base, tag, data);
        try self.open(
            @tagName(tag),
            if (node) |n| @backingInt(n) + self.id_offset else null,
            if (detail.len > 0) detail else null,
        );
    }

    pub fn closeInstruction(self: *ZirSink) !void {
        try self.close();
    }

    fn open(self: *ZirSink, label: []const u8, node: ?u32, detail: ?[]const u8) !void {
        try self.json.beginObject();
        try self.json.objectField("label");
        try self.json.write(label);
        if (detail) |d| {
            try self.json.objectField("detail");
            try self.json.write(d);
        }
        if (node) |n| {
            try self.json.objectField("node");
            try self.json.write(n);
        }
        try self.json.objectField("children");
        try self.json.beginArray();
    }

    fn close(self: *ZirSink) !void {
        try self.json.endArray();
        try self.json.endObject();
    }
};

/// The AST node an instruction lowered from, or null when it has no source node. A ZIR `src_node` is
/// relative to its enclosing declaration (`base`), so this lifts it to an absolute `Ast` node index; only
/// verified shapes are mapped.
fn instNode(base: Ast.Node.Index, tag: Zir.Inst.Tag, data: Zir.Inst.Data) ?Ast.Node.Index {
    return switch (tag) {
        .add,
        .addwrap,
        .add_sat,
        .sub,
        .subwrap,
        .sub_sat,
        .mul,
        .mulwrap,
        .mul_sat,
        .div,
        .mod_rem,
        .mod,
        .rem,
        .shl,
        .shr,
        .bit_and,
        .bit_or,
        .xor,
        .cmp_eq,
        .cmp_neq,
        .cmp_lt,
        .cmp_lte,
        .cmp_gt,
        .cmp_gte,
        .as_node,
        => data.pl_node.src_node.toAbsolute(base),

        .negate,
        .negate_wrap,
        .bit_not,
        .bool_not,
        => data.un_node.src_node.toAbsolute(base),

        else => null,
    };
}
