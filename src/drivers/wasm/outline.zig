//! Source-mapped structured view of one input's lowering, for the web
//! explorer. Emits JSON: the user source, plus AST nodes and ZIR
//! instructions each tagged with the byte range of user text it came from
//! (`lo`/`hi`), or no range when it maps into injected/synthetic bytes or
//! an instruction shape this resolver does not handle. A missing range is
//! an honest gap; a wrong range would silently misrepresent the lowering,
//! so unresolved shapes degrade to "unmapped" rather than guess.
//!
//! ZIR source resolution mirrors `src/print_zir.zig`: a body instruction's
//! `src_node` is an `Ast.Node.Offset` relative to the enclosing
//! declaration's node, made absolute via `toAbsolute(decl_node)`, then
//! `nodeToSpan` + `UserView.translate` into the user's frame. Only a
//! declaration's direct bodies are walked (no sub-body or nested-decl
//! recursion yet), so instructions inside blocks / nested declarations are
//! currently unmapped.

const std = @import("std");
const Ast = std.zig.Ast;
const Zir = std.zig.Zir;
const Json = std.json.Stringify;

const Pipeline = @import("../../front/Pipeline.zig");
const Session = @import("../../Session.zig");

const UserView = Pipeline.UserView;

/// One mapped node/instruction. `lo`/`hi` are user-source byte offsets,
/// omitted from the JSON when unmapped (`emit_null_optional_fields`).
const Item = struct {
    label: []const u8,
    lo: ?u32 = null,
    hi: ?u32 = null,

    fn from(label: []const u8, span: ?Ast.Span) Item {
        return if (span) |s| .{ .label = label, .lo = s.start, .hi = s.end } else .{ .label = label };
    }
};

/// Run the front end on `input` against `session` and write the lowering
/// as JSON `{ source, ast, zir }` to `w`. On a front-end failure the AST
/// and ZIR arrays are empty (the explorer falls back to diagnostics).
pub fn writeJson(session: *Session, input: []const u8, w: *std.Io.Writer) !void {
    var result = Pipeline.runWithInjection(
        session.gpa,
        input,
        session.intern_pool,
        .init(session.root_namespace),
    ) catch {
        try w.writeAll("{\"source\":\"\",\"ast\":[],\"zir\":[]}");
        return;
    };
    defer result.deinit(session.gpa);

    const view = result.userView();
    var json: Json = .{ .writer = w, .options = .{ .emit_null_optional_fields = false } };

    try json.beginObject();
    try json.objectField("source");
    try json.write(view.text);

    try json.objectField("ast");
    try json.beginArray();
    if (!result.hasParseErrors()) try emitAst(&json, result.tree, view);
    try json.endArray();

    try json.objectField("zir");
    try json.beginArray();
    if (!result.hasParseErrors() and !result.hasZirErrors()) try emitZir(&json, result.zir, result.tree, view);
    try json.endArray();

    try json.endObject();
}

fn emitAst(json: *Json, tree: Ast, view: UserView) !void {
    var i: u32 = 1; // skip the root node (spans the whole file)
    while (i < tree.nodes.len) : (i += 1) {
        const node: Ast.Node.Index = @enumFromInt(i);
        const user = view.translate(tree.nodeToSpan(node)) orelse continue;
        try json.write(Item.from(@tagName(tree.nodeTag(node)), user));
    }
}

fn emitZir(json: *Json, zir: Zir, tree: Ast, view: UserView) !void {
    if (zir.instructions.len == 0) return;
    const tags = zir.instructions.items(.tag);
    const datas = zir.instructions.items(.data);
    for (zir.typeDecls(.main_struct_inst)) |decl_inst| {
        // The declaration's own node (already absolute) is the base for its
        // body instructions' relative `src_node` offsets (parent_decl_node
        // in print_zir terms).
        const decl_node = datas[@intFromEnum(decl_inst)].declaration.src_node;
        const decl = zir.getDeclaration(decl_inst);
        for ([_]?[]const Zir.Inst.Index{ decl.type_body, decl.value_body }) |maybe_body| {
            const body = maybe_body orelse continue;
            for (body) |inst| {
                const idx = @intFromEnum(inst);
                try json.write(Item.from(@tagName(tags[idx]), instSpan(tree, view, decl_node, tags[idx], datas[idx])));
            }
        }
    }
}

/// User-frame span of one instruction, or null when its shape carries no
/// resolvable source node (or it maps into synthetic bytes). Only the
/// shapes whose mapping is verified are handled; the rest stay unmapped.
fn instSpan(
    tree: Ast,
    view: UserView,
    base_node: Ast.Node.Index,
    tag: Zir.Inst.Tag,
    data: Zir.Inst.Data,
) ?Ast.Span {
    const wrapped: Ast.Span = switch (tag) {
        // Binary ops + coercion carry `pl_node.src_node`.
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
        => tree.nodeToSpan(data.pl_node.src_node.toAbsolute(base_node)),

        // Unary ops carry `un_node.src_node`.
        .negate,
        .negate_wrap,
        .bit_not,
        .bool_not,
        => tree.nodeToSpan(data.un_node.src_node.toAbsolute(base_node)),

        // Everything else (token-relative shapes like `decl_val`, literals
        // with no source node, control-flow terminators) stays unmapped --
        // their AST nodes still carry the source range.
        else => return null,
    };
    return view.translate(wrapped);
}
