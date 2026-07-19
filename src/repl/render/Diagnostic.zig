const std = @import("std");
const assert = std.debug.assert;

const Pipeline = @import("../front/Pipeline.zig");
const ZirErrors = @import("../front/ZirErrors.zig");

const max_renderable_parse_errors: u32 = 64;
pub const repl_source_path: []const u8 = "<repl>";

/// A sub-note on a Sema error: the compiler's `ErrorMsg.notes`, each already
/// resolved to an absolute AST node by the driver (which holds the ZIR).
pub const Note = struct {
    node: std.zig.Ast.Node.Index,
    msg: []const u8,
};

/// Render a Sema error anchored at `node`, with its `notes`, through the same
/// `std.zig.ErrorBundle` path the compiler and `ZirErrors` use, so the source line
/// + caret + `note:` lines match std's output exactly. A node that anchors entirely
/// in the injected wrap prefix (`view.translate` returns null) is emitted without a
/// source location.
pub fn renderSemaError(
    gpa: std.mem.Allocator,
    src_path: []const u8,
    tree: std.zig.Ast,
    view: Pipeline.UserView,
    node: std.zig.Ast.Node.Index,
    msg: []const u8,
    notes: []const Note,
    writer: *std.Io.Writer,
) !void {
    var wip: std.zig.ErrorBundle.Wip = undefined;
    try wip.init(gpa);
    defer wip.deinit();

    const note_ems = try gpa.alloc(std.zig.ErrorBundle.ErrorMessage, notes.len);
    defer gpa.free(note_ems);
    for (note_ems, notes) |*ne, n| {
        ne.* = .{
            .msg = try wip.addString(n.msg),
            .src_loc = try sourceLocation(&wip, src_path, tree, view, n.node),
            .notes_len = 0,
        };
    }

    try wip.addRootErrorMessageWithNotes(.{
        .msg = try wip.addString(msg),
        .src_loc = try sourceLocation(&wip, src_path, tree, view, node),
        .notes_len = @intCast(notes.len),
    }, note_ems);

    var bundle = try wip.toOwnedBundle("");
    defer bundle.deinit(gpa);
    try bundle.renderToWriter(.{}, writer);
}

/// The `ErrorBundle` source location for `node` translated into the user's frame,
/// or `.none` when `node` anchors entirely in the injected wrap prefix.
fn sourceLocation(
    wip: *std.zig.ErrorBundle.Wip,
    src_path: []const u8,
    tree: std.zig.Ast,
    view: Pipeline.UserView,
    node: std.zig.Ast.Node.Index,
) !std.zig.ErrorBundle.SourceLocationIndex {
    const span = view.translate(tree.nodeToSpan(node)) orelse return .none;
    const loc = view.findLoc(span.main);
    return try wip.addSourceLocation(.{
        .src_path = try wip.addString(src_path),
        .span_start = span.start,
        .span_main = span.main,
        .span_end = span.end,
        .line = @intCast(loc.line),
        .column = @intCast(loc.column),
        .source_line = try wip.addString(loc.source_line),
    });
}

/// Render parse errors with positions translated into the user's
/// coordinate frame.
///
/// The Ast is parsed against the wrapped source (`const __repl_input
/// = (<user>);` for expression shape), so a token's column inside
/// the wrap leaks the prefix bytes into the diagnostic. The
/// translation is essentially free: `std.zig.Ast.tokenLocation`
/// takes a `start_offset` parameter to begin line/column counting
/// from. Pass `view.offset_in_source` and the returned `Location`
/// already lives in the user's frame -- multi-line-safe because
/// tokenLocation walks newlines itself. When the offending token
/// lands in the suffix wrap we substitute a clean "unexpected end of
/// input" message instead of `renderError`'s `, found ')'`.
pub fn renderParseErrors(
    tree: std.zig.Ast,
    view: Pipeline.UserView,
    writer: *std.Io.Writer,
) std.Io.Writer.Error!void {
    assert(tree.errors.len > 0);

    const user_end = view.offset_in_source + @as(u32, @intCast(view.text.len));

    var rendered: u32 = 0;
    var last_token_offset: ?u32 = null;
    for (tree.errors) |parse_error| {
        if (rendered >= max_renderable_parse_errors) {
            try writer.writeAll("... further parse errors elided\n");
            break;
        }
        // Cascade suppression: when the parser fires multiple errors
        // anchored at the same byte, only the first is the root
        // cause; the rest are recovery noise (often referencing the
        // wrapper's `)` for expression shape). One error per
        // position keeps the stream focused on what the user can act
        // on.
        const token_offset = tree.tokenStart(parse_error.token);
        if (last_token_offset) |prev| {
            if (prev == token_offset) continue;
        }
        last_token_offset = token_offset;
        try renderOneParseError(tree, parse_error, view.offset_in_source, user_end, writer);
        rendered += 1;
    }
}

fn renderOneParseError(
    tree: std.zig.Ast,
    parse_error: std.zig.Ast.Error,
    user_offset: u32,
    user_end: u32,
    writer: *std.Io.Writer,
) std.Io.Writer.Error!void {
    assert(user_end >= user_offset);

    const token_offset = tree.tokenStart(parse_error.token);
    const loc = tree.tokenLocation(user_offset, parse_error.token);
    const line_text = loc.line + 1;
    const col_text = loc.column + 1;

    if (token_offset >= user_end) {
        return writer.print("{s}:{d}:{d}: parse error: unexpected end of input\n", .{
            repl_source_path,
            line_text,
            col_text,
        });
    }

    try writer.print("{s}:{d}:{d}: parse error: ", .{ repl_source_path, line_text, col_text });
    try tree.renderError(parse_error, writer);
    try writer.writeAll("\n");
}

/// Render ZIR errors via `ZirErrors.renderActionable`. When every
/// diagnostic anchors on a wrap-injected line (cross-line rebind
/// is the canonical case), `renderActionable` emits nothing -- so
/// surface a fallback line, otherwise the user sees a silent
/// success indistinguishable from a clean declaration.
pub fn renderZirErrors(
    gpa: std.mem.Allocator,
    zir: std.zig.Zir,
    tree: std.zig.Ast,
    view: Pipeline.UserView,
    writer: *std.Io.Writer,
) !void {
    assert(zir.hasCompileErrors());
    assert(view.text.len > 0);

    const emitted = try ZirErrors.renderActionable(gpa, zir, tree, view, repl_source_path, writer);
    if (emitted == 0) {
        try writer.print(
            "{s}: error: a compile error was reported but could not be located" ++
                " in your input (likely a conflict with a prior session binding)\n",
            .{repl_source_path},
        );
    }
}
