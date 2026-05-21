//! Filters AstGen's compile-error stream against a REPL-specific
//! suppression criterion. The compiler treats `var x = 7;` with no
//! syntactic mutation as a hard error ("local variable is never
//! mutated", `std/zig/AstGen.zig:3113`) to push users toward
//! `const`. For a REPL that is *advisory*: mutability is a Sema-time
//! concern enforced by `evalStoreNode`'s `is_const` check against the
//! pointer type, not a parsing concern. Surfacing the warning would
//! block one-shot lines like `var x: u8 = 7; break :blk x;` for no
//! semantic reason.
//!
//! Suppression keys on the AST shape of the error anchor, not the
//! message text:
//!
//!   * AstGen anchors `local_var_*` advisories on the var's name
//!     identifier token (`s.token_src = name_token` at
//!     `std/zig/AstGen.zig:11212`, used at lines 3105 + 3113).
//!   * In Zig grammar, an identifier token is preceded by
//!     `keyword_var` exactly when it is the name in a `var_decl`.
//!     No other production places those tokens adjacent.
//!
//! So `tree.tokenTag(token-1) == .keyword_var` is a structural
//! fingerprint for "this diagnostic anchors on a var-decl name" --
//! insensitive to AstGen rewording, sensitive only to grammar shape.
//!
//! All wrap-shape knowledge -- where the user's text begins, which
//! spans anchor in synthesized wrap-injection bytes -- lives in
//! `Pipeline.UserView`. This module asks `view.translate(span)` and
//! drops or emits based on the answer, never inspecting wrap
//! offsets directly.
//!
//! Per-item walk mirrors `std.zig.ErrorBundle.Wip.addZirErrorMessages`
//! (~line 502) so span / source-location / notes plumbing stays
//! bit-identical to what `zig` itself would render.

const std = @import("std");
const assert = std.debug.assert;

const Zir = std.zig.Zir;
const ErrorBundle = std.zig.ErrorBundle;
const Ast = std.zig.Ast;
const Pipeline = @import("Pipeline.zig");

/// True if `item` is a REPL-advisory diagnostic we drop. Currently:
/// any error anchored on a var-decl name identifier (covers both
/// "local variable is never mutated" and "unused local variable" --
/// both are style guidance the REPL has no use for).
fn isSuppressed(tree: Ast, item: Zir.Inst.CompileErrors.Item) bool {
    const opt_token = item.token.unwrap() orelse return false;
    if (opt_token == 0) return false;
    if (tree.tokenTag(opt_token) != .identifier) return false;
    return tree.tokenTag(opt_token - 1) == .keyword_var;
}

/// Count of compile-error items that survive the suppression filter.
/// Zero means the REPL can proceed to Sema even though
/// `zir.hasCompileErrors()` reports `true`.
pub fn countActionable(zir: Zir, tree: Ast) u32 {
    const payload_index = zir.extra[@intFromEnum(Zir.ExtraIndex.compile_errors)];
    if (payload_index == 0) return 0;

    const header = zir.extraData(Zir.Inst.CompileErrors, payload_index);
    var extra_index = header.end;
    var actionable: u32 = 0;
    for (0..header.data.items_len) |_| {
        const item = zir.extraData(Zir.Inst.CompileErrors.Item, extra_index);
        extra_index = item.end;
        if (!isSuppressed(tree, item.data)) actionable += 1;
    }
    return actionable;
}

/// Render only the actionable compile errors to `writer`. Builds an
/// `ErrorBundle` the same way the compiler does (via `Wip`), skipping
/// suppressed items entirely so they neither block nor surface.
///
/// `view` provides the user-frame translation: all wrap-shape
/// knowledge (where the user's text starts inside the wrapped
/// source, which spans anchor in injection bytes) lives there.
pub fn renderActionable(
    gpa: std.mem.Allocator,
    zir: Zir,
    tree: Ast,
    view: Pipeline.UserView,
    src_path: []const u8,
    writer: *std.Io.Writer,
) !u32 {
    assert(view.text.len > 0);

    var wip: ErrorBundle.Wip = undefined;
    try wip.init(gpa);
    defer wip.deinit();

    const payload_index = zir.extra[@intFromEnum(Zir.ExtraIndex.compile_errors)];
    if (payload_index != 0) {
        const header = zir.extraData(Zir.Inst.CompileErrors, payload_index);
        var extra_index = header.end;
        for (0..header.data.items_len) |_| {
            const item = zir.extraData(Zir.Inst.CompileErrors.Item, extra_index);
            extra_index = item.end;
            if (isSuppressed(tree, item.data)) continue;
            try appendItem(&wip, zir, tree, view, src_path, item.data);
        }
    }

    var bundle = try wip.toOwnedBundle("");
    defer bundle.deinit(gpa);
    try bundle.renderToWriter(.{}, writer);
    return bundle.errorMessageCount();
}

/// Append a single CompileErrors.Item (plus its actionable notes)
/// to `wip`. An item whose span anchors entirely in the injection
/// prefix is dropped (`view.translate` returns null) -- the main
/// error message has no place to render in the user's frame.
fn appendItem(
    wip: *ErrorBundle.Wip,
    zir: Zir,
    tree: Ast,
    view: Pipeline.UserView,
    src_path: []const u8,
    item: Zir.Inst.CompileErrors.Item,
) !void {
    assert(view.text.len > 0);
    assert(src_path.len > 0);

    const raw_span = spanOf(tree, item.node, item.token, item.byte_offset);
    const span = view.translate(raw_span) orelse return;
    const loc = view.findLoc(span.main);
    const actionable_notes = if (item.notes != 0)
        countActionableNotes(zir, tree, view, item)
    else
        0;
    try wip.addRootErrorMessage(.{
        .msg = try wip.addString(zir.nullTerminatedString(item.msg)),
        .src_loc = try wip.addSourceLocation(.{
            .src_path = try wip.addString(src_path),
            .span_start = span.start,
            .span_main = span.main,
            .span_end = span.end,
            .line = @intCast(loc.line),
            .column = @intCast(loc.column),
            .source_line = try wip.addString(loc.source_line),
        }),
        .notes_len = actionable_notes,
    });
    if (actionable_notes != 0) try appendNotes(wip, zir, tree, view, src_path, item, loc);
}

fn countActionableNotes(
    zir: Zir,
    tree: Ast,
    view: Pipeline.UserView,
    item: Zir.Inst.CompileErrors.Item,
) u32 {
    const block = zir.extraData(Zir.Inst.Block, item.notes);
    const body = zir.extra[block.end..][0..block.data.body_len];
    var count: u32 = 0;
    for (body) |body_elem| {
        const note_item = zir.extraData(Zir.Inst.CompileErrors.Item, body_elem);
        const raw_span = spanOf(tree, note_item.data.node, note_item.data.token, note_item.data.byte_offset);
        if (view.translate(raw_span) != null) count += 1;
    }
    return count;
}

fn appendNotes(
    wip: *ErrorBundle.Wip,
    zir: Zir,
    tree: Ast,
    view: Pipeline.UserView,
    src_path: []const u8,
    item: Zir.Inst.CompileErrors.Item,
    err_loc: std.zig.Loc,
) !void {
    assert(view.text.len > 0);
    assert(item.notes != 0);

    const actionable = countActionableNotes(zir, tree, view, item);
    if (actionable == 0) return;

    const notes_start = try wip.reserveNotes(actionable);
    const block = zir.extraData(Zir.Inst.Block, item.notes);
    const body = zir.extra[block.end..][0..block.data.body_len];
    var write_cursor: u32 = notes_start;
    for (body) |body_elem| {
        const note_item = zir.extraData(Zir.Inst.CompileErrors.Item, body_elem);
        const raw_span = spanOf(tree, note_item.data.node, note_item.data.token, note_item.data.byte_offset);
        const span = view.translate(raw_span) orelse continue;
        const loc = view.findLoc(span.main);
        const note_index = @intFromEnum(try wip.addErrorMessage(.{
            .msg = try wip.addString(zir.nullTerminatedString(note_item.data.msg)),
            .src_loc = try wip.addSourceLocation(.{
                .src_path = try wip.addString(src_path),
                .span_start = span.start,
                .span_main = span.main,
                .span_end = span.end,
                .line = @intCast(loc.line),
                .column = @intCast(loc.column),
                .source_line = if (loc.eql(err_loc)) 0 else try wip.addString(loc.source_line),
            }),
            .notes_len = 0,
        }));
        wip.extra.items[write_cursor] = note_index;
        write_cursor += 1;
    }
    assert(write_cursor == notes_start + actionable);
}

fn spanOf(
    tree: Ast,
    node: Ast.Node.OptionalIndex,
    token: Ast.OptionalTokenIndex,
    byte_offset: u32,
) Ast.Span {
    if (node.unwrap()) |n| return tree.nodeToSpan(n);
    const t = token.unwrap().?;
    const start = tree.tokenStart(t) + byte_offset;
    const end = start + @as(u32, @intCast(tree.tokenSlice(t).len)) - byte_offset;
    return .{ .start = start, .end = end, .main = start };
}
