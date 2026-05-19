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
//! Mirrors the per-item walk in
//! `std.zig.ErrorBundle.Wip.addZirErrorMessages` (~line 502) so the
//! span / source-location / notes plumbing stays bit-identical to
//! what `zig` itself would render.

const std = @import("std");
const assert = std.debug.assert;

const Zir = std.zig.Zir;
const ErrorBundle = std.zig.ErrorBundle;
const Ast = std.zig.Ast;

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
/// `user_text` + `user_offset` provide the user-frame translation:
/// the front-end wraps expressions as `const __repl_input = (..);`
/// before parsing, but the user must not see those bytes. Spans
/// originate as offsets into the wrapped source; we translate them
/// to offsets into `user_text` and pass `user_text` as the source
/// string to `findLineColumn` so line/col land in the user's frame.
/// Spans outside `[user_offset, user_offset+user_text.len)` clamp
/// to the nearest user-frame boundary.
pub fn renderActionable(
    gpa: std.mem.Allocator,
    zir: Zir,
    tree: Ast,
    user_text: []const u8,
    user_offset: u32,
    src_path: []const u8,
    writer: *std.Io.Writer,
) !void {
    assert(user_text.len > 0);

    const user_text_z = try gpa.allocSentinel(u8, user_text.len, 0);
    defer gpa.free(user_text_z);
    @memcpy(user_text_z, user_text);

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
            try appendItem(&wip, zir, tree, user_text_z, user_offset, src_path, item.data);
        }
    }

    var bundle = try wip.toOwnedBundle("");
    defer bundle.deinit(gpa);
    try bundle.renderToWriter(.{}, writer);
}

/// Append a single CompileErrors.Item (plus its notes) to `wip`.
/// Span / source-location math mirrors
/// `addZirErrorMessages` in `std/zig/ErrorBundle.zig:502`, with the
/// extra step of translating wrapped-source spans into the user
/// frame before they reach `wip` so the user-visible line/col land
/// in their input rather than the wrap.
fn appendItem(
    wip: *ErrorBundle.Wip,
    zir: Zir,
    tree: Ast,
    user_text: [:0]const u8,
    user_offset: u32,
    src_path: []const u8,
    item: Zir.Inst.CompileErrors.Item,
) !void {
    assert(user_text.len > 0);
    assert(src_path.len > 0);

    const span = translateSpan(spanOf(tree, item.node, item.token, item.byte_offset), user_offset, @intCast(user_text.len));
    const loc = std.zig.findLineColumn(user_text, span.main);
    const notes_len = item.notesLen(zir);
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
        .notes_len = notes_len,
    });
    if (item.notes != 0) try appendNotes(wip, zir, tree, user_text, user_offset, src_path, item, loc);
}

fn appendNotes(
    wip: *ErrorBundle.Wip,
    zir: Zir,
    tree: Ast,
    user_text: [:0]const u8,
    user_offset: u32,
    src_path: []const u8,
    item: Zir.Inst.CompileErrors.Item,
    err_loc: std.zig.Loc,
) !void {
    assert(user_text.len > 0);
    assert(item.notes != 0);

    const notes_start = try wip.reserveNotes(item.notesLen(zir));
    const block = zir.extraData(Zir.Inst.Block, item.notes);
    const body = zir.extra[block.end..][0..block.data.body_len];
    const user_len: u32 = @intCast(user_text.len);
    for (notes_start.., body) |note_i, body_elem| {
        const note_item = zir.extraData(Zir.Inst.CompileErrors.Item, body_elem);
        const span = translateSpan(spanOf(tree, note_item.data.node, note_item.data.token, note_item.data.byte_offset), user_offset, user_len);
        const loc = std.zig.findLineColumn(user_text, span.main);
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
        wip.extra.items[note_i] = note_index;
    }
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

/// Map a wrapped-source span into the user frame. Each coordinate
/// `clamp(wrapped - user_offset, 0, user_len)`. A span entirely in
/// the prefix collapses to `{0,0,0}` (start of user input); a span
/// entirely in the suffix collapses to `{user_len, user_len,
/// user_len}` (end of user input). Spans straddling a boundary clip
/// to the user range -- the diagnostic still points at "where the
/// user can see it" rather than at synthetic wrap bytes.
fn translateSpan(span: Ast.Span, user_offset: u32, user_len: u32) Ast.Span {
    return .{
        .start = mapPos(span.start, user_offset, user_len),
        .main = mapPos(span.main, user_offset, user_len),
        .end = mapPos(span.end, user_offset, user_len),
    };
}

fn mapPos(wrapped_pos: u32, user_offset: u32, user_len: u32) u32 {
    if (wrapped_pos < user_offset) return 0;
    const rel = wrapped_pos - user_offset;
    return @min(rel, user_len);
}
