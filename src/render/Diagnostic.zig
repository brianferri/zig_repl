const std = @import("std");
const assert = std.debug.assert;

const max_renderable_parse_errors: u32 = 64;
const repl_source_path: []const u8 = "<repl>";

pub fn renderParseErrors(
    tree: std.zig.Ast,
    source: [:0]const u8,
    writer: *std.Io.Writer,
) std.Io.Writer.Error!void {
    assert(tree.errors.len > 0);
    assert(source.len > 0);

    var rendered: u32 = 0;
    for (tree.errors) |parse_error| {
        if (rendered >= max_renderable_parse_errors) {
            try writer.writeAll("... further parse errors elided\n");
            break;
        }
        const offset = tree.tokenStart(parse_error.token);
        const loc = std.zig.findLineColumn(source, offset);
        try writer.print("{s}:{d}:{d}: parse error: ", .{
            repl_source_path,
            loc.line + 1,
            loc.column + 1,
        });
        try tree.renderError(parse_error, writer);
        try writer.writeAll("\n");
        rendered += 1;
    }
}

pub fn renderZirErrors(
    gpa: std.mem.Allocator,
    zir: std.zig.Zir,
    tree: std.zig.Ast,
    source: [:0]const u8,
    writer: *std.Io.Writer,
) !void {
    assert(zir.hasCompileErrors());
    assert(source.len > 0);

    var wip: std.zig.ErrorBundle.Wip = undefined;
    try wip.init(gpa);
    defer wip.deinit();

    try wip.addZirErrorMessages(zir, tree, source, repl_source_path);

    var bundle = try wip.toOwnedBundle("");
    defer bundle.deinit(gpa);

    try bundle.renderToWriter(.{}, writer);
}
