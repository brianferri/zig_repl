const std = @import("std");
const assert = std.debug.assert;

const Session = @import("../Session.zig");
const Spec = @import("Spec.zig");
const Pipeline = @import("../front/Pipeline.zig");
const Diagnostic = @import("../render/Diagnostic.zig");

pub const spec: Spec = .{
    .name = "zir",
    .summary = "Dump ZIR summary for an expression: :zir <expr>",
    .run = run,
};

fn run(session: *Session, argument: []const u8, stdout: *std.Io.Writer) anyerror!void {
    assert(@intFromPtr(session) != 0);
    assert(@intFromPtr(stdout) != 0);

    const trimmed = std.mem.trim(u8, argument, " \t");
    if (trimmed.len == 0) {
        try stdout.writeAll("usage: :zir <expression>\n");
        return;
    }

    var result = Pipeline.run(session.gpa, trimmed) catch |err| {
        try stdout.print("front-end failed: {s}\n", .{@errorName(err)});
        return;
    };
    defer result.deinit(session.gpa);

    if (result.hasParseErrors()) {
        try Diagnostic.renderParseErrors(result.tree, result.userView(), stdout);
        return;
    }
    if (result.hasZirErrors()) {
        try Diagnostic.renderZirErrors(
            session.gpa,
            result.zir,
            result.tree,
            result.userView(),
            stdout,
        );
        return;
    }

    const instruction_count: u32 = @intCast(result.zir.instructions.len);
    const extra_words: u32 = @intCast(result.zir.extra.len);
    const string_bytes: u32 = @intCast(result.zir.string_bytes.len);
    try stdout.print(
        "ZIR: {d} instructions, {d} extra words, {d} string bytes\n",
        .{ instruction_count, extra_words, string_bytes },
    );
}
