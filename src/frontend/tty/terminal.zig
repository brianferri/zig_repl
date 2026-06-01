const std = @import("std");
const builtin = @import("builtin");
const assert = std.debug.assert;

const Repl = @import("Repl.zig");
const themes = @import("../../theme/root.zig");
const Spec = @import("../../commands/Spec.zig").Spec;

pub const spec: Spec(*Repl) = .{
    .name = "terminal",
    .summary = "Show the active terminal's detected capabilities",
    .run = run,
};

fn run(repl: *Repl, argument: []const u8, stdout: *std.Io.Writer) anyerror!void {
    assert(@intFromPtr(repl) != 0);
    assert(@intFromPtr(stdout) != 0);
    _ = argument;

    const terminal = repl.terminal orelse {
        try stdout.writeAll("no interactive terminal (running in cooked mode)\n");
        return;
    };
    const level = terminal.color_level;

    try stdout.print("platform:  {s}\n", .{@tagName(builtin.os.tag)});
    try stdout.print("color:     {s}\n", .{@tagName(level)});

    try stdout.writeAll("protocols: ");
    for (terminal.protocols, 0..) |protocol, i| {
        if (i != 0) try stdout.writeAll(", ");
        try stdout.writeAll(protocol.name);
    }
    try stdout.writeByte('\n');

    const active = repl.theme;
    try stdout.print("theme:     {s}  ", .{active.name});
    try active.primary.write(stdout, level);
    try active.continuation.write(stdout, level);
    try stdout.writeByte('\n');

    try stdout.writeAll("themes:    ");
    for (themes.themes, 0..) |theme, i| {
        if (i != 0) try stdout.writeAll(", ");
        try theme.primary.color.write(stdout, theme.name, level);
    }
    try stdout.writeByte('\n');
}
