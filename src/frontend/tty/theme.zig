const std = @import("std");
const assert = std.debug.assert;

const Repl = @import("Repl.zig");
const themes = @import("../../theme/root.zig");
const ColorLevel = @import("../../terminal/Color.zig").ColorLevel;
const Spec = @import("../../commands/Spec.zig").Spec;

pub const spec: Spec(*Repl) = .{
    .name = "theme",
    .summary = "Show or switch the prompt theme: :theme [name]",
    .run = run,
};

fn run(repl: *Repl, argument: []const u8, stdout: *std.Io.Writer) anyerror!void {
    assert(@intFromPtr(repl) != 0);
    assert(@intFromPtr(stdout) != 0);

    const level: ColorLevel = if (repl.terminal) |terminal| terminal.color_level else .none;
    const arg = std.mem.trim(u8, argument, " \t");

    if (arg.len == 0) {
        try report(repl, stdout, level);
        return;
    }

    const selected = themes.byName(arg) orelse {
        try stdout.print("unknown theme: {s}\n", .{arg});
        try report(repl, stdout, level);
        return;
    };
    repl.theme = selected;
    try report(repl, stdout, level);
}

fn report(repl: *Repl, stdout: *std.Io.Writer, level: ColorLevel) !void {
    assert(@intFromPtr(stdout) != 0);
    try stdout.print("theme: {s}\n", .{repl.theme.name});
    try stdout.writeAll("available: ");
    for (themes.themes, 0..) |theme, i| {
        if (i != 0) try stdout.writeAll(", ");
        try theme.primary.color.write(stdout, theme.name, level);
    }
    try stdout.writeByte('\n');
}
