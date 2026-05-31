const std = @import("std");
const assert = std.debug.assert;

const Session = @import("../Session.zig");
const Spec = @import("Spec.zig");
const themes = @import("../theme/root.zig");
const ColorLevel = @import("../terminal/Color.zig").ColorLevel;

pub const spec: Spec = .{
    .name = "theme",
    .summary = "Show or switch the prompt theme: :theme [name]",
    .run = run,
};

fn run(session: *Session, argument: []const u8, stdout: *std.Io.Writer) anyerror!void {
    assert(@intFromPtr(session) != 0);
    assert(@intFromPtr(stdout) != 0);

    // Color the listing at the terminal's tier; cooked mode has none.
    const level: ColorLevel = if (session.terminal) |terminal| terminal.color_level else .none;
    const name = std.mem.trim(u8, argument, " \t");

    if (name.len == 0) {
        try report(session, stdout, level);
        return;
    }

    const selected = themes.byName(name) orelse {
        try stdout.print("unknown theme: {s}\n", .{name});
        try report(session, stdout, level);
        return;
    };
    session.theme = selected;
    try report(session, stdout, level);
}

fn report(session: *Session, stdout: *std.Io.Writer, level: ColorLevel) !void {
    assert(@intFromPtr(stdout) != 0);
    try stdout.print("theme: {s}\n", .{session.theme.name});
    try stdout.writeAll("available: ");
    for (themes.themes, 0..) |theme, i| {
        if (i != 0) try stdout.writeAll(", ");
        try theme.primary.color.write(stdout, theme.name, level);
    }
    try stdout.writeByte('\n');
}
