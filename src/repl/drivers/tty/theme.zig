//! `:theme [name]` -- show or switch the TTY prompt theme.

const std = @import("std");
const assert = std.debug.assert;

const Repl = @import("Repl.zig");
const themes = @import("theme/root.zig");
const ColorLevel = @import("device").Color.ColorLevel;
const Command = @import("../commands/Command.zig").Command;

pub fn command(comptime Ctx: type) Command(Ctx) {
    return .{
        .name = "theme",
        .summary = "Show or switch the prompt theme: :theme [name]",
        .run = struct {
            fn run(ctx: Ctx, _: []const Command(Ctx), argument: []const u8, stdout: *std.Io.Writer) anyerror!void {
                const repl: *Repl = ctx;
                assert(@intFromPtr(repl) != 0);
                assert(@intFromPtr(stdout) != 0);

                const level: ColorLevel = if (repl.terminal) |terminal| terminal.interface.color_level else .none;
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
        }.run,
    };
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
