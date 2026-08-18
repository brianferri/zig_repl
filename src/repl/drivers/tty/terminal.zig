//! `:terminal` -- show the active terminal's detected capabilities.

const std = @import("std");
const builtin = @import("builtin");
const assert = std.debug.assert;

const Repl = @import("Repl.zig");
const themes = @import("editor").themes;
const Command = @import("repl").commands.Command;

pub fn command(comptime Ctx: type) Command(Ctx) {
    return .{
        .name = "terminal",
        .summary = "Show the active terminal's detected capabilities",
        .run = struct {
            fn run(ctx: Ctx, _: []const Command(Ctx), _: []const u8, stdout: *std.Io.Writer) anyerror!void {
                const repl: *Repl = ctx;
                assert(@intFromPtr(repl) != 0);
                assert(@intFromPtr(stdout) != 0);

                const terminal = repl.terminal orelse {
                    try stdout.writeAll("no interactive terminal (running in cooked mode)\n");
                    return;
                };
                const level = terminal.interface.color_level;

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
                try themes.writeList(stdout, level);
                try stdout.writeByte('\n');
            }
        }.run,
    };
}
