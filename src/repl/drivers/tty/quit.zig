//! `:quit` -- end the TTY run loop.

const std = @import("std");
const assert = std.debug.assert;

const Repl = @import("Repl.zig");
const Command = @import("repl").commands.Command;

pub fn command(comptime Ctx: type) Command(Ctx) {
    return .{
        .name = "quit",
        .summary = "Exit the REPL",
        .run = struct {
            fn run(ctx: Ctx, _: []const Command(Ctx), _: []const u8, stdout: *std.Io.Writer) anyerror!void {
                const repl: *Repl = ctx;
                assert(@intFromPtr(repl) != 0);
                assert(@intFromPtr(stdout) != 0);
                try stdout.writeAll("bye\n");
                repl.should_quit = true;
            }
        }.run,
    };
}
