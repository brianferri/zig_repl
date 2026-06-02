//! `:help` -- list every command in the set with its summary.

const std = @import("std");

const Command = @import("Command.zig").Command;

pub fn command(comptime Ctx: type) Command(Ctx) {
    return .{
        .name = "help",
        .summary = "Show available commands",
        .run = struct {
            fn run(_: Ctx, set: []const Command(Ctx), _: []const u8, writer: *std.Io.Writer) anyerror!void {
                try writer.writeAll("commands:\n");
                for (set) |cmd| try writer.print("  :{s: <8}  {s}\n", .{ cmd.name, cmd.summary });
            }
        }.run,
    };
}
