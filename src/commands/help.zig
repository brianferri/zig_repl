const std = @import("std");
const assert = std.debug.assert;

const Session = @import("../Session.zig");
const Spec = @import("Spec.zig");
const commands = @import("../commands.zig");

pub const spec: Spec = .{
    .name = "help",
    .summary = "Show available commands",
    .run = run,
};

fn run(session: *Session, argument: []const u8, stdout: *std.Io.Writer) anyerror!void {
    assert(@intFromPtr(session) != 0);
    assert(@intFromPtr(stdout) != 0);
    _ = argument;

    try stdout.writeAll("commands:\n");
    for (commands.registry) |entry| {
        try stdout.print("  :{s: <8}  {s}\n", .{ entry.name, entry.summary });
    }
}
