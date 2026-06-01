const std = @import("std");
const assert = std.debug.assert;

const Repl = @import("Repl.zig");
const Spec = @import("../../commands/Spec.zig").Spec;

pub const spec: Spec(*Repl) = .{
    .name = "quit",
    .summary = "Exit the REPL",
    .run = run,
};

fn run(repl: *Repl, argument: []const u8, stdout: *std.Io.Writer) anyerror!void {
    assert(@intFromPtr(repl) != 0);
    assert(@intFromPtr(stdout) != 0);
    _ = argument;

    try stdout.writeAll("bye\n");
    repl.should_quit = true;
}
