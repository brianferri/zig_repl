const std = @import("std");
const assert = std.debug.assert;

const Session = @import("../Session.zig");
const Spec = @import("Spec.zig");

pub const spec: Spec = .{
    .name = "quit",
    .summary = "Exit the REPL",
    .run = run,
};

fn run(session: *Session, argument: []const u8, stdout: *std.Io.Writer) anyerror!void {
    assert(@intFromPtr(session) != 0);
    assert(@intFromPtr(stdout) != 0);
    _ = argument;

    try stdout.writeAll("bye\n");
    session.should_quit = true;
}
