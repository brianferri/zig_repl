const std = @import("std");
const assert = std.debug.assert;

const Repl = @import("Repl.zig");
const Command = @import("../../commands/Command.zig");

const Quit = @This();

interface: Command,
repl: *Repl,

pub fn init(repl: *Repl) Quit {
    return .{
        .interface = .{
            .name = "quit",
            .summary = "Exit the REPL",
            .vtable = &vtable,
        },
        .repl = repl,
    };
}

pub fn command(self: *Quit) *Command {
    return &self.interface;
}

const vtable: Command.VTable = .{ .run = run };

fn run(c: *Command, argument: []const u8, stdout: *std.Io.Writer) anyerror!void {
    _ = argument;
    const self: *Quit = @fieldParentPtr("interface", c);
    assert(@intFromPtr(self.repl) != 0);
    assert(@intFromPtr(stdout) != 0);

    try stdout.writeAll("bye\n");
    self.repl.should_quit = true;
}
