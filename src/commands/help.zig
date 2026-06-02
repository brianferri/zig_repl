const std = @import("std");

const Command = @import("Command.zig");

const Help = @This();

interface: Command,
/// The full command set to enumerate. Wired after the registry array
/// is built, since that array contains this command -- it cannot be
/// passed at `init` without a forward reference to itself.
entries: []const *Command,

pub fn init() Help {
    return .{
        .interface = .{
            .name = "help",
            .summary = "Show available commands",
            .vtable = &vtable,
        },
        .entries = &.{},
    };
}

pub fn command(self: *Help) *Command {
    return &self.interface;
}

const vtable: Command.VTable = .{ .run = run };

fn run(c: *Command, argument: []const u8, writer: *std.Io.Writer) anyerror!void {
    _ = argument;
    const self: *Help = @fieldParentPtr("interface", c);
    try writer.writeAll("commands:\n");
    try Command.list(self.entries, writer);
}
