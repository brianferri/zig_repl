//! `:clear` -- wipe the web output log. The log lives in the DOM, which
//! the core cannot reach, so the command calls a host import the page
//! supplies. This is the wasm frontend's analogue of the TTY's
//! terminal-touching commands: it reaches a capability that only the
//! frontend's host has.

const std = @import("std");

const Command = @import("../../commands/Command.zig");

/// Provided by the page's import object (`env.replClearOutput`): clears
/// the scrolling output element. The wasm side only signals intent; the
/// DOM mutation is the host's.
extern "env" fn replClearOutput() void;

const Clear = @This();

interface: Command,

pub fn init() Clear {
    return .{
        .interface = .{
            .name = "clear",
            .summary = "Clear the output log",
            .vtable = &vtable,
        },
    };
}

pub fn command(self: *Clear) *Command {
    return &self.interface;
}

const vtable: Command.VTable = .{ .run = run };

fn run(c: *Command, argument: []const u8, writer: *std.Io.Writer) anyerror!void {
    _ = c;
    _ = argument;
    _ = writer;
    replClearOutput();
}
