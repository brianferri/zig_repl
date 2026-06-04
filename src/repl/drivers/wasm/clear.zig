//! `:clear` -- wipe the web output log. The log lives in the DOM, which the
//! core cannot reach, so the command calls a host import the page supplies.
//! This is the wasm frontend's analogue of the TTY's terminal-touching
//! commands: it reaches a capability that only the frontend's host has.

const std = @import("std");

const Command = @import("../commands/Command.zig").Command;

/// Provided by the page's import object (`env.replClearOutput`): clears the
/// scrolling output element. The wasm side only signals intent; the DOM
/// mutation is the host's.
extern "env" fn replClearOutput() void;

pub fn command(comptime Ctx: type) Command(Ctx) {
    return .{
        .name = "clear",
        .summary = "Clear the output log",
        .run = struct {
            fn run(_: Ctx, _: []const Command(Ctx), _: []const u8, _: *std.Io.Writer) anyerror!void {
                replClearOutput();
            }
        }.run,
    };
}
