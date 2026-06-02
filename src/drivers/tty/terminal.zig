const std = @import("std");
const builtin = @import("builtin");
const assert = std.debug.assert;

const Repl = @import("Repl.zig");
const themes = @import("theme/root.zig");
const Command = @import("../../commands/Command.zig");

const TerminalCmd = @This();

interface: Command,
repl: *Repl,

pub fn init(repl: *Repl) TerminalCmd {
    return .{
        .interface = .{
            .name = "terminal",
            .summary = "Show the active terminal's detected capabilities",
            .vtable = &vtable,
        },
        .repl = repl,
    };
}

pub fn command(self: *TerminalCmd) *Command {
    return &self.interface;
}

const vtable: Command.VTable = .{ .run = run };

fn run(c: *Command, argument: []const u8, stdout: *std.Io.Writer) anyerror!void {
    _ = argument;
    const self: *TerminalCmd = @fieldParentPtr("interface", c);
    const repl = self.repl;
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
    for (themes.themes, 0..) |theme, i| {
        if (i != 0) try stdout.writeAll(", ");
        try theme.primary.color.write(stdout, theme.name, level);
    }
    try stdout.writeByte('\n');
}
