//! Unified command interface. Each command is a small struct that
//! embeds a `Command` as a field named `interface`, binds whatever it
//! acts on, and recovers its concrete `*Self` inside the vtable via
//! `@fieldParentPtr("interface", c)`. Because every command erases to
//! `*Command` regardless of what it binds, one registry holds them all
//! and the dispatcher names no context type.
//! Modelled on `terminal/Protocol.zig` / `terminal/Device.zig`.

const std = @import("std");
const assert = std.debug.assert;

const Command = @This();

/// Bare command name (no leading `:`), matched against the typed word.
name: []const u8,
/// One-line description shown by `:help`.
summary: []const u8,
vtable: *const VTable,

pub const VTable = struct {
    /// Run the command. `argument` is the text after the name; the
    /// function recovers its concrete type via
    /// `@fieldParentPtr("interface", c)`.
    run: *const fn (c: *Command, argument: []const u8, writer: *std.Io.Writer) anyerror!void,
};

pub fn run(c: *Command, argument: []const u8, writer: *std.Io.Writer) anyerror!void {
    assert(@intFromPtr(c.vtable) != 0);
    return c.vtable.run(c, argument, writer);
}

/// Print one `  :name  summary` line per command in `entries`.
pub fn list(entries: []const *Command, writer: *std.Io.Writer) !void {
    for (entries) |c| {
        try writer.print("  :{s: <8}  {s}\n", .{ c.name, c.summary });
    }
}
