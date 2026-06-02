//! The wasm frontend's command set: the session-shared commands plus the
//! web-specific `:clear`, assembled into one `*Command` registry the
//! dispatcher matches against. Same shape as the TTY frontend's registry;
//! registering a command is a one-field change here.

const std = @import("std");

const Session = @import("../../Session.zig");
const commands = @import("../../commands.zig");
const Command = commands.Command;
const clear_cmd = @import("clear.zig");

const Commands = @This();

// Field order is the order `:help` lists the commands.
help: commands.help,
dump: commands.dump,
clear: clear_cmd,

/// Command count -- the caller sizes its `*Command` buffer with it.
pub const count = std.meta.fields(Commands).len;

/// Name-to-index table, derived from the field names at comptime so it
/// cannot drift from the fields and `find` is O(1). The field name is
/// the command's `:`-name (`help` -> `:help`).
const name_index = std.StaticStringMap(usize).initComptime(blk: {
    const fields = std.meta.fields(Commands);
    var pairs: [fields.len]struct { []const u8, usize } = undefined;
    for (fields, 0..) |f, i| pairs[i] = .{ f.name, i };
    break :blk pairs;
});

pub fn init(session: *Session) Commands {
    return .{
        .help = commands.help.init(),
        .dump = commands.dump.init(session),
        .clear = clear_cmd.init(),
    };
}

/// Fill `buf` with each command's interface pointer and return it as a
/// slice. A command that enumerates the whole set declares an
/// `entries: []const *Command` field and is wired to the finished slice
/// here (this is how `:help` reaches every command). Must run after
/// `self` is at its final address -- the pointers reference its fields.
pub fn slice(self: *Commands, buf: *[count]*Command) []const *Command {
    inline for (std.meta.fields(Commands), 0..) |f, i| {
        buf[i] = @field(self, f.name).command();
    }
    inline for (std.meta.fields(Commands)) |f| {
        if (@hasField(f.type, "entries")) @field(self, f.name).entries = buf[0..count];
    }
    return buf[0..count];
}

/// The command named `name`, or null if none matches. O(1) via the
/// comptime name table. `entries` is the slice returned by `slice`.
pub fn find(entries: []const *Command, name: []const u8) ?*Command {
    const i = name_index.get(name) orelse return null;
    return entries[i];
}
