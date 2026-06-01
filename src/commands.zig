const std = @import("std");
const assert = std.debug.assert;

const Session = @import("Session.zig");

/// Shared commands operate on the core `*Session`.
pub const Command = @import("commands/Spec.zig").Spec(*Session);

/// Frontend-agnostic commands: each operates on a `*Session` and writes
/// to the caller's writer, so any frontend reuses them. Frontend-specific
/// commands (quit/theme/terminal -- they touch the loop or the live
/// terminal) live with their frontend's own registry, not here.
pub const registry = [_]Command{
    @import("commands/help.zig").spec,
    @import("commands/dump.zig").spec,
};

const max_name_bytes: u32 = 64;
const max_command_bytes: u32 = 1024;

pub fn lookup(name: []const u8) ?Command {
    assert(name.len <= max_name_bytes);
    for (registry) |spec| {
        if (std.mem.eql(u8, spec.name, name)) return spec;
    }
    return null;
}

/// Run a shared command by name. Returns `false` when no shared command
/// matches, so a frontend can try its own commands (and only then report
/// "unknown command"); the shared set never owns that error message.
pub fn run(session: *Session, name_and_args: []const u8, stdout: *std.Io.Writer) !bool {
    assert(@intFromPtr(session) != 0);
    assert(name_and_args.len <= max_command_bytes);

    var iter = std.mem.splitScalar(u8, name_and_args, ' ');
    const name = iter.first();
    const argument = iter.rest();
    const spec = lookup(name) orelse return false;
    try spec.run(session, argument, stdout);
    return true;
}
