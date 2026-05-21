const std = @import("std");
const assert = std.debug.assert;

const Session = @import("Session.zig");
const Spec = @import("commands/Spec.zig");

pub const registry = [_]Spec{
    @import("commands/help.zig").spec,
    @import("commands/quit.zig").spec,
    @import("commands/show_zir.zig").spec,
    @import("commands/dump.zig").spec,
};

const max_name_bytes: u32 = 64;
const max_command_bytes: u32 = 1024;

pub fn lookup(name: []const u8) ?Spec {
    assert(name.len <= max_name_bytes);
    for (registry) |spec| {
        if (std.mem.eql(u8, spec.name, name)) return spec;
    }
    return null;
}

pub fn run(session: *Session, name_and_args: []const u8, stdout: *std.Io.Writer) !void {
    assert(@intFromPtr(session) != 0);
    assert(name_and_args.len <= max_command_bytes);

    var iter = std.mem.splitScalar(u8, name_and_args, ' ');
    const name = iter.first();
    const argument = iter.rest();
    const spec = lookup(name) orelse {
        try stdout.print("unknown command: :{s}\n", .{name});
        return;
    };
    return spec.run(session, argument, stdout);
}
