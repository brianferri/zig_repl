const std = @import("std");
const assert = std.debug.assert;

const Session = @This();

gpa: std.mem.Allocator,
session_arena: std.mem.Allocator,
io: std.Io,
stdin_file: std.Io.File,
stdout_file: std.Io.File,
stderr_file: std.Io.File,
should_quit: bool,

pub fn init(
    gpa: std.mem.Allocator,
    session_arena: std.mem.Allocator,
    io: std.Io,
) Session {
    assert(@intFromPtr(io.vtable) != 0);
    assert(@intFromPtr(io.userdata) != 0);
    return .{
        .gpa = gpa,
        .session_arena = session_arena,
        .io = io,
        .stdin_file = std.Io.File.stdin(),
        .stdout_file = std.Io.File.stdout(),
        .stderr_file = std.Io.File.stderr(),
        .should_quit = false,
    };
}

pub fn deinit(session: *Session) void {
    assert(@intFromPtr(session) != 0);
    session.* = undefined;
}
