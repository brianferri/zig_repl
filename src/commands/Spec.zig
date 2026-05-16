const std = @import("std");
const Session = @import("../Session.zig");

const Spec = @This();

name: []const u8,
summary: []const u8,
run: *const fn (
    session: *Session,
    argument: []const u8,
    stdout: *std.Io.Writer,
) anyerror!void,
