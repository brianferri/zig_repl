const std = @import("std");

/// A command over `Context`: `*Session` for the shared, frontend-agnostic
/// commands; a frontend type for frontend-specific ones.
pub fn Spec(comptime Context: type) type {
    return struct {
        name: []const u8,
        summary: []const u8,
        run: *const fn (Context, []const u8, *std.Io.Writer) anyerror!void,
    };
}
