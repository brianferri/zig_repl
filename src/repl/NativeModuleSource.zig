//! A `ModuleSource` backed by a real directory, reading each requested path as
//! a file. Both the `Io` and the root directory are supplied by the frontend
//! (the core never opens either itself), so the file-system dependency stays at
//! the edge; locating the standard library -- e.g. via `zig env` -- is likewise
//! the frontend's job. Freestanding wasm has no filesystem and injects nothing.

const std = @import("std");
const ModuleSource = @import("ModuleSource.zig");

const NativeModuleSource = @This();

io: std.Io,
/// The source root every `read` path resolves against (the standard library
/// directory for `@import("std")`, i.e. `zig env`'s `std_dir`).
root: std.Io.Dir,
interface: ModuleSource = .{ .vtable = &vtable },

/// A source file larger than this is treated as unreadable rather than
/// exhausting memory; the standard library's files sit far below it.
const max_bytes: std.Io.Limit = .limited(4 * 1024 * 1024);

const vtable: ModuleSource.VTable = .{ .read = read };

fn read(source: *ModuleSource, gpa: std.mem.Allocator, path: []const u8) ModuleSource.Error![:0]u8 {
    const self: *NativeModuleSource = @alignCast(@fieldParentPtr("interface", source));
    return self.root.readFileAllocOptions(self.io, path, gpa, max_bytes, .of(u8), 0) catch |err| switch (err) {
        error.OutOfMemory => error.OutOfMemory,
        error.FileNotFound => error.FileNotFound,
        else => error.ReadFailed,
    };
}

test "reads a file's bytes with a NUL sentinel" {
    const gpa = std.testing.allocator;
    var io_instance: std.Io.Threaded = .init(gpa, .{});
    defer io_instance.deinit();
    const io = io_instance.io();

    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    try tmp.dir.writeFile(io, .{ .sub_path = "m.zig", .data = "const answer = 42;" });

    var native: NativeModuleSource = .{ .io = io, .root = tmp.dir };
    const bytes = try native.interface.read(gpa, "m.zig");
    defer gpa.free(bytes);

    try std.testing.expectEqualStrings("const answer = 42;", bytes);
    try std.testing.expectEqual(@as(u8, 0), bytes[bytes.len]);
    try std.testing.expectError(error.FileNotFound, native.interface.read(gpa, "missing.zig"));
}
