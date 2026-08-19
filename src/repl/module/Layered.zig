//! An `Fs` that stacks a writable `primary` over a read-only `fallback`: a read tries `primary`, then
//! `fallback`, so a project's files and `std` resolve through one filesystem with the project shadowing.
//! Listing and every mutation act on `primary` alone.

const std = @import("std");
const Fs = @import("Fs.zig");

const Layered = @This();

primary: *Fs,
fallback: *Fs,
interface: Fs = .{ .vtable = &vtable },

const vtable: Fs.VTable = .{
    .read = read,
    .list = list,
    .write = write,
    .mkdir = mkdir,
    .remove = remove,
    .rename = rename,
};

pub fn init(primary: *Fs, fallback: *Fs) Layered {
    return .{ .primary = primary, .fallback = fallback };
}

fn read(fs: *Fs, gpa: std.mem.Allocator, path: []const u8) Fs.Error![:0]u8 {
    const self: *Layered = @alignCast(@fieldParentPtr("interface", fs));
    return self.primary.read(gpa, path) catch |err| switch (err) {
        error.FileNotFound => self.fallback.read(gpa, path),
        else => err,
    };
}

fn list(fs: *Fs, gpa: std.mem.Allocator) Fs.Error![]Fs.Entry {
    const self: *Layered = @alignCast(@fieldParentPtr("interface", fs));
    return self.primary.list(gpa);
}

fn write(fs: *Fs, path: []const u8, bytes: []const u8) Fs.Error!void {
    const self: *Layered = @alignCast(@fieldParentPtr("interface", fs));
    return self.primary.write(path, bytes);
}

fn mkdir(fs: *Fs, path: []const u8) Fs.Error!void {
    const self: *Layered = @alignCast(@fieldParentPtr("interface", fs));
    return self.primary.mkdir(path);
}

fn remove(fs: *Fs, path: []const u8) Fs.Error!void {
    const self: *Layered = @alignCast(@fieldParentPtr("interface", fs));
    return self.primary.remove(path);
}

fn rename(fs: *Fs, old: []const u8, new: []const u8) Fs.Error!void {
    const self: *Layered = @alignCast(@fieldParentPtr("interface", fs));
    return self.primary.rename(old, new);
}

const testing = std.testing;

test "reads fall through to the fallback; writes and listing stay on the primary" {
    const gpa = testing.allocator;
    const Vfs = @import("Vfs.zig");

    var project: Vfs = .init(gpa);
    defer project.deinit();
    var std_lib: Vfs = .init(gpa);
    defer std_lib.deinit();
    try std_lib.interface.write("std.zig", "pub const std = {};");

    var layered: Layered = .init(&project.interface, &std_lib.interface);

    try layered.interface.write("main.zig", "const x = 1;");

    const main = try layered.interface.read(gpa, "main.zig");
    defer gpa.free(main);
    try testing.expectEqualStrings("const x = 1;", main);

    const std_bytes = try layered.interface.read(gpa, "std.zig");
    defer gpa.free(std_bytes);
    try testing.expectEqualStrings("pub const std = {};", std_bytes);

    const names = try layered.interface.list(gpa);
    defer Fs.freeList(gpa, names);
    try testing.expectEqual(@as(usize, 1), names.len);
    try testing.expectEqualStrings("main.zig", names[0].path);
}
