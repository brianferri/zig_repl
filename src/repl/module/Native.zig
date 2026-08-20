//! An `Fs` leaf backed by a real directory: each path resolves under a frontend-supplied `root`, which
//! must be opened with `OpenOptions.iterate` for a caller that intends to `list` it.

const std = @import("std");
const Fs = @import("Fs.zig");

const Native = @This();

io: std.Io,
/// The root every path resolves against -- the std directory (`zig env`'s `std_dir`) for the std layer,
/// the working directory for a project.
root: std.Io.Dir,
interface: Fs = .{ .vtable = &vtable },

/// A file larger than this is treated as unreadable to bound memory use; source files sit far
/// below it.
const max_bytes: std.Io.Limit = .limited(4 * 1024 * 1024);

const vtable: Fs.VTable = .{
    .read = read,
    .list = list,
    .write = write,
    .mkdir = mkdir,
    .remove = remove,
    .rename = rename,
};

fn read(fs: *Fs, gpa: std.mem.Allocator, path: []const u8) Fs.Error![:0]u8 {
    const self: *Native = @alignCast(@fieldParentPtr("interface", fs));
    return self.root.readFileAllocOptions(self.io, path, gpa, max_bytes, .of(u8), 0) catch |err| switch (err) {
        error.OutOfMemory => error.OutOfMemory,
        error.FileNotFound => error.FileNotFound,
        else => error.ReadFailed,
    };
}

fn list(fs: *Fs, gpa: std.mem.Allocator) Fs.Error![]Fs.Entry {
    const self: *Native = @alignCast(@fieldParentPtr("interface", fs));
    var walker = self.root.walk(gpa) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
    };
    defer walker.deinit();

    var out: std.ArrayListUnmanaged(Fs.Entry) = .empty;
    errdefer {
        for (out.items) |entry| gpa.free(entry.path);
        out.deinit(gpa);
    }
    while (walker.next(self.io) catch return error.ReadFailed) |entry| {
        const kind: Fs.Kind = switch (entry.kind) {
            .file => .file,
            .directory => .directory,
            else => continue,
        };
        try out.append(gpa, .{ .path = try gpa.dupe(u8, entry.path), .kind = kind });
    }
    return out.toOwnedSlice(gpa);
}

fn write(fs: *Fs, path: []const u8, bytes: []const u8) Fs.Error!void {
    const self: *Native = @alignCast(@fieldParentPtr("interface", fs));
    self.root.writeFile(self.io, .{ .sub_path = path, .data = bytes }) catch return error.ReadFailed;
}

fn mkdir(fs: *Fs, path: []const u8) Fs.Error!void {
    const self: *Native = @alignCast(@fieldParentPtr("interface", fs));
    self.root.createDirPath(self.io, path) catch return error.ReadFailed;
}

fn remove(fs: *Fs, path: []const u8) Fs.Error!void {
    const self: *Native = @alignCast(@fieldParentPtr("interface", fs));
    self.root.deleteFile(self.io, path) catch |err| switch (err) {
        error.FileNotFound => return error.FileNotFound,
        error.IsDir => self.root.deleteTree(self.io, path) catch return error.ReadFailed,
        else => return error.ReadFailed,
    };
}

fn rename(fs: *Fs, old: []const u8, new: []const u8) Fs.Error!void {
    const self: *Native = @alignCast(@fieldParentPtr("interface", fs));
    // Honor the interface's no-clobber contract: a real `rename` would overwrite.
    if (self.root.access(self.io, new, .{})) |_| {
        return error.PathAlreadyExists;
    } else |_| {}
    self.root.rename(old, self.root, new, self.io) catch |err| switch (err) {
        error.FileNotFound => return error.FileNotFound,
        else => return error.ReadFailed,
    };
}

test "reads, writes, lists, renames, and removes files under the root" {
    const gpa = std.testing.allocator;
    var io_instance: std.Io.Threaded = .init(gpa, .{});
    defer io_instance.deinit();
    const io = io_instance.io();

    var tmp = std.testing.tmpDir(.{ .iterate = true });
    defer tmp.cleanup();

    var native: Native = .{ .io = io, .root = tmp.dir };

    try native.interface.write("m.zig", "const answer = 42;");
    const bytes = try native.interface.read(gpa, "m.zig");
    defer gpa.free(bytes);
    try std.testing.expectEqualStrings("const answer = 42;", bytes);
    try std.testing.expectEqual(@as(u8, 0), bytes[bytes.len]);
    try std.testing.expectError(error.FileNotFound, native.interface.read(gpa, "missing.zig"));

    const names = try native.interface.list(gpa);
    defer Fs.freeList(gpa, names);
    try std.testing.expectEqual(@as(usize, 1), names.len);
    try std.testing.expectEqualStrings("m.zig", names[0].path);
    try std.testing.expectEqual(Fs.Kind.file, names[0].kind);

    try native.interface.write("n.zig", "b");
    try std.testing.expectError(error.PathAlreadyExists, native.interface.rename("m.zig", "n.zig"));
    try native.interface.rename("m.zig", "k.zig");
    try std.testing.expectError(error.FileNotFound, native.interface.read(gpa, "m.zig"));

    try native.interface.remove("k.zig");
    try std.testing.expectError(error.FileNotFound, native.interface.remove("k.zig"));
}

test "creates, lists, and recursively removes a directory under the root" {
    const gpa = std.testing.allocator;
    var io_instance: std.Io.Threaded = .init(gpa, .{});
    defer io_instance.deinit();
    const io = io_instance.io();

    var tmp = std.testing.tmpDir(.{ .iterate = true });
    defer tmp.cleanup();

    var native: Native = .{ .io = io, .root = tmp.dir };

    try native.interface.mkdir("pkg/sub");
    try native.interface.write("pkg/sub/leaf.zig", "const x = 1;");

    const names = try native.interface.list(gpa);
    defer Fs.freeList(gpa, names);
    var saw_dir = false;
    var saw_file = false;
    for (names) |entry| {
        if (entry.kind == .directory and std.mem.eql(u8, entry.path, "pkg")) saw_dir = true;
        if (entry.kind == .file and std.mem.eql(u8, entry.path, "pkg/sub/leaf.zig")) saw_file = true;
    }
    try std.testing.expect(saw_dir and saw_file);

    try native.interface.remove("pkg");
    try std.testing.expectError(error.FileNotFound, native.interface.read(gpa, "pkg/sub/leaf.zig"));
}
