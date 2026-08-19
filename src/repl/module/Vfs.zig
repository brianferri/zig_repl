//! An in-memory `Fs` leaf: a mutable map of path to bytes holding the user's editable files, for a target
//! with no real filesystem (freestanding wasm). Insertion order is preserved so a listing is stable.

const std = @import("std");
const assert = std.debug.assert;
const Fs = @import("Fs.zig");

const Vfs = @This();

gpa: std.mem.Allocator,
files: std.StringArrayHashMapUnmanaged([]u8) = .empty,
interface: Fs = .{ .vtable = &vtable },

const vtable: Fs.VTable = .{
    .read = read,
    .list = list,
    .write = write,
    .remove = remove,
    .rename = rename,
};

pub fn init(gpa: std.mem.Allocator) Vfs {
    return .{ .gpa = gpa };
}

pub fn deinit(self: *Vfs) void {
    for (self.files.keys(), self.files.values()) |key, value| {
        self.gpa.free(key);
        self.gpa.free(value);
    }
    self.files.deinit(self.gpa);
    self.* = undefined;
}

pub fn get(self: *const Vfs, path: []const u8) ?[]const u8 {
    return self.files.get(path);
}

fn read(fs: *Fs, gpa: std.mem.Allocator, path: []const u8) Fs.Error![:0]u8 {
    const self: *Vfs = @alignCast(@fieldParentPtr("interface", fs));
    assert(path.len > 0);
    const bytes = self.files.get(path) orelse return error.FileNotFound;
    return gpa.dupeSentinel(u8, bytes, 0);
}

fn list(fs: *Fs, gpa: std.mem.Allocator) Fs.Error![][]u8 {
    const self: *Vfs = @alignCast(@fieldParentPtr("interface", fs));
    const keys = self.files.keys();
    const out = try gpa.alloc([]u8, keys.len);
    errdefer gpa.free(out);
    var filled: usize = 0;
    errdefer for (out[0..filled]) |entry| gpa.free(entry);
    for (keys, out) |key, *slot| {
        slot.* = try gpa.dupe(u8, key);
        filled += 1;
    }
    return out;
}

/// Create `path` or overwrite its contents with a copy of `bytes`. The key is duplicated only when the
/// path is new, so a caller may hold a path's key across a `write`.
fn write(fs: *Fs, path: []const u8, bytes: []const u8) Fs.Error!void {
    const self: *Vfs = @alignCast(@fieldParentPtr("interface", fs));
    assert(path.len > 0);
    const value = try self.gpa.dupe(u8, bytes);
    errdefer self.gpa.free(value);
    const gop = try self.files.getOrPut(self.gpa, path);
    if (gop.found_existing) {
        self.gpa.free(gop.value_ptr.*);
    } else {
        gop.key_ptr.* = self.gpa.dupe(u8, path) catch |err| {
            self.files.swapRemoveAt(gop.index);
            return err;
        };
    }
    gop.value_ptr.* = value;
}

fn remove(fs: *Fs, path: []const u8) Fs.Error!void {
    const self: *Vfs = @alignCast(@fieldParentPtr("interface", fs));
    const entry = self.files.fetchSwapRemove(path) orelse return error.FileNotFound;
    self.gpa.free(entry.key);
    self.gpa.free(entry.value);
}

fn rename(fs: *Fs, old: []const u8, new: []const u8) Fs.Error!void {
    const self: *Vfs = @alignCast(@fieldParentPtr("interface", fs));
    assert(new.len > 0);
    if (!self.files.contains(old)) return error.FileNotFound;
    if (self.files.contains(new)) return error.PathAlreadyExists;
    const entry = self.files.fetchSwapRemove(old).?;
    self.gpa.free(entry.key);
    errdefer self.gpa.free(entry.value);
    try self.files.put(self.gpa, try self.gpa.dupe(u8, new), entry.value);
}

const testing = std.testing;

test "serves stored files with a NUL sentinel and reports a miss" {
    const gpa = testing.allocator;
    var vfs: Vfs = .init(gpa);
    defer vfs.deinit();

    try vfs.interface.write("main.zig", "const x = 1;");
    const main = try vfs.interface.read(gpa, "main.zig");
    defer gpa.free(main);
    try testing.expectEqualStrings("const x = 1;", main);
    try testing.expectEqual(@as(u8, 0), main[main.len]);
    try testing.expectError(error.FileNotFound, vfs.interface.read(gpa, "missing.zig"));
}

test "write overwrites in place; rename and remove move and drop entries" {
    const gpa = testing.allocator;
    var vfs: Vfs = .init(gpa);
    defer vfs.deinit();

    try vfs.interface.write("a.zig", "one");
    try vfs.interface.write("b.zig", "two");
    try vfs.interface.write("a.zig", "one-updated");
    try testing.expectEqualStrings("one-updated", vfs.get("a.zig").?);

    const names = try vfs.interface.list(gpa);
    defer Fs.freeList(gpa, names);
    try testing.expectEqual(@as(usize, 2), names.len);
    try testing.expectEqualStrings("a.zig", names[0]);
    try testing.expectEqualStrings("b.zig", names[1]);

    try vfs.interface.rename("a.zig", "c.zig");
    try testing.expect(vfs.get("a.zig") == null);
    try testing.expectEqualStrings("one-updated", vfs.get("c.zig").?);
    try testing.expectError(error.PathAlreadyExists, vfs.interface.rename("c.zig", "b.zig"));
    try testing.expectError(error.FileNotFound, vfs.interface.rename("missing.zig", "d.zig"));

    try vfs.interface.remove("b.zig");
    try testing.expectError(error.FileNotFound, vfs.interface.remove("b.zig"));
    try testing.expect(vfs.get("b.zig") == null);
}
