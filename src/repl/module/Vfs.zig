//! An in-memory `Fs` leaf holding the user's editable files as a directory tree (for freestanding wasm,
//! which has no real filesystem): each directory maps one path component to a child node, so an empty
//! directory is just a childless node. `remove`/`rename` act on a file or a whole subtree; insertion order
//! within a directory is preserved so listings are stable.

const std = @import("std");
const assert = std.debug.assert;
const Fs = @import("Fs.zig");

const Vfs = @This();

const Tree = std.StringArrayHashMapUnmanaged(Node);

const Node = union(enum) {
    file: []u8,
    dir: Tree,
};

const Slot = struct { tree: *Tree, name: []const u8 };

gpa: std.mem.Allocator,
root: Tree = .empty,
interface: Fs = .{ .vtable = &vtable },

const vtable: Fs.VTable = .{
    .read = read,
    .list = list,
    .write = write,
    .mkdir = mkdir,
    .remove = remove,
    .rename = rename,
};

pub fn init(gpa: std.mem.Allocator) Vfs {
    return .{ .gpa = gpa };
}

pub fn deinit(self: *Vfs) void {
    self.freeTree(&self.root);
    self.* = undefined;
}

fn freeTree(self: *Vfs, tree: *Tree) void {
    for (tree.keys(), tree.values()) |key, *node| {
        self.gpa.free(key);
        self.freeNode(node);
    }
    tree.deinit(self.gpa);
}

fn freeNode(self: *Vfs, node: *Node) void {
    switch (node.*) {
        .file => |bytes| self.gpa.free(bytes),
        .dir => |*sub| self.freeTree(sub),
    }
}

/// Whether `path` is strictly nested under directory `dir` (`dir/...`).
fn under(path: []const u8, dir: []const u8) bool {
    return path.len > dir.len and std.mem.startsWith(u8, path, dir) and path[dir.len] == '/';
}

/// The node at `path`, or null if a component is missing or a file stands where a directory is needed.
fn resolve(self: *Vfs, path: []const u8) ?*Node {
    var tree: *Tree = &self.root;
    var it = std.mem.splitScalar(u8, path, '/');
    var name = it.first();
    while (it.next()) |next_comp| {
        const node = tree.getPtr(name) orelse return null;
        tree = switch (node.*) {
            .dir => |*sub| sub,
            .file => return null,
        };
        name = next_comp;
    }
    return tree.getPtr(name);
}

/// The directory containing `path`'s final component, without creating anything.
fn parent(self: *Vfs, path: []const u8) ?Slot {
    var tree: *Tree = &self.root;
    var it = std.mem.splitScalar(u8, path, '/');
    var name = it.first();
    while (it.next()) |next_comp| {
        const node = tree.getPtr(name) orelse return null;
        tree = switch (node.*) {
            .dir => |*sub| sub,
            .file => return null,
        };
        name = next_comp;
    }
    return .{ .tree = tree, .name = name };
}

/// Like `parent`, but the intermediate directories are created as needed. Fails if an intermediate
/// component is an existing file.
fn createParents(self: *Vfs, path: []const u8) Fs.Error!Slot {
    var tree: *Tree = &self.root;
    var it = std.mem.splitScalar(u8, path, '/');
    var name = it.first();
    while (it.next()) |next_comp| {
        tree = try self.descend(tree, name);
        name = next_comp;
    }
    return .{ .tree = tree, .name = name };
}

fn descend(self: *Vfs, tree: *Tree, comp: []const u8) Fs.Error!*Tree {
    const gop = try tree.getOrPut(self.gpa, comp);
    if (gop.found_existing) {
        return switch (gop.value_ptr.*) {
            .dir => |*sub| sub,
            .file => error.PathAlreadyExists,
        };
    }
    gop.key_ptr.* = self.gpa.dupe(u8, comp) catch |err| {
        tree.swapRemoveAt(gop.index);
        return err;
    };
    gop.value_ptr.* = .{ .dir = .empty };
    return &gop.value_ptr.dir;
}

pub fn get(self: *Vfs, path: []const u8) ?[]const u8 {
    const node = self.resolve(path) orelse return null;
    return switch (node.*) {
        .file => |bytes| bytes,
        .dir => null,
    };
}

fn isDir(self: *Vfs, path: []const u8) bool {
    const node = self.resolve(path) orelse return false;
    return node.* == .dir;
}

fn read(fs: *Fs, gpa: std.mem.Allocator, path: []const u8) Fs.Error![:0]u8 {
    const self: *Vfs = @alignCast(@fieldParentPtr("interface", fs));
    assert(path.len > 0);
    const bytes = self.get(path) orelse return error.FileNotFound;
    return gpa.dupeSentinel(u8, bytes, 0);
}

fn list(fs: *Fs, gpa: std.mem.Allocator) Fs.Error![]Fs.Entry {
    const self: *Vfs = @alignCast(@fieldParentPtr("interface", fs));
    var out: std.ArrayListUnmanaged(Fs.Entry) = .empty;
    errdefer {
        for (out.items) |entry| gpa.free(entry.path);
        out.deinit(gpa);
    }
    try appendTree(&self.root, "", gpa, &out);
    return out.toOwnedSlice(gpa);
}

fn appendTree(tree: *const Tree, prefix: []const u8, gpa: std.mem.Allocator, out: *std.ArrayListUnmanaged(Fs.Entry)) Fs.Error!void {
    for (tree.keys(), tree.values()) |name, *node| {
        const full = if (prefix.len == 0)
            try gpa.dupe(u8, name)
        else
            try std.mem.concat(gpa, u8, &.{ prefix, "/", name });
        errdefer gpa.free(full);
        {
            const path = try gpa.dupe(u8, full);
            errdefer gpa.free(path);
            try out.append(gpa, .{ .path = path, .kind = if (node.* == .dir) .directory else .file });
        }
        switch (node.*) {
            .file => {},
            .dir => |*sub| try appendTree(sub, full, gpa, out),
        }
        gpa.free(full);
    }
}

/// Create `path` or overwrite its file contents with a copy of `bytes`, creating parent directories.
fn write(fs: *Fs, path: []const u8, bytes: []const u8) Fs.Error!void {
    const self: *Vfs = @alignCast(@fieldParentPtr("interface", fs));
    assert(path.len > 0);
    const slot = try self.createParents(path);
    const value = try self.gpa.dupe(u8, bytes);
    errdefer self.gpa.free(value);
    const gop = try slot.tree.getOrPut(self.gpa, slot.name);
    if (gop.found_existing) {
        switch (gop.value_ptr.*) {
            .file => |old| self.gpa.free(old),
            .dir => return error.PathAlreadyExists,
        }
    } else {
        gop.key_ptr.* = self.gpa.dupe(u8, slot.name) catch |err| {
            slot.tree.swapRemoveAt(gop.index);
            return err;
        };
    }
    gop.value_ptr.* = .{ .file = value };
}

fn mkdir(fs: *Fs, path: []const u8) Fs.Error!void {
    const self: *Vfs = @alignCast(@fieldParentPtr("interface", fs));
    assert(path.len > 0);
    const slot = try self.createParents(path);
    const gop = try slot.tree.getOrPut(self.gpa, slot.name);
    if (gop.found_existing) return error.PathAlreadyExists;
    gop.key_ptr.* = self.gpa.dupe(u8, slot.name) catch |err| {
        slot.tree.swapRemoveAt(gop.index);
        return err;
    };
    gop.value_ptr.* = .{ .dir = .empty };
}

fn remove(fs: *Fs, path: []const u8) Fs.Error!void {
    const self: *Vfs = @alignCast(@fieldParentPtr("interface", fs));
    const slot = self.parent(path) orelse return error.FileNotFound;
    const idx = slot.tree.getIndex(slot.name) orelse return error.FileNotFound;
    const key = slot.tree.keys()[idx];
    var node = slot.tree.values()[idx];
    slot.tree.swapRemoveAt(idx);
    self.gpa.free(key);
    self.freeNode(&node);
}

fn rename(fs: *Fs, old: []const u8, new: []const u8) Fs.Error!void {
    const self: *Vfs = @alignCast(@fieldParentPtr("interface", fs));
    assert(new.len > 0);
    const src = self.parent(old) orelse return error.FileNotFound;
    const src_idx = src.tree.getIndex(src.name) orelse return error.FileNotFound;
    if (under(new, old) or self.resolve(new) != null) return error.PathAlreadyExists;

    // Detach the source node, holding it by value while the destination slot is prepared. `new` is neither
    // `old`'s subtree nor an existing path, so creating the destination cannot disturb the source.
    const src_key = src.tree.keys()[src_idx];
    var node = src.tree.values()[src_idx];
    src.tree.swapRemoveAt(src_idx);
    self.gpa.free(src_key);
    errdefer self.freeNode(&node);

    const dst = try self.createParents(new);
    const key = try self.gpa.dupe(u8, dst.name);
    errdefer self.gpa.free(key);
    const gop = try dst.tree.getOrPut(self.gpa, dst.name);
    assert(!gop.found_existing);
    gop.key_ptr.* = key;
    gop.value_ptr.* = node;
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
    try testing.expectEqualStrings("a.zig", names[0].path);
    try testing.expectEqual(Fs.Kind.file, names[0].kind);
    try testing.expectEqualStrings("b.zig", names[1].path);

    try vfs.interface.rename("a.zig", "c.zig");
    try testing.expect(vfs.get("a.zig") == null);
    try testing.expectEqualStrings("one-updated", vfs.get("c.zig").?);
    try testing.expectError(error.PathAlreadyExists, vfs.interface.rename("c.zig", "b.zig"));
    try testing.expectError(error.FileNotFound, vfs.interface.rename("missing.zig", "d.zig"));

    try vfs.interface.remove("b.zig");
    try testing.expectError(error.FileNotFound, vfs.interface.remove("b.zig"));
    try testing.expect(vfs.get("b.zig") == null);
}

test "an empty directory persists until removed, and lists as a directory" {
    const gpa = testing.allocator;
    var vfs: Vfs = .init(gpa);
    defer vfs.deinit();

    try vfs.interface.mkdir("src");
    try testing.expectError(error.PathAlreadyExists, vfs.interface.mkdir("src"));

    const listing = try vfs.interface.list(gpa);
    defer Fs.freeList(gpa, listing);
    try testing.expectEqual(@as(usize, 1), listing.len);
    try testing.expectEqualStrings("src", listing[0].path);
    try testing.expectEqual(Fs.Kind.directory, listing[0].kind);

    try vfs.interface.remove("src");
    try testing.expectError(error.FileNotFound, vfs.interface.remove("src"));
}

test "removing a directory drops the whole subtree; renaming moves it" {
    const gpa = testing.allocator;
    var vfs: Vfs = .init(gpa);
    defer vfs.deinit();

    try vfs.interface.write("lib/a.zig", "a");
    try vfs.interface.write("lib/nested/b.zig", "b");
    try vfs.interface.mkdir("lib/empty");
    try vfs.interface.write("keep.zig", "k");

    // A directory implied only by a nested file is still a rename source.
    try vfs.interface.rename("lib", "src");
    try testing.expect(vfs.get("lib/a.zig") == null);
    try testing.expectEqualStrings("a", vfs.get("src/a.zig").?);
    try testing.expectEqualStrings("b", vfs.get("src/nested/b.zig").?);
    try testing.expect(vfs.isDir("src/empty"));
    try testing.expectEqualStrings("k", vfs.get("keep.zig").?);

    try testing.expectError(error.PathAlreadyExists, vfs.interface.rename("src", "src/inside"));

    try vfs.interface.remove("src");
    try testing.expect(vfs.get("src/a.zig") == null);
    try testing.expect(vfs.get("src/nested/b.zig") == null);
    try testing.expect(!vfs.isDir("src"));
    try testing.expectEqualStrings("k", vfs.get("keep.zig").?);
}
