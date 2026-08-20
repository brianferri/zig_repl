//! The filesystem `@import` and a running program resolve against: read a source by path, and (for a
//! writable backend) list, write, mkdir, remove, and rename entries. The IO-free interpreter core takes a
//! frontend-injected backend; a read-only backend returns `error.ReadOnly` from the mutators.

const std = @import("std");

const Fs = @This();

vtable: *const VTable,

pub const Error = error{ OutOfMemory, FileNotFound, ReadFailed, ReadOnly, PathAlreadyExists };

pub const Kind = enum { file, directory };

pub const Entry = struct {
    path: []u8,
    kind: Kind,
};

pub const VTable = struct {
    /// Read the full source of `path`, returning newly-allocated NUL-terminated bytes the caller owns.
    /// AstGen requires the sentinel, so it is part of the contract.
    read: *const fn (fs: *Fs, gpa: std.mem.Allocator, path: []const u8) Error![:0]u8,
    list: *const fn (fs: *Fs, gpa: std.mem.Allocator) Error![]Entry,
    write: *const fn (fs: *Fs, path: []const u8, bytes: []const u8) Error!void,
    /// Create an empty directory at `path`, including any missing parents.
    mkdir: *const fn (fs: *Fs, path: []const u8) Error!void,
    /// Remove `path`, whether it names a file or a whole directory subtree.
    remove: *const fn (fs: *Fs, path: []const u8) Error!void,
    /// Move a file or a whole directory subtree. `error.PathAlreadyExists` when `new` is taken.
    rename: *const fn (fs: *Fs, old: []const u8, new: []const u8) Error!void,
};

pub fn read(fs: *Fs, gpa: std.mem.Allocator, path: []const u8) Error![:0]u8 {
    return fs.vtable.read(fs, gpa, path);
}

pub fn list(fs: *Fs, gpa: std.mem.Allocator) Error![]Entry {
    return fs.vtable.list(fs, gpa);
}

pub fn write(fs: *Fs, path: []const u8, bytes: []const u8) Error!void {
    return fs.vtable.write(fs, path, bytes);
}

pub fn mkdir(fs: *Fs, path: []const u8) Error!void {
    return fs.vtable.mkdir(fs, path);
}

pub fn remove(fs: *Fs, path: []const u8) Error!void {
    return fs.vtable.remove(fs, path);
}

pub fn rename(fs: *Fs, old: []const u8, new: []const u8) Error!void {
    return fs.vtable.rename(fs, old, new);
}

pub fn freeList(gpa: std.mem.Allocator, entries: []Entry) void {
    for (entries) |entry| gpa.free(entry.path);
    gpa.free(entries);
}

/// A `list` for a backend with no enumerable tree.
pub fn emptyList(_: *Fs, gpa: std.mem.Allocator) Error![]Entry {
    return gpa.alloc(Entry, 0);
}

/// Mutator slots for a read-only backend: every write rejects with `error.ReadOnly`.
pub const read_only = struct {
    pub fn write(_: *Fs, _: []const u8, _: []const u8) Error!void {
        return error.ReadOnly;
    }
    pub fn mkdir(_: *Fs, _: []const u8) Error!void {
        return error.ReadOnly;
    }
    pub fn remove(_: *Fs, _: []const u8) Error!void {
        return error.ReadOnly;
    }
    pub fn rename(_: *Fs, _: []const u8, _: []const u8) Error!void {
        return error.ReadOnly;
    }
};
