//! The filesystem `@import` and a running program resolve against: read a
//! source by path, and (for a writable backend) list, write, remove, and rename
//! entries. The interpreter core is IO-free (see Session.zig), so a frontend
//! injects a backend -- a real directory (`Native`) where one exists, an
//! in-memory tree (`Vfs`) where none does, an embedded archive (`Buffer`) for a
//! read-only standard library -- and composes project-over-std with `Layered`.
//!
//! Concrete backends embed this struct as a field named `interface` and recover
//! themselves via `@fieldParentPtr("interface", fs)`. A read-only backend
//! returns `error.ReadOnly` from the mutators.

const std = @import("std");

const Fs = @This();

vtable: *const VTable,

pub const Error = error{ OutOfMemory, FileNotFound, ReadFailed, ReadOnly, PathAlreadyExists };

pub const VTable = struct {
    /// Read the full source of `path` (resolved against the backend's own root),
    /// returning newly-allocated NUL-terminated bytes the caller owns. AstGen
    /// requires the sentinel, so it is part of the contract.
    read: *const fn (fs: *Fs, gpa: std.mem.Allocator, path: []const u8) Error![:0]u8,
    /// The backend's own entry paths, as a freshly-allocated slice of owned
    /// strings (caller frees each entry and the slice). A layered backend lists
    /// only its writable layer, not the standard library beneath it.
    list: *const fn (fs: *Fs, gpa: std.mem.Allocator) Error![][]u8,
    /// Create `path` or replace its contents with a copy of `bytes`.
    write: *const fn (fs: *Fs, path: []const u8, bytes: []const u8) Error!void,
    remove: *const fn (fs: *Fs, path: []const u8) Error!void,
    /// Move `old` to `new`; `error.PathAlreadyExists` when `new` is taken.
    rename: *const fn (fs: *Fs, old: []const u8, new: []const u8) Error!void,
};

pub fn read(fs: *Fs, gpa: std.mem.Allocator, path: []const u8) Error![:0]u8 {
    return fs.vtable.read(fs, gpa, path);
}

pub fn list(fs: *Fs, gpa: std.mem.Allocator) Error![][]u8 {
    return fs.vtable.list(fs, gpa);
}

pub fn write(fs: *Fs, path: []const u8, bytes: []const u8) Error!void {
    return fs.vtable.write(fs, path, bytes);
}

pub fn remove(fs: *Fs, path: []const u8) Error!void {
    return fs.vtable.remove(fs, path);
}

pub fn rename(fs: *Fs, old: []const u8, new: []const u8) Error!void {
    return fs.vtable.rename(fs, old, new);
}

/// Free a `list` result: each entry, then the slice.
pub fn freeList(gpa: std.mem.Allocator, entries: [][]u8) void {
    for (entries) |entry| gpa.free(entry);
    gpa.free(entries);
}

/// A `list` for a backend with no enumerable tree (an embedded archive is not
/// the user's editable project).
pub fn emptyList(_: *Fs, gpa: std.mem.Allocator) Error![][]u8 {
    return gpa.alloc([]u8, 0);
}

/// Mutator slots for a read-only backend: every write rejects. A backend that
/// serves bytes it cannot edit points its `write`/`remove`/`rename` here.
pub const read_only = struct {
    pub fn write(_: *Fs, _: []const u8, _: []const u8) Error!void {
        return error.ReadOnly;
    }
    pub fn remove(_: *Fs, _: []const u8) Error!void {
        return error.ReadOnly;
    }
    pub fn rename(_: *Fs, _: []const u8, _: []const u8) Error!void {
        return error.ReadOnly;
    }
};
