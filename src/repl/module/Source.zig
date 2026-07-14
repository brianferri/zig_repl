//! Where `@import` obtains module and file bytes. The interpreter core is
//! IO-free (see Session.zig), so a frontend that can reach the filesystem (the
//! native TTY driver) injects a reader, while one that cannot (freestanding
//! wasm) injects a `Buffer` over an embedded archive -- or none, leaving
//! `@import("std")` unresolved. Concrete readers embed this struct as a field
//! named `interface` and recover themselves via `@fieldParentPtr("interface", source)`.

const std = @import("std");

const Source = @This();

vtable: *const VTable,

pub const Error = error{ OutOfMemory, FileNotFound, ReadFailed };

pub const VTable = struct {
    /// Read the full source of `path` (resolved against the reader's own root),
    /// returning newly-allocated NUL-terminated bytes the caller owns. AstGen
    /// requires the sentinel, so it is part of the contract.
    read: *const fn (source: *Source, gpa: std.mem.Allocator, path: []const u8) Error![:0]u8,
};

pub fn read(source: *Source, gpa: std.mem.Allocator, path: []const u8) Error![:0]u8 {
    return source.vtable.read(source, gpa, path);
}
