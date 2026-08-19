//! A read-only `Fs` leaf served from an in-memory tar archive -- the standard
//! library packed into the binary and decompressed once at init. Where `Native`
//! needs a real directory, this needs only bytes, so `@import("std")` resolves on
//! a target with no filesystem (freestanding wasm), which otherwise injects no
//! source. `Layered` stacks a writable project over it; its own mutators reject.
//!
//! The archive is a gzip-compressed tar rooted at the standard library
//! directory's contents (built by `build.zig` from the pinned toolchain, so it
//! matches the `std.zig` the interpreter was compiled against). The loader passes
//! `read` a sub-path relative to that root (`std.zig`, `os/linux.zig`), which is a
//! tar entry name once an optional leading `./` is stripped.

const std = @import("std");
const Io = std.Io;
const Fs = @import("Fs.zig");

const Buffer = @This();

gpa: std.mem.Allocator,
/// The decompressed tar bytes, owned and held for the session; each `read`
/// iterates it. Std files are read once (the loader dedups via `import_table`),
/// so a linear scan per import is cheaper than a persistent index.
tar: []const u8,
interface: Fs = .{ .vtable = &vtable },

const vtable: Fs.VTable = .{
    .read = read,
    .list = Fs.emptyList,
    .write = Fs.read_only.write,
    .remove = Fs.read_only.remove,
    .rename = Fs.read_only.rename,
};

/// Upper bound on a tar entry name; `std.fs.max_path_bytes` is unavailable on
/// freestanding, the very target this source exists for. Std's own paths sit far
/// below it.
const max_name_bytes = 4096;

/// Decompress a gzip tar (e.g. an `@embedFile`d archive) into memory. The source
/// borrows nothing from `gzip_tar`; `deinit` frees the decompressed copy.
pub fn init(gpa: std.mem.Allocator, gzip_tar: []const u8) !Buffer {
    var input: Io.Reader = .fixed(gzip_tar);
    const window = try gpa.alloc(u8, std.compress.flate.max_window_len);
    defer gpa.free(window);
    var decompress = std.compress.flate.Decompress.init(&input, .gzip, window);
    const tar = try decompress.reader.allocRemaining(gpa, .unlimited);
    return .{ .gpa = gpa, .tar = tar };
}

pub fn deinit(self: *Buffer) void {
    self.gpa.free(self.tar);
    self.* = undefined;
}

fn read(fs: *Fs, gpa: std.mem.Allocator, path: []const u8) Fs.Error![:0]u8 {
    const self: *Buffer = @alignCast(@fieldParentPtr("interface", fs));
    return readFromTar(self.tar, gpa, path);
}

fn readFromTar(tar: []const u8, gpa: std.mem.Allocator, path: []const u8) Fs.Error![:0]u8 {
    var reader: Io.Reader = .fixed(tar);
    var name_buffer: [max_name_bytes]u8 = undefined;
    var link_name_buffer: [max_name_bytes]u8 = undefined;
    var it: std.tar.Iterator = .init(&reader, .{
        .file_name_buffer = &name_buffer,
        .link_name_buffer = &link_name_buffer,
    });
    while (it.next() catch return error.ReadFailed) |entry| {
        if (entry.kind != .file) continue;
        const name = if (std.mem.startsWith(u8, entry.name, "./")) entry.name[2..] else entry.name;
        if (!std.mem.eql(u8, name, path)) continue;
        const bytes = try gpa.allocSentinel(u8, @intCast(entry.size), 0);
        errdefer gpa.free(bytes);
        var writer: Io.Writer = .fixed(bytes);
        it.streamRemaining(entry, &writer) catch return error.ReadFailed;
        return bytes;
    }
    return error.FileNotFound;
}

test "reads a file's bytes with a NUL sentinel, and reports a missing one" {
    const gpa = std.testing.allocator;

    // A raw (uncompressed) tar with one file suffices to exercise the lookup and
    // sentinel; gzip decompression is std's, covered by the end-to-end path.
    var buf: std.Io.Writer.Allocating = .init(gpa);
    defer buf.deinit();
    var tar_writer: std.tar.Writer = .{ .underlying_writer = &buf.writer };
    try tar_writer.writeFileBytes("./m.zig", "const answer = 42;", .{});
    try tar_writer.finishPedantically();

    const bytes = try readFromTar(buf.written(), gpa, "m.zig");
    defer gpa.free(bytes);
    try std.testing.expectEqualStrings("const answer = 42;", bytes);
    try std.testing.expectEqual(@as(u8, 0), bytes[bytes.len]);
    try std.testing.expectError(error.FileNotFound, readFromTar(buf.written(), gpa, "missing.zig"));
}
