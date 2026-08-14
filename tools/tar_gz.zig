//! Build-time tool: pack a directory into a gzip-compressed tar, so `build.zig`
//! can `@embedFile` a standard library without shelling out to a system `tar`
//! (keeping the build hermetic). Entry names are each file's path relative to the
//! source directory (`std.zig`, `os/linux.zig`), which is exactly what the module
//! loader asks `Buffer.read` for. Usage: `tar_gz <src_dir> <out.tar.gz>`.

const std = @import("std");

/// A single source file's ceiling; the standard library's files sit far below it.
const max_file_bytes: std.Io.Limit = .limited(64 * 1024 * 1024);

pub fn main(init: std.process.Init) !void {
    const gpa = init.gpa;
    const io = init.io;

    var arg_it: std.process.Args.Iterator = .init(init.minimal.args);
    _ = arg_it.skip(); // argv0
    const src_path = arg_it.next() orelse return error.ExpectedSrcDir;
    const out_path = arg_it.next() orelse return error.ExpectedOutPath;

    var src = try std.Io.Dir.openDirAbsolute(io, src_path, .{ .iterate = true });
    defer src.close(io);

    // Tar every regular file into memory, named by its path relative to the root.
    var tar_buf: std.Io.Writer.Allocating = .init(gpa);
    defer tar_buf.deinit();
    var tar_writer: std.tar.Writer = .{ .underlying_writer = &tar_buf.writer };

    var walker = try src.walk(gpa);
    defer walker.deinit();
    while (try walker.next(io)) |entry| {
        if (entry.kind != .file) continue;
        const data = try src.readFileAlloc(io, entry.path, gpa, max_file_bytes);
        defer gpa.free(data);
        try tar_writer.writeFileBytes(entry.path, data, .{});
    }
    try tar_writer.finishPedantically();

    // Gzip-compress the tar to the output file.
    if (std.fs.path.dirname(out_path)) |parent| {
        try std.Io.Dir.cwd().createDirPath(io, parent);
    }
    var out_file = try std.Io.Dir.cwd().createFile(io, out_path, .{});
    defer out_file.close(io);
    var out_buf: [64 * 1024]u8 = undefined;
    var out_writer = out_file.writer(io, &out_buf);

    const window = try gpa.alloc(u8, std.compress.flate.max_window_len);
    defer gpa.free(window);
    var compress = try std.compress.flate.Compress.init(&out_writer.interface, window, .gzip, .default);
    var tar_in: std.Io.Reader = .fixed(tar_buf.written());
    _ = try tar_in.streamRemaining(&compress.writer);
    try compress.finish();
    try out_writer.flush();
}
