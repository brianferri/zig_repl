//! The intrinsic `Io`, as source the interpreter evaluates (not compiled into the REPL binary -- it
//! references the externs the interpreter supplies). `runtime.install` binds its `io` as
//! `root.std_options_debug_io`, so real `std` reaches its vtable. Unoverridden slots are reused from
//! `Io.failing`; the overrides route the leaves a compiled program would reach by syscall to externs the
//! interpreter performs -- `operate` writes to `__repl_write(fd, ...)` (so stdout and stderr both flow,
//! keyed by file descriptor), `now` reads the clock via `__repl_now`. `std.debug.print` reaches this
//! through `lockStderr`, which hands back a standard `File.Writer` whose drain calls `operate`.
//! Target-agnostic today, so `root` embeds it for every target.

const std = @import("std");
const Io = std.Io;

extern fn __repl_write(fd: i64, ptr: [*]const u8, len: usize) void;
extern fn __repl_now(clock: u32) i64;
// Opens `path` on the host, returns an index into the session's file table (the descriptor the returned
// `File` carries), or a negative value on failure.
extern fn __repl_open(path_ptr: [*]const u8, path_len: usize) i64;
// Reads up to `len` bytes from the file at descriptor `fd` into the interpreter buffer at `ptr`; returns
// the count, 0 at end of file, or a negative value on failure.
extern fn __repl_read(fd: i64, ptr: [*]u8, len: usize) i64;
// Ends the lifetime of the file at descriptor `fd`, freeing it for reuse.
extern fn __repl_close(fd: i64) void;

fn handleFromIndex(index: i64) Io.File.Handle {
    return if (Io.File.Handle == void) {} else @intCast(index);
}

fn dirOpenFile(_: ?*anyopaque, _: Io.Dir, sub_path: []const u8, _: Io.Dir.OpenFileOptions) Io.File.OpenError!Io.File {
    const index = __repl_open(sub_path.ptr, sub_path.len);
    if (index < 0) return error.FileNotFound;
    return .{ .handle = handleFromIndex(index), .flags = .{ .nonblocking = false } };
}

// stderr as a raw-handle `File`: `File.stderr()` references a posix constant absent on freestanding,
// whose handle type is `void` there anyway. Handle 2 is the posix stderr descriptor; the interpreter
// routes the write by it (and the freestanding host Io ignores it).
const stderr_file: Io.File = .{
    .handle = if (Io.File.Handle == void) {} else 2,
    .flags = .{ .nonblocking = false },
};

fn handleInt(handle: Io.File.Handle) i64 {
    return if (Io.File.Handle == void) 0 else @intCast(handle);
}

fn emit(fd: i64, bytes: []const u8) void {
    if (bytes.len != 0) __repl_write(fd, bytes.ptr, bytes.len);
}

fn operate(_: ?*anyopaque, op: Io.Operation) Io.Cancelable!Io.Operation.Result {
    switch (op) {
        .file_write_streaming => |o| {
            const fd = handleInt(o.file.handle);
            var written: usize = 0;
            emit(fd, o.header);
            written += o.header.len;
            if (o.data.len > 0) {
                for (o.data[0 .. o.data.len - 1]) |bytes| {
                    emit(fd, bytes);
                    written += bytes.len;
                }
                const last = o.data[o.data.len - 1];
                var i: usize = 0;
                while (i < o.splat) : (i += 1) emit(fd, last);
                written += last.len * o.splat;
            }
            return .{ .file_write_streaming = written };
        },
        .file_read_streaming => |o| {
            const fd = handleInt(o.file.handle);
            var read: usize = 0;
            var requested: usize = 0;
            for (o.data) |slice| {
                if (slice.len == 0) continue;
                requested += slice.len;
                const got = __repl_read(fd, slice.ptr, slice.len);
                if (got < 0) return .{ .file_read_streaming = error.InputOutput };
                read += @intCast(got);
                if (@as(usize, @intCast(got)) < slice.len) break;
            }
            // Only a request for bytes that yields none is end-of-file; a zero-length request is not
            // (the `FileReadStreaming` contract distinguishes a 0-length read from `error.EndOfStream`).
            if (requested != 0 and read == 0) return .{ .file_read_streaming = error.EndOfStream };
            return .{ .file_read_streaming = read };
        },
        else => return Io.failing.vtable.operate(null, op),
    }
}

fn fileClose(_: ?*anyopaque, files: []const Io.File) void {
    for (files) |file| __repl_close(handleInt(file.handle));
}

fn swapCancelProtection(_: ?*anyopaque, _: Io.CancelProtection) Io.CancelProtection {
    return .unblocked;
}

var buf: [64]u8 = undefined;
var fw: Io.File.Writer = undefined;

fn lockStderr(_: ?*anyopaque, _: ?Io.Terminal.Mode) Io.Cancelable!Io.LockedStderr {
    fw = Io.File.Writer.initStreaming(stderr_file, io, &buf);
    return .{ .file_writer = &fw, .terminal_mode = .no_color };
}
fn unlockStderr(_: ?*anyopaque) void {
    fw.interface.flush() catch {};
}

fn clockNow(_: ?*anyopaque, clock: Io.Clock) Io.Timestamp {
    return .{ .nanoseconds = __repl_now(@backingInt(clock)) };
}

const vtable: Io.VTable = blk: {
    var v = Io.failing.vtable.*;
    v.swapCancelProtection = swapCancelProtection;
    v.lockStderr = lockStderr;
    v.unlockStderr = unlockStderr;
    v.operate = operate;
    v.dirOpenFile = dirOpenFile;
    v.fileClose = fileClose;
    v.now = clockNow;
    break :blk v;
};

pub const io: Io = .{ .userdata = null, .vtable = &vtable };
