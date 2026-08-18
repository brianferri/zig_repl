//! A host `Io` backed by a `std.Io.Writer`: its stderr write path routes to the writer, its clock reads
//! zero, and every other slot fails via `Io.failing`. A frontend without a real OS `Io` (freestanding
//! wasm) and tests capturing evaluated output use it as `session.runtime.io`, so `std.debug.print` and
//! the other write leaves land in a buffer instead of a file descriptor.

const std = @import("std");
const Io = std.Io;

const WriterIo = @This();

writer: *Io.Writer,

fn operate(userdata: ?*anyopaque, op: Io.Operation) Io.Cancelable!Io.Operation.Result {
    switch (op) {
        .file_write_streaming => |o| {
            const self: *WriterIo = @ptrCast(@alignCast(userdata.?));
            var written: usize = 0;
            self.writer.writeAll(o.header) catch {};
            written += o.header.len;
            if (o.data.len > 0) {
                for (o.data[0 .. o.data.len - 1]) |bytes| {
                    self.writer.writeAll(bytes) catch {};
                    written += bytes.len;
                }
                const last = o.data[o.data.len - 1];
                var i: usize = 0;
                while (i < o.splat) : (i += 1) self.writer.writeAll(last) catch {};
                written += last.len * o.splat;
            }
            return .{ .file_write_streaming = written };
        },
        else => return Io.failing.vtable.operate(userdata, op),
    }
}

fn nowStub(_: ?*anyopaque, _: Io.Clock) Io.Timestamp {
    return .{ .nanoseconds = 0 };
}

const vtable: Io.VTable = blk: {
    var v = Io.failing.vtable.*;
    v.operate = operate;
    v.now = nowStub;
    break :blk v;
};

pub fn io(self: *WriterIo) Io {
    return .{ .userdata = self, .vtable = &vtable };
}
