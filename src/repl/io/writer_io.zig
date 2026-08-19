//! A host `Io` whose write path routes to a `std.Io.Writer` and whose other slots fail via `Io.failing`,
//! for a frontend without an OS `Io` (freestanding wasm) and for tests capturing evaluated output.

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
