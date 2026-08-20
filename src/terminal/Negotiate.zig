//! Capability negotiation: emits each protocol's `query_sequence` plus a DA1 request as a sync sentinel,
//! then drains every reply in one batched read; the DA1 `c` final byte marks the terminal done talking.

const std = @import("std");
const assert = std.debug.assert;
const Protocol = @import("Protocol.zig");
const Csi = @import("standard/Csi.zig");

pub const response_buffer_bytes: u32 = 512;

pub const Result = struct {
    /// Points into the caller's buffer.
    bytes: []const u8,
    /// False means the read timed out without a sentinel; treat the response as
    /// final anyway (some terminals answer capability queries but not DA1).
    da1_terminated: bool,
};

/// `buffer` must hold at least `response_buffer_bytes`; the returned slice points into it.
pub fn run(
    comptime Backend: type,
    backend: *Backend,
    writer: *std.Io.Writer,
    protocols: []const *Protocol,
    buffer: []u8,
) Result {
    assert(buffer.len >= response_buffer_bytes);

    const empty: Result = .{ .bytes = &.{}, .da1_terminated = false };

    for (protocols) |p| {
        if (p.query_sequence.len == 0) continue;
        writer.writeAll(p.query_sequence) catch return empty;
    }
    writer.writeAll("\x1b[c") catch return empty;
    writer.flush() catch return empty;

    var total: u32 = 0;
    // Probe-phase read returns 0 on timeout; two empty reads (~1s silence) = done.
    var empty_reads: u8 = 0;
    while (total < buffer.len) {
        const n = backend.read(buffer[total..]) catch break;
        if (n == 0) {
            empty_reads += 1;
            if (empty_reads >= 2) break;
            continue;
        }
        total += @intCast(n);
        if (Csi.containsFinal(buffer[0..total], null, 'c')) break;
    }

    return .{
        .bytes = buffer[0..total],
        .da1_terminated = Csi.containsFinal(buffer[0..total], null, 'c'),
    };
}

test "DA1 termination: ESC[?6c matches" {
    try std.testing.expect(Csi.containsFinal("\x1b[?6c", null, 'c'));
}

test "DA1 termination: ESC[?6;22c matches" {
    try std.testing.expect(Csi.containsFinal("\x1b[?6;22c", null, 'c'));
}

test "DA1 termination: missing 'c' does not match" {
    try std.testing.expect(!Csi.containsFinal("\x1b[?6", null, 'c'));
}

test "DA1 termination: other CSI final byte does not match" {
    try std.testing.expect(!Csi.containsFinal("\x1b[?6u", null, 'c'));
}
