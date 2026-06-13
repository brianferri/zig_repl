//! Capability negotiation. Sends each protocol's `query_sequence`
//! followed by a Primary Device Attributes (DA1) request as a
//! synchronisation sentinel, then reads until the DA1 reply arrives
//! (or the terminal stays silent past the platform's read timeout).
//!
//! Why DA1 as a sentinel: querying each protocol individually with a
//! per-query timeout serialises latency (one round-trip per probe).
//! Batching all queries followed by DA1 lets a single read drain
//! every protocol's reply at once -- the DA1 `c` final byte tells
//! us the terminal is done talking.
//!
//! Reads go through `Platform.read`, so this module is platform-
//! agnostic. POSIX backends configure VTIME for a 500ms read
//! timeout; Windows backends configure ReadFile's overlapped path
//! analogously.
//!
//! Adding a new probed protocol = write its file under `protocol/`
//! and register it in `Terminal.allProtocols`. This module never
//! changes; per-protocol probe logic lives in the protocol's own
//! `detectSupport` vtable function.

const std = @import("std");
const assert = std.debug.assert;
const Protocol = @import("Protocol.zig");
const Csi = @import("standard/Csi.zig");

pub const response_buffer_bytes: u32 = 512;

pub const Result = struct {
    /// Concatenated response bytes; borrowed from caller's buffer.
    bytes: []const u8,
    /// True when DA1 terminated the read normally. False means we
    /// hit the platform's read timeout without a sentinel -- treat
    /// the response as final anyway (some terminals reply to
    /// capability queries but not DA1).
    da1_terminated: bool,
};

/// Send each protocol's `query_sequence` plus the DA1 request, then
/// pull bytes from `backend.read` until DA1 terminates or input
/// stalls. `buffer` must hold at least `response_buffer_bytes` bytes;
/// the returned slice borrows from it for the call's lifetime.
///
/// `Backend` is the comptime-selected platform backend type (see
/// `Terminal.PlatformBackend`). Comptime dispatch avoids the vtable
/// indirection that runtime polymorphism would impose for a value
/// the compiler already knows.
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
    // DA1: Primary Device Attributes. Every conformant ANSI/VT
    // terminal answers; we use that as the "all replies are in" mark.
    writer.writeAll("\x1b[c") catch return empty;
    writer.flush() catch return empty;

    var total: u32 = 0;
    // Bounded loop: probe-phase read returns 0 after its timeout.
    // Two consecutive empty reads (~1s of silence) = terminal done.
    var empty_reads: u8 = 0;
    while (total < buffer.len) {
        const n = backend.read(buffer[total..]) catch break;
        if (n == 0) {
            empty_reads += 1;
            if (empty_reads >= 2) break;
            continue;
        }
        total += @intCast(n);
        // DA1 reply: `ESC [ ? Pn ; ... ; Pn c`. The final `c` is the
        // reliable terminator; intermediate parameters vary by terminal.
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
