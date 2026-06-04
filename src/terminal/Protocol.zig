//! Type-erased terminal-protocol interface. Modelled after
//! `std.Io.Reader` / `std.Io.Writer`: implementations embed a
//! `Protocol` as a field named `interface` and recover the concrete
//! `*Self` inside their vtable functions via
//! `@fieldParentPtr("interface", p)`.
//!
//! Each protocol owns every piece of knowledge about itself:
//!   * `query_sequence`   -- bytes to emit during negotiation
//!     (empty for always-supported protocols).
//!   * `setup_sequence`   -- bytes to emit to enable, post-negotiation.
//!   * `teardown_sequence` -- bytes to emit on shutdown.
//!   * `vtable.detectSupport` -- scans the negotiation response and
//!     reports whether this protocol's support marker is present.
//!   * `vtable.tryInterpret`  -- token-to-Event interpreter.
//!
//! Adding a new protocol is therefore a single-file change: drop a
//! new file under `protocol/`, register it in the
//! `all_protocols` list in `Terminal.zig`. No edits to a separate
//! capabilities module, no edits to a separate dispatcher table.

const std = @import("std");
const assert = std.debug.assert;
const Token = @import("Standard.zig").Token;
const Event = @import("device").Event.Event;

const Protocol = @This();

/// Human-readable identifier the protocol picks for itself. Shown
/// in the startup `terminal protocols:` line that lists the active
/// protocol set.
name: []const u8,
/// Bytes to emit during capability negotiation. Empty means the
/// protocol is always supported (no query needed).
query_sequence: []const u8,
/// Bytes to emit once negotiation has decided the protocol is
/// supported. Empty for protocols that need no per-session setup.
setup_sequence: []const u8,
/// Bytes to emit on shutdown. Mirrors `setup_sequence`.
teardown_sequence: []const u8,
vtable: *const VTable,

/// Three-way result distinguishes "I'm not interested" from
/// "claimed but accumulating across tokens" -- the second case is
/// what stateful protocols (bracketed paste, future composers) need
/// so the dispatcher knows to keep pulling tokens silently instead
/// of falling through to the next protocol.
pub const Result = union(enum) {
    /// Protocol doesn't recognise this token shape; dispatcher
    /// tries the next protocol in priority order.
    not_mine,
    /// Protocol claimed the token and is mid-accumulation. No event
    /// to surface yet; dispatcher pulls another token without
    /// asking any other protocol.
    consumed,
    /// Protocol claimed the token and produced an event.
    event: Event,
};

pub const VTable = struct {
    /// The function receives `*Protocol` (mutable so stateful
    /// protocols can advance their accumulator) and recovers its
    /// enclosing concrete type via `@fieldParentPtr("interface", p)`.
    tryInterpret: *const fn (p: *Protocol, token: Token) Result,

    /// Decide whether this protocol's support marker is present in
    /// the (concatenated) terminal response to negotiation. Pure
    /// inspection -- no side effects, no state mutation.
    detectSupport: *const fn (p: *const Protocol, response: []const u8) bool,
};

pub fn tryInterpret(p: *Protocol, token: Token) Result {
    assert(@intFromPtr(p.vtable) != 0);
    return p.vtable.tryInterpret(p, token);
}

pub fn detectSupport(p: *const Protocol, response: []const u8) bool {
    assert(@intFromPtr(p.vtable) != 0);
    return p.vtable.detectSupport(p, response);
}

/// Default `detectSupport` for protocols with no probe -- they're
/// always supported. Provided here so each such protocol can wire
/// `.detectSupport = Protocol.alwaysSupported` rather than re-
/// defining the same one-liner.
pub fn alwaysSupported(_: *const Protocol, _: []const u8) bool {
    return true;
}
