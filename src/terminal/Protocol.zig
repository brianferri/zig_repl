//! Type-erased terminal-protocol interface, modelled after `std.Io.Reader`:
//! implementations embed a `Protocol` as a field named `interface` and recover
//! the concrete `*Self` inside their vtable via `@fieldParentPtr("interface", p)`.

const std = @import("std");
const assert = std.debug.assert;
const Token = @import("Standard.zig").Token;
const Event = @import("device").Event.Event;

const Protocol = @This();

name: []const u8,
/// Empty means always supported (no query needed).
query_sequence: []const u8,
setup_sequence: []const u8,
teardown_sequence: []const u8,
vtable: *const VTable,

/// The `consumed` arm is what stateful protocols (bracketed paste) need: the
/// dispatcher keeps pulling tokens silently instead of falling through.
pub const Result = union(enum) {
    /// Unrecognised token shape; the dispatcher tries the next protocol.
    not_mine,
    /// Claimed mid-accumulation, no event yet; the dispatcher pulls another
    /// token without asking any other protocol.
    consumed,
    event: Event,
};

pub const VTable = struct {
    /// Mutable `*Protocol` so stateful protocols can advance their accumulator.
    tryInterpret: *const fn (p: *Protocol, token: Token) Result,

    /// Pure inspection of the concatenated negotiation response.
    detectSupport: *const fn (p: *const Protocol, response: []const u8) bool,
};

pub fn tryInterpret(p: *Protocol, token: Token) Result {
    return p.vtable.tryInterpret(p, token);
}

pub fn detectSupport(p: *const Protocol, response: []const u8) bool {
    return p.vtable.detectSupport(p, response);
}

/// Default `detectSupport` for probe-less protocols.
pub fn alwaysSupported(_: *const Protocol, _: []const u8) bool {
    return true;
}
