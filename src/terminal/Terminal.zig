//! Terminal subsystem entry point. Owns the platform backend (raw-
//! mode lifecycle, fd/handle ownership, cleanup on signals or
//! console-control events), capability negotiation, the parser, and
//! the ordered list of active Protocols. Consumers call `readEvent`
//! to pull one canonical `Event` at a time -- no escape-sequence or
//! OS detail leaks past this boundary.
//!
//! Layered design:
//!   * platform backend -- OS-level raw-mode + read surface (impls
//!     under `platform/`). The target is comptime-known, so the
//!     backend is selected by-name via `builtin.os.tag`, not a
//!     runtime vtable.
//!   * `Protocol` -- token-level keyboard protocols (vtable; impls
//!     under `protocol/`). Each owns its own probe query +
//!     detection + interpretation.
//!   * `Standard` / `Parser` -- ECMA-48 byte-stream classifier,
//!     platform- and protocol-agnostic.
//!
//! Adding a new platform = drop a `platform/Foo.zig`, extend the
//! `PlatformBackend` switch. Adding a new protocol = drop a
//! `protocol/Foo.zig`, append it to `known_protocols`. Nothing else
//! needs to change.

const std = @import("std");
const assert = std.debug.assert;
const builtin = @import("builtin");

const Event = @import("device").Event;
const Negotiate = @import("Negotiate.zig");
const Parser = @import("Parser.zig");
const Protocol = @import("Protocol.zig");
const Device = @import("device").Device;
const Color = @import("device").Color;

const Kitty = @import("protocol/Kitty.zig");
const ModifyOtherKeys = @import("protocol/ModifyOtherKeys.zig");
const Xterm = @import("protocol/Xterm.zig");
const BracketedPaste = @import("protocol/BracketedPaste.zig");

/// Comptime-selected backend module. Platform target is known at
/// compile time, so dispatch is by-name through the concrete module
/// -- no runtime vtable indirection. Backends share an identical
/// public surface (`init`, `deinit`, `setRawMode`, `restore`,
/// `read`); adding a new platform = drop a sibling file under
/// `platform/` and extend this switch.
pub const PlatformBackend = switch (builtin.os.tag) {
    .windows => @import("platform/Windows.zig"),
    else => @import("platform/Posix.zig"),
};

const Terminal = @This();

/// Read-side accumulator. A CSI report with sub-parameters and a
/// trailing text codepoint (e.g. `CSI 13:1:1;1:2;65u`) is already
/// 18 bytes; 256 holds the worst-case sequence plus slack.
const read_buffer_bytes: u32 = 256;

/// Source of truth for which protocols exist. Adding a new one is a
/// single-file change: drop `protocol/Foo.zig`, append its
/// `.protocol()` here in priority order. The negotiator + dispatcher
/// pick it up automatically; no other module learns about it.
///
/// BracketedPaste sits at the top so an in-flight paste claims
/// every token before any keypress interpreter sees it.
const known_protocols = [_]*Protocol{
    BracketedPaste.protocol(),
    Kitty.protocol(),
    ModifyOtherKeys.protocol(),
    Xterm.protocol(),
};

backend: PlatformBackend,
writer: *std.Io.Writer,
gpa: std.mem.Allocator,
/// Ordered list of supported protocols, highest-priority first.
/// `Protocol` is embedded as `interface` in each concrete module;
/// the dispatcher calls `Protocol.tryInterpret(p, token)`, which
/// recovers the concrete via `@fieldParentPtr` inside the vtable.
protocols: []const *Protocol,
/// The input-device interface the editor consumes (carries the
/// resolved color capability). Embedded by value so `device()` can
/// hand out `&interface` and the vtable can recover `*Terminal` via
/// `@fieldParentPtr`.
interface: Device,
read_buffer: [read_buffer_bytes]u8 = @splat(0),
read_buffer_len: u32 = 0,

pub fn init(
    gpa: std.mem.Allocator,
    io: std.Io,
    writer: *std.Io.Writer,
    environ: *const std.process.Environ.Map,
) !Terminal {
    var backend = try PlatformBackend.init(gpa, io);
    errdefer backend.deinit(gpa);

    try backend.setRawMode(.probe);
    var probe_buffer: [Negotiate.response_buffer_bytes]u8 = undefined;
    const negotiation = Negotiate.run(
        PlatformBackend,
        &backend,
        writer,
        &known_protocols,
        &probe_buffer,
    );
    try backend.setRawMode(.interactive);

    const protocols = try buildActive(gpa, &known_protocols, negotiation.bytes);
    errdefer gpa.free(protocols);

    // Protocols hold transient state in file-scope singletons; clear the paste
    // accumulator so this terminal can't inherit a mid-paste state left by a
    // previous one in the same process (one terminal is live at a time).
    BracketedPaste.instance = .{};

    for (protocols) |p| {
        if (p.setup_sequence.len == 0) continue;
        try writer.writeAll(p.setup_sequence);
    }
    try writer.flush();

    return .{
        .backend = backend,
        .writer = writer,
        .gpa = gpa,
        .protocols = protocols,
        .interface = .{
            .color_level = Color.fromEnv(environ),
            .vtable = &device_vtable,
        },
    };
}

/// Hand out the device interface for the editor to drive. Valid only
/// for a live `Terminal` whose address is stable: the vtable resolves
/// `*Terminal` from `&interface` via `@fieldParentPtr`, so a copy's
/// `&interface` would point back at the wrong object.
pub fn device(term: *Terminal) *Device {
    return &term.interface;
}

const device_vtable: Device.VTable = .{ .readEvent = vtableReadEvent };

fn vtableReadEvent(d: *Device) anyerror!?Event.Event {
    const term: *Terminal = @fieldParentPtr("interface", d);
    return term.readEvent();
}

pub fn deinit(term: *Terminal) void {

    // Teardown in reverse priority -- the most-derived protocol's
    // teardown fires first (e.g. a protocol-stack pop sequence)
    // before the always-supported protocols' no-ops at the tail.
    var i: u32 = @intCast(term.protocols.len);
    while (i > 0) {
        i -= 1;
        const p = term.protocols[i];
        if (p.teardown_sequence.len == 0) continue;
        // Teardown runs from deinit: there's no caller to propagate
        // an I/O failure to, and the alternative (panic) would leave
        // the user's terminal in raw mode. Swallow + continue so the
        // remaining tear-downs (termios restore, signal handlers)
        // still run.
        term.writer.writeAll(p.teardown_sequence) catch {};
    }
    // Same swallow rationale as the loop above.
    term.writer.flush() catch {};

    term.gpa.free(term.protocols);
    term.backend.deinit(term.gpa);
    term.* = undefined;
}

/// Read the next high-level Event. Returns `null` on stdin EOF.
/// Blocks until at least one event is available.
pub fn readEvent(term: *Terminal) !?Event.Event {
    while (true) {
        if (try term.parsePending()) |event| return event;
        // If the buffer's already full but the parser produced
        // nothing, the wire form is malformed -- drop everything
        // and re-prompt to keep the editor alive.
        if (term.read_buffer_len >= read_buffer_bytes) {
            term.read_buffer_len = 0;
            continue;
        }
        const n = try term.backend.read(term.read_buffer[term.read_buffer_len..]);
        if (n == 0) return null;
        term.read_buffer_len += @intCast(n);
    }
}

/// Try to extract one event from the buffered bytes, consuming them
/// on success. Returns `null` when the buffer holds no complete
/// sequence; the caller must read more bytes.
fn parsePending(term: *Terminal) !?Event.Event {
    if (term.read_buffer_len == 0) return null;
    const result = Parser.parse(term.read_buffer[0..term.read_buffer_len]);
    if (result.token == null) return null;
    const consumed = result.consumed;
    assert(consumed > 0);
    std.mem.copyForwards(
        u8,
        term.read_buffer[0..],
        term.read_buffer[consumed..term.read_buffer_len],
    );
    term.read_buffer_len -= consumed;

    for (term.protocols) |p| {
        switch (Protocol.tryInterpret(p, result.token.?)) {
            .not_mine => continue,
            // Stateful protocol claimed it (bracketed paste mid-
            // accumulation) but has no event yet -- pull the next
            // token without offering it to other protocols.
            .consumed => return try term.parsePending(),
            .event => |event| return event,
        }
    }
    // No protocol claimed (e.g. an OSC reply nobody cares about);
    // drop the token and try again from the buffer.
    return try term.parsePending();
}

/// Build the active-protocol slice from the negotiation response.
/// Each known protocol's `detectSupport` decides whether it's
/// included; the ordering of `known` is preserved (priority).
fn buildActive(
    gpa: std.mem.Allocator,
    known: []const *Protocol,
    response: []const u8,
) ![]const *Protocol {
    assert(known.len > 0);
    var list: std.ArrayListUnmanaged(*Protocol) = .empty;
    errdefer list.deinit(gpa);
    for (known) |p| {
        if (Protocol.detectSupport(p, response)) try list.append(gpa, p);
    }
    assert(list.items.len <= known.len);
    return list.toOwnedSlice(gpa);
}
