//! Terminal subsystem entry point. Owns the platform backend, capability
//! negotiation, the parser, and the ordered list of active Protocols. Consumers
//! call `readEvent` for one canonical `Event` at a time; no escape-sequence or
//! OS detail leaks past this boundary.

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

/// Comptime-selected backend module; backends share an identical public
/// surface (`init`, `deinit`, `setRawMode`, `restore`, `read`).
pub const PlatformBackend = switch (builtin.os.tag) {
    .windows => @import("platform/Windows.zig"),
    else => @import("platform/Posix.zig"),
};

const Terminal = @This();

/// 256 holds the worst-case CSI report (e.g. `CSI 13:1:1;1:2;65u`) plus slack.
const read_buffer_bytes: u32 = 256;

/// Priority order: BracketedPaste first so an in-flight paste claims every token
/// before any keypress interpreter sees it.
const known_protocols = [_]*Protocol{
    BracketedPaste.protocol(),
    Kitty.protocol(),
    ModifyOtherKeys.protocol(),
    Xterm.protocol(),
};

backend: PlatformBackend,
writer: *std.Io.Writer,
gpa: std.mem.Allocator,
/// Highest-priority first.
protocols: []const *Protocol,
/// Embedded by value so `device()` can hand out `&interface` and the vtable
/// recovers `*Terminal` via `@fieldParentPtr`.
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

    // Protocols keep transient state in file-scope singletons; clear the paste
    // accumulator so this terminal can't inherit a prior one's mid-paste state.
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

/// Valid only for a `Terminal` at a stable address: the vtable resolves
/// `*Terminal` from `&interface` via `@fieldParentPtr`, so a copy's `&interface`
/// points back at the wrong object.
pub fn device(term: *Terminal) *Device {
    return &term.interface;
}

const device_vtable: Device.VTable = .{ .readEvent = vtableReadEvent };

fn vtableReadEvent(d: *Device) anyerror!?Event.Event {
    const term: *Terminal = @fieldParentPtr("interface", d);
    return term.readEvent();
}

pub fn deinit(term: *Terminal) void {

    // Reverse priority: a protocol's teardown must undo its setup before the
    // lower-priority protocols' run.
    var i: u32 = @intCast(term.protocols.len);
    while (i > 0) {
        i -= 1;
        const p = term.protocols[i];
        if (p.teardown_sequence.len == 0) continue;
        // No caller to propagate to, and a panic would strand the terminal in
        // raw mode; swallow so the remaining tear-downs still run.
        term.writer.writeAll(p.teardown_sequence) catch {};
    }
    term.writer.flush() catch {};

    term.gpa.free(term.protocols);
    term.backend.deinit(term.gpa);
    term.* = undefined;
}

/// Returns `null` on stdin EOF; blocks until an event is available.
pub fn readEvent(term: *Terminal) !?Event.Event {
    while (true) {
        if (try term.parsePending()) |event| return event;
        // A full buffer that parses to nothing is malformed wire input; drop it
        // all and re-prompt to keep the editor alive.
        if (term.read_buffer_len >= read_buffer_bytes) {
            term.read_buffer_len = 0;
            continue;
        }
        const n = try term.backend.read(term.read_buffer[term.read_buffer_len..]);
        if (n == 0) return null;
        term.read_buffer_len += @intCast(n);
    }
}

/// `null` when the buffer holds no complete sequence; the caller reads more.
fn parsePending(term: *Terminal) !?Event.Event {
    // Each pass consumes >0 bytes from a finite buffer, so the loop is bounded.
    while (true) {
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
                // A stateful protocol claimed it mid-accumulation with no event
                // yet; pull the next token without offering it to others.
                .consumed => break,
                .event => |event| return event,
            }
        }
    }
}

/// Each known protocol's `detectSupport` decides inclusion; `known`'s order
/// (priority) is preserved.
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
