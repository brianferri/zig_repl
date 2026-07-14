//! Kitty Keyboard Protocol full progressive-enhancement spec.
//! Reference: https://sw.kovidgoyal.net/kitty/keyboard-protocol/
//!
//! Wire form (input side):
//!   CSI <unicode_key_code>[:<alt1>:<alt2>][;<modifiers>[:<event_type>]][;<text_codepoint>]u
//!
//! Setup sequence pushes flag 1 ("disambiguate escape codes") onto
//! the terminal's progressive-enhancement stack; teardown pops one
//! stack frame. Flag 1 is the minimum for Shift+Enter / Ctrl+Tab.
//! Event-report flag (0b10000) is intentionally not requested, to
//! keep the editor loop simple.

const std = @import("std");
const assert = std.debug.assert;
const Protocol = @import("../Protocol.zig");
const Standard = @import("../Standard.zig");

const Event = @import("device").Event;
const Csi = @import("../standard/Csi.zig");

const Kitty = @This();

interface: Protocol = .{
    .name = "kitty",
    // `CSI ? u` asks the terminal "do you speak the Kitty Keyboard
    // Protocol?" Supported terminals reply with `CSI ? <flags> u`;
    // unsupported ones stay silent. Detection scans for the reply
    // shape -- presence is the signal; we don't need the flags here.
    .query_sequence = "\x1b[?u",
    .setup_sequence = "\x1b[>1u",
    .teardown_sequence = "\x1b[<u",
    .vtable = &.{
        .tryInterpret = vtableTryInterpret,
        .detectSupport = vtableDetectSupport,
    },
},

pub var instance: Kitty = .{};

pub fn protocol() *Protocol {
    return &instance.interface;
}

fn vtableTryInterpret(p: *Protocol, token: Standard.Token) Protocol.Result {
    const self: *Kitty = @fieldParentPtr("interface", p);
    assert(@intFromPtr(self) == @intFromPtr(&instance));
    return if (tryInterpret(token)) |e| .{ .event = e } else .not_mine;
}

fn tryInterpret(token: Standard.Token) ?Event.Event {
    if (token != .csi) return null;
    const csi = token.csi;
    if (csi.final != 'u') return null;
    if (csi.hasPrivateLead()) return null;
    if (csi.params_count == 0) return null;
    return interpretKitty(csi);
}

fn interpretKitty(csi: Csi.Sequence) ?Event.Event {
    assert(csi.final == 'u');
    assert(csi.params_count >= 1);
    // The wire form's optional sub-params (alternate codepoint at
    // `params[0]:<alt>`, text codepoint at the third primary slot)
    // are parsed by the byte-level Parser but not surfaced on
    // Event.Key: no consumer in the editor reads them.
    const cp_raw = csi.params[0];
    const modifier_param: u32 = if (csi.params_count >= 2) csi.params[1] else 0;
    const event_type: u32 = if (csi.params_count >= 2 and csi.subparams_count[1] >= 1)
        csi.subparams[1][0]
    else
        1; // 1 = press default per spec

    const key: Event.Key = .{
        .codepoint = Event.clampCodepoint(cp_raw),
        .modifiers = Event.Modifiers.fromParam(modifier_param),
    };

    return switch (event_type) {
        2 => .{ .key_repeat = key },
        3 => .{ .key_release = key },
        // Forward-compat: unknown event_type values treated as press.
        else => .{ .key_press = key },
    };
}

fn vtableDetectSupport(_: *const Protocol, response: []const u8) bool {
    // The Kitty reply has the shape `ESC [ ? <decimal_flags> u`. The
    // leading `?` discriminates it from a bare `ESC [ N u` keypress (a
    // Kitty key report, not a capability reply).
    return Csi.containsFinal(response, '?', 'u');
}

test "kitty: CSI 13;2u -> Shift+Enter key_press" {
    var csi: Csi.Sequence = .{ .final = 'u' };
    csi.params[0] = 13;
    csi.params[1] = 2;
    csi.params_count = 2;
    const e = tryInterpret(.{ .csi = csi }).?;
    try std.testing.expect(e == .key_press);
    try std.testing.expectEqual(Event.key.enter, e.key_press.codepoint);
    try std.testing.expect(e.key_press.modifiers.shift);
}

test "kitty: event_type=3 -> key_release" {
    var csi: Csi.Sequence = .{ .final = 'u' };
    csi.params[0] = 'a';
    csi.params[1] = 1;
    csi.params_count = 2;
    csi.subparams[1][0] = 3;
    csi.subparams_count[1] = 1;
    const e = tryInterpret(.{ .csi = csi }).?;
    try std.testing.expect(e == .key_release);
    try std.testing.expectEqual(@as(u21, 'a'), e.key_release.codepoint);
}

test "kitty: event_type=2 -> key_repeat" {
    var csi: Csi.Sequence = .{ .final = 'u' };
    csi.params[0] = 'a';
    csi.params[1] = 1;
    csi.params_count = 2;
    csi.subparams[1][0] = 2;
    csi.subparams_count[1] = 1;
    const e = tryInterpret(.{ .csi = csi }).?;
    try std.testing.expect(e == .key_repeat);
}

test "kitty: missing modifier defaults to none" {
    var csi: Csi.Sequence = .{ .final = 'u' };
    csi.params[0] = 65;
    csi.params_count = 1;
    const e = tryInterpret(.{ .csi = csi }).?;
    try std.testing.expectEqual(@as(u21, 'A'), e.key_press.codepoint);
    try std.testing.expect(!e.key_press.modifiers.any());
}

test "kitty: CSI ?u (probe response) NOT claimed" {
    var csi: Csi.Sequence = .{ .final = 'u' };
    csi.intermediates[0] = '?';
    csi.intermediates_count = 1;
    try std.testing.expect(tryInterpret(.{ .csi = csi }) == null);
}

test "kitty: out-of-range codepoint clamps to U+FFFD" {
    var csi: Csi.Sequence = .{ .final = 'u' };
    csi.params[0] = 0x200000;
    csi.params_count = 1;
    const e = tryInterpret(.{ .csi = csi }).?;
    try std.testing.expectEqual(@as(u21, 0xfffd), e.key_press.codepoint);
}

test "kitty: ignores non-CSI tokens" {
    try std.testing.expect(tryInterpret(.{ .ground = 'a' }) == null);
    try std.testing.expect(tryInterpret(.{ .ss3 = .{ .final = 'A' } }) == null);
}

test "kitty: detection accepts ESC[?5u" {
    try std.testing.expect(Csi.containsFinal("\x1b[?5u", '?', 'u'));
}

test "kitty: detection rejects bare ESC[5u (no '?')" {
    try std.testing.expect(!Csi.containsFinal("\x1b[5u", '?', 'u'));
}

test "kitty: detection finds the reply embedded in DA1+other noise" {
    try std.testing.expect(Csi.containsFinal("\x1b[?5u\x1b[?6c", '?', 'u'));
}

test "kitty: protocol() returns a usable Protocol pointer" {
    const p = protocol();
    try std.testing.expectEqualStrings("kitty", p.name);
    var csi: Csi.Sequence = .{ .final = 'u' };
    csi.params[0] = 13;
    csi.params[1] = 2;
    csi.params_count = 2;
    const result = p.vtable.tryInterpret(p, .{ .csi = csi });
    try std.testing.expect(result == .event);
    try std.testing.expectEqual(Event.key.enter, result.event.key_press.codepoint);
}
