//! xterm `modifyOtherKeys` disambiguation, covering the ECMA-48 gap where
//! modified letters / Enter / Tab collide with their unmodified forms. Two wire
//! encodings: `CSI 27 ; <mod> ; <cp> ~` (level 1) and `CSI <cp> ; <mod> u`
//! (level 2, sub-param-free). Kitty registers first and claims the sub-param
//! variants, so what falls through here is well-formed modifyOtherKeys.

const std = @import("std");
const assert = std.debug.assert;
const Protocol = @import("../Protocol.zig");
const Standard = @import("../Standard.zig");

const Event = @import("device").Event;
const Csi = @import("../standard/Csi.zig");

const ModifyOtherKeys = @This();

interface: Protocol = .{
    .name = "modifyOtherKeys",
    // No portable capability query; unsupported terminals silently ignore the
    // set-mode sequence, so this protocol is always included.
    .query_sequence = "",
    .setup_sequence = "\x1b[>4;2m",
    .teardown_sequence = "\x1b[>4;0m",
    .vtable = &.{
        .tryInterpret = vtableTryInterpret,
        .detectSupport = Protocol.alwaysSupported,
    },
},

pub var instance: ModifyOtherKeys = .{};

pub fn protocol() *Protocol {
    return &instance.interface;
}

fn vtableTryInterpret(p: *Protocol, token: Standard.Token) Protocol.Result {
    const self: *ModifyOtherKeys = @fieldParentPtr("interface", p);
    assert(@intFromPtr(self) == @intFromPtr(&instance));
    return if (tryInterpret(token)) |e| .{ .event = e } else .not_mine;
}

fn tryInterpret(token: Standard.Token) ?Event.Event {
    if (token != .csi) return null;
    const csi = token.csi;
    // Sub-parameters mean Kitty; modifyOtherKeys never uses ':'.
    for (csi.subparams_count) |sc| {
        if (sc != 0) return null;
    }
    if (csi.intermediates_count != 0) return null;
    return switch (csi.final) {
        '~' => interpretTilde(csi),
        'u' => interpretU(csi),
        else => null,
    };
}

fn interpretTilde(csi: Csi.Sequence) ?Event.Event {
    assert(csi.final == '~');
    if (csi.params_count != 3) return null;
    if (csi.params[0] != 27) return null;
    const modifiers = Event.Modifiers.fromParam(csi.params[1]);
    const cp = csi.params[2];
    return makePress(cp, modifiers);
}

fn interpretU(csi: Csi.Sequence) ?Event.Event {
    assert(csi.final == 'u');
    if (csi.params_count == 0) return null;
    const cp = csi.params[0];
    const modifier_param = if (csi.params_count >= 2) csi.params[1] else 0;
    const modifiers = Event.Modifiers.fromParam(modifier_param);
    return makePress(cp, modifiers);
}

fn makePress(cp_raw: u32, modifiers: Event.Modifiers) Event.Event {
    return .{ .key_press = .{ .codepoint = Event.clampCodepoint(cp_raw), .modifiers = modifiers } };
}

test "modifyOtherKeys: CSI 27;2;13~ -> Shift+Enter" {
    var csi: Csi.Sequence = .{ .final = '~' };
    csi.params[0] = 27;
    csi.params[1] = 2;
    csi.params[2] = 13;
    csi.params_count = 3;
    const e = tryInterpret(.{ .csi = csi }).?;
    try std.testing.expectEqual(Event.key.enter, e.key_press.codepoint);
    try std.testing.expect(e.key_press.modifiers.shift);
}

test "modifyOtherKeys: CSI 65;6u -> Ctrl+Shift+A (level-2 u form)" {
    var csi: Csi.Sequence = .{ .final = 'u' };
    csi.params[0] = 65;
    csi.params[1] = 6;
    csi.params_count = 2;
    const e = tryInterpret(.{ .csi = csi }).?;
    try std.testing.expectEqual(@as(u21, 'A'), e.key_press.codepoint);
    try std.testing.expect(e.key_press.modifiers.shift);
    try std.testing.expect(e.key_press.modifiers.ctrl);
}

test "modifyOtherKeys: CSI 13;2:1u (Kitty sub-param) NOT claimed" {
    var csi: Csi.Sequence = .{ .final = 'u' };
    csi.params[0] = 13;
    csi.params[1] = 2;
    csi.params_count = 2;
    csi.subparams[1][0] = 1;
    csi.subparams_count[1] = 1;
    try std.testing.expect(tryInterpret(.{ .csi = csi }) == null);
}

test "modifyOtherKeys: CSI 27;2;13~ falls through if leading not 27" {
    var csi: Csi.Sequence = .{ .final = '~' };
    csi.params[0] = 28;
    csi.params[1] = 2;
    csi.params[2] = 13;
    csi.params_count = 3;
    try std.testing.expect(tryInterpret(.{ .csi = csi }) == null);
}

test "modifyOtherKeys: ignores non-CSI tokens" {
    try std.testing.expect(tryInterpret(.{ .ground = 'a' }) == null);
    try std.testing.expect(tryInterpret(.{ .ss3 = .{ .final = 'A' } }) == null);
}
