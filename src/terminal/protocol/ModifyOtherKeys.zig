//! xterm `modifyOtherKeys` disambiguation. Pre-dates the Kitty
//! Keyboard Protocol; covers the gap left by ECMA-48 where modified
//! letters / symbols / Enter / Tab collide with their unmodified
//! counterparts.
//!
//! Spec ref: xterm ctlseqs sec "Alt and Meta Keys" + "modifyOtherKeys".
//! Two wire encodings (level 1 / level 2):
//!  * `CSI 27 ; <mod> ; <cp> ~` -- the original form (level 1)
//!  * `CSI <cp> ; <mod> u`      -- the u-form (level 2), shared with
//!    the Kitty protocol grammar but without Kitty's sub-parameters
//!
//! The Kitty progressive-enhancement protocol layered on top of the
//! u-form by adding sub-parameters (`:` separators). Because Kitty
//! registers BEFORE ModifyOtherKeys in the dispatcher when both are
//! supported, it claims sequences with sub-parameters first; what
//! falls through is well-formed modifyOtherKeys.
//!
//! Setup is two-phase: `CSI > 4 ; 2 m` enables the u-form. Teardown
//! resets to level 0 (`CSI > 4 ; 0 m`).

const std = @import("std");
const assert = std.debug.assert;
const Protocol = @import("../Protocol.zig");
const Standard = @import("../Standard.zig");

const Event = @import("../../device/Event.zig");
const Csi = @import("../standard/Csi.zig");

const ModifyOtherKeys = @This();

interface: Protocol = .{
    .name = "modifyOtherKeys",
    // xterm doesn't reply to a portable capability query for this
    // extension. The set-mode sequence itself is silently ignored
    // by terminals that don't speak it, so we always include this
    // protocol and let unsupported terminals drop the setup bytes.
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
    assert(@intFromPtr(p) != 0);
    const self: *ModifyOtherKeys = @fieldParentPtr("interface", p);
    assert(@intFromPtr(self) == @intFromPtr(&instance));
    return if (tryInterpret(token)) |e| .{ .event = e } else .not_mine;
}

fn tryInterpret(token: Standard.Token) ?Event.Event {
    if (token != .csi) return null;
    const csi = token.csi;
    // Sub-parameters mean Kitty. ModifyOtherKeys never uses ':'.
    for (csi.subparams_count) |sc| {
        if (sc != 0) return null;
    }
    // Private intermediates (?, >, <) are queries / responses.
    if (csi.intermediates_count != 0) return null;
    return switch (csi.final) {
        '~' => interpretTilde(csi),
        'u' => interpretU(csi),
        else => null,
    };
}

fn interpretTilde(csi: Csi.Sequence) ?Event.Event {
    assert(csi.final == '~');
    // Level-1 form: CSI 27 ; <mod> ; <cp> ~
    if (csi.params_count != 3) return null;
    if (csi.params[0] != 27) return null;
    const modifiers = Event.Modifiers.fromParam(csi.params[1]);
    const cp = csi.params[2];
    return makePress(cp, modifiers);
}

fn interpretU(csi: Csi.Sequence) ?Event.Event {
    assert(csi.final == 'u');
    if (csi.params_count == 0) return null;
    // Level-2 form: CSI <cp> ; <mod> u  (no sub-params: a progressive-
    // enhancement protocol higher in the priority chain already
    // claimed sequences carrying sub-params).
    const cp = csi.params[0];
    const modifier_param = if (csi.params_count >= 2) csi.params[1] else 0;
    const modifiers = Event.Modifiers.fromParam(modifier_param);
    return makePress(cp, modifiers);
}

fn makePress(cp_raw: u32, modifiers: Event.Modifiers) Event.Event {
    // Clamp out-of-Unicode codepoints to U+FFFD (replacement char)
    // so a malformed wire form produces a key event we can ignore
    // rather than crashing the editor.
    const cp: u21 = if (cp_raw <= 0x10ffff) @intCast(cp_raw) else 0xfffd;
    return .{ .key_press = .{ .codepoint = cp, .modifiers = modifiers } };
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
