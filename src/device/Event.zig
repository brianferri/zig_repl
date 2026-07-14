//! Canonical input event surface. Every protocol parser normalises
//! its wire encoding into one of these variants so the consumer
//! (LineEditor, future TUI layers) never branches on protocol
//! identity.

const std = @import("std");

pub const Event = union(enum) {
    key_press: Key,
    /// Emitted only when a protocol's release-reporting mode is
    /// negotiated; most terminals never produce this variant.
    key_release: Key,
    /// Same as `key_press` for most consumers; surfaced separately
    /// so hold-to-repeat editors can act on it.
    key_repeat: Key,
    /// Bracketed-paste payload (`CSI 200~ ... CSI 201~`). Borrowed
    /// from the parser's scratch buffer; copy if it outlives the
    /// next parse call.
    paste: []const u8,
    resize: WindowSize,
    /// `CSI I` -- requires DECSET 1004.
    focus_in,
    /// `CSI O` -- requires DECSET 1004.
    focus_out,
    eof,
};

/// Clamp a raw wire value to a Unicode code point (0..0x10FFFF). Values
/// above the Unicode maximum map to U+FFFD so a malformed wire form still yields a
/// key event rather than tripping an unreachable. Real terminals don't
/// emit these; this is fuzz-safety for the protocol parsers.
pub fn clampCodepoint(raw: u32) u21 {
    if (raw > 0x10ffff) return 0xfffd;
    return @intCast(raw);
}

pub const Key = struct {
    /// Functional keys (arrows, F-keys) use the `key.*` constants
    /// below; character keys carry the typed codepoint directly.
    codepoint: u21,
    modifiers: Modifiers = .{},

    pub fn eql(a: Key, b: Key) bool {
        if (a.codepoint != b.codepoint) return false;
        if (!std.meta.eql(a.modifiers, b.modifiers)) return false;
        return true;
    }
};

pub const Modifiers = packed struct(u8) {
    shift: bool = false,
    alt: bool = false,
    ctrl: bool = false,
    super: bool = false,
    hyper: bool = false,
    meta: bool = false,
    caps_lock: bool = false,
    num_lock: bool = false,

    /// Decode the modifier-parameter wire encoding:
    /// `(actual_mods << 1) | 1`. Wire `0` means absent, `1` means
    /// no modifiers, `2` means Shift, `3` means Alt, etc. After
    /// subtracting 1, the resulting byte's bits match this struct's
    /// packed layout: bit0=shift, bit1=alt, bit2=ctrl, bit3=super,
    /// bit4=hyper, bit5=meta, bit6=caps_lock, bit7=num_lock.
    pub fn fromParam(raw: u32) Modifiers {
        if (raw == 0) return .{};
        const decoded: u8 = @intCast((raw -% 1) & 0xff);
        return @bitCast(decoded);
    }

    pub fn any(m: Modifiers) bool {
        return @as(u8, @bitCast(m)) != 0;
    }
};

pub const WindowSize = struct {
    rows: u16,
    cols: u16,
};

/// Functional key codepoints. Tab/Enter/Escape/Backspace use their
/// ASCII codepoints; everything else lives in the Unicode Private-
/// Use Area (U+E000 block). Each protocol implementation translates
/// from its wire encoding to these values at its own dispatch site.
pub const key = struct {
    pub const tab: u21 = 0x09;
    pub const enter: u21 = 0x0d;
    pub const escape: u21 = 0x1b;
    pub const backspace: u21 = 0x7f;

    // Navigation: U+E000 PUA block, offsets 0x04..0x0D.
    pub const insert: u21 = 0xe004;
    pub const delete: u21 = 0xe005;
    pub const left: u21 = 0xe006;
    pub const right: u21 = 0xe007;
    pub const up: u21 = 0xe008;
    pub const down: u21 = 0xe009;
    pub const page_up: u21 = 0xe00a;
    pub const page_down: u21 = 0xe00b;
    pub const home: u21 = 0xe00c;
    pub const end: u21 = 0xe00d;

    // Function keys F1..F12: U+E014..U+E01F.
    pub const f1: u21 = 0xe014;
    pub const f2: u21 = 0xe015;
    pub const f3: u21 = 0xe016;
    pub const f4: u21 = 0xe017;
    pub const f5: u21 = 0xe018;
    pub const f6: u21 = 0xe019;
    pub const f7: u21 = 0xe01a;
    pub const f8: u21 = 0xe01b;
    pub const f9: u21 = 0xe01c;
    pub const f10: u21 = 0xe01d;
    pub const f11: u21 = 0xe01e;
    pub const f12: u21 = 0xe01f;
};

test "Modifiers.fromParam: 1 (no mods) decodes empty" {
    const m = Modifiers.fromParam(1);
    try std.testing.expect(!m.any());
}

test "Modifiers.fromParam: 2 (shift) decodes shift" {
    const m = Modifiers.fromParam(2);
    try std.testing.expect(m.shift);
    try std.testing.expect(!m.alt);
    try std.testing.expect(!m.ctrl);
}

test "Modifiers.fromParam: 6 (shift+ctrl) decodes both" {
    // Wire form: shift=1, alt=2, ctrl=4 -> shift+ctrl raw = 5+1 = 6.
    const m = Modifiers.fromParam(6);
    try std.testing.expect(m.shift);
    try std.testing.expect(m.ctrl);
    try std.testing.expect(!m.alt);
}

test "Modifiers.fromParam: 0 (absent) decodes empty" {
    const m = Modifiers.fromParam(0);
    try std.testing.expect(!m.any());
}

test "Key.eql: same fields compare equal" {
    const a: Key = .{ .codepoint = 'a', .modifiers = .{ .shift = true } };
    const b: Key = .{ .codepoint = 'a', .modifiers = .{ .shift = true } };
    try std.testing.expect(a.eql(b));
}

test "Key.eql: different codepoint not equal" {
    const a: Key = .{ .codepoint = 'a' };
    const b: Key = .{ .codepoint = 'b' };
    try std.testing.expect(!a.eql(b));
}
