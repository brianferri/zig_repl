//! xterm keypress interpretation -- the de-facto compatibility
//! baseline. Covers the CSI / SS3 sequences xterm defines for arrow
//! keys, function keys, navigation keys, and their Ctrl/Shift-
//! modified forms, plus the ASCII/C0 ground-byte mapping every
//! xterm-compatible terminal assumes (Ctrl+letter encoding, Tab,
//! Enter via CR/LF, Backspace via BS/DEL).
//!
//! Always registered; assumed supported because every modern
//! terminal speaks at least this dialect.
//!
//! Spec refs:
//!   * xterm ctlseqs (https://invisible-island.net/xterm/ctlseqs/
//!     ctlseqs.html), sections "PC-Style Function Keys" and
//!     "Vt220-Style Function Keys".
//!   * VT100 manual sec 8.6.5 (SS3 application-mode keys), the
//!     historical predecessor xterm extended.
//!
//! Modifier encoding lives in `Event.Modifiers.fromParam`: the
//! second primary parameter is `(mods << 1) | 1`.

const std = @import("std");
const assert = std.debug.assert;
const Protocol = @import("../Protocol.zig");
const Standard = @import("../Standard.zig");

const Event = @import("../Event.zig");
const Csi = @import("../standard/Csi.zig");
const Ss3 = @import("../standard/Ss3.zig");

const Xterm = @This();

interface: Protocol = .{
    .name = "xterm",
    .query_sequence = "",
    .setup_sequence = "",
    .teardown_sequence = "",
    .vtable = &.{
        .tryInterpret = vtableTryInterpret,
        // No probe -- every modern terminal speaks at least this.
        .detectSupport = Protocol.alwaysSupported,
    },
},

/// File-scope instance for the stateless protocol. Callers grab
/// `&instance.interface` for dispatch; no state to mutate. Matches
/// `std.heap.page_allocator`'s single-static-instance pattern.
pub var instance: Xterm = .{};

pub fn protocol() *Protocol {
    return &instance.interface;
}

fn vtableTryInterpret(p: *Protocol, token: Standard.Token) Protocol.Result {
    assert(@intFromPtr(p) != 0);
    const self: *Xterm = @fieldParentPtr("interface", p);
    assert(@intFromPtr(self) == @intFromPtr(&instance));
    return toResult(tryInterpret(token));
}

fn toResult(maybe: ?Event.Event) Protocol.Result {
    return if (maybe) |e| .{ .event = e } else .not_mine;
}

fn tryInterpret(token: Standard.Token) ?Event.Event {
    return switch (token) {
        .ground => |b| interpretGround(b),
        .csi => |csi| interpretCsi(csi),
        .ss3 => |ss3| interpretSs3(ss3),
        .escape_alt => |b| .{ .key_press = .{
            .codepoint = b,
            .modifiers = .{ .alt = true },
        } },
        .bare_escape => .{ .key_press = .{ .codepoint = Event.key.escape } },
        .osc => null,
    };
}

fn interpretGround(b: u8) ?Event.Event {
    return switch (b) {
        // C0 controls -> Ctrl+letter (with the documented exceptions).
        0x00 => .{ .key_press = .{ .codepoint = '@', .modifiers = .{ .ctrl = true } } },
        0x08 => .{ .key_press = .{ .codepoint = Event.key.backspace } },
        0x09 => .{ .key_press = .{ .codepoint = Event.key.tab } },
        0x0A, 0x0D => .{ .key_press = .{ .codepoint = Event.key.enter } },
        0x1B => .{ .key_press = .{ .codepoint = Event.key.escape } },
        0x7F => .{ .key_press = .{ .codepoint = Event.key.backspace } },
        // Other C0 -> Ctrl + lowercase letter. 0x01 -> 'a', etc.
        0x01...0x07,
        0x0B...0x0C,
        0x0E...0x1A,
        => .{ .key_press = .{
            .codepoint = @as(u21, b) + 0x60,
            .modifiers = .{ .ctrl = true },
        } },
        // Printable ASCII -- pass through. UTF-8 multibyte sequences
        // arrive byte-at-a-time and aren't yet assembled into
        // codepoints; that's a Stage-9 ergonomics extension.
        0x20...0x7E => .{ .key_press = .{ .codepoint = b } },
        else => null,
    };
}

fn interpretCsi(csi: Csi.Sequence) ?Event.Event {
    assert(csi.final >= 0x40);
    assert(csi.final <= 0x7e);
    assert(csi.params_count <= Csi.max_params);
    assert(csi.intermediates_count <= Csi.max_intermediates);
    // Sequences with `?` / `>` / `<` private intermediates are
    // capability replies (DA1, progressive enhancement) -- not key
    // events; don't claim them here.
    if (csi.hasIntermediate('?')) return null;
    if (csi.hasIntermediate('>')) return null;
    if (csi.hasIntermediate('<')) return null;

    // xterm modifier convention: when present, modifiers live in
    // the second primary parameter and the leading position is the
    // sentinel `1`. Unmodified sequences have a single param or none.
    const modifier_param = csi.param(1, 0);
    const modifiers = Event.Modifiers.fromParam(modifier_param);

    // Final-byte map for ECMA-48 CSI without `~` suffix.
    switch (csi.final) {
        'A' => return makePress(Event.key.up, modifiers),
        'B' => return makePress(Event.key.down, modifiers),
        'C' => return makePress(Event.key.right, modifiers),
        'D' => return makePress(Event.key.left, modifiers),
        'H' => return makePress(Event.key.home, modifiers),
        'F' => return makePress(Event.key.end, modifiers),
        'P' => return makePress(Event.key.f1, modifiers),
        'Q' => return makePress(Event.key.f2, modifiers),
        'R' => return makePress(Event.key.f3, modifiers),
        'S' => return makePress(Event.key.f4, modifiers),
        'Z' => return .{ .key_press = .{
            .codepoint = Event.key.tab,
            .modifiers = .{ .shift = true },
        } },
        '~' => return interpretCsiTilde(csi.param(0, 0), modifiers),
        // 'u' final without intermediates belongs to progressive-
        // enhancement protocols; let them claim it.
        'u' => return null,
        else => return null,
    }
}

fn interpretCsiTilde(num: u32, modifiers: Event.Modifiers) ?Event.Event {
    const cp: u21 = switch (num) {
        1 => Event.key.home,
        2 => Event.key.insert,
        3 => Event.key.delete,
        4 => Event.key.end,
        5 => Event.key.page_up,
        6 => Event.key.page_down,
        7 => Event.key.home, // rxvt variant
        8 => Event.key.end, // rxvt variant
        11 => Event.key.f1,
        12 => Event.key.f2,
        13 => Event.key.f3,
        14 => Event.key.f4,
        15 => Event.key.f5,
        17 => Event.key.f6,
        18 => Event.key.f7,
        19 => Event.key.f8,
        20 => Event.key.f9,
        21 => Event.key.f10,
        23 => Event.key.f11,
        24 => Event.key.f12,
        else => return null,
    };
    return makePress(cp, modifiers);
}

fn interpretSs3(ss3: Ss3.Sequence) ?Event.Event {
    assert(ss3.final != 0);
    const cp: u21 = switch (ss3.final) {
        'A' => Event.key.up,
        'B' => Event.key.down,
        'C' => Event.key.right,
        'D' => Event.key.left,
        'H' => Event.key.home,
        'F' => Event.key.end,
        'P' => Event.key.f1,
        'Q' => Event.key.f2,
        'R' => Event.key.f3,
        'S' => Event.key.f4,
        else => return null,
    };
    return .{ .key_press = .{ .codepoint = cp } };
}

fn makePress(cp: u21, modifiers: Event.Modifiers) Event.Event {
    return .{ .key_press = .{ .codepoint = cp, .modifiers = modifiers } };
}

test "xterm: ground 'a' -> press 'a'" {
    const e = tryInterpret(.{ .ground = 'a' }).?;
    try std.testing.expectEqual(@as(u21, 'a'), e.key_press.codepoint);
}

test "xterm: Ctrl+A (0x01) decodes to 'a' with ctrl modifier" {
    const e = tryInterpret(.{ .ground = 0x01 }).?;
    try std.testing.expectEqual(@as(u21, 'a'), e.key_press.codepoint);
    try std.testing.expect(e.key_press.modifiers.ctrl);
}

test "xterm: bare CR maps to Enter" {
    const e = tryInterpret(.{ .ground = 0x0d }).?;
    try std.testing.expectEqual(Event.key.enter, e.key_press.codepoint);
}

test "xterm: CSI A -> up arrow" {
    const csi: Csi.Sequence = .{ .final = 'A' };
    const e = tryInterpret(.{ .csi = csi }).?;
    try std.testing.expectEqual(Event.key.up, e.key_press.codepoint);
}

test "xterm: CSI 1;5A -> Ctrl+up" {
    var csi: Csi.Sequence = .{ .final = 'A' };
    csi.params[0] = 1;
    csi.params[1] = 5;
    csi.params_count = 2;
    const e = tryInterpret(.{ .csi = csi }).?;
    try std.testing.expectEqual(Event.key.up, e.key_press.codepoint);
    try std.testing.expect(e.key_press.modifiers.ctrl);
}

test "xterm: CSI 15~ -> F5" {
    var csi: Csi.Sequence = .{ .final = '~' };
    csi.params[0] = 15;
    csi.params_count = 1;
    const e = tryInterpret(.{ .csi = csi }).?;
    try std.testing.expectEqual(Event.key.f5, e.key_press.codepoint);
}

test "xterm: progressive-enhancement 'u' final NOT claimed (CSI 13;2u)" {
    var csi: Csi.Sequence = .{ .final = 'u' };
    csi.params[0] = 13;
    csi.params[1] = 2;
    csi.params_count = 2;
    try std.testing.expect(tryInterpret(.{ .csi = csi }) == null);
}

test "xterm: CSI ?u (private intermediate) NOT claimed" {
    var csi: Csi.Sequence = .{ .final = 'u' };
    csi.intermediates[0] = '?';
    csi.intermediates_count = 1;
    try std.testing.expect(tryInterpret(.{ .csi = csi }) == null);
}

test "xterm: SS3 A -> up arrow" {
    const e = tryInterpret(.{ .ss3 = .{ .final = 'A' } }).?;
    try std.testing.expectEqual(Event.key.up, e.key_press.codepoint);
}

test "xterm: bare ESC -> Escape keypress" {
    const e = tryInterpret(.bare_escape).?;
    try std.testing.expectEqual(Event.key.escape, e.key_press.codepoint);
}

test "xterm: ESC a -> Alt+a" {
    const e = tryInterpret(.{ .escape_alt = 'a' }).?;
    try std.testing.expectEqual(@as(u21, 'a'), e.key_press.codepoint);
    try std.testing.expect(e.key_press.modifiers.alt);
}

test "xterm: CSI Z -> Shift+Tab" {
    const csi: Csi.Sequence = .{ .final = 'Z' };
    const e = tryInterpret(.{ .csi = csi }).?;
    try std.testing.expectEqual(Event.key.tab, e.key_press.codepoint);
    try std.testing.expect(e.key_press.modifiers.shift);
}

test "xterm: protocol() returns a usable Protocol pointer" {
    const p = protocol();
    try std.testing.expectEqualStrings("xterm", p.name);
    const result = p.vtable.tryInterpret(p, .{ .ground = 'x' });
    try std.testing.expect(result == .event);
    try std.testing.expectEqual(@as(u21, 'x'), result.event.key_press.codepoint);
}
