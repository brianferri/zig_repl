//! End-to-end test suite for the `terminal/` subsystem. Per-file
//! tests cover one module; this file composes them through the
//! Parser -> Protocol stack so behaviour drifts surface as
//! integration failures, not just unit-level breakage.

const std = @import("std");
const testing = std.testing;

const Event = @import("Event.zig");
const Parser = @import("Parser.zig");
const Protocol = @import("Protocol.zig");


const Kitty = @import("protocol/Kitty.zig");
const Xterm = @import("protocol/Xterm.zig");
const ModifyOtherKeys = @import("protocol/ModifyOtherKeys.zig");
const BracketedPaste = @import("protocol/BracketedPaste.zig");

/// Dispatch the same way `Terminal.parsePending` does: walk the
/// protocol list in priority order; return the first event a
/// protocol surfaces. `null` means no event (either incomplete
/// input or no protocol claimed it).
fn dispatch(bytes: []const u8, protocols: []const *Protocol) ?Event.Event {
    var remaining = bytes;
    while (remaining.len > 0) {
        const r = Parser.parse(remaining);
        if (r.token == null) return null;
        for (protocols) |p| {
            switch (Protocol.tryInterpret(p, r.token.?)) {
                .not_mine => continue,
                .consumed => break,
                .event => |e| return e,
            }
        }
        remaining = remaining[r.consumed..];
    }
    return null;
}

const kitty_first = [_]*Protocol{
    BracketedPaste.protocol(),
    Kitty.protocol(),
    ModifyOtherKeys.protocol(),
    Xterm.protocol(),
};

const xterm_only = [_]*Protocol{Xterm.protocol()};

test "bare CSI A is modifier-less arrow up" {
    const e = dispatch("\x1b[A", &xterm_only).?;
    try testing.expect(e == .key_press);
    try testing.expectEqual(Event.key.up, e.key_press.codepoint);
    try testing.expect(!e.key_press.modifiers.any());
}

test "kitty CSI 13;2u decodes as Shift+Enter" {
    const e = dispatch("\x1b[13;2u", &kitty_first).?;
    try testing.expect(e == .key_press);
    try testing.expectEqual(Event.key.enter, e.key_press.codepoint);
    try testing.expect(e.key_press.modifiers.shift);
    try testing.expect(!e.key_press.modifiers.ctrl);
    try testing.expect(!e.key_press.modifiers.alt);
}

test "missing primary defaults to 0 in CSI ;2u" {
    const r = Parser.parse("\x1b[;2u");
    try testing.expect(r.token.? == .csi);
    const csi = r.token.?.csi;
    try testing.expectEqual(@as(u32, 2), csi.params_count);
    try testing.expectEqual(@as(u32, 0), csi.params[0]);
    try testing.expectEqual(@as(u32, 2), csi.params[1]);
}

test "trailing separator CSI 1;A reports 1 param not 2" {
    const r = Parser.parse("\x1b[1;A");
    try testing.expect(r.token.? == .csi);
    try testing.expectEqual(@as(u32, 1), r.token.?.csi.params_count);
    try testing.expectEqual(@as(u32, 1), r.token.?.csi.params[0]);
}

test "CSI 1:5u sub-param attaches to slot 0" {
    const r = Parser.parse("\x1b[1:5u");
    try testing.expect(r.token.? == .csi);
    const csi = r.token.?.csi;
    try testing.expectEqual(@as(u32, 1), csi.params_count);
    try testing.expectEqual(@as(u32, 1), csi.subparams_count[0]);
    try testing.expectEqual(@as(u32, 5), csi.subparams[0][0]);
}

test "xterm CSI A still dispatches when Kitty is also registered" {
    const e = dispatch("\x1b[A", &kitty_first).?;
    try testing.expect(e == .key_press);
    try testing.expectEqual(Event.key.up, e.key_press.codepoint);
}

test "ESC[1;5D is Ctrl+Left via Xterm even with Kitty registered" {
    // Kitty only claims `u`-final sequences; anything else falls
    // through to ModifyOtherKeys / Xterm.
    const e = dispatch("\x1b[1;5D", &kitty_first).?;
    try testing.expect(e == .key_press);
    try testing.expectEqual(Event.key.left, e.key_press.codepoint);
    try testing.expect(e.key_press.modifiers.ctrl);
}

test "SS3 arrow up dispatches via Xterm" {
    const e = dispatch("\x1bOA", &xterm_only).?;
    try testing.expect(e == .key_press);
    try testing.expectEqual(Event.key.up, e.key_press.codepoint);
}

test "bracketed paste of 'hi' emits one paste event" {
    BracketedPaste.instance = .{};
    const protocols = [_]*Protocol{ BracketedPaste.protocol(), Xterm.protocol() };
    const e = dispatch("\x1b[200~hi\x1b[201~", &protocols).?;
    try testing.expect(e == .paste);
    try testing.expectEqualStrings("hi", e.paste);
}

test "pasted CSI sequence survives as literal bytes" {
    BracketedPaste.instance = .{};
    const protocols = [_]*Protocol{ BracketedPaste.protocol(), Xterm.protocol() };
    const e = dispatch("\x1b[200~\x1b[1;5A\x1b[201~", &protocols).?;
    try testing.expect(e == .paste);
    try testing.expectEqualStrings("\x1b[1;5A", e.paste);
}

test "ground byte 0x01 is Ctrl+A" {
    const e = dispatch("\x01", &xterm_only).?;
    try testing.expect(e == .key_press);
    try testing.expectEqual(@as(u21, 'a'), e.key_press.codepoint);
    try testing.expect(e.key_press.modifiers.ctrl);
}

test "CR maps to Enter without modifiers" {
    const e = dispatch("\r", &xterm_only).?;
    try testing.expect(e == .key_press);
    try testing.expectEqual(Event.key.enter, e.key_press.codepoint);
    try testing.expect(!e.key_press.modifiers.ctrl);
}

test "LF maps to Enter without modifiers" {
    const e = dispatch("\n", &xterm_only).?;
    try testing.expect(e == .key_press);
    try testing.expectEqual(Event.key.enter, e.key_press.codepoint);
    try testing.expect(!e.key_press.modifiers.ctrl);
}

test "CSI Z is Shift+Tab" {
    const e = dispatch("\x1b[Z", &xterm_only).?;
    try testing.expect(e == .key_press);
    try testing.expectEqual(Event.key.tab, e.key_press.codepoint);
    try testing.expect(e.key_press.modifiers.shift);
}

test "bare ESC byte surfaces as Escape keypress" {
    const e = dispatch("\x1b", &xterm_only).?;
    try testing.expect(e == .key_press);
    try testing.expectEqual(Event.key.escape, e.key_press.codepoint);
}

test "incomplete CSI returns null token and consumed 0" {
    const r = Parser.parse("\x1b[1;");
    try testing.expect(r.token == null);
    try testing.expectEqual(@as(u32, 0), r.consumed);
}

test "Kitty event_type 3 surfaces as key_release" {
    const e = dispatch("\x1b[97;1:3u", &kitty_first).?;
    try testing.expect(e == .key_release);
    try testing.expectEqual(@as(u21, 'a'), e.key_release.codepoint);
}

test "modifyOtherKeys CSI 27;2;13~ is Shift+Enter" {
    const protocols = [_]*Protocol{
        ModifyOtherKeys.protocol(),
        Xterm.protocol(),
    };
    const e = dispatch("\x1b[27;2;13~", &protocols).?;
    try testing.expect(e == .key_press);
    try testing.expectEqual(Event.key.enter, e.key_press.codepoint);
    try testing.expect(e.key_press.modifiers.shift);
}

test "CSI 15~ is F5" {
    const e = dispatch("\x1b[15~", &xterm_only).?;
    try testing.expect(e == .key_press);
    try testing.expectEqual(Event.key.f5, e.key_press.codepoint);
}

