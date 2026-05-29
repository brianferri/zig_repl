//! Stateless byte-stream classifier. ECMA-48 escape framing only:
//!
//!   non-ESC byte               -> Token.ground
//!   ESC alone (no follow-on)   -> Token.bare_escape
//!   ESC <printable c>          -> Token.escape_alt(c)   (xterm Alt+c)
//!   ESC <introducer> ...       -> dispatched to a registered Standard
//!
//! Each per-standard wire form (CSI, SS3, OSC, DCS, ...) lives in
//! its own file under `standard/`. This file is the registry +
//! dispatch shell -- adding a new standard means dropping a sibling
//! file and appending one entry to `standards`.
//!
//! Stateless across calls: each `parse` invocation gets the whole
//! pending buffer and decides. The caller buffers more bytes on
//! incomplete (`null token`, `consumed = 0`) and re-calls.

const std = @import("std");
const assert = std.debug.assert;

const Standard = @import("Standard.zig");

const Csi = @import("standard/Csi.zig");
const Ss2 = @import("standard/Ss2.zig");
const Ss3 = @import("standard/Ss3.zig");
const Osc = @import("standard/Osc.zig");
const St = @import("standard/St.zig");
const StringCommand = @import("standard/StringCommand.zig");

pub const Result = Standard.Result;

const standards = [_]Standard{
    Csi.standard,
    Ss2.standard,
    Ss3.standard,
    Osc.standard,
    St.standard,
    StringCommand.dcs,
    StringCommand.sos,
    StringCommand.pm,
    StringCommand.apc,
};

pub fn parse(input: []const u8) Result {
    assert(input.len > 0);

    if (input[0] != 0x1b) {
        return .{ .token = .{ .ground = input[0] }, .consumed = 1 };
    }
    // Lone ESC with no follow-on yet: surface bare_escape so an
    // Esc keypress without follow-on bytes doesn't block forever.
    if (input.len == 1) {
        return .{ .token = .bare_escape, .consumed = 1 };
    }
    for (standards) |s| {
        if (s.introducer == input[1]) return s.parse(input);
    }
    // ESC <printable> -- xterm Alt+<c> encoding. The skip range
    // excludes the introducer bytes already dispatched above.
    if (input[1] >= 0x20 and input[1] <= 0x7E) {
        return .{ .token = .{ .escape_alt = input[1] }, .consumed = 2 };
    }
    // Anything else after ESC: swallow as bare_escape so the
    // editor keeps making progress instead of hanging on malformed
    // wire input.
    return .{ .token = .bare_escape, .consumed = 1 };
}

test "parse: bare ground byte" {
    const r = parse("a");
    try std.testing.expect(r.token.? == .ground);
    try std.testing.expectEqual(@as(u8, 'a'), r.token.?.ground);
    try std.testing.expectEqual(@as(u32, 1), r.consumed);
}

test "parse: bare ESC alone" {
    const r = parse("\x1b");
    try std.testing.expect(r.token.? == .bare_escape);
    try std.testing.expectEqual(@as(u32, 1), r.consumed);
}

test "parse: escape_alt encoding ESC a" {
    const r = parse("\x1ba");
    try std.testing.expect(r.token.? == .escape_alt);
    try std.testing.expectEqual(@as(u8, 'a'), r.token.?.escape_alt);
}

test "parse: CSI A (legacy arrow up)" {
    const r = parse("\x1b[A");
    try std.testing.expect(r.token.? == .csi);
    try std.testing.expectEqual(@as(u8, 'A'), r.token.?.csi.final);
    try std.testing.expectEqual(@as(u32, 0), r.token.?.csi.params_count);
}

test "parse: CSI 1;2A (modified arrow)" {
    const r = parse("\x1b[1;2A");
    try std.testing.expect(r.token.? == .csi);
    const csi = r.token.?.csi;
    try std.testing.expectEqual(@as(u8, 'A'), csi.final);
    try std.testing.expectEqual(@as(u32, 2), csi.params_count);
    try std.testing.expectEqual(@as(u32, 1), csi.params[0]);
    try std.testing.expectEqual(@as(u32, 2), csi.params[1]);
}

test "parse: CSI 13;2u (progressive Shift+Enter)" {
    const r = parse("\x1b[13;2u");
    try std.testing.expect(r.token.? == .csi);
    const csi = r.token.?.csi;
    try std.testing.expectEqual(@as(u8, 'u'), csi.final);
    try std.testing.expectEqual(@as(u32, 13), csi.params[0]);
    try std.testing.expectEqual(@as(u32, 2), csi.params[1]);
}

test "parse: CSI with sub-parameter 1:5u" {
    const r = parse("\x1b[1:5u");
    try std.testing.expect(r.token.? == .csi);
    const csi = r.token.?.csi;
    try std.testing.expectEqual(@as(u32, 1), csi.params_count);
    try std.testing.expectEqual(@as(u32, 1), csi.params[0]);
    try std.testing.expectEqual(@as(u32, 1), csi.subparams_count[0]);
    try std.testing.expectEqual(@as(u32, 5), csi.subparams[0][0]);
}

test "parse: CSI ?u (private intermediate)" {
    const r = parse("\x1b[?u");
    try std.testing.expect(r.token.? == .csi);
    const csi = r.token.?.csi;
    try std.testing.expectEqual(@as(u8, 'u'), csi.final);
    try std.testing.expect(csi.hasIntermediate('?'));
}

test "parse: SS3 A (legacy F1-key family arrow)" {
    const r = parse("\x1bOA");
    try std.testing.expect(r.token.? == .ss3);
    try std.testing.expectEqual(@as(u8, 'A'), r.token.?.ss3.final);
}

test "parse: incomplete CSI returns null token" {
    const r = parse("\x1b[1;");
    try std.testing.expect(r.token == null);
    try std.testing.expectEqual(@as(u32, 0), r.consumed);
}

test "parse: OSC terminated by BEL" {
    const r = parse("\x1b]0;title\x07");
    try std.testing.expect(r.token.? == .osc);
    try std.testing.expectEqualStrings("0;title", r.token.?.osc);
}

test "parse: OSC terminated by ST (ESC \\)" {
    const r = parse("\x1b]52;c;abc\x1b\\");
    try std.testing.expect(r.token.? == .osc);
    try std.testing.expectEqualStrings("52;c;abc", r.token.?.osc);
}

test "parse: missing primary param defaults to 0 (CSI ;2u)" {
    const r = parse("\x1b[;2u");
    try std.testing.expect(r.token.? == .csi);
    const csi = r.token.?.csi;
    try std.testing.expectEqual(@as(u32, 2), csi.params_count);
    try std.testing.expectEqual(@as(u32, 0), csi.params[0]);
    try std.testing.expectEqual(@as(u32, 2), csi.params[1]);
}

test "parse: DCS payload consumed without emitting a token" {
    const r = parse("\x1bP1$r\x1b\\");
    try std.testing.expect(r.token == null);
    try std.testing.expect(r.consumed > 0);
}

test "parse: APC payload consumed without emitting a token" {
    const r = parse("\x1b_Gi=1\x1b\\");
    try std.testing.expect(r.token == null);
    try std.testing.expect(r.consumed > 0);
}
