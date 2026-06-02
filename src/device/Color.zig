//! Terminal color capability. A `ColorLevel` is what the *terminal*
//! can display; it lives here beside the other capability knowledge
//! (keyboard protocols, negotiation) because it describes the device,
//! not a render preference. The `Terminal` resolves it at init via
//! `fromEnv`, the same place it negotiates protocol support.
//!
//! `detect` is pure -- it takes the environment strings as arguments,
//! so the tier policy is testable without an environment. `fromEnv`
//! is the thin wrapper that pulls those strings from the process
//! environment (only reachable as data, via the env map).

const std = @import("std");

/// Color capability, widest to narrowest. A non-terminal context never
/// constructs a `Terminal`, so it never leaves the `.none` default and
/// emits no escapes.
pub const ColorLevel = enum { none, basic, palette256, truecolor };

/// Tier from the environment strings. `no_color` forces `.none`;
/// otherwise `COLORTERM=truecolor|24bit` wins, then a `*256color*`
/// `TERM`, else basic 16-color.
pub fn detect(no_color: bool, colorterm: ?[]const u8, term: ?[]const u8) ColorLevel {
    if (no_color) return .none;
    if (colorterm) |c| {
        if (std.mem.eql(u8, c, "truecolor") or std.mem.eql(u8, c, "24bit")) {
            return .truecolor;
        }
    }
    if (term) |t| {
        if (std.mem.indexOf(u8, t, "256color") != null) return .palette256;
    }
    return .basic;
}

/// Resolve the level from the process environment. A present,
/// non-empty `NO_COLOR` disables color (per the no-color.org spec).
/// `Map.get` borrows, so there is nothing to free.
pub fn fromEnv(environ: *const std.process.Environ.Map) ColorLevel {
    const no_color = if (environ.get("NO_COLOR")) |v| v.len != 0 else false;
    return detect(no_color, environ.get("COLORTERM"), environ.get("TERM"));
}

const testing = std.testing;

test "detect: NO_COLOR forces none over any tier" {
    try testing.expectEqual(ColorLevel.none, detect(true, "truecolor", "xterm-256color"));
}

test "detect: tiers from COLORTERM then TERM" {
    try testing.expectEqual(ColorLevel.truecolor, detect(false, "truecolor", "xterm"));
    try testing.expectEqual(ColorLevel.truecolor, detect(false, "24bit", null));
    try testing.expectEqual(ColorLevel.palette256, detect(false, null, "xterm-256color"));
    try testing.expectEqual(ColorLevel.basic, detect(false, null, "xterm"));
    try testing.expectEqual(ColorLevel.basic, detect(false, null, null));
}
