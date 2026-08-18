//! The Zig brand theme: prompts in Zig orange (#F7A41D).

const Theme = @import("../Theme.zig");

/// Zig brand orange (#F7A41D) at each capability tier: exact truecolor,
/// nearest 256-palette entry, then plain yellow.
const zig_orange: Theme.Color = .{
    .rgb = .{ 247, 164, 29 },
    .truecolor = "\x1b[38;2;247;164;29m",
    .palette256 = "\x1b[38;5;214m",
    .basic = "\x1b[33m",
};

pub const theme: Theme = .{
    .name = "zig",
    .primary = .{ .text = ">>> ", .color = zig_orange },
    .continuation = .{ .text = "... ", .color = zig_orange },
};
