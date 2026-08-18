//! Catppuccin theme (Mocha flavor): prompts in Mauve (#CBA6F7).

const Theme = @import("../Theme.zig");

/// Mocha Mauve (#CBA6F7) at each tier: exact truecolor, nearest 256-palette
/// entry, then 16-color bright magenta.
const mocha_mauve: Theme.Color = .{
    .rgb = .{ 203, 166, 247 },
    .truecolor = "\x1b[38;2;203;166;247m",
    .palette256 = "\x1b[38;5;183m",
    .basic = "\x1b[95m",
};

pub const theme: Theme = .{
    .name = "catppuccin",
    .primary = .{ .text = ">>> ", .color = mocha_mauve },
    .continuation = .{ .text = "... ", .color = mocha_mauve },
};
