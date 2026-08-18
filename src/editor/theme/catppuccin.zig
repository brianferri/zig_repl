//! Catppuccin theme (Mocha flavor): prompts in Mauve (#CBA6F7).

const Theme = @import("../Theme.zig");

/// Mocha Mauve (#CBA6F7) at each tier: exact truecolor, nearest 256-palette
/// entry, then 16-color bright magenta.
const mocha_mauve: Theme.Color = .{
    .rgb = .{ .r = 203, .g = 166, .b = 247 },
    .truecolor = "\x1b[38;2;203;166;247m",
    .palette256 = "\x1b[38;5;183m",
    .basic = "\x1b[95m",
};

pub const theme: Theme = .{
    .name = "catppuccin",
    .primary = .{ .text = ">>> ", .color = mocha_mauve },
    .continuation = .{ .text = "... ", .color = mocha_mauve },
    .palette = .{
        .base = .{ .r = 30, .g = 30, .b = 46 },
        .mantle = .{ .r = 24, .g = 24, .b = 37 },
        .crust = .{ .r = 17, .g = 17, .b = 27 },
        .surface0 = .{ .r = 49, .g = 50, .b = 68 },
        .surface1 = .{ .r = 69, .g = 71, .b = 90 },
        .text = .{ .r = 205, .g = 214, .b = 244 },
        .subtext = .{ .r = 166, .g = 173, .b = 200 },
        .overlay = .{ .r = 108, .g = 112, .b = 134 },
    },
};
