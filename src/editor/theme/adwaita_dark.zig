//! Adwaita dark theme: prompts in the GNOME Adwaita accent blue (#3584E4)
const Theme = @import("../Theme.zig");

const adwaita_blue: Theme.Color = .{
    .rgb = .{ .r = 53, .g = 132, .b = 228 },
    .truecolor = "\x1b[38;2;53;132;228m",
    .palette256 = "\x1b[38;5;68m",
    .basic = "\x1b[34m",
};

pub const theme: Theme = .{
    .name = "adwaita-dark",
    .primary = .{ .text = ">>> ", .color = adwaita_blue },
    .continuation = .{ .text = "... ", .color = adwaita_blue },
    .palette = .{
        .base = .{ .r = 36, .g = 36, .b = 36 },
        .mantle = .{ .r = 30, .g = 30, .b = 30 },
        .crust = .{ .r = 24, .g = 24, .b = 24 },
        .surface0 = .{ .r = 48, .g = 48, .b = 48 },
        .surface1 = .{ .r = 58, .g = 58, .b = 58 },
        .text = .{ .r = 246, .g = 245, .b = 244 },
        .subtext = .{ .r = 192, .g = 191, .b = 188 },
        .overlay = .{ .r = 119, .g = 118, .b = 123 },
    },
};
