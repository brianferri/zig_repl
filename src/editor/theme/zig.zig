//! The Zig brand theme: prompts in Zig orange (#F7A41D).

const Theme = @import("../Theme.zig");

const zig_orange: Theme.Color = .{
    .rgb = .{ .r = 247, .g = 164, .b = 29 },
    .truecolor = "\x1b[38;2;247;164;29m",
    .palette256 = "\x1b[38;5;214m",
    .basic = "\x1b[33m",
};

pub const theme: Theme = .{
    .name = "zig",
    .primary = .{ .text = ">>> ", .color = zig_orange },
    .continuation = .{ .text = "... ", .color = zig_orange },
    .palette = .{
        .base = .{ .r = 27, .g = 26, .b = 23 },
        .mantle = .{ .r = 21, .g = 20, .b = 18 },
        .crust = .{ .r = 16, .g = 15, .b = 13 },
        .surface0 = .{ .r = 42, .g = 40, .b = 37 },
        .surface1 = .{ .r = 59, .g = 56, .b = 51 },
        .text = .{ .r = 234, .g = 230, .b = 223 },
        .subtext = .{ .r = 182, .g = 176, .b = 166 },
        .overlay = .{ .r = 116, .g = 111, .b = 102 },
    },
};
