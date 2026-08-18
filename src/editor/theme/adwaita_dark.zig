//! Adwaita dark theme: prompts in the GNOME Adwaita accent blue (#3584E4)
const Theme = @import("../Theme.zig");

/// Adwaita accent blue (#3584E4) at each fallback tier: truecolor, nearest
/// 256-palette entry, then 16-color blue.
const adwaita_blue: Theme.Color = .{
    .rgb = .{ 53, 132, 228 },
    .truecolor = "\x1b[38;2;53;132;228m",
    .palette256 = "\x1b[38;5;68m",
    .basic = "\x1b[34m",
};

pub const theme: Theme = .{
    .name = "adwaita-dark",
    .primary = .{ .text = ">>> ", .color = adwaita_blue },
    .continuation = .{ .text = "... ", .color = adwaita_blue },
};
