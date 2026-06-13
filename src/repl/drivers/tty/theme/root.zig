//! Prompt-theme registry. Each theme lives in its own `theme/<name>.zig`;
//! adding one is a new file plus a one-line entry here.

const std = @import("std");
const assert = std.debug.assert;

pub const Theme = @import("../Theme.zig");
const ColorLevel = @import("device").Color.ColorLevel;

/// Every registered theme.
pub const themes = [_]*const Theme{
    &@import("zig.zig").theme,
    &@import("adwaita_dark.zig").theme,
    &@import("catppuccin.zig").theme,
};

/// The theme used when none is chosen.
pub const default = themes[0];

/// Write every registered theme name to `w`, colored to `level` and
/// comma-separated. The caller supplies any surrounding label and newline.
pub fn writeList(w: *std.Io.Writer, level: ColorLevel) !void {
    for (themes, 0..) |theme, i| {
        if (i != 0) try w.writeAll(", ");
        try theme.primary.color.write(w, theme.name, level);
    }
}

/// Resolve a registered theme by name, or null if there is none.
pub fn byName(name: []const u8) ?*const Theme {
    assert(name.len != 0);
    for (themes) |theme| {
        if (std.mem.eql(u8, theme.name, name)) return theme;
    }
    return null;
}

const testing = std.testing;

test "byName resolves every registered theme and rejects an unknown one" {
    for (themes) |registered| {
        try testing.expectEqual(registered, byName(registered.name).?);
    }
    try testing.expectEqual(@as(?*const Theme, null), byName("nope"));
}
