//! Prompt-theme interface. A `Theme` is a *preference*; the terminal's
//! `Color.ColorLevel` (a capability) decides how much color renders.
//!
//! `Prompt` keeps visible `width` separate from emitted bytes: cursor positioning counts `width`, not the
//! zero-width SGR escapes, so a colored prompt should not desync the cursor.

const std = @import("std");
const assert = std.debug.assert;

const ColorLevel = @import("device").Color.ColorLevel;

const Theme = @This();

name: []const u8,
primary: Prompt,
continuation: Prompt,
palette: Palette,

/// SGR reset of the foreground only, unlike the blanket `\x1b[0m`.
const reset: []const u8 = "\x1b[39m";

/// A 24-bit color for a non-terminal frontend; the terminal renders via `Color`'s SGR sequences.
pub const Rgb = struct { r: u8, g: u8, b: u8 };

/// The scheme's surface colors for a graphical frontend; the terminal draws only
/// the prompt. Role names follow the Catppuccin convention, darkest to lightest.
pub const Palette = struct {
    base: Rgb,
    mantle: Rgb,
    crust: Rgb,
    surface0: Rgb,
    surface1: Rgb,
    text: Rgb,
    subtext: Rgb,
    overlay: Rgb,
};

/// A foreground color: RGB plus one SGR sequence per capability tier.
pub const Color = struct {
    rgb: Rgb,
    truecolor: []const u8,
    palette256: []const u8,
    basic: []const u8,

    /// The SGR sequence for `level`, or "" when uncolored. A colored level
    /// must resolve non-empty: a blank tier is a construction bug, not "no color".
    pub fn escape(color: Color, level: ColorLevel) []const u8 {
        const sequence = switch (level) {
            .none => "",
            .basic => color.basic,
            .palette256 => color.palette256,
            .truecolor => color.truecolor,
        };
        if (level != .none) assert(sequence.len != 0);
        return sequence;
    }

    /// Write `text` wrapped in this color at `level`. At `.none` this is
    /// exactly `text`, so piped output carries no escapes.
    pub fn write(color: Color, writer: *std.Io.Writer, text: []const u8, level: ColorLevel) !void {
        assert(@intFromPtr(writer) != 0);
        const sequence = color.escape(level);
        if (sequence.len != 0) try writer.writeAll(sequence);
        try writer.writeAll(text);
        if (sequence.len != 0) try writer.writeAll(reset);
    }
};

pub const Prompt = struct {
    text: []const u8,
    color: Color,

    /// The editor counts one byte as one column (no wide-character
    /// handling), so prompt text must be single-width.
    pub fn width(prompt: Prompt) usize {
        assert(prompt.text.len != 0);
        return prompt.text.len;
    }

    /// Emit the prompt's text in its color at `level`.
    pub fn write(prompt: Prompt, writer: *std.Io.Writer, level: ColorLevel) !void {
        assert(prompt.text.len != 0);
        try prompt.color.write(writer, prompt.text, level);
    }
};

const testing = std.testing;

const test_color: Color = .{
    .rgb = .{ .r = 1, .g = 2, .b = 3 },
    .truecolor = "\x1b[38;2;1;2;3m",
    .palette256 = "\x1b[38;5;9m",
    .basic = "\x1b[33m",
};

test "Prompt.width counts visible columns, not color bytes" {
    const prompt: Prompt = .{ .text = ">>> ", .color = test_color };
    try testing.expectEqual(@as(usize, 4), prompt.width());
}

test "Prompt.write emits bare text at none, wraps with the tier's SGR otherwise" {
    var sink: std.Io.Writer.Allocating = .init(testing.allocator);
    defer sink.deinit();
    const prompt: Prompt = .{ .text = ">>> ", .color = test_color };

    try prompt.write(&sink.writer, .none);
    try testing.expectEqualStrings(">>> ", sink.writer.buffered());

    sink.clearRetainingCapacity();
    try prompt.write(&sink.writer, .truecolor);
    try testing.expectEqualStrings("\x1b[38;2;1;2;3m>>> \x1b[39m", sink.writer.buffered());

    sink.clearRetainingCapacity();
    try prompt.write(&sink.writer, .palette256);
    try testing.expectEqualStrings("\x1b[38;5;9m>>> \x1b[39m", sink.writer.buffered());

    sink.clearRetainingCapacity();
    try prompt.write(&sink.writer, .basic);
    try testing.expectEqualStrings("\x1b[33m>>> \x1b[39m", sink.writer.buffered());
}
