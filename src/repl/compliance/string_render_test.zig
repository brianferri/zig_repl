const std = @import("std");
const compliance = @import("root.zig");

const a = std.testing.allocator;

// A `u8` array/slice renders as a quoted, escaped string, not a byte list -- a
// deliberate divergence from `{any}`, hence `.rendered`.
test "compliance: u8 arrays and slices render as strings" {
    try compliance.check(a, &.{
        .{ .src = &.{"\"hi\""}, .rendered = "\"hi\"" },
        .{ .src = &.{"\"\""}, .rendered = "\"\"" },
        // An embedded NUL survives; only the trailing sentinel is dropped.
        .{ .src = &.{"\"a\\tb\\nc\""}, .rendered = "\"a\\tb\\nc\"" },
        .{ .src = &.{"\"\\xff\\x00mid\""}, .rendered = "\"\\xff\\x00mid\"" },
        .{ .src = &.{"\"hi\".*"}, .rendered = "\"hi\".*" },
        .{ .src = &.{ "const arr = [_]u8{ 104, 105 };", "arr" }, .rendered = "\"hi\".*" },
        .{ .src = &.{ "const s: []const u8 = \"hello\";", "s" }, .rendered = "\"hello\"" },
        .{ .src = &.{ "const z: [:0]const u8 = \"zt\";", "z" }, .rendered = "\"zt\"" },
        .{ .src = &.{"@as([]const u8, \"abc\")"}, .rendered = "\"abc\"" },
        // A non-`u8` array is untouched: still a positional list, so `.want` holds.
        .{ .src = &.{ "const n = [_]u32{ 1, 2 };", "n" }, .want = compliance.want([_]u32{ 1, 2 }) },
        // A single byte is a scalar `u8`, not an array -- an integer, not a string.
        .{ .src = &.{"@as(u8, 65)"}, .want = compliance.want(@as(u8, 65)) },
    });
}

// Floats render through `{d}` with no trailing `.0`. `.rendered` is used because `{any}` switches to
// scientific notation for large magnitudes.
test "compliance: floats render like the compiler's value printer" {
    try compliance.check(a, &.{
        .{ .src = &.{"@as(f64, 4.0)"}, .rendered = "4" },
        .{ .src = &.{"@as(f32, 1.5)"}, .rendered = "1.5" },
        // A magnitude whose decimal form overruns any small fixed buffer.
        .{ .src = &.{"1e130"}, .rendered = "1" ++ @as([130]u8, @splat('0')) },
        .{ .src = &.{"@as(f128, 1e300)"}, .rendered = "1" ++ @as([300]u8, @splat('0')) },
    });
}
