const std = @import("std");
const compliance = @import("root.zig");

const a = std.testing.allocator;

// A `u8` array/slice renders as a quoted, escaped string rather than a byte list.
// The REPL interns each byte as its own `u8` slot (no `.bytes` aggregate storage),
// so this keys on the element type and byte-concreteness -- a deliberate
// divergence from `{any}`, hence `.rendered`. Mirrors src/print_value.zig
// printAggregate's `.bytes` arm, including the `.*` on a by-value array and the
// stripped trailing sentinel.
test "compliance: u8 arrays and slices render as strings" {
    try compliance.check(a, .{
        // String literal: a `*const [N:0]u8`, the pointer/ref form (no `.*`).
        .{ .src = &.{"\"hi\""}, .rendered = "\"hi\"" },
        .{ .src = &.{"\"\""}, .rendered = "\"\"" },
        // Escapes and an embedded NUL survive; only the trailing sentinel is dropped.
        .{ .src = &.{"\"a\\tb\\nc\""}, .rendered = "\"a\\tb\\nc\"" },
        .{ .src = &.{"\"\\xff\\x00mid\""}, .rendered = "\"\\xff\\x00mid\"" },
        // The by-value array (deref of the literal) carries the `.*` suffix.
        .{ .src = &.{"\"hi\".*"}, .rendered = "\"hi\".*" },
        .{ .src = &.{ "const arr = [_]u8{ 104, 105 };", "arr" }, .rendered = "\"hi\".*" },
        // A `[]const u8` / `[:0]const u8` slice shows its bytes over `len`.
        .{ .src = &.{ "const s: []const u8 = \"hello\";", "s" }, .rendered = "\"hello\"" },
        .{ .src = &.{ "const z: [:0]const u8 = \"zt\";", "z" }, .rendered = "\"zt\"" },
        .{ .src = &.{"@as([]const u8, \"abc\")"}, .rendered = "\"abc\"" },
        // A non-`u8` array is untouched: still a positional list, so `.want` holds.
        .{ .src = &.{ "const n = [_]u32{ 1, 2 };", "n" }, .want = [_]u32{ 1, 2 } },
        // A single byte is a scalar `u8`, not an array -- an integer, not a string.
        .{ .src = &.{"@as(u8, 65)"}, .want = @as(u8, 65) },
    });
}

// Floats render at full decimal precision with the trailing `.0` restored, a
// deliberate divergence from `{any}` (which drops the decimal and switches to
// scientific for large magnitudes), hence `.rendered`. Large magnitudes expand
// to hundreds/thousands of digits: the f128 case exceeds any f64-sized buffer,
// so full precision here means rendering through `std.fmt.float.render` directly
// rather than the f64-capped `{d}` path.
test "compliance: floats render full-precision decimal" {
    try compliance.check(a, .{
        .{ .src = &.{"@as(f64, 4.0)"}, .rendered = "4.0" },
        .{ .src = &.{"@as(f32, 1.5)"}, .rendered = "1.5" },
        // A magnitude whose decimal form overruns any small fixed buffer.
        .{ .src = &.{"1e130"}, .rendered = "1" ++ @as([130]u8, @splat('0')) ++ ".0" },
        // f128 keeps native precision instead of degrading to the f64-capped form.
        .{ .src = &.{"@as(f128, 1e300)"}, .rendered = "1" ++ @as([300]u8, @splat('0')) ++ ".0" },
    });
}
