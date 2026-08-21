const std = @import("std");
const compliance = @import("root.zig");

const a = std.testing.allocator;

// Inputs a fuzzer surfaced: each must reject cleanly.
test "adversarial: malformed and out-of-range inputs reject" {
    try compliance.check(a, &.{
        .{ .src = &.{"const x ="}, .reject = true },
        .{ .src = &.{"@"}, .reject = true },
        .{ .src = &.{"@import("}, .reject = true },
        .{ .src = &.{"\"unterminated"}, .reject = true },
        .{ .src = &.{"'"}, .reject = true },
        .{ .src = &.{"0x"}, .reject = true },
        .{ .src = &.{"1."}, .reject = true },
        .{ .src = &.{".{"}, .reject = true },
        .{ .src = &.{"fn f("}, .reject = true },
        .{ .src = &.{";"}, .reject = true },
        .{ .src = &.{"@as(u8, 999999)"}, .reject = true },
        .{ .src = &.{"@intFromEnum(0)"}, .reject = true },
        .{ .src = &.{"@field(1, 2)"}, .reject = true },
        .{ .src = &.{"@Type(.{})"}, .reject = true },
        .{ .src = &.{"@memcpy()"}, .reject = true },
    });
}

// A value in a type position (result type, field, variable, parameter, return) is rejected when that
// position is resolved, before a type method runs on the value.
test "adversarial: a value in a type position rejects" {
    try compliance.check(a, &.{
        .{ .src = &.{"@as(4, .{ .a = 3 }).a"}, .reject = true },
        .{ .src = &.{"@as(0, .{})"}, .reject = true },
        .{ .src = &.{"(struct { x: 5 }){ .x = 1 }"}, .reject = true },
        .{ .src = &.{"(union { x: 5 }){ .x = 1 }"}, .reject = true },
        .{ .src = &.{"const x: 5 = 1;"}, .reject = true },
        .{ .src = &.{"fn f(x: 5) void { _ = x; }"}, .reject = true },
        .{ .src = &.{"fn f() 5 { return 1; }"}, .reject = true },
        .{ .src = &.{"@typeInfo(3)"}, .reject = true },
        .{ .src = &.{"@typeInfo(struct { fn f() void {} }.f)"}, .reject = true },
    });
}

// Bitwise, wrapping, and saturating operators require integer operands.
test "adversarial: non-integer operands to integer-only operators reject" {
    try compliance.check(a, &.{
        .{ .src = &.{"3.5 & 3"}, .reject = true },
        .{ .src = &.{"1.0 | 2"}, .reject = true },
        .{ .src = &.{"2.5 ^ 1"}, .reject = true },
        .{ .src = &.{"true & 1.0"}, .reject = true },
        .{ .src = &.{"@as(u4, 15) *% @as(f64, @floatFromInt(7))"}, .reject = true },
        .{ .src = &.{"3.0 +% 1"}, .reject = true },
        .{ .src = &.{"2.5 -% 1"}, .reject = true },
        .{ .src = &.{"1.0 *| 2"}, .reject = true },
        .{ .src = &.{"3.5 +| 1"}, .reject = true },
    });
}

// A failed line leaves the session usable: the later line reaches its own diagnostic.
test "adversarial: a failed line does not corrupt later evaluation" {
    try compliance.check(a, &.{
        .{ .src = &.{ "const x = 1;", "const x = 2;", "const y = nonexistent;", "y + x" }, .reject = true },
        .{ .src = &.{ "fn f(n: u32) u32 { return !n + 1; }", "f(40)" }, .reject = true },
    });
}

// Extreme literals fold: comptime_int is arbitrary precision, and float overflow saturates to inf.
test "adversarial: extreme numeric literals fold" {
    try compliance.check(a, &.{
        .{ .src = &.{"0xffffffffffffffffffffffffffffffff + 1"}, .want = compliance.want(0xffffffffffffffffffffffffffffffff + 1) },
        .{ .src = &.{"1 << 1000"}, .want = compliance.want(1 << 1000) },
        .{ .src = &.{"-0.0"}, .rendered = "-0" },
        .{ .src = &.{"1e1000"}, .rendered = "inf" },
    });
}
