const std = @import("std");
const compliance = @import("root.zig");

const a = std.testing.allocator;

test "compliance: @typeName and @errorName produce string values" {
    try compliance.check(a, .{
        // A `[N:0]u8` value renders as a string, not `{any}`'s byte list.
        .{ .src = &.{"@typeName(u32).*"}, .rendered = "\"u32\".*" },
        .{ .src = &.{"@typeName(?u8).*"}, .rendered = "\"?u8\".*" },
        .{ .src = &.{"@typeName([*:0]u8).*"}, .rendered = "\"[*:0]u8\".*" },
        .{ .src = &.{"@typeName([:0]u8).*"}, .rendered = "\"[:0]u8\".*" },
        // Non-integer array sentinel renders via Value.print (simple_value), not "?".
        .{ .src = &.{"@typeName([2:true]bool).*"}, .rendered = "\"[2:true]bool\".*" },
        .{ .src = &.{"@typeName(u32)[1]"}, .want = @typeName(u32)[1] },
        .{ .src = &.{"@errorName(error.Foo).*"}, .rendered = "\"Foo\".*" },
        .{ .src = &.{"@errorName(error.Boom)[0]"}, .want = @errorName(error.Boom)[0] },
    });
}

test "compliance: @setEvalBranchQuota and @setRuntimeSafety are accepted no-ops" {
    try compliance.check(a, .{
        .{ .src = &.{"blk: { @setEvalBranchQuota(5000); break :blk 2 + 2; }"}, .want = blk: {
            @setEvalBranchQuota(5000);
            break :blk 2 + 2;
        } },
        .{ .src = &.{"blk: { @setRuntimeSafety(false); break :blk 7; }"}, .want = blk: {
            @setRuntimeSafety(false);
            break :blk 7;
        } },
    });
}

test "compliance: @compileError fails on both sides" {
    try compliance.check(a, .{
        .{ .src = &.{"blk: { @compileError(\"boom\"); break :blk 1; }"}, .reject = {} },
    });
}
