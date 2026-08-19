const std = @import("std");
const compliance = @import("root.zig");

const a = std.testing.allocator;

test "compliance: @typeName and @errorName produce string values" {
    try compliance.check(a, &.{
        .{ .src = &.{"@typeName(u32).*"}, .rendered = "\"u32\".*" },
        .{ .src = &.{"@typeName(?u8).*"}, .rendered = "\"?u8\".*" },
        .{ .src = &.{"@typeName([*:0]u8).*"}, .rendered = "\"[*:0]u8\".*" },
        .{ .src = &.{"@typeName([:0]u8).*"}, .rendered = "\"[:0]u8\".*" },
        // A non-integer array sentinel renders as its value, not "?".
        .{ .src = &.{"@typeName([2:true]bool).*"}, .rendered = "\"[2:true]bool\".*" },
        .{ .src = &.{"@typeName(u32)[1]"}, .want = compliance.want(@typeName(u32)[1]) },
        .{ .src = &.{"@errorName(error.Foo).*"}, .rendered = "\"Foo\".*" },
        .{ .src = &.{"@errorName(error.Boom)[0]"}, .want = compliance.want(@errorName(error.Boom)[0]) },
    });
}

test "compliance: @backingInt and @fromBackingInt round-trip enums and packed structs" {
    try compliance.check(a, &.{
        .{ .src = &.{"blk: { const E = enum(u8) { a, b = 5 }; break :blk @backingInt(E.b); }"}, .want = compliance.want(blk: {
            const E = enum(u8) { a, b = 5 };
            break :blk @backingInt(E.b);
        }) },
        .{ .src = &.{"blk: { const E = enum(u8) { a, b = 5 }; break :blk @as(E, @fromBackingInt(5)) == E.b; }"}, .want = compliance.want(blk: {
            const E = enum(u8) { a, b = 5 };
            break :blk @as(E, @fromBackingInt(5)) == E.b;
        }) },
        .{ .src = &.{"blk: { const PS = packed struct(u8) { lo: u4, hi: u4 }; break :blk @backingInt(PS{ .lo = 1, .hi = 2 }); }"}, .want = compliance.want(blk: {
            const PS = packed struct(u8) { lo: u4, hi: u4 };
            break :blk @backingInt(PS{ .lo = 1, .hi = 2 });
        }) },
        .{ .src = &.{"blk: { const PS = packed struct(u8) { lo: u4, hi: u4 }; break :blk @as(PS, @fromBackingInt(0x21)).hi; }"}, .want = compliance.want(blk: {
            const PS = packed struct(u8) { lo: u4, hi: u4 };
            break :blk @as(PS, @fromBackingInt(0x21)).hi;
        }) },
        .{ .src = &.{"blk: { const S = struct { x: u8 }; break :blk @backingInt(S{ .x = 1 }); }"}, .reject = true },
    });
}

test "compliance: @setEvalBranchQuota and @setRuntimeSafety are accepted no-ops" {
    try compliance.check(a, &.{
        .{ .src = &.{"blk: { @setEvalBranchQuota(5000); break :blk 2 + 2; }"}, .want = compliance.want(blk: {
            @setEvalBranchQuota(5000);
            break :blk 2 + 2;
        }) },
        .{ .src = &.{"blk: { @setRuntimeSafety(false); break :blk 7; }"}, .want = compliance.want(blk: {
            @setRuntimeSafety(false);
            break :blk 7;
        }) },
    });
}

test "compliance: @compileError fails on both sides" {
    try compliance.check(a, &.{
        .{ .src = &.{"blk: { @compileError(\"boom\"); break :blk 1; }"}, .reject = true },
    });
}

test "compliance: @inComptime is true in the always-comptime REPL" {
    try compliance.check(a, &.{
        .{ .src = &.{"blk: { const F = struct { fn f() bool { return @inComptime(); } }; break :blk F.f(); }"}, .want = compliance.want(blk: {
            const F = struct {
                fn f() bool {
                    return @inComptime();
                }
            };
            break :blk F.f();
        }) },
    });
}
