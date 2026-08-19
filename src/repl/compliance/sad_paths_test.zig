const std = @import("std");
const compliance = @import("root.zig");

const a = std.testing.allocator;

test "sad paths: numeric coercion and casts are rejected" {
    try compliance.check(a, &.{
        .{ .src = &.{"blk: { break :blk @as(u8, 300); }"}, .reject = true },
        .{ .src = &.{"blk: { break :blk @as(u8, -1); }"}, .reject = true },
        .{ .src = &.{"blk: { break :blk @as(i8, 200); }"}, .reject = true },
        .{ .src = &.{"blk: { break :blk @as(u8, @intCast(@as(u16, 300))); }"}, .reject = true },
        .{ .src = &.{"blk: { break :blk @floatFromInt(true); }"}, .reject = true },
        .{ .src = &.{"blk: { break :blk @intFromFloat(@as(u8, 1)); }"}, .reject = true },
        .{ .src = &.{"blk: { break :blk @as(u8, 7) / @as(u8, 0); }"}, .reject = true },
    });
}

test "sad paths: a value in a type position is rejected" {
    try compliance.check(a, &.{
        .{ .src = &.{"blk: { const S = struct { x: 5 }; break :blk S{ .x = 1 }; }"}, .reject = true },
        .{ .src = &.{"blk: { const U = union { x: 5 }; break :blk U{ .x = 1 }; }"}, .reject = true },
        .{ .src = &.{"blk: { const x: 5 = 1; break :blk x; }"}, .reject = true },
        .{ .src = &.{"blk: { const f = struct { fn g(x: 5) void { _ = x; } }.g; f(1); break :blk 0; }"}, .reject = true },
        .{ .src = &.{"blk: { const f = struct { fn g() 5 { return 1; } }.g; break :blk f(); }"}, .reject = true },
    });
}

test "sad paths: operator type mismatches are rejected" {
    try compliance.check(a, &.{
        .{ .src = &.{"blk: { break :blk true + 1; }"}, .reject = true },
        .{ .src = &.{"blk: { break :blk void + void; }"}, .reject = true },
        .{ .src = &.{"blk: { const x: bool = 1; break :blk x; }"}, .reject = true },
    });
}

test "sad paths: const mutation and bad deref are rejected" {
    try compliance.check(a, &.{
        .{ .src = &.{"blk: { const x: u8 = 1; x = 2; break :blk x; }"}, .reject = true },
        .{ .src = &.{"blk: { var x: u8 = 1; break :blk x.*; }"}, .reject = true },
    });
}

test "sad paths: optionals and error unions are rejected" {
    try compliance.check(a, &.{
        .{ .src = &.{"blk: { const x: ?u8 = null; break :blk x.?; }"}, .reject = true },
        .{ .src = &.{"blk: { const E = error{A}; const eu: E!u8 = 1; const y: u8 = eu; break :blk y; }"}, .reject = true },
    });
}

test "sad paths: switch item type mismatch is rejected" {
    try compliance.check(a, &.{
        .{ .src = &.{"blk: { break :blk switch (@as(u8, 5)) { true => 1, else => 0 }; }"}, .reject = true },
        .{ .src = &.{"blk: { const E = enum { a, b }; break :blk switch (E.a) { 0 => 1, else => 0 }; }"}, .reject = true },
    });
}

test "sad paths: enums are rejected" {
    try compliance.check(a, &.{
        .{ .src = &.{"blk: { const E = enum { a, b }; break :blk E.z; }"}, .reject = true },
        .{ .src = &.{"blk: { break :blk @intFromEnum(@as(u8, 1)); }"}, .reject = true },
        .{ .src = &.{"blk: { const E = enum(u8) { a = 0, b = 1 }; break :blk @intFromEnum(@as(E, @enumFromInt(200))); }"}, .reject = true },
    });
}

test "sad paths: structs are rejected" {
    try compliance.check(a, &.{
        .{ .src = &.{"blk: { const S = struct { x: u8 }; const s = S{}; break :blk s.x; }"}, .reject = true },
        .{ .src = &.{"blk: { const S = struct { x: u8 }; const s = S{ .x = 1 }; break :blk s.y; }"}, .reject = true },
        .{ .src = &.{"blk: { const S = struct { x: u8 }; break :blk S.nope; }"}, .reject = true },
    });
}

test "sad paths: arrays and tuples are rejected" {
    try compliance.check(a, &.{
        .{ .src = &.{"blk: { const arr = [_]u8{ 1, 2 }; break :blk arr[5]; }"}, .reject = true },
        .{ .src = &.{"blk: { const t = .{ 1, 2 }; break :blk t[5]; }"}, .reject = true },
        .{ .src = &.{"blk: { const t: struct { u8, u8 } = .{ 1, 2, 3 }; break :blk t[0]; }"}, .reject = true },
    });
}

test "sad paths: generics and @TypeOf are rejected" {
    try compliance.check(a, &.{
        .{ .src = &.{"blk: { const S = struct { fn f(comptime T: type) T { return true; } }; break :blk S.f(u8); }"}, .reject = true },
        .{ .src = &.{"blk: { const S = struct { fn f(x: u8) u8 { return x; } }; break :blk S.f(); }"}, .reject = true },
    });
}

test "sad paths: slices, loops, and indexing are rejected" {
    try compliance.check(a, &.{
        .{ .src = &.{"blk: { const arr = [_]u8{ 1, 2, 3 }; const s = arr[1..9]; break :blk s.len; }"}, .reject = true },
        .{ .src = &.{"blk: { var s: u8 = 0; for (@as(u8, 5)) |x| s += x; break :blk s; }"}, .reject = true },
        .{ .src = &.{"blk: { const x: u8 = 5; break :blk x[0]; }"}, .reject = true },
    });
}

test "sad paths: bad builtins and calls are rejected" {
    try compliance.check(a, &.{
        .{ .src = &.{"blk: { break :blk @as(u8, 1) << 100; }"}, .reject = true },
        .{ .src = &.{"blk: { const x: u8 = 5; break :blk x(); }"}, .reject = true },
    });
    try compliance.expectDiagnostic(a, &.{"blk: { break :blk @sizeOf(); }"}, "expected 1 argument, found 0");
}

test "sad paths: @import of an unknown module is rejected" {
    try compliance.check(a, &.{
        .{ .src = &.{"@import(\"nonexistent\")"}, .reject = true },
    });
    try compliance.expectDiagnostic(a, &.{"@import(\"nonexistent\")"}, "no module named 'nonexistent'");
}
