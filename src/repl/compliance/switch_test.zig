const std = @import("std");
const compliance = @import("root.zig");

const a = std.testing.allocator;

test "compliance: switch dispatch, ranges, and multi-case items" {
    try compliance.check(a, .{
        .{ .src = &.{"switch (1) { 0 => 100, 1 => 200, else => 999 }"}, .want = switch (1) {
            0 => 100,
            1 => 200,
            else => 999,
        } },
        .{ .src = &.{"switch (5) { 0 => 100, else => 999 }"}, .want = switch (5) {
            0 => 100,
            else => 999,
        } },
        .{ .src = &.{"switch (@as(u8, 2)) { 0 => 10, 1 => 20, 2 => 30, else => 0 }"}, .want = switch (@as(u8, 2)) {
            0 => 10,
            1 => 20,
            2 => 30,
            else => 0,
        } },
        .{ .src = &.{"switch (3) { 0, 1, 2 => 100, 3, 4 => 200, else => 0 }"}, .want = switch (3) {
            0, 1, 2 => 100,
            3, 4 => 200,
            else => 0,
        } },
        .{ .src = &.{"switch (0) { 0...2 => 100, 3...5 => 200, else => 999 }"}, .want = switch (0) {
            0...2 => 100,
            3...5 => 200,
            else => 999,
        } },
        .{ .src = &.{"switch (5) { 0...2 => 100, 3...5 => 200, else => 999 }"}, .want = switch (5) {
            0...2 => 100,
            3...5 => 200,
            else => 999,
        } },
        .{ .src = &.{"switch (7) { 0...2 => 100, 3...5 => 200, else => 999 }"}, .want = switch (7) {
            0...2 => 100,
            3...5 => 200,
            else => 999,
        } },
    });
}

test "compliance: catch then switch on the captured error name" {
    try compliance.check(a, .{
        .{
            .src = &.{ "const E = error{Bad, Worse};", "const x: E!u32 = error.Bad;", "x catch |e| switch (e) { error.Bad => 1, error.Worse => 2 }" },
            .want = blk: {
                const E = error{ Bad, Worse };
                const x: E!u32 = error.Bad;
                break :blk x catch |e| switch (e) {
                    error.Bad => 1,
                    error.Worse => 2,
                };
            },
        },
        .{
            .src = &.{ "const E = error{Bad, Worse};", "const x: E!u32 = error.Worse;", "x catch |e| switch (e) { error.Bad => 1, error.Worse => 2 }" },
            .want = blk: {
                const E = error{ Bad, Worse };
                const x: E!u32 = error.Worse;
                break :blk x catch |e| switch (e) {
                    error.Bad => 1,
                    error.Worse => 2,
                };
            },
        },
    });
}

test "compliance: anonymous and bound function types render" {
    try compliance.check(a, .{
        .{ .src = &.{"fn () void"}, .want = fn () void },
        .{ .src = &.{"fn (u32) u8"}, .want = fn (u32) u8 },
        .{ .src = &.{"fn (u32, i32) u8"}, .want = fn (u32, i32) u8 },
        .{ .src = &.{"fn (u32, bool) u8"}, .want = fn (u32, bool) u8 },
        .{
            .src = &.{ "const T = fn (u32) i32;", "T" },
            .want = blk: {
                const T = fn (u32) i32;
                break :blk T;
            },
        },
    });
}

test "compliance: switch operand and exhaustiveness are validated" {
    try compliance.check(a, .{
        .{ .src = &.{"blk: { const E = enum { a, b }; break :blk switch (E.b) { .a => 1, .b => 2 }; }"}, .want = blk: {
            const E = enum { a, b };
            break :blk switch (E.b) {
                .a => 1,
                .b => 2,
            };
        } },
        .{ .src = &.{"blk: { const E = enum { a, b, c }; break :blk switch (E.c) { .a => 1, else => 9 }; }"}, .want = blk: {
            const E = enum { a, b, c };
            break :blk switch (E.c) {
                .a => 1,
                else => 9,
            };
        } },
        .{
            .src = &.{"blk: { const E = enum { a, b, pub const B: @This() = .b; }; break :blk switch (E.b) { .B => 1, .a => 2 }; }"},
            .want = blk: {
                const E = enum {
                    a,
                    b,
                    pub const B: @This() = .b;
                };
                break :blk switch (E.b) {
                    .B => 1,
                    .a => 2,
                };
            },
        },
        .{ .src = &.{"blk: { break :blk switch (@as(u1, 0)) { 0 => 10, 1 => 20 }; }"}, .want = blk: {
            break :blk switch (@as(u1, 0)) {
                0 => 10,
                1 => 20,
            };
        } },
        .{ .src = &.{"blk: { break :blk switch (@as(u2, 3)) { 0...3 => 10 }; }"}, .want = blk: {
            break :blk switch (@as(u2, 3)) {
                0...3 => 10,
            };
        } },
        .{ .src = &.{"blk: { break :blk switch (true) { true => 1, false => 0 }; }"}, .want = blk: {
            break :blk switch (true) {
                true => 1,
                false => 0,
            };
        } },
        .{ .src = &.{"blk: { break :blk switch (@as(u8, 5)) { 0...4 => 1, 5...255 => 2 }; }"}, .want = blk: {
            break :blk switch (@as(u8, 5)) {
                0...4 => 1,
                5...255 => 2,
            };
        } },
        .{ .src = &.{ "const E = error{ A, B };", "const x: E!u8 = error.A;", "x catch |e| switch (e) { error.A => 1, error.B => 2 }" }, .want = blk: {
            const E = error{ A, B };
            const x: E!u8 = error.A;
            break :blk x catch |e| switch (e) {
                error.A => 1,
                error.B => 2,
            };
        } },
        .{ .src = &.{"blk: { const x: ?u8 = 1; break :blk switch (x) { else => 0 }; }"}, .reject = {} },
        .{ .src = &.{"blk: { const E = enum { a, b, c }; break :blk switch (E.a) { .a => 1, .b => 2 }; }"}, .reject = {} },
        .{ .src = &.{"blk: { const U = union(enum) { a: u32, b: u8 }; const u = U{ .a = 1 }; break :blk switch (u) { .a => |v| v }; }"}, .reject = {} },
        .{ .src = &.{"blk: { break :blk switch (@as(u8, 0)) { 0 => 10, 1 => 20 }; }"}, .reject = {} },
        .{ .src = &.{"blk: { break :blk switch (true) { true => 1 }; }"}, .reject = {} },
        .{ .src = &.{"blk: { const E = enum { a, b }; const k = E.b; break :blk switch (E.a) { k => 1 }; }"}, .reject = {} },
        .{ .src = &.{"blk: { const E = enum { a, b }; break :blk switch (E.a) { .a => 1, .a => 2, .b => 3 }; }"}, .reject = {} },
        .{ .src = &.{"blk: { const E = enum { a, b }; break :blk switch (E.a) { .a => 1, .b => 2, _ => 3 }; }"}, .reject = {} },
        .{ .src = &.{ "const E = error{ A, B };", "const x: E!u8 = error.A;", "x catch |e| switch (e) { error.A => 1 }" }, .reject = {} },
    });
    try compliance.expectDiagnostic(a, &.{"blk: { break :blk switch (@as(f32, 1)) { else => 0 }; }"}, "switch on type 'f32'");
    try compliance.expectDiagnostic(a, &.{"blk: { const E = enum { a, b }; break :blk switch (E.a) { .a => 1 }; }"}, "switch must handle all possibilities");
    try compliance.expectDiagnostic(a, &.{"blk: { const E = enum { a, b }; break :blk switch (E.a) { .a => 1, .b => 2, else => 9 }; }"}, "unreachable else prong; all cases already handled");
    try compliance.expectDiagnostic(a, &.{"blk: { break :blk switch (@as(usize, 0)) { 0 => 1 }; }"}, "switch must handle all possibilities");
    try compliance.expectDiagnostic(a, &.{"blk: { break :blk switch (@as(comptime_int, 0)) { 0 => 1 }; }"}, "else prong required when switching on type 'comptime_int'");
    try compliance.expectDiagnostic(a, &.{"blk: { const E = enum { a, b }; break :blk switch (E.a) { .a => 1, .a => 2, .b => 3 }; }"}, "duplicate switch value");
    try compliance.expectDiagnostic(a, &.{"blk: { break :blk switch (@as(u8, 0)) { 0 => 1, 0 => 2, else => 3 }; }"}, "duplicate switch value");
    try compliance.expectDiagnostic(a, &.{"blk: { break :blk switch (true) { true...false => 1 }; }"}, "ranges not allowed when switching on type 'bool'");
    try compliance.expectDiagnostic(a, &.{"blk: { const E = enum { a, b }; break :blk switch (E.a) { .a => 1, .b => 2, _ => 3 }; }"}, "'_' prong only allowed when switching on non-exhaustive enums");
}

test "compliance: switch else and scalar-prong captures bind the operand" {
    try compliance.check(a, .{
        .{ .src = &.{"blk: { const x: u32 = 48; break :blk switch (x) { 0 => @as(u32, 0), else => |m| 1 + m }; }"}, .want = blk: {
            const x: u32 = 48;
            break :blk switch (x) {
                0 => @as(u32, 0),
                else => |m| 1 + m,
            };
        } },
        .{ .src = &.{"blk: { const x: u8 = 5; break :blk switch (x) { 1, 2 => |v| @as(u8, v) * 10, else => |v| v }; }"}, .want = blk: {
            const x: u8 = 5;
            break :blk switch (x) {
                1, 2 => |v| @as(u8, v) * 10,
                else => |v| v,
            };
        } },
        .{ .src = &.{"blk: { const E = enum { a, b, c }; const v: E = .c; break :blk switch (v) { .a => @as(u8, 1), else => |e| @intFromEnum(e) }; }"}, .want = blk: {
            const E = enum { a, b, c };
            const v: E = .c;
            break :blk switch (v) {
                .a => @as(u8, 1),
                else => |e| @backingInt(e),
            };
        } },
    });
}

test "compliance: a duplicate switch prong names its value and points at the previous one" {
    // Parity with the compiler's per-prong diagnostic: the value appears in the message and a
    // "previous value here" note anchors the first occurrence.
    try compliance.expectDiagnostic(a, &.{"blk: { const x: u8 = 3; break :blk switch (x) { 3 => @as(u8, 1), 3 => 2, else => 0 }; }"}, "duplicate switch value '3'");
    try compliance.expectDiagnostic(a, &.{"blk: { const x: u8 = 3; break :blk switch (x) { 3 => @as(u8, 1), 3 => 2, else => 0 }; }"}, "previous value here");
    try compliance.expectDiagnostic(a, &.{"blk: { const x: u8 = 3; break :blk switch (x) { 0...5 => @as(u8, 1), 3 => 2, else => 0 }; }"}, "duplicate switch value '3'");
    try compliance.expectDiagnostic(a, &.{"blk: { const E = enum { a, b }; const x: E = .a; break :blk switch (x) { .a => @as(u8, 1), .a => 2, else => 0 }; }"}, "duplicate switch value '.a'");
    try compliance.expectDiagnostic(a, &.{"blk: { const x: anyerror = error.Foo; break :blk switch (x) { error.Foo => @as(u8, 1), error.Foo => 2, else => 0 }; }"}, "duplicate switch value 'error.Foo'");
    try compliance.expectDiagnostic(a, &.{"blk: { const x: bool = true; break :blk switch (x) { true => @as(u8, 1), true => 2, false => 3 }; }"}, "duplicate switch value 'true'");
}

test "compliance: a non-exhaustive switch names each unhandled value" {
    // Parity with the compiler: every unhandled enumeration value is listed as a note. A union's
    // tag enum is generated, so the note resolves through the owning union's field.
    try compliance.expectDiagnostic(a, &.{"blk: { const E = enum { a, b, c }; const x: E = .a; break :blk switch (x) { .a => @as(u8, 1) }; }"}, "unhandled enumeration value: 'b'");
    try compliance.expectDiagnostic(a, &.{"blk: { const E = enum { a, b, c }; const x: E = .a; break :blk switch (x) { .a => @as(u8, 1) }; }"}, "unhandled enumeration value: 'c'");
    try compliance.expectDiagnostic(a, &.{"blk: { const U = union(enum) { a: u32, b: u8 }; const u = U{ .a = 1 }; break :blk switch (u) { .a => |v| v }; }"}, "unhandled enumeration value: 'b'");
    // The '_' prong on an exhaustive enum carries the compiler's guidance note.
    try compliance.expectDiagnostic(a, &.{"blk: { const E = enum { a, b }; const x: E = .a; break :blk switch (x) { .a => @as(u8, 1), .b => 2, _ => 3 }; }"}, "consider using 'else'");
}
