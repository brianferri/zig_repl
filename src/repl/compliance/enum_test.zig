const std = @import("std");
const compliance = @import("root.zig");

const a = std.testing.allocator;

test "compliance: enum declarations, tag access, and @intFromEnum" {
    try compliance.check(a, .{
        .{
            .src = &.{"blk: { const E = enum { a, b, c }; break :blk @intFromEnum(E.a); }"},
            .want = blk: {
                const E = enum { a, b, c };
                break :blk @intFromEnum(E.a);
            },
        },
        .{
            .src = &.{"blk: { const E = enum { a, b, c }; break :blk @intFromEnum(E.c); }"},
            .want = blk: {
                const E = enum { a, b, c };
                break :blk @intFromEnum(E.c);
            },
        },
        .{
            .src = &.{"blk: { const E = enum { a, b, c }; const x = E.b; break :blk @intFromEnum(x); }"},
            .want = blk: {
                const E = enum { a, b, c };
                const x = E.b;
                break :blk @intFromEnum(x);
            },
        },
        .{
            .src = &.{"blk: { const Dir = enum { north, east, south, west }; break :blk @intFromEnum(Dir.west); }"},
            .want = blk: {
                const Dir = enum { north, east, south, west };
                break :blk @intFromEnum(Dir.west);
            },
        },
        .{
            .src = &.{"blk: { const Q = enum { a, b }; break :blk @intFromEnum(Q.z); }"},
            .reject = {},
        },
    });
}

// Member access on an enum type resolves the namespace declarations, not only the tags.
test "compliance: enum member declarations (E.decl)" {
    try compliance.check(a, .{
        .{
            .src = &.{"blk: { const E = enum(u8) { a, b, const N: u8 = 42; }; break :blk E.N; }"},
            .want = blk: {
                const E = enum(u8) {
                    a,
                    b,
                    const N: u8 = 42;
                };
                break :blk E.N;
            },
        },
        .{
            .src = &.{"@sizeOf(blk: { const E = enum(u8) { a, b, const Inner = struct { x: u16 }; }; break :blk E.Inner; })"},
            .want = @sizeOf(blk: {
                const E = enum(u8) {
                    a,
                    b,
                    const Inner = struct { x: u16 };
                };
                break :blk E.Inner;
            }),
        },
        .{ .src = &.{"blk: { const E = enum { a, b, const N = 42; }; break :blk E.missing; }"}, .reject = {} },
    });
}

test "compliance: @enumFromInt and result-typed enum literals" {
    try compliance.check(a, .{
        .{
            .src = &.{"blk: { const E = enum { a, b, c }; const e: E = @enumFromInt(1); break :blk @intFromEnum(e); }"},
            .want = blk: {
                const E = enum { a, b, c };
                const e: E = @enumFromInt(1);
                break :blk @intFromEnum(e);
            },
        },
        .{
            .src = &.{"blk: { const E = enum { a, b, c }; const e: E = .c; break :blk @intFromEnum(e); }"},
            .want = blk: {
                const E = enum { a, b, c };
                const e: E = .c;
                break :blk @intFromEnum(e);
            },
        },
        .{
            .src = &.{"blk: { const E = enum { a, b, c }; const e: E = .a; break :blk @intFromEnum(e); }"},
            .want = blk: {
                const E = enum { a, b, c };
                const e: E = .a;
                break :blk @intFromEnum(e);
            },
        },
        .{
            .src = &.{"blk: { const E = enum { a, b, c }; const e: E = @enumFromInt(9); break :blk @intFromEnum(e); }"},
            .reject = {},
        },
        .{
            .src = &.{"blk: { const E = enum { a, b, c }; const e: E = .z; break :blk @intFromEnum(e); }"},
            .reject = {},
        },
    });
}

test "compliance: enum @sizeOf / @alignOf are the integer tag type's" {
    try compliance.check(a, .{
        .{
            .src = &.{"blk: { const E = enum(u16) { a, b }; break :blk @sizeOf(E); }"},
            .want = blk: {
                const E = enum(u16) { a, b };
                break :blk @sizeOf(E);
            },
        },
        .{
            .src = &.{"blk: { const E = enum(u16) { a, b }; break :blk @alignOf(E); }"},
            .want = blk: {
                const E = enum(u16) { a, b };
                break :blk @alignOf(E);
            },
        },
        .{
            .src = &.{"blk: { const E = enum { a, b, c }; break :blk @sizeOf(E); }"},
            .want = blk: {
                const E = enum { a, b, c };
                break :blk @sizeOf(E);
            },
        },
    });
}

test "compliance: explicit enum tag types and values" {
    try compliance.check(a, .{
        .{
            .src = &.{"blk: { const E = enum(u8) { a, b, c }; break :blk @intFromEnum(E.c); }"},
            .want = blk: {
                const E = enum(u8) { a, b, c };
                break :blk @intFromEnum(E.c);
            },
        },
        .{
            .src = &.{"blk: { const E = enum(u8) { a = 5, b, c = 10 }; break :blk @intFromEnum(E.b); }"},
            .want = blk: {
                const E = enum(u8) { a = 5, b, c = 10 };
                break :blk @intFromEnum(E.b);
            },
        },
        .{
            .src = &.{"blk: { const E = enum(u8) { a = 5, b, c = 10 }; break :blk @intFromEnum(E.c); }"},
            .want = blk: {
                const E = enum(u8) { a = 5, b, c = 10 };
                break :blk @intFromEnum(E.c);
            },
        },
        .{
            .src = &.{"blk: { const E = enum(u16) { a = 300, b = 301 }; break :blk @intFromEnum(E.a); }"},
            .want = blk: {
                const E = enum(u16) { a = 300, b = 301 };
                break :blk @intFromEnum(E.a);
            },
        },
        .{
            .src = &.{"blk: { const E = enum(u8) { a = 5, b = 10 }; const e: E = @enumFromInt(10); break :blk @intFromEnum(e); }"},
            .want = blk: {
                const E = enum(u8) { a = 5, b = 10 };
                const e: E = @enumFromInt(10);
                break :blk @intFromEnum(e);
            },
        },
        .{
            .src = &.{"blk: { const E = enum(u8) { a = 5, b = 10 }; const e: E = @enumFromInt(7); break :blk @intFromEnum(e); }"},
            .reject = {},
        },
        .{
            .src = &.{"blk: { const E = enum(u8) { a = 300 }; break :blk @intFromEnum(E.a); }"},
            .reject = {},
        },
    });
}

test "compliance: @tagName of an enum value" {
    try compliance.check(a, .{
        .{
            .src = &.{"blk: { const E = enum { north, east, south }; break :blk @tagName(E.east).len; }"},
            .want = blk: {
                const E = enum { north, east, south };
                break :blk @tagName(E.east).len;
            },
        },
        .{
            .src = &.{"blk: { const E = enum { north, east, south }; const c: u8 = @tagName(E.south)[0]; break :blk c; }"},
            .want = blk: {
                const E = enum { north, east, south };
                const c: u8 = @tagName(E.south)[0];
                break :blk c;
            },
        },
        .{
            .src = &.{"blk: { const V = enum(u8) { lo = 5, hi = 10 }; const c: u8 = @tagName(V.hi)[0]; break :blk c; }"},
            .want = blk: {
                const V = enum(u8) { lo = 5, hi = 10 };
                const c: u8 = @tagName(V.hi)[0];
                break :blk c;
            },
        },
        .{
            .src = &.{"blk: { break :blk @tagName(5); }"},
            .reject = {},
        },
    });
}

test "compliance: enum equality and switch" {
    try compliance.check(a, .{
        .{
            .src = &.{"blk: { const E = enum { a, b, c }; const e = E.b; break :blk e == E.b; }"},
            .want = blk: {
                const E = enum { a, b, c };
                const e = E.b;
                break :blk e == E.b;
            },
        },
        .{
            .src = &.{"blk: { const E = enum { a, b, c }; const e = E.b; break :blk e != E.a; }"},
            .want = blk: {
                const E = enum { a, b, c };
                const e = E.b;
                break :blk e != E.a;
            },
        },
        .{
            .src = &.{"blk: { const E = enum { a, b, c }; const e = E.c; break :blk switch (e) { .a => 10, .b => 20, .c => 30 }; }"},
            .want = blk: {
                const E = enum { a, b, c };
                const e = E.c;
                break :blk switch (e) {
                    .a => 10,
                    .b => 20,
                    .c => 30,
                };
            },
        },
        .{
            .src = &.{"blk: { const E = enum { a, b, c }; const e = E.a; break :blk switch (e) { .a, .b => 1, .c => 2 }; }"},
            .want = blk: {
                const E = enum { a, b, c };
                const e = E.a;
                break :blk switch (e) {
                    .a, .b => 1,
                    .c => 2,
                };
            },
        },
        .{
            .src = &.{"blk: { const E = enum { a, b, c }; const e = E.c; break :blk switch (e) { .a => 100, else => 200 }; }"},
            .want = blk: {
                const E = enum { a, b, c };
                const e = E.c;
                break :blk switch (e) {
                    .a => 100,
                    else => 200,
                };
            },
        },
        .{
            .src = &.{"blk: { const V = enum(u8) { lo = 5, hi = 10 }; break :blk switch (V.hi) { .lo => 100, .hi => 200 }; }"},
            .want = blk: {
                const V = enum(u8) { lo = 5, hi = 10 };
                break :blk switch (V.hi) {
                    .lo => 100,
                    .hi => 200,
                };
            },
        },
        .{
            .src = &.{"blk: { const E = enum { a, b, c }; const e = E.c; break :blk switch (e) { .a => 1, .z => 2, else => 3 }; }"},
            .reject = {},
        },
    });
}
