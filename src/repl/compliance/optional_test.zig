const std = @import("std");
const compliance = @import("root.zig");

const a = std.testing.allocator;

const awkward = .{ 1, 3, 7, 33, 69, 420 };

fn U(comptime bits: u16) type {
    return @Int(.unsigned, bits);
}

test "compliance: optional values (payload, null, unwrap)" {
    try compliance.check(a, &.{
        .{ .src = &.{"@as(?i32, 5)"}, .want = compliance.want(@as(?i32, 5)) },
        .{ .src = &.{"@as(?i32, null)"}, .want = compliance.want(@as(?i32, null)) },
        .{ .src = &.{"@as(?i32, 5).?"}, .want = compliance.want(@as(?i32, 5).?) },
        .{
            .src = &.{"blk: { var x: ?i32 = 5; x = 6; break :blk x.?; }"},
            .want = compliance.want(blk: {
                var x: ?i32 = 5;
                x = 6;
                break :blk x.?;
            }),
        },
        .{ .src = &.{"@as(?i32, null).?"}, .reject = true },
        .{ .src = &.{"blk: { const x: u32 = 5; break :blk x.?; }"}, .reject = true },
    });
    try compliance.expectDiagnostic(a, &.{"blk: { const x: u32 = 5; break :blk x.?; }"}, "expected optional type, found 'u32'");
    try compliance.expectDiagnostic(a, &.{"blk: { const e: anyerror!u8 = 5; break :blk e.?; }"}, "consider using 'try', 'catch', or 'if'");
}

test "compliance: struct/union init through an optional result location" {
    try compliance.check(a, &.{
        .{
            .src = &.{"(struct { const S = struct { a: u8, b: u8 }; fn f() ?S { return .{ .a = 3, .b = 9 }; } }).f().?.b"},
            .want = compliance.want((struct {
                const S = struct { a: u8, b: u8 };
                fn f() ?S {
                    return .{ .a = 3, .b = 9 };
                }
            }).f().?.b),
        },
        .{
            .src = &.{"(struct { const U = union(enum) { x: u8, y: u16 }; fn f() ?U { return .{ .x = 7 }; } }).f().?.x"},
            .want = compliance.want((struct {
                const Un = union(enum) { x: u8, y: u16 };
                fn f() ?Un {
                    return .{ .x = 7 };
                }
            }).f().?.x),
        },
        .{
            .src = &.{"((struct { const S = struct { a: u8, b: u8 }; fn f() anyerror!S { return .{ .a = 3, .b = 9 }; } }).f() catch unreachable).b"},
            .want = compliance.want(((struct {
                const S = struct { a: u8, b: u8 };
                fn f() anyerror!S {
                    return .{ .a = 3, .b = 9 };
                }
            }).f() catch unreachable).b),
        },
        .{
            .src = &.{"((struct { const U = union(enum) { x: u8, y: u16 }; fn f() anyerror!U { return .{ .x = 7 }; } }).f() catch unreachable).x"},
            .want = compliance.want(((struct {
                const Un = union(enum) { x: u8, y: u16 };
                fn f() anyerror!Un {
                    return .{ .x = 7 };
                }
            }).f() catch unreachable).x),
        },
        .{ .src = &.{"@as(?struct { a: u8, b: u8 }, .{ .a = 3, .b = 9 }).?.b"}, .want = compliance.want(@as(?struct { a: u8, b: u8 }, .{ .a = 3, .b = 9 }).?.b) },
        .{ .src = &.{"@as(?union(enum) { x: u8, y: u16 }, .{ .x = 7 }).?.x"}, .want = compliance.want(@as(?union(enum) { x: u8, y: u16 }, .{ .x = 7 }).?.x) },
        .{ .src = &.{"(@as(anyerror!struct { a: u8 }, .{ .a = 5 }) catch unreachable).a"}, .want = compliance.want((@as(anyerror!struct { a: u8 }, .{ .a = 5 }) catch unreachable).a) },
        .{ .src = &.{"@as(?struct { a: u8 = 4 }, .{}).?.a"}, .want = compliance.want(@as(?struct { a: u8 = 4 }, .{}).?.a) },
    });
}

test "compliance: try and pointer-form catch unwrap error unions" {
    try compliance.check(a, &.{
        .{
            .src = &.{"blk: { const g = struct { fn g(x: anyerror!u8) anyerror!u8 { return (try x) + 1; } }.g; break :blk g(5) catch 0; }"},
            .want = compliance.want(blk: {
                const g = struct {
                    fn g(x: anyerror!u8) anyerror!u8 {
                        return (try x) + 1;
                    }
                }.g;
                break :blk g(5) catch 0;
            }),
        },
        .{
            .src = &.{"blk: { const g = struct { fn g(x: anyerror!u8) anyerror!u8 { return (try x) + 1; } }.g; break :blk g(error.Bad) catch 99; }"},
            .want = compliance.want(blk: {
                const g = struct {
                    fn g(x: anyerror!u8) anyerror!u8 {
                        return (try x) + 1;
                    }
                }.g;
                break :blk g(error.Bad) catch 99;
            }),
        },
        .{ .src = &.{"(@as(anyerror!struct { a: u8 }, .{ .a = 5 }) catch unreachable).a"}, .want = compliance.want((@as(anyerror!struct { a: u8 }, .{ .a = 5 }) catch unreachable).a) },
        .{
            .src = &.{"blk: { var o: ?u8 = 4; const p = &o; break :blk p.* orelse 0; }"},
            .want = compliance.want(blk: {
                var o: ?u8 = 4;
                const p = &o;
                break :blk p.* orelse 0;
            }),
        },
    });
}

test "compliance: optional null test drives if-capture and orelse" {
    try compliance.check(a, &.{
        .{
            .src = &.{"blk: { const x: ?u32 = 7; break :blk if (x) |v| v else 0; }"},
            .want = compliance.want(blk: {
                const x: ?u32 = 7;
                break :blk if (x) |v| v else 0;
            }),
        },
        .{
            .src = &.{"blk: { const x: ?u32 = null; break :blk if (x) |v| v else 42; }"},
            .want = compliance.want(blk: {
                const x: ?u32 = null;
                break :blk if (x) |v| v else 42;
            }),
        },
        .{
            .src = &.{"blk: { const x: ?u32 = null; break :blk x orelse 99; }"},
            .want = compliance.want(blk: {
                const x: ?u32 = null;
                break :blk x orelse 99;
            }),
        },
        .{
            .src = &.{"blk: { const x: ?u32 = 7; break :blk x orelse 99; }"},
            .want = compliance.want(blk: {
                const x: ?u32 = 7;
                break :blk x orelse 99;
            }),
        },
        .{ .src = &.{"blk: { const n: u32 = 5; break :blk if (n) |v| v else 0; }"}, .reject = true },
    });
}

test "compliance: optional across awkward payload widths" {
    inline for (awkward) |bits| {
        try compliance.check(a, &.{
            .{
                .src = &.{std.fmt.comptimePrint("@as(?u{d}, 1)", .{bits})},
                .want = compliance.want(@as(?U(bits), 1)),
            },
        });
    }
}
