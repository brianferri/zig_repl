const std = @import("std");
const compliance = @import("root.zig");

const a = std.testing.allocator;

test "compliance: comptime_int and comptime_float arithmetic" {
    try compliance.check(a, &.{
        .{
            .src = &.{"1 + 2 * 3"},
            .want = compliance.want(1 + 2 * 3),
        },
        .{
            .src = &.{"1000000000 * 1000"},
            .want = compliance.want(1000000000 * 1000),
        },
        .{
            .src = &.{"1.5 + 2.5"},
            .want = compliance.want(1.5 + 2.5),
        },
        .{
            .src = &.{"1 + 1.5"},
            .want = compliance.want(1 + 1.5),
        },
    });
}

test "compliance: fixed-width int arithmetic and peer resolution" {
    try compliance.check(a, &.{
        .{
            .src = &.{"@as(i32, 5) + @as(i32, 3)"},
            .want = compliance.want(@as(i32, 5) + @as(i32, 3)),
        },
        .{
            .src = &.{"@as(u8, 5) + @as(u16, 10)"},
            .want = compliance.want(@as(u8, 5) + @as(u16, 10)),
        },
        .{
            .src = &.{"@as(u8, 5) + @as(i16, 100)"},
            .want = compliance.want(@as(u8, 5) + @as(i16, 100)),
        },
        .{
            .src = &.{"@as(u16, 5) + @as(i8, 100)"},
            .want = compliance.want(@as(u16, 5) + @as(i8, 100)),
        },
    });
}

test "compliance: @divCeil rounds toward positive infinity" {
    try compliance.check(a, &.{
        .{ .src = &.{"@divCeil(7, 2)"}, .want = compliance.want(@divCeil(7, 2)) },
        .{ .src = &.{"@divCeil(@as(i32, -7), 2)"}, .want = compliance.want(@divCeil(@as(i32, -7), 2)) },
        .{ .src = &.{"@divCeil(@as(f32, 7.0), 2.0)"}, .want = compliance.want(@divCeil(@as(f32, 7.0), 2.0)) },
        .{ .src = &.{"@divCeil(@as(i32, 8), 4)"}, .want = compliance.want(@divCeil(@as(i32, 8), 4)) },
    });
}

test "compliance: float arithmetic and widening" {
    try compliance.check(a, &.{
        .{
            .src = &.{"@as(f32, 1.5) + @as(f32, 2.5)"},
            .want = compliance.want(@as(f32, 1.5) + @as(f32, 2.5)),
        },
        .{
            .src = &.{"@as(f32, 1.5) + @as(f64, 2.5)"},
            .want = compliance.want(@as(f32, 1.5) + @as(f64, 2.5)),
        },
        .{
            .src = &.{"@as(f32, 1.5) + @as(i32, 2)"},
            .want = compliance.want(@as(f32, 1.5) + @as(i32, 2)),
        },
    });
}

test "compliance: wrap, saturating, shift, and bitwise arithmetic" {
    try compliance.check(a, &.{
        .{
            .src = &.{"@as(u8, 200) +% @as(u8, 100)"},
            .want = compliance.want(@as(u8, 200) +% @as(u8, 100)),
        },
        .{
            .src = &.{"@as(u8, 200) +| @as(u8, 100)"},
            .want = compliance.want(@as(u8, 200) +| @as(u8, 100)),
        },
        .{
            .src = &.{"@as(u8, 1) << 7"},
            .want = compliance.want(@as(u8, 1) << 7),
        },
        .{
            .src = &.{"@as(u16, 1000) & @as(u16, 0xff)"},
            .want = compliance.want(@as(u16, 1000) & @as(u16, 0xff)),
        },
        .{ .src = &.{"-%@as(i8, 5)"}, .want = compliance.want(-%@as(i8, 5)) },
        // `-%` is integer-only; a float operand is rejected before the wrapping subtract.
        .{ .src = &.{"-%@as(f32, 1.0)"}, .reject = true },
    });
    try compliance.expectDiagnostic(a, &.{"-%@as(f32, 1.0)"}, "invalid operands to binary expression: 'float' and 'float'");
}

// Saturating shift `<<|` requires integer operands like `<<`, but carries no `typeof_log2_int_type`
// coercion to enforce it, so both operands are validated directly -- a float operand is rejected.
test "compliance: saturating shift requires integer operands" {
    try compliance.check(a, &.{
        .{ .src = &.{"@as(u8, 5) <<| 2"}, .want = compliance.want(@as(u8, 5) <<| 2) },
        .{ .src = &.{"@as(f32, 1.5) <<| 2"}, .reject = true, .skip = true },
        .{ .src = &.{"@as(f64, 1.5) <<| 2"}, .reject = true },
        .{ .src = &.{"@as(u8, 5) <<| @as(f32, 1.5)"}, .reject = true },
    });
}

test "compliance: vector arithmetic is lane-wise" {
    try compliance.check(a, &.{
        .{
            .src = &.{"@as(@Vector(4, i32), .{ 1, 2, 3, 4 }) + @as(@Vector(4, i32), .{ 10, 20, 30, 40 })"},
            .want = compliance.want(@as(@Vector(4, i32), .{ 1, 2, 3, 4 }) + @as(@Vector(4, i32), .{ 10, 20, 30, 40 })),
        },
        .{
            .src = &.{"@as(@Vector(4, i32), .{ 10, 20, 30, 40 }) - @as(@Vector(4, i32), .{ 1, 2, 3, 4 })"},
            .want = compliance.want(@as(@Vector(4, i32), .{ 10, 20, 30, 40 }) - @as(@Vector(4, i32), .{ 1, 2, 3, 4 })),
        },
        .{
            .src = &.{"@as(@Vector(4, i32), .{ 1, 2, 3, 4 }) * @as(@Vector(4, i32), .{ 2, 3, 4, 5 })"},
            .want = compliance.want(@as(@Vector(4, i32), .{ 1, 2, 3, 4 }) * @as(@Vector(4, i32), .{ 2, 3, 4, 5 })),
        },
        .{
            .src = &.{"@as(@Vector(4, u8), .{ 12, 10, 255, 15 }) & @as(@Vector(4, u8), .{ 10, 6, 15, 255 })"},
            .want = compliance.want(@as(@Vector(4, u8), .{ 12, 10, 255, 15 }) & @as(@Vector(4, u8), .{ 10, 6, 15, 255 })),
        },
        .{
            .src = &.{"@as(@Vector(4, u8), .{ 100, 200, 50, 25 }) ^ @as(@Vector(4, u8), .{ 1, 2, 3, 4 })"},
            .want = compliance.want(@as(@Vector(4, u8), .{ 100, 200, 50, 25 }) ^ @as(@Vector(4, u8), .{ 1, 2, 3, 4 })),
        },
        .{
            .src = &.{"@as(@Vector(4, u8), .{ 1, 2, 4, 8 }) << @as(@Vector(4, u3), .{ 1, 2, 3, 0 })"},
            .want = compliance.want(@as(@Vector(4, u8), .{ 1, 2, 4, 8 }) << @as(@Vector(4, u3), .{ 1, 2, 3, 0 })),
        },
        .{
            .src = &.{"-@as(@Vector(2, i32), .{ 1, -2 })"},
            .want = compliance.want(-@as(@Vector(2, i32), .{ 1, -2 })),
        },
    });
}

test "compliance: @min/@max fold and refine the result type" {
    try compliance.check(a, &.{
        .{
            .src = &.{"@min(3, 7)"},
            .want = compliance.want(@min(3, 7)),
        },
        .{
            .src = &.{"@max(@as(u8, 200), @as(u8, 100))"},
            .want = compliance.want(@max(@as(u8, 200), @as(u8, 100))),
        },
        .{
            .src = &.{"@min(@as(u8, 200), @as(u8, 100))"},
            .want = compliance.want(@min(@as(u8, 200), @as(u8, 100))),
        },
        .{
            .src = &.{"@max(@as(f32, 1.0), @as(f64, 2.5))"},
            .want = compliance.want(@max(@as(f32, 1.0), @as(f64, 2.5))),
        },
        .{
            .src = &.{"@max(@as(u32, 5), @as(i64, -3))"},
            .want = compliance.want(@max(@as(u32, 5), @as(i64, -3))),
        },
        .{
            .src = &.{"@TypeOf(@max(@as(u32, 5), @as(i64, -3)))"},
            .want = compliance.want(@TypeOf(@max(@as(u32, 5), @as(i64, -3)))),
        },
        .{
            .src = &.{"@min(@as(@Vector(3, i32), .{ 1, 5, 2 }), @as(@Vector(3, i32), .{ 4, 2, 3 }))"},
            .want = compliance.want(@min(@as(@Vector(3, i32), .{ 1, 5, 2 }), @as(@Vector(3, i32), .{ 4, 2, 3 }))),
        },
    });
}

test "compliance: variadic @min/@max fold three or more operands" {
    try compliance.check(a, &.{
        .{
            .src = &.{"@min(3, 7, 2)"},
            .want = compliance.want(@min(3, 7, 2)),
        },
        .{
            .src = &.{"@max(3, 7, 2)"},
            .want = compliance.want(@max(3, 7, 2)),
        },
        .{
            .src = &.{"@min(9, 4, 7, 1, 6)"},
            .want = compliance.want(@min(9, 4, 7, 1, 6)),
        },
        .{
            .src = &.{"@min(@as(u8, 200), @as(u8, 100), @as(u8, 50))"},
            .want = compliance.want(@min(@as(u8, 200), @as(u8, 100), @as(u8, 50))),
        },
        .{
            .src = &.{"@max(@as(u32, 5), @as(i64, -3), @as(u16, 10))"},
            .want = compliance.want(@max(@as(u32, 5), @as(i64, -3), @as(u16, 10))),
        },
        .{
            .src = &.{"@TypeOf(@min(@as(u8, 200), @as(u8, 100), @as(u8, 50)))"},
            .want = compliance.want(@TypeOf(@min(@as(u8, 200), @as(u8, 100), @as(u8, 50)))),
        },
        .{
            .src = &.{"@min(@as(@Vector(2, i32), .{ 1, 5 }), @as(@Vector(2, i32), .{ 4, 2 }), @as(@Vector(2, i32), .{ 3, 9 }))"},
            .want = compliance.want(@min(@as(@Vector(2, i32), .{ 1, 5 }), @as(@Vector(2, i32), .{ 4, 2 }), @as(@Vector(2, i32), .{ 3, 9 }))),
        },
    });
}

test "compliance: @reduce folds a vector to a scalar" {
    try compliance.check(a, &.{
        .{
            .src = &.{"@reduce(.Add, @as(@Vector(4, i32), .{ 1, 2, 3, 4 }))"},
            .want = compliance.want(@reduce(.Add, @as(@Vector(4, i32), .{ 1, 2, 3, 4 }))),
        },
        .{
            .src = &.{"@reduce(.Mul, @as(@Vector(4, i32), .{ 1, 2, 3, 4 }))"},
            .want = compliance.want(@reduce(.Mul, @as(@Vector(4, i32), .{ 1, 2, 3, 4 }))),
        },
        .{
            .src = &.{"@reduce(.Min, @as(@Vector(4, i32), .{ 3, 1, 4, 1 }))"},
            .want = compliance.want(@reduce(.Min, @as(@Vector(4, i32), .{ 3, 1, 4, 1 }))),
        },
        .{
            .src = &.{"@reduce(.Max, @as(@Vector(4, i32), .{ 3, 1, 4, 1 }))"},
            .want = compliance.want(@reduce(.Max, @as(@Vector(4, i32), .{ 3, 1, 4, 1 }))),
        },
        .{
            .src = &.{"@reduce(.And, @as(@Vector(3, u8), .{ 255, 15, 240 }))"},
            .want = compliance.want(@reduce(.And, @as(@Vector(3, u8), .{ 255, 15, 240 }))),
        },
        .{
            .src = &.{"@reduce(.Or, @as(@Vector(3, u8), .{ 1, 2, 4 }))"},
            .want = compliance.want(@reduce(.Or, @as(@Vector(3, u8), .{ 1, 2, 4 }))),
        },
        .{
            .src = &.{"@reduce(.Xor, @as(@Vector(3, u8), .{ 255, 15, 0 }))"},
            .want = compliance.want(@reduce(.Xor, @as(@Vector(3, u8), .{ 255, 15, 0 }))),
        },
    });
}

test "compliance: @mulAdd fuses multiply-add" {
    try compliance.check(a, &.{
        .{
            .src = &.{"@mulAdd(f64, 2.0, 3.0, 4.0)"},
            .want = compliance.want(@mulAdd(f64, 2.0, 3.0, 4.0)),
        },
        .{
            .src = &.{"@mulAdd(f32, 1.5, 2.0, 0.5)"},
            .want = compliance.want(@mulAdd(f32, 1.5, 2.0, 0.5)),
        },
        .{
            .src = &.{"@mulAdd(@Vector(2, f32), .{ 2.0, 3.0 }, .{ 4.0, 5.0 }, .{ 1.0, 1.0 })[1]"},
            .want = compliance.want(@mulAdd(@Vector(2, f32), .{ 2.0, 3.0 }, .{ 4.0, 5.0 }, .{ 1.0, 1.0 })[1]),
        },
        // Segfaults the compiler in comptime (`undefined` in @mulAdd under @TypeOf),
        // so the value is written literally; the REPL still evaluates the real source.
        .{
            .src = &.{"@TypeOf(@mulAdd(f64, undefined, 3.0, 4.0)) == f64"},
            .want = compliance.want(true),
        },
        .{
            .src = &.{"@mulAdd(u8, 2, 3, 4)"},
            .reject = true,
        },
    });
}
