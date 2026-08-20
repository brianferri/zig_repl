//! Fixed inputs the interpreter must survive under the leak-checking allocator, so a
//! fuzzer-found crash stays fixed. Survival is the contract; nothing asserts output.

const std = @import("std");
const harness = @import("harness.zig");

const gpa = std.testing.allocator;

test "survives adversarial single-line inputs" {
    const cases = [_][]const u8{
        "const x =",
        "@",
        "@import(",
        "\"unterminated",
        "'",
        "0x",
        "1.",
        ".{",
        "fn f(",
        " ",
        "\n\n\t",
        ";",
        "//just a comment",
        "0",
        "undefined",
        "0xffffffffffffffffffffffffffffffff + 1",
        "1 << 1000",
        "@as(u8, 999999)",
        "-0.0",
        "1e1000",
        "const \xc3\xa9 = 1;",
        "\"\\xff\\x00\\u{10ffff}\"",
        "@import(\"\xff\xfe\")",
        "const T = struct { next: ?*T };",
        "fn f() void { return f(); }",
        "@intFromEnum(0)",
        "@field(1, 2)",
        "@Type(.{})",
        "@memcpy()",
        // A non-type where a type is required: rejected before type methods run
        // (`@as(4, .{...})` must not reach `zigTypeTag` on a value).
        "@as(4, .{ .a = 3 }).a",
        "@as(0, .{})",
        // A value in a type-declaration position (struct/union field, variable,
        // parameter, return type) must be rejected when that position is resolved,
        // not reach `coerceInMemoryAllowed`'s `zigTypeTag` on a value.
        "(struct { x: 5 }){ .x = 1 }",
        "(union { x: 5 }){ .x = 1 }",
        "const x: 5 = 1;",
        "fn f(x: 5) void { _ = x; }",
        "fn f() 5 { return 1; }",
        // Bitwise operators on non-integer operands: a type error, not a panic
        // (`bitwiseBin`'s `else => unreachable` assumes validated operands).
        "3.5 & 3",
        "1.0 | 2",
        "2.5 ^ 1",
        "true & 1.0",
        // Wrapping / saturating operators reject floats (integer-only).
        "@as(u4, 15) *% @as(f64, @floatFromInt(7))",
        "3.0 +% 1",
        "2.5 -% 1",
        "1.0 *| 2",
        "3.5 +| 1",
    };
    for (cases) |input| harness.runLine(gpa, input);
}

test "survives adversarial multi-line sequences" {
    // A failed evaluation must not corrupt state a later line depends on -- the
    // shape of the root-namespace identity collision (std imports root while std
    // is the file under analysis, aliasing std's own container).
    harness.runSession(gpa, &.{
        "@import(\"std\").debug.print(\"x\", .{})",
        "@import(\"std\").Target",
        "@import(\"builtin\").target",
    });
    harness.runSession(gpa, &.{
        "const x = 1;",
        "const x = 2;",
        "const y = nonexistent;",
        "y + x",
    });
    harness.runSession(gpa, &.{
        "const S = struct { a: u8 };",
        "@as(S, .{ .a = 1 })",
        "@as(S, .{ .a = 2 }).a",
    });
    // An error raised inside a called function's body: its diagnostic must resolve
    // against the function's file (a prior line), not the calling line's tree.
    harness.runSession(gpa, &.{
        "fn f(n: u32) u32 { return !n + 1; }",
        "f(40)",
    });
}
