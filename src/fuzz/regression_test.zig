//! Fixed inputs the interpreter must survive without leaking, over-reading, or
//! panicking. Unlike the exploratory `targets.zig`, these run inside
//! `zig build test` under the leak-checking allocator, so a regression stays
//! fixed. Seed new entries here with the minimized reproduction whenever the
//! fuzzer finds a crash. Nothing here asserts output -- survival is the contract
//! (see harness.zig).

const std = @import("std");
const harness = @import("harness.zig");

const gpa = std.testing.allocator;

test "survives adversarial single-line inputs" {
    const cases = [_][]const u8{
        // Truncated / dangling tokens.
        "const x =",
        "@",
        "@import(",
        "\"unterminated",
        "'",
        "0x",
        "1.",
        ".{",
        "fn f(",
        // Degenerate but valid.
        " ",
        "\n\n\t",
        ";",
        "//just a comment",
        "0",
        "undefined",
        // Numeric edges.
        "0xffffffffffffffffffffffffffffffff + 1",
        "1 << 1000",
        "@as(u8, 999999)",
        "-0.0",
        "1e1000",
        // Unicode and escapes in identifiers / strings.
        "const \xc3\xa9 = 1;",
        "\"\\xff\\x00\\u{10ffff}\"",
        "@import(\"\xff\xfe\")",
        // Self-referential / recursive shapes.
        "const T = struct { next: ?*T };",
        "fn f() void { return f(); }",
        // Builtins with wrong arity / bad args.
        "@intFromEnum(0)",
        "@field(1, 2)",
        "@Type(.{})",
        "@memcpy()",
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
    // Redefinition, shadowing, and use of a name a prior failed line "declared".
    harness.runSession(gpa, &.{
        "const x = 1;",
        "const x = 2;",
        "const y = nonexistent;",
        "y + x",
    });
    // A type defined on one line, used as a result location on the next.
    harness.runSession(gpa, &.{
        "const S = struct { a: u8 };",
        "@as(S, .{ .a = 1 })",
        "@as(S, .{ .a = 2 }).a",
    });
}
