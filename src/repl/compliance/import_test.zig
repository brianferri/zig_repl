const std = @import("std");
const compliance = @import("root.zig");

const a = std.testing.allocator;

test "compliance: @import(\"root\") reaches the session's top-level decls" {
    try compliance.check(a, &.{
        // A prior-line const, read back through root.
        .{ .src = &.{ "const x = 5;", "@import(\"root\").x" }, .rendered = "5" },
        .{ .src = &.{ "const y = 7;", "@import(\"root\").y + 1" }, .rendered = "8" },
        // A same-line decl is in scope for a trailing root access.
        .{ .src = &.{"const w = 3; @import(\"root\").w"}, .rendered = "3" },
        // A function decl, called through root.
        .{ .src = &.{ "fn f() u8 { return 9; }", "@import(\"root\").f()" }, .rendered = "9" },
        // A type decl, reached through root and used as a result-location type.
        .{ .src = &.{ "const S = struct { a: u8 };", "@as(@import(\"root\").S, .{ .a = 4 }).a" }, .rendered = "4" },
        // The pointer form (`&root.x`) resolves the same decl.
        .{ .src = &.{ "const p: u32 = 5;", "@import(\"root\").p + (&@import(\"root\").p).*" }, .rendered = "10" },
        // A root function body resolves another root decl by bare name.
        .{ .src = &.{ "const A = 3;", "fn g() u8 { return @import(\"root\").A + 1; }", "@import(\"root\").g()" }, .rendered = "4" },
        // The root container's identity is stable across imports.
        .{ .src = &.{"@TypeOf(@import(\"root\")) == @TypeOf(@import(\"root\"))"}, .rendered = "true" },
        // An unbound name is rejected.
        .{ .src = &.{"@import(\"root\").nope"}, .reject = true },
    });
}

test "compliance: pub-visibility on qualified member access" {
    try compliance.check(a, &.{
        // Same-file (session) private decl is accessible, qualified.
        .{ .src = &.{"blk: { const S = struct { const x: u8 = 5; }; break :blk S.x; }"}, .want = compliance.want(blk: {
            const S = struct {
                const x: u8 = 5;
            };
            break :blk S.x;
        }) },
        // Cross-module private decl is rejected: `std` is a private decl of the
        // generated `builtin` module.
        .{ .src = &.{"@import(\"builtin\").std"}, .reject = true },
    });
    try compliance.expectDiagnostic(a, &.{"@import(\"builtin\").std"}, "not marked 'pub'");
}
