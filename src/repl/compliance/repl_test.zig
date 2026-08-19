const std = @import("std");
const compliance = @import("root.zig");

const eval = @import("../eval.zig");
const Session = @import("../Session.zig");
const InternPool = @import("../sema/InternPool.zig");

const a = std.testing.allocator;

test "mixed input: declarations then a trailing expression persist across passes" {
    try compliance.check(a, &.{
        .{ .src = &.{"const mx = 10; mx + 1"}, .want = compliance.want(blk: {
            const mx = 10;
            break :blk mx + 1;
        }) },
        .{ .src = &.{ "const mz = 5; mz", "mz * 2" }, .want = compliance.want(blk: {
            const mz = 5;
            break :blk mz * 2;
        }) },
    });
}

test "diagnostic: a Sema error renders a source-anchored caret with notes" {
    const gpa = std.testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();
    const ns = try pool.createNamespace(gpa, .{});
    var session = Session.init(gpa, &pool, ns);
    defer session.deinit();

    var diag: std.Io.Writer.Allocating = .init(gpa);
    defer diag.deinit();
    // A `u16 -> u8` @memcpy element mismatch anchors on the `@memcpy` node and
    // carries an `int_not_coercible` note.
    try std.testing.expectError(error.AnalysisFail, eval.run(
        &session,
        "blk: { var dst = [_]u8{ 0, 0 }; const src = [_]u16{ 1, 2 }; @memcpy(dst[0..2], src[0..2]); break :blk dst[0]; }",
        &diag.writer,
    ));
    const out = diag.written();
    for ([_][]const u8{
        "<repl>:1:",
        "error:",
        "@memcpy",
        "^",
        "note:",
        "cannot represent all possible",
    }) |needle| {
        if (std.mem.indexOf(u8, out, needle) == null) {
            std.debug.print("caret diagnostic missing '{s}':\n{s}\n", .{ needle, out });
            return error.TestCaretMismatch;
        }
    }
}
