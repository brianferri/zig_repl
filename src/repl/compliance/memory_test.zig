//! Memory-safety of the eval pipeline (OOM path + per-eval InternPool leaks). The OOM path uses a manual
//! `FailingAllocator` sweep, not `checkAllAllocationFailures` -- AstGen's address-dependent rehashing
//! shifts the allocation count between runs, which the stricter helper rejects as nondeterministic.

const std = @import("std");
const Io = std.Io;
const eval = @import("../eval.zig");
const Session = @import("../Session.zig");
const InternPool = @import("../sema/InternPool.zig");
const NativeModuleSource = @import("../module/Native.zig");

const gpa = std.testing.allocator;

/// Evaluate one input in a throwaway session, propagating an injected `error.OutOfMemory`
/// (parse/ZIR/analysis errors are swallowed to null) so teardown's leak checking can run.
fn evalUnderOom(allocator: std.mem.Allocator, input: []const u8) !void {
    var pool = try InternPool.init(allocator);
    defer pool.deinit();
    const ns = try pool.createNamespace(allocator, .{});
    var session = Session.init(allocator, &pool, ns);
    defer session.deinit();

    var scratch: [256]u8 = undefined;
    var discarding: std.Io.Writer.Discarding = .init(&scratch);
    _ = try eval.report(&session, input, &discarding.writer);
}

test "OOM: eval releases all memory on any allocation failure" {
    const inputs = [_][]const u8{
        "1 + 2 * 3 - 4",
        "@as(u8, 200) +% 100",
        "\"hello world\"",
        "blk: { const S = struct { a: u8, b: u16 }; const s = S{ .a = 1, .b = 2 }; break :blk s.b; }",
        "blk: { const U = union(enum) { a: u8, b: bool }; const u = U{ .a = 7 }; break :blk u.a; }",
        "blk: { const e: error{X}!u32 = 5; break :blk e catch 0; }",
        "blk: { var arr = [_]u8{ 1, 2, 3 }; for (&arr) |*x| x.* += 1; break :blk arr[2]; }",
        "@divCeil(@as(i32, 7), 2)",
    };
    for (inputs) |input| {
        var fail_index: usize = 0;
        while (true) : (fail_index += 1) {
            var failing: std.testing.FailingAllocator = .init(gpa, .{ .fail_index = fail_index });
            evalUnderOom(failing.allocator(), input) catch |err| switch (err) {
                error.OutOfMemory => continue,
                else => return err,
            };
            // Reached the end without the injected failure: fail_index is past the last allocation, so every site is covered.
            break;
        }
    }
}

test "no per-eval leak into the pool across a repeated line" {
    var pool = try InternPool.init(gpa);
    defer pool.deinit();
    const ns = try pool.createNamespace(gpa, .{});
    var session = Session.init(gpa, &pool, ns);
    defer session.deinit();

    var scratch: [256]u8 = undefined;
    var discarding: std.Io.Writer.Discarding = .init(&scratch);

    // The same expression interns the same values every time, so once warmed up the pool's item
    // count must not keep climbing -- a climb means a value is re-interned or leaked per eval.
    const line = "@as(u32, 6) * @as(u32, 7)";
    _ = try eval.report(&session, line, &discarding.writer);
    _ = try eval.report(&session, line, &discarding.writer);
    const settled = pool.items.len;
    for (0..20) |_| _ = try eval.report(&session, line, &discarding.writer);
    try std.testing.expectEqual(settled, pool.items.len);
}

test "no leak loading and re-importing modules across a session" {
    var io_instance: Io.Threaded = .init(gpa, .{});
    defer io_instance.deinit();
    const io = io_instance.io();
    var root = try std.Io.Dir.openDirAbsolute(io, @import("build_options").zig_std_dir, .{});
    defer root.close(io);
    var native: NativeModuleSource = .{ .io = io, .root = root };

    var pool = try InternPool.init(gpa);
    defer pool.deinit();
    const ns = try pool.createNamespace(gpa, .{});
    var session = Session.init(gpa, &pool, ns);
    defer session.deinit();
    session.module_source = &native.interface;

    var scratch: [256]u8 = undefined;
    var discarding: std.Io.Writer.Discarding = .init(&scratch);
    // A second import of an already-loaded module must reuse it, not reload and leak its sources/ZIR.
    const lines = [_][]const u8{
        "@import(\"std\").mem.eql(u8, \"a\", \"a\")",
        "@import(\"builtin\").is_test",
        "@import(\"std\").math.maxInt(u8)",
        "@import(\"std\").mem.eql(u8, \"b\", \"b\")",
    };
    for (lines) |line| _ = try eval.report(&session, line, &discarding.writer);
}
