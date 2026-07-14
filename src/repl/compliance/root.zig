//! Validates the interpreter against zig's own evaluation.
//!
//! A case pairs interpreter source with the *same expression written as real zig code*.
//! The zig reference is whatever the build's compiler folds that expression to at
//! comptime -- so there is no separate compile step: the build and the zig test runner
//! compile and run the references as part of the test binary itself. `replRun` supplies
//! the interpreter side, running a case's inputs through the same `eval.run` path the
//! interactive REPL takes.
//!
//! A case is one of:
//!   .{ .src = &.{"<input>"...},  .want = <zig expr> }     -- output must match zig's
//!   .{ .src = &.{"<input>"...},  .rendered = "<string>" } -- output must equal this
//!   .{ .src = &.{"<input>"...},  .reject = {} }           -- interpreter must reject
//! `want` is the same expression written as real zig, comptime-folded for the
//! reference. `rendered` gives the expected output literally, for values zig has no
//! comparable form for (build-specific names, deliberate divergences). `reject` cases
//! can't carry a `want`: a compile error can't be written as comptime code.

const std = @import("std");
const Io = std.Io;
const eval = @import("../eval.zig");
const Session = @import("../Session.zig");
const InternPool = @import("../sema/InternPool.zig");
const Value = @import("../sema/Value.zig");
const render = @import("../render/Value.zig");
const NativeModuleSource = @import("../NativeModuleSource.zig");

/// Assert each case's interpreter output matches zig's comptime rendering of its
/// `.want` expression (or that the interpreter rejects a `.reject` case).
pub fn check(gpa: std.mem.Allocator, comptime cases: anytype) !void {
    inline for (cases) |case| {
        if (@hasField(@TypeOf(case), "reject")) {
            if (replRun(gpa, case.src)) |out| {
                gpa.free(out);
                std.debug.print("expected rejection but evaluated: {s}\n", .{case.src[case.src.len - 1]});
                return error.TestUnexpectedSuccess;
            } else |_| {}
        } else {
            const actual = try replRun(gpa, case.src);
            defer gpa.free(actual);
            const want = comptime if (@hasField(@TypeOf(case), "rendered"))
                normalize(case.rendered)
            else
                normalize(std.fmt.comptimePrint("{any}", .{case.want}));
            std.testing.expectEqualStrings(want, normalize(actual)) catch |err| {
                std.debug.print("mismatch for: {s}\n", .{case.src[case.src.len - 1]});
                return err;
            };
        }
    }
}

/// Strip surrounding whitespace and a trailing `.0` (which `{any}` omits on integral
/// floats), so `4.0` and `4` compare equal.
fn normalize(text: []const u8) []const u8 {
    var t = std.mem.trim(u8, text, " \r\n\t");
    if (std.mem.endsWith(u8, t, ".0")) t = t[0 .. t.len - 2];
    return t;
}

/// Assert the REPL rejects `inputs` and its rendered diagnostic contains `needle` --
/// unlike a `.reject` case, this pins the REPL's own wording, so it stays in the test
/// body rather than the data table.
pub fn expectDiagnostic(gpa: std.mem.Allocator, inputs: []const []const u8, needle: []const u8) !void {
    var io_instance: Io.Threaded = .init(gpa, .{});
    defer io_instance.deinit();
    const io = io_instance.io();
    var root = try std.Io.Dir.openDirAbsolute(io, @import("build_options").zig_std_dir, .{});
    defer root.close(io);
    var native: NativeModuleSource = .{ .io = io, .root = root };

    var pool = try InternPool.init(gpa);
    defer pool.deinit();
    const ns = try pool.createNamespace(gpa, .none);
    var session = Session.init(gpa, &pool, ns);
    defer session.deinit();
    session.module_source = &native.interface;

    var diag: Io.Writer.Allocating = .init(gpa);
    defer diag.deinit();

    var rejected = false;
    for (inputs) |source| {
        _ = eval.run(&session, source, &diag.writer) catch |err| switch (err) {
            error.ParseError, error.ZirError, error.AnalysisFail => {
                rejected = true;
                break;
            },
            else => return err,
        };
    }
    try std.testing.expect(rejected);
    if (std.mem.indexOf(u8, diag.written(), needle) == null) {
        std.debug.print("diagnostic did not contain '{s}':\n{s}\n", .{ needle, diag.written() });
        return error.TestDiagnosticMismatch;
    }
}

// Fuzz target: generate plausible zig with `AstSmith` and run it through the
// evaluator, discarding the result -- what matters is that no input panics, corrupts,
// or leaks. In a normal `zig build test` this runs once on an empty seed (a
// deterministic smoke test); `zig build test --fuzz` drives it for real.
test "fuzz: the evaluator survives arbitrary zig source" {
    try std.testing.fuzz({}, fuzzEval, .{});
}

fn fuzzEval(_: void, smith: *std.testing.Smith) anyerror!void {
    const gpa = std.testing.allocator;
    const ast_smith = try gpa.create(std.zig.AstSmith);
    defer gpa.destroy(ast_smith);
    ast_smith.* = .init(smith);
    ast_smith.generateSource() catch return;
    const src = ast_smith.source();
    if (src.len == 0) return; // eval.run requires non-empty input (the REPL never feeds it a blank line)
    const out = replRun(gpa, &.{src}) catch return;
    gpa.free(out);
}

/// Run `inputs` through a fresh session and return the rendered last value. The
/// session is wired to the real std library, so cases using `@import("std")` (e.g.
/// `@reduce`, whose op is a `std.builtin.ReduceOp`) resolve.
fn replRun(gpa: std.mem.Allocator, inputs: []const []const u8) ![]u8 {
    var io_instance: Io.Threaded = .init(gpa, .{});
    defer io_instance.deinit();
    const io = io_instance.io();
    var root = try std.Io.Dir.openDirAbsolute(io, @import("build_options").zig_std_dir, .{});
    defer root.close(io);
    var native: NativeModuleSource = .{ .io = io, .root = root };

    var pool = try InternPool.init(gpa);
    defer pool.deinit();
    const ns = try pool.createNamespace(gpa, .none);
    var session = Session.init(gpa, &pool, ns);
    defer session.deinit();
    session.module_source = &native.interface;

    var diag: Io.Writer.Allocating = .init(gpa);
    defer diag.deinit();

    var last_value: ?Value = null;
    for (inputs) |source| {
        last_value = (try eval.run(&session, source, &diag.writer)).value;
    }
    const value = last_value orelse return error.NoValue;

    var out_buf: [4096]u8 = undefined;
    var out_writer = Io.Writer.fixed(&out_buf);
    try render.render(value, &pool, null, &out_writer);
    return gpa.dupe(u8, std.mem.trimEnd(u8, out_writer.buffered(), "\n"));
}

// Pull every co-located compliance suite into the build so `zig build test`
// discovers them; each file drives `check`/`expectDiagnostic` from this module.
test {
    _ = @import("aggregate_test.zig");
    _ = @import("arith_test.zig");
    _ = @import("array_ops_test.zig");
    _ = @import("async_test.zig");
    _ = @import("builtin_test.zig");
    _ = @import("cast_test.zig");
    _ = @import("coercion_test.zig");
    _ = @import("control_flow_test.zig");
    _ = @import("diagnostics_test.zig");
    _ = @import("enum_test.zig");
    _ = @import("error_test.zig");
    _ = @import("import_test.zig");
    _ = @import("fn_test.zig");
    _ = @import("module_test.zig");
    _ = @import("optional_test.zig");
    _ = @import("pointer_test.zig");
    _ = @import("reflect_test.zig");
    _ = @import("repl_test.zig");
    _ = @import("sad_paths_test.zig");
    _ = @import("slice_test.zig");
    _ = @import("struct_test.zig");
    _ = @import("switch_test.zig");
    _ = @import("typeof_test.zig");
    _ = @import("union_test.zig");
    _ = @import("vector_test.zig");
}
