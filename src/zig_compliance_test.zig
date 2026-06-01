//! Compliance harness -- runs each expression through both our REPL and
//! a freshly-spawned `zig run` on the same source, normalises both
//! outputs, and asserts they match. This proves spec compliance for
//! the expressions we list here at the test-runner level.

const std = @import("std");
const testing = std.testing;
const Io = std.Io;

const Pipeline = @import("front/Pipeline.zig");
const InputShape = @import("front/InputShape.zig");
const Sema = @import("sema/Sema.zig");
const Session = @import("Session.zig");
const InternPool = @import("sema/InternPool.zig");
const Value = @import("sema/Value.zig");
const render = @import("render/Value.zig");

// Shared across cases; sits under .zig-cache so `zig build` cleans it.
const compliance_cache_dir = ".zig-cache/tmp/zig-repl-compliance";

/// Front-end + Sema for one wrapped segment, committing the pipeline so
/// later segments can reference what it bound. Returns the produced
/// Value (null for a declaration segment). Parse/ZIR errors surface as
/// the same error tags `expectBothReject` matches.
fn analyzeViaRepl(
    gpa: std.mem.Allocator,
    pool: *InternPool,
    session: *Session,
    source: []const u8,
) !?Value {
    var result = try Pipeline.runWithInjection(gpa, source, pool, .init(session.root_namespace));
    var committed = false;
    defer if (!committed) result.deinit(gpa);

    if (result.hasParseErrors()) return error.ParseError;
    if (result.hasZirErrors()) return error.ZirError;

    var diag_buf: [4096]u8 = undefined;
    var diag_writer = Io.Writer.fixed(&diag_buf);
    const value = try Sema.analyze(session, result.zir, &diag_writer);
    try session.pipelines.append(gpa, result);
    committed = true;
    return value;
}

/// Run a sequence of REPL inputs through Pipeline + Sema + render
/// against a fresh session namespace. The last input must produce a
/// Value; the prior inputs typically bind decls the last expression
/// references. Returns the rendered text of the final value with
/// trailing newline stripped.
fn runViaRepl(
    gpa: std.mem.Allocator,
    inputs: []const []const u8,
) ![]u8 {
    assert(inputs.len >= 1);

    var pool = try InternPool.init(gpa);
    defer pool.deinit();
    const ns = try pool.createNamespace(gpa, .none);

    var session = Session.initForTest(gpa, &pool, ns);
    defer session.deinit();

    var last_value: ?Value = null;
    for (inputs) |source| {
        // Mirror `Repl.evaluate`: an input that is declarations plus a
        // trailing expression runs as two passes so the harness exercises
        // the same path the REPL does.
        if (try InputShape.splitTrailingExpr(gpa, source)) |split| {
            // The declaration pass yields null (decls render nothing);
            // the trailing expression's value is the one that matters.
            last_value = try analyzeViaRepl(gpa, &pool, &session, split.decls);
            last_value = try analyzeViaRepl(gpa, &pool, &session, split.expr);
        } else {
            last_value = try analyzeViaRepl(gpa, &pool, &session, source);
        }
    }

    const value = last_value orelse return error.NoValue;
    var out_buf: [4096]u8 = undefined;
    var out_writer = Io.Writer.fixed(&out_buf);
    try render.render(value, &pool, &out_writer);

    const raw = out_buf[0 .. out_writer.buffer.len - out_writer.unusedCapacityLen()];
    return try gpa.dupe(u8, std.mem.trimEnd(u8, raw, "\n"));
}

/// Synthesise a Zig program that mirrors the REPL session: all but
/// the last input become container-scope decls; the last input is
/// printed via `std.debug.print("{any}", ...)`. `zig run` it, return
/// captured stderr.
fn runViaZig(
    gpa: std.mem.Allocator,
    inputs: []const []const u8,
) ![]u8 {
    assert(inputs.len >= 1);

    var prog: std.Io.Writer.Allocating = .init(gpa);
    defer prog.deinit();

    try prog.writer.writeAll("const std = @import(\"std\");\n");
    for (inputs[0 .. inputs.len - 1]) |decl_line| {
        try prog.writer.print("{s}\n", .{decl_line});
    }
    // `std.debug.print` writes to stderr -- captured stderr IS the
    // value, sidestepping the file-writer init dance.
    try prog.writer.print(
        "pub fn main() void {{ std.debug.print(\"{{any}}\", .{{ {s} }}); }}\n",
        .{inputs[inputs.len - 1]},
    );

    var io_instance: Io.Threaded = .init(gpa, .{});
    defer io_instance.deinit();
    const io = io_instance.io();

    // tmpDir gives each call its own source path so concurrent runs
    // can't clobber one another's program.
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    tmp.dir.writeFile(io, .{ .sub_path = "prog.zig", .data = prog.written() }) catch
        return error.SkipZigTest;

    var path_buf: [128]u8 = undefined;
    const src_path = std.fmt.bufPrint(&path_buf, ".zig-cache/tmp/{s}/prog.zig", .{tmp.sub_path}) catch
        return error.SkipZigTest;

    // Cache dirs are explicit and shared: `zig build test` runs the
    // test binary with no HOME, so zig can't resolve its default
    // global cache (AppDataDirUnavailable); a shared dir also compiles
    // std once instead of once per case.
    const result = std.process.run(gpa, io, .{
        .argv = &.{
            "zig",                "run",                src_path,
            "--cache-dir",        compliance_cache_dir, "--global-cache-dir",
            compliance_cache_dir,
        },
        .stdout_limit = .limited(4096),
        .stderr_limit = .limited(16 * 1024),
    }) catch |err| switch (err) {
        error.FileNotFound => return error.SkipZigTest,
        else => return err,
    };
    defer gpa.free(result.stdout);

    switch (result.term) {
        .exited => |code| if (code != 0) {
            gpa.free(result.stderr);
            return error.ZigRunFailed;
        },
        else => {
            gpa.free(result.stderr);
            return error.ZigRunFailed;
        },
    }
    return result.stderr;
}

/// Normalise either side's output before comparison: strip surrounding
/// whitespace and the trailing `.0` our renderer adds to integral
/// floats (Zig's `{any}` omits it, e.g. `4.0` prints as `4`).
fn normalize(text: []const u8) []const u8 {
    var t = std.mem.trim(u8, text, " \r\n\t");
    if (std.mem.endsWith(u8, t, ".0")) t = t[0 .. t.len - 2];
    return t;
}

/// Run a sequence of REPL inputs (the last being a value-producing
/// expression) through both our REPL and `zig run`, normalise both
/// outputs, assert equality. Single-expression cases pass a one-
/// element slice; multi-input cases stage decls then the final
/// expression.
fn expectMatchesZig(gpa: std.mem.Allocator, inputs: []const []const u8) !void {
    const our_output = try runViaRepl(gpa, inputs);
    defer gpa.free(our_output);
    const zig_output = try runViaZig(gpa, inputs);
    defer gpa.free(zig_output);

    try testing.expectEqualStrings(normalize(zig_output), normalize(our_output));
}

/// Assert both our REPL and `zig run` reject the program. For cases
/// that are compile errors on both sides (e.g. unwrapping a
/// comptime-known null) there is no output to compare -- only mutual
/// rejection. Matching the exact message would key on wording that
/// drifts between toolchains, so this checks rejection, not text.
fn expectBothReject(gpa: std.mem.Allocator, inputs: []const []const u8) !void {
    if (runViaRepl(gpa, inputs)) |out| {
        gpa.free(out);
        return error.TestUnexpectedReplSuccess;
    } else |err| switch (err) {
        error.ParseError, error.ZirError, error.AnalysisFail => {},
        else => return err,
    }

    if (runViaZig(gpa, inputs)) |out| {
        gpa.free(out);
        return error.TestUnexpectedZigSuccess;
    } else |err| switch (err) {
        error.ZigRunFailed => {},
        else => return err,
    }
}

const assert = std.debug.assert;

test "compliance: comptime_int arithmetic" {
    try expectMatchesZig(testing.allocator, &.{"1 + 2 * 3"});
}

test "compliance: comptime_int big literal" {
    try expectMatchesZig(testing.allocator, &.{"1000000000 * 1000"});
}

test "compliance: comptime_float arithmetic" {
    try expectMatchesZig(testing.allocator, &.{"1.5 + 2.5"});
}

test "compliance: comptime_int + comptime_float promotes" {
    try expectMatchesZig(testing.allocator, &.{"1 + 1.5"});
}

test "compliance: fixed-width int arith" {
    try expectMatchesZig(testing.allocator, &.{"@as(i32, 5) + @as(i32, 3)"});
}

test "compliance: peer resolution to wider int" {
    try expectMatchesZig(testing.allocator, &.{"@as(u8, 5) + @as(u16, 10)"});
}

test "compliance: peer resolution mixed signedness (signed wider)" {
    try expectMatchesZig(testing.allocator, &.{"@as(u8, 5) + @as(i16, 100)"});
}

test "compliance: peer resolution mixed signedness (legacy unsigned wider)" {
    try expectMatchesZig(testing.allocator, &.{"@as(u16, 5) + @as(i8, 100)"});
}

test "compliance: fixed-width float arith" {
    try expectMatchesZig(testing.allocator, &.{"@as(f32, 1.5) + @as(f32, 2.5)"});
}

test "compliance: mixed-width float widens" {
    try expectMatchesZig(testing.allocator, &.{"@as(f32, 1.5) + @as(f64, 2.5)"});
}

test "compliance: fixed-width int + fixed-width float" {
    try expectMatchesZig(testing.allocator, &.{"@as(f32, 1.5) + @as(i32, 2)"});
}

test "compliance: wrap arith" {
    try expectMatchesZig(testing.allocator, &.{"@as(u8, 200) +% @as(u8, 100)"});
}

test "compliance: sat arith" {
    try expectMatchesZig(testing.allocator, &.{"@as(u8, 200) +| @as(u8, 100)"});
}

test "compliance: shift arith" {
    try expectMatchesZig(testing.allocator, &.{"@as(u8, 1) << 7"});
}

test "compliance: bitwise on fixed-width" {
    try expectMatchesZig(testing.allocator, &.{"@as(u16, 1000) & @as(u16, 0xff)"});
}

test "compliance: @intCast widen" {
    try expectMatchesZig(testing.allocator, &.{"@as(u32, @intCast(@as(u8, 200)))"});
}

test "compliance: @truncate" {
    try expectMatchesZig(testing.allocator, &.{"@as(u8, @truncate(@as(u32, 0x1234)))"});
}

test "compliance: @bitCast f32 -> u32" {
    try expectMatchesZig(testing.allocator, &.{"@as(u32, @bitCast(@as(f32, 1.5)))"});
}

test "compliance: @bitCast i8 -> u8 (two's complement)" {
    try expectMatchesZig(testing.allocator, &.{"@as(u8, @bitCast(@as(i8, -1)))"});
}

test "compliance: usize + comptime_int" {
    try expectMatchesZig(testing.allocator, &.{"@as(usize, 100) + 1"});
}

test "compliance: c_int peer participation" {
    try expectMatchesZig(testing.allocator, &.{"@as(c_int, 5) * 2"});
}

test "compliance: comparison across widths" {
    try expectMatchesZig(testing.allocator, &.{"@as(u16, 1000) > @as(u8, 200)"});
}

test "compliance: @as comptime_float -> fixed-width" {
    try expectMatchesZig(testing.allocator, &.{"@as(f32, 1.5)"});
}

test "compliance: @as fixed-width int -> fixed-width float" {
    try expectMatchesZig(testing.allocator, &.{"@as(f64, @as(i32, 1000000))"});
}

test "compliance: @intFromFloat truncate" {
    try expectMatchesZig(testing.allocator, &.{"@as(i32, @intFromFloat(@as(f64, 3.7)))"});
}

test "compliance: @floatFromInt rounding" {
    try expectMatchesZig(testing.allocator, &.{"@as(f32, @floatFromInt(16777217))"});
}

test "compliance: bit_not on fixed-width int" {
    try expectMatchesZig(testing.allocator, &.{"~@as(u8, 5)"});
}

test "compliance: bit_not on signed int" {
    try expectMatchesZig(testing.allocator, &.{"~@as(i32, 100)"});
}

test "compliance: negate_wrap on signed min" {
    try expectMatchesZig(testing.allocator, &.{"-%@as(i8, -128)"});
}

test "compliance: negate on fixed-width int" {
    try expectMatchesZig(testing.allocator, &.{"-@as(i32, 100)"});
}

test "compliance: ptr_type *const u8 renders as Zig prints" {
    try expectMatchesZig(testing.allocator, &.{"*const u8"});
}

test "compliance: ptr_type [*]u32 renders as Zig prints" {
    try expectMatchesZig(testing.allocator, &.{"[*]u32"});
}

test "compliance: ptr_type []i32 renders as Zig prints" {
    try expectMatchesZig(testing.allocator, &.{"[]i32"});
}

test "compliance: ptr_type nested *const *const u32 renders identically" {
    try expectMatchesZig(testing.allocator, &.{"*const *const u32"});
}

test "compliance: @as(type, *const u8) is identity on type-of-type" {
    try expectMatchesZig(testing.allocator, &.{"@as(type, *const u8)"});
}

test "compliance: @as(type, [*]i32) is identity on type-of-type" {
    try expectMatchesZig(testing.allocator, &.{"@as(type, [*]i32)"});
}

test "compliance: @as(type, *const *const u32) recurses correctly" {
    try expectMatchesZig(testing.allocator, &.{"@as(type, *const *const u32)"});
}

test "compliance: var mutation through alloc/store/load" {
    try expectMatchesZig(testing.allocator, &.{"blk: { var x: u8 = 0; x = x + 1; break :blk x; }"});
}

test "compliance: wrap arith through a stored var" {
    try expectMatchesZig(testing.allocator, &.{"blk: { var x: u8 = 200; x = x +% 100; break :blk x; }"});
}

test "compliance: two independent var slots do not alias" {
    try expectMatchesZig(testing.allocator, &.{"blk: { var a: u8 = 1; var b: u8 = 2; a = 10; b = 20; break :blk a + b; }"});
}

test "compliance: error value prints identically to zig" {
    try expectMatchesZig(testing.allocator, &.{"error.Foo"});
}

test "compliance: error set type prints alphabetically (matches @typeName)" {
    try expectMatchesZig(testing.allocator, &.{"error{Foo, Bar}"});
}

test "compliance: error set sorts independently of source order" {
    try expectMatchesZig(testing.allocator, &.{"error{Charlie, Alpha, Bravo}"});
}

test "compliance: large error set renders without truncation" {
    try expectMatchesZig(testing.allocator, &.{
        "error{Z,Y,X,W,V,U,T,S,R,Q,P,O,N,M,L,K,J,I,H,G,F,E,D,C,B,A}",
    });
}

test "compliance: error union type prints as E!T" {
    try expectMatchesZig(testing.allocator, &.{"error{Bad}!u32"});
}

test "compliance: @as(E!T, error.X) prints as the error value" {
    try expectMatchesZig(testing.allocator, &.{"@as(error{Bad}!u32, error.Bad)"});
}

test "compliance: @as(E!T, payload) prints as the payload value" {
    try expectMatchesZig(testing.allocator, &.{"@as(error{Bad}!u32, 42)"});
}

test "compliance: multi-element error union renders alphabetically" {
    try expectMatchesZig(testing.allocator, &.{"error{Worse,Bad}!i64"});
}

test "compliance: cross-line error set + union type round-trip" {
    try expectMatchesZig(testing.allocator, &.{
        "const E = error{Oops};",
        "const EU = E!u8;",
        "EU",
    });
}

test "compliance: cross-line @as(EU, error.X) wraps as error arm" {
    try expectMatchesZig(testing.allocator, &.{
        "const E = error{Oops};",
        "const EU = E!u8;",
        "@as(EU, error.Oops)",
    });
}

test "compliance: cross-line @as(EU, payload) wraps as payload arm" {
    try expectMatchesZig(testing.allocator, &.{
        "const E = error{Oops};",
        "const EU = E!u8;",
        "@as(EU, 7)",
    });
}

test "compliance: cross-line bound int decl evaluates in expression" {
    try expectMatchesZig(testing.allocator, &.{
        "const x: u32 = 100;",
        "x + 5",
    });
}

test "compliance: catch on .err arm returns the error" {
    try expectMatchesZig(testing.allocator, &.{
        "@as(error{Bad}!u32, error.Bad) catch |e| e",
    });
}

test "compliance: catch on .err arm with default returns the default" {
    try expectMatchesZig(testing.allocator, &.{
        "@as(error{Bad}!u32, error.Bad) catch @as(u32, 0)",
    });
}

test "compliance: catch on .payload arm returns the payload" {
    try expectMatchesZig(testing.allocator, &.{
        "@as(error{Bad}!u32, 99) catch @as(u32, 0)",
    });
}

test "compliance: catch on .payload arm with capture returns the payload" {
    try expectMatchesZig(testing.allocator, &.{
        "@as(error{Bad}!u32, 99) catch |e| e",
    });
}

test "compliance: cross-line catch on .err arm" {
    try expectMatchesZig(testing.allocator, &.{
        "const E = error{Bad};",
        "const EU = E!u32;",
        "const x: EU = error.Bad;",
        "x catch |e| e",
    });
}

test "compliance: cross-line catch on .payload arm" {
    try expectMatchesZig(testing.allocator, &.{
        "const E = error{Bad};",
        "const EU = E!u32;",
        "const y: EU = 42;",
        "y catch @as(u32, 0)",
    });
}

test "compliance: switch scalar case match" {
    try expectMatchesZig(testing.allocator, &.{"switch (1) { 0 => 100, 1 => 200, else => 999 }"});
}

test "compliance: switch falls through to else" {
    try expectMatchesZig(testing.allocator, &.{"switch (5) { 0 => 100, else => 999 }"});
}

test "compliance: switch on fixed-width int operand" {
    try expectMatchesZig(testing.allocator, &.{"switch (@as(u8, 2)) { 0 => 10, 1 => 20, 2 => 30, else => 0 }"});
}

test "compliance: switch multi-case items" {
    try expectMatchesZig(testing.allocator, &.{"switch (3) { 0, 1, 2 => 100, 3, 4 => 200, else => 0 }"});
}

test "compliance: switch range lower edge" {
    try expectMatchesZig(testing.allocator, &.{"switch (0) { 0...2 => 100, 3...5 => 200, else => 999 }"});
}

test "compliance: switch range upper edge" {
    try expectMatchesZig(testing.allocator, &.{"switch (5) { 0...2 => 100, 3...5 => 200, else => 999 }"});
}

test "compliance: switch range falls through" {
    try expectMatchesZig(testing.allocator, &.{"switch (7) { 0...2 => 100, 3...5 => 200, else => 999 }"});
}

test "compliance: catch-then-switch matches first error name" {
    try expectMatchesZig(testing.allocator, &.{
        "const E = error{Bad, Worse};",
        "const x: E!u32 = error.Bad;",
        "x catch |e| switch (e) { error.Bad => 1, error.Worse => 2 }",
    });
}

test "compliance: catch-then-switch matches second error name" {
    try expectMatchesZig(testing.allocator, &.{
        "const E = error{Bad, Worse};",
        "const x: E!u32 = error.Worse;",
        "x catch |e| switch (e) { error.Bad => 1, error.Worse => 2 }",
    });
}

test "compliance: anonymous fn type, nullary void" {
    try expectMatchesZig(testing.allocator, &.{"fn () void"});
}

test "compliance: anonymous fn type, single param" {
    try expectMatchesZig(testing.allocator, &.{"fn (u32) u8"});
}

test "compliance: anonymous fn type, two int params" {
    try expectMatchesZig(testing.allocator, &.{"fn (u32, i32) u8"});
}

test "compliance: anonymous fn type, mixed-type params" {
    try expectMatchesZig(testing.allocator, &.{"fn (u32, bool) u8"});
}

test "compliance: fn type bound to a const, then referenced" {
    try expectMatchesZig(testing.allocator, &.{
        "const T = fn (u32) i32;",
        "T",
    });
}

test "compliance: @TypeOf on @as-typed int returns the dest type" {
    try expectMatchesZig(testing.allocator, &.{"@TypeOf(@as(u32, 1))"});
}

test "compliance: @TypeOf on bool literal" {
    try expectMatchesZig(testing.allocator, &.{"@TypeOf(true)"});
}

test "compliance: @TypeOf on bare int literal yields comptime_int" {
    try expectMatchesZig(testing.allocator, &.{"@TypeOf(1)"});
}

test "compliance: @TypeOf on @as-typed signed int" {
    try expectMatchesZig(testing.allocator, &.{"@TypeOf(@as(i32, -5))"});
}

test "compliance: @TypeOf on a normal fn declaration" {
    try expectMatchesZig(testing.allocator, &.{
        "fn foo() void {}",
        "@TypeOf(foo)",
    });
}

test "compliance: @TypeOf on a fn decl with params" {
    try expectMatchesZig(testing.allocator, &.{
        "fn add(a: u32, b: u32) u32 { return a + b; }",
        "@TypeOf(add)",
    });
}

test "compliance: @TypeOf on int arith result is comptime_int" {
    try expectMatchesZig(testing.allocator, &.{"@TypeOf(1 + 2)"});
}

test "compliance: @TypeOf on peer-resolved int arith" {
    try expectMatchesZig(testing.allocator, &.{"@TypeOf(@as(u8, 1) + @as(u16, 2))"});
}

test "compliance: @TypeOf on bare float literal is comptime_float" {
    try expectMatchesZig(testing.allocator, &.{"@TypeOf(1.5)"});
}

test "compliance: @TypeOf on typed float" {
    try expectMatchesZig(testing.allocator, &.{"@TypeOf(@as(f32, 1.5))"});
}

test "compliance: @TypeOf on bool short-circuit yields bool" {
    try expectMatchesZig(testing.allocator, &.{"@TypeOf(true and false)"});
}

test "compliance: @TypeOf on if-as-value picks branch type" {
    try expectMatchesZig(testing.allocator, &.{"@TypeOf(if (true) @as(u32, 1) else @as(u32, 0))"});
}

test "compliance: @TypeOf on empty block is void" {
    try expectMatchesZig(testing.allocator, &.{"@TypeOf({})"});
}

test "compliance: @TypeOf on coerced error union" {
    try expectMatchesZig(testing.allocator, &.{
        "const E = error{Bad, Worse};",
        "@TypeOf(@as(E!u32, 0))",
    });
}

test "compliance: @TypeOf on switch result is the case type" {
    try expectMatchesZig(testing.allocator, &.{"@TypeOf(switch (1) { 0 => @as(u8, 10), else => @as(u8, 20) })"});
}

test "compliance: same-input fn call" {
    try expectMatchesZig(testing.allocator, &.{
        "fn double(x: u32) u32 { return x + x; } const r = double(7);",
        "r",
    });
}

test "compliance: same-input multi-arg fn call" {
    try expectMatchesZig(testing.allocator, &.{
        "fn add(a: u32, b: u32) u32 { return a + b; } const r = add(3, 4);",
        "r",
    });
}

test "compliance: same-input recursive fn (factorial)" {
    try expectMatchesZig(testing.allocator, &.{
        "fn fact(n: u32) u32 { return if (n == 0) 1 else n * fact(n - 1); } const r = fact(5);",
        "r",
    });
}

test "compliance: same-input nested call" {
    try expectMatchesZig(testing.allocator, &.{
        "fn d(x: u32) u32 { return x + x; } const r = d(d(5));",
        "r",
    });
}

test "compliance: cross-line fn call" {
    try expectMatchesZig(testing.allocator, &.{
        "fn id(x: u32) u32 { return x; }",
        "id(42)",
    });
}

test "compliance: cross-line recursive fib(10)" {
    try expectMatchesZig(testing.allocator, &.{
        "fn fib(n: u32) u32 { return if (n < 2) n else fib(n - 1) + fib(n - 2); }",
        "fib(10)",
    });
}

test "compliance: cross-line multi-arg fn" {
    try expectMatchesZig(testing.allocator, &.{
        "fn add(a: u32, b: u32) u32 { return a + b; }",
        "add(3, 4)",
    });
}

test "compliance: defer runs at block exit after subsequent assignments" {
    try expectMatchesZig(testing.allocator, &.{
        "fn run() u32 { var s: u32 = 0; { defer s = 1; s = 2; } return s; }",
        "run()",
    });
}

test "compliance: nested defers fire LIFO" {
    try expectMatchesZig(testing.allocator, &.{
        "fn run() u32 { var t: u32 = 1; { defer t = t * 2; defer t = t + 10; } return t; }",
        "run()",
    });
}

test "compliance: defer reads live state at scope exit, not at declaration" {
    try expectMatchesZig(testing.allocator, &.{
        "fn run() u32 { var x: u32 = 5; { defer x = x * 100; x = 7; } return x; }",
        "run()",
    });
}

test "compliance: array literal index (elems storage)" {
    try expectMatchesZig(testing.allocator, &.{
        "const a = [_]i32{1, 2, 3};",
        "a[1]",
    });
}

test "compliance: array literal index (repeated_elem storage)" {
    try expectMatchesZig(testing.allocator, &.{
        "const a = [_]u32{7, 7, 7};",
        "a[2]",
    });
}

test "compliance: array aggregate renders as brace list" {
    try expectMatchesZig(testing.allocator, &.{"[_]i32{1, 2, 3}"});
}

test "compliance: array type renders" {
    try expectMatchesZig(testing.allocator, &.{"[3]i32"});
}

test "compliance: tuple literal renders with a leading dot" {
    try expectMatchesZig(testing.allocator, &.{".{1, 2, 3}"});
    try expectMatchesZig(testing.allocator, &.{".{1, 2.5, 3}"});
}

test "compliance: tuple index" {
    try expectMatchesZig(testing.allocator, &.{".{1, 2.5}[1]"});
    try expectMatchesZig(testing.allocator, &.{
        "const t = .{ 1, 2.5, 3 };",
        "t[0]",
    });
}

test "compliance: prior decl used as a tuple element" {
    try expectMatchesZig(testing.allocator, &.{
        "const x = 7;",
        ".{ x, 2.5 }",
    });
    try expectMatchesZig(testing.allocator, &.{
        "const y = 9;",
        "const t = .{ y, 2.5 };",
        "t[0]",
    });
}

test "compliance: void renders as `void`, including as a tuple element" {
    try expectMatchesZig(testing.allocator, &.{"{}"});
    try expectMatchesZig(testing.allocator, &.{".{ 1, {} }"});
}

test "compliance: void does not coerce to a non-void type, nor the reverse" {
    try expectBothReject(testing.allocator, &.{"@as(i32, {})"});
    try expectBothReject(testing.allocator, &.{"@as(void, 5)"});
}

test "compliance: an explicit tuple type renders structurally" {
    try expectMatchesZig(testing.allocator, &.{
        "const T = struct { i32, f128 };",
        "T",
    });
    try expectMatchesZig(testing.allocator, &.{"struct { i32, void }"});
}

test "compliance: a typed tuple literal coerces elements to the field types" {
    // Non-integral float so the rendered form has no trailing `.0` for
    // `normalize` to reconcile mid-string (see renderFloat's note).
    try expectMatchesZig(testing.allocator, &.{
        "const x: struct { i32, f128, void } = .{ 420, 2.5, {} };",
        "x",
    });
}

test "compliance: tuple element type and arity mismatches are rejected" {
    // void into a non-void field, and a non-void value into a void field.
    try expectBothReject(testing.allocator, &.{"const x: struct { i32 } = .{ {} };"});
    try expectBothReject(testing.allocator, &.{"const x: struct { void } = .{ 420 };"});
    // Too few / too many initializers for the field count.
    try expectBothReject(testing.allocator, &.{"const x: struct { i32, f128 } = .{ 1 };"});
    try expectBothReject(testing.allocator, &.{"const x: struct { i32 } = .{ 1, 2 };"});
}

test "mixed input: declarations then a trailing expression on one line" {
    // `zig run` can't wrap a compound line as a print argument, so this
    // is REPL-only: the line runs as two passes (bind, then evaluate).
    const out = try runViaRepl(testing.allocator, &.{"const mx = 10; mx + 1"});
    defer testing.allocator.free(out);
    try testing.expectEqualStrings("11", out);
}

test "mixed input: a declaration from a compound line persists to later input" {
    const out = try runViaRepl(testing.allocator, &.{ "const mz = 5; mz", "mz * 2" });
    defer testing.allocator.free(out);
    try testing.expectEqualStrings("10", out);
}

test "named struct renders with the session-qualified `repl.` prefix" {
    // End-to-end render coverage. The type's structure (it is a
    // `struct_type` named `repl.P`, distinct per declaration) is asserted
    // on the interned Key in sema_eval_test; a build-specific qualified
    // name has no portable `zig run` form to compare against here.
    const out = try runViaRepl(testing.allocator, &.{ "const P = struct { x: i32 };", "P" });
    defer testing.allocator.free(out);
    try testing.expectEqualStrings("repl.P", out);
}

// Non-power-of-two widths reach the `int_type` handler rather than a
// well-known Inst.Ref -- the path the round-number widths never hit.
const awkward_widths = [_]u16{ 1, 3, 7, 33, 69, 420 };

test "compliance: array index across awkward integer widths" {
    // {1, 0, 1} fits every width >= 1, so one template serves all.
    inline for (awkward_widths) |bits| {
        const decl = std.fmt.comptimePrint("const a = [_]u{d}{{1, 0, 1}};", .{bits});
        try expectMatchesZig(testing.allocator, &.{ decl, "a[0]" });
    }
}

test "compliance: array type renders across awkward integer widths" {
    inline for (awkward_widths) |bits| {
        const src = std.fmt.comptimePrint("[3]u{d}", .{bits});
        try expectMatchesZig(testing.allocator, &.{src});
    }
}

// Targeted value round-trips the uniform sweep can't express: large
// positive values at a wide width, and negatives at a wide signed
// width.
test "compliance: wide-width values round-trip (u69 large, i420 negative)" {
    try expectMatchesZig(testing.allocator, &.{
        "const a = [_]u69{100, 200, 300};",
        "a[2]",
    });
    try expectMatchesZig(testing.allocator, &.{
        "const a = [_]i420{-123456789, 0, 1};",
        "a[0]",
    });
}

test "compliance: vector type renders across element kinds" {
    try expectMatchesZig(testing.allocator, &.{"@Vector(4, i32)"});
    try expectMatchesZig(testing.allocator, &.{"@Vector(2, f32)"});
    try expectMatchesZig(testing.allocator, &.{"@Vector(8, bool)"});
    try expectMatchesZig(testing.allocator, &.{"@Vector(3, *const u8)"});
}

test "compliance: vector type renders across awkward element widths" {
    inline for (awkward_widths) |bits| {
        const src = std.fmt.comptimePrint("@Vector(7, u{d})", .{bits});
        try expectMatchesZig(testing.allocator, &.{src});
    }
}

test "compliance: pointer to aggregate renders (vector / array as a pointer child)" {
    try expectMatchesZig(testing.allocator, &.{"*@Vector(4, i32)"});
    try expectMatchesZig(testing.allocator, &.{"*[3]i32"});
}

test "compliance: optional type renders across child kinds" {
    try expectMatchesZig(testing.allocator, &.{"?i32"});
    try expectMatchesZig(testing.allocator, &.{"?*const u8"});
    try expectMatchesZig(testing.allocator, &.{"?@Vector(4, i32)"});
}

test "compliance: optional values (payload, null, unwrap)" {
    try expectMatchesZig(testing.allocator, &.{"@as(?i32, 5)"});
    try expectMatchesZig(testing.allocator, &.{"@as(?i32, null)"});
    try expectMatchesZig(testing.allocator, &.{"@as(?i32, 5).?"});
    // var must be mutated or zig rejects it ("never mutated"); the
    // store-through path coerces 6 into the ?i32 slot, then .? unwraps.
    try expectMatchesZig(testing.allocator, &.{"blk: { var x: ?i32 = 5; x = 6; break :blk x.?; }"});
}

test "compliance: unwrapping a comptime-known null is rejected by both" {
    try expectBothReject(testing.allocator, &.{"@as(?i32, null).?"});
}

test "compliance: optional across awkward payload widths" {
    inline for (awkward_widths) |bits| {
        const decl = std.fmt.comptimePrint("@as(?u{d}, 1)", .{bits});
        try expectMatchesZig(testing.allocator, &.{decl});
    }
}
