//! Compliance harness -- runs each expression through both our REPL and
//! a freshly-spawned `zig run` on the same source, normalises both
//! outputs, and asserts they match. This proves spec compliance for
//! the expressions we list here at the test-runner level.

const std = @import("std");
const testing = std.testing;
const Io = std.Io;

const eval = @import("eval.zig");
const Session = @import("Session.zig");
const InternPool = @import("sema/InternPool.zig");
const Value = @import("sema/Value.zig");
const render = @import("render/Value.zig");

// Shared across cases; sits under .zig-cache so `zig build` cleans it.
const compliance_cache_dir = ".zig-cache/tmp/zig-repl-compliance";

/// Run a sequence of REPL inputs through the shared `eval.run` driver --
/// the same path the interactive REPL takes -- against a fresh session.
/// The last input must produce a Value; prior inputs typically bind decls
/// the last expression references. Returns the rendered text of the final
/// value with the trailing newline stripped. Parse/ZIR/analysis errors
/// propagate as the tags `expectBothReject` matches; their diagnostics go
/// to a discarded allocating writer (so a long rendering can't overflow).
fn runViaRepl(
    gpa: std.mem.Allocator,
    inputs: []const []const u8,
) ![]u8 {
    assert(inputs.len >= 1);

    var pool = try InternPool.init(gpa);
    defer pool.deinit();
    const ns = try pool.createNamespace(gpa, .none);

    var session = Session.init(gpa, &pool, ns);
    defer session.deinit();

    var diag: std.Io.Writer.Allocating = .init(gpa);
    defer diag.deinit();

    var last_value: ?Value = null;
    for (inputs) |source| {
        last_value = (try eval.run(&session, source, &diag.writer)).value;
    }

    const value = last_value orelse return error.NoValue;
    var out_buf: [4096]u8 = undefined;
    var out_writer = Io.Writer.fixed(&out_buf);
    try render.render(value, &pool, &out_writer);

    const raw = out_writer.buffered();
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

/// Run `inputs` through the REPL, expect rejection, and assert the emitted
/// diagnostic contains `needle`. Unlike `expectBothReject`, this pins the REPL's
/// own wording so a message regression is caught. It is not compared to `zig`'s
/// text (whose type names differ); `needle` is the compiler-aligned phrasing the
/// message is expected to carry.
fn expectReplDiagnostic(gpa: std.mem.Allocator, inputs: []const []const u8, needle: []const u8) !void {
    var pool = try InternPool.init(gpa);
    defer pool.deinit();
    const ns = try pool.createNamespace(gpa, .none);
    var session = Session.init(gpa, &pool, ns);
    defer session.deinit();

    var diag: std.Io.Writer.Allocating = .init(gpa);
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
    try testing.expect(rejected);
    if (std.mem.indexOf(u8, diag.written(), needle) == null) {
        std.debug.print("diagnostic did not contain '{s}':\n{s}\n", .{ needle, diag.written() });
        return error.TestDiagnosticMismatch;
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

test "compliance: aligned pointer types render as Zig prints" {
    // An explicit `align(N)` prints verbatim -- even when N equals the
    // pointee's natural alignment, Zig does not fold it away.
    const a = testing.allocator;
    try expectMatchesZig(a, &.{"*align(4) u8"});
    try expectMatchesZig(a, &.{"*align(16) u32"});
    try expectMatchesZig(a, &.{"*align(8) const u32"}); // align prints before const
    try expectMatchesZig(a, &.{"[]align(2) i16"}); // slice carries alignment
    try expectMatchesZig(a, &.{"*align(1) u8"}); // natural alignment still printed
}

test "compliance: @alignOf matches the host target ABI" {
    // `@alignOf` resolves the host ABI alignment (the target `zig run` uses
    // with no `-target`). `@alignOf` of a pointer is the pointer's own
    // alignment, not the pointee's. A comptime-only type is accepted (yields
    // 1), unlike `@sizeOf`.
    const a = testing.allocator;
    for ([_][]const u8{
        "@alignOf(u8)",  "@alignOf(u32)",  "@alignOf(u64)",           "@alignOf(u128)",
        "@alignOf(i7)",  "@alignOf(bool)", "@alignOf(usize)",         "@alignOf(f32)",
        "@alignOf(f64)", "@alignOf(*u8)",  "@alignOf(*align(16) u8)", "@alignOf(comptime_int)",
    }) |expr| try expectMatchesZig(a, &.{expr});
}

test "compliance: @sizeOf matches the host target ABI" {
    const a = testing.allocator;
    for ([_][]const u8{
        "@sizeOf(u8)",   "@sizeOf(u32)",  "@sizeOf(u64)",    "@sizeOf(f16)",
        "@sizeOf(void)", "@sizeOf([]u8)", "@sizeOf([4]u16)", "@sizeOf(usize)",
    }) |expr| try expectMatchesZig(a, &.{expr});
    // A comptime-only type and an uninstantiable type have no size on either side.
    try expectBothReject(a, &.{"@sizeOf(comptime_int)"});
    try expectBothReject(a, &.{"@sizeOf(noreturn)"});
}

test "compliance: &decl carries the binding's constness and alignment" {
    // `&x` types as the binding's own pointer: mutable for `var`, const for
    // `const`, with the declared `align(N)`. A bare `var` is `*T` (not the
    // `*const T` an address-of-temporary produces).
    const a = testing.allocator;
    try expectMatchesZig(a, &.{ "var x: u32 = 5;", "@TypeOf(&x)" }); // var -> *u32
    try expectMatchesZig(a, &.{ "const z: u32 = 5;", "@TypeOf(&z)" }); // const -> *const u32
    try expectMatchesZig(a, &.{ "var w: u32 align(4) = 5;", "@TypeOf(&w)" }); // var + align
    try expectMatchesZig(a, &.{ "const c: u8 align(16) = 1;", "@TypeOf(&c)" }); // const + align
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

test "compliance: store through a pointer mutates the pointee" {
    try expectMatchesZig(testing.allocator, &.{"blk: { var y: u32 = 1; const p = &y; p.* = 5; break :blk y; }"});
}

test "compliance: load through a pointer reads the current value" {
    try expectMatchesZig(testing.allocator, &.{"blk: { var y: u32 = 1; const p = &y; p.* = 9; break :blk p.*; }"});
}

test "compliance: read-modify-write through a pointer" {
    try expectMatchesZig(testing.allocator, &.{"blk: { var y: i32 = 10; const p = &y; p.* = p.* - 3; break :blk y; }"});
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

test "compliance: type and bool equality compare by identity" {
    const a = testing.allocator;
    // Types compare by interned identity (the compiler's Type.eql); only ==/!=.
    try expectMatchesZig(a, &.{"u8 == u8"});
    try expectMatchesZig(a, &.{"u8 == u16"});
    try expectMatchesZig(a, &.{"u8 != u16"});
    try expectMatchesZig(a, &.{"blk: { const x: u8 = 1; const y: u8 = 2; break :blk @TypeOf(x) == @TypeOf(y); }"});
    try expectMatchesZig(a, &.{"blk: { const x: u8 = 1; const y: u16 = 2; break :blk @TypeOf(x) == @TypeOf(y); }"});
    // Bools compare the same way.
    try expectMatchesZig(a, &.{"true == false"});
    try expectMatchesZig(a, &.{"blk: { const b = true; break :blk b != false; }"});
    // Ordering on types is a compile error on both sides.
    try expectBothReject(a, &.{"blk: { break :blk u8 < u16; }"});
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

test "pointer to a named struct resolves the struct as its child type" {
    // Regression guard for the `Key.isType` consolidation: `*P` routes the
    // struct type through `resolveDestType`, which previously rejected
    // `struct_type` as "not a type".
    const out = try runViaRepl(testing.allocator, &.{ "const P = struct { x: i32 };", "*P" });
    defer testing.allocator.free(out);
    try testing.expectEqualStrings("*repl.P", out);
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

test "compliance: optional null test drives if-capture and orelse" {
    // `if (opt) |v|` and `orelse` both lower to `is_non_null` -> `condbr`.
    try expectMatchesZig(testing.allocator, &.{"blk: { const x: ?u32 = 7; break :blk if (x) |v| v else 0; }"});
    try expectMatchesZig(testing.allocator, &.{"blk: { const x: ?u32 = null; break :blk if (x) |v| v else 42; }"});
    try expectMatchesZig(testing.allocator, &.{"blk: { const x: ?u32 = null; break :blk x orelse 99; }"});
    try expectMatchesZig(testing.allocator, &.{"blk: { const x: ?u32 = 7; break :blk x orelse 99; }"});
}

test "compliance: if-capture on a non-optional is rejected by both" {
    try expectBothReject(testing.allocator, &.{"blk: { const n: u32 = 5; break :blk if (n) |v| v else 0; }"});
}

test "compliance: optional across awkward payload widths" {
    inline for (awkward_widths) |bits| {
        const decl = std.fmt.comptimePrint("@as(?u{d}, 1)", .{bits});
        try expectMatchesZig(testing.allocator, &.{decl});
    }
}

test "compliance: a comptime-known int coerces to a fixed-width int when it fits" {
    // The operand is comptime-known, so the value-fits rule applies on both
    // sides: a wider/in-range target accepts, an out-of-range one is rejected.
    try expectMatchesZig(testing.allocator, &.{"@as(i64, @as(u32, 42))"});
    try expectMatchesZig(testing.allocator, &.{"@as(i32, @as(u8, 200))"});
    try expectBothReject(testing.allocator, &.{"@as(i8, @as(u32, 200))"});
    try expectBothReject(testing.allocator, &.{"@as(u16, @as(u32, 70000))"});
}

test "compliance: a function return coerces to the declared return type" {
    // A comptime-known return coerces value-based; a runtime (param-derived)
    // return coerces type-based -- a widening succeeds, a type that can't
    // represent the source is rejected -- each matching the compiler.
    try expectMatchesZig(testing.allocator, &.{ "fn five() i32 { return 5; }", "five()" });
    try expectMatchesZig(testing.allocator, &.{ "fn widen(a: u8) u32 { return a; }", "widen(7)" });
    try expectBothReject(testing.allocator, &.{ "fn small() u8 { return 300; }", "small()" });
    try expectBothReject(testing.allocator, &.{ "fn id(a: u32) i32 { return a; }", "id(7)" });
    try expectBothReject(testing.allocator, &.{ "fn add(a: u32, b: u32) i32 { return a + b; }", "add(40, 2)" });
}

test "compliance: runtime-ness propagates through operations" {
    // A value derived from a runtime parameter stays runtime through each kind
    // of operation, so coercing it to a type that can't represent its source
    // type is rejected (as the compiler rejects the body); a widening passes.
    const a = testing.allocator;
    try expectBothReject(a, &.{ "fn f(x: u32) i32 { return x & 1; }", "f(7)" }); // bitwise
    try expectBothReject(a, &.{ "fn f(x: u32) i32 { return x << 1; }", "f(7)" }); // shift
    try expectBothReject(a, &.{ "fn f(x: i32) i16 { return -x; }", "f(7)" }); // negate
    try expectBothReject(a, &.{ "fn f(x: u8) i32 { return @as(u32, x); }", "f(7)" }); // coercion result stays runtime
    try expectBothReject(a, &.{ "fn f(x: u32) i32 { return blk: { break :blk x; }; }", "f(7)" }); // compound passes it through

    try expectMatchesZig(a, &.{ "fn f(x: u8) u32 { return x & 1; }", "f(7)" }); // widening through an op
    try expectMatchesZig(a, &.{ "fn f(x: u8) u32 { return blk: { break :blk x; }; }", "f(7)" }); // compound keeps comptime/runtime intact
}

test "compliance: runtime float coercion is type-based" {
    const a = testing.allocator;
    try expectBothReject(a, &.{ "fn f(x: f64) f32 { return x; }", "f(1.5)" }); // narrowing
    try expectBothReject(a, &.{ "fn f(x: u32) f32 { return x; }", "f(5)" }); // runtime int -> float
    try expectMatchesZig(a, &.{ "fn f(x: f32) f64 { return x; }", "f(1.5)" }); // widening
}

test "compliance: a generic return type resolves per instantiation" {
    // `fn make(comptime T: type) T`: the return type is unknown at definition
    // (poison) and re-resolves to the comptime argument when the call binds it,
    // so the body's return coerces against the concrete type of that call.
    const a = testing.allocator;
    const make = "fn make(comptime T: type) T { return 300; }";
    try expectMatchesZig(a, &.{ make, "make(u16)" }); // 300 fits u16
    try expectMatchesZig(a, &.{ make, "@TypeOf(make(u16))" }); // instantiated type, not poison
    try expectBothReject(a, &.{ make, "make(u8)" }); // 300 does not fit u8
}

test "compliance: a generic return body computes through arithmetic and @as" {
    const a = testing.allocator;
    try expectMatchesZig(a, &.{ "fn make(comptime T: type) T { return 1 + 2; }", "make(u8)" });
    try expectMatchesZig(a, &.{ "fn make(comptime T: type) T { return @as(T, 7) * 2; }", "make(u8)" });
}

test "compliance: a generic return body assigns and mutates a T-typed local" {
    const a = testing.allocator;
    try expectMatchesZig(a, &.{ "fn make(comptime T: type) T { var x: T = 10; x = x + 5; return x; }", "make(u8)" });
    try expectMatchesZig(a, &.{ "fn make(comptime T: type) T { const n: T = 3; return n; }", "make(i32)" });
}

test "compliance: a generic return coerces a runtime value type-based" {
    // A runtime (concrete-param-derived) value returned through a generic type
    // coerces against the re-resolved type *type-based*, not value-based: the
    // narrowing is rejected even when the value would fit, exactly as the
    // runtime-coercion path rejects a non-generic narrowing.
    const a = testing.allocator;
    const make = "fn make(comptime T: type, x: u16) T { return x; }";
    try expectMatchesZig(a, &.{ make, "make(u16, 300)" }); // same width, passes
    try expectBothReject(a, &.{ make, "make(u8, 5)" }); // narrowing rejected though 5 fits u8
}

test "compliance: a generic parameter type resolves per instantiation" {
    const a = testing.allocator;
    const id = "fn id(comptime T: type, x: T) T { return x; }";
    try expectMatchesZig(a, &.{ id, "id(u8, 5)" });
    try expectMatchesZig(a, &.{ id, "id(i32, -7)" });
    try expectMatchesZig(a, &.{ id, "@TypeOf(id(u16, 1))" }); // instantiated param type, not poison
    try expectBothReject(a, &.{ id, "id(u8, 300)" }); // 300 does not fit u8
}

test "compliance: generic and concrete parameters mix in one signature" {
    const a = testing.allocator;
    try expectMatchesZig(a, &.{ "fn add(comptime T: type, x: T, y: T) T { return x + y; }", "add(u16, 40, 2)" });
    try expectMatchesZig(a, &.{ "fn f(comptime T: type, x: T, y: u8) T { return x + y; }", "f(u16, 40, 2)" });
}

test "compliance: an anytype parameter takes the argument's type per call" {
    const a = testing.allocator;
    const dbl = "fn dbl(x: anytype) @TypeOf(x) { return x + x; }";
    try expectMatchesZig(a, &.{ dbl, "dbl(21)" }); // comptime_int
    try expectMatchesZig(a, &.{ dbl, "dbl(@as(u8, 100))" }); // u8, no overflow
    try expectMatchesZig(a, &.{ dbl, "@TypeOf(dbl(@as(u16, 3)))" }); // instantiated type
    try expectMatchesZig(a, &.{ "fn add(x: anytype, y: anytype) @TypeOf(x) { return x + y; }", "add(@as(u8, 40), @as(u8, 2))" });
}

test "compliance: an anytype generic dispatches over the argument type (math.order-style)" {
    // Models std.math.order: one anytype comparison generic, instantiated over
    // comptime_int and float arguments.
    const a = testing.allocator;
    const cmp = "fn cmp(a: anytype, b: anytype) i8 { return if (a < b) -1 else if (a > b) 1 else 0; }";
    try expectMatchesZig(a, &.{ cmp, "cmp(3, 7)" });
    try expectMatchesZig(a, &.{ cmp, "cmp(9, 4)" });
    try expectMatchesZig(a, &.{ cmp, "cmp(5, 5)" });
    try expectMatchesZig(a, &.{ cmp, "cmp(@as(f64, 1.5), @as(f64, 2.5))" });
}

test "compliance: anytype params over comptime, fixed-width, and multi-statement bodies" {
    const a = testing.allocator;
    try expectMatchesZig(a, &.{ "fn tw(comptime x: anytype) @TypeOf(x) { return x + x; }", "tw(21)" });
    try expectMatchesZig(a, &.{ "fn sq(x: anytype) @TypeOf(x) { const y = x * x; return y; }", "sq(@as(u8, 9))" });
}

test "compliance: multi-arg @TypeOf peer-resolves the operand types" {
    const a = testing.allocator;
    try expectMatchesZig(a, &.{"@TypeOf(1, 2, 3)"}); // all comptime_int
    try expectMatchesZig(a, &.{"@TypeOf(@as(u8, 1), @as(u16, 2))"}); // wider int wins
    try expectMatchesZig(a, &.{"@TypeOf(@as(f32, 1), @as(f64, 2))"}); // wider float wins
    try expectMatchesZig(a, &.{"@TypeOf(1, @as(f32, 2))"}); // comptime_int coerces to the float
    try expectBothReject(a, &.{"@TypeOf(@as(i32, 5), 1.5)"}); // fixed int + comptime_float has no peer
}

test "compliance: std.math.clamp-style anytype generic with @TypeOf(v, lo, hi)" {
    // The real std.math.clamp signature: three anytype params peer-resolved for
    // the return type, dispatched by comparison.
    const a = testing.allocator;
    const clamp = "fn clamp(v: anytype, lo: anytype, hi: anytype) @TypeOf(v, lo, hi) { return if (v < lo) lo else if (v > hi) hi else v; }";
    try expectMatchesZig(a, &.{ clamp, "clamp(5, 0, 10)" });
    try expectMatchesZig(a, &.{ clamp, "clamp(15, 0, 10)" });
    try expectMatchesZig(a, &.{ clamp, "clamp(@as(i32, -5), @as(i32, 0), @as(i32, 10))" });
    try expectMatchesZig(a, &.{ clamp, "clamp(@as(f64, 1.5), @as(f64, 0.0), @as(f64, 1.0))" });
}

test "compliance: the % operator" {
    const a = testing.allocator;
    try expectMatchesZig(a, &.{"17 % 8"}); // comptime_int
    try expectMatchesZig(a, &.{"@as(u32, 17) % @as(u32, 8)"}); // fixed-width unsigned
    try expectMatchesZig(a, &.{"@as(i32, 7) % @as(i32, 3)"}); // signed but non-negative
    try expectMatchesZig(a, &.{"@as(f64, 5.5) % @as(f64, 2.0)"}); // float remainder
    try expectMatchesZig(a, &.{"@as(i32, -9) % @as(i32, 3)"}); // negative but zero remainder is allowed
    try expectBothReject(a, &.{"@as(i32, -7) % @as(i32, 3)"}); // negative + nonzero -> use @rem/@mod
    try expectBothReject(a, &.{"@as(f64, -9.5) % @as(f64, 2.0)"}); // same rule governs floats
}

test "compliance: compound assignment" {
    const a = testing.allocator;
    try expectMatchesZig(a, &.{"blk: { var s: u32 = 5; s += 1; break :blk s; }"});
    try expectMatchesZig(a, &.{"blk: { var s: i32 = 5; s -= 8; break :blk s; }"});
    try expectMatchesZig(a, &.{"blk: { var s: u32 = 5; s *= 3; break :blk s; }"});
    try expectMatchesZig(a, &.{"blk: { var s: u32 = 9; s /= 2; break :blk s; }"});
    try expectMatchesZig(a, &.{"blk: { var i: u32 = 0; while (i < 5) : (i += 1) {} break :blk i; }"});
}

test "compliance: struct init and field access" {
    const a = testing.allocator;
    const P = "const P = struct { a: u8, b: u16 };";
    // Out-of-order init must resolve fields by name, not position.
    try expectMatchesZig(a, &.{"blk: { " ++ P ++ " const p: P = .{ .b = 8, .a = 7 }; break :blk p.a; }"});
    try expectMatchesZig(a, &.{"blk: { " ++ P ++ " const p: P = .{ .b = 8, .a = 7 }; break :blk p.b; }"});
    // Field values carry their declared type into arithmetic.
    try expectMatchesZig(a, &.{"blk: { const Q = struct { x: u32, y: u32 }; const q: Q = .{ .x = 10, .y = 32 }; break :blk q.x + q.y; }"});
    try expectMatchesZig(a, &.{"blk: { const R = struct { a: u8 }; const r: R = .{ .a = 250 }; break :blk r.a + 5; }"});
}

test "compliance: a struct type exposes its member declarations (P.decl)" {
    const a = testing.allocator;
    const F = "const P = struct { fn id(v: u8) u8 { return v; } };";
    try expectMatchesZig(a, &.{"blk: { " ++ F ++ " break :blk @TypeOf(P.id); }"}); // fn decl
    const K = "const P = struct { const K: u8 = 5; };";
    try expectMatchesZig(a, &.{"blk: { " ++ K ++ " break :blk P.K; }"}); // value decl
    try expectMatchesZig(a, &.{"blk: { " ++ K ++ " break :blk P.K + 1; }"}); // carries its type
    // A chain through nested type declarations (S.A.y needs S.A as an addressable
    // type -- a namespace decl access on a type via field_ptr).
    try expectMatchesZig(a, &.{"blk: { const S = struct { const A = struct { const y: u8 = 5; }; }; break :blk S.A.y; }"});
    try expectMatchesZig(a, &.{"blk: { const S = struct { const A = struct { const B = struct { const z: u8 = 7; }; }; }; break :blk S.A.B.z; }"});
}

test "compliance: calling a struct's namespace declaration (P.decl(args))" {
    const a = testing.allocator;
    try expectMatchesZig(a, &.{"blk: { const P = struct { fn id(v: u8) u8 { return v; } }; break :blk P.id(7); }"});
    try expectMatchesZig(a, &.{"blk: { const P = struct { fn add(a: u8, b: u8) u8 { return a + b; } }; break :blk P.add(40, 2); }"});
    // A comptime-int argument coerces to the declared parameter type.
    try expectMatchesZig(a, &.{"blk: { const P = struct { fn sq(x: u16) u16 { return x * x; } }; break :blk P.sq(9); }"});
}

test "compliance: a struct value method binds the receiver (p.method())" {
    const a = testing.allocator;
    const G = "const P = struct { x: u8, fn get(self: @This()) u8 { return self.x; } };";
    try expectMatchesZig(a, &.{"blk: { " ++ G ++ " const p: P = .{ .x = 9 }; break :blk p.get(); }"});
    // A method with an explicit argument beyond the bound receiver.
    const A = "const P = struct { x: u8, fn addk(self: @This(), k: u8) u8 { return self.x + k; } };";
    try expectMatchesZig(a, &.{"blk: { " ++ A ++ " const p: P = .{ .x = 10 }; break :blk p.addk(5); }"});
}

test "compliance: methods compose -- call each other and take struct args" {
    const a = testing.allocator;
    // A method calling another method on the receiver, chained three deep.
    const V = "const V = struct { n: u8, fn base(self: @This()) u8 { return self.n; } fn p1(self: @This()) u8 { return self.base() + 1; } fn p2(self: @This()) u8 { return self.p1() + 1; } };";
    try expectMatchesZig(a, &.{"blk: { " ++ V ++ " const v: V = .{ .n = 40 }; break :blk v.p2(); }"});
    // A method taking another value of the same struct: a 2D dot product.
    const Vec = "const Vec = struct { x: u8, y: u8, fn dot(self: @This(), o: @This()) u8 { return self.x * o.x + self.y * o.y; } };";
    try expectMatchesZig(a, &.{"blk: { " ++ Vec ++ " const p: Vec = .{ .x = 2, .y = 3 }; const q: Vec = .{ .x = 4, .y = 5 }; break :blk p.dot(q); }"});
}

test "compliance: a body resolves a bare sibling declaration in its container" {
    // A member body naming a sibling by bare identifier (no `Self.`/`self.`)
    // resolves it in the enclosing container, matching the compiler's
    // innermost-first `lookupIdentifier` over the namespace chain.
    const a = testing.allocator;
    // Method body -> sibling static decl.
    const S = "const S = struct { a: u8, b: u8, fn sum2(x: u8, y: u8) u8 { return x + y; } fn total(self: @This()) u8 { return sum2(self.a, self.b); } };";
    try expectMatchesZig(a, &.{"blk: { " ++ S ++ " const s: S = .{ .a = 20, .b = 22 }; break :blk s.total(); }"});
    // Static decl body -> sibling static decl.
    const P = "const P = struct { fn a() u8 { return 7; } fn b() u8 { return a() + 1; } };";
    try expectMatchesZig(a, &.{"blk: { " ++ P ++ " break :blk P.b(); }"});
}

test "compliance: a nested container resolves an enclosing container's decl" {
    // An unqualified identifier in a nested container walks outward to the
    // enclosing container (the compiler's namespace parent chain), not just the
    // innermost container + session.
    const a = testing.allocator;
    // Field default referencing the parent container's decl.
    try expectMatchesZig(a, &.{"blk: { const S = struct { const x: u8 = 9; const A = struct { const y: u8 = x; }; }; break :blk S.A.y; }"});
    // Method in a nested container referencing a grandparent decl.
    try expectMatchesZig(a, &.{"blk: { const Outer = struct { const shared: u8 = 42; const Inner = struct { fn get() u8 { return shared; } }; }; break :blk Outer.Inner.get(); }"});
    // A struct returned from a method referencing the method's container decl.
    try expectMatchesZig(a, &.{"blk: { const S = struct { const k: u8 = 5; fn mk() type { return struct { const v: u8 = k; }; } }; break :blk S.mk().v; }"});
}

test "compliance: declaration and field access do not cross" {
    // A declaration is reachable through the type, a field through a value --
    // never the other way (mirrors the compiler's fieldVal split).
    const a = testing.allocator;
    try expectBothReject(a, &.{"blk: { const P = struct { fn id(v: u8) u8 { return v; } }; break :blk P.nope; }"}); // no such decl
    try expectBothReject(a, &.{"blk: { const P = struct { x: u8 }; break :blk P.x; }"}); // field via type
    try expectBothReject(a, &.{"blk: { const P = struct { x: u8, fn id(v: u8) u8 { return v; } }; const p: P = .{ .x = 1 }; break :blk p.id; }"}); // decl via value
}

test "compliance: struct field defaults and missing-field validation" {
    const a = testing.allocator;
    const P = "const P = struct { a: u8, b: u16 = 99 };";
    try expectMatchesZig(a, &.{"blk: { " ++ P ++ " const p: P = .{ .a = 7 }; break :blk p.b; }"}); // default fills b
    try expectMatchesZig(a, &.{"blk: { " ++ P ++ " const p: P = .{ .a = 7, .b = 5 }; break :blk p.b; }"}); // explicit overrides
    // A field with no default left out is a compile error on both sides.
    try expectBothReject(a, &.{"blk: { const Q = struct { a: u8, b: u16 }; const q: Q = .{ .a = 7 }; break :blk q.a; }"});
}

test "compliance: @field reads a field by comptime-string name" {
    // `@field(obj, "name")` is the same read as `obj.name`, name from a string.
    const a = testing.allocator;
    const S = "const S = struct { x: u32, y: u8 };";
    try expectMatchesZig(a, &.{"blk: { " ++ S ++ " const s = S{ .x = 7, .y = 3 }; break :blk @field(s, \"x\"); }"}); // 7
    try expectMatchesZig(a, &.{"blk: { " ++ S ++ " const s = S{ .x = 7, .y = 3 }; break :blk @field(s, \"x\") + @field(s, \"y\"); }"}); // 10
    // On a union it reads the active field; on an enum type it names a tag.
    const U = "const U = union(enum) { a: u8, b: bool };";
    try expectMatchesZig(a, &.{"blk: { " ++ U ++ " const u = U{ .a = 5 }; break :blk @field(u, \"a\"); }"}); // 5
    try expectMatchesZig(a, &.{"blk: { const E = enum { north, south }; break :blk @field(E, \"south\") == E.south; }"}); // true
    // A slice's `len`/`ptr` and an array's `len` are reachable through @field too.
    try expectMatchesZig(a, &.{"blk: { const s: []const u8 = \"hello\"; break :blk @field(s, \"len\"); }"}); // 5
    try expectMatchesZig(a, &.{"blk: { const arr = [_]u8{ 1, 2, 3, 4 }; break :blk @field(arr, \"len\"); }"}); // 4
    // The pointer form: `&@field(...)` and `@field(...) = v` (an lvalue).
    try expectMatchesZig(a, &.{"blk: { " ++ S ++ " const s = S{ .x = 7, .y = 3 }; const p = &@field(s, \"x\"); break :blk p.*; }"}); // 7
    try expectMatchesZig(a, &.{"blk: { " ++ S ++ " var s = S{ .x = 1, .y = 2 }; @field(s, \"x\") = 9; break :blk s.x; }"}); // 9
    // The name may be any comptime `[]const u8`, not just a string literal.
    try expectMatchesZig(a, &.{"blk: { " ++ S ++ " const s = S{ .x = 7, .y = 3 }; const n: []const u8 = \"x\"; break :blk @field(s, n); }"}); // 7
    // Nested @field: the object of one @field is itself an @field result.
    const N = "const N = struct { inner: struct { x: u8 } };";
    try expectMatchesZig(a, &.{"blk: { " ++ N ++ " const s = N{ .inner = .{ .x = 3 } }; break :blk @field(@field(s, \"inner\"), \"x\"); }"}); // 3
    // Sad paths: a missing field name, reading an inactive union field, @field on
    // a non-aggregate, writing through a const, and a non-string name.
    try expectBothReject(a, &.{"blk: { " ++ S ++ " const s = S{ .x = 1, .y = 2 }; break :blk @field(s, \"z\"); }"});
    try expectBothReject(a, &.{"blk: { " ++ U ++ " const u = U{ .a = 5 }; break :blk @field(u, \"b\"); }"});
    try expectBothReject(a, &.{"blk: { const n: u32 = 5; break :blk @field(n, \"x\"); }"});
    try expectBothReject(a, &.{"blk: { " ++ S ++ " const s = S{ .x = 1, .y = 2 }; @field(s, \"x\") = 9; break :blk s.x; }"});
    try expectBothReject(a, &.{"blk: { " ++ S ++ " const s = S{ .x = 1, .y = 2 }; break :blk @field(s, 5); }"});
}

test "compliance: @hasField and @hasDecl" {
    const a = testing.allocator;
    // @hasField across the container kinds it supports.
    try expectMatchesZig(a, &.{"blk: { const S = struct { x: u32, y: bool }; break :blk @hasField(S, \"x\"); }"}); // true
    try expectMatchesZig(a, &.{"blk: { const S = struct { x: u32, y: bool }; break :blk @hasField(S, \"z\"); }"}); // false
    try expectMatchesZig(a, &.{"blk: { const U = union { a: u8, b: bool }; break :blk @hasField(U, \"b\"); }"}); // true
    try expectMatchesZig(a, &.{"blk: { const U = union(enum) { a: u8, b: bool }; break :blk @hasField(U, \"c\"); }"}); // false
    try expectMatchesZig(a, &.{"blk: { const E = enum { a, b }; break :blk @hasField(E, \"a\"); }"}); // true
    try expectMatchesZig(a, &.{"blk: { const E = enum { a, b }; break :blk @hasField(E, \"c\"); }"}); // false
    try expectMatchesZig(a, &.{"blk: { const Tup = struct { u32, u8 }; break :blk @hasField(Tup, \"1\"); }"}); // true
    try expectMatchesZig(a, &.{"blk: { const Tup = struct { u32, u8 }; break :blk @hasField(Tup, \"2\"); }"}); // false
    // A tuple field name must be a canonical unsigned index: non-numeric, a
    // leading zero, an underscore, or an out-of-range/overflowing value are false
    // (toUnsigned's rules).
    try expectMatchesZig(a, &.{"blk: { const Tup = struct { u32, u8 }; break :blk @hasField(Tup, \"a\"); }"}); // false
    try expectMatchesZig(a, &.{"blk: { const Tup = struct { u32, u8 }; break :blk @hasField(Tup, \"01\"); }"}); // false (leading zero)
    try expectMatchesZig(a, &.{"blk: { const Tup = struct { u32, u8 }; break :blk @hasField(Tup, \"1_0\"); }"}); // false (underscore)
    try expectMatchesZig(a, &.{"blk: { const Tup = struct { u32, u8 }; break :blk @hasField(Tup, \"9999999999999999999999999\"); }"}); // false (overflows)
    // A decl (not a field) is not a field: @hasField is false for a `pub const`.
    try expectMatchesZig(a, &.{"blk: { const S = struct { a: i32, pub const nope = 1; }; break :blk @hasField(S, \"nope\"); }"}); // false
    try expectMatchesZig(a, &.{"blk: { const U = union { a: u64, pub const nope = 1; }; break :blk @hasField(U, \"nope\"); }"}); // false
    try expectMatchesZig(a, &.{"blk: { const E = enum { a, pub const nope = 1; }; break :blk @hasField(E, \"nope\"); }"}); // false
    // The name may be any comptime `[]const u8`.
    try expectMatchesZig(a, &.{"blk: { const S = struct { xx: u8 }; const n: []const u8 = \"xx\"; break :blk @hasField(S, n); }"}); // true
    try expectMatchesZig(a, &.{"@hasField([3]u8, \"len\")"}); // true
    try expectMatchesZig(a, &.{"@hasField([3]u8, \"ptr\")"}); // false
    try expectMatchesZig(a, &.{"@hasField([]const u8, \"ptr\")"}); // true
    try expectMatchesZig(a, &.{"@hasField([]const u8, \"len\")"}); // true
    // @hasDecl checks the namespace; a value field is not a decl.
    try expectMatchesZig(a, &.{"blk: { const T = struct { x: u8, const K = 9; }; break :blk @hasDecl(T, \"K\"); }"}); // true
    try expectMatchesZig(a, &.{"blk: { const T = struct { x: u8, const K = 9; }; break :blk @hasDecl(T, \"x\"); }"}); // false (field, not decl)
    try expectMatchesZig(a, &.{"blk: { const T = struct { fn f() void {} }; break :blk @hasDecl(T, \"f\"); }"}); // true
    try expectMatchesZig(a, &.{"blk: { const T = struct { fn f() void {} }; break :blk @hasDecl(T, \"g\"); }"}); // false
    // A non-pub decl and a `pub var` are both visible to @hasDecl within a file.
    try expectMatchesZig(a, &.{"blk: { const B = struct { nope: i32, const hi = 1; }; break :blk @hasDecl(B, \"hi\"); }"}); // true
    try expectMatchesZig(a, &.{"blk: { const B = struct { nope: i32, pub var blah = 3; }; break :blk @hasDecl(B, \"blah\"); }"}); // true
    try expectMatchesZig(a, &.{"blk: { const B = struct { nope: i32, const hi = 1; }; break :blk @hasDecl(B, \"nope\"); }"}); // false (field)
    // @hasDecl also works on enum and union namespaces, and takes a []const u8 name.
    try expectMatchesZig(a, &.{"blk: { const E = enum { a, const N = 2; }; break :blk @hasDecl(E, \"N\"); }"}); // true
    try expectMatchesZig(a, &.{"blk: { const T = struct { const K = 9; }; const n: []const u8 = \"K\"; break :blk @hasDecl(T, n); }"}); // true
    // A nested container reached through a decl, and a decl that is itself a type.
    try expectMatchesZig(a, &.{"blk: { const O = struct { const I = struct { const K = 7; }; }; break :blk @hasDecl(O.I, \"K\"); }"}); // true
    try expectMatchesZig(a, &.{"blk: { const O = struct { const I = struct {}; }; break :blk @hasDecl(O, \"I\"); }"}); // true
    // Sad paths: @hasField on a fieldless type -- a non-slice pointer (unlike a
    // slice, not answerable), an optional, a vector, `void` -- all reject.
    try expectBothReject(a, &.{"@hasField(u32, \"x\")"});
    try expectBothReject(a, &.{"@hasField(*u32, \"x\")"});
    try expectBothReject(a, &.{"@hasField(?u32, \"x\")"});
    try expectBothReject(a, &.{"@hasField(@Vector(4, i32), \"x\")"});
    try expectBothReject(a, &.{"@hasField(void, \"x\")"});
    // @hasDecl on a non-container type (checkNamespaceType) rejects on both sides.
    try expectBothReject(a, &.{"@hasDecl(u32, \"x\")"});
    try expectBothReject(a, &.{"@hasDecl(bool, \"x\")"});
    try expectBothReject(a, &.{"@hasDecl([3]u8, \"x\")"});
    try expectBothReject(a, &.{"@hasDecl(?u32, \"x\")"});
}

test "compliance: explicit-type struct init (T{ ... })" {
    // The `T{ .a = ... }` form (struct_init) parallels the result-location
    // `.{ ... }` form: same defaults, same missing/unknown-field validation.
    const a = testing.allocator;
    const S = "const S = struct { a: u8, b: u8 };";
    try expectMatchesZig(a, &.{"blk: { " ++ S ++ " const s = S{ .a = 1, .b = 2 }; break :blk s.a + s.b; }"});
    // A defaulted field left out is filled; an explicit value overrides it.
    const D = "const D = struct { a: u8, b: u16 = 99 };";
    try expectMatchesZig(a, &.{"blk: { " ++ D ++ " const d = D{ .a = 7 }; break :blk d.b; }"});
    // `T{}` takes every field's default (struct_init_empty).
    try expectMatchesZig(a, &.{"blk: { const E = struct { a: u8 = 3, b: u8 = 4 }; const e = E{}; break :blk e.a + e.b; }"});
    // A temporary's field, read directly (struct_init_ref).
    try expectMatchesZig(a, &.{"blk: { " ++ S ++ " break :blk (S{ .a = 5, .b = 6 }).b; }"});
    // Missing a non-defaulted field, an unknown field, and an out-of-range
    // value are compile errors on both sides.
    try expectBothReject(a, &.{"blk: { " ++ S ++ " const s = S{ .a = 1 }; break :blk s.a; }"});
    try expectBothReject(a, &.{"blk: { const Q = struct { a: u8 }; const q = Q{ .a = 1, .b = 2 }; break :blk q.a; }"});
    try expectBothReject(a, &.{"blk: { const Q = struct { a: u8 }; const q = Q{ .a = 300 }; break :blk q.a; }"});
}

test "compliance: field pointers (&x.field and chained access)" {
    // `field_ptr` builds a pointer to a struct field: taking its address, reading
    // and writing through it, and the intermediate step of a chained access.
    const a = testing.allocator;
    // Address of a field, read back through the pointer.
    try expectMatchesZig(a, &.{"blk: { const P = struct { x: u8, y: u8 }; var p: P = .{ .x = 7, .y = 8 }; const px = &p.x; break :blk px.*; }"});
    // Write through the field pointer, observe it on the parent.
    try expectMatchesZig(a, &.{"blk: { const P = struct { x: u8, y: u8 }; var p: P = .{ .x = 7, .y = 8 }; const px = &p.x; px.* = 20; break :blk p.x; }"});
    // Chained field access `l.a.x` -- a field_ptr to `l.a`, then read `.x`. The
    // inner struct is a top-level decl so its type is not a captured local.
    const P = "const P = struct { x: u8, y: u8 };";
    const Line = "const Line = struct { a: P, b: P };";
    const l = "const l = Line{ .a = P{ .x = 1, .y = 2 }, .b = P{ .x = 3, .y = 4 } };";
    try expectMatchesZig(a, &.{ P, Line, l, "l.a.x + l.b.y" });
    // A method on a nested struct value: field_ptr to `l.a`, then the method call.
    const PM = "const P = struct { x: u8, y: u8, fn sum(self: @This()) u8 { return self.x + self.y; } };";
    try expectMatchesZig(a, &.{ PM, Line, l, "l.a.sum() + l.b.sum()" });
    // A field pointer inherits the parent's constness: writing through a field of
    // a `const` is rejected on both sides.
    try expectBothReject(a, &.{"blk: { const P = struct { x: u8 }; const p: P = .{ .x = 9 }; const px = &p.x; px.* = 1; break :blk p.x; }"});
}

test "compliance: enum declarations, tag access, and @intFromEnum" {
    // An auto-numbered enum: each tag's integer is its declaration order, read
    // back through @intFromEnum. The tag type is the smallest unsigned int.
    const a = testing.allocator;
    const E = "const E = enum { a, b, c };";
    try expectMatchesZig(a, &.{"blk: { " ++ E ++ " break :blk @intFromEnum(E.a); }"});
    try expectMatchesZig(a, &.{"blk: { " ++ E ++ " break :blk @intFromEnum(E.c); }"});
    // A tag bound to a name, then converted.
    try expectMatchesZig(a, &.{"blk: { " ++ E ++ " const x = E.b; break :blk @intFromEnum(x); }"});
    // A four-tag enum still fits u2; @intFromEnum yields the ordinal.
    try expectMatchesZig(a, &.{"blk: { const Dir = enum { north, east, south, west }; break :blk @intFromEnum(Dir.west); }"});
    // Referencing a tag the enum does not declare is a compile error on both sides.
    try expectBothReject(a, &.{"blk: { const Q = enum { a, b }; break :blk @intFromEnum(Q.z); }"});
}

test "compliance: @enumFromInt and result-typed enum literals" {
    const a = testing.allocator;
    const E = "const E = enum { a, b, c };";
    // @enumFromInt builds the tag with that integer; round-trips through @intFromEnum.
    try expectMatchesZig(a, &.{"blk: { " ++ E ++ " const e: E = @enumFromInt(1); break :blk @intFromEnum(e); }"});
    // A result-typed enum literal `.c` resolves to the tag (decl_literal).
    try expectMatchesZig(a, &.{"blk: { " ++ E ++ " const e: E = .c; break :blk @intFromEnum(e); }"});
    try expectMatchesZig(a, &.{"blk: { " ++ E ++ " const e: E = .a; break :blk @intFromEnum(e); }"});
    // An integer with no corresponding tag is a compile error on both sides.
    try expectBothReject(a, &.{"blk: { " ++ E ++ " const e: E = @enumFromInt(9); break :blk @intFromEnum(e); }"});
    // A literal naming a tag the enum lacks is rejected on both sides.
    try expectBothReject(a, &.{"blk: { " ++ E ++ " const e: E = .z; break :blk @intFromEnum(e); }"});
}

test "compliance: explicit enum tag types and values" {
    const a = testing.allocator;
    // An explicit tag type with auto-numbered fields.
    try expectMatchesZig(a, &.{"blk: { const E = enum(u8) { a, b, c }; break :blk @intFromEnum(E.c); }"});
    // Explicit values, with auto-increment resuming after each.
    const V = "const E = enum(u8) { a = 5, b, c = 10 };";
    try expectMatchesZig(a, &.{"blk: { " ++ V ++ " break :blk @intFromEnum(E.b); }"}); // 6
    try expectMatchesZig(a, &.{"blk: { " ++ V ++ " break :blk @intFromEnum(E.c); }"}); // 10
    // A value beyond u8 needs a wider tag type.
    try expectMatchesZig(a, &.{"blk: { const E = enum(u16) { a = 300, b = 301 }; break :blk @intFromEnum(E.a); }"});
    // @enumFromInt matches against the actual tag values, not positions.
    const W = "const E = enum(u8) { a = 5, b = 10 };";
    try expectMatchesZig(a, &.{"blk: { " ++ W ++ " const e: E = @enumFromInt(10); break :blk @intFromEnum(e); }"});
    // An integer matching no explicit tag value is rejected on both sides.
    try expectBothReject(a, &.{"blk: { " ++ W ++ " const e: E = @enumFromInt(7); break :blk @intFromEnum(e); }"});
    // A field value that overflows the tag type is a compile error on both sides.
    try expectBothReject(a, &.{"blk: { const E = enum(u8) { a = 300 }; break :blk @intFromEnum(E.a); }"});
}

test "compliance: @tagName of an enum value" {
    // @tagName yields the tag's name as a `*const [N:0]u8`; check its length and
    // bytes (rendering the string itself needs slices, a later stage).
    const a = testing.allocator;
    const E = "const E = enum { north, east, south };";
    try expectMatchesZig(a, &.{"blk: { " ++ E ++ " break :blk @tagName(E.east).len; }"}); // 4
    try expectMatchesZig(a, &.{"blk: { " ++ E ++ " const c: u8 = @tagName(E.south)[0]; break :blk c; }"}); // 's'
    // The name tracks the tag, not its integer, for an explicit-value enum.
    try expectMatchesZig(a, &.{"blk: { const V = enum(u8) { lo = 5, hi = 10 }; const c: u8 = @tagName(V.hi)[0]; break :blk c; }"}); // 'h'
    // @tagName of a non-enum is a compile error on both sides.
    try expectBothReject(a, &.{"blk: { break :blk @tagName(5); }"});
}

test "compliance: @tagName of a tagged union names the active field" {
    const a = testing.allocator;
    const E = "const E = union(enum) { a: u32, b: bool };";
    // @tagName on a tagged union yields the active field's name.
    try expectMatchesZig(a, &.{"blk: { " ++ E ++ " const e = E{ .b = true }; break :blk @tagName(e)[0]; }"}); // 'b'
    try expectMatchesZig(a, &.{"blk: { " ++ E ++ " const e = E{ .a = 9 }; const c: u8 = @tagName(e)[0]; break :blk c; }"}); // 'a'
    // @tagName of an untagged union is a compile error on both sides.
    try expectBothReject(a, &.{"blk: { const U = union { a: u32, b: bool }; const u = U{ .a = 5 }; break :blk @tagName(u)[0]; }"});
    try expectReplDiagnostic(
        a,
        &.{ "const U = union { a: u32 };", "const u = U{ .a = 5 };", "@tagName(u)" },
        "is untagged",
    );
}

test "compliance: enum equality and switch" {
    const a = testing.allocator;
    const E = "const E = enum { a, b, c };";
    // Equality compares tags; ordering is not defined for enums.
    try expectMatchesZig(a, &.{"blk: { " ++ E ++ " const e = E.b; break :blk e == E.b; }"});
    try expectMatchesZig(a, &.{"blk: { " ++ E ++ " const e = E.b; break :blk e != E.a; }"});
    // Switch dispatches on the tag; a multi-tag prong and an else both work.
    try expectMatchesZig(a, &.{"blk: { " ++ E ++ " const e = E.c; break :blk switch (e) { .a => 10, .b => 20, .c => 30 }; }"});
    try expectMatchesZig(a, &.{"blk: { " ++ E ++ " const e = E.a; break :blk switch (e) { .a, .b => 1, .c => 2 }; }"});
    try expectMatchesZig(a, &.{"blk: { " ++ E ++ " const e = E.c; break :blk switch (e) { .a => 100, else => 200 }; }"});
    // Switch over an explicit-value enum matches by tag identity, not value.
    try expectMatchesZig(a, &.{"blk: { const V = enum(u8) { lo = 5, hi = 10 }; break :blk switch (V.hi) { .lo => 100, .hi => 200 }; }"});
    // A case naming a tag the enum lacks is rejected on both sides. The operand
    // does not match the first prong, so the REPL reaches (and rejects) the bad
    // one; the compiler rejects it as an invalid tag regardless.
    try expectBothReject(a, &.{"blk: { " ++ E ++ " const e = E.c; break :blk switch (e) { .a => 1, .z => 2, else => 3 }; }"});
}

test "compliance: switch on a tagged union captures the active payload" {
    const a = testing.allocator;
    const E = "const E = union(enum) { a: u32, b: u8 };";
    // The switch dispatches on the active tag; a prong capture binds the payload.
    try expectMatchesZig(a, &.{"blk: { " ++ E ++ " const e = E{ .a = 5 }; break :blk switch (e) { .a => |v| v, .b => 0 }; }"});
    try expectMatchesZig(a, &.{"blk: { " ++ E ++ " const e = E{ .b = 7 }; break :blk switch (e) { .a => |v| v, .b => |v| v + 1 }; }"}); // 8
    // A by-ref capture reads through the payload pointer.
    try expectMatchesZig(a, &.{"blk: { " ++ E ++ " const e = E{ .a = 42 }; break :blk switch (e) { .a => |*v| v.*, .b => 0 }; }"});
    // A non-capturing prong and an else prong both work.
    try expectMatchesZig(a, &.{"blk: { " ++ E ++ " const e = E{ .b = 7 }; break :blk switch (e) { .a => |v| v, .b => 100 }; }"});
    try expectMatchesZig(a, &.{"blk: { const V = union(enum) { a: u32, b: u8, c: u8 }; const v = V{ .c = 3 }; break :blk switch (v) { .a => |x| x, else => 99 }; }"});
    // A multi-item capture prong binds one value across fields of the same type.
    try expectMatchesZig(a, &.{"blk: { const V = union(enum) { a: u8, b: u8, c: u8 }; const v = V{ .b = 7 }; break :blk switch (v) { .a, .b => |x| x, .c => 0 }; }"});
    // Switch on an untagged union is a compile error on both sides; so is a
    // multi-item capture across incompatible field types.
    try expectBothReject(a, &.{"blk: { const U = union { a: u32, b: u8 }; const u = U{ .a = 5 }; break :blk switch (u) { .a => |v| v, .b => 0 }; }"});
    try expectBothReject(a, &.{"blk: { const V = union(enum) { a: u32, b: bool }; const v = V{ .a = 5 }; break :blk switch (v) { .a, .b => |x| x }; }"});
}

test "compliance: unions with explicit tag types" {
    const a = testing.allocator;
    // `union(enum(T))`: the tag enum has an explicit backing int; access/switch
    // behave as for `union(enum)`.
    const T = "const T = union(enum(u8)) { a: u32, b: u8 };";
    try expectMatchesZig(a, &.{"blk: { " ++ T ++ " const t = T{ .b = 7 }; break :blk switch (t) { .a => |v| v, .b => |v| v + 1 }; }"}); // 8
    // `union(E)`: the tag is the existing enum `E`, whose values may be explicit;
    // the active-field check and @tagName resolve through `E`.
    const U = "const E = enum(u8) { a = 5, b = 10 }; const U = union(E) { a: u32, b: u8 };";
    try expectMatchesZig(a, &.{"blk: { " ++ U ++ " const u = U{ .b = 9 }; break :blk u.b; }"});
    try expectMatchesZig(a, &.{"blk: { " ++ U ++ " const u = U{ .a = 3 }; break :blk switch (u) { .a => |v| v, .b => 0 }; }"});
    try expectMatchesZig(a, &.{"blk: { " ++ U ++ " const u = U{ .b = 9 }; const c: u8 = @tagName(u)[0]; break :blk c; }"}); // 'b'
    try expectBothReject(a, &.{"blk: { " ++ U ++ " const u = U{ .b = 9 }; break :blk u.a; }"});
    // A non-enum tag type, and a union field absent from the tag enum, are both
    // compile errors on both sides. So is a field-order mismatch or a tag enum
    // with fields the union lacks.
    try expectBothReject(a, &.{"blk: { const U = union(u8) { a: u32, b: u8 }; const u = U{ .a = 5 }; break :blk u.a; }"});
    try expectBothReject(a, &.{"blk: { const E = enum { a, b }; const U = union(E) { a: u32, x: u8 }; const u = U{ .x = 1 }; break :blk u.x; }"});
    try expectBothReject(a, &.{"blk: { const E = enum { a, b }; const U = union(E) { b: bool, a: u32 }; const u = U{ .a = 5 }; break :blk u.a; }"});
    try expectBothReject(a, &.{"blk: { const E = enum { a, b, c }; const U = union(E) { a: u32, b: u8 }; const u = U{ .a = 5 }; break :blk u.a; }"});
}

test "compliance: union sad paths pin the REPL's diagnostics" {
    const a = testing.allocator;
    const U = "const U = union(enum) { a: u32, b: u8 };";
    // Initializing or accessing a field the union lacks names the union (this used
    // to crash: the diagnostic assumed a struct type).
    try expectReplDiagnostic(a, &.{"blk: { " ++ U ++ " const u = U{ .z = 1 }; break :blk u.a; }"}, "no field named 'z' in union");
    try expectReplDiagnostic(a, &.{"blk: { " ++ U ++ " const u = U{ .a = 1 }; break :blk u.z; }"}, "no field named 'z' in union");
    // A union init names exactly one field.
    try expectReplDiagnostic(a, &.{"blk: { " ++ U ++ " const u = U{ .a = 1, .b = 2 }; break :blk u.a; }"}, "union initialization expects exactly one field");
    // The init value must coerce to the field type.
    try expectReplDiagnostic(a, &.{"blk: { " ++ U ++ " const u = U{ .a = true }; break :blk u.a; }"}, "cannot coerce value to destination type");
    // @tagName rejects a non-enum/union operand.
    try expectReplDiagnostic(a, &.{"blk: { const S = struct { x: u8 }; const s = S{ .x = 1 }; break :blk @tagName(s); }"}, "expected enum or union");
    // An explicit non-enum tag type, and union(E) order/count mismatches, are
    // rejected with the compiler's wording.
    try expectReplDiagnostic(a, &.{"blk: { const V = union(u8) { a: u32, b: u8 }; const v = V{ .a = 1 }; break :blk v.a; }"}, "expected enum tag type, found 'u8'");
    try expectReplDiagnostic(a, &.{"blk: { const E = enum { a, b }; const V = union(E) { b: bool, a: u32 }; const v = V{ .a = 1 }; break :blk v.a; }"}, "union field order does not match tag enum field order");
}

test "compliance: string literals -- length and byte indexing" {
    // A string literal is a `*const [N:0]u8`. `.len` is the array length; indexing
    // reads a byte. (`@tagName` and slices, which return `[]const u8`, come later.)
    const a = testing.allocator;
    try expectMatchesZig(a, &.{"blk: { const s = \"hello\"; break :blk s.len; }"});
    try expectMatchesZig(a, &.{"blk: { break :blk \"hi\".len; }"});
    try expectMatchesZig(a, &.{"blk: { break :blk \"hi\"[0]; }"}); // 'h' = 104
    try expectMatchesZig(a, &.{"blk: { const s = \"abc\"; break :blk s[2]; }"}); // 'c' = 99
    // `.len` on a plain u8 array works the same (previously misrouted to a field lookup).
    try expectMatchesZig(a, &.{"blk: { const arr = [_]u8{ 10, 20, 30 }; break :blk arr.len; }"});
    // An out-of-range index is a compile error on both sides.
    try expectBothReject(a, &.{"blk: { break :blk \"hi\"[5]; }"});
}

test "compliance: slices -- coercion from a string literal, .len, indexing" {
    // A `*const [N:0]u8` (string literal, `@tagName`) coerces to `[]const u8`.
    // `.len` and byte indexing read through the slice.
    const a = testing.allocator;
    try expectMatchesZig(a, &.{"blk: { const s: []const u8 = \"hello\"; break :blk s.len; }"});
    try expectMatchesZig(a, &.{"blk: { const s: []const u8 = \"hello\"; break :blk s[1]; }"}); // 'e'
    // @tagName's result coerces to a []const u8 slice.
    try expectMatchesZig(a, &.{"blk: { const E = enum { north, east }; const s: []const u8 = @tagName(E.east); break :blk s[0]; }"});
    // Indexing past the slice length is a compile error on both sides.
    try expectBothReject(a, &.{"blk: { const s: []const u8 = \"hi\"; break :blk s[5]; }"});
}

test "compliance: address-of an array literal coerces to slice/many-ptr" {
    // `&[_]T{...}` bound to a `[]T` / `[*]T` result type: validate_ref_ty
    // accepts the pointer result, coerce_ptr_elem_ty sizes the array to the
    // element type, and the array-ptr coerces to the slice/many pointer.
    const a = testing.allocator;
    try expectMatchesZig(a, &.{"blk: { const s: []const u8 = &[_]u8{ 1, 2, 3 }; break :blk s[1]; }"}); // 2
    try expectMatchesZig(a, &.{"blk: { const s: []const u8 = &[_]u8{ 1, 2, 3 }; break :blk s.len; }"}); // 3
    try expectMatchesZig(a, &.{"blk: { const t: []const u32 = &[_]u32{ 10, 20, 30 }; break :blk t[2]; }"}); // 30
    try expectMatchesZig(a, &.{"blk: { const m: [*]const u8 = &[_]u8{ 9, 8, 7 }; break :blk m[0]; }"}); // 9
    // `&expr` bound to a non-pointer result type is rejected on both sides.
    try expectBothReject(a, &.{"blk: { const y: u32 = 5; const x: u32 = &y; break :blk x; }"});
    // Bound to a session const and indexed on a LATER line (the anonymous-decl
    // pointer persists across lines).
    try expectMatchesZig(a, &.{ "const s: []const u8 = &[_]u8{ 1, 2, 3 };", "s[2]" }); // 3
    try expectMatchesZig(a, &.{ "const m: [*]const u8 = &[_]u8{ 9, 8 };", "m[1]" }); // 8
}

test "compliance: indexing a const pointer built on an earlier line" {
    // Regression: a const decl holding a pointer to an anonymous constant used
    // to keep a `.comptime_alloc` base, whose backing slot is discarded when the
    // next line is analysed -- indexing it on a LATER line panicked in
    // `lookupComptimeAlloc` (slot index out of range). A `.uav` base carries the
    // pointee inline, so it survives. These are the exact reproducers.
    const a = testing.allocator;
    try expectMatchesZig(a, &.{ "const s: []const u8 = \"abc\";", "s[0]" }); // 'a'
    try expectMatchesZig(a, &.{ "const s: []const u8 = \"abc\";", "s.len" }); // 3
    // A `&decl` pointer bound to a const and dereferenced on the next line.
    try expectMatchesZig(a, &.{ "const a = [_]u8{ 4, 5, 6 };", "const p = &a;", "p[0]" }); // 4
    // Sub-slicing an array on one line and indexing the result on the next: the
    // sub-slice's `.arr_elem` base is the same anonymous-constant pointer.
    try expectMatchesZig(a, &.{ "const arr = [_]u8{ 10, 20, 30, 40 };", "const s = arr[1..3];", "s[0]" }); // 20
}

test "compliance: array element store" {
    const a = testing.allocator;
    // Store into an array element, directly and through an element pointer.
    try expectMatchesZig(a, &.{"blk: { var arr = [_]u8{ 1, 2, 3 }; arr[1] = 9; break :blk arr[1]; }"});
    try expectMatchesZig(a, &.{"blk: { var arr = [_]u8{ 1, 2, 3 }; arr[0] = 10; arr[2] = 30; break :blk arr[0] + arr[2]; }"});
    try expectMatchesZig(a, &.{"blk: { var arr = [_]u8{ 5, 6 }; const p = &arr[1]; p.* = 99; break :blk arr[1]; }"});
    // Writing an element of a `const` array is rejected on both sides.
    try expectBothReject(a, &.{"blk: { const arr = [_]u8{ 1, 2 }; arr[0] = 5; break :blk arr[0]; }"});
}

test "compliance: array slicing (a[start..end])" {
    const a = testing.allocator;
    // A sub-slice reads through its own start offset and length.
    try expectMatchesZig(a, &.{"blk: { const arr = [_]u8{ 10, 20, 30, 40 }; const s = arr[1..3]; break :blk s.len; }"}); // 2
    try expectMatchesZig(a, &.{"blk: { const arr = [_]u8{ 10, 20, 30, 40 }; const s = arr[1..3]; break :blk s[0]; }"}); // 20
    try expectMatchesZig(a, &.{"blk: { const arr = [_]u8{ 10, 20, 30, 40 }; const s = arr[1..3]; break :blk s[1]; }"}); // 30
    try expectMatchesZig(a, &.{"blk: { const arr = [_]u8{ 10, 20, 30, 40 }; const s = arr[0..4]; break :blk s[3]; }"}); // 40
    // Indexing past the slice length, and an end past the array, are rejected.
    try expectBothReject(a, &.{"blk: { const arr = [_]u8{ 10, 20, 30, 40 }; const s = arr[1..3]; break :blk s[2]; }"});
    try expectBothReject(a, &.{"blk: { const arr = [_]u8{ 1, 2 }; const s = arr[0..9]; break :blk s.len; }"});
    // `len`/`ptr` taken by pointer (fieldPtr's array / slice arms).
    try expectMatchesZig(a, &.{"blk: { const arr = [_]u8{ 1, 2, 3 }; const p = &arr.len; break :blk p.*; }"}); // 3
    try expectMatchesZig(a, &.{"blk: { const arr = [_]u8{ 10, 20, 30 }; const s = arr[0..2]; const p = &s.len; break :blk p.*; }"}); // 2
}

test "compliance: typed array initialization ([N]T = .{ ... })" {
    const a = testing.allocator;
    // The result-location form (array_init_elem_ptr / validate_ptr_array_init).
    try expectMatchesZig(a, &.{"blk: { const arr: [3]u8 = .{ 7, 8, 9 }; break :blk arr[2]; }"});
    try expectMatchesZig(a, &.{"blk: { const arr: [3]u8 = .{ 7, 8, 9 }; break :blk arr[0] + arr[1] + arr[2]; }"});
    // Element-count mismatches are compile errors on both sides.
    try expectBothReject(a, &.{"blk: { const arr: [3]u8 = .{ 1, 2 }; break :blk arr[0]; }"});
    try expectBothReject(a, &.{"blk: { const arr: [2]u8 = .{ 1, 2, 3 }; break :blk arr[0]; }"});
}

test "compliance: sentinel array types ([N:S]T)" {
    const a = testing.allocator;
    // The type renders with its sentinel, and values init/index/`len` like a
    // plain array; the length excludes the sentinel.
    try expectMatchesZig(a, &.{"[3:0]u8"});
    try expectMatchesZig(a, &.{"blk: { const arr: [3:0]u8 = .{ 1, 2, 3 }; break :blk arr.len; }"}); // 3
    try expectMatchesZig(a, &.{"blk: { const arr: [3:0]u8 = .{ 1, 2, 3 }; break :blk arr[1]; }"}); // 2
    // Inferred length and a non-zero sentinel.
    try expectMatchesZig(a, &.{"blk: { const arr = [_:9]u8{ 4, 5 }; break :blk arr.len; }"}); // 2
    try expectMatchesZig(a, &.{"blk: { const arr = [_:9]u8{ 4, 5 }; break :blk arr[0]; }"}); // 4
    // The sentinel is part of type identity: differing/absent sentinels are
    // distinct types.
    try expectMatchesZig(a, &.{"@as(type, [3:0]u8) == @as(type, [3:0]u8)"}); // true
    try expectMatchesZig(a, &.{"@as(type, [3:0]u8) == @as(type, [3:1]u8)"}); // false
    try expectMatchesZig(a, &.{"@as(type, [3:0]u8) == @as(type, [3]u8)"}); // false
    // Sad paths reject on both sides, each on a distinct guard:
    // out-of-range sentinel value (coercion),
    try expectBothReject(a, &.{"blk: { const arr: [2:256]u8 = .{ 1, 2 }; break :blk arr[0]; }"});
    // a fractional or wrong-typed sentinel (coercion),
    try expectBothReject(a, &.{"blk: { const a: [2:1.5]u8 = .{ 1, 2 }; break :blk a[0]; }"});
    try expectBothReject(a, &.{"blk: { const a: [2:\"hi\"]u8 = .{ 1, 2 }; break :blk a[0]; }"});
    // an undefined sentinel (resolveConstDefinedValue),
    try expectBothReject(a, &.{"blk: { const T = [3:undefined]u8; break :blk @sizeOf(T); }"});
    // and a non-scalar element type -- a struct or a slice (checkSentinelType).
    try expectBothReject(a, &.{"blk: { const S = struct { x: u8 }; const T = [2:S{ .x = 0 }]S; break :blk @sizeOf(T); }"});
    try expectBothReject(a, &.{"blk: { const T = [2:\"x\"][]const u8; break :blk @sizeOf(T); }"});
}

test "compliance: union initialization and active-field access" {
    const a = testing.allocator;
    const U = "const U = union { a: u32, b: bool };";
    // Initialize a union and read back its active field.
    try expectMatchesZig(a, &.{"blk: { " ++ U ++ " const u = U{ .a = 5 }; break :blk u.a; }"});
    try expectMatchesZig(a, &.{"blk: { " ++ U ++ " const u = U{ .b = true }; break :blk u.b; }"});
    // A union field can be another aggregate, reached through both.
    const W = "const W = struct { x: u8, y: u8 }; const V = union { p: W, n: u8 };";
    try expectMatchesZig(a, &.{"blk: { " ++ W ++ " const v = V{ .p = W{ .x = 3, .y = 4 } }; break :blk v.p.x + v.p.y; }"});
    // Reading an inactive field is a compile error on both sides; a two-field
    // init is rejected on both. Taking a *pointer* to an inactive field is
    // rejected at the pointer op, even without a load (matching unionFieldPtr).
    try expectBothReject(a, &.{"blk: { " ++ U ++ " const u = U{ .a = 5 }; break :blk u.b; }"});
    try expectBothReject(a, &.{"blk: { " ++ U ++ " const u = U{ .a = 5 }; const q = &u.b; _ = q; break :blk 0; }"});
    try expectBothReject(a, &.{"blk: { " ++ U ++ " const u = U{ .a = 5, .b = true }; break :blk u.a; }"});
    // Pin the REPL's active-field wording to the compiler's.
    try expectReplDiagnostic(
        a,
        &.{"blk: { " ++ U ++ " const u = U{ .a = 5 }; break :blk u.b; }"},
        "access of union field 'b' while field 'a' is active",
    );
}

test "compliance: slices nested in structs and arrays of slices" {
    const a = testing.allocator;
    // A `[]const u8` field of a struct: access, `.len`, and byte indexing.
    const S = "const S = struct { name: []const u8 };";
    try expectMatchesZig(a, &.{"blk: { " ++ S ++ " const s = S{ .name = \"hello\" }; break :blk s.name.len; }"});
    try expectMatchesZig(a, &.{"blk: { " ++ S ++ " const s = S{ .name = \"abc\" }; break :blk s.name[1]; }"}); // 'b'
    // An array of slices (`[N][]const u8`): element `.len`, and chained indexing --
    // `arr[i].len` / `arr[i][j]` go through elem_ptr_node to the element slice.
    const Arr = "const arr = [_][]const u8{ \"a\", \"bb\", \"ccc\" };";
    try expectMatchesZig(a, &.{"blk: { " ++ Arr ++ " break :blk arr[2].len; }"}); // 3
    try expectMatchesZig(a, &.{"blk: { " ++ Arr ++ " break :blk arr[0][0]; }"}); // 'a'
    // A struct holding an array of slices, reached through both.
    const W = "const W = struct { rows: [2][]const u8 };";
    try expectMatchesZig(a, &.{"blk: { " ++ W ++ " const w = W{ .rows = .{ \"xy\", \"z\" } }; break :blk w.rows[0][1]; }"}); // 'y'
}

test "compliance: a member body takes the address of a sibling declaration" {
    // `&k` inside a method body resolves `k` in the enclosing container, like a
    // bare `k` does -- decl_ref and decl_val share the same lookup.
    const a = testing.allocator;
    try expectMatchesZig(a, &.{"blk: { const S = struct { const k: u8 = 7; fn go() u8 { const p = &k; return p.*; } }; break :blk S.go(); }"});
}

test "compliance: diagnostics match the compiler's wording" {
    // These conditions are compile errors on both sides; pin the REPL's message to
    // the compiler's phrasing (not compared to zig's text, whose type names differ).
    const a = testing.allocator;
    try expectReplDiagnostic(a, &.{"blk: { const arr = [_]u8{ 1, 2, 3 }; break :blk arr[5]; }"}, "index 5 outside array of length 3");
    try expectReplDiagnostic(a, &.{"@as(u8, 7) / @as(u8, 0)"}, "division by zero here causes illegal behavior");
    try expectReplDiagnostic(a, &.{"blk: { break :blk @as(i32, -7) % @as(i32, 3); }"}, "signed integers and floats must use @rem or @mod");
    try expectReplDiagnostic(a, &.{"blk: { const S = struct { fn f(x: u32) u8 { return x; } }; break :blk S.f(5); }"}, "expected type 'u8', found 'u32'");
    try expectReplDiagnostic(a, &.{"blk: { const S = struct { fn f(x: u8) u8 { return x; } }; break :blk S.f(1, 2); }"}, "expected 1 argument(s), found 2");
}

test "compliance: nested struct types capture an enclosing local (closure_get)" {
    // A struct whose field type names a local from the enclosing scope captures
    // that local (closure_capture); the field body reads it via closure_get.
    const a = testing.allocator;
    // Field type is a captured struct local, then a nested field read.
    try expectMatchesZig(a, &.{"blk: { const P = struct { x: u8 }; const W = struct { p: P }; const w = W{ .p = P{ .x = 42 } }; break :blk w.p.x; }"});
    // A captured type alias as a field type.
    try expectMatchesZig(a, &.{"blk: { const T = u16; const Box = struct { v: T }; const b = Box{ .v = 500 }; break :blk b.v; }"});
    // Two levels of captured struct types, read through the chain.
    try expectMatchesZig(a, &.{"blk: { const P = struct { x: u8 }; const N = struct { inner: P }; const M = struct { mid: N }; const m = M{ .mid = N{ .inner = P{ .x = 7 } } }; break :blk m.mid.inner.x; }"});
    // A captured struct with a method, invoked on a nested value.
    try expectMatchesZig(a, &.{"blk: { const P = struct { x: u8, y: u8, fn sum(self: @This()) u8 { return self.x + self.y; } }; const Line = struct { a: P, b: P }; const l = Line{ .a = P{ .x = 1, .y = 2 }, .b = P{ .x = 3, .y = 4 } }; break :blk l.a.sum() + l.b.sum(); }"});
}

test "compliance: a struct type declared inside a function body" {
    // A struct created in a called function's body records that function's line
    // as its source, so its fields resolve when the type is used later. A generic
    // struct factory instantiated with different types yields distinct types.
    const a = testing.allocator;
    try expectMatchesZig(a, &.{ "fn mk() type { return struct { v: u8 }; }", "const m: mk() = .{ .v = 5 };", "m.v" });
    const Box = "fn Box(comptime T: type) type { return struct { v: T }; }";
    try expectMatchesZig(a, &.{ Box, "const b: Box(u16) = .{ .v = 500 };", "b.v" });
    // Two instantiations coexist: each keeps its own captured element type.
    try expectMatchesZig(a, &.{ Box, "const p: Box(u8) = .{ .v = 1 };", "const q: Box(u16) = .{ .v = 500 };", "q.v" });
}

test "compliance: type-inferred locals (var y = expr)" {
    // `var`/`const` with no written type infer it from the initializer via
    // alloc_inferred + store_to_inferred_ptr + resolve_inferred_alloc.
    const a = testing.allocator;
    // Inferred `var`, then mutated.
    try expectMatchesZig(a, &.{"blk: { var x: u8 = 5; x += 1; var y = x; y += 1; break :blk y; }"});
    // Inferred `const`.
    try expectMatchesZig(a, &.{"blk: { var x: u8 = 5; x += 1; const y = x; break :blk y; }"});
    // Inferred `var` of a struct, then a field mutated.
    const S = "const S = struct { a: u8, b: u8 };";
    try expectMatchesZig(a, &.{"blk: { " ++ S ++ " var s = S{ .a = 1, .b = 2 }; s.a = 10; break :blk s.a + s.b; }"});
    // An inferred `const` is not writable: mutating a field is rejected on both sides.
    try expectBothReject(a, &.{"blk: { const Q = struct { a: u8 }; const q = Q{ .a = 1 }; q.a = 2; break :blk q.a; }"});
}

test "compliance: for loops (range and array)" {
    const a = testing.allocator;
    try expectMatchesZig(a, &.{"blk: { var s: u32 = 0; for (0..4) |i| { s += @intCast(i); } break :blk s; }"});
    try expectMatchesZig(a, &.{"blk: { var s: u32 = 0; for (2..5) |i| { s += @intCast(i); } break :blk s; }"});
    try expectMatchesZig(a, &.{"blk: { const arr = [_]u8{ 10, 20, 30 }; var s: u32 = 0; for (arr) |x| { s += x; } break :blk s; }"});
    try expectMatchesZig(a, &.{"blk: { var s: u32 = 0; for (0..3) |i| { for (0..3) |j| { s += @intCast(i * j); } } break :blk s; }"});
    // By-reference capture over a pointer-to-array (`for (&arr) |*e|`): the
    // element pointer stores back into the array. With an index input too.
    try expectMatchesZig(a, &.{"blk: { var arr = [_]u8{ 1, 2, 3 }; for (&arr) |*e| { e.* += 10; } break :blk arr[0] + arr[1] + arr[2]; }"}); // 36
    try expectMatchesZig(a, &.{"blk: { var arr = [_]u8{ 5, 6, 7, 8 }; for (&arr) |*e| { e.* = e.* * 2; } break :blk arr[3]; }"}); // 16
    try expectMatchesZig(a, &.{"blk: { var arr = [_]u32{ 0, 0, 0 }; for (&arr, 0..) |*e, i| { e.* = @intCast(i); } break :blk arr[2]; }"}); // 2
}

test "compliance: @Vector element indexing" {
    const a = testing.allocator;
    // A vector initialises and indexes like an array; the element type is the
    // lane type.
    try expectMatchesZig(a, &.{"blk: { const v: @Vector(4, i32) = .{ 10, 20, 30, 40 }; break :blk v[2]; }"}); // 30
    try expectMatchesZig(a, &.{"blk: { const v: @Vector(4, i32) = .{ 10, 20, 30, 40 }; break :blk v[0] + v[3]; }"}); // 50
    try expectMatchesZig(a, &.{"blk: { const v: @Vector(3, u8) = .{ 5, 6, 7 }; break :blk v[1]; }"}); // 6
    // Indexing past the vector length is a compile error on both sides.
    try expectBothReject(a, &.{"blk: { const v: @Vector(3, u8) = .{ 5, 6, 7 }; break :blk v[5]; }"});
}

test "compliance: nested aggregate init and element store" {
    const a = testing.allocator;
    // Storing through a nested element pointer rebuilds each enclosing aggregate.
    try expectMatchesZig(a, &.{"blk: { const arr: [2][3]u8 = .{ .{ 1, 2, 3 }, .{ 4, 5, 6 } }; break :blk arr[1][0] + arr[0][2]; }"}); // 7
    try expectMatchesZig(a, &.{"blk: { var m: [2][2]u8 = .{ .{ 1, 2 }, .{ 3, 4 } }; m[0][1] = 9; break :blk m[0][1] + m[1][0]; }"}); // 12
    try expectMatchesZig(a, &.{"blk: { const S = struct { p: struct { x: u8 } }; var s: S = .{ .p = .{ .x = 1 } }; s.p.x = 7; break :blk s.p.x; }"}); // 7
}

test "compliance: @intFromPtr honors the pointer's alignment" {
    // The REPL's address is synthetic (it won't equal a real `zig run`
    // address), but both sides honor `@intFromPtr(&x) % align == 0`: zig's
    // address is aligned by the linker, the REPL's by construction. This is a
    // shared-invariant check, not address-value parity.
    const a = testing.allocator;
    try expectMatchesZig(a, &.{ "var x: u32 align(8) = 5;", "@intFromPtr(&x) % 8" });
    try expectMatchesZig(a, &.{ "var w: u64 align(16) = 5;", "@intFromPtr(&w) % 16" });
    try expectMatchesZig(a, &.{ "var p: u32 = 5;", "@intFromPtr(&p) % @alignOf(u32)" });
    // The synthetic address is stable per pointer: address-of the same binding
    // compares equal (pointer identity), two distinct bindings compare unequal.
    try expectMatchesZig(a, &.{ "const a = [_]u8{ 1, 2, 3 };", "@intFromPtr(&a) == @intFromPtr(&a)" });
    try expectMatchesZig(a, &.{ "const a = [_]u8{ 1, 2 };", "const b = [_]u8{ 3, 4 };", "@intFromPtr(&a) == @intFromPtr(&b)" });
    try expectMatchesZig(a, &.{ "var v: u32 = 5;", "@intFromPtr(&v) == @intFromPtr(&v)" });
}

test "compliance: a type-returning generic function and composition" {
    // `fn Id(comptime T: type) type` returns a type value; feeding it as the
    // type argument of another generic resolves both instantiations.
    const a = testing.allocator;
    const id = "fn Id(comptime T: type) type { return T; }";
    const make = "fn make(comptime T: type) T { return 200 + 100; }";
    try expectMatchesZig(a, &.{ id, "Id(u8)" });
    try expectMatchesZig(a, &.{ id, make, "@TypeOf(make(Id(u16)))" });
    try expectMatchesZig(a, &.{ id, make, "make(Id(u16))" });
}

test "sad paths: numeric coercion and casts are rejected" {
    const a = testing.allocator;
    // Out-of-range and wrong-sign comptime coercions fail on both sides.
    try expectBothReject(a, &.{"blk: { break :blk @as(u8, 300); }"});
    try expectBothReject(a, &.{"blk: { break :blk @as(u8, -1); }"});
    try expectBothReject(a, &.{"blk: { break :blk @as(i8, 200); }"});
    try expectBothReject(a, &.{"blk: { break :blk @as(u8, @intCast(@as(u16, 300))); }"});
    // Casts require an operand of the right category.
    try expectBothReject(a, &.{"blk: { break :blk @floatFromInt(true); }"});
    try expectBothReject(a, &.{"blk: { break :blk @intFromFloat(@as(u8, 1)); }"});
    // Division by zero is illegal behavior at comptime.
    try expectBothReject(a, &.{"blk: { break :blk @as(u8, 7) / @as(u8, 0); }"});
}

test "sad paths: operator type mismatches are rejected" {
    const a = testing.allocator;
    try expectBothReject(a, &.{"blk: { break :blk true + 1; }"});
    try expectBothReject(a, &.{"blk: { break :blk void + void; }"});
    try expectBothReject(a, &.{"blk: { const x: bool = 1; break :blk x; }"});
}

test "sad paths: const mutation and bad deref are rejected" {
    const a = testing.allocator;
    try expectBothReject(a, &.{"blk: { const x: u8 = 1; x = 2; break :blk x; }"});
    try expectBothReject(a, &.{"blk: { var x: u8 = 1; break :blk x.*; }"});
}

test "sad paths: optionals and error unions are rejected" {
    const a = testing.allocator;
    // Unwrapping a comptime-known null is illegal behavior.
    try expectBothReject(a, &.{"blk: { const x: ?u8 = null; break :blk x.?; }"});
    // An error union does not coerce to its payload without catch/try.
    try expectBothReject(a, &.{"blk: { const E = error{A}; const eu: E!u8 = 1; const y: u8 = eu; break :blk y; }"});
}

test "sad paths: switch item type mismatch is rejected" {
    const a = testing.allocator;
    // A case item whose type cannot coerce to the operand type is rejected.
    try expectBothReject(a, &.{"blk: { break :blk switch (@as(u8, 5)) { true => 1, else => 0 }; }"});
    try expectBothReject(a, &.{"blk: { const E = enum { a, b }; break :blk switch (E.a) { 0 => 1, else => 0 }; }"});
}

test "compliance: switch operand and exhaustiveness are validated" {
    const a = testing.allocator;
    // Switching on an un-switchable type is rejected ("switch on type '{f}'").
    try expectReplDiagnostic(a, &.{"blk: { break :blk switch (@as(f32, 1)) { else => 0 }; }"}, "switch on type 'f32'");
    try expectBothReject(a, &.{"blk: { const x: ?u8 = 1; break :blk switch (x) { else => 0 }; }"});
    // An enum switch with no else must handle every tag.
    try expectReplDiagnostic(a, &.{"blk: { const E = enum { a, b }; break :blk switch (E.a) { .a => 1 }; }"}, "switch must handle all possibilities");
    try expectBothReject(a, &.{"blk: { const E = enum { a, b, c }; break :blk switch (E.a) { .a => 1, .b => 2 }; }"});
    // A tagged union (switched via its tag enum) is validated the same way.
    try expectBothReject(a, &.{"blk: { const U = union(enum) { a: u32, b: u8 }; const u = U{ .a = 1 }; break :blk switch (u) { .a => |v| v }; }"});
    // Exhaustive-or-else switches remain accepted.
    try expectMatchesZig(a, &.{"blk: { const E = enum { a, b }; break :blk switch (E.b) { .a => 1, .b => 2 }; }"});
    try expectMatchesZig(a, &.{"blk: { const E = enum { a, b, c }; break :blk switch (E.c) { .a => 1, else => 9 }; }"});
    // A no-else switch is exhaustive when its cases span the whole domain: a small
    // int fully covered by values or a range, or a bool covering true and false.
    try expectMatchesZig(a, &.{"blk: { break :blk switch (@as(u1, 0)) { 0 => 10, 1 => 20 }; }"});
    try expectMatchesZig(a, &.{"blk: { break :blk switch (@as(u2, 3)) { 0...3 => 10 }; }"});
    try expectMatchesZig(a, &.{"blk: { break :blk switch (true) { true => 1, false => 0 }; }"});
    // A non-spanning int or a missing bool value without else is rejected.
    try expectBothReject(a, &.{"blk: { break :blk switch (@as(u8, 0)) { 0 => 10, 1 => 20 }; }"});
    try expectBothReject(a, &.{"blk: { break :blk switch (true) { true => 1 }; }"});
    // A computed (non-literal) case item is resolved, so a gap is still caught.
    try expectBothReject(a, &.{"blk: { const E = enum { a, b }; const k = E.b; break :blk switch (E.a) { k => 1 }; }"});
    // A redundant else on a fully-covered switch is rejected on both sides.
    try expectReplDiagnostic(a, &.{"blk: { const E = enum { a, b }; break :blk switch (E.a) { .a => 1, .b => 2, else => 9 }; }"}, "unreachable else prong; all cases already handled");
    // Wide/target-width ints are the `.int` category (span-or-else, "must handle
    // all possibilities"), while comptime_int is else-required -- matching how the
    // compiler's zigTypeTag routes them.
    try expectReplDiagnostic(a, &.{"blk: { break :blk switch (@as(usize, 0)) { 0 => 1 }; }"}, "switch must handle all possibilities");
    try expectReplDiagnostic(a, &.{"blk: { break :blk switch (@as(comptime_int, 0)) { 0 => 1 }; }"}, "else prong required when switching on type 'comptime_int'");
    // Non-else full coverage via multiple ranges is accepted (RangeSet spanning).
    try expectMatchesZig(a, &.{"blk: { break :blk switch (@as(u8, 5)) { 0...4 => 1, 5...255 => 2 }; }"});
    // Duplicate items, a range on a non-int, and a `_` prong are all rejected.
    try expectReplDiagnostic(a, &.{"blk: { const E = enum { a, b }; break :blk switch (E.a) { .a => 1, .a => 2, .b => 3 }; }"}, "duplicate switch value");
    try expectReplDiagnostic(a, &.{"blk: { break :blk switch (@as(u8, 0)) { 0 => 1, 0 => 2, else => 3 }; }"}, "duplicate switch value");
    try expectReplDiagnostic(a, &.{"blk: { break :blk switch (true) { true...false => 1 }; }"}, "ranges not allowed when switching on type 'bool'");
    try expectReplDiagnostic(a, &.{"blk: { const E = enum { a, b }; break :blk switch (E.a) { .a => 1, .b => 2, _ => 3 }; }"}, "'_' prong only allowed when switching on non-exhaustive enums");
    try expectBothReject(a, &.{"blk: { const E = enum { a, b }; break :blk switch (E.a) { .a => 1, .a => 2, .b => 3 }; }"});
    try expectBothReject(a, &.{"blk: { const E = enum { a, b }; break :blk switch (E.a) { .a => 1, .b => 2, _ => 3 }; }"});
    // Error-set switches are exhaustive over the set's names.
    try expectMatchesZig(a, &.{ "const E = error{ A, B };", "const x: E!u8 = error.A;", "x catch |e| switch (e) { error.A => 1, error.B => 2 }" });
    try expectBothReject(a, &.{ "const E = error{ A, B };", "const x: E!u8 = error.A;", "x catch |e| switch (e) { error.A => 1 }" });
}

test "sad paths: enums are rejected" {
    const a = testing.allocator;
    try expectBothReject(a, &.{"blk: { const E = enum { a, b }; break :blk E.z; }"});
    try expectBothReject(a, &.{"blk: { break :blk @intFromEnum(@as(u8, 1)); }"});
    try expectBothReject(a, &.{"blk: { const E = enum(u8) { a = 0, b = 1 }; break :blk @intFromEnum(@as(E, @enumFromInt(200))); }"});
}

test "sad paths: structs are rejected" {
    const a = testing.allocator;
    try expectBothReject(a, &.{"blk: { const S = struct { x: u8 }; const s = S{}; break :blk s.x; }"});
    try expectBothReject(a, &.{"blk: { const S = struct { x: u8 }; const s = S{ .x = 1 }; break :blk s.y; }"});
    try expectBothReject(a, &.{"blk: { const S = struct { x: u8 }; break :blk S.nope; }"});
}

test "sad paths: arrays and tuples are rejected" {
    const a = testing.allocator;
    try expectBothReject(a, &.{"blk: { const arr = [_]u8{ 1, 2 }; break :blk arr[5]; }"});
    try expectBothReject(a, &.{"blk: { const t = .{ 1, 2 }; break :blk t[5]; }"});
    try expectBothReject(a, &.{"blk: { const t: struct { u8, u8 } = .{ 1, 2, 3 }; break :blk t[0]; }"});
}

test "sad paths: generics and @TypeOf are rejected" {
    const a = testing.allocator;
    // A generic body whose result cannot coerce to the resolved return type.
    try expectBothReject(a, &.{"blk: { const S = struct { fn f(comptime T: type) T { return true; } }; break :blk S.f(u8); }"});
    // Wrong argument count to a function.
    try expectBothReject(a, &.{"blk: { const S = struct { fn f(x: u8) u8 { return x; } }; break :blk S.f(); }"});
}

test "sad paths: slices, loops, and indexing are rejected" {
    const a = testing.allocator;
    try expectBothReject(a, &.{"blk: { const arr = [_]u8{ 1, 2, 3 }; const s = arr[1..9]; break :blk s.len; }"});
    try expectBothReject(a, &.{"blk: { var s: u8 = 0; for (@as(u8, 5)) |x| s += x; break :blk s; }"});
    try expectBothReject(a, &.{"blk: { const x: u8 = 5; break :blk x[0]; }"});
}

test "sad paths: bad builtins and calls are rejected" {
    const a = testing.allocator;
    try expectBothReject(a, &.{"blk: { break :blk @as(u8, 1) << 100; }"});
    try expectBothReject(a, &.{"blk: { const x: u8 = 5; break :blk x(); }"});
    try expectReplDiagnostic(a, &.{"blk: { break :blk @sizeOf(); }"}, "expected 1 argument, found 0");
}
