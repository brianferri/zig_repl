//! Compliance harness -- runs each expression through both our REPL and
//! a freshly-spawned `zig run` on the same source, normalises both
//! outputs, and asserts they match. This proves spec compliance for
//! the expressions we list here at the test-runner level.

const std = @import("std");
const testing = std.testing;
const Io = std.Io;

const Pipeline = @import("front/Pipeline.zig");
const Sema = @import("sema/Sema.zig");
const InternPool = @import("sema/InternPool.zig");
const Value = @import("sema/Value.zig");
const render = @import("render/Value.zig");

const tmp_zig_path = "/tmp/zig_repl_compliance_check.zig";

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

    var last_value: ?@import("sema/Value.zig") = null;
    for (inputs) |source| {
        var result = try Pipeline.runWithInjection(gpa, source, &pool, .init(ns));
        defer result.deinit(gpa);

        if (result.hasParseErrors()) return error.ParseError;
        if (result.hasZirErrors()) return error.ZirError;

        var diag_buf: [4096]u8 = undefined;
        var diag_writer = Io.Writer.fixed(&diag_buf);
        last_value = try Sema.analyze(gpa, &pool, result.zir, &diag_writer, ns);
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

    Io.Dir.cwd().writeFile(io, .{ .sub_path = tmp_zig_path, .data = prog.written() }) catch
        return error.SkipZigTest;

    // Explicit cache dirs so the subprocess doesn't need
    // `$XDG_CACHE_HOME` / `$HOME` from a possibly-empty inherited
    // environment.
    const result = std.process.run(gpa, io, .{
        .argv = &.{
            "zig",                "run",
            "--cache-dir",        "/tmp/zig-compliance-cache",
            "--global-cache-dir", "/tmp/zig-compliance-global-cache",
            tmp_zig_path,
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
