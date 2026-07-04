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
