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

/// Run the expression through Pipeline + Sema + render. Pipeline.run
/// handles the `const __repl_input = (...);` wrap. Returns the
/// rendered text with the trailing newline stripped.
fn runViaRepl(gpa: std.mem.Allocator, expr: []const u8) ![]u8 {
    var pool = try InternPool.init(gpa);
    defer pool.deinit();

    var result = try Pipeline.run(gpa, expr);
    defer result.deinit(gpa);

    if (result.hasParseErrors()) return error.ParseError;
    if (result.hasZirErrors()) return error.ZirError;

    var diag_buf: [4096]u8 = undefined;
    var diag_writer = Io.Writer.fixed(&diag_buf);
    const maybe_value = try Sema.analyze(gpa, &pool, result.zir, &diag_writer, null);
    const value = maybe_value orelse return error.NoValue;

    var out_buf: [512]u8 = undefined;
    var out_writer = Io.Writer.fixed(&out_buf);
    try render.render(value, &pool, &out_writer);

    const raw = out_buf[0 .. out_writer.buffer.len - out_writer.unusedCapacityLen()];
    return try gpa.dupe(u8, std.mem.trimEnd(u8, raw, "\n"));
}

/// Synthesise a tiny Zig program that prints the expression's value via
/// `{any}` (works for ints / floats / bools uniformly), then `zig run`
/// it. Returns the captured stdout. The caller owns the slice.
fn runViaZig(gpa: std.mem.Allocator, expr: []const u8) ![]u8 {
    var prog_buf: [4096]u8 = undefined;
    // `std.debug.print` writes to stderr without needing an Io setup,
    // sidestepping the file-writer/init dance for what is otherwise a
    // throwaway program. `zig run` itself adds nothing to stderr on
    // success, so the captured stderr IS the value.
    const prog = try std.fmt.bufPrint(&prog_buf,
        \\const std = @import("std");
        \\pub fn main() void {{
        \\    std.debug.print("{{any}}", .{{ {s} }});
        \\}}
    , .{expr});

    // `global_single_threaded` uses a failing allocator internally -- the
    // subprocess spawn path needs a real one for its argv / environ
    // buffers. Init a fresh Threaded backed by the caller's gpa.
    var io_instance: Io.Threaded = .init(gpa, .{});
    defer io_instance.deinit();
    const io = io_instance.io();

    Io.Dir.cwd().writeFile(io, .{ .sub_path = tmp_zig_path, .data = prog }) catch
        return error.SkipZigTest;

    // Provide an explicit cache dir so the subprocess doesn't need
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

/// Run `expr` through both our REPL and `zig run`, normalise both
/// outputs, assert equality.
fn expectMatchesZig(gpa: std.mem.Allocator, expr: []const u8) !void {
    const our_output = try runViaRepl(gpa, expr);
    defer gpa.free(our_output);
    const zig_output = try runViaZig(gpa, expr);
    defer gpa.free(zig_output);

    try testing.expectEqualStrings(normalize(zig_output), normalize(our_output));
}

test "compliance: comptime_int arithmetic" {
    try expectMatchesZig(testing.allocator, "1 + 2 * 3");
}

test "compliance: comptime_int big literal" {
    try expectMatchesZig(testing.allocator, "1000000000 * 1000");
}

test "compliance: comptime_float arithmetic" {
    try expectMatchesZig(testing.allocator, "1.5 + 2.5");
}

test "compliance: comptime_int + comptime_float promotes" {
    try expectMatchesZig(testing.allocator, "1 + 1.5");
}

test "compliance: fixed-width int arith" {
    try expectMatchesZig(testing.allocator, "@as(i32, 5) + @as(i32, 3)");
}

test "compliance: peer resolution to wider int" {
    try expectMatchesZig(testing.allocator, "@as(u8, 5) + @as(u16, 10)");
}

test "compliance: peer resolution mixed signedness (signed wider)" {
    try expectMatchesZig(testing.allocator, "@as(u8, 5) + @as(i16, 100)");
}

test "compliance: peer resolution mixed signedness (legacy unsigned wider)" {
    try expectMatchesZig(testing.allocator, "@as(u16, 5) + @as(i8, 100)");
}

test "compliance: fixed-width float arith" {
    try expectMatchesZig(testing.allocator, "@as(f32, 1.5) + @as(f32, 2.5)");
}

test "compliance: mixed-width float widens" {
    try expectMatchesZig(testing.allocator, "@as(f32, 1.5) + @as(f64, 2.5)");
}

test "compliance: fixed-width int + fixed-width float" {
    try expectMatchesZig(testing.allocator, "@as(f32, 1.5) + @as(i32, 2)");
}

test "compliance: wrap arith" {
    try expectMatchesZig(testing.allocator, "@as(u8, 200) +% @as(u8, 100)");
}

test "compliance: sat arith" {
    try expectMatchesZig(testing.allocator, "@as(u8, 200) +| @as(u8, 100)");
}

test "compliance: shift arith" {
    try expectMatchesZig(testing.allocator, "@as(u8, 1) << 7");
}

test "compliance: bitwise on fixed-width" {
    try expectMatchesZig(testing.allocator, "@as(u16, 1000) & @as(u16, 0xff)");
}

test "compliance: @intCast widen" {
    try expectMatchesZig(testing.allocator, "@as(u32, @intCast(@as(u8, 200)))");
}

test "compliance: @truncate" {
    try expectMatchesZig(testing.allocator, "@as(u8, @truncate(@as(u32, 0x1234)))");
}

test "compliance: @bitCast f32 -> u32" {
    try expectMatchesZig(testing.allocator, "@as(u32, @bitCast(@as(f32, 1.5)))");
}

test "compliance: @bitCast i8 -> u8 (two's complement)" {
    try expectMatchesZig(testing.allocator, "@as(u8, @bitCast(@as(i8, -1)))");
}

test "compliance: usize + comptime_int" {
    try expectMatchesZig(testing.allocator, "@as(usize, 100) + 1");
}

test "compliance: c_int peer participation" {
    try expectMatchesZig(testing.allocator, "@as(c_int, 5) * 2");
}

test "compliance: comparison across widths" {
    try expectMatchesZig(testing.allocator, "@as(u16, 1000) > @as(u8, 200)");
}

test "compliance: @as comptime_float -> fixed-width" {
    try expectMatchesZig(testing.allocator, "@as(f32, 1.5)");
}

test "compliance: @as fixed-width int -> fixed-width float" {
    try expectMatchesZig(testing.allocator, "@as(f64, @as(i32, 1000000))");
}

test "compliance: @intFromFloat truncate" {
    try expectMatchesZig(testing.allocator, "@as(i32, @intFromFloat(@as(f64, 3.7)))");
}

test "compliance: @floatFromInt rounding" {
    try expectMatchesZig(testing.allocator, "@as(f32, @floatFromInt(16777217))");
}

test "compliance: bit_not on fixed-width int" {
    try expectMatchesZig(testing.allocator, "~@as(u8, 5)");
}

test "compliance: bit_not on signed int" {
    try expectMatchesZig(testing.allocator, "~@as(i32, 100)");
}

test "compliance: negate_wrap on signed min" {
    try expectMatchesZig(testing.allocator, "-%@as(i8, -128)");
}

test "compliance: negate on fixed-width int" {
    try expectMatchesZig(testing.allocator, "-@as(i32, 100)");
}

test "compliance: ptr_type *const u8 renders as Zig prints" {
    try expectMatchesZig(testing.allocator, "*const u8");
}

test "compliance: ptr_type [*]u32 renders as Zig prints" {
    try expectMatchesZig(testing.allocator, "[*]u32");
}

test "compliance: ptr_type []i32 renders as Zig prints" {
    try expectMatchesZig(testing.allocator, "[]i32");
}

test "compliance: ptr_type nested *const *const u32 renders identically" {
    try expectMatchesZig(testing.allocator, "*const *const u32");
}

test "compliance: @as(type, *const u8) is identity on type-of-type" {
    try expectMatchesZig(testing.allocator, "@as(type, *const u8)");
}

test "compliance: @as(type, [*]i32) is identity on type-of-type" {
    try expectMatchesZig(testing.allocator, "@as(type, [*]i32)");
}

test "compliance: @as(type, *const *const u32) recurses correctly" {
    try expectMatchesZig(testing.allocator, "@as(type, *const *const u32)");
}

test "compliance: var mutation through alloc/store/load" {
    try expectMatchesZig(testing.allocator, "blk: { var x: u8 = 0; x = x + 1; break :blk x; }");
}

test "compliance: wrap arith through a stored var" {
    try expectMatchesZig(testing.allocator, "blk: { var x: u8 = 200; x = x +% 100; break :blk x; }");
}

test "compliance: two independent var slots do not alias" {
    try expectMatchesZig(testing.allocator, "blk: { var a: u8 = 1; var b: u8 = 2; a = 10; b = 20; break :blk a + b; }");
}
