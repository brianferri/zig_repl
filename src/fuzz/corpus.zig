//! Seed inputs for the mutational stress suite: valid REPL snippets spanning the
//! supported feature surface. The mutator perturbs these (see stress_test.zig),
//! so starting from working programs keeps generated inputs near-valid and drives
//! them deep into AstGen/Sema/eval, where memory bugs live -- unlike raw random
//! bytes, which the parser rejects on sight. Breadth matters more than depth
//! here: every distinct language construct is a seed the mutator can splice.

/// Single-line expressions and declarations.
pub const lines = [_][]const u8{
    // Integer / float arithmetic and the overflow edges.
    "1 + 2 * 3 - 4",
    "@as(u8, 255) + 1",
    "@as(i8, -128) - 1",
    "1 << 63",
    "0xffff_ffff_ffff_ffff",
    "@as(u4, 15) *% 2",
    "10 / 3",
    "10 % 3",
    "3.14 * 2.0",
    "@as(f32, 1.5) + @as(f32, 2.5)",
    "1e10",
    "-0.0",
    "~@as(u8, 0)",
    "5 & 3 | 8 ^ 1",
    // Bools, optionals, comparisons.
    "true and false or !true",
    "1 == 1 and 2 != 3",
    "@as(?u8, 5) orelse 0",
    "@as(?u8, null) orelse 42",
    "if (@as(?u8, 3)) |v| v else 0",
    // Casts and conversions.
    "@as(u16, @intCast(@as(u8, 200)))",
    "@as(f64, @floatFromInt(7))",
    "@as(u8, @truncate(@as(u16, 300)))",
    "@intFromBool(true)",
    "@as(i32, @intFromFloat(3.9))",
    "@bitCast(@as(u32, 0x3f800000))",
    // Pointer-cast family: element retype, qualifier drop, alignment assert, slice retype.
    "blk: { const p: *const u32 = @ptrFromInt(0x1000); const q: *const u8 = @ptrCast(p); break :blk @intFromPtr(q); }",
    "blk: { const p: *const u32 = @ptrFromInt(0x1000); break :blk @intFromPtr(@constCast(p)); }",
    "blk: { const p: *volatile u32 = @ptrFromInt(0x1000); break :blk @intFromPtr(@volatileCast(p)); }",
    "blk: { const p: *u32 = @ptrFromInt(0x1000); break :blk @intFromPtr(@as(*align(4) u32, @alignCast(p))); }",
    "blk: { var arr = [_]u32{ 1, 2, 3 }; const s: []u32 = &arr; break :blk @as([]const u8, @ptrCast(s)).len; }",
    // Arrays, slices, strings.
    "[_]u8{ 1, 2, 3 }",
    "[_]u8{ 1, 2, 3 }.len",
    "\"hello world\"",
    "\"hi\"[0]",
    "blk: { const s: []const u8 = \"abcdef\"; break :blk s[1..4]; }",
    "@as([]const u8, \"xyz\").len",
    "[_]i32{ 5, 6, 7 } ++ [_]i32{ 8 }",
    "[_]u8{0} ** 4",
    // Structs.
    "blk: { const S = struct { a: u8, b: u16 }; break :blk @as(S, .{ .a = 1, .b = 2 }).b; }",
    ".{ .x = 1, .y = 2 }",
    ".{ 1, 2, 3 }",
    "@sizeOf(struct { a: u64, b: u8 })",
    // Enums and unions.
    "blk: { const E = enum { a, b, c }; break :blk @intFromEnum(E.c); }",
    "blk: { const E = enum { north, south }; break :blk @tagName(E.south); }",
    "blk: { const U = union(enum) { n: u8, f: f32 }; break :blk @as(U, .{ .n = 7 }); }",
    // Control flow.
    "blk: { var s: u32 = 0; for (0..10) |i| s += i; break :blk s; }",
    "blk: { var n: u32 = 1; while (n < 100) n *= 2; break :blk n; }",
    "blk: { const x = 3; break :blk switch (x) { 1 => 10, 3 => 30, else => 0 }; }",
    // Builtins and reflection.
    "@typeName(u32)",
    "@typeInfo(u8).int.bits",
    "@min(3, 7, 1)",
    "@max(@as(u8, 4), 9)",
    "@popCount(@as(u8, 0b1011))",
    "@ctz(@as(u8, 8))",
    "@abs(@as(i32, -5))",
    "@errorName(error.Boom)",
    "@as(anyerror!u8, 5) catch 0",
    "@as(anyerror!u8, error.X) catch 0",
    // Modules (embedded std resolves natively too when a source is wired).
    "@import(\"builtin\").target.cpu.arch",
    "@TypeOf(@import(\"std\"))",
};

/// Multi-line sequences, for cross-line session state.
pub const sequences = [_][]const []const u8{
    &.{ "const x = 5;", "const y = x * 2;", "y + 1" },
    &.{ "const S = struct { a: u8 };", "@as(S, .{ .a = 3 }).a" },
    &.{ "fn f(n: u32) u32 { return n + 1; }", "f(41)" },
    &.{ "const E = enum { a, b };", "@intFromEnum(E.b)" },
    &.{ "const p: u32 = 5;", "&p", "p + 1" },
};
