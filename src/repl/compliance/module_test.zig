const std = @import("std");
const builtin = @import("builtin");
const testing = std.testing;
const Io = std.Io;

const compliance = @import("root.zig");
const eval = @import("../eval.zig");
const Session = @import("../Session.zig");
const InternPool = @import("../sema/InternPool.zig");
const Value = @import("../sema/Value.zig");
const render = @import("../render/Value.zig");
const ModuleSource = @import("../module/Source.zig");
const NativeModuleSource = @import("../module/Native.zig");

/// A bool as the string `render` prints it, for comptime-derived `.want` values.
fn comptimeBool(comptime b: bool) []const u8 {
    return if (b) "true" else "false";
}

/// One compliance probe: an expression and the string `render` should print.
const Probe = struct { src: []const u8, want: []const u8 };

/// A probe for every scalar `builtin` declaration, derived from the evaluating
/// binary's own `@import("builtin")` so the expected values follow the host.
/// `generate()` emits exactly the bool and enum decls; the struct/string/slice
/// decls (target, cpu, zig_version_string, test_functions) are reached through
/// their own probes. An enum tag is compared with an escaped literal so keyword
/// tags (e.g. unwind_tables `.@"async"`) parse. A new emitted enum/bool decl is
/// covered automatically; a decl the compiler adds that `generate()` omits
/// surfaces here as a resolution failure.
fn builtinDeclProbes() []const Probe {
    var list: []const Probe = &.{};
    inline for (comptime std.meta.declarations(builtin)) |name| {
        switch (@typeInfo(@TypeOf(@field(builtin, name)))) {
            .bool => list = list ++ &[_]Probe{.{
                .src = "@import(\"builtin\")." ++ name,
                .want = comptimeBool(@field(builtin, name)),
            }},
            .@"enum" => list = list ++ &[_]Probe{.{
                .src = "@import(\"builtin\")." ++ name ++ " == .@\"" ++ @tagName(@field(builtin, name)) ++ "\"",
                .want = "true",
            }},
            else => {},
        }
    }
    return list;
}

/// Run one probe against `session`, printing and counting a mismatch rather than
/// aborting so every gap in a probe set surfaces in a single run.
fn runProbe(session: *Session, p: Probe, failures: *usize) void {
    expectReplValue(session, p.src, p.want) catch |err| {
        std.debug.print("PROBE FAILED ({s}): {s}\n", .{ @errorName(err), p.src });
        failures.* += 1;
    };
}

/// A module source backed by an in-memory string, so a fixture container can be
/// resolved without touching the filesystem.
const FixtureSource = struct {
    src: [:0]const u8,
    interface: ModuleSource = .{ .vtable = &vtable },

    const vtable: ModuleSource.VTable = .{ .read = read };

    fn read(source: *ModuleSource, gpa: std.mem.Allocator, path: []const u8) ModuleSource.Error![:0]u8 {
        _ = path;
        const self: *FixtureSource = @alignCast(@fieldParentPtr("interface", source));
        const buf = try gpa.allocSentinel(u8, self.src.len, 0);
        @memcpy(buf, self.src);
        return buf;
    }
};

/// Run one REPL expression against `session` and assert its rendered value.
fn expectReplValue(session: *Session, source: []const u8, expected: []const u8) !void {
    var diag: std.Io.Writer.Allocating = .init(session.gpa);
    defer diag.deinit();
    const value = (try eval.run(session, source, &diag.writer)).value orelse return error.NoValue;
    var buf: [256]u8 = undefined;
    var w = Io.Writer.fixed(&buf);
    try render.render(value, session.intern_pool, null, &w);
    try testing.expectEqualStrings(expected, std.mem.trimEnd(u8, w.buffered(), "\n"));
}

test "@import loads a module container and resolves its decls" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();
    const ns = try pool.createNamespace(gpa, .{});
    var session = Session.init(gpa, &pool, ns);
    defer session.deinit();

    var fixture: FixtureSource = .{ .src = "pub const marker = 123;" };
    session.module_source = &fixture.interface;

    try expectReplValue(&session, "@import(\"std\").marker", "123");
    try expectReplValue(&session, "@hasDecl(@import(\"std\"), \"marker\")", "true");
    try expectReplValue(&session, "@hasDecl(@import(\"std\"), \"nope\")", "false");
}

test "@import(std) reaches std.lang across files" {
    const gpa = testing.allocator;
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

    try expectReplValue(&session, "@intFromEnum(@import(\"std\").lang.ReduceOp.Add)", "5");
    try expectReplValue(&session, "@hasDecl(@import(\"std\").lang, \"Type\")", "true");
    try expectReplValue(&session, "@hasDecl(@import(\"std\").lang.Type, \"Int\")", "true");
    try expectReplValue(&session, "@hasField(@import(\"std\").lang.Type.Int, \"bits\")", "true");
}

test "@import(std) broad access probes" {
    const gpa = testing.allocator;
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

    const probes = [_]Probe{
        .{ .src = "@hasDecl(@import(\"std\"), \"mem\")", .want = "true" },
        .{ .src = "@hasDecl(@import(\"std\"), \"math\")", .want = "true" },
        .{ .src = "@hasDecl(@import(\"std\"), \"no_such_decl\")", .want = "false" },
        .{ .src = "@intFromEnum(@import(\"std\").lang.ReduceOp.And)", .want = "0" },
        .{ .src = "@intFromEnum(@import(\"std\").lang.ReduceOp.Mul)", .want = "6" },
        .{ .src = "@hasDecl(@import(\"std\").lang, \"CallingConvention\")", .want = "true" },
        .{ .src = "@hasField(@import(\"std\").lang.AtomicOrder, \"seq_cst\")", .want = "true" },
        .{ .src = "@hasDecl(@import(\"std\").lang.Type, \"Struct\")", .want = "true" },
        .{ .src = "@hasField(@import(\"std\").lang.Type.Int, \"signedness\")", .want = "true" },
        .{ .src = "@hasField(@import(\"std\").lang.Type.Pointer, \"size\")", .want = "true" },
        .{ .src = "@hasDecl(@import(\"std\").math, \"pi\")", .want = "true" },
        .{ .src = "@hasDecl(@import(\"std\").mem, \"eql\")", .want = "true" },
        .{ .src = "@hasDecl(@import(\"std\").meta, \"Tag\")", .want = "true" },
        .{ .src = "@hasDecl(@import(\"std\"), \"Io\")", .want = "true" },
        .{ .src = "@hasDecl(@import(\"std\").Io, \"Writer\")", .want = "true" },
        .{ .src = "@hasDecl(@import(\"std\").Io, \"Reader\")", .want = "true" },
        .{ .src = "@hasDecl(@import(\"std\").Io, \"File\")", .want = "true" },
        .{ .src = "@hasDecl(@import(\"std\").Io, \"VTable\")", .want = "true" },
        .{ .src = "@hasDecl(@import(\"std\").Io.Writer, \"Error\")", .want = "true" },
        .{ .src = "@hasDecl(@import(\"std\").Io.net, \"IpAddress\")", .want = "true" },
        .{ .src = "@hasDecl(@import(\"std\").http, \"Client\")", .want = "true" },
        .{ .src = "@intFromEnum(@import(\"std\").http.Method.GET)", .want = "0" },
        .{ .src = "@hasDecl(@import(\"std\").fmt, \"comptimePrint\")", .want = "true" },
        .{ .src = "@typeInfo(u8).int.bits", .want = "8" },
        .{ .src = "@typeInfo(u16).int.bits", .want = "16" },
        .{ .src = "@intFromEnum(@typeInfo(u8).int.signedness)", .want = "1" },
        .{ .src = "@intFromEnum(@typeInfo(i32).int.signedness)", .want = "0" },
        .{ .src = "@typeInfo(f32).float.bits", .want = "32" },
        .{ .src = "@typeInfo(f64).float.bits", .want = "64" },
        .{ .src = "@typeInfo(u8) == .int", .want = "true" },
        .{ .src = "@typeInfo(bool) == .bool", .want = "true" },
        .{ .src = "@typeInfo(void) == .void", .want = "true" },
        .{ .src = "@typeInfo(bool) == .int", .want = "false" },
        .{ .src = "@typeInfo(?u8).optional.child == u8", .want = "true" },
        .{ .src = "@typeInfo(@Vector(4, u8)).vector.len", .want = "4" },
        .{ .src = "@typeInfo(@Vector(4, u8)).vector.child == u8", .want = "true" },
        .{ .src = "@typeInfo([3]u8).array.len", .want = "3" },
        .{ .src = "@typeInfo([3]u8).array.child == u8", .want = "true" },
        .{ .src = "@typeInfo([3]u8).array.sentinel_ptr == null", .want = "true" },
        .{ .src = "@typeInfo([3:0]u8).array.sentinel_ptr == null", .want = "false" },
        .{ .src = "@typeInfo(*u8).pointer.child == u8", .want = "true" },
        .{ .src = "@typeInfo(*u8).pointer.size == .one", .want = "true" },
        .{ .src = "@typeInfo([]u8).pointer.size == .slice", .want = "true" },
        .{ .src = "@typeInfo(*const u8).pointer.attrs.@\"const\"", .want = "true" },
        .{ .src = "@typeInfo(*u8).pointer.attrs.@\"const\"", .want = "false" },
        .{ .src = "@typeInfo(*align(4) u8).pointer.attrs.@\"align\" == 4", .want = "true" },
        .{ .src = "@typeInfo(anyerror!u8).error_union.payload == u8", .want = "true" },
        .{ .src = "@typeInfo(anyerror!u8).error_union.error_set == anyerror", .want = "true" },
        .{ .src = "@typeInfo(anyerror).error_set.error_names == null", .want = "true" },
        .{ .src = "@typeInfo(error{ Foo, Bar }).error_set.error_names.?.len", .want = "2" },
        .{ .src = "@typeInfo(error{Foo}).error_set.error_names.?[0][0]", .want = "70" },
        .{ .src = "@typeInfo(enum { a, b, c }).@\"enum\".field_names.len", .want = "3" },
        .{ .src = "@typeInfo(enum { a, b, c }).@\"enum\".field_names[0][0]", .want = "97" },
        .{ .src = "@typeInfo(enum { a, b }).@\"enum\".tag_type == u1", .want = "true" },
        .{ .src = "@typeInfo(enum { a, b, c }).@\"enum\".tag_type == u2", .want = "true" },
        .{ .src = "@typeInfo(enum(u8) { a = 5, b }).@\"enum\".field_values[0]", .want = "5" },
        .{ .src = "@typeInfo(enum(u8) { a = 5, b }).@\"enum\".field_values[1]", .want = "6" },
        .{ .src = "@typeInfo(enum { a }).@\"enum\".mode == .exhaustive", .want = "true" },
        .{ .src = "@typeInfo(enum(u8) { a, _ }).@\"enum\".mode == .nonexhaustive", .want = "true" },
        .{ .src = "@typeInfo(enum { a, pub const x = 1; }).@\"enum\".decl_names.len", .want = "1" },
        .{ .src = "@typeInfo(enum { a, pub const x = 1; }).@\"enum\".decl_names[0][0] == 'x'", .want = "true" },
        .{ .src = "@typeInfo(union(enum) { a: u8, b: bool }).@\"union\".field_names.len", .want = "2" },
        .{ .src = "@typeInfo(union(enum) { a: u8, b: bool }).@\"union\".field_names[0][0]", .want = "97" },
        .{ .src = "@typeInfo(union(enum) { a: u8, b: bool }).@\"union\".field_types[0] == u8", .want = "true" },
        .{ .src = "@typeInfo(union(enum) { a: u8, b: bool }).@\"union\".field_types[1] == bool", .want = "true" },
        .{ .src = "@typeInfo(union(enum) { a: u8 }).@\"union\".tag_type != null", .want = "true" },
        .{ .src = "@typeInfo(union { a: u8 }).@\"union\".tag_type == null", .want = "true" },
        .{ .src = "@intFromEnum(@typeInfo(union(enum) { a: u8 }).@\"union\".layout)", .want = "0" },
        .{ .src = "@typeInfo(union(enum) { a: u8 }).@\"union\".field_attrs[0].@\"align\" == null", .want = "true" },
        .{ .src = "@typeInfo(union(enum) { a: u8 }).@\"union\".backing_integer == null", .want = "true" },
        .{ .src = "@typeInfo(union(enum) { a: u8 align(4) }).@\"union\".field_attrs[0].@\"align\" == 4", .want = "true" },
        .{ .src = "@typeInfo(struct { x: u8, y: bool }).@\"struct\".field_names.len", .want = "2" },
        .{ .src = "@typeInfo(struct { x: u8, y: bool }).@\"struct\".field_names[0][0]", .want = "120" },
        .{ .src = "@typeInfo(struct { x: u8, y: bool }).@\"struct\".field_types[0] == u8", .want = "true" },
        .{ .src = "@typeInfo(struct { x: u8, y: bool }).@\"struct\".field_types[1] == bool", .want = "true" },
        .{ .src = "@typeInfo(struct { x: u8 }).@\"struct\".is_tuple", .want = "false" },
        .{ .src = "@typeInfo(struct { x: u8 }).@\"struct\".field_attrs[0].@\"comptime\"", .want = "false" },
        .{ .src = "@typeInfo(struct { x: u8 }).@\"struct\".field_attrs[0].@\"align\" == null", .want = "true" },
        .{ .src = "@typeInfo(struct { x: u8 }).@\"struct\".field_attrs[0].default_value_ptr == null", .want = "true" },
        .{ .src = "@typeInfo(struct { x: u8 = 5 }).@\"struct\".field_attrs[0].default_value_ptr != null", .want = "true" },
        .{ .src = "@typeInfo(struct { x: u8 align(4) }).@\"struct\".field_attrs[0].@\"align\" == 4", .want = "true" },
        .{ .src = "@intFromEnum(@typeInfo(struct { x: u8 }).@\"struct\".layout)", .want = "0" },
        .{ .src = "@typeInfo(fn (u8) u8).@\"fn\".param_types.len", .want = "1" },
        .{ .src = "@typeInfo(fn (u8, bool) u8).@\"fn\".param_types.len", .want = "2" },
        .{ .src = "@typeInfo(fn (u8) u8).@\"fn\".param_types[0].? == u8", .want = "true" },
        .{ .src = "@typeInfo(fn (u8) u8).@\"fn\".return_type.? == u8", .want = "true" },
        .{ .src = "@typeInfo(fn (u8) u8).@\"fn\".is_generic", .want = "false" },
        .{ .src = "@typeInfo(fn (u8) u8).@\"fn\".attrs.@\"callconv\" == .auto", .want = "true" },
        .{ .src = "@typeInfo(fn (u8) u8).@\"fn\".attrs.varargs", .want = "false" },
        .{ .src = "@typeInfo(fn (u8) u8).@\"fn\".param_attrs[0].@\"noalias\"", .want = "false" },
        .{ .src = "@typeInfo(fn (noalias *u8) void).@\"fn\".param_attrs[0].@\"noalias\"", .want = "true" },
        .{ .src = "@Int(.unsigned, 8) == u8", .want = "true" },
        .{ .src = "@Int(.signed, 16) == i16", .want = "true" },
        .{ .src = "@Int(@typeInfo(u32).int.signedness, @typeInfo(u32).int.bits) == u32", .want = "true" },
        .{ .src = "@typeInfo(@Int(.unsigned, 7)).int.bits == 7", .want = "true" },
        .{ .src = "@Int(.unsigned, 0) == u0", .want = "true" },
        .{ .src = "@TypeOf(.{}) == @TypeOf(.{})", .want = "true" },
        .{ .src = "@TypeOf(.{}) == @TypeOf(.{ 1, 2 })", .want = "false" },
        .{ .src = "@TypeOf(.{}) == @TypeOf(.{ .x = 1 })", .want = "false" },
        .{ .src = "@typeInfo(@TypeOf(.{})).@\"struct\".is_tuple", .want = "true" },
        .{ .src = "@typeInfo(@TypeOf(.{})).@\"struct\".field_types.len == 0", .want = "true" },
        .{ .src = "@typeInfo(@TypeOf(.{})).@\"struct\".decl_names.len == 0", .want = "true" },
        .{ .src = "@typeInfo(@TypeOf(.{ 1, 2 })).@\"struct\".is_tuple", .want = "true" },
        .{ .src = "@typeInfo(@TypeOf(.{ 1, 2 })).@\"struct\".field_types.len == 2", .want = "true" },
        .{ .src = "@typeInfo(@TypeOf(.{ 1, 2 })).@\"struct\".field_types[0] == comptime_int", .want = "true" },
        .{ .src = "@typeInfo(@TypeOf(.{ @as(u8, 3) })).@\"struct\".field_types[0] == u8", .want = "true" },
        .{ .src = "@Vector(4, u8) == @Vector(4, u8)", .want = "true" },
        .{ .src = "@typeInfo(@Vector(4, u8)).vector.len == 4", .want = "true" },
        .{ .src = "@typeInfo(@Vector(4, u8)).vector.child == u8", .want = "true" },
        .{ .src = "@typeInfo(@Tuple(&.{ u8, u16 })).@\"struct\".is_tuple", .want = "true" },
        .{ .src = "@typeInfo(@Tuple(&.{ u8, u16 })).@\"struct\".field_types.len == 2", .want = "true" },
        .{ .src = "@typeInfo(@Tuple(&.{ u8, u16 })).@\"struct\".field_types[1] == u16", .want = "true" },
        .{ .src = "@Pointer(.one, .{}, u8, null) == *u8", .want = "true" },
        .{ .src = "@Pointer(.one, .{ .@\"const\" = true }, u8, null) == *const u8", .want = "true" },
        .{ .src = "@Pointer(.slice, .{}, u8, null) == []u8", .want = "true" },
        .{ .src = "@Pointer(.many, .{}, u8, @as(u8, 0)) == [*:0]u8", .want = "true" },
        .{ .src = "@Pointer(.one, .{ .@\"align\" = 4 }, u32, null) == *align(4) u32", .want = "true" },
        .{ .src = "@Fn(&.{u8}, &.{.{}}, u8, .{}) == fn (u8) u8", .want = "true" },
        .{ .src = "@Fn(&.{ u8, bool }, &.{ .{}, .{} }, void, .{}) == fn (u8, bool) void", .want = "true" },
        .{ .src = "@Fn(&.{*u8}, &.{.{ .@\"noalias\" = true }}, void, .{}) == fn (noalias *u8) void", .want = "true" },
        .{ .src = "@typeInfo(@Enum(u8, .exhaustive, &.{ \"a\", \"b\" }, &.{ 0, 1 })).@\"enum\".tag_type == u8", .want = "true" },
        .{ .src = "@typeInfo(@Enum(u8, .exhaustive, &.{ \"a\", \"b\" }, &.{ 0, 1 })).@\"enum\".field_names.len == 2", .want = "true" },
        .{ .src = "@typeInfo(@Enum(u8, .exhaustive, &.{ \"a\", \"b\" }, &.{ 0, 1 })).@\"enum\".field_values[1] == 1", .want = "true" },
        .{ .src = "@typeInfo(@Enum(u16, .nonexhaustive, &.{\"x\"}, &.{5})).@\"enum\".mode == .nonexhaustive", .want = "true" },
        .{ .src = "@typeInfo(@Struct(.auto, null, &.{ \"a\", \"b\" }, &.{ u8, u16 }, &.{ .{}, .{} })).@\"struct\".field_types.len == 2", .want = "true" },
        .{ .src = "@typeInfo(@Struct(.auto, null, &.{ \"a\", \"b\" }, &.{ u8, u16 }, &.{ .{}, .{} })).@\"struct\".field_types[1] == u16", .want = "true" },
        .{ .src = "@typeInfo(@Struct(.auto, null, &.{\"x\"}, &.{u8}, &.{.{}})).@\"struct\".is_tuple", .want = "false" },
        .{ .src = "(@Struct(.auto, null, &.{\"x\"}, &.{u8}, &.{.{}}){ .x = 5 }).x == 5", .want = "true" },
        .{ .src = "(@Struct(.auto, null, &.{ \"a\", \"b\" }, &.{ u8, u16 }, &.{ .{ .default_value_ptr = &@as(u8, 9) }, .{} }){ .b = 2 }).a == 9", .want = "true" },
        .{ .src = "@alignOf(@Struct(.auto, null, &.{ \"a\", \"b\" }, &.{ u8, u32 }, &.{ .{ .@\"align\" = 16 }, .{} })) == 16", .want = "true" },
        .{ .src = "@typeInfo(@Union(.auto, null, &.{ \"a\", \"b\" }, &.{ u8, u16 }, &.{ .{}, .{} })).@\"union\".field_types.len == 2", .want = "true" },
        .{ .src = "@typeInfo(@Union(.auto, null, &.{ \"a\", \"b\" }, &.{ u8, u16 }, &.{ .{}, .{} })).@\"union\".field_types[1] == u16", .want = "true" },
        .{ .src = "@typeInfo(@Union(.auto, null, &.{\"x\"}, &.{u8}, &.{.{}})).@\"union\".tag_type == null", .want = "true" },
        .{ .src = "@typeInfo(@Union(.auto, @Enum(u8, .exhaustive, &.{\"x\"}, &.{0}), &.{\"x\"}, &.{u8}, &.{.{}})).@\"union\".tag_type != null", .want = "true" },
        .{ .src = "(struct { cc: @import(\"std\").lang.CallingConvention = .auto }{}).cc == .auto", .want = "true" },
        .{ .src = "@typeInfo(u8).int.signedness == .signed", .want = "false" },
        .{ .src = "1 << @as(u16, 8)", .want = "256" },
        .{ .src = "@import(\"std\").math.maxInt(u8)", .want = "255" },
        .{ .src = "@import(\"std\").math.maxInt(i8)", .want = "127" },
        .{ .src = "@import(\"std\").math.minInt(u8)", .want = "0" },
        .{ .src = "@import(\"std\").math.minInt(i8)", .want = "-128" },
        .{ .src = "@TypeOf(@import(\"builtin\").target) == @import(\"std\").Target", .want = "true" },
        .{ .src = "@TypeOf(@import(\"builtin\").target.cCallingConvention().?) == @import(\"std\").builtin.CallingConvention", .want = "true" },
        .{ .src = "@import(\"builtin\").target.cpu.arch == .@\"" ++ @tagName(builtin.target.cpu.arch) ++ "\"", .want = "true" },
        .{ .src = "@import(\"builtin\").target.os.tag == .@\"" ++ @tagName(builtin.target.os.tag) ++ "\"", .want = "true" },
    };

    var failures: usize = 0;
    for (&probes) |p| runProbe(&session, p, &failures);
    for (comptime builtinDeclProbes()) |p| runProbe(&session, p, &failures);
    try testing.expectEqual(@as(usize, 0), failures);
}

test "reify constructors: value paths and rejected inputs" {
    const gpa = testing.allocator;
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

    const values = [_]struct { src: []const u8, want: []const u8 }{
        .{ .src = "@intFromEnum(@Enum(u8, .exhaustive, &.{ \"a\", \"b\" }, &.{ 0, 1 }).b) == 1", .want = "true" },
        .{ .src = "(@Struct(.auto, null, &.{ \"a\", \"b\" }, &.{ u8, bool }, &.{ .{}, .{} }){ .a = 3, .b = true }).b", .want = "true" },
        .{ .src = "(@Union(.auto, @Enum(u8, .exhaustive, &.{\"x\"}, &.{0}), &.{\"x\"}, &.{u8}, &.{.{}}){ .x = 7 }).x == 7", .want = "true" },
        .{ .src = "(@Union(.auto, null, &.{\"x\"}, &.{u8}, &.{.{}}){ .x = 7 }).x == 7", .want = "true" },
        .{ .src = "@typeInfo(@Struct(.@\"extern\", null, &.{\"a\"}, &.{u8}, &.{.{}})).@\"struct\".layout == .@\"extern\"", .want = "true" },
        .{ .src = "@typeInfo(@Struct(.@\"packed\", null, &.{\"a\"}, &.{u8}, &.{.{}})).@\"struct\".layout == .@\"packed\"", .want = "true" },
        .{ .src = "@typeInfo(@Struct(.@\"packed\", u8, &.{\"a\"}, &.{u8}, &.{.{}})).@\"struct\".backing_integer == u8", .want = "true" },
        .{ .src = "@typeInfo(@Union(.@\"extern\", null, &.{\"a\"}, &.{u8}, &.{.{}})).@\"union\".layout == .@\"extern\"", .want = "true" },
        .{ .src = "@typeInfo(@Union(.@\"packed\", u8, &.{\"a\"}, &.{u8}, &.{.{}})).@\"union\".backing_integer == u8", .want = "true" },
    };
    for (values) |p| try expectReplValue(&session, p.src, p.want);

    const rejected = [_]struct { src: []const u8, needle: []const u8 }{
        .{ .src = "@Struct(.auto, null, &.{\"a\"}, &.{u8}, &.{.{ .@\"comptime\" = true }})", .needle = "comptime field without default initialization value" },
        .{ .src = "@Struct(.@\"packed\", null, &.{\"a\"}, &.{u8}, &.{.{ .@\"align\" = 4 }})", .needle = "packed struct fields cannot be aligned" },
        .{ .src = "@Struct(.auto, u8, &.{\"a\"}, &.{u8}, &.{.{}})", .needle = "non-packed struct does not support backing integer type" },
        .{ .src = "@Union(.@\"extern\", @Enum(u8, .exhaustive, &.{\"x\"}, &.{0}), &.{\"x\"}, &.{u8}, &.{.{}})", .needle = "extern union does not support enum tag type" },
        .{ .src = "@Union(.@\"packed\", null, &.{\"a\"}, &.{u8}, &.{.{ .@\"align\" = 4 }})", .needle = "packed union fields cannot be aligned" },
        .{ .src = "(@Struct(.auto, null, &.{\"a\"}, &.{u8}, &.{.{}}){ .a = 1 }).b", .needle = "no field named 'b'" },
        .{ .src = "@Enum(u8, .exhaustive, &.{\"a\"}, &.{0}).zzz", .needle = "has no member named 'zzz'" },
        .{ .src = "@Struct(.auto, null, &.{ \"a\", \"a\" }, &.{ u8, u16 }, &.{ .{}, .{} })", .needle = "duplicate struct field 'a' at index '1" },
        .{ .src = "@Enum(u8, .exhaustive, &.{ \"x\", \"x\" }, &.{ 0, 1 })", .needle = "duplicate enum field 'x' at index '1'" },
        .{ .src = "@Enum(u8, .exhaustive, &.{ \"a\", \"b\" }, &.{ 1, 1 })", .needle = "enum tag value '1' for field 'b' already taken" },
        .{ .src = "@Union(.auto, null, &.{ \"u\", \"u\" }, &.{ u8, u16 }, &.{ .{}, .{} })", .needle = "duplicate union field 'u' at index '1" },
    };
    for (rejected) |p| {
        var diag: std.Io.Writer.Allocating = .init(gpa);
        defer diag.deinit();
        if (eval.run(&session, p.src, &diag.writer)) |_| {
            std.debug.print("expected rejection but accepted: {s}\n", .{p.src});
            return error.TestUnexpectedAcceptance;
        } else |err| switch (err) {
            error.AnalysisFail => {},
            else => return err,
        }
        if (std.mem.indexOf(u8, diag.written(), p.needle) == null) {
            std.debug.print("diagnostic for '{s}' did not contain '{s}':\n{s}\n", .{ p.src, p.needle, diag.written() });
            return error.TestDiagnosticMismatch;
        }
    }
}

test "render: a struct value prints .{ .field = val }" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();
    const ns = try pool.createNamespace(gpa, .{});
    var session = Session.init(gpa, &pool, ns);
    defer session.deinit();

    var diag: std.Io.Writer.Allocating = .init(gpa);
    defer diag.deinit();
    _ = try eval.run(&session, "const P = struct { x: u8, y: u8 };", &diag.writer);
    const value = (try eval.run(&session, "P{ .x = 3, .y = 7 }", &diag.writer)).value.?;

    var buf: [256]u8 = undefined;
    var w = Io.Writer.fixed(&buf);
    // A struct prints `.{ .field = val }` (no type-name prefix), matching `{any}` and the
    // compiler's `printAggregate`; without a session to read field names, positionally.
    try render.render(value, &pool, &session, &w);
    try testing.expectEqualStrings(".{ .x = 3, .y = 7 }", w.buffered());

    var buf2: [256]u8 = undefined;
    var w2 = Io.Writer.fixed(&buf2);
    try render.render(value, &pool, null, &w2);
    try testing.expectEqualStrings("{ 3, 7 }", w2.buffered());
}

test "render: enum and union values print their names" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();
    const ns = try pool.createNamespace(gpa, .{});
    var session = Session.init(gpa, &pool, ns);
    defer session.deinit();
    var diag: std.Io.Writer.Allocating = .init(gpa);
    defer diag.deinit();

    const cases = [_]struct { decl: []const u8, expr: []const u8, want: []const u8 }{
        .{ .decl = "const E1 = enum { a, b, c };", .expr = "E1.b", .want = ".b" },
        .{ .decl = "const E2 = enum(u8) { a = 10, b = 20 };", .expr = "E2.b", .want = ".b" },
        .{ .decl = "const U = union(enum) { a: u8, b: bool };", .expr = "U{ .b = true }", .want = ".{ .b = true }" },
    };
    for (cases) |c| {
        _ = try eval.run(&session, c.decl, &diag.writer);
        const value = (try eval.run(&session, c.expr, &diag.writer)).value.?;
        var buf: [128]u8 = undefined;
        var w = Io.Writer.fixed(&buf);
        try render.render(value, &pool, &session, &w);
        try testing.expectEqualStrings(c.want, w.buffered());
    }
}

test "render: a packed struct value unpacks its fields; a packed union shows the backing bits" {
    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();
    const ns = try pool.createNamespace(gpa, .{});
    var session = Session.init(gpa, &pool, ns);
    defer session.deinit();
    var diag: std.Io.Writer.Allocating = .init(gpa);
    defer diag.deinit();

    _ = try eval.run(&session, "const S = packed struct(u8) { a: u4, b: u4 };", &diag.writer);
    _ = try eval.run(&session, "const sv: S = @bitCast(@as(u8, 0x21));", &diag.writer);
    const s = (try eval.run(&session, "sv", &diag.writer)).value.?;
    var sbuf: [128]u8 = undefined;
    var sw = Io.Writer.fixed(&sbuf);
    try render.render(s, &pool, &session, &sw);
    try testing.expectEqualStrings(".{ .a = 1, .b = 2 }", sw.buffered());

    // A packed union has no active field, so it prints the backing integer as an explicit @bitCast.
    _ = try eval.run(&session, "const U = packed union { a: u8, b: u8 };", &diag.writer);
    _ = try eval.run(&session, "const uv: U = @bitCast(@as(u8, 0x21));", &diag.writer);
    const u = (try eval.run(&session, "uv", &diag.writer)).value.?;
    var ubuf: [128]u8 = undefined;
    var uw = Io.Writer.fixed(&ubuf);
    try render.render(u, &pool, &session, &uw);
    try testing.expectEqualStrings("@bitCast(@as(u8, 33))", uw.buffered());
}

test "compliance: a failure raised inside a loaded module still surfaces its message" {
    // A @compileError reached inside std's own source must surface its message rather
    // than vanish into an empty result; the caret re-reads the module's source on demand.
    try compliance.expectDiagnostic(testing.allocator, &.{ "const std = @import(\"std\");", "std.math.sqrt(@as(i32, 4))" }, "sqrt not implemented");
}
