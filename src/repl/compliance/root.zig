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
const NativeModuleSource = @import("../module/Native.zig");
const WriterIo = @import("../io/writer_io.zig");

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

fn normalize(text: []const u8) []const u8 {
    return std.mem.trim(u8, text, " \r\n\t");
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
    const ns = try pool.createNamespace(gpa, .{});
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

// A comptime shift by billions of bits requests gigabytes in a single limb
// allocation -- the same evaluation the compiler performs (both OOM on it). Under
// the per-allocation cap that request fails as `error.OutOfMemory` instead of
// OS-killing the process, and the eval path surfaces it gracefully.
test "fuzz-harness: a pathological comptime allocation fails gracefully" {
    var capped: CappedAllocator = .{ .child = std.testing.allocator, .max_alloc_bytes = 512 * 1024 * 1024 };
    const gpa = capped.allocator();
    const out = replRun(gpa, &.{"-306690 <<| 95721572180"}) catch return;
    gpa.free(out);
}

// Fuzz target: exercise the runtime layer directly. The generic fuzzer above feeds
// arbitrary token streams, which almost never assemble into a top-level `var` plus a
// store reaching into it -- the exact shape the runtime store/load path handles. This
// generates that shape: a mutable global of a chosen type, a run of stores through a
// field/element/optional chain, and a final read. The grammar stays well-defined, so a
// value read back that disagrees with the shadow model is a real defect, not generated
// undefined behavior -- catching a wrong result, not just a crash.
test "fuzz: runtime mutable-global store/load round-trips" {
    try std.testing.fuzz({}, fuzzRuntime, .{});
}

fn fuzzRuntime(_: void, smith: *std.testing.Smith) anyerror!void {
    var capped: CappedAllocator = .{ .child = std.testing.allocator, .max_alloc_bytes = 512 * 1024 * 1024 };
    const gpa = capped.allocator();
    var prog: Io.Writer.Allocating = .init(gpa);
    defer prog.deinit();
    const expected = genRuntimeProgram(smith, &prog.writer) catch return;
    // A rejected run means the REPL does not yet support the generated combination; that
    // is not a store/load defect, so tolerate it. A run that succeeds must round-trip.
    const out = replRun(gpa, &.{prog.written()}) catch return;
    defer gpa.free(out);
    var want_buf: [32]u8 = undefined;
    const want = std.fmt.bufPrint(&want_buf, "{d}", .{expected}) catch return;
    std.testing.expectEqualStrings(want, normalize(out)) catch |err| {
        std.debug.print("runtime store/load mismatch for:\n{s}\n", .{prog.written()});
        return err;
    };
}

/// Emit a program that declares a mutable global, applies Smith-chosen stores through a
/// field/element/optional chain, and reads one location back; return the value that read
/// must produce. Indices stay in bounds and the optional stays non-null, so the program
/// is always well-defined.
fn genRuntimeProgram(smith: *std.testing.Smith, w: *Io.Writer) !u64 {
    const Shape = enum { scalar, array, record, nested_record, matrix, optional };
    const max_ops = 8;
    switch (smith.value(Shape)) {
        .scalar => {
            var model: u32 = 0;
            try w.writeAll("var g: u32 = 0;\nblk: {\n");
            for (0..max_ops) |_| {
                if (smith.eos()) break;
                model = smith.value(u32);
                try w.print("g = {d};\n", .{model});
            }
            try w.writeAll("break :blk g;\n}");
            return model;
        },
        .array => {
            var model = [_]u32{ 0, 0, 0, 0 };
            try w.writeAll("var g: [4]u32 = .{ 0, 0, 0, 0 };\nblk: {\n");
            for (0..max_ops) |_| {
                if (smith.eos()) break;
                const i = smith.index(model.len);
                model[i] = smith.value(u32);
                try w.print("g[{d}] = {d};\n", .{ i, model[i] });
            }
            const r = smith.index(model.len);
            try w.print("break :blk g[{d}];\n}}", .{r});
            return model[r];
        },
        .record => {
            var model = [_]u32{ 0, 0 };
            try w.writeAll("var g: struct { a: u32, b: u32 } = .{ .a = 0, .b = 0 };\nblk: {\n");
            for (0..max_ops) |_| {
                if (smith.eos()) break;
                const f = smith.index(model.len);
                model[f] = smith.value(u32);
                try w.print("g.{c} = {d};\n", .{ @as(u8, 'a') + @as(u8, @intCast(f)), model[f] });
            }
            const r = smith.index(model.len);
            try w.print("break :blk g.{c};\n}}", .{@as(u8, 'a') + @as(u8, @intCast(r))});
            return model[r];
        },
        .nested_record => {
            var model: u32 = 0;
            try w.writeAll("var g: struct { p: struct { w: u32 } } = .{ .p = .{ .w = 0 } };\nblk: {\n");
            for (0..max_ops) |_| {
                if (smith.eos()) break;
                model = smith.value(u32);
                // Alternate reaching the leaf and replacing the whole inner struct.
                if (smith.value(bool))
                    try w.print("g.p.w = {d};\n", .{model})
                else
                    try w.print("g.p = .{{ .w = {d} }};\n", .{model});
            }
            try w.writeAll("break :blk g.p.w;\n}");
            return model;
        },
        .matrix => {
            var model = [_][2]u32{ .{ 0, 0 }, .{ 0, 0 } };
            try w.writeAll("var g: [2][2]u32 = .{ .{ 0, 0 }, .{ 0, 0 } };\nblk: {\n");
            for (0..max_ops) |_| {
                if (smith.eos()) break;
                const i = smith.index(model.len);
                const j = smith.index(model[i].len);
                model[i][j] = smith.value(u32);
                try w.print("g[{d}][{d}] = {d};\n", .{ i, j, model[i][j] });
            }
            const ri = smith.index(model.len);
            const rj = smith.index(model[ri].len);
            try w.print("break :blk g[{d}][{d}];\n}}", .{ ri, rj });
            return model[ri][rj];
        },
        .optional => {
            var model: u32 = 0;
            // Init non-null and only ever store the payload, so `g.?` stays defined.
            try w.writeAll("var g: ?u32 = 0;\nblk: {\n");
            for (0..max_ops) |_| {
                if (smith.eos()) break;
                model = smith.value(u32);
                try w.print("g.? = {d};\n", .{model});
            }
            try w.writeAll("break :blk g.?;\n}");
            return model;
        },
    }
}

fn fuzzEval(_: void, smith: *std.testing.Smith) anyerror!void {
    // A pathological comptime computation -- e.g. a shift by billions of bits --
    // requests gigabytes in a single allocation. Uncapped, that request succeeds
    // under memory overcommit and the fuzz process is OS-killed on first write,
    // before the allocator can report failure. Capping the per-allocation size
    // turns it into `error.OutOfMemory`, which the eval path already surfaces and
    // the `catch return` below tolerates, so the fuzzer survives the input.
    var capped: CappedAllocator = .{ .child = std.testing.allocator, .max_alloc_bytes = 512 * 1024 * 1024 };
    const gpa = capped.allocator();
    const token_smith = try gpa.create(std.zig.TokenSmith);
    defer gpa.destroy(token_smith);
    token_smith.* = .gen(smith);
    const src = token_smith.source();
    if (src.len == 0) return; // eval.run requires non-empty input (the REPL never feeds it a blank line)
    const out = replRun(gpa, &.{src}) catch return;
    gpa.free(out);
}

/// Wraps a child allocator, failing any single allocation or in-place grow that
/// exceeds `max_alloc_bytes` instead of forwarding it. Frees and shrinks pass
/// straight through, so the child's leak tracking stays intact.
const CappedAllocator = struct {
    child: std.mem.Allocator,
    max_alloc_bytes: usize,

    fn alloc(ctx: *anyopaque, len: usize, alignment: std.mem.Alignment, ret_addr: usize) ?[*]u8 {
        const self: *CappedAllocator = @ptrCast(@alignCast(ctx));
        if (len > self.max_alloc_bytes) return null;
        return self.child.rawAlloc(len, alignment, ret_addr);
    }
    fn resize(ctx: *anyopaque, memory: []u8, alignment: std.mem.Alignment, new_len: usize, ret_addr: usize) bool {
        const self: *CappedAllocator = @ptrCast(@alignCast(ctx));
        if (new_len > self.max_alloc_bytes) return false;
        return self.child.rawResize(memory, alignment, new_len, ret_addr);
    }
    fn remap(ctx: *anyopaque, memory: []u8, alignment: std.mem.Alignment, new_len: usize, ret_addr: usize) ?[*]u8 {
        const self: *CappedAllocator = @ptrCast(@alignCast(ctx));
        if (new_len > self.max_alloc_bytes) return null;
        return self.child.rawRemap(memory, alignment, new_len, ret_addr);
    }
    fn free(ctx: *anyopaque, memory: []u8, alignment: std.mem.Alignment, ret_addr: usize) void {
        const self: *CappedAllocator = @ptrCast(@alignCast(ctx));
        self.child.rawFree(memory, alignment, ret_addr);
    }

    const vtable: std.mem.Allocator.VTable = .{ .alloc = alloc, .resize = resize, .remap = remap, .free = free };

    fn allocator(self: *CappedAllocator) std.mem.Allocator {
        return .{ .ptr = self, .vtable = &vtable };
    }
};

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
    const ns = try pool.createNamespace(gpa, .{});
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
    // Render with the session, like the interactive REPL, so struct values print their field names.
    try render.render(value, &pool, &session, &out_writer);
    return gpa.dupe(u8, std.mem.trimEnd(u8, out_writer.buffered(), "\n"));
}

// The evaluated Io helper's writer drain calls `__repl_write(ptr, len)`; the interpreter performs that
// leaf against the host Io's stderr. A `WriterIo` over `out` captures it. The extern and call here stand
// in for that helper, exercising the runtime-I/O sink end to end without the full `std.debug.print` stack.
test "runtime I/O: __repl_write emits its argument bytes to the session sink" {
    const gpa = std.testing.allocator;
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

    var out: Io.Writer.Allocating = .init(gpa);
    defer out.deinit();
    var host: WriterIo = .{ .writer = &out.writer };
    session.runtime.io = host.io();
    var diag: Io.Writer.Allocating = .init(gpa);
    defer diag.deinit();

    _ = try eval.run(&session, "extern fn __repl_write(fd: i64, ptr: [*]const u8, len: usize) void;", &diag.writer);
    _ = try eval.run(&session, "blk: { __repl_write(2, \"Hi\", 2); break :blk 0; }", &diag.writer);
    try std.testing.expectEqualStrings("Hi", out.written());
}

// The full `std.debug.print` stack, end to end: with a host Io wired, the intrinsic `Io` is installed
// and the formatted bytes reach that Io's stderr (here a `WriterIo` over `out`). Reaching the write leaf
// required folding the comptime-required `@Int` operands inside `std.Progress`, so this guards that path.
test "runtime I/O: std.debug.print emits formatted bytes to the session sink" {
    const gpa = std.testing.allocator;
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

    var out: Io.Writer.Allocating = .init(gpa);
    defer out.deinit();
    var host: WriterIo = .{ .writer = &out.writer };
    session.runtime.io = host.io();
    var diag: Io.Writer.Allocating = .init(gpa);
    defer diag.deinit();

    _ = try eval.run(&session, "const std = @import(\"std\");", &diag.writer);
    _ = try eval.run(&session, "std.debug.print(\"Hi {d}!\\n\", .{42})", &diag.writer);
    try std.testing.expectEqualStrings("Hi 42!\n", out.written());
}

// The clock read-back: `Io.Clock.now` reaches `__repl_now`, which the interpreter performs against the
// host Io, materializing the reading as a runtime `i64`. The value is real time, so the case asserts a
// derived boolean rather than a fixed number: a `.real` reading is past 2020, and consecutive `.awake`
// readings do not go backwards. Uses the threaded Io directly -- its clock is the real one.
test "runtime I/O: the clock read-back returns a real host timestamp" {
    const gpa = std.testing.allocator;
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
    session.runtime.io = io;

    var diag: Io.Writer.Allocating = .init(gpa);
    defer diag.deinit();

    _ = try eval.run(&session, "const io = @import(\"root\").std_options_debug_io;", &diag.writer);
    try expectRendersTrue(gpa, &session, "@import(\"std\").Io.Clock.now(.real, io).nanoseconds > 1600000000000000000");
    try expectRendersTrue(gpa, &session, "blk: { const std = @import(\"std\"); const a = std.Io.Clock.now(.awake, io); const b = std.Io.Clock.now(.awake, io); break :blk b.nanoseconds >= a.nanoseconds; }");
}

// The filesystem read: `openFile` reaches `__repl_open`, which opens the host file and returns its
// handle-table index; `readStreaming` reaches `__repl_read`, which reads host bytes and stores them back
// into the interpreter buffer. Reads `build.zig.zon` from the test's cwd (it begins with `.`), and
// checks a missing file surfaces the error. Uses the threaded Io directly -- its filesystem is the real
// one.
test "runtime I/O: openFile + read materializes host bytes into the interpreter buffer" {
    const gpa = std.testing.allocator;
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
    session.runtime.io = io;

    var diag: Io.Writer.Allocating = .init(gpa);
    defer diag.deinit();

    _ = try eval.run(&session, "const std = @import(\"std\"); const io = @import(\"root\").std_options_debug_io;", &diag.writer);
    try expectRendersTrue(gpa, &session, "blk: { var buf: [8]u8 = undefined; const f = std.Io.Dir.cwd().openFile(io, \"build.zig.zon\", .{}) catch break :blk false; const n = f.readStreaming(io, &.{buf[0..]}) catch break :blk false; break :blk n > 0 and buf[0] == '.'; }");
    try expectRendersTrue(gpa, &session, "if (std.Io.Dir.cwd().openFile(io, \"no-such-file-zzz\", .{})) |_| false else |_| true");
}

// The filesystem close: `File.close` reaches `__repl_close`, which ends the host file's lifetime and
// frees its descriptor. Opening and closing the same file repeatedly keeps every read working (close
// does not disturb later opens) and reuses the freed slot, so the handle table stays bounded rather than
// growing once per open. The bound is the property the descriptor namespace fix guarantees, so the case
// asserts the table's size directly.
test "runtime I/O: close frees the descriptor and the handle table stays bounded" {
    const gpa = std.testing.allocator;
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
    session.runtime.io = io;

    var diag: Io.Writer.Allocating = .init(gpa);
    defer diag.deinit();

    _ = try eval.run(&session, "const std = @import(\"std\"); const io = @import(\"root\").std_options_debug_io;", &diag.writer);
    try expectRendersTrue(gpa, &session,
        \\blk: {
        \\    var i: usize = 0;
        \\    while (i < 5) : (i += 1) {
        \\        var buf: [1]u8 = undefined;
        \\        const f = std.Io.Dir.cwd().openFile(io, "build.zig.zon", .{}) catch break :blk false;
        \\        const n = f.readStreaming(io, &.{buf[0..]}) catch break :blk false;
        \\        if (n == 0) break :blk false;
        \\        f.close(io);
        \\    }
        \\    break :blk true;
        \\}
    );
    try std.testing.expectEqual(@as(usize, 1), session.runtime.open_files.items.len);
}

fn expectRendersTrue(gpa: std.mem.Allocator, session: *Session, src: []const u8) !void {
    var diag: Io.Writer.Allocating = .init(gpa);
    defer diag.deinit();
    const value = (try eval.run(session, src, &diag.writer)).value.?;
    var buf: [16]u8 = undefined;
    var w = Io.Writer.fixed(&buf);
    try render.render(value, session.intern_pool, session, &w);
    try std.testing.expectEqualStrings("true", w.buffered());
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
    _ = @import("comptime_scope_test.zig");
    _ = @import("control_flow_test.zig");
    _ = @import("diagnostics_test.zig");
    _ = @import("enum_test.zig");
    _ = @import("error_test.zig");
    _ = @import("import_test.zig");
    _ = @import("fn_test.zig");
    _ = @import("memory_test.zig");
    _ = @import("module_test.zig");
    _ = @import("optional_test.zig");
    _ = @import("pointer_test.zig");
    _ = @import("reflect_test.zig");
    _ = @import("repl_test.zig");
    _ = @import("sad_paths_test.zig");
    _ = @import("slice_test.zig");
    _ = @import("string_render_test.zig");
    _ = @import("struct_test.zig");
    _ = @import("switch_test.zig");
    _ = @import("typeof_test.zig");
    _ = @import("union_test.zig");
    _ = @import("vector_test.zig");
}
