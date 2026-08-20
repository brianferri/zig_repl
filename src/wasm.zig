//! Wasm frontend entry: a line-in / text-out REPL the browser drives. The result buffer is a module global,
//! reset at the start of each call and read via `replResultPtr`/`replResultLen` before the next.

const std = @import("std");
const repl = @import("repl");
const drivers_wasm = @import("drivers_wasm");

const eval = repl.eval;
const Session = repl.Session;
const InternPool = repl.sema.InternPool;
const InputShape = repl.front.InputShape;
const render_value = repl.render.Value;
const Type = repl.sema.Type;
const outline = drivers_wasm.outline;
const Commands = drivers_wasm.commands;
const LineInput = drivers_wasm.LineInput;
const themes = drivers_wasm.themes;

// `wasm_allocator` grows linear memory as needed, which detaches the host's view of
// `memory.buffer`; the page re-reads it after every call that allocates.
const gpa = std.heap.wasm_allocator;

// The standard library, gzip-tarred into the binary by `build.zig`. Freestanding
// wasm has no filesystem, so this is how `@import("std")` resolves here.
const embedded_std = @embedFile("embedded_std");

var pool: InternPool = undefined;
var session: Session = undefined;
var module_source: repl.module.Buffer = undefined;
// The user's editable files, stacked over the embedded std by `project`: an
// `@import` resolves from `vfs` first and falls through to `module_source`.
var vfs: repl.module.Vfs = undefined;
var project: repl.module.Layered = undefined;
var output: std.Io.Writer.Allocating = undefined;
// Freestanding wasm has no OS `Io`, so the host Io the interpreter delegates to is one backed by
// `output`: its stderr routes to the result buffer, so evaluated `std.debug.print` lands inline with
// rendered values.
var host_io: repl.io.WriterIo = undefined;
var line_input: LineInput = undefined;
var ready = false;

/// Set up the interpreter. Safe to call more than once; later calls are
/// no-ops. Returns false if setup allocation failed.
export fn replInit() bool {
    if (ready) return true;
    pool = InternPool.init(gpa) catch return false;
    const root_namespace = pool.createNamespace(gpa, .{}) catch return false;
    session = Session.init(gpa, &pool, root_namespace);
    module_source = repl.module.Buffer.init(gpa, embedded_std) catch return false;
    vfs = repl.module.Vfs.init(gpa);
    project = repl.module.Layered.init(&vfs.interface, &module_source.interface);
    session.module_source = &project.interface;
    output = .init(gpa);
    // Route every runtime leaf through this host Io; its stderr lands in `output` and
    // bypasses the freestanding posix stack the default debug writer would reach.
    host_io = .{ .writer = &output.writer };
    session.runtime.io = host_io.io();
    line_input.setup(gpa);
    ready = true;
    return true;
}

/// The matching `replEval` frees the returned buffer; null on allocation failure.
export fn replAlloc(len: usize) ?[*]u8 {
    const buf = gpa.alloc(u8, len) catch return null;
    return buf.ptr;
}

/// The `ptr` buffer is freed here; the rendered result and diagnostics land in the result buffer, read
/// via `replResultPtr`/`replResultLen` before the next call.
export fn replEval(ptr: [*]u8, len: usize) void {
    if (!ready and !replInit()) return;
    defer gpa.free(ptr[0..len]);
    output.clearRetainingCapacity();
    dispatch(ptr[0..len]) catch |err| {
        output.writer.print("internal error: {s}\n", .{@errorName(err)}) catch {};
    };
}

export fn replResultPtr() [*]const u8 {
    return output.written().ptr;
}

export fn replResultLen() usize {
    return output.written().len;
}

/// Feed `len` bytes of xterm key sequences (the `ptr` buffer, freed here) to the
/// shared line editor. Read `replInputBuffer*`/`replInputCursor` afterward to
/// render, and `replInputTakeSubmitted` for a completed line to `replEval`.
export fn replInputFeed(ptr: [*]u8, len: usize) void {
    if (!ready and !replInit()) return;
    defer gpa.free(ptr[0..len]);
    line_input.feed(ptr[0..len]) catch {};
}

export fn replInputBufferPtr() [*]const u8 {
    return line_input.buffer().ptr;
}

export fn replInputBufferLen() usize {
    return line_input.buffer().len;
}

export fn replInputCursor() usize {
    return line_input.cursor();
}

/// The length of a line submitted since the last call (Enter was pressed), or
/// -1 if none; read the bytes at `replInputSubmittedPtr`. Consumed once.
export fn replInputTakeSubmitted() isize {
    if (line_input.takeSubmitted()) |line| return @intCast(line.len);
    return -1;
}

export fn replInputSubmittedPtr() [*]const u8 {
    return line_input.submitted.items.ptr;
}

/// Write the registered themes as JSON into the result buffer, so a graphical
/// frontend paints its surfaces and prompt from the same registry the tty draws from.
export fn replThemes() void {
    if (!ready and !replInit()) return;
    output.clearRetainingCapacity();
    writeThemesJson(&output.writer) catch {};
}

fn writeThemesJson(w: *std.Io.Writer) !void {
    // Project away the prompt text and its SGR bytes; std.json renders the rest.
    const Entry = struct {
        name: []const u8,
        accent: themes.Theme.Rgb,
        palette: themes.Theme.Palette,
    };
    var entries: [themes.themes.len]Entry = undefined;
    for (themes.themes, &entries) |theme, *entry| {
        entry.* = .{ .name = theme.name, .accent = theme.primary.color.rgb, .palette = theme.palette };
    }
    try std.json.Stringify.value(entries[0..], .{}, w);
}

export fn replFsList() void {
    if (!ready and !replInit()) return;
    output.clearRetainingCapacity();
    const entries = vfs.interface.list(gpa) catch return;
    defer repl.module.Fs.freeList(gpa, entries);
    const w = &output.writer;
    w.writeByte('[') catch return;
    for (entries, 0..) |entry, i| {
        if (i != 0) w.writeByte(',') catch return;
        std.json.Stringify.value(.{ .path = entry.path, .kind = @tagName(entry.kind) }, .{}, w) catch return;
    }
    w.writeByte(']') catch return;
}

export fn replFsRead(ptr: [*]u8, len: usize) void {
    if (!ready and !replInit()) return;
    defer gpa.free(ptr[0..len]);
    output.clearRetainingCapacity();
    if (vfs.get(ptr[0..len])) |bytes| output.writer.writeAll(bytes) catch {};
}

export fn replFsWrite(path: [*]u8, path_len: usize, data: [*]u8, data_len: usize) void {
    if (!ready and !replInit()) return;
    defer gpa.free(path[0..path_len]);
    defer gpa.free(data[0..data_len]);
    vfs.interface.write(path[0..path_len], data[0..data_len]) catch {};
}

export fn replFsMkdir(ptr: [*]u8, len: usize) void {
    if (!ready and !replInit()) return;
    defer gpa.free(ptr[0..len]);
    vfs.interface.mkdir(ptr[0..len]) catch {};
}

export fn replFsDelete(ptr: [*]u8, len: usize) void {
    if (!ready and !replInit()) return;
    defer gpa.free(ptr[0..len]);
    vfs.interface.remove(ptr[0..len]) catch {};
}

export fn replFsRename(old: [*]u8, old_len: usize, new: [*]u8, new_len: usize) void {
    if (!ready and !replInit()) return;
    defer gpa.free(old[0..old_len]);
    defer gpa.free(new[0..new_len]);
    vfs.interface.rename(old[0..old_len], new[0..new_len]) catch {};
}

export fn replRun(ptr: [*]u8, len: usize) void {
    if (!ready and !replInit()) return;
    defer gpa.free(ptr[0..len]);
    output.clearRetainingCapacity();
    runFile(ptr[0..len]) catch |err| {
        output.writer.print("internal error: {s}\n", .{@errorName(err)}) catch {};
    };
}

fn runFile(path: []const u8) !void {
    const w = &output.writer;
    var run_pool = try InternPool.init(gpa);
    defer run_pool.deinit();
    const root_namespace = try run_pool.createNamespace(gpa, .{});
    var run_session = Session.init(gpa, &run_pool, root_namespace);
    run_session.module_source = &project.interface;
    run_session.runtime.io = session.runtime.io;
    defer run_session.deinit();

    var expr: std.Io.Writer.Allocating = .init(gpa);
    defer expr.deinit();
    try expr.writer.print("@import(\"{s}\").main()", .{path});

    const value = (try eval.report(&run_session, expr.written(), w)) orelse return;
    if (value.index == .void_value) return;
    try render_value.render(value, run_session.intern_pool, &run_session, w);
    try w.writeByte('\n');
}

// The interpreter asserts an input fits `max_input_bytes`; reject an over-long line
// at this untrusted boundary so a large paste is a message, not a module-killing trap.
fn overLength(input: []const u8) bool {
    return input.len > InputShape.max_input_bytes;
}

fn dispatch(input: []const u8) !void {
    const w = &output.writer;
    const trimmed = std.mem.trim(u8, input, " \t\r\n");
    if (trimmed.len == 0) return;
    if (overLength(trimmed)) return w.print("input too long: {d} bytes (max {d})\n", .{ trimmed.len, InputShape.max_input_bytes });
    if (trimmed[0] != ':') return evaluate(trimmed, w);
    try Commands.dispatch(&session, trimmed[1..], w);
}

fn evaluate(input: []const u8, w: *std.Io.Writer) !void {
    if (try eval.report(&session, input, w)) |value| {
        try render_value.render(value, session.intern_pool, &session, w);
        try w.writeByte('\n');
    }
}

/// Evaluate `input` for the explorer: the value and its type, computed in
/// a throwaway session so a trailing expression resolves the declarations
/// before it (eval.run injects them) without persisting anything into the
/// live REPL session -- the explorer re-runs this on every keystroke.
export fn replPreview(ptr: [*]u8, len: usize) void {
    if (!ready and !replInit()) return;
    defer gpa.free(ptr[0..len]);
    output.clearRetainingCapacity();
    preview(ptr[0..len]) catch |err| {
        output.writer.print("internal error: {s}\n", .{@errorName(err)}) catch {};
    };
}

fn preview(input: []const u8) !void {
    const w = &output.writer;
    const trimmed = std.mem.trim(u8, input, " \t\r\n");
    if (trimmed.len == 0) return;
    if (overLength(trimmed)) return w.print("input too long: {d} bytes (max {d})\n", .{ trimmed.len, InputShape.max_input_bytes });

    var preview_pool = try InternPool.init(gpa);
    defer preview_pool.deinit();
    const root_namespace = try preview_pool.createNamespace(gpa, .{});
    var preview_session = Session.init(gpa, &preview_pool, root_namespace);
    preview_session.module_source = &module_source.interface;
    // Reuse the live session's host Io (its stderr routes to `output`, this session's `w`), so a
    // previewed `std.debug.print` behaves as in the real session, on the intrinsic Io path.
    preview_session.runtime.io = session.runtime.io;
    defer preview_session.deinit();

    // Bind the declarations first so the trailing expression resolves them; a lone
    // segment (pure expression or pure declarations) runs as-is.
    var expr = trimmed;
    if (try InputShape.splitTrailingExpr(gpa, trimmed)) |split| {
        _ = eval.run(&preview_session, split.decls, w) catch |err| switch (err) {
            error.ParseError, error.ZirError, error.AnalysisFail => return,
            else => |e| return e,
        };
        expr = split.expr;
    }

    const outcome = eval.run(&preview_session, expr, w) catch |err| switch (err) {
        error.ParseError, error.ZirError, error.AnalysisFail => return,
        else => |e| return e,
    };
    const value = outcome.value orelse {
        if (outcome.shape == .expression) try w.writeAll("(no value)\n");
        return;
    };
    try w.writeAll("=> ");
    try render_value.render(value, preview_session.intern_pool, &preview_session, w);
    try w.writeAll("   type: ");
    try Type.print(value.typeOf(preview_session.intern_pool), preview_session.intern_pool, w);
    try w.writeByte('\n');
}

/// Emit the source-mapped lowering of `input` as JSON for the explorer:
/// `{ source, ast, zir }`, each AST node / ZIR instruction carrying the
/// user-text byte range it came from. Runs in a throwaway session;
/// declarations and a trailing expression are outlined together (see `outline.writeJson`).
export fn replOutline(ptr: [*]u8, len: usize) void {
    if (!ready and !replInit()) return;
    defer gpa.free(ptr[0..len]);
    output.clearRetainingCapacity();
    buildOutline(ptr[0..len]) catch |err| {
        // Drop any partial outline so the error object is the whole result, not
        // a second object concatenated onto a truncated one.
        output.clearRetainingCapacity();
        outline.emitEmpty(&output.writer, @errorName(err)) catch {};
    };
}

fn buildOutline(input: []const u8) !void {
    const w = &output.writer;
    const trimmed = std.mem.trim(u8, input, " \t\r\n");
    if (trimmed.len == 0) return outline.emitEmpty(w, null);
    if (overLength(trimmed)) return outline.emitEmpty(w, "input too long");

    var preview_pool = try InternPool.init(gpa);
    defer preview_pool.deinit();
    const root_namespace = try preview_pool.createNamespace(gpa, .{});
    var preview_session = Session.init(gpa, &preview_pool, root_namespace);
    preview_session.module_source = &module_source.interface;
    defer preview_session.deinit();

    try outline.writeJson(&preview_session, trimmed, w);
}
