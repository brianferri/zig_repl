//! Wasm frontend entry: a line-in / text-out REPL the browser drives. The
//! host writes an input line into wasm memory, calls `replEval`, then reads
//! the rendered output back out -- there is no terminal, no `LineEditor` (the
//! page's input box does the editing). It builds on the `repl` core module and
//! the `drivers_wasm` driver, neither of which pulls in the posix tty stack.
//!
//! Reentrancy: the page calls `replEval` once per submitted line. The result
//! buffer is a module global, reset at the start of each call and read via
//! `replResultPtr` / `replResultLen` before the next.

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

// `wasm_allocator` requires the module be single-threaded (build.zig sets
// it); it grows linear memory as needed, which detaches the host's view of
// `memory.buffer` -- the page re-reads it after every call that allocates.
const gpa = std.heap.wasm_allocator;

// The standard library, gzip-tarred into the binary by `build.zig`. Freestanding
// wasm has no filesystem, so this is how `@import("std")` resolves here.
const embedded_std = @embedFile("embedded_std");

var pool: InternPool = undefined;
var session: Session = undefined;
var module_source: repl.module.Buffer = undefined;
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
    session.module_source = &module_source.interface;
    output = .init(gpa);
    // The single host Io the interpreter routes every runtime leaf through; its stderr writes land in
    // `output`, so evaluated `std.debug.print` appears inline with rendered values. Installing it also
    // bypasses the freestanding posix stack the default debug writer would reach.
    host_io = .{ .writer = &output.writer };
    session.runtime.io = host_io.io();
    line_input.setup(gpa);
    ready = true;
    return true;
}

/// Reserve `len` bytes for the host to write an input line into. The
/// matching `replEval` frees it. Returns null on allocation failure.
export fn replAlloc(len: usize) ?[*]u8 {
    const buf = gpa.alloc(u8, len) catch return null;
    return buf.ptr;
}

/// Evaluate one input line (the `len` bytes at `ptr`, freed here). The
/// rendered result and any diagnostics land in the result buffer; read
/// them with `replResultPtr` / `replResultLen` before the next call.
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
/// frontend paints its surfaces and prompt from the same registry the tty draws
/// from.
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

fn dispatch(input: []const u8) !void {
    const w = &output.writer;
    const trimmed = std.mem.trim(u8, input, " \t\r\n");
    if (trimmed.len == 0) return;
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

    var preview_pool = try InternPool.init(gpa);
    defer preview_pool.deinit();
    const root_namespace = try preview_pool.createNamespace(gpa, .{});
    var preview_session = Session.init(gpa, &preview_pool, root_namespace);
    preview_session.module_source = &module_source.interface;
    // Reuse the live session's host Io (its stderr routes to `output`, this session's `w`), so a
    // previewed `std.debug.print` behaves as in the real session rather than hitting the posix stack.
    preview_session.runtime.io = session.runtime.io;
    defer preview_session.deinit();

    // For "declarations; trailing expression", bind the declarations into
    // the throwaway session first so the trailing expression resolves them.
    // The lone-segment case (pure expression or pure declarations) runs as-is.
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
/// declarations and a trailing expression are outlined together (see
/// `outline.writeJson`).
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

    var preview_pool = try InternPool.init(gpa);
    defer preview_pool.deinit();
    const root_namespace = try preview_pool.createNamespace(gpa, .{});
    var preview_session = Session.init(gpa, &preview_pool, root_namespace);
    preview_session.module_source = &module_source.interface;
    defer preview_session.deinit();

    try outline.writeJson(&preview_session, trimmed, w);
}
