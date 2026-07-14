//! TTY frontend: the interactive REPL over the `terminal/` stack. Owns the
//! IO surface (Io + stdin/stdout files), the live terminal, the prompt
//! theme, and the run loop, wrapping a borrowed `*Session` (the
//! frontend-agnostic core). A different frontend (e.g. a wasm terminal
//! emulator) reuses the core and the session-utility commands
//! (`commands/`) but supplies its own device behavior and its own
//! equivalents of the TTY-specific commands handled here.

const std = @import("std");
const assert = std.debug.assert;

const core = @import("repl");
const Session = core.Session;
const eval = core.eval;
const renderValue = core.render.Value.render;
const LineEditor = @import("LineEditor.zig");
const Terminal = @import("terminal").Terminal;
const themes = @import("theme/root.zig");
const Commands = @import("root.zig").commands;

const Repl = @This();

const input_buffer_bytes: u32 = 4096;
const output_buffer_bytes: u32 = 4096;

/// The frontend-agnostic core, borrowed for the frontend's lifetime.
session: *Session,
io: std.Io,
stdin_file: std.Io.File,
stdout_file: std.Io.File,
/// True when stdin is a terminal. Drives whether input is echoed back:
/// interactive stdin echoes via the kernel's line discipline, so the REPL
/// stays quiet; piped stdin does not, so the REPL mirrors each line (see
/// `echoInput`) for readable transcripts.
is_interactive: bool,
/// Selected prompt theme (a preference; the terminal's color capability
/// decides how much shows). Repoint to switch themes at runtime.
theme: *const themes.Theme,
/// The live terminal while interactive: `readLine` drives it for events
/// and the prompt's color level, and the `:terminal`/`:theme` commands
/// introspect it. Null in cooked/piped mode.
terminal: ?*Terminal,
should_quit: bool,

pub fn init(session: *Session, io: std.Io) std.Io.Cancelable!Repl {
    assert(@intFromPtr(io.vtable) != 0);
    assert(@intFromPtr(io.userdata) != 0);

    const stdin_file = std.Io.File.stdin();
    const is_interactive = try stdin_file.isTty(io);

    return .{
        .session = session,
        .io = io,
        .stdin_file = stdin_file,
        .stdout_file = std.Io.File.stdout(),
        .is_interactive = is_interactive,
        .theme = themes.default,
        .terminal = null,
        .should_quit = false,
    };
}

pub fn run(repl: *Repl, environ: *const std.process.Environ.Map) !void {
    assert(@intFromPtr(repl.session) != 0);

    var input_buffer: [input_buffer_bytes]u8 = undefined;
    var output_buffer: [output_buffer_bytes]u8 = undefined;
    var stdin_reader = std.Io.File.Reader.initStreaming(repl.stdin_file, repl.io, &input_buffer);
    var stdout_writer = std.Io.File.Writer.initStreaming(repl.stdout_file, repl.io, &output_buffer);
    const stdin = &stdin_reader.interface;
    const stdout = &stdout_writer.interface;

    // Piped stdin stays on `takeDelimiter` so shell pipelines and the
    // compliance harness keep working unchanged.
    if (repl.is_interactive) return repl.runInteractive(stdout, environ);
    return repl.runCooked(stdin, stdout);
}

fn runInteractive(repl: *Repl, stdout: *std.Io.Writer, environ: *const std.process.Environ.Map) !void {
    // A `var` local: the frontend borrows `&terminal`, and `readEvent`
    // needs a mutable pointee (the address of a temporary would be
    // `*const`). The reference lasts only the interactive scope.
    var terminal = Terminal.init(repl.session.gpa, repl.io, stdout, environ) catch |err| {
        // Init failure usually means we couldn't open /dev/repl or apply
        // termios -- e.g. detached console. Fall back loudly.
        try stdout.print("raw-mode terminal unavailable ({s}); using cooked mode\n", .{@errorName(err)});
        try stdout.flush();
        var input_buffer: [input_buffer_bytes]u8 = undefined;
        var stdin_reader = std.Io.File.Reader.initStreaming(repl.stdin_file, repl.io, &input_buffer);
        return repl.runCooked(&stdin_reader.interface, stdout);
    };
    repl.terminal = &terminal;
    defer {
        repl.terminal = null;
        terminal.deinit();
    }

    var editor = LineEditor.init(repl.session.gpa, stdout);
    defer editor.deinit();

    while (!repl.should_quit) {
        const maybe_line = editor.readLine(terminal.device(), repl.theme) catch |err| {
            try stdout.print("input error: {s}\r\n", .{@errorName(err)});
            try stdout.flush();
            continue;
        };
        const line = maybe_line orelse break;
        if (line.len == 0) continue;
        try repl.dispatch(line, stdout);
    }
    try stdout.flush();
}

fn runCooked(repl: *Repl, stdin: *std.Io.Reader, stdout: *std.Io.Writer) !void {
    while (!repl.should_quit) {
        // Cooked mode has no Terminal, hence no detected color level;
        // the prompt stays uncolored (piped output must, anyway).
        try repl.theme.primary.write(stdout, .none);
        try stdout.flush();
        const maybe_line = stdin.takeDelimiter('\n') catch |err| switch (err) {
            error.StreamTooLong => {
                try stdout.writeAll("input too long; line dropped\n");
                continue;
            },
            error.ReadFailed => return err,
        };
        const line = maybe_line orelse break;
        try echoInput(repl.is_interactive, line, stdout);
        try repl.dispatch(line, stdout);
    }
    try stdout.flush();
}

/// Piped stdin doesn't echo to the terminal -- mirror what the user
/// "typed" so transcripts read like an interactive session. Interactive
/// stdin already echoes via the kernel's line discipline; `takeDelimiter`
/// strips the `\n`, so this restores it.
fn echoInput(is_interactive: bool, line: []const u8, writer: *std.Io.Writer) !void {
    if (is_interactive) return;
    try writer.print("{s}\n", .{line});
}

fn dispatch(repl: *Repl, raw_line: []const u8, stdout: *std.Io.Writer) !void {
    assert(@intFromPtr(repl.session) != 0);
    assert(raw_line.len <= input_buffer_bytes);
    const trimmed = std.mem.trim(u8, raw_line, " \t\r");
    if (trimmed.len == 0) return;
    if (trimmed[0] != ':') return repl.evaluate(trimmed, stdout);
    try Commands.dispatch(repl, trimmed[1..], stdout);
}

fn evaluate(repl: *Repl, input: []const u8, stdout: *std.Io.Writer) !void {
    assert(input.len > 0);
    assert(input.len <= input_buffer_bytes);
    if (try eval.report(repl.session, input, stdout)) |value| {
        try renderValue(value, repl.session.intern_pool, repl.session, stdout);
        try stdout.writeByte('\n');
    }
}

test "echoInput: interactive mode writes nothing (repl echoes via line discipline)" {
    var buf: [64]u8 = undefined;
    var writer = std.Io.Writer.fixed(&buf);
    try echoInput(true, "1 + 2", &writer);
    try std.testing.expectEqual(@as(usize, 0), writer.end);
}

test "echoInput: piped mode mirrors the line with a trailing newline" {
    var buf: [64]u8 = undefined;
    var writer = std.Io.Writer.fixed(&buf);
    try echoInput(false, "1 + 2", &writer);
    try std.testing.expectEqualStrings("1 + 2\n", buf[0..writer.end]);
}
