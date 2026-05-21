const std = @import("std");
const assert = std.debug.assert;

const Session = @import("Session.zig");
const commands = @import("commands.zig");
const Pipeline = @import("front/Pipeline.zig");
const Diagnostic = @import("render/Diagnostic.zig");
const Sema = @import("sema/Sema.zig");
const renderValue = @import("render/Value.zig").render;

const Repl = @This();

const prompt_string: []const u8 = "> ";
const input_buffer_bytes: u32 = 4096;
const output_buffer_bytes: u32 = 4096;
const max_command_line_bytes: u32 = 1024;

session: *Session,

pub fn init(session: *Session) Repl {
    assert(@intFromPtr(session) != 0);
    return .{ .session = session };
}

pub fn run(repl: *Repl) !void {
    assert(@intFromPtr(repl.session) != 0);

    var input_buffer: [input_buffer_bytes]u8 = undefined;
    var output_buffer: [output_buffer_bytes]u8 = undefined;
    var stdin_reader = std.Io.File.Reader.initStreaming(
        repl.session.stdin_file,
        repl.session.io,
        &input_buffer,
    );
    var stdout_writer = std.Io.File.Writer.initStreaming(
        repl.session.stdout_file,
        repl.session.io,
        &output_buffer,
    );
    const stdin = &stdin_reader.interface;
    const stdout = &stdout_writer.interface;

    while (!repl.session.should_quit) {
        try stdout.writeAll(prompt_string);
        try stdout.flush();
        const maybe_line = stdin.takeDelimiter('\n') catch |err| switch (err) {
            error.StreamTooLong => {
                try stdout.writeAll("input too long; line dropped\n");
                continue;
            },
            error.ReadFailed => return err,
        };
        const line = maybe_line orelse break;
        try echoInput(repl.session.is_interactive, line, stdout);
        try repl.dispatch(line, stdout);
    }
    try stdout.flush();
}

/// Piped stdin doesn't echo to the terminal -- mirror what the user
/// "typed" so transcripts read like an interactive session.
/// Interactive stdin already echoes via the kernel's line
/// discipline. `takeDelimiter` strips the `\n`, so this restores
/// it.
fn echoInput(is_interactive: bool, line: []const u8, writer: *std.Io.Writer) !void {
    if (is_interactive) return;
    try writer.print("{s}\n", .{line});
}

fn dispatch(repl: *Repl, raw_line: []const u8, stdout: *std.Io.Writer) !void {
    assert(@intFromPtr(repl.session) != 0);
    assert(raw_line.len <= input_buffer_bytes);
    const trimmed = std.mem.trim(u8, raw_line, " \t\r");
    if (trimmed.len == 0) return;
    if (trimmed[0] == ':') return commands.run(repl.session, trimmed[1..], stdout);
    return repl.evaluate(trimmed, stdout);
}

fn evaluate(repl: *Repl, input: []const u8, stdout: *std.Io.Writer) !void {
    assert(input.len > 0);
    assert(input.len <= input_buffer_bytes);

    var result = Pipeline.runWithInjection(
        repl.session.gpa,
        input,
        &repl.session.intern_pool,
        .init(repl.session.root_namespace),
    ) catch |err| {
        try stdout.print("front-end failed: {s}\n", .{@errorName(err)});
        return;
    };
    defer result.deinit(repl.session.gpa);

    if (result.hasParseErrors()) {
        return Diagnostic.renderParseErrors(result.tree, result.userView(), stdout);
    }
    if (result.hasZirErrors()) {
        return Diagnostic.renderZirErrors(
            repl.session.gpa,
            result.zir,
            result.tree,
            result.userView(),
            stdout,
        );
    }

    if (Sema.analyze(
        repl.session.gpa,
        &repl.session.intern_pool,
        result.zir,
        stdout,
        repl.session.root_namespace,
    ) catch |err| switch (err) {
        error.AnalysisFail => return, // diagnostic already written
        else => |e| return e,
    }) |value| {
        try renderValue(value, &repl.session.intern_pool, stdout);
        return;
    }

    if (result.wrapped.shape == .expression) {
        // Expression shape with no result is a Sema-side gap.
        try stdout.writeAll("(no value)\n");
    }
}

test "echoInput: interactive mode writes nothing (tty echoes via line discipline)" {
    var buf: [64]u8 = undefined;
    var writer = std.Io.Writer.fixed(&buf);
    try echoInput(true, "1 + 2", &writer);
    try std.testing.expectEqual(@as(usize, 0), writer.buffer.len - writer.unusedCapacityLen());
}

test "echoInput: piped mode mirrors the input with a trailing newline" {
    var buf: [64]u8 = undefined;
    var writer = std.Io.Writer.fixed(&buf);
    try echoInput(false, "const x = 10;", &writer);
    const written = buf[0 .. writer.buffer.len - writer.unusedCapacityLen()];
    try std.testing.expectEqualStrings("const x = 10;\n", written);
}

test "echoInput: piped mode preserves the input verbatim (no trimming)" {
    var buf: [64]u8 = undefined;
    var writer = std.Io.Writer.fixed(&buf);
    try echoInput(false, "  leading spaces", &writer);
    const written = buf[0 .. writer.buffer.len - writer.unusedCapacityLen()];
    try std.testing.expectEqualStrings("  leading spaces\n", written);
}
