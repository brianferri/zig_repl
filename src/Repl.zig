const std = @import("std");
const assert = std.debug.assert;

const Session = @import("Session.zig");
const commands = @import("commands.zig");
const Pipeline = @import("front/Pipeline.zig");
const Diagnostic = @import("render/Diagnostic.zig");

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
        try repl.dispatch(line, stdout);
    }
    try stdout.flush();
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

    var result = Pipeline.run(repl.session.gpa, input) catch |err| {
        try stdout.print("front-end failed: {s}\n", .{@errorName(err)});
        return;
    };
    defer result.deinit(repl.session.gpa);

    if (result.hasParseErrors()) {
        return Diagnostic.renderParseErrors(result.tree, result.source(), stdout);
    }
    if (result.hasZirErrors()) {
        return Diagnostic.renderZirErrors(
            repl.session.gpa,
            result.zir,
            result.tree,
            result.source(),
            stdout,
        );
    }
    try stdout.writeAll("not-yet-evaluable: requires Sema\n");
}
