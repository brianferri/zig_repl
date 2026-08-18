//! Drives the shared `LineEditor` from a host-fed byte stream of standard xterm
//! key sequences, so the wasm REPL reuses the tty's parsing, editing, and
//! history. The host writes bytes with `feed`, reads `buffer`/`cursor` to render
//! the input line, and takes a completed line with `takeSubmitted` to evaluate.

const std = @import("std");
const terminal = @import("terminal");
const editor = @import("editor");
const Event = @import("device").Event;

const Parser = terminal.Parser;
const Protocol = terminal.Protocol;
const Xterm = terminal.Xterm;
const LineEditor = editor.LineEditor;

const LineInput = @This();

const read_buffer_bytes = 512;

gpa: std.mem.Allocator,
line_editor: LineEditor,
protocols: [1]*Protocol,
discard: std.Io.Writer.Discarding,
discard_buffer: [64]u8,
read_buffer: [read_buffer_bytes]u8,
read_len: usize,
submitted: std.ArrayListUnmanaged(u8),
has_submitted: bool,

/// Wire the internal self-pointer -- the editor's discard sink lives inside this
/// struct -- so this runs after the value is at its final address.
pub fn setup(self: *LineInput, gpa: std.mem.Allocator) void {
    self.gpa = gpa;
    self.discard = .init(&self.discard_buffer);
    self.line_editor = LineEditor.init(gpa, &self.discard.writer);
    self.protocols = .{Xterm.protocol()};
    self.read_len = 0;
    self.submitted = .empty;
    self.has_submitted = false;
    self.line_editor.beginLine();
}

pub fn feed(self: *LineInput, bytes: []const u8) !void {
    for (bytes) |b| {
        // A full buffer with no complete sequence is malformed wire input; drop
        // it and keep going rather than wedging the editor.
        if (self.read_len >= read_buffer_bytes) self.read_len = 0;
        self.read_buffer[self.read_len] = b;
        self.read_len += 1;
    }
    while (self.read_len > 0) {
        const result = Parser.parse(self.read_buffer[0..self.read_len]);
        const token = result.token orelse return;
        std.mem.copyForwards(u8, self.read_buffer[0..], self.read_buffer[result.consumed..self.read_len]);
        self.read_len -= result.consumed;
        for (self.protocols) |p| switch (Protocol.tryInterpret(p, token)) {
            .not_mine => continue,
            .consumed => break,
            .event => |event| {
                try self.dispatch(event);
                break;
            },
        };
    }
}

fn dispatch(self: *LineInput, event: Event.Event) !void {
    switch (try self.line_editor.applyEvent(event)) {
        .keep_reading => {},
        .submit => {
            self.submitted.clearRetainingCapacity();
            try self.submitted.appendSlice(self.gpa, self.line_editor.buffer.items);
            self.has_submitted = true;
            try self.line_editor.pushHistory(self.line_editor.buffer.items);
            self.line_editor.beginLine();
        },
        .eof_empty => {},
    }
}

pub fn buffer(self: *const LineInput) []const u8 {
    return self.line_editor.buffer.items;
}

pub fn cursor(self: *const LineInput) u32 {
    return self.line_editor.cursor;
}

/// The most recently submitted line, exactly once; null after it is taken, so
/// the host evaluates each submission once. Valid until the next `feed`.
pub fn takeSubmitted(self: *LineInput) ?[]const u8 {
    if (!self.has_submitted) return null;
    self.has_submitted = false;
    return self.submitted.items;
}
