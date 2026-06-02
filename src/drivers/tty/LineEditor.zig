//! Multi-line REPL editor over the `terminal/` subsystem.
//! Consumes canonical `Event`s and emits one assembled input per
//! `readLine`. Whether Shift+Enter is actually distinguishable from
//! Enter is the terminal's concern -- this file just dispatches on
//! `Event.key_press { codepoint: enter, modifiers: shift }`.
//!
//! Display model: full-redraw on every state change. The whole
//! buffer is re-emitted with continuation prompts on each `\n` and
//! the cursor is repositioned via CSI escapes. Flicker is invisible
//! on typical REPL input sizes; the alternative (incremental edit
//! sequences) is significantly more complex without observable
//! benefit at this scale.
//!
//! Cursor position is a byte index into `buffer`. Movement (arrow
//! keys, Home/End) mutates `cursor`; insert/delete mutates `buffer`
//! and `cursor` together. Line-join on backspace falls out for free
//! because deleting the `\n` at `cursor - 1` is the same byte-level
//! operation as any other backspace.

const std = @import("std");
const assert = std.debug.assert;
const Device = @import("../../device/Device.zig");
const Event = @import("../../device/Event.zig");
const themes = @import("theme/root.zig");
const ColorLevel = @import("../../device/Color.zig").ColorLevel;

const LineEditor = @This();

pub const max_input_bytes: u32 = 4096;
pub const history_max_entries: u32 = 1000;

/// Output sink. `readLine` reads input via the session's terminal;
/// every other method (applyEvent, redraw, etc.) writes only here,
/// which keeps the editor core unit-testable without a real terminal.
writer: *std.Io.Writer,
gpa: std.mem.Allocator,
buffer: std.ArrayListUnmanaged(u8),
cursor: u32,
/// Number of visible rows the current draw occupies (prompt line +
/// one per embedded `\n`). The next redraw uses this to know how
/// far to clear below; combined with `cursor_row_drawn` it doesn't
/// over-reach above the input area.
lines_drawn: u32,
/// Display row the cursor sat at after the previous draw (0 = top
/// row of the input). The next redraw moves up by this amount to
/// reach row 0 before clearing -- moving by `lines_drawn - 1` would
/// over-shoot whenever the cursor wasn't on the bottom row, wiping
/// prompt + history above the input area.
cursor_row_drawn: u32,
/// Ring of previously-submitted inputs, oldest-first. Each entry
/// is gpa-owned. Older-than-cap entries rotate out on push.
history: std.ArrayListUnmanaged([]u8),
/// 0 = newest entry; null = not in recall mode (editing live draft).
history_offset: ?u32,
/// Snapshot of `buffer` before entering history mode so down-past-
/// newest can restore the in-progress edit.
draft: std.ArrayListUnmanaged(u8),

pub fn init(gpa: std.mem.Allocator, writer: *std.Io.Writer) LineEditor {
    assert(@intFromPtr(writer) != 0);
    return .{
        .writer = writer,
        .gpa = gpa,
        .buffer = .empty,
        .cursor = 0,
        .lines_drawn = 0,
        .cursor_row_drawn = 0,
        .history = .empty,
        .history_offset = null,
        .draft = .empty,
    };
}

pub fn deinit(editor: *LineEditor) void {
    for (editor.history.items) |entry| editor.gpa.free(entry);
    editor.history.deinit(editor.gpa);
    editor.draft.deinit(editor.gpa);
    editor.buffer.deinit(editor.gpa);
    editor.* = undefined;
}

/// Read one logical input from the user. Returns `null` on EOF
/// (Ctrl+D on empty buffer, or the underlying terminal closing).
/// The returned slice is borrowed from the editor's buffer and is
/// invalidated on the next `readLine` call.
pub fn readLine(editor: *LineEditor, device: *Device, theme: *const themes.Theme) !?[]const u8 {
    assert(@intFromPtr(editor) != 0);
    assert(@intFromPtr(device) != 0);
    const level = device.color_level;

    editor.buffer.clearRetainingCapacity();
    editor.cursor = 0;
    editor.lines_drawn = 0;
    editor.cursor_row_drawn = 0;
    editor.history_offset = null;
    editor.draft.clearRetainingCapacity();
    try editor.redraw(theme, level);

    while (true) {
        const maybe_event = try device.readEvent();
        const event = maybe_event orelse return null;
        const outcome = try editor.applyEvent(event);
        switch (outcome) {
            .keep_reading => try editor.redraw(theme, level),
            .submit => {
                try editor.moveCursorBelowInput();
                try editor.pushHistory(editor.buffer.items);
                return editor.buffer.items;
            },
            .eof_empty => {
                try editor.moveCursorBelowInput();
                return null;
            },
        }
    }
}

/// Position the terminal cursor on a fresh row below the last
/// rendered input row. Without this, the caller's output starts
/// wherever the cursor happened to sit after the final redraw --
/// typically mid-buffer -- and overwrites already-displayed input
/// lines.
fn moveCursorBelowInput(editor: *LineEditor) !void {
    assert(editor.lines_drawn >= 1);
    assert(editor.cursor_row_drawn < editor.lines_drawn);
    const rows_below = editor.lines_drawn - editor.cursor_row_drawn;
    if (rows_below > 1) {
        try editor.writer.print("\x1b[{d}B", .{rows_below - 1});
    }
    try editor.writer.writeAll("\r\n");
    try editor.writer.flush();
}

fn pushHistory(editor: *LineEditor, input: []const u8) !void {
    const trimmed = std.mem.trim(u8, input, " \t\r\n");
    if (trimmed.len == 0) return;
    if (editor.history.items.len > 0) {
        const last = editor.history.items[editor.history.items.len - 1];
        if (std.mem.eql(u8, last, trimmed)) return;
    }
    if (editor.history.items.len >= history_max_entries) {
        const oldest = editor.history.orderedRemove(0);
        editor.gpa.free(oldest);
    }
    const copy = try editor.gpa.dupe(u8, trimmed);
    errdefer editor.gpa.free(copy);
    try editor.history.append(editor.gpa, copy);
}

const Outcome = enum { keep_reading, submit, eof_empty };

fn applyEvent(editor: *LineEditor, event: Event.Event) !Outcome {
    assert(@intFromPtr(editor) != 0);
    assert(editor.cursor <= editor.buffer.items.len);
    return switch (event) {
        .key_press, .key_repeat => |k| editor.applyKey(k),
        .key_release, .focus_in, .focus_out, .resize => .keep_reading,
        .paste => |bytes| editor.applyPaste(bytes),
        .eof => .eof_empty,
    };
}

fn applyKey(editor: *LineEditor, key: Event.Key) !Outcome {
    if (key.codepoint == Event.key.enter) {
        if (key.modifiers.shift) return editor.insertByte('\n');
        return .submit;
    }
    if (key.modifiers.ctrl) return editor.applyCtrl(key.codepoint);
    return switch (key.codepoint) {
        Event.key.backspace => editor.backspace(),
        Event.key.delete => editor.deleteForward(),
        Event.key.left => editor.moveLeft(),
        Event.key.right => editor.moveRight(),
        Event.key.home => editor.moveToLineStart(),
        Event.key.end => editor.moveToLineEnd(),
        Event.key.up => editor.moveUp(),
        Event.key.down => editor.moveDown(),
        Event.key.tab => editor.insertByte('\t'),
        0x20...0x7e => editor.insertByte(@intCast(key.codepoint)),
        else => .keep_reading,
    };
}

fn applyCtrl(editor: *LineEditor, codepoint: u21) !Outcome {
    return switch (codepoint) {
        'c' => editor.cancelInput(),
        'd' => if (editor.buffer.items.len == 0) .eof_empty else .keep_reading,
        'l' => editor.clearScreen(),
        'a' => editor.moveToLineStart(),
        'e' => editor.moveToLineEnd(),
        'k' => editor.deleteToLineEnd(),
        else => .keep_reading,
    };
}

fn insertByte(editor: *LineEditor, b: u8) !Outcome {
    assert(editor.cursor <= editor.buffer.items.len);
    if (editor.buffer.items.len >= max_input_bytes) return editor.beep();
    try editor.buffer.insert(editor.gpa, editor.cursor, b);
    editor.cursor += 1;
    assert(editor.cursor <= editor.buffer.items.len);
    return .keep_reading;
}

fn applyPaste(editor: *LineEditor, bytes: []const u8) !Outcome {
    for (bytes) |b| {
        if (editor.buffer.items.len >= max_input_bytes) break;
        try editor.buffer.insert(editor.gpa, editor.cursor, b);
        editor.cursor += 1;
    }
    return .keep_reading;
}

fn backspace(editor: *LineEditor) !Outcome {
    assert(editor.cursor <= editor.buffer.items.len);
    if (editor.cursor == 0) return editor.beep();
    _ = editor.buffer.orderedRemove(editor.cursor - 1);
    editor.cursor -= 1;
    assert(editor.cursor <= editor.buffer.items.len);
    return .keep_reading;
}

fn deleteForward(editor: *LineEditor) !Outcome {
    assert(editor.cursor <= editor.buffer.items.len);
    if (editor.cursor >= editor.buffer.items.len) return editor.beep();
    _ = editor.buffer.orderedRemove(editor.cursor);
    assert(editor.cursor <= editor.buffer.items.len);
    return .keep_reading;
}

fn deleteToLineEnd(editor: *LineEditor) !Outcome {
    var end = editor.cursor;
    while (end < editor.buffer.items.len and editor.buffer.items[end] != '\n') end += 1;
    const removed = end - editor.cursor;
    if (removed == 0) return editor.beep();
    editor.buffer.replaceRangeAssumeCapacity(editor.cursor, removed, &.{});
    return .keep_reading;
}

fn moveLeft(editor: *LineEditor) !Outcome {
    if (editor.cursor > 0) editor.cursor -= 1;
    return .keep_reading;
}

fn moveRight(editor: *LineEditor) !Outcome {
    if (editor.cursor < editor.buffer.items.len) editor.cursor += 1;
    return .keep_reading;
}

fn moveToLineStart(editor: *LineEditor) !Outcome {
    while (editor.cursor > 0 and editor.buffer.items[editor.cursor - 1] != '\n') {
        editor.cursor -= 1;
    }
    return .keep_reading;
}

fn moveToLineEnd(editor: *LineEditor) !Outcome {
    while (editor.cursor < editor.buffer.items.len and editor.buffer.items[editor.cursor] != '\n') {
        editor.cursor += 1;
    }
    return .keep_reading;
}

fn moveUp(editor: *LineEditor) !Outcome {
    // Already in history mode -> step further back.
    if (editor.history_offset != null) return editor.recallOlder();
    // Cursor on the first row of the current buffer -> enter
    // history recall. Otherwise navigate buffer lines.
    if (!editor.onFirstBufferRow()) return editor.moveUpWithinBuffer();
    return editor.recallOlder();
}

fn moveDown(editor: *LineEditor) !Outcome {
    if (editor.history_offset != null) return editor.recallNewer();
    if (!editor.onLastBufferRow()) return editor.moveDownWithinBuffer();
    return .keep_reading;
}

fn onFirstBufferRow(editor: *LineEditor) bool {
    var i: u32 = 0;
    while (i < editor.cursor) : (i += 1) {
        if (editor.buffer.items[i] == '\n') return false;
    }
    return true;
}

fn onLastBufferRow(editor: *LineEditor) bool {
    var i: u32 = editor.cursor;
    while (i < editor.buffer.items.len) : (i += 1) {
        if (editor.buffer.items[i] == '\n') return false;
    }
    return true;
}

fn moveUpWithinBuffer(editor: *LineEditor) !Outcome {
    const col = editor.currentColumn();
    while (editor.cursor > 0 and editor.buffer.items[editor.cursor - 1] != '\n') {
        editor.cursor -= 1;
    }
    if (editor.cursor == 0) return editor.beep();
    editor.cursor -= 1; // step over the `\n` into the previous line's last char
    while (editor.cursor > 0 and editor.buffer.items[editor.cursor - 1] != '\n') {
        editor.cursor -= 1;
    }
    var step: u32 = 0;
    while (step < col and
        editor.cursor < editor.buffer.items.len and
        editor.buffer.items[editor.cursor] != '\n') : (step += 1)
    {
        editor.cursor += 1;
    }
    return .keep_reading;
}

fn moveDownWithinBuffer(editor: *LineEditor) !Outcome {
    const col = editor.currentColumn();
    while (editor.cursor < editor.buffer.items.len and editor.buffer.items[editor.cursor] != '\n') {
        editor.cursor += 1;
    }
    if (editor.cursor >= editor.buffer.items.len) return editor.beep();
    editor.cursor += 1; // step past the `\n` into the next line
    var step: u32 = 0;
    while (step < col and
        editor.cursor < editor.buffer.items.len and
        editor.buffer.items[editor.cursor] != '\n') : (step += 1)
    {
        editor.cursor += 1;
    }
    return .keep_reading;
}

fn recallOlder(editor: *LineEditor) !Outcome {
    if (editor.history.items.len == 0) return editor.beep();
    const next_offset: u32 = if (editor.history_offset) |o|
        @min(o + 1, @as(u32, @intCast(editor.history.items.len - 1)))
    else
        0;
    if (editor.history_offset == null) try editor.saveDraft();
    if (editor.history_offset != null and next_offset == editor.history_offset.?) {
        return editor.beep(); // already at oldest
    }
    editor.history_offset = next_offset;
    try editor.replaceWithHistory(next_offset);
    return .keep_reading;
}

fn recallNewer(editor: *LineEditor) !Outcome {
    const offset = editor.history_offset orelse return editor.beep();
    if (offset == 0) {
        // Past the newest entry -> restore the draft.
        editor.history_offset = null;
        try editor.restoreDraft();
        return .keep_reading;
    }
    const new_offset = offset - 1;
    editor.history_offset = new_offset;
    try editor.replaceWithHistory(new_offset);
    return .keep_reading;
}

fn saveDraft(editor: *LineEditor) !void {
    editor.draft.clearRetainingCapacity();
    try editor.draft.appendSlice(editor.gpa, editor.buffer.items);
}

fn restoreDraft(editor: *LineEditor) !void {
    editor.buffer.clearRetainingCapacity();
    try editor.buffer.appendSlice(editor.gpa, editor.draft.items);
    editor.cursor = @intCast(editor.buffer.items.len);
}

fn replaceWithHistory(editor: *LineEditor, offset: u32) !void {
    assert(editor.history.items.len > 0);
    assert(offset < editor.history.items.len);
    const idx = editor.history.items.len - 1 - offset;
    const entry = editor.history.items[idx];
    editor.buffer.clearRetainingCapacity();
    try editor.buffer.appendSlice(editor.gpa, entry);
    editor.cursor = @intCast(editor.buffer.items.len);
    assert(editor.cursor == editor.buffer.items.len);
}

fn currentColumn(editor: *LineEditor) u32 {
    var c = editor.cursor;
    while (c > 0 and editor.buffer.items[c - 1] != '\n') c -= 1;
    return editor.cursor - c;
}

fn cancelInput(editor: *LineEditor) !Outcome {
    try editor.writer.writeAll("^C\r\n");
    try editor.writer.flush();
    editor.buffer.clearRetainingCapacity();
    editor.cursor = 0;
    editor.lines_drawn = 0;
    editor.cursor_row_drawn = 0;
    return .keep_reading;
}

fn clearScreen(editor: *LineEditor) !Outcome {
    // CSI 2J clears the screen, CSI H homes the cursor. Next redraw
    // paints fresh -- reset both tracking fields so we don't try to
    // move up through a row that no longer exists.
    try editor.writer.writeAll("\x1b[2J\x1b[H");
    editor.lines_drawn = 0;
    editor.cursor_row_drawn = 0;
    return .keep_reading;
}

fn beep(editor: *LineEditor) !Outcome {
    try editor.writer.writeAll("\x07");
    try editor.writer.flush();
    return .keep_reading;
}

/// Rewrite the entire input area: cursor to start of input region,
/// erase below, emit prompt + buffer (with continuation prompts on
/// embedded `\n`), reposition cursor at its logical location. `theme`
/// and `level` come from the caller (the session theme + the
/// terminal's color capability) so the editor core stays session-free.
fn redraw(editor: *LineEditor, theme: *const themes.Theme, level: ColorLevel) !void {
    assert(@intFromPtr(editor) != 0);
    assert(editor.cursor <= editor.buffer.items.len);
    // Previous-draw invariant: the cursor row was within the
    // rendered area. (lines_drawn == 0 on the first redraw, so the
    // check trivially holds there too.)
    assert(editor.lines_drawn == 0 or editor.cursor_row_drawn < editor.lines_drawn);
    const writer = editor.writer;

    // Move from wherever the cursor currently sits (set by the
    // previous redraw at `cursor_row_drawn`) up to row 0 of the
    // input area, then to col 0, then erase everything below.
    if (editor.cursor_row_drawn > 0) {
        try writer.print("\x1b[{d}A", .{editor.cursor_row_drawn});
    }
    try writer.writeAll("\r\x1b[J");

    try theme.primary.write(writer, level);

    var col: u32 = @intCast(theme.primary.width());
    var row: u32 = 0;
    var cursor_col: u32 = col;
    var cursor_row: u32 = 0;
    var seen_cursor = editor.cursor == 0;

    for (editor.buffer.items, 0..) |b, i| {
        if (!seen_cursor and @as(u32, @intCast(i)) == editor.cursor) {
            cursor_col = col;
            cursor_row = row;
            seen_cursor = true;
        }
        if (b == '\n') {
            try writer.writeAll("\r\n");
            try theme.continuation.write(writer, level);
            row += 1;
            col = @intCast(theme.continuation.width());
        } else {
            try writer.writeByte(b);
            col += 1;
        }
    }
    if (!seen_cursor) {
        cursor_col = col;
        cursor_row = row;
    }

    editor.lines_drawn = row + 1;
    editor.cursor_row_drawn = cursor_row;
    assert(editor.cursor_row_drawn < editor.lines_drawn);

    if (row > cursor_row) try writer.print("\x1b[{d}A", .{row - cursor_row});
    try writer.writeAll("\r");
    if (cursor_col > 0) try writer.print("\x1b[{d}C", .{cursor_col});

    try writer.flush();
}

const testing = std.testing;

fn keyPress(cp: u21) Event.Event {
    return .{ .key_press = .{ .codepoint = cp } };
}

fn shiftPress(cp: u21) Event.Event {
    return .{ .key_press = .{ .codepoint = cp, .modifiers = .{ .shift = true } } };
}

fn ctrlPress(cp: u21) Event.Event {
    return .{ .key_press = .{ .codepoint = cp, .modifiers = .{ .ctrl = true } } };
}

fn typeBytes(ed: *LineEditor, bytes: []const u8) !void {
    for (bytes) |b| _ = try ed.applyEvent(keyPress(b));
}

test "currentColumn: single-line buffer reports cursor offset" {
    var aw: std.Io.Writer.Allocating = .init(testing.allocator);
    defer aw.deinit();
    var ed = LineEditor.init(testing.allocator, &aw.writer);
    defer ed.deinit();
    try typeBytes(&ed, "hello");
    ed.cursor = 3;
    try testing.expectEqual(@as(u32, 3), ed.currentColumn());
}

test "currentColumn: multi-line buffer reports column within current line" {
    var aw: std.Io.Writer.Allocating = .init(testing.allocator);
    defer aw.deinit();
    var ed = LineEditor.init(testing.allocator, &aw.writer);
    defer ed.deinit();
    try ed.buffer.appendSlice(ed.gpa, "abc\ndefgh");
    ed.cursor = 6; // 'f' (offset 2 from line-start at 4)
    try testing.expectEqual(@as(u32, 2), ed.currentColumn());
}

test "mid-line insert preserves bytes after cursor" {
    var aw: std.Io.Writer.Allocating = .init(testing.allocator);
    defer aw.deinit();
    var ed = LineEditor.init(testing.allocator, &aw.writer);
    defer ed.deinit();
    try typeBytes(&ed, "abc");
    _ = try ed.applyEvent(keyPress(Event.key.left));
    _ = try ed.applyEvent(keyPress('X'));
    try testing.expectEqualStrings("abXc", ed.buffer.items);
    try testing.expectEqual(@as(u32, 3), ed.cursor);
}

test "shift+enter inserts a newline at cursor" {
    var aw: std.Io.Writer.Allocating = .init(testing.allocator);
    defer aw.deinit();
    var ed = LineEditor.init(testing.allocator, &aw.writer);
    defer ed.deinit();
    try typeBytes(&ed, "a");
    _ = try ed.applyEvent(shiftPress(Event.key.enter));
    try typeBytes(&ed, "b");
    try testing.expectEqualStrings("a\nb", ed.buffer.items);
    try testing.expectEqual(@as(u32, 3), ed.cursor);
}

test "backspace at start of continuation joins lines" {
    var aw: std.Io.Writer.Allocating = .init(testing.allocator);
    defer aw.deinit();
    var ed = LineEditor.init(testing.allocator, &aw.writer);
    defer ed.deinit();
    try typeBytes(&ed, "a");
    _ = try ed.applyEvent(shiftPress(Event.key.enter));
    try typeBytes(&ed, "b");
    _ = try ed.applyEvent(keyPress(Event.key.home));
    _ = try ed.applyEvent(keyPress(Event.key.backspace));
    try testing.expectEqualStrings("ab", ed.buffer.items);
    try testing.expectEqual(@as(u32, 1), ed.cursor);
}

test "arrow up + edit keeps cursor bookkeeping inside drawn area" {
    var aw: std.Io.Writer.Allocating = .init(testing.allocator);
    defer aw.deinit();
    var ed = LineEditor.init(testing.allocator, &aw.writer);
    defer ed.deinit();
    try typeBytes(&ed, "abc");
    _ = try ed.applyEvent(shiftPress(Event.key.enter));
    try typeBytes(&ed, "def");
    try ed.redraw(themes.default, .none);
    _ = try ed.applyEvent(keyPress(Event.key.up));
    try ed.redraw(themes.default, .none);
    _ = try ed.applyEvent(keyPress('X'));
    try ed.redraw(themes.default, .none);
    try testing.expectEqualStrings("abcX\ndef", ed.buffer.items);
    // The bug we're guarding against: cursor_row_drawn was set
    // higher than lines_drawn, causing the next redraw's CSI A
    // move to overshoot into already-rendered terminal lines.
    try testing.expect(ed.cursor_row_drawn < ed.lines_drawn);
}

test "moveCursorBelowInput descends past last input row before newline" {
    var aw: std.Io.Writer.Allocating = .init(testing.allocator);
    defer aw.deinit();
    var ed = LineEditor.init(testing.allocator, &aw.writer);
    defer ed.deinit();
    try typeBytes(&ed, "a");
    _ = try ed.applyEvent(shiftPress(Event.key.enter));
    try typeBytes(&ed, "b");
    try ed.redraw(themes.default, .none);
    _ = try ed.applyEvent(keyPress(Event.key.up));
    try ed.redraw(themes.default, .none);
    aw.clearRetainingCapacity();
    try ed.moveCursorBelowInput();
    const out = aw.writer.buffered();
    // The submit-overwrite bug: without a cursor-down, the trailing
    // `\r\n` lands inside the input area and the caller's diagnostic
    // overwrites the last input row.
    try testing.expect(std.mem.indexOf(u8, out, "\x1b[1B") != null);
    try testing.expect(std.mem.endsWith(u8, out, "\r\n"));
}

test "history recall replaces buffer with prior entry" {
    var aw: std.Io.Writer.Allocating = .init(testing.allocator);
    defer aw.deinit();
    var ed = LineEditor.init(testing.allocator, &aw.writer);
    defer ed.deinit();
    try ed.pushHistory("foo");
    try ed.pushHistory("bar");
    _ = try ed.applyEvent(keyPress(Event.key.up));
    try testing.expectEqualStrings("bar", ed.buffer.items);
    _ = try ed.applyEvent(keyPress(Event.key.up));
    try testing.expectEqualStrings("foo", ed.buffer.items);
    _ = try ed.applyEvent(keyPress(Event.key.down));
    try testing.expectEqualStrings("bar", ed.buffer.items);
    _ = try ed.applyEvent(keyPress(Event.key.down));
    try testing.expectEqualStrings("", ed.buffer.items);
}

test "history dedups consecutive identical entries" {
    var aw: std.Io.Writer.Allocating = .init(testing.allocator);
    defer aw.deinit();
    var ed = LineEditor.init(testing.allocator, &aw.writer);
    defer ed.deinit();
    try ed.pushHistory("foo");
    try ed.pushHistory("foo");
    try ed.pushHistory("bar");
    try testing.expectEqual(@as(usize, 2), ed.history.items.len);
}

test "paste with embedded newline splits into multi-line buffer" {
    var aw: std.Io.Writer.Allocating = .init(testing.allocator);
    defer aw.deinit();
    var ed = LineEditor.init(testing.allocator, &aw.writer);
    defer ed.deinit();
    _ = try ed.applyEvent(.{ .paste = "abc\ndef" });
    try testing.expectEqualStrings("abc\ndef", ed.buffer.items);
    try testing.expectEqual(@as(u32, 7), ed.cursor);
}

test "ctrl+a then ctrl+e bookend cursor across line" {
    var aw: std.Io.Writer.Allocating = .init(testing.allocator);
    defer aw.deinit();
    var ed = LineEditor.init(testing.allocator, &aw.writer);
    defer ed.deinit();
    try typeBytes(&ed, "hello world");
    _ = try ed.applyEvent(ctrlPress('a'));
    try testing.expectEqual(@as(u32, 0), ed.cursor);
    _ = try ed.applyEvent(ctrlPress('e'));
    try testing.expectEqual(@as(u32, 11), ed.cursor);
}

test "ctrl+k kills from cursor to end of line" {
    var aw: std.Io.Writer.Allocating = .init(testing.allocator);
    defer aw.deinit();
    var ed = LineEditor.init(testing.allocator, &aw.writer);
    defer ed.deinit();
    try typeBytes(&ed, "abcdef");
    ed.cursor = 3;
    _ = try ed.applyEvent(ctrlPress('k'));
    try testing.expectEqualStrings("abc", ed.buffer.items);
    try testing.expectEqual(@as(u32, 3), ed.cursor);
}
