//! Mock `Device`: events are queued up front rather than read from a
//! terminal. Implements the `device/Device.zig` interface from a replayed
//! event queue, so tests can drive a `Device` consumer (e.g. `LineEditor`)
//! without a raw-mode tty.
//!
//! `readEvent` is non-blocking: it yields the next queued event, then
//! `null` once the queue drains (end-of-input).

const std = @import("std");
const assert = std.debug.assert;
const Device = @import("device").Device;
const Event = @import("device").Event;
const Color = @import("device").Color;

const Mock = @This();

interface: Device,
/// Pending events, oldest at `head`. The host enqueues with `push`;
/// `readEvent` advances `head` rather than shifting, so a drained
/// queue keeps its capacity for the next batch.
queue: std.ArrayListUnmanaged(Event.Event),
head: usize,
gpa: std.mem.Allocator,

pub fn init(gpa: std.mem.Allocator, color_level: Color.ColorLevel) Mock {
    return .{
        .interface = .{ .color_level = color_level, .vtable = &device_vtable },
        .queue = .empty,
        .head = 0,
        .gpa = gpa,
    };
}

pub fn deinit(self: *Mock) void {
    self.queue.deinit(self.gpa);
    self.* = undefined;
}

/// Hand out the device interface. Valid
/// only for a live `Mock` at a stable address: the vtable
/// recovers `*Mock` from `&interface` via `@fieldParentPtr`.
pub fn device(self: *Mock) *Device {
    return &self.interface;
}

/// Enqueue one event for the editor to read. A `paste` payload is
/// borrowed, not copied -- its bytes must outlive the matching read.
pub fn push(self: *Mock, event: Event.Event) !void {
    try self.queue.append(self.gpa, event);
}

const device_vtable: Device.VTable = .{ .readEvent = vtableReadEvent };

fn vtableReadEvent(d: *Device) anyerror!?Event.Event {
    const self: *Mock = @fieldParentPtr("interface", d);
    if (self.head >= self.queue.items.len) return null;
    const event = self.queue.items[self.head];
    self.head += 1;
    return event;
}

// `readLine`'s read loop has no other unit-test entry: its only other
// device, `Terminal`, needs a raw-mode tty.

const testing = std.testing;
const LineEditor = @import("../LineEditor.zig");
const themes = @import("../theme/root.zig");

fn pushKeys(dev: *Mock, bytes: []const u8) !void {
    for (bytes) |b| try dev.push(.{ .key_press = .{ .codepoint = b } });
}

test "readLine assembles a submitted line through the Device vtable" {
    var dev = Mock.init(testing.allocator, .none);
    defer dev.deinit();
    try pushKeys(&dev, "1 + 2");
    try dev.push(.{ .key_press = .{ .codepoint = Event.key.enter } });

    var aw: std.Io.Writer.Allocating = .init(testing.allocator);
    defer aw.deinit();
    var editor = LineEditor.init(testing.allocator, &aw.writer);
    defer editor.deinit();

    const line = try editor.readLine(dev.device(), themes.default);
    try testing.expect(line != null);
    try testing.expectEqualStrings("1 + 2", line.?);
}

test "readLine returns null when the device drains (end of input)" {
    var dev = Mock.init(testing.allocator, .none);
    defer dev.deinit();

    var aw: std.Io.Writer.Allocating = .init(testing.allocator);
    defer aw.deinit();
    var editor = LineEditor.init(testing.allocator, &aw.writer);
    defer editor.deinit();

    const line = try editor.readLine(dev.device(), themes.default);
    try testing.expect(line == null);
}

test "shift+enter keeps reading; the line spans the embedded newline" {
    var dev = Mock.init(testing.allocator, .none);
    defer dev.deinit();
    try pushKeys(&dev, "a");
    try dev.push(.{ .key_press = .{ .codepoint = Event.key.enter, .modifiers = .{ .shift = true } } });
    try pushKeys(&dev, "b");
    try dev.push(.{ .key_press = .{ .codepoint = Event.key.enter } });

    var aw: std.Io.Writer.Allocating = .init(testing.allocator);
    defer aw.deinit();
    var editor = LineEditor.init(testing.allocator, &aw.writer);
    defer editor.deinit();

    const line = try editor.readLine(dev.device(), themes.default);
    try testing.expect(line != null);
    try testing.expectEqualStrings("a\nb", line.?);
}
