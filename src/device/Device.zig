//! Input-device interface the `LineEditor` drives, modelled on `std.Io.Reader`. The editor reads only this
//! interface, so any frontend supplies its own source.

const std = @import("std");
const assert = std.debug.assert;
const Event = @import("Event.zig");
const Color = @import("Color.zig");

const Device = @This();

/// Data, not behavior, so it lives on the interface rather than behind a vtable call.
color_level: Color.ColorLevel,
vtable: *const VTable,

pub const VTable = struct {
    /// Blocks until the next event; `null` signals end-of-input.
    readEvent: *const fn (d: *Device) anyerror!?Event.Event,
};

pub fn readEvent(d: *Device) anyerror!?Event.Event {
    return d.vtable.readEvent(d);
}
