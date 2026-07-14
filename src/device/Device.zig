//! Input-device interface the `LineEditor` drives. Modelled on
//! `std.Io.Reader`: an implementation embeds a `Device` as a field named
//! `interface` and recovers its concrete `*Self` inside the vtable via
//! `@fieldParentPtr("interface", d)`. The editor reads only this
//! interface, so any frontend supplies its own event source without the
//! editor learning of it.

const std = @import("std");
const assert = std.debug.assert;
const Event = @import("Event.zig");
const Color = @import("Color.zig");

const Device = @This();

/// Color capability the device reports for its output surface. The
/// editor reads it to pick how much of the prompt theme to colorize;
/// it is data, not behavior, so it lives on the interface (like
/// `Protocol.query_sequence`) rather than behind a vtable call.
color_level: Color.ColorLevel,
vtable: *const VTable,

pub const VTable = struct {
    /// Block until the next high-level input event. `null` signals
    /// end-of-input (the device closed).
    readEvent: *const fn (d: *Device) anyerror!?Event.Event,
};

pub fn readEvent(d: *Device) anyerror!?Event.Event {
    return d.vtable.readEvent(d);
}
