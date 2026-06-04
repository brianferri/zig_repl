//! Input-device abstraction. A frontend's input source implements `Device`
//! (the interface the shared `LineEditor` drives), producing canonical
//! `Event`s and reporting a `Color` capability. Self-contained -- depends
//! only on `std` -- so any frontend builds on it without reaching into a
//! concrete backend: the posix tty stack (`terminal/`) and a wasm event
//! queue (`frontend/wasm/Device.zig`) are two implementations.

pub const Device = @import("Device.zig");
pub const Event = @import("Event.zig");
pub const Color = @import("Color.zig");

test {
    _ = Device;
    _ = Event;
    _ = Color;
}
