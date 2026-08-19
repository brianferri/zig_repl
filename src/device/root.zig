//! Input-device abstraction: a frontend's input source implements `Device` (the
//! interface the shared `LineEditor` drives), producing canonical `Event`s and
//! reporting a `Color` capability. The posix tty stack (`terminal/`) and the
//! wasm event queue are two implementations.

pub const Device = @import("Device.zig");
pub const Event = @import("Event.zig");
pub const Color = @import("Color.zig");

test {
    _ = Device;
    _ = Event;
    _ = Color;
}
