//! Module sources: where `@import` obtains bytes. `Source` is the interface the
//! interpreter resolves imports against; `Native` reads a real directory (the
//! system standard library), `Buffer` an in-memory archive packed into the binary
//! for targets with no filesystem.

pub const Source = @import("Source.zig");
pub const Native = @import("Native.zig");
pub const Buffer = @import("Buffer.zig");

test {
    _ = Native;
    _ = Buffer;
}
