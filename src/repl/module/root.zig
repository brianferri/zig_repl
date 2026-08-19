//! The filesystem `@import` resolves against: `Fs` is the interface, backed by `Native` (a real
//! directory), `Vfs` (a mutable in-memory tree), or `Buffer` (a read-only embedded archive); `Layered`
//! stacks a writable project over a read-only std.

pub const Fs = @import("Fs.zig");
pub const Native = @import("Native.zig");
pub const Buffer = @import("Buffer.zig");
pub const Vfs = @import("Vfs.zig");
pub const Layered = @import("Layered.zig");

test {
    _ = Native;
    _ = Buffer;
    _ = Vfs;
    _ = Layered;
}
