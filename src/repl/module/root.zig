//! The filesystem `@import` resolves against. `Fs` is the interface; `Native`
//! backs it with a real directory, `Vfs` with a mutable in-memory tree, `Buffer`
//! with a read-only embedded archive (the standard library on a target with no
//! filesystem). `Layered` stacks a writable project over a read-only std.

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
