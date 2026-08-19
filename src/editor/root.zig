//! Interactive line editing over `device.Event`s; depends only on `device`,
//! so any frontend reuses it.

pub const LineEditor = @import("LineEditor.zig");
pub const themes = @import("theme/root.zig");

test {
    _ = LineEditor;
    _ = themes;
    _ = @import("mock/Device.zig");
}
