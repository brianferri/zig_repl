//! Interactive line editing over `device.Event`s: the multi-line `LineEditor`
//! (cursor, history, redraw) and the prompt `themes` it draws with. Depends only
//! on `device`, so any frontend -- the tty driver or the wasm frontend -- reuses it.

pub const LineEditor = @import("LineEditor.zig");
pub const themes = @import("theme/root.zig");

test {
    _ = LineEditor;
    _ = themes;
    _ = @import("mock/Device.zig");
}
