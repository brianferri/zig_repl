//! Raw-mode terminal input stack: negotiates keyboard protocols, parses the
//! ECMA-48 byte stream, and yields canonical `device.Event`s through the
//! `device.Device` interface. `Terminal` is the entry point; the `standard/`
//! and `protocol/` parsers and the `platform/` backends are internal.
//! Depends only on `std` and the sibling `device/` vocabulary.

pub const Terminal = @import("Terminal.zig");

test {
    _ = Terminal;
    _ = @import("Parser.zig");
    _ = @import("Protocol.zig");
    _ = @import("Standard.zig");
    _ = @import("Negotiate.zig");
    _ = @import("standard/Csi.zig");
    _ = @import("standard/Ss2.zig");
    _ = @import("standard/Ss3.zig");
    _ = @import("standard/Osc.zig");
    _ = @import("standard/St.zig");
    _ = @import("standard/StringCommand.zig");
    _ = @import("protocol/Xterm.zig");
    _ = @import("protocol/ModifyOtherKeys.zig");
    _ = @import("protocol/Kitty.zig");
    _ = @import("protocol/BracketedPaste.zig");
    _ = @import("terminal_test.zig");
    // Platform backends import OS-specific headers; pick the one matching
    // the host so cross-target test runs stay clean.
    _ = switch (@import("builtin").os.tag) {
        .windows => @import("platform/Windows.zig"),
        else => @import("platform/Posix.zig"),
    };
}
