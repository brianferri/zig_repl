//! Raw-mode terminal input stack: negotiates keyboard protocols, parses the
//! ECMA-48 byte stream, and yields canonical `device.Event`s.

pub const Terminal = @import("Terminal.zig");

// Exposed for a frontend that supplies its own byte stream (the wasm REPL).
pub const Parser = @import("Parser.zig");
pub const Protocol = @import("Protocol.zig");
pub const Xterm = @import("protocol/Xterm.zig");

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
    // Only the host's backend compiles; its OS-specific headers won't cross-build.
    _ = switch (@import("builtin").os.tag) {
        .windows => @import("platform/Windows.zig"),
        else => @import("platform/Posix.zig"),
    };
}
