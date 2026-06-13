//! The tty frontend module: the line-driven REPL over the raw-mode terminal.
//! `commands` is its command set in the order `:help` lists them; registering
//! one is writing its module and adding an `@import` here.

const repl = @import("repl");
const Registry = repl.commands.Registry;
const help = repl.commands.help;
const dump = repl.commands.dump;

pub const Repl = @import("Repl.zig");

pub const commands = Registry(&[_]type{
    help,
    dump,
    @import("quit.zig"),
    @import("theme.zig"),
    @import("terminal.zig"),
}, *Repl);

test {
    _ = @import("Repl.zig");
    _ = @import("quit.zig");
    _ = @import("theme.zig");
    _ = @import("terminal.zig");
    _ = @import("LineEditor.zig");
    _ = @import("Theme.zig");
    _ = @import("theme/root.zig");
    _ = @import("mock/Device.zig");
}
