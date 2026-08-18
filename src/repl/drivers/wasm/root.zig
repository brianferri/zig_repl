//! The wasm frontend's driver module: its command set and the explorer
//! outline, over the shared core (`repl`). `commands` is ordered as `:help`
//! shows them.

const repl = @import("repl");
const Registry = repl.commands.Registry;
const help = repl.commands.help;
const dump = repl.commands.dump;
const Session = repl.Session;

pub const outline = @import("outline.zig");
pub const LineInput = @import("LineInput.zig");
pub const themes = @import("editor").themes;

pub const commands = Registry(&[_]type{
    help,
    dump,
    @import("clear.zig"),
}, *Session);
