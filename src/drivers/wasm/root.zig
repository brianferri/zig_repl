//! The wasm frontend's command set, in the order `:help` lists them. Each entry
//! is a command module; registering one is writing its module and adding an
//! `@import` to this list. The registry derives the lookup and dispatch from
//! the list, with the `*Session` as every command's context.

const Registry = @import("../commands/registry.zig").Registry;
const help = @import("../commands/help.zig");
const dump = @import("../commands/dump.zig");
const Session = @import("../../Session.zig");

pub const commands = Registry(&[_]type{
    help,
    dump,
    @import("clear.zig"),
}, *Session);
