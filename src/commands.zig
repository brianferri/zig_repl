//! Session-utility commands, reusable across frontends. Each is a module
//! whose struct binds the context it acts on and embeds the `Command`
//! interface; a frontend assembles its own registry of `*Command` from
//! these plus its frontend-specific commands, then drives it through
//! `Command.dispatch` / `Command.list`.

pub const Command = @import("commands/Command.zig");
pub const help = @import("commands/help.zig");
pub const dump = @import("commands/dump.zig");
