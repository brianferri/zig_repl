//! A frontend's command set: the command descriptors plus an O(1) name lookup,
//! both comptime-derived from `mods` (the command modules) for context `Ctx`.
//! Each module exposes `command(Ctx) Command(Ctx)`, so registering a command is
//! writing its module and adding it to the `mods` a frontend instantiates with.

const std = @import("std");

const Command = @import("Command.zig").Command;

pub fn Registry(comptime mods: []const type, comptime Ctx: type) type {
    return struct {
        /// Every command, in declared order -- the order `:help` lists them.
        pub const all = blk: {
            var set: [mods.len]Command(Ctx) = undefined;
            for (mods, 0..) |Module, i| set[i] = Module.command(Ctx);
            break :blk set;
        };

        /// Name -> index, derived from the descriptors' own names so it cannot
        /// drift from the set and `find` is O(1).
        const index = blk: {
            var pairs: [all.len]struct { []const u8, usize } = undefined;
            for (all, 0..) |cmd, i| pairs[i] = .{ cmd.name, i };
            break :blk std.StaticStringMap(usize).initComptime(pairs);
        };

        /// The command named `name`, or null if none matches.
        pub fn find(name: []const u8) ?Command(Ctx) {
            return all[index.get(name) orelse return null];
        }
    };
}
