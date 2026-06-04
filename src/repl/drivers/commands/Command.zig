//! Command interface, generic over the frontend context `Ctx` its `run`
//! receives (`*Repl` for the TTY, `*Session` for wasm). A command is a
//! stateless descriptor -- a name, a summary, and a `run` that takes the
//! context, the full set (so `:help` can enumerate it), the argument text, and
//! the output writer. A frontend builds its set as an array of these (see
//! `registry.zig`): no `*anyopaque`, no per-command state, and registering one
//! is a single entry in that array.

const std = @import("std");

pub fn Command(comptime Ctx: type) type {
    return struct {
        name: []const u8,
        summary: []const u8,
        run: *const fn (ctx: Ctx, set: []const @This(), argument: []const u8, writer: *std.Io.Writer) anyerror!void,
    };
}
