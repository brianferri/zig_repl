//! Command interface, generic over the frontend context `Ctx` its `run` receives (`*Repl` for the TTY,
//! `*Session` for wasm). Stateless; `run` gets the full command set too, so `:help` can enumerate it.

const std = @import("std");

pub fn Command(comptime Ctx: type) type {
    return struct {
        name: []const u8,
        summary: []const u8,
        run: *const fn (ctx: Ctx, set: []const @This(), argument: []const u8, writer: *std.Io.Writer) anyerror!void,
    };
}
