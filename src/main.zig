const std = @import("std");
const zig_repl = @import("zig_repl");

pub fn main(init: std.process.Init) !void {
    var session = zig_repl.Session.init(init.gpa, init.arena.allocator(), init.io);
    defer session.deinit();

    var repl = zig_repl.Repl.init(&session);
    return repl.run();
}
