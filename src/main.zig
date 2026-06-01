const std = @import("std");
const zig_repl = @import("zig_repl");

pub fn main(init: std.process.Init) !void {
    // InternPool is externally owned; Session borrows it.
    // Decouples pool lifetime from Session so tests can reuse a
    // pool across Sessions and Sema doesn't need to know which is
    // which.
    var pool = try zig_repl.sema.InternPool.init(init.gpa);
    defer pool.deinit();
    const root_namespace = try pool.createNamespace(init.gpa, .none);

    var session = zig_repl.Session.init(init.gpa, &pool, root_namespace);
    defer session.deinit();

    // The TTY frontend wraps the core session with the terminal/IO surface.
    var repl = try zig_repl.frontend.tty.Repl.init(&session, init.io);
    return repl.run(init.environ_map);
}
