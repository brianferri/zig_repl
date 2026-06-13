const std = @import("std");
const repl = @import("repl");
const tty = @import("tty");

pub fn main(init: std.process.Init) !void {
    // InternPool is externally owned; Session borrows it.
    // Decouples pool lifetime from Session so tests can reuse a
    // pool across Sessions and Sema doesn't need to know which is
    // which.
    var pool = try repl.sema.InternPool.init(init.gpa);
    defer pool.deinit();
    const root_namespace = try pool.createNamespace(init.gpa, .none);

    var session = repl.Session.init(init.gpa, &pool, root_namespace);
    defer session.deinit();

    // The tty driver wraps the core session with the terminal/IO surface.
    var driver = try tty.Repl.init(&session, init.io);
    return driver.run(init.environ_map);
}
