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

    var session = try zig_repl.Session.init(init.gpa, init.io, &pool, root_namespace);
    defer session.deinit();

    var repl = zig_repl.Repl.init(&session);
    return repl.run();
}
