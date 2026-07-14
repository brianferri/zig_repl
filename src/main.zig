const std = @import("std");
const builtin = @import("builtin");
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

    // Point `@import("std")` at the system standard library when it can be
    // located. Best-effort: without it the REPL still runs and std imports report
    // the usual unloaded-module diagnostic. The directory handle and the source
    // both outlive the session, which only borrows the interface pointer.
    var std_root = openSystemStd(init.gpa, init.io, init.environ_map);
    defer if (std_root) |*d| d.close(init.io);
    var source: repl.NativeModuleSource = undefined;
    if (std_root) |root| {
        source = .{ .io = init.io, .root = root };
        session.module_source = &source.interface;
    }

    var driver = try tty.Repl.init(&session, init.io);
    return driver.run(init.environ_map);
}

/// Open the system standard-library directory so `@import("std")` resolves.
/// Prefers an explicit `ZIG_LIB_DIR`; otherwise finds `zig` on `PATH` and reuses
/// the compiler's own lib-dir discovery (`findZigLibDirFromSelfExe`, as
/// `build.zig` does at configure time). Returns null on any failure -- loading
/// std is optional, so a missing or unreadable toolchain degrades to no std.
fn openSystemStd(gpa: std.mem.Allocator, io: std.Io, environ_map: *std.process.Environ.Map) ?std.Io.Dir {
    if (std.zig.EnvVar.ZIG_LIB_DIR.get(environ_map)) |lib_dir| {
        const std_path = std.fs.path.join(gpa, &.{ lib_dir, "std" }) catch return null;
        defer gpa.free(std_path);
        return std.Io.Dir.openDirAbsolute(io, std_path, .{}) catch null;
    }

    const zig_exe = findExeOnPath(gpa, io, environ_map, if (builtin.os.tag == .windows) "zig.exe" else "zig") orelse return null;
    defer gpa.free(zig_exe);
    const cwd = std.zig.getResolvedCwd(io, gpa) catch return null;
    defer gpa.free(cwd);
    var lib_dir = std.zig.findZigLibDirFromSelfExe(gpa, io, cwd, zig_exe) catch return null;
    defer lib_dir.handle.close(io);
    defer if (lib_dir.path) |p| gpa.free(p);
    return lib_dir.handle.openDir(io, "std", .{}) catch null;
}

/// Search `PATH` for an executable named `name`, returning its absolute path
/// (caller owns) or null. `std` has no such helper, and `findZigLibDirFromSelfExe`
/// needs a concrete path to walk up from.
fn findExeOnPath(gpa: std.mem.Allocator, io: std.Io, environ_map: *std.process.Environ.Map, name: []const u8) ?[]const u8 {
    const path_var = environ_map.get("PATH") orelse return null;
    const sep: u8 = if (builtin.os.tag == .windows) ';' else ':';
    var it = std.mem.tokenizeScalar(u8, path_var, sep);
    while (it.next()) |dir| {
        const full = std.fs.path.join(gpa, &.{ dir, name }) catch continue;
        std.Io.Dir.accessAbsolute(io, full, .{}) catch {
            gpa.free(full);
            continue;
        };
        return full;
    }
    return null;
}
