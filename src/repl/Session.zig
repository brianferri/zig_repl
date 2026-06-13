//! Frontend-agnostic interpreter session: the state a backend needs to
//! evaluate input -- allocator, intern pool, root namespace, and the
//! committed pipeline snapshots. No terminal, file, or IO surface; those
//! live in the frontend (`frontend/tty/Repl.zig` for the TTY REPL). Any
//! frontend -- the TTY REPL, a wasm module, or a test -- creates one of
//! these directly.

const std = @import("std");
const assert = std.debug.assert;

const InternPool = @import("sema/InternPool.zig");

const Session = @This();

gpa: std.mem.Allocator,
/// Borrowed: caller owns the InternPool and is responsible for
/// `deinit`-ing it. Session.deinit does not touch the pool.
/// Decoupling lets tests share a pool across multiple Sessions
/// or construct minimal Sessions on top of an existing pool
/// without lifecycle complications.
intern_pool: *InternPool,
/// The session-root namespace -- the parent-less scope into which
/// top-level `const` / `var` lines bind. Mirrors the role of the
/// compiler's per-file-root namespace; future modules hang their own
/// namespaces off this root via the `parent` chain.
root_namespace: InternPool.NamespaceIndex,
/// Each successfully-analysed line's ZIR, kept for the session
/// lifetime. Function values store an index into this list
/// (`Key.Func.source_zir_id`); call sites swap `sema.zir` to the
/// matching snapshot when crossing line boundaries. The session keeps
/// only the ZIR -- the Ast and wrapped source the front end produced
/// alongside it are released at commit.
line_zir: std.ArrayListUnmanaged(std.zig.Zir),

pub fn init(
    gpa: std.mem.Allocator,
    intern_pool: *InternPool,
    root_namespace: InternPool.NamespaceIndex,
) Session {
    return .{
        .gpa = gpa,
        .intern_pool = intern_pool,
        .root_namespace = root_namespace,
        .line_zir = .empty,
    };
}

pub fn deinit(session: *Session) void {
    for (session.line_zir.items) |*z| z.deinit(session.gpa);
    session.line_zir.deinit(session.gpa);
    session.* = undefined;
}
