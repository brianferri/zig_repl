const std = @import("std");
const assert = std.debug.assert;

const InternPool = @import("sema/InternPool.zig");

const Session = @This();

gpa: std.mem.Allocator,
io: std.Io,
stdin_file: std.Io.File,
stdout_file: std.Io.File,
/// Set up at session init so Stage 5/8 FFI smoke tests can capture
/// stderr without re-plumbing the field through Session.init. Not
/// read by Stage 2 code paths -- see the plan's Session sketch.
stderr_file: std.Io.File,
intern_pool: InternPool,
/// The session-root namespace -- the parent-less scope into which
/// top-level `const` / `var` lines bind. Mirrors the role of the
/// compiler's per-file-root namespace; future modules (Stage 6) hang
/// their own namespaces off this root via the `parent` chain.
root_namespace: InternPool.NamespaceIndex,
/// True when stdin is a terminal. Drives UX choices that depend on
/// whether the user's input is being echoed back to them:
///   * interactive: the kernel's line discipline echoes typed
///     input to the terminal; the REPL writes nothing extra.
///   * piped: the REPL mirrors each input line back to stdout
///     (see `Repl.echoInput`) so transcripts read like an
///     interactive session instead of bunching prompts together.
is_interactive: bool,
should_quit: bool,

pub fn init(
    gpa: std.mem.Allocator,
    io: std.Io,
) (std.mem.Allocator.Error || std.Io.Cancelable)!Session {
    assert(@intFromPtr(io.vtable) != 0);
    assert(@intFromPtr(io.userdata) != 0);

    var pool = try InternPool.init(gpa);
    errdefer pool.deinit();

    const root_namespace = try pool.createNamespace(gpa, .none);

    const stdin_file = std.Io.File.stdin();
    const is_interactive = try stdin_file.isTty(io);

    return .{
        .gpa = gpa,
        .io = io,
        .stdin_file = stdin_file,
        .stdout_file = std.Io.File.stdout(),
        .stderr_file = std.Io.File.stderr(),
        .intern_pool = pool,
        .root_namespace = root_namespace,
        .is_interactive = is_interactive,
        .should_quit = false,
    };
}

pub fn deinit(session: *Session) void {
    assert(@intFromPtr(session) != 0);
    session.intern_pool.deinit();
    session.* = undefined;
}
