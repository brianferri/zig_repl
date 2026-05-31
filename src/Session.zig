const std = @import("std");
const assert = std.debug.assert;

const InternPool = @import("sema/InternPool.zig");
const Pipeline = @import("front/Pipeline.zig");
const Terminal = @import("terminal/Terminal.zig");
const themes = @import("theme/root.zig");

const Session = @This();

gpa: std.mem.Allocator,
io: std.Io,
stdin_file: std.Io.File,
stdout_file: std.Io.File,
/// Set up at session init so Stage 5/8 FFI smoke tests can capture
/// stderr without re-plumbing the field through Session.init. Not
/// read by Stage 2 code paths -- see the plan's Session sketch.
stderr_file: std.Io.File,
/// Borrowed: caller owns the InternPool and is responsible for
/// `deinit`-ing it. Session.deinit does not touch the pool.
/// Decoupling lets tests share a pool across multiple Sessions
/// or construct minimal Sessions on top of an existing pool
/// without lifecycle complications.
intern_pool: *InternPool,
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
/// Selected prompt theme (a preference; the terminal's color
/// capability decides how much of it shows). Defaults to the Zig
/// theme; repoint to switch themes at runtime.
theme: *const themes.Theme,
/// The live terminal while an interactive session runs: `readLine`
/// drives it for events and the prompt's color level, and commands
/// introspect it. Null in cooked/piped mode.
terminal: ?*Terminal,
should_quit: bool,
/// Every successfully-analysed Pipeline.Result stays here for
/// the session lifetime. Function values store an index into
/// this list (`Key.Func.source_zir_id`); call sites swap
/// `sema.zir` to the matching snapshot when crossing line
/// boundaries. Function values retain their compiled
/// body's host data via a back-reference.
pipelines: std.ArrayListUnmanaged(Pipeline.Result),

pub fn init(
    gpa: std.mem.Allocator,
    io: std.Io,
    intern_pool: *InternPool,
    root_namespace: InternPool.NamespaceIndex,
) std.Io.Cancelable!Session {
    assert(@intFromPtr(io.vtable) != 0);
    assert(@intFromPtr(io.userdata) != 0);

    const stdin_file = std.Io.File.stdin();
    const is_interactive = try stdin_file.isTty(io);

    return .{
        .gpa = gpa,
        .io = io,
        .stdin_file = stdin_file,
        .stdout_file = std.Io.File.stdout(),
        .stderr_file = std.Io.File.stderr(),
        .intern_pool = intern_pool,
        .root_namespace = root_namespace,
        .is_interactive = is_interactive,
        .theme = themes.default,
        .terminal = null,
        .should_quit = false,
        .pipelines = .empty,
    };
}

/// Bare constructor for tests that drive Sema directly without
/// needing the I/O surface (`isTty`, stdin/stdout/stderr). Skips
/// the tty probe so unit tests stay hermetic. Anything that reads
/// `io` / `stdin_file` / `stdout_file` / `stderr_file` /
/// `is_interactive` will hit `undefined` -- intentional, so misuse
/// surfaces loudly.
pub fn initForTest(
    gpa: std.mem.Allocator,
    intern_pool: *InternPool,
    root_namespace: InternPool.NamespaceIndex,
) Session {
    return .{
        .gpa = gpa,
        .io = undefined,
        .stdin_file = undefined,
        .stdout_file = undefined,
        .stderr_file = undefined,
        .intern_pool = intern_pool,
        .root_namespace = root_namespace,
        .is_interactive = false,
        .theme = themes.default,
        .terminal = null,
        .should_quit = false,
        .pipelines = .empty,
    };
}

pub fn deinit(session: *Session) void {
    assert(@intFromPtr(session) != 0);
    for (session.pipelines.items) |*p| p.deinit(session.gpa);
    session.pipelines.deinit(session.gpa);
    session.* = undefined;
}
