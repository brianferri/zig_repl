//! Shared runner for the fuzz and regression suites: drives arbitrary input
//! through the interpreter under the caller's allocator (a leak-checking one in
//! tests), swallowing every *expected* failure -- parse, ZIR, and analysis errors
//! are the normal outcome for hostile input -- so only a leak, a double free, an
//! out-of-bounds access, or a panic makes a run fail. The counterpart to
//! compliance's `replRun`, but it asserts nothing about the OUTPUT: the contract
//! is merely that the pipeline survives.

const std = @import("std");
// Consume the interpreter as an external module (like the tty/wasm frontends), so
// the fuzz suite is fully decoupled from the repl's internals: it can be built and
// run on its own, and rewiring how it runs (its own step vs the normal test step)
// is a build.zig change, not a code change.
const repl = @import("repl");
const eval = repl.eval;
const Session = repl.Session;
const InternPool = repl.sema.InternPool;
const InputShape = repl.front.InputShape;

/// One persistent session fed input line by line -- the shape that surfaces
/// cross-line state bugs, where a later line trips over state an earlier one left
/// behind (as the root-namespace identity collision did). The pool is heap-owned
/// so the `Session`'s pointer to it stays valid across the runner's own moves.
pub const SessionRunner = struct {
    gpa: std.mem.Allocator,
    pool: *InternPool,
    session: Session,

    pub fn init(gpa: std.mem.Allocator) ?SessionRunner {
        const pool = gpa.create(InternPool) catch return null;
        pool.* = InternPool.init(gpa) catch {
            gpa.destroy(pool);
            return null;
        };
        const root_namespace = pool.createNamespace(gpa, .none) catch {
            pool.deinit();
            gpa.destroy(pool);
            return null;
        };
        return .{ .gpa = gpa, .pool = pool, .session = Session.init(gpa, pool, root_namespace) };
    }

    pub fn deinit(self: *SessionRunner) void {
        self.session.deinit();
        self.pool.deinit();
        self.gpa.destroy(self.pool);
    }

    pub fn feed(self: *SessionRunner, input: []const u8) void {
        // Respect the front end's own contract: it asserts a non-empty input
        // within the byte cap, so feeding out-of-range input would trip an
        // assertion that is the caller's bug, not the interpreter's.
        if (input.len == 0 or input.len > InputShape.max_input_bytes) return;
        var scratch: [64]u8 = undefined;
        var discarding: std.Io.Writer.Discarding = .init(&scratch);
        // `report` renders parse/ZIR/analysis diagnostics to the writer and
        // returns null; only host errors (OOM, a writer failure) propagate --
        // swallow those too, since the fuzzer's business is crashes and leaks.
        _ = eval.report(&self.session, input, &discarding.writer) catch {};
    }
};

/// Run one input through a fresh session.
pub fn runLine(gpa: std.mem.Allocator, input: []const u8) void {
    runSession(gpa, &.{input});
}

/// Run a sequence of inputs against one persistent session.
pub fn runSession(gpa: std.mem.Allocator, inputs: []const []const u8) void {
    var runner = SessionRunner.init(gpa) orelse return;
    defer runner.deinit();
    for (inputs) |input| runner.feed(input);
}
