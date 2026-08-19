//! Shared runner for the fuzz and regression suites: drive arbitrary input through
//! the interpreter, swallowing expected parse/ZIR/analysis failures so only a leak
//! or crash fails a run. Asserts nothing about output -- survival is the contract.

const std = @import("std");
const repl = @import("repl");
const eval = repl.eval;
const Session = repl.Session;
const InternPool = repl.sema.InternPool;
const InputShape = repl.front.InputShape;

/// One persistent session fed input line by line, to surface cross-line state bugs.
/// The pool is heap-owned so the `Session`'s pointer to it stays valid across moves.
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
        const root_namespace = pool.createNamespace(gpa, .{}) catch {
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
        // The front end asserts a non-empty input within the byte cap; guard so
        // out-of-range input is rejected here, not tripping that assertion.
        if (input.len == 0 or input.len > InputShape.max_input_bytes) return;
        var scratch: [64]u8 = undefined;
        var discarding: std.Io.Writer.Discarding = .init(&scratch);
        // Swallow host errors too (OOM, writer failure); the fuzzer's business is
        // crashes and leaks.
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
