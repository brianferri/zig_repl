//! The single owner of "run one REPL input against a session": wrap +
//! inject prior decls, gate parse/ZIR errors, analyze, and commit the
//! pipeline so later lines resolve cross-references. `Repl` and the test
//! harnesses call `run` instead of re-walking this loop -- which also
//! means the test suite exercises the same path the interactive REPL does.
//!
//! Lives at `src/` (not a subdir) so it can import both `front/` and
//! `sema/`, which Zig blocks across sibling subdirs.
//!
//! Not for single-shot Sema unit tests: those want no injection, no
//! commit, and no session lifecycle (see `evalSource` in sema_eval_test).

const std = @import("std");
const assert = std.debug.assert;

const Pipeline = @import("front/Pipeline.zig");
const InputShape = @import("front/InputShape.zig");
const Diagnostic = @import("render/Diagnostic.zig");
const Sema = @import("sema/Sema.zig");
const Session = @import("Session.zig");
const Value = @import("sema/Value.zig");

/// `value` is null for a declaration (or a Sema gap); `shape` lets the
/// caller decide whether a null result is expected (declaration) or a
/// gap to report (expression). Diagnostics are written to the caller's
/// writer, not surfaced here.
pub const Outcome = struct {
    value: ?Value,
    shape: InputShape.Shape,
};

/// Evaluate a full REPL input. A line that is declarations followed by a
/// trailing expression runs as two passes (bind, then evaluate with the
/// bindings in scope); the returned `Outcome` is the last segment's. If
/// the declaration pass fails, its error propagates and the expression
/// pass is skipped -- it would only reference unbound names.
pub fn run(session: *Session, input: []const u8, diag: *std.Io.Writer) !Outcome {
    assert(input.len > 0);
    assert(input.len <= InputShape.max_input_bytes);
    if (try InputShape.splitTrailingExpr(session.gpa, input)) |split| {
        _ = try analyzeSegment(session, split.decls, diag);
        return analyzeSegment(session, split.expr, diag);
    }
    return analyzeSegment(session, input, diag);
}

/// Run `input` for an interactive prompt and resolve its diagnostics. `run`
/// already writes parse/ZIR/analysis errors to `diag`, so those are swallowed
/// here (the prompt keeps going); an expression that produced no value writes
/// the "(no value)" marker. Returns the Value the caller should render, or
/// null when there is nothing to display. Host errors (OOM, writer) are fatal.
pub fn report(session: *Session, input: []const u8, diag: *std.Io.Writer) !?Value {
    const outcome = run(session, input, diag) catch |err| switch (err) {
        error.ParseError, error.ZirError, error.AnalysisFail => return null,
        else => |e| return e,
    };
    if (outcome.value) |value| return value;
    if (outcome.shape == .expression) try diag.writeAll("(no value)\n");
    return null;
}

/// One wrapped segment: front end + Sema + commit. Parse/ZIR errors are
/// rendered to `diag` and returned as `error.ParseError`/`error.ZirError`;
/// `Sema.analyze` writes its own diagnostics to `diag` and returns
/// `error.AnalysisFail`. On success the pipeline is committed so a later
/// segment/line can reference what it bound.
fn analyzeSegment(session: *Session, input: []const u8, diag: *std.Io.Writer) !Outcome {
    assert(input.len > 0);
    assert(input.len <= InputShape.max_input_bytes);
    var result = Pipeline.runWithInjection(
        session.gpa,
        input,
        session.intern_pool,
        .init(session.root_namespace),
    ) catch |err| {
        try diag.print("front-end failed: {s}\n", .{@errorName(err)});
        return err;
    };
    var committed = false;
    defer if (!committed) result.deinit(session.gpa);

    if (result.hasParseErrors()) {
        try Diagnostic.renderParseErrors(result.tree, result.userView(), diag);
        return error.ParseError;
    }
    if (result.hasZirErrors()) {
        try Diagnostic.renderZirErrors(session.gpa, result.zir, result.tree, result.userView(), diag);
        return error.ZirError;
    }

    // Register this line as a file BEFORE analysing it, so its `File.Index` is
    // fixed and any module `@import`d mid-analysis takes a later index without
    // colliding. A Func bound here replays its body on a later cross-line call by
    // that index. The Ast + wrapped source move onto the `File` (mirroring
    // `Zcu.File.tree`/`.source`), kept so a Sema error resolves against this file's
    // own tree -- as the compiler resolves `SrcLoc.span` against `file.getTree`.
    const shape = result.wrapped.shape;
    committed = true;
    const line_index: Session.Index = @intCast(session.files.items.len);
    session.files.append(session.gpa, .{
        .zir = result.zir,
        .tree = result.tree,
        .wrapped = result.wrapped,
        .sub_file_path = null,
    }) catch |err| {
        result.deinit(session.gpa);
        return err;
    };

    const value = Sema.analyze(session, line_index, diag) catch |err| {
        // Render the source-anchored caret for a Sema failure. Sema stored the
        // (unresolved) error in `failed_analysis`; resolve its `LazySrcLoc` against
        // this file's ZIR and Ast -- both now owned by the `File` (so `result`'s
        // handles alias live memory) -- as the compiler resolves late against
        // `file.getTree` in its driver.
        if (session.failed_analysis) |em| {
            defer {
                em.destroy(session.gpa);
                session.failed_analysis = null;
            }
            if (session.files.items[line_index].zir) |file_zir| {
                const node = em.src_loc.resolveNode(file_zir);
                var notes_buf: [16]Diagnostic.Note = undefined;
                const n = @min(em.notes.len, notes_buf.len);
                for (notes_buf[0..n], em.notes[0..n]) |*dst, note| {
                    dst.* = .{ .node = note.src_loc.resolveNode(file_zir), .msg = note.msg };
                }
                Diagnostic.renderSemaError(session.gpa, result.tree, result.userView(), node, em.msg, notes_buf[0..n], diag) catch {};
            }
        }
        // Tombstone the failed line: free its ZIR but keep the `File` slot (and
        // any modules it loaded, at later indices) so `File.Index` values stay
        // stable -- the compiler likewise retains failed files.
        if (session.files.items[line_index].zir) |*z| z.deinit(session.gpa);
        session.files.items[line_index].zir = null;
        return err;
    };
    return .{ .value = value, .shape = shape };
}
