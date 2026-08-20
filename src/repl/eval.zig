//! Runs one REPL input against a session: wrap + inject prior decls, gate parse/ZIR errors, analyze, and
//! commit so later lines resolve cross-references.

const std = @import("std");
const assert = std.debug.assert;

const Pipeline = @import("front/Pipeline.zig");
const InputShape = @import("front/InputShape.zig");
const Diagnostic = @import("render/Diagnostic.zig");
const Sema = @import("sema/Sema.zig");
const Session = @import("Session.zig");
const Value = @import("sema/Value.zig");

/// `value` is null for a declaration or a Sema gap; `shape` disambiguates (expected vs. a gap to report).
pub const Outcome = struct {
    value: ?Value,
    shape: InputShape.Shape,
};

/// Declarations followed by a trailing expression run as two passes (bind, then evaluate with the bindings
/// in scope); the `Outcome` is the last segment's. A failed declaration pass skips the expression pass,
/// which would only reference unbound names.
pub fn run(session: *Session, input: []const u8, diag: *std.Io.Writer) !Outcome {
    assert(input.len > 0);
    assert(input.len <= InputShape.max_input_bytes);
    if (try InputShape.splitTrailingExpr(session.gpa, input)) |split| {
        _ = try analyzeSegment(session, split.decls, diag);
        return analyzeSegment(session, split.expr, diag);
    }
    return analyzeSegment(session, input, diag);
}

/// Swallows the parse/ZIR/analysis errors `run` already wrote to `diag` so the prompt keeps going, and
/// writes the `(no value)` marker for an expression with no value. Host errors (OOM, writer) are fatal.
pub fn report(session: *Session, input: []const u8, diag: *std.Io.Writer) !?Value {
    const outcome = run(session, input, diag) catch |err| switch (err) {
        error.ParseError, error.ZirError, error.AnalysisFail => return null,
        else => |e| return e,
    };
    if (outcome.value) |value| return value;
    if (outcome.shape == .expression) try diag.writeAll("(no value)\n");
    return null;
}

/// Front end + Sema for one segment; errors are rendered to `diag`. On success the pipeline is committed,
/// so a later segment/line can reference what it bound.
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

    // Register this line as a file BEFORE analysing it, so its `File.Index` is fixed and a module
    // `@import`d mid-analysis takes a later index without colliding.
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
        // Resolve the error's `LazySrcLoc` against the file it was raised in (`em.file`) -- a prior line
        // when the error is inside a called function's body, whose retained source is still available.
        if (session.failed_analysis) |em| {
            defer {
                em.destroy(session.gpa);
                session.failed_analysis = null;
            }
            const err_file = &session.files.items[em.file];
            // A REPL line has no on-disk path; fall back to the placeholder.
            const src_path = err_file.sub_file_path orelse Diagnostic.repl_source_path;
            const rendered = caret: {
                const file_zir = err_file.zir orelse break :caret false;

                // A loaded module keeps only ZIR, so re-read and re-parse its source on demand (a REPL line
                // still has its tree). The tree is needed to resolve the src loc into an AST node.
                var owned_src: ?[:0]u8 = null;
                var owned_tree: ?std.zig.Ast = null;
                defer if (owned_src) |s| session.gpa.free(s);
                defer if (owned_tree) |*t| t.deinit(session.gpa);

                var tree: std.zig.Ast = undefined;
                var view: Pipeline.UserView = undefined;
                if (err_file.wrapped) |*wrapped| {
                    tree = err_file.tree orelse break :caret false;
                    view = .{ .text = wrapped.userText(), .offset_in_source = wrapped.user_offset };
                } else {
                    const provider = session.module_source orelse break :caret false;
                    const src = provider.read(session.gpa, src_path) catch break :caret false;
                    owned_src = src;
                    tree = std.zig.Ast.parse(session.gpa, src, .{ .mode = .zig }) catch break :caret false;
                    owned_tree = tree;
                    view = .{ .text = src, .offset_in_source = 0 };
                }

                const node = em.src_loc.resolveNode(file_zir, tree);
                var notes_buf: [16]Diagnostic.Note = undefined;
                const n = @min(em.notes.len, notes_buf.len);
                for (notes_buf[0..n], em.notes[0..n]) |*dst, note| {
                    dst.* = .{ .node = note.src_loc.resolveNode(file_zir, tree), .msg = note.msg };
                }
                Diagnostic.renderSemaError(session.gpa, src_path, tree, view, node, em.msg, notes_buf[0..n], diag) catch {};
                break :caret true;
            };
            // No source to anchor against (e.g. the reserved root file); print the message alone.
            if (!rendered) {
                diag.print("error: {s}\n", .{em.msg}) catch {};
                for (em.notes) |note| diag.print("note: {s}\n", .{note.msg}) catch {};
            }
        }
        // Tombstone the failed line: free its ZIR/AST/source but keep the `File` slot so later `File.Index`
        // values stay stable. A later caret lookup bails at the now-null ZIR.
        const failed = &session.files.items[line_index];
        if (failed.zir) |*z| z.deinit(session.gpa);
        failed.zir = null;
        if (failed.tree) |*t| t.deinit(session.gpa);
        failed.tree = null;
        if (failed.wrapped) |*w| w.deinit(session.gpa);
        failed.wrapped = null;
        return err;
    };
    return .{ .value = value, .shape = shape };
}
