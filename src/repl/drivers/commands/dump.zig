//! `:dump <expr>` -- AST + tree-walked ZIR listing.

const std = @import("std");
const assert = std.debug.assert;

const Session = @import("../../Session.zig");
const Command = @import("Command.zig").Command;
const Pipeline = @import("../../front/Pipeline.zig");
const InputShape = @import("../../front/InputShape.zig");
const Diagnostic = @import("../../render/Diagnostic.zig");
const ZirWalk = @import("../../front/ZirWalk.zig");
const ZirSummary = @import("../../render/ZirSummary.zig");

const Ast = std.zig.Ast;
const Zir = std.zig.Zir;

pub fn command(comptime Ctx: type) Command(Ctx) {
    return .{
        .name = "dump",
        .summary = "Dump AST + ZIR for an expression: :dump <expr>",
        .run = struct {
            fn run(ctx: Ctx, _: []const Command(Ctx), argument: []const u8, stdout: *std.Io.Writer) anyerror!void {
                // The wasm frontend passes the session directly; the TTY
                // frontend passes its `*Repl`, which holds one.
                const session: *Session = if (Ctx == *Session) ctx else ctx.session;
                assert(@intFromPtr(session) != 0);
                assert(@intFromPtr(stdout) != 0);

                const trimmed = std.mem.trim(u8, argument, " \t");
                if (trimmed.len == 0) {
                    try stdout.writeAll("usage: :dump <expression>\n");
                    return;
                }

                // Route through the same splitter the evaluator uses so
                // `:dump` of a mixed input (declarations + a trailing
                // expression) shows what the REPL would actually run -- two
                // passes -- rather than wrapping it as one file and reporting
                // the spurious "file cannot be a tuple". Each segment is dumped
                // on its own; the expression segment is shown in isolation (the
                // declarations are not persisted by `:dump`).
                if (try InputShape.splitTrailingExpr(session.gpa, trimmed)) |split| {
                    try stdout.writeAll("=== declarations ===\n");
                    try dumpInput(session, split.decls, stdout);
                    try stdout.writeAll("\n=== trailing expression ===\n");
                    try dumpInput(session, split.expr, stdout);
                    return;
                }
                try dumpInput(session, trimmed, stdout);
            }
        }.run,
    };
}

/// Dump one input unit (no trailing-expression split): wrapped source,
/// AST, then ZIR -- or the parse/ZIR diagnostics if the front end failed.
fn dumpInput(session: *Session, input: []const u8, stdout: *std.Io.Writer) !void {
    var result = Pipeline.runWithInjection(
        session.gpa,
        input,
        session.intern_pool,
        .init(session.root_namespace),
    ) catch |err| {
        try stdout.print("front-end failed: {s}\n", .{@errorName(err)});
        return;
    };
    defer result.deinit(session.gpa);

    try dumpSource(result, stdout);
    if (result.hasParseErrors()) {
        try Diagnostic.renderParseErrors(result.tree, result.userView(), stdout);
        return;
    }
    try dumpAst(result.tree, stdout);
    // A failed AstGen emits error-ZIR with no instructions; walking it
    // (typeDecls reads the root container at index 0) would panic. Mirror
    // the eval path and surface the compile errors instead.
    if (result.hasZirErrors()) {
        return Diagnostic.renderZirErrors(
            session.gpa,
            result.zir,
            result.tree,
            result.userView(),
            stdout,
        );
    }
    try dumpZir(result.zir, stdout);
}

fn dumpSource(result: Pipeline.Result, stdout: *std.Io.Writer) !void {
    try stdout.print("source (wrapped, {d} bytes):\n  ", .{result.wrapped.text.len});
    try stdout.writeAll(result.wrapped.text);
}

fn dumpAst(tree: Ast, stdout: *std.Io.Writer) !void {
    const root_decls = tree.rootDecls();
    try stdout.print("\nast (root_decls: {d}):\n", .{root_decls.len});
    for (root_decls, 0..) |node, i| {
        const tag = tree.nodeTag(node);
        var idx_buf: [16]u8 = undefined;
        const idx_str = std.fmt.bufPrint(&idx_buf, "[{d}]", .{i}) catch unreachable;
        if (astDeclName(tree, node, tag)) |n| {
            try stdout.print("  {s:<5}{s:<22} {s}\n", .{ idx_str, @tagName(tag), n });
        } else {
            try stdout.print("  {s:<5}{s}\n", .{ idx_str, @tagName(tag) });
        }
    }
}

/// Identifier carried by a top-level decl AST node, when the tag's
/// grammar specifies one. Returns null for decls without a
/// user-visible name (test, comptime block).
fn astDeclName(tree: Ast, node: Ast.Node.Index, tag: Ast.Node.Tag) ?[]const u8 {
    return switch (tag) {
        .simple_var_decl,
        .global_var_decl,
        .local_var_decl,
        .aligned_var_decl,
        => name: {
            const main_token = tree.nodeMainToken(node);
            break :name tree.tokenSlice(main_token + 1);
        },
        else => null,
    };
}

fn dumpZir(zir: Zir, stdout: *std.Io.Writer) !void {
    try stdout.print("\nzir ({d} instructions, {d} extra words, {d} string bytes):\n", .{
        zir.instructions.len,
        zir.extra.len,
        zir.string_bytes.len,
    });

    // A failed AstGen produces error-ZIR with no instructions, so the
    // root container `typeDecls` reads at index 0 is absent and the walk
    // would index out of bounds. Compile errors can be present yet
    // suppressed (so the caller's `hasZirErrors` gate lets them through,
    // matching `Sema.analyze`), so guard on the instruction list rather
    // than the error flag -- a user typo must surface as the rendered
    // diagnostic, never a panic.
    if (zir.instructions.len == 0) return;

    var sink: TextSink = .{ .zir = zir, .stdout = stdout };
    try ZirWalk.walk(TextSink, zir, &sink);
}

const idx_col_width: u32 = 7;
const summary_col: u32 = 40;
const indent_step: u32 = 4;

/// `ZirWalk` sink that renders the indented `%N tag  <summary>` listing,
/// with `decl`/section headers above the bodies they introduce.
const TextSink = struct {
    zir: Zir,
    stdout: *std.Io.Writer,
    indent: u32 = 0,

    pub fn openDeclaration(self: *TextSink, decl_inst: Zir.Inst.Index, base: Ast.Node.Index) !void {
        _ = base;
        try self.stdout.splatByteAll(' ', idx_col_width + self.indent);
        const u = self.zir.getDeclaration(decl_inst);
        const name = if (u.name == .empty)
            "<unnamed>"
        else
            self.zir.nullTerminatedString(u.name);
        try self.stdout.print(
            "decl %{d} {s}  kind={s}  linkage={s}  pub={}\n",
            .{ @intFromEnum(decl_inst), name, @tagName(u.kind), @tagName(u.linkage), u.is_pub },
        );
        self.indent += indent_step;
    }

    pub fn closeDeclaration(self: *TextSink) !void {
        self.indent -= indent_step;
    }

    pub fn openSection(self: *TextSink, label: []const u8) !void {
        try self.stdout.splatByteAll(' ', idx_col_width + self.indent);
        try self.stdout.print("{s}:\n", .{label});
        self.indent += indent_step;
    }

    pub fn closeSection(self: *TextSink) !void {
        self.indent -= indent_step;
    }

    pub fn openInstruction(
        self: *TextSink,
        inst: Zir.Inst.Index,
        tag: Zir.Inst.Tag,
        data: Zir.Inst.Data,
        base: Ast.Node.Index,
    ) !void {
        _ = base;
        const idx: u32 = @intFromEnum(inst);
        var idx_buf: [16]u8 = undefined;
        const idx_str = std.fmt.bufPrint(&idx_buf, "%{d}", .{idx}) catch unreachable;
        try self.stdout.writeAll(idx_str);
        try self.stdout.splatByteAll(' ', idx_col_width - @as(u32, @intCast(idx_str.len)));
        try self.stdout.splatByteAll(' ', self.indent);
        const tag_name = @tagName(tag);
        try self.stdout.writeAll(tag_name);
        const written: u32 = idx_col_width + self.indent + @as(u32, @intCast(tag_name.len));
        if (written < summary_col) {
            try self.stdout.splatByteAll(' ', summary_col - written);
        } else {
            try self.stdout.writeByte(' ');
        }
        try ZirSummary.write(self.zir, tag, data, self.stdout);
        try self.stdout.writeAll("\n");
    }

    pub fn closeInstruction(self: *TextSink) !void {
        _ = self;
    }
};

test "zir listing nests a declaration's instructions under its body" {
    const testing = std.testing;
    const InternPool = @import("../../sema/InternPool.zig");

    const gpa = testing.allocator;
    var pool = try InternPool.init(gpa);
    defer pool.deinit();
    const ns = try pool.createNamespace(gpa, .none);
    var session = Session.init(gpa, &pool, ns);
    defer session.deinit();

    var out: std.Io.Writer.Allocating = .init(gpa);
    defer out.deinit();
    try dumpInput(&session, "1 + 2", &out.writer);

    // The walker drives the sink as declaration -> section -> instruction, so
    // the `value_body` header precedes the arithmetic lowered beneath it.
    const text = out.written();
    const body_at = std.mem.indexOf(u8, text, "value_body:") orelse return error.MissingBody;
    const add_at = std.mem.indexOf(u8, text, "add") orelse return error.MissingAdd;
    try testing.expect(add_at > body_at);
    try testing.expect(std.mem.indexOf(u8, text, "break_inline") != null);
}
