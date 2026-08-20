//! Single recursive traversal of a ZIR body tree, reporting nesting to a sink so a textual dump and a
//! structured view share one notion of the tree. `base_node` (passed to the sink) is the enclosing
//! declaration's AST node; a ZIR `src_node` is an `Ast.Node.Offset` relative to it, so a sink mapping
//! instructions to source resolves offsets against this base.

const std = @import("std");
const Ast = std.zig.Ast;
const Zir = std.zig.Zir;

pub fn Walker(comptime Sink: type) type {
    return struct {
        zir: Zir,
        sink: *Sink,

        const Self = @This();

        pub fn run(self: *Self) anyerror!void {
            if (self.zir.instructions.len == 0) return;
            for (self.zir.typeDecls(.main_struct_inst)) |decl_inst| {
                try self.declaration(decl_inst);
            }
        }

        fn declaration(self: *Self, decl_inst: Zir.Inst.Index) anyerror!void {
            const decl = self.zir.getDeclaration(decl_inst);
            const base = self.zir.instructions.items(.data)[@backingInt(decl_inst)].declaration.src_node;
            try self.sink.openDeclaration(decl_inst, base);
            if (decl.type_body) |b| try self.section("type_body", b, base);
            if (decl.align_body) |b| try self.section("align_body", b, base);
            if (decl.linksection_body) |b| try self.section("linksection_body", b, base);
            if (decl.addrspace_body) |b| try self.section("addrspace_body", b, base);
            if (decl.value_body) |b| try self.section("value_body", b, base);
            try self.sink.closeDeclaration();
        }

        fn section(self: *Self, label: []const u8, slice: []const Zir.Inst.Index, base: Ast.Node.Index) anyerror!void {
            if (slice.len == 0) return;
            try self.sink.openSection(label);
            for (slice) |inst| try self.instruction(inst, base);
            try self.sink.closeSection();
        }

        fn instruction(self: *Self, inst: Zir.Inst.Index, base: Ast.Node.Index) anyerror!void {
            const idx = @backingInt(inst);
            const tag = self.zir.instructions.items(.tag)[idx];
            const data = self.zir.instructions.items(.data)[idx];
            try self.sink.openInstruction(inst, tag, data, base);
            try self.recurseBodies(inst, tag, data, base);
            try self.sink.closeInstruction();
        }

        fn recurseBodies(
            self: *Self,
            inst: Zir.Inst.Index,
            tag: Zir.Inst.Tag,
            data: Zir.Inst.Data,
            base: Ast.Node.Index,
        ) anyerror!void {
            switch (tag) {
                .block, .block_inline, .loop, .suspend_block => {
                    const e = self.zir.extraData(Zir.Inst.Block, data.pl_node.payload_index);
                    try self.section("body", self.zir.bodySlice(e.end, e.data.body_len), base);
                },
                .block_comptime => {
                    const e = self.zir.extraData(Zir.Inst.BlockComptime, data.pl_node.payload_index);
                    try self.section("body", self.zir.bodySlice(e.end, e.data.body_len), base);
                },
                .condbr, .condbr_inline => {
                    const e = self.zir.extraData(Zir.Inst.CondBr, data.pl_node.payload_index);
                    const then_body = self.zir.bodySlice(e.end, e.data.then_body_len);
                    const else_body = self.zir.bodySlice(e.end + e.data.then_body_len, e.data.else_body_len);
                    try self.section("then", then_body, base);
                    try self.section("else", else_body, base);
                },
                .@"try", .try_ptr => {
                    const e = self.zir.extraData(Zir.Inst.Try, data.pl_node.payload_index);
                    try self.section("body", self.zir.bodySlice(e.end, e.data.body_len), base);
                },
                .bool_br_and, .bool_br_or => {
                    const e = self.zir.extraData(Zir.Inst.BoolBr, data.pl_node.payload_index);
                    try self.section("rhs", self.zir.bodySlice(e.end, e.data.body_len), base);
                },
                .@"defer" => {
                    try self.section("body", self.zir.bodySlice(data.@"defer".index, data.@"defer".len), base);
                },
                .func, .func_inferred, .func_fancy => {
                    // `info.param_body` is the enclosing block containing this func instruction;
                    // recursing into it re-walks `inst` and loops. `ret_ty_body` + `body` are
                    // self-contained, so show only those.
                    const info = self.zir.getFnInfo(inst);
                    try self.section("ret_ty_body", info.ret_ty_body, base);
                    try self.section("body", info.body, base);
                },
                else => {},
            }
        }
    };
}

/// Walk every top-level declaration in `zir`, reporting its structure to `sink`.
pub fn walk(comptime Sink: type, zir: Zir, sink: *Sink) anyerror!void {
    var w = Walker(Sink){ .zir = zir, .sink = sink };
    try w.run();
}

/// Walk a single declaration, for callers wanting only one of several (e.g. dropping an injected prelude).
pub fn walkDecl(comptime Sink: type, zir: Zir, decl_inst: Zir.Inst.Index, sink: *Sink) anyerror!void {
    var w = Walker(Sink){ .zir = zir, .sink = sink };
    try w.declaration(decl_inst);
}
