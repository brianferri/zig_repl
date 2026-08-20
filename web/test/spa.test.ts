import assert from "node:assert/strict";

import { after, before, describe, test } from "node:test";

import { chromium } from "playwright";

import type { Browser, Page } from "playwright";

const BASE = process.env.BASE_URL ?? "http://localhost:3000";

interface AstNode {
    id: number;
    label: string;
    lo: number;
    hi: number;
    children: Array<AstNode>;
}

interface ZirNode {
    label: string;
    detail?: string;
    node?: number;
    children: Array<ZirNode>;
}

interface Outline {
    source: string;
    ast: Array<AstNode>;
    zir: Array<ZirNode>;
}

declare global {
    interface Window {
        repl: {
            evalLine: (line: string) => string,
            preview: (line: string) => string,
            outline: (line: string) => Outline,
            feed: (bytes: Uint8Array) => void,
            inputState: () => { buffer: string, cursor: number },
            takeSubmitted: () => string | null,
            themes: () => Array<{
                name: string,
                accent: { r: number, g: number, b: number },
                palette: Record<string, { r: number, g: number, b: number }>
            }>,
            fs: {
                list: () => Array<{ path: string, kind: "file" | "directory" }>,
                read: (path: string) => string,
                write: (path: string, data: string) => void,
                mkdir: (path: string) => void,
                remove: (path: string) => void,
                rename: (from: string, to: string) => void
            },
            run: (path: string) => string
        };
    }
}

function flattenZir(nodes: Array<ZirNode>): Array<ZirNode> {
    const out: Array<ZirNode> = [];
    for (const node of nodes) {
        out.push(node);
        out.push(...flattenZir(node.children));
    }
    return out;
}

await describe("wasm repl", async () => {
    let browser: Browser;
    let page: Page;
    const errors: Array<string> = [];

    before(async () => {
        browser = await chromium.launch();
        page = await browser.newPage();
        page.on("pageerror", (error) => errors.push(String(error)));
        page.on("console", (message) => {
            if (message.type() === "error")
                errors.push(message.text());
        });
        await page.goto(BASE, { waitUntil: "load" });
        await page.waitForSelector("body[data-ready]", { timeout: 15000 });
    });

    after(async () => {
        await browser.close();
    });

    await test("evaluates an expression to its value", async () => {
        const out = await page.evaluate(() => window.repl.evalLine("1 + 2"));
        assert.match(out, /\b3\b/);
    });

    await test("persists session bindings across evaluations", async () => {
        const first = await page.evaluate(() => window.repl.evalLine("const x = 40; x + 2"));
        assert.match(first, /\b42\b/);
        const second = await page.evaluate(() => window.repl.evalLine("x * 2"));
        assert.match(second, /\b80\b/);
    });

    await test("emits evaluated std.debug.print output inline", async () => {
        const out = await page.evaluate(() => window.repl.evalLine("@import(\"std\").debug.print(\"Hi {d}!\\n\", .{42})"));
        assert.match(out, /Hi 42!/);
    });

    await test("the shared line editor drives typing, editing, submit, and history from key bytes", async () => {
        const r = await page.evaluate(() => {
            const te = new TextEncoder();
            const R = window.repl;
            R.feed(te.encode("1 + 2"));
            const typed = R.inputState();
            R.feed(te.encode("\x7f")); // Backspace -> "1 + "
            R.feed(te.encode("3")); // -> "1 + 3"
            const { buffer: edited } = R.inputState();
            R.feed(te.encode("\x1b[D\x1b[D")); // Left twice -> cursor 3
            const { cursor } = R.inputState();
            R.feed(te.encode("\x1b[F")); // End -> cursor 5
            const { cursor: atEnd } = R.inputState();
            R.feed(te.encode("\r")); // submit "1 + 3"
            const submitted = R.takeSubmitted();
            R.feed(te.encode("\x1b[A")); // Up recalls the submitted line
            const { buffer: recalled } = R.inputState();
            return { typed, edited, cursor, atEnd, submitted, recalled };
        });
        assert.equal(r.typed.buffer, "1 + 2");
        assert.equal(r.typed.cursor, 5);
        assert.equal(r.edited, "1 + 3");
        assert.equal(r.cursor, 3);
        assert.equal(r.atEnd, 5);
        assert.equal(r.submitted, "1 + 3");
        assert.equal(r.recalled, "1 + 3");
    });

    await test("recognises :clear and reports unknown commands", async () => {
        assert.equal((await page.evaluate(() => window.repl.evalLine(":clear"))).trim(), "");
        assert.match(await page.evaluate(() => window.repl.evalLine(":help")), /:clear/);
        assert.match(await page.evaluate(() => window.repl.evalLine(":bogus")), /unknown command: :bogus/);
    });

    await test("previews value and type without touching session state", async () => {
        const out = await page.evaluate(() => window.repl.preview("40 * 3 - 1"));
        assert.match(out, /\b119\b/);
        assert.match(out, /comptime_int/);
    });

    await test("outlines the ast as a tree and binds zir instructions to it by id", async () => {
        const out = await page.evaluate(() => window.repl.outline("40 * 3 - 1"));
        assert.equal(out.source, "40 * 3 - 1");

        // the syntax tree roots at `sub`, with `mul` and the `1` literal as its
        // children -- `1` belongs to the subtraction, not the multiplication
        const [root] = out.ast;
        assert.equal(root.label, "sub");
        assert.equal(out.source.slice(root.lo, root.hi), "40 * 3 - 1");
        const mul = root.children.find((node) => node.label === "mul");
        assert.ok(mul);
        assert.equal(out.source.slice(mul.lo, mul.hi), "40 * 3");
        assert.equal(mul.children.length, 2);
        assert.ok(root.children.some((node) => node.label === "number_literal"));

        // the zir comes back as a tree too; its arithmetic points back to those
        // ast nodes by id, not by overlapping spans
        assert.ok(out.zir[0].children.length);
        const zir = flattenZir(out.zir);
        const zmul = zir.find((node) => node.label === "mul");
        assert.ok(zmul);
        assert.equal(zmul.node, mul.id);
        assert.match(zmul.detail ?? "", /lhs=/);
        assert.equal(zir.find((node) => node.label === "sub")?.node, root.id);
    });

    await test("outlines a bare declaration and its zir directly (no expression wrapper)", async () => {
        const out = await page.evaluate(() => window.repl.outline("const x = 40;"));
        assert.equal(out.ast[0].label, "simple_var_decl");
        assert.ok(flattenZir(out.zir).some((node) => node.label === "int"));
    });

    await test("outlines a function definition and walks its body zir", async () => {
        const out = await page.evaluate(() => window.repl.outline("fn f(a: u32) u32 { return a + 1; }"));
        assert.equal(out.ast[0].label, "fn_decl");
        const zir = flattenZir(out.zir);
        assert.ok(zir.some((node) => node.label === "func"));
        assert.ok(zir.some((node) => node.label === "add"));
    });

    await test("outlines declarations then a trailing expression as one merged view", async () => {
        const out = await page.evaluate(() => window.repl.outline("const y = 7;\ny * 2"));
        assert.deepEqual(out.ast.map((node) => node.label), ["simple_var_decl", "mul"]);
        const zir = flattenZir(out.zir);
        assert.ok(zir.some((node) => node.label === "int")); // the 7 binding
        assert.ok(zir.some((node) => node.label === "mul")); // y * 2
    });

    await test("exposes the prompt theme registry with accent and surface palette", async () => {
        const list = await page.evaluate(() => window.repl.themes());
        assert.ok(list.length >= 1);
        const zig = list.find((t) => t.name === "zig");
        assert.ok(zig);
        assert.deepEqual(zig.accent, { r: 247, g: 164, b: 29 });
        assert.deepEqual(zig.palette.base, { r: 27, g: 26, b: 23 });
        assert.deepEqual(zig.palette.text, { r: 234, g: 230, b: 223 });
    });

    await test("applies a chosen theme's palette to the css variables and remembers it", async () => {
        const applied = await page.evaluate(() => {
            const select = document.getElementById("theme-select") as HTMLSelectElement;
            select.value = "zig";
            select.dispatchEvent(new Event("change"));
            const style = getComputedStyle(document.documentElement);
            return {
                accent: style.getPropertyValue("--accent").trim(),
                base: style.getPropertyValue("--base").trim(),
                stored: localStorage.getItem("zig_repl_theme")
            };
        });
        assert.equal(applied.accent, "rgb(247 164 29)");
        assert.equal(applied.base, "rgb(27 26 23)");
        assert.equal(applied.stored, "zig");
    });

    await test("rejects an over-long paste without trapping the module", async () => {
        const result = await page.evaluate(() => {
            const huge = "1".repeat(20000); // past the 16 KiB interpreter cap
            const rejected = window.repl.evalLine(huge);
            const stillAlive = window.repl.evalLine("1 + 2"); // module survives for the next line
            return { rejected, stillAlive };
        });
        assert.match(result.rejected, /too long/);
        assert.match(result.stillAlive, /\b3\b/);
    });

    await test("edits and runs a multi-file program from the virtual filesystem", async () => {
        const result = await page.evaluate(() => {
            const R = window.repl;
            R.fs.write("util.zig", "pub fn greet() u32 { return 42; }");
            R.fs.write("main.zig", "const util = @import(\"util.zig\");\npub fn main() void { @import(\"std\").debug.print(\"got {d}\\n\", .{util.greet()}); }");
            const files = R.fs.list().map((e) => e.path).sort();
            const output = R.run("main.zig");
            R.fs.remove("util.zig");
            return { files, output, afterRemove: R.fs.list().map((e) => e.path) };
        });
        assert.deepEqual(result.files, ["main.zig", "util.zig"]);
        assert.match(result.output, /got 42/);
        assert.deepEqual(result.afterRemove, ["main.zig"]);
    });

    await test("resolves @import across subdirectories in the virtual filesystem", async () => {
        const output = await page.evaluate(() => {
            const R = window.repl;
            R.fs.write("lib/math.zig", "pub fn square(x: u32) u32 { return x * x; }");
            R.fs.write("app.zig", "const math = @import(\"lib/math.zig\");\npub fn main() void { @import(\"std\").debug.print(\"sq {d}\\n\", .{math.square(7)}); }");
            const out = R.run("app.zig");
            R.fs.remove("lib/math.zig");
            R.fs.remove("app.zig");
            return out;
        });
        assert.match(output, /sq 49/);
    });

    await test("resolves relative @import against the importing file's directory", async () => {
        const output = await page.evaluate(() => {
            const R = window.repl;
            R.fs.write("top.zig", "pub const w = 10;");
            R.fs.write("lib/b.zig", "pub const v = 5;");
            R.fs.write("lib/a.zig", "const b = @import(\"b.zig\");\nconst top = @import(\"../top.zig\");\npub fn main() void { @import(\"std\").debug.print(\"sum {d}\\n\", .{b.v + top.w}); }");
            const out = R.run("lib/a.zig");
            for (const f of ["top.zig", "lib/b.zig", "lib/a.zig"]) R.fs.remove(f);
            return out;
        });
        assert.match(output, /sum 15/);
    });

    await test("writes and reads an empty file without a memory error", async () => {
        const result = await page.evaluate(() => {
            window.repl.fs.write("empty.zig", "");
            const empty = window.repl.fs.read("empty.zig");
            window.repl.fs.write("empty.zig", "pub const x = 1;");
            const filled = window.repl.fs.read("empty.zig");
            window.repl.fs.remove("empty.zig");
            return { empty, filled };
        });
        assert.equal(result.empty, "");
        assert.equal(result.filled, "pub const x = 1;");
    });

    await test("tracks an empty directory and moves or drops a whole subtree", async () => {
        const result = await page.evaluate(() => {
            const R = window.repl;
            R.fs.mkdir("gamma");
            const madeEmpty = R.fs.list().find((e) => e.path === "gamma");
            R.fs.write("alpha/a.zig", "pub const a = 1;");
            R.fs.write("alpha/nested/b.zig", "pub const b = 2;");
            R.fs.rename("alpha", "beta");
            const movedFile = R.fs.read("beta/nested/b.zig");
            const alphaGone = R.fs.list().every((e) => !e.path.startsWith("alpha"));
            R.fs.remove("beta");
            const betaGone = R.fs.list().every((e) => !e.path.startsWith("beta"));
            R.fs.remove("gamma");
            return { kind: madeEmpty?.kind, movedFile, alphaGone, betaGone };
        });
        assert.equal(result.kind, "directory");
        assert.match(result.movedFile, /pub const b = 2;/);
        assert.ok(result.alphaGone);
        assert.ok(result.betaGone);
    });

    await test("loads without page errors", () => {
        assert.deepEqual(errors, []);
    });
});
