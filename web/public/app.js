import { loadRepl } from "./wasm.js";

/** @typedef {import("./wasm.js").AstNode} AstNode */
/** @typedef {import("./wasm.js").ZirNode} ZirNode */

const replOutput = /** @type {HTMLElement} */ (document.getElementById("repl-output"));
const replInput = /** @type {HTMLTextAreaElement} */ (document.getElementById("repl-input"));

const editor = /** @type {HTMLTextAreaElement} */ (document.getElementById("editor"));
const outResult = /** @type {HTMLElement} */ (document.getElementById("out-result"));
const outAst = /** @type {HTMLElement} */ (document.getElementById("out-ast"));
const outZir = /** @type {HTMLElement} */ (document.getElementById("out-zir"));

// One wasm instance backs both tabs: the REPL persists its session
// (replEval); the explorer uses throwaway sessions (replPreview / replOutline)
// so exploring never disturbs REPL state.
const {
    evalLine,
    preview,
    outline,
    feed,
    inputState,
    takeSubmitted,
    themes,
    fs,
    run
} = await loadRepl({
    replClearOutput() {
        replOutput.textContent = "";
    },
});

// Expose the interpreter binding for the console and the test harness.
window.repl = {
    evalLine,
    preview,
    outline,
    feed,
    inputState,
    takeSubmitted,
    themes,
    fs,
    run
};

// Palette role names map 1:1 to the `--<role>` variables in style.css;
// `--accent-dim` is a darkened accent for hover/active states.
const themeSelect = /** @type {HTMLSelectElement} */ (document.getElementById("theme-select"));
const themeList = themes();

/** @param {{ r: number, g: number, b: number }} rgb @param {number} scale @returns {string} */
function rgbCss(rgb, scale) {
    return `rgb(${Math.round(rgb.r * scale)} ${Math.round(rgb.g * scale)} ${Math.round(rgb.b * scale)})`;
}

/** @param {string} name */
function applyTheme(name) {
    const theme = themeList.find((t) => t.name === name) ?? themeList[0];
    if (theme === undefined) return;
    const root = document.documentElement.style;
    for (const [role, rgb] of Object.entries(theme.palette))
        root.setProperty(`--${role}`, rgbCss(rgb, 1));
    root.setProperty("--accent", rgbCss(theme.accent, 1));
    root.setProperty("--accent-dim", rgbCss(theme.accent, 0.85));
    themeSelect.value = theme.name;
    try {
        localStorage.setItem("zig_repl_theme", theme.name);
    } catch {
        // Storage disabled (private mode): the choice holds for the session.
    }
}

for (const theme of themeList) {
    const option = document.createElement("option");
    option.value = theme.name;
    option.textContent = theme.name;
    themeSelect.appendChild(option);
}
themeSelect.addEventListener("change", () => applyTheme(themeSelect.value));
applyTheme(localStorage.getItem("zig_repl_theme") ?? "");

const tabs = /** @type {NodeListOf<HTMLElement>} */ (document.querySelectorAll("nav button"));
tabs.forEach((btn) => {
    btn.addEventListener("click", () => {
        tabs.forEach((b) => b.classList.toggle("active", b === btn));
        for (const view of /** @type {NodeListOf<HTMLElement>} */ (document.querySelectorAll(".view"))) {
            view.hidden = view.id !== btn.dataset.view;
        }
        (btn.dataset.view === "explorer-view" ? editor : replInput).focus();
    });
});

/**
 * @param {HTMLElement} gutter
 * @param {(dx: number, dy: number) => void} onDrag cumulative move since the last step.
 */
function draggable(gutter, onDrag) {
    gutter.addEventListener("pointerdown", (down) => {
        down.preventDefault();
        gutter.setPointerCapture(down.pointerId);
        let px = down.clientX;
        let py = down.clientY;
        /** @param {PointerEvent} move */
        const onMove = (move) => {
            onDrag(move.clientX - px, move.clientY - py);
            px = move.clientX;
            py = move.clientY;
        };
        const onUp = () => {
            gutter.removeEventListener("pointermove", onMove);
            gutter.removeEventListener("pointerup", onUp);
            gutter.removeEventListener("pointercancel", onUp);
        };
        gutter.addEventListener("pointermove", onMove);
        gutter.addEventListener("pointerup", onUp);
        // A cancelled gesture (touch interrupted, OS takeover) ends the drag
        // too; without this the move listener would leak and keep resizing.
        gutter.addEventListener("pointercancel", onUp);
    });
}

for (const gutter of document.querySelectorAll(".gutter-col")) {
    const pane = /** @type {HTMLElement} */ (gutter.previousElementSibling);
    const view = /** @type {HTMLElement} */ (gutter.closest(".view"));
    draggable(/** @type {HTMLElement} */ (gutter), (dx) => {
        const width = Math.max(0, Math.min(pane.offsetWidth + dx, view.clientWidth - 320));
        pane.style.flex = `0 0 ${width}px`;
    });
}

// Each section's labelled header drags the boundary above it, resizing the
// preceding section (the first section has nothing above it, so it is skipped).
for (const pane of document.querySelectorAll("#panels .pane")) {
    const above = pane.previousElementSibling;
    if (!(above instanceof HTMLElement)) continue;
    const header = /** @type {HTMLElement} */ (pane.querySelector("h2"));
    draggable(header, (_dx, dy) => {
        above.style.flex = `0 0 ${Math.max(above.offsetHeight + dy, 40)}px`;
    });
}

/** @param {string} text */
function appendEcho(text) {
    const span = document.createElement("span");
    span.className = "echo";
    span.textContent = text;
    replOutput.appendChild(span);
    replOutput.scrollTop = replOutput.scrollHeight;
}

/** @param {string} text */
function appendOutput(text) {
    replOutput.appendChild(document.createTextNode(text));
    replOutput.scrollTop = replOutput.scrollHeight;
}

appendOutput("zig_repl (wasm). try `1 + 2`, `const x = 40; x + 2`, `:help`, `:clear`.\n");

function fitInput() {
    replInput.style.height = "auto";
    replInput.style.height = `${replInput.scrollHeight}px`;
}

// The textarea is display-only: the shared Zig line editor owns the buffer,
// cursor, and history. Keystrokes are translated to the terminal byte sequences
// it parses and fed in; its state is mirrored back into the textarea.
const encoder = new TextEncoder();
const keySequences = {
    Enter: "\r",
    Backspace: "\x7f",
    Delete: "\x1b[3~",
    ArrowUp: "\x1b[A",
    ArrowDown: "\x1b[B",
    ArrowRight: "\x1b[C",
    ArrowLeft: "\x1b[D",
    Home: "\x1b[H",
    End: "\x1b[F",
    Tab: "\t",
};

/** @param {KeyboardEvent} event @returns {Uint8Array | null} */
function keyToBytes(event) {
    const seq = /** @type {Record<string, string>} */ (keySequences)[event.key];
    if (seq !== undefined) return encoder.encode(seq);
    if (event.ctrlKey && event.key.length === 1) {
        const c = event.key.toLowerCase().charCodeAt(0);
        if (c >= 97 && c <= 122) return Uint8Array.of(c - 96); // Ctrl+A..Z -> 0x01..0x1a
    }
    if (event.key.length === 1 && !event.ctrlKey && !event.metaKey) return encoder.encode(event.key);
    return null;
}

function renderInput() {
    const state = inputState();
    replInput.value = state.buffer;
    replInput.selectionStart = replInput.selectionEnd = state.cursor;
    fitInput();
}

replInput.addEventListener("keydown", (event) => {
    const bytes = keyToBytes(event);
    if (bytes === null) return;
    event.preventDefault();
    feed(bytes);
    const line = takeSubmitted();
    if (line !== null && line.trim().length !== 0) {
        appendEcho(">>> " + line + "\n");
        appendOutput(evalLine(line));
    }
    renderInput();
});

replInput.addEventListener("paste", (event) => {
    event.preventDefault();
    const text = event.clipboardData?.getData("text") ?? "";
    if (text.length === 0) return;
    feed(encoder.encode(text));
    renderInput();
});

renderInput();

// Hover binds the three views by AST node identity: an ast node carries its
// node id, a zir instruction carries the id it lowered from, and both map to
// the source span the editor selects. Keying on one id is exact, where matching
// by overlapping spans was a guess. `spans` maps each id to its source range.

/** @type {Map<number, { lo: number, hi: number }>} */
const spans = new Map();

function clearHighlight() {
    // Scope to nodes: a bare `.active` would also strip the nav tab's state.
    for (const el of document.querySelectorAll(".node.active, .node.linked")) {
        el.classList.remove("active", "linked");
    }
}

/**
 * Highlight the ast and zir for `id`; `active` (the originating element, if any)
 * is marked active, the rest linked.
 * @param {number} id
 * @param {Element | null} active
 */
function setHighlight(id, active) {
    clearHighlight();
    for (const el of document.querySelectorAll(`[data-id="${id}"], [data-node="${id}"]`)) {
        el.classList.add(el === active ? "active" : "linked");
    }
}

/**
 * Hovering a node: highlight the others and select the matching source.
 * @param {number} id
 * @param {Element} source
 */
function highlight(id, source) {
    setHighlight(id, source);
    const span = spans.get(id);
    // Selects the matching source in the editor. No focus change, so it doesn't
    // disturb a selection elsewhere on the page.
    if (span !== undefined) editor.setSelectionRange(span.lo, span.hi);
}

// Clicking in the editor highlights the deepest node whose source range holds
// the caret -- the source -> ast/zir direction. The caret stays where clicked
// (no selection change), so it composes with editing.
function highlightCaret() {
    const offset = editor.selectionStart;
    let best = -1;
    let width = Infinity;
    for (const [id, span] of spans) {
        if (span.lo <= offset && offset < span.hi && span.hi - span.lo < width) {
            best = id;
            width = span.hi - span.lo;
        }
    }
    if (best < 0) clearHighlight();
    else setHighlight(best, document.querySelector(`[data-id="${best}"]`));
}
editor.addEventListener("click", highlightCaret);

/**
 * The ast panel is the syntax tree: each node shows its tag and the source
 * fragment it spans, with children nested beneath it.
 * @param {HTMLElement} container
 * @param {Array<AstNode>} nodes
 * @param {string} source
 */
function renderAst(container, nodes, source) {
    container.replaceChildren();
    for (const node of nodes) container.appendChild(astNode(node, source));
}

/**
 * @param {AstNode} node
 * @param {string} source
 * @returns {HTMLElement}
 */
function astNode(node, source) {
    const el = document.createElement("div");
    el.className = "tree-node";
    const head = document.createElement("div");
    head.className = "node";
    head.dataset.id = String(node.id);
    const tag = document.createElement("span");
    tag.className = "tag";
    tag.textContent = node.label;
    const frag = document.createElement("code");
    frag.className = "frag";
    frag.textContent = source.slice(node.lo, node.hi);
    head.append(tag, frag);
    head.addEventListener("mouseenter", () => highlight(node.id, head));
    head.addEventListener("mouseleave", clearHighlight);
    el.appendChild(head);
    if (node.children.length > 0) {
        const kids = document.createElement("div");
        kids.className = "tree-children";
        for (const child of node.children) kids.appendChild(astNode(child, source));
        el.appendChild(kids);
    }
    return el;
}

/**
 * The zir panel is the instruction tree: section headers nest their bodies,
 * and an instruction that resolved an ast node binds to it on hover.
 * @param {HTMLElement} container
 * @param {Array<ZirNode>} nodes
 */
function renderZir(container, nodes) {
    container.replaceChildren();
    for (const node of nodes) container.appendChild(zirNode(node));
}

/**
 * @param {ZirNode} node
 * @returns {HTMLElement}
 */
function zirNode(node) {
    const el = document.createElement("div");
    el.className = "tree-node";
    const head = document.createElement("div");
    head.className = "node";
    const tag = document.createElement("span");
    tag.className = "tag";
    tag.textContent = node.label;
    head.appendChild(tag);
    if (node.detail !== undefined) {
        const detail = document.createElement("code");
        detail.className = "frag";
        detail.textContent = node.detail;
        head.appendChild(detail);
    }
    if (node.node !== undefined) {
        const id = node.node;
        head.dataset.node = String(id);
        head.addEventListener("mouseenter", () => highlight(id, head));
        head.addEventListener("mouseleave", clearHighlight);
    }
    el.appendChild(head);
    if (node.children.length > 0) {
        const kids = document.createElement("div");
        kids.className = "tree-children";
        for (const child of node.children) kids.appendChild(zirNode(child));
        el.appendChild(kids);
    }
    return el;
}

/** @type {number | undefined} */
let timer;
editor.addEventListener("input", () => {
    clearTimeout(timer);
    timer = setTimeout(renderExplorer, 150);
});

/**
 * Record each ast node's source range, shifted by `base` so the offsets address
 * `editor.value` (what `setSelectionRange` indexes) rather than the outline's own source.
 * @param {Array<AstNode>} nodes
 * @param {number} base
 */
function indexSpans(nodes, base) {
    for (const node of nodes) {
        spans.set(node.id, { lo: node.lo + base, hi: node.hi + base });
        indexSpans(node.children, base);
    }
}

function renderExplorer() {
    const value = editor.value;
    const src = value.trim();
    spans.clear();
    if (src.length === 0) {
        outResult.textContent = "—";
        outAst.replaceChildren();
        outZir.replaceChildren();
        return;
    }
    const data = outline(src);
    // The outline's `source` is the trimmed input; its offsets are relative to
    // that. Locate it in the raw editor value so selections account for any
    // leading whitespace the user typed.
    const base = Math.max(value.lastIndexOf(data.source), 0);
    indexSpans(data.ast, base);
    renderAst(outAst, data.ast, data.source);
    renderZir(outZir, data.zir);
    outResult.textContent = preview(src).trim() || "(no value)";
}

// Seed the editor so the explorer is populated on load (kept in JS, not as
// textarea markup, to leave the HTML cleanly indented). Mixes declarations, a
// function, and a trailing expression to exercise the multi-segment outline.
editor.value = `const x: u32 = 40;

fn add(a: u32, b: u32) u32 {
    return a + b;
}

const c = add(x, 2);

c`;
renderExplorer();

// Environment tab: a file tree, editor, and runner over the virtual filesystem,
// mirrored to OPFS when the browser grants it.
const envEditor = /** @type {HTMLTextAreaElement} */ (document.getElementById("env-editor"));
const fileTree = /** @type {HTMLElement} */ (document.getElementById("file-tree"));
const fileList = /** @type {HTMLElement} */ (document.getElementById("file-list"));
const envOutput = /** @type {HTMLElement} */ (document.getElementById("env-output"));
const envActive = /** @type {HTMLElement} */ (document.getElementById("env-active"));
const contextMenu = /** @type {HTMLElement} */ (document.getElementById("context-menu"));

/** @type {string | null} */
let activeFile = null;

/** @param {number} x @param {number} y @param {Array<{ label: string, action: () => void }>} items */
function showMenu(x, y, items) {
    contextMenu.replaceChildren();
    for (const { label, action } of items) {
        const button = document.createElement("button");
        button.textContent = label;
        button.addEventListener("click", () => {
            hideMenu();
            action();
        });
        contextMenu.appendChild(button);
    }
    contextMenu.style.left = `${x}px`;
    contextMenu.style.top = `${y}px`;
    contextMenu.hidden = false;
}

function hideMenu() {
    contextMenu.hidden = true;
}

document.addEventListener("click", hideMenu);
document.addEventListener("keydown", (event) => {
    if (event.key === "Escape") hideMenu();
});

fileTree.addEventListener("contextmenu", (event) => {
    event.preventDefault();
    showMenu(event.clientX, event.clientY, [
        { label: "New File", action: () => newFile("") },
        { label: "New Folder", action: () => newFolder("") },
    ]);
});

/**
 * @typedef {FileSystemDirectoryHandle & {
 *   entries(): AsyncIterableIterator<[string, FileSystemHandle]>
 * }} OpfsDir
 */

/** @returns {Promise<OpfsDir | null>} */
async function opfsDir() {
    try {
        return /** @type {OpfsDir} */ (await navigator.storage.getDirectory());
    } catch {
        return null;
    }
}

// The parent directory handle of a `/`-separated path, and the basename within
// it. Intermediate directories are created or navigated per `create`.
/** @param {OpfsDir} dir @param {string} path @param {boolean} create @returns {Promise<{ parent: OpfsDir, name: string } | null>} */
async function opfsParent(dir, path, create) {
    const parts = path.split("/");
    if (parts.some((segment) => segment.length === 0)) return null;
    let node = dir;
    for (const part of parts.slice(0, -1)) {
        try {
            node = /** @type {OpfsDir} */ (await node.getDirectoryHandle(part, { create }));
        } catch {
            return null;
        }
    }
    return { parent: node, name: parts[parts.length - 1] };
}

/** @param {OpfsDir} dir @param {string} prefix @param {Array<[string, FileSystemFileHandle]>} out @param {Array<string>} [dirsOut] */
async function opfsWalk(dir, prefix, out, dirsOut) {
    for await (const [name, handle] of dir.entries()) {
        const path = prefix ? `${prefix}/${name}` : name;
        if (handle.kind === "file") {
            out.push([path, /** @type {FileSystemFileHandle} */ (handle)]);
        } else {
            if (dirsOut !== undefined) dirsOut.push(path);
            await opfsWalk(/** @type {OpfsDir} */ (handle), path, out, dirsOut);
        }
    }
}

/** @param {OpfsDir} dir @param {string} path */
async function opfsMkdir(dir, path) {
    let node = dir;
    for (const part of path.split("/")) {
        node = /** @type {OpfsDir} */ (await node.getDirectoryHandle(part, { create: true }));
    }
}

// Every path prefix that must survive reconciliation: each file's ancestors plus
// the explicitly-created directories and their ancestors.
/** @param {Set<string>} names @param {Array<string>} explicitDirs @returns {Set<string>} */
function liveDirs(names, explicitDirs) {
    const live = new Set();
    /** @param {string} path */
    const ancestors = (path) => {
        const parts = path.split("/");
        for (let i = 1; i < parts.length; i += 1) live.add(parts.slice(0, i).join("/"));
    };
    for (const name of names) ancestors(name);
    for (const name of explicitDirs) {
        live.add(name);
        ancestors(name);
    }
    return live;
}

async function persist() {
    const dir = await opfsDir();
    if (dir === null) return;
    const entries = fs.list();
    const names = new Set(entries.filter((e) => e.kind === "file").map((e) => e.path));
    const explicitDirs = entries.filter((e) => e.kind === "directory").map((e) => e.path);
    for (const name of names) {
        const at = await opfsParent(dir, name, true);
        if (at === null) continue;
        const handle = await at.parent.getFileHandle(at.name, { create: true });
        const writable = await handle.createWritable();
        await writable.write(fs.read(name));
        await writable.close();
    }
    for (const name of explicitDirs) await opfsMkdir(dir, name);
    /** @type {Array<[string, FileSystemFileHandle]>} */
    const existing = [];
    /** @type {Array<string>} */
    const existingDirs = [];
    await opfsWalk(dir, "", existing, existingDirs);
    for (const [path] of existing) {
        if (names.has(path)) continue;
        const at = await opfsParent(dir, path, false);
        if (at !== null) await at.parent.removeEntry(at.name);
    }
    const live = liveDirs(names, explicitDirs);
    for (const path of existingDirs) {
        if (live.has(path)) continue;
        const at = await opfsParent(dir, path, false);
        if (at !== null) await at.parent.removeEntry(at.name, { recursive: true });
    }
}

/** @typedef {{ dirs: Map<string, TreeNode>, files: Array<string> }} TreeNode */

/** @param {TreeNode} root @param {Array<string>} segments @returns {TreeNode} */
function descend(root, segments) {
    let node = root;
    for (const segment of segments) {
        let child = node.dirs.get(segment);
        if (child === undefined) {
            child = { dirs: new Map(), files: [] };
            node.dirs.set(segment, child);
        }
        node = child;
    }
    return node;
}

/** @param {Array<import("./wasm.js").FsEntry>} entries @returns {TreeNode} */
function buildTree(entries) {
    /** @type {TreeNode} */
    const root = { dirs: new Map(), files: [] };
    for (const entry of entries) {
        const parts = entry.path.split("/");
        if (entry.kind === "directory") descend(root, parts);
        else descend(root, parts.slice(0, -1)).files.push(entry.path);
    }
    return root;
}

/** @type {Set<string>} */
const collapsed = new Set();

/** @param {TreeNode} node @param {string} prefix @param {HTMLElement} container */
function renderTree(node, prefix, container) {
    for (const name of [...node.dirs.keys()].sort()) {
        const path = prefix ? `${prefix}/${name}` : name;
        const li = document.createElement("li");
        li.className = "tree-dir";
        const details = document.createElement("details");
        details.open = !collapsed.has(path);
        details.addEventListener("toggle", () => {
            if (details.open) collapsed.delete(path);
            else collapsed.add(path);
        });
        const summary = document.createElement("summary");
        summary.className = "dir-name";
        summary.textContent = name;
        summary.addEventListener("contextmenu", (event) => {
            event.preventDefault();
            event.stopPropagation();
            showMenu(event.clientX, event.clientY, [
                { label: "New File", action: () => newFile(`${path}/`) },
                { label: "New Folder", action: () => newFolder(`${path}/`) },
                { label: "Rename", action: () => renameDir(path) },
                { label: "Delete", action: () => deleteDir(path) },
            ]);
        });
        const sub = document.createElement("ul");
        sub.className = "tree-sub";
        renderTree(/** @type {TreeNode} */ (node.dirs.get(name)), path, sub);
        details.append(summary, sub);
        li.appendChild(details);
        container.appendChild(li);
    }
    for (const path of [...node.files].sort()) {
        const li = document.createElement("li");
        li.className = "tree-file";
        li.classList.toggle("active", path === activeFile);
        li.textContent = /** @type {string} */ (path.split("/").pop());
        li.addEventListener("click", () => selectFile(path));
        li.addEventListener("contextmenu", (event) => {
            event.preventDefault();
            event.stopPropagation();
            showMenu(event.clientX, event.clientY, [
                { label: "Rename", action: () => renameFile(path) },
                { label: "Delete", action: () => deleteFile(path) },
            ]);
        });
        container.appendChild(li);
    }
}

function renderFileTree() {
    fileList.replaceChildren();
    renderTree(buildTree(fs.list()), "", fileList);
}

/** @param {string} path */
function selectFile(path) {
    activeFile = path;
    envEditor.value = fs.read(path);
    envActive.textContent = path;
    renderFileTree();
}

/** @param {string} path */
function renameFile(path) {
    const to = window.prompt("Rename to (a path moves it)", path);
    if (to === null) return;
    const clean = to.trim();
    if (!validPath(clean) || clean === path) return;
    fs.rename(path, clean);
    if (activeFile === path) selectFile(clean);
    else renderFileTree();
    void persist();
}

/** @param {string} path */
function deleteFile(path) {
    fs.remove(path);
    if (activeFile === path) {
        activeFile = null;
        envEditor.value = "";
        envActive.textContent = "";
    }
    renderFileTree();
    void persist();
}

// A file path is one or more non-empty, `/`-separated segments -- no leading or
// trailing slash, no empty segment (which would be a directory, not a file).
/** @param {string} path @returns {boolean} */
function validPath(path) {
    return path.length > 0 && !path.split("/").some((segment) => segment.length === 0);
}

/** @param {string} prefix */
function newFile(prefix) {
    const path = window.prompt("File path (use / for a directory)", `${prefix}new.zig`);
    if (path === null) return;
    const clean = path.trim();
    if (!validPath(clean)) return;
    fs.write(clean, "");
    selectFile(clean);
    void persist();
}

/** @param {string} prefix */
function newFolder(prefix) {
    const path = window.prompt("Folder path", `${prefix}new`);
    if (path === null) return;
    const clean = path.trim().replace(/\/+$/, "");
    if (!validPath(clean)) return;
    fs.mkdir(clean);
    collapsed.delete(clean);
    renderFileTree();
    void persist();
}

/** @param {string} path @param {string} dir @returns {boolean} */
function isUnder(path, dir) {
    return path === dir || path.startsWith(`${dir}/`);
}

/** @param {string} dir */
function renameDir(dir) {
    const to = window.prompt("Rename folder to", dir);
    if (to === null) return;
    const clean = to.trim().replace(/\/+$/, "");
    if (!validPath(clean) || clean === dir) return;
    fs.rename(dir, clean);
    if (activeFile !== null && isUnder(activeFile, dir)) {
        activeFile = clean + activeFile.slice(dir.length);
        envActive.textContent = activeFile;
    }
    renderFileTree();
    void persist();
}

/** @param {string} dir */
function deleteDir(dir) {
    fs.remove(dir);
    if (activeFile !== null && isUnder(activeFile, dir)) {
        activeFile = null;
        envEditor.value = "";
        envActive.textContent = "";
    }
    renderFileTree();
    void persist();
}

envEditor.addEventListener("input", () => {
    if (activeFile === null) return;
    fs.write(activeFile, envEditor.value);
    void persist();
});

/** @type {HTMLElement} */ (document.getElementById("file-new")).addEventListener("click", () => newFile(""));

/** @type {HTMLElement} */ (document.getElementById("run-active")).addEventListener("click", () => {
    if (activeFile !== null) envOutput.textContent = run(activeFile);
});

/** @type {HTMLElement} */ (document.getElementById("run-main")).addEventListener("click", () => {
    envOutput.textContent = run("main.zig");
});

async function initEnvironment() {
    const dir = await opfsDir();
    if (dir !== null) {
        /** @type {Array<[string, FileSystemFileHandle]>} */
        const stored = [];
        /** @type {Array<string>} */
        const storedDirs = [];
        await opfsWalk(dir, "", stored, storedDirs);
        for (const [path, handle] of stored) fs.write(path, await (await handle.getFile()).text());
        for (const d of storedDirs) {
            if (!stored.some(([path]) => path.startsWith(`${d}/`))) fs.mkdir(d);
        }
    }
    if (fs.list().length === 0) {
        fs.write("main.zig", "pub fn main() void {\n    @import(\"std\").debug.print(\"Hello from the VFS!\\n\", .{});\n}\n");
    }
    const files = fs.list().filter((e) => e.kind === "file").map((e) => e.path);
    if (files.length > 0) selectFile(files[0]);
    else renderFileTree();
}
await initEnvironment();

// Readiness signal for automated harnesses: handlers attach only after the
// wasm has instantiated, so a test must wait for this before interacting.
document.body.dataset.ready = "true";
