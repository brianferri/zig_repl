import { loadRepl } from "./wasm.js";

/** @typedef {import("./wasm.js").AstNode} AstNode */
/** @typedef {import("./wasm.js").ZirNode} ZirNode */

const replOutput = /** @type {HTMLElement} */ (document.getElementById("repl-output"));
const replInput = /** @type {HTMLTextAreaElement} */ (document.getElementById("repl-input"));
const replForm = /** @type {HTMLFormElement} */ (document.getElementById("repl-form"));

const editor = /** @type {HTMLTextAreaElement} */ (document.getElementById("editor"));
const outResult = /** @type {HTMLElement} */ (document.getElementById("out-result"));
const outAst = /** @type {HTMLElement} */ (document.getElementById("out-ast"));
const outZir = /** @type {HTMLElement} */ (document.getElementById("out-zir"));

// One wasm instance backs both tabs: the REPL persists its session
// (replEval); the explorer uses throwaway sessions (replPreview / replOutline)
// so exploring never disturbs REPL state.
const { evalLine, preview, outline } = await loadRepl({
    replClearOutput() {
        replOutput.textContent = "";
    },
});

// Expose the interpreter binding for the console and the test harness.
window.repl = { evalLine, preview, outline };

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

// Drag the gutters to resize the editor/panels split and the panel sections.
// Each gutter resizes the sibling before it, pinning that pane to a pixel size
// while the rest of the flex column absorbs the remainder.
const explorerView = /** @type {HTMLElement} */ (document.getElementById("explorer-view"));

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
    draggable(/** @type {HTMLElement} */ (gutter), (dx) => {
        const width = Math.min(Math.max(pane.offsetWidth + dx, 240), explorerView.clientWidth - 320);
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

// Grow the input to fit its content (CSS caps it, then it scrolls).
function fitInput() {
    replInput.style.height = "auto";
    replInput.style.height = `${replInput.scrollHeight}px`;
}
replInput.addEventListener("input", fitInput);

// Enter runs the input; Shift+Enter inserts a newline, so a multi-line program
// (a function, a paste) is entered as one submission.
replInput.addEventListener("keydown", (event) => {
    if (event.key === "Enter" && !event.shiftKey) {
        event.preventDefault();
        replForm.requestSubmit();
    }
});

replForm.addEventListener("submit", (event) => {
    event.preventDefault();
    const source = replInput.value;
    replInput.value = "";
    fitInput();
    if (source.trim().length === 0) return;
    appendEcho(">>> " + source + "\n");
    appendOutput(evalLine(source));
});

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
 * `editor.value` (what `setSelectionRange` indexes) rather than the outline's
 * own source.
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
    // The outline reports offsets into its own `source` -- the trailing
    // expression when declarations precede it, so a sub-slice of the editor.
    // Locate it so editor selections land on the right span.
    const base = Math.max(value.lastIndexOf(data.source), 0);
    indexSpans(data.ast, base);
    renderAst(outAst, data.ast, data.source);
    renderZir(outZir, data.zir);
    outResult.textContent = preview(src).trim() || "(no value)";
}

// Seed the editor so the explorer is populated on load (kept in JS, not as
// textarea markup, to leave the HTML cleanly indented).
editor.value = "const x: u32 = 40;\nx + 2";
renderExplorer();

// Readiness signal for automated harnesses: handlers attach only after the
// wasm has instantiated, so a test must wait for this before interacting.
document.body.dataset.ready = "true";
