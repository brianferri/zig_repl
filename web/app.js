import { loadRepl } from "./wasm.js";

const replOutput = document.getElementById("repl-output");
const replInput = document.getElementById("repl-input");
const replForm = document.getElementById("repl-form");

const editor = document.getElementById("editor");
const outResult = document.getElementById("out-result");
const outAst = document.getElementById("out-ast");
const outZir = document.getElementById("out-zir");
const cardResult = document.getElementById("card-result");
const cardAst = document.getElementById("card-ast");
const cardZir = document.getElementById("card-zir");

// One wasm instance backs both views: the REPL persists its session across
// lines (replEval); the explorer evaluates in a throwaway one (replPreview),
// so exploring never disturbs REPL state. `:clear` reaches the REPL log.
const { evalLine, preview } = await loadRepl({
    replClearOutput() {
        replOutput.textContent = "";
    },
});

// ---- tabs ----

const tabs = document.querySelectorAll("nav button");
tabs.forEach((btn) => {
    btn.addEventListener("click", () => {
        tabs.forEach((b) => b.classList.toggle("active", b === btn));
        for (const view of document.querySelectorAll(".view")) {
            view.hidden = view.id !== btn.dataset.view;
        }
        (btn.dataset.view === "explorer-view" ? editor : replInput).focus();
    });
});

// ---- repl ----

function appendEcho(text) {
    const span = document.createElement("span");
    span.className = "echo";
    span.textContent = text;
    replOutput.appendChild(span);
    replOutput.scrollTop = replOutput.scrollHeight;
}

function appendOutput(text) {
    replOutput.appendChild(document.createTextNode(text));
    replOutput.scrollTop = replOutput.scrollHeight;
}

replForm.addEventListener("submit", (event) => {
    event.preventDefault();
    const line = replInput.value;
    replInput.value = "";
    if (line.trim().length === 0) return;
    appendEcho(">>> " + line + "\n");
    appendOutput(evalLine(line));
});

// ---- explorer ----

let timer;
editor.addEventListener("input", () => {
    clearTimeout(timer);
    timer = setTimeout(renderExplorer, 150);
});

// Split the preview text into its sections. The dumper emits, in order,
// `source (...)`, `ast (...)`, `zir (...)`, then `replPreview` appends
// `=> value` / `type:`. A failed parse/analysis has none of those -- the
// whole text is the diagnostic.
function parsePreview(text) {
    const result = { ast: "", zir: "", result: "", error: false };
    let dump = text;
    const resultAt = text.indexOf("\n=> ");
    if (resultAt >= 0) {
        dump = text.slice(0, resultAt);
        result.result = text.slice(resultAt + 1).trim();
    }
    const astAt = dump.indexOf("ast (");
    const zirAt = dump.indexOf("zir (");
    if (astAt < 0) {
        result.error = true;
        result.result = text.trim();
        return result;
    }
    result.ast = (zirAt >= 0 ? dump.slice(astAt, zirAt) : dump.slice(astAt)).trim();
    if (zirAt >= 0) result.zir = dump.slice(zirAt).trim();
    if (!result.result) result.result = "(no value)";
    return result;
}

function renderExplorer() {
    const src = editor.value.trim();
    const parsed = src.length ? parsePreview(preview(src)) : { ast: "", zir: "", result: "", error: false };
    outResult.textContent = parsed.result || "—";
    cardResult.classList.toggle("error", parsed.error);
    outAst.textContent = parsed.ast;
    cardAst.hidden = parsed.ast.length === 0;
    outZir.textContent = parsed.zir;
    cardZir.hidden = parsed.zir.length === 0;
}

renderExplorer();
