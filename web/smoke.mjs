// Headless check that the wasm REPL actually computes -- the same binding
// logic repl.js runs, without a browser. Run after `zig build wasm`:
//   node zig-out/web/smoke.mjs
import { readFile } from "node:fs/promises";

const wasmBytes = await readFile(new URL("./zig_repl.wasm", import.meta.url));
const { instance } = await WebAssembly.instantiate(wasmBytes, {
    env: { replClearOutput() {} },
});
const wasm = instance.exports;

const encoder = new TextEncoder();
const decoder = new TextDecoder();

function evalLine(line) {
    const bytes = encoder.encode(line);
    const ptr = wasm.replAlloc(bytes.length);
    new Uint8Array(wasm.memory.buffer, ptr, bytes.length).set(bytes);
    wasm.replEval(ptr, bytes.length);
    return decoder.decode(
        new Uint8Array(wasm.memory.buffer, wasm.replResultPtr(), wasm.replResultLen()),
    );
}

if (!wasm.replInit()) throw new Error("replInit failed");

let failed = 0;
function check(label, got, want) {
    const ok = got === want;
    if (!ok) failed++;
    console.log(`${ok ? "ok  " : "FAIL"}  ${label} => ${JSON.stringify(got)}${ok ? "" : ` (want ${JSON.stringify(want)})`}`);
}

check('"1 + 2"', evalLine("1 + 2").trim(), "3");
check('"const x = 40; x + 2" (session persists)', evalLine("const x = 40; x + 2").trim(), "42");
check('"x * 2" (binding from a prior line)', evalLine("x * 2").trim(), "80");
check('":help" lists :clear', evalLine(":help").includes(":clear"), true);
check('":bogus" reports unknown', evalLine(":bogus").trim(), "unknown command: :bogus");

process.exit(failed === 0 ? 0 : 1);
