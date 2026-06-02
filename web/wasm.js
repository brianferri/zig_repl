// Shared binding for the wasm REPL: load the module, then `evalLine`
// writes an input line into wasm memory, calls `replEval`, and reads the
// rendered text back.
//
// Memory-growth trap: any call that allocates (replAlloc, replEval) can
// grow wasm linear memory, which detaches the old `memory.buffer`. So we
// build every Uint8Array view *after* the call that produced the bytes we
// want to read, never caching a view across a wasm call.

export async function loadRepl(env = {}) {
    const imports = { env: { replClearOutput() {}, ...env } };
    const { instance } = await WebAssembly.instantiateStreaming(fetch("./zig_repl.wasm"), imports);
    const wasm = instance.exports;
    if (!wasm.replInit()) throw new Error("failed to initialise interpreter");

    const encoder = new TextEncoder();
    const decoder = new TextDecoder();

    // `wasmFn` is `replEval` (run + persist) or `replPreview` (run in a
    // throwaway session for the explorer). Both take (ptr, len) and leave
    // their text in the result buffer.
    function call(wasmFn, line) {
        const bytes = encoder.encode(line);
        const ptr = wasm.replAlloc(bytes.length);
        if (ptr === 0) return "out of memory\n";
        new Uint8Array(wasm.memory.buffer, ptr, bytes.length).set(bytes);
        wasmFn(ptr, bytes.length);
        const resultPtr = wasm.replResultPtr();
        const resultLen = wasm.replResultLen();
        return decoder.decode(new Uint8Array(wasm.memory.buffer, resultPtr, resultLen));
    }

    return {
        wasm,
        evalLine: (line) => call(wasm.replEval, line),
        preview: (line) => call(wasm.replPreview, line),
    };
}
