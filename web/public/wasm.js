// Memory-growth trap: any call that allocates (replAlloc, replEval) can grow
// wasm linear memory, detaching the old `memory.buffer`. So every Uint8Array
// view is built *after* the call that produced the bytes, never cached across
// a wasm call.

/**
 * The wasm exports this binding drives. The module is line-in / text-out: the
 * host writes a line into linear memory, calls an export, then reads the
 * rendered result back out of the result buffer.
 * @typedef {object} Exports
 * @property {WebAssembly.Memory} memory
 * @property {() => boolean} replInit
 * @property {(len: number) => number} replAlloc
 * @property {(ptr: number, len: number) => void} replEval
 * @property {(ptr: number, len: number) => void} replPreview
 * @property {(ptr: number, len: number) => void} replOutline
 * @property {() => number} replResultPtr
 * @property {() => number} replResultLen
 */

/**
 * A node in the syntax tree, keyed by its `Ast` node index. `children` nest.
 * @typedef {object} AstNode
 * @property {number} id
 * @property {string} label
 * @property {number} lo start byte offset into the source.
 * @property {number} hi end byte offset into the source.
 * @property {Array<AstNode>} children
 */

/**
 * A node in the ZIR instruction tree. `detail` is the operand/value summary
 * (absent on structural section headers); `node` is the `AstNode.id` the
 * instruction lowered from, absent when its shape resolves no source node.
 * @typedef {object} ZirNode
 * @property {string} label
 * @property {string} [detail]
 * @property {number} [node]
 * @property {Array<ZirNode>} children
 */

/**
 * Structured lowering of one input: the source plus the syntax nodes and the
 * ZIR tree that index into it.
 * @typedef {object} Outline
 * @property {string} source
 * @property {Array<AstNode>} ast
 * @property {Array<ZirNode>} zir
 */

/**
 * The interpreter, line in / text out. `evalLine` runs against the persistent
 * session; `preview` and `outline` use throwaway sessions.
 * @typedef {object} Binding
 * @property {(line: string) => string} evalLine
 * @property {(line: string) => string} preview
 * @property {(line: string) => Outline} outline
 */

/**
 * Instantiate the wasm interpreter and bind its exports.
 * @param {Record<string, (...args: Array<number>) => void>} [env] host imports
 *   the module may call (e.g. `replClearOutput`).
 * @returns {Promise<Binding & { wasm: Exports }>}
 */
export async function loadRepl(env = {}) {
    const imports = { env: { replClearOutput() {}, ...env } };
    const { instance } = await WebAssembly.instantiateStreaming(fetch("./zig_repl.wasm"), imports);
    const wasm = /** @type {Exports} */ (instance.exports);
    if (!wasm.replInit()) throw new Error("failed to initialise interpreter");

    const encoder = new TextEncoder();
    const decoder = new TextDecoder();

    /**
     * Run an export that takes (ptr, len) and leaves its bytes in the result
     * buffer, returning the decoded result.
     * @param {(ptr: number, len: number) => void} wasmFn
     * @param {string} line
     * @returns {string}
     */
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
        outline: (line) => /** @type {Outline} */ (JSON.parse(call(wasm.replOutline, line))),
    };
}
