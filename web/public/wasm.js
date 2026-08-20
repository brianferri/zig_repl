// Memory-growth trap: any call that allocates (replAlloc, replEval) can grow
// wasm linear memory, detaching the old `memory.buffer`. So every Uint8Array
// view is built *after* the call that produced the bytes, never cached across a wasm call.

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
 * @property {(ptr: number, len: number) => void} replInputFeed
 * @property {() => number} replInputBufferPtr
 * @property {() => number} replInputBufferLen
 * @property {() => number} replInputCursor
 * @property {() => number} replInputTakeSubmitted
 * @property {() => number} replInputSubmittedPtr
 * @property {() => void} replThemes
 * @property {() => void} replFsList
 * @property {(ptr: number, len: number) => void} replFsRead
 * @property {(pathPtr: number, pathLen: number, dataPtr: number, dataLen: number) => void} replFsWrite
 * @property {(ptr: number, len: number) => void} replFsMkdir
 * @property {(ptr: number, len: number) => void} replFsDelete
 * @property {(oldPtr: number, oldLen: number, newPtr: number, newLen: number) => void} replFsRename
 * @property {(ptr: number, len: number) => void} replRun
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
 * @typedef {object} InputState
 * @property {string} buffer the current input line (may span multiple lines).
 * @property {number} cursor byte offset of the cursor within `buffer`.
 */

/**
 * The interpreter, line in / text out. `evalLine` runs against the persistent
 * session; `preview` and `outline` use throwaway sessions. `feed`/`inputState`/
 * `takeSubmitted` drive the shared line editor from raw key bytes.
 * @typedef {object} Binding
 * @property {(line: string) => string} evalLine
 * @property {(line: string) => string} preview
 * @property {(line: string) => Outline} outline
 * @property {(bytes: Uint8Array) => void} feed
 * @property {() => InputState} inputState
 * @property {() => (string | null)} takeSubmitted
 * @property {() => Array<Theme>} themes
 * @property {Fs} fs
 * @property {(path: string) => string} run
 */

/**
 * One entry from `Fs.list`: its path and whether it names a file or a directory. An empty directory
 * appears only as its own `directory` entry.
 * @typedef {object} FsEntry
 * @property {string} path
 * @property {"file" | "directory"} kind
 */

/**
 * The virtual filesystem the environment tab edits and `run` resolves `@import` against.
 * @typedef {object} Fs
 * @property {() => Array<FsEntry>} list
 * @property {(path: string) => string} read
 * @property {(path: string, data: string) => void} write
 * @property {(path: string) => void} mkdir
 * @property {(path: string) => void} remove
 * @property {(from: string, to: string) => void} rename
 */

/**
 * An RGB color, each channel 0-255.
 * @typedef {object} Rgb
 * @property {number} r
 * @property {number} g
 * @property {number} b
 */

/**
 * A prompt theme: its name, its accent (the terminal prompt color), and the
 * scheme's surface palette keyed by role. A non-terminal frontend paints its
 * background and body from `palette` and its prompt from `accent`.
 * @typedef {object} Theme
 * @property {string} name
 * @property {Rgb} accent
 * @property {Record<string, Rgb>} palette
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

    // Pointer to a fresh wasm buffer holding `bytes`; 0 for empty (the export
    // slices [0..0], freeing nothing), -1 on allocation failure.
    /** @param {Uint8Array} bytes @returns {number} */
    function writeBytes(bytes) {
        if (bytes.length === 0) return 0;
        const ptr = wasm.replAlloc(bytes.length);
        if (ptr === 0) return -1;
        new Uint8Array(wasm.memory.buffer, ptr, bytes.length).set(bytes);
        return ptr;
    }

    /**
     * Run an export that takes (ptr, len) and leaves its bytes in the result
     * buffer, returning the decoded result.
     * @param {(ptr: number, len: number) => void} wasmFn
     * @param {string} line
     * @returns {string}
     */
    function call(wasmFn, line) {
        const bytes = encoder.encode(line);
        const ptr = writeBytes(bytes);
        if (ptr < 0) return "out of memory\n";
        wasmFn(ptr, bytes.length);
        return decoder.decode(new Uint8Array(wasm.memory.buffer, wasm.replResultPtr(), wasm.replResultLen()));
    }

    /** @param {string} line @returns {Outline} */
    function outline(line) {
        const text = call(wasm.replOutline, line);
        // `call` returns a plain message (not JSON) when allocation fails;
        // degrade to an empty outline.
        try {
            return /** @type {Outline} */ (JSON.parse(text));
        } catch {
            return { source: "", ast: [], zir: [] };
        }
    }

    /** @param {number} ptr @param {number} len @returns {string} */
    function readString(ptr, len) {
        return decoder.decode(new Uint8Array(wasm.memory.buffer, ptr, len));
    }

    /** @param {Uint8Array} bytes */
    function feed(bytes) {
        const ptr = writeBytes(bytes);
        if (ptr < 0) return;
        wasm.replInputFeed(ptr, bytes.length);
    }

    /** @returns {InputState} */
    function inputState() {
        return {
            buffer: readString(wasm.replInputBufferPtr(), wasm.replInputBufferLen()),
            cursor: wasm.replInputCursor(),
        };
    }

    /** @returns {string | null} */
    function takeSubmitted() {
        const len = wasm.replInputTakeSubmitted();
        if (len < 0) return null;
        return readString(wasm.replInputSubmittedPtr(), len);
    }

    /** @returns {Array<Theme>} */
    function themes() {
        wasm.replThemes();
        try {
            return JSON.parse(readString(wasm.replResultPtr(), wasm.replResultLen()));
        } catch {
            return [];
        }
    }

    /** @param {(ptr: number, len: number) => void} wasmFn @param {string} s */
    function send(wasmFn, s) {
        const bytes = encoder.encode(s);
        const ptr = writeBytes(bytes);
        if (ptr < 0) return;
        wasmFn(ptr, bytes.length);
    }

    /** @param {(ap: number, al: number, bp: number, bl: number) => void} wasmFn @param {string} a @param {string} b */
    function sendTwo(wasmFn, a, b) {
        const ab = encoder.encode(a);
        const bb = encoder.encode(b);
        const ap = writeBytes(ab);
        const bp = writeBytes(bb);
        if (ap < 0 || bp < 0) return;
        wasmFn(ap, ab.length, bp, bb.length);
    }

    /** @type {Fs} */
    const fs = {
        list() {
            wasm.replFsList();
            try {
                return JSON.parse(readString(wasm.replResultPtr(), wasm.replResultLen()));
            } catch {
                return [];
            }
        },
        read: (path) => call(wasm.replFsRead, path),
        write: (path, data) => sendTwo(wasm.replFsWrite, path, data),
        mkdir: (path) => send(wasm.replFsMkdir, path),
        remove: (path) => send(wasm.replFsDelete, path),
        rename: (from, to) => sendTwo(wasm.replFsRename, from, to),
    };

    return {
        wasm,
        evalLine: (line) => call(wasm.replEval, line),
        preview: (line) => call(wasm.replPreview, line),
        outline,
        feed,
        inputState,
        takeSubmitted,
        themes,
        fs,
        run: (path) => call(wasm.replRun, path),
    };
}
