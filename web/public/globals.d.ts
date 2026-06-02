// `app.js` publishes the interpreter binding on `window` for the console and
// the test harness; this types that access.
declare global {
    interface Window {
        repl: import("./wasm.js").Binding;
    }
}

export {};
