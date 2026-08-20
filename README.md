---
accent:    "#f7a41d"
bg:        "#0e1116"
dark:       true
font:       Inter
titleFont:  Inter
mono:      "JetBrains Mono"
particles:  false
---

# zig-repl

An expression-first REPL for Zig.

It evaluates input with a faithful port of the compiler's own semantic
analysis, so results match what `zig` folds at comptime.

---

## How it works

Input is parsed by Zig's own parser and lowered to ZIR by
`std.zig.AstGen`; the same front end the compiler uses.

Evaluation is a port of the compiler's `Sema`, `InternPool`, `Type`, and `Value`, run comptime-eager:
every expression folds to a concrete value, with session state persisting across
lines.

---

## Run it

```sh
zig build run     # the terminal REPL
zig build wasm    # the wasm REPL + web explorer -> zig-out/web
zig build test    # compliance and unit tests (--fuzz to drive the coverage-guided fuzzer)
```

A hosted build runs in the browser at [brianferri.github.io/zig_repl](https://brianferri.github.io/zig_repl).

---

## Commands

- `:help` list every command with its summary
- `:dump <expr>` show the AST and tree-walked ZIR for an expression
- `:theme [name]` show or switch the prompt theme (`zig`, `catppuccin`, `adwaita-dark`)
- `:terminal` show the active terminal's detected capabilities
- `:clear` wipe the output log (web)
- `:quit` exit the REPL

---

## What it evaluates

### Values & aggregates

Integers, floats, bools, strings; structs, tuples, enums, unions; arrays,
slices, and vectors.

### Pointers & wrappers

Pointers, optionals, and error unions, with the pointer-cast family
(`@ptrCast`, `@alignCast`, `@constCast`, `@volatileCast`).

### Control flow

`if` / `switch` / `while` / `for`, plus `catch`, `try`, and error-union capture.

### Types & reflection

`@TypeOf`, `@typeInfo`, `@Type`, `@sizeOf` / `@alignOf` / `@offsetOf`, and
`@import` of `std`, `root`, and local modules.

---

## Web explorer

The wasm frontend is two views over the same core:

- a **REPL** with persistent session state, and
- an **explorer** that renders the **AST** and the tree-walked **ZIR** for any
  input side by side, so you can watch the front end lower your code.

---

This README is a valid [dropdeck](https://brianferri.github.io/dropdeck)!

Drop it into the presenter to read these notes as slides.
