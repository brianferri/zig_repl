# zig-repl

An expression-first REPL for Zig 0.16.

The REPL parses input with Zig's own parser (`std.zig.Ast`) and evaluates a
bounded language subset with persistent session state.

## Commands

- `:help` show available commands
- `:vars` list current variables
- `:fns` list defined functions
- `:reset` clear all session state
- `:quit` exit the REPL

## Runtime Contract

### Output Channels

- Value output is written to stdout.
- Captured external output (for emulated external calls) is written to stdout.
- Diagnostics and debug logs are written through `std.log` (typically stderr).

### Debug vs Release

- Debug builds emit scoped debug logs (`debug(repl): ...`, `debug(ast): ...`, `debug(eval): ...`).
- Release builds do not emit debug logs by default.
- Error logs are scoped (`error(ast): ...`, `error(eval): ...`).

### Inline Statements

The REPL supports semicolon-separated inline statements in one input line:

```zig
const std = @import("std"); std.debug.print("Hello", .{});
```

Execution is sequential and non-transactional. If an early segment succeeds and a
later segment fails, prior state mutations remain committed.

### Multiline Input

If input has unclosed delimiters/strings, the REPL waits for continuation and
prompts with `...`.

## Display Representation Policy

### Top-level integers

Top-level integer results are rendered as a base table:

```text
Base    Value
BIN     0b1
OCT     0o1
DEC     1
HEX     0x1
```

### Nested integers

Nested integers (for example inside arrays/structs) are currently rendered as
plain decimal in aggregate formatting.

### Strings

Strings are displayed as byte-slice literals:

- `"A"` renders as `&.{65}`
- `"Hello"` renders as `&.{72, 101, 108, 108, 111}`

Operationally, string values are still used as text payloads for output capture.

### Address-of

`&expr` is modeled as an address wrapper value and printed with `&` prefix (for
example `&.{69}`). This is not a full pointer memory model.

## Builtin Support

Builtins are recognized via `std.zig.BuiltinFn.list`.

Implemented runtime builtins:

- `@import("...")` recursive module loading with cache/cycle checks
- `@addWithOverflow` (used by `std.math.add` paths)

All other recognized builtins currently return `UnsupportedBuiltin`.

## Supported Input (Current Subset)

### Declarations

- `const` / `var` declarations
- `fn` declarations

### Expressions

- literals: int, float, bool, string, char
- unary: `-`, `!`, `&`
- binary arithmetic/comparison/boolean/bitwise
- error-set merge `||`
- function calls and builtin calls
- field access and index access
- `if` expression forms
- `catch` expression
- array and struct literal forms

### Known reduced semantics

- some constructs are intentionally reduced and not Zig-complete (for example
  selected lowering shortcuts for currently unsupported full semantics).
- see `docs/repl_subset_spec.md` for detailed support and rationale.

## Import Resolution

`@import("std")` resolution order:

1. `ZIG_LIB_DIR`
2. probing from `PATH` entries near `zig`

Relative imports resolve from current module path when available, otherwise from
cwd.

## Example

```text
> const std = @import("std"); std.debug.print("Hello", .{});
Hello
void
> &.{69}
&.{69}
> "A"
&.{65}
```
