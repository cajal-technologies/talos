# Talos

[![Lean](https://img.shields.io/badge/Lean-v4.34.1-blue?logo=lean)](lean-toolchain)
[![Telegram](https://img.shields.io/badge/Telegram-Join%20the%20discussion-2CA5E0?logo=telegram&logoColor=white)](https://t.me/TalosDev)

**Talos** is a WebAssembly interpreter written in Lean 4, named after the bronze giant of Greek mythology who guarded Crete — a mechanical guardian, built to enforce rules.

The same definitions that _execute_ a Wasm program are the ones you _reason about_. There is no separate spec interpreter to keep in sync: evaluation and proof share a single codebase.

> **Work in progress.** Talos is under active development. APIs and proof interfaces may change.

## What this is

The goal is a **feature-complete, executable semantics for WebAssembly** that doubles as a formal object. You can:

- Run programs on concrete inputs.
- State and prove theorems about their behavior — correctness against a spec, equivalence between programs, properties that hold for all inputs — using Lean's proof tooling.

The interpreter is deliberately optimized for **clarity of reasoning over execution speed**. Talos aims for full Wasm coverage, but the immediate focus is on the subset of features that arise naturally from non-optimized, higher-level source code (Rust, C, etc.) — the semantics that actually matter when you want to verify what a program _does_, not how fast it does it.

Proof is the north star. Performance work belongs behind a separately proven-equivalent implementation.

## Reasoning foundation

Proofs in Talos are built on **weakest precondition (WP) calculus** — a [predicate transformer semantics](https://en.wikipedia.org/wiki/Predicate_transformer_semantics) that lets you reason backwards from postconditions to the preconditions that guarantee them. This gives structured, compositional proofs for loops, branches, and function calls without re-unfolding the interpreter at every step.

## Quick start

**Clone and build the interpreter** (the Wasm spec testsuite is a git submodule, and `lake exe cache get` downloads prebuilt Mathlib instead of compiling it from source):

```
git clone --recurse-submodules https://github.com/cajal-technologies/talos.git
cd talos/interpreter
lake exe cache get   # or `just lake-shared` from the repo root (also runs `lake update`)
lake build
```

**Run a `.wat` module** (still in `interpreter/`):

```
lake exe runner samples/factorial.wat fact 5
```

Output: `120`

**Run with a fuel cap** (default 1 000 000 steps):

```
lake exe runner --fuel 10000 samples/factorial.wat fact 5
```

**Traps and exit codes.** A trap is specified Wasm behaviour, not an interpreter failure. The runner reports it on stderr and exits non-zero:

```
lake exe runner samples/trap.wat div_by_zero          # trap: integer divide by zero   (exit 1)
lake exe runner --fuel 5 samples/factorial.wat fact 5  # out of fuel                    (exit 2)
```

Exit codes: `0` success, `1` trap, `2` out of fuel, `3` any other error (bad arguments, unknown export, decode failure). Note that `i32` arithmetic wraps modulo 2^32: `fact 13` prints `1932053504`, not 13! (6227020800).

See [`interpreter/samples/`](interpreter/samples/) for the example modules and `lake exe runner --help` for the full CLI.

**Prove something about it:**

[`interpreter/Interpreter/Wasm/Examples/Factorial.lean`](interpreter/Interpreter/Wasm/Examples/Factorial.lean) shows a complete correctness proof by composing instruction-granular small-step traces.

## Repository layout

Three Lake packages in a monorepo, forming a strict dependency chain:

| Package | Path | Purpose |
|---------|------|---------|
| `Interpreter` | `interpreter/` | Wasm AST, semantics, WP tactic layer |
| `CodeLib` | `codelib/` | Lifting lemmas and program-reasoning helpers |
| `Project` | `programs/lean/` | Concrete Rust-to-Wasm verification tasks |

## Using as a dependency

**Depend on the interpreter only** (Wasm semantics + WP calculus):

```toml
# lakefile.toml
[[require]]
name = "WasmInterpreterLean"
scope = "your-org"           # if published, or use path/git
path = "path/to/repo/interpreter"
```

**Depend on CodeLib** (adds lifting lemmas and reasoning helpers on top):

```toml
[[require]]
name = "CodeLib"
path = "path/to/repo/codelib"
```

Code that imports `CodeLib` never needs to import the interpreter directly —
`CodeLib` re-exports the parts of the interpreter that downstream proofs need.

## Building

The `programs/lean` package reads the Wasm emitted by the Rust crates (`programs/rust/build/<crate>/program.wat`, which is not checked in), so build those first, once and again whenever a crate changes:

```bash
just verifier-build   # cargo build-wasm + wasm-tools strip/print → programs/rust/build/<crate>/program.wat
```

This needs Rust (the toolchain and the `wasm32-unknown-unknown` target are pinned in `programs/rust/rust-toolchain.toml`, so `rustup` installs them) and `wasm-tools`. Note that `just rust-build` alone is not enough: it runs a plain `cargo build` and does not write `program.wat`.

Then:

```bash
just build   # builds interpreter → codelib → programs in order
```

Or build a single package (each line runs from the repository root):

```bash
(cd interpreter   && lake exe cache get && lake build)   # cache get: once, fetches prebuilt Mathlib
(cd codelib       && lake build)
(cd programs/lean && lake build)                         # needs `just verifier-build` first
```

`just build` runs the cache step for you (via `just lake-shared`).

Dependencies:

- **Lean 4** — toolchain pinned in `interpreter/lean-toolchain`, fetched automatically by [`elan`](https://github.com/leanprover/elan).
- **[`wasm-tools`](https://github.com/bytecodealliance/wasm-tools)** — needed to decode `.wasm` binaries, to run the Wasm testsuite, and by `just verifier-build`. `brew install wasm-tools` or `cargo install wasm-tools`. The emitted `Program.lean` files embed the printed `.wat`, so use the version pinned as `WASM_TOOLS_VERSION` in the `justfile` (currently 1.251.0, e.g. `cargo install wasm-tools --version 1.251.0`).
- **Rust** (via [`rustup`](https://rustup.rs)) — only for `programs/`; see above.

## Running the Wasm testsuite

```bash
just testsuite
```

Filter to a specific file by name:

```bash
just testsuite i32
```

## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md).

## License

GNU Affero General Public License v3.0 — see [LICENSE](LICENSE).
