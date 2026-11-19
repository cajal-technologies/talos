# Talos

[![Lean](https://img.shields.io/badge/Lean-v4.36.0-blue?logo=lean)](lean-toolchain)
[![Telegram](https://img.shields.io/badge/Telegram-Join%20the%20discussion-2CA5E0?logo=telegram&logoColor=white)](https://t.me/TalosDev)

**Talos** is a WebAssembly interpreter written in Lean 4, named after the bronze giant of Greek mythology who guarded Crete — a mechanical guardian, built to enforce rules.

The same definitions that _execute_ a Wasm program are the ones you _reason about_. There is no separate spec interpreter to keep in sync: evaluation and proof share a single codebase.

> **Work in progress.** Talos is under active development. APIs and proof interfaces may change.

## Visual overview

A visual introduction to how WebAssembly, Talos, and Lean fit together to support proofs about compiled programs.

https://github.com/user-attachments/assets/70255831-491e-40b4-a658-b3bee326197f

## What this is

The goal is a **feature-complete, executable semantics for WebAssembly** that doubles as a formal object. You can:

- Run programs on concrete inputs.
- State and prove theorems about their behavior — correctness against a spec, equivalence between programs, properties that hold for all inputs — using Lean's proof tooling.

The interpreter is deliberately optimized for **clarity of reasoning over execution speed**. Talos aims for full Wasm coverage, but the immediate focus is on the subset of features that arise naturally from non-optimized, higher-level source code (Rust, C, etc.) — the semantics that actually matter when you want to verify what a program _does_, not how fast it does it.

Proof is the north star. Performance work belongs behind a separately proven-equivalent implementation.

## Reasoning foundation

Proofs in Talos are built on **weakest precondition (WP) calculus** — a [predicate transformer semantics](https://en.wikipedia.org/wiki/Predicate_transformer_semantics) that lets you reason backwards from postconditions to the preconditions that guarantee them. This gives structured, compositional proofs for loops, branches, and function calls without re-unfolding the interpreter at every step.

## Quick start

**Clone the repository and build the interpreter** (the WebAssembly spec testsuite is a git submodule):

```bash
git clone --recurse-submodules https://github.com/cajal-technologies/talos.git
cd talos
(cd interpreter && lake exe cache get && lake build)
```

`lake exe cache get` downloads the available prebuilt Mathlib cache, avoiding a full source build.

**Run a `.wat` module** (from `interpreter/`):

```
cd interpreter
lake exe runner samples/factorial.wat fact 5
```

Output: `120`

**Run with a fuel cap** (default 1 000 000 steps):

```
lake exe runner --fuel 10000 samples/factorial.wat fact 5
```

**Traps and exit codes.** A WebAssembly trap is program behavior, not an interpreter crash. The runner reports it to stderr and exits nonzero:

```bash
lake exe runner samples/trap.wat div_by_zero           # trap, exit 1
lake exe runner --fuel 5 samples/factorial.wat fact 5   # out of fuel, exit 2
```

Exit codes: `0` on success, `1` for a trap, `2` when fuel runs out, and `3` for other errors such as bad arguments or a decoding failure. `i32` arithmetic wraps modulo 2^32, so `fact 13` prints `1932053504` rather than `13!`.

See [`interpreter/samples/`](interpreter/samples/) for example modules and `lake exe runner --help` for CLI options.

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

Build the Rust-to-Wasm artifacts before building the Lean program proofs. `programs/lean` reads the generated `programs/rust/build/<crate>/program.wat` files, which are not checked in:

```bash
just verifier-build  # Rust → Wasm → printed WAT
just build           # build Interpreter → CodeLib → programs/lean
```

The generated `Program.lean` files read `program.wat` through `watFunctionBody%` and retain a WAT SHA-256 line; they do not embed all the printed WAT. Keep the `wasm-tools` version consistent with `WASM_TOOLS_VERSION` in the root [`justfile`](justfile), particularly when generating WAT or regenerating the testsuite report.

`just build` runs the root Lake workspace build and its `lake-shared` prerequisite, which performs `lake update` and `lake exe cache get`. For the cache only, run `lake exe cache get` from `interpreter/` without invoking `lake-shared`. To build a single package from the repo root, use:

```bash
just build-interpreter
just build-codelib
just build-programs  # run `just verifier-build` first for generated WAT
```

Dependencies:

- **Lean 4** via [`elan`](https://github.com/leanprover/elan), using the pinned toolchain.
- **Rust** via [`rustup`](https://rustup.rs), with the toolchain and `wasm32-unknown-unknown` target pinned in [`programs/rust/rust-toolchain.toml`](programs/rust/rust-toolchain.toml), for building Rust programs.
- **[`wasm-tools`](https://github.com/bytecodealliance/wasm-tools)** for WAT generation and the spec testsuite. Install the version pinned in the root `justfile` when reproducing generated artifacts and reports.

## Running the Wasm testsuite

```bash
just testsuite
```

Filter to a specific file by name:

```bash
just testsuite i32
```

`just testsuite` hides `skipped` and `module_unavailable` rows. For the complete status of the spec cases, consult [`testsuite_report.txt`](testsuite_report.txt). Regenerate it with `just testsuite-report` (which checks the pinned `wasm-tools` version) before committing a coverage change.

## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md).

## License

GNU Affero General Public License v3.0 — see [LICENSE](LICENSE).
