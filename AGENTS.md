# AGENTS.md

This file provides guidance to Codex (Codex.ai/code) when working with code in this repository.

## Project

A project for **verifying WebAssembly code using Lean 4**. The vehicle is a built-in Wasm interpreter written in Lean: the same definitions that _execute_ a program are the ones you _reason about_, so there is no separate "spec" interpreter to keep in sync with the runner.

The interpreter is deliberately optimized for **simplicity of reasoning, not execution speed**. When making changes, prefer the formulation that is easiest to unfold and `simp` through in proofs over the one that runs faster — performance work belongs behind a separate, proven-equivalent implementation, not in the reference interpreter.

Lean toolchain is pinned in `lean-toolchain`.

## Repository layout

Three Lake packages in a monorepo, forming a strict dependency chain:

```
interpreter/   ← Wasm AST, semantics, WP tactic layer  (Lake package: Interpreter)
codelib/       ← lifting lemmas and reasoning helpers   (Lake package: CodeLib)
programs/      ← concrete Rust-to-Wasm verification     (Lake package: Programs)
```

`programs/rust/` holds the Rust source crates; `programs/Programs/` holds the
generated `Program.lean` files and hand-written `Spec.lean` / `Proofs.lean`.

Dependency direction: `interpreter` → `codelib` → `programs`. Downstream code
imports `CodeLib`, never the interpreter directly.

## Build / run / verify

```bash
just lake-shared        # once: populate repo-root .lake/packages (Mathlib owner: interpreter/)
# then, for each package:
cd <package> && lake build
```

Third-party Lake dependencies (Mathlib and its transitive packages) live in **one** tree at the repo root: `.lake/packages`. Every `lakefile.toml` sets `packagesDir` to that path; per-package `.lake/` holds only `build/` and `config/`.

There is no separate test runner. Example correctness is encoded as Lean theorems and `native_decide` checks inside the examples; a successful `lake build` means every proof and decidable example check passed. To check a single source file in isolation: `lake env lean <path>`.

## Architecture

Three layers, kept deliberately small:

- **Syntax (AST).** Instructions, functions, and modules. Keep the surface area minimal — only add constructs once they are needed by a concrete proof, and prefer the formulation that matches the Wasm spec's terminology so semantics and reasoning lemmas stay legible. Read the current state of `interpreter/Interpreter/Wasm/Syntax.lean` before assuming what is or isn't supported.
- **Semantics (interpreter).** A fuel-bounded big-step interpreter. Traps (insufficient operands, out-of-bounds access, division by zero, etc.) are observable as a `none` result from `run`. When changing the semantics, the structure of the state and the shape of `step`/`run` are load-bearing for every existing proof — extend in place rather than rewriting, and keep new cases consistent with the existing ones. Read the file before editing.
- **Reasoning (examples and lemmas).** The standard proof style: unfold the interpreter and `simp` to reduce both sides to the same concrete computation; use `native_decide` for concrete-input sanity checks; compose previously proven theorems as black boxes rather than re-unfolding the interpreter for larger results. New examples should follow this pattern.

## Public spec API: don't expose fuel

`run` takes an explicit `fuel : Nat` so that it terminates syntactically, but fuel is a proof obligation, not part of what a wasm function "does". User-facing specs should never mention fuel — no `∃ fuel, run … fuel = some rs` and no fixed numeric fuel in the statement. Use the fuel-free predicates from `Interpreter/Wasm/Spec/Termination.lean` instead:

- `Wasm.TerminatesWith m entry args P` — total correctness (some fuel succeeds, result satisfies `P`). Discharge via `TerminatesWith.of_run` / `of_run_eq` by exhibiting a concrete fuel internally.
- `Wasm.PartiallyMeets m entry args P` — partial correctness (every terminating fuel-bounded run satisfies `P`).

When writing or updating a `@[wasm_spec]` theorem, reach for these — the fuel value belongs inside the proof, not the statement.

## Examples

Examples live in `interpreter/Interpreter/Wasm/Examples/`. Each file defines a hand-built Wasm module and proves theorems about it using the WP tactic layer. The standard pattern: state the property, apply `wp_run` to reduce to a concrete computation, then close with `simp` / `omega` / domain lemmas. New examples should follow this pattern; browse the existing examples directory to find one close to what you are doing and mirror its structure.
