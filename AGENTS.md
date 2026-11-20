# AGENTS.md

This file provides guidance to Codex when working with code in this repository.

## Project

A project for **verifying WebAssembly code using Lean 4**. The vehicle is a built-in Wasm interpreter written in Lean: the same definitions that _execute_ a program are the ones you _reason about_, so there is no separate "spec" interpreter to keep in sync with the runner.

The interpreter is deliberately optimized for **simplicity of reasoning, not execution speed**. When making changes, prefer the formulation that is easiest to unfold and `simp` through in proofs over the one that runs faster — performance work belongs behind a separate, proven-equivalent implementation, not in the reference interpreter.

Lean toolchain is pinned in `lean-toolchain`.

## Semantics and program logic

The authoritative semantics is the small-step machine in
`interpreter/Interpreter/Wasm/SmallStep.lean`: the relational
`Wasm.SmallStep.Step` over a `Config` (an `Expr` holding the per-execution
thread state, plus the shared store), and its deterministic executable
presentation `stepChecked?`, proved against `Step` by `stepChecked?_sound` and
`stepChecked?_complete`. `runSteps` iterates it under fuel; the CLI runner
(`Interpreter/Runner.lean`) and the testsuite driver execute only this
iterator. Keep one `Step` per Wasm instruction by default, with small explicit
administrative transitions for control frames, calls, returns and trap
propagation, and keep `Step` and `stepChecked?` in agreement whenever a
transition is added.

The fuel-bounded big-step interpreter (`execOne` / `exec` / `run` in
`Interpreter/Wasm/Semantics.lean`) remains as a regression oracle and as the
semantics behind the big-step `Wasm.TerminatesWith` / `Wasm.PartiallyMeets`
predicates and the `Wp` tactic layer. Some existing specs still use
`Wasm.TerminatesWith` and the `Wp` layer.

`codelib/CodeLib/SepLogic/` instantiates iris-lean for the small-step machine:
the language instance, heap/global ghost state, partial (`wp_*`) and total
(`twp_*`) lifting rules, and adequacy theorems that lower Iris proofs to
`SmallStep.PartiallyMeets` / `SmallStep.TerminatesWith`. The iris-lean
revision is pinned in `codelib/lakefile.toml`.

## Repository layout

Three Lake packages in a monorepo, forming a strict dependency chain:

```
interpreter/   ← Wasm AST, semantics, WP tactic layer  (Lake package: Interpreter)
codelib/       ← lifting lemmas and reasoning helpers   (Lake package: CodeLib)
programs/lean/ ← concrete Rust-to-Wasm verification     (Lake package: Project)
```

`programs/rust/` holds the Rust source crates; `programs/lean/Project/<Name>/`
holds each program's generated `Program.lean`, its hand-written `Spec.lean`,
and its proof modules. The hex encode/decode proofs are the separate
`HexEncodeStdio` and `HexDecodeStdio` libraries of the same package.

Dependency direction: `interpreter` → `codelib` → `programs`. Proofs reach the
interpreter through `CodeLib`; `Spec.lean` files import the specific
interpreter modules their statements name (for example
`Interpreter.Wasm.Host.Universal`).

## Build / run / verify

```bash
just lake-shared        # once: populate repo-root .lake/packages (Mathlib owner: interpreter/)
# then, for each package (the `Project` package lives in programs/lean/, not programs/):
cd <package> && lake build
```

Third-party Lake dependencies (Mathlib and its transitive packages) live in **one** tree at the repo root: `.lake/packages`. Every `lakefile.toml` sets `packagesDir` to that path; per-package `.lake/` holds only `build/` and `config/`.

There is no separate test runner. Example correctness is encoded as Lean theorems and kernel-checked decidable checks inside the examples; a successful `lake build` means every proof and decidable example check passed. To check a single source file in isolation: `lake env lean <path>`.

## Architecture

Three layers, kept deliberately small:

- **Syntax (AST).** Instructions, functions, and modules. Keep the surface area minimal — only add constructs once they are needed by a concrete proof, and prefer the formulation that matches the Wasm spec's terminology so semantics and reasoning lemmas stay legible. Read the current state of `interpreter/Interpreter/Wasm/Syntax.lean` before assuming what is or isn't supported.
- **Semantics (interpreter).** The small-step machine described above, with the big-step `run` kept beside it. Traps (out-of-bounds access, division by zero, etc.) are observable: the small-step machine reaches `Expr.trapped` with a `TrapReason`, and `run` returns `.Trap` in its `Result α` (`.Success` / `.Trap` / `.Invalid` / `.OutOfFuel` / `.Thrown`), distinct from success. When changing the semantics, the structure of the state and the shape of `Step` / `stepChecked?` / `run` are load-bearing for every existing proof — extend in place rather than rewriting, and keep new cases consistent with the existing ones. Read the file before editing.
- **Reasoning (examples and lemmas).** The standard proof style: unfold the interpreter and `simp` to reduce both sides to the same concrete computation; use kernel-checked `decide` or explicit traces for concrete-input sanity checks; compose previously proven theorems as black boxes rather than re-unfolding the interpreter for larger results. New examples should follow this pattern.

## Kernel-checked proofs

Always use proofs checked by Lean's kernel. Do not introduce `bv_decide`,
`bv_check`, `native_decide`, or other native-evaluation axioms to shorten or
discharge proofs. Use ordinary proof terms and kernel-checked tactics instead,
and check representative theorem dependencies with `#print axioms` after
refactoring shared proof infrastructure. Existing uses of native tactics are
legacy code, not precedent for new or rewritten proofs.

## Public spec API: don't expose fuel

`run` takes an explicit `fuel : Nat` so that it terminates syntactically, but fuel is a proof obligation, not part of what a wasm function "does". User-facing specs should never mention fuel — no `∃ fuel, run … fuel = some rs` and no fixed numeric fuel in the statement. Use the fuel-free predicates from `Interpreter/Wasm/Spec/Defs.lean` instead (`Spec/Termination.lean` re-exports them and adds the `FuncSpec` bridge):

- `Wasm.TerminatesWith env m entry initial args P` — total correctness (some fuel succeeds, result satisfies `P`). Discharge via `TerminatesWith.of_run` / `of_run_eq` by exhibiting a concrete fuel internally.
- `Wasm.PartiallyMeets env m entry initial args P` — partial correctness (every terminating fuel-bounded run satisfies `P`).

When writing or updating a spec theorem (tagged `@[spec_of …]` / `@[proves …]`; see `codelib/CodeLib/Attrs.lean`), reach for these — the fuel value belongs inside the proof, not the statement.

## Examples

Examples live in `interpreter/Interpreter/Wasm/Examples/`. Each file defines a hand-built (or WAT-decoded) Wasm module plus the `SmallStep.Config` that starts it, and proves theorems against the small-step machine. The WP tactic layer is *not* used here — no example calls `wp_run`. Two idioms carry the directory:

- **Concrete inputs.** Pin `(runSteps n config).result` with `rfl`, kernel-checked `decide`, or an explicit trace. The decoder-oriented examples use the total projections in `Examples/Harness.lean` (`runValues` / `runTrapMsg` / `runInvalidMsg` / `decodeOrDefault`) for concrete execution checks.
- **Symbolic inputs.** Exhibit the trace explicitly: `apply Steps.cons` once per named `Step` constructor, closing side conditions with `decide` / `simp` / `omega` / domain lemmas. Loops state an invariant at an intermediate `Config` and are closed by `Nat.strong_induction_on` over a decreasing measure (see `Factorial.lean`, `SimpleLoop.lean`, `Gcd.lean`).

The fuel-free statement comes last: lift the run with `runSteps_eq_success_of_steps` / `runSteps_values_terminates` / `runSteps_values_partiallyMeets` / `runSteps_trapped_trapsWith` into `SmallStep.TerminatesWith` / `PartiallyMeets` / `TrapsWith`. New examples should follow this pattern; browse the existing examples directory to find one close to what you are doing and mirror its structure.
