# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project

A project for **verifying WebAssembly code using Lean 4**. The vehicle is a built-in Wasm interpreter written in Lean: the same definitions that _execute_ a program are the ones you _reason about_, so there is no separate "spec" interpreter to keep in sync with the runner.

The interpreter is deliberately optimized for **simplicity of reasoning, not execution speed**. When making changes, prefer the formulation that is easiest to unfold and `simp` through in proofs over the one that runs faster — performance work belongs behind a separate, proven-equivalent implementation, not in the reference interpreter.

Lean toolchain is pinned in `lean-toolchain`.

## Repository layout

Three Lake packages in a monorepo, forming a strict dependency chain:

```
interpreter/   ← Wasm AST, semantics, WP tactic layer  (Lake package: Interpreter)
codelib/       ← lifting lemmas and reasoning helpers   (Lake package: CodeLib)
programs/lean/ ← concrete Rust-to-Wasm verification     (Lake package: Project)
```

`programs/rust/` holds the Rust source crates; `programs/lean/Project/` holds the
generated `Program.lean` files and hand-written `Spec.lean` / `Proofs.lean`.

Dependency direction: `interpreter` → `codelib` → `programs`. Downstream code
imports `CodeLib`, never the interpreter directly.

## Build / run / verify

```bash
just lake-shared        # once: populate repo-root .lake/packages (Mathlib owner: interpreter/)
# then, for each package (the `Project` package lives in programs/lean/, not programs/):
cd <package> && lake build
```

Third-party Lake dependencies (Mathlib and its transitive packages) live in **one** tree at the repo root: `.lake/packages`. Every `lakefile.toml` sets `packagesDir` to that path; per-package `.lake/` holds only `build/` and `config/`.

There is no separate test runner. Example correctness is encoded as Lean theorems and `native_decide` checks inside the examples; a successful `lake build` means every proof and decidable example check passed. To check a single source file in isolation: `lake env lean <path>`.

## Architecture

Three layers, kept deliberately small:

- **Syntax (AST).** Instructions, functions, and modules. Keep the surface area minimal — only add constructs once they are needed by a concrete proof, and prefer the formulation that matches the Wasm spec's terminology so semantics and reasoning lemmas stay legible. Read the current state of `interpreter/Interpreter/Wasm/Syntax.lean` before assuming what is or isn't supported.
- **Semantics (interpreter).** A fuel-bounded big-step interpreter. Traps (insufficient operands, out-of-bounds access, division by zero, etc.) are observable as a `.Trap` result from `run` (which returns a `Result α`: `.Success` / `.Trap` / `.Invalid` / `.OutOfFuel`), distinct from a successful `.Success`. When changing the semantics, the structure of the state and the shape of `step`/`run` are load-bearing for every existing proof — extend in place rather than rewriting, and keep new cases consistent with the existing ones. Read the file before editing.
- **Reasoning (examples and lemmas).** The standard proof style: unfold the interpreter and `simp` to reduce both sides to the same concrete computation; use `native_decide` for concrete-input sanity checks; compose previously proven theorems as black boxes rather than re-unfolding the interpreter for larger results. New examples should follow this pattern.

## Public spec API: don't expose fuel

`run` takes an explicit `fuel : Nat` so that it terminates syntactically, but fuel is a proof obligation, not part of what a wasm function "does". User-facing specs should never mention fuel — no `∃ fuel, run … fuel = some rs` and no fixed numeric fuel in the statement. Use the fuel-free predicates from `Interpreter/Wasm/Spec/Defs.lean` instead (`Spec/Termination.lean` re-exports them and adds the `FuncSpec` bridge):

- `Wasm.TerminatesWith env m entry initial args P` — total correctness (some fuel succeeds, result satisfies `P`). Discharge via `TerminatesWith.of_run` / `of_run_eq` by exhibiting a concrete fuel internally.
- `Wasm.PartiallyMeets env m entry initial args P` — partial correctness (every terminating fuel-bounded run satisfies `P`).

When writing or updating a spec theorem (tagged `@[spec_of …]` / `@[proves …]`; see `codelib/CodeLib/Attrs.lean`), reach for these — the fuel value belongs inside the proof, not the statement.

## Hosts: default to the universal one

Host imports are resolved **positionally** — `call i` looks up `env.funcs[i]`, matching `m.imports[i]`. A hand-built `HostEnv` therefore serves exactly one import list, in one order, which is why each per-host `env_satisfies` carries the hypothesis `m.imports = thatHost.imports`.

Don't choose a host. Use `Wasm.Universal` (`Interpreter/Wasm/Host/Universal.lean`), which offers every host function the interpreter knows and resolves a module's imports **by name**, in that module's own order:

- `Universal.envFor m` / `Universal.specFor m` — the environment and spec for any module, whatever it imports (a subset, a mixture of hosts, or nothing).
- `Universal.envFor_satisfies m` — holds for **every** module, with no hypothesis on its imports. Prefer it over the per-host `env_satisfies`.
- `Universal.Runs` / `Universal.RunsBytes` — user-facing run predicates; specs name `Universal.State` directly.
- `Universal.covers m` — smoke test that every import is implemented. Resolution is total: an unimplemented import traps rather than failing to resolve, so carry this check in the spec.

Unused host functions are harmless — they sit in the state, unreachable, because no `call` resolves to them. Import-free modules get `HostEnv.empty` definitionally, so they pay nothing.

**Adding a host** (`Interpreter/Wasm/Host/<Name>.lean`): write it exactly the way `Host/StdIO.lean` and `Host/Random.lean` are written — a `State`, the `HostFn`s, an `imports` list, and an `env` whose `funcs` line up with it positionally. **A host file never mentions registries, lenses, composition, or any other host.** There is one way to write a host, and the universal host did not change it.

Then in `Host/Universal.lean` — the only file that knows hosts get composed — one field on `State` (with a default) and one `component` term:

```lean
structure State where
  stdio : StdIO.State := default
  clock : Clock.State := default
deriving Inhabited

def registry : HostRegistry State :=
  .component StdIO.imports StdIO.env.funcs
      State.stdio (fun whole part => { whole with stdio := part })
  ++ .component Clock.imports Clock.env.funcs
      State.clock (fun whole part => { whole with clock := part })
```

`component` asks a host for nothing it does not already have. It takes the field's getter and setter; the lens laws are auto-params that close by `rfl` for any record field, so no `HostLens` is ever named. Contracts and their soundness proofs default to the exact ones, so nobody writes a `HostContract` or a `Satisfies` proof for the universal path.

That is the whole cost. Nothing else, anywhere, needs to change: every existing spec keeps compiling, because adding a defaulted field leaves construction sites and theorem statements valid.

Prefer new host state to be a record of defaulted fields, and never tag `HostFn.lift` or `HostEntry.lift` `@[simp]` — unfolding a lift expands a whole `Store` update at every host call. Use the `HostFn.lift_invoke_*` inversion lemmas instead.

## Examples

Examples live in `interpreter/Interpreter/Wasm/Examples/`. Each file defines a hand-built (or WAT-decoded) Wasm module plus the `SmallStep.Config` that starts it, and proves theorems against the small-step machine. The WP tactic layer is *not* used here — no example calls `wp_run`. Two idioms carry the directory:

- **Concrete inputs.** Pin `(runSteps n config).result` with `rfl` or `native_decide`. The decoder-oriented examples go through the total projections in `Examples/Harness.lean` (`runValues` / `runTrapMsg` / `runInvalidMsg` / `decodeOrDefault`) so `native_decide` can evaluate them.
- **Symbolic inputs.** Exhibit the trace explicitly: `apply Steps.cons` once per named `Step` constructor, closing side conditions with `decide` / `simp` / `omega` / domain lemmas. Loops state an invariant at an intermediate `Config` and are closed by `Nat.strong_induction_on` over a decreasing measure (see `Factorial.lean`, `SimpleLoop.lean`, `Gcd.lean`).

The fuel-free statement comes last: lift the run with `runSteps_eq_success_of_steps` / `runSteps_values_terminates` / `runSteps_values_partiallyMeets` / `runSteps_trapped_trapsWith` into `SmallStep.TerminatesWith` / `PartiallyMeets` / `TrapsWith`. New examples should follow this pattern; browse the existing examples directory to find one close to what you are doing and mirror its structure.
