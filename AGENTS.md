# AGENTS.md

This file provides guidance to Codex (Codex.ai/code) when working with code in this repository.

## Project

A project for **verifying WebAssembly code using Lean 4**. The vehicle is a built-in Wasm interpreter written in Lean: the same definitions that _execute_ a program are the ones you _reason about_, so there is no separate "spec" interpreter to keep in sync with the runner.

The interpreter is deliberately optimized for **simplicity of reasoning, not execution speed**. When making changes, prefer the formulation that is easiest to unfold and `simp` through in proofs over the one that runs faster — performance work belongs behind a separate, proven-equivalent implementation, not in the reference interpreter.

Lean toolchain is pinned in `lean-toolchain`.

## Iris migration (`iris` branch only)

> **Temporary branch-scoped notice.** This section must exist only on the
> `iris` integration branch and branches created from `iris` during the
> migration. It overrides conflicting guidance elsewhere in this file,
> especially guidance to preserve the current big-step interpreter's shape.
> Before merging the completed migration into `main`, remove this notice or
> update it to describe the new permanent architecture.

The purpose of the `iris` branch is to integrate
[iris-lean](https://github.com/leanprover-community/iris-lean) and migrate the
reference Wasm interpreter from its current fuel-bounded big-step semantics to
small-step semantics suitable for Iris.

The migration is complete when:

- The interpreter is fully expressed using small-step semantics in the form
  expected by iris-lean.
- Every currently supported Wasm feature and test remains covered, with no
  semantic regressions.
- Differential testing remains possible. In particular, there must still be an
  executable, fuel-bounded way to run Wasm code, built by iterating the
  executable small-step function rather than by maintaining a second semantics.
- All required iris-lean language and proof-mode instances are implemented, so
  downstream proofs can use iris-lean directly.
- Existing proofs and theorem statements need not retain their exact shape.
  Nevertheless, preserve the intent and coverage of existing examples whenever
  possible, rewriting them against the new semantics rather than silently
  deleting them.

The intended split between an Iris expression and state is approximately:

```lean
inductive Expr
  | running : ThreadState → Expr
  | done : List WasmVal → Expr
  | trapped : TrapReason → Expr
  deriving BEq, Repr

structure Store where
  functions : Array Function
  memories : Array Memory
  globals : Array Global
  tables : Array Table
  deriving BEq, Repr
```

Treat this as an architectural guide, not a requirement to preserve these exact
names. `Expr` contains the whole per-execution `ThreadState`, not merely the
remaining instruction list. `Store` contains the shared runtime resources.
Keep that ownership boundary explicit when adding fields: thread-local control
and operand state belongs in `ThreadState`; resources observed or mutated
through the runtime store belong in `Store`.

For convenient executable interpretation, package the Iris expression and
state together, while keeping the relational semantics authoritative:

```lean
/- Convenient packaging for the executable interpreter. The Iris adapter will
   split this back into its `Expr` and `State` arguments. -/
structure Config where
  expr : Expr
  store : Store
  deriving BEq, Repr

inductive Step : Config → Config → Prop where
  -- Full definition of all valid transitions.

def step? : Config → Option Config
  | ⟨.running thread, store⟩ => stepRunning? thread store
  | ⟨.done _, _⟩ => none
  | ⟨.trapped _, _⟩ => none

theorem step?_sound {config config' : Config} :
    step? config = some config' → Step config config' := by
  sorry

theorem step?_complete {config config' : Config} :
    Step config config' → step? config = some config' := by
  sorry

theorem step_sound {config config' : Config} :
    step? config = some config' → Step config config' :=
  step?_sound

theorem step_complete {config config' : Config} :
    Step config config' → step? config = some config' :=
  step?_complete

theorem step_iff {config config' : Config} :
    step? config = some config' ↔ Step config config' :=
  ⟨step_sound, step_complete⟩
```

The exact iris-lean adapter must follow the API of the pinned iris-lean
dependency. Implement every required instance from this `Expr`/`Store` split
and prove it against `Step`; do not introduce a parallel Iris-only transition
relation.

Use instruction-level granularity as the default: one `Step` should normally
execute one Wasm instruction. Administrative transitions may execute no Wasm
instruction when they expose or remove control frames, prepare or return from a
function call, propagate a trap, or otherwise reorganize the machine so the
next instruction can run. Prefer small, explicit administrative transitions
over hiding multi-stage control behavior inside a single large step. A
transition may perform the atomic state effects intrinsic to its instruction;
do not split an instruction solely to mirror implementation helper functions.
Document intentional exceptions and keep the granularity consistent across
related instructions.

For now, assume the Wasm semantics implemented here is deterministic, as
required by `step? : Config → Option Config` and `step?_complete`. Whenever a
feature appears nondeterministic—or depends on unspecified host behavior,
scheduling, external input, or an arbitrary choice—flag it before implementing
the transition. Record whether the behavior can be made deterministic by an
explicit input or policy in `Store`. If genuine nondeterminism is required,
stop and decide how to represent executable successor choices and adapt the
Iris semantics and correspondence theorem; never choose an outcome silently.

During the migration:

- Pin iris-lean to a known revision. Upgrade it intentionally, recording any
  adapter or instance changes required by the new API.
- Treat the instruction and administrative-step policy above as the default
  Iris atomicity boundary. Review deviations explicitly; do not change
  granularity merely to make the executable runner more convenient.
- Make the relational `Step` and executable `step?` correspond in every PR.
  A new transition is incomplete until both sides and their soundness and
  completeness proofs agree.
- State and preserve invariants at transition boundaries, including stack
  typing, index validity, store-extension/ownership properties, and the
  distinction between normal completion and traps.
- Keep `.done` and `.trapped` terminal. Out-of-fuel belongs to the executable
  runner's result, not to `Expr` or the semantic relation.
- Add regression or differential tests while porting each instruction family.
  Where feasible, compare the new runner with the old interpreter until the old
  implementation is removed.
- Keep migration PRs reviewable and layered: introduce representation and
  compatibility lemmas first, then port coherent instruction families and
  their examples. Do not remove the old path before equivalent coverage exists.
- Build every affected package in dependency order. A successful build remains
  the test criterion throughout the transition.

iris-lean does not currently provide total-execution reasoning for this
integration. Iris proofs therefore establish behavior conditional on reaching
completion; they do not establish termination. This loss of total-correctness
claims is accepted during the migration. Keep termination-sensitive theorem
intent documented so it can be restored if total reasoning becomes available,
and do not describe a partial-correctness result as a termination proof.

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

`run` takes an explicit `fuel : Nat` so that it terminates syntactically, but fuel is a proof obligation, not part of what a wasm function "does". User-facing specs should never mention fuel — no `∃ fuel, run … fuel = some rs` and no fixed numeric fuel in the statement. Use the fuel-free predicates from `Interpreter/Wasm/Spec/Termination.lean` instead:

- `Wasm.TerminatesWith env m entry initial args P` — total correctness (some fuel succeeds, result satisfies `P`). Discharge via `TerminatesWith.of_run` / `of_run_eq` by exhibiting a concrete fuel internally.
- `Wasm.PartiallyMeets env m entry initial args P` — partial correctness (every terminating fuel-bounded run satisfies `P`).

When writing or updating a spec theorem (tagged `@[spec_of …]` / `@[proves …]`; see `codelib/CodeLib/Attrs.lean`), reach for these — the fuel value belongs inside the proof, not the statement.

## Examples

Examples live in `interpreter/Interpreter/Wasm/Examples/`. Each file defines a hand-built Wasm module and proves theorems about it using the WP tactic layer. The standard pattern: state the property, apply `wp_run` to reduce to a concrete computation, then close with `simp` / `omega` / domain lemmas. New examples should follow this pattern; browse the existing examples directory to find one close to what you are doing and mirror its structure.
