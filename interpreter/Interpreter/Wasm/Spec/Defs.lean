import Interpreter.Wasm.Semantics
import Interpreter.Wasm.Semantics.Lemmas

/-!
# Fuel-free spec predicates

`run` takes an explicit `fuel : Nat` so the interpreter terminates
syntactically, but fuel is a proof obligation -- it isn't part of what a
function "does". User-facing specs should never mention fuel. This module
introduces the two predicates the corpus + verifier use to state specs:

* `TerminatesWith env m id initial args P` -- total correctness. Some fuel
  succeeds with a result satisfying `P`, and (by `run_fuel_mono`) every
  larger fuel produces the same result. Discharge by exhibiting one
  concrete fuel internally and calling `TerminatesWith.of_run` /
  `of_run_eq`.

* `PartiallyMeets env m id initial args P` -- partial correctness. Whenever
  a fuel-bounded run terminates with `.Success`, the result satisfies
  `P`. No termination claim; weaker than `TerminatesWith` but composable
  with programs whose termination depends on inputs.

`of_run` / `of_run_eq` (total-correctness discharge) and `toPartiallyMeets`
(total ⇒ partial bridge) are the intended public discharge API; they are
staged ahead of their first corpus consumer (a target whose termination is
input-dependent, e.g. the recursive `merge_sort` work).
-/

namespace Wasm

/-! ## Definitions -/

/-- Total correctness: from these args, the function call eventually
succeeds (for some bounded fuel and all larger fuels) with a result
satisfying `P`. -/
def TerminatesWith (env : HostEnv α) (m : Module) (id : Nat) (initial : Store α)
    (args : List Value) (P : Store α → List Value → Prop) : Prop :=
  ∃ N, ∀ fuel ≥ N, ∃ vs st, run fuel m id initial args env = .Success vs st ∧ P st vs

/-- Partial correctness: whenever a run terminates with success, the
result satisfies `P`. Does not require termination -- `run` may diverge
(returning `.OutOfFuel` at every fuel) and the predicate still holds. -/
def PartiallyMeets (env : HostEnv α) (m : Module) (id : Nat) (initial : Store α)
    (args : List Value) (P : Store α → List Value → Prop) : Prop :=
  ∀ fuel vs st, run fuel m id initial args env = .Success vs st → P st vs

/-! ## `TerminatesWith` constructors -/

/-- Discharge `TerminatesWith` by exhibiting a concrete fuel that
succeeds, plus the post-condition for that result. Fuel monotonicity
(via `run_fuel_mono`) lifts to "all fuel ≥ N". -/
theorem TerminatesWith.of_run {env : HostEnv α} {m : Module} {id : Nat}
    {initial : Store α} {args : List Value}
    {P : Store α → List Value → Prop} (N : Nat) (vs : List Value) (st : Store α)
    (h_run : run N m id initial args env = .Success vs st) (h_post : P st vs) :
    TerminatesWith env m id initial args P := by
  refine ⟨N, fun fuel hle => ⟨vs, st, ?_, h_post⟩⟩
  have h_ne : run N m id initial args env ≠ .OutOfFuel := by
    rw [h_run]; intro h; cases h
  rw [run_fuel_mono hle h_ne]
  exact h_run

/-- Sugar for the common case where the post is `· = expected` on values
and ignores the final store: simply exhibit a fuel that produces the
expected values. -/
theorem TerminatesWith.of_run_eq {env : HostEnv α} {m : Module} {id : Nat}
    {initial : Store α} {args : List Value}
    (N : Nat) (expected : List Value) (st : Store α)
    (h : run N m id initial args env = .Success expected st) :
    TerminatesWith env m id initial args (fun _ vs => vs = expected) :=
  TerminatesWith.of_run N expected st h rfl

/-- `TerminatesWith` implies `PartiallyMeets` (same env on both sides). -/
theorem TerminatesWith.toPartiallyMeets {env : HostEnv α} {m : Module} {id : Nat}
    {initial : Store α} {args : List Value} {P : Store α → List Value → Prop}
    (h : TerminatesWith env m id initial args P) :
    PartiallyMeets env m id initial args P := by
  obtain ⟨N, hN⟩ := h
  intro fuel vs st hSucc
  have hne : run fuel m id initial args env ≠ .OutOfFuel := by
    rw [hSucc]; intro h; cases h
  obtain ⟨vs', st', hRun', hP'⟩ := hN (max fuel N) (Nat.le_max_right _ _)
  have heq : run (max fuel N) m id initial args env = run fuel m id initial args env :=
    run_fuel_mono (Nat.le_max_left _ _) hne
  rw [hRun', hSucc] at heq
  injection heq with hvs hst
  subst hvs
  subst hst
  exact hP'

end Wasm
