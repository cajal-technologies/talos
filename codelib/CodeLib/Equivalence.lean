import Interpreter.Wasm

/-!
# Observational equivalence of two wasm entry points

`TerminatesWith` says *one* entry point meets a spec. This file lifts it to a
*relation between two* entry points: `ObservationallyEquiv` says that, run from
the same initial store on the same arguments, two exported functions reach
exactly the same observable outcomes — the **returned values** and the final
**host state** (`Store.host`) — with success and failure treated symmetrically
(if one fails to return, so does the other).

The observation deliberately **omits linear memory**: two builds of the same
function can differ in scratch / shadow-stack traffic the caller never sees.
Programs whose *result* lives in memory need a stronger observation than this
one; add it when such a proof arrives.

This is the reusable core behind the `num_integer` opt0-vs-opt3 equivalence.
`ObservationallyEquiv.of_common_outcome` reduces "these two programs are
equivalent" to "each one `TerminatesWith` the *same* `(result, host)` outcome",
which is how a concrete equivalence is discharged: prove each program meets the
same total spec, then combine.
-/

namespace Wasm

/-- Two entry points are **observationally equivalent** at a given initial
store and argument list: for every candidate outcome `(result, hostFinal)`,
the first entry point terminates with that outcome **iff** the second does.

Because `TerminatesWith` demands an actual return, "no outcome is reachable"
encodes a trap / divergence, so the biconditional also forces the two to *fail
together*. Linear memory is not part of the observed outcome. -/
def ObservationallyEquiv (env : HostEnv α)
    (m₁ : Module) (id₁ : Nat) (m₂ : Module) (id₂ : Nat)
    (initial : Store α) (args : List Value) : Prop :=
  ∀ (result : List Value) (hostFinal : α),
    TerminatesWith env m₁ id₁ initial args (fun st vs => vs = result ∧ st.host = hostFinal)
      ↔
    TerminatesWith env m₂ id₂ initial args (fun st vs => vs = result ∧ st.host = hostFinal)

/-- A total-correctness run pins its outcome uniquely: if the *same* call
`TerminatesWith` both `(vs = r ∧ host = h)` and `(vs = r' ∧ host = h')`, then
`r = r'` and `h = h'`. (`run` is a function of fuel, so the two witnesses
coincide at a large enough fuel.) -/
theorem TerminatesWith.outcome_unique {env : HostEnv α} {m : Module} {id : Nat}
    {initial : Store α} {args : List Value} {r r' : List Value} {h h' : α}
    (H  : TerminatesWith env m id initial args (fun st vs => vs = r  ∧ st.host = h))
    (H' : TerminatesWith env m id initial args (fun st vs => vs = r' ∧ st.host = h')) :
    r = r' ∧ h = h' := by
  obtain ⟨N, hN⟩ := H
  obtain ⟨N', hN'⟩ := H'
  obtain ⟨vs, st, hrun, hvs, hhost⟩ := hN (max N N') (Nat.le_max_left _ _)
  obtain ⟨vs', st', hrun', hvs', hhost'⟩ := hN' (max N N') (Nat.le_max_right _ _)
  have heq : (Result.Success vs st : Result α) = Result.Success vs' st' :=
    hrun.symm.trans hrun'
  injection heq with hvseq hsteq
  exact ⟨hvs.symm.trans (hvseq.trans hvs'),
         hhost.symm.trans ((congrArg Store.host hsteq).trans hhost')⟩

/-- **Discharge rule.** To prove two entry points observationally equivalent it
suffices to exhibit a *single common outcome* both produce: if each one
`TerminatesWith` the same `(result = r ∧ host = h)`, they are equivalent. This
is the workhorse — prove each program meets the same total spec, then combine. -/
theorem ObservationallyEquiv.of_common_outcome {env : HostEnv α}
    {m₁ : Module} {id₁ : Nat} {m₂ : Module} {id₂ : Nat}
    {initial : Store α} {args : List Value} {r : List Value} {h : α}
    (h₁ : TerminatesWith env m₁ id₁ initial args (fun st vs => vs = r ∧ st.host = h))
    (h₂ : TerminatesWith env m₂ id₂ initial args (fun st vs => vs = r ∧ st.host = h)) :
    ObservationallyEquiv env m₁ id₁ m₂ id₂ initial args := by
  intro result hostFinal
  constructor
  · intro hm
    obtain ⟨hr, hh⟩ := TerminatesWith.outcome_unique hm h₁
    subst hr; subst hh; exact h₂
  · intro hm
    obtain ⟨hr, hh⟩ := TerminatesWith.outcome_unique hm h₂
    subst hr; subst hh; exact h₁

/-! ## `ObservationallyEquiv` is an equivalence relation (at a fixed store + args) -/

/-- Every entry point is observationally equivalent to itself. -/
theorem ObservationallyEquiv.refl (env : HostEnv α) (m : Module) (id : Nat)
    (initial : Store α) (args : List Value) :
    ObservationallyEquiv env m id m id initial args :=
  fun _ _ => Iff.rfl

/-- Observational equivalence is symmetric. -/
theorem ObservationallyEquiv.symm {env : HostEnv α}
    {m₁ : Module} {id₁ : Nat} {m₂ : Module} {id₂ : Nat}
    {initial : Store α} {args : List Value}
    (h : ObservationallyEquiv env m₁ id₁ m₂ id₂ initial args) :
    ObservationallyEquiv env m₂ id₂ m₁ id₁ initial args :=
  fun result hostFinal => (h result hostFinal).symm

/-- Observational equivalence is transitive. -/
theorem ObservationallyEquiv.trans {env : HostEnv α}
    {m₁ : Module} {id₁ : Nat} {m₂ : Module} {id₂ : Nat} {m₃ : Module} {id₃ : Nat}
    {initial : Store α} {args : List Value}
    (h₁₂ : ObservationallyEquiv env m₁ id₁ m₂ id₂ initial args)
    (h₂₃ : ObservationallyEquiv env m₂ id₂ m₃ id₃ initial args) :
    ObservationallyEquiv env m₁ id₁ m₃ id₃ initial args :=
  fun result hostFinal => (h₁₂ result hostFinal).trans (h₂₃ result hostFinal)

end Wasm
