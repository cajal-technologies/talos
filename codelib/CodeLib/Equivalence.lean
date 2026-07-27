import Interpreter.Wasm

/-!
# Observational equivalence of two wasm entry points

`TerminatesWith` says *one* entry point meets a spec. This file lifts it to a
*relation between two* entry points: run from the same initial store on the same
arguments, two exported functions reach exactly the same observable outcomes,
with success and failure treated symmetrically (if one fails to return, so does
the other).

**What counts as observable is a parameter.** `ObservationallyEquivOn … obs`
observes the returned values together with `obs : Store α → β` of the final
store; every concrete notion is a one-line instance of it, and a new observation
costs only its instance, not another copy of the proofs.

* `ObservationallyEquiv` — the instance at `Store.host`. It deliberately
  **omits linear memory**: two builds of the same function can differ in
  scratch / shadow-stack traffic the caller never sees. This is the right
  notion when the result is a *returned value*, as in the `num_integer`
  opt0-vs-opt3 `gcd` equivalence.
* A program whose *result lives in memory* — `swap_elements` returns `[]` and
  communicates only through the caller's array, so the `Store.host` instance
  degenerates to bare co-termination — needs a stronger observation. Instantiate
  `ObservationallyEquivOn` at one that includes the caller-visible region, e.g.
  `fun st => (st.host, st.mem.words64 base n)`, which observes that region as a
  value while still ignoring scratch traffic outside it.

`ObservationallyEquivOn.of_common_outcome` reduces "these two programs are
equivalent" to "each one `TerminatesWith` the *same* `(result, observation)`
outcome", which is how a concrete equivalence is discharged: prove each program
meets the same total spec, then combine.
-/

namespace Wasm

/-! ## The observation-generic core

Everything below is stated once here, against an arbitrary observation
`obs : Store α → β`, and instantiated afterwards. -/

/-- Two entry points are **observationally equivalent under `obs`** at a given
initial store and argument list: for every candidate outcome
`(result, observation)`, the first entry point terminates with that outcome
**iff** the second does.

Because `TerminatesWith` demands an actual return, "no outcome is reachable"
encodes a trap / divergence, so the biconditional also forces the two to *fail
together*. Anything `obs` does not look at — typically scratch memory and other
module-internal state — is not part of the observed outcome. -/
def ObservationallyEquivOn (env : HostEnv α)
    (m₁ : Module) (id₁ : Nat) (m₂ : Module) (id₂ : Nat)
    (initial : Store α) (args : List Value) (obs : Store α → β) : Prop :=
  ∀ (result : List Value) (o : β),
    TerminatesWith env m₁ id₁ initial args (fun st vs => vs = result ∧ obs st = o)
      ↔
    TerminatesWith env m₂ id₂ initial args (fun st vs => vs = result ∧ obs st = o)

/-- A total-correctness run pins its outcome uniquely: if the *same* call
`TerminatesWith` both `(vs = r ∧ obs = o)` and `(vs = r' ∧ obs = o')`, then
`r = r'` and `o = o'`. (`run` is a function of fuel, so the two witnesses
coincide at a large enough fuel; the final store — hence any observation of
it — is therefore determined.) -/
theorem TerminatesWith.outcome_unique_on {env : HostEnv α} {m : Module} {id : Nat}
    {initial : Store α} {args : List Value} {obs : Store α → β}
    {r r' : List Value} {o o' : β}
    (H  : TerminatesWith env m id initial args (fun st vs => vs = r  ∧ obs st = o))
    (H' : TerminatesWith env m id initial args (fun st vs => vs = r' ∧ obs st = o')) :
    r = r' ∧ o = o' := by
  obtain ⟨N, hN⟩ := H
  obtain ⟨N', hN'⟩ := H'
  obtain ⟨vs, st, hrun, hvs, hobs⟩ := hN (max N N') (Nat.le_max_left _ _)
  obtain ⟨vs', st', hrun', hvs', hobs'⟩ := hN' (max N N') (Nat.le_max_right _ _)
  have heq : (Result.Success vs st : Result α) = Result.Success vs' st' :=
    hrun.symm.trans hrun'
  injection heq with hvseq hsteq
  exact ⟨hvs.symm.trans (hvseq.trans hvs'),
         hobs.symm.trans ((congrArg obs hsteq).trans hobs')⟩

/-- **Discharge rule.** To prove two entry points observationally equivalent it
suffices to exhibit a *single common outcome* both produce: if each one
`TerminatesWith` the same `(result = r ∧ obs = o)`, they are equivalent. This
is the workhorse — prove each program meets the same total spec, then combine. -/
theorem ObservationallyEquivOn.of_common_outcome {env : HostEnv α}
    {m₁ : Module} {id₁ : Nat} {m₂ : Module} {id₂ : Nat}
    {initial : Store α} {args : List Value} {obs : Store α → β}
    {r : List Value} {o : β}
    (h₁ : TerminatesWith env m₁ id₁ initial args (fun st vs => vs = r ∧ obs st = o))
    (h₂ : TerminatesWith env m₂ id₂ initial args (fun st vs => vs = r ∧ obs st = o)) :
    ObservationallyEquivOn env m₁ id₁ m₂ id₂ initial args obs := by
  intro result o'
  constructor
  · intro hm
    obtain ⟨hr, ho⟩ := TerminatesWith.outcome_unique_on hm h₁
    subst hr; subst ho; exact h₂
  · intro hm
    obtain ⟨hr, ho⟩ := TerminatesWith.outcome_unique_on hm h₂
    subst hr; subst ho; exact h₁

/-! ## `ObservationallyEquivOn` is an equivalence relation (at a fixed store, args
and observation) -/

/-- Every entry point is observationally equivalent to itself. -/
theorem ObservationallyEquivOn.refl (env : HostEnv α) (m : Module) (id : Nat)
    (initial : Store α) (args : List Value) (obs : Store α → β) :
    ObservationallyEquivOn env m id m id initial args obs :=
  fun _ _ => Iff.rfl

/-- Observational equivalence is symmetric. -/
theorem ObservationallyEquivOn.symm {env : HostEnv α}
    {m₁ : Module} {id₁ : Nat} {m₂ : Module} {id₂ : Nat}
    {initial : Store α} {args : List Value} {obs : Store α → β}
    (h : ObservationallyEquivOn env m₁ id₁ m₂ id₂ initial args obs) :
    ObservationallyEquivOn env m₂ id₂ m₁ id₁ initial args obs :=
  fun result o => (h result o).symm

/-- Observational equivalence is transitive. -/
theorem ObservationallyEquivOn.trans {env : HostEnv α}
    {m₁ : Module} {id₁ : Nat} {m₂ : Module} {id₂ : Nat} {m₃ : Module} {id₃ : Nat}
    {initial : Store α} {args : List Value} {obs : Store α → β}
    (h₁₂ : ObservationallyEquivOn env m₁ id₁ m₂ id₂ initial args obs)
    (h₂₃ : ObservationallyEquivOn env m₂ id₂ m₃ id₃ initial args obs) :
    ObservationallyEquivOn env m₁ id₁ m₃ id₃ initial args obs :=
  fun result o => (h₁₂ result o).trans (h₂₃ result o)

/-! ## The `Store.host` instance

The observation that ignores linear memory entirely. Each fact below is the
corresponding `…On` fact at `obs := Store.host`; the statements are unchanged
from before the generalisation. -/

/-- Two entry points are **observationally equivalent** at a given initial
store and argument list: for every candidate outcome `(result, hostFinal)`,
the first entry point terminates with that outcome **iff** the second does.

Because `TerminatesWith` demands an actual return, "no outcome is reachable"
encodes a trap / divergence, so the biconditional also forces the two to *fail
together*. Linear memory is not part of the observed outcome. -/
def ObservationallyEquiv (env : HostEnv α)
    (m₁ : Module) (id₁ : Nat) (m₂ : Module) (id₂ : Nat)
    (initial : Store α) (args : List Value) : Prop :=
  ObservationallyEquivOn env m₁ id₁ m₂ id₂ initial args Store.host

/-- A total-correctness run pins its outcome uniquely: if the *same* call
`TerminatesWith` both `(vs = r ∧ host = h)` and `(vs = r' ∧ host = h')`, then
`r = r'` and `h = h'`. (`run` is a function of fuel, so the two witnesses
coincide at a large enough fuel.) -/
theorem TerminatesWith.outcome_unique {env : HostEnv α} {m : Module} {id : Nat}
    {initial : Store α} {args : List Value} {r r' : List Value} {h h' : α}
    (H  : TerminatesWith env m id initial args (fun st vs => vs = r  ∧ st.host = h))
    (H' : TerminatesWith env m id initial args (fun st vs => vs = r' ∧ st.host = h')) :
    r = r' ∧ h = h' :=
  TerminatesWith.outcome_unique_on H H'

/-- **Discharge rule.** To prove two entry points observationally equivalent it
suffices to exhibit a *single common outcome* both produce: if each one
`TerminatesWith` the same `(result = r ∧ host = h)`, they are equivalent. This
is the workhorse — prove each program meets the same total spec, then combine. -/
theorem ObservationallyEquiv.of_common_outcome {env : HostEnv α}
    {m₁ : Module} {id₁ : Nat} {m₂ : Module} {id₂ : Nat}
    {initial : Store α} {args : List Value} {r : List Value} {h : α}
    (h₁ : TerminatesWith env m₁ id₁ initial args (fun st vs => vs = r ∧ st.host = h))
    (h₂ : TerminatesWith env m₂ id₂ initial args (fun st vs => vs = r ∧ st.host = h)) :
    ObservationallyEquiv env m₁ id₁ m₂ id₂ initial args :=
  ObservationallyEquivOn.of_common_outcome h₁ h₂

/-! ## `ObservationallyEquiv` is an equivalence relation (at a fixed store + args) -/

/-- Every entry point is observationally equivalent to itself. -/
theorem ObservationallyEquiv.refl (env : HostEnv α) (m : Module) (id : Nat)
    (initial : Store α) (args : List Value) :
    ObservationallyEquiv env m id m id initial args :=
  ObservationallyEquivOn.refl env m id initial args Store.host

/-- Observational equivalence is symmetric. -/
theorem ObservationallyEquiv.symm {env : HostEnv α}
    {m₁ : Module} {id₁ : Nat} {m₂ : Module} {id₂ : Nat}
    {initial : Store α} {args : List Value}
    (h : ObservationallyEquiv env m₁ id₁ m₂ id₂ initial args) :
    ObservationallyEquiv env m₂ id₂ m₁ id₁ initial args :=
  ObservationallyEquivOn.symm h

/-- Observational equivalence is transitive. -/
theorem ObservationallyEquiv.trans {env : HostEnv α}
    {m₁ : Module} {id₁ : Nat} {m₂ : Module} {id₂ : Nat} {m₃ : Module} {id₃ : Nat}
    {initial : Store α} {args : List Value}
    (h₁₂ : ObservationallyEquiv env m₁ id₁ m₂ id₂ initial args)
    (h₂₃ : ObservationallyEquiv env m₂ id₂ m₃ id₃ initial args) :
    ObservationallyEquiv env m₁ id₁ m₃ id₃ initial args :=
  ObservationallyEquivOn.trans h₁₂ h₂₃

/-! ## Authoritative small-step equivalence

This is the cutover form of the relation above.  It observes finite executions
of `SmallStep.Step` directly and therefore has no fuel or dependency on the
legacy `run` function. -/

namespace SmallStep

/-- Terminal outcomes observed by equivalence.  Traps remain structural and
are not collapsed into divergence. -/
inductive ObservableOutcome where
  | done (values : List Value)
  | trapped (reason : TrapReason)
  deriving BEq, Repr

def ObservableOutcome.toExpr : ObservableOutcome → Expr α
  | .done values => .done values
  | .trapped reason => .trapped reason

/-- A finite authoritative trace reaches a particular terminal outcome. -/
def Reaches (config : Config α)
    (outcome : ObservableOutcome) (store : MachineStore α) : Prop :=
  ∃ trace, Steps config trace ⟨outcome.toExpr, store⟩

/-- Two initialized configurations have exactly the same successful or
trapping observable outcomes. -/
def ObservationallyEquivOn
    (config₁ config₂ : Config α) (obs : MachineStore α → β) : Prop :=
  ∀ (outcome : ObservableOutcome) (o : β),
    (∃ store, Reaches config₁ outcome store ∧ obs store = o) ↔
    (∃ store, Reaches config₂ outcome store ∧ obs store = o)

private theorem ObservableOutcome.toExpr_injective :
    Function.Injective (ObservableOutcome.toExpr : ObservableOutcome → Expr α) := by
  intro first second heq
  cases first <;> cases second <;>
    simp_all [ObservableOutcome.toExpr]

/-- Determinism and terminal irreducibility make a reached outcome unique. -/
theorem Reaches.outcome_unique_on
    {config : Config α} {obs : MachineStore α → β}
    {outcome outcome' : ObservableOutcome}
    {store store' : MachineStore α} {o o' : β}
    (first : Reaches config outcome store) (hfirst : obs store = o)
    (second : Reaches config outcome' store') (hsecond : obs store' = o') :
    outcome = outcome' ∧ o = o' := by
  obtain ⟨trace, execution⟩ := first
  obtain ⟨trace', execution'⟩ := second
  have terminal (terminalOutcome : ObservableOutcome)
      (kind : StepKind) (next : Config α) :
      ¬Step ⟨terminalOutcome.toExpr, store⟩ kind next := by
    cases terminalOutcome with
    | done => exact done_terminal
    | trapped => exact trapped_terminal
  have terminal' (terminalOutcome : ObservableOutcome)
      (kind : StepKind) (next : Config α) :
      ¬Step ⟨terminalOutcome.toExpr, store'⟩ kind next := by
    cases terminalOutcome with
    | done => exact done_terminal
    | trapped => exact trapped_terminal
  have hconfig := steps_irreducible_deterministic execution execution'
    (terminal outcome) (terminal' outcome')
  have hparts := Config.mk.inj hconfig
  have houtcome := ObservableOutcome.toExpr_injective hparts.1
  exact
    ⟨houtcome,
      hfirst.symm.trans ((congrArg obs hparts.2).trans hsecond)⟩

/-- A common reached terminal outcome discharges equivalence. -/
theorem ObservationallyEquivOn.of_common_reached
    {config₁ config₂ : Config α} {obs : MachineStore α → β}
    {outcome : ObservableOutcome} {store₁ store₂ : MachineStore α} {o : β}
    (first : Reaches config₁ outcome store₁) (hfirst : obs store₁ = o)
    (second : Reaches config₂ outcome store₂) (hsecond : obs store₂ = o) :
    ObservationallyEquivOn config₁ config₂ obs := by
  intro candidate observed
  constructor
  · rintro ⟨store, reached, hobs⟩
    obtain ⟨rfl, rfl⟩ :=
      Reaches.outcome_unique_on reached hobs first hfirst
    exact ⟨store₂, second, hsecond⟩
  · rintro ⟨store, reached, hobs⟩
    obtain ⟨rfl, rfl⟩ :=
      Reaches.outcome_unique_on reached hobs second hsecond
    exact ⟨store₁, first, hfirst⟩

/-- A common normally terminating result is the main success-specialized
discharge rule. -/
theorem ObservationallyEquivOn.of_common_outcome
    {config₁ config₂ : Config α} {obs : MachineStore α → β}
    {r : List Value} {o : β}
    (first : TerminatesWith config₁
      (fun values store => values = r ∧ obs store = o))
    (second : TerminatesWith config₂
      (fun values store => values = r ∧ obs store = o)) :
    ObservationallyEquivOn config₁ config₂ obs := by
  obtain ⟨trace₁, values₁, store₁, execution₁, hvalues₁, hobs₁⟩ := first
  obtain ⟨trace₂, values₂, store₂, execution₂, hvalues₂, hobs₂⟩ := second
  subst values₁
  subst values₂
  apply ObservationallyEquivOn.of_common_reached
    (outcome := .done r) (store₁ := store₁) (store₂ := store₂)
  · exact ⟨trace₁, execution₁⟩
  · exact hobs₁
  · exact ⟨trace₂, execution₂⟩
  · exact hobs₂

/-- A common structural trap is an observable common outcome. -/
theorem ObservationallyEquivOn.of_common_trap
    {config₁ config₂ : Config α} {obs : MachineStore α → β}
    {reason : TrapReason} {store₁ store₂ : MachineStore α} {o : β}
    (first : Reaches config₁ (.trapped reason) store₁)
    (hfirst : obs store₁ = o)
    (second : Reaches config₂ (.trapped reason) store₂)
    (hsecond : obs store₂ = o) :
    ObservationallyEquivOn config₁ config₂ obs :=
  ObservationallyEquivOn.of_common_reached first hfirst second hsecond

theorem ObservationallyEquivOn.refl
    (config : Config α) (obs : MachineStore α → β) :
    ObservationallyEquivOn config config obs :=
  fun _ _ => Iff.rfl

theorem ObservationallyEquivOn.symm
    {config₁ config₂ : Config α} {obs : MachineStore α → β}
    (equivalent : ObservationallyEquivOn config₁ config₂ obs) :
    ObservationallyEquivOn config₂ config₁ obs :=
  fun outcome observed => (equivalent outcome observed).symm

theorem ObservationallyEquivOn.trans
    {config₁ config₂ config₃ : Config α} {obs : MachineStore α → β}
    (first : ObservationallyEquivOn config₁ config₂ obs)
    (second : ObservationallyEquivOn config₂ config₃ obs) :
    ObservationallyEquivOn config₁ config₃ obs :=
  fun outcome observed =>
    (first outcome observed).trans (second outcome observed)

/-- Host-state observation, deliberately ignoring module-private scratch
memory as in the legacy relation. -/
def ObservationallyEquiv (config₁ config₂ : Config α) : Prop :=
  ObservationallyEquivOn config₁ config₂ (fun store => store.wasm.host)

theorem ObservationallyEquiv.of_common_outcome
    {config₁ config₂ : Config α} {r : List Value} {h : α}
    (first : TerminatesWith config₁
      (fun values store => values = r ∧ store.wasm.host = h))
    (second : TerminatesWith config₂
      (fun values store => values = r ∧ store.wasm.host = h)) :
    ObservationallyEquiv config₁ config₂ :=
  ObservationallyEquivOn.of_common_outcome first second

end SmallStep

end Wasm
