import Interpreter.Wasm

/-!
# Observational equivalence of two small-step configurations

`SmallStep.TerminatesWith` says *one* configuration meets a spec. This file
lifts that to a *relation between two* configurations: they reach exactly the
same terminal outcomes (successful results or structural traps) by finite
`SmallStep.Step` traces, so success and failure are treated symmetrically.

**What counts as observable is a parameter.** `ObservationallyEquivOn … obs`
observes the terminal outcome together with `obs : MachineStore α → β` of the
final store. `ObservationallyEquiv` is the instance at the host state: it
deliberately ignores linear memory, so two builds of the same function may
differ in scratch / shadow-stack traffic. A program whose result lives in
memory instantiates `ObservationallyEquivOn` at an observation that includes
the caller-visible region instead.

`ObservationallyEquivOn.of_common_outcome` reduces "these two programs are
equivalent" to "each one `TerminatesWith` the *same* `(result, observation)`
outcome": prove each program meets the same total spec, then combine.
-/

namespace Wasm

namespace SmallStep

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
  obtain ⟨houtcome, hstore⟩ := steps_outcome_deterministic execution execution'
  exact
    ⟨houtcome,
      hfirst.symm.trans ((congrArg obs hstore).trans hsecond)⟩

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
memory. -/
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
