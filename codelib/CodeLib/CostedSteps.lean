import CodeLib.Basic

/-!
# Costs on finite Wasm traces

A charge can depend on both machine states and the step label. Erasing a cost
annotation gives the original small-step execution with the same terminal store.
Concatenating segments adds their costs.
-/

namespace Wasm.SmallStep

/-- A charge may inspect operands, the executed instruction, and the state
change, including host transfers and successful memory growth. -/
abbrev StepCost (α : Type) := Config α → StepKind → Config α → Nat

/-- Derived cost annotation of the existing authoritative transition relation. -/
inductive CostedSteps (charge : StepCost α) :
    Config α → List StepKind → Config α → Nat → Prop where
  | refl (config) : CostedSteps charge config [] config 0
  | cons (head : Step config kind next)
      (tail : CostedSteps charge next trace final amount) :
      CostedSteps charge config (kind :: trace) final
        (charge config kind next + amount)

variable {α : Type} {charge : StepCost α}
  {config next middle final : Config α}
  {kind : StepKind} {trace trace₁ trace₂ : List StepKind}
  {amount amount₁ amount₂ : Nat}

namespace CostedSteps

theorem erase (execution : CostedSteps charge config trace final amount) :
    Steps config trace final := by
  induction execution with
  | refl => exact .refl _
  | cons head _ ih => exact .cons head ih

theorem single (head : Step config kind next) :
    CostedSteps charge config [kind] next (charge config kind next) := by
  simpa using CostedSteps.cons (charge := charge) head (.refl next)

theorem trans
    (first : CostedSteps charge config trace₁ middle amount₁)
    (second : CostedSteps charge middle trace₂ final amount₂) :
    CostedSteps charge config (trace₁ ++ trace₂) final (amount₁ + amount₂) := by
  induction first with
  | refl => simpa using second
  | cons head _ ih =>
      simpa [Nat.add_assoc] using CostedSteps.cons head (ih second)

/-- Charging each transition one unit counts exactly the labels of the trace. -/
theorem unit_amount (execution : CostedSteps (fun _ _ _ => 1) config trace final amount) :
    amount = trace.length := by
  induction execution with
  | refl => rfl
  | cons _ _ ih => simp [ih, Nat.add_comm]

end CostedSteps

/-- Every existing finite trace has an annotation; no symbolic execution is
replayed. Existence of a cost is weaker than an upper bound on that cost. -/
theorem Steps.with_cost (execution : Steps config trace final)
    (charge : StepCost α) :
    ∃ amount, CostedSteps charge config trace final amount := by
  induction execution with
  | refl => exact ⟨0, .refl _⟩
  | cons head _ ih =>
      obtain ⟨amount, tail⟩ := ih
      exact ⟨_, .cons head tail⟩

/-- Compose bounded iteration segments. A strictly decreasing variant gives a
linear bound in the number of possible variant decrements; the exit branch
has its own bounded cost. Neither hypothesis assumes whole-loop execution. -/
theorem costed_loop_of_variant
    {α ι : Type} (charge : StepCost α) (head : ι → Config α)
    (variant : ι → Nat) (iterationCost exitCost : Nat)
    (exit : ∀ i, variant i = 0 →
      ∃ trace values store amount,
        CostedSteps charge (head i) trace ⟨.done values, store⟩ amount ∧ amount ≤ exitCost)
    (iterate : ∀ i, 0 < variant i →
      ∃ j trace amount, CostedSteps charge (head i) trace (head j) amount ∧
        variant j < variant i ∧ amount ≤ iterationCost)
    (initial : ι) :
    ∃ trace values store amount,
      CostedSteps charge (head initial) trace ⟨.done values, store⟩ amount ∧
      amount ≤ iterationCost * variant initial + exitCost := by
  induction hvariant : variant initial using Nat.strongRecOn generalizing initial with
  | ind n ih =>
      subst n
      by_cases zero : variant initial = 0
      · obtain ⟨trace, values, store, amount, steps, bound⟩ := exit initial zero
        exact ⟨trace, values, store, amount, steps, by simpa [zero] using bound⟩
      · obtain ⟨next, trace, amount, steps, decreases, localBound⟩ :=
          iterate initial (by omega)
        obtain ⟨suffix, values, store, rest, tail, tailBound⟩ :=
          ih (variant next) decreases next rfl
        have decreaseBound := Nat.mul_le_mul_left iterationCost
          (show variant next + 1 ≤ variant initial by omega)
        simp only [Nat.mul_add, Nat.mul_one] at decreaseBound
        exact ⟨trace ++ suffix, values, store, amount + rest, steps.trans tail, by omega⟩

/-- Apply an existing functional theorem to a costed execution, so both claims
describe exactly the same trace and terminal store. Iris TWP adequacy supplies
the functional argument through `TerminatesWith.toPartiallyMeets`. -/
theorem CostedSteps.meets_post
    {α : Type} {charge : StepCost α} {initial : Config α}
    {trace : List StepKind} {values : List Value} {store : MachineStore α} {amount : Nat}
    {post : List Value → MachineStore α → Prop}
    (execution : CostedSteps charge initial trace ⟨.done values, store⟩ amount)
    (functional : PartiallyMeets initial post) : post values store :=
  functional trace values store execution.erase

/-- Equip a finite execution with its exact small-step count. -/
theorem Steps.with_unit_cost (execution : Steps config trace final) :
    CostedSteps (fun _ _ _ => 1) config trace final trace.length := by
  obtain ⟨_, counted⟩ := execution.with_cost (fun _ _ _ => 1)
  exact counted.unit_amount ▸ counted

end Wasm.SmallStep
