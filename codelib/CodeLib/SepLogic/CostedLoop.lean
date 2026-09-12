import CodeLib.SepLogic.CostedSteps
import CodeLib.Examples.Gcd

/-!
# Costed loop segments with an existing Iris functional proof

The loop rule composes finite authoritative iteration certificates using a
natural-number variant. It needs one local cost certificate per loop branch;
it does not re-execute Wasm or extract a budget from an opaque total WP.

The consumer is the existing handwritten GCD program and its existing Iris
total-WP theorem. Only its short guard/iteration traces are certified here.
The mathematical GCD invariant is reused from `gcd_terminatesWith`, not proved
again. This demonstrates semantic composition and functional-proof reuse.
Local cost certificates are explicit premises of this rule; an arbitrary
heap-owning TWP body proof alone does not supply them.
-/

namespace Wasm.SmallStep

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

/-- Scalar-only semantic segments have cost equal to their trace length.
This reuses an authoritative trace certificate and proves no new transitions. -/
theorem Steps.with_unit_cost
    {α : Type} {charge : StepCost α} {initial final : Config α} {trace : List StepKind}
    (execution : Steps initial trace final)
    (unit : ∀ before kind after, kind ∈ trace → charge before kind after = 1) :
    CostedSteps charge initial trace final trace.length := by
  induction execution with
  | refl => exact .refl _
  | @cons config kind next trace final head tail ih =>
      have tailUnit : ∀ before kind after, kind ∈ trace → charge before kind after = 1 := by
        intro before label after member
        exact unit before label after (by simp [member])
      have prefixUnit := unit config kind next (by simp)
      simpa [prefixUnit, Nat.add_comm] using CostedSteps.cons head (ih tailUnit)

end Wasm.SmallStep

namespace Wasm.Examples.Gcd.Cost

open Wasm.SmallStep

/-- GCD uses scalar operations only, but retains the same byte-work metric as
memory- and host-using consumers of `CostedSteps`. -/
abbrev work : StepCost Unit := byteWork (fun _ _ _ => 0)

private structure State where
  a : UInt32
  b : UInt32
  temporary : UInt32

private def loopFrame : ControlFrame :=
  { kind := .loop, paramArity := 0, resultArity := 0
    body := gcdLoopBody, continuation := [.localGet 0, .ret], belowStack := [] }

private def head (state : State) : Config Unit :=
  { expr := .running
      ⟨⟨[.i32 state.a, .i32 state.b], [.i32 state.temporary], []⟩,
        gcdLoopBody, 1, [], [loopFrame], []⟩
    store := (gcdConfig state.a state.b).store }

private theorem exit_segment (a temporary : UInt32) :
    ∃ trace, CostedSteps work (head ⟨a, 0, temporary⟩) trace
      ⟨.done [.i32 a], (gcdConfig a 0).store⟩ 7 := by
  let trace : List StepKind :=
    [.instruction (.block 0 0 gcdLoopBlock), .instruction (.localGet 1),
      .instruction .eqz, .instruction (.br_if 0), .administrative .exitControl,
      .instruction (.localGet 0), .administrative .returnFromFunction]
  have steps : Steps (head ⟨a, 0, temporary⟩) trace
      ⟨.done [.i32 a], (gcdConfig a 0).store⟩ := by
    wasm_steps [.block, (.localGet rfl), (.eqz rfl),
      (.brIf (by simp) rfl), (.exitControl rfl), (.localGet rfl)]
    exact Steps.single .returnFromFunction
  refine ⟨trace, steps.with_unit_cost ?_⟩
  intro before kind after member
  simp only [trace, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem iteration_segment (a b temporary : UInt32) (nonzero : b ≠ 0) :
    ∃ trace, CostedSteps work (head ⟨a, b, temporary⟩) trace
      (head ⟨b, a % b, a % b⟩) 13 := by
  let trace : List StepKind :=
    [.instruction (.block 0 0 gcdLoopBlock), .instruction (.localGet 1),
      .instruction .eqz, .instruction (.br_if 0), .instruction (.localGet 0),
      .instruction (.localGet 1), .instruction .remU, .instruction (.localSet 2),
      .instruction (.localGet 1), .instruction (.localSet 0),
      .instruction (.localGet 2), .instruction (.localSet 1), .instruction (.br 1)]
  have steps : Steps (head ⟨a, b, temporary⟩) trace (head ⟨b, a % b, a % b⟩) := by
    wasm_steps [.block, (.localGet rfl), (.eqz (result := 0) (by simp [nonzero])),
      .brIfZero, (.localGet rfl), (.localGet rfl), (.remU nonzero),
      (.localSet rfl), (.localGet rfl), (.localSet rfl), (.localGet rfl),
      (.localSet rfl)]
    exact Steps.single (.br rfl)
  refine ⟨trace, steps.with_unit_cost ?_⟩
  intro before kind after member
  simp only [trace, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl <;> rfl

private theorem loop_bound (initial : State) :
    ∃ trace values store amount,
      CostedSteps work (head initial) trace ⟨.done values, store⟩ amount ∧
      amount ≤ 13 * initial.b.toNat + 7 := by
  apply costed_loop_of_variant work head (fun state => state.b.toNat) 13 7
  · intro state zero
    rcases state with ⟨a, b, temporary⟩
    have : b = 0 := UInt32.toNat.inj zero
    subst b
    obtain ⟨trace, steps⟩ := exit_segment a temporary
    exact ⟨trace, [.i32 a], (gcdConfig a 0).store, 7, steps, by omega⟩
  · intro state positive
    have nonzero : state.b ≠ 0 := by intro zero; simp [zero] at positive
    obtain ⟨trace, steps⟩ := iteration_segment state.a state.b state.temporary nonzero
    refine ⟨⟨state.b, state.a % state.b, state.a % state.b⟩, trace, 13, steps, ?_, by omega⟩
    simpa using Nat.mod_lt state.a.toNat positive

/-- The existing Iris GCD theorem supplies the mathematical result; the new
segment rule supplies the cost. This is a deliberately loose linear bound in
the numeric second argument, not a logarithmic Euclidean-complexity claim. -/
theorem gcd_work_bound (a b : UInt32) :
    ∃ trace store amount,
      CostedSteps work (gcdConfig a b) trace
        ⟨.done [.i32 (UInt32.ofNat (Nat.gcd a.toNat b.toNat))], store⟩ amount ∧
      trace.length ≤ amount ∧ amount ≤ 13 * b.toNat + 8 := by
  obtain ⟨trace, values, store, amount, loop, bound⟩ := loop_bound ⟨a, b, 0⟩
  change amount ≤ 13 * b.toNat + 7 at bound
  have entry : CostedSteps work (gcdConfig a b)
      [.instruction (.loop 0 0 gcdLoopBody)] (head ⟨a, b, 0⟩) 1 :=
    CostedSteps.single Step.loop
  have execution := entry.trans loop
  have result := execution.meets_post (gcd_terminatesWith a b).toPartiallyMeets
  subst values
  refine ⟨_, store, 1 + amount, execution, ?_, by omega⟩
  exact execution.length_le (fun before kind after _ => byteWork_positive _ before kind after)

/-- The zero-iteration case still charges loop entry, the guard and return. -/
theorem zero_case_exact (a : UInt32) :
    ∃ trace, CostedSteps work (gcdConfig a 0) trace
      ⟨.done [.i32 a], (gcdConfig a 0).store⟩ 8 := by
  obtain ⟨trace, exit⟩ := exit_segment a 0
  have entry : CostedSteps work (gcdConfig a 0)
      [.instruction (.loop 0 0 gcdLoopBody)] (head ⟨a, 0, 0⟩) 1 :=
    CostedSteps.single Step.loop
  exact ⟨_, entry.trans exit⟩

/-- Two nonzero Euclidean iterations exercise both the recursive segment rule
and the zero exit; all costs belong to the same authoritative execution. -/
theorem two_iterations_exact :
    ∃ trace, CostedSteps work (gcdConfig 24 18) trace
      ⟨.done [.i32 6], (gcdConfig 24 18).store⟩ 34 := by
  have entry : CostedSteps work (gcdConfig 24 18)
      [.instruction (.loop 0 0 gcdLoopBody)] (head ⟨24, 18, 0⟩) 1 :=
    CostedSteps.single Step.loop
  obtain ⟨firstTrace, first⟩ := iteration_segment 24 18 0 (by decide)
  obtain ⟨secondTrace, second⟩ := iteration_segment 18 6 6 (by decide)
  obtain ⟨exitTrace, exit⟩ := exit_segment 6 0
  exact ⟨_, entry.trans (first.trans (second.trans exit))⟩

/-- Concrete sanity check through the existing runner, not a cost interpreter. -/
theorem two_iterations_runner :
    (runSteps 34 (gcdConfig 24 18)).result.values? = some [.i32 6] := by rfl

end Wasm.Examples.Gcd.Cost
