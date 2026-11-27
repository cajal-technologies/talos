import CodeLib.CostedSteps
import CodeLib.Examples.Gcd

/-!
# Step bound for Euclidean GCD

Each Euclidean iteration takes thirteen small steps. Loop entry and the final
guard and return take eight more. The existing Iris theorem identifies the
result of this same execution.
-/

namespace Wasm.Examples.Gcd.Cost

open Wasm.SmallStep

/-- Count each instruction or administrative transition once. -/
abbrev work : StepCost Unit := fun _ _ _ => 1

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
  exact ⟨trace, steps.with_unit_cost⟩

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
  exact ⟨trace, steps.with_unit_cost⟩

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
      trace.length = amount ∧ amount ≤ 13 * b.toNat + 8 := by
  obtain ⟨trace, values, store, amount, loop, bound⟩ := loop_bound ⟨a, b, 0⟩
  change amount ≤ 13 * b.toNat + 7 at bound
  have entry : CostedSteps work (gcdConfig a b)
      [.instruction (.loop 0 0 gcdLoopBody)] (head ⟨a, b, 0⟩) 1 :=
    CostedSteps.single Step.loop
  have execution := entry.trans loop
  have result := execution.meets_post (gcd_terminatesWith a b).toPartiallyMeets
  subst values
  exact ⟨_, store, 1 + amount, execution, execution.unit_amount.symm, by omega⟩

/-- The zero-iteration case still charges loop entry, the guard and return. -/
theorem zero_case_exact (a : UInt32) :
    ∃ trace, CostedSteps work (gcdConfig a 0) trace
      ⟨.done [.i32 a], (gcdConfig a 0).store⟩ 8 := by
  obtain ⟨trace, exit⟩ := exit_segment a 0
  have entry : CostedSteps work (gcdConfig a 0)
      [.instruction (.loop 0 0 gcdLoopBody)] (head ⟨a, 0, 0⟩) 1 :=
    CostedSteps.single Step.loop
  exact ⟨_, entry.trans exit⟩

/-- Composing the loop entry, two iteration segments, and the exit segment
gives exactly 34 steps for GCD(24, 18). -/
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
