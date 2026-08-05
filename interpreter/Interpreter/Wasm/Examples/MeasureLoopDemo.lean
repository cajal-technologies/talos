import Interpreter.Wasm.MeasureTermination
import Interpreter.Wasm.Examples.SimpleLoop
import Interpreter.Wasm.Examples.UIntLemmas
import Mathlib.Tactic

/-! ## Demo: the countdown loop, terminated by `terminatesWith_of_loop`

This reproves `Examples/SimpleLoop.lean`'s `simpleLoopSpec`, about the very
same `simpleLoopConfig`, with one difference: where that file writes out a
`Nat.strong_induction_on` over `x.toNat` and reassembles the trace by hand,
this one supplies the two branches and applies
`SmallStep.terminatesWith_of_loop`.

The per-iteration trace lemmas are unchanged in character — those are the
genuine semantic content and no lemma can remove them. What disappears is the
induction skeleton, which is currently duplicated across `SimpleLoop`, `Gcd`,
`Factorial`, and `EvenOddRec`.

The module, config and spec statement are imported so the comparison is exact.
The loop-head decomposition below is restated only because `SimpleLoop`'s own
copies of it are `private`.
-/

namespace Wasm.MeasureLoopDemo

open SmallStep

private def innerBody : Program :=
  [.localGet 0, .br_if 0, .br 1]

private def outerBody : Program := [
  .block 0 0 innerBody,
  .localGet 1,
  .const 1,
  .add,
  .localSet 1,
  .localGet 0,
  .const 1,
  .sub,
  .localSet 0,
  .br 1
]

private def loopBody : Program :=
  [.block 0 0 outerBody]

private def loopFrame : ControlFrame :=
  { kind := .loop
    paramArity := 0
    resultArity := 0
    body := loopBody
    continuation := [.localGet 1]
    belowStack := [] }

/-- The loop head, indexed by the live counter and accumulator. This pair is
the loop state, and `terminatesWith_of_loop` is instantiated at it. -/
private def head (x y : UInt32) : Config Unit :=
  { expr := .running
      { locals :=
          { params := [.i32 x]
            locals := [.i32 y] }
        code := loopBody
        resultArity := 1
        callerRemainder := []
        control := [loopFrame] }
    store := (simpleLoopConfig x).store }

/-- Exit branch: the counter is zero, the accumulator is the result. -/
private theorem zero_steps (y : UInt32) :
    Steps (head 0 y) [
      .instruction (.block 0 0 outerBody),
      .instruction (.block 0 0 innerBody),
      .instruction (.localGet 0),
      .instruction (.br_if 0),
      .instruction (.br 1),
      .administrative .exitControl,
      .instruction (.localGet 1),
      .administrative .finish]
      ⟨.done [.i32 y], (simpleLoopConfig 0).store⟩ := by
  apply Steps.cons .block
  apply Steps.cons .block
  apply Steps.cons (.localGet rfl)
  apply Steps.cons .brIfZero
  apply Steps.cons (.br rfl)
  apply Steps.cons (.exitControl rfl)
  apply Steps.cons (.localGet rfl)
  exact Steps.single .finish

/-- Iteration branch: one unit moves from the counter to the accumulator. -/
private theorem iteration_steps (x y : UInt32) (hx : x ≠ 0) :
    Steps (head x y) [
      .instruction (.block 0 0 outerBody),
      .instruction (.block 0 0 innerBody),
      .instruction (.localGet 0),
      .instruction (.br_if 0),
      .instruction (.localGet 1),
      .instruction (.const 1),
      .instruction .add,
      .instruction (.localSet 1),
      .instruction (.localGet 0),
      .instruction (.const 1),
      .instruction .sub,
      .instruction (.localSet 0),
      .instruction (.br 1)]
      (head (x - 1) (1 + y)) := by
  apply Steps.cons .block
  apply Steps.cons .block
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.brIf hx (by rfl))
  simp only [List.take_zero, List.drop_zero, List.nil_append]
  apply Steps.cons (.localGet rfl)
  apply Steps.cons .const
  apply Steps.cons .add
  apply Steps.cons (.localSet rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons .const
  apply Steps.cons .sub
  apply Steps.cons (.localSet rfl)
  simp
  exact Steps.single (.br rfl)

/-- Termination of the loop head, with no induction written by hand: the
variant is `x.toNat`, the two branches are the lemmas above, and
`terminatesWith_of_loop` supplies the recursion. -/
private theorem head_terminates (x y : UInt32) :
    TerminatesWith (head x y)
      (fun values _ => values = [.i32 (x + y)]) := by
  refine terminatesWith_of_loop
    (configs := fun state : UInt32 × UInt32 => head state.1 state.2)
    (μ := fun state => state.1.toNat)
    (post := fun state values _ => values = [.i32 (state.1 + state.2)])
    ?exit ?iterate (x, y)
  case exit =>
    rintro ⟨x, y⟩ hzero
    simp only at hzero
    have hx : x = 0 := UInt32.toNat.inj hzero
    subst hx
    exact ⟨_, _, _, zero_steps y, by simp⟩
  case iterate =>
    rintro ⟨x, y⟩ hnonzero
    simp only at hnonzero
    have hx : x ≠ 0 := by
      intro hz
      exact hnonzero (by simp [hz])
    refine ⟨(x - 1, 1 + y), _, ?_, iteration_steps x y hx, ?_⟩
    · show (x - 1).toNat < x.toNat
      have hxn : x.toNat ≠ 0 := by
        intro hz
        exact hx (UInt32.toNat.inj hz)
      rw [UInt32.toNat_sub_one_eq hxn]
      omega
    · intro values store hpost
      refine hpost.trans ?_
      have hcancel : (-1 : UInt32) + 1 = 0 := by decide
      have : (x - 1) + (1 + y) = x + y := by
        rw [UInt32.sub_eq_add_neg, UInt32.add_assoc,
          ← UInt32.add_assoc (-1) 1 y, hcancel, UInt32.zero_add]
      simp [this]

/-- Entry into the loop: the prologue that zeroes the accumulator. -/
private theorem initial_steps (n : UInt32) :
    Steps (simpleLoopConfig n)
      [.instruction (.const 0), .instruction (.localSet 1),
        .instruction (.loop 0 0 loopBody)]
      (head n 0) :=
  Steps.cons .const (Steps.cons (.localSet rfl) (Steps.single .loop))

/-- The specification, symbolic in the input: `SimpleLoop.simpleLoopSpec`
restated, proved through `terminatesWith_of_loop`. -/
theorem spec (n : UInt32) :
    TerminatesWith (simpleLoopConfig n) (fun values _ => values = [.i32 n]) := by
  refine TerminatesWith.prependSteps (initial_steps n) ?_
  refine (head_terminates n 0).mono ?_
  intro values store hpost
  simpa using hpost

end Wasm.MeasureLoopDemo
