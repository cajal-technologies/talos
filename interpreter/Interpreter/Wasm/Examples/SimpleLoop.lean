import Interpreter.Wasm.SmallStep
import Interpreter.Wasm.Examples.UIntLemmas
import Mathlib.Tactic

/-! ## Example: Simple countdown loop

The loop moves one unit from the parameter counter to the local accumulator.
Its relational invariant is the modular `UInt32` sum `x + y`; termination is
proved independently with the strictly decreasing measure `x.toNat`.
-/

namespace Wasm
open SmallStep

def SimpleLoop : Program := [
  .const 0,
  .localSet 1,
  .loop 0 0 [
    .block 0 0 [
      .block 0 0 [
        .localGet 0,
        .br_if 0,
        .br 1
      ],
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
  ],
  .localGet 1
]

def simpleLoopModule : Module :=
  { funcs := [{
      params := [.i32]
      results := [.i32]
      locals := [.i32]
      body := SimpleLoop }] }

def simpleLoopConfig (n : UInt32) : Config Unit :=
  { expr := .running
      { locals :=
          { params := [.i32 n]
            locals := [.i32 0] }
        code := SimpleLoop
        resultArity := 1
        callerRemainder := [] }
    store :=
      { runtime := { module := simpleLoopModule, host := {} }
        wasm := simpleLoopModule.initialStore } }

private def simpleInnerBody : Program :=
  [.localGet 0, .br_if 0, .br 1]

private def simpleOuterBody : Program := [
  .block 0 0 simpleInnerBody,
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

private def simpleLoopBody : Program :=
  [.block 0 0 simpleOuterBody]

private def simpleLoopFrame : ControlFrame :=
  { kind := .loop
    paramArity := 0
    resultArity := 0
    body := simpleLoopBody
    continuation := [.localGet 1]
    belowStack := [] }

private def simpleLoopHead (x y : UInt32) : Config Unit :=
  { expr := .running
      { locals :=
          { params := [.i32 x]
            locals := [.i32 y] }
        code := simpleLoopBody
        resultArity := 1
        callerRemainder := []
        control := [simpleLoopFrame] }
    store := (simpleLoopConfig x).store }

private theorem simpleLoop_zero_steps (y : UInt32) :
    ∃ trace,
      Steps (simpleLoopHead 0 y) trace
        ⟨.done [.i32 y], (simpleLoopConfig 0).store⟩ := by
  refine ⟨[
    .instruction (.block 0 0 simpleOuterBody),
    .instruction (.block 0 0 simpleInnerBody),
    .instruction (.localGet 0),
    .instruction (.br_if 0),
    .instruction (.br 1),
    .administrative .exitControl,
    .instruction (.localGet 1),
    .administrative .finish], ?_⟩
  apply Steps.cons .block
  apply Steps.cons .block
  apply Steps.cons (.localGet rfl)
  apply Steps.cons .brIfZero
  apply Steps.cons (.br rfl)
  apply Steps.cons (.exitControl rfl)
  apply Steps.cons (.localGet rfl)
  exact Steps.single .finish

private theorem simpleLoop_iteration_steps (x y : UInt32)
    (hx : x ≠ 0) :
    ∃ trace,
      Steps (simpleLoopHead x y) trace
        (simpleLoopHead (x - 1) (1 + y)) := by
  refine ⟨[
    .instruction (.block 0 0 simpleOuterBody),
    .instruction (.block 0 0 simpleInnerBody),
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
    .instruction (.br 1)], ?_⟩
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

private theorem simpleLoopHead_steps (x y : UInt32) :
    ∃ trace,
      Steps (simpleLoopHead x y) trace
        ⟨.done [.i32 (x + y)], (simpleLoopConfig x).store⟩ := by
  induction h : x.toNat using Nat.strong_induction_on generalizing x y with
  | h n ih =>
    subst n
    by_cases hx : x = 0
    · subst x
      simpa using simpleLoop_zero_steps y
    · have hxn : x.toNat ≠ 0 := by
        intro hz
        exact hx (UInt32.toNat.inj hz)
      have hpred : (x - 1).toNat < x.toNat := by
        rw [UInt32.toNat_sub_one_eq hxn]
        omega
      obtain ⟨initialTrace, hinitial⟩ :=
        simpleLoop_iteration_steps x y hx
      obtain ⟨suffix, hsuffix⟩ :=
        ih (x - 1).toNat hpred (x - 1) (1 + y) rfl
      have hvalue : (x - 1) + (1 + y) = x + y := by
        have hcancel : (-1 : UInt32) + 1 = 0 := by decide
        rw [UInt32.sub_eq_add_neg, UInt32.add_assoc,
          ← UInt32.add_assoc (-1) 1 y, hcancel, UInt32.zero_add]
      rw [hvalue] at hsuffix
      exact ⟨initialTrace ++ suffix, Steps.trans hinitial hsuffix⟩

private theorem simpleLoop_initial_steps (n : UInt32) :
    Steps (simpleLoopConfig n)
      [.instruction (.const 0), .instruction (.localSet 1),
        .instruction (.loop 0 0 simpleLoopBody)]
      (simpleLoopHead n 0) :=
  Steps.cons .const
    (Steps.cons (.localSet rfl) (Steps.single .loop))

theorem simpleLoop_steps (n : UInt32) :
    ∃ trace,
      Steps (simpleLoopConfig n) trace
        ⟨.done [.i32 n], (simpleLoopConfig n).store⟩ := by
  obtain ⟨suffix, hsuffix⟩ := simpleLoopHead_steps n 0
  exact ⟨_ ++ suffix,
    Steps.trans (simpleLoop_initial_steps n) (by simpa using hsuffix)⟩

theorem simpleLoopSpec (n : UInt32) :
    TerminatesWith (simpleLoopConfig n)
      (fun values _ => values = [.i32 n]) := by
  obtain ⟨trace, execution⟩ := simpleLoop_steps n
  exact ⟨trace, _, _, execution, rfl⟩

theorem simpleLoopPartial (n : UInt32) :
    PartiallyMeets (simpleLoopConfig n)
      (fun values _ => values = [.i32 n]) := by
  intro trace values store observed
  obtain ⟨expectedTrace, expected⟩ := simpleLoop_steps n
  obtain ⟨rfl, rfl⟩ := steps_done_deterministic expected observed
  rfl

end Wasm
