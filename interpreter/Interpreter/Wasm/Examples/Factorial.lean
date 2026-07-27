import Interpreter.Wasm.Examples.UIntLemmas
import Interpreter.Wasm.SmallStep
import Mathlib.Data.Nat.Factorial.Basic

/-! ## Example: Factorial

    Loop with measure `k.toNat` (the counter). Invariant:
    `acc * (k.toNat)! = (n.toNat)!`. -/

namespace Wasm

open SmallStep

def Factorial : Program := [
  .const 1, .localSet 1,
  .loop 0 0 [
    .block 0 0 [
      .localGet 0, .eqz, .br_if 0, -- if n == 0 break
      .localGet 0, .localGet 1, .mul, .localSet 1, -- acc *= n
      .localGet 0, .const 1, .sub, .localSet 0, -- n -= 1
      .br 1 -- repeat
    ]
  ],
  .localGet 1
]

/-! The loop invariant lives at an explicit machine configuration. Each
nonzero iteration is a 13-transition relational trace, while the zero case is
the 7-transition exit trace. -/

def factorialModule : Module :=
  { funcs := [{
      params := [.i32]
      results := [.i32]
      locals := [.i32]
      body := Factorial }] }

def factorialConfig (n : UInt32) : Config Unit :=
  { expr := .running
      { locals := { params := [.i32 n], locals := [.i32 0] }
        code := Factorial
        resultArity := 1
        callerRemainder := [] }
    store :=
      { runtime := { module := factorialModule, host := {} }
        wasm := factorialModule.initialStore } }

private def factorialBlockBody : Program := [
  .localGet 0, .eqz, .br_if 0,
  .localGet 0, .localGet 1, .mul, .localSet 1,
  .localGet 0, .const 1, .sub, .localSet 0,
  .br 1
]

private def factorialLoopBody : Program :=
  [.block 0 0 factorialBlockBody]

private def factorialLoopFrame : ControlFrame :=
  { kind := .loop
    paramArity := 0
    resultArity := 0
    body := factorialLoopBody
    continuation := [.localGet 1]
    belowStack := [] }

private def factorialLoopConfig (x acc : UInt32) : Config Unit :=
  { expr := .running
      { locals := { params := [.i32 x], locals := [.i32 acc] }
        code := factorialLoopBody
        resultArity := 1
        callerRemainder := []
        control := [factorialLoopFrame] }
    store := (factorialConfig x).store }

private theorem factorialLoop_zero_steps (acc : UInt32) :
    ∃ trace,
      Steps (factorialLoopConfig 0 acc) trace
        ⟨.done [.i32 acc], (factorialConfig 0).store⟩ := by
  refine ⟨[
    .instruction (.block 0 0 factorialBlockBody),
    .instruction (.localGet 0),
    .instruction .eqz,
    .instruction (.br_if 0),
    .administrative .exitControl,
    .instruction (.localGet 1),
    .administrative .finish], ?_⟩
  apply Steps.cons .block
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.eqz rfl)
  apply Steps.cons (.brIf (by decide) (by rfl))
  apply Steps.cons (.exitControl rfl)
  apply Steps.cons (.localGet rfl)
  exact Steps.single .finish

private theorem factorialLoop_iteration_steps (x acc : UInt32)
    (hx : x ≠ 0) :
    ∃ trace,
      Steps (factorialLoopConfig x acc) trace
        (factorialLoopConfig (x - 1) (acc * x)) := by
  refine ⟨[
    .instruction (.block 0 0 factorialBlockBody),
    .instruction (.localGet 0),
    .instruction .eqz,
    .instruction (.br_if 0),
    .instruction (.localGet 0),
    .instruction (.localGet 1),
    .instruction .mul,
    .instruction (.localSet 1),
    .instruction (.localGet 0),
    .instruction (.const 1),
    .instruction .sub,
    .instruction (.localSet 0),
    .instruction (.br 1)], ?_⟩
  apply Steps.cons .block
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.eqz (result := 0) (by simp [hx]))
  apply Steps.cons .brIfZero
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons .mul
  apply Steps.cons (.localSet rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons .const
  apply Steps.cons .sub
  apply Steps.cons (.localSet rfl)
  exact Steps.single (.br rfl)

private theorem factorialLoop_steps (x acc : UInt32) :
    ∃ trace,
      Steps (factorialLoopConfig x acc) trace
        ⟨.done [.i32 (UInt32.ofNat (acc.toNat * x.toNat.factorial))],
          (factorialConfig x).store⟩ := by
  induction h : x.toNat using Nat.strong_induction_on generalizing x acc with
  | h n ih =>
    subst n
    by_cases hx : x = 0
    · subst x
      simpa using factorialLoop_zero_steps acc
    · have hxn : x.toNat ≠ 0 := by
        intro hz
        exact hx (UInt32.toNat.inj hz)
      have hpred : (x - 1).toNat < x.toNat := by
        rw [UInt32.toNat_sub_one_eq hxn]
        omega
      obtain ⟨initialTrace, hinitial⟩ :=
        factorialLoop_iteration_steps x acc hx
      obtain ⟨suffix, hsuffix⟩ :=
        ih (x - 1).toNat hpred (x - 1) (acc * x) rfl
      have hxsub := UInt32.toNat_sub_one_eq hxn
      have hxfact :
          x.toNat.factorial = x.toNat * (x.toNat - 1).factorial := by
        rcases hxval : x.toNat with _ | k
        · exact absurd hxval hxn
        · simp [Nat.factorial_succ]
      have hvalue :
          UInt32.ofNat ((acc * x).toNat * (x - 1).toNat.factorial) =
            UInt32.ofNat (acc.toNat * x.toNat.factorial) := by
        apply UInt32.toNat.inj
        simp [UInt32.toNat_mul, hxsub, hxfact]
        rw [Nat.mul_assoc]
      rw [hvalue] at hsuffix
      exact ⟨initialTrace ++ suffix, Steps.trans hinitial hsuffix⟩

private theorem factorial_initial_steps (n : UInt32) :
    Steps (factorialConfig n)
      [.instruction (.const 1), .instruction (.localSet 1),
        .instruction (.loop 0 0 factorialLoopBody)]
      (factorialLoopConfig n 1) := by
  exact Steps.cons .const
    (Steps.cons (.localSet rfl) (Steps.single .loop))

theorem factorial_steps (n : UInt32) :
    ∃ trace,
      Steps (factorialConfig n) trace
        ⟨.done [.i32 (UInt32.ofNat n.toNat.factorial)],
          (factorialConfig n).store⟩ := by
  obtain ⟨suffix, hsuffix⟩ := factorialLoop_steps n 1
  exact ⟨_ ++ suffix,
    Steps.trans (factorial_initial_steps n) (by simpa using hsuffix)⟩

theorem factorialSpec (n : UInt32) :
    TerminatesWith (factorialConfig n)
      (fun values _ =>
        values = [.i32 (UInt32.ofNat n.toNat.factorial)]) := by
  obtain ⟨trace, execution⟩ := factorial_steps n
  exact ⟨trace, _, _, execution, rfl⟩

theorem factorialPartial (n : UInt32) :
    PartiallyMeets (factorialConfig n)
      (fun values _ =>
        values = [.i32 (UInt32.ofNat n.toNat.factorial)]) := by
  intro trace values store observed
  obtain ⟨expectedTrace, expected⟩ := factorial_steps n
  obtain ⟨rfl, rfl⟩ := steps_done_deterministic expected observed
  rfl

end Wasm
