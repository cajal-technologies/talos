import Interpreter.Wasm.SmallStep
import Mathlib.Tactic

/-! ## Example: Euclidean GCD

The second parameter is the well-founded measure. A nonzero iteration performs
`(a, b) ↦ (b, a % b)` as one explicit instruction-granular trace; the zero
trace exits the loop and returns `a`.
-/

namespace Wasm
open SmallStep

def Gcd : Program := [
  .loop 0 0 [
    .block 0 0 [
      .localGet 1,
      .eqz,
      .br_if 0,
      .localGet 0,
      .localGet 1,
      .remU,
      .localSet 2,
      .localGet 1,
      .localSet 0,
      .localGet 2,
      .localSet 1,
      .br 1
    ]
  ],
  .localGet 0
]

def gcdModule : Module :=
  { funcs := [{
      params := [.i32, .i32]
      results := [.i32]
      locals := [.i32]
      body := Gcd }] }

def gcdConfig (a b : UInt32) : Config Unit :=
  { expr := .running
      { locals :=
          { params := [.i32 a, .i32 b]
            locals := [.i32 0] }
        code := Gcd
        resultArity := 1
        callerRemainder := [] }
    store :=
      { runtime := { module := gcdModule, host := {} }
        wasm := gcdModule.initialStore } }

private def gcdBlockBody : Program := [
  .localGet 1,
  .eqz,
  .br_if 0,
  .localGet 0,
  .localGet 1,
  .remU,
  .localSet 2,
  .localGet 1,
  .localSet 0,
  .localGet 2,
  .localSet 1,
  .br 1
]

private def gcdLoopBody : Program :=
  [.block 0 0 gcdBlockBody]

private def gcdLoopFrame : ControlFrame :=
  { kind := .loop
    paramArity := 0
    resultArity := 0
    body := gcdLoopBody
    continuation := [.localGet 0]
    belowStack := [] }

private def gcdLoopConfig (a b temporary : UInt32) : Config Unit :=
  { expr := .running
      { locals :=
          { params := [.i32 a, .i32 b]
            locals := [.i32 temporary] }
        code := gcdLoopBody
        resultArity := 1
        callerRemainder := []
        control := [gcdLoopFrame] }
    store := (gcdConfig a b).store }

private theorem gcdLoop_zero_steps (a temporary : UInt32) :
    ∃ trace,
      Steps (gcdLoopConfig a 0 temporary) trace
        ⟨.done [.i32 a], (gcdConfig a 0).store⟩ := by
  refine ⟨[
    .instruction (.block 0 0 gcdBlockBody),
    .instruction (.localGet 1),
    .instruction .eqz,
    .instruction (.br_if 0),
    .administrative .exitControl,
    .instruction (.localGet 0),
    .administrative .finish], ?_⟩
  apply Steps.cons .block
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.eqz rfl)
  apply Steps.cons (.brIf (by decide) (by rfl))
  apply Steps.cons (.exitControl rfl)
  apply Steps.cons (.localGet rfl)
  exact Steps.single .finish

private theorem gcdLoop_iteration_steps (a b temporary : UInt32)
    (hb : b ≠ 0) :
    ∃ trace,
      Steps (gcdLoopConfig a b temporary) trace
        (gcdLoopConfig b (a % b) (a % b)) := by
  refine ⟨[
    .instruction (.block 0 0 gcdBlockBody),
    .instruction (.localGet 1),
    .instruction .eqz,
    .instruction (.br_if 0),
    .instruction (.localGet 0),
    .instruction (.localGet 1),
    .instruction .remU,
    .instruction (.localSet 2),
    .instruction (.localGet 1),
    .instruction (.localSet 0),
    .instruction (.localGet 2),
    .instruction (.localSet 1),
    .instruction (.br 1)], ?_⟩
  apply Steps.cons .block
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.eqz (result := 0) (by simp [hb]))
  apply Steps.cons .brIfZero
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.remU hb)
  apply Steps.cons (.localSet rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.localSet rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons (.localSet rfl)
  exact Steps.single (.br rfl)

private theorem gcdLoop_steps (a b temporary : UInt32) :
    ∃ trace,
      Steps (gcdLoopConfig a b temporary) trace
        ⟨.done [.i32 (UInt32.ofNat (Nat.gcd a.toNat b.toNat))],
          (gcdConfig a b).store⟩ := by
  induction h : b.toNat using Nat.strong_induction_on
      generalizing a b temporary with
  | h n ih =>
    subst n
    by_cases hb : b = 0
    · subst b
      simpa [Nat.gcd_zero_right, UInt32.ofNat_toNat] using
        gcdLoop_zero_steps a temporary
    · have hbpos : 0 < b.toNat := by
        rcases Nat.eq_zero_or_pos b.toNat with hz | hp
        · exact absurd (UInt32.toNat.inj hz) hb
        · exact hp
      have hmod : (a % b).toNat < b.toNat := by
        simpa using Nat.mod_lt a.toNat hbpos
      obtain ⟨initialTrace, hinitial⟩ :=
        gcdLoop_iteration_steps a b temporary hb
      obtain ⟨suffix, hsuffix⟩ :=
        ih (a % b).toNat hmod b (a % b) (a % b) rfl
      have hgcd :
          Nat.gcd b.toNat (a.toNat % b.toNat) =
            Nat.gcd a.toNat b.toNat := by
        rw [Nat.gcd_comm b.toNat (a.toNat % b.toNat),
          Nat.gcd_comm a.toNat b.toNat, Nat.gcd_rec b.toNat a.toNat]
      have hvalue :
          UInt32.ofNat (Nat.gcd b.toNat (a % b).toNat) =
            UInt32.ofNat (Nat.gcd a.toNat b.toNat) :=
        congrArg UInt32.ofNat (by simpa using hgcd)
      rw [hvalue] at hsuffix
      exact ⟨initialTrace ++ suffix, Steps.trans hinitial hsuffix⟩

private theorem gcd_initial_steps (a b : UInt32) :
    Steps (gcdConfig a b)
      [.instruction (.loop 0 0 gcdLoopBody)]
      (gcdLoopConfig a b 0) :=
  Steps.single .loop

theorem gcd_steps (a b : UInt32) :
    ∃ trace,
      Steps (gcdConfig a b) trace
        ⟨.done [.i32 (UInt32.ofNat (Nat.gcd a.toNat b.toNat))],
          (gcdConfig a b).store⟩ := by
  obtain ⟨suffix, hsuffix⟩ := gcdLoop_steps a b 0
  exact ⟨_ ++ suffix, Steps.trans (gcd_initial_steps a b) hsuffix⟩

theorem gcdSpec (a b : UInt32) :
    TerminatesWith (gcdConfig a b)
      (fun values _ =>
        values = [.i32 (UInt32.ofNat (Nat.gcd a.toNat b.toNat))]) := by
  obtain ⟨trace, execution⟩ := gcd_steps a b
  exact ⟨trace, _, _, execution, rfl⟩

theorem gcdPartial (a b : UInt32) :
    PartiallyMeets (gcdConfig a b)
      (fun values _ =>
        values = [.i32 (UInt32.ofNat (Nat.gcd a.toNat b.toNat))]) := by
  intro trace values store observed
  obtain ⟨expectedTrace, expected⟩ := gcd_steps a b
  obtain ⟨rfl, rfl⟩ := steps_done_deterministic expected observed
  rfl

end Wasm
