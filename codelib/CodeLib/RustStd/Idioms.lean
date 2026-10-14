import CodeLib.SepLogic.SmallStepTotalLifting

/-!
# Rust-compiled Wasm idioms

Contextual total-WP lemmas for instruction sequences produced by Rust's
LLVM backend at `opt-level = 0`.  Each rule packages exactly the steps the
programs apply manually today.

**Rule sources**

* `twp_rustc_prologue`: `HexDecodeStdio/DecodeCore.lean` and
  `Project/Mergesort/DriverProof.lean`
* `twp_rustc_prologue_set`: `Project/FloatReinterpret/Spec.lean`,
  `Project/FloatRound/Spec.lean`, `Project/NumInteger/Spec.lean` and
  `Project/SwapElements/SwapSepLogic.lean`
* `twp_rustc_epilogue`: `HexDecodeStdio/DecodeCore.lean` and
  `Project/GcdStdio/DriverProof.lean`
-/

namespace Wasm.SmallStep

open Iris Iris.ProgramLogic Language.Notation
open Wasm.SepLogic

section

variable [WasmSmallStepGS hlc α]
variable {Terminal : Type}
variable [view : TerminalView α Terminal]
local instance (priority := high) idioms_terminalLanguage :
    Language (Expr α) (MachineStore α) StepKind Terminal :=
  TerminalView.canonicalLanguage
local instance (priority := high) idioms_terminalIrisGS :
    @IrisGS_gen hlc (Expr α) Terminal (MachineStore α) StepKind
      idioms_terminalLanguage (WasmHeapGF α) :=
  { numLatersPerStep _ := 0
    forkPost _ := iprop(True)
    stateInterp_mono _ _ _ _ := by iintro $ }
variable {s : Stuckness} {E : CoPset}
variable {Φ : Terminal → IProp (WasmHeapGF α)}

private theorem set?_values {ls : Locals} {i : Nat} {v : Value} {ls' : Locals}
    (h : ls.set? i v = some ls') : ls'.values = ls.values := by
  simp only [Locals.set?] at h
  by_cases h1 : i < ls.params.length
  · simp only [h1, ↓reduceIte, Option.some.injEq] at h; subst h; rfl
  · by_cases h2 : i < ls.params.length + ls.locals.length
    · simp only [h1, h2, ↓reduceIte, Option.some.injEq] at h; subst h; rfl
    · simp only [h1, h2, ↓reduceIte] at h; contradiction

/-- Shadow-stack prologue (tee form).
    Steps `globalGet 0 :: const N :: sub :: localTee L :: globalSet 0 :: code`.
    Reads `sp` from global 0, computes `sp − N`, writes it to local `L` and
    to global 0.  No no-wrap hypothesis: `sub` wraps on underflow and always
    steps. -/
theorem twp_rustc_prologue
    {params localValues : List Value} {values : List Value}
    {frameSize : UInt32} {localIdx : Nat} {locals' : Locals}
    {sp : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    (hset : (⟨params, localValues, .i32 (sp - frameSize) :: values⟩ : Locals).set?
        localIdx (.i32 (sp - frameSize)) = some locals') :
    globalPointsToAt 0 0 (.i32 sp) -∗
    (globalPointsToAt 0 0 (.i32 (sp - frameSize)) -∗
      WP (Expr.running ⟨⟨locals'.params, locals'.locals, values⟩,
            code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }]) -∗
    WP (Expr.running ⟨⟨params, localValues, values⟩,
          .globalGet 0 :: .const frameSize :: .sub :: .localTee localIdx
            :: .globalSet 0 :: code,
          arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] := by
  have hvals : locals'.values = .i32 (sp - frameSize) :: values := set?_values hset
  iintro Hsp Hcont
  iapply twp_globalGet $$ Hsp; iintro Hsp
  iapply twp_const
  iapply twp_sub
  iapply twp_localTee hset
  have hstruct : locals' = ⟨locals'.params, locals'.locals, .i32 (sp - frameSize) :: values⟩ := by
    obtain ⟨p, l, v⟩ := locals'; subst hvals; rfl
  rw [hstruct]
  iapply twp_globalSet $$ Hsp; iintro Hframe
  iapply Hcont $$ Hframe

private theorem set?_get {ls : Locals} {i : Nat} {v : Value} {ls' : Locals}
    (h : ls.set? i v = some ls') (vs : List Value) :
    (⟨ls'.params, ls'.locals, vs⟩ : Locals).get i = some v := by
  simp only [Locals.set?] at h
  by_cases h1 : i < ls.params.length
  · simp only [h1, ↓reduceIte, Option.some.injEq] at h
    subst h
    simp only [Locals.get, List.length_set, h1, ↓reduceIte]
    exact List.getElem?_set_self h1
  · by_cases h2 : i < ls.params.length + ls.locals.length
    · simp only [h1, h2, ↓reduceIte, Option.some.injEq] at h
      subst h
      simp only [Locals.get, List.length_set, h1, h2, ↓reduceIte]
      exact List.getElem?_set_self (by omega)
    · simp only [h1, h2, ↓reduceIte] at h; contradiction

/-- Shadow-stack prologue (set/get form).
    Steps `globalGet 0 :: const N :: sub :: localSet L :: localGet L ::
    globalSet 0 :: code`.  Rustc sometimes lowers the shadow-stack prologue
    with a plain `local.set` followed by a `local.get` instead of a
    `local.tee`; this rule packages that six-instruction form.  Same
    resources and continuation shape as `twp_rustc_prologue`. -/
theorem twp_rustc_prologue_set
    {params localValues : List Value} {values : List Value}
    {frameSize : UInt32} {localIdx : Nat} {locals' : Locals}
    {sp : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    (hset : (⟨params, localValues, .i32 (sp - frameSize) :: values⟩ : Locals).set?
        localIdx (.i32 (sp - frameSize)) = some locals') :
    globalPointsToAt 0 0 (.i32 sp) -∗
    (globalPointsToAt 0 0 (.i32 (sp - frameSize)) -∗
      WP (Expr.running ⟨⟨locals'.params, locals'.locals, values⟩,
            code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }]) -∗
    WP (Expr.running ⟨⟨params, localValues, values⟩,
          .globalGet 0 :: .const frameSize :: .sub :: .localSet localIdx
            :: .localGet localIdx :: .globalSet 0 :: code,
          arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro Hsp Hcont
  iapply twp_globalGet $$ Hsp; iintro Hsp
  iapply twp_const
  iapply twp_sub
  iapply twp_localSet hset
  iapply twp_localGet (set?_get hset values)
  iapply twp_globalSet $$ Hsp; iintro Hframe
  iapply Hcont $$ Hframe

/-- Shadow-stack epilogue.
    Steps `localGet L :: const N :: add :: globalSet 0 :: code`.
    Reads saved `frame` from local `L`, adds `N` to recover `sp`, and stores
    `sp` back in global 0.
    `hrestore : N + frame = sp` closes by `by decide` for concrete frame sizes. -/
theorem twp_rustc_epilogue
    {params localValues : List Value} {values : List Value}
    {frameSize frame sp : UInt32} {localIdx : Nat} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    (hget : (⟨params, localValues, values⟩ : Locals).get localIdx =
      some (.i32 frame))
    (hrestore : frameSize + frame = sp) :
    globalPointsToAt 0 0 (.i32 frame) -∗
    (globalPointsToAt 0 0 (.i32 sp) -∗
      WP (Expr.running ⟨⟨params, localValues, values⟩,
            code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }]) -∗
    WP (Expr.running ⟨⟨params, localValues, values⟩,
          .localGet localIdx :: .const frameSize :: .add :: .globalSet 0 :: code,
          arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro Hframe Hcont
  iapply twp_localGet hget
  iapply twp_const
  iapply twp_add
  rw [hrestore]
  iapply twp_globalSet $$ Hframe; iintro Hsp
  iapply Hcont $$ Hsp

end

end Wasm.SmallStep
