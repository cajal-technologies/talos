import CodeLib.SepLogic.SmallStepTotalLifting
import CodeLib.SepLogic.ByteSlice

/-!
# The `memory.copy` rule over byte slices

`Wasm.SmallStep.twp_memoryCopy32` in
`CodeLib/SepLogic/SmallStepTotalLifting.lean` is the total-WP rule for
`memory.copy`.  It takes two bare `pointsToBytes` resources and two
no-wrap facts.  Body proofs hold their memory as
`Wasm.SepLogic.Slices.ByteSlice`, which packs a `pointsToBytes` with the
no-wrap fact of the same range.  Each call site therefore opens the two
slices, applies the rule, and packs the two results again.

`twp_memoryCopy32_slices` is that rule over slices.  It states the same
step and keeps the three length hypotheses.

## The two hypotheses that the slices give

`twp_memoryCopy32` asks for `hnowrap_dst` and `hnowrap_src`.  This rule
drops both.  The source slice carries
`source.toNat + srcBytes.length < UInt32.size` and `hlen_src` rewrites
the length to `len.toNat`.  The destination slice carries the same fact
for `destination` and `oldDstBytes`, and `hlen_dst` rewrites it the same
way.

The destination slice comes back with the source bytes in it.  The
no-wrap fact still holds, because `hlen_dst` and `hlen_src` say that
`srcBytes` and `oldDstBytes` have the same length.

## Why there is no zero-length companion

`twp_memoryCopy32` has no zero-length form, so this file states none.
The rule keeps `hpos`.

## Consumer

The small sort of the quicksort body copies the sorted frame back to the
buffer at WAT lines 8648 to 8651 of
`programs/rust/build/rust_hash_map/program.wat`, with `dst = buf`,
`src = frame` and a length of `8 * len` bytes for `len` at most 32.  The
branch at WAT lines 8642 to 8647 skips the copy when `len * 8` is zero,
so `hpos` holds at the call.
-/

namespace Wasm.SmallStep

open Iris Iris.ProgramLogic Language.Notation
open Wasm.SepLogic

section terminalGenericSliceCopy

variable {hlc : outParam HasLC} {α : Type}
variable [WasmSmallStepGS hlc α]
variable {Terminal : Type}
variable [view : TerminalView α Terminal]
local instance (priority := high) activeTerminalLanguageSliceCopy :
    Language (Expr α) (MachineStore α) StepKind Terminal :=
  TerminalView.canonicalLanguage
local instance (priority := high) activeTerminalIrisGSSliceCopy :
    @IrisGS_gen hlc (Expr α) Terminal (MachineStore α) StepKind
      activeTerminalLanguageSliceCopy (WasmHeapGF α) :=
  { numLatersPerStep _ := 0
    forkPost _ := iprop(True)
    stateInterp_mono _ _ _ _ := by iintro $ }
variable {s : Stuckness} {E : CoPset}
variable {Φ : Terminal → IProp (WasmHeapGF α)}

/-- Total rule for `memory.copy` over two byte slices of memory `0`.  The
source slice comes back unchanged and the destination slice comes back
with the source bytes in it.  The two no-wrap hypotheses of
`twp_memoryCopy32` are absent, because the two slices carry them. -/
theorem twp_memoryCopy32_slices
    {params localValues values : List Value}
    {destination source len : UInt32}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (oldDstBytes srcBytes : List UInt8)
    (hlen_dst : oldDstBytes.length = len.toNat)
    (hlen_src : srcBytes.length = len.toNat)
    (hpos : 0 < len.toNat) :
    Slices.ByteSlice 0 source srcBytes -∗
    Slices.ByteSlice 0 destination oldDstBytes -∗
    (Slices.ByteSlice 0 source srcBytes -∗
      Slices.ByteSlice 0 destination srcBytes -∗
      WP (Expr.running ⟨⟨params, localValues, values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }]) -∗
    WP (Expr.running ⟨⟨params, localValues,
        .i32 len :: .i32 source :: .i32 destination :: values⟩,
        .memoryCopy :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro Hsrc Hdst Htwp
  isimp only [Slices.ByteSlice] at Hsrc Hdst
  icases Hsrc with ⟨%hnowrap_src, Hsrc⟩
  icases Hdst with ⟨%hnowrap_dst, Hdst⟩
  have hsize : UInt32.size = 4294967296 := rfl
  iapply twp_memoryCopy32 oldDstBytes srcBytes hlen_dst hlen_src hpos
    (by omega) (by omega) $$ Hsrc Hdst
  iintro Hsrc Hdst
  ihave Hsrc : Slices.ByteSlice 0 source srcBytes $$ [Hsrc]
  · isimp only [Slices.ByteSlice]
    isplitl_pureexact hnowrap_src
    · iexact Hsrc
  ihave Hdst : Slices.ByteSlice 0 destination srcBytes $$ [Hdst]
  · isimp only [Slices.ByteSlice]
    isplitl_pureexact (by omega)
    · iexact Hdst
  iapply Htwp $$ Hsrc Hdst

end terminalGenericSliceCopy

end Wasm.SmallStep
