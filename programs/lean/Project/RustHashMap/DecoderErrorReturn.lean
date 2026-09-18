import Project.RustHashMap.DecoderErrorFree

/-!
# The error return of the decoder

`Project.RustHashMap.Decoder.errorReturn` is the four writes and then the
free of the pair buffer.  `twp_error_stores` proves the writes and
`twp_error_free` proves the free, so this file joins the two.

The scratch slot of the frame is 48 bytes and the decode error is its
first 16, so the proof cuts the slot in two, gives the error words to the
writes, and joins the slot again for the caller.

Both paths of the free end at the continuation of the block that holds
the body of the decoder.
-/

namespace Project.RustHashMap.Decoder

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open Project.RustHashMap.BodyContracts
open Project.RustHashMap.FrameCells
open scoped Wasm.SmallStep.Outcome

set_option maxHeartbeats 2000000 in
/-- The error return writes the error into the output slot and frees the
pair buffer. -/
theorem twp_error_return [WasmSmallStepGS hlc Universal.State]
    (out hdr frame capacity buffer word0 v0 v1 v2 v3 : UInt32)
    (outBefore scratchAfter : List UInt8)
    (l3 l4 l5 l6 l7 l9 l10 l12 : Value)
    (blockBody afterBlock : Program) (belowStack : List Value)
    {stack : List Value} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (houtLength : outBefore.length = 16)
    (houtNowrap : out.toNat + 16 < UInt32.size)
    (hframeNowrap : frame.toNat + 64 < UInt32.size) :
    iprop(
      RuntimeContext ∗
      Slices.ByteSlice 0 out outBefore ∗
      Slices.ByteSlice 0 (frame + 16)
        (WordCodec.u32le.serialize [v0, v1, v2, v3] ++ scratchAfter) ∗
      pointsTo_u32 0 (frame + 4) capacity ∗
      (RuntimeContext -∗
        Slices.ByteSlice 0 out
          (WordCodec.u32le.serialize [word0, v1, v2, v3]) -∗
        Slices.ByteSlice 0 (frame + 16)
          (WordCodec.u32le.serialize [v0, v1, v2, v3] ++ scratchAfter) -∗
        pointsTo_u32 0 (frame + 4) capacity -∗
        WP (.running
            ⟨⟨[.i32 out, .i32 hdr],
                [.i32 frame, .i32 capacity, l4, l5, l6, l7, .i32 buffer, l9,
                  l10, .i32 word0, l12],
              belowStack⟩,
              afterBlock, arity, remainder, controls, calls⟩
            : Expr Universal.State) @ s; E [{ Φ }])) ⊢
      WP (.running
          ⟨⟨[.i32 out, .i32 hdr],
              [.i32 frame, l3, l4, l5, l6, l7, .i32 buffer, l9, l10,
                .i32 word0, l12],
            stack⟩,
            errorReturn, arity, remainder,
            { kind := .block, paramArity := 0, resultArity := 0,
              body := blockBody, continuation := afterBlock,
              belowStack := belowStack } :: controls, calls⟩
          : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hout, Hscratch, Hcapacity, Hcont⟩
  ihave ⟨Hslot, Hafter⟩ :=
    (Slices.ByteSlice_append 0 (frame + 16)
      (WordCodec.u32le.serialize [v0, v1, v2, v3]) scratchAfter).mp
      $$ Hscratch
  rw [errorReturn_free_shape]
  iapply twp_error_stores out hdr frame word0 v0 v1 v2 v3 outBefore
    l3 l4 l5 l6 l7 (.i32 buffer) l9 l10 l12 houtLength houtNowrap
    hframeNowrap
  isplitl_exacts [Hout Hslot]
  iintro Hout Hslot
  iapply twp_error_free out hdr frame capacity buffer (.i32 v1) l4 l5 l6 l7
    l9 l10 (.i32 word0) l12 blockBody afterBlock belowStack hframeNowrap
  isplitl_exacts [Hruntime Hcapacity]
  iintro Hruntime Hcapacity
  ihave Hscratch :=
    (Slices.ByteSlice_append 0 (frame + 16)
      (WordCodec.u32le.serialize [v0, v1, v2, v3]) scratchAfter).mpr
      $$ [Hslot Hafter]
  · isplitl_exact Hslot
    · iexact Hafter
  iapply Hcont $$ Hruntime Hout Hscratch Hcapacity

end Project.RustHashMap.Decoder
