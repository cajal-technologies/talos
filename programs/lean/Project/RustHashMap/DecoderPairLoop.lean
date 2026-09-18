import Project.RustHashMap.DecoderStep

/-!
# The pair loop of the decoder

`twp_pair_loop` closes the `.loop` of absolute `func 4` with the
well-founded loop rule `Wasm.SmallStep.twp_loop_wf_family`.  The family
index is `LoopState`, the measure is `loopMeasure count.toNat`, and the
body proof is `twp_loop_iteration`.

The measure counts the pairs that the loop has still to read.  Each turn
either raises the index by one, which lowers the measure, or leaves the
loop through one of the three arms of `LoopCont`.  The loop therefore
stops, and the rule needs no later to guard the recursion.
-/

namespace Project.RustHashMap.Decoder

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open Project.RustHashMap.Allocator
open Project.RustHashMap.EntryContracts
open Project.RustHashMap.BodyContracts
open Project.RustHashMap.DecodeErrorContracts
open Project.RustHashMap.PairGrow
open scoped Wasm.SmallStep.Outcome

set_option maxHeartbeats 2000000 in
/-- The pair loop keeps the loop invariant and stops. -/
theorem twp_pair_loop [WasmSmallStepGS hlc Universal.State]
    (out hdr ptr len frame count : UInt32) (heapId : GName)
    (bytes outBefore pad scratch dataBytes : List UInt8)
    (input output : List UInt8) (raised : Bool)
    (arity : Nat) (remainder : List Value)
    (decodeFrame : ControlFrame)
    (errorBody errorCont : Program) (errorBelow : List Value)
    (errorControls : List ControlFrame)
    (calls : List CallFrame) (s : Stuckness) (E : CoPset)
    (Φ : ObservableOutcome → HeapIProp)
    (hlen : bytes.length = len.toNat)
    (hscratchLength : scratch.length = 48)
    (hdataLength : dataBytes.length = dataSegmentSize)
    (hframeLow : func49Depth ≤ frame.toNat)
    (hframeNowrap : frame.toNat + 64 < UInt32.size)
    (hhdrNowrap : hdr.toNat + 8 < UInt32.size)
    (hptrNowrap : ptr.toNat + bytes.length < UInt32.size)
    (initial : LoopState) :
    LoopInv out hdr ptr len frame count heapId bytes outBefore pad scratch
        dataBytes input output raised arity remainder
        (decodeFrame :: allocFrame errorBody errorCont errorBelow ::
          errorControls)
        errorControls errorCont errorBelow calls s E Φ initial ⊢
      WP (.running
        ⟨loopLocals out hdr frame ptr len count initial,
          .loop 0 0 pairLoopBody :: okReturn, arity, remainder,
          decodeFrame :: allocFrame errorBody errorCont errorBelow ::
            errorControls, calls⟩
          : Expr Universal.State) @ s; E [{ Φ }] := by
  iapply Wasm.SmallStep.twp_loop_wf_family
    (ι := LoopState) (measure := loopMeasure count.toNat)
    (locals := loopLocals out hdr frame ptr len count)
    (I := LoopInv out hdr ptr len frame count heapId bytes outBefore pad
      scratch dataBytes input output raised arity remainder
      (decodeFrame :: allocFrame errorBody errorCont errorBelow ::
        errorControls)
      errorControls errorCont errorBelow calls s E Φ)
    (initial := initial)
    (initialLocals := loopLocals out hdr frame ptr len count initial)
    (body := pairLoopBody) (code := okReturn)
    (paramArity := 0) (resultArity := 0)
    (arity := arity) (remainder := remainder)
    (controls := decodeFrame :: allocFrame errorBody errorCont errorBelow ::
      errorControls)
    (calls := calls) (belowStack := []) rfl rfl
  · intro st
    iintro Hrec Hinv
    iapply twp_loop_iteration out hdr ptr len frame count heapId bytes
      outBefore pad scratch dataBytes input output raised arity remainder
      decodeFrame errorBody errorCont errorBelow errorControls calls s E Φ
      hlen hscratchLength hdataLength hframeLow hframeNowrap hhdrNowrap
      hptrNowrap st
    isplitl [Hinv]
    · iexact Hinv
    · iexact Hrec

end Project.RustHashMap.Decoder
