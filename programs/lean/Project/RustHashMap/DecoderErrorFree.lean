import Project.RustHashMap.DecoderErrorStores
import Project.RustHashMap.DeallocNoop

/-!
# The borsh decoder: the free of the error return

The error return ends with the free of the pair buffer, WAT lines 837 to
844.  It reads the capacity word at `frame + 4` into local 3.  A capacity
of zero leaves the outer block at once.  A capacity that is not zero calls
absolute `func 60` with the buffer, `8 * capacity` bytes, and the alignment
4.

The body of absolute `func 60` is empty, so
`Project.RustHashMap.DeallocNoop.Func57NoopSpec` takes the call with the
runtime context alone.  The proof therefore needs no live block and no
allocator.  The caller drops the block that the loop allocated, which is
what `Project.RustHashMap.BodyContracts.Func1Spec` asks for: its rejecting
arm returns no buffer.

Both paths end at the same place, because a block of result arity zero
leaves the same values behind on a branch and on a fall-through.  The
lemma names the control frame, because the branch is inside the fragment
and not at its end.
-/

namespace Project.RustHashMap.Decoder

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open Project.RustHashMap.BodyContracts
open Project.RustHashMap.DeallocNoop
open Project.RustHashMap.FrameCells
open scoped Wasm.SmallStep.Outcome

/-- The free of the pair buffer. -/
def errorFree : Program :=
  [.localGet 2, .load32 4, .localTee 3, .eqz, .br_if 0, .localGet 8,
    .localGet 3, .const 3, .shl, .const 4, .call 60]

/-- The error return is the four writes and the free. -/
theorem errorReturn_free_shape : errorReturn = errorStores ++ errorFree := by
  rfl

set_option maxHeartbeats 2000000 in
/-- The free leaves the outer block and changes nothing that the caller can
see. -/
theorem twp_error_free [WasmSmallStepGS hlc Universal.State]
    (out hdr frame capacity buffer : UInt32)
    (l3 l4 l5 l6 l7 l9 l10 l11 l12 : Value)
    (blockBody afterBlock : Program) (belowStack : List Value)
    {stack : List Value} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp}
    (hframeNowrap : frame.toNat + 64 < UInt32.size) :
    iprop(
      RuntimeContext ∗
      pointsTo_u32 0 (frame + 4) capacity ∗
      (RuntimeContext -∗
        pointsTo_u32 0 (frame + 4) capacity -∗
        WP (.running
            ⟨⟨[.i32 out, .i32 hdr],
                [.i32 frame, .i32 capacity, l4, l5, l6, l7, .i32 buffer, l9,
                  l10, l11, l12],
              belowStack⟩,
              afterBlock, arity, remainder, controls, calls⟩
            : Expr Universal.State) @ s; E [{ Φ }])) ⊢
      WP (.running
          ⟨⟨[.i32 out, .i32 hdr],
              [.i32 frame, l3, l4, l5, l6, l7, .i32 buffer, l9, l10, l11,
                l12],
            stack⟩,
            errorFree, arity, remainder,
            { kind := .block, paramArity := 0, resultArity := 0,
              body := blockBody, continuation := afterBlock,
              belowStack := belowStack } :: controls, calls⟩
          : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hcapacity, Hcont⟩
  obtain ⟨hf4, hf4a, hf4b, hf4c⟩ := offset_facts frame 4 4 rfl (by omega)
  simp only [errorFree]
  wasm_twp_pures [twp_localGet]
  wasm_twp_rebind twp_load32 (address := frame) (offset := 4) capacity
    hf4 hf4a hf4b hf4c with Hcapacity
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  by_cases hempty : capacity = 0
  · -- an empty buffer frees nothing
    iapply twp_eqz (result := 1) (by rw [if_pos hempty])
    iapply twp_brIf (by decide : (1 : UInt32) ≠ 0) (by rfl)
    simp only [List.take_zero, List.nil_append]
    iapply Hcont $$ Hruntime Hcapacity
  · -- a live buffer calls the empty deallocator
    iapply twp_eqz (result := 0) (by rw [if_neg hempty])
    wasm_twp_pures [twp_brIfZero twp_localGet twp_localGet twp_const twp_shl
      twp_const]
    have Hfree : Func57NoopSpec (hlc := hlc) := func57_noop_correct
    unfold Func57NoopSpec CallContract callExpr at Hfree
    simp only [List.cons_append, List.nil_append] at Hfree
    iapply Hfree (ptr := buffer) (size := capacity <<< ((3 : UInt32) % 32))
      (alignment := 4)
      (callerLocals :=
        { params := [.i32 out, .i32 hdr]
          locals := [.i32 frame, .i32 capacity, l4, l5, l6, l7,
            .i32 buffer, l9, l10, l11, l12]
          values := [] })
      (stack := stack)
    isplitl_exact Hruntime
    · iintro Hruntime
      isimp only [ResumeWP, resumeExpr, List.nil_append]
      wasm_twp_pures [twp_exitControl]
        using [List.take_zero, List.nil_append]
      iapply Hcont $$ Hruntime Hcapacity

end Project.RustHashMap.Decoder
