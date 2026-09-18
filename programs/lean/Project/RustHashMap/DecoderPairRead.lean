import Project.RustHashMap.DecoderOkReturn

/-!
# The borsh decoder: the pair read

Eight or more unread bytes takes one loop step to
`Project.RustHashMap.Decoder.pairRead`, WAT lines 745 to 761.  The read
takes eight bytes off the slice in one step:

1. The length in the slice header goes down by eight and the cursor goes
   up by eight.
2. Local 11 keeps the new cursor and local 6 takes it after the load.
3. Local 12 takes the value, the second word of the pair, from
   `cursor + 4`.

The key itself was read by `keyRead` before the branch that reaches this
fragment, so the read here is the value alone.  `keyRead` also wrote the
slice header with a step of four; this fragment overwrites both words with
the step of eight, so those two writes are dead.

The fragment holds no branch, so the lemma holds for any control stack.
-/

namespace Project.RustHashMap.Decoder

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open Project.RustHashMap.BodyContracts
open Project.RustHashMap.FrameCells
open scoped Wasm.SmallStep.Outcome

/-- `.const 4294967288` is minus eight. -/
private theorem sub_eight (x : UInt32) : x + 4294967288 = x - 8 := by
  have hmax : (4294967288 : UInt32) = 0 - 8 := by decide
  calc x + 4294967288 = (x - 8 + 8) + (0 - 8) := by
        rw [UInt32.sub_add_cancel, hmax]
    _ = (x - 8) + ((0 - 8) + 8) := by ac_rfl
    _ = x - 8 := by rw [UInt32.sub_add_cancel, UInt32.add_zero]

set_option maxHeartbeats 2000000 in
/-- The pair read takes eight bytes off the slice and loads the value. -/
theorem twp_pair_read [WasmSmallStepGS hlc Universal.State]
    (out hdr frame cursor remaining value oldPtr oldLen : UInt32)
    (l3 l4 l7 l8 l9 l10 l11 l12 : Value)
    {stack : List Value} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp}
    (hhdrNowrap : hdr.toNat + 8 < UInt32.size)
    (hcursorNowrap : cursor.toNat + 8 < UInt32.size) :
    iprop(
      pointsTo_u32 0 hdr oldPtr ∗
      pointsTo_u32 0 (hdr + 4) oldLen ∗
      pointsTo_u32 0 (cursor + 4) value ∗
      (pointsTo_u32 0 hdr (cursor + 8) -∗
        pointsTo_u32 0 (hdr + 4) (remaining - 8) -∗
        pointsTo_u32 0 (cursor + 4) value -∗
        WP (.running
            ⟨⟨[.i32 out, .i32 hdr],
                [.i32 frame, l3, l4, .i32 (remaining - 8), .i32 (cursor + 8),
                  l7, l8, l9, l10, .i32 (cursor + 8), .i32 value],
              stack⟩,
              code, arity, remainder, controls, calls⟩
            : Expr Universal.State) @ s; E [{ Φ }])) ⊢
      WP (.running
          ⟨⟨[.i32 out, .i32 hdr],
              [.i32 frame, l3, l4, .i32 remaining, .i32 cursor, l7, l8, l9,
                l10, l11, l12],
            stack⟩,
            pairRead ++ code, arity, remainder, controls, calls⟩
          : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hptr, Hlen, Hvalue, Hcont⟩
  obtain ⟨hf4, hf4a, hf4b, hf4c⟩ := offset_facts hdr 4 4 rfl (by omega)
  obtain ⟨hf0, hf0a, hf0b, hf0c⟩ := offset_facts hdr 0 0 rfl (by omega)
  obtain ⟨hc4, hc4a, hc4b, hc4c⟩ := offset_facts cursor 4 4 rfl (by omega)
  have hzero : hdr + 0 = hdr := UInt32.add_zero hdr
  simp only [pairRead, List.cons_append, List.nil_append]
  -- the new length goes into the slice header
  wasm_twp_pures [twp_localGet twp_localGet twp_const twp_add]
  rw [UInt32.add_comm (4294967288 : UInt32), sub_eight]
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_rebind twp_store32 (address := hdr) (offset := 4) oldLen
    hf4 hf4a hf4b hf4c with Hlen
  -- the new cursor goes into the slice header
  wasm_twp_pures [twp_localGet twp_localGet twp_const twp_add]
  rw [show (8 : UInt32) + cursor = cursor + 8 from UInt32.add_comm _ _]
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  ihave Hptr := word_move hdr (hdr + 0) oldPtr hzero $$ Hptr
  wasm_twp_rebind twp_store32 (address := hdr) (offset := 0) oldPtr
    hf0 hf0a hf0b hf0c with Hptr
  ihave Hptr := word_move (hdr + 0) hdr (cursor + 8) hzero.symm $$ Hptr
  -- the value of the pair
  wasm_twp_pures [twp_localGet]
  wasm_twp_rebind twp_load32 (address := cursor) (offset := 4) value
    hc4 hc4a hc4b hc4c with Hvalue
  wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_localGet]
  wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  iapply Hcont $$ Hptr Hlen Hvalue

end Project.RustHashMap.Decoder
