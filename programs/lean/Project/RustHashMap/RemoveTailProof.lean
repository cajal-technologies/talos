import Project.RustHashMap.RemoveTailContracts
import Project.RustHashMap.RemovePures
import Project.RustHashMap.GetTailProof
import Project.RustHashMap.Func4Proof
import Project.RustHashMap.Func5Proof
import Project.RustHashMap.Func8Proof
import Project.RustHashMap.TailShared

/-!
# The tail of the `map_remove` driver: the proof

`Project.RustHashMap.RemoveTailContracts.RemoveTailSpec` is the contract
of everything after the read phase of absolute `func 9`.  This module
proves it.  `collect_entries`, absolute `func 5`, is the one open
contract; every other callee is a proved theorem.

The proof follows the block structure of
`Project.RustHashMap.RemoveTailDefs`, one lemma per control block, from
the innermost outward.  `Project.RustHashMap.GetTailProof` is the
template, because the `map_get` driver shares the frame size, the read
phase and the key decoder.

## The four frames

`rmOuterFrame` is the block that every path leaves; its continuation is
the stack epilogue.  `rmOkFrame` is the block that the reject guard
leaves; its continuation is the reject arm.  `rmFreeInputFrame`,
`rmFreePairsFrame` and `rmDropErrorFrame` are the three small blocks of
the free tests.  The `map_get` driver has one frame more, because its
reply allocates and tests the result for zero.  This driver allocates in
no block of its own.

## Why the map slot overlaps the decoder output

The driver gives the key decoder a 20-byte output slot at frame offset
16, and then uses the 32 bytes at that same offset as the map value.  So
the accept arm reads the decoder answer as five words, and the collect
call takes the same bytes back as one 32-byte slice.  The `map_get`
driver keeps the two apart, at offsets 32 and 64.
-/

namespace Project.RustHashMap.RemoveTailProof

open Wasm Wasm.RustStd
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open Project.RustHashMap.Allocator
open Project.RustHashMap.AllocatorContracts
open Project.RustHashMap.EntryContracts
open Project.RustHashMap.VecGrow
open Project.RustHashMap.BodyContracts
open Project.RustHashMap.CollectContract
open Project.RustHashMap.EntriesContracts
open Project.RustHashMap.MapOpContracts
open Project.RustHashMap.FrameCells
open Project.RustHashMap.KeyDecoderContract
open Project.RustHashMap.LookupPures
open Project.RustHashMap.RemovePures
open Project.RustHashMap.DeallocNoop
open Project.RustHashMap.Func4Proof
open Project.RustHashMap.Func5Proof
open Project.RustHashMap.Func7Proof
open Project.RustHashMap.Func8Proof
open Project.RustHashMap.ReadAll
open Project.RustHashMap.RemoveRead
open Project.RustHashMap.RemoveTailDefs
open Project.RustHashMap.RemoveTailContracts
open Project.RustHashMap.DriverTail
open Project.RustHashMap.DriverTailProof
open Project.RustHashMap.ContainsKeyTailProof
open Project.RustHashMap.TailShared
open scoped Wasm.SmallStep.Outcome

/-! ## The suffixes of the code

Each call needs the code that follows it as an explicit argument, so each
suffix gets a name. -/

/-- The reply, the free of the pair buffer and the table drop.  WAT lines
1667 to 1713. -/
def rmAfterSort : Program :=
  rmReply ++ .block 0 0 rmFreePairs :: rmTableDrop

/-- The sort call and everything after it.  WAT lines 1660 to 1713. -/
def rmAfterCopyBack : Program := rmSort ++ rmAfterSort

/-- The copy back of the new map value and everything after it.  WAT
lines 1644 to 1713. -/
def rmAfterRemove : Program := rmCopyBack ++ rmAfterCopyBack

/-- The remove kernel and everything after it.  WAT lines 1633 to
1713. -/
def rmAfterCollect : Program := rmRemove ++ rmAfterRemove

/-- The collect call and everything after it.  WAT lines 1628 to 1713. -/
def rmCollectAndRest : Program := rmCollect ++ rmAfterCollect

/-- The accept arm after its guard: the header copy, the release of the
input, and everything after it.  WAT lines 1608 to 1713. -/
def rmOkBody : Program :=
  rmAcceptCopy ++ .block 0 0 rmFreeInput :: rmCollectAndRest

theorem rmOkArm_shape :
    rmOkArm = .localGet 0 :: .load32 16 :: .br_if 0 :: rmOkBody := rfl

/-- The reject arm after the drop of the error string.  WAT lines 1728 to
1734. -/
def rmErrTail : Program :=
  [.localGet 2, .eqz, .br_if 0, .localGet 3, .localGet 2, .const 1,
    .call 60]

theorem rmErrArm_shape :
    rmErrArm = .block 0 0 rmDropError :: rmErrTail := rfl

/-- The outer block and the stack epilogue, which is what follows the
call of the key decoder. -/
def rmAfterDecode (afterTail : Program) : Program :=
  .block 0 0 rmOuterBody :: (rmEpilogue ++ afterTail)

/-- The tail of the driver in cons form, with the decoder call exposed. -/
theorem func6AfterRead_cons (afterTail : Program) :
    func6AfterRead ++ afterTail =
      .localGet 0 :: .const 16 :: .add :: .localGet 3 :: .localGet 1 ::
        .call 10 :: rmAfterDecode afterTail := rfl

/-! ## The control frames of the tail -/

/-- The outermost block of the tail.  Its continuation is the stack
epilogue, so every path that leaves it returns. -/
def rmOuterFrame (afterTail : Program) : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body := rmOuterBody, continuation := rmEpilogue ++ afterTail,
    belowStack := [] }

theorem rmOuterFrame_literal (afterTail : Program) :
    ({ kind := .block, paramArity := 0, resultArity := 0,
       body := rmOuterBody, continuation := rmEpilogue ++ afterTail,
       belowStack := [] } : ControlFrame) = rmOuterFrame afterTail := rfl

/-- The block that the reject guard leaves.  Its continuation is the
reject arm. -/
def rmOkFrame : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body := rmOkArm, continuation := rmErrArm, belowStack := [] }

theorem rmOkFrame_literal :
    ({ kind := .block, paramArity := 0, resultArity := 0,
       body := rmOkArm, continuation := rmErrArm,
       belowStack := [] } : ControlFrame) = rmOkFrame := rfl

/-- The block that releases the input byte vector before the collect
call. -/
def rmFreeInputFrame : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body := rmFreeInput, continuation := rmCollectAndRest,
    belowStack := [] }

theorem rmFreeInputFrame_literal :
    ({ kind := .block, paramArity := 0, resultArity := 0,
       body := rmFreeInput, continuation := rmCollectAndRest,
       belowStack := [] } : ControlFrame) = rmFreeInputFrame := rfl

/-- The block that releases the pair buffer after the reply. -/
def rmFreePairsFrame : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body := rmFreePairs, continuation := rmTableDrop, belowStack := [] }

theorem rmFreePairsFrame_literal :
    ({ kind := .block, paramArity := 0, resultArity := 0,
       body := rmFreePairs, continuation := rmTableDrop,
       belowStack := [] } : ControlFrame) = rmFreePairsFrame := rfl

/-- The block that drops the decoded error string on the reject arm. -/
def rmDropErrorFrame : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body := rmDropError, continuation := rmErrTail, belowStack := [] }

theorem rmDropErrorFrame_literal :
    ({ kind := .block, paramArity := 0, resultArity := 0,
       body := rmDropError, continuation := rmErrTail,
       belowStack := [] } : ControlFrame) = rmDropErrorFrame := rfl

/-! ## Pure helpers

The lemmas below carry no program state.  Each one is a shape that the
template modules state at one address or one depth and that this proof
needs at another. -/

/-- A twelve-byte header that holds three little-endian words is three
cells.  The sorted-entries answer arrives in this shape. -/
private theorem ByteSlice_three_words [WasmHeapGS Universal.State]
    (ptr : UInt32) (w0 w1 w2 : UInt32) :
    Slices.ByteSlice (α := Universal.State) 0 ptr
        (WordCodec.u32le.serialize [w0, w1, w2]) ⊢
      iprop(pointsTo_u32 0 ptr w0 ∗ pointsTo_u32 0 (ptr + 4) w1 ∗
        pointsTo_u32 0 (ptr + 4 + 4) w2) := by
  iintro Hbytes
  isimp only [Slices.ByteSlice] at Hbytes
  icases Hbytes with ⟨%_hnowrap, Hbytes⟩
  ihave Harray :=
    (Slices.arrayAt_eq_wordCells (α := Universal.State) 0 ptr
      [w0, w1, w2]).mpr $$ Hbytes
  isimp only [arrayAt] at Harray
  icases Harray with ⟨H0, H1, H2, _Hemp⟩
  isplitl_exacts [H0 H1]
  iexact H2

/-- The bucket count of the table that `collect_entries` builds.  The
sizing reserves the exact entry count, so the table has one bucket or the
bucket count of that capacity. -/
private theorem buckets_ofEntries_le {K V : Type} [BEq K] [LawfulBEq K]
    (hash : K → UInt64) (es : List (K × V)) (hn : es.length ≤ 2 ^ 30)
    (hmax : es.length ≤ 117440512) :
    (HashMap.Table.ofEntries hash es).buckets ≤ 2 ^ 27 := by
  rw [HashMap.Table.ofEntries_eq]
  have hw0 : HashMap.Table.WF hash (HashMap.Table.empty : HashMap.Table K V) :=
    HashMap.Table.wf_newEmpty ⟨0, by omega, by omega, rfl⟩ hash
  have hcl0 : HashMap.Table.Clean
      (HashMap.Table.empty : HashMap.Table K V) :=
    HashMap.Table.clean_newEmpty 1
  have hc : max ((HashMap.Table.empty : HashMap.Table K V).items + es.length)
      (HashMap.Table.bucketMaskToCapacity
        ((HashMap.Table.empty : HashMap.Table K V).buckets - 1) + 1)
      * 8 / 7 ≤ 2 ^ 32 := by
    show max (0 + es.length) (0 + 1) * 8 / 7 ≤ 2 ^ 32
    omega
  obtain ⟨hw1, hcl1, hperm1, hg1, hb1⟩ := hw0.reserve hcl0 hc
  have htl : HashMap.Table.toList
      (HashMap.Table.empty : HashMap.Table K V) = [] :=
    HashMap.Table.toList_newEmpty 1
  rw [htl] at hperm1
  obtain ⟨-, -, w3, -⟩ :=
    HashMap.Table.insertAll_inv es []
      (HashMap.Table.reserve hash HashMap.Table.empty es.length) hw1 hcl1
      hperm1 hg1
  rw [w3]
  rcases hb1 with hb1 | hb1
  · rw [hb1]
    show 1 ≤ 2 ^ 27
    omega
  · rw [hb1]
    refine HashMap.Table.capBuckets_le_of_le_max ?_
    show max (0 + es.length) (0 + 1) ≤ 117440512
    omega

/-! ## The stack epilogue -/

set_option maxHeartbeats 2000000 in
/-- The stack pointer restore that ends every path.  The driver frame is
320 bytes and the driver declares six locals, the last of them an `i64`,
so this lemma is neither the one of
`Project.RustHashMap.DriverTailProof` nor the one of
`Project.RustHashMap.GetTailProof`.  WAT lines 1736 to 1739. -/
theorem twp_rm_epilogue [WasmSmallStepGS hlc Universal.State]
    {l1 l2 l3 l4 : UInt32} {v5 : UInt64} {afterTail : Program}
    {finalOutput : List UInt8} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp} :
    iprop(RuntimeContext ∗ StackPointer func6Base ∗
      Streams [] finalOutput false ∗
      TailDone finalOutput afterTail arity remainder controls calls
        s E Φ) ⊢
      WP (.running
          ⟨⟨[], [Value.i32 func6Base, .i32 l1, .i32 l2, .i32 l3, .i32 l4,
              .i64 v5], []⟩,
            rmEpilogue ++ afterTail, arity, remainder, controls, calls⟩ :
            Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hstreams, Hcont⟩
  isimp only [StackPointer] at Hsp
  isimp only [TailDone] at Hcont
  simp only [rmEpilogue, List.cons_append, List.nil_append]
  wasm_twp_pures [twp_localGet twp_const twp_add]
  rw [show (320 : UInt32) + func6Base = entryStackTop by decide]
  wasm_twp_rebind twp_globalSet with Hsp
  ihave Hsp : StackPointer entryStackTop $$ [Hsp]
  · unfold StackPointer
    iexact Hsp
  iapply Hcont $$ %(⟨[], [Value.i32 func6Base, .i32 l1, .i32 l2, .i32 l3,
    .i32 l4, .i64 v5], []⟩ : Locals) Hruntime Hsp Hstreams

/-! ## The reject arm -/

set_option maxHeartbeats 2000000 in
/-- The release of the input byte vector on the reject arm.  The last
free of the arm is the last instruction of the outer block, so the arm
leaves the block by running out of code and not by a branch.  WAT lines
1728 to 1734. -/
theorem twp_rm_err_epilogue [WasmSmallStepGS hlc Universal.State]
    {l1 l2 l3 l4 : UInt32} {v5 : UInt64} {afterTail : Program}
    {finalOutput : List UInt8} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp} :
    iprop(RuntimeContext ∗ StackPointer func6Base ∗
      Streams [] finalOutput false ∗
      TailDone finalOutput afterTail arity remainder controls calls
        s E Φ) ⊢
      WP (.running
          ⟨⟨[], [Value.i32 func6Base, .i32 l1, .i32 l2, .i32 l3, .i32 l4,
              .i64 v5], []⟩,
            rmErrTail, arity, remainder,
            rmOuterFrame afterTail :: controls, calls⟩ :
            Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hstreams, Hcont⟩
  simp only [rmErrTail]
  by_cases hcapacity : l2 = 0
  · wasm_twp_pures [twp_localGet]
    iapply twp_eqz (result := 1) (by simp [hcapacity])
    iapply twp_brIf (by decide) (by rfl)
    simp only [rmOuterFrame, List.take_zero, List.nil_append]
    iapply twp_rm_epilogue
    iframe
  · wasm_twp_pures [twp_localGet]
    iapply twp_eqz (result := 0) (by simp [hcapacity])
    wasm_twp_pures [twp_brIfZero twp_localGet twp_localGet twp_const]
    have Hfree := func57_noop_correct (hlc := hlc) l3 l2 1
      (callerLocals :=
        ⟨[], [Value.i32 func6Base, .i32 l1, .i32 l2, .i32 l3, .i32 l4,
          .i64 v5], []⟩)
      (stack := []) (code := []) (arity := arity) (remainder := remainder)
      (controls := rmOuterFrame afterTail :: controls)
      (calls := calls) (s := s) (E := E) (Φ := Φ)
    unfold CallContract callExpr at Hfree
    simp only [List.cons_append, List.nil_append] at Hfree
    iapply Hfree
    isplitl_exact Hruntime
    · iintro Hruntime
      isimp only [ResumeWP, resumeExpr, List.nil_append]
      wasm_twp_pures [twp_exitControl]
      simp only [rmOuterFrame, List.take_zero, List.nil_append]
      iapply twp_rm_epilogue
      iframe

set_option maxHeartbeats 2000000 in
/-- The reject arm.  It drops the decoded error string and releases the
input byte vector.  The driver writes no byte on this arm.  WAT lines
1715 to 1734. -/
theorem twp_rm_reject [WasmSmallStepGS hlc Universal.State]
    (word1 word2 : UInt32)
    {l1 l2 l3 l4 : UInt32} {v5 : UInt64} {afterTail : Program}
    {finalOutput : List UInt8} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp} :
    iprop(RuntimeContext ∗ StackPointer func6Base ∗
      Streams [] finalOutput false ∗
      pointsTo_u32 0 (func6Base + 20) word1 ∗
      pointsTo_u32 0 (func6Base + 24) word2 ∗
      TailDone finalOutput afterTail arity remainder controls calls
        s E Φ) ⊢
      WP (.running
          ⟨⟨[], [Value.i32 func6Base, .i32 l1, .i32 l2, .i32 l3, .i32 l4,
              .i64 v5], []⟩,
            rmErrArm, arity, remainder,
            rmOuterFrame afterTail :: controls, calls⟩ :
            Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hstreams, Hword1, Hword2, Hcont⟩
  have h20 := offset_facts func6Base 20 20 rfl (by decide)
  have h24 := offset_facts func6Base 24 24 rfl (by decide)
  simp only [rmErrArm_shape]
  wasm_twp_pures [twp_block]
  simp only [List.drop_zero]
  rw [rmDropErrorFrame_literal]
  simp only [rmDropError]
  wasm_twp_pures [twp_localGet]
  wasm_twp_rebind twp_load32 (address := func6Base) (offset := 20) word1
    h20.1 h20.2.1 h20.2.2.1 h20.2.2.2 with Hword1
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_const]
  by_cases hshort : word1.toInt32 < (1 : UInt32).toInt32
  · iapply twp_ltS (result := 1) (by rw [if_pos hshort])
    iapply twp_brIf (by decide) (by rfl)
    simp only [rmDropErrorFrame, List.take_zero, List.nil_append]
    iapply twp_rm_err_epilogue
    iframe
  · iapply twp_ltS (result := 0) (by rw [if_neg hshort])
    wasm_twp_pures [twp_brIfZero twp_localGet]
    wasm_twp_rebind twp_load32 (address := func6Base) (offset := 24) word2
      h24.1 h24.2.1 h24.2.2.1 h24.2.2.2 with Hword2
    wasm_twp_pures [twp_localGet twp_const]
    have Hfree := func57_noop_correct (hlc := hlc) word2 word1 1
      (callerLocals :=
        ⟨[], [Value.i32 func6Base, .i32 word1, .i32 l2, .i32 l3, .i32 l4,
          .i64 v5], []⟩)
      (stack := []) (code := []) (arity := arity) (remainder := remainder)
      (controls :=
        rmDropErrorFrame :: rmOuterFrame afterTail :: controls)
      (calls := calls) (s := s) (E := E) (Φ := Φ)
    unfold CallContract callExpr at Hfree
    simp only [List.cons_append, List.nil_append] at Hfree
    iapply Hfree
    isplitl_exact Hruntime
    · iintro Hruntime
      isimp only [ResumeWP, resumeExpr, List.nil_append]
      wasm_twp_pures [twp_exitControl]
      simp only [rmDropErrorFrame, List.take_zero, List.nil_append]
      iapply twp_rm_err_epilogue
      iframe

/-! ## The table drop -/

set_option maxHeartbeats 2000000 in
/-- The drop of the hash table, which is the last step of the accept arm.
The first guard reads the bucket count at map offset 4 and the second
guard tests the wrapped total size, which is the same word again.  Both
arms of both guards reach `rmOuterFrame`, so neither guard has to be
decided.  WAT lines 1688 to 1713. -/
theorem twp_rm_table_drop [WasmSmallStepGS hlc Universal.State]
    {l1 l2 l3 l4 ctrl mask : UInt32} {v5 : UInt64} {afterTail : Program}
    {finalOutput : List UInt8} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp} :
    iprop(RuntimeContext ∗ StackPointer func6Base ∗
      Streams [] finalOutput false ∗
      pointsTo_u32 0 (func6Base + 16) ctrl ∗
      pointsTo_u32 0 (func6Base + 20) mask ∗
      TailDone finalOutput afterTail arity remainder controls calls
        s E Φ) ⊢
      WP (.running
          ⟨⟨[], [Value.i32 func6Base, .i32 l1, .i32 l2, .i32 l3, .i32 l4,
              .i64 v5], []⟩,
            rmTableDrop, arity, remainder,
            rmOkFrame :: rmOuterFrame afterTail :: controls, calls⟩ :
            Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hstreams, Hctrl, Hmask, Hcont⟩
  have h16 := offset_facts func6Base 16 16 rfl (by decide)
  have h20 := offset_facts func6Base 20 20 rfl (by decide)
  simp only [rmTableDrop]
  wasm_twp_pures [twp_localGet]
  wasm_twp_rebind twp_load32 (address := func6Base) (offset := 20) mask
    h20.1 h20.2.1 h20.2.2.1 h20.2.2.2 with Hmask
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  by_cases hmask : mask = 0
  · iapply twp_eqz (result := 1) (by simp [hmask])
    iapply twp_brIf (by decide) (by rfl)
    simp only [rmOuterFrame, List.take_zero, List.nil_append]
    iapply twp_rm_epilogue
    iframe
  · iapply twp_eqz (result := 0) (by simp [hmask])
    wasm_twp_pures [twp_brIfZero twp_localGet twp_const twp_shl]
      rewriting [show (3 : UInt32) % 32 = 3 by decide]
    wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceSub, List.set]
    wasm_twp_pures [twp_localGet twp_add twp_const twp_add]
    wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceSub, List.set]
    by_cases hsize : (17 : UInt32) + (mask + mask <<< 3) = 0
    · iapply twp_eqz (result := 1) (by simp [hsize])
      iapply twp_brIf (by decide) (by rfl)
      simp only [rmOuterFrame, List.take_zero, List.nil_append]
      iapply twp_rm_epilogue
      iframe
    · iapply twp_eqz (result := 0) (by simp [hsize])
      wasm_twp_pures [twp_brIfZero twp_localGet]
      wasm_twp_rebind twp_load32 (address := func6Base) (offset := 16) ctrl
        h16.1 h16.2.1 h16.2.2.1 h16.2.2.2 with Hctrl
      wasm_twp_pures [twp_localGet twp_sub twp_const twp_add twp_localGet
        twp_const]
      have Hfree := func57_noop_correct (hlc := hlc)
        ((4294967288 : UInt32) + (ctrl - mask <<< 3))
        ((17 : UInt32) + (mask + mask <<< 3)) 8
        (callerLocals :=
          ⟨[], [Value.i32 func6Base,
            .i32 ((17 : UInt32) + (mask + mask <<< 3)), .i32 l2,
            .i32 (mask <<< 3), .i32 l4, .i64 v5], []⟩)
        (stack := []) (code := [.br 1]) (arity := arity)
        (remainder := remainder)
        (controls := rmOkFrame :: rmOuterFrame afterTail :: controls)
        (calls := calls) (s := s) (E := E) (Φ := Φ)
      unfold CallContract callExpr at Hfree
      simp only [List.cons_append, List.nil_append] at Hfree
      iapply Hfree
      isplitl_exact Hruntime
      · iintro Hruntime
        isimp only [ResumeWP, resumeExpr, List.nil_append]
        iapply twp_br (by rfl)
        simp only [rmOuterFrame, List.take_zero, List.nil_append]
        iapply twp_rm_epilogue
        iframe

/-! ## The release of the pair buffer -/

set_option maxHeartbeats 2000000 in
/-- The release of the pair buffer that `sorted_entries` allocated.  The
entry count sits at frame offset 72 and the pointer at frame offset 76.
A count of zero leaves nothing to free.  The deallocator is a no-op, so
the block never reads the buffer itself.  WAT lines 1675 to 1686. -/
theorem twp_rm_free_pairs [WasmSmallStepGS hlc Universal.State]
    (cap bufPtr : UInt32)
    {l1 l2 l3 l4 ctrl mask : UInt32} {v5 : UInt64} {afterTail : Program}
    {finalOutput : List UInt8} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp} :
    iprop(RuntimeContext ∗ StackPointer func6Base ∗
      Streams [] finalOutput false ∗
      pointsTo_u32 0 (func6Base + 72) cap ∗
      pointsTo_u32 0 (func6Base + 76) bufPtr ∗
      pointsTo_u32 0 (func6Base + 16) ctrl ∗
      pointsTo_u32 0 (func6Base + 20) mask ∗
      TailDone finalOutput afterTail arity remainder controls calls
        s E Φ) ⊢
      WP (.running
          ⟨⟨[], [Value.i32 func6Base, .i32 l1, .i32 l2, .i32 l3, .i32 l4,
              .i64 v5], []⟩,
            rmFreePairs, arity, remainder,
            rmFreePairsFrame :: rmOkFrame :: rmOuterFrame afterTail ::
              controls, calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hstreams, Hcap, Hptr, Hctrl, Hmask, Hcont⟩
  have h72 := offset_facts func6Base 72 72 rfl (by decide)
  have h76 := offset_facts func6Base 76 76 rfl (by decide)
  simp only [rmFreePairs]
  wasm_twp_pures [twp_localGet]
  wasm_twp_rebind twp_load32 (address := func6Base) (offset := 72) cap
    h72.1 h72.2.1 h72.2.2.1 h72.2.2.2 with Hcap
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  by_cases hcap : cap = 0
  · iapply twp_eqz (result := 1) (by simp [hcap])
    iapply twp_brIf (by decide) (by rfl)
    simp only [rmFreePairsFrame, List.take_zero, List.nil_append]
    iapply twp_rm_table_drop
    iframe
  · iapply twp_eqz (result := 0) (by simp [hcap])
    wasm_twp_pures [twp_brIfZero twp_localGet]
    wasm_twp_rebind twp_load32 (address := func6Base) (offset := 76) bufPtr
      h76.1 h76.2.1 h76.2.2.1 h76.2.2.2 with Hptr
    wasm_twp_pures [twp_localGet twp_const twp_shl]
      rewriting [show (3 : UInt32) % 32 = 3 by decide]
    wasm_twp_pures [twp_const]
    have Hfree := func57_noop_correct (hlc := hlc) bufPtr (cap <<< 3) 4
      (callerLocals :=
        ⟨[], [Value.i32 func6Base, .i32 cap, .i32 l2, .i32 l3, .i32 l4,
          .i64 v5], []⟩)
      (stack := []) (code := []) (arity := arity) (remainder := remainder)
      (controls :=
        rmFreePairsFrame :: rmOkFrame :: rmOuterFrame afterTail ::
          controls)
      (calls := calls) (s := s) (E := E) (Φ := Φ)
    unfold CallContract callExpr at Hfree
    simp only [List.cons_append, List.nil_append] at Hfree
    iapply Hfree
    isplitl_exact Hruntime
    · iintro Hruntime
      isimp only [ResumeWP, resumeExpr, List.nil_append]
      wasm_twp_pures [twp_exitControl]
      simp only [rmFreePairsFrame, List.take_zero, List.nil_append]
      iapply twp_rm_table_drop
      iframe

/-! ## The reply -/

set_option maxHeartbeats 2000000 in
/-- The reply.  The store puts the answer word back at frame offset 64,
so the record at offsets 64 to 84 holds the `Option<u32>` and then the
header of the pair buffer.  `call 8` writes the borsh form of both to the
output stream.  The block after it frees the pair buffer and the table
drop ends the arm.  WAT lines 1667 to 1713. -/
theorem twp_rm_reply [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (allocationId : Nat) (capacity pairPtr : UInt32)
    (o : Option UInt32) (pairs : List (UInt32 × UInt32))
    (oldWord answer : UInt64) (below : List UInt8)
    (storedCursor : UInt32) (frontier : Nat) (history : AllocationHistory)
    (output : List UInt8)
    {l1 l2 l3 l4 ctrl mask : UInt32} {afterTail : Program}
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hpairs : pairs.length ≤ 2 ^ 27) :
    iprop(RuntimeContext ∗ StackPointer func6Base ∗
      StackBelow func6Base replyDepth below ∗
      pointsTo_u64 0 (func6Base + 64) oldWord ∗
      (pointsTo_u64 0 (func6Base + 64) answer -∗
        HashMap.Table.optionU32At 0 (func6Base + 64) o) ∗
      Slices.ByteSlice 0 (func6Base + 72)
        (WordCodec.u32le.serialize
          [capacity, pairPtr, UInt32.ofNat pairs.length]) ∗
      PairVecAt heapId allocationId capacity.toNat pairPtr pairs ∗
      pointsTo_u32 0 (func6Base + 16) ctrl ∗
      pointsTo_u32 0 (func6Base + 20) mask ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams [] output false ∗
      TailDone (output ++ Borsh.option Borsh.u32 o ++
          HashMap.serializeEntries WordCodec.u32le WordCodec.u32le pairs)
        afterTail arity remainder controls calls s E Φ ∗
      (ExportOOM -∗ Φ (.trapped (.host OOM.trapMessage)))) ⊢
      WP (.running
          ⟨⟨[], [Value.i32 func6Base, .i32 l1, .i32 l2, .i32 l3, .i32 l4,
              .i64 answer], []⟩,
            rmAfterSort, arity, remainder,
            rmOkFrame :: rmOuterFrame afterTail :: controls, calls⟩ :
            Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hbelow, Hcell, Hwand, Hheader, Hpairbuf, Hctrl,
    Hmask, Hbump, Hstreams, Hcont, Hoom⟩
  have h64 := offset_facts64 func6Base 64 64 rfl (by decide)
  ihave ⟨Hbytes, %hbound⟩ :=
    PairVecAt_bytes heapId allocationId capacity.toNat pairPtr pairs $$
    Hpairbuf
  simp only [rmAfterSort, rmReply, List.cons_append, List.nil_append]
  wasm_twp_pures [twp_localGet twp_localGet]
  wasm_twp_rebind Wasm.SmallStep.twp_store64 (address := func6Base)
    (offset := 64) oldWord h64.1 h64.2.1 h64.2.2.1 h64.2.2.2.1
    h64.2.2.2.2.1 h64.2.2.2.2.2.1 h64.2.2.2.2.2.2.1 h64.2.2.2.2.2.2.2
    with Hcell
  ihave Hoption := Hwand $$ Hcell
  ihave Hheader : Slices.ByteSlice 0 (func6Base + 64 + 8)
      (WordCodec.u32le.serialize
        [capacity, pairPtr, UInt32.ofNat pairs.length]) $$ [Hheader]
  · irw_exact [show func6Base + 64 + 8 = func6Base + 72 by decide]
      with Hheader
  wasm_twp_pures [twp_localGet twp_const twp_add]
    rewriting [show (64 : UInt32) + func6Base = func6Base + 64 by decide]
  have Hwrite := func5_correct (hlc := hlc) func6Base (func6Base + 64)
    capacity pairPtr o pairs below heapId storedCursor frontier history
    [] output false
    (callerLocals :=
      ⟨[], [Value.i32 func6Base, .i32 l1, .i32 l2, .i32 l3, .i32 l4,
        .i64 answer], []⟩)
    (stack := []) (code := .block 0 0 rmFreePairs :: rmTableDrop)
    (arity := arity) (remainder := remainder)
    (controls := rmOkFrame :: rmOuterFrame afterTail :: controls)
    (calls := calls) (s := s) (E := E) (Φ := Φ)
  unfold CallContract callExpr at Hwrite
  simp only [List.cons_append, List.nil_append] at Hwrite
  iapply Hwrite
  isplitl_exacts [Hruntime Hsp Hbelow Hoption Hheader Hbytes Hbump
    Hstreams]
  isplitl_pureexact ⟨hpairs, by decide, by decide, hbound⟩
  isplit
  · iintro %below' %storedCursor' %frontier' %history' Hruntime Hsp Hbelow
      Hoption Hheader Hbytes Hbump Hstreams
    isimp only [ResumeWP, resumeExpr, List.nil_append]
    ihave Hheader : Slices.ByteSlice 0 (func6Base + 72)
        (WordCodec.u32le.serialize
          [capacity, pairPtr, UInt32.ofNat pairs.length]) $$ [Hheader]
    · irw_exact [show func6Base + 64 + 8 = func6Base + 72 by decide]
        with Hheader
    ihave ⟨Hcap, Hptr, _Hcount⟩ :=
      ByteSlice_three_words (func6Base + 72) capacity pairPtr
        (UInt32.ofNat pairs.length) $$ Hheader
    isimp only [show func6Base + 72 + 4 = func6Base + 76 by decide]
      at Hptr
    wasm_twp_pures [twp_block]
    simp only [List.drop_zero]
    rw [rmFreePairsFrame_literal]
    iapply twp_rm_free_pairs capacity pairPtr
    iframe
  · iintro %remaining Hstreams
    iapply Hoom
    isimp only [ExportOOM]
    iexists remaining, output
    iexact Hstreams

/-! ## The stack region and the table size -/

/-- A table holds at most one entry for each bucket. -/
private theorem items_le_buckets {hash : UInt32 → UInt64}
    {t : HashMap.Table UInt32 UInt32} (hw : HashMap.Table.WF hash t) :
    t.items ≤ t.buckets := by
  rw [hw.items_eq]
  exact HashMap.Table.length_toList_le hw.toLayout

/-- The sorted entry list is as long as the table. -/
private theorem sorted_length_le_buckets {hash : UInt32 → UInt64}
    {t : HashMap.Table UInt32 UInt32} (hw : HashMap.Table.WF hash t) :
    (HashMap.sortByKey (HashMap.Table.toList t)).length ≤ t.buckets := by
  rw [(HashMap.sortByKey_perm (HashMap.Table.toList t)).length_eq]
  exact HashMap.Table.length_toList_le hw.toLayout

/-! ## The sort -/

set_option maxHeartbeats 2000000 in
/-- The sort of the entries that stay in the map.  `sorted_entries`,
absolute `func 7`, takes the twelve dead bytes at frame offset 72 as its
output header and the map value at frame offset 16.  It answers with the
header of a fresh pair buffer in key order.  WAT lines 1660 to 1713. -/
theorem twp_rm_sort [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (k0 k1 : UInt64) (t : HashMap.Table UInt32 UInt32)
    (o : Option UInt32) (oldWord answer : UInt64)
    (outBefore below : List UInt8)
    (storedCursor : UInt32) (frontier : Nat) (history : AllocationHistory)
    (output : List UInt8)
    {l1 l2 l3 l4 : UInt32} {afterTail : Program}
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hout : outBefore.length = 12)
    (hwf : HashMap.Table.WF (HashMap.SipHash.hashU32 k0 k1) t)
    (hbuckets : t.buckets ≤ 2 ^ 27) :
    iprop(RuntimeContext ∗ StackPointer func6Base ∗
      StackBelow func6Base removeCalleeDepth below ∗
      Slices.ByteSlice 0 (func6Base + 72) outBefore ∗
      HashMap.Table.HashMapAt 0 (func6Base + 16) k0 k1 t ∗
      pointsTo_u64 0 (func6Base + 64) oldWord ∗
      (pointsTo_u64 0 (func6Base + 64) answer -∗
        HashMap.Table.optionU32At 0 (func6Base + 64) o) ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams [] output false ∗
      TailDone (output ++ Borsh.option Borsh.u32 o ++
          HashMap.serializeEntries WordCodec.u32le WordCodec.u32le
            (HashMap.sortByKey (HashMap.Table.toList t)))
        afterTail arity remainder controls calls s E Φ ∗
      (ExportOOM -∗ Φ (.trapped (.host OOM.trapMessage)))) ⊢
      WP (.running
          ⟨⟨[], [Value.i32 func6Base, .i32 l1, .i32 l2, .i32 l3, .i32 l4,
              .i64 answer], []⟩,
            rmAfterCopyBack, arity, remainder,
            rmOkFrame :: rmOuterFrame afterTail :: controls, calls⟩ :
            Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hbelow, Hout, Hmap, Hcell, Hwand, Hbump, Hstreams,
    Hcont, Hoom⟩
  have hitems : t.items ≤ 2 ^ 27 :=
    Nat.le_trans (items_le_buckets hwf) hbuckets
  have hdepth := sortedEntriesDepth_le_remove hitems
  have hpairs : (HashMap.sortByKey (HashMap.Table.toList t)).length ≤ 2 ^ 27 :=
    Nat.le_trans (sorted_length_le_buckets hwf) hbuckets
  have hcount : UInt32.ofNat t.items =
      UInt32.ofNat (HashMap.sortByKey (HashMap.Table.toList t)).length := by
    rw [hwf.items_eq,
      (HashMap.sortByKey_perm (HashMap.Table.toList t)).length_eq]
  ihave ⟨%low, Hbelow, Hrestore⟩ :=
    StackBelow_reshape func6Base removeCalleeDepth
      (sortedEntriesDepth t.items) below hdepth $$ Hbelow
  simp only [rmAfterCopyBack, rmSort, List.cons_append, List.nil_append]
  wasm_twp_pures [twp_localGet twp_const twp_add twp_localGet twp_const
    twp_add]
    rewriting [show (72 : UInt32) + func6Base = func6Base + 72 by decide,
      show (16 : UInt32) + func6Base = func6Base + 16 by decide]
  have Hsort := func4_correct (hlc := hlc) func6Base (func6Base + 72)
    (func6Base + 16) k0 k1 t outBefore low heapId storedCursor frontier
    history [] output false
    (callerLocals :=
      ⟨[], [Value.i32 func6Base, .i32 l1, .i32 l2, .i32 l3, .i32 l4,
        .i64 answer], []⟩)
    (stack := []) (code := rmAfterSort) (arity := arity)
    (remainder := remainder)
    (controls := rmOkFrame :: rmOuterFrame afterTail :: controls)
    (calls := calls) (s := s) (E := E) (Φ := Φ)
  unfold CallContract callExpr at Hsort
  simp only [List.append_nil] at Hsort
  iapply Hsort
  isplitl_exacts [Hruntime Hsp Hbelow Hout Hmap Hbump Hstreams]
  isplitl_pureexact ⟨hout, hwf, hbuckets, by decide, by decide,
    by have : removeCalleeDepth ≤ func6Base.toNat := by decide
       omega⟩
  isplit
  · iintro %capacity %pairPtr %allocationId %below' %storedCursor'
      %frontier' %history' Hruntime Hsp Hbelow Hheader Hmap Hbump Hbuf
      Hstreams %hcapfact
    isimp only [ResumeWP, resumeExpr, List.nil_append]
    ihave ⟨%b, Hbelow⟩ := Hrestore $$ %below' Hbelow
    ihave ⟨%low2, Hbelow, _Hrestore2⟩ :=
      StackBelow_reshape func6Base removeCalleeDepth replyDepth b
        replyDepth_le_remove $$ Hbelow
    isimp only [HashMap.Table.HashMapAt] at Hmap
    icases Hmap with ⟨Htable, Hk0, Hk1⟩
    ihave Hwords := TableAt_header_words (func6Base + 16) t $$ Htable
    icases Hwords with ⟨%ctrl, %mask, Hctrl, Hmask, Hitems⟩
    isimp only [show func6Base + 16 + 4 = func6Base + 20 by decide]
      at Hmask
    iclear Hk0 Hk1 Hitems
    isimp only [hcount] at Hheader
    iapply twp_rm_reply heapId allocationId capacity pairPtr o
      (HashMap.sortByKey (HashMap.Table.toList t)) oldWord answer low2
      storedCursor' frontier' history' output hpairs
    iframe
  · iintro %remaining Hstreams
    iapply Hoom
    isimp only [ExportOOM]
    iexists remaining, output
    iexact Hstreams

/-! ## The copy back of the new map value -/

set_option maxHeartbeats 2000000 in
/-- The copy back of the new map value over the map slot.  The four
64-bit words move from the top down, so the source and the target never
overlap in the wrong order.  The words that stay at frame offset 72 are
the old header of the table, and their first twelve bytes become the
output slot of `sorted_entries`.  WAT lines 1644 to 1713. -/
theorem twp_rm_copy_back [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (k0 k1 : UInt64) (t : HashMap.Table UInt32 UInt32)
    (o : Option UInt32) (oldWord answer : UInt64)
    (mapBytes below : List UInt8)
    (storedCursor : UInt32) (frontier : Nat) (history : AllocationHistory)
    (output : List UInt8)
    {l1 l2 l3 l4 : UInt32} {afterTail : Program}
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hmap : mapBytes.length = 32)
    (hwf : HashMap.Table.WF (HashMap.SipHash.hashU32 k0 k1) t)
    (hbuckets : t.buckets ≤ 2 ^ 27) :
    iprop(RuntimeContext ∗ StackPointer func6Base ∗
      StackBelow func6Base removeCalleeDepth below ∗
      Slices.ByteSlice 0 (func6Base + 16) mapBytes ∗
      HashMap.Table.HashMapAt 0 (func6Base + 72) k0 k1 t ∗
      pointsTo_u64 0 (func6Base + 64) oldWord ∗
      (pointsTo_u64 0 (func6Base + 64) answer -∗
        HashMap.Table.optionU32At 0 (func6Base + 64) o) ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams [] output false ∗
      TailDone (output ++ Borsh.option Borsh.u32 o ++
          HashMap.serializeEntries WordCodec.u32le WordCodec.u32le
            (HashMap.sortByKey (HashMap.Table.toList t)))
        afterTail arity remainder controls calls s E Φ ∗
      (ExportOOM -∗ Φ (.trapped (.host OOM.trapMessage)))) ⊢
      WP (.running
          ⟨⟨[], [Value.i32 func6Base, .i32 l1, .i32 l2, .i32 l3, .i32 l4,
              .i64 answer], []⟩,
            rmAfterRemove, arity, remainder,
            rmOkFrame :: rmOuterFrame afterTail :: controls, calls⟩ :
            Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hbelow, Hdest, Hmap, Hcell, Hwand, Hbump,
    Hstreams, Hcont, Hoom⟩
  have h16 := offset_facts64 func6Base 16 16 rfl (by decide)
  have h24 := offset_facts64 func6Base 24 24 rfl (by decide)
  have h32 := offset_facts64 func6Base 32 32 rfl (by decide)
  have h40 := offset_facts64 func6Base 40 40 rfl (by decide)
  have h72 := offset_facts64 func6Base 72 72 rfl (by decide)
  have h80 := offset_facts64 func6Base 80 80 rfl (by decide)
  have h88 := offset_facts64 func6Base 88 88 rfl (by decide)
  have h96 := offset_facts64 func6Base 96 96 rfl (by decide)
  ihave ⟨%ctrl, %mask, %growthLeft, %items, Hs0, Hs1, Hs2, Hs3, Hback⟩ :=
    HashMapAt_move_words (func6Base + 72) (func6Base + 16) k0 k1 t $$ Hmap
  isimp only [show func6Base + 72 + 8 = func6Base + 80 by decide] at Hs1
  isimp only [show func6Base + 72 + 16 = func6Base + 88 by decide] at Hs2
  isimp only [show func6Base + 72 + 24 = func6Base + 96 by decide] at Hs3
  ihave ⟨%d0, %d1, %d2, %d3, Hd0, Hd1, Hd2, Hd3⟩ :=
    ByteSlice_thirtyTwo_as_cells 0 (func6Base + 16) mapBytes hmap $$ Hdest
  isimp only [show func6Base + 16 + 8 = func6Base + 24 by decide] at Hd1
  isimp only [show func6Base + 16 + 16 = func6Base + 32 by decide] at Hd2
  isimp only [show func6Base + 16 + 24 = func6Base + 40 by decide] at Hd3
  simp only [rmAfterRemove, rmCopyBack, List.cons_append, List.nil_append]
  wasm_twp_block_move (func6Base, 96, k1, h96) (func6Base, 40, d3, h40)
    with Hs3 Hd3
  wasm_twp_block_move (func6Base, 88, k0, h88) (func6Base, 32, d2, h32)
    with Hs2 Hd2
  wasm_twp_block_move (func6Base, 80, wordPair growthLeft items, h80)
    (func6Base, 24, d1, h24) with Hs1 Hd1
  wasm_twp_block_move (func6Base, 72, wordPair ctrl mask, h72)
    (func6Base, 16, d0, h16) with Hs0 Hd0
  -- the map value is whole again at frame offset 16
  ihave Hd1 : pointsTo_u64 0 (func6Base + 16 + 8)
      (wordPair growthLeft items) $$ [Hd1]
  · irw_exact [show func6Base + 16 + 8 = func6Base + 24 by decide] with Hd1
  ihave Hd2 : pointsTo_u64 0 (func6Base + 16 + 16) k0 $$ [Hd2]
  · irw_exact [show func6Base + 16 + 16 = func6Base + 32 by decide] with Hd2
  ihave Hd3 : pointsTo_u64 0 (func6Base + 16 + 24) k1 $$ [Hd3]
  · irw_exact [show func6Base + 16 + 24 = func6Base + 40 by decide] with Hd3
  ihave Hmap := Hback $$ Hd0 Hd1 Hd2 Hd3
  -- the old header words become the output slot of the sort
  ihave ⟨Hw0, Hw1⟩ :=
    (pointsTo_u32_pair_as_groupWord 0 (func6Base + 72) ctrl mask).mpr $$
    Hs0
  ihave ⟨Hw2, _Hw3⟩ :=
    (pointsTo_u32_pair_as_groupWord 0 (func6Base + 80) growthLeft
      items).mpr $$ Hs1
  ihave Hw1 : pointsTo_u32 0 (func6Base + 72 + 4) mask $$ [Hw1]
  · irw_exact [show func6Base + 72 + 4 = func6Base + 76 by decide] with Hw1
  ihave Hw2 : pointsTo_u32 0 (func6Base + 72 + 4 + 4) growthLeft $$ [Hw2]
  · irw_exact [show func6Base + 72 + 4 + 4 = func6Base + 80 by decide]
      with Hw2
  ihave Hout :=
    ByteSlice_of_three_words (func6Base + 72) ctrl mask growthLeft
      (by decide) $$ [Hw0 Hw1 Hw2]
  · iframe Hw0 Hw1 Hw2
  iclear Hs2 Hs3
  iapply twp_rm_sort heapId k0 k1 t o oldWord answer
    (WordCodec.u32le.serialize [ctrl, mask, growthLeft]) below
    storedCursor frontier history output rfl hwf hbuckets
  iframe

/-! ## The remove kernel -/

set_option maxHeartbeats 2000000 in
/-- The remove kernel, absolute `func 11`, and the load of its answer
word.  The kernel takes a 40-byte output slot at frame offset 64 and the
map value at frame offset 16.  It writes the removed value as an
`Option<u32>` at offsets 64 to 72 and the map that remains at offsets 72
to 104, and it gives the old map slot back as raw bytes.  The driver
saves the answer word in local 5.  WAT lines 1633 to 1713. -/
theorem twp_rm_remove [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (k0 k1 : UInt64) (key : UInt32)
    (entries : HashMap.Map UInt32 UInt32) (outBefore below : List UInt8)
    (storedCursor : UInt32) (frontier : Nat) (history : AllocationHistory)
    (output : List UInt8)
    {l2 l3 l4 : UInt32} {v5 : UInt64} {afterTail : Program}
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hout : outBefore.length = 40)
    (hn : entries.length ≤ 2 ^ 30)
    (hmax : entries.length ≤ 117440512) :
    iprop(RuntimeContext ∗ StackPointer func6Base ∗
      StackBelow func6Base removeCalleeDepth below ∗
      Slices.ByteSlice 0 (func6Base + 64) outBefore ∗
      HashMap.Table.MapAt 0 (func6Base + 16) k0 k1 entries ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams [] output false ∗
      TailDone (output ++ Borsh.option Borsh.u32
            (HashMap.Table.remove (HashMap.SipHash.hashU32 k0 k1)
              (HashMap.Table.ofEntries (HashMap.SipHash.hashU32 k0 k1)
                entries) key).1 ++
          HashMap.serializeEntries WordCodec.u32le WordCodec.u32le
            (HashMap.sortByKey (HashMap.Table.toList
              (HashMap.Table.remove (HashMap.SipHash.hashU32 k0 k1)
                (HashMap.Table.ofEntries (HashMap.SipHash.hashU32 k0 k1)
                  entries) key).2)))
        afterTail arity remainder controls calls s E Φ ∗
      (ExportOOM -∗ Φ (.trapped (.host OOM.trapMessage)))) ⊢
      WP (.running
          ⟨⟨[], [Value.i32 func6Base, .i32 key, .i32 l2, .i32 l3, .i32 l4,
              .i64 v5], []⟩,
            rmAfterCollect, arity, remainder,
            rmOkFrame :: rmOuterFrame afterTail :: controls, calls⟩ :
            Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hbelow, Hout, Hmap, Hbump, Hstreams, Hcont, Hoom⟩
  obtain ⟨hwf, hclean, _, _⟩ :=
    HashMap.Table.wf_ofEntries_u32 k0 k1 entries hn
  have hbuckets :
      (HashMap.Table.ofEntries (HashMap.SipHash.hashU32 k0 k1)
        entries).buckets ≤ 2 ^ 27 :=
    buckets_ofEntries_le (HashMap.SipHash.hashU32 k0 k1) entries hn hmax
  obtain ⟨hwf', hkeep, _, _⟩ := hwf.remove key
  have h64 := offset_facts64 func6Base 64 64 rfl (by decide)
  isimp only [HashMap.Table.MapAt] at Hmap
  simp only [rmAfterCollect, rmRemove, List.cons_append, List.nil_append]
  wasm_twp_pures [twp_localGet twp_const twp_add twp_localGet twp_const
    twp_add twp_localGet]
    rewriting [show (64 : UInt32) + func6Base = func6Base + 64 by decide,
      show (16 : UInt32) + func6Base = func6Base + 16 by decide]
  have Hkernel := func8_correct (hlc := hlc) (func6Base + 64)
    (func6Base + 16) key k0 k1
    (HashMap.Table.ofEntries (HashMap.SipHash.hashU32 k0 k1) entries)
    outBefore
    (callerLocals :=
      ⟨[], [Value.i32 func6Base, .i32 key, .i32 l2, .i32 l3, .i32 l4,
        .i64 v5], []⟩)
    (stack := [])
    (code := .localGet 0 :: .load64 64 :: .localSet 5 :: rmAfterRemove)
    (arity := arity) (remainder := remainder)
    (controls := rmOkFrame :: rmOuterFrame afterTail :: controls)
    (calls := calls) (s := s) (E := E) (Φ := Φ)
  unfold CallContract callExpr at Hkernel
  simp only [List.append_nil] at Hkernel
  iapply Hkernel
  isplitl_exacts [Hruntime Hout Hmap]
  isplitl_pureexact ⟨hout, hwf, hclean, by decide, by decide⟩
  iintro %mapBytes Hruntime Hanswer Hnew Hold %hmapBytes
  isimp only [ResumeWP, resumeExpr, List.nil_append]
  isimp only [show func6Base + 64 + 8 = func6Base + 72 by decide] at Hnew
  ihave ⟨%answer, Hcell, Hwand⟩ :=
    optionU32At_as_u64 0 (func6Base + 64)
      (HashMap.Table.remove (HashMap.SipHash.hashU32 k0 k1)
        (HashMap.Table.ofEntries (HashMap.SipHash.hashU32 k0 k1) entries)
        key).1 $$ Hanswer
  wasm_twp_pures [twp_localGet]
  wasm_twp_rebind Wasm.SmallStep.twp_load64 (address := func6Base)
    (offset := 64) answer h64.1 h64.2.1 h64.2.2.1 h64.2.2.2.1
    h64.2.2.2.2.1 h64.2.2.2.2.2.1 h64.2.2.2.2.2.2.1 h64.2.2.2.2.2.2.2
    with Hcell
  wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  iapply twp_rm_copy_back heapId k0 k1
    (HashMap.Table.remove (HashMap.SipHash.hashU32 k0 k1)
      (HashMap.Table.ofEntries (HashMap.SipHash.hashU32 k0 k1) entries)
      key).2
    (HashMap.Table.remove (HashMap.SipHash.hashU32 k0 k1)
      (HashMap.Table.ofEntries (HashMap.SipHash.hashU32 k0 k1) entries)
      key).1
    answer answer mapBytes below storedCursor frontier history output
    hmapBytes hwf' (by rw [hkeep]; exact hbuckets)
  iframe

/-! ## The collect call -/

set_option maxHeartbeats 2000000 in
/-- The build of the hash table.  `collect_entries`, absolute `func 5`,
takes the pair buffer through the vector header at frame offset 0 and
builds the map value in the 32 bytes at frame offset 16, which are the
bytes that the key decoder wrote its answer into.  The two seeds stay
existential, and `Project.RustHashMap.RemovePures.removeOutput_of_accepts`
names the output that the rest of the arm writes.  WAT lines 1628 to
1713. -/
theorem twp_rm_collect [WasmSmallStepGS hlc Universal.State]
    (hfunc2 : CollectContract.Func2Spec (hlc := hlc))
    (heapId : GName) (cap bufPtr len : UInt32) (input : List UInt8)
    (payload spare mapBefore outBefore keysBefore below : List UInt8)
    (storedCursor : UInt32) (frontier : Nat) (history : AllocationHistory)
    (output : List UInt8)
    {l2 l3 l4 : UInt32} {v5 : UInt64} {afterTail : Program}
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (haccept : KeyDecodeAccepts input)
    (hn : (acceptedEntries input).length ≤ 2 ^ 30)
    (hmax : (acceptedEntries input).length ≤ 117440512)
    (hmapBefore : mapBefore.length = 32)
    (hslot : outBefore.length = 40)
    (hkeys : keysBefore.length = randomStateSize)
    (hpayload : payload =
      CollectContract.entryCodec.serialize (acceptedEntries input))
    (hentries : (acceptedEntries input).length = len.toNat)
    (hcap : len.toNat ≤ cap.toNat)
    (hspare : spare.length = 8 * (cap.toNat - len.toNat))
    (hstate : keysBefore[16]? ≠ some 2)
    (halign : bufPtr.toNat % 4 = 0) :
    iprop(RuntimeContext ∗ StackPointer func6Base ∗
      StackBelow func6Base removeCalleeDepth below ∗
      Slices.ByteSlice 0 (func6Base + 16) mapBefore ∗
      pointsTo_u32 0 func6Base cap ∗
      pointsTo_u32 0 (func6Base + 4) bufPtr ∗
      pointsTo_u32 0 (func6Base + 8) len ∗
      Slices.ByteSlice 0 bufPtr (payload ++ spare) ∗
      Slices.ByteSlice 0 randomStateCell keysBefore ∗
      Slices.ByteSlice 0 entryStackTop staticTableBytes ∗
      Slices.ByteSlice 0 (func6Base + 64) outBefore ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams [] output false ∗
      TailDone (output ++ Project.RustHashMap.Spec.removeOutput input)
        afterTail arity remainder controls calls s E Φ ∗
      (ExportOOM -∗ Φ (.trapped (.host OOM.trapMessage)))) ⊢
      WP (.running
          ⟨⟨[], [Value.i32 func6Base, .i32 (leadingKey input), .i32 l2,
              .i32 l3, .i32 l4, .i64 v5], []⟩,
            rmCollectAndRest, arity, remainder,
            rmOkFrame :: rmOuterFrame afterTail :: controls, calls⟩ :
            Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hbelow, Hmap, Hcap, Hptr, Hlen, Hbuf, Hkeys,
    Hstatic, Hout, Hbump, Hstreams, Hcont, Hoom⟩
  have hmaxLen : len.toNat ≤ maxTableCapacity := by
    rw [maxTableCapacity_eq, ← hentries]
    exact hmax
  ihave ⟨Hctrl, Hhdr, Hzero⟩ :=
    CollectContract.staticTable_resources $$ Hstatic
  ihave ⟨%low, Hbelow, Hrestore⟩ :=
    StackBelow_reshape func6Base removeCalleeDepth
      CollectContract.collectDepth below collectDepth_le_remove $$ Hbelow
  simp only [rmCollectAndRest, rmCollect, List.cons_append,
    List.nil_append]
  wasm_twp_pures [twp_localGet twp_const twp_add twp_localGet]
    rewriting [show (16 : UInt32) + func6Base = func6Base + 16 by decide]
  have Hcollect := hfunc2 func6Base (func6Base + 16) func6Base cap bufPtr
    len heapId (acceptedEntries input) payload spare mapBefore keysBefore
    low storedCursor frontier history [] output false
    (callerLocals :=
      ⟨[], [Value.i32 func6Base, .i32 (leadingKey input), .i32 l2,
        .i32 l3, .i32 l4, .i64 v5], []⟩)
    (stack := []) (code := rmAfterCollect) (arity := arity)
    (remainder := remainder)
    (controls := rmOkFrame :: rmOuterFrame afterTail :: controls)
    (calls := calls) (s := s) (E := E) (Φ := Φ)
  unfold CallContract callExpr at Hcollect
  simp only [List.append_nil] at Hcollect
  iapply Hcollect
  isplitl_exacts [Hruntime Hsp Hbelow Hmap Hcap Hptr Hlen Hbuf Hkeys Hctrl
    Hhdr Hzero Hbump Hstreams]
  isplitl_pureexact ⟨hmapBefore, hkeys, hstate, hpayload, hentries, hcap,
    hmaxLen, hspare, halign, by decide, by decide, by decide⟩
  isplit
  · iintro %k0 %k1 %below' %keysAfter %storedCursor' %frontier' %history'
      Hruntime Hsp Hbelow Hmapv Hcap Hptr Hlen Hkeys Hhdr Hzero Hbump Hstreams
      %hfacts
    isimp only [ResumeWP, resumeExpr, List.nil_append]
    iclear Hhdr Hzero
    ihave ⟨%b, Hbelow⟩ := Hrestore $$ %below' Hbelow
    have hshape : output ++ Project.RustHashMap.Spec.removeOutput input =
        output ++ Borsh.option Borsh.u32
            (HashMap.Table.remove (HashMap.SipHash.hashU32 k0 k1)
              (HashMap.Table.ofEntries (HashMap.SipHash.hashU32 k0 k1)
                (acceptedEntries input)) (leadingKey input)).1 ++
          HashMap.serializeEntries WordCodec.u32le WordCodec.u32le
            (HashMap.sortByKey (HashMap.Table.toList
              (HashMap.Table.remove (HashMap.SipHash.hashU32 k0 k1)
                (HashMap.Table.ofEntries (HashMap.SipHash.hashU32 k0 k1)
                  (acceptedEntries input)) (leadingKey input)).2)) := by
      rw [removeOutput_of_accepts input k0 k1 haccept hn,
        List.append_assoc]
    isimp only [hshape] at Hcont
    iclear Hcap Hptr Hlen Hkeys
    iapply twp_rm_remove heapId k0 k1 (leadingKey input)
      (acceptedEntries input) outBefore b storedCursor' frontier' history'
      output hslot hn hmax
    iframe
  · iintro %remaining Hstreams
    iapply Hoom
    isimp only [ExportOOM]
    iexists remaining, output
    iexact Hstreams

/-! ## The release of the input byte vector -/

set_option maxHeartbeats 2000000 in
/-- The release of the input byte vector before the collect call.  A
capacity of zero leaves nothing to free, and the deallocator is a no-op,
so neither arm reads the buffer.  WAT lines 1620 to 1626. -/
theorem twp_rm_free_input [WasmSmallStepGS hlc Universal.State]
    (hfunc2 : CollectContract.Func2Spec (hlc := hlc))
    (heapId : GName) (cap bufPtr len : UInt32) (input : List UInt8)
    (payload spare mapBefore outBefore keysBefore below : List UInt8)
    (storedCursor : UInt32) (frontier : Nat) (history : AllocationHistory)
    (output : List UInt8)
    {l2 l3 l4 : UInt32} {v5 : UInt64} {afterTail : Program}
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (haccept : KeyDecodeAccepts input)
    (hn : (acceptedEntries input).length ≤ 2 ^ 30)
    (hmax : (acceptedEntries input).length ≤ 117440512)
    (hmapBefore : mapBefore.length = 32)
    (hslot : outBefore.length = 40)
    (hkeys : keysBefore.length = randomStateSize)
    (hpayload : payload =
      CollectContract.entryCodec.serialize (acceptedEntries input))
    (hentries : (acceptedEntries input).length = len.toNat)
    (hcap : len.toNat ≤ cap.toNat)
    (hspare : spare.length = 8 * (cap.toNat - len.toNat))
    (hstate : keysBefore[16]? ≠ some 2)
    (halign : bufPtr.toNat % 4 = 0) :
    iprop(RuntimeContext ∗ StackPointer func6Base ∗
      StackBelow func6Base removeCalleeDepth below ∗
      Slices.ByteSlice 0 (func6Base + 16) mapBefore ∗
      pointsTo_u32 0 func6Base cap ∗
      pointsTo_u32 0 (func6Base + 4) bufPtr ∗
      pointsTo_u32 0 (func6Base + 8) len ∗
      Slices.ByteSlice 0 bufPtr (payload ++ spare) ∗
      Slices.ByteSlice 0 randomStateCell keysBefore ∗
      Slices.ByteSlice 0 entryStackTop staticTableBytes ∗
      Slices.ByteSlice 0 (func6Base + 64) outBefore ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams [] output false ∗
      TailDone (output ++ Project.RustHashMap.Spec.removeOutput input)
        afterTail arity remainder controls calls s E Φ ∗
      (ExportOOM -∗ Φ (.trapped (.host OOM.trapMessage)))) ⊢
      WP (.running
          ⟨⟨[], [Value.i32 func6Base, .i32 (leadingKey input), .i32 l2,
              .i32 l3, .i32 l4, .i64 v5], []⟩,
            rmFreeInput, arity, remainder,
            rmFreeInputFrame :: rmOkFrame :: rmOuterFrame afterTail ::
              controls, calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hbelow, Hmap, Hcap, Hptr, Hlen, Hbuf, Hkeys,
    Hstatic, Hout, Hbump, Hstreams, Hcont, Hoom⟩
  simp only [rmFreeInput]
  by_cases hcapacity : l2 = 0
  · wasm_twp_pures [twp_localGet]
    iapply twp_eqz (result := 1) (by simp [hcapacity])
    iapply twp_brIf (by decide) (by rfl)
    simp only [rmFreeInputFrame, List.take_zero, List.nil_append]
    iapply twp_rm_collect hfunc2 heapId cap bufPtr len input payload spare
      mapBefore outBefore keysBefore below storedCursor frontier history
      output haccept hn hmax hmapBefore hslot hkeys hpayload hentries hcap
      hspare hstate halign
    iframe
  · wasm_twp_pures [twp_localGet]
    iapply twp_eqz (result := 0) (by simp [hcapacity])
    wasm_twp_pures [twp_brIfZero twp_localGet twp_localGet twp_const]
    have Hfree := func57_noop_correct (hlc := hlc) l3 l2 1
      (callerLocals :=
        ⟨[], [Value.i32 func6Base, .i32 (leadingKey input), .i32 l2,
          .i32 l3, .i32 l4, .i64 v5], []⟩)
      (stack := []) (code := []) (arity := arity) (remainder := remainder)
      (controls :=
        rmFreeInputFrame :: rmOkFrame :: rmOuterFrame afterTail ::
          controls)
      (calls := calls) (s := s) (E := E) (Φ := Φ)
    unfold CallContract callExpr at Hfree
    simp only [List.cons_append, List.nil_append] at Hfree
    iapply Hfree
    isplitl_exact Hruntime
    · iintro Hruntime
      isimp only [ResumeWP, resumeExpr, List.nil_append]
      wasm_twp_pures [twp_exitControl]
      simp only [rmFreeInputFrame, List.take_zero, List.nil_append]
      iapply twp_rm_collect hfunc2 heapId cap bufPtr len input payload
        spare mapBefore outBefore keysBefore below storedCursor frontier
        history output haccept hn hmax hmapBefore hslot hkeys hpayload
        hentries hcap hspare hstate halign
      iframe

/-! ## The header copy of the accept arm -/

set_option maxHeartbeats 2000000 in
/-- The accept arm after its guard.  The arm copies the capacity and the
buffer pointer of the decoded pair vector into the entries header at
frame offset 0, copies the pair count after them, moves the leading key
into local 1, and releases the input byte vector.  The bytes that the
decoder wrote stay where they are, and the accept arm hands them on as
the first twenty bytes of the map slot.  WAT lines 1608 to 1713. -/
theorem twp_rm_accept_copy [WasmSmallStepGS hlc Universal.State]
    (hfunc2 : CollectContract.Func2Spec (hlc := hlc))
    (heapId : GName) (cap bufPtr oldLen : UInt32) (oldPair : UInt64)
    (input : List UInt8)
    (payload spare raw12 outBefore keysBefore below : List UInt8)
    (storedCursor : UInt32) (frontier : Nat) (history : AllocationHistory)
    (output : List UInt8)
    {l1 l2 l3 l4 : UInt32} {v5 : UInt64} {afterTail : Program}
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (haccept : KeyDecodeAccepts input)
    (hn : (acceptedEntries input).length ≤ 2 ^ 30)
    (hmax : (acceptedEntries input).length ≤ 117440512)
    (hraw : raw12.length = 12)
    (hslot : outBefore.length = 40)
    (hkeys : keysBefore.length = randomStateSize)
    (hpayload : payload =
      CollectContract.entryCodec.serialize (acceptedEntries input))
    (hcap : (pairCount input).toNat ≤ cap.toNat)
    (hspare : spare.length =
      8 * (cap.toNat - (pairCount input).toNat))
    (hstate : keysBefore[16]? ≠ some 2)
    (halign : bufPtr.toNat % 4 = 0) :
    iprop(RuntimeContext ∗ StackPointer func6Base ∗
      StackBelow func6Base removeCalleeDepth below ∗
      pointsTo_u64 0 (func6Base + 0) oldPair ∗
      pointsTo_u32 0 (func6Base + 8) oldLen ∗
      Slices.ByteSlice 0 (func6Base + 16)
        (WordCodec.u32le.serialize
          [0, leadingKey input, cap, bufPtr, pairCount input]) ∗
      Slices.ByteSlice 0 (func6Base + 36) raw12 ∗
      Slices.ByteSlice 0 bufPtr (payload ++ spare) ∗
      Slices.ByteSlice 0 randomStateCell keysBefore ∗
      Slices.ByteSlice 0 entryStackTop staticTableBytes ∗
      Slices.ByteSlice 0 (func6Base + 64) outBefore ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams [] output false ∗
      TailDone (output ++ Project.RustHashMap.Spec.removeOutput input)
        afterTail arity remainder controls calls s E Φ ∗
      (ExportOOM -∗ Φ (.trapped (.host OOM.trapMessage)))) ⊢
      WP (.running
          ⟨⟨[], [Value.i32 func6Base, .i32 l1, .i32 l2, .i32 l3, .i32 l4,
              .i64 v5], []⟩,
            rmOkBody, arity, remainder,
            rmOkFrame :: rmOuterFrame afterTail :: controls, calls⟩ :
            Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hbelow, Hpair0, Hlen0, Hdec, Hraw, Hbuf, Hkeys,
    Hstatic, Hout, Hbump, Hstreams, Hcont, Hoom⟩
  have h0 := offset_facts64 func6Base 0 0 rfl (by decide)
  have h24 := offset_facts64 func6Base 24 24 rfl (by decide)
  have h8 := offset_facts func6Base 8 8 rfl (by decide)
  have h20 := offset_facts func6Base 20 20 rfl (by decide)
  have h32 := offset_facts func6Base 32 32 rfl (by decide)
  ihave ⟨H16, H20, H24, H28, H32⟩ :=
    ByteSlice_five_words (func6Base + 16) 0 (leadingKey input) cap bufPtr
      (pairCount input) $$ Hdec
  isimp only [show func6Base + 16 + 4 = func6Base + 20 by decide] at H20
  isimp only [show func6Base + 16 + 4 + 4 = func6Base + 24 by decide]
    at H24
  isimp only [show func6Base + 16 + 4 + 4 + 4 = func6Base + 28 by decide]
    at H28
  isimp only
    [show func6Base + 16 + 4 + 4 + 4 + 4 = func6Base + 32 by decide] at H32
  ihave Hpair :=
    (pointsTo_u32_pair_as_groupWord 0 (func6Base + 24) cap bufPtr).mp $$
    [H24 H28]
  · isplitl_exact H24
    · irw_exact [show func6Base + 24 + 4 = func6Base + 28 by decide]
        with H28
  simp only [rmOkBody, rmAcceptCopy, List.cons_append, List.nil_append]
  wasm_twp_block_move (func6Base, 24, wordPair cap bufPtr, h24)
    (func6Base, 0, oldPair, h0) with Hpair Hpair0
  wasm_twp_pures [twp_localGet twp_localGet]
  wasm_twp_rebind twp_load32 (address := func6Base) (offset := 32)
    (pairCount input) h32.1 h32.2.1 h32.2.2.1 h32.2.2.2 with H32
  wasm_twp_rebind twp_store32 (address := func6Base) (offset := 8) oldLen
    h8.1 h8.2.1 h8.2.2.1 h8.2.2.2 with Hlen0
  wasm_twp_pures [twp_localGet]
  wasm_twp_rebind twp_load32 (address := func6Base) (offset := 20)
    (leadingKey input) h20.1 h20.2.1 h20.2.2.1 h20.2.2.2 with H20
  wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  -- the entries header at frame offset 0
  ihave Hpair0 : pointsTo_u64 0 func6Base (wordPair cap bufPtr) $$ [Hpair0]
  · irw_exact [show func6Base + 0 = func6Base by decide] with Hpair0
  ihave ⟨Hcapw, Hptrw⟩ :=
    (pointsTo_u32_pair_as_groupWord 0 func6Base cap bufPtr).mpr $$ Hpair0
  -- the decoder answer, whole again, as the head of the map slot
  ihave ⟨H24, H28⟩ :=
    (pointsTo_u32_pair_as_groupWord 0 (func6Base + 24) cap bufPtr).mpr $$
    Hpair
  ihave H24 : pointsTo_u32 0 (func6Base + 16 + 4 + 4) cap $$ [H24]
  · irw_exact [show func6Base + 16 + 4 + 4 = func6Base + 24 by decide]
      with H24
  ihave H28 : pointsTo_u32 0 (func6Base + 16 + 4 + 4 + 4) bufPtr $$ [H28]
  · irw_exact
      [show func6Base + 16 + 4 + 4 + 4 = func6Base + 24 + 4 by decide]
      with H28
  ihave H20 : pointsTo_u32 0 (func6Base + 16 + 4) (leadingKey input) $$
      [H20]
  · irw_exact [show func6Base + 16 + 4 = func6Base + 20 by decide] with H20
  ihave H32 : pointsTo_u32 0 (func6Base + 16 + 4 + 4 + 4 + 4)
      (pairCount input) $$ [H32]
  · irw_exact
      [show func6Base + 16 + 4 + 4 + 4 + 4 = func6Base + 32 by decide]
      with H32
  ihave Hdec :=
    ByteSlice_of_five_words (func6Base + 16) 0 (leadingKey input) cap
      bufPtr (pairCount input) (by decide) $$ [H16 H20 H24 H28 H32]
  · iframe H16 H20 H24 H28 H32
  ihave Hraw : Slices.ByteSlice 0 (func6Base + 16 + UInt32.ofNat 20)
      raw12 $$ [Hraw]
  · irw_exact
      [show func6Base + 16 + UInt32.ofNat 20 = func6Base + 36 by decide]
      with Hraw
  ihave Hmap :=
    ByteSlice_glue (func6Base + 16)
      (WordCodec.u32le.serialize
        [0, leadingKey input, cap, bufPtr, pairCount input]) raw12 20
      rfl $$ [Hdec Hraw]
  · iframe Hdec Hraw
  ihave Hlen0 : pointsTo_u32 0 (func6Base + 8) (pairCount input) $$
      [Hlen0]
  · iexact Hlen0
  wasm_twp_pures [twp_block]
  simp only [List.drop_zero]
  rw [rmFreeInputFrame_literal]
  iapply twp_rm_free_input hfunc2 heapId cap bufPtr (pairCount input)
    input payload spare
    (WordCodec.u32le.serialize
      [0, leadingKey input, cap, bufPtr, pairCount input] ++ raw12)
    outBefore keysBefore below storedCursor frontier history output
    haccept hn hmax (by rw [List.length_append, hraw]; rfl) hslot hkeys
    hpayload (acceptedEntries_length input) hcap hspare hstate halign
  iframe

/-! ## The whole tail -/

set_option maxHeartbeats 2000000 in
/-- The tail of the `map_remove` driver, from the end of the read loop to
the return.  `collect_entries` is the one open contract.  WAT lines 1597
to 1739. -/
theorem twp_remove_tail [WasmSmallStepGS hlc Universal.State]
    (hfunc2 : CollectContract.Func2Spec (hlc := hlc)) :
    RemoveTailContracts.RemoveTailSpec (hlc := hlc) := by
  unfold RemoveTailContracts.RemoveTailSpec
  intro heapId capacity ptr aux4 input output reserve head chunk extra
    keysBefore dataBytes storedCursor frontier history afterTail arity
    remainder controls calls s E Φ
  iintro ⟨HafterRead, Hextra, Hkeys, Hdata, %hsizes, Hcont, Hoom⟩
  obtain ⟨hextra, hkeys, hdata, hstate, hstatic, hinput⟩ := hsizes
  isimp only [AfterReadRm] at HafterRead
  icases HafterRead with ⟨Hruntime, Hsp, Hreserve, Hhead, Hvec, Hchunk,
    Hbump, Hstreams, %hshape⟩
  obtain ⟨hhead, hchunk, hpush⟩ := hshape
  have hlenNat : (UInt32.ofNat input.length).toNat = input.length :=
    UInt32.toNat_ofNat_of_lt' hinput
  have h16 := offset_facts func6Base 16 16 rfl (by decide)
  -- the region that the callees take, and the part the decoder gets
  ihave Hbelow : StackBelow func6Base removeCalleeDepth (extra ++ reserve)
      $$ [Hextra Hreserve]
  · iapply StackBelow_of_reserve_at func6Base removeCalleeDepth extra
      reserve (by rw [hextra]; rfl) (by decide) (by decide)
    iframe
  ihave ⟨%low, Hbelow, Hrestore⟩ :=
    StackBelow_reshape func6Base removeCalleeDepth keyDecoderDepth
      (extra ++ reserve) keyDecoderDepth_le_remove $$ Hbelow
  -- the five regions of the frame head
  icases (ByteSlice_split_at func6Base 12 head (by simp [hhead])).mp $$
    Hhead with ⟨Hhead0, Hrest1⟩
  isimp only [UInt32.reduceToNat] at Hhead0
  isimp only [UInt32.reduceToNat] at Hrest1
  icases (ByteSlice_split_at (func6Base + 12) 4 (head.drop 12)
    (by simp [hhead])).mp $$ Hrest1 with ⟨_Hgap0, Hrest2⟩
  isimp only [UInt32.reduceToNat,
    show func6Base + 12 + 4 = func6Base + 16 by decide,
    show (head.drop 12).drop 4 = head.drop 16 from by
      simp [List.drop_drop]] at Hrest2
  icases (ByteSlice_split_at (func6Base + 16) 20 (head.drop 16)
    (by simp [hhead])).mp $$ Hrest2 with ⟨Hslot, Hrest3⟩
  isimp only [UInt32.reduceToNat] at Hslot
  isimp only [UInt32.reduceToNat,
    show func6Base + 16 + 20 = func6Base + 36 by decide,
    show (head.drop 16).drop 20 = head.drop 36 from by
      simp [List.drop_drop]] at Hrest3
  icases (ByteSlice_split_at (func6Base + 36) 12 (head.drop 36)
    (by simp [hhead])).mp $$ Hrest3 with ⟨Hraw, _Hgap1⟩
  isimp only [UInt32.reduceToNat] at Hraw
  -- the entries header at frame offset 0
  ihave Hwords := ByteSlice_header_as_words func6Base (head.take 12)
    (by simp [hhead]) (by decide) $$ Hhead0
  icases Hwords with ⟨%oldCap, %oldPtr, %oldLen, Hcapw, Hptrw, Hlenw⟩
  ihave HoldPair :=
    (pointsTo_u32_pair_as_groupWord 0 func6Base oldCap oldPtr).mp $$
    [Hcapw Hptrw]
  · iframe Hcapw Hptrw
  ihave HoldPair : pointsTo_u64 0 (func6Base + 0) (wordPair oldCap oldPtr)
      $$ [HoldPair]
  · irw_exact [show func6Base + 0 = func6Base by decide] with HoldPair
  -- the output slot of the remove kernel, cut from the chunk buffer
  icases (ByteSlice_split_at (func6Base + 64) 40 chunk
    (by simp [hchunk])).mp $$ Hchunk with ⟨Hslot40, _Hchunkrest⟩
  isimp only [UInt32.reduceToNat] at Hslot40
  -- the input bytes, and the bound that the entry count needs
  ihave ⟨_Hheader, Hstorage⟩ :=
    (VecU8_as_headerBytes_storage heapId (func6Base + 52) capacity ptr
      input (by decide)).mp $$ Hvec
  ihave ⟨Hstorage, %hfits⟩ :=
    VecStorage_fits heapId capacity ptr input $$ Hstorage
  ihave Hinput := VecStorage_bytes heapId capacity ptr input $$ Hstorage
  simp only [func6AfterRead_cons, afterReadLocalsRm]
  wasm_twp_pures [twp_localGet twp_const twp_add twp_localGet twp_localGet]
    rewriting [show (16 : UInt32) + func6Base = func6Base + 16 by decide]
  have Hdecode := func7_correct (hlc := hlc) func6Base (func6Base + 16)
    ptr (UInt32.ofNat input.length) heapId input ((head.drop 16).take 20)
    low dataBytes storedCursor frontier history [] output false
    (callerLocals :=
      ⟨[], [Value.i32 func6Base, .i32 (UInt32.ofNat input.length),
        .i32 capacity, .i32 ptr, .i32 aux4, .i64 0], []⟩)
    (stack := []) (code := rmAfterDecode afterTail) (arity := arity)
    (remainder := remainder) (controls := controls) (calls := calls)
    (s := s) (E := E) (Φ := Φ)
  unfold CallContract callExpr at Hdecode
  simp only [List.cons_append, List.nil_append] at Hdecode
  iapply Hdecode
  isplitl_exacts [Hruntime Hsp Hbelow Hslot Hinput Hdata Hbump Hstreams]
  isplitl_pureexact ⟨by simp [hhead], hlenNat.symm, by decide, by decide,
    hdata⟩
  isplit
  · -- the accept arm
    iintro %cap' %buffer %spare' %below' %storedCursor' %frontier'
      %history' %haccept Hruntime Hsp Hbelow Hslot Hbytes Hdata Hbuf Hbump
      Hstreams %hfacts
    isimp only [ResumeWP, resumeExpr, List.nil_append]
    obtain ⟨hcapBound, hspareLen, _hzero, halign⟩ := hfacts
    have hn := acceptedEntries_bound input haccept hinput
    have hmaxEntries := acceptedEntries_le_max input capacity ptr frontier
      haccept hpush hfits
    ihave ⟨%b, Hbelow⟩ := Hrestore $$ %below' Hbelow
    -- the static singleton table is the first 24 bytes of the segment
    icases (ByteSlice_split_at entryStackTop 24 dataBytes
      (by simp [hdata, dataSegmentSize])).mp $$ Hdata with ⟨Hstatic, _Hgap⟩
    isimp only [UInt32.reduceToNat, hstatic] at Hstatic
    iclear Hbytes
    ihave ⟨H16, H20, H24, H28, H32⟩ :=
      ByteSlice_five_words (func6Base + 16) 0 (leadingKey input) cap'
        buffer (pairCount input) $$ Hslot
    simp only [rmAfterDecode]
    wasm_twp_pures [twp_block]
    simp only [List.drop_zero]
    rw [rmOuterFrame_literal]
    simp only [rmOuterBody]
    wasm_twp_pures [twp_block]
    simp only [List.drop_zero]
    rw [rmOkFrame_literal]
    simp only [rmOkArm_shape]
    wasm_twp_pures [twp_localGet]
    wasm_twp_rebind twp_load32 (address := func6Base) (offset := 16) 0
      h16.1 h16.2.1 h16.2.2.1 h16.2.2.2 with H16
    wasm_twp_pures [twp_brIfZero]
    ihave Hslot :=
      ByteSlice_of_five_words (func6Base + 16) 0 (leadingKey input) cap'
        buffer (pairCount input) (by decide) $$ [H16 H20 H24 H28 H32]
    · iframe H16 H20 H24 H28 H32
    iapply twp_rm_accept_copy hfunc2 heapId cap' buffer oldLen
      (wordPair oldCap oldPtr) input (keyPayload input) spare'
      ((head.drop 36).take 12) (chunk.take 40) keysBefore b
      storedCursor' frontier' history' output haccept hn
      (by omega) (by simp [hhead]) (by simp [hchunk]) hkeys
      (keyPayload_serialize input haccept).symm hcapBound hspareLen hstate
      halign
    iframe
  · isplit
    · -- the reject arm
      iintro %word1 %word2 %word3 %word4 %below' %storedCursor' %frontier'
        %history' %hreject Hruntime Hsp Hbelow Hslot Hbytes Hdata Hbump
        Hstreams %hword1
      isimp only [ResumeWP, resumeExpr, List.nil_append]
      ihave ⟨H16, H20, H24, _H28, _H32⟩ :=
        ByteSlice_five_words (func6Base + 16) 1 word1 word2 word3 word4 $$
        Hslot
      isimp only [show func6Base + 16 + 4 = func6Base + 20 by decide]
        at H20
      isimp only [show func6Base + 16 + 4 + 4 = func6Base + 24 by decide]
        at H24
      simp only [rmAfterDecode]
      wasm_twp_pures [twp_block]
      simp only [List.drop_zero]
      rw [rmOuterFrame_literal]
      simp only [rmOuterBody]
      wasm_twp_pures [twp_block]
      simp only [List.drop_zero]
      rw [rmOkFrame_literal]
      simp only [rmOkArm_shape]
      wasm_twp_pures [twp_localGet]
      wasm_twp_rebind twp_load32 (address := func6Base) (offset := 16) 1
        h16.1 h16.2.1 h16.2.2.1 h16.2.2.2 with H16
      iapply twp_brIf (by decide) (by rfl)
      simp only [rmOkFrame, List.take_zero, List.nil_append]
      rw [removeOutput_of_not_accepts input hreject, List.append_nil]
      iapply twp_rm_reject word1 word2
      iframe
    · iintro %remaining' Hstreams
      iapply Hoom
      isimp only [ExportOOM]
      iexists remaining', output
      iexact Hstreams

end Project.RustHashMap.RemoveTailProof
