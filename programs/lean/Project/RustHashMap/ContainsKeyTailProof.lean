import Project.RustHashMap.LookupTailContracts
import Project.RustHashMap.LookupPures
import Project.RustHashMap.LookupContracts
import Project.RustHashMap.Func7Proof
import Project.RustHashMap.Func9Proof

/-!
# The tail of the `map_contains_key` driver: the proof

`Project.RustHashMap.LookupTailContracts.ContainsKeyTailSpec` is the
contract of everything after the read phase of absolute `func 19`.  This
module proves it.  `collect_entries`, absolute `func 5`, is the one open
contract; every other callee is a proved theorem.

The proof follows the block structure of
`Project.RustHashMap.LookupTailDefs`, one lemma per control block, from the
innermost outward.  Every lemma names its control frames, because
`branchTarget?` reads them.

## The five frames

`ckOuterFrame` is the block that every path leaves.  Its continuation is
the stack epilogue.  `ckDecodeFrame` is the block that the allocator
failure follows; the allocator never returns zero, so that continuation is
dead.  `ckOkFrame` is the block that the reject guard leaves; its
continuation is the reject arm.  `ckFreeInputFrame` and `ckDropErrorFrame`
are the two small blocks of the free tests.

## Why the table drop needs no reasoning

Both arms of each guard in `ckTableDrop` reach `ckOuterFrame`.  The
addresses that the drop computes are unsigned and wrap, and the free goes
through the empty body of absolute `func 60`.  So the drop needs neither a
bound on the bucket count nor a token for the block.
-/

namespace Project.RustHashMap.ContainsKeyTailProof

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
open Project.RustHashMap.FrameCells
open Project.RustHashMap.KeyDecoderContract
open Project.RustHashMap.LookupContracts
open Project.RustHashMap.LookupPures
open Project.RustHashMap.DeallocNoop
open Project.RustHashMap.Func55Proof
open Project.RustHashMap.Func7Proof
open Project.RustHashMap.Func9Proof
open Project.RustHashMap.Func30Proof
open Project.RustHashMap.ImportProofs
open Project.RustHashMap.ReadAll
open Project.RustHashMap.ContainsKeyRead
open Project.RustHashMap.LookupTailDefs
open Project.RustHashMap.DriverTail
open Project.RustHashMap.DriverTailProof
open scoped Wasm.SmallStep.Outcome

/-! ## The suffixes of the code

Each call needs the code that follows it as an explicit argument, so each
suffix gets a name. -/

/-- The free of the reply buffer, and the table drop after it.  WAT lines
4706 to 4737. -/
def ckReplyFree : Program :=
  .localGet 1 :: .const 1024 :: .const 1 :: .call 60 :: ckTableDrop

/-- The write of the answer byte to the output stream.  WAT lines 4703 to
4737. -/
def ckReplyWrite : Program :=
  .localGet 1 :: .const 1 :: .call 64 :: ckReplyFree

/-- The store of the answer byte in the first byte of the buffer.  WAT
lines 4700 to 4737. -/
def ckReplyStore : Program :=
  .localGet 1 :: .localGet 3 :: .store8 0 :: ckReplyWrite

/-- The null test of the allocation result.  WAT lines 4697 to 4737. -/
def ckReplyAfterAlloc : Program :=
  .localTee 1 :: .eqz :: .br_if 1 :: ckReplyStore

theorem ckReply_shape :
    ckReply = .const 1024 :: .const 1 :: .call 58 :: ckReplyAfterAlloc := rfl

/-- The kernel call, the marker call and the reply.  WAT lines 4688 to
4737. -/
def ckAfterCollect : Program :=
  .localGet 0 :: .const 48 :: .add :: .localGet 1 :: .call 12 ::
    .localSet 3 :: .call 33 :: ckReply

/-- The collect call and everything after it.  WAT lines 4684 to 4737. -/
def ckCollectAndReply : Program :=
  .localGet 0 :: .const 48 :: .add :: .localGet 0 :: .call 5 :: ckAfterCollect

/-- The accept arm after its guard: the header copy, the release of the
input, and the collect call.  WAT lines 4664 to 4737. -/
def ckOkBody : Program :=
  .localGet 0 :: .localGet 0 :: .load64 24 :: .store64 0 :: .localGet 0 ::
    .localGet 0 :: .load32 32 :: .store32 8 :: .localGet 0 :: .load32 20 ::
    .localSet 1 :: .block 0 0 ckFreeInput :: ckCollectAndReply

theorem ckOkArm_shape :
    ckOkArm = .localGet 0 :: .load32 16 :: .br_if 0 :: ckOkBody := rfl

/-- The reject arm after the drop of the error string.  WAT lines 4752 to
4759. -/
def ckErrTail : Program :=
  [.localGet 2, .eqz, .br_if 1, .localGet 3, .localGet 2, .const 1,
    .call 60, .br 1]

theorem ckErrArm_shape :
    ckErrArm = .block 0 0 ckDropError :: ckErrTail := rfl

/-- The outer block and the stack epilogue, which is what follows the call
of the key decoder. -/
def ckAfterDecode (afterTail : Program) : Program :=
  .block 0 0 ckOuterBody :: (ckEpilogue ++ afterTail)

/-- The tail of the driver in cons form, with the decoder call exposed. -/
theorem func16AfterRead_cons (afterTail : Program) :
    func16AfterRead ++ afterTail =
      .localGet 0 :: .const 16 :: .add :: .localGet 3 :: .localGet 1 ::
        .call 10 :: ckAfterDecode afterTail := rfl

/-! ## The control frames of the tail -/

/-- The outermost block of the tail.  Its continuation is the stack
epilogue, so every path that leaves it returns. -/
def ckOuterFrame (afterTail : Program) : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body := ckOuterBody, continuation := ckEpilogue ++ afterTail,
    belowStack := [] }

theorem ckOuterFrame_literal (afterTail : Program) :
    ({ kind := .block, paramArity := 0, resultArity := 0,
       body := ckOuterBody, continuation := ckEpilogue ++ afterTail,
       belowStack := [] } : ControlFrame) = ckOuterFrame afterTail := rfl

/-- The block that the reply leaves when the allocator returns zero.  The
allocator never returns zero, so the continuation is dead. -/
def ckDecodeFrame : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body := ckDecodeBlock,
    continuation := [.const 1, .const 1024, .call 99, .unreachable],
    belowStack := [] }

theorem ckDecodeFrame_literal :
    ({ kind := .block, paramArity := 0, resultArity := 0,
       body := ckDecodeBlock,
       continuation := [.const 1, .const 1024, .call 99, .unreachable],
       belowStack := [] } : ControlFrame) = ckDecodeFrame := rfl

/-- The block that the reject guard leaves.  Its continuation is the reject
arm. -/
def ckOkFrame : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body := ckOkArm, continuation := ckErrArm, belowStack := [] }

theorem ckOkFrame_literal :
    ({ kind := .block, paramArity := 0, resultArity := 0,
       body := ckOkArm, continuation := ckErrArm,
       belowStack := [] } : ControlFrame) = ckOkFrame := rfl

/-- The block that releases the input byte vector before the collect
call. -/
def ckFreeInputFrame : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body := ckFreeInput, continuation := ckCollectAndReply,
    belowStack := [] }

theorem ckFreeInputFrame_literal :
    ({ kind := .block, paramArity := 0, resultArity := 0,
       body := ckFreeInput, continuation := ckCollectAndReply,
       belowStack := [] } : ControlFrame) = ckFreeInputFrame := rfl

/-- The block that drops the decoded error string on the reject arm. -/
def ckDropErrorFrame : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body := ckDropError, continuation := ckErrTail, belowStack := [] }

theorem ckDropErrorFrame_literal :
    ({ kind := .block, paramArity := 0, resultArity := 0,
       body := ckDropError, continuation := ckErrTail,
       belowStack := [] } : ControlFrame) = ckDropErrorFrame := rfl

/-! ## The stack epilogue -/

set_option maxHeartbeats 2000000 in
/-- The stack pointer restore that ends every path.  WAT lines 4766 to
4769. -/
theorem twp_ck_stack_epilogue [WasmSmallStepGS hlc Universal.State]
    {l1 l2 l3 l4 : UInt32} {afterTail : Program}
    {finalOutput : List UInt8} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp} :
    iprop(RuntimeContext ∗ StackPointer func16Base ∗
      Streams [] finalOutput false ∗
      TailDone finalOutput afterTail arity remainder controls calls s E Φ) ⊢
      WP (.running
          ⟨⟨[], [Value.i32 func16Base, .i32 l1, .i32 l2, .i32 l3, .i32 l4],
              []⟩,
            ckEpilogue ++ afterTail, arity, remainder, controls, calls⟩ :
            Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hstreams, Hcont⟩
  isimp only [StackPointer] at Hsp
  isimp only [TailDone] at Hcont
  simp only [ckEpilogue, List.cons_append, List.nil_append]
  wasm_twp_pures [twp_localGet twp_const twp_add]
  rw [show (304 : UInt32) + func16Base = entryStackTop by decide]
  wasm_twp_rebind twp_globalSet with Hsp
  ihave Hsp : StackPointer entryStackTop $$ [Hsp]
  · unfold StackPointer
    iexact Hsp
  iapply Hcont $$ %(⟨[], [Value.i32 func16Base, .i32 l1, .i32 l2, .i32 l3,
    .i32 l4], []⟩ : Locals) Hruntime Hsp Hstreams

/-! ## Small ownership helpers -/

/-- A one-byte slice is the address bound and one owned byte cell. -/
theorem ByteSlice_single [WasmHeapGS Universal.State]
    (ptr : UInt32) (b : UInt8) :
    Slices.ByteSlice (α := Universal.State) 0 ptr [b] ⊣⊢
      iprop(⌜ptr.toNat + 1 < UInt32.size⌝ ∗
        pointsTo (GF := WasmHeapGF Universal.State) (H := WasmHeapMap)
          ⟨0, ptr⟩ (DFrac.own 1) (some b)) := by
  unfold Slices.ByteSlice
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, pointsToBytes]
  exact BI.sep_congr .rfl BI.sep_emp

/-- A twenty-byte slot that holds five little-endian words is five cells.
The accept arm reads four of them out of the decoder output slot. -/
theorem ByteSlice_five_words [WasmHeapGS Universal.State]
    (ptr : UInt32) (w0 w1 w2 w3 w4 : UInt32) :
    Slices.ByteSlice (α := Universal.State) 0 ptr
        (WordCodec.u32le.serialize [w0, w1, w2, w3, w4]) ⊢
      iprop(pointsTo_u32 0 ptr w0 ∗ pointsTo_u32 0 (ptr + 4) w1 ∗
        pointsTo_u32 0 (ptr + 4 + 4) w2 ∗
        pointsTo_u32 0 (ptr + 4 + 4 + 4) w3 ∗
        pointsTo_u32 0 (ptr + 4 + 4 + 4 + 4) w4) := by
  iintro Hbytes
  isimp only [Slices.ByteSlice] at Hbytes
  icases Hbytes with ⟨%_hnowrap, Hbytes⟩
  ihave Harray :=
    (Slices.arrayAt_eq_wordCells (α := Universal.State) 0 ptr
      [w0, w1, w2, w3, w4]).mpr $$ Hbytes
  isimp only [arrayAt] at Harray
  icases Harray with ⟨H0, H1, H2, H3, H4, _Hemp⟩
  isplitl_exacts [H0 H1 H2 H3]
  iexact H4

/-! ## The table drop -/

set_option maxHeartbeats 2000000 in
/-- The drop of the hash table, which is the last step of the reply.  Both
arms of both guards reach `ckOuterFrame`, so neither guard has to be
decided.  The free goes through the empty body of absolute `func 60`, so
the drop needs no token for the block.  The addresses that it computes are
unsigned and wrap, so they need no bound either.  WAT lines 4712 to
4737. -/
theorem twp_ck_table_drop [WasmSmallStepGS hlc Universal.State]
    {l1 l2 l3 l4 ctrl mask : UInt32} {afterTail : Program}
    {finalOutput : List UInt8} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp} :
    iprop(RuntimeContext ∗ StackPointer func16Base ∗
      Streams [] finalOutput false ∗
      pointsTo_u32 0 (func16Base + 48) ctrl ∗
      pointsTo_u32 0 (func16Base + 52) mask ∗
      TailDone finalOutput afterTail arity remainder controls calls s E Φ) ⊢
      WP (.running
          ⟨⟨[], [Value.i32 func16Base, .i32 l1, .i32 l2, .i32 l3, .i32 l4],
              []⟩,
            ckTableDrop, arity, remainder,
            ckOkFrame :: ckDecodeFrame :: ckOuterFrame afterTail :: controls,
            calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hstreams, Hctrl, Hmask, Hcont⟩
  simp only [ckTableDrop]
  wasm_twp_pures [twp_localGet]
  wasm_twp_rebind twp_load32 (address := func16Base) (offset := 52) mask
    (by decide) (by decide) (by decide) (by decide) with Hmask
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  by_cases hmask : mask = 0
  · iapply twp_eqz (result := 1) (by simp [hmask])
    iapply twp_brIf (by decide) (by rfl)
    simp only [ckOuterFrame, List.take_zero, List.nil_append]
    iapply twp_ck_stack_epilogue
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
      simp only [ckOuterFrame, List.take_zero, List.nil_append]
      iapply twp_ck_stack_epilogue
      iframe
    · iapply twp_eqz (result := 0) (by simp [hsize])
      wasm_twp_pures [twp_brIfZero twp_localGet]
      wasm_twp_rebind twp_load32 (address := func16Base) (offset := 48) ctrl
        (by decide) (by decide) (by decide) (by decide) with Hctrl
      wasm_twp_pures [twp_localGet twp_sub twp_const twp_add twp_localGet
        twp_const]
      have Hfree := func57_noop_correct (hlc := hlc)
        ((4294967288 : UInt32) + (ctrl - mask <<< 3))
        ((17 : UInt32) + (mask + mask <<< 3)) 8
        (callerLocals :=
          ⟨[], [Value.i32 func16Base,
            .i32 ((17 : UInt32) + (mask + mask <<< 3)), .i32 l2,
            .i32 (mask <<< 3), .i32 l4], []⟩)
        (stack := []) (code := [.br 2]) (arity := arity)
        (remainder := remainder)
        (controls :=
          ckOkFrame :: ckDecodeFrame :: ckOuterFrame afterTail :: controls)
        (calls := calls) (s := s) (E := E) (Φ := Φ)
      unfold CallContract callExpr at Hfree
      simp only [List.cons_append, List.nil_append] at Hfree
      iapply Hfree
      isplitl_exact Hruntime
      · iintro Hruntime
        isimp only [ResumeWP, resumeExpr, List.nil_append]
        iapply twp_br (by rfl)
        simp only [ckOuterFrame, List.take_zero, List.nil_append]
        iapply twp_ck_stack_epilogue
        iframe

/-! ## The reply -/

set_option maxHeartbeats 2000000 in
/-- The reply.  It allocates 1024 bytes with alignment 1, stores the answer
in the first of them, writes that byte to the output stream, frees the
buffer and drops the table.  The null test after the allocation is dead,
because a live block never starts at address zero.  WAT lines 4696 to
4737. -/
theorem twp_ck_reply [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory) (output : List UInt8)
    {l1 l2 answer l4 ctrl mask : UInt32} {afterTail : Program}
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp} :
    iprop(RuntimeContext ∗ StackPointer func16Base ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams [] output false ∗
      pointsTo_u32 0 (func16Base + 48) ctrl ∗
      pointsTo_u32 0 (func16Base + 52) mask ∗
      TailDone (output ++ [answer.toUInt8]) afterTail arity remainder
        controls calls s E Φ ∗
      (ExportOOM -∗ Φ (.trapped (.host OOM.trapMessage)))) ⊢
      WP (.running
          ⟨⟨[], [Value.i32 func16Base, .i32 l1, .i32 l2, .i32 answer,
              .i32 l4], []⟩,
            ckReply, arity, remainder,
            ckOkFrame :: ckDecodeFrame :: ckOuterFrame afterTail :: controls,
            calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hbump, Hstreams, Hctrl, Hmask, Hcont, Hoom⟩
  simp only [ckReply_shape]
  wasm_twp_pures [twp_const twp_const]
  have Halloc := func55_correct (hlc := hlc) 1024 1
    { size := 1024, alignment := 1 } heapId storedCursor frontier history
    [] output false
    (callerLocals :=
      ⟨[], [Value.i32 func16Base, .i32 l1, .i32 l2, .i32 answer, .i32 l4],
        []⟩)
    (stack := []) (code := ckReplyAfterAlloc) (arity := arity)
    (remainder := remainder)
    (controls :=
      ckOkFrame :: ckDecodeFrame :: ckOuterFrame afterTail :: controls)
    (calls := calls) (s := s) (E := E) (Φ := Φ)
  unfold CallContract callExpr at Halloc
  simp only [List.cons_append, List.nil_append] at Halloc
  iapply Halloc
  isplitl_exacts [Hruntime Hbump Hstreams]
  have hmatches :
      AllocLayout.Matches { size := 1024, alignment := 1 } 1024 1 :=
    ⟨by decide, by decide⟩
  have hvalid : AllocLayout.Valid { size := 1024, alignment := 1 } :=
    ⟨by decide, by decide, ⟨0, rfl⟩, by decide, by decide, by decide,
      by decide⟩
  isplitl_pureexact ⟨hmatches, hvalid, Or.inl trivial⟩
  cases hdecision : classifyBump frontier { size := 1024, alignment := 1 } with
  | oom =>
      isimp only [AllocContinuation, hdecision]
      iintro Hbump Hstreams
      iapply Hoom
      isimp only [ExportOOM]
      iexists ([] : List UInt8), output
      iexact Hstreams
  | success blockBase finish =>
      isimp only [AllocContinuation, hdecision]
      isplit
      · iintro %bytes Hruntime Hbump Hblock Hstreams
        isimp only [ResumeWP, resumeExpr, List.nil_append, List.append_nil]
        iunfold LiveBlock at Hblock
        icases Hblock with ⟨Htoken, Hbytes, %hfacts⟩
        obtain ⟨hlength, hnonnull, _⟩ := hfacts
        have hbytes : bytes.length = 1024 := hlength
        obtain ⟨b0, rest, hcons⟩ : ∃ b0 rest, bytes = b0 :: rest := by
          cases bytes with
          | nil => exact absurd hbytes (by simp)
          | cons b0 rest => exact ⟨b0, rest, rfl⟩
        subst hcons
        simp only [ckReplyAfterAlloc]
        wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
          Nat.reduceSub, List.set]
        iapply twp_eqz (result := 0) (by simp [hnonnull])
        wasm_twp_pures [twp_brIfZero]
        simp only [ckReplyStore]
        wasm_twp_pures [twp_localGet twp_localGet]
        icases (ByteSlice_split_at blockBase 1 (b0 :: rest)
          (by simp)).mp $$ Hbytes with ⟨Hhead, _Hrest⟩
        isimp only [UInt32.reduceToNat,
          show (b0 :: rest).take 1 = [b0] from rfl] at Hhead
        icases (ByteSlice_single blockBase b0).mp $$ Hhead with
          ⟨%hbound, Hcell⟩
        iapply twp_store8_addr_gen (address := blockBase) (value := answer)
          b0 $$ Hcell
        iintro Hcell
        ihave Hslice : Slices.ByteSlice 0 blockBase [answer.toUInt8] $$
            [Hcell]
        · iapply (ByteSlice_single blockBase answer.toUInt8).mpr
          isplitl_pureexact hbound
          · iexact Hcell
        simp only [ckReplyWrite]
        wasm_twp_pures [twp_localGet twp_const]
        have Hwrite := func61_correct (hlc := hlc) blockBase 1
          [answer.toUInt8] [] output false
          (callerLocals :=
            ⟨[], [Value.i32 func16Base, .i32 blockBase, .i32 l2, .i32 answer,
              .i32 l4], []⟩)
          (stack := []) (code := ckReplyFree) (arity := arity)
          (remainder := remainder)
          (controls :=
            ckOkFrame :: ckDecodeFrame :: ckOuterFrame afterTail :: controls)
          (calls := calls) (s := s) (E := E) (Φ := Φ)
        unfold CallContract callExpr at Hwrite
        simp only [List.cons_append, List.nil_append] at Hwrite
        iapply Hwrite
        isplitl_exacts [Hruntime Hstreams Hslice]
        isplitl_pureexact ⟨by simp, by decide⟩
        iintro Hruntime Hstreams Hslice
        isimp only [ResumeWP, resumeExpr, List.nil_append]
        simp only [ckReplyFree]
        wasm_twp_pures [twp_localGet twp_const twp_const]
        have Hfree := func57_noop_correct (hlc := hlc) blockBase 1024 1
          (callerLocals :=
            ⟨[], [Value.i32 func16Base, .i32 blockBase, .i32 l2, .i32 answer,
              .i32 l4], []⟩)
          (stack := []) (code := ckTableDrop) (arity := arity)
          (remainder := remainder)
          (controls :=
            ckOkFrame :: ckDecodeFrame :: ckOuterFrame afterTail :: controls)
          (calls := calls) (s := s) (E := E) (Φ := Φ)
        unfold CallContract callExpr at Hfree
        simp only [List.cons_append, List.nil_append] at Hfree
        iapply Hfree
        isplitl_exact Hruntime
        · iintro Hruntime
          isimp only [ResumeWP, resumeExpr, List.nil_append]
          iapply twp_ck_table_drop
          iframe
      · iintro Hbump Hstreams
        iapply Hoom
        isimp only [ExportOOM]
        iexists ([] : List UInt8), output
        iexact Hstreams

/-! ## The kernel call -/

set_option maxHeartbeats 2000000 in
/-- The lookup kernel, the marker call and the reply.  The answer that the
kernel returns is the borsh `bool` that the driver writes out.  WAT lines
4688 to 4737. -/
theorem twp_ck_lookup [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (k0 k1 : UInt64)
    (entries : HashMap.Map UInt32 UInt32) (key : UInt32)
    (storedCursor : UInt32) (frontier : Nat) (history : AllocationHistory)
    (output : List UInt8)
    {l2 l3 l4 : UInt32} {afterTail : Program}
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hn : entries.length ≤ 2 ^ 30) :
    iprop(RuntimeContext ∗ StackPointer func16Base ∗
      HashMap.Table.MapAt 0 (func16Base + 48) k0 k1 entries ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams [] output false ∗
      TailDone (output ++ Borsh.bool (HashMap.Table.containsKey
            (HashMap.SipHash.hashU32 k0 k1)
            (HashMap.Table.ofEntries (HashMap.SipHash.hashU32 k0 k1) entries)
            key))
        afterTail arity remainder controls calls s E Φ ∗
      (ExportOOM -∗ Φ (.trapped (.host OOM.trapMessage)))) ⊢
      WP (.running
          ⟨⟨[], [Value.i32 func16Base, .i32 key, .i32 l2, .i32 l3, .i32 l4],
              []⟩,
            ckAfterCollect, arity, remainder,
            ckOkFrame :: ckDecodeFrame :: ckOuterFrame afterTail :: controls,
            calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hmap, Hbump, Hstreams, Hcont, Hoom⟩
  obtain ⟨hwf, hclean, _, _⟩ :=
    HashMap.Table.wf_ofEntries_u32 k0 k1 entries hn
  isimp only [borsh_bool_eq_byte] at Hcont
  isimp only [HashMap.Table.MapAt] at Hmap
  simp only [ckAfterCollect]
  wasm_twp_pures [twp_localGet twp_const twp_add twp_localGet]
    rewriting [show (48 : UInt32) + func16Base = func16Base + 48 by decide]
  have Hlookup := func9_correct (hlc := hlc) (func16Base + 48) key k0 k1
    (HashMap.Table.ofEntries (HashMap.SipHash.hashU32 k0 k1) entries)
    (callerLocals :=
      ⟨[], [Value.i32 func16Base, .i32 key, .i32 l2, .i32 l3, .i32 l4], []⟩)
    (stack := []) (code := .localSet 3 :: .call 33 :: ckReply)
    (arity := arity) (remainder := remainder)
    (controls :=
      ckOkFrame :: ckDecodeFrame :: ckOuterFrame afterTail :: controls)
    (calls := calls) (s := s) (E := E) (Φ := Φ)
  unfold CallContract callExpr at Hlookup
  simp only [List.append_nil] at Hlookup
  iapply Hlookup
  isplitl_exacts [Hruntime Hmap]
  isplitl_pureexact ⟨hwf, hclean, by decide⟩
  iintro Hruntime Hmap
  isimp only [ResumeWP, resumeExpr, List.nil_append, List.append_nil]
  wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  have Hmarker := func30_correct (hlc := hlc)
    (callerLocals :=
      ⟨[], [Value.i32 func16Base, .i32 key, .i32 l2,
        .i32 (if HashMap.Table.containsKey (HashMap.SipHash.hashU32 k0 k1)
            (HashMap.Table.ofEntries (HashMap.SipHash.hashU32 k0 k1) entries)
            key = true then (1 : UInt32) else 0),
        .i32 l4], []⟩)
    (stack := []) (code := ckReply) (arity := arity) (remainder := remainder)
    (controls :=
      ckOkFrame :: ckDecodeFrame :: ckOuterFrame afterTail :: controls)
    (calls := calls) (s := s) (E := E) (Φ := Φ)
  unfold CallContract callExpr at Hmarker
  simp only [List.nil_append] at Hmarker
  iapply Hmarker
  isplitl_exact Hruntime
  · iintro Hruntime
    isimp only [ResumeWP, resumeExpr, List.nil_append]
    isimp only [HashMap.Table.HashMapAt] at Hmap
    icases Hmap with ⟨Htable, Hk0, Hk1⟩
    ihave Hheader := TableAt_header_words (func16Base + 48)
      (HashMap.Table.ofEntries (HashMap.SipHash.hashU32 k0 k1) entries) $$
      Htable
    icases Hheader with ⟨%ctrl, %mask, Hctrl, Hmask, Hitems⟩
    isimp only [show func16Base + 48 + 4 = func16Base + 52 by decide] at Hmask
    iclear Hk0 Hk1 Hitems
    iapply twp_ck_reply heapId storedCursor frontier history output
    iframe

/-! ## The collect call -/

set_option maxHeartbeats 2000000 in
/-- The build of the hash table and the answer.  `collect_entries` takes
the pair buffer and gives the map value back in the first 32 bytes of the
chunk buffer.  The answer does not name the two seeds, because
`HashMap.Table.containsKey_ofEntries_u32` removes them.  WAT lines 4682 to
4737. -/
theorem twp_ck_collect [WasmSmallStepGS hlc Universal.State]
    (hfunc2 : CollectContract.Func2Spec (hlc := hlc))
    (heapId : GName) (cap bufPtr len key : UInt32)
    (entries : HashMap.Map UInt32 UInt32)
    (payload spare mapBefore keysBefore below : List UInt8)
    (storedCursor : UInt32) (frontier : Nat) (history : AllocationHistory)
    (output : List UInt8)
    {l2 l3 l4 : UInt32} {afterTail : Program}
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hmapBefore : mapBefore.length = 32)
    (hkeys : keysBefore.length = randomStateSize)
    (hpayload : payload = CollectContract.entryCodec.serialize entries)
    (hentries : entries.length = len.toNat)
    (hcap : len.toNat ≤ cap.toNat)
    (hspare : spare.length = 8 * (cap.toNat - len.toNat))
    (hn : entries.length ≤ 2 ^ 30)
    (hstate : keysBefore[16]? ≠ some 2)
    (hmax : len.toNat ≤ maxTableCapacity)
    (halign : bufPtr.toNat % 4 = 0) :
    iprop(RuntimeContext ∗ StackPointer func16Base ∗
      StackBelow func16Base CollectContract.collectDepth below ∗
      Slices.ByteSlice 0 (func16Base + 48) mapBefore ∗
      pointsTo_u32 0 func16Base cap ∗
      pointsTo_u32 0 (func16Base + 4) bufPtr ∗
      pointsTo_u32 0 (func16Base + 8) len ∗
      Slices.ByteSlice 0 bufPtr (payload ++ spare) ∗
      Slices.ByteSlice 0 randomStateCell keysBefore ∗
      Slices.ByteSlice 0 entryStackTop staticTableBytes ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams [] output false ∗
      TailDone (output ++ Borsh.bool
          (HashMap.containsKey (HashMap.ofEntries entries) key))
        afterTail arity remainder controls calls s E Φ ∗
      (ExportOOM -∗ Φ (.trapped (.host OOM.trapMessage)))) ⊢
      WP (.running
          ⟨⟨[], [Value.i32 func16Base, .i32 key, .i32 l2, .i32 l3, .i32 l4],
              []⟩,
            ckCollectAndReply, arity, remainder,
            ckOkFrame :: ckDecodeFrame :: ckOuterFrame afterTail :: controls,
            calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hbelow, Hmap, Hcap, Hptr, Hlen, Hbuf, Hkeys, Hstatic,
    Hbump, Hstreams, Hcont, Hoom⟩
  ihave ⟨Hctrl, Hhdr, Hzero⟩ :=
    CollectContract.staticTable_resources $$ Hstatic
  simp only [ckCollectAndReply]
  wasm_twp_pures [twp_localGet twp_const twp_add twp_localGet]
    rewriting [show (48 : UInt32) + func16Base = func16Base + 48 by decide]
  have Hcollect := hfunc2 func16Base (func16Base + 48) func16Base
    cap bufPtr len heapId entries payload spare mapBefore keysBefore below
    storedCursor frontier history [] output false
    (callerLocals :=
      ⟨[], [Value.i32 func16Base, .i32 key, .i32 l2, .i32 l3, .i32 l4], []⟩)
    (stack := []) (code := ckAfterCollect) (arity := arity)
    (remainder := remainder)
    (controls :=
      ckOkFrame :: ckDecodeFrame :: ckOuterFrame afterTail :: controls)
    (calls := calls) (s := s) (E := E) (Φ := Φ)
  unfold CallContract callExpr at Hcollect
  simp only [List.append_nil] at Hcollect
  iapply Hcollect
  isplitl_exacts [Hruntime Hsp Hbelow Hmap Hcap Hptr Hlen Hbuf Hkeys Hctrl
    Hhdr Hzero Hbump Hstreams]
  isplitl_pureexact ⟨hmapBefore, hkeys, hstate, hpayload, hentries, hcap, hmax,
    hspare, halign, by decide, by decide, by decide⟩
  isplit
  · iintro %k0 %k1 %below' %keysAfter %storedCursor' %frontier' %history'
      Hruntime Hsp Hbelow Hmapv Hcap Hptr Hlen Hkeys Hhdr Hzero Hbump Hstreams
      %hfacts
    isimp only [ResumeWP, resumeExpr, List.nil_append, List.append_nil]
    iclear Hhdr Hzero
    isimp only [show HashMap.containsKey (HashMap.ofEntries entries) key =
      HashMap.Table.containsKey (HashMap.SipHash.hashU32 k0 k1)
        (HashMap.Table.ofEntries (HashMap.SipHash.hashU32 k0 k1) entries)
        key from
      (HashMap.Table.containsKey_ofEntries_u32 k0 k1 entries hn key).symm]
      at Hcont
    iapply twp_ck_lookup heapId k0 k1 entries key storedCursor' frontier'
      history' output hn
    iframe
  · iintro %remaining Hstreams
    iapply Hoom
    isimp only [ExportOOM]
    iexists remaining, output
    iexact Hstreams

/-! ## The header copy of the accept arm -/

set_option maxHeartbeats 2000000 in
/-- The accept arm after its guard.  The arm moves the decoded vector
header into the entries header at frame offset 0, moves the leading key
into local 1, and releases the input byte vector.  WAT lines 4664 to
4737. -/
theorem twp_ck_accept_copy [WasmSmallStepGS hlc Universal.State]
    (hfunc2 : CollectContract.Func2Spec (hlc := hlc))
    (heapId : GName) (cap bufPtr len key oldLen : UInt32)
    (oldPair : UInt64)
    (entries : HashMap.Map UInt32 UInt32)
    (payload spare mapBefore keysBefore below : List UInt8)
    (storedCursor : UInt32) (frontier : Nat) (history : AllocationHistory)
    (output : List UInt8)
    {l1 l2 l3 l4 : UInt32} {afterTail : Program}
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hmapBefore : mapBefore.length = 32)
    (hkeys : keysBefore.length = randomStateSize)
    (hpayload : payload = CollectContract.entryCodec.serialize entries)
    (hentries : entries.length = len.toNat)
    (hcap : len.toNat ≤ cap.toNat)
    (hspare : spare.length = 8 * (cap.toNat - len.toNat))
    (hn : entries.length ≤ 2 ^ 30)
    (hstate : keysBefore[16]? ≠ some 2)
    (hmax : len.toNat ≤ maxTableCapacity)
    (halign : bufPtr.toNat % 4 = 0) :
    iprop(RuntimeContext ∗ StackPointer func16Base ∗
      StackBelow func16Base CollectContract.collectDepth below ∗
      pointsTo_u64 0 func16Base oldPair ∗
      pointsTo_u32 0 (func16Base + 8) oldLen ∗
      pointsTo_u32 0 (func16Base + 20) key ∗
      pointsTo_u64 0 (func16Base + 24) (wordPair cap bufPtr) ∗
      pointsTo_u32 0 (func16Base + 32) len ∗
      Slices.ByteSlice 0 (func16Base + 48) mapBefore ∗
      Slices.ByteSlice 0 bufPtr (payload ++ spare) ∗
      Slices.ByteSlice 0 randomStateCell keysBefore ∗
      Slices.ByteSlice 0 entryStackTop staticTableBytes ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams [] output false ∗
      TailDone (output ++ Borsh.bool
          (HashMap.containsKey (HashMap.ofEntries entries) key))
        afterTail arity remainder controls calls s E Φ ∗
      (ExportOOM -∗ Φ (.trapped (.host OOM.trapMessage)))) ⊢
      WP (.running
          ⟨⟨[], [Value.i32 func16Base, .i32 l1, .i32 l2, .i32 l3, .i32 l4],
              []⟩,
            ckOkBody, arity, remainder,
            ckOkFrame :: ckDecodeFrame :: ckOuterFrame afterTail :: controls,
            calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hbelow, Hpair0, Hlen0, Hkey, Hpair, Hcount, Hmap,
    Hbuf, Hkeys, Hstatic, Hbump, Hstreams, Hcont, Hoom⟩
  ihave Hpair0 : pointsTo_u64 0 (func16Base + 0) oldPair $$ [Hpair0]
  · irw_exact [show func16Base + 0 = func16Base by decide] with Hpair0
  have h0 := offset_facts64 func16Base 0 0 rfl (by decide)
  have h24 := offset_facts64 func16Base 24 24 rfl (by decide)
  have h8 := offset_facts func16Base 8 8 rfl (by decide)
  have h20 := offset_facts func16Base 20 20 rfl (by decide)
  have h32 := offset_facts func16Base 32 32 rfl (by decide)
  simp only [ckOkBody]
  wasm_twp_block_move (func16Base, 24, wordPair cap bufPtr, h24)
    (func16Base, 0, oldPair, h0) with Hpair Hpair0
  ihave ⟨Hcapw, Hptrw⟩ :=
    (pointsTo_u32_pair_as_groupWord 0 func16Base cap bufPtr).mpr $$ [Hpair0]
  · irw_exact [show func16Base + 0 = func16Base by decide] with Hpair0
  wasm_twp_pures [twp_localGet twp_localGet]
  wasm_twp_rebind twp_load32 (address := func16Base) (offset := 32) len
    h32.1 h32.2.1 h32.2.2.1 h32.2.2.2 with Hcount
  wasm_twp_rebind twp_store32 (address := func16Base) (offset := 8) oldLen
    h8.1 h8.2.1 h8.2.2.1 h8.2.2.2 with Hlen0
  wasm_twp_pures [twp_localGet]
  wasm_twp_rebind twp_load32 (address := func16Base) (offset := 20) key
    h20.1 h20.2.1 h20.2.2.1 h20.2.2.2 with Hkey
  wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_block]
  simp only [List.drop_zero]
  rw [ckFreeInputFrame_literal]
  simp only [ckFreeInput]
  by_cases hcapacity : l2 = 0
  · wasm_twp_pures [twp_localGet]
    iapply twp_eqz (result := 1) (by simp [hcapacity])
    iapply twp_brIf (by decide) (by rfl)
    simp only [ckFreeInputFrame, List.take_zero, List.nil_append]
    iapply twp_ck_collect hfunc2 heapId cap bufPtr len key entries payload
      spare mapBefore keysBefore below storedCursor frontier history output
      hmapBefore hkeys hpayload hentries hcap hspare hn hstate hmax halign
    iframe
  · wasm_twp_pures [twp_localGet]
    iapply twp_eqz (result := 0) (by simp [hcapacity])
    wasm_twp_pures [twp_brIfZero twp_localGet twp_localGet twp_const]
    have Hfree := func57_noop_correct (hlc := hlc) l3 l2 1
      (callerLocals :=
        ⟨[], [Value.i32 func16Base, .i32 key, .i32 l2, .i32 l3, .i32 l4],
          []⟩)
      (stack := []) (code := []) (arity := arity) (remainder := remainder)
      (controls :=
        ckFreeInputFrame :: ckOkFrame :: ckDecodeFrame ::
          ckOuterFrame afterTail :: controls)
      (calls := calls) (s := s) (E := E) (Φ := Φ)
    unfold CallContract callExpr at Hfree
    simp only [List.cons_append, List.nil_append] at Hfree
    iapply Hfree
    isplitl_exact Hruntime
    · iintro Hruntime
      isimp only [ResumeWP, resumeExpr, List.nil_append]
      wasm_twp_pures [twp_exitControl]
      simp only [ckFreeInputFrame, List.take_zero, List.nil_append]
      iapply twp_ck_collect hfunc2 heapId cap bufPtr len key entries payload
        spare mapBefore keysBefore below storedCursor frontier history output
        hmapBefore hkeys hpayload hentries hcap hspare hn hstate hmax halign
      iframe

/-! ## The reject arm -/

set_option maxHeartbeats 2000000 in
/-- The release of the input byte vector on the reject arm, and the branch
that leaves the outer block.  WAT lines 4752 to 4759. -/
theorem twp_ck_err_epilogue [WasmSmallStepGS hlc Universal.State]
    {l1 l2 l3 l4 : UInt32} {afterTail : Program}
    {finalOutput : List UInt8} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp} :
    iprop(RuntimeContext ∗ StackPointer func16Base ∗
      Streams [] finalOutput false ∗
      TailDone finalOutput afterTail arity remainder controls calls s E Φ) ⊢
      WP (.running
          ⟨⟨[], [Value.i32 func16Base, .i32 l1, .i32 l2, .i32 l3, .i32 l4],
              []⟩,
            ckErrTail, arity, remainder,
            ckDecodeFrame :: ckOuterFrame afterTail :: controls, calls⟩ :
            Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hstreams, Hcont⟩
  simp only [ckErrTail]
  by_cases hcapacity : l2 = 0
  · wasm_twp_pures [twp_localGet]
    iapply twp_eqz (result := 1) (by simp [hcapacity])
    iapply twp_brIf (by decide) (by rfl)
    simp only [ckOuterFrame, List.take_zero, List.nil_append]
    iapply twp_ck_stack_epilogue
    iframe
  · wasm_twp_pures [twp_localGet]
    iapply twp_eqz (result := 0) (by simp [hcapacity])
    wasm_twp_pures [twp_brIfZero twp_localGet twp_localGet twp_const]
    have Hfree := func57_noop_correct (hlc := hlc) l3 l2 1
      (callerLocals :=
        ⟨[], [Value.i32 func16Base, .i32 l1, .i32 l2, .i32 l3, .i32 l4],
          []⟩)
      (stack := []) (code := [.br 1]) (arity := arity)
      (remainder := remainder)
      (controls := ckDecodeFrame :: ckOuterFrame afterTail :: controls)
      (calls := calls) (s := s) (E := E) (Φ := Φ)
    unfold CallContract callExpr at Hfree
    simp only [List.cons_append, List.nil_append] at Hfree
    iapply Hfree
    isplitl_exact Hruntime
    · iintro Hruntime
      isimp only [ResumeWP, resumeExpr, List.nil_append]
      iapply twp_br (by rfl)
      simp only [ckOuterFrame, List.take_zero, List.nil_append]
      iapply twp_ck_stack_epilogue
      iframe

set_option maxHeartbeats 2000000 in
/-- The reject arm.  It drops the decoded error string, releases the input
byte vector and leaves the outer block.  The driver writes no byte on this
arm.  WAT lines 4739 to 4759. -/
theorem twp_ck_reject [WasmSmallStepGS hlc Universal.State]
    (word1 word2 : UInt32)
    {l1 l2 l3 l4 : UInt32} {afterTail : Program}
    {finalOutput : List UInt8} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp} :
    iprop(RuntimeContext ∗ StackPointer func16Base ∗
      Streams [] finalOutput false ∗
      pointsTo_u32 0 (func16Base + 20) word1 ∗
      pointsTo_u32 0 (func16Base + 24) word2 ∗
      TailDone finalOutput afterTail arity remainder controls calls s E Φ) ⊢
      WP (.running
          ⟨⟨[], [Value.i32 func16Base, .i32 l1, .i32 l2, .i32 l3, .i32 l4],
              []⟩,
            ckErrArm, arity, remainder,
            ckDecodeFrame :: ckOuterFrame afterTail :: controls, calls⟩ :
            Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hstreams, Hword1, Hword2, Hcont⟩
  have h20 := offset_facts func16Base 20 20 rfl (by decide)
  have h24 := offset_facts func16Base 24 24 rfl (by decide)
  simp only [ckErrArm_shape]
  wasm_twp_pures [twp_block]
  simp only [List.drop_zero]
  rw [ckDropErrorFrame_literal]
  simp only [ckDropError]
  wasm_twp_pures [twp_localGet]
  wasm_twp_rebind twp_load32 (address := func16Base) (offset := 20) word1
    h20.1 h20.2.1 h20.2.2.1 h20.2.2.2 with Hword1
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_const]
  by_cases hshort : word1.toInt32 < (1 : UInt32).toInt32
  · iapply twp_ltS (result := 1) (by rw [if_pos hshort])
    iapply twp_brIf (by decide) (by rfl)
    simp only [ckDropErrorFrame, List.take_zero, List.nil_append]
    iapply twp_ck_err_epilogue
    iframe
  · iapply twp_ltS (result := 0) (by rw [if_neg hshort])
    wasm_twp_pures [twp_brIfZero twp_localGet]
    wasm_twp_rebind twp_load32 (address := func16Base) (offset := 24) word2
      h24.1 h24.2.1 h24.2.2.1 h24.2.2.2 with Hword2
    wasm_twp_pures [twp_localGet twp_const]
    have Hfree := func57_noop_correct (hlc := hlc) word2 word1 1
      (callerLocals :=
        ⟨[], [Value.i32 func16Base, .i32 word1, .i32 l2, .i32 l3, .i32 l4],
          []⟩)
      (stack := []) (code := []) (arity := arity) (remainder := remainder)
      (controls :=
        ckDropErrorFrame :: ckDecodeFrame :: ckOuterFrame afterTail ::
          controls)
      (calls := calls) (s := s) (E := E) (Φ := Φ)
    unfold CallContract callExpr at Hfree
    simp only [List.cons_append, List.nil_append] at Hfree
    iapply Hfree
    isplitl_exact Hruntime
    · iintro Hruntime
      isimp only [ResumeWP, resumeExpr, List.nil_append]
      wasm_twp_pures [twp_exitControl]
      simp only [ckDropErrorFrame, List.take_zero, List.nil_append]
      iapply twp_ck_err_epilogue
      iframe

/-! ## The region below the frame

The lemmas of this section and of the next one name no frame offset, so
the `map_get` tail uses them without a change. -/

/-- The read phase gives the sixteen bytes of `StackReserve` just below the
frame.  With the bytes below them, that is the region that the callees of
the tail need.  `Project.RustHashMap.DriverTail.StackBelow_of_reserve`
names `func19Base` and `driverDepth`, so this copy takes both as
arguments. -/
theorem StackBelow_of_reserve_at [WasmHeapGS Universal.State]
    (base : UInt32) (depth : Nat) (extra reserve : List UInt8)
    (hextra : extra.length = depth - 16) (hle : 16 ≤ depth)
    (haddr : base - UInt32.ofNat depth + UInt32.ofNat (depth - 16)
      = base - UInt32.ofNat 16) :
    iprop(Slices.ByteSlice 0 (base - UInt32.ofNat depth) extra ∗
        StackReserve (base - 16) reserve) ⊢
      StackBelow base depth (extra ++ reserve) := by
  iintro ⟨Hextra, Hreserve⟩
  unfold StackReserve
  icases Hreserve with ⟨%hreserve, Hbytes⟩
  iapply StackBelow_join base depth 16 extra reserve hextra hle haddr
  isplitl_exact Hextra
  · unfold StackBelow
    isplitl_pureexact hreserve
    iexact Hbytes

/-! ## The pure facts of an accepted input -/

/-- The pair bytes of an accepted input are the wire form of the entries
that the model builds.  The take in `keyPayload` drops nothing, because
the header names the whole rest. -/
theorem keyPayload_serialize (input : List UInt8)
    (haccept : KeyDecodeAccepts input) :
    CollectContract.entryCodec.serialize (acceptedEntries input)
      = keyPayload input := by
  obtain ⟨_hfour, _hdec, hexact⟩ := haccept
  unfold CollectContract.entryCodec acceptedEntries keyPayload
  rw [HashMap.BorshBridge.serialize_wireEntries _ hexact.symm]
  rw [List.take_of_length_le]
  rw [List.length_drop]
  omega

/-- The entry count of an accepted input is the header word. -/
theorem acceptedEntries_length (input : List UInt8) :
    (acceptedEntries input).length = (pairCount input).toNat := by
  unfold acceptedEntries pairCount
  exact HashMap.BorshBridge.length_wireEntries _

/-- An accepted input holds fewer pairs than the model bound.  Eight bytes
carry one pair, and the input is shorter than `UInt32.size`. -/
theorem acceptedEntries_bound (input : List UInt8)
    (haccept : KeyDecodeAccepts input) (hinput : input.length < UInt32.size) :
    (acceptedEntries input).length ≤ 2 ^ 30 := by
  obtain ⟨_hfour, _hdec, hexact⟩ := haccept
  rw [acceptedEntries_length]
  have hlen : (mapBytes input).length ≤ input.length := by
    unfold mapBytes
    rw [List.length_drop]
    omega
  have hsize : UInt32.size = 4294967296 := rfl
  omega

/-- An accepted input never reaches the capacity that absolute `func 17`
rejects.  The read phase puts the input in a vector of at most 536870912
bytes, the input fits in that capacity, and the first four bytes of an
accepted input are the key, so they carry no pair.

`Project.RustHashMap.RemovePures` states the same bound for the entry
list.  That module is downstream of this one, so the bound is restated
here. -/
theorem pairCount_le_maxTable (input : List UInt8)
    (capacity ptr : UInt32) (frontier : Nat)
    (haccept : KeyDecodeAccepts input)
    (hfacts : PushVecFacts capacity ptr frontier)
    (hfits : input.length ≤ capacity.toNat) :
    (pairCount input).toNat ≤ maxTableCapacity := by
  obtain ⟨hfour, _hdec, hexact⟩ := haccept
  have hcap := hfacts.capacity_le
  have hmap : (mapBytes input).length = input.length - 4 := by
    unfold mapBytes
    rw [List.length_drop]
  rw [maxTableCapacity_eq]
  omega

/-! ## The whole tail -/

set_option maxHeartbeats 2000000 in
/-- The tail of the `map_contains_key` driver, from the end of the read
loop to the return.  `collect_entries` is the one open contract.  WAT lines
4652 to 4769. -/
theorem twp_contains_key_tail [WasmSmallStepGS hlc Universal.State]
    (hfunc2 : CollectContract.Func2Spec (hlc := hlc)) :
    LookupTailContracts.ContainsKeyTailSpec (hlc := hlc) := by
  unfold LookupTailContracts.ContainsKeyTailSpec
  intro heapId capacity ptr aux4 input output reserve head chunk extra
    keysBefore dataBytes storedCursor frontier history afterTail arity
    remainder controls calls s E Φ
  iintro ⟨HafterRead, Hextra, Hkeys, Hdata, %hsizes, Hcont, Hoom⟩
  obtain ⟨hextra, hkeys, hdata, hstate, hstatic, hinput⟩ := hsizes
  isimp only [AfterReadCK] at HafterRead
  icases HafterRead with ⟨Hruntime, Hsp, Hreserve, Hhead, Hvec, Hchunk,
    Hbump, Hstreams, %hshape⟩
  obtain ⟨hhead, hchunk, hpush⟩ := hshape
  have hlenNat : (UInt32.ofNat input.length).toNat = input.length :=
    UInt32.toNat_ofNat_of_lt' hinput
  isimp only [← lookupCalleeDepth_keyDecoder] at Hextra
  ihave Hbelow : StackBelow func16Base keyDecoderDepth (extra ++ reserve) $$
      [Hextra Hreserve]
  · iapply StackBelow_of_reserve_at func16Base keyDecoderDepth extra reserve
      (by rw [hextra]; rfl) (by decide) (by decide)
    iframe
  -- the entries header at frame offset 0 and the output slot at 16
  icases (ByteSlice_split_at func16Base 12 head (by simp [hhead])).mp $$ Hhead
    with ⟨Hhead0, Hhead1⟩
  isimp only [UInt32.reduceToNat] at Hhead0
  isimp only [UInt32.reduceToNat] at Hhead1
  icases (ByteSlice_split_at (func16Base + 12) 4 (head.drop 12)
    (by simp [hhead])).mp $$ Hhead1 with ⟨_Hgap, Hslot⟩
  isimp only [UInt32.reduceToNat,
    show func16Base + 12 + 4 = func16Base + 16 by decide,
    show (head.drop 12).drop 4 = head.drop 16 from by
      simp [List.drop_drop]] at Hslot
  ihave Hwords := ByteSlice_header_as_words func16Base (head.take 12)
    (by simp [hhead]) (by decide) $$ Hhead0
  icases Hwords with ⟨%oldCap, %oldPtr, %oldLen, Hcapw, Hptrw, Hlenw⟩
  ihave HoldPair :=
    (pointsTo_u32_pair_as_groupWord 0 func16Base oldCap oldPtr).mp $$
    [Hcapw Hptrw]
  · iframe
  -- the map slot is the head of the chunk buffer
  icases (ByteSlice_split_at (func16Base + 48) 32 chunk
    (by simp [hchunk])).mp $$ Hchunk with ⟨Hmap, _Hchunkrest⟩
  isimp only [UInt32.reduceToNat] at Hmap
  ihave ⟨_Hheader, Hstorage⟩ :=
    (VecU8_as_headerBytes_storage heapId (func16Base + 36) capacity ptr input
      (by decide)).mp $$ Hvec
  ihave ⟨Hstorage, %hcapFits⟩ :=
    VecStorage_length_le heapId capacity ptr input $$ Hstorage
  ihave Hinput := VecStorage_bytes heapId capacity ptr input $$ Hstorage
  simp only [func16AfterRead_cons, afterReadLocalsCK]
  wasm_twp_pures [twp_localGet twp_const twp_add twp_localGet twp_localGet]
    rewriting [show (16 : UInt32) + func16Base = func16Base + 16 by decide]
  have Hdecode := func7_correct (hlc := hlc) func16Base (func16Base + 16) ptr
    (UInt32.ofNat input.length) heapId input (head.drop 16) (extra ++ reserve)
    dataBytes storedCursor frontier history [] output false
    (callerLocals :=
      ⟨[], [Value.i32 func16Base, .i32 (UInt32.ofNat input.length),
        .i32 capacity, .i32 ptr, .i32 aux4], []⟩)
    (stack := []) (code := ckAfterDecode afterTail) (arity := arity)
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
    iintro %cap' %buffer %spare' %below' %storedCursor' %frontier' %history'
      %haccept Hruntime Hsp Hbelow Hslot Hbytes Hdata Hbuf Hbump Hstreams
      %hfacts
    isimp only [ResumeWP, resumeExpr, List.nil_append]
    obtain ⟨hcapBound, hspareLen, _hzero, halign⟩ := hfacts
    have hn := acceptedEntries_bound input haccept hinput
    have hmax := pairCount_le_maxTable input capacity ptr frontier haccept
      hpush hcapFits
    -- the static singleton table is the first 24 bytes of the segment
    icases (ByteSlice_split_at entryStackTop 24 dataBytes
      (by simp [hdata, dataSegmentSize])).mp $$ Hdata with ⟨Hstatic, _Hgap⟩
    isimp only [UInt32.reduceToNat, hstatic] at Hstatic
    ihave ⟨H16, H20, H24, H28, H32⟩ :=
      ByteSlice_five_words (func16Base + 16) 0 (leadingKey input) cap' buffer
        (pairCount input) $$ Hslot
    isimp only [show func16Base + 16 + 4 = func16Base + 20 by decide] at H20
    isimp only [show func16Base + 16 + 4 + 4 = func16Base + 24 by decide]
      at H24
    isimp only [show func16Base + 16 + 4 + 4 + 4 = func16Base + 28 by decide]
      at H28
    isimp only [show func16Base + 16 + 4 + 4 + 4 + 4 = func16Base + 32
      by decide] at H32
    ihave Hpair :=
      (pointsTo_u32_pair_as_groupWord 0 (func16Base + 24) cap' buffer).mp $$
      [H24 H28]
    · isplitl_exact H24
      · irw_exact [show func16Base + 24 + 4 = func16Base + 28 by decide]
          with H28
    simp only [ckAfterDecode]
    wasm_twp_pures [twp_block]
    simp only [List.drop_zero]
    rw [ckOuterFrame_literal]
    simp only [ckOuterBody]
    wasm_twp_pures [twp_block]
    simp only [List.drop_zero]
    rw [ckDecodeFrame_literal]
    simp only [ckDecodeBlock]
    wasm_twp_pures [twp_block]
    simp only [List.drop_zero]
    rw [ckOkFrame_literal]
    simp only [ckOkArm_shape]
    have h16 := offset_facts func16Base 16 16 rfl (by decide)
    wasm_twp_pures [twp_localGet]
    wasm_twp_rebind twp_load32 (address := func16Base) (offset := 16) 0
      h16.1 h16.2.1 h16.2.2.1 h16.2.2.2 with H16
    wasm_twp_pures [twp_brIfZero]
    ihave ⟨_Hlow, Hbelow⟩ :=
      StackBelow_split func16Base keyDecoderDepth
        CollectContract.collectDepth below' (by decide) (by decide) $$ Hbelow
    rw [containsKeyOutput_of_accepts input 0 0 haccept hn,
      HashMap.Table.containsKey_ofEntries_u32 0 0 (acceptedEntries input) hn
        (leadingKey input)]
    iapply twp_ck_accept_copy hfunc2 heapId cap' buffer (pairCount input)
      (leadingKey input) oldLen (wordPair oldCap oldPtr)
      (acceptedEntries input) (keyPayload input) spare' (chunk.take 32)
      keysBefore
      (below'.drop (keyDecoderDepth - CollectContract.collectDepth))
      storedCursor' frontier' history' output
      (by simp [hchunk]) hkeys (keyPayload_serialize input haccept).symm
      (acceptedEntries_length input) hcapBound hspareLen hn hstate hmax halign
    iframe
  · isplit
    · -- the reject arm
      iintro %word1 %word2 %word3 %word4 %below' %storedCursor' %frontier'
        %history' %hreject Hruntime Hsp Hbelow Hslot Hbytes Hdata Hbump
        Hstreams %hword1
      isimp only [ResumeWP, resumeExpr, List.nil_append]
      ihave ⟨H16, H20, H24, _H28, _H32⟩ :=
        ByteSlice_five_words (func16Base + 16) 1 word1 word2 word3 word4 $$
        Hslot
      isimp only [show func16Base + 16 + 4 = func16Base + 20 by decide] at H20
      isimp only [show func16Base + 16 + 4 + 4 = func16Base + 24 by decide]
        at H24
      simp only [ckAfterDecode]
      wasm_twp_pures [twp_block]
      simp only [List.drop_zero]
      rw [ckOuterFrame_literal]
      simp only [ckOuterBody]
      wasm_twp_pures [twp_block]
      simp only [List.drop_zero]
      rw [ckDecodeFrame_literal]
      simp only [ckDecodeBlock]
      wasm_twp_pures [twp_block]
      simp only [List.drop_zero]
      rw [ckOkFrame_literal]
      simp only [ckOkArm_shape]
      have h16 := offset_facts func16Base 16 16 rfl (by decide)
      wasm_twp_pures [twp_localGet]
      wasm_twp_rebind twp_load32 (address := func16Base) (offset := 16) 1
        h16.1 h16.2.1 h16.2.2.1 h16.2.2.2 with H16
      iapply twp_brIf (by decide) (by rfl)
      simp only [ckOkFrame, List.take_zero, List.nil_append]
      rw [containsKeyOutput_of_rejects input hreject, List.append_nil]
      iapply twp_ck_reject word1 word2
      iframe
    · iintro %remaining' Hstreams
      iapply Hoom
      isimp only [ExportOOM]
      iexists remaining', output
      iexact Hstreams

end Project.RustHashMap.ContainsKeyTailProof
