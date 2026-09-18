import Project.RustHashMap.ContainsKeyTailProof
import Project.RustHashMap.Func17Proof

/-!
# The tail of the `map_get` driver: the proof

`Project.RustHashMap.LookupTailContracts.GetTailSpec` is the contract of
everything after the read phase of absolute `func 21`.  This module proves
it.  `collect_entries`, absolute `func 5`, arrives as a hypothesis, which
`CollectProof.func2_correct` supplies; every other callee is a proved
theorem.

The proof follows the block structure of
`Project.RustHashMap.LookupTailDefs`, one lemma per control block, from the
innermost outward.  It has the same shape as
`Project.RustHashMap.ContainsKeyTailProof`, and it uses the pure lemmas of
that module.

## The six frames

`getOuterFrame` is the block that every path leaves.  Its continuation is
the stack epilogue.  `getDecodeFrame` is the block that the allocator
failure follows; the allocator never returns zero, so that continuation is
dead.  `getOkFrame` is the block that the reject guard leaves; its
continuation is the reject arm.  `getFreeInputFrame` and
`getDropErrorFrame` are the two small blocks of the free tests, and
`getPayloadFrame` is the block that writes the payload word of a `some`
answer.

## Why the answer has two shapes

The kernel writes `HashMap.Table.optionU32At`, which is a discriminant
word and a payload word.  The driver moves both into locals and the reply
block turns them into the borsh `Option`: one byte for `none` and five
bytes for `some`.  So the reply lemma takes the answer as an
`Option UInt32` and splits on it.
-/

namespace Project.RustHashMap.GetTailProof

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
open Project.RustHashMap.Func17Proof
open Project.RustHashMap.Func30Proof
open Project.RustHashMap.ImportProofs
open Project.RustHashMap.ReadAll
open Project.RustHashMap.GetRead
open Project.RustHashMap.LookupTailDefs
open Project.RustHashMap.DriverTail
open Project.RustHashMap.DriverTailProof
open Project.RustHashMap.ContainsKeyTailProof
open scoped Wasm.SmallStep.Outcome

/-! ## The suffixes of the code

Each call needs the code that follows it as an explicit argument, so each
suffix gets a name. -/

/-- The free of the reply buffer, and the table drop after it.  WAT lines
5243 to 5274. -/
def getReplyFree : Program :=
  .localGet 1 :: .const 1024 :: .const 1 :: .call 60 :: getTableDrop

/-- The write of the reply bytes to the output stream.  WAT lines 5240 to
5274. -/
def getReplyWrite : Program :=
  .localGet 1 :: .localGet 3 :: .call 64 :: getReplyFree

/-- The store of the tag byte in the first byte of the buffer.  WAT lines
5238 to 5274. -/
def getReplyStore : Program :=
  .localGet 1 :: .localGet 2 :: .store8 0 :: getReplyWrite

/-- The null test of the allocation result, and the payload block.  WAT
lines 5221 to 5274. -/
def getReplyAfterAlloc : Program :=
  .localTee 1 :: .eqz :: .br_if 1 :: .const 0 :: .localSet 2 ::
    .block 0 0 getPayloadBlock :: getReplyStore

theorem getReply_shape :
    getReply = .const 1 :: .localSet 3 :: .const 1024 :: .const 1 ::
      .call 58 :: getReplyAfterAlloc := rfl

/-- The two loads of the kernel output, the marker call and the reply.
WAT lines 5209 to 5274. -/
def getAfterKernel : Program :=
  .localGet 0 :: .load32 12 :: .localSet 5 :: .localGet 0 :: .load32 8 ::
    .localSet 4 :: .call 33 :: getReply

/-- The kernel call and everything after it.  WAT lines 5200 to 5274. -/
def getAfterCollect : Program :=
  .localGet 0 :: .const 8 :: .add :: .localGet 0 :: .const 64 :: .add ::
    .localGet 1 :: .call 20 :: getAfterKernel

/-- The collect call and everything after it.  WAT lines 5194 to 5274. -/
def getCollectAndReply : Program :=
  .localGet 0 :: .const 64 :: .add :: .localGet 0 :: .const 16 :: .add ::
    .call 5 :: getAfterCollect

/-- The accept arm after its guard: the header copy, the release of the
input, and the collect call.  WAT lines 5174 to 5274. -/
def getOkBody : Program :=
  .localGet 0 :: .localGet 0 :: .load64 40 :: .store64 16 :: .localGet 0 ::
    .localGet 0 :: .load32 48 :: .store32 24 :: .localGet 0 ::
    .load32 36 :: .localSet 1 :: .block 0 0 getFreeInput ::
    getCollectAndReply

theorem getOkArm_shape :
    getOkArm = .localGet 0 :: .load32 32 :: .br_if 0 :: getOkBody := rfl

/-- The reject arm after the drop of the error string.  WAT lines 5289 to
5296. -/
def getErrTail : Program :=
  [.localGet 2, .eqz, .br_if 1, .localGet 3, .localGet 2, .const 1,
    .call 60, .br 1]

theorem getErrArm_shape :
    getErrArm = .block 0 0 getDropError :: getErrTail := rfl

/-- The outer block and the stack epilogue, which is what follows the call
of the key decoder. -/
def getAfterDecode (afterTail : Program) : Program :=
  .block 0 0 getOuterBody :: (getEpilogue ++ afterTail)

/-- The tail of the driver in cons form, with the decoder call exposed. -/
theorem func18AfterRead_cons (afterTail : Program) :
    func18AfterRead ++ afterTail =
      .localGet 0 :: .const 32 :: .add :: .localGet 3 :: .localGet 1 ::
        .call 10 :: getAfterDecode afterTail := rfl

/-! ## The control frames of the tail -/

/-- The outermost block of the tail.  Its continuation is the stack
epilogue, so every path that leaves it returns. -/
def getOuterFrame (afterTail : Program) : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body := getOuterBody, continuation := getEpilogue ++ afterTail,
    belowStack := [] }

theorem getOuterFrame_literal (afterTail : Program) :
    ({ kind := .block, paramArity := 0, resultArity := 0,
       body := getOuterBody, continuation := getEpilogue ++ afterTail,
       belowStack := [] } : ControlFrame) = getOuterFrame afterTail := rfl

/-- The block that the reply leaves when the allocator returns zero.  The
allocator never returns zero, so the continuation is dead. -/
def getDecodeFrame : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body := getDecodeBlock,
    continuation := [.const 1, .const 1024, .call 99, .unreachable],
    belowStack := [] }

theorem getDecodeFrame_literal :
    ({ kind := .block, paramArity := 0, resultArity := 0,
       body := getDecodeBlock,
       continuation := [.const 1, .const 1024, .call 99, .unreachable],
       belowStack := [] } : ControlFrame) = getDecodeFrame := rfl

/-- The block that the reject guard leaves.  Its continuation is the reject
arm. -/
def getOkFrame : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body := getOkArm, continuation := getErrArm, belowStack := [] }

theorem getOkFrame_literal :
    ({ kind := .block, paramArity := 0, resultArity := 0,
       body := getOkArm, continuation := getErrArm,
       belowStack := [] } : ControlFrame) = getOkFrame := rfl

/-- The block that releases the input byte vector before the collect
call. -/
def getFreeInputFrame : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body := getFreeInput, continuation := getCollectAndReply,
    belowStack := [] }

theorem getFreeInputFrame_literal :
    ({ kind := .block, paramArity := 0, resultArity := 0,
       body := getFreeInput, continuation := getCollectAndReply,
       belowStack := [] } : ControlFrame) = getFreeInputFrame := rfl

/-- The block that writes the payload word of a `some` answer. -/
def getPayloadFrame : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body := getPayloadBlock, continuation := getReplyStore,
    belowStack := [] }

theorem getPayloadFrame_literal :
    ({ kind := .block, paramArity := 0, resultArity := 0,
       body := getPayloadBlock, continuation := getReplyStore,
       belowStack := [] } : ControlFrame) = getPayloadFrame := rfl

/-- The block that drops the decoded error string on the reject arm. -/
def getDropErrorFrame : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body := getDropError, continuation := getErrTail, belowStack := [] }

theorem getDropErrorFrame_literal :
    ({ kind := .block, paramArity := 0, resultArity := 0,
       body := getDropError, continuation := getErrTail,
       belowStack := [] } : ControlFrame) = getDropErrorFrame := rfl

/-! ## The stack epilogue -/

set_option maxHeartbeats 2000000 in
/-- The stack pointer restore that ends every path.  The driver frame is
320 bytes, so this lemma is not the one of
`Project.RustHashMap.DriverTailProof`, which names 304 bytes and nine
locals.  WAT lines 5303 to 5306. -/
theorem twp_get_stack_epilogue [WasmSmallStepGS hlc Universal.State]
    {l1 l2 l3 l4 l5 : UInt32} {afterTail : Program}
    {finalOutput : List UInt8} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp} :
    iprop(RuntimeContext ∗ StackPointer func18Base ∗
      Streams [] finalOutput false ∗
      TailDone finalOutput afterTail arity remainder controls calls s E Φ) ⊢
      WP (.running
          ⟨⟨[], [Value.i32 func18Base, .i32 l1, .i32 l2, .i32 l3, .i32 l4,
              .i32 l5], []⟩,
            getEpilogue ++ afterTail, arity, remainder, controls, calls⟩ :
            Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hstreams, Hcont⟩
  isimp only [StackPointer] at Hsp
  isimp only [TailDone] at Hcont
  simp only [getEpilogue, List.cons_append, List.nil_append]
  wasm_twp_pures [twp_localGet twp_const twp_add]
  rw [show (320 : UInt32) + func18Base = entryStackTop by decide]
  wasm_twp_rebind twp_globalSet with Hsp
  ihave Hsp : StackPointer entryStackTop $$ [Hsp]
  · unfold StackPointer
    iexact Hsp
  iapply Hcont $$ %(⟨[], [Value.i32 func18Base, .i32 l1, .i32 l2, .i32 l3,
    .i32 l4, .i32 l5], []⟩ : Locals) Hruntime Hsp Hstreams

/-! ## The table drop -/

set_option maxHeartbeats 2000000 in
/-- The drop of the hash table, which is the last step of the reply.  Both
arms of both guards reach `getOuterFrame`, so neither guard has to be
decided.  WAT lines 5249 to 5274. -/
theorem twp_get_table_drop [WasmSmallStepGS hlc Universal.State]
    {l1 l2 l3 l4 l5 ctrl mask : UInt32} {afterTail : Program}
    {finalOutput : List UInt8} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp} :
    iprop(RuntimeContext ∗ StackPointer func18Base ∗
      Streams [] finalOutput false ∗
      pointsTo_u32 0 (func18Base + 64) ctrl ∗
      pointsTo_u32 0 (func18Base + 68) mask ∗
      TailDone finalOutput afterTail arity remainder controls calls s E Φ) ⊢
      WP (.running
          ⟨⟨[], [Value.i32 func18Base, .i32 l1, .i32 l2, .i32 l3, .i32 l4,
              .i32 l5], []⟩,
            getTableDrop, arity, remainder,
            getOkFrame :: getDecodeFrame :: getOuterFrame afterTail ::
              controls, calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hstreams, Hctrl, Hmask, Hcont⟩
  have h64 := offset_facts func18Base 64 64 rfl (by decide)
  have h68 := offset_facts func18Base 68 68 rfl (by decide)
  simp only [getTableDrop]
  wasm_twp_pures [twp_localGet]
  wasm_twp_rebind twp_load32 (address := func18Base) (offset := 68) mask
    h68.1 h68.2.1 h68.2.2.1 h68.2.2.2 with Hmask
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  by_cases hmask : mask = 0
  · iapply twp_eqz (result := 1) (by simp [hmask])
    iapply twp_brIf (by decide) (by rfl)
    simp only [getOuterFrame, List.take_zero, List.nil_append]
    iapply twp_get_stack_epilogue
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
      simp only [getOuterFrame, List.take_zero, List.nil_append]
      iapply twp_get_stack_epilogue
      iframe
    · iapply twp_eqz (result := 0) (by simp [hsize])
      wasm_twp_pures [twp_brIfZero twp_localGet]
      wasm_twp_rebind twp_load32 (address := func18Base) (offset := 64) ctrl
        h64.1 h64.2.1 h64.2.2.1 h64.2.2.2 with Hctrl
      wasm_twp_pures [twp_localGet twp_sub twp_const twp_add twp_localGet
        twp_const]
      have Hfree := func57_noop_correct (hlc := hlc)
        ((4294967288 : UInt32) + (ctrl - mask <<< 3))
        ((17 : UInt32) + (mask + mask <<< 3)) 8
        (callerLocals :=
          ⟨[], [Value.i32 func18Base,
            .i32 ((17 : UInt32) + (mask + mask <<< 3)), .i32 l2,
            .i32 (mask <<< 3), .i32 l4, .i32 l5], []⟩)
        (stack := []) (code := [.br 2]) (arity := arity)
        (remainder := remainder)
        (controls :=
          getOkFrame :: getDecodeFrame :: getOuterFrame afterTail ::
            controls)
        (calls := calls) (s := s) (E := E) (Φ := Φ)
      unfold CallContract callExpr at Hfree
      simp only [List.cons_append, List.nil_append] at Hfree
      iapply Hfree
      isplitl_exact Hruntime
      · iintro Hruntime
        isimp only [ResumeWP, resumeExpr, List.nil_append]
        iapply twp_br (by rfl)
        simp only [getOuterFrame, List.take_zero, List.nil_append]
        iapply twp_get_stack_epilogue
        iframe

/-! ## The reply -/

set_option maxHeartbeats 2000000 in
/-- The reply.  It allocates 1024 bytes with alignment 1, writes the borsh
`Option` of the answer in the first bytes of them, writes those bytes to
the output stream, frees the buffer and drops the table.  The null test
after the allocation is dead, because a live block never starts at address
zero.  WAT lines 5216 to 5274. -/
theorem twp_get_reply [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory) (output : List UInt8)
    (answer : Option UInt32) (payload : UInt32)
    {l1 l2 l3 ctrl mask : UInt32} {afterTail : Program}
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hpayload : ∀ v : UInt32, answer = some v → payload = v) :
    iprop(RuntimeContext ∗ StackPointer func18Base ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams [] output false ∗
      pointsTo_u32 0 (func18Base + 64) ctrl ∗
      pointsTo_u32 0 (func18Base + 68) mask ∗
      TailDone (output ++ Borsh.option Borsh.u32 answer) afterTail arity
        remainder controls calls s E Φ ∗
      (ExportOOM -∗ Φ (.trapped (.host OOM.trapMessage)))) ⊢
      WP (.running
          ⟨⟨[], [Value.i32 func18Base, .i32 l1, .i32 l2, .i32 l3,
              .i32 (if answer.isSome then 1 else 0), .i32 payload], []⟩,
            getReply, arity, remainder,
            getOkFrame :: getDecodeFrame :: getOuterFrame afterTail ::
              controls, calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hbump, Hstreams, Hctrl, Hmask, Hcont, Hoom⟩
  simp only [getReply_shape]
  wasm_twp_pures [twp_const]
  wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_const twp_const]
  have Halloc := func55_correct (hlc := hlc) 1024 1
    { size := 1024, alignment := 1 } heapId storedCursor frontier history
    [] output false
    (callerLocals :=
      ⟨[], [Value.i32 func18Base, .i32 l1, .i32 l2, .i32 1,
        .i32 (if answer.isSome then 1 else 0), .i32 payload], []⟩)
    (stack := []) (code := getReplyAfterAlloc) (arity := arity)
    (remainder := remainder)
    (controls :=
      getOkFrame :: getDecodeFrame :: getOuterFrame afterTail :: controls)
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
        obtain ⟨_, _, _, hbound, _, _⟩ :=
          classifyBump_success_align1 frontier 1024 blockBase finish hdecision
        have hfacts1 := offset_facts blockBase 1 1 rfl (by omega)
        have hnowrap1 : (blockBase + 1).toNat + 4 < UInt32.size := by
          rw [hfacts1.1]
          have : (1 : UInt32).toNat = 1 := rfl
          omega
        obtain ⟨b0, b1, b2, b3, b4, rest, hcons⟩ :
            ∃ b0 b1 b2 b3 b4 rest,
              bytes = b0 :: b1 :: b2 :: b3 :: b4 :: rest := by
          match bytes, hbytes with
          | b0 :: b1 :: b2 :: b3 :: b4 :: rest, _ =>
            exact ⟨b0, b1, b2, b3, b4, rest, rfl⟩
        subst hcons
        simp only [getReplyAfterAlloc]
        wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
          Nat.reduceSub, List.set]
        iapply twp_eqz (result := 0) (by simp [hnonnull])
        wasm_twp_pures [twp_brIfZero twp_const]
        wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
          Nat.reduceSub, List.set]
        wasm_twp_pures [twp_block]
        simp only [List.drop_zero]
        rw [getPayloadFrame_literal]
        simp only [getPayloadBlock]
        icases (ByteSlice_split_at blockBase 1
          (b0 :: b1 :: b2 :: b3 :: b4 :: rest) (by simp)).mp $$ Hbytes
          with ⟨Hhead, Hrest⟩
        isimp only [UInt32.reduceToNat,
          show (b0 :: b1 :: b2 :: b3 :: b4 :: rest).take 1 = [b0] from rfl,
          show (b0 :: b1 :: b2 :: b3 :: b4 :: rest).drop 1
            = b1 :: b2 :: b3 :: b4 :: rest from rfl] at Hhead Hrest
        icases (ByteSlice_single blockBase b0).mp $$ Hhead with
          ⟨%hbyte0, Hcell0⟩
        cases answer with
        | none =>
            simp only [Option.isSome_none, Bool.false_eq_true, if_false]
            wasm_twp_pures [twp_localGet twp_const]
            iapply twp_ne (result := 1) (by decide)
            iapply twp_brIf (by decide) (by rfl)
            simp only [getPayloadFrame, List.take_zero, List.nil_append]
            simp only [getReplyStore]
            wasm_twp_pures [twp_localGet twp_localGet]
            iapply twp_store8_addr_gen (address := blockBase) (value := 0)
              b0 $$ Hcell0
            iintro Hcell0
            ihave Hslice : Slices.ByteSlice 0 blockBase
                (Borsh.option Borsh.u32 none) $$ [Hcell0]
            · rw [show Borsh.option Borsh.u32 none
                  = [(0 : UInt32).toUInt8] by decide]
              iapply (ByteSlice_single blockBase ((0 : UInt32).toUInt8)).mpr
              isplitl_pureexact hbyte0
              · iexact Hcell0
            simp only [getReplyWrite]
            wasm_twp_pures [twp_localGet twp_localGet]
            have Hwrite := func61_correct (hlc := hlc) blockBase 1
              (Borsh.option Borsh.u32 none) [] output false
              (callerLocals :=
                ⟨[], [Value.i32 func18Base, .i32 blockBase, .i32 0, .i32 1,
                  .i32 0, .i32 payload], []⟩)
              (stack := []) (code := getReplyFree) (arity := arity)
              (remainder := remainder)
              (controls :=
                getOkFrame :: getDecodeFrame :: getOuterFrame afterTail ::
                  controls)
              (calls := calls) (s := s) (E := E) (Φ := Φ)
            unfold CallContract callExpr at Hwrite
            simp only [List.cons_append, List.nil_append] at Hwrite
            iapply Hwrite
            isplitl_exacts [Hruntime Hstreams Hslice]
            isplitl_pureexact ⟨by decide, by decide⟩
            iintro Hruntime Hstreams Hslice
            isimp only [ResumeWP, resumeExpr, List.nil_append]
            simp only [getReplyFree]
            wasm_twp_pures [twp_localGet twp_const twp_const]
            have Hfree := func57_noop_correct (hlc := hlc) blockBase 1024 1
              (callerLocals :=
                ⟨[], [Value.i32 func18Base, .i32 blockBase, .i32 0, .i32 1,
                  .i32 0, .i32 payload], []⟩)
              (stack := []) (code := getTableDrop) (arity := arity)
              (remainder := remainder)
              (controls :=
                getOkFrame :: getDecodeFrame :: getOuterFrame afterTail ::
                  controls)
              (calls := calls) (s := s) (E := E) (Φ := Φ)
            unfold CallContract callExpr at Hfree
            simp only [List.cons_append, List.nil_append] at Hfree
            iapply Hfree
            isplitl_exact Hruntime
            · iintro Hruntime
              isimp only [ResumeWP, resumeExpr, List.nil_append]
              iapply twp_get_table_drop
              iframe
        | some v =>
            have hv : payload = v := hpayload v rfl
            subst hv
            simp only [Option.isSome_some, if_true]
            wasm_twp_pures [twp_localGet twp_const]
            iapply twp_ne (result := 0) (by decide)
            wasm_twp_pures [twp_brIfZero twp_localGet twp_localGet]
            icases (ByteSlice_split_at (blockBase + 1) 4
              (b1 :: b2 :: b3 :: b4 :: rest) (by simp)).mp $$ Hrest
              with ⟨Hword, _Htail⟩
            isimp only [UInt32.reduceToNat,
              show (b1 :: b2 :: b3 :: b4 :: rest).take 4 = [b1, b2, b3, b4]
                from rfl] at Hword
            ihave ⟨Hcell, Hclose⟩ :=
              Slices.ByteSlice_storeWordFocus 0 (blockBase + 1)
                [b1, b2, b3, b4] payload rfl hnowrap1 $$ Hword
            iapply twp_store32 (address := blockBase) (offset := 1)
              (WordCodec.decodeU32 [b1, b2, b3, b4]) hfacts1.1 hfacts1.2.1
              hfacts1.2.2.1 hfacts1.2.2.2 $$ Hcell
            iintro Hcell
            ihave Hword := Hclose $$ Hcell
            wasm_twp_pures [twp_const]
            wasm_twp_localSet [List.length_cons, List.length_nil,
              Nat.reduceAdd, Nat.reduceSub, List.set]
            wasm_twp_pures [twp_const]
            wasm_twp_localSet [List.length_cons, List.length_nil,
              Nat.reduceAdd, Nat.reduceSub, List.set]
            wasm_twp_pures [twp_exitControl]
            simp only [getPayloadFrame, List.take_zero, List.nil_append]
            simp only [getReplyStore]
            wasm_twp_pures [twp_localGet twp_localGet]
            iapply twp_store8_addr_gen (address := blockBase) (value := 1)
              b0 $$ Hcell0
            iintro Hcell0
            ihave Hhead : Slices.ByteSlice 0 blockBase [1] $$ [Hcell0]
            · rw [show ([1] : List UInt8) = [(1 : UInt32).toUInt8]
                by decide]
              iapply (ByteSlice_single blockBase ((1 : UInt32).toUInt8)).mpr
              isplitl_pureexact hbyte0
              · iexact Hcell0
            ihave Hslice : Slices.ByteSlice 0 blockBase
                (Borsh.option Borsh.u32 (some payload)) $$ [Hhead Hword]
            · rw [borsh_option_u32_some payload,
                show (1 : UInt8) :: WordCodec.u32le.serialize [payload]
                  = [1] ++ WordCodec.u32le.serialize [payload] from rfl]
              iapply (Slices.ByteSlice_append 0 blockBase [1]
                (WordCodec.u32le.serialize [payload])).mpr
              isplitl_exact Hhead
              · irw_exact [show blockBase + UInt32.ofNat [(1 : UInt8)].length
                  = blockBase + 1 from rfl] with Hword
            simp only [getReplyWrite]
            wasm_twp_pures [twp_localGet twp_localGet]
            have Hwrite := func61_correct (hlc := hlc) blockBase 5
              (Borsh.option Borsh.u32 (some payload)) [] output false
              (callerLocals :=
                ⟨[], [Value.i32 func18Base, .i32 blockBase, .i32 1, .i32 5,
                  .i32 1, .i32 payload], []⟩)
              (stack := []) (code := getReplyFree) (arity := arity)
              (remainder := remainder)
              (controls :=
                getOkFrame :: getDecodeFrame :: getOuterFrame afterTail ::
                  controls)
              (calls := calls) (s := s) (E := E) (Φ := Φ)
            unfold CallContract callExpr at Hwrite
            simp only [List.cons_append, List.nil_append] at Hwrite
            iapply Hwrite
            isplitl_exacts [Hruntime Hstreams Hslice]
            isplitl_pureexact ⟨by simp [borsh_option_u32_some], by decide⟩
            iintro Hruntime Hstreams Hslice
            isimp only [ResumeWP, resumeExpr, List.nil_append]
            simp only [getReplyFree]
            wasm_twp_pures [twp_localGet twp_const twp_const]
            have Hfree := func57_noop_correct (hlc := hlc) blockBase 1024 1
              (callerLocals :=
                ⟨[], [Value.i32 func18Base, .i32 blockBase, .i32 1, .i32 5,
                  .i32 1, .i32 payload], []⟩)
              (stack := []) (code := getTableDrop) (arity := arity)
              (remainder := remainder)
              (controls :=
                getOkFrame :: getDecodeFrame :: getOuterFrame afterTail ::
                  controls)
              (calls := calls) (s := s) (E := E) (Φ := Φ)
            unfold CallContract callExpr at Hfree
            simp only [List.cons_append, List.nil_append] at Hfree
            iapply Hfree
            isplitl_exact Hruntime
            · iintro Hruntime
              isimp only [ResumeWP, resumeExpr, List.nil_append]
              iapply twp_get_table_drop
              iframe
      · iintro Hbump Hstreams
        iapply Hoom
        isimp only [ExportOOM]
        iexists ([] : List UInt8), output
        iexact Hstreams

/-! ## The kernel call -/

set_option maxHeartbeats 2000000 in
/-- The lookup kernel, the two loads of its output, the marker call and
the reply.  The kernel writes `HashMap.Table.optionU32At`, and the two
loads move the discriminant into local 4 and the payload into local 5.
WAT lines 5200 to 5274. -/
theorem twp_get_kernel [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (k0 k1 : UInt64)
    (entries : HashMap.Map UInt32 UInt32) (key : UInt32)
    (outBefore : List UInt8)
    (storedCursor : UInt32) (frontier : Nat) (history : AllocationHistory)
    (output : List UInt8)
    {l2 l3 l4 l5 : UInt32} {afterTail : Program}
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hout : outBefore.length = 8)
    (hn : entries.length ≤ 2 ^ 30) :
    iprop(RuntimeContext ∗ StackPointer func18Base ∗
      Slices.ByteSlice 0 (func18Base + 8) outBefore ∗
      HashMap.Table.MapAt 0 (func18Base + 64) k0 k1 entries ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams [] output false ∗
      TailDone (output ++ Borsh.option Borsh.u32
          (HashMap.Table.get (HashMap.SipHash.hashU32 k0 k1)
            (HashMap.Table.ofEntries (HashMap.SipHash.hashU32 k0 k1) entries)
            key))
        afterTail arity remainder controls calls s E Φ ∗
      (ExportOOM -∗ Φ (.trapped (.host OOM.trapMessage)))) ⊢
      WP (.running
          ⟨⟨[], [Value.i32 func18Base, .i32 key, .i32 l2, .i32 l3, .i32 l4,
              .i32 l5], []⟩,
            getAfterCollect, arity, remainder,
            getOkFrame :: getDecodeFrame :: getOuterFrame afterTail ::
              controls, calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hout, Hmap, Hbump, Hstreams, Hcont, Hoom⟩
  obtain ⟨hwf, hclean, _, _⟩ :=
    HashMap.Table.wf_ofEntries_u32 k0 k1 entries hn
  isimp only [HashMap.Table.MapAt] at Hmap
  have h8 := offset_facts func18Base 8 8 rfl (by decide)
  have h12 := offset_facts func18Base 12 12 rfl (by decide)
  simp only [getAfterCollect]
  wasm_twp_pures [twp_localGet twp_const twp_add twp_localGet twp_const
    twp_add twp_localGet]
    rewriting [show (8 : UInt32) + func18Base = func18Base + 8 by decide,
      show (64 : UInt32) + func18Base = func18Base + 64 by decide]
  have Hkernel := func17_correct (hlc := hlc) (func18Base + 8)
    (func18Base + 64) key k0 k1
    (HashMap.Table.ofEntries (HashMap.SipHash.hashU32 k0 k1) entries)
    outBefore
    (callerLocals :=
      ⟨[], [Value.i32 func18Base, .i32 key, .i32 l2, .i32 l3, .i32 l4,
        .i32 l5], []⟩)
    (stack := []) (code := getAfterKernel) (arity := arity)
    (remainder := remainder)
    (controls :=
      getOkFrame :: getDecodeFrame :: getOuterFrame afterTail :: controls)
    (calls := calls) (s := s) (E := E) (Φ := Φ)
  unfold CallContract callExpr at Hkernel
  simp only [List.append_nil] at Hkernel
  iapply Hkernel
  isplitl_exacts [Hruntime Hout Hmap]
  isplitl_pureexact ⟨hout, by decide, by decide, hwf, hclean⟩
  iintro Hruntime Hanswer Hmap
  isimp only [ResumeWP, resumeExpr, List.nil_append]
  isimp only [HashMap.Table.HashMapAt] at Hmap
  icases Hmap with ⟨Htable, Hk0, Hk1⟩
  ihave Hheader := TableAt_header_words (func18Base + 64)
    (HashMap.Table.ofEntries (HashMap.SipHash.hashU32 k0 k1) entries) $$
    Htable
  icases Hheader with ⟨%ctrl, %mask, Hctrl, Hmask, Hitems⟩
  isimp only [show func18Base + 64 + 4 = func18Base + 68 by decide] at Hmask
  iclear Hk0 Hk1 Hitems
  simp only [getAfterKernel]
  cases hanswer : HashMap.Table.get (HashMap.SipHash.hashU32 k0 k1)
      (HashMap.Table.ofEntries (HashMap.SipHash.hashU32 k0 k1) entries)
      key with
  | none =>
      isimp only [hanswer, HashMap.Table.optionU32At] at Hanswer
      icases Hanswer with ⟨%pad, Htag, Hpay⟩
      isimp only [show func18Base + 8 + 4 = func18Base + 12 by decide] at Hpay
      wasm_twp_pures [twp_localGet]
      wasm_twp_rebind twp_load32 (address := func18Base) (offset := 12) pad
        h12.1 h12.2.1 h12.2.2.1 h12.2.2.2 with Hpay
      wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
        Nat.reduceSub, List.set]
      wasm_twp_pures [twp_localGet]
      wasm_twp_rebind twp_load32 (address := func18Base) (offset := 8) 0
        h8.1 h8.2.1 h8.2.2.1 h8.2.2.2 with Htag
      wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
        Nat.reduceSub, List.set]
      have Hmarker := func30_correct (hlc := hlc)
        (callerLocals :=
          ⟨[], [Value.i32 func18Base, .i32 key, .i32 l2, .i32 l3, .i32 0,
            .i32 pad], []⟩)
        (stack := []) (code := getReply) (arity := arity)
        (remainder := remainder)
        (controls :=
          getOkFrame :: getDecodeFrame :: getOuterFrame afterTail ::
            controls)
        (calls := calls) (s := s) (E := E) (Φ := Φ)
      unfold CallContract callExpr at Hmarker
      simp only [List.nil_append] at Hmarker
      iapply Hmarker
      isplitl_exact Hruntime
      · iintro Hruntime
        isimp only [ResumeWP, resumeExpr, List.nil_append]
        rw [show (0 : UInt32)
          = if (none : Option UInt32).isSome then 1 else 0 from rfl]
        iapply twp_get_reply heapId storedCursor frontier history output
          none pad (by simp)
        iframe
  | some v =>
      isimp only [hanswer, HashMap.Table.optionU32At] at Hanswer
      icases Hanswer with ⟨Htag, Hpay⟩
      isimp only [show func18Base + 8 + 4 = func18Base + 12 by decide] at Hpay
      wasm_twp_pures [twp_localGet]
      wasm_twp_rebind twp_load32 (address := func18Base) (offset := 12) v
        h12.1 h12.2.1 h12.2.2.1 h12.2.2.2 with Hpay
      wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
        Nat.reduceSub, List.set]
      wasm_twp_pures [twp_localGet]
      wasm_twp_rebind twp_load32 (address := func18Base) (offset := 8) 1
        h8.1 h8.2.1 h8.2.2.1 h8.2.2.2 with Htag
      wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
        Nat.reduceSub, List.set]
      have Hmarker := func30_correct (hlc := hlc)
        (callerLocals :=
          ⟨[], [Value.i32 func18Base, .i32 key, .i32 l2, .i32 l3, .i32 1,
            .i32 v], []⟩)
        (stack := []) (code := getReply) (arity := arity)
        (remainder := remainder)
        (controls :=
          getOkFrame :: getDecodeFrame :: getOuterFrame afterTail ::
            controls)
        (calls := calls) (s := s) (E := E) (Φ := Φ)
      unfold CallContract callExpr at Hmarker
      simp only [List.nil_append] at Hmarker
      iapply Hmarker
      isplitl_exact Hruntime
      · iintro Hruntime
        isimp only [ResumeWP, resumeExpr, List.nil_append]
        rw [show (1 : UInt32)
          = if (some v).isSome then 1 else 0 from rfl]
        iapply twp_get_reply heapId storedCursor frontier history output
          (some v) v (by simp)
        iframe

/-! ## The collect call -/

set_option maxHeartbeats 2000000 in
/-- The build of the hash table and the answer.  `collect_entries` takes
the pair buffer and gives the map value back in the first 32 bytes of the
chunk buffer.  The answer does not name the two seeds, because
`HashMap.Table.get_ofEntries_u32` removes them.  WAT lines 5194 to
5274. -/
theorem twp_get_collect [WasmSmallStepGS hlc Universal.State]
    (hfunc2 : CollectContract.Func2Spec (hlc := hlc))
    (heapId : GName) (cap bufPtr len key : UInt32)
    (entries : HashMap.Map UInt32 UInt32)
    (payload spare mapBefore outBefore keysBefore below : List UInt8)
    (storedCursor : UInt32) (frontier : Nat) (history : AllocationHistory)
    (output : List UInt8)
    {l2 l3 l4 l5 : UInt32} {afterTail : Program}
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hmapBefore : mapBefore.length = 32)
    (hout : outBefore.length = 8)
    (hkeys : keysBefore.length = randomStateSize)
    (hpayload : payload = CollectContract.entryCodec.serialize entries)
    (hentries : entries.length = len.toNat)
    (hcap : len.toNat ≤ cap.toNat)
    (hspare : spare.length = 8 * (cap.toNat - len.toNat))
    (hn : entries.length ≤ 2 ^ 30)
    (hstate : keysBefore[16]? ≠ some 2)
    (hmax : len.toNat ≤ maxTableCapacity)
    (halign : bufPtr.toNat % 4 = 0) :
    iprop(RuntimeContext ∗ StackPointer func18Base ∗
      StackBelow func18Base CollectContract.collectDepth below ∗
      Slices.ByteSlice 0 (func18Base + 8) outBefore ∗
      Slices.ByteSlice 0 (func18Base + 64) mapBefore ∗
      pointsTo_u32 0 (func18Base + 16) cap ∗
      pointsTo_u32 0 (func18Base + 20) bufPtr ∗
      pointsTo_u32 0 (func18Base + 24) len ∗
      Slices.ByteSlice 0 bufPtr (payload ++ spare) ∗
      Slices.ByteSlice 0 randomStateCell keysBefore ∗
      Slices.ByteSlice 0 entryStackTop staticTableBytes ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams [] output false ∗
      TailDone (output ++ Borsh.option Borsh.u32
          (HashMap.get (HashMap.ofEntries entries) key))
        afterTail arity remainder controls calls s E Φ ∗
      (ExportOOM -∗ Φ (.trapped (.host OOM.trapMessage)))) ⊢
      WP (.running
          ⟨⟨[], [Value.i32 func18Base, .i32 key, .i32 l2, .i32 l3, .i32 l4,
              .i32 l5], []⟩,
            getCollectAndReply, arity, remainder,
            getOkFrame :: getDecodeFrame :: getOuterFrame afterTail ::
              controls, calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hbelow, Hout, Hmap, Hcap, Hptr, Hlen, Hbuf, Hkeys,
    Hstatic, Hbump, Hstreams, Hcont, Hoom⟩
  ihave ⟨Hctrl, Hhdr, Hzero⟩ :=
    CollectContract.staticTable_resources $$ Hstatic
  ihave Hptr : pointsTo_u32 0 (func18Base + 16 + 4) bufPtr $$ [Hptr]
  · irw_exact [show func18Base + 16 + 4 = func18Base + 20 by decide] with Hptr
  ihave Hlen : pointsTo_u32 0 (func18Base + 16 + 8) len $$ [Hlen]
  · irw_exact [show func18Base + 16 + 8 = func18Base + 24 by decide] with Hlen
  simp only [getCollectAndReply]
  wasm_twp_pures [twp_localGet twp_const twp_add twp_localGet twp_const
    twp_add]
    rewriting [show (64 : UInt32) + func18Base = func18Base + 64 by decide,
      show (16 : UInt32) + func18Base = func18Base + 16 by decide]
  have Hcollect := hfunc2 func18Base (func18Base + 64) (func18Base + 16)
    cap bufPtr len heapId entries payload spare mapBefore keysBefore below
    storedCursor frontier history [] output false
    (callerLocals :=
      ⟨[], [Value.i32 func18Base, .i32 key, .i32 l2, .i32 l3, .i32 l4,
        .i32 l5], []⟩)
    (stack := []) (code := getAfterCollect) (arity := arity)
    (remainder := remainder)
    (controls :=
      getOkFrame :: getDecodeFrame :: getOuterFrame afterTail :: controls)
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
    isimp only [show HashMap.get (HashMap.ofEntries entries) key =
      HashMap.Table.get (HashMap.SipHash.hashU32 k0 k1)
        (HashMap.Table.ofEntries (HashMap.SipHash.hashU32 k0 k1) entries)
        key from
      (HashMap.Table.get_ofEntries_u32 k0 k1 entries hn key).symm] at Hcont
    iapply twp_get_kernel heapId k0 k1 entries key outBefore storedCursor'
      frontier' history' output hout hn
    iframe
  · iintro %remaining Hstreams
    iapply Hoom
    isimp only [ExportOOM]
    iexists remaining, output
    iexact Hstreams

/-! ## The header copy of the accept arm -/

set_option maxHeartbeats 2000000 in
/-- The accept arm after its guard.  The arm moves the decoded vector
header into the entries header at frame offset 16, moves the leading key
into local 1, and releases the input byte vector.  WAT lines 5174 to
5274. -/
theorem twp_get_accept_copy [WasmSmallStepGS hlc Universal.State]
    (hfunc2 : CollectContract.Func2Spec (hlc := hlc))
    (heapId : GName) (cap bufPtr len key oldLen : UInt32)
    (oldPair : UInt64)
    (entries : HashMap.Map UInt32 UInt32)
    (payload spare mapBefore outBefore keysBefore below : List UInt8)
    (storedCursor : UInt32) (frontier : Nat) (history : AllocationHistory)
    (output : List UInt8)
    {l1 l2 l3 l4 l5 : UInt32} {afterTail : Program}
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hmapBefore : mapBefore.length = 32)
    (hout : outBefore.length = 8)
    (hkeys : keysBefore.length = randomStateSize)
    (hpayload : payload = CollectContract.entryCodec.serialize entries)
    (hentries : entries.length = len.toNat)
    (hcap : len.toNat ≤ cap.toNat)
    (hspare : spare.length = 8 * (cap.toNat - len.toNat))
    (hn : entries.length ≤ 2 ^ 30)
    (hstate : keysBefore[16]? ≠ some 2)
    (hmax : len.toNat ≤ maxTableCapacity)
    (halign : bufPtr.toNat % 4 = 0) :
    iprop(RuntimeContext ∗ StackPointer func18Base ∗
      StackBelow func18Base CollectContract.collectDepth below ∗
      Slices.ByteSlice 0 (func18Base + 8) outBefore ∗
      pointsTo_u64 0 (func18Base + 16) oldPair ∗
      pointsTo_u32 0 (func18Base + 24) oldLen ∗
      pointsTo_u32 0 (func18Base + 36) key ∗
      pointsTo_u64 0 (func18Base + 40) (wordPair cap bufPtr) ∗
      pointsTo_u32 0 (func18Base + 48) len ∗
      Slices.ByteSlice 0 (func18Base + 64) mapBefore ∗
      Slices.ByteSlice 0 bufPtr (payload ++ spare) ∗
      Slices.ByteSlice 0 randomStateCell keysBefore ∗
      Slices.ByteSlice 0 entryStackTop staticTableBytes ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams [] output false ∗
      TailDone (output ++ Borsh.option Borsh.u32
          (HashMap.get (HashMap.ofEntries entries) key))
        afterTail arity remainder controls calls s E Φ ∗
      (ExportOOM -∗ Φ (.trapped (.host OOM.trapMessage)))) ⊢
      WP (.running
          ⟨⟨[], [Value.i32 func18Base, .i32 l1, .i32 l2, .i32 l3, .i32 l4,
              .i32 l5], []⟩,
            getOkBody, arity, remainder,
            getOkFrame :: getDecodeFrame :: getOuterFrame afterTail ::
              controls, calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hbelow, Hout, Hpair0, Hlen0, Hkey, Hpair, Hcount,
    Hmap, Hbuf, Hkeys, Hstatic, Hbump, Hstreams, Hcont, Hoom⟩
  have h16 := offset_facts64 func18Base 16 16 rfl (by decide)
  have h40 := offset_facts64 func18Base 40 40 rfl (by decide)
  have h24 := offset_facts func18Base 24 24 rfl (by decide)
  have h36 := offset_facts func18Base 36 36 rfl (by decide)
  have h48 := offset_facts func18Base 48 48 rfl (by decide)
  simp only [getOkBody]
  wasm_twp_block_move (func18Base, 40, wordPair cap bufPtr, h40)
    (func18Base, 16, oldPair, h16) with Hpair Hpair0
  ihave ⟨Hcapw, Hptrw⟩ :=
    (pointsTo_u32_pair_as_groupWord 0 (func18Base + 16) cap bufPtr).mpr $$
    [Hpair0]
  · iexact Hpair0
  ihave Hptrw : pointsTo_u32 0 (func18Base + 20) bufPtr $$ [Hptrw]
  · irw_exact [show func18Base + 20 = func18Base + 16 + 4 by decide]
      with Hptrw
  wasm_twp_pures [twp_localGet twp_localGet]
  wasm_twp_rebind twp_load32 (address := func18Base) (offset := 48) len
    h48.1 h48.2.1 h48.2.2.1 h48.2.2.2 with Hcount
  wasm_twp_rebind twp_store32 (address := func18Base) (offset := 24) oldLen
    h24.1 h24.2.1 h24.2.2.1 h24.2.2.2 with Hlen0
  wasm_twp_pures [twp_localGet]
  wasm_twp_rebind twp_load32 (address := func18Base) (offset := 36) key
    h36.1 h36.2.1 h36.2.2.1 h36.2.2.2 with Hkey
  wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_block]
  simp only [List.drop_zero]
  rw [getFreeInputFrame_literal]
  simp only [getFreeInput]
  by_cases hcapacity : l2 = 0
  · wasm_twp_pures [twp_localGet]
    iapply twp_eqz (result := 1) (by simp [hcapacity])
    iapply twp_brIf (by decide) (by rfl)
    simp only [getFreeInputFrame, List.take_zero, List.nil_append]
    iapply twp_get_collect hfunc2 heapId cap bufPtr len key entries payload
      spare mapBefore outBefore keysBefore below storedCursor frontier
      history output hmapBefore hout hkeys hpayload hentries hcap hspare hn
      hstate hmax halign
    iframe
  · wasm_twp_pures [twp_localGet]
    iapply twp_eqz (result := 0) (by simp [hcapacity])
    wasm_twp_pures [twp_brIfZero twp_localGet twp_localGet twp_const]
    have Hfree := func57_noop_correct (hlc := hlc) l3 l2 1
      (callerLocals :=
        ⟨[], [Value.i32 func18Base, .i32 key, .i32 l2, .i32 l3, .i32 l4,
          .i32 l5], []⟩)
      (stack := []) (code := []) (arity := arity) (remainder := remainder)
      (controls :=
        getFreeInputFrame :: getOkFrame :: getDecodeFrame ::
          getOuterFrame afterTail :: controls)
      (calls := calls) (s := s) (E := E) (Φ := Φ)
    unfold CallContract callExpr at Hfree
    simp only [List.cons_append, List.nil_append] at Hfree
    iapply Hfree
    isplitl_exact Hruntime
    · iintro Hruntime
      isimp only [ResumeWP, resumeExpr, List.nil_append]
      wasm_twp_pures [twp_exitControl]
      simp only [getFreeInputFrame, List.take_zero, List.nil_append]
      iapply twp_get_collect hfunc2 heapId cap bufPtr len key entries payload
        spare mapBefore outBefore keysBefore below storedCursor frontier
        history output hmapBefore hout hkeys hpayload hentries hcap hspare hn
        hstate hmax halign
      iframe

/-! ## The reject arm -/

set_option maxHeartbeats 2000000 in
/-- The release of the input byte vector on the reject arm, and the branch
that leaves the outer block.  WAT lines 5289 to 5296. -/
theorem twp_get_err_epilogue [WasmSmallStepGS hlc Universal.State]
    {l1 l2 l3 l4 l5 : UInt32} {afterTail : Program}
    {finalOutput : List UInt8} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp} :
    iprop(RuntimeContext ∗ StackPointer func18Base ∗
      Streams [] finalOutput false ∗
      TailDone finalOutput afterTail arity remainder controls calls s E Φ) ⊢
      WP (.running
          ⟨⟨[], [Value.i32 func18Base, .i32 l1, .i32 l2, .i32 l3, .i32 l4,
              .i32 l5], []⟩,
            getErrTail, arity, remainder,
            getDecodeFrame :: getOuterFrame afterTail :: controls, calls⟩ :
            Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hstreams, Hcont⟩
  simp only [getErrTail]
  by_cases hcapacity : l2 = 0
  · wasm_twp_pures [twp_localGet]
    iapply twp_eqz (result := 1) (by simp [hcapacity])
    iapply twp_brIf (by decide) (by rfl)
    simp only [getOuterFrame, List.take_zero, List.nil_append]
    iapply twp_get_stack_epilogue
    iframe
  · wasm_twp_pures [twp_localGet]
    iapply twp_eqz (result := 0) (by simp [hcapacity])
    wasm_twp_pures [twp_brIfZero twp_localGet twp_localGet twp_const]
    have Hfree := func57_noop_correct (hlc := hlc) l3 l2 1
      (callerLocals :=
        ⟨[], [Value.i32 func18Base, .i32 l1, .i32 l2, .i32 l3, .i32 l4,
          .i32 l5], []⟩)
      (stack := []) (code := [.br 1]) (arity := arity)
      (remainder := remainder)
      (controls := getDecodeFrame :: getOuterFrame afterTail :: controls)
      (calls := calls) (s := s) (E := E) (Φ := Φ)
    unfold CallContract callExpr at Hfree
    simp only [List.cons_append, List.nil_append] at Hfree
    iapply Hfree
    isplitl_exact Hruntime
    · iintro Hruntime
      isimp only [ResumeWP, resumeExpr, List.nil_append]
      iapply twp_br (by rfl)
      simp only [getOuterFrame, List.take_zero, List.nil_append]
      iapply twp_get_stack_epilogue
      iframe

set_option maxHeartbeats 2000000 in
/-- The reject arm.  It drops the decoded error string, releases the input
byte vector and leaves the outer block.  The driver writes no byte on this
arm.  WAT lines 5276 to 5296. -/
theorem twp_get_reject [WasmSmallStepGS hlc Universal.State]
    (word1 word2 : UInt32)
    {l1 l2 l3 l4 l5 : UInt32} {afterTail : Program}
    {finalOutput : List UInt8} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp} :
    iprop(RuntimeContext ∗ StackPointer func18Base ∗
      Streams [] finalOutput false ∗
      pointsTo_u32 0 (func18Base + 36) word1 ∗
      pointsTo_u32 0 (func18Base + 40) word2 ∗
      TailDone finalOutput afterTail arity remainder controls calls s E Φ) ⊢
      WP (.running
          ⟨⟨[], [Value.i32 func18Base, .i32 l1, .i32 l2, .i32 l3, .i32 l4,
              .i32 l5], []⟩,
            getErrArm, arity, remainder,
            getDecodeFrame :: getOuterFrame afterTail :: controls, calls⟩ :
            Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hstreams, Hword1, Hword2, Hcont⟩
  have h36 := offset_facts func18Base 36 36 rfl (by decide)
  have h40 := offset_facts func18Base 40 40 rfl (by decide)
  simp only [getErrArm_shape]
  wasm_twp_pures [twp_block]
  simp only [List.drop_zero]
  rw [getDropErrorFrame_literal]
  simp only [getDropError]
  wasm_twp_pures [twp_localGet]
  wasm_twp_rebind twp_load32 (address := func18Base) (offset := 36) word1
    h36.1 h36.2.1 h36.2.2.1 h36.2.2.2 with Hword1
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_const]
  by_cases hshort : word1.toInt32 < (1 : UInt32).toInt32
  · iapply twp_ltS (result := 1) (by rw [if_pos hshort])
    iapply twp_brIf (by decide) (by rfl)
    simp only [getDropErrorFrame, List.take_zero, List.nil_append]
    iapply twp_get_err_epilogue
    iframe
  · iapply twp_ltS (result := 0) (by rw [if_neg hshort])
    wasm_twp_pures [twp_brIfZero twp_localGet]
    wasm_twp_rebind twp_load32 (address := func18Base) (offset := 40) word2
      h40.1 h40.2.1 h40.2.2.1 h40.2.2.2 with Hword2
    wasm_twp_pures [twp_localGet twp_const]
    have Hfree := func57_noop_correct (hlc := hlc) word2 word1 1
      (callerLocals :=
        ⟨[], [Value.i32 func18Base, .i32 word1, .i32 l2, .i32 l3, .i32 l4,
          .i32 l5], []⟩)
      (stack := []) (code := []) (arity := arity) (remainder := remainder)
      (controls :=
        getDropErrorFrame :: getDecodeFrame :: getOuterFrame afterTail ::
          controls)
      (calls := calls) (s := s) (E := E) (Φ := Φ)
    unfold CallContract callExpr at Hfree
    simp only [List.cons_append, List.nil_append] at Hfree
    iapply Hfree
    isplitl_exact Hruntime
    · iintro Hruntime
      isimp only [ResumeWP, resumeExpr, List.nil_append]
      wasm_twp_pures [twp_exitControl]
      simp only [getDropErrorFrame, List.take_zero, List.nil_append]
      iapply twp_get_err_epilogue
      iframe

/-! ## The whole tail -/

set_option maxHeartbeats 2000000 in
/-- The tail of the `map_get` driver, from the end of the read loop to the
return.  `collect_entries` arrives as a hypothesis.  WAT lines 5162 to
5306. -/
theorem twp_get_tail [WasmSmallStepGS hlc Universal.State]
    (hfunc2 : CollectContract.Func2Spec (hlc := hlc)) :
    LookupTailContracts.GetTailSpec (hlc := hlc) := by
  unfold LookupTailContracts.GetTailSpec
  intro heapId capacity ptr aux4 input output reserve head chunk extra
    keysBefore dataBytes storedCursor frontier history afterTail arity
    remainder controls calls s E Φ
  iintro ⟨HafterRead, Hextra, Hkeys, Hdata, %hsizes, Hcont, Hoom⟩
  obtain ⟨hextra, hkeys, hdata, hstate, hstatic, hinput⟩ := hsizes
  isimp only [AfterReadGet] at HafterRead
  icases HafterRead with ⟨Hruntime, Hsp, Hreserve, Hhead, Hvec, Hchunk,
    Hbump, Hstreams, %hshape⟩
  obtain ⟨hhead, hchunk, hpush⟩ := hshape
  have hlenNat : (UInt32.ofNat input.length).toNat = input.length :=
    UInt32.toNat_ofNat_of_lt' hinput
  isimp only [← lookupCalleeDepth_keyDecoder] at Hextra
  ihave Hbelow : StackBelow func18Base keyDecoderDepth (extra ++ reserve) $$
      [Hextra Hreserve]
  · iapply StackBelow_of_reserve_at func18Base keyDecoderDepth extra reserve
      (by rw [hextra]; rfl) (by decide) (by decide)
    iframe
  -- the kernel output slot at 8, the entries header at 16, and the output
  -- slot of the key decoder at 32
  icases (ByteSlice_split_at func18Base 8 head (by simp [hhead])).mp $$ Hhead
    with ⟨_Hgap0, Hhead1⟩
  isimp only [UInt32.reduceToNat] at Hhead1
  icases (ByteSlice_split_at (func18Base + 8) 8 (head.drop 8)
    (by simp [hhead])).mp $$ Hhead1 with ⟨Hout, Hhead2⟩
  isimp only [UInt32.reduceToNat] at Hout
  isimp only [UInt32.reduceToNat,
    show func18Base + 8 + 8 = func18Base + 16 by decide,
    show (head.drop 8).drop 8 = head.drop 16 from by
      simp [List.drop_drop]] at Hhead2
  icases (ByteSlice_split_at (func18Base + 16) 12 (head.drop 16)
    (by simp [hhead])).mp $$ Hhead2 with ⟨Hhead0, Hhead3⟩
  isimp only [UInt32.reduceToNat] at Hhead0
  isimp only [UInt32.reduceToNat,
    show func18Base + 16 + 12 = func18Base + 28 by decide,
    show (head.drop 16).drop 12 = head.drop 28 from by
      simp [List.drop_drop]] at Hhead3
  icases (ByteSlice_split_at (func18Base + 28) 4 (head.drop 28)
    (by simp [hhead])).mp $$ Hhead3 with ⟨_Hgap1, Hslot⟩
  isimp only [UInt32.reduceToNat,
    show func18Base + 28 + 4 = func18Base + 32 by decide,
    show (head.drop 28).drop 4 = head.drop 32 from by
      simp [List.drop_drop]] at Hslot
  ihave Hwords := ByteSlice_header_as_words (func18Base + 16)
    ((head.drop 16).take 12) (by simp [hhead]) (by decide) $$ Hhead0
  icases Hwords with ⟨%oldCap, %oldPtr, %oldLen, Hcapw, Hptrw, Hlenw⟩
  ihave HoldPair :=
    (pointsTo_u32_pair_as_groupWord 0 (func18Base + 16) oldCap oldPtr).mp $$
    [Hcapw Hptrw]
  · iframe
  ihave Hlenw : pointsTo_u32 0 (func18Base + 24) oldLen $$ [Hlenw]
  · irw_exact [show func18Base + 16 + 8 = func18Base + 24 by decide]
      with Hlenw
  -- the map slot is the head of the chunk buffer
  icases (ByteSlice_split_at (func18Base + 64) 32 chunk
    (by simp [hchunk])).mp $$ Hchunk with ⟨Hmap, _Hchunkrest⟩
  isimp only [UInt32.reduceToNat] at Hmap
  ihave ⟨_Hheader, Hstorage⟩ :=
    (VecU8_as_headerBytes_storage heapId (func18Base + 52) capacity ptr input
      (by decide)).mp $$ Hvec
  ihave ⟨Hstorage, %hcapFits⟩ :=
    VecStorage_length_le heapId capacity ptr input $$ Hstorage
  ihave Hinput := VecStorage_bytes heapId capacity ptr input $$ Hstorage
  simp only [func18AfterRead_cons, afterReadLocalsGet]
  wasm_twp_pures [twp_localGet twp_const twp_add twp_localGet twp_localGet]
    rewriting [show (32 : UInt32) + func18Base = func18Base + 32 by decide]
  have Hdecode := func7_correct (hlc := hlc) func18Base (func18Base + 32) ptr
    (UInt32.ofNat input.length) heapId input (head.drop 32) (extra ++ reserve)
    dataBytes storedCursor frontier history [] output false
    (callerLocals :=
      ⟨[], [Value.i32 func18Base, .i32 (UInt32.ofNat input.length),
        .i32 capacity, .i32 ptr, .i32 aux4, .i32 0], []⟩)
    (stack := []) (code := getAfterDecode afterTail) (arity := arity)
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
    ihave ⟨H32, H36, H40, H44, H48⟩ :=
      ByteSlice_five_words (func18Base + 32) 0 (leadingKey input) cap' buffer
        (pairCount input) $$ Hslot
    isimp only [show func18Base + 32 + 4 = func18Base + 36 by decide] at H36
    isimp only [show func18Base + 32 + 4 + 4 = func18Base + 40 by decide]
      at H40
    isimp only [show func18Base + 32 + 4 + 4 + 4 = func18Base + 44 by decide]
      at H44
    isimp only [show func18Base + 32 + 4 + 4 + 4 + 4 = func18Base + 48
      by decide] at H48
    ihave Hpair :=
      (pointsTo_u32_pair_as_groupWord 0 (func18Base + 40) cap' buffer).mp $$
      [H40 H44]
    · isplitl_exact H40
      · irw_exact [show func18Base + 40 + 4 = func18Base + 44 by decide]
          with H44
    simp only [getAfterDecode]
    wasm_twp_pures [twp_block]
    simp only [List.drop_zero]
    rw [getOuterFrame_literal]
    simp only [getOuterBody]
    wasm_twp_pures [twp_block]
    simp only [List.drop_zero]
    rw [getDecodeFrame_literal]
    simp only [getDecodeBlock]
    wasm_twp_pures [twp_block]
    simp only [List.drop_zero]
    rw [getOkFrame_literal]
    simp only [getOkArm_shape]
    have h32 := offset_facts func18Base 32 32 rfl (by decide)
    wasm_twp_pures [twp_localGet]
    wasm_twp_rebind twp_load32 (address := func18Base) (offset := 32) 0
      h32.1 h32.2.1 h32.2.2.1 h32.2.2.2 with H32
    wasm_twp_pures [twp_brIfZero]
    ihave ⟨_Hlow, Hbelow⟩ :=
      StackBelow_split func18Base keyDecoderDepth
        CollectContract.collectDepth below' (by decide) (by decide) $$ Hbelow
    rw [getOutput_of_accepts input 0 0 haccept hn,
      HashMap.Table.get_ofEntries_u32 0 0 (acceptedEntries input) hn
        (leadingKey input)]
    iapply twp_get_accept_copy hfunc2 heapId cap' buffer (pairCount input)
      (leadingKey input) oldLen (wordPair oldCap oldPtr)
      (acceptedEntries input) (keyPayload input) spare' (chunk.take 32)
      ((head.drop 8).take 8) keysBefore
      (below'.drop (keyDecoderDepth - CollectContract.collectDepth))
      storedCursor' frontier' history' output
      (by simp [hchunk]) (by simp [hhead]) hkeys
      (keyPayload_serialize input haccept).symm
      (acceptedEntries_length input) hcapBound hspareLen hn hstate hmax halign
    iframe
  · isplit
    · -- the reject arm
      iintro %word1 %word2 %word3 %word4 %below' %storedCursor' %frontier'
        %history' %hreject Hruntime Hsp Hbelow Hslot Hbytes Hdata Hbump
        Hstreams %hword1
      isimp only [ResumeWP, resumeExpr, List.nil_append]
      ihave ⟨H32, H36, H40, _H44, _H48⟩ :=
        ByteSlice_five_words (func18Base + 32) 1 word1 word2 word3 word4 $$
        Hslot
      isimp only [show func18Base + 32 + 4 = func18Base + 36 by decide] at H36
      isimp only [show func18Base + 32 + 4 + 4 = func18Base + 40 by decide]
        at H40
      simp only [getAfterDecode]
      wasm_twp_pures [twp_block]
      simp only [List.drop_zero]
      rw [getOuterFrame_literal]
      simp only [getOuterBody]
      wasm_twp_pures [twp_block]
      simp only [List.drop_zero]
      rw [getDecodeFrame_literal]
      simp only [getDecodeBlock]
      wasm_twp_pures [twp_block]
      simp only [List.drop_zero]
      rw [getOkFrame_literal]
      simp only [getOkArm_shape]
      have h32 := offset_facts func18Base 32 32 rfl (by decide)
      wasm_twp_pures [twp_localGet]
      wasm_twp_rebind twp_load32 (address := func18Base) (offset := 32) 1
        h32.1 h32.2.1 h32.2.2.1 h32.2.2.2 with H32
      iapply twp_brIf (by decide) (by rfl)
      simp only [getOkFrame, List.take_zero, List.nil_append]
      rw [getOutput_of_rejects input hreject, List.append_nil]
      iapply twp_get_reject word1 word2
      iframe
    · iintro %remaining' Hstreams
      iapply Hoom
      isimp only [ExportOOM]
      iexists remaining', output
      iexact Hstreams

end Project.RustHashMap.GetTailProof
