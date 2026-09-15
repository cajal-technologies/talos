import Project.RustHashMap.InsertTailContracts
import Project.RustHashMap.InsertPures
import Project.RustHashMap.RemoveTailProof
import Project.RustHashMap.Func1Proof
import Project.RustHashMap.Func49Proof
import Project.RustHashMap.Func52Proof
import Project.RustHashMap.Func4Proof
import Project.RustHashMap.Func5Proof

/-!
# The tail of the `map_insert` driver: the proof

`Project.RustHashMap.InsertTailContracts.InsertTailSpec` is the contract
of everything after the read phase of absolute `func 3`.  This module
proves it.  `collect_entries`, absolute `func 5`, and the insert shim,
absolute `func 6`, are the two open contracts; every other callee is a
proved theorem.

The proof follows the block structure of
`Project.RustHashMap.InsertTailDefs`, one lemma for each control block,
from the innermost outward.  `Project.RustHashMap.RemoveTailProof` is
the template, because the success tail of `map_remove` is this one with
the frame offsets moved.

## The seven blocks

The driver opens seven blocks in a row.  `insOuterFrame` is the block
that every path leaves; its continuation is the stack epilogue.
`insBlock2Frame` to `insBlock7Frame` are the six inner ones, and each
one carries the arm that its own exit runs.  Five small blocks open
later: the block of the first error arm, the guard block of the
decoder, and the three blocks of the free tests.

## Why the input vector is not rejoined

The read phase hands the input as `VecU8`.  The tail splits it into the
three header words and the storage, reads the storage as plain bytes,
and never puts the two back together.  The reason is that every free of
the input goes through `Project.RustHashMap.DeallocNoop`, whose body is
empty, so no path needs the block back.  The three header words are
dead after WAT 136, and the map slot of the collect call overlays them.
-/

namespace Project.RustHashMap.InsertTailProof

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
open Project.RustHashMap.DecodeErrorContracts
open Project.RustHashMap.KeyDecoderContract
open Project.RustHashMap.FrameCells
open Project.RustHashMap.LookupPures
open Project.RustHashMap.InsertPures
open Project.RustHashMap.DeallocNoop
open Project.RustHashMap.Func1Proof
open Project.RustHashMap.Func4Proof
open Project.RustHashMap.Func5Proof
open Project.RustHashMap.Func49Proof
open Project.RustHashMap.Func52Proof
open Project.RustHashMap.ReadAll
open Project.RustHashMap.InsertRead
open Project.RustHashMap.InsertTailDefs
open Project.RustHashMap.InsertTailContracts
open Project.RustHashMap.DriverTail
open Project.RustHashMap.DriverTailProof
open Project.RustHashMap.ContainsKeyTailProof
open scoped Wasm.SmallStep.Outcome

/-! ## The shape of the epilogue -/

/-- The stack epilogue in literal form.  WAT lines 465 to 468. -/
theorem insEpilogue_shape :
    insEpilogue = [.localGet 0, .const 368, .add, .globalSet 0] := rfl

/-! ## The control frames of the seven blocks -/

/-- The outermost block of the tail.  Its continuation is the stack
epilogue, so every path that leaves it returns. -/
def insOuterFrame (afterTail : Program) : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body := insOuterBody, continuation := insEpilogue ++ afterTail,
    belowStack := [] }

/-- The second block.  Its continuation is the success tail. -/
def insBlock2Frame : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body := insBlock2Body, continuation := insAfter2, belowStack := [] }

/-- The third block.  Its continuation is the reject exit. -/
def insBlock3Frame : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body := insBlock3Body, continuation := insAfter3, belowStack := [] }

/-- The fourth block.  Its continuation is the decoder call. -/
def insBlock4Frame : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body := insBlock4Body, continuation := insAfter4, belowStack := [] }

/-- The fifth block.  Its continuation is the second error arm. -/
def insBlock5Frame : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body := insBlock5Body, continuation := insAfter5, belowStack := [] }

/-- The sixth block.  Its continuation is the first error arm. -/
def insBlock6Frame : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body := insBlock6Body, continuation := insAfter6, belowStack := [] }

/-- The seventh block.  Its continuation is the empty arm. -/
def insBlock7Frame : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body := insBlock7Body, continuation := insAfter7, belowStack := [] }

theorem insOuterFrame_literal (afterTail : Program) :
    ({ kind := .block, paramArity := 0, resultArity := 0,
       body := insOuterBody, continuation := insEpilogue ++ afterTail,
       belowStack := [] } : ControlFrame) = insOuterFrame afterTail := rfl

/-- The seven frames of the non-empty exit, in literal form. -/
theorem insControls7_eq (afterTail : Program)
    (controls : List ControlFrame) :
    insControls7 (insEpilogue ++ afterTail) ++ controls =
      insBlock7Frame :: insBlock6Frame :: insBlock5Frame ::
        insBlock4Frame :: insBlock3Frame :: insBlock2Frame ::
          insOuterFrame afterTail :: controls := rfl

/-- The six frames of the empty exit, in literal form. -/
theorem insControls6_eq (afterTail : Program)
    (controls : List ControlFrame) :
    insControls6 (insEpilogue ++ afterTail) ++ controls =
      insBlock6Frame :: insBlock5Frame :: insBlock4Frame ::
        insBlock3Frame :: insBlock2Frame :: insOuterFrame afterTail ::
          controls := rfl

/-! ## The control frames of the five small blocks -/

/-- The block that drops the decoded error string on the reject exit. -/
def insDropErrorFrame : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body := insDropError, continuation := insRejectTail,
    belowStack := [] }

theorem insDropErrorFrame_literal :
    ({ kind := .block, paramArity := 0, resultArity := 0,
       body := insDropError, continuation := insRejectTail,
       belowStack := [] } : ControlFrame) = insDropErrorFrame := rfl

/-- The block of the first error arm.  The two dead tag tests leave
it. -/
def insErrFrameA : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body := insErrBodyA, continuation := insErrTailA, belowStack := [] }

theorem insErrFrameA_literal :
    ({ kind := .block, paramArity := 0, resultArity := 0,
       body := insErrBodyA, continuation := insErrTailA,
       belowStack := [] } : ControlFrame) = insErrFrameA := rfl

/-- The guard block of the decoder answer. -/
def insOkGuardFrame : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body := insOkGuard, continuation := insAfterDecode,
    belowStack := [] }

theorem insOkGuardFrame_literal :
    ({ kind := .block, paramArity := 0, resultArity := 0,
       body := insOkGuard, continuation := insAfterDecode,
       belowStack := [] } : ControlFrame) = insOkGuardFrame := rfl

/-- The block that releases the input before the collect call. -/
def insFreeInputFrame : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body := insFreeInput, continuation := insCollectAndRest,
    belowStack := [] }

theorem insFreeInputFrame_literal :
    ({ kind := .block, paramArity := 0, resultArity := 0,
       body := insFreeInput, continuation := insCollectAndRest,
       belowStack := [] } : ControlFrame) = insFreeInputFrame := rfl

/-- The block that releases the pair buffer after the reply. -/
def insFreePairsFrame : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body := insFreePairs, continuation := insTableDrop,
    belowStack := [] }

theorem insFreePairsFrame_literal :
    ({ kind := .block, paramArity := 0, resultArity := 0,
       body := insFreePairs, continuation := insTableDrop,
       belowStack := [] } : ControlFrame) = insFreePairsFrame := rfl

/-! ## Pure helpers

The lemmas below carry no program state.  Each one repeats a shape that
`Project.RustHashMap.RemoveTailProof` states privately, so the insert
tail cannot import it. -/

/-- The address of a shallower region inside a deeper one. -/
private theorem stack_addr (sp : UInt32) (deep shallow : Nat)
    (hle : shallow ≤ deep) :
    sp - UInt32.ofNat deep + UInt32.ofNat (deep - shallow)
      = sp - UInt32.ofNat shallow := by
  obtain ⟨e, rfl⟩ : ∃ e, deep = shallow + e := ⟨deep - shallow, by omega⟩
  rw [Nat.add_sub_cancel_left, UInt32.ofNat_add,
    ← HashMap.Table.sub_sub_addr, UInt32.sub_add_cancel]

/-- Hand a callee the top `shallow` bytes of the region and take them
back afterwards. -/
private theorem StackBelow_reshape [WasmHeapGS Universal.State]
    (sp : UInt32) (deep shallow : Nat) (bytes : List UInt8)
    (hle : shallow ≤ deep) :
    StackBelow sp deep bytes ⊢
      iprop(∃ low : List UInt8, StackBelow sp shallow low ∗
        (∀ below' : List UInt8, StackBelow sp shallow below' -∗
          ∃ b : List UInt8, StackBelow sp deep b)) := by
  iintro Hbelow
  ihave ⟨Hbelow, %hlen⟩ := StackBelow_length sp deep bytes $$ Hbelow
  ihave ⟨Hlow, Hhigh⟩ :=
    StackBelow_split sp deep shallow bytes hle
      (stack_addr sp deep shallow hle) $$ Hbelow
  iexists (bytes.drop (deep - shallow))
  isplitl [Hhigh]
  · iexact Hhigh
  · iintro %below' Hbelow'
    iexists (bytes.take (deep - shallow) ++ below')
    iapply StackBelow_join sp deep shallow (bytes.take (deep - shallow))
      below' (by rw [List.length_take, hlen]; omega) hle
      (stack_addr sp deep shallow hle)
    iframe Hlow Hbelow'

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

/-- Three cells back as a twelve-byte header. -/
private theorem ByteSlice_of_three_words [WasmHeapGS Universal.State]
    (ptr : UInt32) (w0 w1 w2 : UInt32)
    (hnowrap : ptr.toNat + 12 < UInt32.size) :
    iprop(pointsTo_u32 (α := Universal.State) 0 ptr w0 ∗
        pointsTo_u32 0 (ptr + 4) w1 ∗
        pointsTo_u32 0 (ptr + 4 + 4) w2) ⊢
      Slices.ByteSlice 0 ptr
        (WordCodec.u32le.serialize [w0, w1, w2]) := by
  iintro ⟨H0, H1, H2⟩
  isimp only [Slices.ByteSlice]
  isplitl_pureexact (by
    rw [show (WordCodec.u32le.serialize [w0, w1, w2]).length = 12
      from rfl]
    exact hnowrap)
  iapply (Slices.arrayAt_eq_wordCells (α := Universal.State) 0 ptr
    [w0, w1, w2]).mp
  isimp only [arrayAt]
  iframe H0 H1 H2

/-- Four cells back as a sixteen-byte slot.  The two error arms rebuild
the slot that absolute `func 55` wrote. -/
private theorem ByteSlice_of_four_words [WasmHeapGS Universal.State]
    (ptr : UInt32) (w0 w1 w2 w3 : UInt32)
    (hnowrap : ptr.toNat + 16 < UInt32.size) :
    iprop(pointsTo_u32 (α := Universal.State) 0 ptr w0 ∗
        pointsTo_u32 0 (ptr + 4) w1 ∗ pointsTo_u32 0 (ptr + 4 + 4) w2 ∗
        pointsTo_u32 0 (ptr + 4 + 4 + 4) w3) ⊢
      Slices.ByteSlice 0 ptr
        (WordCodec.u32le.serialize [w0, w1, w2, w3]) := by
  iintro ⟨H0, H1, H2, H3⟩
  isimp only [Slices.ByteSlice]
  isplitl_pureexact (by
    rw [show (WordCodec.u32le.serialize [w0, w1, w2, w3]).length = 16
      from rfl]
    exact hnowrap)
  iapply (Slices.arrayAt_eq_wordCells (α := Universal.State) 0 ptr
    [w0, w1, w2, w3]).mp
  isimp only [arrayAt]
  iframe H0 H1 H2 H3

/-- The vector storage reports that the initialized bytes fit in the
capacity. -/
private theorem VecStorage_fits [WasmHeapGS Universal.State]
    (heapId : GName) (capacity ptr : UInt32)
    (initialized : List UInt8) :
    VecStorage heapId capacity ptr initialized ⊢
      iprop(VecStorage heapId capacity ptr initialized ∗
        ⌜initialized.length ≤ capacity.toNat⌝) := by
  iintro Hstorage
  isimp only [VecStorage] at Hstorage
  icases Hstorage with (%hempty | ⟨%allocationId, %allBytes, %spare,
    %hfacts, Hblock⟩)
  · isplitl []
    · isimp only [VecStorage]
      ileft
      ipureexact hempty
    · ipureexact (by rw [hempty.2.2]; exact Nat.zero_le _)
  · isplitl [Hblock]
    · isimp only [VecStorage]
      iright
      iexists allocationId, allBytes, spare
      isplitl_pureexact hfacts
      · iexact Hblock
    · ipureexact hfacts.2.1

/-- The map value as four `u64` cells with the header words named, and
the wand that puts it back at another address. -/
private theorem HashMapAt_move_words [WasmHeapGS Universal.State]
    (src dst : UInt32) (k0 k1 : UInt64)
    (t : HashMap.Table UInt32 UInt32) :
    HashMap.Table.HashMapAt (α := Universal.State) 0 src k0 k1 t ⊢
      iprop(∃ ctrl : UInt32, ∃ mask : UInt32, ∃ growthLeft : UInt32,
        ∃ items : UInt32,
        pointsTo_u64 0 src (wordPair ctrl mask) ∗
        pointsTo_u64 0 (src + 8) (wordPair growthLeft items) ∗
        pointsTo_u64 0 (src + 16) k0 ∗ pointsTo_u64 0 (src + 24) k1 ∗
        (pointsTo_u64 0 dst (wordPair ctrl mask) -∗
          pointsTo_u64 0 (dst + 8) (wordPair growthLeft items) -∗
          pointsTo_u64 0 (dst + 16) k0 -∗
          pointsTo_u64 0 (dst + 24) k1 -∗
          HashMap.Table.HashMapAt 0 dst k0 k1 t)) := by
  iintro Hmap
  isimp only [HashMap.Table.HashMapAt] at Hmap
  icases Hmap with ⟨Htable, Hk0, Hk1⟩
  ihave ⟨%ctrl, %mask, %growthLeft, %items, Hheader, Hback⟩ :=
    TableAt_relocate 0 src dst t $$ Htable
  ihave Hcells :=
    (tableHeader_as_u64 0 src ctrl mask growthLeft items).mp $$ Hheader
  icases Hcells with ⟨Hc0, Hc1⟩
  iexists ctrl, mask, growthLeft, items
  iframe Hc0 Hc1 Hk0 Hk1
  iintro Hd0 Hd1 Hdk0 Hdk1
  ihave Hheader :
      HashMap.Table.tableHeader 0 dst ctrl mask growthLeft items
      $$ [Hd0 Hd1]
  · iapply (tableHeader_as_u64 0 dst ctrl mask growthLeft items).mpr
    iframe Hd0 Hd1
  ihave Htable := Hback $$ Hheader
  isimp only [HashMap.Table.HashMapAt]
  iframe Htable Hdk0 Hdk1

/-- The bytes that the reply writer reads. -/
private theorem PairVecAt_bytes [WasmHeapGS Universal.State]
    (heapId : GName) (allocationId capacity : Nat) (ptr : UInt32)
    (pairs : List (UInt32 × UInt32)) :
    PairVecAt heapId allocationId capacity ptr pairs ⊢
      iprop(Slices.ByteSlice 0 ptr (HashMap.Table.pairBytes pairs) ∗
        ⌜ptr.toNat + 8 * pairs.length < UInt32.size⌝) := by
  unfold PairVecAt
  by_cases hcap : capacity = 0
  · rw [if_pos hcap]
    iintro %hfacts
    obtain ⟨hptr, hpairs⟩ := hfacts
    subst hptr
    subst hpairs
    isimp only [HashMap.Table.pairBytes_nil, List.length_nil,
      Nat.mul_zero, Nat.add_zero]
    isplitl []
    · isimp only [Slices.ByteSlice, List.length_nil]
      isplitl_pureexact (by decide)
      · iapply (pointsToBytes_nil 0 (4 : UInt32)).mpr
        itrivial
    · ipureexact (by decide)
  · rw [if_neg hcap]
    iintro ⟨%pad, %hlen, Hblock⟩
    iunfold LiveBlock at Hblock
    icases Hblock with ⟨_Htoken, Hbytes, %_hfields⟩
    ihave ⟨Hlow, _Hhigh⟩ :=
      (Slices.ByteSlice_append 0 ptr (HashMap.Table.pairBytes pairs)
        pad).mp $$ Hbytes
    isimp only [Slices.ByteSlice] at Hlow
    icases Hlow with ⟨%hbound, Hlow⟩
    isplitl [Hlow]
    · isimp only [Slices.ByteSlice]
      isplitl_pureexact hbound
      · iexact Hlow
    · ipureexact (by
        rw [← HashMap.Table.pairBytes_length pairs]
        exact hbound)

/-- Cut a static message out of the data segment and put it back.  The
two error arms read "failed to fill whole buffer" at 1049080 and the
trailing-bytes arm reads "Not all bytes read" at 1049107. -/
private theorem dataSegment_cut [WasmHeapGS Universal.State]
    (dataBytes : List UInt8) (hdata : dataBytes.length = dataSegmentSize)
    (start len addr : UInt32)
    (hstart : entryStackTop + start = addr)
    (hfit : start.toNat + len.toNat ≤ dataSegmentSize) :
    Slices.ByteSlice (α := Universal.State) 0 entryStackTop dataBytes ⊢
      iprop(Slices.ByteSlice 0 addr
          ((dataBytes.drop start.toNat).take len.toNat) ∗
        (Slices.ByteSlice 0 addr
            ((dataBytes.drop start.toNat).take len.toNat) -∗
          Slices.ByteSlice 0 entryStackTop dataBytes)) := by
  have hk1 : start.toNat ≤ dataBytes.length := by rw [hdata]; omega
  have hk2 : len.toNat ≤ (dataBytes.drop start.toNat).length := by
    rw [List.length_drop, hdata]; omega
  iintro Hbytes
  icases (ByteSlice_split_at entryStackTop start dataBytes hk1).mp $$
    Hbytes with ⟨Hhead, Hrest⟩
  isimp only [hstart] at Hrest
  icases (ByteSlice_split_at addr len (dataBytes.drop start.toNat)
    hk2).mp $$ Hrest with ⟨Hmid, Htail⟩
  isplitl [Hmid]
  · iexact Hmid
  · iintro Hmid
    ihave Hrest :=
      (ByteSlice_split_at addr len (dataBytes.drop start.toNat)
        hk2).mpr $$ [Hmid Htail]
    · isplitl_exact Hmid
      · iexact Htail
    ihave Hall :=
      (ByteSlice_split_at entryStackTop start dataBytes hk1).mpr $$
      [Hhead Hrest]
    · isplitl_exact Hhead
      · irw_exact [hstart] with Hrest
    iexact Hall

/-- The conversion of the decode error takes less stack than the
deepest callee of the tail. -/
private theorem func49Depth_le_insert :
    func49Depth ≤ insertCalleeDepth := by decide

/-! ## The stack epilogue -/

set_option maxHeartbeats 2000000 in
/-- The stack pointer restore that ends every path.  The driver frame is
368 bytes and the driver declares seven locals, the last of them an
`i64`.  WAT lines 465 to 468. -/
theorem twp_ins_epilogue [WasmSmallStepGS hlc Universal.State]
    {l1 l2 l3 l4 l5 : UInt32} {v6 : UInt64} {afterTail : Program}
    {finalOutput : List UInt8} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp} :
    iprop(RuntimeContext ∗ StackPointer func0Base ∗
      Streams [] finalOutput false ∗
      TailDone finalOutput afterTail arity remainder controls calls
        s E Φ) ⊢
      WP (.running
          ⟨⟨[], [Value.i32 func0Base, .i32 l1, .i32 l2, .i32 l3, .i32 l4,
              .i32 l5, .i64 v6], []⟩,
            insEpilogue ++ afterTail, arity, remainder, controls,
            calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hstreams, Hcont⟩
  isimp only [StackPointer] at Hsp
  isimp only [TailDone] at Hcont
  simp only [insEpilogue_shape, List.cons_append, List.nil_append]
  wasm_twp_pures [twp_localGet twp_const twp_add]
  rw [show (368 : UInt32) + func0Base = entryStackTop by decide]
  wasm_twp_rebind twp_globalSet with Hsp
  ihave Hsp : StackPointer entryStackTop $$ [Hsp]
  · unfold StackPointer
    iexact Hsp
  iapply Hcont $$ %(⟨[], [Value.i32 func0Base, .i32 l1, .i32 l2, .i32 l3,
    .i32 l4, .i32 l5, .i64 v6], []⟩ : Locals) Hruntime Hsp Hstreams

/-! ## The table drop -/

set_option maxHeartbeats 2000000 in
/-- The drop of the hash table, which is the last step of the success
tail.  The first guard reads the bucket count at map offset 4 and the
second guard tests the wrapped total size.  Both arms of both guards
reach `insOuterFrame`, so neither guard has to be decided.  The arm
carries no branch of its own, so the last free falls out of the outer
block.  WAT lines 439 to 463. -/
theorem twp_ins_table_drop [WasmSmallStepGS hlc Universal.State]
    {l1 l2 l3 l4 l5 ctrl mask : UInt32} {v6 : UInt64}
    {afterTail : Program} {finalOutput : List UInt8} {arity : Nat}
    {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp} :
    iprop(RuntimeContext ∗ StackPointer func0Base ∗
      Streams [] finalOutput false ∗
      pointsTo_u32 0 (func0Base + 24) ctrl ∗
      pointsTo_u32 0 (func0Base + 28) mask ∗
      TailDone finalOutput afterTail arity remainder controls calls
        s E Φ) ⊢
      WP (.running
          ⟨⟨[], [Value.i32 func0Base, .i32 l1, .i32 l2, .i32 l3, .i32 l4,
              .i32 l5, .i64 v6], []⟩,
            insTableDrop, arity, remainder,
            insOuterFrame afterTail :: controls, calls⟩ :
            Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hstreams, Hctrl, Hmask, Hcont⟩
  have h24 := offset_facts func0Base 24 24 rfl (by decide)
  have h28 := offset_facts func0Base 28 28 rfl (by decide)
  simp only [insTableDrop]
  wasm_twp_pures [twp_localGet]
  wasm_twp_rebind twp_load32 (address := func0Base) (offset := 28) mask
    h28.1 h28.2.1 h28.2.2.1 h28.2.2.2 with Hmask
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  by_cases hmask : mask = 0
  · iapply twp_eqz (result := 1) (by simp [hmask])
    iapply twp_brIf (by decide) (by rfl)
    simp only [insOuterFrame, List.take_zero, List.nil_append]
    iapply twp_ins_epilogue
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
      simp only [insOuterFrame, List.take_zero, List.nil_append]
      iapply twp_ins_epilogue
      iframe
    · iapply twp_eqz (result := 0) (by simp [hsize])
      wasm_twp_pures [twp_brIfZero twp_localGet]
      wasm_twp_rebind twp_load32 (address := func0Base) (offset := 24)
        ctrl h24.1 h24.2.1 h24.2.2.1 h24.2.2.2 with Hctrl
      wasm_twp_pures [twp_localGet twp_sub twp_const twp_add
        twp_localGet twp_const]
      have Hfree := func57_noop_correct (hlc := hlc)
        ((4294967288 : UInt32) + (ctrl - mask <<< 3))
        ((17 : UInt32) + (mask + mask <<< 3)) 8
        (callerLocals :=
          ⟨[], [Value.i32 func0Base,
            .i32 ((17 : UInt32) + (mask + mask <<< 3)), .i32 l2, .i32 l3,
            .i32 (mask <<< 3), .i32 l5, .i64 v6], []⟩)
        (stack := []) (code := []) (arity := arity)
        (remainder := remainder)
        (controls := insOuterFrame afterTail :: controls)
        (calls := calls) (s := s) (E := E) (Φ := Φ)
      unfold CallContract callExpr at Hfree
      simp only [List.cons_append, List.nil_append] at Hfree
      iapply Hfree
      isplitl_exact Hruntime
      · iintro Hruntime
        isimp only [ResumeWP, resumeExpr, List.nil_append]
        wasm_twp_pures [twp_exitControl]
        simp only [insOuterFrame, List.take_zero, List.nil_append]
        iapply twp_ins_epilogue
        iframe

/-! ## The release of the pair buffer -/

set_option maxHeartbeats 2000000 in
/-- The release of the pair buffer that `sorted_entries` allocated.  The
entry count sits at frame offset 64 and the pointer at frame offset 68.
A count of zero leaves nothing to free.  WAT lines 425 to 438. -/
theorem twp_ins_free_pairs [WasmSmallStepGS hlc Universal.State]
    (cap bufPtr : UInt32)
    {l1 l2 l3 l4 l5 ctrl mask : UInt32} {v6 : UInt64}
    {afterTail : Program} {finalOutput : List UInt8} {arity : Nat}
    {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp} :
    iprop(RuntimeContext ∗ StackPointer func0Base ∗
      Streams [] finalOutput false ∗
      pointsTo_u32 0 (func0Base + 64) cap ∗
      pointsTo_u32 0 (func0Base + 68) bufPtr ∗
      pointsTo_u32 0 (func0Base + 24) ctrl ∗
      pointsTo_u32 0 (func0Base + 28) mask ∗
      TailDone finalOutput afterTail arity remainder controls calls
        s E Φ) ⊢
      WP (.running
          ⟨⟨[], [Value.i32 func0Base, .i32 l1, .i32 l2, .i32 l3, .i32 l4,
              .i32 l5, .i64 v6], []⟩,
            insFreePairs, arity, remainder,
            insFreePairsFrame :: insOuterFrame afterTail :: controls,
            calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hstreams, Hcap, Hptr, Hctrl, Hmask, Hcont⟩
  have h64 := offset_facts func0Base 64 64 rfl (by decide)
  have h68 := offset_facts func0Base 68 68 rfl (by decide)
  simp only [insFreePairs]
  wasm_twp_pures [twp_localGet]
  wasm_twp_rebind twp_load32 (address := func0Base) (offset := 64) cap
    h64.1 h64.2.1 h64.2.2.1 h64.2.2.2 with Hcap
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  by_cases hcap : cap = 0
  · iapply twp_eqz (result := 1) (by simp [hcap])
    iapply twp_brIf (by decide) (by rfl)
    simp only [insFreePairsFrame, List.take_zero, List.nil_append]
    iapply twp_ins_table_drop
    iframe
  · iapply twp_eqz (result := 0) (by simp [hcap])
    wasm_twp_pures [twp_brIfZero twp_localGet]
    wasm_twp_rebind twp_load32 (address := func0Base) (offset := 68)
      bufPtr h68.1 h68.2.1 h68.2.2.1 h68.2.2.2 with Hptr
    wasm_twp_pures [twp_localGet twp_const twp_shl]
      rewriting [show (3 : UInt32) % 32 = 3 by decide]
    wasm_twp_pures [twp_const]
    have Hfree := func57_noop_correct (hlc := hlc) bufPtr (cap <<< 3) 4
      (callerLocals :=
        ⟨[], [Value.i32 func0Base, .i32 cap, .i32 l2, .i32 l3, .i32 l4,
          .i32 l5, .i64 v6], []⟩)
      (stack := []) (code := []) (arity := arity)
      (remainder := remainder)
      (controls :=
        insFreePairsFrame :: insOuterFrame afterTail :: controls)
      (calls := calls) (s := s) (E := E) (Φ := Φ)
    unfold CallContract callExpr at Hfree
    simp only [List.cons_append, List.nil_append] at Hfree
    iapply Hfree
    isplitl_exact Hruntime
    · iintro Hruntime
      isimp only [ResumeWP, resumeExpr, List.nil_append]
      wasm_twp_pures [twp_exitControl]
      simp only [insFreePairsFrame, List.take_zero, List.nil_append]
      iapply twp_ins_table_drop
      iframe

/-! ## The reject exit -/

set_option maxHeartbeats 2000000 in
/-- The release of the input byte vector on the reject exit.  Both arms
leave the outer block, so the arm ends with a branch of its own.  WAT
lines 351 to 358. -/
theorem twp_ins_reject_tail [WasmSmallStepGS hlc Universal.State]
    {l1 l2 l3 l4 l5 : UInt32} {v6 : UInt64} {afterTail : Program}
    {finalOutput : List UInt8} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp} :
    iprop(RuntimeContext ∗ StackPointer func0Base ∗
      Streams [] finalOutput false ∗
      TailDone finalOutput afterTail arity remainder controls calls
        s E Φ) ⊢
      WP (.running
          ⟨⟨[], [Value.i32 func0Base, .i32 l1, .i32 l2, .i32 l3, .i32 l4,
              .i32 l5, .i64 v6], []⟩,
            insRejectTail, arity, remainder,
            insBlock2Frame :: insOuterFrame afterTail :: controls,
            calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hstreams, Hcont⟩
  simp only [insRejectTail]
  by_cases hcapacity : l2 = 0
  · wasm_twp_pures [twp_localGet]
    iapply twp_eqz (result := 1) (by simp [hcapacity])
    iapply twp_brIf (by decide) (by rfl)
    simp only [insOuterFrame, List.take_zero, List.nil_append]
    iapply twp_ins_epilogue
    iframe
  · wasm_twp_pures [twp_localGet]
    iapply twp_eqz (result := 0) (by simp [hcapacity])
    wasm_twp_pures [twp_brIfZero twp_localGet twp_localGet twp_const]
    have Hfree := func57_noop_correct (hlc := hlc) l1 l2 1
      (callerLocals :=
        ⟨[], [Value.i32 func0Base, .i32 l1, .i32 l2, .i32 l3, .i32 l4,
          .i32 l5, .i64 v6], []⟩)
      (stack := []) (code := [.br 1]) (arity := arity)
      (remainder := remainder)
      (controls := insBlock2Frame :: insOuterFrame afterTail :: controls)
      (calls := calls) (s := s) (E := E) (Φ := Φ)
    unfold CallContract callExpr at Hfree
    simp only [List.cons_append, List.nil_append] at Hfree
    iapply Hfree
    isplitl_exact Hruntime
    · iintro Hruntime
      isimp only [ResumeWP, resumeExpr, List.nil_append]
      iapply twp_br (by rfl)
      simp only [insOuterFrame, List.take_zero, List.nil_append]
      iapply twp_ins_epilogue
      iframe

set_option maxHeartbeats 2000000 in
/-- The reject exit.  It drops the decoded error string and releases the
input byte vector, and it writes nothing.  Both frees read registers
only, so the exit needs no frame cell.  WAT lines 341 to 358. -/
theorem twp_ins_reject [WasmSmallStepGS hlc Universal.State]
    {l1 l2 l3 l4 l5 : UInt32} {v6 : UInt64} {afterTail : Program}
    {finalOutput : List UInt8} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp} :
    iprop(RuntimeContext ∗ StackPointer func0Base ∗
      Streams [] finalOutput false ∗
      TailDone finalOutput afterTail arity remainder controls calls
        s E Φ) ⊢
      WP (.running
          ⟨⟨[], [Value.i32 func0Base, .i32 l1, .i32 l2, .i32 l3, .i32 l4,
              .i32 l5, .i64 v6], []⟩,
            insReject, arity, remainder,
            insBlock2Frame :: insOuterFrame afterTail :: controls,
            calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hstreams, Hcont⟩
  simp only [insAfter3_shape]
  wasm_twp_pures [twp_block]
  simp only [List.drop_zero]
  rw [insDropErrorFrame_literal]
  simp only [insDropError]
  wasm_twp_pures [twp_localGet twp_const]
  by_cases hshort : l4.toInt32 < (1 : UInt32).toInt32
  · iapply twp_ltS (result := 1) (by rw [if_pos hshort])
    iapply twp_brIf (by decide) (by rfl)
    simp only [insDropErrorFrame, List.take_zero, List.nil_append]
    iapply twp_ins_reject_tail
    iframe
  · iapply twp_ltS (result := 0) (by rw [if_neg hshort])
    wasm_twp_pures [twp_brIfZero twp_localGet twp_localGet twp_const]
    have Hfree := func57_noop_correct (hlc := hlc) l3 l4 1
      (callerLocals :=
        ⟨[], [Value.i32 func0Base, .i32 l1, .i32 l2, .i32 l3, .i32 l4,
          .i32 l5, .i64 v6], []⟩)
      (stack := []) (code := []) (arity := arity)
      (remainder := remainder)
      (controls :=
        insDropErrorFrame :: insBlock2Frame ::
          insOuterFrame afterTail :: controls)
      (calls := calls) (s := s) (E := E) (Φ := Φ)
    unfold CallContract callExpr at Hfree
    simp only [List.cons_append, List.nil_append] at Hfree
    iapply Hfree
    isplitl_exact Hruntime
    · iintro Hruntime
      isimp only [ResumeWP, resumeExpr, List.nil_append]
      wasm_twp_pures [twp_exitControl]
      simp only [insDropErrorFrame, List.take_zero, List.nil_append]
      iapply twp_ins_reject_tail
      iframe
/-! ## The reply -/

set_option maxHeartbeats 2000000 in
/-- The reply.  The store puts the answer word back at frame offset 56,
so the record at offsets 56 to 76 holds the `Option<u32>` and then the
header of the pair buffer.  `call 8` writes the borsh form of both to
the output stream.  The block after it frees the pair buffer and the
table drop ends the tail.  WAT lines 418 to 463. -/
theorem twp_ins_reply [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (allocationId : Nat) (capacity pairPtr : UInt32)
    (o : Option UInt32) (pairs : List (UInt32 × UInt32))
    (oldWord answer : UInt64) (below : List UInt8)
    (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory) (output : List UInt8)
    {l1 l2 l3 l4 l5 ctrl mask : UInt32} {afterTail : Program}
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hpairs : pairs.length ≤ 2 ^ 27) :
    iprop(RuntimeContext ∗ StackPointer func0Base ∗
      StackBelow func0Base replyDepth below ∗
      pointsTo_u64 0 (func0Base + 56) oldWord ∗
      (pointsTo_u64 0 (func0Base + 56) answer -∗
        HashMap.Table.optionU32At 0 (func0Base + 56) o) ∗
      Slices.ByteSlice 0 (func0Base + 64)
        (WordCodec.u32le.serialize
          [capacity, pairPtr, UInt32.ofNat pairs.length]) ∗
      PairVecAt heapId allocationId capacity.toNat pairPtr pairs ∗
      pointsTo_u32 0 (func0Base + 24) ctrl ∗
      pointsTo_u32 0 (func0Base + 28) mask ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams [] output false ∗
      TailDone (output ++ Borsh.option Borsh.u32 o ++
          HashMap.serializeEntries WordCodec.u32le WordCodec.u32le pairs)
        afterTail arity remainder controls calls s E Φ ∗
      (ExportOOM -∗ Φ (.trapped (.host OOM.trapMessage)))) ⊢
      WP (.running
          ⟨⟨[], [Value.i32 func0Base, .i32 l1, .i32 l2, .i32 l3, .i32 l4,
              .i32 l5, .i64 answer], []⟩,
            insAfterSort, arity, remainder,
            insOuterFrame afterTail :: controls, calls⟩ :
            Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hbelow, Hcell, Hwand, Hheader, Hpairbuf, Hctrl,
    Hmask, Hbump, Hstreams, Hcont, Hoom⟩
  have h56 := offset_facts64 func0Base 56 56 rfl (by decide)
  ihave ⟨Hbytes, %hbound⟩ :=
    PairVecAt_bytes heapId allocationId capacity.toNat pairPtr pairs $$
    Hpairbuf
  simp only [insAfterSort, insReply, List.cons_append, List.nil_append]
  wasm_twp_pures [twp_localGet twp_localGet]
  wasm_twp_rebind Wasm.SmallStep.twp_store64 (address := func0Base)
    (offset := 56) oldWord h56.1 h56.2.1 h56.2.2.1 h56.2.2.2.1
    h56.2.2.2.2.1 h56.2.2.2.2.2.1 h56.2.2.2.2.2.2.1 h56.2.2.2.2.2.2.2
    with Hcell
  ihave Hoption := Hwand $$ Hcell
  ihave Hheader : Slices.ByteSlice 0 (func0Base + 56 + 8)
      (WordCodec.u32le.serialize
        [capacity, pairPtr, UInt32.ofNat pairs.length]) $$ [Hheader]
  · irw_exact [show func0Base + 56 + 8 = func0Base + 64 by decide]
      with Hheader
  wasm_twp_pures [twp_localGet twp_const twp_add]
    rewriting [show (56 : UInt32) + func0Base = func0Base + 56 by decide]
  have Hwrite := func5_correct (hlc := hlc) func0Base (func0Base + 56)
    capacity pairPtr o pairs below heapId storedCursor frontier history
    [] output false
    (callerLocals :=
      ⟨[], [Value.i32 func0Base, .i32 l1, .i32 l2, .i32 l3, .i32 l4,
        .i32 l5, .i64 answer], []⟩)
    (stack := []) (code := .block 0 0 insFreePairs :: insTableDrop)
    (arity := arity) (remainder := remainder)
    (controls := insOuterFrame afterTail :: controls)
    (calls := calls) (s := s) (E := E) (Φ := Φ)
  unfold CallContract callExpr at Hwrite
  simp only [List.cons_append, List.nil_append] at Hwrite
  iapply Hwrite
  isplitl_exacts [Hruntime Hsp Hbelow Hoption Hheader Hbytes Hbump
    Hstreams]
  isplitl_pureexact ⟨hpairs, by decide, by decide, hbound⟩
  isplit
  · iintro %below' %storedCursor' %frontier' %history' Hruntime Hsp
      Hbelow Hoption Hheader Hbytes Hbump Hstreams
    isimp only [ResumeWP, resumeExpr, List.nil_append]
    ihave Hheader : Slices.ByteSlice 0 (func0Base + 64)
        (WordCodec.u32le.serialize
          [capacity, pairPtr, UInt32.ofNat pairs.length]) $$ [Hheader]
    · irw_exact [show func0Base + 56 + 8 = func0Base + 64 by decide]
        with Hheader
    ihave ⟨Hcap, Hptr, _Hcount⟩ :=
      ByteSlice_three_words (func0Base + 64) capacity pairPtr
        (UInt32.ofNat pairs.length) $$ Hheader
    isimp only [show func0Base + 64 + 4 = func0Base + 68 by decide]
      at Hptr
    wasm_twp_pures [twp_block]
    simp only [List.drop_zero]
    rw [insFreePairsFrame_literal]
    iapply twp_ins_free_pairs capacity pairPtr
    iframe
  · iintro %remaining Hstreams
    iapply Hoom
    isimp only [ExportOOM]
    iexists remaining, output
    iexact Hstreams
/-! ## The sort -/

/-- The sort call in cons form.  A `rw` with this equation keeps the
suffix folded, which a `simp only` over `List.cons_append` does not. -/
private theorem insAfterCopyBack_cons :
    insAfterCopyBack =
      .localGet 0 :: .const 64 :: .add :: .localGet 0 :: .const 24 ::
        .add :: .call 7 :: insAfterSort := rfl

set_option maxHeartbeats 2000000 in
/-- The sort of the entries of the new map.  `sorted_entries`, absolute
`func 7`, takes the twelve dead bytes at frame offset 64 as its output
header and the map value at frame offset 24.  It answers with the header
of a fresh pair buffer in key order.  WAT lines 411 to 463. -/
theorem twp_ins_sort [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (k0 k1 : UInt64) (t : HashMap.Table UInt32 UInt32)
    (o : Option UInt32) (oldWord answer : UInt64)
    (outBefore below : List UInt8)
    (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory) (output : List UInt8)
    {l1 l2 l3 l4 l5 : UInt32} {afterTail : Program}
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hout : outBefore.length = 12)
    (hwf : HashMap.Table.WF (HashMap.SipHash.hashU32 k0 k1) t)
    (hbuckets : t.buckets ≤ 2 ^ 27) :
    iprop(RuntimeContext ∗ StackPointer func0Base ∗
      StackBelow func0Base insertCalleeDepth below ∗
      Slices.ByteSlice 0 (func0Base + 64) outBefore ∗
      HashMap.Table.HashMapAt 0 (func0Base + 24) k0 k1 t ∗
      pointsTo_u64 0 (func0Base + 56) oldWord ∗
      (pointsTo_u64 0 (func0Base + 56) answer -∗
        HashMap.Table.optionU32At 0 (func0Base + 56) o) ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams [] output false ∗
      TailDone (output ++ Borsh.option Borsh.u32 o ++
          HashMap.serializeEntries WordCodec.u32le WordCodec.u32le
            (HashMap.sortByKey (HashMap.Table.toList t)))
        afterTail arity remainder controls calls s E Φ ∗
      (ExportOOM -∗ Φ (.trapped (.host OOM.trapMessage)))) ⊢
      WP (.running
          ⟨⟨[], [Value.i32 func0Base, .i32 l1, .i32 l2, .i32 l3, .i32 l4,
              .i32 l5, .i64 answer], []⟩,
            insAfterCopyBack, arity, remainder,
            insOuterFrame afterTail :: controls, calls⟩ :
            Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hbelow, Hout, Hmap, Hcell, Hwand, Hbump,
    Hstreams, Hcont, Hoom⟩
  have hitems : t.items ≤ 2 ^ 27 :=
    Nat.le_trans (items_le_buckets hwf) hbuckets
  have hdepth := sortedEntriesDepth_le_insert hitems
  have hpairs :
      (HashMap.sortByKey (HashMap.Table.toList t)).length ≤ 2 ^ 27 :=
    Nat.le_trans (sorted_length_le_buckets hwf) hbuckets
  have hcount : UInt32.ofNat t.items =
      UInt32.ofNat
        (HashMap.sortByKey (HashMap.Table.toList t)).length := by
    rw [hwf.items_eq,
      (HashMap.sortByKey_perm (HashMap.Table.toList t)).length_eq]
  ihave ⟨%low, Hbelow, Hrestore⟩ :=
    StackBelow_reshape func0Base insertCalleeDepth
      (sortedEntriesDepth t.items) below hdepth $$ Hbelow
  rw [insAfterCopyBack_cons]
  wasm_twp_pures [twp_localGet twp_const twp_add twp_localGet twp_const
    twp_add]
    rewriting [show (64 : UInt32) + func0Base = func0Base + 64 by decide,
      show (24 : UInt32) + func0Base = func0Base + 24 by decide]
  have Hsort := func4_correct (hlc := hlc) func0Base (func0Base + 64)
    (func0Base + 24) k0 k1 t outBefore low heapId storedCursor frontier
    history [] output false
    (callerLocals :=
      ⟨[], [Value.i32 func0Base, .i32 l1, .i32 l2, .i32 l3, .i32 l4,
        .i32 l5, .i64 answer], []⟩)
    (stack := []) (code := insAfterSort) (arity := arity)
    (remainder := remainder)
    (controls := insOuterFrame afterTail :: controls)
    (calls := calls) (s := s) (E := E) (Φ := Φ)
  unfold CallContract callExpr at Hsort
  simp only [List.append_nil] at Hsort
  iapply Hsort
  isplitl_exacts [Hruntime Hsp Hbelow Hout Hmap Hbump Hstreams]
  isplitl_pureexact ⟨hout, hwf, hbuckets, by decide, by decide,
    by have : insertCalleeDepth ≤ func0Base.toNat := by decide
       omega⟩
  isplit
  · iintro %capacity %pairPtr %allocationId %below' %storedCursor'
      %frontier' %history' Hruntime Hsp Hbelow Hheader Hmap Hbump Hbuf
      Hstreams %hcapfact
    isimp only [ResumeWP, resumeExpr, List.nil_append]
    ihave ⟨%b, Hbelow⟩ := Hrestore $$ %below' Hbelow
    ihave ⟨%low2, Hbelow, _Hrestore2⟩ :=
      StackBelow_reshape func0Base insertCalleeDepth replyDepth b
        replyDepth_le_insert $$ Hbelow
    isimp only [HashMap.Table.HashMapAt] at Hmap
    icases Hmap with ⟨Htable, Hk0, Hk1⟩
    ihave Hwords := TableAt_header_words (func0Base + 24) t $$ Htable
    icases Hwords with ⟨%ctrl, %mask, Hctrl, Hmask, Hitems⟩
    isimp only [show func0Base + 24 + 4 = func0Base + 28 by decide]
      at Hmask
    iclear Hk0 Hk1 Hitems
    isimp only [hcount] at Hheader
    iapply twp_ins_reply heapId allocationId capacity pairPtr o
      (HashMap.sortByKey (HashMap.Table.toList t)) oldWord answer low2
      storedCursor' frontier' history' output hpairs
    iframe
  · iintro %remaining Hstreams
    iapply Hoom
    isimp only [ExportOOM]
    iexists remaining, output
    iexact Hstreams
/-! ## The copy back of the new map value -/

/-- The copy back in cons form. -/
private theorem insAfterShim_cons :
    insAfterShim =
      .localGet 0 :: .localGet 0 :: .load64 88 :: .store64 48 ::
        .localGet 0 :: .localGet 0 :: .load64 80 :: .store64 40 ::
        .localGet 0 :: .localGet 0 :: .load64 72 :: .store64 32 ::
        .localGet 0 :: .localGet 0 :: .load64 64 :: .store64 24 ::
        insAfterCopyBack := rfl

set_option maxHeartbeats 2000000 in
/-- The copy back of the new map value over the map slot.  The four
64-bit words move from the top down, so the source and the target never
overlap in the wrong order.  The words that stay at frame offset 64 are
the old header of the table, and their first twelve bytes become the
output slot of `sorted_entries`.  WAT lines 395 to 463. -/
theorem twp_ins_copy_back [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (k0 k1 : UInt64) (t : HashMap.Table UInt32 UInt32)
    (o : Option UInt32) (oldWord answer : UInt64)
    (mapBytes below : List UInt8)
    (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory) (output : List UInt8)
    {l1 l2 l3 l4 l5 : UInt32} {afterTail : Program}
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hmap : mapBytes.length = 32)
    (hwf : HashMap.Table.WF (HashMap.SipHash.hashU32 k0 k1) t)
    (hbuckets : t.buckets ≤ 2 ^ 27) :
    iprop(RuntimeContext ∗ StackPointer func0Base ∗
      StackBelow func0Base insertCalleeDepth below ∗
      Slices.ByteSlice 0 (func0Base + 24) mapBytes ∗
      HashMap.Table.HashMapAt 0 (func0Base + 64) k0 k1 t ∗
      pointsTo_u64 0 (func0Base + 56) oldWord ∗
      (pointsTo_u64 0 (func0Base + 56) answer -∗
        HashMap.Table.optionU32At 0 (func0Base + 56) o) ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams [] output false ∗
      TailDone (output ++ Borsh.option Borsh.u32 o ++
          HashMap.serializeEntries WordCodec.u32le WordCodec.u32le
            (HashMap.sortByKey (HashMap.Table.toList t)))
        afterTail arity remainder controls calls s E Φ ∗
      (ExportOOM -∗ Φ (.trapped (.host OOM.trapMessage)))) ⊢
      WP (.running
          ⟨⟨[], [Value.i32 func0Base, .i32 l1, .i32 l2, .i32 l3, .i32 l4,
              .i32 l5, .i64 answer], []⟩,
            insAfterShim, arity, remainder,
            insOuterFrame afterTail :: controls, calls⟩ :
            Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hbelow, Hdest, Hmap, Hcell, Hwand, Hbump,
    Hstreams, Hcont, Hoom⟩
  have h24 := offset_facts64 func0Base 24 24 rfl (by decide)
  have h32 := offset_facts64 func0Base 32 32 rfl (by decide)
  have h40 := offset_facts64 func0Base 40 40 rfl (by decide)
  have h48 := offset_facts64 func0Base 48 48 rfl (by decide)
  have h64 := offset_facts64 func0Base 64 64 rfl (by decide)
  have h72 := offset_facts64 func0Base 72 72 rfl (by decide)
  have h80 := offset_facts64 func0Base 80 80 rfl (by decide)
  have h88 := offset_facts64 func0Base 88 88 rfl (by decide)
  ihave ⟨%ctrl, %mask, %growthLeft, %items, Hs0, Hs1, Hs2, Hs3, Hback⟩ :=
    HashMapAt_move_words (func0Base + 64) (func0Base + 24) k0 k1 t $$
    Hmap
  isimp only [show func0Base + 64 + 8 = func0Base + 72 by decide] at Hs1
  isimp only [show func0Base + 64 + 16 = func0Base + 80 by decide] at Hs2
  isimp only [show func0Base + 64 + 24 = func0Base + 88 by decide] at Hs3
  ihave ⟨%d0, %d1, %d2, %d3, Hd0, Hd1, Hd2, Hd3⟩ :=
    ByteSlice_thirtyTwo_as_cells 0 (func0Base + 24) mapBytes hmap $$ Hdest
  isimp only [show func0Base + 24 + 8 = func0Base + 32 by decide] at Hd1
  isimp only [show func0Base + 24 + 16 = func0Base + 40 by decide] at Hd2
  isimp only [show func0Base + 24 + 24 = func0Base + 48 by decide] at Hd3
  rw [insAfterShim_cons]
  wasm_twp_block_move (func0Base, 88, k1, h88) (func0Base, 48, d3, h48)
    with Hs3 Hd3
  wasm_twp_block_move (func0Base, 80, k0, h80) (func0Base, 40, d2, h40)
    with Hs2 Hd2
  wasm_twp_block_move (func0Base, 72, wordPair growthLeft items, h72)
    (func0Base, 32, d1, h32) with Hs1 Hd1
  wasm_twp_block_move (func0Base, 64, wordPair ctrl mask, h64)
    (func0Base, 24, d0, h24) with Hs0 Hd0
  ihave Hd1 : pointsTo_u64 0 (func0Base + 24 + 8)
      (wordPair growthLeft items) $$ [Hd1]
  · irw_exact [show func0Base + 24 + 8 = func0Base + 32 by decide]
      with Hd1
  ihave Hd2 : pointsTo_u64 0 (func0Base + 24 + 16) k0 $$ [Hd2]
  · irw_exact [show func0Base + 24 + 16 = func0Base + 40 by decide]
      with Hd2
  ihave Hd3 : pointsTo_u64 0 (func0Base + 24 + 24) k1 $$ [Hd3]
  · irw_exact [show func0Base + 24 + 24 = func0Base + 48 by decide]
      with Hd3
  ihave Hmap := Hback $$ Hd0 Hd1 Hd2 Hd3
  ihave ⟨Hw0, Hw1⟩ :=
    (pointsTo_u32_pair_as_groupWord 0 (func0Base + 64) ctrl mask).mpr $$
    Hs0
  ihave ⟨Hw2, _Hw3⟩ :=
    (pointsTo_u32_pair_as_groupWord 0 (func0Base + 72) growthLeft
      items).mpr $$ Hs1
  ihave Hw2 : pointsTo_u32 0 (func0Base + 64 + 4 + 4) growthLeft $$
      [Hw2]
  · irw_exact [show func0Base + 64 + 4 + 4 = func0Base + 72 by decide]
      with Hw2
  ihave Hout :=
    ByteSlice_of_three_words (func0Base + 64) ctrl mask growthLeft
      (by decide) $$ [Hw0 Hw1 Hw2]
  · iframe Hw0 Hw1 Hw2
  iclear Hs2 Hs3
  iapply twp_ins_sort heapId k0 k1 t o oldWord answer
    (WordCodec.u32le.serialize [ctrl, mask, growthLeft]) below
    storedCursor frontier history output rfl hwf hbuckets
  iframe
/-! ## The insert shim -/

/-- The shim call in cons form. -/
private theorem insAfterCollect_cons :
    insAfterCollect =
      .localGet 0 :: .const 56 :: .add :: .localGet 0 :: .const 24 ::
        .add :: .localGet 3 :: .localGet 5 :: .call 6 :: .localGet 0 ::
        .load64 56 :: .localSet 6 :: insAfterShim := rfl

/-- The item count of the decoded table is at most the entry count of
the list that built it, because `ofEntries` drops a repeated key. -/
private theorem items_ofEntries_le (k0 k1 : UInt64)
    (entries : HashMap.Map UInt32 UInt32)
    (hn : entries.length ≤ 2 ^ 30) :
    (HashMap.Table.ofEntries (HashMap.SipHash.hashU32 k0 k1)
      entries).items ≤ entries.length := by
  obtain ⟨hwf, _hclean, _hb, hperm⟩ :=
    HashMap.Table.wf_ofEntries_u32 k0 k1 entries hn
  rw [hwf.items_eq, hperm.length_eq]
  exact HashMap.length_ofEntries_le entries

set_option maxHeartbeats 4000000 in
/-- The insert shim, absolute `func 6`, and the load of its answer word.
The shim takes a 40-byte output slot at frame offset 56 and the map
value at frame offset 24.  It writes the displaced value as an
`Option<u32>` at offsets 56 to 64 and the new map at offsets 64 to 96,
and it gives the old map slot back as raw bytes.  The driver saves the
answer word in local 6.  WAT lines 383 to 463. -/
theorem twp_ins_shim [WasmSmallStepGS hlc Universal.State]
    (hfunc3 : Func3Spec (hlc := hlc))
    (heapId : GName) (k0 k1 : UInt64) (key value : UInt32)
    (entries : HashMap.Map UInt32 UInt32) (outBefore below : List UInt8)
    (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory) (output : List UInt8)
    {l1 l2 l4 : UInt32} {v6 : UInt64} {afterTail : Program}
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hout : outBefore.length = 40)
    (hn : entries.length ≤ 2 ^ 30)
    (hlt : entries.length < maxTableCapacity) :
    iprop(RuntimeContext ∗ StackPointer func0Base ∗
      StackBelow func0Base insertCalleeDepth below ∗
      Slices.ByteSlice 0 (func0Base + 56) outBefore ∗
      HashMap.Table.MapAt 0 (func0Base + 24) k0 k1 entries ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams [] output false ∗
      TailDone (output ++ Borsh.option Borsh.u32
            (HashMap.Table.insert (HashMap.SipHash.hashU32 k0 k1)
              (HashMap.Table.ofEntries (HashMap.SipHash.hashU32 k0 k1)
                entries) key value).1 ++
          HashMap.serializeEntries WordCodec.u32le WordCodec.u32le
            (HashMap.sortByKey (HashMap.Table.toList
              (HashMap.Table.insert (HashMap.SipHash.hashU32 k0 k1)
                (HashMap.Table.ofEntries (HashMap.SipHash.hashU32 k0 k1)
                  entries) key value).2)))
        afterTail arity remainder controls calls s E Φ ∗
      (ExportOOM -∗ Φ (.trapped (.host OOM.trapMessage)))) ⊢
      WP (.running
          ⟨⟨[], [Value.i32 func0Base, .i32 l1, .i32 l2, .i32 key,
              .i32 l4, .i32 value, .i64 v6], []⟩,
            insAfterCollect, arity, remainder,
            insOuterFrame afterTail :: controls, calls⟩ :
            Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hbelow, Hout, Hmap, Hbump, Hstreams, Hcont,
    Hoom⟩
  obtain ⟨hwf, hclean, hb32, _hperm⟩ :=
    HashMap.Table.wf_ofEntries_u32 k0 k1 entries hn
  have hbuckets :
      (HashMap.Table.ofEntries (HashMap.SipHash.hashU32 k0 k1)
        entries).buckets ≤ 2 ^ 27 :=
    buckets_ofEntries_le (HashMap.SipHash.hashU32 k0 k1) entries hn
      (by rw [maxTableCapacity_eq] at hlt; omega)
  have hgrowth :
      (HashMap.Table.ofEntries (HashMap.SipHash.hashU32 k0 k1)
        entries).growthLeft < UInt32.size :=
    growthLeft_lt_of_wf hwf hclean hbuckets
  have hitems :
      (HashMap.Table.ofEntries (HashMap.SipHash.hashU32 k0 k1)
        entries).items < maxTableCapacity := by
    have h := items_ofEntries_le k0 k1 entries hn
    omega
  obtain ⟨hwf', hclean', _, _⟩ := hwf.insert hclean hb32 key value
  have hbuckets' :=
    buckets_insert_le hwf hclean hitems hbuckets key value
  have h56 := offset_facts64 func0Base 56 56 rfl (by decide)
  ihave ⟨%low, Hbelow, Hrestore⟩ :=
    StackBelow_reshape func0Base insertCalleeDepth insertWrapDepth below
      insertWrapDepth_le_insert $$ Hbelow
  isimp only [HashMap.Table.MapAt] at Hmap
  rw [insAfterCollect_cons]
  wasm_twp_pures [twp_localGet twp_const twp_add twp_localGet twp_const
    twp_add twp_localGet twp_localGet]
    rewriting [show (56 : UInt32) + func0Base = func0Base + 56 by decide,
      show (24 : UInt32) + func0Base = func0Base + 24 by decide]
  have Hshim := hfunc3 func0Base (func0Base + 56) (func0Base + 24) key
    value k0 k1
    (HashMap.Table.ofEntries (HashMap.SipHash.hashU32 k0 k1) entries)
    outBefore low heapId storedCursor frontier history [] output false
    (callerLocals :=
      ⟨[], [Value.i32 func0Base, .i32 l1, .i32 l2, .i32 key, .i32 l4,
        .i32 value, .i64 v6], []⟩)
    (stack := [])
    (code := .localGet 0 :: .load64 56 :: .localSet 6 :: insAfterShim)
    (arity := arity) (remainder := remainder)
    (controls := insOuterFrame afterTail :: controls)
    (calls := calls) (s := s) (E := E) (Φ := Φ)
  unfold CallContract callExpr at Hshim
  simp only [List.append_nil] at Hshim
  iapply Hshim
  isplitl_exacts [Hruntime Hsp Hbelow Hout Hmap Hbump Hstreams]
  isplitl_pureexact ⟨hout, hwf, hclean, hitems, hbuckets, hgrowth,
    by decide, by decide, by decide⟩
  isplit
  · iintro %mapBytes %below' %storedCursor' %frontier' %history'
      Hruntime Hsp Hbelow Hanswer Hnew Hold Hbump Hstreams %hmapBytes
    isimp only [ResumeWP, resumeExpr, List.nil_append]
    isimp only [show func0Base + 56 + 8 = func0Base + 64 by decide]
      at Hnew
    ihave ⟨%b, Hbelow⟩ := Hrestore $$ %below' Hbelow
    ihave ⟨%answer, Hcell, Hwand⟩ :=
      RemovePures.optionU32At_as_u64 0 (func0Base + 56)
        (HashMap.Table.insert (HashMap.SipHash.hashU32 k0 k1)
          (HashMap.Table.ofEntries (HashMap.SipHash.hashU32 k0 k1)
            entries) key value).1 $$ Hanswer
    wasm_twp_pures [twp_localGet]
    wasm_twp_rebind Wasm.SmallStep.twp_load64 (address := func0Base)
      (offset := 56) answer h56.1 h56.2.1 h56.2.2.1 h56.2.2.2.1
      h56.2.2.2.2.1 h56.2.2.2.2.2.1 h56.2.2.2.2.2.2.1 h56.2.2.2.2.2.2.2
      with Hcell
    wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceSub, List.set]
    iapply twp_ins_copy_back heapId k0 k1
      (HashMap.Table.insert (HashMap.SipHash.hashU32 k0 k1)
        (HashMap.Table.ofEntries (HashMap.SipHash.hashU32 k0 k1) entries)
        key value).2
      (HashMap.Table.insert (HashMap.SipHash.hashU32 k0 k1)
        (HashMap.Table.ofEntries (HashMap.SipHash.hashU32 k0 k1) entries)
        key value).1
      answer answer mapBytes b storedCursor' frontier' history' output
      hmapBytes hwf' hbuckets'
    iframe
  · iintro %remaining Hstreams
    iapply Hoom
    isimp only [ExportOOM]
    iexists remaining, output
    iexact Hstreams
/-! ## The collect call -/

/-- The collect call in cons form. -/
private theorem insCollectAndRest_cons :
    insCollectAndRest =
      .localGet 0 :: .const 24 :: .add :: .localGet 0 :: .const 8 ::
        .add :: .call 5 :: insAfterCollect := rfl

set_option maxHeartbeats 4000000 in
/-- The build of the hash table.  `collect_entries`, absolute `func 5`,
takes the pair buffer through the vector header at frame offset 8 and
builds the map value in the 32 bytes at frame offset 24, which are the
dead input header and the dead middle region.  The two seeds stay
existential, and
`Project.RustHashMap.InsertPures.insertOutput_of_accepts` names the
output that the rest of the tail writes.  WAT lines 376 to 463. -/
theorem twp_ins_collect [WasmSmallStepGS hlc Universal.State]
    (hfunc2 : Func2Spec (hlc := hlc)) (hfunc3 : Func3Spec (hlc := hlc))
    (heapId : GName) (cap bufPtr len : UInt32) (input : List UInt8)
    (payload spare mapBefore outBefore keysBefore below : List UInt8)
    (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory) (output : List UInt8)
    {l1 l2 l4 : UInt32} {v6 : UInt64} {afterTail : Program}
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (haccept : InsertDecodeAccepts input)
    (hn : (acceptedInsertEntries input).length ≤ 2 ^ 30)
    (hlt : (acceptedInsertEntries input).length < maxTableCapacity)
    (hmapBefore : mapBefore.length = 32)
    (hslot : outBefore.length = 40)
    (hkeys : keysBefore.length = randomStateSize)
    (hpayload : payload =
      entryCodec.serialize (acceptedInsertEntries input))
    (hentries : (acceptedInsertEntries input).length = len.toNat)
    (hcap : len.toNat ≤ cap.toNat)
    (hspare : spare.length = 8 * (cap.toNat - len.toNat)) :
    iprop(RuntimeContext ∗ StackPointer func0Base ∗
      StackBelow func0Base insertCalleeDepth below ∗
      Slices.ByteSlice 0 (func0Base + 24) mapBefore ∗
      pointsTo_u32 0 (func0Base + 8) cap ∗
      pointsTo_u32 0 (func0Base + 12) bufPtr ∗
      pointsTo_u32 0 (func0Base + 16) len ∗
      Slices.ByteSlice 0 bufPtr (payload ++ spare) ∗
      Slices.ByteSlice 0 randomStateCell keysBefore ∗
      Slices.ByteSlice 0 (func0Base + 56) outBefore ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams [] output false ∗
      TailDone (output ++ Project.RustHashMap.Spec.insertOutput input)
        afterTail arity remainder controls calls s E Φ ∗
      (ExportOOM -∗ Φ (.trapped (.host OOM.trapMessage)))) ⊢
      WP (.running
          ⟨⟨[], [Value.i32 func0Base, .i32 l1, .i32 l2,
              .i32 (leadingKey input), .i32 l4,
              .i32 (leadingValue input), .i64 v6], []⟩,
            insCollectAndRest, arity, remainder,
            insOuterFrame afterTail :: controls, calls⟩ :
            Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hbelow, Hmap, Hcap, Hptr, Hlen, Hbuf, Hkeys,
    Hout, Hbump, Hstreams, Hcont, Hoom⟩
  ihave ⟨%low, Hbelow, Hrestore⟩ :=
    StackBelow_reshape func0Base insertCalleeDepth collectDepth below
      collectDepth_le_insert $$ Hbelow
  ihave Hptr : pointsTo_u32 0 (func0Base + 8 + 4) bufPtr $$ [Hptr]
  · irw_exact [show func0Base + 8 + 4 = func0Base + 12 by decide]
      with Hptr
  ihave Hlen : pointsTo_u32 0 (func0Base + 8 + 8) len $$ [Hlen]
  · irw_exact [show func0Base + 8 + 8 = func0Base + 16 by decide]
      with Hlen
  rw [insCollectAndRest_cons]
  wasm_twp_pures [twp_localGet twp_const twp_add twp_localGet twp_const
    twp_add]
    rewriting [show (24 : UInt32) + func0Base = func0Base + 24 by decide,
      show (8 : UInt32) + func0Base = func0Base + 8 by decide]
  have Hcollect := hfunc2 func0Base (func0Base + 24) (func0Base + 8) cap
    bufPtr len heapId (acceptedInsertEntries input) payload spare
    mapBefore keysBefore low storedCursor frontier history [] output
    false
    (callerLocals :=
      ⟨[], [Value.i32 func0Base, .i32 l1, .i32 l2,
        .i32 (leadingKey input), .i32 l4, .i32 (leadingValue input),
        .i64 v6], []⟩)
    (stack := []) (code := insAfterCollect) (arity := arity)
    (remainder := remainder)
    (controls := insOuterFrame afterTail :: controls)
    (calls := calls) (s := s) (E := E) (Φ := Φ)
  unfold CallContract callExpr at Hcollect
  simp only [List.append_nil] at Hcollect
  iapply Hcollect
  isplitl_exacts [Hruntime Hsp Hbelow Hmap Hcap Hptr Hlen Hbuf Hkeys
    Hbump Hstreams]
  isplitl_pureexact ⟨hmapBefore, hkeys, hpayload, hentries, hcap, hspare,
    by decide, by decide, by decide⟩
  isplit
  · iintro %k0 %k1 %below' %keysAfter %storedCursor' %frontier' %history'
      Hruntime Hsp Hbelow Hmapv Hcap Hptr Hlen Hkeys Hbump Hstreams
      %hfacts
    isimp only [ResumeWP, resumeExpr, List.nil_append]
    ihave ⟨%b, Hbelow⟩ := Hrestore $$ %below' Hbelow
    have hshape :
        output ++ Project.RustHashMap.Spec.insertOutput input =
          output ++ Borsh.option Borsh.u32
              (HashMap.Table.insert (HashMap.SipHash.hashU32 k0 k1)
                (HashMap.Table.ofEntries
                  (HashMap.SipHash.hashU32 k0 k1)
                  (acceptedInsertEntries input)) (leadingKey input)
                (leadingValue input)).1 ++
            HashMap.serializeEntries WordCodec.u32le WordCodec.u32le
              (HashMap.sortByKey (HashMap.Table.toList
                (HashMap.Table.insert (HashMap.SipHash.hashU32 k0 k1)
                  (HashMap.Table.ofEntries
                    (HashMap.SipHash.hashU32 k0 k1)
                    (acceptedInsertEntries input)) (leadingKey input)
                  (leadingValue input)).2)) := by
      rw [insertOutput_of_accepts input k0 k1 haccept hn,
        List.append_assoc]
    isimp only [hshape] at Hcont
    iclear Hcap Hptr Hlen Hkeys
    iapply twp_ins_shim hfunc3 heapId k0 k1 (leadingKey input)
      (leadingValue input) (acceptedInsertEntries input) outBefore b
      storedCursor' frontier' history' output hslot hn hlt
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
so neither arm reads the buffer.  WAT lines 367 to 375. -/
theorem twp_ins_free_input [WasmSmallStepGS hlc Universal.State]
    (hfunc2 : Func2Spec (hlc := hlc)) (hfunc3 : Func3Spec (hlc := hlc))
    (heapId : GName) (cap bufPtr len : UInt32) (input : List UInt8)
    (payload spare mapBefore outBefore keysBefore below : List UInt8)
    (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory) (output : List UInt8)
    {l1 l2 l4 : UInt32} {v6 : UInt64} {afterTail : Program}
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (haccept : InsertDecodeAccepts input)
    (hn : (acceptedInsertEntries input).length ≤ 2 ^ 30)
    (hlt : (acceptedInsertEntries input).length < maxTableCapacity)
    (hmapBefore : mapBefore.length = 32)
    (hslot : outBefore.length = 40)
    (hkeys : keysBefore.length = randomStateSize)
    (hpayload : payload =
      entryCodec.serialize (acceptedInsertEntries input))
    (hentries : (acceptedInsertEntries input).length = len.toNat)
    (hcap : len.toNat ≤ cap.toNat)
    (hspare : spare.length = 8 * (cap.toNat - len.toNat)) :
    iprop(RuntimeContext ∗ StackPointer func0Base ∗
      StackBelow func0Base insertCalleeDepth below ∗
      Slices.ByteSlice 0 (func0Base + 24) mapBefore ∗
      pointsTo_u32 0 (func0Base + 8) cap ∗
      pointsTo_u32 0 (func0Base + 12) bufPtr ∗
      pointsTo_u32 0 (func0Base + 16) len ∗
      Slices.ByteSlice 0 bufPtr (payload ++ spare) ∗
      Slices.ByteSlice 0 randomStateCell keysBefore ∗
      Slices.ByteSlice 0 (func0Base + 56) outBefore ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams [] output false ∗
      TailDone (output ++ Project.RustHashMap.Spec.insertOutput input)
        afterTail arity remainder controls calls s E Φ ∗
      (ExportOOM -∗ Φ (.trapped (.host OOM.trapMessage)))) ⊢
      WP (.running
          ⟨⟨[], [Value.i32 func0Base, .i32 l1, .i32 l2,
              .i32 (leadingKey input), .i32 l4,
              .i32 (leadingValue input), .i64 v6], []⟩,
            insFreeInput, arity, remainder,
            insFreeInputFrame :: insOuterFrame afterTail :: controls,
            calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hbelow, Hmap, Hcap, Hptr, Hlen, Hbuf, Hkeys,
    Hout, Hbump, Hstreams, Hcont, Hoom⟩
  simp only [insFreeInput]
  by_cases hcapacity : l2 = 0
  · wasm_twp_pures [twp_localGet]
    iapply twp_eqz (result := 1) (by simp [hcapacity])
    iapply twp_brIf (by decide) (by rfl)
    simp only [insFreeInputFrame, List.take_zero, List.nil_append]
    iapply twp_ins_collect hfunc2 hfunc3 heapId cap bufPtr len input
      payload spare mapBefore outBefore keysBefore below storedCursor
      frontier history output haccept hn hlt hmapBefore hslot hkeys
      hpayload hentries hcap hspare
    iframe
  · wasm_twp_pures [twp_localGet]
    iapply twp_eqz (result := 0) (by simp [hcapacity])
    wasm_twp_pures [twp_brIfZero twp_localGet twp_localGet twp_const]
    have Hfree := func57_noop_correct (hlc := hlc) l1 l2 1
      (callerLocals :=
        ⟨[], [Value.i32 func0Base, .i32 l1, .i32 l2,
          .i32 (leadingKey input), .i32 l4, .i32 (leadingValue input),
          .i64 v6], []⟩)
      (stack := []) (code := []) (arity := arity)
      (remainder := remainder)
      (controls :=
        insFreeInputFrame :: insOuterFrame afterTail :: controls)
      (calls := calls) (s := s) (E := E) (Φ := Φ)
    unfold CallContract callExpr at Hfree
    simp only [List.cons_append, List.nil_append] at Hfree
    iapply Hfree
    isplitl_exact Hruntime
    · iintro Hruntime
      isimp only [ResumeWP, resumeExpr, List.nil_append]
      wasm_twp_pures [twp_exitControl]
      simp only [insFreeInputFrame, List.take_zero, List.nil_append]
      iapply twp_ins_collect hfunc2 hfunc3 heapId cap bufPtr len input
        payload spare mapBefore outBefore keysBefore below storedCursor
        frontier history output haccept hn hlt hmapBefore hslot hkeys
        hpayload hentries hcap hspare
      iframe
/-! ## The entries vector header -/

/-- The success tail in cons form. -/
private theorem insSuccessTail_cons :
    insSuccessTail =
      .localGet 0 :: .localGet 0 :: .load32 348 :: .store32 16 ::
        .localGet 0 :: .localGet 6 :: .store64 8 ::
        .block 0 0 insFreeInput :: insCollectAndRest := rfl

set_option maxHeartbeats 2000000 in
/-- The entries vector header for the collect call.  The pair count sits
at frame offset 348 and goes to offset 16, and the capacity and the
pointer travel as one 64-bit word to offsets 8 and 12.  WAT lines 360 to
463. -/
theorem twp_ins_entries_header [WasmSmallStepGS hlc Universal.State]
    (hfunc2 : Func2Spec (hlc := hlc)) (hfunc3 : Func3Spec (hlc := hlc))
    (heapId : GName) (cap bufPtr len old16 : UInt32) (oldPair : UInt64)
    (input : List UInt8)
    (payload spare mapBefore outBefore keysBefore below : List UInt8)
    (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory) (output : List UInt8)
    {l1 l2 l4 : UInt32} {afterTail : Program}
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (haccept : InsertDecodeAccepts input)
    (hn : (acceptedInsertEntries input).length ≤ 2 ^ 30)
    (hlt : (acceptedInsertEntries input).length < maxTableCapacity)
    (hmapBefore : mapBefore.length = 32)
    (hslot : outBefore.length = 40)
    (hkeys : keysBefore.length = randomStateSize)
    (hpayload : payload =
      entryCodec.serialize (acceptedInsertEntries input))
    (hentries : (acceptedInsertEntries input).length = len.toNat)
    (hcap : len.toNat ≤ cap.toNat)
    (hspare : spare.length = 8 * (cap.toNat - len.toNat)) :
    iprop(RuntimeContext ∗ StackPointer func0Base ∗
      StackBelow func0Base insertCalleeDepth below ∗
      Slices.ByteSlice 0 (func0Base + 24) mapBefore ∗
      pointsTo_u64 0 (func0Base + 8) oldPair ∗
      pointsTo_u32 0 (func0Base + 16) old16 ∗
      pointsTo_u32 0 (func0Base + 348) len ∗
      Slices.ByteSlice 0 bufPtr (payload ++ spare) ∗
      Slices.ByteSlice 0 randomStateCell keysBefore ∗
      Slices.ByteSlice 0 (func0Base + 56) outBefore ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams [] output false ∗
      TailDone (output ++ Project.RustHashMap.Spec.insertOutput input)
        afterTail arity remainder controls calls s E Φ ∗
      (ExportOOM -∗ Φ (.trapped (.host OOM.trapMessage)))) ⊢
      WP (.running
          ⟨⟨[], [Value.i32 func0Base, .i32 l1, .i32 l2,
              .i32 (leadingKey input), .i32 l4,
              .i32 (leadingValue input), .i64 (wordPair cap bufPtr)],
            []⟩,
            insSuccessTail, arity, remainder,
            insOuterFrame afterTail :: controls, calls⟩ :
            Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hbelow, Hmap, Hpair, H16, Hcount, Hbuf, Hkeys,
    Hout, Hbump, Hstreams, Hcont, Hoom⟩
  have h8 := offset_facts64 func0Base 8 8 rfl (by decide)
  have h16 := offset_facts func0Base 16 16 rfl (by decide)
  have h348 := offset_facts func0Base 348 348 rfl (by decide)
  rw [insSuccessTail_cons]
  wasm_twp_pures [twp_localGet twp_localGet]
  wasm_twp_rebind twp_load32 (address := func0Base) (offset := 348) len
    h348.1 h348.2.1 h348.2.2.1 h348.2.2.2 with Hcount
  wasm_twp_rebind twp_store32 (address := func0Base) (offset := 16) old16
    h16.1 h16.2.1 h16.2.2.1 h16.2.2.2 with H16
  wasm_twp_pures [twp_localGet twp_localGet]
  wasm_twp_rebind Wasm.SmallStep.twp_store64 (address := func0Base)
    (offset := 8) oldPair h8.1 h8.2.1 h8.2.2.1 h8.2.2.2.1
    h8.2.2.2.2.1 h8.2.2.2.2.2.1 h8.2.2.2.2.2.2.1 h8.2.2.2.2.2.2.2
    with Hpair
  ihave ⟨Hcapw, Hptrw⟩ :=
    (pointsTo_u32_pair_as_groupWord 0 (func0Base + 8) cap bufPtr).mpr $$
    Hpair
  ihave Hptrw : pointsTo_u32 0 (func0Base + 12) bufPtr $$ [Hptrw]
  · irw_exact [show func0Base + 12 = func0Base + 8 + 4 by decide]
      with Hptrw
  wasm_twp_pures [twp_block]
  simp only [List.drop_zero]
  rw [insFreeInputFrame_literal]
  iclear Hcount
  iapply twp_ins_free_input hfunc2 hfunc3 heapId cap bufPtr len input
    payload spare mapBefore outBefore keysBefore below storedCursor
    frontier history output haccept hn hlt hmapBefore hslot hkeys
    hpayload hentries hcap hspare
  iframe
/-! ## The "not all bytes read" arm -/

set_option maxHeartbeats 2000000 in
/-- The arm that the trailing-bytes test fails.  It builds the
`io::Error` with kind 12 and the 18 bytes "Not all bytes read" at
address 1049107, reads the two error words out of the slot at frame
offset 320, and frees the decoded pair buffer when its capacity is not
zero.  Both paths join the reject exit, and the arm writes nothing.  WAT
lines 313 to 339. -/
theorem twp_ins_not_all_read [WasmSmallStepGS hlc Universal.State]
    (hfunc52 : Func52Spec (hlc := hlc))
    (heapId : GName) (pair : UInt64)
    (errSlot dataBytes below : List UInt8)
    (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory) (output : List UInt8)
    {l1 l2 l3 l4 l5 : UInt32} {afterTail : Program}
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (herrSlot : errSlot.length = 16)
    (hdata : dataBytes.length = dataSegmentSize) :
    iprop(RuntimeContext ∗ StackPointer func0Base ∗
      StackBelow func0Base insertCalleeDepth below ∗
      Slices.ByteSlice 0 (func0Base + 320) errSlot ∗
      Slices.ByteSlice 0 entryStackTop dataBytes ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams [] output false ∗
      TailDone output afterTail arity remainder controls calls s E Φ ∗
      (ExportOOM -∗ Φ (.trapped (.host OOM.trapMessage)))) ⊢
      WP (.running
          ⟨⟨[], [Value.i32 func0Base, .i32 l1, .i32 l2, .i32 l3, .i32 l4,
              .i32 l5, .i64 pair], []⟩,
            insNotAllRead, arity, remainder,
            insBlock3Frame :: insBlock2Frame ::
              insOuterFrame afterTail :: controls, calls⟩ :
            Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hbelow, Hslot, Hdata, Hbump, Hstreams, Hcont,
    Hoom⟩
  have h320 := offset_facts func0Base 320 320 rfl (by decide)
  have h324 := offset_facts func0Base 324 324 rfl (by decide)
  ihave ⟨Hmsg, Hjoin⟩ :=
    dataSegment_cut dataBytes hdata 531 18 1049107 (by decide)
      (by decide) $$ Hdata
  ihave ⟨%low, Hbelow, Hrestore⟩ :=
    StackBelow_reshape func0Base insertCalleeDepth errorNewDepth below
      errorNewDepth_le_insert $$ Hbelow
  simp only [insNotAllRead]
  wasm_twp_pures [twp_localGet twp_const twp_add twp_const twp_const
    twp_const]
    rewriting
      [show (320 : UInt32) + func0Base = func0Base + 320 by decide]
  have Herr := hfunc52 func0Base (func0Base + 320) 12 1049107 18 heapId
    errSlot low ((dataBytes.drop (531 : UInt32).toNat).take
      (18 : UInt32).toNat) storedCursor frontier history [] output false
    (callerLocals :=
      ⟨[], [Value.i32 func0Base, .i32 l1, .i32 l2, .i32 l3, .i32 l4,
        .i32 l5, .i64 pair], []⟩)
    (stack := [])
    (code :=
      [.localGet 0, .load32 324, .localSet 3, .localGet 0, .load32 320,
        .localSet 4, .localGet 6, .wrapI64, .localTee 5, .eqz, .br_if 0,
        .localGet 6, .constI64 32, .shrUI64, .wrapI64, .localGet 5,
        .const 3, .shl, .const 4, .call 60])
    (arity := arity) (remainder := remainder)
    (controls :=
      insBlock3Frame :: insBlock2Frame :: insOuterFrame afterTail ::
        controls)
    (calls := calls) (s := s) (E := E) (Φ := Φ)
  unfold CallContract callExpr at Herr
  simp only [List.cons_append, List.nil_append] at Herr
  iapply Herr
  isplitl_exacts [Hruntime Hsp Hbelow Hslot Hmsg Hbump Hstreams]
  isplitl_pureexact
    ⟨herrSlot, by decide, by decide, by decide, by decide,
      by simp [hdata, dataSegmentSize]⟩
  isplit
  · iintro %word0 %word1 %word2 %word3 %below' %storedCursor' %frontier'
      %history' Hruntime Hsp Hbelow Hslot Hmsg Hbump Hstreams %hword0
    isimp only [ResumeWP, resumeExpr, List.nil_append]
    ihave Hdata := Hjoin $$ Hmsg
    ihave ⟨%b, Hbelow⟩ := Hrestore $$ %below' Hbelow
    ihave ⟨Hw0, Hw1, _Hw2, _Hw3⟩ :=
      ByteSlice_four_words (func0Base + 320) word0 word1 word2 word3 $$
      Hslot
    isimp only [show func0Base + 320 + 4 = func0Base + 324 by decide]
      at Hw1
    wasm_twp_pures [twp_localGet]
    wasm_twp_rebind twp_load32 (address := func0Base) (offset := 324)
      word1 h324.1 h324.2.1 h324.2.2.1 h324.2.2.2 with Hw1
    wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceSub, List.set]
    wasm_twp_pures [twp_localGet]
    wasm_twp_rebind twp_load32 (address := func0Base) (offset := 320)
      word0 h320.1 h320.2.1 h320.2.2.1 h320.2.2.2 with Hw0
    wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceSub, List.set]
    wasm_twp_pures [twp_localGet twp_wrapI64]
    wasm_twp_localTee [List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub, List.set]
    by_cases hcount :
        UInt32.ofNat (pair.toNat % 2 ^ 32) = 0
    · iapply twp_eqz (result := 1) (by rw [if_pos hcount])
      iapply twp_brIf (by decide) (by rfl)
      simp only [insBlock3Frame, List.take_zero, List.nil_append]
      iapply twp_ins_reject
      iframe
    · iapply twp_eqz (result := 0) (by rw [if_neg hcount])
      wasm_twp_pures [twp_brIfZero twp_localGet twp_constI64 twp_shrUI64
        twp_wrapI64 twp_localGet twp_const twp_shl]
        rewriting [show (3 : UInt32) % 32 = 3 by decide]
      wasm_twp_pures [twp_const]
      have Hfree := func57_noop_correct (hlc := hlc)
        (UInt32.ofNat ((pair >>> (32 % 64 : UInt64)).toNat % 2 ^ 32))
        (UInt32.ofNat (pair.toNat % 2 ^ 32) <<< 3) 4
        (callerLocals :=
          ⟨[], [Value.i32 func0Base, .i32 l1, .i32 l2, .i32 word1,
            .i32 word0, .i32 (UInt32.ofNat (pair.toNat % 2 ^ 32)),
            .i64 pair], []⟩)
        (stack := []) (code := []) (arity := arity)
        (remainder := remainder)
        (controls :=
          insBlock3Frame :: insBlock2Frame ::
            insOuterFrame afterTail :: controls)
        (calls := calls) (s := s) (E := E) (Φ := Φ)
      unfold CallContract callExpr at Hfree
      simp only [List.cons_append, List.nil_append] at Hfree
      iapply Hfree
      isplitl_exact Hruntime
      · iintro Hruntime
        isimp only [ResumeWP, resumeExpr, List.nil_append]
        wasm_twp_pures [twp_exitControl]
        simp only [insBlock3Frame, List.take_zero, List.nil_append]
        iapply twp_ins_reject
        iframe
  · iintro %remaining Hstreams
    iapply Hoom
    isimp only [ExportOOM]
    iexists remaining, output
    iexact Hstreams
/-! ## The decoder answer -/

/-- The payload that the decoder leaves is the wire form of the entries
that the model reads.  The take drops nothing, because the header names
the whole rest of the map bytes. -/
private theorem insertPayload_serialize (input : List UInt8)
    (haccept : InsertDecodeAccepts input) :
    entryCodec.serialize (acceptedInsertEntries input)
      = ((insertMapBytes input).drop 4).take
          (8 * (headerWord (insertMapBytes input)).toNat) := by
  obtain ⟨_h8, _hdec, hexact⟩ := haccept
  unfold insertPairCount at hexact
  unfold entryCodec acceptedInsertEntries
  rw [HashMap.BorshBridge.serialize_wireEntries _ hexact.symm]
  rw [List.take_of_length_le]
  rw [List.length_drop]
  omega

/-- An accepted input holds at most `67108862` pairs.  The read phase
puts the input in a vector whose capacity is at most `536870912` bytes,
and twelve bytes of an accepted input are not pairs. -/
private theorem entries_le_max (input : List UInt8)
    (haccept : InsertDecodeAccepts input)
    (hfits : input.length ≤ 536870912) :
    (acceptedInsertEntries input).length ≤ 67108862 := by
  obtain ⟨h8, _hdec, hexact⟩ := haccept
  have hmap : (insertMapBytes input).length = input.length - 8 := by
    unfold insertMapBytes
    rw [List.length_drop]
  rw [acceptedInsertEntries_length]
  omega

/-- The decoder answer in cons form. -/
private theorem insAfterDecode_cons :
    insAfterDecode =
      .localGet 0 :: .load64 340 :: .localSet 6 :: .localGet 0 ::
        .load32 316 :: .eqz :: .br_if 1 :: insNotAllRead := rfl

set_option maxHeartbeats 4000000 in
/-- The pair load and the trailing-bytes test.  A count of zero at frame
offset 316 leaves the second block for the success tail; any other count
builds the "not all bytes read" error and joins the reject exit.  WAT
lines 306 to 339. -/
theorem twp_ins_after_decode [WasmSmallStepGS hlc Universal.State]
    (hfunc2 : Func2Spec (hlc := hlc)) (hfunc3 : Func3Spec (hlc := hlc))
    (hfunc52 : Func52Spec (hlc := hlc))
    (heapId : GName) (capacity buffer count remaining old16 : UInt32)
    (oldPair : UInt64) (v6 : UInt64) (input : List UInt8)
    (payload spare mapBefore outBefore errSlot keysBefore dataBytes
      below : List UInt8)
    (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory) (output : List UInt8)
    {l1 l2 : UInt32} {afterTail : Program}
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hok : remaining = 0 → InsertDecodeAccepts input)
    (herr : remaining ≠ 0 → ¬ InsertDecodeAccepts input)
    (hfits : input.length ≤ 536870912)
    (hcount : count = headerWord (insertMapBytes input))
    (hpayloadEq : payload =
      ((insertMapBytes input).drop 4).take (8 * count.toNat))
    (hcapBound : count.toNat ≤ capacity.toNat)
    (hspareLen : spare.length = 8 * (capacity.toNat - count.toNat))
    (hmapBefore : mapBefore.length = 32)
    (hslot : outBefore.length = 40)
    (herrSlot : errSlot.length = 16)
    (hkeys : keysBefore.length = randomStateSize)
    (hdata : dataBytes.length = dataSegmentSize) :
    iprop(RuntimeContext ∗ StackPointer func0Base ∗
      StackBelow func0Base insertCalleeDepth below ∗
      pointsTo_u32 0 (func0Base + 340) capacity ∗
      pointsTo_u32 0 (func0Base + 344) buffer ∗
      pointsTo_u32 0 (func0Base + 348) count ∗
      pointsTo_u32 0 (func0Base + 316) remaining ∗
      Slices.ByteSlice 0 (func0Base + 24) mapBefore ∗
      pointsTo_u64 0 (func0Base + 8) oldPair ∗
      pointsTo_u32 0 (func0Base + 16) old16 ∗
      Slices.ByteSlice 0 buffer (payload ++ spare) ∗
      Slices.ByteSlice 0 randomStateCell keysBefore ∗
      Slices.ByteSlice 0 (func0Base + 56) outBefore ∗
      Slices.ByteSlice 0 (func0Base + 320) errSlot ∗
      Slices.ByteSlice 0 entryStackTop dataBytes ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams [] output false ∗
      TailDone (output ++ Project.RustHashMap.Spec.insertOutput input)
        afterTail arity remainder controls calls s E Φ ∗
      (ExportOOM -∗ Φ (.trapped (.host OOM.trapMessage)))) ⊢
      WP (.running
          ⟨⟨[], [Value.i32 func0Base, .i32 l1, .i32 l2,
              .i32 (leadingKey input), .i32 okTag,
              .i32 (leadingValue input), .i64 v6], []⟩,
            insAfterDecode, arity, remainder,
            insBlock3Frame :: insBlock2Frame ::
              insOuterFrame afterTail :: controls, calls⟩ :
            Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hbelow, Hcapw, Hbufw, Hcountw, Hrem, Hmap,
    Hpair, H16, Hbuf, Hkeys, Hout, Herrslot, Hdata, Hbump, Hstreams,
    Hcont, Hoom⟩
  have h316 := offset_facts func0Base 316 316 rfl (by decide)
  have h340 := offset_facts64 func0Base 340 340 rfl (by decide)
  ihave Hbufw : pointsTo_u32 0 (func0Base + 340 + 4) buffer $$ [Hbufw]
  · irw_exact [show func0Base + 340 + 4 = func0Base + 344 by decide]
      with Hbufw
  ihave Hcell :=
    (pointsTo_u32_pair_as_groupWord 0 (func0Base + 340) capacity
      buffer).mp $$ [Hcapw Hbufw]
  · iframe Hcapw Hbufw
  rw [insAfterDecode_cons]
  wasm_twp_pures [twp_localGet]
  wasm_twp_rebind Wasm.SmallStep.twp_load64 (address := func0Base)
    (offset := 340) (wordPair capacity buffer) h340.1 h340.2.1
    h340.2.2.1 h340.2.2.2.1 h340.2.2.2.2.1 h340.2.2.2.2.2.1
    h340.2.2.2.2.2.2.1 h340.2.2.2.2.2.2.2 with Hcell
  wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_localGet]
  wasm_twp_rebind twp_load32 (address := func0Base) (offset := 316)
    remaining h316.1 h316.2.1 h316.2.2.1 h316.2.2.2 with Hrem
  by_cases hremaining : remaining = 0
  · iapply twp_eqz (result := 1) (by rw [if_pos hremaining])
    iapply twp_brIf (by decide) (by rfl)
    simp only [insBlock2Frame, List.take_zero, List.nil_append]
    have haccept := hok hremaining
    have hmax := entries_le_max input haccept hfits
    have hn : (acceptedInsertEntries input).length ≤ 2 ^ 30 := by
      have hpow : (2 : Nat) ^ 30 = 1073741824 := by norm_num
      omega
    have hlt :
        (acceptedInsertEntries input).length < maxTableCapacity := by
      rw [maxTableCapacity_eq]
      omega
    have hentries :
        (acceptedInsertEntries input).length = count.toNat := by
      rw [acceptedInsertEntries_length, hcount]
      rfl
    have hpayload :
        payload = entryCodec.serialize (acceptedInsertEntries input) := by
      rw [insertPayload_serialize input haccept, hpayloadEq, hcount]
    iclear Hrem Herrslot Hdata
    iapply twp_ins_entries_header hfunc2 hfunc3 heapId capacity buffer
      count old16 oldPair input payload spare mapBefore outBefore
      keysBefore below storedCursor frontier history output haccept hn
      hlt hmapBefore hslot hkeys hpayload hentries hcapBound hspareLen
    iframe
  · iapply twp_eqz (result := 0) (by rw [if_neg hremaining])
    wasm_twp_pures [twp_brIfZero]
    rw [insertOutput_of_not_accepts input (herr hremaining),
      List.append_nil]
    iclear Hcountw Hrem Hmap Hpair H16 Hbuf Hkeys Hout Hcell
    iapply twp_ins_not_all_read hfunc52 heapId
      (wordPair capacity buffer) errSlot dataBytes below storedCursor
      frontier history output herrSlot hdata
    iframe
/-! ## The decoder call -/

/-- The guard block and the decoder answer.  This is a plain
definition, so that a `simp only` over `List.cons_append` leaves it
folded. -/
private def insDecodeTail : Program :=
  .block 0 0 insOkGuard :: insAfterDecode

/-- The decoder call in cons form. -/
private theorem insAfter4_cons :
    insAfter4 =
      .localGet 0 :: .const 336 :: .add :: .localGet 0 :: .const 312 ::
        .add :: .call 4 :: insDecodeTail := rfl

set_option maxHeartbeats 4000000 in
/-- The call of the borsh decoder, absolute `func 4`, and the guard on
its tag word.  The decoder reads the map bytes from `ptr + 8`, which is
the input without the key and the value.  A tag that is not `okTag`
leaves through the reject exit.  WAT lines 287 to 339. -/
theorem twp_ins_decode_call [WasmSmallStepGS hlc Universal.State]
    (hfunc1 : Func1Spec (hlc := hlc)) (hfunc2 : Func2Spec (hlc := hlc))
    (hfunc3 : Func3Spec (hlc := hlc)) (hfunc52 : Func52Spec (hlc := hlc))
    (heapId : GName) (dataPtr dataLen old16 : UInt32) (oldPair v6 : UInt64)
    (input : List UInt8)
    (decOut mapBefore outBefore errSlot keysBefore dataBytes
      below : List UInt8)
    (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory) (output : List UInt8)
    {l1 l2 l4 : UInt32} {afterTail : Program}
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (h8 : 8 ≤ input.length)
    (hfits : input.length ≤ 536870912)
    (hlen : (insertMapBytes input).length = dataLen.toNat)
    (hdec : decOut.length = 16)
    (hmapBefore : mapBefore.length = 32)
    (hslot : outBefore.length = 40)
    (herrSlot : errSlot.length = 16)
    (hkeys : keysBefore.length = randomStateSize)
    (hdata : dataBytes.length = dataSegmentSize) :
    iprop(RuntimeContext ∗ StackPointer func0Base ∗
      StackBelow func0Base insertCalleeDepth below ∗
      Slices.ByteSlice 0 (func0Base + 336) decOut ∗
      pointsTo_u32 0 (func0Base + 312) dataPtr ∗
      pointsTo_u32 0 (func0Base + 316) dataLen ∗
      Slices.ByteSlice 0 dataPtr (insertMapBytes input) ∗
      Slices.ByteSlice 0 entryStackTop dataBytes ∗
      Slices.ByteSlice 0 (func0Base + 24) mapBefore ∗
      pointsTo_u64 0 (func0Base + 8) oldPair ∗
      pointsTo_u32 0 (func0Base + 16) old16 ∗
      Slices.ByteSlice 0 randomStateCell keysBefore ∗
      Slices.ByteSlice 0 (func0Base + 56) outBefore ∗
      Slices.ByteSlice 0 (func0Base + 320) errSlot ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams [] output false ∗
      TailDone (output ++ Project.RustHashMap.Spec.insertOutput input)
        afterTail arity remainder controls calls s E Φ ∗
      (ExportOOM -∗ Φ (.trapped (.host OOM.trapMessage)))) ⊢
      WP (.running
          ⟨⟨[], [Value.i32 func0Base, .i32 l1, .i32 l2,
              .i32 (leadingKey input), .i32 l4,
              .i32 (leadingValue input), .i64 v6], []⟩,
            insAfter4, arity, remainder,
            insBlock3Frame :: insBlock2Frame ::
              insOuterFrame afterTail :: controls, calls⟩ :
            Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hbelow, Hdec, Hptrw, Hlenw, Hbytes, Hdata,
    Hmap, Hpair, H16, Hkeys, Hout, Herrslot, Hbump, Hstreams, Hcont,
    Hoom⟩
  have h336 := offset_facts func0Base 336 336 rfl (by decide)
  ihave ⟨%low, Hbelow, Hrestore⟩ :=
    StackBelow_reshape func0Base insertCalleeDepth decoderDepth below
      decoderDepth_le_insert $$ Hbelow
  ihave Hlenw : pointsTo_u32 0 (func0Base + 312 + 4) dataLen $$ [Hlenw]
  · irw_exact [show func0Base + 312 + 4 = func0Base + 316 by decide]
      with Hlenw
  rw [insAfter4_cons]
  wasm_twp_pures [twp_localGet twp_const twp_add twp_localGet twp_const
    twp_add]
    rewriting
      [show (336 : UInt32) + func0Base = func0Base + 336 by decide,
        show (312 : UInt32) + func0Base = func0Base + 312 by decide]
  have Hdecode := hfunc1 func0Base (func0Base + 336) (func0Base + 312)
    dataPtr dataLen heapId (insertMapBytes input) decOut low dataBytes
    storedCursor frontier history [] output false
    (callerLocals :=
      ⟨[], [Value.i32 func0Base, .i32 l1, .i32 l2,
        .i32 (leadingKey input), .i32 l4, .i32 (leadingValue input),
        .i64 v6], []⟩)
    (stack := [])
    (code := insDecodeTail) (arity := arity)
    (remainder := remainder)
    (controls :=
      insBlock3Frame :: insBlock2Frame :: insOuterFrame afterTail ::
        controls)
    (calls := calls) (s := s) (E := E) (Φ := Φ)
  unfold CallContract callExpr at Hdecode
  simp only [List.cons_append, List.nil_append] at Hdecode
  iapply Hdecode
  isplitl_exacts [Hruntime Hsp Hbelow Hdec Hptrw Hlenw Hbytes Hdata
    Hbump Hstreams]
  isplitl_pureexact ⟨hdec, hlen, by decide, by decide, by decide, hdata⟩
  isplit
  · -- the accepting arm
    iintro %cap' %buffer %payload %spare' %below' %storedCursor'
      %frontier' %history' %haccept Hruntime Hsp Hbelow Hdec Hptrw
      Hlenw Hbytes Hdata Hbuf Hbump Hstreams %hfacts
    isimp only [ResumeWP, resumeExpr, List.nil_append]
    obtain ⟨hpayloadEq, hcapBound, hspareLen, _hzero⟩ := hfacts
    have hiff :=
      DriverTailProof.remaining_eq_zero_iff (insertMapBytes input)
        dataLen hlen haccept
    have hok :
        dataLen - 4 - 8 * headerWord (insertMapBytes input) = 0 →
          InsertDecodeAccepts input :=
      fun h => ⟨h8, haccept, (hiff.mp h).symm⟩
    have herr :
        dataLen - 4 - 8 * headerWord (insertMapBytes input) ≠ 0 →
          ¬ InsertDecodeAccepts input :=
      fun h hacc => h (hiff.mpr hacc.2.2.symm)
    ihave ⟨%b, Hbelow⟩ := Hrestore $$ %below' Hbelow
    ihave ⟨H336, H340, H344, H348⟩ :=
      ByteSlice_four_words (func0Base + 336) okTag cap' buffer
        (headerWord (insertMapBytes input)) $$ Hdec
    isimp only [show func0Base + 336 + 4 = func0Base + 340 by decide]
      at H340
    isimp only
      [show func0Base + 336 + 4 + 4 = func0Base + 344 by decide] at H344
    isimp only
      [show func0Base + 336 + 4 + 4 + 4 = func0Base + 348 by decide]
      at H348
    ihave Hlenw : pointsTo_u32 0 (func0Base + 316)
        (dataLen - 4 - 8 * headerWord (insertMapBytes input)) $$ [Hlenw]
    · irw_exact [show func0Base + 312 + 4 = func0Base + 316 by decide]
        with Hlenw
    simp only [insDecodeTail]
    wasm_twp_pures [twp_block]
    simp only [List.drop_zero]
    rw [insOkGuardFrame_literal]
    simp only [insOkGuard]
    wasm_twp_pures [twp_localGet]
    wasm_twp_rebind twp_load32 (address := func0Base) (offset := 336)
      okTag h336.1 h336.2.1 h336.2.2.1 h336.2.2.2 with H336
    wasm_twp_localTee [List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub, List.set]
    wasm_twp_pures [twp_const]
    iapply twp_eq (result := 1) (by simp [okTag])
    iapply twp_brIf (by decide) (by rfl)
    simp only [insOkGuardFrame, List.take_zero, List.nil_append]
    iclear H336 Hptrw Hbytes
    iapply twp_ins_after_decode hfunc2 hfunc3 hfunc52 heapId cap'
      buffer (headerWord (insertMapBytes input))
      (dataLen - 4 - 8 * headerWord (insertMapBytes input)) old16
      oldPair v6 input payload spare' mapBefore outBefore errSlot
      keysBefore dataBytes b storedCursor' frontier' history' output
      hok herr hfits rfl hpayloadEq hcapBound hspareLen hmapBefore
      hslot herrSlot hkeys hdata
    iframe
  · isplit
    · -- the rejecting arm
      iintro %word0 %word1 %word2 %word3 %ptr' %len' %below'
        %storedCursor' %frontier' %history' %hreject Hruntime Hsp Hbelow
        Hdec Hptrw Hlenw Hbytes Hdata Hbump Hstreams %hword0
      isimp only [ResumeWP, resumeExpr, List.nil_append]
      have hne : word0 ≠ (2147483649 : UInt32) := by
        simpa [okTag] using hword0
      have hno : ¬ InsertDecodeAccepts input := fun hacc => hreject hacc.2.1
      ihave ⟨H336, H340, _H344, _H348⟩ :=
        ByteSlice_four_words (func0Base + 336) word0 word1 word2 word3 $$
        Hdec
      isimp only [show func0Base + 336 + 4 = func0Base + 340 by decide]
        at H340
      simp only [insDecodeTail]
      wasm_twp_pures [twp_block]
      simp only [List.drop_zero]
      rw [insOkGuardFrame_literal]
      simp only [insOkGuard]
      wasm_twp_pures [twp_localGet]
      wasm_twp_rebind twp_load32 (address := func0Base) (offset := 336)
        word0 h336.1 h336.2.1 h336.2.2.1 h336.2.2.2 with H336
      wasm_twp_localTee [List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceSub, List.set]
      wasm_twp_pures [twp_const]
      iapply twp_eq (result := 0) (by simp [hne])
      wasm_twp_pures [twp_brIfZero twp_localGet]
      wasm_twp_rebind twp_load32 (address := func0Base) (offset := 340)
        word1 (by decide) (by decide) (by decide) (by decide) with H340
      wasm_twp_localSet [List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceSub, List.set]
      iapply twp_br (by rfl)
      simp only [insBlock3Frame, List.take_zero, List.nil_append]
      rw [insertOutput_of_not_accepts input hno, List.append_nil]
      iapply twp_ins_reject
      iframe
    · iintro %remaining Hstreams
      iapply Hoom
      isimp only [ExportOOM]
      iexists remaining, output
      iexact Hstreams
/-! ## The two error arms -/

/-- The part that the two error arms share after the error call and the
word saves.  The two arms differ in the depth of the live branch only:
the first arm leaves the third block with `br 3` and the second with
`br 1`. -/
private def insErrCore (d : Nat) : Program :=
  [.localGet 0, .load32 56, .localTee 4, .const 2147483649, .eq,
    .br_if 0, .localGet 0, .localGet 4, .store32 56,
    .localGet 0, .localGet 0, .load64 352, .store64 60,
    .localGet 0, .localGet 0, .load32 360, .store32 68,
    .localGet 0, .const 24, .add, .localGet 0, .const 56, .add,
    .call 52, .localGet 0, .load32 24, .localTee 4,
    .const 2147483649, .eq, .br_if 0, .localGet 0, .load32 28,
    .localSet 3, .br d]

theorem insErrBodyA_core : insErrBodyA = insErrCore 3 := rfl

theorem insErrRestB_core : insErrRestB = insErrCore 1 := rfl

set_option maxHeartbeats 4000000 in
/-- The shared part of the two error arms.  It restores the three saved
words, decodes the `io::Error` with absolute `func 52` into the slot at
frame offset 24, moves the message pointer into local 3, and leaves the
third block.  Both tag tests are dead, because `Func52Spec` and
`Func49Spec` each promise a first word that is not `okTag`.  WAT lines
197 to 230 and 252 to 285. -/
theorem twp_ins_error_core [WasmSmallStepGS hlc Universal.State]
    (hfunc49 : Func49Spec (hlc := hlc))
    (heapId : GName) (w0 w1 w2 w3 : UInt32)
    (convSlot dataBytes below : List UInt8)
    (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory) (output : List UInt8)
    (d : Nat) (ctrls : List ControlFrame)
    {l1 l2 l3 l4 l5 : UInt32} {v6 : UInt64} {afterTail : Program}
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hword0 : w0 ≠ okTag)
    (hconv : convSlot.length = 16)
    (hdata : dataBytes.length = dataSegmentSize)
    (htarget : branchTarget? arity d ctrls [] =
      some (insAfter3,
        insBlock2Frame :: insOuterFrame afterTail :: controls, [])) :
    iprop(RuntimeContext ∗ StackPointer func0Base ∗
      StackBelow func0Base insertCalleeDepth below ∗
      Slices.ByteSlice 0 (func0Base + 56)
        (WordCodec.u32le.serialize [w0, w1, w2, w3]) ∗
      pointsTo_u64 0 (func0Base + 352) (wordPair w1 w2) ∗
      pointsTo_u32 0 (func0Base + 360) w3 ∗
      Slices.ByteSlice 0 (func0Base + 24) convSlot ∗
      Slices.ByteSlice 0 entryStackTop dataBytes ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams [] output false ∗
      TailDone output afterTail arity remainder controls calls s E Φ ∗
      (ExportOOM -∗ Φ (.trapped (.host OOM.trapMessage)))) ⊢
      WP (.running
          ⟨⟨[], [Value.i32 func0Base, .i32 l1, .i32 l2, .i32 l3,
              .i32 l4, .i32 l5, .i64 v6], []⟩,
            insErrCore d, arity, remainder, ctrls, calls⟩ :
            Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hbelow, Hslot, Hsc0, Hsc1, Hconv, Hdata, Hbump,
    Hstreams, Hcont, Hoom⟩
  have hne : w0 ≠ (2147483649 : UInt32) := by simpa [okTag] using hword0
  have h24 := offset_facts func0Base 24 24 rfl (by decide)
  have h28 := offset_facts func0Base 28 28 rfl (by decide)
  have h56 := offset_facts func0Base 56 56 rfl (by decide)
  have h68 := offset_facts func0Base 68 68 rfl (by decide)
  have h360 := offset_facts func0Base 360 360 rfl (by decide)
  have h60 := offset_facts64 func0Base 60 60 rfl (by decide)
  have h352 := offset_facts64 func0Base 352 352 rfl (by decide)
  ihave ⟨H56, H60, H64, H68⟩ :=
    ByteSlice_four_words (func0Base + 56) w0 w1 w2 w3 $$ Hslot
  isimp only [show func0Base + 56 + 4 = func0Base + 60 by decide] at H60
  isimp only [show func0Base + 56 + 4 + 4 = func0Base + 64 by decide]
    at H64
  isimp only
    [show func0Base + 56 + 4 + 4 + 4 = func0Base + 68 by decide] at H68
  ihave H64 : pointsTo_u32 0 (func0Base + 60 + 4) w2 $$ [H64]
  · irw_exact [show func0Base + 60 + 4 = func0Base + 64 by decide]
      with H64
  ihave Hpair :=
    (pointsTo_u32_pair_as_groupWord 0 (func0Base + 60) w1 w2).mp $$
    [H60 H64]
  · iframe H60 H64
  simp only [insErrCore]
  wasm_twp_pures [twp_localGet]
  wasm_twp_rebind twp_load32 (address := func0Base) (offset := 56) w0
    h56.1 h56.2.1 h56.2.2.1 h56.2.2.2 with H56
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_const]
  iapply twp_eq (result := 0) (by simp [hne])
  wasm_twp_pures [twp_brIfZero twp_localGet twp_localGet]
  wasm_twp_rebind twp_store32 (address := func0Base) (offset := 56) w0
    h56.1 h56.2.1 h56.2.2.1 h56.2.2.2 with H56
  wasm_twp_block_move (func0Base, 352, wordPair w1 w2, h352)
    (func0Base, 60, wordPair w1 w2, h60) with Hsc0 Hpair
  wasm_twp_pures [twp_localGet twp_localGet]
  wasm_twp_rebind twp_load32 (address := func0Base) (offset := 360) w3
    h360.1 h360.2.1 h360.2.2.1 h360.2.2.2 with Hsc1
  wasm_twp_rebind twp_store32 (address := func0Base) (offset := 68) w3
    h68.1 h68.2.1 h68.2.2.1 h68.2.2.2 with H68
  ihave ⟨H60, H64⟩ :=
    (pointsTo_u32_pair_as_groupWord 0 (func0Base + 60) w1 w2).mpr $$
    Hpair
  ihave H60 : pointsTo_u32 0 (func0Base + 56 + 4) w1 $$ [H60]
  · irw_exact [show func0Base + 56 + 4 = func0Base + 60 by decide]
      with H60
  ihave H64 : pointsTo_u32 0 (func0Base + 56 + 4 + 4) w2 $$ [H64]
  · irw_exact [show func0Base + 56 + 4 + 4 = func0Base + 60 + 4
      by decide] with H64
  ihave H68 : pointsTo_u32 0 (func0Base + 56 + 4 + 4 + 4) w3 $$ [H68]
  · irw_exact [show func0Base + 56 + 4 + 4 + 4 = func0Base + 68
      by decide] with H68
  ihave Hslot :=
    ByteSlice_of_four_words (func0Base + 56) w0 w1 w2 w3 (by decide) $$
    [H56 H60 H64 H68]
  · iframe H56 H60 H64 H68
  ihave ⟨%low, Hbelow, Hrestore⟩ :=
    StackBelow_reshape func0Base insertCalleeDepth func49Depth below
      func49Depth_le_insert $$ Hbelow
  wasm_twp_pures [twp_localGet twp_const twp_add twp_localGet twp_const
    twp_add]
    rewriting [show (24 : UInt32) + func0Base = func0Base + 24 by decide,
      show (56 : UInt32) + func0Base = func0Base + 56 by decide]
  have Hturn := hfunc49 func0Base (func0Base + 24) (func0Base + 56) w0
    w1 w2 w3 heapId convSlot low dataBytes storedCursor frontier history
    [] output false
    (callerLocals :=
      ⟨[], [Value.i32 func0Base, .i32 l1, .i32 l2, .i32 l3, .i32 w0,
        .i32 l5, .i64 v6], []⟩)
    (stack := [])
    (code :=
      [.localGet 0, .load32 24, .localTee 4, .const 2147483649, .eq,
        .br_if 0, .localGet 0, .load32 28, .localSet 3, .br d])
    (arity := arity) (remainder := remainder) (controls := ctrls)
    (calls := calls) (s := s) (E := E) (Φ := Φ)
  unfold CallContract callExpr at Hturn
  simp only [List.cons_append, List.nil_append] at Hturn
  iapply Hturn
  isplitl_exacts [Hruntime Hsp Hbelow Hconv Hslot Hdata Hbump Hstreams]
  isplitl_pureexact
    ⟨hconv, by decide, by decide, by decide, hword0, hdata⟩
  isplit
  · iintro %u0 %u1 %u2 %u3 %errAfter %below' %storedCursor' %frontier'
      %history' Hruntime Hsp Hbelow Hconv Hslot Hdata Hbump Hstreams
      %hfacts
    isimp only [ResumeWP, resumeExpr, List.nil_append]
    obtain ⟨hu0, _hlen⟩ := hfacts
    have hune : u0 ≠ (2147483649 : UInt32) := by simpa [okTag] using hu0
    ihave ⟨H24, H28, _H32, _H36⟩ :=
      ByteSlice_four_words (func0Base + 24) u0 u1 u2 u3 $$ Hconv
    isimp only [show func0Base + 24 + 4 = func0Base + 28 by decide]
      at H28
    wasm_twp_pures [twp_localGet]
    wasm_twp_rebind twp_load32 (address := func0Base) (offset := 24) u0
      h24.1 h24.2.1 h24.2.2.1 h24.2.2.2 with H24
    wasm_twp_localTee [List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub, List.set]
    wasm_twp_pures [twp_const]
    iapply twp_eq (result := 0) (by simp [hune])
    wasm_twp_pures [twp_brIfZero twp_localGet]
    wasm_twp_rebind twp_load32 (address := func0Base) (offset := 28) u1
      h28.1 h28.2.1 h28.2.2.1 h28.2.2.2 with H28
    wasm_twp_localSet [List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub, List.set]
    iapply twp_br htarget
    iapply twp_ins_reject
    iframe
  · iintro %remaining Hstreams
    iapply Hoom
    isimp only [ExportOOM]
    iexists remaining, output
    iexact Hstreams
/-- The block of the first error arm and the code that follows it. -/
private def insErrTailBlockA : Program :=
  .block 0 0 insErrBodyA :: insErrTailA

/-- The clear of the value register and the shared part of the second
error arm. -/
private def insErrTailB : Program :=
  .const 0 :: .localSet 5 :: insErrRestB

/-- The first error arm in cons form. -/
private theorem insAfter6_cons :
    insAfter6 =
      .localGet 0 :: .const 56 :: .add :: .const 17 :: .const 1049080 ::
        .const 27 :: .call 55 :: .localGet 0 :: .localGet 0 ::
        .load64 60 :: .store64 352 :: .localGet 0 :: .localGet 0 ::
        .load32 68 :: .store32 360 :: insErrTailBlockA := rfl

/-- The second error arm in cons form. -/
private theorem insAfter5_cons :
    insAfter5 =
      .localGet 0 :: .const 56 :: .add :: .const 17 :: .const 1049080 ::
        .const 27 :: .call 55 :: .localGet 0 :: .localGet 0 ::
        .load64 60 :: .store64 352 :: .localGet 0 :: .localGet 0 ::
        .load32 68 :: .store32 360 :: insErrTailB := rfl

set_option maxHeartbeats 4000000 in
/-- The second error arm.  The input held a key but no value.  The arm
builds the "failed to fill whole buffer" error with absolute `func 55`,
saves the three words of the answer, clears the value register, and
joins the shared part.  WAT lines 235 to 285. -/
theorem twp_ins_err_arm_b [WasmSmallStepGS hlc Universal.State]
    (hfunc49 : Func49Spec (hlc := hlc)) (hfunc52 : Func52Spec (hlc := hlc))
    (heapId : GName) (sc0 : UInt64) (sc1 : UInt32)
    (errSlot convSlot dataBytes below : List UInt8)
    (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory) (output : List UInt8)
    {l1 l2 l3 l4 l5 : UInt32} {v6 : UInt64} {afterTail : Program}
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (herrSlot : errSlot.length = 16)
    (hconv : convSlot.length = 16)
    (hdata : dataBytes.length = dataSegmentSize) :
    iprop(RuntimeContext ∗ StackPointer func0Base ∗
      StackBelow func0Base insertCalleeDepth below ∗
      Slices.ByteSlice 0 (func0Base + 56) errSlot ∗
      pointsTo_u64 0 (func0Base + 352) sc0 ∗
      pointsTo_u32 0 (func0Base + 360) sc1 ∗
      Slices.ByteSlice 0 (func0Base + 24) convSlot ∗
      Slices.ByteSlice 0 entryStackTop dataBytes ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams [] output false ∗
      TailDone output afterTail arity remainder controls calls s E Φ ∗
      (ExportOOM -∗ Φ (.trapped (.host OOM.trapMessage)))) ⊢
      WP (.running
          ⟨⟨[], [Value.i32 func0Base, .i32 l1, .i32 l2, .i32 l3,
              .i32 l4, .i32 l5, .i64 v6], []⟩,
            insAfter5, arity, remainder,
            insBlock4Frame :: insBlock3Frame :: insBlock2Frame ::
              insOuterFrame afterTail :: controls, calls⟩ :
            Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hbelow, Hslot, Hsc0, Hsc1, Hconv, Hdata, Hbump,
    Hstreams, Hcont, Hoom⟩
  have h68 := offset_facts func0Base 68 68 rfl (by decide)
  have h360 := offset_facts func0Base 360 360 rfl (by decide)
  have h60 := offset_facts64 func0Base 60 60 rfl (by decide)
  have h352 := offset_facts64 func0Base 352 352 rfl (by decide)
  ihave ⟨Hmsg, Hjoin⟩ :=
    dataSegment_cut dataBytes hdata 504 27 1049080 (by decide)
      (by decide) $$ Hdata
  ihave ⟨%low, Hbelow, Hrestore⟩ :=
    StackBelow_reshape func0Base insertCalleeDepth errorNewDepth below
      errorNewDepth_le_insert $$ Hbelow
  rw [insAfter5_cons]
  wasm_twp_pures [twp_localGet twp_const twp_add twp_const twp_const
    twp_const]
    rewriting [show (56 : UInt32) + func0Base = func0Base + 56 by decide]
  have Herr := hfunc52 func0Base (func0Base + 56) 17 1049080 27 heapId
    errSlot low ((dataBytes.drop (504 : UInt32).toNat).take
      (27 : UInt32).toNat) storedCursor frontier history [] output false
    (callerLocals :=
      ⟨[], [Value.i32 func0Base, .i32 l1, .i32 l2, .i32 l3, .i32 l4,
        .i32 l5, .i64 v6], []⟩)
    (stack := [])
    (code :=
      .localGet 0 :: .localGet 0 :: .load64 60 :: .store64 352 ::
        .localGet 0 :: .localGet 0 :: .load32 68 :: .store32 360 ::
        insErrTailB)
    (arity := arity) (remainder := remainder)
    (controls :=
      insBlock4Frame :: insBlock3Frame :: insBlock2Frame ::
        insOuterFrame afterTail :: controls)
    (calls := calls) (s := s) (E := E) (Φ := Φ)
  unfold CallContract callExpr at Herr
  simp only [List.cons_append, List.nil_append] at Herr
  iapply Herr
  isplitl_exacts [Hruntime Hsp Hbelow Hslot Hmsg Hbump Hstreams]
  isplitl_pureexact
    ⟨herrSlot, by decide, by decide, by decide, by decide,
      by simp [hdata, dataSegmentSize]⟩
  isplit
  · iintro %w0 %w1 %w2 %w3 %below' %storedCursor' %frontier' %history'
      Hruntime Hsp Hbelow Hslot Hmsg Hbump Hstreams %hword0
    isimp only [ResumeWP, resumeExpr, List.nil_append]
    ihave Hdata := Hjoin $$ Hmsg
    ihave ⟨%b, Hbelow⟩ := Hrestore $$ %below' Hbelow
    ihave ⟨H56, H60, H64, H68⟩ :=
      ByteSlice_four_words (func0Base + 56) w0 w1 w2 w3 $$ Hslot
    isimp only [show func0Base + 56 + 4 = func0Base + 60 by decide]
      at H60
    isimp only [show func0Base + 56 + 4 + 4 = func0Base + 64 by decide]
      at H64
    isimp only
      [show func0Base + 56 + 4 + 4 + 4 = func0Base + 68 by decide] at H68
    ihave H64 : pointsTo_u32 0 (func0Base + 60 + 4) w2 $$ [H64]
    · irw_exact [show func0Base + 60 + 4 = func0Base + 64 by decide]
        with H64
    ihave Hpair :=
      (pointsTo_u32_pair_as_groupWord 0 (func0Base + 60) w1 w2).mp $$
      [H60 H64]
    · iframe H60 H64
    wasm_twp_block_move (func0Base, 60, wordPair w1 w2, h60)
      (func0Base, 352, sc0, h352) with Hpair Hsc0
    wasm_twp_pures [twp_localGet twp_localGet]
    wasm_twp_rebind twp_load32 (address := func0Base) (offset := 68) w3
      h68.1 h68.2.1 h68.2.2.1 h68.2.2.2 with H68
    wasm_twp_rebind twp_store32 (address := func0Base) (offset := 360)
      sc1 h360.1 h360.2.1 h360.2.2.1 h360.2.2.2 with Hsc1
    ihave ⟨H60, H64⟩ :=
      (pointsTo_u32_pair_as_groupWord 0 (func0Base + 60) w1 w2).mpr $$
      Hpair
    ihave H60 : pointsTo_u32 0 (func0Base + 56 + 4) w1 $$ [H60]
    · irw_exact [show func0Base + 56 + 4 = func0Base + 60 by decide]
        with H60
    ihave H64 : pointsTo_u32 0 (func0Base + 56 + 4 + 4) w2 $$ [H64]
    · irw_exact [show func0Base + 56 + 4 + 4 = func0Base + 60 + 4
        by decide] with H64
    ihave H68 : pointsTo_u32 0 (func0Base + 56 + 4 + 4 + 4) w3 $$ [H68]
    · irw_exact [show func0Base + 56 + 4 + 4 + 4 = func0Base + 68
        by decide] with H68
    ihave Hslot :=
      ByteSlice_of_four_words (func0Base + 56) w0 w1 w2 w3 (by decide) $$
      [H56 H60 H64 H68]
    · iframe H56 H60 H64 H68
    simp only [insErrTailB]
    wasm_twp_pures [twp_const]
    wasm_twp_localSet [List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub, List.set]
    rw [insErrRestB_core]
    iapply twp_ins_error_core hfunc49 heapId w0 w1 w2 w3 convSlot
      dataBytes b storedCursor' frontier' history' output 1
      (insBlock4Frame :: insBlock3Frame :: insBlock2Frame ::
        insOuterFrame afterTail :: controls)
      hword0 hconv hdata (by rfl)
    iframe
  · iintro %remaining Hstreams
    iapply Hoom
    isimp only [ExportOOM]
    iexists remaining, output
    iexact Hstreams
set_option maxHeartbeats 4000000 in
/-- The first error arm.  The input was shorter than four bytes, or it
was empty.  The arm builds the "failed to fill whole buffer" error with
absolute `func 55`, saves the three words of the answer, and joins the
shared part inside a block of its own.  WAT lines 181 to 233. -/
theorem twp_ins_err_arm_a [WasmSmallStepGS hlc Universal.State]
    (hfunc49 : Func49Spec (hlc := hlc)) (hfunc52 : Func52Spec (hlc := hlc))
    (heapId : GName) (sc0 : UInt64) (sc1 : UInt32)
    (errSlot convSlot dataBytes below : List UInt8)
    (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory) (output : List UInt8)
    {l1 l2 l3 l4 l5 : UInt32} {v6 : UInt64} {afterTail : Program}
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (herrSlot : errSlot.length = 16)
    (hconv : convSlot.length = 16)
    (hdata : dataBytes.length = dataSegmentSize) :
    iprop(RuntimeContext ∗ StackPointer func0Base ∗
      StackBelow func0Base insertCalleeDepth below ∗
      Slices.ByteSlice 0 (func0Base + 56) errSlot ∗
      pointsTo_u64 0 (func0Base + 352) sc0 ∗
      pointsTo_u32 0 (func0Base + 360) sc1 ∗
      Slices.ByteSlice 0 (func0Base + 24) convSlot ∗
      Slices.ByteSlice 0 entryStackTop dataBytes ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams [] output false ∗
      TailDone output afterTail arity remainder controls calls s E Φ ∗
      (ExportOOM -∗ Φ (.trapped (.host OOM.trapMessage)))) ⊢
      WP (.running
          ⟨⟨[], [Value.i32 func0Base, .i32 l1, .i32 l2, .i32 l3,
              .i32 l4, .i32 l5, .i64 v6], []⟩,
            insAfter6, arity, remainder,
            insBlock5Frame :: insBlock4Frame :: insBlock3Frame ::
              insBlock2Frame :: insOuterFrame afterTail :: controls,
            calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hbelow, Hslot, Hsc0, Hsc1, Hconv, Hdata, Hbump,
    Hstreams, Hcont, Hoom⟩
  have h68 := offset_facts func0Base 68 68 rfl (by decide)
  have h360 := offset_facts func0Base 360 360 rfl (by decide)
  have h60 := offset_facts64 func0Base 60 60 rfl (by decide)
  have h352 := offset_facts64 func0Base 352 352 rfl (by decide)
  ihave ⟨Hmsg, Hjoin⟩ :=
    dataSegment_cut dataBytes hdata 504 27 1049080 (by decide)
      (by decide) $$ Hdata
  ihave ⟨%low, Hbelow, Hrestore⟩ :=
    StackBelow_reshape func0Base insertCalleeDepth errorNewDepth below
      errorNewDepth_le_insert $$ Hbelow
  rw [insAfter6_cons]
  wasm_twp_pures [twp_localGet twp_const twp_add twp_const twp_const
    twp_const]
    rewriting [show (56 : UInt32) + func0Base = func0Base + 56 by decide]
  have Herr := hfunc52 func0Base (func0Base + 56) 17 1049080 27 heapId
    errSlot low ((dataBytes.drop (504 : UInt32).toNat).take
      (27 : UInt32).toNat) storedCursor frontier history [] output false
    (callerLocals :=
      ⟨[], [Value.i32 func0Base, .i32 l1, .i32 l2, .i32 l3, .i32 l4,
        .i32 l5, .i64 v6], []⟩)
    (stack := [])
    (code :=
      .localGet 0 :: .localGet 0 :: .load64 60 :: .store64 352 ::
        .localGet 0 :: .localGet 0 :: .load32 68 :: .store32 360 ::
        insErrTailBlockA)
    (arity := arity) (remainder := remainder)
    (controls :=
      insBlock5Frame :: insBlock4Frame :: insBlock3Frame ::
        insBlock2Frame :: insOuterFrame afterTail :: controls)
    (calls := calls) (s := s) (E := E) (Φ := Φ)
  unfold CallContract callExpr at Herr
  simp only [List.cons_append, List.nil_append] at Herr
  iapply Herr
  isplitl_exacts [Hruntime Hsp Hbelow Hslot Hmsg Hbump Hstreams]
  isplitl_pureexact
    ⟨herrSlot, by decide, by decide, by decide, by decide,
      by simp [hdata, dataSegmentSize]⟩
  isplit
  · iintro %w0 %w1 %w2 %w3 %below' %storedCursor' %frontier' %history'
      Hruntime Hsp Hbelow Hslot Hmsg Hbump Hstreams %hword0
    isimp only [ResumeWP, resumeExpr, List.nil_append]
    ihave Hdata := Hjoin $$ Hmsg
    ihave ⟨%b, Hbelow⟩ := Hrestore $$ %below' Hbelow
    ihave ⟨H56, H60, H64, H68⟩ :=
      ByteSlice_four_words (func0Base + 56) w0 w1 w2 w3 $$ Hslot
    isimp only [show func0Base + 56 + 4 = func0Base + 60 by decide]
      at H60
    isimp only [show func0Base + 56 + 4 + 4 = func0Base + 64 by decide]
      at H64
    isimp only
      [show func0Base + 56 + 4 + 4 + 4 = func0Base + 68 by decide] at H68
    ihave H64 : pointsTo_u32 0 (func0Base + 60 + 4) w2 $$ [H64]
    · irw_exact [show func0Base + 60 + 4 = func0Base + 64 by decide]
        with H64
    ihave Hpair :=
      (pointsTo_u32_pair_as_groupWord 0 (func0Base + 60) w1 w2).mp $$
      [H60 H64]
    · iframe H60 H64
    wasm_twp_block_move (func0Base, 60, wordPair w1 w2, h60)
      (func0Base, 352, sc0, h352) with Hpair Hsc0
    wasm_twp_pures [twp_localGet twp_localGet]
    wasm_twp_rebind twp_load32 (address := func0Base) (offset := 68) w3
      h68.1 h68.2.1 h68.2.2.1 h68.2.2.2 with H68
    wasm_twp_rebind twp_store32 (address := func0Base) (offset := 360)
      sc1 h360.1 h360.2.1 h360.2.2.1 h360.2.2.2 with Hsc1
    ihave ⟨H60, H64⟩ :=
      (pointsTo_u32_pair_as_groupWord 0 (func0Base + 60) w1 w2).mpr $$
      Hpair
    ihave H60 : pointsTo_u32 0 (func0Base + 56 + 4) w1 $$ [H60]
    · irw_exact [show func0Base + 56 + 4 = func0Base + 60 by decide]
        with H60
    ihave H64 : pointsTo_u32 0 (func0Base + 56 + 4 + 4) w2 $$ [H64]
    · irw_exact [show func0Base + 56 + 4 + 4 = func0Base + 60 + 4
        by decide] with H64
    ihave H68 : pointsTo_u32 0 (func0Base + 56 + 4 + 4 + 4) w3 $$ [H68]
    · irw_exact [show func0Base + 56 + 4 + 4 + 4 = func0Base + 68
        by decide] with H68
    ihave Hslot :=
      ByteSlice_of_four_words (func0Base + 56) w0 w1 w2 w3 (by decide) $$
      [H56 H60 H64 H68]
    · iframe H56 H60 H64 H68
    simp only [insErrTailBlockA]
    wasm_twp_pures [twp_block]
    simp only [List.drop_zero]
    rw [insErrFrameA_literal, insErrBodyA_core]
    iapply twp_ins_error_core hfunc49 heapId w0 w1 w2 w3 convSlot
      dataBytes b storedCursor' frontier' history' output 3
      (insErrFrameA :: insBlock5Frame :: insBlock4Frame ::
        insBlock3Frame :: insBlock2Frame :: insOuterFrame afterTail ::
        controls)
      hword0 hconv hdata (by rfl)
    iframe
  · iintro %remaining Hstreams
    iapply Hoom
    isimp only [ExportOOM]
    iexists remaining, output
    iexact Hstreams
/-! ## A byte slice reports its own address bound -/

/-- Read the no-wrap bound of a slice without giving the slice up. -/
private theorem ByteSlice_nowrap [WasmHeapGS Universal.State]
    (ptr : UInt32) (bs : List UInt8) :
    Slices.ByteSlice (α := Universal.State) 0 ptr bs ⊢
      iprop(Slices.ByteSlice 0 ptr bs ∗
        ⌜ptr.toNat + bs.length < UInt32.size⌝) := by
  iintro Hbytes
  isimp only [Slices.ByteSlice] at Hbytes
  icases Hbytes with ⟨%hbound, Hbytes⟩
  isplitl [Hbytes]
  · isimp only [Slices.ByteSlice]
    isplitl_pureexact hbound
    · iexact Hbytes
  · ipureexact hbound

/-! ## The empty arm -/

set_option maxHeartbeats 4000000 in
/-- The tail of the `map_insert` driver on the empty exit of its read
phase.  The arm writes an empty slice into the decode header, sets the
pointer register to one and the capacity register to zero, and falls
into the first error arm.  WAT lines 173 to 179. -/
theorem twp_insert_tail_empty [WasmSmallStepGS hlc Universal.State]
    (hfunc49 : Func49Spec (hlc := hlc))
    (hfunc52 : Func52Spec (hlc := hlc)) :
    InsertTailEmptySpec (hlc := hlc) := by
  unfold InsertTailEmptySpec
  intro heapId input output reserve head mid top extra dataBytes
    storedCursor frontier history afterTail arity remainder controls
    calls s E Φ hempty
  iintro ⟨HemptyArm, Hextra, Hdata, %hsizes, Hcont, Hoom⟩
  obtain ⟨hextra, hdata⟩ := hsizes
  subst hempty
  isimp only [EmptyArmIns] at HemptyArm
  icases HemptyArm with ⟨Hruntime, Hsp, Hreserve, Hhead, Hvec, Hmid,
    Hchunk, Htop, Hbump, Hstreams, %hshape⟩
  obtain ⟨hhead, hmid, htop⟩ := hshape
  isimp only [insertOutput_nil, List.append_nil] at Hcont
  have h312 := offset_facts64 func0Base 312 312 rfl (by decide)
  -- the region that the callees take
  ihave Hbelow : StackBelow func0Base insertCalleeDepth
      (extra ++ reserve) $$ [Hextra Hreserve]
  · iapply StackBelow_of_reserve_at func0Base insertCalleeDepth extra
      reserve (by rw [hextra]; rfl) (by decide) (by decide)
    iframe
  -- the decode header, the scratch words and the dead middle of the top
  icases (ByteSlice_split_at (func0Base + 312) 8 top
    (by simp [htop])).mp $$ Htop with ⟨T312, Hrest⟩
  isimp only [UInt32.reduceToNat] at T312
  isimp only [UInt32.reduceToNat,
    show func0Base + 312 + 8 = func0Base + 320 by decide] at Hrest
  icases (ByteSlice_split_at (func0Base + 320) 32 (top.drop 8)
    (by simp [htop])).mp $$ Hrest with ⟨_Tdead, Hrest⟩
  isimp only [UInt32.reduceToNat,
    show func0Base + 320 + 32 = func0Base + 352 by decide,
    show (top.drop 8).drop 32 = top.drop 40 from by
      simp [List.drop_drop]] at Hrest
  icases (ByteSlice_split_at (func0Base + 352) 8 (top.drop 40)
    (by simp [htop])).mp $$ Hrest with ⟨T352, Hrest⟩
  isimp only [UInt32.reduceToNat] at T352
  isimp only [UInt32.reduceToNat,
    show func0Base + 352 + 8 = func0Base + 360 by decide,
    show (top.drop 40).drop 8 = top.drop 48 from by
      simp [List.drop_drop]] at Hrest
  icases (ByteSlice_split_at (func0Base + 360) 4 (top.drop 48)
    (by simp [htop])).mp $$ Hrest with ⟨T360, _Tlast⟩
  isimp only [UInt32.reduceToNat] at T360
  ihave T312 := ByteSlice_as_word (func0Base + 312) (func0Base + 312)
    (top.take 8) rfl (by simp [htop]) $$ T312
  ihave T352 := ByteSlice_as_word (func0Base + 352) (func0Base + 352)
    ((top.drop 40).take 8) rfl (by simp [htop]) $$ T352
  ihave T360 :=
    (Slices.ByteSlice_four_as_word 0 (func0Base + 360)
      ((top.drop 48).take 4) (by simp [htop]) (by decide)).mp $$ T360
  -- the conversion slot: the dead vector header and four bytes of the
  -- dead middle region
  ihave ⟨Hheader, _Hstorage⟩ :=
    (VecU8_as_headerBytes_storage heapId (func0Base + 24) 0 1 []
      (by decide)).mp $$ Hvec
  icases (ByteSlice_split_at (func0Base + 36) 4 mid
    (by simp [hmid])).mp $$ Hmid with ⟨Hmid4, _Hmidrest⟩
  isimp only [UInt32.reduceToNat] at Hmid4
  ihave Hmid4 : Slices.ByteSlice 0 (func0Base + 24 + UInt32.ofNat 12)
      (mid.take 4) $$ [Hmid4]
  · irw_exact
      [show func0Base + 24 + UInt32.ofNat 12 = func0Base + 36 by decide]
      with Hmid4
  ihave Hconv :=
    ByteSlice_glue (func0Base + 24) (vecHeaderBytes 0 1 []) (mid.take 4)
      12 (by simp) $$ [Hheader Hmid4]
  · iframe Hheader Hmid4
  -- the error slot, cut from the zeroed chunk buffer
  icases (ByteSlice_split_at (func0Base + 56) 16
    (List.replicate 256 (0 : UInt8))
    (by rw [List.length_replicate]; decide)).mp $$ Hchunk
    with ⟨Herrslot, _Hchunkrest⟩
  isimp only [UInt32.reduceToNat] at Herrslot
  -- the empty arm itself
  rw [insControls6_eq]
  simp only [insAfter7, emptyArmLocals]
  wasm_twp_pures [twp_localGet twp_constI64]
  wasm_twp_rebind Wasm.SmallStep.twp_store64 (address := func0Base)
    (offset := 312) (HashMap.Table.groupWord (top.take 8)) h312.1
    h312.2.1 h312.2.2.1 h312.2.2.2.1 h312.2.2.2.2.1 h312.2.2.2.2.2.1
    h312.2.2.2.2.2.2.1 h312.2.2.2.2.2.2.2 with T312
  wasm_twp_pures [twp_const]
  wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_const]
  wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_exitControl]
  simp only [insBlock6Frame, List.take_zero, List.nil_append]
  iclear T312 Hhead
  iapply twp_ins_err_arm_a hfunc49 hfunc52 heapId
    (HashMap.Table.groupWord ((top.drop 40).take 8))
    (WordCodec.decodeU32 ((top.drop 48).take 4))
    ((List.replicate 256 (0 : UInt8)).take 16)
    (vecHeaderBytes 0 1 [] ++ mid.take 4) dataBytes (extra ++ reserve)
    storedCursor frontier history output
    (by simp only [List.length_take, List.length_replicate]; decide)
    (by simp [hmid]) hdata
  iframe
/-! ## The non-empty arm -/

/-- The stored length after the two cuts.  The two subtractions are
unsigned additions of `2 ^ 32 - 4` and `2 ^ 32 - 8`, and the second one
reads the original length again. -/
private theorem cut_length (n : Nat) (h8 : 8 ≤ n)
    (hn : n < UInt32.size) :
    ((4294967288 : UInt32) + UInt32.ofNat n).toNat = n - 8 := by
  have h1 : (4294967288 : UInt32).toNat = 4294967288 := rfl
  have h3 : (UInt32.ofNat n).toNat = n := UInt32.toNat_ofNat_of_lt' hn
  have hn' : n < 4294967296 := hn
  have hp : (2 : Nat) ^ 32 = 4294967296 := by norm_num
  rw [UInt32.toNat_add, h1, h3, hp]
  omega

set_option maxHeartbeats 8000000 in
/-- The tail of the `map_insert` driver on the non-empty exit of its
read phase.  The reload puts the three vector words in registers, the
two inline cuts take the key and the value off the front, and the rest
of the input goes to the borsh decoder.  WAT lines 123 to 171. -/
theorem twp_insert_tail_nonempty [WasmSmallStepGS hlc Universal.State]
    (hfunc2 : Func2Spec (hlc := hlc))
    (hfunc3 : Func3Spec (hlc := hlc)) :
    InsertTailNonEmptySpec (hlc := hlc) := by
  unfold InsertTailNonEmptySpec
  intro heapId capacity ptr byte length input output reserve head mid
    chunk top extra keysBefore dataBytes storedCursor frontier history
    afterTail arity remainder controls calls s E Φ _hnonempty
  iintro ⟨HafterRead, Hextra, Hkeys, Hdata, %hsizes, Hcont, Hoom⟩
  obtain ⟨hextra, hkeys, hdata, hinput⟩ := hsizes
  isimp only [AfterReadIns] at HafterRead
  icases HafterRead with ⟨Hruntime, Hsp, Hreserve, Hhead, Hvec, Hmid,
    Hchunk, Htop, Hbump, Hstreams, %hshape⟩
  obtain ⟨hhead, hmid, hchunk, htop, hpush⟩ := hshape
  have hlenNat : (UInt32.ofNat input.length).toNat = input.length :=
    UInt32.toNat_ofNat_of_lt' hinput
  have hcapLe := hpush.capacity_le
  have h8f := offset_facts64 func0Base 8 8 rfl (by decide)
  have h16f := offset_facts func0Base 16 16 rfl (by decide)
  have h24f := offset_facts func0Base 24 24 rfl (by decide)
  have h28f := offset_facts func0Base 28 28 rfl (by decide)
  have h32f := offset_facts func0Base 32 32 rfl (by decide)
  have h312f := offset_facts func0Base 312 312 rfl (by decide)
  have h316f := offset_facts func0Base 316 316 rfl (by decide)
  -- the region that the callees take
  ihave Hbelow : StackBelow func0Base insertCalleeDepth
      (extra ++ reserve) $$ [Hextra Hreserve]
  · iapply StackBelow_of_reserve_at func0Base insertCalleeDepth extra
      reserve (by rw [hextra]; rfl) (by decide) (by decide)
    iframe
  -- the entries header cells in the frame head
  icases (ByteSlice_split_at func0Base 8 head
    (by simp [hhead])).mp $$ Hhead with ⟨_Hhead0, Hrest⟩
  isimp only [UInt32.reduceToNat,
    show func0Base + 8 = func0Base + 8 by rfl] at Hrest
  icases (ByteSlice_split_at (func0Base + 8) 8 (head.drop 8)
    (by simp [hhead])).mp $$ Hrest with ⟨H8, Hrest⟩
  isimp only [UInt32.reduceToNat] at H8
  isimp only [UInt32.reduceToNat,
    show func0Base + 8 + 8 = func0Base + 16 by decide,
    show (head.drop 8).drop 8 = head.drop 16 from by
      simp [List.drop_drop]] at Hrest
  icases (ByteSlice_split_at (func0Base + 16) 4 (head.drop 16)
    (by simp [hhead])).mp $$ Hrest with ⟨H16, _Hrest⟩
  isimp only [UInt32.reduceToNat] at H16
  ihave H8 := ByteSlice_as_word (func0Base + 8) (func0Base + 8)
    ((head.drop 8).take 8) rfl (by simp [hhead]) $$ H8
  ihave H16 :=
    (Slices.ByteSlice_four_as_word 0 (func0Base + 16)
      ((head.drop 16).take 4) (by simp [hhead]) (by decide)).mp $$ H16
  -- the three vector words and the input bytes
  isimp only [VecU8, RawVecHeader] at Hvec
  icases Hvec with ⟨⟨Hcapw, Hptrw⟩, Hlenw, Hstorage⟩
  isimp only [show func0Base + 24 + 4 = func0Base + 28 by decide]
    at Hptrw
  isimp only [show func0Base + 24 + 8 = func0Base + 32 by decide]
    at Hlenw
  ihave ⟨Hstorage, %hfits⟩ :=
    VecStorage_fits heapId capacity ptr input $$ Hstorage
  ihave Hinput := VecStorage_bytes heapId capacity ptr input $$ Hstorage
  ihave ⟨Hinput, %hnowrap⟩ := ByteSlice_nowrap ptr input $$ Hinput
  -- the six regions of the frame top
  icases (ByteSlice_split_at (func0Base + 312) 4 top
    (by simp [htop])).mp $$ Htop with ⟨T312, Hrest⟩
  isimp only [UInt32.reduceToNat] at T312
  isimp only [UInt32.reduceToNat,
    show func0Base + 312 + 4 = func0Base + 316 by decide] at Hrest
  icases (ByteSlice_split_at (func0Base + 316) 4 (top.drop 4)
    (by simp [htop])).mp $$ Hrest with ⟨T316, Hrest⟩
  isimp only [UInt32.reduceToNat] at T316
  isimp only [UInt32.reduceToNat,
    show func0Base + 316 + 4 = func0Base + 320 by decide,
    show (top.drop 4).drop 4 = top.drop 8 from by
      simp [List.drop_drop]] at Hrest
  icases (ByteSlice_split_at (func0Base + 320) 16 (top.drop 8)
    (by simp [htop])).mp $$ Hrest with ⟨T320, Hrest⟩
  isimp only [UInt32.reduceToNat] at T320
  isimp only [UInt32.reduceToNat,
    show func0Base + 320 + 16 = func0Base + 336 by decide,
    show (top.drop 8).drop 16 = top.drop 24 from by
      simp [List.drop_drop]] at Hrest
  icases (ByteSlice_split_at (func0Base + 336) 16 (top.drop 24)
    (by simp [htop])).mp $$ Hrest with ⟨T336, Hrest⟩
  isimp only [UInt32.reduceToNat] at T336
  isimp only [UInt32.reduceToNat,
    show func0Base + 336 + 16 = func0Base + 352 by decide,
    show (top.drop 24).drop 16 = top.drop 40 from by
      simp [List.drop_drop]] at Hrest
  icases (ByteSlice_split_at (func0Base + 352) 8 (top.drop 40)
    (by simp [htop])).mp $$ Hrest with ⟨T352, Hrest⟩
  isimp only [UInt32.reduceToNat] at T352
  isimp only [UInt32.reduceToNat,
    show func0Base + 352 + 8 = func0Base + 360 by decide,
    show (top.drop 40).drop 8 = top.drop 48 from by
      simp [List.drop_drop]] at Hrest
  icases (ByteSlice_split_at (func0Base + 360) 4 (top.drop 48)
    (by simp [htop])).mp $$ Hrest with ⟨T360, _Tlast⟩
  isimp only [UInt32.reduceToNat] at T360
  ihave T312 :=
    (Slices.ByteSlice_four_as_word 0 (func0Base + 312) (top.take 4)
      (by simp [htop]) (by decide)).mp $$ T312
  ihave T316 :=
    (Slices.ByteSlice_four_as_word 0 (func0Base + 316)
      ((top.drop 4).take 4) (by simp [htop]) (by decide)).mp $$ T316
  ihave T352 := ByteSlice_as_word (func0Base + 352) (func0Base + 352)
    ((top.drop 40).take 8) rfl (by simp [htop]) $$ T352
  ihave T360 :=
    (Slices.ByteSlice_four_as_word 0 (func0Base + 360)
      ((top.drop 48).take 4) (by simp [htop]) (by decide)).mp $$ T360
  -- the four bytes of the middle region that the conversion slot uses
  icases (ByteSlice_split_at (func0Base + 36) 4 mid
    (by simp [hmid])).mp $$ Hmid with ⟨Hmid4, Hmidrest⟩
  isimp only [UInt32.reduceToNat] at Hmid4
  isimp only [UInt32.reduceToNat,
    show func0Base + 36 + 4 = func0Base + 40 by decide] at Hmidrest
  -- the reload of the three vector words
  rw [insControls7_eq, insRest7_shape]
  simp only [afterReadLocalsIns, insReload, insDecodeKV,
    List.cons_append, List.nil_append]
  wasm_twp_pures [twp_localGet]
  wasm_twp_rebind twp_load32 (address := func0Base) (offset := 24)
    capacity h24f.1 h24f.2.1 h24f.2.2.1 h24f.2.2.2 with Hcapw
  wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_localGet]
  wasm_twp_rebind twp_load32 (address := func0Base) (offset := 28) ptr
    h28f.1 h28f.2.1 h28f.2.2.1 h28f.2.2.2 with Hptrw
  wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_localGet twp_localGet]
  wasm_twp_rebind twp_load32 (address := func0Base) (offset := 32)
    (UInt32.ofNat input.length) h32f.1 h32f.2.1 h32f.2.2.1 h32f.2.2.2
    with Hlenw
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_rebind twp_store32 (address := func0Base) (offset := 316)
    (WordCodec.decodeU32 ((top.drop 4).take 4)) h316f.1 h316f.2.1
    h316f.2.2.1 h316f.2.2.2 with T316
  wasm_twp_pures [twp_localGet twp_localGet]
  wasm_twp_rebind twp_store32 (address := func0Base) (offset := 312)
    (WordCodec.decodeU32 (top.take 4)) h312f.1 h312f.2.1 h312f.2.2.1
    h312f.2.2.2 with T312
  wasm_twp_pures [twp_localGet twp_const]
  by_cases hshort : UInt32.ofNat input.length ≤ (3 : UInt32)
  · -- the input is shorter than four bytes: the first error arm
    have hlen3 : input.length ≤ 3 := by
      have := UInt32.le_iff_toNat_le.mp hshort
      rw [hlenNat] at this
      exact this
    have hno : ¬ InsertDecodeAccepts input := by
      rintro ⟨h8, -, -⟩
      omega
    iapply twp_leU (result := 1) (by rw [if_pos hshort])
    iapply twp_brIf (by decide) (by rfl)
    simp only [insBlock6Frame, List.take_zero, List.nil_append]
    rw [insertOutput_of_not_accepts input hno, List.append_nil]
    ihave Hptrw : pointsTo_u32 0 (func0Base + 24 + 4) ptr $$ [Hptrw]
    · irw_exact [show func0Base + 24 + 4 = func0Base + 28 by decide]
        with Hptrw
    ihave Hlenw : pointsTo_u32 0 (func0Base + 24 + 4 + 4)
        (UInt32.ofNat input.length) $$ [Hlenw]
    · irw_exact [show func0Base + 24 + 4 + 4 = func0Base + 32 by decide]
        with Hlenw
    ihave Hhdr :=
      ByteSlice_of_three_words (func0Base + 24) capacity ptr
        (UInt32.ofNat input.length) (by decide) $$
      [Hcapw Hptrw Hlenw]
    · iframe Hcapw Hptrw Hlenw
    ihave Hmid4 : Slices.ByteSlice 0 (func0Base + 24 + UInt32.ofNat 12)
        (mid.take 4) $$ [Hmid4]
    · irw_exact [show func0Base + 24 + UInt32.ofNat 12 = func0Base + 36
        by decide] with Hmid4
    ihave Hconv :=
      ByteSlice_glue (func0Base + 24)
        (WordCodec.u32le.serialize
          [capacity, ptr, UInt32.ofNat input.length]) (mid.take 4) 12
        rfl $$ [Hhdr Hmid4]
    · iframe Hhdr Hmid4
    icases (ByteSlice_split_at (func0Base + 56) 16 chunk
      (by simp [hchunk])).mp $$ Hchunk with ⟨Herrslot, _Hchunkrest⟩
    isimp only [UInt32.reduceToNat] at Herrslot
    iclear T312 T316 T320 T336 H8 H16 Hkeys Hinput Hmidrest
    iapply twp_ins_err_arm_a func49_correct func52_correct heapId
      (HashMap.Table.groupWord ((top.drop 40).take 8))
      (WordCodec.decodeU32 ((top.drop 48).take 4)) (chunk.take 16)
      (WordCodec.u32le.serialize
        [capacity, ptr, UInt32.ofNat input.length] ++ mid.take 4)
      dataBytes (extra ++ reserve) storedCursor frontier history output
      (by simp [hchunk]) (by simp [hmid]) hdata
    iframe
  · -- the input holds a key: the first inline cut
    have h3t : (3 : UInt32).toNat = 3 := rfl
    have h4t : (4 : UInt32).toNat = 4 := rfl
    have hlen4 : 4 ≤ input.length := by
      by_contra hlt
      exact hshort (UInt32.le_iff_toNat_le.mpr
        (by rw [hlenNat, h3t]; omega))
    have hptr4 : ptr.toNat + 4 < UInt32.size := by omega
    iapply twp_leU (result := 0) (by rw [if_neg hshort])
    iapply twp_brIfZero
    -- the header moves past the key
    wasm_twp_pures [twp_localGet twp_localGet twp_const twp_add]
    wasm_twp_rebind twp_store32 (address := func0Base) (offset := 316)
      (UInt32.ofNat input.length) h316f.1 h316f.2.1 h316f.2.2.1
      h316f.2.2.2 with T316
    wasm_twp_pures [twp_localGet twp_localGet twp_const twp_add]
    wasm_twp_rebind twp_store32 (address := func0Base) (offset := 312)
      ptr h312f.1 h312f.2.1 h312f.2.2.1 h312f.2.2.2 with T312
    -- the key is the first word of the input
    icases (ByteSlice_split_at ptr 4 input
      (by simp only [UInt32.reduceToNat]; omega)).mp $$ Hinput
      with ⟨Hkey, Hrest⟩
    isimp only [UInt32.reduceToNat] at Hkey
    isimp only [UInt32.reduceToNat] at Hrest
    ihave Hkey :=
      (Slices.ByteSlice_four_as_word 0 ptr (input.take 4)
        (by simp only [List.length_take]; omega) hptr4).mp $$ Hkey
    ihave Hkey : pointsTo_u32 0 ptr (leadingKey input) $$ [Hkey]
    · isimp only [leadingKey]
      iexact Hkey
    obtain ⟨_hk0, hk1, hk2, hk3⟩ := offset_facts ptr 0 0 rfl (by omega)
    rw [show ptr + (0 : UInt32) = ptr from UInt32.add_zero ptr]
      at hk1 hk2 hk3
    wasm_twp_pures [twp_localGet]
    wasm_twp_rebind twp_load32_addr (leadingKey input) hk1 hk2 hk3
      with Hkey
    wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceSub, List.set]
    wasm_twp_pures [twp_localGet twp_const]
    by_cases hshort2 : UInt32.ofNat input.length < (8 : UInt32)
    · -- the input held a key but no value: the second error arm
      have h8t : (8 : UInt32).toNat = 8 := rfl
      have hlen8 : input.length < 8 := by
        have hlt := UInt32.lt_iff_toNat_lt.mp hshort2
        rw [hlenNat, h8t] at hlt
        exact hlt
      have hno : ¬ InsertDecodeAccepts input := by
        rintro ⟨h8, -, -⟩
        omega
      iapply twp_ltU (result := 1) (by rw [if_pos hshort2])
      iapply twp_brIf (by decide) (by rfl)
      simp only [insBlock5Frame, List.take_zero, List.nil_append]
      rw [insertOutput_of_not_accepts input hno, List.append_nil]
      ihave Hptrw : pointsTo_u32 0 (func0Base + 24 + 4) ptr $$ [Hptrw]
      · irw_exact [show func0Base + 24 + 4 = func0Base + 28 by decide]
          with Hptrw
      ihave Hlenw : pointsTo_u32 0 (func0Base + 24 + 4 + 4)
          (UInt32.ofNat input.length) $$ [Hlenw]
      · irw_exact
          [show func0Base + 24 + 4 + 4 = func0Base + 32 by decide]
          with Hlenw
      ihave Hhdr :=
        ByteSlice_of_three_words (func0Base + 24) capacity ptr
          (UInt32.ofNat input.length) (by decide) $$
        [Hcapw Hptrw Hlenw]
      · iframe Hcapw Hptrw Hlenw
      ihave Hmid4 :
          Slices.ByteSlice 0 (func0Base + 24 + UInt32.ofNat 12)
            (mid.take 4) $$ [Hmid4]
      · irw_exact [show func0Base + 24 + UInt32.ofNat 12 = func0Base + 36
          by decide] with Hmid4
      ihave Hconv :=
        ByteSlice_glue (func0Base + 24)
          (WordCodec.u32le.serialize
            [capacity, ptr, UInt32.ofNat input.length]) (mid.take 4) 12
          rfl $$ [Hhdr Hmid4]
      · iframe Hhdr Hmid4
      icases (ByteSlice_split_at (func0Base + 56) 16 chunk
        (by simp [hchunk])).mp $$ Hchunk with ⟨Herrslot, _Hchunkrest⟩
      isimp only [UInt32.reduceToNat] at Herrslot
      iclear T312 T316 T320 T336 H8 H16 Hkeys Hkey Hrest Hmidrest
      iapply twp_ins_err_arm_b func49_correct func52_correct heapId
        (HashMap.Table.groupWord ((top.drop 40).take 8))
        (WordCodec.decodeU32 ((top.drop 48).take 4)) (chunk.take 16)
        (WordCodec.u32le.serialize
          [capacity, ptr, UInt32.ofNat input.length] ++ mid.take 4)
        dataBytes (extra ++ reserve) storedCursor frontier history output
        (by simp [hchunk]) (by simp [hmid]) hdata
      iframe
    · -- the input holds a key and a value: the decoder call
      have h8t : (8 : UInt32).toNat = 8 := rfl
      have hlen8 : 8 ≤ input.length := by
        by_contra hlt
        exact hshort2 (UInt32.lt_iff_toNat_lt.mpr
          (by rw [hlenNat, h8t]; omega))
      have h4f := offset_facts ptr 4 4 rfl (by omega)
      have hptr8 : (ptr + 4).toNat + 4 < UInt32.size := by
        rw [h4f.1, h4t]; omega
      iapply twp_ltU (result := 0) (by rw [if_neg hshort2])
      iapply twp_brIfZero
      -- the header moves past the value
      wasm_twp_pures [twp_localGet twp_localGet twp_const twp_add]
      wasm_twp_rebind twp_store32 (address := func0Base) (offset := 316)
        ((4294967292 : UInt32) + UInt32.ofNat input.length) h316f.1
        h316f.2.1 h316f.2.2.1 h316f.2.2.2 with T316
      wasm_twp_pures [twp_localGet twp_localGet twp_const twp_add]
      wasm_twp_rebind twp_store32 (address := func0Base) (offset := 312)
        ((4 : UInt32) + ptr) h312f.1 h312f.2.1 h312f.2.2.1 h312f.2.2.2
        with T312
      -- the value is the second word of the input
      have hdrop4 : (4 : UInt32).toNat ≤ (input.drop 4).length := by
        simp only [UInt32.reduceToNat, List.length_drop]
        omega
      icases (ByteSlice_split_at (ptr + 4) 4 (input.drop 4)
        hdrop4).mp $$ Hrest with ⟨Hval, Hmap⟩
      isimp only [UInt32.reduceToNat] at Hval
      isimp only [UInt32.reduceToNat,
        show (input.drop 4).drop 4 = input.drop 8 from by
          simp [List.drop_drop]] at Hmap
      ihave Hval :=
        (Slices.ByteSlice_four_as_word 0 (ptr + 4)
          ((input.drop 4).take 4)
          (by simp only [List.length_take, List.length_drop]; omega)
          hptr8).mp $$ Hval
      ihave Hval : pointsTo_u32 0 (ptr + 4) (leadingValue input) $$
        [Hval]
      · isimp only [leadingValue]
        iexact Hval
      wasm_twp_pures [twp_localGet]
      wasm_twp_rebind twp_load32 (address := ptr) (offset := 4)
        (leadingValue input) h4f.1 h4f.2.1 h4f.2.2.1 h4f.2.2.2 with Hval
      wasm_twp_localSet [List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceSub, List.set]
      iapply twp_br (by rfl)
      simp only [insBlock4Frame, List.take_zero, List.nil_append]
      -- the map slot goes back together
      ihave Hptrw : pointsTo_u32 0 (func0Base + 24 + 4) ptr $$ [Hptrw]
      · irw_exact [show func0Base + 24 + 4 = func0Base + 28 by decide]
          with Hptrw
      ihave Hlenw : pointsTo_u32 0 (func0Base + 24 + 4 + 4)
          (UInt32.ofNat input.length) $$ [Hlenw]
      · irw_exact
          [show func0Base + 24 + 4 + 4 = func0Base + 32 by decide]
          with Hlenw
      ihave Hhdr :=
        ByteSlice_of_three_words (func0Base + 24) capacity ptr
          (UInt32.ofNat input.length) (by decide) $$
        [Hcapw Hptrw Hlenw]
      · iframe Hcapw Hptrw Hlenw
      ihave Hmidrest :
          Slices.ByteSlice 0 (func0Base + 36 + UInt32.ofNat 4)
            (mid.drop 4) $$ [Hmidrest]
      · irw_exact [show func0Base + 36 + UInt32.ofNat 4 = func0Base + 40
          by decide] with Hmidrest
      ihave Hmid :=
        ByteSlice_glue (func0Base + 36) (mid.take 4) (mid.drop 4) 4
          (by simp [hmid]) $$ [Hmid4 Hmidrest]
      · iframe Hmid4 Hmidrest
      isimp only [List.take_append_drop] at Hmid
      ihave Hmid : Slices.ByteSlice 0 (func0Base + 24 + UInt32.ofNat 12)
          mid $$ [Hmid]
      · irw_exact [show func0Base + 24 + UInt32.ofNat 12 = func0Base + 36
          by decide] with Hmid
      ihave Hconv :=
        ByteSlice_glue (func0Base + 24)
          (WordCodec.u32le.serialize
            [capacity, ptr, UInt32.ofNat input.length]) mid 12
          rfl $$ [Hhdr Hmid]
      · iframe Hhdr Hmid
      -- the bytes behind the value are the map
      ihave Hmap : Slices.ByteSlice 0 (8 + ptr) (insertMapBytes input) $$
        [Hmap]
      · isimp only [insertMapBytes]
        irw_exact [show ptr + 4 + 4 = 8 + ptr from by
          rw [UInt32.add_assoc, show (4 : UInt32) + 4 = 8 from by decide,
            UInt32.add_comm]] with Hmap
      -- the two callee slots in the chunk
      icases (ByteSlice_split_at (func0Base + 56) 40 chunk
        (by simp [hchunk])).mp $$ Hchunk with ⟨Hout, _Hchunkrest⟩
      isimp only [UInt32.reduceToNat] at Hout
      have hmapLen :
          (insertMapBytes input).length =
            ((4294967288 : UInt32) + UInt32.ofNat input.length).toNat := by
        rw [cut_length input.length hlen8 hinput]
        unfold insertMapBytes
        rw [List.length_drop]
      iclear T352 T360 Hkey
      iapply twp_ins_decode_call func1_correct hfunc2 hfunc3
        func52_correct heapId (8 + ptr)
        ((4294967288 : UInt32) + UInt32.ofNat input.length)
        (WordCodec.decodeU32 ((head.drop 16).take 4))
        (HashMap.Table.groupWord ((head.drop 8).take 8)) _ input
        ((top.drop 24).take 16)
        (WordCodec.u32le.serialize
          [capacity, ptr, UInt32.ofNat input.length] ++ mid)
        (chunk.take 40) ((top.drop 8).take 16) keysBefore dataBytes
        (extra ++ reserve) storedCursor frontier history output hlen8
        (by omega) hmapLen (by simp [htop]) (by simp [hmid])
        (by simp [hchunk]) (by simp [htop]) hkeys hdata
      iframe
/-! ## The contract of the driver tail -/

/-- The tail of the `map_insert` driver meets its contract.  The two
open hypotheses are the contract of `collect_entries`, absolute `func
5`, and the contract of the insert shim, absolute `func 6`.  Every
other callee of the tail carries a proof. -/
theorem twp_insert_tail [WasmSmallStepGS hlc Universal.State]
    (hfunc2 : Func2Spec (hlc := hlc))
    (hfunc3 : Func3Spec (hlc := hlc)) :
    InsertTailSpec (hlc := hlc) :=
  ⟨twp_insert_tail_nonempty hfunc2 hfunc3,
    twp_insert_tail_empty func49_correct func52_correct⟩

end Project.RustHashMap.InsertTailProof
