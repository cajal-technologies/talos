import Project.RustHashMap.CollectLoop
import Project.RustHashMap.DeallocNoop

/-!
# The tail of `collect_entries`

Absolute `func 5` ends with three pieces that name no open contract: the
guarded free of the pair buffer at WAT 943 to 953, the copy of the map
value at WAT 954 to 969, and the epilogue at WAT 970 to 973.  This module
proves one WP rule for each, so the assembly of `Func2Spec` has only the
prologue and the reserve left.

## The free asks for no live block

`Func57Spec` wants a `LiveBlock` for the memory it retires.  `Func2Spec`
takes the pair buffer as plain bytes and gives it back to nobody, and
`Func1Spec` hands the buffer to the driver the same way, so no caller of
`func 5` holds an allocation record for it.  The compiled body of absolute
60 is empty, so `twp_free_block` steps the call through
`DeallocNoop.Func57NoopSpec`, which asks for the runtime context alone and
leaves the block live in the allocator history.  Nothing below reads that
history.

## The copy is four block moves

`HashMapAt` names its base address in the four header words and in the two
seed cells, and nowhere else.  `TableAt_relocate` says so, `wordPair` reads
two adjacent words as the `u64` that the `i64.load` returns, and
`HashMapAt_move` puts the two together as the eight cells that the four
moves read and write.  The `u64` values stay in the raw `groupWord` form:
the code loads a word and stores the same word, so nothing reads them.

`wordPair`, `pointsTo_u32_pair_as_groupWord` and `ByteSlice_thirtyTwo_as_cells`
are generic memory lemmas.  They belong beside `ByteSlice_eight_as_u64` in
`CodeLib.RustStd.HashMap.TableMem`, and moving them is a pure relocation.
The pair lemma carries `groupWord` in its name because
`Project.RustHashMap.ReadAll.pointsTo_u32_pair_as_u64` already packs the
same two words with a shift, and only the `groupWord` form composes with
`ByteSlice_eight_as_u64`.
-/

namespace Project.RustHashMap.CollectTail

open Wasm Wasm.RustStd
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open Project.RustHashMap.Allocator
open Project.RustHashMap.AllocatorContracts
open Project.RustHashMap.EntryContracts
open Project.RustHashMap.BodyContracts
open Project.RustHashMap.CollectContract
open Project.RustHashMap.CollectBodyContracts
open Project.RustHashMap.FrameCells
open Project.RustHashMap.CollectLoop
open scoped Wasm.SmallStep.Outcome

/-! ## The map value at another address -/

section Move

variable {α : Type} [WasmHeapGS α]

/-- The `u64` that two adjacent words pack into. -/
def wordPair (w0 w1 : UInt32) : UInt64 :=
  HashMap.Table.groupWord
    [u32Byte w0 0, u32Byte w0 1, u32Byte w0 2, u32Byte w0 3,
      u32Byte w1 0, u32Byte w1 1, u32Byte w1 2, u32Byte w1 3]

/-- Two adjacent owned words are one owned `u64`. -/
theorem pointsTo_u32_pair_as_groupWord (memId : Nat) (addr : UInt32) (w0 w1 : UInt32) :
    iprop(pointsTo_u32 (α := α) memId addr w0 ∗
        pointsTo_u32 memId (addr + 4) w1) ⊣⊢
      pointsTo_u64 memId addr (wordPair w0 w1) := by
  unfold wordPair
  refine (BI.sep_congr (pointsTo_u32_as_bytes memId addr w0)
    (pointsTo_u32_as_bytes memId (addr + 4) w1)).trans ?_
  refine (pointsToBytes_append (α := α) memId addr
    [u32Byte w0 0, u32Byte w0 1, u32Byte w0 2, u32Byte w0 3]
    [u32Byte w1 0, u32Byte w1 1, u32Byte w1 2, u32Byte w1 3]).symm.trans ?_
  exact HashMap.Table.pointsToBytes_eight_as_u64 memId addr
    [u32Byte w0 0, u32Byte w0 1, u32Byte w0 2, u32Byte w0 3,
      u32Byte w1 0, u32Byte w1 1, u32Byte w1 2, u32Byte w1 3] rfl

/-- The four header words are two `u64` cells. -/
theorem tableHeader_as_u64 (memId : Nat)
    (base ctrl mask growthLeft items : UInt32) :
    HashMap.Table.tableHeader (α := α) memId base ctrl mask growthLeft items
        ⊣⊢
      iprop(pointsTo_u64 memId base (wordPair ctrl mask) ∗
        pointsTo_u64 memId (base + 8) (wordPair growthLeft items)) := by
  have e12 : base + 12 = base + 8 + 4 := by rw [UInt32.add_assoc]; rfl
  unfold HashMap.Table.tableHeader
  rw [e12]
  refine BI.sep_assoc.symm.trans ?_
  exact BI.sep_congr (pointsTo_u32_pair_as_groupWord memId base ctrl mask)
    (pointsTo_u32_pair_as_groupWord memId (base + 8) growthLeft items)

/-- A table names its base address only in the header, so a caller that
rebuilds the header at another address holds the table there.  The control
bytes and the buckets do not move. -/
theorem TableAt_relocate (memId : Nat) (src dst : UInt32)
    (t : HashMap.Table UInt32 UInt32) :
    HashMap.Table.TableAt (α := α) memId src t ⊢
      iprop(∃ ctrl : UInt32, ∃ mask : UInt32, ∃ growthLeft : UInt32,
        ∃ items : UInt32,
        HashMap.Table.tableHeader memId src ctrl mask growthLeft items ∗
        (HashMap.Table.tableHeader memId dst ctrl mask growthLeft items -∗
          HashMap.Table.TableAt memId dst t)) := by
  iintro Htable
  isimp only [HashMap.Table.TableAt] at Htable
  icases Htable with ⟨%ctrl, Hbody⟩
  icases Hbody with (Hsingleton | ⟨%hbuckets, Hallocated⟩)
  · isimp only [HashMap.Table.SingletonBody] at Hsingleton
    icases Hsingleton with ⟨%hfacts, Hheader, Hctrl⟩
    iexists ctrl, (0 : UInt32), (0 : UInt32), (0 : UInt32)
    isplitl [Hheader]
    · iexact Hheader
    · iintro Hheader
      isimp only [HashMap.Table.TableAt]
      iexists ctrl
      ileft
      isimp only [HashMap.Table.SingletonBody]
      isplitl_pureexact hfacts
      · iframe Hheader Hctrl
  · isimp only [HashMap.Table.TableBody] at Hallocated
    icases Hallocated with ⟨%hctrlBound, Hheader, Hbytes, Hslots⟩
    iexists ctrl, (UInt32.ofNat (t.buckets - 1)),
      (UInt32.ofNat t.growthLeft), (UInt32.ofNat t.items)
    isplitl [Hheader]
    · iexact Hheader
    · iintro Hheader
      isimp only [HashMap.Table.TableAt]
      iexists ctrl
      iright
      isplitl_pureexact hbuckets
      · isimp only [HashMap.Table.TableBody]
        isplitl_pureexact hctrlBound
        · iframe Hheader Hbytes Hslots

/-- The whole 32-byte map value as four `u64` cells, and the wand that puts
it back at another address.  This is the copy at WAT 954 to 969. -/
theorem HashMapAt_move (memId : Nat) (src dst : UInt32) (k0 k1 : UInt64)
    (t : HashMap.Table UInt32 UInt32) :
    HashMap.Table.HashMapAt (α := α) memId src k0 k1 t ⊢
      iprop(∃ v0 : UInt64, ∃ v1 : UInt64,
        pointsTo_u64 memId src v0 ∗ pointsTo_u64 memId (src + 8) v1 ∗
        pointsTo_u64 memId (src + 16) k0 ∗ pointsTo_u64 memId (src + 24) k1 ∗
        (pointsTo_u64 memId dst v0 -∗ pointsTo_u64 memId (dst + 8) v1 -∗
          pointsTo_u64 memId (dst + 16) k0 -∗
          pointsTo_u64 memId (dst + 24) k1 -∗
          HashMap.Table.HashMapAt memId dst k0 k1 t)) := by
  iintro Hmap
  isimp only [HashMap.Table.HashMapAt] at Hmap
  icases Hmap with ⟨Htable, Hk0, Hk1⟩
  ihave ⟨%ctrl, %mask, %growthLeft, %items, Hheader, Hback⟩ :=
    TableAt_relocate memId src dst t $$ Htable
  ihave Hcells :=
    (tableHeader_as_u64 memId src ctrl mask growthLeft items).mp $$ Hheader
  icases Hcells with ⟨Hc0, Hc1⟩
  iexists (wordPair ctrl mask), (wordPair growthLeft items)
  iframe Hc0 Hc1 Hk0 Hk1
  iintro Hd0 Hd1 Hdk0 Hdk1
  ihave Hheader :
      HashMap.Table.tableHeader memId dst ctrl mask growthLeft items
      $$ [Hd0 Hd1]
  · iapply (tableHeader_as_u64 memId dst ctrl mask growthLeft items).mpr
    iframe Hd0 Hd1
  ihave Htable := Hback $$ Hheader
  isimp only [HashMap.Table.HashMapAt]
  iframe Htable Hdk0 Hdk1

/-- A 32-byte slice is four `u64` cells.  The map output slot arrives as
bytes and the copy writes it as four `i64` stores. -/
theorem ByteSlice_thirtyTwo_as_cells (memId : Nat) (addr : UInt32)
    (bytes : List UInt8) (hlength : bytes.length = 32) :
    Slices.ByteSlice (α := α) memId addr bytes ⊢
      iprop(∃ d0 : UInt64, ∃ d1 : UInt64, ∃ d2 : UInt64, ∃ d3 : UInt64,
        pointsTo_u64 memId addr d0 ∗ pointsTo_u64 memId (addr + 8) d1 ∗
        pointsTo_u64 memId (addr + 16) d2 ∗
        pointsTo_u64 memId (addr + 24) d3) := by
  obtain ⟨x0, x1, x2, x3, hcat, hl0, hl1, hl2, hl3⟩ :
      ∃ x0 x1 x2 x3 : List UInt8, bytes = x0 ++ (x1 ++ (x2 ++ x3)) ∧
        x0.length = 8 ∧ x1.length = 8 ∧ x2.length = 8 ∧ x3.length = 8 := by
    refine ⟨bytes.take 8, (bytes.drop 8).take 8, (bytes.drop 16).take 8,
      bytes.drop 24, ?_, ?_, ?_, ?_, ?_⟩
    · rw [show bytes.drop 24 = (bytes.drop 16).drop 8 by
        rw [List.drop_drop], List.take_append_drop,
        show bytes.drop 16 = (bytes.drop 8).drop 8 by rw [List.drop_drop],
        List.take_append_drop, List.take_append_drop]
    · rw [List.length_take]; omega
    · rw [List.length_take, List.length_drop]; omega
    · rw [List.length_take, List.length_drop]; omega
    · rw [List.length_drop]; omega
  subst hcat
  have e8 : UInt32.ofNat 8 = (8 : UInt32) := rfl
  have e16 : addr + 8 + 8 = addr + 16 := by rw [UInt32.add_assoc]; rfl
  have e24 : addr + 16 + 8 = addr + 24 := by rw [UInt32.add_assoc]; rfl
  iintro Hslice
  ihave ⟨H0, Hrest⟩ :=
    (Slices.ByteSlice_append memId addr x0 (x1 ++ (x2 ++ x3))).mp $$ Hslice
  isimp only [hl0, e8] at Hrest
  ihave ⟨H1, Hrest⟩ :=
    (Slices.ByteSlice_append memId (addr + 8) x1 (x2 ++ x3)).mp $$ Hrest
  isimp only [hl1, e8, e16] at Hrest
  ihave ⟨H2, H3⟩ :=
    (Slices.ByteSlice_append memId (addr + 16) x2 x3).mp $$ Hrest
  isimp only [hl2, e8, e24] at H3
  ihave ⟨%_hb0, Hc0⟩ :=
    (HashMap.Table.ByteSlice_eight_as_u64 memId addr x0 hl0).mp $$ H0
  ihave ⟨%_hb1, Hc1⟩ :=
    (HashMap.Table.ByteSlice_eight_as_u64 memId (addr + 8) x1 hl1).mp $$ H1
  ihave ⟨%_hb2, Hc2⟩ :=
    (HashMap.Table.ByteSlice_eight_as_u64 memId (addr + 16) x2 hl2).mp $$ H2
  ihave ⟨%_hb3, Hc3⟩ :=
    (HashMap.Table.ByteSlice_eight_as_u64 memId (addr + 24) x3 hl3).mp $$ H3
  iexists (HashMap.Table.groupWord x0), (HashMap.Table.groupWord x1),
    (HashMap.Table.groupWord x2), (HashMap.Table.groupWord x3)
  iframe Hc0 Hc1 Hc2 Hc3

end Move


/-! ## The compiled tail -/

section Machine

variable [WasmSmallStepGS hlc Universal.State]

/-! ## The free of the pair buffer -/

/-- WAT 944 to 952: the guarded free.  Local 1 is the capacity and local 4
the buffer start, so the freed size is `8 * cap` and the alignment is 4. -/
def freeBlockBody : Program :=
  [.localGet 1, .eqz, .br_if 0, .localGet 4, .localGet 1, .const 3, .shl,
    .const 4, .call 60]

/-- The free block is instruction 38 of the compiled body. -/
theorem func2_free_block :
    Project.RustHashMap.func2 =
      Project.RustHashMap.func2.take 38 ++
        .block 0 0 freeBlockBody :: Project.RustHashMap.func2.drop 39 := by
  rfl

set_option maxHeartbeats 2000000 in
/-- WAT 943 to 953.  The block drops the pair buffer.  The bytes are gone
either way, so the rule asks for the runtime context alone. -/
theorem twp_free_block
    (mapSlot cap frame cur ptr endAddr : UInt32) (seed : UInt64)
    (contCode : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (s : Stuckness) (E : CoPset) (Φ : ObservableOutcome → HeapIProp) :
    iprop(RuntimeContext ∗
      (RuntimeContext -∗
        WP (Expr.running
            ⟨collectLocals mapSlot cap frame cur ptr endAddr seed, contCode,
              arity, remainder, controls, calls⟩ :
            Expr Universal.State) @ s; E [{ Φ }])) ⊢
      WP (Expr.running
          ⟨collectLocals mapSlot cap frame cur ptr endAddr seed,
            .block 0 0 freeBlockBody :: contCode, arity, remainder, controls,
            calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hcont⟩
  simp only [freeBlockBody]
  iapply Wasm.SmallStep.twp_block
  simp only [collectLocals, List.drop_nil]
  wasm_twp_pures [twp_localGet]
  by_cases hcap : cap = 0
  · iapply twp_eqz (result := 1) (by rw [if_pos hcap])
    iapply twp_brIf (by decide) (by rfl)
    simp only [List.take_zero, List.nil_append]
    iapply Hcont
    iexact Hruntime
  · iapply twp_eqz (result := 0) (by rw [if_neg hcap])
    iapply twp_brIfZero
    wasm_twp_pures [twp_localGet twp_localGet twp_const twp_shl twp_const]
    rw [show ((3 : UInt32) % 32) = 3 from rfl]
    have Hfree : DeallocNoop.Func57NoopSpec (hlc := hlc) :=
      DeallocNoop.func57_noop_correct
    unfold DeallocNoop.Func57NoopSpec CallContract callExpr at Hfree
    simp only [List.cons_append, List.nil_append] at Hfree
    iapply Hfree (ptr := ptr) (size := cap <<< 3) (alignment := 4)
      (callerLocals :=
        ⟨[.i32 mapSlot, .i32 cap],
          [.i32 frame, .i32 cur, .i32 ptr, .i64 seed, .i32 endAddr], []⟩)
      (stack := [])
    isplitl_exact Hruntime
    · iintro Hruntime
      isimp only [ResumeWP, resumeExpr, List.nil_append]
      wasm_twp_pures [twp_exitControl]
      dsimp only
      simp only [List.take_zero, List.nil_append]
      iapply Hcont
      iexact Hruntime

/-! ## The copy of the map value -/

/-- The same cell under an equal address. -/
private theorem pointsTo_u64_address_eq (memId : Nat) {a b : UInt32}
    (h : a = b) (v : UInt64) :
    pointsTo_u64 (α := Universal.State) memId a v ⊢
      pointsTo_u64 memId b v := by
  subst h
  iintro Hcell
  iexact Hcell

/-- WAT 954 to 969: the four `i64` moves that copy the 32-byte map value
out of the frame into the caller slot.  The continuation is a cons chain,
because `iapply` does not unfold `List.append`. -/
@[reducible] def copyOutCode (contCode : Program) : Program :=
  .localGet 0 :: .localGet 2 :: .load64 40 :: .store64 24 ::
    .localGet 0 :: .localGet 2 :: .load64 32 :: .store64 16 ::
    .localGet 0 :: .localGet 2 :: .load64 24 :: .store64 8 ::
    .localGet 0 :: .localGet 2 :: .load64 16 :: .store64 0 :: contCode

/-- The copy starts at instruction 39 of the compiled body. -/
theorem func2_copy_out :
    Project.RustHashMap.func2.drop 39 =
      copyOutCode (Project.RustHashMap.func2.drop 55) := by
  rfl

set_option maxHeartbeats 2000000 in
/-- WAT 954 to 969.  The frame holds the map value at offset 16 and the
caller slot takes it at offset 0. -/
theorem twp_copy_out
    (mapSlot cap frame cur ptr endAddr : UInt32) (seed : UInt64)
    (k0 k1 : UInt64) (t : HashMap.Table UInt32 UInt32)
    (mapBefore : List UInt8)
    (contCode : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (s : Stuckness) (E : CoPset) (Φ : ObservableOutcome → HeapIProp)
    (hmapLength : mapBefore.length = 32)
    (hmapSlot : mapSlot.toNat + 32 < UInt32.size)
    (hframe : frame.toNat + 48 < UInt32.size) :
    iprop(Slices.ByteSlice 0 mapSlot mapBefore ∗
      HashMap.Table.HashMapAt 0 (frame + 16) k0 k1 t ∗
      (HashMap.Table.HashMapAt 0 mapSlot k0 k1 t -∗
        WP (Expr.running
            ⟨collectLocals mapSlot cap frame cur ptr endAddr seed, contCode,
              arity, remainder, controls, calls⟩ :
            Expr Universal.State) @ s; E [{ Φ }])) ⊢
      WP (Expr.running
          ⟨collectLocals mapSlot cap frame cur ptr endAddr seed,
            copyOutCode contCode, arity, remainder, controls, calls⟩ :
          Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hslot, Hmap, Hcont⟩
  have a24 : frame + 16 + 8 = frame + 24 := by rw [UInt32.add_assoc]; rfl
  have a32 : frame + 16 + 16 = frame + 32 := by rw [UInt32.add_assoc]; rfl
  have a40 : frame + 16 + 24 = frame + 40 := by rw [UInt32.add_assoc]; rfl
  have a0 : mapSlot + 0 = mapSlot := UInt32.add_zero mapSlot
  ihave ⟨%d0, %d1, %d2, %d3, Hd0, Hd1, Hd2, Hd3⟩ :=
    ByteSlice_thirtyTwo_as_cells 0 mapSlot mapBefore hmapLength $$ Hslot
  ihave ⟨%v0, %v1, Hs0, Hs1, Hsk0, Hsk1, Hback⟩ :=
    HashMapAt_move 0 (frame + 16) mapSlot k0 k1 t $$ Hmap
  isimp only [a24] at Hs1
  isimp only [a32] at Hsk0
  isimp only [a40] at Hsk1
  ihave Hd0 := pointsTo_u64_address_eq 0 a0.symm d0 $$ Hd0
  have hf40 := offset_facts64 frame 40 40 rfl (by omega)
  have hf32 := offset_facts64 frame 32 32 rfl (by omega)
  have hf24 := offset_facts64 frame 24 24 rfl (by omega)
  have hf16 := offset_facts64 frame 16 16 rfl (by omega)
  have hm24 := offset_facts64 mapSlot 24 24 rfl (by omega)
  have hm16 := offset_facts64 mapSlot 16 16 rfl (by omega)
  have hm8 := offset_facts64 mapSlot 8 8 rfl (by omega)
  have hm0 := offset_facts64 mapSlot 0 0 rfl (by omega)
  simp only [copyOutCode, collectLocals]
  wasm_twp_block_move (frame, 40, k1, hf40) (mapSlot, 24, d3, hm24)
    with Hsk1 Hd3
  wasm_twp_block_move (frame, 32, k0, hf32) (mapSlot, 16, d2, hm16)
    with Hsk0 Hd2
  wasm_twp_block_move (frame, 24, v1, hf24) (mapSlot, 8, d1, hm8)
    with Hs1 Hd1
  wasm_twp_block_move (frame, 16, v0, hf16) (mapSlot, 0, d0, hm0)
    with Hs0 Hd0
  isimp only [a0] at Hd0
  ihave Hmap := Hback $$ Hd0 Hd1 Hd2 Hd3
  iapply Hcont
  iexact Hmap

/-! ## The epilogue -/

/-- WAT 970 to 973: the frame goes back to the stack pointer. -/
@[reducible] def epilogueCode (contCode : Program) : Program :=
  .localGet 2 :: .const 48 :: .add :: .globalSet 0 :: contCode

/-- The epilogue is instruction 55 of the compiled body. -/
theorem func2_epilogue :
    Project.RustHashMap.func2.drop 55 = epilogueCode [] := by
  rfl

set_option maxHeartbeats 2000000 in
/-- WAT 970 to 973.  The 48-byte frame returns to the caller. -/
theorem twp_restore_sp
    (mapSlot cap frame cur ptr endAddr : UInt32) (seed : UInt64)
    (contCode : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (s : Stuckness) (E : CoPset) (Φ : ObservableOutcome → HeapIProp) :
    iprop(StackPointer frame ∗
      (StackPointer (frame + 48) -∗
        WP (Expr.running
            ⟨collectLocals mapSlot cap frame cur ptr endAddr seed, contCode,
              arity, remainder, controls, calls⟩ :
            Expr Universal.State) @ s; E [{ Φ }])) ⊢
      WP (Expr.running
          ⟨collectLocals mapSlot cap frame cur ptr endAddr seed,
            epilogueCode contCode, arity, remainder, controls, calls⟩ :
          Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hsp, Hcont⟩
  isimp only [StackPointer] at Hsp
  simp only [epilogueCode, collectLocals]
  wasm_twp_pures [twp_localGet twp_const twp_add]
    rewriting [UInt32.add_comm 48 frame]
  wasm_twp_rebind twp_globalSet with Hsp
  iapply Hcont
  isimp only [StackPointer]
  iexact Hsp

end Machine

end Project.RustHashMap.CollectTail
