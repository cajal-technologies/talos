import Project.RustHashMap.CollectTail
import Project.RustHashMap.Func13Proof

/-!
# The prologue of `collect_entries`

Absolute `func 5` opens with 37 instructions that build the frame, read the
`Vec` header, take the two SipHash seeds from the thread-local cells and
copy the static empty table into the frame.  WAT lines 853 to 897.  This
module proves one WP rule for each of the three phases, so the assembly of
`Func2Spec` has only the reserve at WAT 908 to 919 left.

## What the phases do

`twp_collect_frame` lowers the stack pointer by 48 and reads the three
header words.  The `Vec<(u32, u32)>` header holds the capacity at offset 0,
the buffer pointer at offset 4 and the entry count at offset 8, and the
body keeps them in locals 1, 4 and 3.  Local 1 is a parameter slot, so the
header pointer is gone after this phase.

`twp_seed_guard` runs the block at WAT 867 to 875.  The state byte at
1049528 is 1 once absolute `func 16` has run, so the block calls it at most
once in a run.  The rule takes `keysBefore[16]? != some 2`, the same
precondition that `Func13Spec` takes: the byte is 2 only while the
thread-local is being dropped, and the compiled guard panics on it.

`twp_seed_copy` runs WAT 876 to 897.  It reads the seed pair, writes
`k0 + 1` back to the thread-local cell, and copies the sixteen bytes of the
static empty table from the data segment into the frame at offset 16.  The
seeds land at frame offsets 32 and 40, which is where `Table.HashMapAt`
keeps them, so `twp_copy_out` in `Project.RustHashMap.CollectTail` reads
them back without a move.

## Two resources that the rules take as arguments

The copy phase reads the data segment at 1048584 and 1048592, and the guard
reads the thread-local state byte.  The rules take both as explicit
arguments.  `Func2Spec` lends the two data cells and takes the guard
condition on the state byte, and `Project.RustHashMap.CollectAssembly`
passes them down.
-/

namespace Project.RustHashMap.CollectPrologue

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
open Project.RustHashMap.CollectTail
open scoped Wasm.SmallStep.Outcome

/-- The stack that `collect_entries` lends to its callees.  Its own frame is
48 bytes of the 192 that `collectDepth` names. -/
def collectBelowDepth : Nat := 144

/-! ## The frame and the header -/

/-- WAT 853 to 866: the frame and the three header words. -/
@[reducible] def framePhase (contCode : Program) : Program :=
  .globalGet 0 :: .const 48 :: .sub :: .localTee 2 :: .globalSet 0 ::
    .localGet 1 :: .load32 8 :: .localSet 3 ::
    .localGet 1 :: .load32 4 :: .localSet 4 ::
    .localGet 1 :: .load32 0 :: .localSet 1 :: contCode

/-- The frame phase is the first fourteen instructions of the body. -/
theorem func2_frame :
    Project.RustHashMap.func2
      = framePhase (Project.RustHashMap.func2.drop 14) := by
  rfl

set_option maxHeartbeats 2000000 in
/-- WAT 853 to 866.  The body takes 48 bytes of the region below the caller
and reads the three words of the `Vec` header into locals 1, 3 and 4. -/
theorem twp_collect_frame [WasmSmallStepGS hlc Universal.State]
    (sp mapSlot vecHeader cap ptr len endAddr0 : UInt32) (seed0 : UInt64)
    (below : List UInt8) (l2 l3 l4 : Value)
    (contCode : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (s : Stuckness) (E : CoPset) (Φ : ObservableOutcome → HeapIProp)
    (hheader : vecHeader.toNat + 12 < UInt32.size) :
    iprop(StackPointer sp ∗
      StackBelow sp collectDepth below ∗
      pointsTo_u32 0 vecHeader cap ∗
      pointsTo_u32 0 (vecHeader + 4) ptr ∗
      pointsTo_u32 0 (vecHeader + 8) len ∗
      (StackPointer (sp - 48) -∗
        StackBelow (sp - 48) collectBelowDepth (below.take collectBelowDepth) -∗
        Slices.ByteSlice 0 (sp - 48) (below.drop collectBelowDepth) -∗
        pointsTo_u32 0 vecHeader cap -∗
        pointsTo_u32 0 (vecHeader + 4) ptr -∗
        pointsTo_u32 0 (vecHeader + 8) len -∗
        ⌜(below.drop collectBelowDepth).length = 48⌝ -∗
        WP (Expr.running
            ⟨collectLocals mapSlot cap (sp - 48) len ptr endAddr0 seed0,
              contCode, arity, remainder, controls, calls⟩ :
            Expr Universal.State) @ s; E [{ Φ }])) ⊢
      WP (Expr.running
          ⟨⟨[.i32 mapSlot, .i32 vecHeader],
              [l2, l3, l4, .i64 seed0, .i32 endAddr0], []⟩,
            framePhase contCode, arity, remainder, controls, calls⟩ :
          Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hsp, Hbelow, Hcap, Hptr, Hlen, Hcont⟩
  have hcut : collectDepth - 48 = collectBelowDepth := rfl
  have hbase : sp - UInt32.ofNat 48 = sp - 48 := rfl
  have hh0_1 : (vecHeader + 1).toNat = vecHeader.toNat + 1 := by
    simpa using Slices.byteOffset_toNat vecHeader 1 (by omega)
  have hh0_2 : (vecHeader + 2).toNat = vecHeader.toNat + 2 := by
    simpa using Slices.byteOffset_toNat vecHeader 2 (by omega)
  have hh0_3 : (vecHeader + 3).toNat = vecHeader.toNat + 3 := by
    simpa using Slices.byteOffset_toNat vecHeader 3 (by omega)
  have hf4 := offset_facts vecHeader 4 4 rfl (by omega)
  have hf8 := offset_facts vecHeader 8 8 rfl (by omega)
  simp only [framePhase, collectLocals]
  isimp only [StackPointer] at Hsp
  wasm_twp_rebind twp_globalGet with Hsp
  wasm_twp_pures [twp_const twp_sub]
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_rebind twp_globalSet with Hsp
  wasm_twp_pures [twp_localGet]
  wasm_twp_rebind twp_load32 (address := vecHeader) (offset := 8) len
    hf8.1 hf8.2.1 hf8.2.2.1 hf8.2.2.2 with Hlen
  wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_localGet]
  wasm_twp_rebind twp_load32 (address := vecHeader) (offset := 4) ptr
    hf4.1 hf4.2.1 hf4.2.2.1 hf4.2.2.2 with Hptr
  wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_localGet]
  wasm_twp_rebind twp_load32_addr cap hh0_1 hh0_2 hh0_3 with Hcap
  wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  ihave ⟨Hlower, Hframe⟩ :=
    frame_split sp collectDepth 48 below (by decide) $$ Hbelow
  isimp only [hcut, hbase] at Hlower Hframe
  ihave ⟨%hframeLength, Hframe⟩ :=
    StackBelow_base sp (sp - 48) 48 (below.drop collectBelowDepth) hbase $$
      Hframe
  ihave Hsp : StackPointer (sp - 48) $$ [Hsp]
  · unfold StackPointer
    iexact Hsp
  iapply Hcont $$ Hsp Hlower Hframe Hcap Hptr Hlen
  ipureintro
  exact hframeLength

/-! ## The thread-local seed region -/

/-- Borrow the state byte at 1049528 out of the seed region and keep a way
back.  The address is already in the form that `twp_load8U_gen` reads. -/
private theorem ByteSlice_state_byte [WasmSmallStepGS hlc Universal.State]
    (keys : List UInt8) (b : UInt8) (rest : List UInt8)
    (hlength : keys.length = randomStateSize)
    (hdrop : keys.drop 16 = b :: rest) :
    Slices.ByteSlice 0 randomStateCell keys ⊢
      iprop(pointsTo (GF := WasmHeapGF Universal.State) (H := WasmHeapMap)
          ⟨0, (0 : UInt32) + 1049528⟩ (DFrac.own 1) (some b) ∗
        (pointsTo (GF := WasmHeapGF Universal.State) (H := WasmHeapMap)
            ⟨0, (0 : UInt32) + 1049528⟩ (DFrac.own 1) (some b) -∗
          Slices.ByteSlice 0 randomStateCell keys)) := by
  have hkeys24 : keys.length = 24 := hlength
  have hk16 : randomStateCell + UInt32.ofNat 16 = randomStateCell + 16 := rfl
  have hcell16 : (0 : UInt32) + 1049528 = randomStateCell + 16 := by decide
  have hsplit : keys.take 16 ++ (b :: rest) = keys := by
    rw [← hdrop]; exact List.take_append_drop 16 keys
  have htake16 : (keys.take 16).length = 16 := by
    rw [List.length_take, hkeys24]; omega
  iintro Hkeys
  ihave ⟨Hhead, Htail⟩ :=
    ByteSlice_cut randomStateCell keys 16 (by omega) $$ Hkeys
  isimp only [hk16, hdrop] at Htail
  isimp only [Slices.ByteSlice] at Htail
  icases Htail with ⟨%hbound, Hbytes⟩
  isimp only [pointsToBytes] at Hbytes
  icases Hbytes with ⟨Hbyte, Hrest⟩
  isimp only [← hcell16] at Hbyte
  isplitl [Hbyte]
  · iexact Hbyte
  · iintro Hbyte
    isimp only [hcell16] at Hbyte
    ihave Htail : Slices.ByteSlice 0 (randomStateCell + 16) (b :: rest) $$
        [Hbyte Hrest]
    · isimp only [Slices.ByteSlice, pointsToBytes]
      isplitl_pureexact hbound
      · iframe Hbyte Hrest
    ihave Hkeys :=
      (Slices.ByteSlice_append 0 randomStateCell (keys.take 16)
        (b :: rest)).mpr $$ [Hhead Htail]
    · isimp only [htake16, hk16]
      iframe Hhead Htail
    irw_exact [hsplit] with Hkeys

/-- The seed region as the two words and the eight bytes above them. -/
private theorem ByteSlice_as_seed_pair [WasmSmallStepGS hlc Universal.State]
    (keys : List UInt8) (hlength : keys.length = randomStateSize) :
    Slices.ByteSlice 0 randomStateCell keys ⊢
      iprop(pointsTo_u64 0 randomStateCell
          (HashMap.Table.groupWord (keys.take 8)) ∗
        pointsTo_u64 0 (randomStateCell + 8)
          (HashMap.Table.groupWord ((keys.drop 8).take 8)) ∗
        Slices.ByteSlice 0 (randomStateCell + 16) (keys.drop 16)) := by
  have hkeys24 : keys.length = 24 := hlength
  have hk8 : randomStateCell + UInt32.ofNat 8 = randomStateCell + 8 := rfl
  have hk16 : randomStateCell + (8 : UInt32) + UInt32.ofNat 8
      = randomStateCell + 16 := by decide
  have hdrop8 : (keys.drop 8).length = 16 := by
    rw [List.length_drop, hkeys24]
  have hw0 : (keys.take 8).length = 8 := by
    rw [List.length_take, hkeys24]; omega
  have hw1 : ((keys.drop 8).take 8).length = 8 := by
    rw [List.length_take, hdrop8]; omega
  have hrest : (keys.drop 8).drop 8 = keys.drop 16 := by
    rw [List.drop_drop]
  iintro Hkeys
  ihave ⟨Hword0, Hupper⟩ :=
    ByteSlice_cut randomStateCell keys 8 (by omega) $$ Hkeys
  isimp only [hk8] at Hupper
  ihave ⟨Hword1, Htail⟩ :=
    ByteSlice_cut (randomStateCell + 8) (keys.drop 8) 8 (by omega) $$ Hupper
  isimp only [hk16, hrest] at Htail
  ihave ⟨%_hb0, Hword0⟩ :=
    (HashMap.Table.ByteSlice_eight_as_u64 0 randomStateCell (keys.take 8)
      hw0).mp $$ Hword0
  ihave ⟨%_hb1, Hword1⟩ :=
    (HashMap.Table.ByteSlice_eight_as_u64 0 (randomStateCell + 8)
      ((keys.drop 8).take 8) hw1).mp $$ Hword1
  iframe Hword0 Hword1 Htail

/-! ## The thread-local guard -/

/-- WAT 867 to 875: the block that initialises the thread-local seed pair
once per run.  Instruction 14 of the body. -/
def stateGuardBody : Program :=
  [.const 0, .load8U 1049528, .const 1, .eq, .br_if 0, .const 0, .call 16]

/-- The guard block is instruction 14 of the body. -/
theorem func2_seed_guard :
    Project.RustHashMap.func2.drop 14
      = .block 0 0 stateGuardBody :: Project.RustHashMap.func2.drop 15 := by
  rfl

set_option maxHeartbeats 2000000 in
/-- WAT 867 to 875.  The state byte at 1049528 is 1 once absolute `func 16`
has run, so the block calls it at most once per run.  Both paths leave the
seed pair readable as two words. -/
theorem twp_seed_guard [WasmSmallStepGS hlc Universal.State]
    (mapSlot cap frame cur ptr endAddr : UInt32) (seed0 : UInt64)
    (keysBefore lower : List UInt8)
    (heapId : GName) (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory) (input output : List UInt8) (raised : Bool)
    (contCode : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (s : Stuckness) (E : CoPset) (Φ : ObservableOutcome → HeapIProp)
    (hkeysLength : keysBefore.length = randomStateSize)
    (hstate : keysBefore[16]? ≠ some 2)
    (hframe : collectBelowDepth ≤ frame.toNat) :
    iprop(RuntimeContext ∗
      StackPointer frame ∗
      StackBelow frame collectBelowDepth lower ∗
      Slices.ByteSlice 0 randomStateCell keysBefore ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams input output raised ∗
      ((∀ k0 : UInt64, ∀ k1 : UInt64, ∀ tail : List UInt8,
          ∀ lower' : List UInt8, ∀ storedCursor' : UInt32,
          ∀ frontier' : Nat, ∀ history' : AllocationHistory,
          RuntimeContext -∗
          StackPointer frame -∗
          StackBelow frame collectBelowDepth lower' -∗
          pointsTo_u64 0 randomStateCell k0 -∗
          pointsTo_u64 0 (randomStateCell + 8) k1 -∗
          Slices.ByteSlice 0 (randomStateCell + 16) tail -∗
          BumpHeap heapId storedCursor' frontier' history' -∗
          Streams input output raised -∗
          ⌜tail.length = randomStateSize - 16⌝ -∗
          WP (Expr.running
              ⟨collectLocals mapSlot cap frame cur ptr endAddr seed0,
                contCode, arity, remainder, controls, calls⟩ :
              Expr Universal.State) @ s; E [{ Φ }]) ∧
        (∀ remaining' : List UInt8,
          Streams remaining' output true -∗
            Φ (.trapped (.host OOM.trapMessage))))) ⊢
      WP (Expr.running
          ⟨collectLocals mapSlot cap frame cur ptr endAddr seed0,
            .block 0 0 stateGuardBody :: contCode, arity, remainder, controls,
            calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hbelow, Hkeys, Hbump, Hstreams, Hcont⟩
  have hkeys24 : keysBefore.length = 24 := hkeysLength
  have hstore8 : ((0 : UInt32) + 1049528).toNat
      = (0 : UInt32).toNat + (1049528 : UInt32).toNat := by decide
  have hdrop16 : (keysBefore.drop 16).length = 8 := by
    rw [List.length_drop, hkeys24]
  have hcb : collectBelowDepth = 144 := rfl
  have hrd : randomStateDepth = 112 := rfl
  have hdepth : randomStateDepth ≤ frame.toNat := by omega
  obtain ⟨stateByte, tailRest, hcons⟩ :
      ∃ b r, keysBefore.drop 16 = b :: r := by
    cases h : keysBefore.drop 16 with
    | nil => rw [h] at hdrop16; simp at hdrop16
    | cons b r => exact ⟨b, r, rfl⟩
  simp only [stateGuardBody, collectLocals]
  iapply Wasm.SmallStep.twp_block
  simp only [List.drop_nil]
  ihave ⟨Hbyte, Hback⟩ :=
    ByteSlice_state_byte keysBefore stateByte tailRest hkeysLength hcons $$
      Hkeys
  wasm_twp_pures [twp_const]
  wasm_twp_rebind twp_load8U_gen (address := 0) (offset := 1049528)
    stateByte hstore8 with Hbyte
  wasm_twp_pures [twp_const]
  ihave Hkeys := Hback $$ Hbyte
  by_cases hone : stateByte.toUInt32 = (1 : UInt32)
  · -- the seed pair is already there
    iapply twp_eq (result := 1) (by rw [if_pos hone])
    iapply twp_brIf (by decide) (by rfl)
    simp only [List.take_zero, List.nil_append]
    ihave ⟨Hword0, Hword1, Htail⟩ :=
      ByteSlice_as_seed_pair keysBefore hkeysLength $$ Hkeys
    ihave Hnormal := BI.and_elim_l $$ Hcont
    ihave Hexit := Hnormal $$
      %(HashMap.Table.groupWord (keysBefore.take 8))
      %(HashMap.Table.groupWord ((keysBefore.drop 8).take 8))
      %(keysBefore.drop 16) %lower %storedCursor %frontier %history
      Hruntime Hsp Hbelow Hword0 Hword1 Htail Hbump Hstreams %hdrop16
    iexact Hexit
  · -- the first call of the run: absolute `func 16` writes the pair
    iapply twp_eq (result := 0) (by rw [if_neg hone])
    iapply twp_brIfZero
    wasm_twp_pures [twp_const]
    ihave ⟨Hlow, Hown⟩ :=
      frame_split frame collectBelowDepth randomStateDepth lower
        (by decide) $$ Hbelow
    ihave ⟨Hlow, %hlowLength⟩ :=
      StackBelow_length (frame - UInt32.ofNat randomStateDepth)
        (collectBelowDepth - randomStateDepth)
        (lower.take (collectBelowDepth - randomStateDepth)) $$ Hlow
    have Hseed : Func13Spec (hlc := hlc) :=
      Project.RustHashMap.Func13Proof.func13_correct
    unfold Func13Spec CallContract callExpr at Hseed
    simp only [List.cons_append, List.nil_append] at Hseed
    iapply Hseed (sp := frame) (keysBefore := keysBefore)
      (below := lower.drop (collectBelowDepth - randomStateDepth))
      (heapId := heapId) (storedCursor := storedCursor) (frontier := frontier)
      (history := history) (input := input) (output := output)
      (raised := raised)
      (callerLocals :=
        ⟨[.i32 mapSlot, .i32 cap],
          [.i32 frame, .i32 cur, .i32 ptr, .i64 seed0, .i32 endAddr], []⟩)
      (stack := [])
    isplitl_exacts [Hruntime Hsp Hown Hkeys Hbump Hstreams]
    isplitl_pureexact ⟨hkeysLength, hdepth, hstate⟩
    isplit
    · iintro %k0 %k1 %tail %below' %storedCursor' %frontier' %history'
        Hruntime Hsp Hown Hword0 Hword1 Htail Hbump Hstreams %htail
      isimp only [ResumeWP, resumeExpr, List.nil_append]
      wasm_twp_pures [twp_exitControl]
      dsimp only
      simp only [List.take_zero, List.nil_append]
      ihave Hbelow :=
        frame_join frame collectBelowDepth randomStateDepth
          (lower.take (collectBelowDepth - randomStateDepth)) below'
          hlowLength (by decide) $$ [Hlow Hown]
      · iframe Hlow Hown
      ihave Hnormal := BI.and_elim_l $$ Hcont
      ihave Hexit := Hnormal $$ %k0 %k1 %tail
        %(lower.take (collectBelowDepth - randomStateDepth) ++ below')
        %storedCursor' %frontier' %history'
        Hruntime Hsp Hbelow Hword0 Hword1 Htail Hbump Hstreams %htail.1
      iexact Hexit
    · iintro %remaining' Hstreams
      ihave Hoom := BI.and_elim_r $$ Hcont
      ihave Hoom := Hoom $$ %remaining'
      iapply Hoom $$ Hstreams

/-! ## The seeds and the static table -/

/-- WAT 876 to 897: the seed bump and the copy of the static empty table.
Instructions 15 to 36 of the body. -/
@[reducible] def seedCopyPhase (contCode : Program) : Program :=
  .const 0 :: .const 0 :: .load64 1049512 :: .localTee 5 ::
    .constI64 1 :: .addI64 :: .store64 1049512 ::
    .localGet 2 :: .const 0 :: .load64 1048584 :: .store64 16 ::
    .localGet 2 :: .const 0 :: .load64 1048592 :: .store64 24 ::
    .localGet 2 :: .const 0 :: .load64 1049520 :: .store64 40 ::
    .localGet 2 :: .localGet 5 :: .store64 32 :: contCode

/-- The seed phase is instructions 15 to 36 of the body. -/
theorem func2_seed_copy :
    Project.RustHashMap.func2.drop 15
      = seedCopyPhase (Project.RustHashMap.func2.drop 37) := by
  rfl

set_option maxHeartbeats 2000000 in
/-- WAT 876 to 897.  The body reads the seed pair, writes `k0 + 1` back to
the thread-local cell, and copies the sixteen bytes of the static empty
table into the frame at offset 16.  The seeds go to frame offsets 32 and
40, which is where `HashMapAt` keeps them. -/
theorem twp_seed_copy [WasmSmallStepGS hlc Universal.State]
    (mapSlot cap frame cur ptr endAddr : UInt32) (seed0 : UInt64)
    (k0 k1 d0 d1 f16 f24 f32 f40 : UInt64)
    (contCode : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (s : Stuckness) (E : CoPset) (Φ : ObservableOutcome → HeapIProp)
    (hframe : frame.toNat + 48 < UInt32.size) :
    iprop(pointsTo_u64 0 randomStateCell k0 ∗
      pointsTo_u64 0 (randomStateCell + 8) k1 ∗
      pointsTo_u64 0 (entryStackTop + 8) d0 ∗
      pointsTo_u64 0 (entryStackTop + 16) d1 ∗
      pointsTo_u64 0 (frame + 16) f16 ∗
      pointsTo_u64 0 (frame + 24) f24 ∗
      pointsTo_u64 0 (frame + 32) f32 ∗
      pointsTo_u64 0 (frame + 40) f40 ∗
      (iprop(pointsTo_u64 0 randomStateCell (k0 + 1) ∗
          pointsTo_u64 0 (randomStateCell + 8) k1 ∗
          pointsTo_u64 0 (entryStackTop + 8) d0 ∗
          pointsTo_u64 0 (entryStackTop + 16) d1 ∗
          pointsTo_u64 0 (frame + 16) d0 ∗
          pointsTo_u64 0 (frame + 24) d1 ∗
          pointsTo_u64 0 (frame + 32) k0 ∗
          pointsTo_u64 0 (frame + 40) k1) -∗
        WP (Expr.running
            ⟨collectLocals mapSlot cap frame cur ptr endAddr k0, contCode,
              arity, remainder, controls, calls⟩ :
            Expr Universal.State) @ s; E [{ Φ }])) ⊢
      WP (Expr.running
          ⟨collectLocals mapSlot cap frame cur ptr endAddr seed0,
            seedCopyPhase contCode, arity, remainder, controls, calls⟩ :
          Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hk0, Hk1, Hd0, Hd1, H16, H24, H32, H40, Hcont⟩
  have hr0 : (0 : UInt32) + 1049512 = randomStateCell := by decide
  have hr8 : (0 : UInt32) + 1049520 = randomStateCell + 8 := by decide
  have hs0 : (0 : UInt32) + 1048584 = entryStackTop + 8 := by decide
  have hs1 : (0 : UInt32) + 1048592 = entryStackTop + 16 := by decide
  have hra0 := offset_facts64 (0 : UInt32) 1049512 1049512 rfl (by decide)
  have hra8 := offset_facts64 (0 : UInt32) 1049520 1049520 rfl (by decide)
  have hsa0 := offset_facts64 (0 : UInt32) 1048584 1048584 rfl (by decide)
  have hsa1 := offset_facts64 (0 : UInt32) 1048592 1048592 rfl (by decide)
  have hf16 := offset_facts64 frame 16 16 rfl (by omega)
  have hf24 := offset_facts64 frame 24 24 rfl (by omega)
  have hf32 := offset_facts64 frame 32 32 rfl (by omega)
  have hf40 := offset_facts64 frame 40 40 rfl (by omega)
  isimp only [hr0.symm] at Hk0
  isimp only [hr8.symm] at Hk1
  isimp only [hs0.symm] at Hd0
  isimp only [hs1.symm] at Hd1
  simp only [seedCopyPhase, collectLocals]
  wasm_twp_pures [twp_const twp_const]
  wasm_twp_rebind Wasm.SmallStep.twp_load64 (address := 0) (offset := 1049512)
    k0 hra0.1 hra0.2.1 hra0.2.2.1 hra0.2.2.2.1 hra0.2.2.2.2.1
    hra0.2.2.2.2.2.1 hra0.2.2.2.2.2.2.1 hra0.2.2.2.2.2.2.2 with Hk0
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_constI64 twp_addI64]
  wasm_twp_rebind Wasm.SmallStep.twp_store64 (address := 0) (offset := 1049512)
    k0 hra0.1 hra0.2.1 hra0.2.2.1 hra0.2.2.2.1 hra0.2.2.2.2.1
    hra0.2.2.2.2.2.1 hra0.2.2.2.2.2.2.1 hra0.2.2.2.2.2.2.2 with Hk0
  wasm_twp_pures [twp_localGet twp_const]
  wasm_twp_rebind Wasm.SmallStep.twp_load64 (address := 0) (offset := 1048584)
    d0 hsa0.1 hsa0.2.1 hsa0.2.2.1 hsa0.2.2.2.1 hsa0.2.2.2.2.1
    hsa0.2.2.2.2.2.1 hsa0.2.2.2.2.2.2.1 hsa0.2.2.2.2.2.2.2 with Hd0
  wasm_twp_rebind Wasm.SmallStep.twp_store64 (address := frame) (offset := 16)
    f16 hf16.1 hf16.2.1 hf16.2.2.1 hf16.2.2.2.1 hf16.2.2.2.2.1
    hf16.2.2.2.2.2.1 hf16.2.2.2.2.2.2.1 hf16.2.2.2.2.2.2.2 with H16
  wasm_twp_pures [twp_localGet twp_const]
  wasm_twp_rebind Wasm.SmallStep.twp_load64 (address := 0) (offset := 1048592)
    d1 hsa1.1 hsa1.2.1 hsa1.2.2.1 hsa1.2.2.2.1 hsa1.2.2.2.2.1
    hsa1.2.2.2.2.2.1 hsa1.2.2.2.2.2.2.1 hsa1.2.2.2.2.2.2.2 with Hd1
  wasm_twp_rebind Wasm.SmallStep.twp_store64 (address := frame) (offset := 24)
    f24 hf24.1 hf24.2.1 hf24.2.2.1 hf24.2.2.2.1 hf24.2.2.2.2.1
    hf24.2.2.2.2.2.1 hf24.2.2.2.2.2.2.1 hf24.2.2.2.2.2.2.2 with H24
  wasm_twp_pures [twp_localGet twp_const]
  wasm_twp_rebind Wasm.SmallStep.twp_load64 (address := 0) (offset := 1049520)
    k1 hra8.1 hra8.2.1 hra8.2.2.1 hra8.2.2.2.1 hra8.2.2.2.2.1
    hra8.2.2.2.2.2.1 hra8.2.2.2.2.2.2.1 hra8.2.2.2.2.2.2.2 with Hk1
  wasm_twp_rebind Wasm.SmallStep.twp_store64 (address := frame) (offset := 40)
    f40 hf40.1 hf40.2.1 hf40.2.2.1 hf40.2.2.2.1 hf40.2.2.2.2.1
    hf40.2.2.2.2.2.1 hf40.2.2.2.2.2.2.1 hf40.2.2.2.2.2.2.2 with H40
  wasm_twp_pures [twp_localGet twp_localGet]
  wasm_twp_rebind Wasm.SmallStep.twp_store64 (address := frame) (offset := 32)
    f32 hf32.1 hf32.2.1 hf32.2.2.1 hf32.2.2.2.1 hf32.2.2.2.2.1
    hf32.2.2.2.2.2.1 hf32.2.2.2.2.2.2.1 hf32.2.2.2.2.2.2.2 with H32
  isimp only [hr0] at Hk0
  isimp only [hr8] at Hk1
  isimp only [hs0] at Hd0
  isimp only [hs1] at Hd1
  iapply Hcont
  iframe Hk0 Hk1 Hd0 Hd1 H16 H24 H32 H40

end Project.RustHashMap.CollectPrologue
