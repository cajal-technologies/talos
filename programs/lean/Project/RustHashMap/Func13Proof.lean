import Project.RustHashMap.CollectBodyContracts
import Project.RustHashMap.FrameCells
import Project.RustHashMap.Func80Proof

/-!
# Proof of the `RandomState` thread-local of `collect_entries`

This file proves local `func13`, absolute index 16, WAT lines 2953 to
3018.  `collect_entries` calls it with the literal argument 0, so the
cached-pair branch at WAT 2965 to 2982 never runs and the body takes a
fresh seed pair from absolute `func 83`.

The body stores the pair at 1049512 and 1049520 and the state byte 1 at
1049528.  The guard at WAT 2993 to 2998 panics when the state byte is
already 2, through `call 104` and then `unreachable`, which is neither arm
of the contract.  `Func13Spec` takes `keysBefore[16]? != some 2` as a
precondition for that reason.

The theorem rests on `Func80Proof.func80_correct`, which is itself
unconditional, so this one is unconditional too.

`func 83` gives its two output words back as `pointsTo_u64`, and the frame
that holds them is part of the stack region that the contract returns as
raw bytes.  `u64Bytes` and `ByteSlice_of_u64` name that direction: the
eight bytes of a word are its eight `u64Byte`s, so a word at an address is
a byte slice of length 8 at the same address.
-/

namespace Project.RustHashMap.Func13Proof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open Project.RustHashMap.Allocator
open Project.RustHashMap.AllocatorContracts
open Project.RustHashMap.EntryContracts
open Project.RustHashMap.VecGrow
open Project.RustHashMap.BodyContracts
open Project.RustHashMap.CollectContract
open Project.RustHashMap.CollectBodyContracts
open Project.RustHashMap.FrameCells
open scoped Wasm.SmallStep.Outcome

private theorem func13_index :
    Project.RustHashMap.«module».funcs[13]? =
      some Project.RustHashMap.func13Def := by rfl

/-- A zero-extended byte differs from 2 whenever the byte does. -/
private theorem toUInt32_ne_two {b : UInt8} (h : b ≠ 2) :
    b.toUInt32 ≠ (2 : UInt32) := by
  intro hc
  apply h
  have hh : b.toUInt32.toUInt8 = (2 : UInt32).toUInt8 := by rw [hc]
  simpa using hh

/-- Move a word to an equal address. -/
private theorem pointsTo_u64_address_eq
    [WasmSmallStepGS hlc Universal.State]
    {address address' : UInt32} {value : UInt64}
    (haddress : address = address') :
    pointsTo_u64 0 address value ⊢ pointsTo_u64 0 address' value := by
  rw [haddress]

/-- The eight little-endian bytes of a `u64`. -/
private def u64Bytes (w : UInt64) : List UInt8 :=
  [u64Byte w 0, u64Byte w 1, u64Byte w 2, u64Byte w 3,
    u64Byte w 4, u64Byte w 5, u64Byte w 6, u64Byte w 7]

/-- To own a `u64` is to own its eight bytes. -/
private theorem pointsToBytes_u64Bytes [WasmHeapGS Universal.State]
    (addr : UInt32) (w : UInt64) :
    pointsToBytes 0 addr (u64Bytes w) ⊣⊢ pointsTo_u64 0 addr w := by
  have e2 : addr + 1 + 1 = addr + 2 := by rw [UInt32.add_assoc]; rfl
  have e3 : addr + 2 + 1 = addr + 3 := by rw [UInt32.add_assoc]; rfl
  have e4 : addr + 3 + 1 = addr + 4 := by rw [UInt32.add_assoc]; rfl
  have e5 : addr + 4 + 1 = addr + 5 := by rw [UInt32.add_assoc]; rfl
  have e6 : addr + 5 + 1 = addr + 6 := by rw [UInt32.add_assoc]; rfl
  have e7 : addr + 6 + 1 = addr + 7 := by rw [UInt32.add_assoc]; rfl
  simp only [u64Bytes, pointsToBytes, pointsTo_u64, e2, e3, e4, e5, e6, e7,
    (BI.sep_emp (PROP := IProp (WasmHeapGF Universal.State))).to_eq]
  exact .rfl

/-- An owned word is a byte slice of eight bytes at the same address. -/
private theorem ByteSlice_of_u64 [WasmHeapGS Universal.State]
    (addr : UInt32) (w : UInt64)
    (hbound : addr.toNat + 8 < UInt32.size) :
    pointsTo_u64 0 addr w ⊢ Slices.ByteSlice 0 addr (u64Bytes w) := by
  iintro Hword
  unfold Slices.ByteSlice
  isplitl_pureexact (show addr.toNat + (u64Bytes w).length < UInt32.size by
    simpa [u64Bytes] using hbound)
  iapply (pointsToBytes_u64Bytes addr w).mpr
  iexact Hword

set_option maxHeartbeats 2000000 in
theorem func13_correct [WasmSmallStepGS hlc Universal.State] :
    Func13Spec (hlc := hlc) := by
  unfold Func13Spec CallContract callExpr
  intro sp keysBefore below heapId storedCursor frontier history
    input output raised callerLocals stack code arity remainder controls
    calls s E Φ
  iintro ⟨Hruntime, Hsp, Hbelow, Hkeys, Hbump, Hstreams, %hfacts, Hcont⟩
  obtain ⟨hkeysLength, hspLow, hstateFact⟩ := hfacts
  iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
  simp only [List.cons_append, List.nil_append]
  wasm_twp_rebind Wasm.SmallStep.twp_call Project.RustHashMap.«module» 16
      Project.RustHashMap.func13Def (by decide) func13_index with Hmodule
  simp [Project.RustHashMap.func13Def, Project.RustHashMap.func13,
    Function.toLocals, Function.numParams]
  -- arithmetic on the frame base and on the thread-local cells
  have hsize32 : UInt32.size = 4294967296 := rfl
  have hspLt : sp.toNat < 4294967296 := sp.toBitVec.isLt
  have hdepth : randomStateDepth = 112 := rfl
  have hsd : seedSourceDepth = 32 := rfl
  have hrs : randomStateSize = 24 := rfl
  have hkeys24 : keysBefore.length = 24 := hkeysLength.trans hrs
  have hspNat : (112 : Nat) ≤ sp.toNat := by
    rw [hdepth] at hspLow; exact hspLow
  have hframeNat : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le sp 16
      (UInt32.le_iff_toNat_le.mpr
        (by simpa using (by omega : (16 : Nat) ≤ sp.toNat)))]
    rfl
  have hbase16 : sp - UInt32.ofNat 16 = sp - 16 := rfl
  have hlit8f : sp - 16 + UInt32.ofNat 8 = sp - 16 + 8 := rfl
  have hk8 : randomStateCell + UInt32.ofNat 8 = randomStateCell + 8 := rfl
  have hk16 : randomStateCell + UInt32.ofNat 16 = randomStateCell + 16 := rfl
  have hk17 : randomStateCell + (16 : UInt32) + UInt32.ofNat 1
      = randomStateCell + 17 := by decide
  have hcell0 : (0 : UInt32) + 1049512 = randomStateCell := by decide
  have hcell8 : (0 : UInt32) + 1049520 = randomStateCell + 8 := by decide
  have hcell16 : (0 : UInt32) + 1049528 = randomStateCell + 16 := by decide
  have hcell16' : randomStateCell + (16 : UInt32) = (0 : UInt32) + 1049528 :=
    hcell16.symm
  have hstore8 : ((0 : UInt32) + 1049528).toNat
      = (0 : UInt32).toNat + (1049528 : UInt32).toNat := by decide
  have hra0 := offset_facts64 (0 : UInt32) 1049512 1049512 rfl (by decide)
  have hra8 := offset_facts64 (0 : UInt32) 1049520 1049520 rfl (by decide)
  have hfa0 := offset_facts64 (sp - 16) 0 0 rfl (by omega)
  have hfa8 := offset_facts64 (sp - 16) 8 8 rfl (by omega)
  have hfa8Nat : (sp - 16 + (8 : UInt32)).toNat = (sp - 16).toNat + 8 := by
    rw [hfa8.1]; rfl
  -- the thread-local region: two words, the state byte, and the rest
  have hdrop16 : (keysBefore.drop 16).length = 8 := by
    rw [List.length_drop, hkeys24]
  obtain ⟨stateByte, tailRest, hcons⟩ :
      ∃ b r, keysBefore.drop 16 = b :: r := by
    cases h : keysBefore.drop 16 with
    | nil => rw [h] at hdrop16; simp at hdrop16
    | cons b r => exact ⟨b, r, rfl⟩
  have hstateNe : stateByte ≠ 2 := by
    intro h
    apply hstateFact
    rw [← List.head?_drop, hcons, List.head?_cons, h]
  have hrestLength : tailRest.length = 7 := by
    rw [hcons] at hdrop16; simpa using hdrop16
  have htake1 : (stateByte :: tailRest).take 1 = [stateByte] := rfl
  have hdrop1 : (stateByte :: tailRest).drop 1 = tailRest := rfl
  have htake16 : (keysBefore.take 16).length = 16 := by
    rw [List.length_take, hkeys24]; omega
  have hword0 : ((keysBefore.take 16).take 8).length = 8 := by
    rw [List.length_take, htake16]; omega
  have hword1 : ((keysBefore.take 16).drop 8).length = 8 := by
    rw [List.length_drop, htake16]
  ihave ⟨Hhead, Htail⟩ :=
    ByteSlice_cut randomStateCell keysBefore 16 (by omega) $$ Hkeys
  isimp only [hk16, hcons] at Htail
  ihave ⟨Hword0, Hword1⟩ :=
    ByteSlice_cut randomStateCell (keysBefore.take 16) 8 (by omega) $$ Hhead
  isimp only [hk8] at Hword1
  ihave ⟨Hstate, Hrest⟩ :=
    ByteSlice_cut (randomStateCell + 16) (stateByte :: tailRest) 1
      (by simp) $$ Htail
  isimp only [htake1] at Hstate
  isimp only [hk17, hdrop1] at Hrest
  ihave ⟨%hstateBound, Hstatebyte⟩ :=
    (Slices.ByteSlice_singleton 0 (randomStateCell + 16) stateByte).mp $$
      Hstate
  -- the frame, committed
  isimp only [StackPointer] at Hsp
  wasm_twp_rebind twp_globalGet with Hsp
  wasm_twp_pures [twp_const twp_sub]
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_rebind twp_globalSet with Hsp
  -- the own frame, then the region that `func 83` gets
  ihave ⟨Hbelow, %hbelowLength⟩ :=
    StackBelow_length sp randomStateDepth below $$ Hbelow
  ihave ⟨Hlower, Hframe⟩ :=
    frame_split sp randomStateDepth 16 below (by decide) $$ Hbelow
  isimp only [hbase16] at Hlower
  ihave ⟨%hframeLength, Hframe⟩ :=
    StackBelow_base sp (sp - 16) 16 (below.drop (randomStateDepth - 16))
      hbase16 $$ Hframe
  have hlowerLength :
      (below.take (randomStateDepth - 16)).length = randomStateDepth - 16 := by
    rw [List.length_take, hbelowLength]
    omega
  ihave ⟨Hdeep, Hseed⟩ :=
    frame_split (sp - 16) (randomStateDepth - 16) seedSourceDepth
      (below.take (randomStateDepth - 16)) (by decide) $$ Hlower
  have hdeepLength :
      ((below.take (randomStateDepth - 16)).take
          (randomStateDepth - 16 - seedSourceDepth)).length
        = randomStateDepth - 16 - seedSourceDepth := by
    rw [List.length_take, hlowerLength]
    omega
  -- the cached-pair branch is dead: the argument is 0
  wasm_twp_pures [twp_block twp_block twp_localGet]
  iapply twp_eqz (result := 1) (by simp)
  iapply twp_brIf (by decide) (by rfl)
  simp only [List.take_zero, List.drop_zero, List.nil_append]
  -- `call 83`, the seed source
  ihave Hsp : StackPointer (sp - 16) $$ [Hsp]
  · unfold StackPointer
    iexact Hsp
  have Hseeds : Func80Spec (hlc := hlc) :=
    Project.RustHashMap.Func80Proof.func80_correct
  unfold Func80Spec CallContract callExpr at Hseeds
  simp only [List.cons_append, List.nil_append] at Hseeds
  wasm_twp_pures [twp_localGet]
  iapply Hseeds (sp := sp - 16) (out := sp - 16)
    (outBefore := below.drop (randomStateDepth - 16))
    (below := (below.take (randomStateDepth - 16)).drop
      (randomStateDepth - 16 - seedSourceDepth))
    (heapId := heapId) (storedCursor := storedCursor) (frontier := frontier)
    (history := history) (input := input) (output := output)
    (raised := raised)
    (callerLocals :=
      { params := [.i32 0]
        locals := [.i32 (sp - 16), ValueType.i32.zero, ValueType.i64.zero,
          ValueType.i64.zero]
        values := [] })
    (stack := [])
  isplitl [Hmodule Henv]
  · unfold RuntimeContext
    iframe Hmodule Henv
  isplitl_exacts [Hsp Hseed Hframe Hbump Hstreams]
  isplitl_pureexact ⟨hframeLength, by rw [hsd]; omega, by omega⟩
  isplit
  · iintro %k0 %k1 %seedAfter %storedCursor' %frontier' %history'
      Hruntime Hsp Hseed Hword0Out Hword1Out Hbump Hstreams
    isimp only [ResumeWP, resumeExpr, List.nil_append]
    iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
    isimp only [StackPointer] at Hsp
    -- `local 3 := [frame + 8]`, then `local 4 := [frame]`
    wasm_twp_pures [twp_localGet]
    wasm_twp_rebind Wasm.SmallStep.twp_load64 (address := sp - 16)
      (offset := 8) k1
      hfa8.1 hfa8.2.1 hfa8.2.2.1 hfa8.2.2.2.1 hfa8.2.2.2.2.1
      hfa8.2.2.2.2.2.1 hfa8.2.2.2.2.2.2.1 hfa8.2.2.2.2.2.2.2 with Hword1Out
    wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceSub, List.set]
    wasm_twp_pures [twp_localGet]
    ihave Hword0Out :=
      pointsTo_u64_address_eq (UInt32.add_zero (sp - 16)).symm $$ Hword0Out
    wasm_twp_rebind Wasm.SmallStep.twp_load64 (address := sp - 16)
      (offset := 0) k0
      hfa0.1 hfa0.2.1 hfa0.2.2.1 hfa0.2.2.2.1 hfa0.2.2.2.2.1
      hfa0.2.2.2.2.2.1 hfa0.2.2.2.2.2.2.1 hfa0.2.2.2.2.2.2.2 with Hword0Out
    wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceSub, List.set]
    wasm_twp_pures [twp_exitControl]
    simp only [List.take_zero, List.nil_append]
    -- the panic guard: the state byte is not 2
    wasm_twp_pures [twp_block twp_const]
    isimp only [hcell16'] at Hstatebyte
    wasm_twp_rebind twp_load8U_gen (address := 0) (offset := 1049528)
      stateByte hstore8 with Hstatebyte
    wasm_twp_pures [twp_const]
    iapply twp_ne (result := 1) (by rw [if_pos (toUInt32_ne_two hstateNe)])
    iapply twp_brIf (by decide) (by rfl)
    simp only [List.take_zero, List.drop_zero, List.nil_append]
    -- `[1049528] := 1`
    wasm_twp_pures [twp_const twp_const]
    wasm_twp_rebind twp_store8_gen (address := 0) (offset := 1049528)
      stateByte hstore8 with Hstatebyte
    -- `[1049520] := local 3`, then `[1049512] := local 4`
    ihave Hcell1 :=
      ByteSlice_as_word (randomStateCell + 8) ((0 : UInt32) + 1049520)
        ((keysBefore.take 16).drop 8) hcell8 hword1 $$ Hword1
    ihave Hcell0 :=
      ByteSlice_as_word randomStateCell ((0 : UInt32) + 1049512)
        ((keysBefore.take 16).take 8) hcell0 hword0 $$ Hword0
    wasm_twp_pures [twp_const twp_localGet]
    wasm_twp_rebind Wasm.SmallStep.twp_store64 (address := 0)
      (offset := 1049520)
      (Wasm.RustStd.HashMap.Table.groupWord ((keysBefore.take 16).drop 8))
      hra8.1 hra8.2.1 hra8.2.2.1 hra8.2.2.2.1 hra8.2.2.2.2.1
      hra8.2.2.2.2.2.1 hra8.2.2.2.2.2.2.1 hra8.2.2.2.2.2.2.2 with Hcell1
    wasm_twp_pures [twp_const twp_localGet]
    wasm_twp_rebind Wasm.SmallStep.twp_store64 (address := 0)
      (offset := 1049512)
      (Wasm.RustStd.HashMap.Table.groupWord ((keysBefore.take 16).take 8))
      hra0.1 hra0.2.1 hra0.2.2.1 hra0.2.2.2.1 hra0.2.2.2.2.1
      hra0.2.2.2.2.2.1 hra0.2.2.2.2.2.2.1 hra0.2.2.2.2.2.2.2 with Hcell0
    -- restore the stack pointer and return
    wasm_twp_pures [twp_localGet twp_const twp_add]
    rw [show (16 : UInt32) + (sp - 16) = sp by
      rw [UInt32.add_comm, UInt32.sub_add_cancel]]
    wasm_twp_rebind twp_globalSet with Hsp
    wasm_twp_rebind twp_returnFromCallFallthrough with Hmodule
    simp only [List.take_zero, List.nil_append]
    -- rebuild the state byte and the trailing bytes
    ihave Hstate :=
      (Slices.ByteSlice_singleton 0 (randomStateCell + 16)
        ((1 : UInt32).toUInt8)).mpr $$ [Hstatebyte]
    · isplitl_pureexact hstateBound
      irw_exact [hcell16'] with Hstatebyte
    ihave Htail :=
      ByteSlice_glue (randomStateCell + 16) [(1 : UInt32).toUInt8] tailRest 1
        rfl $$ [Hstate Hrest]
    · isplitl_exact Hstate
      · irw_exact [hk17] with Hrest
    -- rebuild the frame from the two words that `func 83` wrote
    isimp only [UInt32.add_zero] at Hword0Out
    ihave Hfr0 :=
      ByteSlice_of_u64 (sp - 16) k0 (by omega) $$ Hword0Out
    ihave Hfr1 :=
      ByteSlice_of_u64 (sp - 16 + 8) k1 (by omega) $$ Hword1Out
    ihave Hframe :=
      ByteSlice_glue (sp - 16) (u64Bytes k0) (u64Bytes k1) 8 rfl $$
        [Hfr0 Hfr1]
    · isplitl_exact Hfr0
      · irw_exact [hlit8f] with Hfr1
    ihave Hframe :=
      StackBelow_intro sp (sp - 16) 16 (u64Bytes k0 ++ u64Bytes k1)
        (by simp [u64Bytes]) hbase16 $$ Hframe
    -- rebuild the region below the frame
    ihave Hlower :=
      frame_join (sp - 16) (randomStateDepth - 16) seedSourceDepth
        ((below.take (randomStateDepth - 16)).take
          (randomStateDepth - 16 - seedSourceDepth))
        seedAfter hdeepLength (by decide) $$ [Hdeep Hseed]
    · isplitl_exact Hdeep
      · iexact Hseed
    ihave ⟨Hlower, %hjoinLength⟩ :=
      StackBelow_length (sp - 16) (randomStateDepth - 16)
        ((below.take (randomStateDepth - 16)).take
          (randomStateDepth - 16 - seedSourceDepth) ++ seedAfter) $$ Hlower
    isimp only [← hbase16] at Hlower
    ihave Hbelow :=
      frame_join sp randomStateDepth 16
        ((below.take (randomStateDepth - 16)).take
          (randomStateDepth - 16 - seedSourceDepth) ++ seedAfter)
        (u64Bytes k0 ++ u64Bytes k1) hjoinLength (by decide) $$
        [Hlower Hframe]
    · isplitl_exact Hlower
      · iexact Hframe
    ihave Hsp : StackPointer sp $$ [Hsp]
    · unfold StackPointer
      iexact Hsp
    isimp only [hcell0, hcell8] at Hcell0 Hcell1
    iclose_map_runtime Hruntime with Hmodule Henv
    have htailFacts :
        ([(1 : UInt32).toUInt8] ++ tailRest).length = randomStateSize - 16 ∧
          ([(1 : UInt32).toUInt8] ++ tailRest).head? = some 1 := by
      refine ⟨?_, rfl⟩
      rw [List.length_append, hrestLength]
      rfl
    ihave Hnormal := BI.and_elim_l $$ Hcont
    ihave Hnormal := Hnormal $$ %k0 %k1
      %([(1 : UInt32).toUInt8] ++ tailRest)
      %(((below.take (randomStateDepth - 16)).take
          (randomStateDepth - 16 - seedSourceDepth) ++ seedAfter)
        ++ (u64Bytes k0 ++ u64Bytes k1))
      %storedCursor' %frontier' %history'
    isimp only [ResumeWP, resumeExpr, List.nil_append] at Hnormal
    iapply Hnormal $$ Hruntime Hsp Hbelow Hcell0 Hcell1 Htail Hbump Hstreams
      %htailFacts
  · iintro %remaining' Hstreams
    ihave Hoom := BI.and_elim_r $$ Hcont
    ihave Hoom := Hoom $$ %remaining'
    iapply Hoom $$ Hstreams

end Project.RustHashMap.Func13Proof
