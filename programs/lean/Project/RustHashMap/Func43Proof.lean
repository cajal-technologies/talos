import Project.RustHashMap.DropErrorContracts
import Project.RustHashMap.FrameCells

/-!
# Proof of the layout body of the decode-error subtree

Local `func43` (absolute index 46) computes the layout of the message
buffer.  It takes a twelve-byte output slot, the buffer record, the
alignment and the element count.  The only caller fixes the alignment and
the count at 1.

The body reads the capacity at `[record]`.  When the capacity is zero it
writes one word, the middle word of the slot.  When the capacity is not
zero it writes three words of its red zone and copies them into the slot,
with one `i32` store and one `i64` block move.

The count is 1, so the zero-count arm at WAT line 9273 is dead.  Both
capacity arms are live, because the caller leaves the capacity abstract.

The body reads the stack pointer and never writes it, so the sixteen bytes
below the pointer stay a red zone.  The contract leaves the content of the
slot abstract and gives back its length alone.

The theorem is unconditional.
-/

namespace Project.RustHashMap.Func43Proof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open Project.RustHashMap.EntryContracts
open Project.RustHashMap.BodyContracts
open Project.RustHashMap.FrameCells
open Project.RustHashMap.DropErrorContracts
open scoped Wasm.SmallStep.Outcome

/-- The shape of a one-word list. -/
private theorem one_word (values : List UInt32) (hlength : values.length = 1) :
    ∃ a : UInt32, values = [a] := by
  rcases values with _ | ⟨a, rest⟩
  · simp at hlength
  rcases rest with _ | ⟨b, rest⟩
  · exact ⟨a, rfl⟩
  · simp at hlength

/-- The shape of a two-word list. -/
private theorem two_words (values : List UInt32) (hlength : values.length = 2) :
    ∃ a b : UInt32, values = [a, b] := by
  rcases values with _ | ⟨a, rest⟩
  · simp at hlength
  rcases rest with _ | ⟨b, rest⟩
  · simp at hlength
  rcases rest with _ | ⟨c, rest⟩
  · exact ⟨a, b, rfl⟩
  · simp at hlength

/-- The shape of a three-word list. -/
private theorem three_words (values : List UInt32)
    (hlength : values.length = 3) :
    ∃ a b c : UInt32, values = [a, b, c] := by
  rcases values with _ | ⟨a, rest⟩
  · simp at hlength
  rcases rest with _ | ⟨b, rest⟩
  · simp at hlength
  rcases rest with _ | ⟨c, rest⟩
  · simp at hlength
  rcases rest with _ | ⟨d, rest⟩
  · exact ⟨a, b, c, rfl⟩
  · simp at hlength

/-- The middle cell of a three-word slot after one store. -/
private theorem set_middle (a b c d : UInt32) :
    [a, b, c].set 1 d = [a, d, c] := rfl

/-- The element count of the only caller is 1, so the product is the
capacity itself. -/
private theorem mul_one_word (capacity : UInt32) : capacity * 1 = capacity := by
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_mul]
  have h1 : (1 : UInt32).toNat = 1 := rfl
  have hlt : capacity.toNat < UInt32.size := capacity.toBitVec.isLt
  rw [h1, Nat.mul_one, Nat.mod_eq_of_lt hlt]

private theorem func43_index :
    Project.RustHashMap.«module».funcs[43]? =
      some Project.RustHashMap.func43Def := by rfl

set_option maxHeartbeats 2000000 in
/-- The layout body leaves the caller with a twelve-byte slot, the record
unchanged and the red zone below the stack pointer. -/
theorem func43_correct [WasmSmallStepGS hlc Universal.State] :
    Func43Spec (hlc := hlc) := by
  unfold Func43Spec CallContract callExpr
  intro sp out record capacity ptr outBefore below callerLocals stack code
    arity remainder controls calls s E Φ
  iintro ⟨Hruntime, Hsp, Hbelow, Hout, Hrecord, %hfacts, Hcont⟩
  obtain ⟨houtLength, hspLow, houtNowrap, hrecordNowrap⟩ := hfacts
  iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
  simp only [List.cons_append, List.nil_append]
  wasm_twp_rebind Wasm.SmallStep.twp_call Project.RustHashMap.«module» 46
      Project.RustHashMap.func43Def (by decide) func43_index with Hmodule
  simp [Project.RustHashMap.func43Def, Project.RustHashMap.func43,
    Function.toLocals, Function.numParams]
  -- the call rule normalizes the record into its two encoded words
  ihave Hrecord : Slices.ByteSlice 0 record
      (WordCodec.u32le.serialize [capacity, ptr]) $$ [Hrecord]
  · isimp only [WordCodec.serialize_cons, WordCodec.serialize_nil,
      List.append_nil]
    iexact Hrecord
  -- the address facts of the red zone, of the slot and of the record
  have hsize32 : UInt32.size = 4294967296 := rfl
  have hspLt : sp.toNat < 4294967296 := sp.toBitVec.isLt
  have hspNat : (16 : Nat) ≤ sp.toNat := hspLow
  have h4nat : (4 : UInt32).toNat = 4 := rfl
  have h8nat : (8 : UInt32).toNat = 8 := rfl
  have h12nat : (12 : UInt32).toNat = 12 := rfl
  have hframeNat : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le sp 16
      (UInt32.le_iff_toNat_le.mpr (by simpa using (by omega : (16 : Nat) ≤ sp.toNat)))]
    rfl
  have hbase16 : sp - UInt32.ofNat redZoneDepth = sp - 16 := by rfl
  obtain ⟨hf4, hf4_1, hf4_2, hf4_3⟩ :=
    offset_facts (sp - 16) 4 4 (by decide) (by omega)
  obtain ⟨hf8, hf8_1, hf8_2, hf8_3⟩ :=
    offset_facts (sp - 16) 8 8 (by decide) (by omega)
  obtain ⟨hf12, hf12_1, hf12_2, hf12_3⟩ :=
    offset_facts (sp - 16) 12 12 (by decide) (by omega)
  have hf64 := offset_facts64 (sp - 16) 4 4 (by decide) (by omega)
  have hout64 := offset_facts64 out 0 0 (by decide) (by omega)
  obtain ⟨hout4, hout4_1, hout4_2, hout4_3⟩ :=
    offset_facts out 4 4 (by decide) (by omega)
  obtain ⟨hout8, hout8_1, hout8_2, hout8_3⟩ :=
    offset_facts out 8 8 (by decide) (by omega)
  obtain ⟨hr0, hr0_1, hr0_2, hr0_3⟩ :=
    offset_facts record 0 0 (by decide) (by omega)
  obtain ⟨hr4, hr4_1, hr4_2, hr4_3⟩ :=
    offset_facts record 4 4 (by decide) (by omega)
  -- the frame pointer, which the body never commits
  isimp only [StackPointer] at Hsp
  wasm_twp_rebind twp_globalGet with Hsp
  wasm_twp_pures [twp_const twp_sub]
  wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  -- the count is 1, so the first guard never branches
  wasm_twp_pures [twp_block twp_block twp_localGet]
  iapply twp_eqz (result := 0) (by decide)
  wasm_twp_pures [twp_brIfZero twp_block twp_localGet]
  ihave Hrecarray := cells_of_ByteSlice record [capacity, ptr] $$ Hrecord
  ihave ⟨Hrec0, Hrec0close⟩ :=
    cell_load record 0 [capacity, ptr] 0 capacity (by simp) rfl (by decide) $$
      Hrecarray
  wasm_twp_rebind twp_load32 (address := record) (offset := 0) capacity
    hr0 hr0_1 hr0_2 hr0_3 with Hrec0
  ihave Hrecarray := Hrec0close $$ Hrec0
  by_cases hcap : capacity = 0
  · -- the empty buffer: the body writes the middle word of the slot alone
    subst hcap
    wasm_twp_pures [twp_brIfZero]
    iapply twp_br (by rfl)
    simp only [List.take_zero, List.nil_append]
    wasm_twp_pures [twp_localGet twp_const]
    ihave ⟨%houtCells, Houtarray⟩ :=
      ByteSlice_as_cells out outBefore 3 (by omega) $$ Hout
    obtain ⟨o0, o1, o2, houtShape⟩ := three_words _ houtCells
    isimp only [houtShape] at Houtarray
    ihave ⟨Houtcell, Houtclose⟩ :=
      cell_focus out 4 [o0, o1, o2] 1 o1 0 (by simp) rfl (by decide) $$
        Houtarray
    wasm_twp_rebind twp_store32 (address := out) (offset := 4) o1
      hout4 hout4_1 hout4_2 hout4_3 with Houtcell
    ihave Houtarray := Houtclose $$ Houtcell
    isimp only [set_middle] at Houtarray
    wasm_twp_pures [twp_exitControl] using [List.take_zero, List.nil_append]
    wasm_twp_return_from_call Hmodule [List.take_zero, List.nil_append]
    ihave Hout :=
      ByteSlice_of_cells out [o0, 0, o2] (by simpa using houtNowrap) $$
        Houtarray
    ihave Hrecord :=
      ByteSlice_of_cells record [0, ptr] (by simpa using hrecordNowrap) $$
        Hrecarray
    wasm_serialize_norm at Hrecord
    ihave Hsp : StackPointer sp $$ [Hsp]
    · unfold StackPointer
      iexact Hsp
    isimp only [RuntimeContext, ResumeWP, resumeExpr, List.nil_append] at Hcont
    ihave Hcont := Hcont $$ %(WordCodec.u32le.serialize [o0, 0, o2]) %below
    iapply Hcont $$ [Hmodule Henv] Hsp Hbelow Hout Hrecord
    · isplitl_exact Hmodule
      · iexact Henv
    ipureintro
    simp
  · -- the live buffer: the body fills the red zone and copies it out
    iapply twp_brIf hcap (by rfl)
    simp only [List.take_zero, List.nil_append]
    -- the red zone, cut into the untouched head, the block and the tail
    ihave ⟨%hbelowLength, Hframe⟩ :=
      StackBelow_base sp (sp - 16) redZoneDepth below hbase16 $$ Hbelow
    have hbelow16 : below.length = 16 := hbelowLength
    have hlenA : ((below.take 12).take 4).length = 4 := by simp [hbelow16]
    have hlenB : ((below.take 12).drop 4).length = 8 := by simp [hbelow16]
    have hlenC : (below.drop 12).length = 4 := by simp [hbelow16]
    have hlit4 : sp - 16 + UInt32.ofNat 4 = sp - 16 + 4 := rfl
    have hlit12 : sp - 16 + UInt32.ofNat 12 = sp - 16 + 12 := rfl
    have hlit8out : out + UInt32.ofNat 8 = out + 8 := rfl
    have haddrB : sp - 16 + 4 + 4 = sp - 16 + 8 := by
      rw [UInt32.add_assoc, show (4 : UInt32) + 4 = 8 from by decide]
    have hlit8B : sp - 16 + 4 + UInt32.ofNat 8 = sp - 16 + 12 := by
      rw [UInt32.add_assoc, show (4 : UInt32) + UInt32.ofNat 8 = 12 from by decide]
    ihave ⟨Hlow12, Hhigh4⟩ :=
      ByteSlice_cut (sp - 16) below 12 (by omega) $$ Hframe
    isimp only [hlit12] at Hhigh4
    ihave ⟨HpartA, HpartB⟩ :=
      ByteSlice_cut (sp - 16) (below.take 12) 4 (by simp [hbelow16]) $$ Hlow12
    isimp only [hlit4] at HpartB
    ihave ⟨%hcellsB, HarrayB⟩ :=
      ByteSlice_as_cells (sp - 16 + 4) ((below.take 12).drop 4) 2 (by omega) $$
        HpartB
    obtain ⟨b0, b1, hshapeB⟩ := two_words _ hcellsB
    isimp only [hshapeB, arrayAt, haddrB] at HarrayB
    icases HarrayB with ⟨Hb0, Hb1, _HnilB⟩
    ihave ⟨%hcellsC, HarrayC⟩ :=
      ByteSlice_as_cells (sp - 16 + 12) (below.drop 12) 1 (by omega) $$ Hhigh4
    obtain ⟨c0, hshapeC⟩ := one_word _ hcellsC
    isimp only [hshapeC, arrayAt] at HarrayC
    icases HarrayC with ⟨Hc0, _HnilC⟩
    -- the slot, cut into the block and the tail word
    have houtLow : (outBefore.take 8).length = 8 := by simp [houtLength]
    have houtHigh : (outBefore.drop 8).length = 4 := by simp [houtLength]
    ihave ⟨HoutLow, HoutHigh⟩ :=
      ByteSlice_cut out outBefore 8 (by omega) $$ Hout
    isimp only [hlit8out] at HoutHigh
    ihave ⟨%hcellsO, HarrayO⟩ :=
      ByteSlice_as_cells (out + 8) (outBefore.drop 8) 1 (by omega) $$ HoutHigh
    obtain ⟨g0, hshapeO⟩ := one_word _ hcellsO
    isimp only [hshapeO, arrayAt] at HarrayO
    icases HarrayO with ⟨Hg0, _HnilO⟩
    ihave HoutWord :=
      ByteSlice_as_word out (out + 0) (outBefore.take 8)
        (by rw [UInt32.add_zero]) houtLow $$ HoutLow
    -- `local 5 := [record]`, `local 6 := 1 * local 5`
    wasm_twp_pures [twp_localGet]
    ihave ⟨Hrec0, Hrec0close⟩ :=
      cell_load record 0 [capacity, ptr] 0 capacity (by simp) rfl (by decide) $$
        Hrecarray
    wasm_twp_rebind twp_load32 (address := record) (offset := 0) capacity
      hr0 hr0_1 hr0_2 hr0_3 with Hrec0
    ihave Hrecarray := Hrec0close $$ Hrec0
    wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceSub, List.set]
    wasm_twp_pures [twp_localGet twp_localGet twp_mul]
      rewriting [mul_one_word capacity]
    wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceSub, List.set]
    -- `[frame + 4] := [record + 4]`
    wasm_twp_pures [twp_localGet twp_localGet]
    ihave ⟨Hrec4, Hrec4close⟩ :=
      cell_load record 4 [capacity, ptr] 1 ptr (by simp) rfl (by decide) $$
        Hrecarray
    wasm_twp_rebind twp_load32 (address := record) (offset := 4) ptr
      hr4 hr4_1 hr4_2 hr4_3 with Hrec4
    ihave Hrecarray := Hrec4close $$ Hrec4
    wasm_twp_rebind twp_store32 (address := sp - 16) (offset := 4) b0
      hf4 hf4_1 hf4_2 hf4_3 with Hb0
    -- `[frame + 8] := 1`
    wasm_twp_pures [twp_localGet twp_localGet]
    wasm_twp_rebind twp_store32 (address := sp - 16) (offset := 8) b1
      hf8 hf8_1 hf8_2 hf8_3 with Hb1
    ihave HarrayB : arrayAt 0 (sp - 16 + 4) [ptr, 1] $$ [Hb0 Hb1]
    · isimp only [arrayAt, haddrB]
      iframe Hb0 Hb1
    ihave HpartB :=
      ByteSlice_of_cells (sp - 16 + 4) [ptr, 1] (by
        simp only [List.length_cons, List.length_nil]
        omega) $$ HarrayB
    ihave HframeWord :=
      ByteSlice_as_word (sp - 16 + 4) (sp - 16 + 4)
        (WordCodec.u32le.serialize [ptr, 1]) rfl (by simp) $$ HpartB
    -- `[frame + 12] := capacity`
    wasm_twp_pures [twp_localGet twp_localGet]
    wasm_twp_rebind twp_store32 (address := sp - 16) (offset := 12) c0
      hf12 hf12_1 hf12_2 hf12_3 with Hc0
    -- `[out + 8] := [frame + 12]`
    wasm_twp_pures [twp_localGet twp_localGet]
    wasm_twp_rebind twp_load32 (address := sp - 16) (offset := 12) capacity
      hf12 hf12_1 hf12_2 hf12_3 with Hc0
    wasm_twp_rebind twp_store32 (address := out) (offset := 8) g0
      hout8 hout8_1 hout8_2 hout8_3 with Hg0
    -- `[out] := [frame + 4]`, one eight-byte block move
    wasm_twp_block_move
      (sp - 16, 4, Wasm.RustStd.HashMap.Table.groupWord
        (WordCodec.u32le.serialize [ptr, 1]), hf64)
      (out, 0, Wasm.RustStd.HashMap.Table.groupWord (outBefore.take 8), hout64)
      with HframeWord HoutWord
    iapply twp_br (by rfl)
    simp only [List.take_zero, List.nil_append]
    wasm_twp_return_from_call Hmodule [List.take_zero, List.nil_append]
    -- put the red zone, the slot and the record back together
    ihave HpartB :=
      ByteSlice_of_word (sp - 16 + 4) (sp - 16 + 4)
        (WordCodec.u32le.serialize [ptr, 1]) rfl (by simp) (by omega) $$
        HframeWord
    ihave HoutLow :=
      ByteSlice_of_word out (out + 0) (WordCodec.u32le.serialize [ptr, 1])
        (by rw [UInt32.add_zero]) (by simp) (by omega) $$ HoutWord
    ihave HarrayC : arrayAt 0 (sp - 16 + 12) [capacity] $$ [Hc0]
    · isimp only [arrayAt]
      iframe Hc0
    ihave Hhigh4 :=
      ByteSlice_of_cells (sp - 16 + 12) [capacity] (by
        simp only [List.length_cons, List.length_nil]
        omega) $$ HarrayC
    ihave HarrayO : arrayAt 0 (out + 8) [capacity] $$ [Hg0]
    · isimp only [arrayAt]
      iframe Hg0
    ihave HoutHigh :=
      ByteSlice_of_cells (out + 8) [capacity] (by
        simp only [List.length_cons, List.length_nil]
        omega) $$ HarrayO
    ihave HpartBC :=
      ByteSlice_glue (sp - 16 + 4) (WordCodec.u32le.serialize [ptr, 1])
        (WordCodec.u32le.serialize [capacity]) 8 (by simp) $$ [HpartB Hhigh4]
    · isplitl_exact HpartB
      · irw_exact [hlit8B] with Hhigh4
    ihave Hframe :=
      ByteSlice_glue (sp - 16) ((below.take 12).take 4)
        (WordCodec.u32le.serialize [ptr, 1]
          ++ WordCodec.u32le.serialize [capacity]) 4 hlenA $$ [HpartA HpartBC]
    · isplitl_exact HpartA
      · irw_exact [hlit4] with HpartBC
    ihave Hbelow :=
      StackBelow_intro sp (sp - 16) redZoneDepth
        ((below.take 12).take 4 ++ (WordCodec.u32le.serialize [ptr, 1]
          ++ WordCodec.u32le.serialize [capacity]))
        (by simp [redZoneDepth, hlenA])
        hbase16 $$ Hframe
    ihave Hout :=
      ByteSlice_glue out (WordCodec.u32le.serialize [ptr, 1])
        (WordCodec.u32le.serialize [capacity]) 8 (by simp) $$
        [HoutLow HoutHigh]
    · isplitl_exact HoutLow
      · irw_exact [hlit8out] with HoutHigh
    ihave Hrecord :=
      ByteSlice_of_cells record [capacity, ptr] (by simpa using hrecordNowrap) $$
        Hrecarray
    wasm_serialize_norm at Hrecord
    ihave Hsp : StackPointer sp $$ [Hsp]
    · unfold StackPointer
      iexact Hsp
    isimp only [RuntimeContext, ResumeWP, resumeExpr, List.nil_append] at Hcont
    ihave Hcont := Hcont
      $$ %(WordCodec.u32le.serialize [ptr, 1]
        ++ WordCodec.u32le.serialize [capacity])
      %((below.take 12).take 4 ++ (WordCodec.u32le.serialize [ptr, 1]
        ++ WordCodec.u32le.serialize [capacity]))
    iapply Hcont $$ [Hmodule Henv] Hsp Hbelow Hout Hrecord
    · isplitl_exact Hmodule
      · iexact Henv
    ipureintro
    simp

end Project.RustHashMap.Func43Proof
