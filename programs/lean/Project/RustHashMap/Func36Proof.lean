import Project.RustHashMap.DropErrorContracts
import Project.RustHashMap.FrameCells
import CodeLib.SepLogic.SmallStepTotalLiftingBytesTerminal
import CodeLib.SepLogic.SmallStepTotalLoop

/-!
# Proof of the walk of the decode-error subtree

Local `func36`, absolute index 39, walks the elements of the message
buffer, at WAT lines 9017 to 9051.  It reads the pointer at `[record + 4]`
and drops it, reads the length at `[record + 8]`, and then counts from 0 up
to the length in a red zone of 16 bytes.  The element type has no drop
glue, so the loop body only increments the counter.

This is the only loop of the subtree.  The measure is the length minus the
counter, and `Wasm.SmallStep.twp_loop_wf_family` closes it.

The body reads the stack pointer but never commits the new value, so the
16 bytes it uses stay a red zone.  Its own 4-byte counter is the last word
of that zone, and the first three words come back unchanged.
-/

namespace Project.RustHashMap.Func36Proof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open Project.RustHashMap.EntryContracts
open Project.RustHashMap.BodyContracts
open Project.RustHashMap.FrameCells
open Project.RustHashMap.DropErrorContracts
open scoped Wasm.SmallStep.Outcome

/-! ## The fragments of the body -/

/-- The body of the loop, WAT lines 9033 to 9048. -/
private abbrev walkBody : Program :=
  [.localGet 1, .load32 12, .localGet 2, .eq, .const 1, .and, .br_if 1,
    .localGet 1, .localGet 1, .load32 12, .const 1, .add, .store32 12,
    .br 0]

/-- The loop, which is the whole body of the block. -/
private abbrev walkLoop : Program := [.loop 0 0 walkBody]

/-- The locals of the walk.  They do not change over the loop, because the
counter lives in the red zone. -/
private abbrev walkLocals (record sp length : UInt32) : Locals :=
  { params := [.i32 record], locals := [.i32 (sp - 16), .i32 length],
    values := [] }

/-- The control frame of the block that the exit branch targets. -/
private abbrev walkBlock (exitCode : Program) : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0, body := walkLoop,
    continuation := exitCode, belowStack := [] }

/-! ## The arithmetic of the counter -/

/-- The mask of a set answer. -/
private theorem and_one_one : (1 : UInt32) &&& 1 = 1 := by decide

/-- The mask of a clear answer. -/
private theorem and_zero_one : (0 : UInt32) &&& 1 = 0 := by decide

/-- The counter cell is the last of the four. -/
private theorem set_last (a b c d e : UInt32) :
    [a, b, c, d].set 3 e = [a, b, c, e] := rfl

/-- One turn of the counter. -/
private theorem ofNat_succ (i : Nat) :
    1 + UInt32.ofNat i = UInt32.ofNat (i + 1) := by
  rw [UInt32.ofNat_add, UInt32.add_comm]
  rfl

/-- A word is the word of its own natural number. -/
private theorem ofNat_toNat (value : UInt32) :
    UInt32.ofNat value.toNat = value := by
  apply UInt32.toNat_inj.mp
  exact UInt32.toNat_ofNat_of_lt' value.toBitVec.isLt

/-- A counter below the length is not the length. -/
private theorem ofNat_ne_of_lt (i : Nat) (length : UInt32)
    (hlt : i < length.toNat) : UInt32.ofNat i ≠ length := by
  have hsize : UInt32.size = 4294967296 := rfl
  have hlength : length.toNat < 4294967296 := length.toBitVec.isLt
  intro heq
  have hnat := congrArg UInt32.toNat heq
  rw [UInt32.toNat_ofNat_of_lt' (by omega : i < UInt32.size)] at hnat
  omega

/-! ## The loop -/

set_option maxHeartbeats 2000000 in
/-- The counting loop.  It starts at any counter below the length and it
leaves the counter at the length.  Nothing else of the frame moves. -/
private theorem twp_walk_loop [WasmSmallStepGS hlc Universal.State]
    (sp record length a b c : UInt32) (start : Nat)
    {exitCode : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hspLow : 16 ≤ sp.toNat) (hstart : start ≤ length.toNat) :
    iprop(
      arrayAt 0 (sp - 16) [a, b, c, UInt32.ofNat start] ∗
      (arrayAt 0 (sp - 16) [a, b, c, length] -∗
        WP (.running
            ⟨walkLocals record sp length, exitCode, arity, remainder,
              controls, calls⟩ : Expr Universal.State) @ s; E [{ Φ }])) ⊢
      WP (.running
          ⟨walkLocals record sp length, walkLoop, arity, remainder,
            walkBlock exitCode :: controls, calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }] := by
  have hsize32 : UInt32.size = 4294967296 := rfl
  have hspLt : sp.toNat < 4294967296 := sp.toBitVec.isLt
  have hframeNat : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le sp 16
      (UInt32.le_iff_toNat_le.mpr (by simpa using (by omega : (16 : Nat) ≤ sp.toNat)))]
    rfl
  obtain ⟨hf12, hf12_1, hf12_2, hf12_3⟩ :=
    offset_facts (sp - 16) 12 12 (by decide) (by omega)
  iintro ⟨Hcell, Hexit⟩
  simp only [walkLoop]
  iapply Wasm.SmallStep.twp_loop_wf_family
    (ι := Nat) (measure := fun i => length.toNat - i)
    (locals := fun _ => walkLocals record sp length)
    (I := fun i => iprop(
      ⌜i ≤ length.toNat⌝ ∗
      arrayAt 0 (sp - 16) [a, b, c, UInt32.ofNat i] ∗
      (arrayAt 0 (sp - 16) [a, b, c, length] -∗
        WP (.running
            ⟨walkLocals record sp length, exitCode, arity, remainder,
              controls, calls⟩ : Expr Universal.State) @ s; E [{ Φ }])))
    (initial := start)
    (initialLocals := walkLocals record sp length)
    rfl rfl
  · intro i
    iintro Hrec ⟨%hi, Hcell, Hexit⟩
    simp only [Wasm.SmallStep.loopBodyExpr, walkBody, walkLocals]
    by_cases hdone : i = length.toNat
    · -- the counter reached the length: leave the block
      subst hdone
      isimp only [ofNat_toNat] at Hcell
      wasm_twp_pures [twp_localGet]
      ihave ⟨Hcounter, Hclose⟩ :=
        cell_load (sp - 16) 12 [a, b, c, length] 3 length (by simp) rfl
          (by decide) $$ Hcell
      wasm_twp_rebind twp_load32 (address := sp - 16) (offset := 12) length
        hf12 hf12_1 hf12_2 hf12_3 with Hcounter
      ihave Hcell := Hclose $$ Hcounter
      wasm_twp_pures [twp_localGet]
      iapply twp_eq (result := 1) (by rw [if_pos rfl])
      wasm_twp_pures [twp_const twp_and] using [and_one_one]
      iapply twp_brIf (by decide : (1 : UInt32) ≠ 0) (by rfl)
      simp only [walkBlock, List.take_zero, List.nil_append]
      iapply Hexit $$ Hcell
    · -- the counter is below the length: one turn
      have hlt : i < length.toNat := by omega
      have hne : UInt32.ofNat i ≠ length := ofNat_ne_of_lt i length hlt
      wasm_twp_pures [twp_localGet]
      ihave ⟨Hcounter, Hclose⟩ :=
        cell_focus (sp - 16) 12 [a, b, c, UInt32.ofNat i] 3
          (UInt32.ofNat i) (1 + UInt32.ofNat i) (by simp) rfl (by decide) $$
          Hcell
      wasm_twp_rebind twp_load32 (address := sp - 16) (offset := 12)
        (UInt32.ofNat i) hf12 hf12_1 hf12_2 hf12_3 with Hcounter
      wasm_twp_pures [twp_localGet]
      iapply twp_eq (result := 0) (by rw [if_neg hne])
      wasm_twp_pures [twp_const twp_and] using [and_zero_one]
      iapply twp_brIfZero
      wasm_twp_pures [twp_localGet twp_localGet]
      wasm_twp_rebind twp_load32 (address := sp - 16) (offset := 12)
        (UInt32.ofNat i) hf12 hf12_1 hf12_2 hf12_3 with Hcounter
      wasm_twp_pures [twp_const twp_add]
      wasm_twp_rebind twp_store32 (address := sp - 16) (offset := 12)
        (UInt32.ofNat i) hf12 hf12_1 hf12_2 hf12_3 with Hcounter
      ihave Hcell := Hclose $$ Hcounter
      isimp only [set_last, ofNat_succ] at Hcell
      iapply twp_br (by rfl)
      simp only [List.take_zero, List.nil_append]
      ihave Hback := Hrec $$ %(i + 1)
        %(by omega : length.toNat - (i + 1) < length.toNat - i)
      simp only [List.drop_zero]
      iapply Hback
      isplitl_pureexact (by omega : i + 1 ≤ length.toNat)
      isplitl_exacts [Hcell]
      iexact Hexit
  · isplitl_pureexact hstart
    isplitl_exacts [Hcell]
    iexact Hexit

/-! ## The body -/

private theorem func36_index :
    Project.RustHashMap.«module».funcs[36]? =
      some Project.RustHashMap.func36Def := by rfl

set_option maxHeartbeats 2000000 in
/-- The walk changes nothing that the caller can see. -/
theorem func36_correct [WasmSmallStepGS hlc Universal.State] :
    Func36Spec (hlc := hlc) := by
  unfold Func36Spec CallContract callExpr
  intro sp record capacity ptr length below callerLocals stack code arity
    remainder controls calls s E Φ
  iintro ⟨Hruntime, Hsp, Hbelow, Hrecord, %hfacts, Hcont⟩
  obtain ⟨hspLow, hrecordNowrap⟩ := hfacts
  have hsize32 : UInt32.size = 4294967296 := rfl
  have hspLt : sp.toNat < 4294967296 := sp.toBitVec.isLt
  have hspNat : (16 : Nat) ≤ sp.toNat := hspLow
  have hframeNat : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le sp 16
      (UInt32.le_iff_toNat_le.mpr (by simpa using (by omega : (16 : Nat) ≤ sp.toNat)))]
    rfl
  have hbase16 : sp - UInt32.ofNat redZoneDepth = sp - 16 := by rfl
  have hred : redZoneDepth = 16 := rfl
  obtain ⟨hf12, hf12_1, hf12_2, hf12_3⟩ :=
    offset_facts (sp - 16) 12 12 (by decide) (by omega)
  obtain ⟨hr4, hr4_1, hr4_2, hr4_3⟩ :=
    offset_facts record 4 4 (by decide) (by omega)
  obtain ⟨hr8, hr8_1, hr8_2, hr8_3⟩ :=
    offset_facts record 8 8 (by decide) (by omega)
  iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
  simp only [List.cons_append, List.nil_append]
  wasm_twp_rebind Wasm.SmallStep.twp_call Project.RustHashMap.«module» 39
      Project.RustHashMap.func36Def (by decide) func36_index with Hmodule
  simp [Project.RustHashMap.func36Def, Project.RustHashMap.func36,
    Function.toLocals, Function.numParams]
  ihave Hrecord : Slices.ByteSlice 0 record
      (WordCodec.u32le.serialize [capacity, ptr, length]) $$ [Hrecord]
  · isimp only [WordCodec.serialize_cons, WordCodec.serialize_nil,
      List.append_nil]
    iexact Hrecord
  -- the red zone as four word cells
  ihave ⟨%hcount, Hcells⟩ :=
    StackBelow_as_cells sp (sp - 16) redZoneDepth 4 below (by decide)
      hbase16 $$ Hbelow
  obtain ⟨a, b, c, d, hwords⟩ := four_words (Slices.decodeWords below) hcount
  isimp only [hwords] at Hcells
  -- the frame pointer, which the body never commits
  isimp only [StackPointer] at Hsp
  wasm_twp_rebind twp_globalGet with Hsp
  wasm_twp_pures [twp_const twp_sub]
  wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  -- the dropped pointer and the length
  ihave Hrecarray :=
    cells_of_ByteSlice record [capacity, ptr, length] $$ Hrecord
  wasm_twp_pures [twp_localGet]
  ihave ⟨Hptr, Hptrclose⟩ :=
    cell_load record 4 [capacity, ptr, length] 1 ptr (by simp) rfl
      (by decide) $$ Hrecarray
  wasm_twp_rebind twp_load32 (address := record) (offset := 4) ptr
    hr4 hr4_1 hr4_2 hr4_3 with Hptr
  ihave Hrecarray := Hptrclose $$ Hptr
  iapply twp_drop_gen
  wasm_twp_pures [twp_localGet]
  ihave ⟨Hlength, Hlengthclose⟩ :=
    cell_load record 8 [capacity, ptr, length] 2 length (by simp) rfl
      (by decide) $$ Hrecarray
  wasm_twp_rebind twp_load32 (address := record) (offset := 8) length
    hr8 hr8_1 hr8_2 hr8_3 with Hlength
  ihave Hrecarray := Hlengthclose $$ Hlength
  wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  -- the counter starts at zero
  wasm_twp_pures [twp_localGet twp_const]
  ihave ⟨Hcounter, Hcounterset⟩ :=
    cell_focus (sp - 16) 12 [a, b, c, d] 3 d 0 (by simp) rfl (by decide) $$
      Hcells
  wasm_twp_rebind twp_store32 (address := sp - 16) (offset := 12) d
    hf12 hf12_1 hf12_2 hf12_3 with Hcounter
  ihave Hcells := Hcounterset $$ Hcounter
  isimp only [set_last] at Hcells
  -- the loop
  wasm_twp_pures [twp_block]
  simp only [List.drop_zero]
  iapply twp_walk_loop sp record length a b c 0 hspNat (by omega)
  isplitl_exacts [Hcells]
  iintro Hcells
  -- the epilogue gives the region and the record back
  ihave Hbelow :=
    StackBelow_of_cells sp (sp - 16) redZoneDepth 4 [a, b, c, length]
      (by decide) rfl hbase16 (by omega) $$ Hcells
  ihave Hrecord :=
    ByteSlice_of_cells record [capacity, ptr, length] (by
      simp only [List.length_cons, List.length_nil]
      omega) $$ Hrecarray
  ihave Hsp : StackPointer sp $$ [Hsp]
  · unfold StackPointer
    iexact Hsp
  wasm_twp_return_from_call Hmodule [List.take_zero, List.nil_append]
  wasm_serialize_norm at Hrecord
  isimp only [RuntimeContext, ResumeWP, resumeExpr, List.nil_append] at Hcont
  ihave Hcont := Hcont $$ %(WordCodec.u32le.serialize [a, b, c, length])
  iapply Hcont $$ [Hmodule Henv] Hsp Hbelow Hrecord
  · isplitl_exact Hmodule
    · iexact Henv

end Project.RustHashMap.Func36Proof
