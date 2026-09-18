import Project.RustHashMap.Func34Proof

/-!
# Proof of the representation test of the decode-error subtree

Local `func33`, absolute index 36, reads word 0 of the error record and
compares it with `0x80000000`, at WAT lines 8986 to 9006.  The comparison
goes into local 1, and the mask, the `select` and the `eqz` turn it back
into the branch condition of the block.

A simple error keeps `0x80000000` in word 0 and owns no buffer, so the
branch leaves the block at once.  Every other value means the error owns
a buffer, and the body passes the record to absolute `func 37`.

The theorem is unconditional, because `func34_correct` is.
-/

namespace Project.RustHashMap.Func33Proof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open Project.RustHashMap.EntryContracts
open Project.RustHashMap.BodyContracts
open Project.RustHashMap.FrameCells
open Project.RustHashMap.DropErrorContracts
open scoped Wasm.SmallStep.Outcome

/-- The mask of the flag keeps a set flag. -/
private theorem and_one_one : (1 : UInt32) &&& 1 = 1 := by decide

/-- The mask of the flag keeps a clear flag. -/
private theorem and_zero_one : (0 : UInt32) &&& 1 = 0 := by decide

private theorem func33_index :
    Project.RustHashMap.«module».funcs[33]? =
      some Project.RustHashMap.func33Def := by rfl

set_option maxHeartbeats 2000000 in
/-- The test changes nothing that the caller can see. -/
theorem func33_correct [WasmSmallStepGS hlc Universal.State] :
    Func33Spec (hlc := hlc) := by
  unfold Func33Spec CallContract callExpr
  intro sp record capacity ptr length below callerLocals stack code arity
    remainder controls calls s E Φ
  iintro ⟨Hruntime, Hsp, Hbelow, Hrecord, %hfacts, Hcont⟩
  obtain ⟨hspLow, hrecordNowrap⟩ := hfacts
  have hsize32 : UInt32.size = 4294967296 := rfl
  obtain ⟨hr0, hr0_1, hr0_2, hr0_3⟩ :=
    offset_facts record 0 0 rfl (by omega)
  iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
  simp only [List.cons_append, List.nil_append]
  wasm_twp_rebind Wasm.SmallStep.twp_call Project.RustHashMap.«module» 36
      Project.RustHashMap.func33Def (by decide) func33_index with Hmodule
  simp [Project.RustHashMap.func33Def, Project.RustHashMap.func33,
    Function.toLocals, Function.numParams]
  ihave Hrecord : Slices.ByteSlice 0 record
      (WordCodec.u32le.serialize [capacity, ptr, length]) $$ [Hrecord]
  · isimp only [WordCodec.serialize_cons, WordCodec.serialize_nil,
      List.append_nil]
    iexact Hrecord
  -- word 0 of the record carries the representation flag
  ihave Hrecarray :=
    cells_of_ByteSlice record [capacity, ptr, length] $$ Hrecord
  wasm_twp_pures [twp_localGet]
  ihave ⟨Hword0, Hclose⟩ :=
    cell_load record 0 [capacity, ptr, length] 0 capacity (by simp) rfl rfl $$
      Hrecarray
  wasm_twp_rebind twp_load32 (address := record) (offset := 0) capacity
    hr0 hr0_1 hr0_2 hr0_3 with Hword0
  ihave Hrecarray := Hclose $$ Hword0
  ihave Hrecord :=
    ByteSlice_of_cells record [capacity, ptr, length] (by
      simp only [List.length_cons, List.length_nil]
      omega) $$ Hrecarray
  wasm_twp_pures [twp_const]
  by_cases hsimple : capacity = 2147483648
  · -- the simple error: the branch leaves the block
    iapply twp_eq (result := 1) (by rw [if_pos hsimple])
    wasm_twp_localSet
    wasm_twp_pures [twp_block]
    simp only [List.drop_zero]
    wasm_twp_pures [twp_const twp_const twp_localGet twp_const twp_and]
      using [and_one_one]
    iapply twp_select (selected := .i32 0)
      (by rw [if_pos (by decide : (1 : UInt32) ≠ 0)])
    iapply twp_eqz (result := 1) (by decide)
    iapply twp_brIf (by decide : (1 : UInt32) ≠ 0) (by rfl)
    simp only [List.take_zero, List.nil_append]
    wasm_twp_return_from_call Hmodule [List.take_zero, List.nil_append]
    wasm_serialize_norm at Hrecord
    isimp only [RuntimeContext, ResumeWP, resumeExpr, List.nil_append] at Hcont
    ihave Hcont := Hcont $$ %below
    iapply Hcont $$ [Hmodule Henv] Hsp Hbelow Hrecord
    · isplitl_exact Hmodule
      · iexact Henv
  · -- the error owns a buffer: the body forwards the record
    iapply twp_eq (result := 0) (by rw [if_neg hsimple])
    wasm_twp_localSet
    wasm_twp_pures [twp_block]
    simp only [List.drop_zero]
    wasm_twp_pures [twp_const twp_const twp_localGet twp_const twp_and]
      using [and_zero_one]
    iapply twp_select (selected := .i32 1)
      (by rw [if_neg (by decide : ¬ (0 : UInt32) ≠ 0)])
    iapply twp_eqz (result := 0) (by decide)
    iapply twp_brIfZero
    wasm_twp_pures [twp_localGet]
    iclose_map_runtime Hruntime with Hmodule Henv
    have Hfwd : Func34Spec (hlc := hlc) :=
      Project.RustHashMap.Func34Proof.func34_correct
    unfold Func34Spec CallContract callExpr at Hfwd
    simp only [List.cons_append, List.nil_append] at Hfwd
    iapply Hfwd (sp := sp) (record := record) (capacity := capacity)
      (ptr := ptr) (length := length) (below := below)
      (callerLocals :=
        { params := [.i32 record], locals := [.i32 0], values := [] })
      (stack := [])
    isplitl_exacts [Hruntime Hsp Hbelow Hrecord]
    isplitl_pureexact ⟨hspLow, hrecordNowrap⟩
    iintro %below' Hruntime Hsp Hbelow Hrecord
    isimp only [ResumeWP, resumeExpr, List.nil_append]
    wasm_twp_pures [twp_exitControl] using [List.take_zero, List.nil_append]
    iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
    wasm_twp_return_from_call Hmodule [List.take_zero, List.nil_append]
    wasm_serialize_norm at Hrecord
    isimp only [RuntimeContext, ResumeWP, resumeExpr, List.nil_append] at Hcont
    ihave Hcont := Hcont $$ %below'
    iapply Hcont $$ [Hmodule Henv] Hsp Hbelow Hrecord
    · isplitl_exact Hmodule
      · iexact Henv

end Project.RustHashMap.Func33Proof
