import Project.RustHashMap.Func36Proof
import Project.RustHashMap.Func37Proof

/-!
# Proof of the drop of the buffer of the decode-error subtree

Local `func32`, absolute index 35, drops the message buffer of the error,
at WAT lines 8980 to 8983.  It calls absolute `func 39` for the walk over
the elements and then absolute `func 40` for the free.

The two callees take different parts of what the body holds.  The walk
takes the 16-byte red zone directly below the stack pointer, so the body
cuts its own 32 bytes and keeps the deeper half.  The free takes the first
two words of the record, so the body cuts the third word off and keeps it.
Both cuts go back together before the body returns.

The theorem is unconditional, because `func36_correct` and
`func37_correct` are.
-/

namespace Project.RustHashMap.Func32Proof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open Project.RustHashMap.EntryContracts
open Project.RustHashMap.BodyContracts
open Project.RustHashMap.FrameCells
open Project.RustHashMap.DropErrorContracts
open scoped Wasm.SmallStep.Outcome

private theorem func32_index :
    Project.RustHashMap.«module».funcs[32]? =
      some Project.RustHashMap.func32Def := by rfl

set_option maxHeartbeats 2000000 in
/-- The drop changes nothing that the caller can see. -/
theorem func32_correct [WasmSmallStepGS hlc Universal.State] :
    Func32Spec (hlc := hlc) := by
  unfold Func32Spec CallContract callExpr
  intro sp record capacity ptr length below callerLocals stack code arity
    remainder controls calls s E Φ
  iintro ⟨Hruntime, Hsp, Hbelow, Hrecord, %hfacts, Hcont⟩
  obtain ⟨hspLow, hrecordNowrap⟩ := hfacts
  have hsize32 : UInt32.size = 4294967296 := rfl
  have hdrop : dropDepth = 32 := rfl
  have hred : redZoneDepth = 16 := rfl
  have hpairLength : (WordCodec.u32le.serialize [capacity, ptr]).length = 8 := by
    simp
  iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
  simp only [List.cons_append, List.nil_append]
  wasm_twp_rebind Wasm.SmallStep.twp_call Project.RustHashMap.«module» 35
      Project.RustHashMap.func32Def (by decide) func32_index with Hmodule
  simp [Project.RustHashMap.func32Def, Project.RustHashMap.func32,
    Function.toLocals, Function.numParams]
  ihave Hrecord : Slices.ByteSlice 0 record
      (WordCodec.u32le.serialize [capacity, ptr, length]) $$ [Hrecord]
  · isimp only [WordCodec.serialize_cons, WordCodec.serialize_nil,
      List.append_nil]
    iexact Hrecord
  -- the walk takes the red zone alone, so the deeper half stays here
  ihave ⟨Hbelow, %hbelowLength⟩ := StackBelow_length sp dropDepth below $$ Hbelow
  ihave ⟨Hlower, Htop⟩ :=
    frame_split sp dropDepth 16 below (by decide) $$ Hbelow
  wasm_twp_pures [twp_localGet]
  iclose_map_runtime Hruntime with Hmodule Henv
  have Hwalk : Func36Spec (hlc := hlc) :=
    Project.RustHashMap.Func36Proof.func36_correct
  unfold Func36Spec CallContract callExpr at Hwalk
  simp only [List.cons_append, List.nil_append] at Hwalk
  iapply Hwalk (sp := sp) (record := record) (capacity := capacity)
    (ptr := ptr) (length := length) (below := below.drop (dropDepth - 16))
    (callerLocals := { params := [.i32 record], locals := [], values := [] })
    (stack := [])
  isimp only [hred]
  isplitl_exacts [Hruntime Hsp Htop Hrecord]
  isplitl_pureexact ⟨by omega, hrecordNowrap⟩
  iintro %walked Hruntime Hsp Htop Hrecord
  isimp only [ResumeWP, resumeExpr, List.nil_append]
  -- the region goes back together for the free
  ihave Hbelow :=
    frame_join sp dropDepth 16 (below.take (dropDepth - 16)) walked
      (by rw [List.length_take, hbelowLength]; omega) (by decide) $$
      [Hlower Htop]
  · isplitl_exact Hlower
    · iexact Htop
  -- the free takes the first two words of the record
  ihave ⟨Hpair, Htail⟩ :=
    (Slices.ByteSlice_append 0 record
        (WordCodec.u32le.serialize [capacity, ptr])
        (WordCodec.u32le.serialize [length])).mp $$ [Hrecord]
  · wasm_serialize_norm at Hrecord
    isimp only [WordCodec.serialize_cons, WordCodec.serialize_nil,
      List.append_nil, List.append_assoc]
    iexact Hrecord
  isimp only [hpairLength] at Htail
  wasm_twp_pures [twp_localGet]
  have Hfree : Func37Spec (hlc := hlc) :=
    Project.RustHashMap.Func37Proof.func37_correct
  unfold Func37Spec CallContract callExpr at Hfree
  simp only [List.cons_append, List.nil_append] at Hfree
  iapply Hfree (sp := sp) (record := record) (capacity := capacity)
    (ptr := ptr) (below := below.take (dropDepth - 16) ++ walked)
    (callerLocals := { params := [.i32 record], locals := [], values := [] })
    (stack := [])
  isplitl_exacts [Hruntime Hsp Hbelow Hpair]
  isplitl_pureexact ⟨hspLow, by omega⟩
  iintro %below' Hruntime Hsp Hbelow Hpair
  isimp only [ResumeWP, resumeExpr, List.nil_append]
  iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
  wasm_twp_return_from_call Hmodule [List.take_zero, List.nil_append]
  ihave Hrecord :=
    ByteSlice_glue record (WordCodec.u32le.serialize [capacity, ptr])
      (WordCodec.u32le.serialize [length]) 8 hpairLength $$ [Hpair Htail]
  · isplitl_exact Hpair
    · iexact Htail
  wasm_serialize_norm at Hrecord
  isimp only [RuntimeContext, ResumeWP, resumeExpr, List.nil_append] at Hcont
  ihave Hcont := Hcont $$ %below'
  iapply Hcont $$ [Hmodule Henv] Hsp Hbelow Hrecord
  · isplitl_exact Hmodule
    · iexact Henv

end Project.RustHashMap.Func32Proof
