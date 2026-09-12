import Project.RustHashMap.Func38Proof

/-!
# Proof of the bare forwarder of the decode-error subtree

Local `func37` (absolute index 40) passes the buffer record straight to
absolute `func 41`, at WAT lines 9053 to 9055.  It keeps no frame and it
holds no local of its own.

The theorem is unconditional, because `func38_correct` is.
-/

namespace Project.RustHashMap.Func37Proof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open Project.RustHashMap.EntryContracts
open Project.RustHashMap.BodyContracts
open Project.RustHashMap.FrameCells
open Project.RustHashMap.DropErrorContracts
open scoped Wasm.SmallStep.Outcome

private theorem func37_index :
    Project.RustHashMap.«module».funcs[37]? =
      some Project.RustHashMap.func37Def := by rfl

set_option maxHeartbeats 2000000 in
/-- The forwarder changes nothing that the caller can see. -/
theorem func37_correct [WasmSmallStepGS hlc Universal.State] :
    Func37Spec (hlc := hlc) := by
  unfold Func37Spec CallContract callExpr
  intro sp record capacity ptr below callerLocals stack code arity remainder
    controls calls s E Φ
  iintro ⟨Hruntime, Hsp, Hbelow, Hrecord, %hfacts, Hcont⟩
  obtain ⟨hspLow, hrecordNowrap⟩ := hfacts
  iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
  simp only [List.cons_append, List.nil_append]
  wasm_twp_rebind Wasm.SmallStep.twp_call Project.RustHashMap.«module» 40
      Project.RustHashMap.func37Def (by decide) func37_index with Hmodule
  simp [Project.RustHashMap.func37Def, Project.RustHashMap.func37,
    Function.toLocals, Function.numParams]
  ihave Hrecord : Slices.ByteSlice 0 record
      (WordCodec.u32le.serialize [capacity, ptr]) $$ [Hrecord]
  · isimp only [WordCodec.serialize_cons, WordCodec.serialize_nil,
      List.append_nil]
    iexact Hrecord
  wasm_twp_pures [twp_localGet]
  iclose_map_runtime Hruntime with Hmodule Henv
  have Hdrop : Func38Spec (hlc := hlc) :=
    Project.RustHashMap.Func38Proof.func38_correct
  unfold Func38Spec CallContract callExpr at Hdrop
  simp only [List.cons_append, List.nil_append] at Hdrop
  iapply Hdrop (sp := sp) (record := record) (capacity := capacity)
    (ptr := ptr) (below := below)
    (callerLocals := { params := [.i32 record], locals := [], values := [] })
    (stack := [])
  isplitl_exacts [Hruntime Hsp Hbelow Hrecord]
  isplitl_pureexact ⟨hspLow, hrecordNowrap⟩
  iintro %below' Hruntime Hsp Hbelow Hrecord
  isimp only [ResumeWP, resumeExpr, List.nil_append]
  iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
  wasm_twp_return_from_call Hmodule [List.take_zero, List.nil_append]
  wasm_serialize_norm at Hrecord
  isimp only [RuntimeContext, ResumeWP, resumeExpr, List.nil_append] at Hcont
  ihave Hcont := Hcont $$ %below'
  iapply Hcont $$ [Hmodule Henv] Hsp Hbelow Hrecord
  · isplitl_exact Hmodule
    · iexact Henv

end Project.RustHashMap.Func37Proof
