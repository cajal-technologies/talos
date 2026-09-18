import Project.RustHashMap.Func31Proof

/-!
# Proof of the third forwarder of the decode-error subtree

Local `func34`, absolute index 37, passes the buffer record to absolute
`func 34` and returns, at WAT lines 9008 to 9010.  It keeps no frame and
it holds no local.

The theorem is unconditional, because `func31_correct` is.
-/

namespace Project.RustHashMap.Func34Proof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open Project.RustHashMap.EntryContracts
open Project.RustHashMap.BodyContracts
open Project.RustHashMap.FrameCells
open Project.RustHashMap.DropErrorContracts
open scoped Wasm.SmallStep.Outcome

private theorem func34_index :
    Project.RustHashMap.«module».funcs[34]? =
      some Project.RustHashMap.func34Def := by rfl

set_option maxHeartbeats 2000000 in
/-- The forwarder changes nothing that the caller can see. -/
theorem func34_correct [WasmSmallStepGS hlc Universal.State] :
    Func34Spec (hlc := hlc) := by
  unfold Func34Spec CallContract callExpr
  intro sp record capacity ptr length below callerLocals stack code arity
    remainder controls calls s E Φ
  iintro ⟨Hruntime, Hsp, Hbelow, Hrecord, %hfacts, Hcont⟩
  obtain ⟨hspLow, hrecordNowrap⟩ := hfacts
  iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
  simp only [List.cons_append, List.nil_append]
  wasm_twp_rebind Wasm.SmallStep.twp_call Project.RustHashMap.«module» 37
      Project.RustHashMap.func34Def (by decide) func34_index with Hmodule
  simp [Project.RustHashMap.func34Def, Project.RustHashMap.func34,
    Function.toLocals, Function.numParams]
  ihave Hrecord : Slices.ByteSlice 0 record
      (WordCodec.u32le.serialize [capacity, ptr, length]) $$ [Hrecord]
  · isimp only [WordCodec.serialize_cons, WordCodec.serialize_nil,
      List.append_nil]
    iexact Hrecord
  wasm_twp_pures [twp_localGet]
  iclose_map_runtime Hruntime with Hmodule Henv
  have Hdrop : Func31Spec (hlc := hlc) :=
    Project.RustHashMap.Func31Proof.func31_correct
  unfold Func31Spec CallContract callExpr at Hdrop
  simp only [List.cons_append, List.nil_append] at Hdrop
  iapply Hdrop (sp := sp) (record := record) (capacity := capacity)
    (ptr := ptr) (length := length) (below := below)
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

end Project.RustHashMap.Func34Proof
