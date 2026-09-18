import Project.RustHashMap.Func42Proof

/-!
# Proof of the first forwarder of the decode-error subtree

Local `func38` (absolute index 41) takes the buffer record and calls
absolute `func 45` with the alignment and the element size fixed at 1, at
WAT lines 9059 to 9064.  It keeps no frame of its own.

The theorem is unconditional, because `func42_correct` is.
-/

namespace Project.RustHashMap.Func38Proof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open Project.RustHashMap.EntryContracts
open Project.RustHashMap.BodyContracts
open Project.RustHashMap.FrameCells
open Project.RustHashMap.DropErrorContracts
open scoped Wasm.SmallStep.Outcome

private theorem func38_index :
    Project.RustHashMap.«module».funcs[38]? =
      some Project.RustHashMap.func38Def := by rfl

set_option maxHeartbeats 2000000 in
/-- The forwarder changes nothing that the caller can see. -/
theorem func38_correct [WasmSmallStepGS hlc Universal.State] :
    Func38Spec (hlc := hlc) := by
  unfold Func38Spec CallContract callExpr
  intro sp record capacity ptr below callerLocals stack code arity remainder
    controls calls s E Φ
  iintro ⟨Hruntime, Hsp, Hbelow, Hrecord, %hfacts, Hcont⟩
  obtain ⟨hspLow, hrecordNowrap⟩ := hfacts
  iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
  simp only [List.cons_append, List.nil_append]
  wasm_twp_rebind Wasm.SmallStep.twp_call Project.RustHashMap.«module» 41
      Project.RustHashMap.func38Def (by decide) func38_index with Hmodule
  simp [Project.RustHashMap.func38Def, Project.RustHashMap.func38,
    Function.toLocals, Function.numParams]
  ihave Hrecord : Slices.ByteSlice 0 record
      (WordCodec.u32le.serialize [capacity, ptr]) $$ [Hrecord]
  · isimp only [WordCodec.serialize_cons, WordCodec.serialize_nil,
      List.append_nil]
    iexact Hrecord
  wasm_twp_pures [twp_const]
  wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet]
  iclose_map_runtime Hruntime with Hmodule Henv
  have Hdrop : Func42Spec (hlc := hlc) :=
    Project.RustHashMap.Func42Proof.func42_correct
  unfold Func42Spec CallContract callExpr at Hdrop
  simp only [List.cons_append, List.nil_append] at Hdrop
  iapply Hdrop (sp := sp) (record := record) (capacity := capacity)
    (ptr := ptr) (below := below)
    (callerLocals :=
      { params := [.i32 record], locals := [.i32 1], values := [] })
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

end Project.RustHashMap.Func38Proof
