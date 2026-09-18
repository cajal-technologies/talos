import Project.RustHashMap.AllocatorContracts

/-!
# Proof of the hash map deallocator

This module proves local `func57` (absolute index 60) against `Func57Spec`.
The compiled body is empty.  The logical effect moves the live block into
the retired part of `BumpHeap`.  The proof is a port of the mergesort
`func7_correct`.
-/

namespace Project.RustHashMap.Func57Proof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open Project.RustHashMap.Allocator
open Project.RustHashMap.AllocatorContracts
open scoped Wasm.SmallStep.Outcome

private theorem func57_index :
    Project.RustHashMap.«module».funcs[57]? =
      some Project.RustHashMap.func57Def := by rfl

/-- The generated physical deallocator is a Wasm no-op; its authoritative
logical effect transfers the complete live block into retired allocator
ownership exactly once. -/
theorem func57_correct [WasmSmallStepGS hlc Universal.State] :
    Func57Spec (hlc := hlc) := by
  unfold Func57Spec CallContract callExpr
  intro ptr size alignment layout heapId allocationId bytes storedCursor
    frontier history callerLocals stack code arity remainder controls calls s
    E Φ
  iintro ⟨Hruntime, ⟨Hbump, ⟨Hblock, ⟨%_hlayout, Hcont⟩⟩⟩⟩
  iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
  imod BumpHeap_retire heapId storedCursor frontier history allocationId ptr
      layout bytes $$ [Hbump Hblock] with Hbump
  · iframe
  wasm_twp_bind Wasm.SmallStep.twp_call Project.RustHashMap.«module» 60
      Project.RustHashMap.func57Def (by decide)
      func57_index with Hmodule => Hmodule
  simp [Project.RustHashMap.func57Def, Project.RustHashMap.func57,
    Function.toLocals, Function.numParams]
  wasm_twp_rebind Wasm.SmallStep.twp_returnFromCallFallthrough with Hmodule
  simp only [List.take_zero, List.nil_append]
  isimp only [RuntimeContext, ResumeWP, resumeExpr, List.nil_append] at Hcont
  iapply_frame Hcont $$ [Hmodule Henv] Hbump

end Project.RustHashMap.Func57Proof
