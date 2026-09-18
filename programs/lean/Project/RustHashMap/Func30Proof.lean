import Project.RustHashMap.VecGrow
import Project.RustHashMap.ImportProofs

/-!
# Proof of the empty marker function

Local `func30` (absolute index 33) has the body `[return]`.  The generated
`finish_grow` calls it before its first allocation.  The proof follows
`Project.Mergesort.ContractProofs.func4_correct`.
-/

namespace Project.RustHashMap.Func30Proof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open Project.RustHashMap.VecGrow
open scoped Wasm.SmallStep.Outcome

private theorem func30_index :
    Project.RustHashMap.«module».funcs[30]? =
      some Project.RustHashMap.func30Def := by rfl

/-- The marker function returns at once and changes nothing. -/
theorem func30_correct [WasmSmallStepGS hlc Universal.State] :
    Func30Spec (hlc := hlc) := by
  unfold Func30Spec CallContract callExpr
  intro callerLocals stack code arity remainder controls calls s E Φ
  iintro ⟨Hruntime, Hcont⟩
  iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
  wasm_twp_bind Wasm.SmallStep.twp_call Project.RustHashMap.«module» 33
      Project.RustHashMap.func30Def (by decide) func30_index with Hmodule =>
      Hmodule
  simp [Project.RustHashMap.func30Def, Project.RustHashMap.func30,
    Function.toLocals, Function.numParams]
  wasm_twp_return_from_call Hmodule [List.take_zero, List.nil_append]
  isimp only [RuntimeContext, ResumeWP, resumeExpr, List.nil_append] at Hcont
  iapply_frame Hcont $$ [Hmodule Henv]

end Project.RustHashMap.Func30Proof
