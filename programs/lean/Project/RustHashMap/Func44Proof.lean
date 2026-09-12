import Project.RustHashMap.DropErrorContracts
import Project.RustHashMap.DeallocNoop

/-!
# Proof of the free of the decode-error subtree

Local `func44` (absolute index 47) frees the message buffer of the error.
It returns at once when the size is zero, and otherwise calls absolute
`func 60`.

The body of `func 60` is empty, so
`Project.RustHashMap.DeallocNoop.Func57NoopSpec` takes the call with the
runtime context alone.  Both arms of `func44` therefore leave the caller
with exactly what it had, and the contract asks for nothing else.

The theorem is unconditional.
-/

namespace Project.RustHashMap.Func44Proof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open Project.RustHashMap.DeallocNoop
open Project.RustHashMap.DropErrorContracts
open scoped Wasm.SmallStep.Outcome

private theorem func44_index :
    Project.RustHashMap.«module».funcs[44]? =
      some Project.RustHashMap.func44Def := by rfl

set_option maxHeartbeats 2000000 in
/-- The free changes nothing that the caller can see. -/
theorem func44_correct [WasmSmallStepGS hlc Universal.State] :
    Func44Spec (hlc := hlc) := by
  unfold Func44Spec CallContract callExpr
  intro unused ptr alignment size callerLocals stack code arity remainder
    controls calls s E Φ
  iintro ⟨Hruntime, Hcont⟩
  iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
  simp only [List.cons_append, List.nil_append]
  wasm_twp_rebind Wasm.SmallStep.twp_call Project.RustHashMap.«module» 47
      Project.RustHashMap.func44Def (by decide) func44_index with Hmodule
  simp [Project.RustHashMap.func44Def, Project.RustHashMap.func44,
    Function.toLocals, Function.numParams]
  wasm_twp_pures [twp_block twp_localGet]
  by_cases hsize : size = 0
  · -- the empty buffer: the body branches out of the block at once
    iapply twp_eqz (result := 1) (by simp [hsize])
    iapply twp_brIf (by decide : (1 : UInt32) ≠ 0) (by rfl)
    simp only [List.take_zero, List.nil_append]
    wasm_twp_return_from_call Hmodule [List.take_zero, List.nil_append]
    isimp only [RuntimeContext, ResumeWP, resumeExpr, List.nil_append] at Hcont
    iapply Hcont $$ [Hmodule Henv]
    · isplitl_exact Hmodule
      · iexact Henv
  · -- the live buffer: the body calls the empty deallocator
    iapply twp_eqz (result := 0) (by simp [hsize])
    wasm_twp_pures [twp_brIfZero twp_localGet twp_localGet twp_localGet]
    iclose_map_runtime Hruntime with Hmodule Henv
    have Hfree : Func57NoopSpec (hlc := hlc) := func57_noop_correct
    unfold Func57NoopSpec CallContract callExpr at Hfree
    simp only [List.cons_append, List.nil_append] at Hfree
    iapply Hfree (ptr := ptr) (size := size) (alignment := alignment)
      (callerLocals :=
        ⟨[.i32 unused, .i32 ptr, .i32 alignment, .i32 size], [], []⟩)
      (stack := [])
    isplitl_exact Hruntime
    · iintro Hruntime
      isimp only [ResumeWP, resumeExpr, List.nil_append]
      wasm_twp_pures [twp_exitControl] using [List.take_zero, List.nil_append]
      iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
      wasm_twp_return_from_call Hmodule [List.take_zero, List.nil_append]
      isimp only [RuntimeContext, ResumeWP, resumeExpr,
        List.nil_append] at Hcont
      iapply Hcont $$ [Hmodule Henv]
      · isplitl_exact Hmodule
        · iexact Henv

end Project.RustHashMap.Func44Proof
