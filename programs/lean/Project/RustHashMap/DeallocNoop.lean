import Project.RustHashMap.AllocatorContracts

/-!
# The deallocator as a no-op

`Func57Spec` in `Project.RustHashMap.AllocatorContracts` gives local
`func57` (absolute index 60) its authoritative meaning: it retires a live
block.  A caller that uses that contract must hold a `LiveBlock` for the
pointer that it frees.

The tail of the `map_len` driver frees memory that the caller does not own
a token for.  It drops the hash table with alignment 8, and it frees the
error string and the input buffer on paths where the ownership came from a
callee that this proof treats as a black box.

The compiled body of `func57` is empty, so the function has no effect on
the heap at all.  This module states that weaker contract,
`Func57NoopSpec`, which takes no `LiveBlock` and no `BumpHeap`, and holds
for any pointer, size and alignment.  It is proved from the empty body, so
it costs nothing and it loses nothing: `Func57Spec` stays available for the
callers that do own a block.

Use `Func57NoopSpec` only to step over a free whose memory this proof does
not track.  A free of tracked memory must still go through `Func57Spec`,
because only that contract records the retirement in the allocation
history.
-/

namespace Project.RustHashMap.DeallocNoop

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open Project.RustHashMap.Allocator
open Project.RustHashMap.AllocatorContracts
open scoped Wasm.SmallStep.Outcome

/-- Local `func57`, absolute index 60, seen as a no-op.  The three
arguments are arbitrary.  The caller keeps every resource it had. -/
def Func57NoopSpec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (ptr size alignment : UInt32)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    CallContract 60 [.i32 alignment, .i32 size, .i32 ptr]
      callerLocals stack code arity remainder controls calls s E Φ iprop(
        RuntimeContext ∗
        (RuntimeContext -∗
          ResumeWP [] callerLocals stack code arity remainder controls calls
            s E Φ))

private theorem func57_index :
    Project.RustHashMap.«module».funcs[57]? =
      some Project.RustHashMap.func57Def := by rfl

/-- The generated deallocator has an empty body, so it returns with every
resource of the caller untouched. -/
theorem func57_noop_correct [WasmSmallStepGS hlc Universal.State] :
    Func57NoopSpec (hlc := hlc) := by
  unfold Func57NoopSpec CallContract callExpr
  intro ptr size alignment callerLocals stack code arity remainder controls
    calls s E Φ
  iintro ⟨Hruntime, Hcont⟩
  iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
  wasm_twp_bind Wasm.SmallStep.twp_call Project.RustHashMap.«module» 60
      Project.RustHashMap.func57Def (by decide)
      func57_index with Hmodule => Hmodule
  simp [Project.RustHashMap.func57Def, Project.RustHashMap.func57,
    Function.toLocals, Function.numParams]
  wasm_twp_rebind Wasm.SmallStep.twp_returnFromCallFallthrough with Hmodule
  simp only [List.take_zero, List.nil_append]
  isimp only [RuntimeContext, ResumeWP, resumeExpr, List.nil_append] at Hcont
  iapply_frame Hcont $$ [Hmodule Henv]

end Project.RustHashMap.DeallocNoop
