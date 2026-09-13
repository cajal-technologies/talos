import Project.RustHashMap.Adequacy

/-!
# The four export wrappers that are still open

The five exports of the module are one-instruction wrappers.  Each one
calls its driver and returns.  `Project.RustHashMap.DriverProof` carries
the `map_len` wrapper at absolute function 31.  This file does the other
four, and it states the rule once instead of four times.

| Export | Wrapper | Driver |
| --- | --- | --- |
| `map_contains_key` | 28 | 19 |
| `map_get` | 29 | 21 |
| `map_insert` | 30 | 3 |
| `map_remove` | 32 | 9 |

The four driver contracts are open.  Every theorem here takes one as a
named hypothesis, so none of them carries `@[proves]`.
-/

namespace Project.RustHashMap.ExportWrappers

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open Project.RustHashMap.EntryContracts
open scoped Wasm.SmallStep.Outcome

/-! ## The four driver contracts -/

/-- Local `func16`, absolute index 19, the `map_contains_key` driver.  It
takes the same entry resources as its wrapper, because the wrapper passes
everything through. -/
def Func16Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  EntrySpec (hlc := hlc) 19 Project.RustHashMap.Spec.containsKeyOutput

/-- Local `func18`, absolute index 21, the `map_get` driver. -/
def Func18Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  EntrySpec (hlc := hlc) 21 Project.RustHashMap.Spec.getOutput

/-- Local `func0`, absolute index 3, the `map_insert` driver. -/
def Func0Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  EntrySpec (hlc := hlc) 3 Project.RustHashMap.Spec.insertOutput

/-- Local `func6`, absolute index 9, the `map_remove` driver. -/
def Func6Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  EntrySpec (hlc := hlc) 9 Project.RustHashMap.Spec.removeOutput

/-! ## The wrapper rule -/

/-- A call contract with no operands, taken from an empty frame, is an
entailment at its call site. -/
private theorem callContract_entails [WasmSmallStepGS hlc Universal.State]
    {absoluteIndex arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    {resources : HeapIProp}
    (h : CallContract absoluteIndex [] (⟨[], [], []⟩ : Locals) [] [] arity
      remainder controls calls s E Φ resources) :
    resources ⊢ WP (.running
        ⟨(⟨[], [], []⟩ : Locals), Instruction.call absoluteIndex :: [], arity,
          remainder, controls, calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }] := h

set_option maxHeartbeats 2000000 in
/-- An export wrapper whose body is one call carries the entry contract of
its driver.  The wrapper takes no parameter and returns no result, so the
frame it builds is empty and the resources pass straight through. -/
theorem entrySpec_of_call [WasmSmallStepGS hlc Universal.State]
    (wrapperIndex driverIndex : Nat) (fn : Function)
    (expected : List UInt8 → List UInt8)
    (himports :
      ¬wrapperIndex < Project.RustHashMap.«module».imports.length)
    (hfn : Project.RustHashMap.«module».funcs[
      wrapperIndex - Project.RustHashMap.«module».imports.length]? = some fn)
    (hparams : fn.numParams = 0)
    (harity : fn.results.length = 0)
    (hlocals : fn.toLocals [] = (⟨[], [], []⟩ : Locals))
    (hbody : fn.body = Instruction.call driverIndex :: [])
    (hdriver : EntrySpec (hlc := hlc) driverIndex expected) :
    EntrySpec (hlc := hlc) wrapperIndex expected := by
  unfold EntrySpec CallContract callExpr
  intro heapId input stackBytes dataBytes randomState callerLocals stack code
    arity remainder controls calls s E Φ
  iintro ⟨Hruntime, Hsp, Hstack, Hdata, Hrandom, Hbump, Hstreams, %hlens,
    Hcont, Hoom⟩
  iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
  wasm_twp_bind Wasm.SmallStep.twp_call Project.RustHashMap.«module»
      wrapperIndex fn himports hfn with Hmodule => Hmodule
  simp only [hparams, harity, hlocals, hbody, List.nil_append, List.take_zero,
    List.reverse_nil, List.drop_zero]
  ihave Hruntime : RuntimeContext $$ [Hmodule Henv]
  · isimp only [RuntimeContext]
    iframe
  iapply callContract_entails (hdriver heapId input stackBytes dataBytes
    randomState
    (callerLocals := (⟨[], [], []⟩ : Locals)) (stack := []) (code := [])
    (arity := 0) (remainder := []) (controls := []))
  isplitl_exacts [Hruntime Hsp Hstack Hdata Hrandom Hbump Hstreams]
  isplitl_pureexact hlens
  isplitl [Hcont]
  · iintro Hruntime Hsuccess
    isimp only [ResumeWP, resumeExpr, List.nil_append]
    iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
    wasm_twp_rebind twp_returnFromCallFallthrough with Hmodule
    simp only [List.take_zero, List.nil_append]
    ihave Hruntime : RuntimeContext $$ [Hmodule Henv]
    · isimp only [RuntimeContext]
      iframe
    isimp only [ResumeWP, resumeExpr, List.nil_append] at Hcont
    iapply Hcont $$ Hruntime Hsuccess
  · iexact Hoom

/-! ## The four wrappers -/

private theorem func25_index :
    Project.RustHashMap.«module».funcs[
      28 - Project.RustHashMap.«module».imports.length]? =
      some Project.RustHashMap.func25Def := by rfl

private theorem func26_index :
    Project.RustHashMap.«module».funcs[
      29 - Project.RustHashMap.«module».imports.length]? =
      some Project.RustHashMap.func26Def := by rfl

private theorem func27_index :
    Project.RustHashMap.«module».funcs[
      30 - Project.RustHashMap.«module».imports.length]? =
      some Project.RustHashMap.func27Def := by rfl

private theorem func29_index :
    Project.RustHashMap.«module».funcs[
      32 - Project.RustHashMap.«module».imports.length]? =
      some Project.RustHashMap.func29Def := by rfl

/-- The `map_contains_key` export wrapper.  Its body is one call. -/
theorem func25_correct_of [WasmSmallStepGS hlc Universal.State]
    (hfunc16 : Func16Spec (hlc := hlc)) :
    Func25Spec (hlc := hlc) :=
  entrySpec_of_call 28 19 Project.RustHashMap.func25Def
    Project.RustHashMap.Spec.containsKeyOutput (by decide) func25_index
    rfl rfl rfl rfl hfunc16

/-- The `map_get` export wrapper.  Its body is one call. -/
theorem func26_correct_of [WasmSmallStepGS hlc Universal.State]
    (hfunc18 : Func18Spec (hlc := hlc)) :
    Func26Spec (hlc := hlc) :=
  entrySpec_of_call 29 21 Project.RustHashMap.func26Def
    Project.RustHashMap.Spec.getOutput (by decide) func26_index
    rfl rfl rfl rfl hfunc18

/-- The `map_insert` export wrapper.  Its body is one call. -/
theorem func27_correct_of [WasmSmallStepGS hlc Universal.State]
    (hfunc0 : Func0Spec (hlc := hlc)) :
    Func27Spec (hlc := hlc) :=
  entrySpec_of_call 30 3 Project.RustHashMap.func27Def
    Project.RustHashMap.Spec.insertOutput (by decide) func27_index
    rfl rfl rfl rfl hfunc0

/-- The `map_remove` export wrapper.  Its body is one call. -/
theorem func29_correct_of [WasmSmallStepGS hlc Universal.State]
    (hfunc6 : Func6Spec (hlc := hlc)) :
    Func29Spec (hlc := hlc) :=
  entrySpec_of_call 32 9 Project.RustHashMap.func29Def
    Project.RustHashMap.Spec.removeOutput (by decide) func29_index
    rfl rfl rfl rfl hfunc6

/-! ## The four public lines, conditional on the drivers -/

/-- The public partial contract of `map_contains_key`, conditional on its
driver. -/
theorem mapContainsKey_of_driver
    (hfunc16 : ∀ {hlc : HasLC} [WasmSmallStepGS hlc Universal.State],
      Func16Spec (hlc := hlc)) :
    Project.RustHashMap.Spec.MapContainsKeySpec :=
  Project.RustHashMap.Adequacy.containsKey_of_func25
    (fun {_hlc} [_] => func25_correct_of hfunc16)

/-- The public partial contract of `map_get`, conditional on its driver. -/
theorem mapGet_of_driver
    (hfunc18 : ∀ {hlc : HasLC} [WasmSmallStepGS hlc Universal.State],
      Func18Spec (hlc := hlc)) :
    Project.RustHashMap.Spec.MapGetSpec :=
  Project.RustHashMap.Adequacy.get_of_func26
    (fun {_hlc} [_] => func26_correct_of hfunc18)

/-- The public partial contract of `map_insert`, conditional on its
driver. -/
theorem mapInsert_of_driver
    (hfunc0 : ∀ {hlc : HasLC} [WasmSmallStepGS hlc Universal.State],
      Func0Spec (hlc := hlc)) :
    Project.RustHashMap.Spec.MapInsertSpec :=
  Project.RustHashMap.Adequacy.insert_of_func27
    (fun {_hlc} [_] => func27_correct_of hfunc0)

/-- The public partial contract of `map_remove`, conditional on its
driver. -/
theorem mapRemove_of_driver
    (hfunc6 : ∀ {hlc : HasLC} [WasmSmallStepGS hlc Universal.State],
      Func6Spec (hlc := hlc)) :
    Project.RustHashMap.Spec.MapRemoveSpec :=
  Project.RustHashMap.Adequacy.remove_of_func29
    (fun {_hlc} [_] => func29_correct_of hfunc6)

end Project.RustHashMap.ExportWrappers
