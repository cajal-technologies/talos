import Interpreter.Wasm.SmallStep
import Interpreter.Wasm.Validate

/-! ## Example: `call_indirect` through a single-entry table

The dispatch proof exposes table lookup, signature agreement, callee entry,
call-frame return, and final completion as one authoritative relational trace.
-/

namespace Wasm
open SmallStep

def Incr : Program := [.localGet 0, .const 1, .add]
def Dispatch : Program := [.localGet 0, .const 0, .callIndirect 0 0]

def callIndirectModule : Module :=
  { types := [{ params := [.i32], results := [.i32] }]
    funcs := [
      { params := [.i32], body := Incr, results := [.i32] },
      { params := [.i32], body := Dispatch, results := [.i32] }]
    tables := [{ min := 1 }]
    elements := [{
      tableIdx := some 0, offset := some 0, funcs := [some 0] }] }

/-- Function-type indices used by `call_indirect` are validated against
`Module.types`, independently of the empty GC type section. -/
theorem callIndirectModule_valid :
    (match callIndirectModule.validate with
      | .ok () => true
      | .error _ => false) = true := by
  native_decide

private def validationAccepts (module : Module) : Bool :=
  match module.validate with
  | .ok () => true
  | .error _ => false

private def validationModuleWith (body : Program) : Module :=
  { types := [{ params := [], results := [] }]
    funcs := [{ body }]
    tables := [{ min := 1 }] }

theorem callIndirect_type_out_of_range_rejected :
    validationAccepts (validationModuleWith [.callIndirect 1 0]) = false := by
  native_decide

theorem returnCallIndirect_type_out_of_range_rejected :
    validationAccepts (validationModuleWith [.returnCallIndirect 1 0]) = false := by
  native_decide

theorem callRef_type_out_of_range_rejected :
    validationAccepts (validationModuleWith [.callRef 1]) = false := by
  native_decide

theorem returnCallRef_type_out_of_range_rejected :
    validationAccepts (validationModuleWith [.returnCallRef 1]) = false := by
  native_decide

theorem gc_type_out_of_range_rejected :
    validationAccepts (validationModuleWith [.gc (.structNew 0)]) = false := by
  native_decide

def incrConfig (st : Store Unit) (n : UInt32) : Config Unit :=
  { expr := .running
      { locals := { params := [.i32 n] }
        code := Incr
        resultArity := 1
        callerRemainder := [] }
    store :=
      { runtime := { instances := #[{ module := callIndirectModule, host := {} }], entry := ⟨0⟩ }
        wasm := st } }

def dispatchConfig (n : UInt32) : Config Unit :=
  { expr := .running
      { locals := { params := [.i32 n] }
        code := Dispatch
        resultArity := 1
        callerRemainder := [] }
    store :=
      { runtime := { instances := #[{ module := callIndirectModule, host := {} }], entry := ⟨0⟩ }
        wasm := callIndirectModule.initialStore } }

theorem incr_steps (st : Store Unit) (n : UInt32) :
    Steps (incrConfig st n)
      [(.instruction (.localGet 0)), (.instruction (.const 1)),
       (.instruction .add), (.administrative .finish)]
      ⟨.done [.i32 (n + 1)], (incrConfig st n).store⟩ := by
  apply Steps.cons (.localGet rfl)
  apply Steps.cons .const
  apply Steps.cons .add
  apply Steps.cons .finish
  simpa [incrConfig, UInt32.add_comm] using
    (Steps.refl
      (⟨.done [.i32 (n + 1)], (incrConfig st n).store⟩ : Config Unit))

theorem incrSpec (st : Store Unit) (n : UInt32) :
    TerminatesWith (incrConfig st n)
      (fun values store =>
        values = [.i32 (n + 1)] ∧ store.wasm = st) := by
  refine ⟨_, _, _, incr_steps st n, rfl, rfl⟩

theorem dispatch_steps (n : UInt32) :
    Steps (dispatchConfig n)
      [(.instruction (.localGet 0)), (.instruction (.const 0)),
       (.instruction (.callIndirect 0 0)),
       (.instruction (.localGet 0)), (.instruction (.const 1)),
       (.instruction .add), (.administrative .returnFromCall),
       (.administrative .finish)]
      ⟨.done [.i32 (n + 1)], (dispatchConfig n).store⟩ := by
  apply Steps.cons (.localGet rfl)
  apply Steps.cons .const
  apply Steps.cons (.callIndirect rfl rfl rfl (by decide) (by decide)
    rfl rfl rfl rfl)
  apply Steps.cons (.localGet rfl)
  apply Steps.cons .const
  apply Steps.cons .add
  apply Steps.cons (.returnFromCallFallthrough rfl)
  apply Steps.cons .finish
  simpa [dispatchConfig, Incr, Function.numParams, Function.toLocals,
    UInt32.add_comm] using
    (Steps.refl
      (⟨.done [.i32 (n + 1)], (dispatchConfig n).store⟩ : Config Unit))

theorem dispatch_runs (n : UInt32) :
    (runSteps 8 (dispatchConfig n)).result.values? =
      some [.i32 (n + 1)] :=
  congrArg RunnerResult.values?
    (runSteps_eq_success_of_steps (dispatch_steps n))

theorem dispatchSpec (n : UInt32) :
    TerminatesWith (dispatchConfig n)
      (fun values _ => values = [.i32 (n + 1)]) :=
  runSteps_values_terminates (dispatch_runs n)

theorem dispatch_partial (n : UInt32) :
    PartiallyMeets (dispatchConfig n)
      (fun values _ => values = [.i32 (n + 1)]) :=
  runSteps_values_partiallyMeets (dispatch_runs n)

end Wasm
