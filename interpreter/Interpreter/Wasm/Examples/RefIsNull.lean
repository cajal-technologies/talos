import Interpreter.Wasm.Decoder.Wat
import Interpreter.Wasm.SmallStep

/-! ## Example: reference instructions (`ref.null`, `ref.func`, `ref.is_null`)

The AST theorem is an instruction-granular relational trace. The decoded
checks execute the same authoritative small-step machine, covering parsing,
constant-global initialization, and execution without the legacy interpreter.
-/

namespace Wasm
open SmallStep

def RefReflect : Program := [
  .refNull, .refIsNull,
  .refFunc 0, .refIsNull
]

def refReflectConfig (m : Module) (st : Store α) : Config α :=
  { expr := .running
      { locals := {}
        code := RefReflect
        resultArity := 2
        callerRemainder := [] }
    store := { runtime := { module := m, host := {} }, wasm := st } }

theorem refReflect_steps (m : Module) (st : Store α) :
    Steps (refReflectConfig m st)
      [(.instruction .refNull), (.instruction .refIsNull),
       (.instruction (.refFunc 0)), (.instruction .refIsNull),
       (.administrative .finish)]
      ⟨.done [.i32 0, .i32 1], (refReflectConfig m st).store⟩ := by
  apply Steps.cons .refNull
  apply Steps.cons (.refIsNullTrue rfl)
  apply Steps.cons .refFunc
  apply Steps.cons (.refIsNullFalse rfl)
  exact Steps.cons .finish (Steps.refl _)

theorem refReflectSpec (m : Module) (st : Store α) :
    TerminatesWith (refReflectConfig m st)
      (fun values store =>
        values = [.i32 0, .i32 1] ∧ store.wasm = st) := by
  refine ⟨_, _, _, refReflect_steps m st, ?_⟩
  exact ⟨rfl, rfl⟩

theorem refReflect_partial (m : Module) (st : Store α) :
    PartiallyMeets (refReflectConfig m st)
      (fun values store =>
        values = [.i32 0, .i32 1] ∧ store.wasm = st) := by
  intro trace values store execution
  obtain ⟨rfl, rfl⟩ :=
    steps_done_deterministic (refReflect_steps m st) execution
  exact ⟨rfl, rfl⟩

namespace Decoded

def refWat : String := "
(module
  (func $f (result i32) i32.const 7)
  (global $g_func funcref (ref.func $f))
  (global $g_null funcref (ref.null nofunc))
  (func $null_is_null (export \"null_is_null\") (result i32)
    ref.null func
    ref.is_null)
  (func $func_is_null (export \"func_is_null\") (result i32)
    ref.func $f
    ref.is_null)
  (func $nofunc_is_null (export \"nofunc_is_null\") (result i32)
    ref.null nofunc
    ref.is_null)
  (func $global_func_is_null (export \"global_func_is_null\") (result i32)
    global.get $g_func
    ref.is_null)
  (func $global_null_is_null (export \"global_null_is_null\") (result i32)
    global.get $g_null
    ref.is_null))
"

private def decoded : Wasm.Module :=
  match Wasm.Decoder.Wat.decode refWat with
  | .ok module => module
  | .error _ => default

private def initializedStore : Store Unit :=
  decoded.runConstGlobals 64 (decoded.initialStore (α := Unit)) {}

private def decodedConfig (index : Nat) : Config Unit :=
  { expr := .running
      { locals := {}
        code := decoded.funcs[index]!.body
        resultArity := decoded.funcs[index]!.results.length
        callerRemainder := [] }
    store :=
      { runtime := { module := decoded, host := {} }
        wasm := initializedStore } }

private def runVals (index : Nat) : Option (List Value) :=
  (runSteps 3 (decodedConfig index)).result.values?

theorem decodes_six_funcs : decoded.funcs.length = 6 := by native_decide

theorem null_is_null_runs : runVals 1 = some [.i32 1] := by native_decide

theorem func_is_null_runs : runVals 2 = some [.i32 0] := by native_decide

theorem nofunc_is_null_runs : runVals 3 = some [.i32 1] := by native_decide

theorem global_func_is_null_runs : runVals 4 = some [.i32 0] := by native_decide

theorem global_null_is_null_runs : runVals 5 = some [.i32 1] := by native_decide

theorem null_is_null_spec :
    TerminatesWith (decodedConfig 1) (fun values _ => values = [.i32 1]) :=
  runSteps_values_terminates null_is_null_runs

theorem func_is_null_spec :
    TerminatesWith (decodedConfig 2) (fun values _ => values = [.i32 0]) :=
  runSteps_values_terminates func_is_null_runs

end Decoded
end Wasm
