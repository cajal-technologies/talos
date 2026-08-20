import Interpreter.Wasm.Decoder.Wat
import Interpreter.Wasm.SmallStep

/-! ## Example: table inspection and decoded indirect dispatch

The symbolic probe frames an arbitrary physical store with a known table.
Decoded checks cover table size/get/null testing and indirect dispatch through
the same authoritative table representation.
-/

namespace Wasm
open SmallStep

def TableProbe : Program := [
  .const 2, .tableGet 0, .refIsNull, .tableSize 0
]

def tableProbeConfig (m : Module) (st : Store Unit) : Config Unit :=
  { expr := .running
      { locals := {}
        code := TableProbe
        resultArity := 2
        callerRemainder := [] }
    store := { runtime := { instances := #[{ module := m, host := {} }], entry := ⟨0⟩ }, wasm := st } }

theorem tableProbe_steps (m : Module) (st : Store Unit)
    (htbl :
      st.tables =
        [[.funcref (some 0), .funcref (some 1), .funcref none]])
    (h64 : m.tableIs64 0 = false) :
    Steps (tableProbeConfig m st)
      [(.instruction (.const 2)), (.instruction (.tableGet 0)),
       (.instruction .refIsNull), (.instruction (.tableSize 0)),
       (.administrative .finish)]
      ⟨.done [.i32 3, .i32 1], (tableProbeConfig m st).store⟩ := by
  apply Steps.cons .const
  apply Steps.cons (.tableGet
    (table := [.funcref (some 0), .funcref (some 1), .funcref none])
    (value := .funcref none) rfl (by simp [htbl]) rfl)
  apply Steps.cons (.refIsNullTrue rfl)
  apply Steps.cons (.tableSize
    (table := [.funcref (some 0), .funcref (some 1), .funcref none])
    (by simp [htbl]))
  apply Steps.cons .finish
  simpa [tableProbeConfig, h64, sizeValue,
         RuntimeEnv.currentModule, RuntimeEnv.currentInstance] using
    (Steps.refl
      (⟨.done [.i32 3, .i32 1],
        (tableProbeConfig m st).store⟩ : Config Unit))

theorem tableProbeSpec (m : Module) (st : Store Unit)
    (htbl :
      st.tables =
        [[.funcref (some 0), .funcref (some 1), .funcref none]])
    (h64 : m.tableIs64 0 = false) :
    TerminatesWith (tableProbeConfig m st)
      (fun values store =>
        values = [.i32 3, .i32 1] ∧ store.wasm = st) := by
  refine ⟨_, _, _, tableProbe_steps m st htbl h64, rfl, rfl⟩

namespace Decoded

def dispatchWat : String := "
(module
  (type $sig (func (result i32)))
  (func $f0 (result i32) i32.const 10)
  (func $f1 (result i32) i32.const 20)
  (table 3 funcref)
  (elem (i32.const 0) $f0 $f1)
  (func $sz (export \"sz\") (result i32)
    table.size)
  (func $is_null (export \"is_null\") (param i32) (result i32)
    local.get 0
    table.get
    ref.is_null)
  (func $dispatch (export \"dispatch\") (param i32) (result i32)
    local.get 0
    call_indirect (type $sig)))
"

private def decoded : Wasm.Module :=
  match Wasm.Decoder.Wat.decode dispatchWat with
  | .ok module => module
  | .error _ => default

private def decodedConfig (index : Nat)
    (args : List Value) : Config Unit :=
  { expr := .running
      { locals := decoded.funcs[index]!.toLocals args.reverse
        code := decoded.funcs[index]!.body
        resultArity := decoded.funcs[index]!.results.length
        callerRemainder := [] }
    store :=
      { runtime := { instances := #[{ module := decoded, host := {} }], entry := ⟨0⟩ }
        wasm := decoded.initialStore } }

private def runVals (index : Nat)
    (args : List Value) : Option (List Value) :=
  (runSteps 20 (decodedConfig index args)).result.values?

theorem decodes_five_funcs : decoded.funcs.length = 5 := by native_decide

theorem table_populated :
    (decoded.initialStore (α := Unit)).tables =
      [[.funcref (some 0), .funcref (some 1), .funcref none]] := by
  native_decide

theorem sz_runs : runVals 2 [] = some [.i32 3] := by native_decide

theorem is_null_slot0_runs :
    runVals 3 [.i32 0] = some [.i32 0] := by native_decide

theorem is_null_slot2_runs :
    runVals 3 [.i32 2] = some [.i32 1] := by native_decide

theorem dispatch_slot0_runs :
    runVals 4 [.i32 0] = some [.i32 10] := by native_decide

theorem dispatch_slot1_runs :
    runVals 4 [.i32 1] = some [.i32 20] := by native_decide

theorem dispatch_slot0_spec :
    TerminatesWith (decodedConfig 4 [.i32 0])
      (fun values _ => values = [.i32 10]) :=
  runSteps_values_terminates dispatch_slot0_runs

end Decoded
end Wasm
