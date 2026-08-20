import Interpreter.Wasm.SmallStep

namespace Wasm
open SmallStep

def SumI64 : Program := [
  .localGet 0, .extendUI32,
  .localGet 0, .extendUI32,
  .addI64,
  .constI64 1, .addI64,
  .wrapI64
]

def sumI64Module : Module :=
  { funcs := [{ params := [.i32], body := SumI64, results := [.i32] }] }

def sumI64Config (x : UInt32) : Config Unit :=
  { expr := .running
      { locals := { params := [.i32 x] }
        code := SumI64
        resultArity := 1
        callerRemainder := [] }
    store :=
      { runtime := { instances := #[{ module := sumI64Module, host := {} }], entry := ⟨0⟩ }
        wasm := sumI64Module.initialStore } }

def sumI64Result (x : UInt32) : UInt32 :=
  UInt32.ofNat
    ((UInt64.ofNat x.toNat + UInt64.ofNat x.toNat + 1).toNat % 2 ^ 32)

theorem sumI64_runs (x : UInt32) :
    (runSteps 9 (sumI64Config x)).result.values? =
      some [.i32 (sumI64Result x)] := by
  rfl

theorem sumI64Spec (x : UInt32) :
    TerminatesWith (sumI64Config x)
      (fun values _ => values = [.i32 (sumI64Result x)]) :=
  runSteps_values_terminates (sumI64_runs x)

theorem sumI64_partial (x : UInt32) :
    PartiallyMeets (sumI64Config x)
      (fun values _ => values = [.i32 (sumI64Result x)]) :=
  runSteps_values_partiallyMeets (sumI64_runs x)

end Wasm
