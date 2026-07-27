import Interpreter.Wasm.SmallStep

/-! ## Example: i32 narrow loads/stores

    Small-step coverage for zero/sign-extending byte and half-word loads plus
    partial-width stores followed by matching unsigned loads.
-/

namespace Wasm
open SmallStep

private def initBytes : List UInt8 :=
  [0x42, 0xFF, 0xCD, 0xAB, 0xCD, 0xFF, 0, 0]

def load8UBody : Program := [.const 0, .load8U 0]
def load8SBody : Program := [.const 1, .load8S 0]
def load16UBody : Program := [.const 2, .load16U 0]
def load16SBody : Program := [.const 4, .load16S 0]
def store8RoundtripBody : Program := [
  .const 0, .const 0xAB, .store8 0, .const 0, .load8U 0
]
def store16RoundtripBody : Program := [
  .const 4, .const 0xABCD, .store16 0, .const 4, .load16U 0
]

def narrowI32Module : Module :=
  { funcs :=
      [ { body := load8UBody, results := [.i32] }
      , { body := load8SBody, results := [.i32] }
      , { body := load16UBody, results := [.i32] }
      , { body := load16SBody, results := [.i32] }
      , { body := store8RoundtripBody, results := [.i32] }
      , { body := store16RoundtripBody, results := [.i32] } ]
    memory := some { pagesMin := 1, data := [{ offset := some 0, bytes := initBytes }] } }

def narrowI32Store : MachineStore Unit :=
  { runtime := { module := narrowI32Module, host := {} }
    wasm := narrowI32Module.initialStore }

def narrowI32Config (index : Nat) : Config Unit :=
  { expr := .running
      { locals := {}
        code := narrowI32Module.funcs[index]!.body
        resultArity := 1
        callerRemainder := [] }
    store := narrowI32Store }

theorem load8U_returns_byte :
    (runSteps 8 (narrowI32Config 0)).result.values? = some [.i32 0x42] := by
  native_decide
theorem load8S_sign_extends :
    (runSteps 8 (narrowI32Config 1)).result.values? = some [.i32 0xFFFFFFFF] := by
  native_decide
theorem load16U_returns_halfword :
    (runSteps 8 (narrowI32Config 2)).result.values? = some [.i32 0xABCD] := by
  native_decide
theorem load16S_sign_extends :
    (runSteps 8 (narrowI32Config 3)).result.values? = some [.i32 0xFFFFFFCD] := by
  native_decide
theorem store8_roundtrip :
    (runSteps 8 (narrowI32Config 4)).result.values? = some [.i32 0xAB] := by
  native_decide
theorem store16_roundtrip :
    (runSteps 8 (narrowI32Config 5)).result.values? = some [.i32 0xABCD] := by
  native_decide

theorem narrowI32_contracts :
    TerminatesWith (narrowI32Config 0) (fun vs _ => vs = [.i32 0x42]) ∧
    TerminatesWith (narrowI32Config 1) (fun vs _ => vs = [.i32 0xFFFFFFFF]) ∧
    TerminatesWith (narrowI32Config 2) (fun vs _ => vs = [.i32 0xABCD]) ∧
    TerminatesWith (narrowI32Config 3) (fun vs _ => vs = [.i32 0xFFFFFFCD]) ∧
    TerminatesWith (narrowI32Config 4) (fun vs _ => vs = [.i32 0xAB]) ∧
    TerminatesWith (narrowI32Config 5) (fun vs _ => vs = [.i32 0xABCD]) := by
  exact ⟨runSteps_values_terminates load8U_returns_byte,
    runSteps_values_terminates load8S_sign_extends,
    runSteps_values_terminates load16U_returns_halfword,
    runSteps_values_terminates load16S_sign_extends,
    runSteps_values_terminates store8_roundtrip,
    runSteps_values_terminates store16_roundtrip⟩

theorem narrowI32_partial_contracts :
    PartiallyMeets (narrowI32Config 0) (fun vs _ => vs = [.i32 0x42]) ∧
    PartiallyMeets (narrowI32Config 1) (fun vs _ => vs = [.i32 0xFFFFFFFF]) ∧
    PartiallyMeets (narrowI32Config 2) (fun vs _ => vs = [.i32 0xABCD]) ∧
    PartiallyMeets (narrowI32Config 3) (fun vs _ => vs = [.i32 0xFFFFFFCD]) ∧
    PartiallyMeets (narrowI32Config 4) (fun vs _ => vs = [.i32 0xAB]) ∧
    PartiallyMeets (narrowI32Config 5) (fun vs _ => vs = [.i32 0xABCD]) := by
  exact ⟨runSteps_values_partiallyMeets load8U_returns_byte,
    runSteps_values_partiallyMeets load8S_sign_extends,
    runSteps_values_partiallyMeets load16U_returns_halfword,
    runSteps_values_partiallyMeets load16S_sign_extends,
    runSteps_values_partiallyMeets store8_roundtrip,
    runSteps_values_partiallyMeets store16_roundtrip⟩

end Wasm
