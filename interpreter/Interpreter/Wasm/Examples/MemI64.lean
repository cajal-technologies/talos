import Interpreter.Wasm.SmallStep

/-! ## Example: i64 memory loads/stores

    Small-step coverage for full-width i64 memory access, signed/unsigned
    narrow loads, and partial-width store roundtrips.
-/

namespace Wasm
open SmallStep

private def initBytes : List UInt8 :=
  [0x88, 0xFF, 0x66, 0x55, 0x44, 0x33, 0x22, 0xFF]

def load64Body : Program := [.const 0, .load64 0]
def load8UI64Body : Program := [.const 1, .load8UI64 0]
def load8SI64Body : Program := [.const 1, .load8SI64 0]
def load16UI64Body : Program := [.const 0, .load16UI64 0]
def load16SI64Body : Program := [.const 0, .load16SI64 0]
def load32UI64Body : Program := [.const 4, .load32UI64 0]
def load32SI64Body : Program := [.const 4, .load32SI64 0]
def store8I64RoundtripBody : Program := [
  .const 8, .constI64 0xABCD, .store8I64 0, .const 8, .load8UI64 0
]
def store16I64RoundtripBody : Program := [
  .const 8, .constI64 0xABCDEF, .store16I64 0, .const 8, .load16UI64 0
]
def store32I64RoundtripBody : Program := [
  .const 8, .constI64 0xABCDEF01, .store32I64 0, .const 8, .load32UI64 0
]
def store64RoundtripBody : Program := [
  .const 16, .constI64 0x1122334455667788, .store64 0, .const 16, .load64 0
]

def i64MemModule : Module :=
  { funcs :=
      [ { body := load64Body, results := [.i64] }
      , { body := load8UI64Body, results := [.i64] }
      , { body := load8SI64Body, results := [.i64] }
      , { body := load16UI64Body, results := [.i64] }
      , { body := load16SI64Body, results := [.i64] }
      , { body := load32UI64Body, results := [.i64] }
      , { body := load32SI64Body, results := [.i64] }
      , { body := store8I64RoundtripBody, results := [.i64] }
      , { body := store16I64RoundtripBody, results := [.i64] }
      , { body := store32I64RoundtripBody, results := [.i64] }
      , { body := store64RoundtripBody, results := [.i64] } ]
    memory := some { pagesMin := 1, data := [{ offset := some 0, bytes := initBytes }] } }

def i64MemStore : MachineStore Unit :=
  { runtime := { instances := #[{ module := i64MemModule, host := {} }], entry := ⟨0⟩ }
    wasm := i64MemModule.initialStore }

def i64MemConfig (index : Nat) : Config Unit :=
  { expr := .running
      { locals := {}
        code := i64MemModule.funcs[index]!.body
        resultArity := 1
        callerRemainder := [] }
    store := i64MemStore }

theorem load64_returns_word :
    (runSteps 8 (i64MemConfig 0)).result.values? = some [.i64 0xFF2233445566FF88] := by native_decide
theorem load8UI64_zero_extends :
    (runSteps 8 (i64MemConfig 1)).result.values? = some [.i64 0xFF] := by native_decide
theorem load8SI64_sign_extends :
    (runSteps 8 (i64MemConfig 2)).result.values? = some [.i64 0xFFFFFFFFFFFFFFFF] := by native_decide
theorem load16UI64_zero_extends :
    (runSteps 8 (i64MemConfig 3)).result.values? = some [.i64 0xFF88] := by native_decide
theorem load16SI64_sign_extends :
    (runSteps 8 (i64MemConfig 4)).result.values? = some [.i64 0xFFFFFFFFFFFFFF88] := by native_decide
theorem load32UI64_zero_extends :
    (runSteps 8 (i64MemConfig 5)).result.values? = some [.i64 0xFF223344] := by native_decide
theorem load32SI64_sign_extends :
    (runSteps 8 (i64MemConfig 6)).result.values? = some [.i64 0xFFFFFFFFFF223344] := by native_decide
theorem store8I64_roundtrip :
    (runSteps 8 (i64MemConfig 7)).result.values? = some [.i64 0xCD] := by native_decide
theorem store16I64_roundtrip :
    (runSteps 8 (i64MemConfig 8)).result.values? = some [.i64 0xCDEF] := by native_decide
theorem store32I64_roundtrip :
    (runSteps 8 (i64MemConfig 9)).result.values? = some [.i64 0xABCDEF01] := by native_decide
theorem store64_roundtrip :
    (runSteps 8 (i64MemConfig 10)).result.values? = some [.i64 0x1122334455667788] := by native_decide

theorem i64Mem_contracts :
    TerminatesWith (i64MemConfig 0) (fun vs _ => vs = [.i64 0xFF2233445566FF88]) ∧
    TerminatesWith (i64MemConfig 1) (fun vs _ => vs = [.i64 0xFF]) ∧
    TerminatesWith (i64MemConfig 2) (fun vs _ => vs = [.i64 0xFFFFFFFFFFFFFFFF]) ∧
    TerminatesWith (i64MemConfig 3) (fun vs _ => vs = [.i64 0xFF88]) ∧
    TerminatesWith (i64MemConfig 4) (fun vs _ => vs = [.i64 0xFFFFFFFFFFFFFF88]) ∧
    TerminatesWith (i64MemConfig 5) (fun vs _ => vs = [.i64 0xFF223344]) ∧
    TerminatesWith (i64MemConfig 6) (fun vs _ => vs = [.i64 0xFFFFFFFFFF223344]) ∧
    TerminatesWith (i64MemConfig 7) (fun vs _ => vs = [.i64 0xCD]) ∧
    TerminatesWith (i64MemConfig 8) (fun vs _ => vs = [.i64 0xCDEF]) ∧
    TerminatesWith (i64MemConfig 9) (fun vs _ => vs = [.i64 0xABCDEF01]) ∧
    TerminatesWith (i64MemConfig 10) (fun vs _ => vs = [.i64 0x1122334455667788]) := by
  exact ⟨runSteps_values_terminates load64_returns_word,
    runSteps_values_terminates load8UI64_zero_extends,
    runSteps_values_terminates load8SI64_sign_extends,
    runSteps_values_terminates load16UI64_zero_extends,
    runSteps_values_terminates load16SI64_sign_extends,
    runSteps_values_terminates load32UI64_zero_extends,
    runSteps_values_terminates load32SI64_sign_extends,
    runSteps_values_terminates store8I64_roundtrip,
    runSteps_values_terminates store16I64_roundtrip,
    runSteps_values_terminates store32I64_roundtrip,
    runSteps_values_terminates store64_roundtrip⟩

theorem i64Mem_partial_contracts :
    PartiallyMeets (i64MemConfig 0) (fun vs _ => vs = [.i64 0xFF2233445566FF88]) ∧
    PartiallyMeets (i64MemConfig 1) (fun vs _ => vs = [.i64 0xFF]) ∧
    PartiallyMeets (i64MemConfig 2) (fun vs _ => vs = [.i64 0xFFFFFFFFFFFFFFFF]) ∧
    PartiallyMeets (i64MemConfig 3) (fun vs _ => vs = [.i64 0xFF88]) ∧
    PartiallyMeets (i64MemConfig 4) (fun vs _ => vs = [.i64 0xFFFFFFFFFFFFFF88]) ∧
    PartiallyMeets (i64MemConfig 5) (fun vs _ => vs = [.i64 0xFF223344]) ∧
    PartiallyMeets (i64MemConfig 6) (fun vs _ => vs = [.i64 0xFFFFFFFFFF223344]) ∧
    PartiallyMeets (i64MemConfig 7) (fun vs _ => vs = [.i64 0xCD]) ∧
    PartiallyMeets (i64MemConfig 8) (fun vs _ => vs = [.i64 0xCDEF]) ∧
    PartiallyMeets (i64MemConfig 9) (fun vs _ => vs = [.i64 0xABCDEF01]) ∧
    PartiallyMeets (i64MemConfig 10) (fun vs _ => vs = [.i64 0x1122334455667788]) := by
  exact ⟨runSteps_values_partiallyMeets load64_returns_word,
    runSteps_values_partiallyMeets load8UI64_zero_extends,
    runSteps_values_partiallyMeets load8SI64_sign_extends,
    runSteps_values_partiallyMeets load16UI64_zero_extends,
    runSteps_values_partiallyMeets load16SI64_sign_extends,
    runSteps_values_partiallyMeets load32UI64_zero_extends,
    runSteps_values_partiallyMeets load32SI64_sign_extends,
    runSteps_values_partiallyMeets store8I64_roundtrip,
    runSteps_values_partiallyMeets store16I64_roundtrip,
    runSteps_values_partiallyMeets store32I64_roundtrip,
    runSteps_values_partiallyMeets store64_roundtrip⟩

end Wasm
