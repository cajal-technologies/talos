import Interpreter.Wasm.SmallStep

/-! ## Example: memory.fill

    `memory.fill` pops `[dst, val, len]` (top = `len`) and writes
    `val.low8` into `mem[dst, dst+len)`. The authoritative small-step
    semantics performs the write atomically and traps before changing memory
    when the destination range escapes the legal byte span.
-/

namespace Wasm
open SmallStep

/-- Fill the first 8 bytes with `0xAB`, then read them back as one i64. -/
def fillThenReadBody : Program := [
  .const 0,
  .const 0xAB,
  .const 8,
  .memoryFill,
  .const 0, .load64 0
]

/-- Trap case: dst (65 530) + len (100) overflows the only page. -/
def fillTrapBody : Program := [
  .const 65530, .const 0xCD, .const 100,
  .memoryFill
]

def fillModule : Module :=
  { funcs := [{ body := fillThenReadBody, results := [.i64] }, { body := fillTrapBody }]
    memory := some { pagesMin := 1 } }

def fillStore : MachineStore Unit :=
  { runtime := { module := fillModule, host := {} }
    wasm := fillModule.initialStore }

def fillThenReadConfig : Config Unit :=
  { expr := .running
      { locals := {}
        code := fillThenReadBody
        resultArity := 1
        callerRemainder := [] }
    store := fillStore }

def fillTrapConfig : Config Unit :=
  { expr := .running
      { locals := {}
        code := fillTrapBody
        resultArity := 0
        callerRemainder := [] }
    store := fillStore }

def fillFinalStore : MachineStore Unit :=
  { fillStore with
    wasm := { fillStore.wasm with mem := fillStore.wasm.mem.fill 0 8 0xAB } }

theorem fill_then_load_returns_repeated_byte :
    (runSteps 7 fillThenReadConfig).result =
      .success [.i64 0xABABABABABABABAB] fillFinalStore := by
  rfl

/-- Fuel-free total contract: the returned word and all affected bytes agree. -/
theorem fill_then_load_spec :
    TerminatesWith fillThenReadConfig (fun values store =>
      values = [.i64 0xABABABABABABABAB] ∧
      store.wasm.mem.read64 0 = 0xABABABABABABABAB ∧
      store.wasm.mem.read8 8 = 0) := by
  apply runSteps_success_terminates fill_then_load_returns_repeated_byte
  constructor
  · rfl
  constructor <;> native_decide

theorem fill_then_load_partial :
    PartiallyMeets fillThenReadConfig (fun values store =>
      values = [.i64 0xABABABABABABABAB] ∧
      store.wasm.mem.read64 0 = 0xABABABABABABABAB) := by
  apply runSteps_success_partiallyMeets fill_then_load_returns_repeated_byte
  constructor <;> native_decide

/-- The failing instruction is atomic: the trap retains the original store. -/
theorem fill_out_of_bounds_traps :
    (runSteps 4 fillTrapConfig).result =
      .trapped .outOfBoundsMemory fillStore := by
  rfl

/-- Fuel-free trap contract, including atomic preservation of the store. -/
theorem fill_out_of_bounds_trapsWith :
    TrapsWith fillTrapConfig .outOfBoundsMemory
      (fun store => store = fillStore) := by
  apply runSteps_trapped_trapsWith fill_out_of_bounds_traps
  rfl

end Wasm
