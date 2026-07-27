import Interpreter.Wasm.SmallStep
import Interpreter.Wasm.Examples.Harness
import Interpreter.Wasm.Validate

/-!
# First small-step regression slice

These checks keep the new iterator and the existing big-step interpreter side
by side.  They compare observable results, deliberately ignoring fuel and the
new machine's administrative step count.
-/

namespace Wasm.Examples.SmallStep

open Wasm.SmallStep

def arithmeticModule : Module :=
  { funcs :=
      [ { body := [.const 40, .const 2, .add], results := [.i32] }
      , { body := [.const 1, .const 0, .divU], results := [.i32] } ] }

def arithmeticRuntime : RuntimeEnv Unit :=
  { module := arithmeticModule, host := {} }

def arithmeticConfig : Config Unit :=
  { expr := .running
      { locals := {}, code := [.const 40, .const 2, .add],
        resultArity := 1, callerRemainder := [] }
    store := { runtime := arithmeticRuntime, wasm := arithmeticModule.initialStore } }

def divideByZeroConfig : Config Unit :=
  { expr := .running
      { locals := {}, code := [.const 1, .const 0, .divU],
        resultArity := 1, callerRemainder := [] }
    store := { runtime := arithmeticRuntime, wasm := arithmeticModule.initialStore } }

theorem arithmetic_small_step :
    (runSteps 4 arithmeticConfig).result.values? = some [.i32 42] := by
  native_decide

theorem arithmetic_matches_big_step :
    (runSteps 4 arithmeticConfig).result.values? =
      some (runValues 4 arithmeticModule 0 arithmeticModule.initialStore []) := by
  native_decide

def isDivideByZero : RunnerResult α → Bool
  | .trapped .integerDivideByZero _ => true
  | _ => false

theorem divide_by_zero_is_structured :
    isDivideByZero (runSteps 3 divideByZeroConfig).result = true := by
  native_decide

def comparisonModule : Module :=
  { funcs :=
      [ { body :=
          [ .const 7, .const 9, .ltU,
            .const 9, .const 9, .eq,
            .const 0, .eqz ],
          results := [.i32, .i32, .i32] } ] }

def comparisonConfig : Config Unit :=
  { expr := .running
      { locals := {}, code := comparisonModule.funcs[0]!.body,
        resultArity := 3, callerRemainder := [] }
    store :=
      { runtime := { module := comparisonModule, host := {} },
        wasm := comparisonModule.initialStore } }

theorem comparisons_small_step :
    (runSteps 11 comparisonConfig).result.values? =
      some [.i32 1, .i32 1, .i32 1] := by
  native_decide

theorem comparisons_match_big_step :
    (runSteps 11 comparisonConfig).result.values? =
      some (runValues 11 comparisonModule 0 comparisonModule.initialStore []) := by
  native_decide

theorem terminal_done_has_no_step :
    stepChecked?
      ({ expr := .done [.i32 42], store := arithmeticConfig.store } : Config Unit) =
      .ok none := by
  rfl
def memoryModule : Module :=
  { funcs :=
      [ { body :=
          [ .const 16, .const 0x12345678, .store32 0,
            .const 16, .load32 0 ],
          results := [.i32] }
      , { body := [.const 65535, .load32 0], results := [.i32] }
      , { body :=
          [ .const 24, .const 0x1234AB, .store8 0,
            .const 24, .load8U 0 ],
          results := [.i32] } ]
    memory := some { pagesMin := 1 } }

def memoryRuntime : RuntimeEnv Unit :=
  { module := memoryModule, host := {} }

def memoryRoundtripConfig : Config Unit :=
  { expr := .running
      { locals := {},
        code :=
          [ .const 16, .const 0x12345678, .store32 0,
            .const 16, .load32 0 ],
        resultArity := 1, callerRemainder := [] }
    store := { runtime := memoryRuntime, wasm := memoryModule.initialStore } }

def memoryTrapConfig : Config Unit :=
  { expr := .running
      { locals := {}, code := [.const 65535, .load32 0],
        resultArity := 1, callerRemainder := [] }
    store := { runtime := memoryRuntime, wasm := memoryModule.initialStore } }

def memoryResultMatches : RunnerResult Unit → Bool
  | .success [.i32 value] store =>
      value == 0x12345678 && store.wasm.mem.read32 16 == 0x12345678
  | _ => false

def memoryFinalStore : MachineStore Unit :=
  { memoryRoundtripConfig.store with
    wasm :=
      { memoryRoundtripConfig.store.wasm with
        mem := memoryRoundtripConfig.store.wasm.mem.write32 16 0x12345678 } }

theorem memory_roundtrip_run :
    (runSteps 6 memoryRoundtripConfig).result =
      .success [.i32 0x12345678] memoryFinalStore := by
  rfl
def memoryValidConfig : ValidConfig Unit :=
  ⟨memoryRoundtripConfig, safe_of_runSteps_success memory_roundtrip_run⟩

theorem memory_valid_step_is_relational {kind} {next : ValidConfig Unit}
    (h : step? memoryValidConfig = some (kind, next)) :
    Step memoryRoundtripConfig kind next.config :=
  step?_sound h

/-- A manual memory specification: the function returns the word it stored,
and the final physical memory contains that same word at address 16. -/
theorem memory_roundtrip_spec :
    memoryResultMatches (runSteps 6 memoryRoundtripConfig).result = true := by
  native_decide

/-- The same contract stated over the authoritative relational semantics,
rather than only over the executable iterator. -/
theorem memory_roundtrip_relational :
    TerminatesWith memoryRoundtripConfig (fun values store =>
      values = [.i32 0x12345678] ∧ store.wasm.mem.read32 16 = 0x12345678) := by
  apply runSteps_success_terminates memory_roundtrip_run
  constructor
  native_decide
  · native_decide

theorem memory_roundtrip_partial :
    PartiallyMeets memoryRoundtripConfig (fun values store =>
      values = [.i32 0x12345678] ∧ store.wasm.mem.read32 16 = 0x12345678) := by
  apply runSteps_success_partiallyMeets memory_roundtrip_run
  constructor
  native_decide
  · native_decide

/-- A disjoint address remains unchanged by the store at address 16. -/
theorem memory_roundtrip_frames_disjoint_word :
    memoryFinalStore.wasm.mem.read32 32 =
      memoryRoundtripConfig.store.wasm.mem.read32 32 := by
  native_decide

theorem memory_roundtrip_matches_big_step :
    (runSteps 6 memoryRoundtripConfig).result.values? =
      some (runValues 6 memoryModule 0 memoryModule.initialStore []) := by
  native_decide

def isOutOfBoundsMemory : RunnerResult α → Bool
  | .trapped .outOfBoundsMemory _ => true
  | _ => false

theorem memory_out_of_bounds_is_structured :
    isDivideByZero (runSteps 3 memoryTrapConfig).result = false ∧
      isOutOfBoundsMemory (runSteps 3 memoryTrapConfig).result = true := by
  native_decide

def memoryGrowthModule : Module :=
  { funcs :=
      [ { body :=
          [ .memorySize,
            .const 1, .memoryGrow, .memorySize,
            .const 1, .memoryGrow, .memorySize ],
          results := [.i32, .i32, .i32, .i32, .i32] } ]
    memory := some { pagesMin := 1, pagesMax := some 2 } }

def memoryGrowthConfig : Config Unit :=
  { expr := .running
      { locals := {}, code := memoryGrowthModule.funcs[0]!.body,
        resultArity := 5, callerRemainder := [] }
    store :=
      { runtime := { module := memoryGrowthModule, host := {} },
        wasm := memoryGrowthModule.initialStore } }

def memoryGrowthFinalStore : MachineStore Unit :=
  match (runSteps 8 memoryGrowthConfig).result with
  | .success _ store => store
  | _ => memoryGrowthConfig.store

theorem memory_growth_run :
    (runSteps 8 memoryGrowthConfig).result =
      .success
        [.i32 2, .i32 0xFFFFFFFF, .i32 2, .i32 1, .i32 1]
        memoryGrowthFinalStore := by
  rfl
/-- Growth returns the old size, respects the declared cap, and failed growth
leaves the physical memory size unchanged. -/
theorem memory_growth_relational :
    TerminatesWith memoryGrowthConfig (fun values store =>
      values = [.i32 2, .i32 0xFFFFFFFF, .i32 2, .i32 1, .i32 1] ∧
      store.wasm.mem.pages = 2) := by
  apply runSteps_success_terminates memory_growth_run
  exact ⟨rfl, rfl⟩

theorem memory_growth_matches_big_step :
    (runSteps 8 memoryGrowthConfig).result.values? =
      some (runValues 20 memoryGrowthModule 0
        memoryGrowthModule.initialStore []) := by
  native_decide

def memory64GrowthModule : Module :=
  { funcs :=
      [ { body :=
          [ .memorySize,
            .constI64 1, .memoryGrow, .memorySize,
            .constI64 1, .memoryGrow, .memorySize,
            .constI64 0x100000000, .memoryGrow, .memorySize ],
          results := [.i64, .i64, .i64, .i64, .i64, .i64, .i64] } ]
    memory := some { pagesMin := 1, pagesMax := some 2, is64 := true } }

def memory64GrowthConfig : Config Unit :=
  { expr := .running
      { locals := {}, code := memory64GrowthModule.funcs[0]!.body,
        resultArity := 7, callerRemainder := [] }
    store :=
      { runtime := { module := memory64GrowthModule, host := {} },
        wasm := memory64GrowthModule.initialStore } }

def memory64GrowthFinalStore : MachineStore Unit :=
  match (runSteps 11 memory64GrowthConfig).result with
  | .success _ store => store
  | _ => memory64GrowthConfig.store

theorem memory64_growth_run :
    (runSteps 11 memory64GrowthConfig).result =
      .success
        [.i64 2, .i64 0xFFFFFFFFFFFFFFFF, .i64 2,
          .i64 0xFFFFFFFFFFFFFFFF, .i64 2, .i64 1, .i64 1]
        memory64GrowthFinalStore := by
  rfl
/-- Memory64 growth uses i64 operands/results, preserves the cap on ordinary
deltas, and deterministically rejects deltas of at least 2^32 pages. -/
theorem memory64_growth_relational :
    TerminatesWith memory64GrowthConfig (fun values store =>
      values =
        [.i64 2, .i64 0xFFFFFFFFFFFFFFFF, .i64 2,
          .i64 0xFFFFFFFFFFFFFFFF, .i64 2, .i64 1, .i64 1] ∧
      store.wasm.mem.pages = 2) := by
  apply runSteps_success_terminates memory64_growth_run
  exact ⟨rfl, rfl⟩

theorem memory64_growth_matches_big_step :
    (runSteps 11 memory64GrowthConfig).result.values? =
      some (runValues 24 memory64GrowthModule 0
        memory64GrowthModule.initialStore []) := by
  native_decide

def memoryFillProgram : Program :=
  [ .const 16, .const 0xAB, .const 4, .memoryFill,
    .const 16, .load32 0,
    .const 32, .load32 0 ]

def memoryFillModule : Module :=
  { funcs := [{ body := memoryFillProgram, results := [.i32, .i32] }]
    memory := some { pagesMin := 1 } }

def memoryFillInitialStore : Store Unit :=
  { memoryFillModule.initialStore (α := Unit) with
    mem := (memoryFillModule.initialStore (α := Unit)).mem.write32
      32 0x12345678 }

def memoryFillConfig : Config Unit :=
  { expr := .running
      { locals := {}, code := memoryFillProgram,
        resultArity := 2, callerRemainder := [] }
    store :=
      { runtime := { module := memoryFillModule, host := {} },
        wasm := memoryFillInitialStore } }

def memoryFillFinalStore : MachineStore Unit :=
  { memoryFillConfig.store with
    wasm :=
      { memoryFillConfig.store.wasm with
        mem := memoryFillConfig.store.wasm.mem.fill 16 4 0xAB } }

theorem memory_fill_run :
    (runSteps 9 memoryFillConfig).result =
      .success [.i32 0x12345678, .i32 0xABABABAB] memoryFillFinalStore := by
  rfl
/-- Filling four bytes produces the expected little-endian word and frames a
disjoint word at address 32. -/
theorem memory_fill_relational :
    TerminatesWith memoryFillConfig (fun values store =>
      values = [.i32 0x12345678, .i32 0xABABABAB] ∧
      store.wasm.mem.read32 16 = 0xABABABAB ∧
      store.wasm.mem.read32 32 = 0x12345678) := by
  apply runSteps_success_terminates memory_fill_run
  constructor
  native_decide
  constructor <;> native_decide

theorem memory_fill_matches_big_step :
    (runSteps 9 memoryFillConfig).result.values? =
      some (runValues 16 memoryFillModule 0 memoryFillInitialStore []) := by
  native_decide

def memoryFillTrapConfig : Config Unit :=
  { expr := .running
      { locals := {},
        code := [.const 65534, .const 0xAB, .const 4, .memoryFill],
        resultArity := 0, callerRemainder := [] }
    store := memoryFillConfig.store }

theorem memory_fill_traps_atomically :
    (runSteps 4 memoryFillTrapConfig).result =
      .trapped .outOfBoundsMemory memoryFillTrapConfig.store := by
  rfl
theorem memory_fill_trapsWith :
    TrapsWith memoryFillTrapConfig .outOfBoundsMemory
      (fun store => store = memoryFillTrapConfig.store) := by
  apply runSteps_trapped_trapsWith memory_fill_traps_atomically
  rfl
def memory64FillModule : Module :=
  { funcs :=
      [{ body :=
          [.constI64 20, .const 0xCD, .constI64 3, .memoryFill,
            .memorySize],
         results := [.i64] }]
    memory := some { pagesMin := 1, is64 := true } }

def memory64FillConfig : Config Unit :=
  { expr := .running
      { locals := {}, code := memory64FillModule.funcs[0]!.body,
        resultArity := 1, callerRemainder := [] }
    store :=
      { runtime := { module := memory64FillModule, host := {} },
        wasm := memory64FillModule.initialStore } }

def memory64FillFinalStore : MachineStore Unit :=
  { memory64FillConfig.store with
    wasm :=
      { memory64FillConfig.store.wasm with
        mem := memory64FillConfig.store.wasm.mem.fill 20 3 0xCD } }

theorem memory64_fill_run :
    (runSteps 6 memory64FillConfig).result =
      .success [.i64 1] memory64FillFinalStore := by
  rfl
theorem memory64_fill_relational :
    TerminatesWith memory64FillConfig (fun values store =>
      values = [.i64 1] ∧
      store.wasm.mem.read8 20 = 0xCD ∧
      store.wasm.mem.read8 21 = 0xCD ∧
      store.wasm.mem.read8 22 = 0xCD) := by
  apply runSteps_success_terminates memory64_fill_run
  constructor
  native_decide
  constructor
  · native_decide
  constructor <;> native_decide

theorem memory64_fill_matches_big_step :
    (runSteps 6 memory64FillConfig).result.values? =
      some (runValues 14 memory64FillModule 0
        memory64FillModule.initialStore []) := by
  native_decide

def overlappingCopyProgram : Program :=
  [ .const 2, .const 0, .const 4, .memoryCopy,
    .const 0, .load32 0,
    .const 2, .load32 0 ]

def overlappingCopyModule : Module :=
  { funcs := [{ body := overlappingCopyProgram, results := [.i32, .i32] }]
    memory := some { pagesMin := 1 } }

def overlappingCopyInitialStore : Store Unit :=
  { overlappingCopyModule.initialStore (α := Unit) with
    mem := (overlappingCopyModule.initialStore (α := Unit)).mem.write32
      0 0x04030201 }

def overlappingCopyConfig : Config Unit :=
  { expr := .running
      { locals := {}, code := overlappingCopyProgram,
        resultArity := 2, callerRemainder := [] }
    store :=
      { runtime := { module := overlappingCopyModule, host := {} },
        wasm := overlappingCopyInitialStore } }

def overlappingCopyFinalStore : MachineStore Unit :=
  { overlappingCopyConfig.store with
    wasm :=
      { overlappingCopyConfig.store.wasm with
        mem := overlappingCopyConfig.store.wasm.mem.copy 2 0 4 } }

theorem overlapping_copy_run :
    (runSteps 9 overlappingCopyConfig).result =
      .success [.i32 0x04030201, .i32 0x02010201]
        overlappingCopyFinalStore := by
  rfl
/-- Overlap reads from the pre-copy byte function, giving `memmove` rather
than forward-loop semantics. -/
theorem overlapping_copy_relational :
    TerminatesWith overlappingCopyConfig (fun values store =>
      values = [.i32 0x04030201, .i32 0x02010201] ∧
      store.wasm.mem.read32 0 = 0x02010201 ∧
      store.wasm.mem.read32 2 = 0x04030201) := by
  apply runSteps_success_terminates overlapping_copy_run
  constructor
  native_decide
  constructor <;> native_decide

theorem overlapping_copy_matches_big_step :
    (runSteps 9 overlappingCopyConfig).result.values? =
      some (runValues 16 overlappingCopyModule 0
        overlappingCopyInitialStore []) := by
  native_decide

def memoryCopyTrapConfig : Config Unit :=
  { expr := .running
      { locals := {},
        code := [.const 65534, .const 0, .const 4, .memoryCopy],
        resultArity := 0, callerRemainder := [] }
    store := overlappingCopyConfig.store }

theorem memory_copy_traps_atomically :
    (runSteps 4 memoryCopyTrapConfig).result =
      .trapped .outOfBoundsMemory memoryCopyTrapConfig.store := by
  rfl
theorem memory_copy_trapsWith :
    TrapsWith memoryCopyTrapConfig .outOfBoundsMemory
      (fun store => store = memoryCopyTrapConfig.store) := by
  apply runSteps_trapped_trapsWith memory_copy_traps_atomically
  rfl
def memory64CopyModule : Module :=
  { funcs :=
      [{ body :=
          [.constI64 8, .constI64 0, .constI64 4, .memoryCopy,
            .memorySize],
         results := [.i64] }]
    memory := some { pagesMin := 1, is64 := true } }

def memory64CopyInitialStore : Store Unit :=
  { memory64CopyModule.initialStore (α := Unit) with
    mem := (memory64CopyModule.initialStore (α := Unit)).mem.write32
      0 0x12345678 }

def memory64CopyConfig : Config Unit :=
  { expr := .running
      { locals := {}, code := memory64CopyModule.funcs[0]!.body,
        resultArity := 1, callerRemainder := [] }
    store :=
      { runtime := { module := memory64CopyModule, host := {} },
        wasm := memory64CopyInitialStore } }

def memory64CopyFinalStore : MachineStore Unit :=
  { memory64CopyConfig.store with
    wasm :=
      { memory64CopyConfig.store.wasm with
        mem := memory64CopyConfig.store.wasm.mem.copy 8 0 4 } }

theorem memory64_copy_run :
    (runSteps 6 memory64CopyConfig).result =
      .success [.i64 1] memory64CopyFinalStore := by
  rfl
theorem memory64_copy_relational :
    TerminatesWith memory64CopyConfig (fun values store =>
      values = [.i64 1] ∧
      store.wasm.mem.read32 0 = 0x12345678 ∧
      store.wasm.mem.read32 8 = 0x12345678) := by
  apply runSteps_success_terminates memory64_copy_run
  constructor
  native_decide
  constructor <;> native_decide

theorem memory64_copy_matches_big_step :
    (runSteps 6 memory64CopyConfig).result.values? =
      some (runValues 14 memory64CopyModule 0
        memory64CopyInitialStore []) := by
  native_decide

def memoryInitProgram : Program :=
  [ .const 16, .const 0, .const 4, .memoryInit 0,
    .const 16, .load32 0,
    .dataDrop 0,
    .const 16, .const 0, .const 0, .memoryInit 0 ]

def memoryInitModule : Module :=
  { funcs := [{ body := memoryInitProgram, results := [.i32] }]
    memory := some
      { pagesMin := 1
        data := [{ offset := none, bytes := [1, 2, 3, 4] }] } }

def memoryInitConfig : Config Unit :=
  { expr := .running
      { locals := {}, code := memoryInitProgram,
        resultArity := 1, callerRemainder := [] }
    store :=
      { runtime := { module := memoryInitModule, host := {} },
        wasm := memoryInitModule.initialStore } }

def memoryInitFinalStore : MachineStore Unit :=
  { memoryInitConfig.store with
    wasm :=
      { memoryInitConfig.store.wasm with
        mem := memoryInitConfig.store.wasm.mem.writeBytesFrom
          16 [1, 2, 3, 4] 0 4
        dataSegments := [none] } }

theorem memory_init_run :
    (runSteps 12 memoryInitConfig).result =
      .success [.i32 0x04030201] memoryInitFinalStore := by
  rfl
/-- A passive segment initializes memory once, `data.drop` consumes it, and a
zero-length initialization remains valid after the drop. -/
theorem memory_init_relational :
    TerminatesWith memoryInitConfig (fun values store =>
      values = [.i32 0x04030201] ∧
      store.wasm.mem.read32 16 = 0x04030201 ∧
      store.wasm.dataSegments = [none]) := by
  apply runSteps_success_terminates memory_init_run
  constructor
  native_decide
  constructor <;> native_decide

theorem memory_init_matches_big_step :
    (runSteps 12 memoryInitConfig).result.values? =
      some (runValues 24 memoryInitModule 0
        memoryInitModule.initialStore []) := by
  native_decide

def droppedMemoryInitTrapConfig : Config Unit :=
  { expr := .running
      { locals := {},
        code := [.const 16, .const 0, .const 1, .memoryInit 0],
        resultArity := 0, callerRemainder := [] }
    store :=
      { memoryInitConfig.store with
        wasm :=
          { memoryInitConfig.store.wasm with dataSegments := [none] } } }

theorem dropped_memory_init_traps_atomically :
    (runSteps 4 droppedMemoryInitTrapConfig).result =
      .trapped .outOfBoundsMemory droppedMemoryInitTrapConfig.store := by
  rfl
theorem dropped_memory_init_trapsWith :
    TrapsWith droppedMemoryInitTrapConfig .outOfBoundsMemory
      (fun store => store = droppedMemoryInitTrapConfig.store) := by
  apply runSteps_trapped_trapsWith dropped_memory_init_traps_atomically
  rfl

def invalidDataDropModule : Module :=
  { funcs := [{ body := [.dataDrop 0] }] }

def invalidMemoryInitIndexModule : Module :=
  { funcs :=
      [{ body := [.const 0, .const 0, .const 0, .memoryInit 1] }]
    memory := some
      { pagesMin := 1
        data := [{ offset := none, bytes := [1] }] } }

def validMemoryInit64ValidationModule : Module :=
  { funcs :=
      [{ body := [.constI64 0, .const 0, .const 1, .memoryInit 0] }]
    memory := some
      { pagesMin := 1
        is64 := true
        data := [{ offset := none, bytes := [1] }] } }

def invalidMemoryFillWithoutMemoryModule : Module :=
  { funcs := [{ body := [.const 0, .const 0, .const 0, .memoryFill] }] }

def validMemoryFill64ValidationModule : Module :=
  { funcs :=
      [{ body := [.constI64 0, .const 0, .constI64 1, .memoryFill] }]
    memory := some { pagesMin := 1, is64 := true } }

def invalidMemoryCopy64LengthModule : Module :=
  { funcs :=
      [{ body :=
          [.constI64 0, .constI64 0, .const 1, .memoryCopy] }]
    memory := some { pagesMin := 1, is64 := true } }

def validMemoryCopy64ValidationModule : Module :=
  { funcs :=
      [{ body :=
          [.constI64 0, .constI64 0, .constI64 1, .memoryCopy] }]
    memory := some { pagesMin := 1, is64 := true } }

def invalidLoadWithoutMemoryModule : Module :=
  { funcs := [{ body := [.const 0, .load32 0], results := [.i32] }] }

def invalidMemory64LoadAddressModule : Module :=
  { funcs := [{ body := [.const 0, .load32 0], results := [.i32] }]
    memory := some { pagesMin := 1, is64 := true } }

def validMemory64LoadValidationModule : Module :=
  { funcs := [{ body := [.constI64 0, .load32 0], results := [.i32] }]
    memory := some { pagesMin := 1, is64 := true } }

def validMemory64I64StoreValidationModule : Module :=
  { funcs := [{ body := [.constI64 0, .constI64 1, .store64 0] }]
    memory := some { pagesMin := 1, is64 := true } }

def invalidMemorySizeWithoutMemoryModule : Module :=
  { funcs := [{ body := [.memorySize], results := [.i32] }] }

def validMemory64SizeValidationModule : Module :=
  { funcs := [{ body := [.memorySize], results := [.i64] }]
    memory := some { pagesMin := 1, is64 := true } }

def invalidMemory64GrowDeltaModule : Module :=
  { funcs := [{ body := [.const 1, .memoryGrow], results := [.i64] }]
    memory := some { pagesMin := 1, is64 := true } }

def validMemory64GrowValidationModule : Module :=
  { funcs := [{ body := [.constI64 1, .memoryGrow], results := [.i64] }]
    memory := some { pagesMin := 1, is64 := true } }

def invalidGlobalGetIndexModule : Module :=
  { funcs := [{ body := [.globalGet 0], results := [.i32] }] }

def invalidGlobalSetIndexModule : Module :=
  { funcs := [{ body := [.const 0, .globalSet 1] }]
    globals := [{ init := .i32 0 }] }

def invalidImmutableGlobalSetModule : Module :=
  { funcs := [{ body := [.const 0, .globalSet 0] }]
    globals :=
      [{ init := .i32 0, declaredType := some .i32, isMut := false }] }

def invalidGlobalInitializerTypeModule : Module :=
  { funcs := []
    globals :=
      [{ init := .f32 0, declaredType := some .i32, isMut := false }] }

def invalidGlobalInitializerInstructionModule : Module :=
  { funcs := []
    globals :=
      [{ init := .i32 0, declaredType := some .i32, isMut := false,
         sourceInit := some [.const 0, .nop] }] }

def invalidForwardGlobalInitializerModule : Module :=
  { funcs := []
    globals :=
      [ { init := .i32 0, declaredType := some .i32, isMut := false,
          sourceInit := some [.globalGet 1] }
      , { init := .i32 0, declaredType := some .i32, isMut := false,
          sourceInit := some [.const 0] } ] }

def invalidElemDropModule : Module :=
  { funcs := [{ body := [.elemDrop 0] }] }

def invalidTableInitTableModule : Module :=
  { funcs :=
      [{ body := [.const 0, .const 0, .const 0, .tableInit 0 0] }]
    elements := [{ funcs := [some 0] }] }

def invalidTableInitElementModule : Module :=
  { funcs :=
      [{ body := [.const 0, .const 0, .const 0, .tableInit 0 1] }]
    tables := [{ min := 1 }]
    elements := [{ funcs := [some 0] }] }

def validTableInit64ValidationModule : Module :=
  { funcs :=
      [{ body := [.constI64 0, .const 0, .const 1, .tableInit 0 0] }]
    tables := [{ min := 1, is64 := true }]
    elements := [{ funcs := [some 0] }] }

def invalidTableGetIndexModule : Module :=
  { funcs := [{ body := [.const 0, .tableGet 0], results := [.funcref] }] }

def validTable64FillValidationModule : Module :=
  { funcs :=
      [{ params := [.i64, .externref, .i64],
         body := [.localGet 0, .localGet 1, .localGet 2, .tableFill 0] }]
    tables := [{ min := 1, elemType := .externref, is64 := true }] }

def validMixedTableCopyValidationModule : Module :=
  { funcs :=
      [{ params := [.i32, .i64, .i32],
         body := [.localGet 0, .localGet 1, .localGet 2, .tableCopy 0 1] }]
    tables :=
      [ { min := 1, is64 := false }
      , { min := 1, is64 := true } ] }

def invalidMixedTableCopyLengthModule : Module :=
  { funcs :=
      [{ params := [.i32, .i64, .i64],
         body := [.localGet 0, .localGet 1, .localGet 2, .tableCopy 0 1] }]
    tables :=
      [ { min := 1, is64 := false }
      , { min := 1, is64 := true } ] }

def invalidDirectCallIndexModule : Module :=
  { funcs := [{ body := [.call 1] }] }

def validImportedCallValidationModule : Module :=
  { imports := [{ module := "host", name := "f",
                  params := [.i32], results := [.i64] }]
    funcs :=
      [{ body := [.const 7, .call 0], results := [.i64] }] }

def invalidIndirectCallTypeModule : Module :=
  { funcs := [{ body := [.const 0, .callIndirect 0 0] }]
    tables := [{ min := 1 }] }

def validTable64IndirectCallValidationModule : Module :=
  { funcs :=
      [{ body := [.constI64 0, .callIndirect 0 0], results := [.i32] }]
    types := [{ results := [.i32] }]
    gcTypes := [{ comp := .func { results := [.i32] } }]
    tables := [{ min := 1, is64 := true }] }

def invalidRefFuncIndexModule : Module :=
  { funcs := [{ body := [.refFunc 1], results := [.funcref] }] }

def invalidStructuredBlockExtraValueModule : Module :=
  { funcs := [{ body := [.block 0 0 [.const 1]] }] }

def invalidStructuredBlockMissingResultModule : Module :=
  { funcs := [{ body := [.block 0 1 []], results := [.i32] }] }

def invalidStructuredIfResultMismatchModule : Module :=
  { funcs :=
      [{ body := [.const 0, .iff 0 1 [.const 1] [.constI64 1]],
         results := [.i32] }] }

def validStructuredBranchPolymorphicModule : Module :=
  { funcs :=
      [{ body := [.block 0 1 [.const 7, .br 0, .add]],
         results := [.i32] }] }

def invalidSimdExtractLaneModule : Module :=
  { funcs :=
      [{ body := [.vConst 0, .vExtractLane .i8x16 false 16],
         results := [.i32] }] }

def invalidSimdSplatOperandModule : Module :=
  { funcs :=
      [{ body := [.constI64 0, .vSplat .i32x4],
         results := [.v128] }] }

def validSimdSplatValidationModule : Module :=
  { funcs :=
      [{ body := [.const 0, .vSplat .i32x4],
         results := [.v128] }] }

def invalidSimdLoadWithoutMemoryModule : Module :=
  { funcs :=
      [{ body := [.const 0, .v128Load 0],
         results := [.v128] }] }

def validMemory64SimdLoadValidationModule : Module :=
  { funcs :=
      [{ body := [.constI64 0, .v128Load 0],
         results := [.v128] }]
    memory := some { pagesMin := 1, is64 := true } }

def invalidLocalIndexValidationModule : Module :=
  { funcs := [{ body := [.localGet 0] }] }

def invalidUnreachableLocalIndexValidationModule : Module :=
  { funcs := [{ body := [.unreachable, .localSet 0] }] }

def validParamAndLocalIndexValidationModule : Module :=
  { funcs :=
      [{ params := [.i32], locals := [.i64],
         body := [.localGet 0, .drop, .localGet 1],
         results := [.i64] }] }

def invalidFunctionExportValidationModule : Module :=
  { funcs := [], exports := [{ name := "missing", funcIdx := 0 }] }

def invalidDuplicateCrossKindExportValidationModule : Module :=
  { funcs := [{ body := [] }]
    exports := [{ name := "same", funcIdx := 0 }]
    memory := some { pagesMin := 0 }
    memoryExports := [("same", 0)] }

def invalidStartSignatureValidationModule : Module :=
  { funcs := [{ params := [.i32], body := [] }]
    startFunc := some 0 }

def invalidStartIndexValidationModule : Module :=
  { funcs := [], startFunc := some 0 }

def validImportedStartValidationModule : Module :=
  { funcs := []
    imports := [{ module := "host", name := "start" }]
    startFunc := some 0 }

def invalidSyntheticDataMemoryValidationModule : Module :=
  { funcs := []
    memory := some
      { pagesMin := 0
        data := [{ offset := some 0, bytes := [] }] }
    dataWithoutMemory := true }

def invalidDataOffsetTypeValidationModule : Module :=
  { funcs := []
    memory := some
      { pagesMin := 1
        data :=
          [{ offset := some 0, offsetType := some .i64, bytes := [] }] } }

def validMemory64DataOffsetValidationModule : Module :=
  { funcs := []
    memory := some
      { pagesMin := 1
        is64 := true
        data :=
          [{ offset := some 0, offsetType := some .i64, bytes := [] }] } }

def invalidActiveElementTableValidationModule : Module :=
  { funcs := []
    elements :=
      [{ tableIdx := some 0, offset := some 0,
         offsetType := some .i32, elemType := some .funcref }] }

def invalidActiveElementTypeValidationModule : Module :=
  { funcs := []
    tables := [{ min := 1, elemType := .externref }]
    elements :=
      [{ tableIdx := some 0, offset := some 0,
         offsetType := some .i32, elemType := some .funcref }] }

def validTable64ElementOffsetValidationModule : Module :=
  { funcs := []
    tables := [{ min := 1, is64 := true }]
    elements :=
      [{ tableIdx := some 0, offset := some 0,
         offsetType := some .i64, elemType := some .funcref }] }

def invalidDirectTailCallResultValidationModule : Module :=
  { funcs :=
      [{ body := [.returnCall 1], results := [.i32] },
       { body := [.constI64 0], results := [.i64] }] }

def validDirectTailCallValidationModule : Module :=
  { funcs :=
      [{ body := [.returnCall 1], results := [.i32] },
       { body := [.const 0], results := [.i32] }] }

def invalidIndirectTailCallResultValidationModule : Module :=
  { funcs :=
      [{ body := [.const 0, .returnCallIndirect 0 0], results := [.i32] }]
    types := [{ results := [.i64] }]
    gcTypes := [{ comp := .func { results := [.i64] } }]
    tables := [{ min := 1 }] }

def invalidReferenceTailCallResultValidationModule : Module :=
  { funcs :=
      [{ body := [.refNull, .returnCallRef 0], results := [.i32] }]
    types := [{ results := [.i64] }]
    gcTypes := [{ comp := .func { results := [.i64] } }] }

def invalidRefAsNonNullPolymorphicResultValidationModule : Module :=
  { funcs :=
      [{ body := [.unreachable, .refAsNonNull, .f32Abs] }] }

def invalidRefIsNullScalarValidationModule : Module :=
  { funcs :=
      [{ body := [.const 0, .refIsNull, .drop] }] }

def validPolymorphicReferenceValidationModule : Module :=
  { funcs :=
      [{ body := [.unreachable, .refAsNonNull, .refIsNull, .drop] }] }

def invalidImmutableArrayCopyValidationModule : Module :=
  { funcs :=
      [{ body :=
          [.unreachable, .gc (.arrayCopy 0 1)] }]
    gcTypes :=
      [{ comp := .array { storage := .packed 8 } },
       { comp := .array { storage := .packed 8, isMut := true } }] }

def invalidMismatchedArrayCopyValidationModule : Module :=
  { funcs :=
      [{ body :=
          [.unreachable, .gc (.arrayCopy 0 1)] }]
    gcTypes :=
      [{ comp := .array { storage := .packed 8, isMut := true } },
       { comp := .array { storage := .packed 16 } }] }

def validArrayCopyValidationModule : Module :=
  { funcs :=
      [{ params :=
          [.ref false (.concrete 0), .ref false (.concrete 1)]
         body :=
          [.localGet 0, .const 0, .localGet 1, .const 0, .const 0,
           .gc (.arrayCopy 0 1)] }]
    gcTypes :=
      [{ comp := .array { storage := .packed 8, isMut := true } },
       { comp := .array { storage := .packed 8 } }] }

def invalidTypedBlockResultValidationModule : Module :=
  { funcs :=
      [{ body :=
          [.block 0 1 [.f32Const 0] [] [.i32], .drop] }] }

def invalidTypedBlockBranchValidationModule : Module :=
  { funcs :=
      [{ body :=
          [.block 0 1 [.f32Const 0, .br 0] [] [.i32], .drop] }] }

def invalidTypedLoopParameterValidationModule : Module :=
  { funcs :=
      [{ body :=
          [.f32Const 0,
           .loop 1 0 [.br 0] [.i32] []] }] }

def validTypedStructuredValidationModule : Module :=
  { funcs :=
      [{ body :=
          [.const 7,
           .block 1 1 [.br 0] [.i32] [.i32],
           .drop] }] }

def invalidUnknownThrowValidationModule : Module :=
  { funcs := [{ body := [.throwI 0] }] }

def invalidThrowArgumentValidationModule : Module :=
  { tags := [{ params := [.i32] }]
    funcs := [{ body := [.throwI 0] }] }

def invalidThrowRefOperandValidationModule : Module :=
  { funcs := [{ body := [.throwRef] }] }

def invalidTryTableResultValidationModule : Module :=
  { funcs :=
      [{ body :=
          [.tryTable 0 1 [] [] [] [.i32]],
         results := [.i32] }] }

def invalidCatchRefTargetValidationModule : Module :=
  { tags := [{}]
    funcs :=
      [{ body :=
          [.tryTable 0 0 [.catchRef 0 0] []] }] }

def validTryTableCatchValidationModule : Module :=
  { tags := [{}]
    funcs :=
      [{ body :=
          [.tryTable 0 0 [.catch 0 0] [.throwI 0]] }] }

def invalidBrOnNullScalarValidationModule : Module :=
  { funcs := [{ body := [.const 0, .brOnNull 0] }] }

def invalidBrOnNonNullTargetValidationModule : Module :=
  { funcs :=
      [{ body := [.refNullExtern, .brOnNonNull 0],
         results := [.i32] }] }

def validReferenceBranchValidationModule : Module :=
  { funcs :=
      [{ body := [.refNull, .brOnNull 0, .drop] }] }

def invalidBroadReturnCallRefValidationModule : Module :=
  { types := [{}]
    gcTypes := [{ comp := .func {} }]
    funcs :=
      [{ params := [.funcref],
         body := [.localGet 0, .returnCallRef 0] }] }

def validPreciseReturnCallRefValidationModule : Module :=
  { types := [{}]
    gcTypes := [{ comp := .func {} }]
    exports := [{ name := "callee", funcIdx := 1 }]
    funcs :=
      [{ body := [.refFunc 1, .returnCallRef 0] },
       { body := [], typeIdx := some 0 }] }

def invalidRefEqAnyValidationModule : Module :=
  { funcs :=
      [{ params := [.ref true .any],
         body := [.localGet 0, .localGet 0, .gc .refEq, .drop] }] }

def validationErrorIs (module : Module) (expected : String) : Bool :=
  match module.validate with
  | .error actual => actual == expected
  | .ok () => false

def validationSucceeds (module : Module) : Bool :=
  match module.validate with
  | .ok () => true
  | .error _ => false

def passiveDataWithoutMemoryModule : Module :=
  decodeOrDefault "(module (data \"payload\"))"

def activeDataWithoutMemoryModule : Module :=
  decodeOrDefault "(module (data (i32.const 0) \"payload\"))"

def floatConstantGlobalValidationModule : Module :=
  decodeOrDefault "(module (global f32 (f32.const 1)))"

def immutableArrayInitDataValidationModule : Module :=
  decodeOrDefault
    "(module
       (type $a (array i8))
       (data $d \"a\")
       (func (param (ref $a))
         (array.init_data $a 0
           (local.get 0) (i32.const 0) (i32.const 0) (i32.const 0))))"

def referenceArrayInitDataValidationModule : Module :=
  decodeOrDefault
    "(module
       (type $a (array (mut funcref)))
       (data $d \"a\")
       (func (param (ref $a))
         (array.init_data $a 0
           (local.get 0) (i32.const 0) (i32.const 0) (i32.const 0))))"

def preciseArrayConstructorValidationModule : Module :=
  decodeOrDefault
    "(module
       (type $a (array f32))
       (global (ref $a)
         (array.new $a (f32.const 1) (i32.const 3))))"

def crossTypedArrayGetValidationModule : Module :=
  decodeOrDefault
    "(module
       (type $bytes (array i8))
       (type $floats (array f32))
       (func (param (ref $bytes))
         (array.get $floats (local.get 0) (i32.const 0))
         drop))"

def declarativeFunctionReferenceValidationModule : Module :=
  decodeOrDefault
    "(module
       (elem declare func $f)
       (type $t (func))
       (func $f (type $t))
       (func (ref.func $f) drop))"

def preciseFunctionReferenceGlobalValidationModule : Module :=
  decodeOrDefault
    "(module
       (type $t (func))
       (elem declare func $f)
       (global (ref $t) (ref.func $f))
       (func $f (type $t)))"

def covariantElementTableValidationModule : Module :=
  decodeOrDefault
    "(module
       (type $t (func))
       (table 1 (ref null $t))
       (elem (table 0) (i32.const 0)
         (ref $t) (ref.func $f))
       (func $f (type $t)))"

def brOnNonNullRefinementValidationModule : Module :=
  decodeOrDefault
    "(module
       (type $t (func))
       (func (param (ref null $t))
         (drop
           (block (result (ref $t))
             (br_on_non_null 0 (local.get 0))
             unreachable))))"

theorem validator_accepts_passive_data_without_linear_memory :
    passiveDataWithoutMemoryModule.dataWithoutMemory = false ∧
      validationSucceeds passiveDataWithoutMemoryModule = true := by
  native_decide

theorem validator_rejects_active_data_without_linear_memory :
    activeDataWithoutMemoryModule.dataWithoutMemory = true ∧
      validationErrorIs activeDataWithoutMemoryModule "unknown memory" = true := by
  native_decide

theorem validator_accepts_float_constant_global :
    validationSucceeds floatConstantGlobalValidationModule = true := by
  native_decide

theorem validator_rejects_immutable_array_init_data :
    validationErrorIs immutableArrayInitDataValidationModule
      "immutable array" = true := by
  native_decide

theorem validator_rejects_reference_array_init_data :
    validationErrorIs referenceArrayInitDataValidationModule
      "array type is not numeric or vector" = true := by
  native_decide

theorem validator_accepts_precise_array_constructor_result :
    validationSucceeds preciseArrayConstructorValidationModule = true := by
  native_decide

theorem validator_rejects_cross_typed_array_get :
    validationErrorIs crossTypedArrayGetValidationModule
      "type mismatch" = true := by
  native_decide

theorem validator_accepts_declarative_function_reference :
    validationSucceeds declarativeFunctionReferenceValidationModule = true := by
  native_decide

theorem validator_accepts_precise_function_reference_global :
    validationSucceeds preciseFunctionReferenceGlobalValidationModule = true := by
  native_decide

theorem validator_accepts_nonnull_element_for_nullable_table :
    validationSucceeds covariantElementTableValidationModule = true := by
  native_decide

theorem validator_accepts_br_on_non_null_refinement :
    validationSucceeds brOnNonNullRefinementValidationModule = true := by
  native_decide

theorem validator_rejects_unknown_data_drop :
    validationErrorIs invalidDataDropModule "unknown data segment" = true := by
  native_decide

theorem validator_rejects_unknown_memory_init_segment :
    validationErrorIs invalidMemoryInitIndexModule
      "unknown data segment" = true := by
  native_decide

theorem validator_accepts_typed_memory64_init :
    validationSucceeds validMemoryInit64ValidationModule = true := by
  native_decide

theorem validator_rejects_memory_fill_without_memory :
    validationErrorIs invalidMemoryFillWithoutMemoryModule
      "unknown memory" = true := by
  native_decide

theorem validator_accepts_typed_memory64_fill :
    validationSucceeds validMemoryFill64ValidationModule = true := by
  native_decide

theorem validator_rejects_mistyped_memory64_copy_length :
    validationErrorIs invalidMemoryCopy64LengthModule
      "type mismatch" = true := by
  native_decide

theorem validator_accepts_typed_memory64_copy :
    validationSucceeds validMemoryCopy64ValidationModule = true := by
  native_decide

theorem validator_rejects_load_without_memory :
    validationErrorIs invalidLoadWithoutMemoryModule
      "unknown memory" = true := by
  native_decide

theorem validator_rejects_mistyped_memory64_load_address :
    validationErrorIs invalidMemory64LoadAddressModule
      "type mismatch" = true := by
  native_decide

theorem validator_accepts_typed_memory64_load :
    validationSucceeds validMemory64LoadValidationModule = true := by
  native_decide

theorem validator_accepts_typed_memory64_i64_store :
    validationSucceeds validMemory64I64StoreValidationModule = true := by
  native_decide

theorem validator_rejects_memory_size_without_memory :
    validationErrorIs invalidMemorySizeWithoutMemoryModule
      "unknown memory" = true := by
  native_decide

theorem validator_accepts_typed_memory64_size :
    validationSucceeds validMemory64SizeValidationModule = true := by
  native_decide

theorem validator_rejects_mistyped_memory64_grow_delta :
    validationErrorIs invalidMemory64GrowDeltaModule
      "type mismatch" = true := by
  native_decide

theorem validator_accepts_typed_memory64_grow :
    validationSucceeds validMemory64GrowValidationModule = true := by
  native_decide

theorem validator_rejects_unknown_global_get :
    validationErrorIs invalidGlobalGetIndexModule
      "unknown global" = true := by
  native_decide

theorem validator_rejects_unknown_global_set :
    validationErrorIs invalidGlobalSetIndexModule
      "unknown global" = true := by
  native_decide

theorem validator_rejects_immutable_global_set :
    validationErrorIs invalidImmutableGlobalSetModule
      "immutable global" = true := by
  native_decide

theorem validator_rejects_mistyped_global_initializer :
    validationErrorIs invalidGlobalInitializerTypeModule
      "type mismatch" = true := by
  native_decide

theorem validator_rejects_nonconstant_global_initializer :
    validationErrorIs invalidGlobalInitializerInstructionModule
      "constant expression required" = true := by
  native_decide

theorem validator_rejects_forward_global_initializer :
    validationErrorIs invalidForwardGlobalInitializerModule
      "unknown global" = true := by
  native_decide

theorem validator_rejects_unknown_element_drop :
    validationErrorIs invalidElemDropModule
      "unknown element segment" = true := by
  native_decide

theorem validator_rejects_unknown_table_init_table :
    validationErrorIs invalidTableInitTableModule "unknown table" = true := by
  native_decide

theorem validator_rejects_unknown_table_init_element :
    validationErrorIs invalidTableInitElementModule
      "unknown element segment" = true := by
  native_decide

theorem validator_accepts_typed_table64_init :
    validationSucceeds validTableInit64ValidationModule = true := by
  native_decide

theorem validator_rejects_unknown_table_get :
    validationErrorIs invalidTableGetIndexModule "unknown table" = true := by
  native_decide

theorem validator_accepts_typed_table64_fill :
    validationSucceeds validTable64FillValidationModule = true := by
  native_decide

theorem validator_accepts_typed_mixed_table_copy :
    validationSucceeds validMixedTableCopyValidationModule = true := by
  native_decide

theorem validator_rejects_mistyped_mixed_table_copy_length :
    validationErrorIs invalidMixedTableCopyLengthModule
      "type mismatch" = true := by
  native_decide

theorem validator_rejects_unknown_direct_call :
    validationErrorIs invalidDirectCallIndexModule
      "unknown function" = true := by
  native_decide

theorem validator_accepts_typed_imported_call :
    validationSucceeds validImportedCallValidationModule = true := by
  native_decide

theorem validator_rejects_unknown_indirect_call_type :
    validationErrorIs invalidIndirectCallTypeModule
      "unknown type" = true := by
  native_decide

theorem validator_accepts_typed_table64_indirect_call :
    validationSucceeds validTable64IndirectCallValidationModule = true := by
  native_decide

theorem validator_rejects_unknown_ref_func :
    validationErrorIs invalidRefFuncIndexModule
      "unknown function" = true := by
  native_decide

theorem validator_rejects_extra_block_value :
    validationErrorIs invalidStructuredBlockExtraValueModule
      "type mismatch" = true := by
  native_decide

theorem validator_rejects_missing_block_result :
    validationErrorIs invalidStructuredBlockMissingResultModule
      "type mismatch" = true := by
  native_decide

theorem validator_rejects_mismatched_if_results :
    validationErrorIs invalidStructuredIfResultMismatchModule
      "type mismatch" = true := by
  native_decide

theorem validator_accepts_branch_stack_polymorphism :
    validationSucceeds validStructuredBranchPolymorphicModule = true := by
  native_decide

theorem validator_rejects_invalid_simd_lane :
    validationErrorIs invalidSimdExtractLaneModule
      "invalid lane index" = true := by
  native_decide

theorem validator_rejects_mistyped_simd_splat :
    validationErrorIs invalidSimdSplatOperandModule
      "type mismatch" = true := by
  native_decide

theorem validator_accepts_typed_simd_splat :
    validationSucceeds validSimdSplatValidationModule = true := by
  native_decide

theorem validator_rejects_simd_load_without_memory :
    validationErrorIs invalidSimdLoadWithoutMemoryModule
      "unknown memory" = true := by
  native_decide

theorem validator_accepts_memory64_simd_load :
    validationSucceeds validMemory64SimdLoadValidationModule = true := by
  native_decide

theorem validator_rejects_unknown_local :
    validationErrorIs invalidLocalIndexValidationModule
      "unknown local" = true := by
  native_decide

theorem validator_rejects_unknown_local_after_unreachable :
    validationErrorIs invalidUnreachableLocalIndexValidationModule
      "unknown local" = true := by
  native_decide

theorem validator_accepts_param_and_local_indices :
    validationSucceeds validParamAndLocalIndexValidationModule = true := by
  native_decide

theorem validator_rejects_unknown_function_export :
    validationErrorIs invalidFunctionExportValidationModule
      "unknown function" = true := by
  native_decide

theorem validator_rejects_duplicate_cross_kind_export :
    validationErrorIs invalidDuplicateCrossKindExportValidationModule
      "duplicate export name" = true := by
  native_decide

theorem validator_rejects_start_signature :
    validationErrorIs invalidStartSignatureValidationModule
      "start function" = true := by
  native_decide

theorem validator_rejects_unknown_start_function :
    validationErrorIs invalidStartIndexValidationModule
      "unknown function" = true := by
  native_decide

theorem validator_accepts_imported_start_function :
    validationSucceeds validImportedStartValidationModule = true := by
  native_decide

theorem validator_rejects_decoder_synthesized_data_memory :
    validationErrorIs invalidSyntheticDataMemoryValidationModule
      "unknown memory" = true := by
  native_decide

theorem validator_rejects_mistyped_data_offset :
    validationErrorIs invalidDataOffsetTypeValidationModule
      "type mismatch" = true := by
  native_decide

theorem validator_accepts_memory64_data_offset :
    validationSucceeds validMemory64DataOffsetValidationModule = true := by
  native_decide

theorem validator_rejects_active_element_without_table :
    validationErrorIs invalidActiveElementTableValidationModule
      "unknown table" = true := by
  native_decide

theorem validator_rejects_active_element_type_mismatch :
    validationErrorIs invalidActiveElementTypeValidationModule
      "type mismatch" = true := by
  native_decide

theorem validator_accepts_table64_element_offset :
    validationSucceeds validTable64ElementOffsetValidationModule = true := by
  native_decide

theorem validator_rejects_direct_tail_call_result_mismatch :
    validationErrorIs invalidDirectTailCallResultValidationModule
      "type mismatch" = true := by
  native_decide

theorem validator_accepts_direct_tail_call :
    validationSucceeds validDirectTailCallValidationModule = true := by
  native_decide

theorem validator_rejects_indirect_tail_call_result_mismatch :
    validationErrorIs invalidIndirectTailCallResultValidationModule
      "type mismatch" = true := by
  native_decide

theorem validator_rejects_reference_tail_call_result_mismatch :
    validationErrorIs invalidReferenceTailCallResultValidationModule
      "type mismatch" = true := by
  native_decide

theorem validator_rejects_polymorphic_ref_as_non_null_result :
    validationErrorIs invalidRefAsNonNullPolymorphicResultValidationModule
      "type mismatch" = true := by
  native_decide

theorem validator_rejects_ref_is_null_on_scalar :
    validationErrorIs invalidRefIsNullScalarValidationModule
      "type mismatch" = true := by
  native_decide

theorem validator_accepts_polymorphic_reference_operations :
    validationSucceeds validPolymorphicReferenceValidationModule = true := by
  native_decide

theorem validator_rejects_copy_into_immutable_array :
    validationErrorIs invalidImmutableArrayCopyValidationModule
      "immutable array" = true := by
  native_decide

theorem validator_rejects_mismatched_array_copy :
    validationErrorIs invalidMismatchedArrayCopyValidationModule
      "array types do not match" = true := by
  native_decide

theorem validator_accepts_matching_array_copy :
    validationSucceeds validArrayCopyValidationModule = true := by
  native_decide

theorem validator_rejects_typed_block_result_mismatch :
    validationErrorIs invalidTypedBlockResultValidationModule
      "type mismatch" = true := by
  native_decide

theorem validator_rejects_typed_block_branch_mismatch :
    validationErrorIs invalidTypedBlockBranchValidationModule
      "type mismatch" = true := by
  native_decide

theorem validator_rejects_typed_loop_parameter_mismatch :
    validationErrorIs invalidTypedLoopParameterValidationModule
      "type mismatch" = true := by
  native_decide

theorem validator_accepts_typed_structured_control :
    validationSucceeds validTypedStructuredValidationModule = true := by
  native_decide

theorem validator_rejects_unknown_throw_tag :
    validationErrorIs invalidUnknownThrowValidationModule
      "unknown tag" = true := by
  native_decide

theorem validator_rejects_missing_throw_argument :
    validationErrorIs invalidThrowArgumentValidationModule
      "type mismatch" = true := by
  native_decide

theorem validator_rejects_missing_throw_ref_operand :
    validationErrorIs invalidThrowRefOperandValidationModule
      "type mismatch" = true := by
  native_decide

theorem validator_rejects_try_table_result_mismatch :
    validationErrorIs invalidTryTableResultValidationModule
      "type mismatch" = true := by
  native_decide

theorem validator_rejects_catch_ref_target_mismatch :
    validationErrorIs invalidCatchRefTargetValidationModule
      "type mismatch" = true := by
  native_decide

theorem validator_accepts_typed_try_table_catch :
    validationSucceeds validTryTableCatchValidationModule = true := by
  native_decide

theorem validator_rejects_br_on_null_scalar :
    validationErrorIs invalidBrOnNullScalarValidationModule
      "type mismatch" = true := by
  native_decide

theorem validator_rejects_br_on_non_null_target_mismatch :
    validationErrorIs invalidBrOnNonNullTargetValidationModule
      "type mismatch" = true := by
  native_decide

theorem validator_accepts_reference_branch :
    validationSucceeds validReferenceBranchValidationModule = true := by
  native_decide

theorem validator_rejects_broad_return_call_ref :
    validationErrorIs invalidBroadReturnCallRefValidationModule
      "type mismatch" = true := by
  native_decide

theorem validator_accepts_precise_return_call_ref :
    validationSucceeds validPreciseReturnCallRefValidationModule = true := by
  native_decide

theorem validator_rejects_ref_eq_on_anyref :
    validationErrorIs invalidRefEqAnyValidationModule
      "type mismatch" = true := by
  native_decide

def memory64InitModule : Module :=
  { funcs :=
      [{ body :=
          [.constI64 20, .const 1, .const 2, .memoryInit 0,
            .memorySize],
         results := [.i64] }]
    memory := some
      { pagesMin := 1
        is64 := true
        data := [{ offset := none, bytes := [0xAA, 0xBB, 0xCC, 0xDD] }] } }

def memory64InitConfig : Config Unit :=
  { expr := .running
      { locals := {}, code := memory64InitModule.funcs[0]!.body,
        resultArity := 1, callerRemainder := [] }
    store :=
      { runtime := { module := memory64InitModule, host := {} },
        wasm := memory64InitModule.initialStore } }

def memory64InitFinalStore : MachineStore Unit :=
  { memory64InitConfig.store with
    wasm :=
      { memory64InitConfig.store.wasm with
        mem := memory64InitConfig.store.wasm.mem.writeBytesFrom
          20 [0xAA, 0xBB, 0xCC, 0xDD] 1 2 } }

theorem memory64_init_run :
    (runSteps 6 memory64InitConfig).result =
      .success [.i64 1] memory64InitFinalStore := by
  rfl
theorem memory64_init_relational :
    TerminatesWith memory64InitConfig (fun values store =>
      values = [.i64 1] ∧
      store.wasm.mem.read8 20 = 0xBB ∧
      store.wasm.mem.read8 21 = 0xCC) := by
  apply runSteps_success_terminates memory64_init_run
  constructor
  native_decide
  constructor <;> native_decide

theorem memory64_init_matches_big_step :
    (runSteps 6 memory64InitConfig).result.values? =
      some (runValues 14 memory64InitModule 0
        memory64InitModule.initialStore []) := by
  native_decide

def byteRoundtripConfig : Config Unit :=
  { expr := .running
      { locals := {},
        code :=
          [ .const 24, .const 0x1234AB, .store8 0,
            .const 24, .load8U 0 ],
        resultArity := 1, callerRemainder := [] }
    store := { runtime := memoryRuntime, wasm := memoryModule.initialStore } }

def byteFinalStore : MachineStore Unit :=
  { byteRoundtripConfig.store with
    wasm :=
      { byteRoundtripConfig.store.wasm with
        mem := byteRoundtripConfig.store.wasm.mem.write8 24
          (0x1234AB : UInt32).toUInt8 } }

theorem byte_roundtrip_run :
    (runSteps 6 byteRoundtripConfig).result =
      .success [.i32 0xAB] byteFinalStore := by
  rfl
/-- Narrow stores retain the low byte, and `load8_u` returns its zero extension. -/
theorem byte_roundtrip_relational :
    TerminatesWith byteRoundtripConfig (fun values store =>
      values = [.i32 0xAB] ∧ store.wasm.mem.read8 24 = 0xAB) := by
  apply runSteps_success_terminates byte_roundtrip_run
  constructor
  native_decide
  · native_decide

theorem byte_roundtrip_matches_big_step :
    (runSteps 6 byteRoundtripConfig).result.values? =
      some (runValues 6 memoryModule 2 memoryModule.initialStore []) := by
  native_decide

def narrowMemoryProgram : Program :=
  [ .const 24, .const 0x80, .store8 0,
    .const 24, .load8S 0,
    .const 26, .const 0x12348001, .store16 0,
    .const 26, .load16U 0,
    .const 26, .load16S 0 ]

def narrowMemoryModule : Module :=
  { funcs := [{ body := narrowMemoryProgram,
                results := [.i32, .i32, .i32] }]
    memory := some { pagesMin := 1 } }

def narrowMemoryConfig : Config Unit :=
  { expr := .running
      { locals := {}, code := narrowMemoryProgram,
        resultArity := 3, callerRemainder := [] }
    store :=
      { runtime := { module := narrowMemoryModule, host := {} },
        wasm := narrowMemoryModule.initialStore } }

def narrowMemoryFinalStore : MachineStore Unit :=
  { narrowMemoryConfig.store with
    wasm :=
      { narrowMemoryConfig.store.wasm with
        mem := (narrowMemoryConfig.store.wasm.mem.write8 24 0x80).write16
          26 0x12348001 } }

theorem narrow_memory_run :
    (runSteps 13 narrowMemoryConfig).result =
      .success [.i32 0xFFFF8001, .i32 0x8001, .i32 0xFFFFFF80]
        narrowMemoryFinalStore := by
  rfl
/-- Signed and unsigned narrow loads agree on the stored low bits and differ
only in their extension to the i32 result width. -/
theorem narrow_memory_relational :
    TerminatesWith narrowMemoryConfig (fun values store =>
      values = [.i32 0xFFFF8001, .i32 0x8001, .i32 0xFFFFFF80] ∧
      store.wasm.mem.read8 24 = 0x80 ∧
      store.wasm.mem.read16 26 = 0x8001) := by
  apply runSteps_success_terminates narrow_memory_run
  constructor
  native_decide
  constructor <;> native_decide

theorem narrow_memory_matches_big_step :
    (runSteps 13 narrowMemoryConfig).result.values? =
      some (runValues 20 narrowMemoryModule 0
        narrowMemoryModule.initialStore []) := by
  native_decide

def i64MemoryModule (is64 : Bool) : Module :=
  { funcs :=
      [{ body :=
          (if is64 then
            [ .constI64 32, .constI64 0x0123456789ABCDEF, .store64 0,
              .constI64 32, .load64 0 ]
           else
            [ .const 32, .constI64 0x0123456789ABCDEF, .store64 0,
              .const 32, .load64 0 ]),
         results := [.i64] }]
    memory := some { pagesMin := 1, is64 } }

def i64MemoryConfig (is64 : Bool) : Config Unit :=
  let module := i64MemoryModule is64
  { expr := .running
      { locals := {}, code := module.funcs[0]!.body,
        resultArity := 1, callerRemainder := [] }
    store :=
      { runtime := { module, host := {} },
        wasm := module.initialStore } }

def i64MemoryFinalStore (is64 : Bool) : MachineStore Unit :=
  let config := i64MemoryConfig is64
  { config.store with
    wasm :=
      { config.store.wasm with
        mem := config.store.wasm.mem.write64 32 0x0123456789ABCDEF } }

theorem i64_memory32_run :
    (runSteps 6 (i64MemoryConfig false)).result =
      .success [.i64 0x0123456789ABCDEF] (i64MemoryFinalStore false) := by
  rfl
theorem i64_memory64_run :
    (runSteps 6 (i64MemoryConfig true)).result =
      .success [.i64 0x0123456789ABCDEF] (i64MemoryFinalStore true) := by
  rfl
/-- Full-width i64 store/load has the same byte-level effect for memory32 and
memory64 addressing; only the operand type used to form the address differs. -/
theorem i64_memory_relational (is64 : Bool) :
    TerminatesWith (i64MemoryConfig is64) (fun values store =>
      values = [.i64 0x0123456789ABCDEF] ∧
      store.wasm.mem.read64 32 = 0x0123456789ABCDEF) := by
  cases is64
  · apply runSteps_success_terminates i64_memory32_run
    constructor <;> native_decide
  · apply runSteps_success_terminates i64_memory64_run
    constructor <;> native_decide

theorem i64_memory_matches_big_step :
    (runSteps 6 (i64MemoryConfig false)).result.values? =
        some (runValues 10 (i64MemoryModule false) 0
          (i64MemoryModule false).initialStore []) ∧
      (runSteps 6 (i64MemoryConfig true)).result.values? =
        some (runValues 10 (i64MemoryModule true) 0
          (i64MemoryModule true).initialStore []) := by
  native_decide

def i32Memory64Module : Module :=
  { funcs :=
      [{ body :=
          [ .constI64 24, .const 0x12345678, .store32 0,
            .constI64 24, .load32 0 ],
         results := [.i32] }]
    memory := some { pagesMin := 1, is64 := true } }

def i32Memory64Config : Config Unit :=
  { expr := .running
      { locals := {}, code := i32Memory64Module.funcs[0]!.body,
        resultArity := 1, callerRemainder := [] }
    store :=
      { runtime := { module := i32Memory64Module, host := {} },
        wasm := i32Memory64Module.initialStore } }

def i32Memory64FinalStore : MachineStore Unit :=
  { i32Memory64Config.store with
    wasm :=
      { i32Memory64Config.store.wasm with
        mem := i32Memory64Config.store.wasm.mem.write32 24 0x12345678 } }

theorem i32_memory64_run :
    (runSteps 6 i32Memory64Config).result =
      .success [.i32 0x12345678] i32Memory64FinalStore := by
  rfl

/-- Ordinary i32 loads and stores consume i64 addresses for a memory64
instance while retaining their i32 value type. -/
theorem i32_memory64_relational :
    TerminatesWith i32Memory64Config (fun values store =>
      values = [.i32 0x12345678] ∧
      store.wasm.mem.read32 24 = 0x12345678) := by
  apply runSteps_success_terminates i32_memory64_run
  constructor <;> native_decide

def i32Memory64TrapConfig : Config Unit :=
  { i32Memory64Config with
    expr := .running
      { locals := {}, code := [.constI64 65535, .load32 0],
        resultArity := 1, callerRemainder := [] } }

theorem i32_memory64_out_of_bounds_traps :
    (runSteps 2 i32Memory64TrapConfig).result =
      .trapped .outOfBoundsMemory i32Memory64TrapConfig.store := by
  rfl
theorem i32_memory64_out_of_bounds_trapsWith :
    TrapsWith i32Memory64TrapConfig .outOfBoundsMemory
      (fun store => store = i32Memory64TrapConfig.store) := by
  apply runSteps_trapped_trapsWith i32_memory64_out_of_bounds_traps
  rfl

theorem i32_memory64_matches_big_step :
    (runSteps 6 i32Memory64Config).result.values? =
      some (runValues 10 i32Memory64Module 0
        i32Memory64Module.initialStore []) := by
  native_decide

def i64Load8Config (is64 : Bool) : Config Unit :=
  { expr := .running
      { locals := {},
        code := if is64 then [.constI64 32, .load8UI64 0]
                else [.const 32, .load8UI64 0],
        resultArity := 1, callerRemainder := [] }
    store := i64MemoryFinalStore is64 }

theorem i64_load8_u_memory32 :
    (runSteps 3 (i64Load8Config false)).result.values? =
      some [.i64 0xEF] := by
  native_decide

theorem i64_load8_u_memory64 :
    (runSteps 3 (i64Load8Config true)).result.values? =
      some [.i64 0xEF] := by
  native_decide

def i64NarrowLoadConfig (is64 : Bool) : Config Unit :=
  let address : Instruction := if is64 then .constI64 32 else .const 32
  { expr := .running
      { locals := {},
        code :=
          [address, .load8SI64 0,
           address, .load16UI64 0,
           address, .load16SI64 0,
           address, .load32UI64 0,
           address, .load32SI64 0],
        resultArity := 5, callerRemainder := [] }
    store := i64MemoryFinalStore is64 }

theorem i64_narrow_loads_memory32 :
    (runSteps 11 (i64NarrowLoadConfig false)).result.values? =
      some
        [.i64 0xFFFFFFFF89ABCDEF, .i64 0x89ABCDEF,
          .i64 0xFFFFFFFFFFFFCDEF, .i64 0xCDEF,
          .i64 0xFFFFFFFFFFFFFFEF] := by
  native_decide

theorem i64_narrow_loads_memory64 :
    (runSteps 11 (i64NarrowLoadConfig true)).result.values? =
      some
        [.i64 0xFFFFFFFF89ABCDEF, .i64 0x89ABCDEF,
          .i64 0xFFFFFFFFFFFFCDEF, .i64 0xCDEF,
          .i64 0xFFFFFFFFFFFFFFEF] := by
  native_decide

def i64NarrowStoreModule (is64 : Bool) : Module :=
  let address (n : UInt32) : Instruction :=
    if is64 then .constI64 n.toUInt64 else .const n
  { funcs :=
      [{ body :=
          [ address 40, .constI64 0x0123456789ABCDEF, .store8I64 0,
            address 42, .constI64 0x0123456789ABCDEF, .store16I64 0,
            address 44, .constI64 0x0123456789ABCDEF, .store32I64 0,
            address 40, .load8UI64 0,
            address 42, .load16UI64 0,
            address 44, .load32UI64 0 ],
         results := [.i64, .i64, .i64] }]
    memory := some { pagesMin := 1, is64 } }

def i64NarrowStoreConfig (is64 : Bool) : Config Unit :=
  let module := i64NarrowStoreModule is64
  { expr := .running
      { locals := {}, code := module.funcs[0]!.body,
        resultArity := 3, callerRemainder := [] }
    store :=
      { runtime := { module, host := {} },
        wasm := module.initialStore } }

def i64NarrowStoreFinalStore (is64 : Bool) : MachineStore Unit :=
  let config := i64NarrowStoreConfig is64
  { config.store with
    wasm :=
      { config.store.wasm with
        mem :=
          (((config.store.wasm.mem.write8 40 0xEF).write16
            42 0x89ABCDEF).write32 44 0x89ABCDEF) } }

theorem i64_narrow_store_memory32_run :
    (runSteps 16 (i64NarrowStoreConfig false)).result =
      .success [.i64 0x89ABCDEF, .i64 0xCDEF, .i64 0xEF]
        (i64NarrowStoreFinalStore false) := by
  rfl
theorem i64_narrow_store_memory64_run :
    (runSteps 16 (i64NarrowStoreConfig true)).result =
      .success [.i64 0x89ABCDEF, .i64 0xCDEF, .i64 0xEF]
        (i64NarrowStoreFinalStore true) := by
  rfl
/-- Narrow i64 stores retain exactly the low 8/16/32 bits, independently of
whether the memory uses i32 or i64 addresses. -/
theorem i64_narrow_store_relational (is64 : Bool) :
    TerminatesWith (i64NarrowStoreConfig is64) (fun values store =>
      values = [.i64 0x89ABCDEF, .i64 0xCDEF, .i64 0xEF] ∧
      store.wasm.mem.read8 40 = 0xEF ∧
      store.wasm.mem.read16 42 = 0xCDEF ∧
      store.wasm.mem.read32 44 = 0x89ABCDEF) := by
  cases is64
  · apply runSteps_success_terminates i64_narrow_store_memory32_run
    constructor
    native_decide
    constructor <;> native_decide
  · apply runSteps_success_terminates i64_narrow_store_memory64_run
    constructor
    native_decide
    constructor <;> native_decide

theorem i64_narrow_store_matches_big_step :
    (runSteps 16 (i64NarrowStoreConfig false)).result.values? =
        some (runValues 24 (i64NarrowStoreModule false) 0
          (i64NarrowStoreModule false).initialStore []) ∧
      (runSteps 16 (i64NarrowStoreConfig true)).result.values? =
        some (runValues 24 (i64NarrowStoreModule true) 0
          (i64NarrowStoreModule true).initialStore []) := by
  native_decide

def swapProgram : Program :=
  [ .const 0, .load32 0, .localSet 0,
    .const 4, .load32 0, .localSet 1,
    .const 0, .localGet 1, .store32 0,
    .const 4, .localGet 0, .store32 0,
    .const 0, .load32 0,
    .const 4, .load32 0 ]

def swapModule : Module :=
  { funcs :=
      [ { body := swapProgram, locals := [.i32, .i32],
          results := [.i32, .i32] } ]
    memory := some { pagesMin := 1 } }

def swapInitialStore : Store Unit :=
  { swapModule.initialStore (α := Unit) with
    mem := ((swapModule.initialStore (α := Unit)).mem.write32 0 11).write32 4 22 }

def swapRuntime : RuntimeEnv Unit :=
  { module := swapModule, host := {} }

def swapConfig : Config Unit :=
  { expr := .running
      { locals := { locals := [.i32 0, .i32 0] },
        code := swapProgram, resultArity := 2, callerRemainder := [] }
    store := { runtime := swapRuntime, wasm := swapInitialStore } }

def swapFinalStore : MachineStore Unit :=
  { swapConfig.store with
    wasm :=
      { swapConfig.store.wasm with
        mem := (swapConfig.store.wasm.mem.write32 0 22).write32 4 11 } }

set_option maxRecDepth 10000 in
theorem swap_run :
    (runSteps 17 swapConfig).result =
      .success [.i32 11, .i32 22] swapFinalStore := by
  rfl
def swapValidConfig : ValidConfig Unit :=
  ⟨swapConfig, safe_of_runSteps_success swap_run⟩

/-- Relational contract for a hand-written two-word memory swap. -/
theorem swap_relational :
    TerminatesWith swapConfig (fun values store =>
      values = [.i32 11, .i32 22] ∧
      store.wasm.mem.read32 0 = 22 ∧
      store.wasm.mem.read32 4 = 11) := by
  apply runSteps_success_terminates swap_run
  constructor
  native_decide
  constructor <;> native_decide

theorem swap_partial :
    PartiallyMeets swapConfig (fun values store =>
      values = [.i32 11, .i32 22] ∧
      store.wasm.mem.read32 0 = 22 ∧
      store.wasm.mem.read32 4 = 11) := by
  apply runSteps_success_partiallyMeets swap_run
  constructor
  native_decide
  constructor <;> native_decide

theorem swap_matches_big_step :
    (runSteps 17 swapConfig).result.values? =
      some (runValues 17 swapModule 0 swapInitialStore []) := by
  native_decide

def reverseThreeProgram : Program :=
  [ .const 0, .load32 0, .localSet 0,
    .const 8, .load32 0, .localSet 1,
    .const 0, .localGet 1, .store32 0,
    .const 8, .localGet 0, .store32 0,
    .const 0, .load32 0,
    .const 8, .load32 0 ]

def reverseThreeModule : Module :=
  { funcs :=
      [ { body := reverseThreeProgram, locals := [.i32, .i32],
          results := [.i32, .i32] } ]
    memory := some { pagesMin := 1 } }

def reverseThreeInitialStore : Store Unit :=
  { reverseThreeModule.initialStore (α := Unit) with
    mem :=
      Mem.write32
        (Mem.write32
          (Mem.write32 (reverseThreeModule.initialStore (α := Unit)).mem 0 11)
          4 22)
        8 33 }

def reverseThreeConfig : Config Unit :=
  { expr := .running
      { locals := { locals := [.i32 0, .i32 0] },
        code := reverseThreeProgram, resultArity := 2, callerRemainder := [] }
    store :=
      { runtime := { module := reverseThreeModule, host := {} },
        wasm := reverseThreeInitialStore } }

def reverseThreeFinalStore : MachineStore Unit :=
  { reverseThreeConfig.store with
    wasm :=
      { reverseThreeConfig.store.wasm with
        mem := (reverseThreeConfig.store.wasm.mem.write32 0 33).write32 8 11 } }

set_option maxRecDepth 10000 in
theorem reverse_three_run :
    (runSteps 17 reverseThreeConfig).result =
      .success [.i32 11, .i32 33] reverseThreeFinalStore := by
  rfl
/-- Reversing three words swaps the endpoints and frames the middle word. -/
theorem reverse_three_relational :
    TerminatesWith reverseThreeConfig (fun values store =>
      values = [.i32 11, .i32 33] ∧
      store.wasm.mem.read32 0 = 33 ∧
      store.wasm.mem.read32 4 = 22 ∧
      store.wasm.mem.read32 8 = 11) := by
  apply runSteps_success_terminates reverse_three_run
  constructor
  native_decide
  constructor
  · native_decide
  constructor <;> native_decide

theorem reverse_three_partial :
    PartiallyMeets reverseThreeConfig (fun values store =>
      values = [.i32 11, .i32 33] ∧
      store.wasm.mem.read32 0 = 33 ∧
      store.wasm.mem.read32 4 = 22 ∧
      store.wasm.mem.read32 8 = 11) := by
  apply runSteps_success_partiallyMeets reverse_three_run
  constructor
  native_decide
  constructor
  · native_decide
  constructor <;> native_decide

theorem reverse_three_matches_big_step :
    (runSteps 17 reverseThreeConfig).result.values? =
      some (runValues 17 reverseThreeModule 0 reverseThreeInitialStore []) := by
  native_decide

/-! ### Three-word partition kernel

This is the first sorting-ladder example after swap and reverse.  The input
`[33, 11, 22]` uses the final word as its pivot; the kernel moves the smaller
word left, the pivot into its final position, and the larger word right. -/

def partitionThreeProgram : Program :=
  [ .const 0, .load32 0, .localSet 0,
    .const 4, .load32 0, .localSet 1,
    .const 8, .load32 0, .localSet 2,
    .const 0, .localGet 1, .store32 0,
    .const 4, .localGet 2, .store32 0,
    .const 8, .localGet 0, .store32 0 ]

def partitionThreeModule : Module :=
  { funcs :=
      [ { body := partitionThreeProgram, locals := [.i32, .i32, .i32] } ]
    memory := some { pagesMin := 1 } }

def partitionThreeInitialStore : Store Unit :=
  { partitionThreeModule.initialStore (α := Unit) with
    mem :=
      Mem.write32
        (Mem.write32
          (Mem.write32 (partitionThreeModule.initialStore (α := Unit)).mem 0 33)
          4 11)
        8 22 }

def partitionThreeConfig : Config Unit :=
  { expr := .running
      { locals := { locals := [.i32 0, .i32 0, .i32 0] },
        code := partitionThreeProgram, resultArity := 0,
        callerRemainder := [] }
    store :=
      { runtime := { module := partitionThreeModule, host := {} },
        wasm := partitionThreeInitialStore } }

def partitionThreeFinalStore : MachineStore Unit :=
  { partitionThreeConfig.store with
    wasm :=
      { partitionThreeConfig.store.wasm with
        mem :=
          ((partitionThreeConfig.store.wasm.mem.write32 0 11).write32 4 22)
            |>.write32 8 33 } }

set_option maxRecDepth 10000 in
theorem partition_three_run :
    (runSteps 19 partitionThreeConfig).result =
      .success [] partitionThreeFinalStore := by
  rfl

/-- The concrete partition kernel preserves the three input words, places the
pivot at address four, and establishes the left/right unsigned partition
inequalities. -/
theorem partition_three_relational :
    TerminatesWith partitionThreeConfig (fun values store =>
      values = [] ∧
      store.wasm.mem.read32 0 = 11 ∧
      store.wasm.mem.read32 4 = 22 ∧
      store.wasm.mem.read32 8 = 33 ∧
      store.wasm.mem.read32 0 ≤ store.wasm.mem.read32 4 ∧
      store.wasm.mem.read32 4 ≤ store.wasm.mem.read32 8) := by
  apply runSteps_success_terminates partition_three_run
  native_decide

theorem partition_three_partial :
    PartiallyMeets partitionThreeConfig (fun values store =>
      values = [] ∧
      store.wasm.mem.read32 0 = 11 ∧
      store.wasm.mem.read32 4 = 22 ∧
      store.wasm.mem.read32 8 = 33 ∧
      store.wasm.mem.read32 0 ≤ store.wasm.mem.read32 4 ∧
      store.wasm.mem.read32 4 ≤ store.wasm.mem.read32 8) := by
  apply runSteps_success_partiallyMeets partition_three_run
  native_decide

theorem partition_three_matches_big_step :
    (runSteps 19 partitionThreeConfig).result.values? =
      some (runValues 19 partitionThreeModule 0 partitionThreeInitialStore []) := by
  native_decide

/-! ### Merge of two singleton sorted runs

Unlike the concrete partition permutation above, this kernel performs the
comparison in Wasm and selects a store sequence through structured control.
Each input cell is a sorted run of length one. -/

def mergeTwoKeepBody : Program :=
  [ .const 0, .localGet 0, .store32 0,
    .const 4, .localGet 1, .store32 0 ]

def mergeTwoSwapBody : Program :=
  [ .const 0, .localGet 1, .store32 0,
    .const 4, .localGet 0, .store32 0 ]

def mergeTwoProgram : Program :=
  [ .const 0, .load32 0, .localSet 0,
    .const 4, .load32 0, .localSet 1,
    .localGet 0, .localGet 1, .ltU,
    .iff 0 0 mergeTwoKeepBody mergeTwoSwapBody ]

def mergeTwoModule : Module :=
  { funcs :=
      [ { body := mergeTwoProgram, locals := [.i32, .i32] } ]
    memory := some { pagesMin := 1 } }

def mergeTwoInitialStore : Store Unit :=
  { mergeTwoModule.initialStore (α := Unit) with
    mem := ((mergeTwoModule.initialStore (α := Unit)).mem.write32 0 9)
      |>.write32 4 4 }

def mergeTwoConfig : Config Unit :=
  { expr := .running
      { locals := { locals := [.i32 0, .i32 0] },
        code := mergeTwoProgram, resultArity := 0,
        callerRemainder := [] }
    store :=
      { runtime := { module := mergeTwoModule, host := {} },
        wasm := mergeTwoInitialStore } }

def mergeTwoFinalStore : MachineStore Unit :=
  { mergeTwoConfig.store with
    wasm :=
      { mergeTwoConfig.store.wasm with
        mem := (mergeTwoConfig.store.wasm.mem.write32 0 4).write32 4 9 } }

set_option maxRecDepth 10000 in
theorem merge_two_run :
    (runSteps 18 mergeTwoConfig).result =
      .success [] mergeTwoFinalStore := by
  rfl

/-- The two singleton runs are merged in ascending unsigned order, while the
output remains a permutation of the two input words. -/
theorem merge_two_relational :
    TerminatesWith mergeTwoConfig (fun values store =>
      values = [] ∧
      store.wasm.mem.read32 0 = 4 ∧
      store.wasm.mem.read32 4 = 9 ∧
      store.wasm.mem.read32 0 ≤ store.wasm.mem.read32 4) := by
  apply runSteps_success_terminates merge_two_run
  native_decide

theorem merge_two_partial :
    PartiallyMeets mergeTwoConfig (fun values store =>
      values = [] ∧
      store.wasm.mem.read32 0 = 4 ∧
      store.wasm.mem.read32 4 = 9 ∧
      store.wasm.mem.read32 0 ≤ store.wasm.mem.read32 4) := by
  apply runSteps_success_partiallyMeets merge_two_run
  native_decide

theorem merge_two_matches_big_step :
    (runSteps 18 mergeTwoConfig).result.values? =
      some (runValues 18 mergeTwoModule 0 mergeTwoInitialStore []) := by
  native_decide

def mergeTwoKeepInitialStore : Store Unit :=
  { mergeTwoModule.initialStore (α := Unit) with
    mem := ((mergeTwoModule.initialStore (α := Unit)).mem.write32 0 4)
      |>.write32 4 9 }

def mergeTwoKeepConfig : Config Unit :=
  { expr := .running
      { locals := { locals := [.i32 0, .i32 0] },
        code := mergeTwoProgram, resultArity := 0,
        callerRemainder := [] }
    store :=
      { runtime := { module := mergeTwoModule, host := {} },
        wasm := mergeTwoKeepInitialStore } }

def mergeTwoKeepFinalStore : MachineStore Unit :=
  { mergeTwoKeepConfig.store with
    wasm :=
      { mergeTwoKeepConfig.store.wasm with
        mem := (mergeTwoKeepConfig.store.wasm.mem.write32 0 4).write32 4 9 } }

-- Regression for the non-swapping branch of the same merge kernel.
set_option maxRecDepth 10000 in
theorem merge_two_keep_run :
    (runSteps 18 mergeTwoKeepConfig).result =
      .success [] mergeTwoKeepFinalStore := by
  rfl

theorem merge_two_both_branches_match_big_step :
    (runSteps 18 mergeTwoConfig).result.values? =
        some (runValues 18 mergeTwoModule 0 mergeTwoInitialStore []) ∧
      (runSteps 18 mergeTwoKeepConfig).result.values? =
        some (runValues 18 mergeTwoModule 0 mergeTwoKeepInitialStore []) := by
  native_decide

def controlModule : Module :=
  { funcs :=
      [ { body :=
          [ .const 99,
            .block 0 1 [.const 7, .br 0, .const 8],
            .add ],
          results := [.i32] }
      , { body :=
          [ .const 3, .localSet 0,
            .loop 0 0
              [ .localGet 0, .const 1, .sub, .localSet 0,
                .localGet 0, .br_if 0 ],
            .localGet 0 ],
          locals := [.i32], results := [.i32] }
      , { body :=
          [ .const 1,
            .iff 0 1 [.const 42] [.const 0] ],
          results := [.i32] } ] }

def controlRuntime : RuntimeEnv Unit :=
  { module := controlModule, host := {} }

def blockBranchConfig : Config Unit :=
  { expr := .running
      { locals := {}, code := controlModule.funcs[0]!.body,
        resultArity := 1, callerRemainder := [] }
    store := { runtime := controlRuntime, wasm := controlModule.initialStore } }

def loopConfig : Config Unit :=
  { expr := .running
      { locals := { locals := [.i32 0] }, code := controlModule.funcs[1]!.body,
        resultArity := 1, callerRemainder := [] }
    store := { runtime := controlRuntime, wasm := controlModule.initialStore } }

def ifConfig : Config Unit :=
  { expr := .running
      { locals := {}, code := controlModule.funcs[2]!.body,
        resultArity := 1, callerRemainder := [] }
    store := { runtime := controlRuntime, wasm := controlModule.initialStore } }

theorem block_branch_small_step :
    (runSteps 7 blockBranchConfig).result.values? = some [.i32 106] := by
  native_decide

theorem loop_small_step :
    (runSteps 24 loopConfig).result.values? = some [.i32 0] := by
  native_decide

theorem if_small_step :
    (runSteps 5 ifConfig).result.values? = some [.i32 42] := by
  native_decide

theorem block_branch_relational :
    TerminatesWith blockBranchConfig (fun values _ => values = [.i32 106]) := by
  apply runSteps_success_terminates
    (fuel := 7) (store := blockBranchConfig.store)
  rfl
  native_decide
theorem control_matches_big_step :
    (runSteps 7 blockBranchConfig).result.values? =
        some (runValues 12 controlModule 0 controlModule.initialStore []) ∧
      (runSteps 24 loopConfig).result.values? =
        some (runValues 30 controlModule 1 controlModule.initialStore []) ∧
      (runSteps 5 ifConfig).result.values? =
        some (runValues 12 controlModule 2 controlModule.initialStore []) := by
  native_decide

def functionLabelBranchModule : Module :=
  { funcs :=
      [ { body := [.const 42, .br 0, .const 0], results := [.i32] }
      , { body :=
          [.block 0 0 [.const 42, .br 1, .const 0], .const 1],
          results := [.i32] } ] }

def functionLabelBranchConfig (index : Nat) : Config Unit :=
  { expr := .running
      { locals := {}, code := functionLabelBranchModule.funcs[index]!.body,
        resultArity := 1, callerRemainder := [] }
    store :=
      { runtime := { module := functionLabelBranchModule, host := {} },
        wasm := functionLabelBranchModule.initialStore } }

theorem branch_to_function_label :
    (runSteps 3 (functionLabelBranchConfig 0)).result.values? =
      some [.i32 42] := by
  native_decide

theorem branch_through_block_to_function_label :
    (runSteps 4 (functionLabelBranchConfig 1)).result.values? =
      some [.i32 42] := by
  native_decide

theorem function_label_branch_relational :
    TerminatesWith (functionLabelBranchConfig 1)
      (fun values _ => values = [.i32 42]) := by
  apply runSteps_success_terminates
    (fuel := 4) (store := (functionLabelBranchConfig 1).store)
  rfl
  native_decide

theorem function_label_branch_matches_big_step :
    (runSteps 3 (functionLabelBranchConfig 0)).result.values? =
        some (runValues 8 functionLabelBranchModule 0
          functionLabelBranchModule.initialStore []) ∧
      (runSteps 4 (functionLabelBranchConfig 1)).result.values? =
        some (runValues 8 functionLabelBranchModule 1
          functionLabelBranchModule.initialStore []) := by
  native_decide

def callModule : Module :=
  { funcs :=
      [ { body := [.const 41, .call 1], results := [.i32] }
      , { params := [.i32],
          body := [.localGet 0, .const 1, .add],
          results := [.i32] } ] }

def callRuntime : RuntimeEnv Unit :=
  { module := callModule, host := {} }

def callConfig : Config Unit :=
  { expr := .running
      { locals := {}, code := callModule.funcs[0]!.body,
        resultArity := 1, callerRemainder := [] }
    store := { runtime := callRuntime, wasm := callModule.initialStore } }

theorem direct_call_small_step :
    (runSteps 7 callConfig).result.values? = some [.i32 42] := by
  native_decide

theorem direct_call_matches_big_step :
    (runSteps 7 callConfig).result.values? =
      some (runValues 12 callModule 0 callModule.initialStore []) := by
  native_decide

def factorialModule : Module :=
  { funcs :=
      [ { params := [.i32],
          body :=
            [ .localGet 0, .eqz,
              .iff 0 1
                [.const 1]
                [ .localGet 0, .localGet 0, .const 1, .sub,
                  .call 0, .mul ] ],
          results := [.i32] } ] }

def factorialRuntime : RuntimeEnv Unit :=
  { module := factorialModule, host := {} }

def factorialConfig : Config Unit :=
  { expr := .running
      { locals := factorialModule.funcs[0]!.toLocals [.i32 5],
        code := factorialModule.funcs[0]!.body,
        resultArity := 1, callerRemainder := [] }
    store :=
      { runtime := factorialRuntime, wasm := factorialModule.initialStore } }

theorem factorial_small_step :
    (runSteps 61 factorialConfig).result.values? = some [.i32 120] := by
  native_decide

theorem factorial_relational :
    TerminatesWith factorialConfig (fun values _ => values = [.i32 120]) := by
  apply runSteps_success_terminates
    (fuel := 61) (store := factorialConfig.store)
  rfl
  native_decide
theorem factorial_matches_big_step :
    (runSteps 61 factorialConfig).result.values? =
      some (runValues 20 factorialModule 0 factorialModule.initialStore [.i32 5]) := by
  native_decide

def parametricModule : Module :=
  { funcs :=
      [ { body :=
          [ .const 10, .const 20, .const 1, .select,
            .const 99, .drop ],
          results := [.i32] }
      , { body :=
          [ .const 42,
            .block 0 1
              [.const 99, .const 0, .brTable [0] 0, .drop] ],
          results := [.i32] } ] }

def parametricConfig (index : Nat) : Config Unit :=
  { expr := .running
      { locals := {}, code := parametricModule.funcs[index]!.body,
        resultArity := 1, callerRemainder := [] }
    store :=
      { runtime := { module := parametricModule, host := {} },
        wasm := parametricModule.initialStore } }

theorem select_and_drop_small_step :
    (runSteps 7 (parametricConfig 0)).result.values? = some [.i32 10] := by
  native_decide

theorem br_table_small_step :
    (runSteps 6 (parametricConfig 1)).result.values? = some [.i32 99] := by
  native_decide

theorem parametric_matches_big_step :
    (runSteps 7 (parametricConfig 0)).result.values? =
        some (runValues 12 parametricModule 0 parametricModule.initialStore []) ∧
      (runSteps 6 (parametricConfig 1)).result.values? =
        some (runValues 12 parametricModule 1 parametricModule.initialStore []) := by
  native_decide

def tailCallModule : Module :=
  { funcs :=
      [ { body := [.returnCall 1], results := [.i32] }
      , { body := [.const 42], results := [.i32] } ] }

def tailCallConfig : Config Unit :=
  { expr := .running
      { locals := {}, code := tailCallModule.funcs[0]!.body,
        resultArity := 1, callerRemainder := [] }
    store :=
      { runtime := { module := tailCallModule, host := {} },
        wasm := tailCallModule.initialStore } }

theorem tail_call_small_step :
    (runSteps 3 tailCallConfig).result.values? = some [.i32 42] := by
  native_decide

theorem tail_call_matches_big_step :
    (runSteps 3 tailCallConfig).result.values? =
      some (runValues 8 tailCallModule 0 tailCallModule.initialStore []) := by
  native_decide

def i64ArithmeticModule : Module :=
  { funcs :=
      [ { body :=
          [ .constI64 6, .constI64 7, .mulI64,
            .constI64 2, .addI64, .constI64 1, .subI64 ],
          results := [.i64] } ] }

def i64ArithmeticConfig : Config Unit :=
  { expr := .running
      { locals := {}, code := i64ArithmeticModule.funcs[0]!.body,
        resultArity := 1, callerRemainder := [] }
    store :=
      { runtime := { module := i64ArithmeticModule, host := {} },
        wasm := i64ArithmeticModule.initialStore } }

theorem i64_arithmetic_small_step :
    (runSteps 8 i64ArithmeticConfig).result.values? = some [.i64 43] := by
  native_decide

theorem i64_arithmetic_matches_big_step :
    (runSteps 8 i64ArithmeticConfig).result.values? =
      some (runValues 12 i64ArithmeticModule 0
        i64ArithmeticModule.initialStore []) := by
  native_decide

def bitwiseModule : Module :=
  { funcs :=
      [ { body :=
          [ .const 0xF0F0, .const 0x0FF0, .and,
            .const 0xF0F0, .const 0x0FF0, .or,
            .const 0xF0F0, .const 0x0FF0, .xor,
            .const 1, .const 33, .shl,
            .const 0x80000000, .const 1, .shrU,
            .const 0x80000000, .const 1, .shrS,
            .const 0x12345678, .const 8, .rotl,
            .const 0x12345678, .const 8, .rotr ],
          results := List.replicate 8 .i32 }
      , { body :=
          [ .constI64 0xF0F0, .constI64 0x0FF0, .andI64,
            .constI64 1, .constI64 65, .shlI64,
            .constI64 0x8000000000000000, .constI64 1, .shrSI64,
            .constI64 0x0123456789ABCDEF, .constI64 8, .rotlI64,
            .constI64 0x0123456789ABCDEF, .constI64 8, .rotrI64 ],
          results := List.replicate 5 .i64 } ] }

def bitwiseConfig (index resultArity : Nat) : Config Unit :=
  { expr := .running
      { locals := {}, code := bitwiseModule.funcs[index]!.body,
        resultArity, callerRemainder := [] }
    store :=
      { runtime := { module := bitwiseModule, host := {} },
        wasm := bitwiseModule.initialStore } }

theorem i32_bitwise_small_step :
    (runSteps 25 (bitwiseConfig 0 8)).result.values? =
      some
        [.i32 0x78123456, .i32 0x34567812,
          .i32 0xC0000000, .i32 0x40000000,
          .i32 2, .i32 0xFF00, .i32 0xFFF0, .i32 0x00F0] := by
  native_decide

theorem i64_bitwise_small_step :
    (runSteps 16 (bitwiseConfig 1 5)).result.values? =
      some
        [.i64 0xEF0123456789ABCD, .i64 0x23456789ABCDEF01,
          .i64 0xC000000000000000, .i64 2, .i64 0x00F0] := by
  native_decide

theorem bitwise_matches_big_step :
    (runSteps 25 (bitwiseConfig 0 8)).result.values? =
        some (runValues 40 bitwiseModule 0 bitwiseModule.initialStore []) ∧
      (runSteps 16 (bitwiseConfig 1 5)).result.values? =
        some (runValues 30 bitwiseModule 1 bitwiseModule.initialStore []) := by
  native_decide

def divisionModule : Module :=
  { funcs :=
      [ { body :=
          [ .const 20, .const 3, .divU,
            .const 0xFFFFFFEC, .const 3, .divS,
            .const 20, .const 6, .remU,
            .const 0xFFFFFFEC, .const 6, .remS ],
          results := List.replicate 4 .i32 }
      , { body :=
          [ .constI64 20, .constI64 3, .divUI64,
            .constI64 0xFFFFFFFFFFFFFFEC, .constI64 3, .divSI64,
            .constI64 20, .constI64 6, .remUI64,
            .constI64 0xFFFFFFFFFFFFFFEC, .constI64 6, .remSI64 ],
          results := List.replicate 4 .i64 }
      , { body := [.const 1, .const 0, .remU], results := [.i32] }
      , { body := [.const 0x80000000, .const 0xFFFFFFFF, .divS],
          results := [.i32] }
      , { body :=
          [.constI64 0x8000000000000000, .constI64 0xFFFFFFFFFFFFFFFF, .divSI64],
          results := [.i64] } ] }

def divisionConfig (index resultArity : Nat) : Config Unit :=
  { expr := .running
      { locals := {}, code := divisionModule.funcs[index]!.body,
        resultArity, callerRemainder := [] }
    store :=
      { runtime := { module := divisionModule, host := {} },
        wasm := divisionModule.initialStore } }

theorem i32_division_small_step :
    (runSteps 13 (divisionConfig 0 4)).result.values? =
      some [.i32 0xFFFFFFFE, .i32 2, .i32 0xFFFFFFFA, .i32 6] := by
  native_decide

theorem i64_division_small_step :
    (runSteps 13 (divisionConfig 1 4)).result.values? =
      some
        [.i64 0xFFFFFFFFFFFFFFFE, .i64 2,
          .i64 0xFFFFFFFFFFFFFFFA, .i64 6] := by
  native_decide

theorem division_matches_big_step :
    (runSteps 13 (divisionConfig 0 4)).result.values? =
        some (runValues 20 divisionModule 0 divisionModule.initialStore []) ∧
      (runSteps 13 (divisionConfig 1 4)).result.values? =
        some (runValues 20 divisionModule 1 divisionModule.initialStore []) := by
  native_decide

def trapReason? : RunnerResult α → Option TrapReason
  | .trapped reason _ => some reason
  | _ => none

theorem remainder_by_zero_traps :
    trapReason? (runSteps 4 (divisionConfig 2 1)).result =
      some .integerDivideByZero := by
  native_decide

theorem signed_i32_overflow_traps :
    trapReason? (runSteps 4 (divisionConfig 3 1)).result =
      some .integerOverflow := by
  native_decide

theorem signed_i64_overflow_traps :
    trapReason? (runSteps 4 (divisionConfig 4 1)).result =
      some .integerOverflow := by
  native_decide

theorem remainder_by_zero_trapsWith :
    TrapsWith (divisionConfig 2 1) .integerDivideByZero
      (fun store => store = (divisionConfig 2 1).store) := by
  apply runSteps_trapped_trapsWith (fuel := 4)
    (store := (divisionConfig 2 1).store) <;> rfl

theorem signed_i32_overflow_trapsWith :
    TrapsWith (divisionConfig 3 1) .integerOverflow
      (fun store => store = (divisionConfig 3 1).store) := by
  apply runSteps_trapped_trapsWith (fuel := 4)
    (store := (divisionConfig 3 1).store) <;> rfl

theorem signed_i64_overflow_trapsWith :
    TrapsWith (divisionConfig 4 1) .integerOverflow
      (fun store => store = (divisionConfig 4 1).store) := by
  apply runSteps_trapped_trapsWith (fuel := 4)
    (store := (divisionConfig 4 1).store) <;> rfl

def integerComparisonModule : Module :=
  { funcs :=
      [ { body :=
          [ .const 0xFFFFFFFF, .const 0, .ltS,
            .const 0, .const 0xFFFFFFFF, .gtS,
            .const 0xFFFFFFFF, .const 0, .leS,
            .const 0, .const 0xFFFFFFFF, .geS,
            .constI64 0, .eqzI64,
            .constI64 5, .constI64 5, .eqI64,
            .constI64 5, .constI64 6, .neI64,
            .constI64 1, .constI64 2, .ltUI64,
            .constI64 0xFFFFFFFFFFFFFFFF, .constI64 0, .ltSI64,
            .constI64 2, .constI64 1, .gtUI64,
            .constI64 0, .constI64 0xFFFFFFFFFFFFFFFF, .gtSI64,
            .constI64 1, .constI64 1, .leUI64,
            .constI64 0xFFFFFFFFFFFFFFFF, .constI64 0, .leSI64,
            .constI64 2, .constI64 1, .geUI64,
            .constI64 0, .constI64 0xFFFFFFFFFFFFFFFF, .geSI64 ],
          results := List.replicate 15 .i32 } ] }

def integerComparisonConfig : Config Unit :=
  { expr := .running
      { locals := {}, code := integerComparisonModule.funcs[0]!.body,
        resultArity := 15, callerRemainder := [] }
    store :=
      { runtime := { module := integerComparisonModule, host := {} },
        wasm := integerComparisonModule.initialStore } }

theorem integer_comparisons_small_step :
    (runSteps 45 integerComparisonConfig).result.values? =
      some (List.replicate 15 (.i32 1)) := by
  native_decide

theorem integer_comparisons_match_big_step :
    (runSteps 45 integerComparisonConfig).result.values? =
      some (runValues 60 integerComparisonModule 0
        integerComparisonModule.initialStore []) := by
  native_decide

def integerConversionModule : Module :=
  { funcs :=
      [ { body :=
          [ .constI64 0x123456789ABCDEF0, .wrapI64,
            .const 0xFFFFFFFF, .extendUI32,
            .const 0xFFFFFFFF, .extendSI32,
            .const 0x80, .extend8S,
            .const 0x8000, .extend16S,
            .constI64 0x80, .extend8SI64,
            .constI64 0x8000, .extend16SI64,
            .constI64 0x80000000, .extend32SI64 ],
          results :=
            [.i32, .i64, .i64, .i32, .i32, .i64, .i64, .i64] } ] }

def integerConversionConfig : Config Unit :=
  { expr := .running
      { locals := {}, code := integerConversionModule.funcs[0]!.body,
        resultArity := 8, callerRemainder := [] }
    store :=
      { runtime := { module := integerConversionModule, host := {} },
        wasm := integerConversionModule.initialStore } }

theorem integer_conversions_small_step :
    (runSteps 17 integerConversionConfig).result.values? =
      some
        [ .i64 0xFFFFFFFF80000000, .i64 0xFFFFFFFFFFFF8000,
          .i64 0xFFFFFFFFFFFFFF80, .i32 0xFFFF8000,
          .i32 0xFFFFFF80, .i64 0xFFFFFFFFFFFFFFFF,
          .i64 0x00000000FFFFFFFF, .i32 0x9ABCDEF0 ] := by
  native_decide

theorem integer_conversions_match_big_step :
    (runSteps 17 integerConversionConfig).result.values? =
      some (runValues 25 integerConversionModule 0
        integerConversionModule.initialStore []) := by
  native_decide

def referenceModule : Module :=
  { funcs :=
      [ { body :=
          [ .refNull, .refIsNull,
            .refFunc 0, .refIsNull,
            .refNullExtern, .refIsNull,
            .refNullExn, .refIsNull ],
          results := List.replicate 4 .i32 }
      , { body := [.refNull, .refAsNonNull], results := [.funcref] } ] }

def referenceConfig (index resultArity : Nat) : Config Unit :=
  { expr := .running
      { locals := {}, code := referenceModule.funcs[index]!.body,
        resultArity, callerRemainder := [] }
    store :=
      { runtime := { module := referenceModule, host := {} },
        wasm := referenceModule.initialStore } }

theorem reference_values_small_step :
    (runSteps 9 (referenceConfig 0 4)).result.values? =
      some [.i32 1, .i32 1, .i32 0, .i32 1] := by
  native_decide

theorem reference_values_relational :
    TerminatesWith (referenceConfig 0 4)
      (fun values _ => values = [.i32 1, .i32 1, .i32 0, .i32 1]) := by
  apply runSteps_success_terminates
    (fuel := 9) (store := (referenceConfig 0 4).store)
  rfl
  native_decide
theorem null_as_non_null_traps :
    trapReason? (runSteps 2 (referenceConfig 1 1)).result =
      some .nullReference := by
  native_decide

theorem null_as_non_null_trapsWith :
    TrapsWith (referenceConfig 1 1) .nullReference
      (fun store => store = (referenceConfig 1 1).store) := by
  apply runSteps_trapped_trapsWith (fuel := 2)
    (store := (referenceConfig 1 1).store)
  · rfl
  · rfl

theorem reference_values_match_big_step :
    (runSteps 9 (referenceConfig 0 4)).result.values? =
      some (runValues 15 referenceModule 0 referenceModule.initialStore []) := by
  native_decide

def tableModule : Module :=
  { tables := [{ min := 2 }]
    funcs :=
      [ { body :=
          [ .const 0, .refFunc 0, .tableSet 0,
            .const 0, .tableGet 0, .refIsNull,
            .const 1, .tableGet 0, .refIsNull,
            .tableSize 0 ],
          results := [.i32, .i32, .i32] }
      , { body := [.const 2, .tableGet 0], results := [.funcref] } ] }

def tableConfig (index resultArity : Nat) : Config Unit :=
  { expr := .running
      { locals := {}, code := tableModule.funcs[index]!.body,
        resultArity, callerRemainder := [] }
    store :=
      { runtime := { module := tableModule, host := {} },
        wasm := tableModule.initialStore } }

def tableFinalStore : MachineStore Unit :=
  { (tableConfig 0 3).store with
    wasm :=
      { (tableConfig 0 3).store.wasm with
        tables := [[.funcref (some 0), .funcref none]] } }

theorem table_read_write_small_step :
    (runSteps 11 (tableConfig 0 3)).result.values? =
      some [.i32 2, .i32 1, .i32 0] := by
  native_decide

theorem table_read_write_relational :
    TerminatesWith (tableConfig 0 3)
      (fun values store =>
        values = [.i32 2, .i32 1, .i32 0] ∧
          store.wasm.tables[0]? =
            some [.funcref (some 0), .funcref none]) := by
  apply runSteps_success_terminates
    (fuel := 11) (store := tableFinalStore)
  rfl
  · constructor <;> rfl

theorem table_get_out_of_bounds_traps :
    trapReason? (runSteps 2 (tableConfig 1 1)).result =
      some .outOfBoundsTable := by
  native_decide

theorem table_get_out_of_bounds_trapsWith :
    TrapsWith (tableConfig 1 1) .outOfBoundsTable
      (fun store => store = (tableConfig 1 1).store) := by
  apply runSteps_trapped_trapsWith (fuel := 2)
    (store := (tableConfig 1 1).store)
  · rfl
  · rfl

theorem table_read_write_matches_big_step :
    (runSteps 11 (tableConfig 0 3)).result.values? =
      some (runValues 18 tableModule 0 tableModule.initialStore []) := by
  native_decide

def tableBulkModule : Module :=
  { tables := [{ min := 4, max := some 6 }]
    funcs :=
      [ { body :=
          [ .const 0, .refFunc 0, .const 2, .tableFill 0,
            .const 1, .const 0, .const 3, .tableCopy 0 0,
            .refNull, .const 2, .tableGrow 0,
            .tableSize 0 ],
          results := [.i32, .i32] }
      , { body := [.refNull, .const 3, .tableGrow 0], results := [.i32] }
      , { body := [.const 3, .refNull, .const 2, .tableFill 0],
          results := [] } ] }

def tableBulkConfig (index resultArity : Nat) : Config Unit :=
  { expr := .running
      { locals := {}, code := tableBulkModule.funcs[index]!.body,
        resultArity, callerRemainder := [] }
    store :=
      { runtime := { module := tableBulkModule, host := {} },
        wasm := tableBulkModule.initialStore } }

def tableBulkFinalStore : MachineStore Unit :=
  { (tableBulkConfig 0 2).store with
    wasm :=
      { (tableBulkConfig 0 2).store.wasm with
        tables :=
          [[.funcref (some 0), .funcref (some 0), .funcref (some 0),
            .funcref none, .funcref none, .funcref none]] } }

theorem table_bulk_small_step :
    (runSteps 13 (tableBulkConfig 0 2)).result =
      .success [.i32 6, .i32 4] tableBulkFinalStore := by
  rfl
theorem table_bulk_relational :
    TerminatesWith (tableBulkConfig 0 2)
      (fun values store =>
        values = [.i32 6, .i32 4] ∧
          store.wasm.tables = tableBulkFinalStore.wasm.tables) := by
  apply runSteps_success_terminates
    (fuel := 13) (store := tableBulkFinalStore)
  · rfl
  · exact ⟨rfl, rfl⟩

theorem table_grow_failure_is_atomic :
    (runSteps 4 (tableBulkConfig 1 1)).result =
      .success [.i32 0xFFFFFFFF] (tableBulkConfig 1 1).store := by
  rfl
theorem table_fill_out_of_bounds_traps_atomically :
    (runSteps 4 (tableBulkConfig 2 0)).result =
      .trapped .outOfBoundsTable (tableBulkConfig 2 0).store := by
  rfl
theorem table_fill_out_of_bounds_trapsWith :
    TrapsWith (tableBulkConfig 2 0) .outOfBoundsTable
      (fun store => store = (tableBulkConfig 2 0).store) := by
  apply runSteps_trapped_trapsWith
    table_fill_out_of_bounds_traps_atomically
  rfl
theorem table_bulk_matches_big_step :
    (runSteps 13 (tableBulkConfig 0 2)).result.values? =
      some (runValues 20 tableBulkModule 0 tableBulkModule.initialStore []) := by
  native_decide

def elementInitModule (is64 : Bool) : Module :=
  { tables := [{ min := 4, is64 }]
    elements := [{ funcs := [some 0, none, some 0] }]
    funcs :=
      [ { body :=
          [ (if is64 then .constI64 1 else .const 1),
            .const 0, .const 3, .tableInit 0 0,
            .elemDrop 0,
            (if is64 then .constI64 1 else .const 1),
            .tableGet 0, .refIsNull,
            (if is64 then .constI64 2 else .const 2),
            .tableGet 0, .refIsNull ],
          results := [.i32, .i32] }
      , { body :=
          [ .elemDrop 0,
            (if is64 then .constI64 0 else .const 0),
            .const 0, .const 1, .tableInit 0 0 ],
          results := [] } ] }

def elementInitConfig (is64 : Bool) (index resultArity : Nat) : Config Unit :=
  { expr := .running
      { locals := {}, code := (elementInitModule is64).funcs[index]!.body,
        resultArity, callerRemainder := [] }
    store :=
      { runtime := { module := elementInitModule is64, host := {} },
        wasm := (elementInitModule is64).initialStore } }

def elementInitFinalStore (is64 : Bool) : MachineStore Unit :=
  { (elementInitConfig is64 0 2).store with
    wasm :=
      { (elementInitConfig is64 0 2).store.wasm with
        tables :=
          [[.funcref none, .funcref (some 0),
            .funcref none, .funcref (some 0)]]
        elementSegments := [none] } }

def elementDroppedStore (is64 : Bool) : MachineStore Unit :=
  { (elementInitConfig is64 1 0).store with
    wasm :=
      { (elementInitConfig is64 1 0).store.wasm with
        elementSegments := [none] } }

theorem element_init_table32_run :
    (runSteps 12 (elementInitConfig false 0 2)).result =
      .success [.i32 1, .i32 0] (elementInitFinalStore false) := by
  rfl
theorem element_init_table64_run :
    (runSteps 12 (elementInitConfig true 0 2)).result =
      .success [.i32 1, .i32 0] (elementInitFinalStore true) := by
  rfl
theorem element_init_relational (is64 : Bool) :
    TerminatesWith (elementInitConfig is64 0 2)
      (fun values store =>
        values = [.i32 1, .i32 0] ∧
          store.wasm.tables = (elementInitFinalStore is64).wasm.tables ∧
          store.wasm.elementSegments = [none]) := by
  apply runSteps_success_terminates
    (fuel := 12) (store := elementInitFinalStore is64)
  · cases is64 <;> rfl
  · exact ⟨rfl, rfl, rfl⟩

theorem table_init_after_drop_traps_atomically (is64 : Bool) :
    (runSteps 5 (elementInitConfig is64 1 0)).result =
      .trapped .outOfBoundsTable (elementDroppedStore is64) := by
  cases is64 <;> rfl
theorem table_init_after_drop_trapsWith (is64 : Bool) :
    TrapsWith (elementInitConfig is64 1 0) .outOfBoundsTable
      (fun store => store = elementDroppedStore is64) := by
  apply runSteps_trapped_trapsWith
    (table_init_after_drop_traps_atomically is64)
  rfl

theorem element_init_matches_big_step (is64 : Bool) :
    (runSteps 12 (elementInitConfig is64 0 2)).result.values? =
      some (runValues 20 (elementInitModule is64) 0
        (elementInitModule is64).initialStore []) := by
  cases is64 <;> native_decide

def indirectCallModule : Module :=
  { types :=
      [{ results := [.i32] }, { results := [.i64] }]
    tables := [{ min := 3 }]
    elements :=
      [{ tableIdx := some 0, offset := some 0,
         funcs := [some 0, some 1, none] }]
    funcs :=
      [ { body := [.const 42], results := [.i32] }
      , { body := [.constI64 7], results := [.i64] }
      , { body := [.const 0, .callIndirect 0 0], results := [.i32] }
      , { body := [.const 0, .returnCallIndirect 0 0], results := [.i32] }
      , { body := [.refFunc 0, .callRef 0], results := [.i32] }
      , { body := [.refFunc 0, .returnCallRef 0], results := [.i32] }
      , { body := [.const 3, .callIndirect 0 0], results := [.i32] }
      , { body := [.const 2, .callIndirect 0 0], results := [.i32] }
      , { body := [.const 1, .callIndirect 0 0], results := [.i32] }
      , { body := [.refNull, .callRef 0], results := [.i32] } ] }

def indirectCallConfig (index : Nat) : Config Unit :=
  { expr := .running
      { locals := {}, code := indirectCallModule.funcs[index]!.body,
        resultArity := 1, callerRemainder := [] }
    store :=
      { runtime := { module := indirectCallModule, host := {} },
        wasm := indirectCallModule.initialStore } }

theorem call_indirect_run :
    (runSteps 5 (indirectCallConfig 2)).result.values? =
      some [.i32 42] := by
  native_decide

theorem return_call_indirect_run :
    (runSteps 4 (indirectCallConfig 3)).result.values? =
      some [.i32 42] := by
  native_decide

theorem call_ref_run :
    (runSteps 5 (indirectCallConfig 4)).result.values? =
      some [.i32 42] := by
  native_decide

theorem return_call_ref_run :
    (runSteps 4 (indirectCallConfig 5)).result.values? =
      some [.i32 42] := by
  native_decide

theorem call_indirect_relational :
    TerminatesWith (indirectCallConfig 2)
      (fun values _ => values = [.i32 42]) := by
  apply runSteps_success_terminates
    (fuel := 5) (store := (indirectCallConfig 2).store)
  · rfl
  · rfl
theorem call_indirect_undefined_traps :
    trapReason? (runSteps 2 (indirectCallConfig 6)).result =
      some .undefinedElement := by
  native_decide

theorem call_indirect_uninitialized_traps :
    trapReason? (runSteps 2 (indirectCallConfig 7)).result =
      some (.uninitializedElement 2) := by
  native_decide

theorem call_indirect_type_mismatch_traps :
    trapReason? (runSteps 2 (indirectCallConfig 8)).result =
      some .indirectCallTypeMismatch := by
  native_decide

theorem call_ref_null_traps :
    trapReason? (runSteps 2 (indirectCallConfig 9)).result =
      some .nullFunctionReference := by
  native_decide

theorem call_indirect_undefined_trapsWith :
    TrapsWith (indirectCallConfig 6) .undefinedElement
      (fun store => store = (indirectCallConfig 6).store) := by
  apply runSteps_trapped_trapsWith (fuel := 2)
    (store := (indirectCallConfig 6).store) <;> rfl

theorem call_indirect_uninitialized_trapsWith :
    TrapsWith (indirectCallConfig 7) (.uninitializedElement 2)
      (fun store => store = (indirectCallConfig 7).store) := by
  apply runSteps_trapped_trapsWith (fuel := 2)
    (store := (indirectCallConfig 7).store) <;> rfl

theorem call_indirect_type_mismatch_trapsWith :
    TrapsWith (indirectCallConfig 8) .indirectCallTypeMismatch
      (fun store => store = (indirectCallConfig 8).store) := by
  apply runSteps_trapped_trapsWith (fuel := 2)
    (store := (indirectCallConfig 8).store) <;> rfl

theorem call_ref_null_trapsWith :
    TrapsWith (indirectCallConfig 9) .nullFunctionReference
      (fun store => store = (indirectCallConfig 9).store) := by
  apply runSteps_trapped_trapsWith (fuel := 2)
    (store := (indirectCallConfig 9).store) <;> rfl

theorem indirect_calls_match_big_step :
    (runSteps 5 (indirectCallConfig 2)).result.values? =
        some (runValues 8 indirectCallModule 2
          indirectCallModule.initialStore []) ∧
      (runSteps 4 (indirectCallConfig 3)).result.values? =
        some (runValues 8 indirectCallModule 3
          indirectCallModule.initialStore []) ∧
      (runSteps 5 (indirectCallConfig 4)).result.values? =
        some (runValues 8 indirectCallModule 4
          indirectCallModule.initialStore []) ∧
      (runSteps 4 (indirectCallConfig 5)).result.values? =
        some (runValues 8 indirectCallModule 5
          indirectCallModule.initialStore []) := by
  native_decide

def scalarFloatModule : Module :=
  { funcs :=
      [ { body :=
          [ .f32Const (1.5 : Float32).toBits,
            .f32Const (2.0 : Float32).toBits, .f32Mul,
            .f32Const (-3.5 : Float32).toBits, .f32Abs,
            .f32Const (4.0 : Float32).toBits, .f32Sqrt,
            .f32Const (1.0 : Float32).toBits,
            .f32Const (2.0 : Float32).toBits, .f32Lt ],
          results := [.f32, .f32, .f32, .i32] }
      , { body :=
          [ .f64Const (1.5 : Float).toBits,
            .f64Const (2.5 : Float).toBits, .f64Add,
            .f64Const (7.0 : Float).toBits,
            .f64Const (3.0 : Float).toBits, .f64Min,
            .f64Const (3.5 : Float).toBits, .f64Nearest,
            .f64Const (2.0 : Float).toBits,
            .f64Const (-1.0 : Float).toBits, .f64Copysign ],
          results := [.f64, .f64, .f64, .f64] }
      , { body :=
          [ .const 7, .f32ConvertI32S,
            .constI64 9, .f64ConvertI64U,
            .const (1.0 : Float32).toBits, .f32ReinterpretI32,
            .f64Const (2.5 : Float).toBits, .i64ReinterpretF64,
            .f32Const (3.9 : Float32).toBits, .i32TruncSatF32S ],
          results := [.f32, .f64, .f32, .i64, .i32] }
      , { body :=
          [ .f32Const (7.75 : Float32).toBits, .i32TruncF32S ],
          results := [.i32] }
      , { body := [ .f32Const 0x7FC00000, .i32TruncF32S ],
          results := [.i32] }
      , { body :=
          [ .f64Const (1.0e300 : Float).toBits, .i32TruncF64S ],
          results := [.i32] } ] }

def scalarFloatConfig (index resultArity : Nat) : Config Unit :=
  { expr := .running
      { locals := {}, code := scalarFloatModule.funcs[index]!.body,
        resultArity, callerRemainder := [] }
    store :=
      { runtime := { module := scalarFloatModule, host := {} },
        wasm := scalarFloatModule.initialStore } }

theorem f32_scalar_float_run :
    (runSteps 11 (scalarFloatConfig 0 4)).result.values? =
      some
        [ .i32 1, .f32 (2.0 : Float32).toBits,
          .f32 (3.5 : Float32).toBits,
          .f32 (3.0 : Float32).toBits ] := by
  native_decide

theorem f64_scalar_float_run :
    (runSteps 12 (scalarFloatConfig 1 4)).result.values? =
      some
        [ .f64 (-2.0 : Float).toBits, .f64 (4.0 : Float).toBits,
          .f64 (3.0 : Float).toBits, .f64 (4.0 : Float).toBits ] := by
  native_decide

theorem scalar_float_conversion_run :
    (runSteps 11 (scalarFloatConfig 2 5)).result.values? =
      some
        [ .i32 3, .i64 (2.5 : Float).toBits,
          .f32 (1.0 : Float32).toBits, .f64 (9.0 : Float).toBits,
          .f32 (7.0 : Float32).toBits ] := by
  native_decide

theorem scalar_float_truncation_run :
    (runSteps 3 (scalarFloatConfig 3 1)).result.values? =
      some [.i32 7] := by
  native_decide

theorem scalar_float_nan_traps :
    (match (runSteps 3 (scalarFloatConfig 4 1)).result with
      | .trapped reason _ => some reason
      | _ => none) = some .invalidConversionToInteger := by
  native_decide

theorem scalar_float_overflow_traps :
    (match (runSteps 3 (scalarFloatConfig 5 1)).result with
      | .trapped reason _ => some reason
      | _ => none) = some .integerOverflow := by
  native_decide

theorem scalar_float_nan_trapsWith :
    TrapsWith (scalarFloatConfig 4 1) .invalidConversionToInteger
      (fun _ => True) := by
  apply runSteps_trapReason_trapsWith (fuel := 3)
  native_decide

theorem scalar_float_overflow_trapsWith :
    TrapsWith (scalarFloatConfig 5 1) .integerOverflow
      (fun _ => True) := by
  apply runSteps_trapReason_trapsWith (fuel := 3)
  native_decide

theorem scalar_float_relational :
    TerminatesWith (scalarFloatConfig 0 4)
      (fun values _ =>
        values =
          [ .i32 1, .f32 (2.0 : Float32).toBits,
            .f32 (3.5 : Float32).toBits,
            .f32 (3.0 : Float32).toBits ]) := by
  have hvalues := f32_scalar_float_run
  cases hresult : (runSteps 11 (scalarFloatConfig 0 4)).result with
  | success values store =>
      rw [hresult] at hvalues
      have hpost :
          values =
            [ .i32 1, .f32 (2.0 : Float32).toBits,
              .f32 (3.5 : Float32).toBits,
              .f32 (3.0 : Float32).toBits ] := by
        simpa [RunnerResult.values?] using hvalues
      refine ⟨(runSteps 11 (scalarFloatConfig 0 4)).trace,
        values, store, ?_, hpost⟩
      apply runSteps_sound
      simp [hresult, RunnerResult.finalConfig?]
  | trapped reason store =>
      rw [hresult] at hvalues
      simp [RunnerResult.values?] at hvalues
  | outOfFuel config =>
      rw [hresult] at hvalues
      simp [RunnerResult.values?] at hvalues
  | internalError error config =>
      rw [hresult] at hvalues
      simp [RunnerResult.values?] at hvalues

theorem scalar_floats_match_big_step :
    (runSteps 11 (scalarFloatConfig 0 4)).result.values? =
        some (runValues 16 scalarFloatModule 0
          scalarFloatModule.initialStore []) ∧
      (runSteps 12 (scalarFloatConfig 1 4)).result.values? =
        some (runValues 16 scalarFloatModule 1
          scalarFloatModule.initialStore []) ∧
      (runSteps 11 (scalarFloatConfig 2 5)).result.values? =
        some (runValues 16 scalarFloatModule 2
          scalarFloatModule.initialStore []) ∧
      (runSteps 3 (scalarFloatConfig 3 1)).result.values? =
        some (runValues 16 scalarFloatModule 3
          scalarFloatModule.initialStore []) := by
  native_decide

def floatMemoryModule : Module :=
  { funcs :=
      [ { body :=
          [ .const 32, .f32Const (1.25 : Float32).toBits, .f32Store 0,
            .constI64 40, .f64Const (-7.5 : Float).toBits, .f64Store 0,
            .const 32, .f32Load 0,
            .constI64 40, .f64Load 0 ],
          results := [.f32, .f64] } ],
    memory := some { pagesMin := 1 } }

def floatMemoryConfig : Config Unit :=
  { expr := .running
      { locals := {}, code := floatMemoryModule.funcs[0]!.body,
        resultArity := 2, callerRemainder := [] },
    store :=
      { runtime := { module := floatMemoryModule, host := {} },
        wasm := floatMemoryModule.initialStore } }

def floatMemoryResultMatches : RunnerResult Unit → Bool
  | .success _ store =>
    store.wasm.mem.read32 32 == (1.25 : Float32).toBits &&
      store.wasm.mem.read64 40 == (-7.5 : Float).toBits
  | _ => false

theorem float_memory_roundtrip_values :
    (runSteps 11 floatMemoryConfig).result.values? =
      some
        [ .f64 (-7.5 : Float).toBits, .f32 (1.25 : Float32).toBits ] := by
  native_decide

theorem float_memory_roundtrip_run :
    floatMemoryResultMatches (runSteps 11 floatMemoryConfig).result = true := by
  native_decide

/-- A clean physical-memory contract for scalar floating-point accesses:
loads preserve the exact IEEE bit patterns written by both stores. -/
theorem float_memory_roundtrip_relational :
    TerminatesWith floatMemoryConfig (fun values store =>
      values =
        [ .f64 (-7.5 : Float).toBits, .f32 (1.25 : Float32).toBits ] ∧
      store.wasm.mem.read32 32 = (1.25 : Float32).toBits ∧
      store.wasm.mem.read64 40 = (-7.5 : Float).toBits) := by
  cases hresult : (runSteps 11 floatMemoryConfig).result with
  | success values store =>
      have hvalues :
          values =
            [ .f64 (-7.5 : Float).toBits,
              .f32 (1.25 : Float32).toBits ] := by
        have hvaluesResult := float_memory_roundtrip_values
        rw [hresult] at hvaluesResult
        simpa [RunnerResult.values?] using hvaluesResult
      have hmemory :
          store.wasm.mem.read32 32 = (1.25 : Float32).toBits ∧
            store.wasm.mem.read64 40 = (-7.5 : Float).toBits := by
        simpa [hresult, floatMemoryResultMatches, Bool.and_eq_true] using
          float_memory_roundtrip_run
      have hpost :
          values =
              [ .f64 (-7.5 : Float).toBits,
                .f32 (1.25 : Float32).toBits ] ∧
            store.wasm.mem.read32 32 = (1.25 : Float32).toBits ∧
            store.wasm.mem.read64 40 = (-7.5 : Float).toBits := by
        exact ⟨hvalues, hmemory⟩
      refine ⟨(runSteps 11 floatMemoryConfig).trace,
        values, store, ?_, hpost⟩
      apply runSteps_sound
      simp [hresult, RunnerResult.finalConfig?]
  | trapped reason store =>
      simpa [hresult, floatMemoryResultMatches] using
        float_memory_roundtrip_run
  | outOfFuel config =>
      simpa [hresult, floatMemoryResultMatches] using
        float_memory_roundtrip_run
  | internalError error config =>
      simpa [hresult, floatMemoryResultMatches] using
        float_memory_roundtrip_run

theorem float_memory_roundtrip_partial :
    PartiallyMeets floatMemoryConfig (fun values store =>
      values =
        [ .f64 (-7.5 : Float).toBits, .f32 (1.25 : Float32).toBits ] ∧
      store.wasm.mem.read32 32 = (1.25 : Float32).toBits ∧
      store.wasm.mem.read64 40 = (-7.5 : Float).toBits) := by
  intro trace values store execution
  obtain ⟨runTrace, runValues, runStore, runExecution, hpost⟩ :=
    float_memory_roundtrip_relational
  obtain ⟨rfl, rfl⟩ :=
    steps_done_deterministic runExecution execution
  exact hpost

theorem float_memory_matches_big_step :
    (runSteps 11 floatMemoryConfig).result.values? =
      some (runValues 32 floatMemoryModule 0
        floatMemoryModule.initialStore []) := by
  native_decide

def simdModule : Module :=
  { funcs :=
      [ { body :=
          [ .vConst 1, .vConst 2, .vBinOp (.add .i32x4),
            .vExtractLane .i32x4 false 0 ],
          results := [.i32] },
        { body :=
          [ .vConst 0, .const 42, .vReplaceLane .i32x4 2,
            .vExtractLane .i32x4 false 2 ],
          results := [.i32] } ] }

def simdConfig (functionIndex : Nat) : Config Unit :=
  { expr := .running
      { locals := {}, code := simdModule.funcs[functionIndex]!.body,
        resultArity := 1, callerRemainder := [] },
    store :=
      { runtime := { module := simdModule, host := {} },
        wasm := simdModule.initialStore } }

theorem simd_add_and_extract :
    (runSteps 5 (simdConfig 0)).result.values? = some [.i32 3] := by
  native_decide

theorem simd_replace_and_extract :
    (runSteps 5 (simdConfig 1)).result.values? = some [.i32 42] := by
  native_decide

theorem simd_matches_big_step :
    (runSteps 5 (simdConfig 0)).result.values? =
        some (runValues 16 simdModule 0 simdModule.initialStore []) ∧
      (runSteps 5 (simdConfig 1)).result.values? =
        some (runValues 16 simdModule 1 simdModule.initialStore []) := by
  native_decide

def simdMemoryValue : BitVec 128 :=
  0x112233445566778899AABBCCDDEEFF00

def simdMemoryModule : Module :=
  { funcs :=
      [ { body :=
          [ .const 64, .vConst simdMemoryValue, .v128Store 0,
            .const 64, .v128Load 0 ],
          results := [.v128] } ],
    memory := some { pagesMin := 1 } }

def simdMemoryConfig : Config Unit :=
  { expr := .running
      { locals := {}, code := simdMemoryModule.funcs[0]!.body,
        resultArity := 1, callerRemainder := [] },
    store :=
      { runtime := { module := simdMemoryModule, host := {} },
        wasm := simdMemoryModule.initialStore } }

theorem simd_memory_roundtrip :
    (runSteps 6 simdMemoryConfig).result.values? =
      some [.v128 simdMemoryValue] := by
  native_decide

def simdMemoryPhysicalResult : RunnerResult Unit → Bool
  | .success _ store =>
    store.wasm.mem.read64 64 == UInt64.ofNat simdMemoryValue.toNat &&
      store.wasm.mem.read64 72 ==
        UInt64.ofNat (simdMemoryValue.toNat / 2 ^ 64)
  | _ => false

theorem simd_memory_physical_bytes :
    simdMemoryPhysicalResult (runSteps 6 simdMemoryConfig).result = true := by
  native_decide

theorem simd_memory_matches_big_step :
    (runSteps 6 simdMemoryConfig).result.values? =
      some (runValues 16 simdMemoryModule 0
        simdMemoryModule.initialStore []) := by
  native_decide

def simdMemoryVariantsModule : Module :=
  { funcs :=
      [ { body :=
          [ .const 96, .constI64 0x8070605040302010, .store64 0,
            .const 96, .v128LoadExt 8 false 0 ],
          results := [.v128] },
        { body :=
          [ .const 104, .const 0x1234, .store16 0,
            .const 104, .v128LoadSplat 16 0 ],
          results := [.v128] },
        { body :=
          [ .const 108, .const 0x89ABCDEF, .store32 0,
            .const 108, .v128LoadZero 32 0 ],
          results := [.v128] },
        { body :=
          [ .const 120, .vConst simdMemoryValue, .v128StoreLane 16 2 0,
            .const 120, .vConst 0, .v128LoadLane 16 5 0,
            .vExtractLane .i16x8 false 5 ],
          results := [.i32] } ],
    memory := some { pagesMin := 1 } }

def simdMemoryVariantsConfig (functionIndex : Nat) : Config Unit :=
  { expr := .running
      { locals := {},
        code := simdMemoryVariantsModule.funcs[functionIndex]!.body,
        resultArity := 1, callerRemainder := [] },
    store :=
      { runtime := { module := simdMemoryVariantsModule, host := {} },
        wasm := simdMemoryVariantsModule.initialStore } }

theorem simd_load_ext_unsigned :
    (runSteps 6 (simdMemoryVariantsConfig 0)).result.values? =
      some [.v128
        (Simd.ofLanes 16
          [0x10, 0x20, 0x30, 0x40, 0x50, 0x60, 0x70, 0x80])] := by
  native_decide

theorem simd_load_splat :
    (runSteps 6 (simdMemoryVariantsConfig 1)).result.values? =
      some [.v128 (Simd.ofLanes 16 (List.replicate 8 0x1234))] := by
  native_decide

theorem simd_load_zero :
    (runSteps 6 (simdMemoryVariantsConfig 2)).result.values? =
      some [.v128 (BitVec.ofNat 128 0x89ABCDEF)] := by
  native_decide

theorem simd_lane_store_load :
    (runSteps 8 (simdMemoryVariantsConfig 3)).result.values? =
      some [.i32 (UInt32.ofNat (Simd.getLane 16 2 simdMemoryValue))] := by
  native_decide

theorem simd_memory_variants_match_big_step :
    (runSteps 6 (simdMemoryVariantsConfig 0)).result.values? =
        some (runValues 16 simdMemoryVariantsModule 0
          simdMemoryVariantsModule.initialStore []) ∧
      (runSteps 6 (simdMemoryVariantsConfig 1)).result.values? =
        some (runValues 16 simdMemoryVariantsModule 1
          simdMemoryVariantsModule.initialStore []) ∧
      (runSteps 6 (simdMemoryVariantsConfig 2)).result.values? =
        some (runValues 16 simdMemoryVariantsModule 2
          simdMemoryVariantsModule.initialStore []) ∧
      (runSteps 8 (simdMemoryVariantsConfig 3)).result.values? =
        some (runValues 24 simdMemoryVariantsModule 3
          simdMemoryVariantsModule.initialStore []) := by
  native_decide

def simdMemoryVariantTrapConfig : Config Unit :=
  { expr := .running
      { locals := {},
        code := [.const 65535, .v128LoadSplat 64 0],
        resultArity := 1, callerRemainder := [] },
    store :=
      { runtime := { module := simdMemoryVariantsModule, host := {} },
        wasm := simdMemoryVariantsModule.initialStore } }

theorem simd_memory_variant_traps_structurally :
    (runSteps 2 simdMemoryVariantTrapConfig).result =
      .trapped .outOfBoundsMemory simdMemoryVariantTrapConfig.store := by
  rfl
theorem simd_memory_variant_trapsWith :
    TrapsWith simdMemoryVariantTrapConfig .outOfBoundsMemory
      (fun store => store = simdMemoryVariantTrapConfig.store) := by
  apply runSteps_trapped_trapsWith
    simd_memory_variant_traps_structurally
  rfl
def crossMemoryModule : Module :=
  { funcs :=
      [ { body :=
          [ .const 64, .const 32, .const 4, .memoryCopyBetween 0 1,
            .const 64, .load32 0 ],
          results := [.i32] } ],
    memory := some { pagesMin := 1 },
    extraMemories := [{ pagesMin := 1 }] }

def crossMemoryInitialStore : Store Unit :=
  let initial := crossMemoryModule.initialStore
  { initial with
    extraMems :=
      initial.extraMems.set 0
        (initial.extraMems[0]!.write32 32 0xC0DEC0DE) }

def crossMemoryConfig : Config Unit :=
  { expr := .running
      { locals := {}, code := crossMemoryModule.funcs[0]!.body,
        resultArity := 1, callerRemainder := [] },
    store :=
      { runtime := { module := crossMemoryModule, host := {} },
        wasm := crossMemoryInitialStore } }

theorem cross_memory_copy_result :
    (runSteps 7 crossMemoryConfig).result.values? =
      some [.i32 0xC0DEC0DE] := by
  native_decide

def crossMemoryPhysicalResult : RunnerResult Unit → Bool
  | .success _ store =>
    store.wasm.mem.read32 64 == 0xC0DEC0DE &&
      store.wasm.extraMems[0]!.read32 32 == 0xC0DEC0DE
  | _ => false

theorem cross_memory_copy_preserves_source :
    crossMemoryPhysicalResult (runSteps 7 crossMemoryConfig).result = true := by
  native_decide

theorem cross_memory_copy_matches_big_step :
    (runSteps 7 crossMemoryConfig).result.values? =
      some (runValues 20 crossMemoryModule 0 crossMemoryInitialStore []) := by
  native_decide

def indexedMemoryModule : Module :=
  { funcs :=
      [ { body :=
          [ .const 24, .const 0xA1B2C3D4, .memOp 1 (.store32 0),
            .const 24, .memOp 1 (.load32 0) ],
          results := [.i32] } ],
    memory := some { pagesMin := 1 },
    extraMemories := [{ pagesMin := 1 }] }

def indexedMemoryConfig : Config Unit :=
  { expr := .running
      { locals := {}, code := indexedMemoryModule.funcs[0]!.body,
        resultArity := 1, callerRemainder := [] },
    store :=
      { runtime := { module := indexedMemoryModule, host := {} },
        wasm := indexedMemoryModule.initialStore } }

def indexedMemoryFinalStore : MachineStore Unit :=
  { indexedMemoryConfig.store with
    wasm :=
      { indexedMemoryConfig.store.wasm with
        extraMems :=
          indexedMemoryConfig.store.wasm.extraMems.set 0
            (indexedMemoryConfig.store.wasm.extraMems[0]!.write32
              24 0xA1B2C3D4) } }

theorem indexed_memory_roundtrip_run :
    (runSteps 6 indexedMemoryConfig).result =
      .success [.i32 0xA1B2C3D4] indexedMemoryFinalStore := by
  rfl

def indexedMemoryResultMatches : RunnerResult Unit → Bool
  | .success [.i32 value] store =>
      value == 0xA1B2C3D4 &&
        store.wasm.mem.read32 24 == 0 &&
        store.wasm.extraMems[0]!.read32 24 == 0xA1B2C3D4
  | _ => false

/-- The indexed instruction updates only memory 1; stable memory identities
are restored before the transition becomes observable. -/
theorem indexed_memory_roundtrip_spec :
    indexedMemoryResultMatches (runSteps 6 indexedMemoryConfig).result = true := by
  native_decide

theorem indexed_memory_roundtrip_relational :
    TerminatesWith indexedMemoryConfig
      (fun values store =>
        values = [.i32 0xA1B2C3D4] ∧
          store.wasm.mem.read32 24 = 0 ∧
          store.wasm.extraMems[0]!.read32 24 = 0xA1B2C3D4) := by
  apply runSteps_success_terminates indexed_memory_roundtrip_run
  exact ⟨rfl, rfl, rfl⟩

theorem indexed_memory_roundtrip_matches_big_step :
    (runSteps 6 indexedMemoryConfig).result.values? =
      some (runValues 20 indexedMemoryModule 0
        indexedMemoryModule.initialStore []) := by
  native_decide

def indexedMemoryTrapConfig : Config Unit :=
  { indexedMemoryConfig with
    expr := .running
      { locals := {}, code := [.const 65535, .memOp 1 (.load32 0)],
        resultArity := 1, callerRemainder := [] } }

theorem indexed_memory_trap_restores_stable_slots :
    (runSteps 2 indexedMemoryTrapConfig).result =
      .trapped .outOfBoundsMemory indexedMemoryTrapConfig.store := by
  rfl
theorem indexed_memory_trap_trapsWith :
    TrapsWith indexedMemoryTrapConfig .outOfBoundsMemory
      (fun store => store = indexedMemoryTrapConfig.store) := by
  apply runSteps_trapped_trapsWith
    indexed_memory_trap_restores_stable_slots
  rfl

def smallStepHost : HostFn Unit :=
  { params := [.i32]
    results := [.i32]
    invoke := fun store args =>
      match args with
      | [.i32 value] =>
        .Return [.i32 (value + 1)]
          { store with mem := store.mem.write32 200 value }
      | _ => .Trap store "small-step host: bad arguments" }

def smallStepHostEnv : HostEnv Unit :=
  { funcs := [smallStepHost] }

def smallStepHostModule : Module :=
  { imports :=
      [{ «module» := "env", name := "write_and_increment",
         params := [.i32], results := [.i32] }]
    funcs :=
      [{ params := [.i32],
         body := [.localGet 0, .call 0],
         results := [.i32] }]
    memory := some { pagesMin := 1 } }

def smallStepHostRuntime : RuntimeEnv Unit :=
  { module := smallStepHostModule, host := smallStepHostEnv }

def smallStepHostConfig : Config Unit :=
  { expr := .running
      { locals := smallStepHostModule.funcs[0]!.toLocals [.i32 41],
        code := smallStepHostModule.funcs[0]!.body,
        resultArity := 1, callerRemainder := [] },
    store :=
      { runtime := smallStepHostRuntime,
        wasm := smallStepHostModule.initialStore } }

def smallStepHostPhysicalResult : RunnerResult Unit → Bool
  | .success values store =>
    values == [.i32 42] && store.wasm.mem.read32 200 == 41
  | _ => false

def smallStepHostFinalStore : MachineStore Unit :=
  { smallStepHostConfig.store with
    wasm :=
      { smallStepHostConfig.store.wasm with
        mem := smallStepHostConfig.store.wasm.mem.write32 200 41 } }

theorem host_call_run :
    (runSteps 4 smallStepHostConfig).result =
      .success [.i32 42] smallStepHostFinalStore := by
  rfl
theorem host_call_returns_and_updates_memory :
    smallStepHostPhysicalResult (runSteps 4 smallStepHostConfig).result = true := by
  native_decide

/-- A host call may update physical memory atomically; the relational contract
records both its returned value and the committed store effect. -/
theorem host_call_relational :
    TerminatesWith smallStepHostConfig (fun values store =>
      values = [.i32 42] ∧ store.wasm.mem.read32 200 = 41) := by
  apply runSteps_success_terminates host_call_run
  constructor
  native_decide
  · native_decide

theorem host_call_partial :
    PartiallyMeets smallStepHostConfig (fun values store =>
      values = [.i32 42] ∧ store.wasm.mem.read32 200 = 41) := by
  apply runSteps_success_partiallyMeets host_call_run
  constructor
  native_decide
  · native_decide

theorem host_call_matches_big_step :
    (runSteps 4 smallStepHostConfig).result.values? =
      some (runValues 16 smallStepHostModule 1
        smallStepHostModule.initialStore [.i32 41] smallStepHostEnv) := by
  native_decide

def smallStepHostEntryConfig : Config Unit :=
  { expr := .running
      { locals := { values := [.i32 10] },
        code := [.call 0], resultArity := 1, callerRemainder := [] },
    store :=
      { runtime := smallStepHostRuntime,
        wasm := smallStepHostModule.initialStore } }

theorem host_entry_initialization :
    initConfig smallStepHostRuntime 0 smallStepHostModule.initialStore
      [.i32 10] = .ok smallStepHostEntryConfig := by
  rfl
theorem host_entry_executes :
    (runSteps 2 smallStepHostEntryConfig).result.values? =
      some [.i32 11] := by
  native_decide

def smallStepTrapHost : HostFn Unit :=
  { invoke := fun store _ =>
      .Trap { store with mem := store.mem.write8 255 0xAB } "host abort" }

def smallStepTrapModule : Module :=
  { imports := [{ «module» := "env", name := "abort" }]
    funcs := [{ body := [.call 0, .unreachable] }]
    memory := some { pagesMin := 1 } }

def smallStepTrapConfig : Config Unit :=
  { expr := .running
      { locals := {}, code := smallStepTrapModule.funcs[0]!.body,
        resultArity := 0, callerRemainder := [] },
    store :=
      { runtime :=
          { module := smallStepTrapModule,
            host := { funcs := [smallStepTrapHost] } },
        wasm := smallStepTrapModule.initialStore } }

def smallStepTrapFinalStore : MachineStore Unit :=
  { smallStepTrapConfig.store with
    wasm :=
      { smallStepTrapConfig.store.wasm with
        mem := smallStepTrapConfig.store.wasm.mem.write8 255 0xAB } }

def smallStepHostTrapResult : RunnerResult Unit → Bool
  | .trapped (.host "host abort") store =>
    store.wasm.mem.read8 255 == 0xAB
  | _ => false

theorem host_trap_preserves_committed_effect :
    smallStepHostTrapResult (runSteps 1 smallStepTrapConfig).result = true := by
  native_decide

theorem host_trap_run :
    (runSteps 1 smallStepTrapConfig).result =
      .trapped (.host "host abort") smallStepTrapFinalStore := by
  rfl

/-- Unlike an atomic Wasm bounds trap, a host trap preserves the state effect
committed by the host before returning the trap. -/
theorem host_trap_trapsWith :
    TrapsWith smallStepTrapConfig (.host "host abort")
      (fun store => store.wasm.mem.read8 255 = 0xAB) := by
  apply runSteps_trapped_trapsWith host_trap_run
  rfl

def smallStepHostDispatchModule : Module :=
  { types := [{ params := [.i32], results := [.i32] }]
    imports :=
      [{ «module» := "env", name := "write_and_increment",
         params := [.i32], results := [.i32] }]
    funcs :=
      [ { params := [.i32],
          body := [.localGet 0, .const 0, .callIndirect 0 0],
          results := [.i32] },
        { params := [.i32],
          body := [.localGet 0, .refFunc 0, .callRef 0],
          results := [.i32] } ]
    tables := [{ min := 1 }]
    elements := [{ tableIdx := some 0, offset := some 0, funcs := [some 0] }]
    memory := some { pagesMin := 1 } }

def smallStepHostDispatchConfig (localFunctionIndex : Nat) : Config Unit :=
  { expr := .running
      { locals :=
          smallStepHostDispatchModule.funcs[localFunctionIndex]!.toLocals
            [.i32 41],
        code := smallStepHostDispatchModule.funcs[localFunctionIndex]!.body,
        resultArity := 1, callerRemainder := [] },
    store :=
      { runtime :=
          { module := smallStepHostDispatchModule, host := smallStepHostEnv },
        wasm := smallStepHostDispatchModule.initialStore } }

theorem indirect_host_call_returns_and_updates_memory :
    smallStepHostPhysicalResult
      (runSteps 10 (smallStepHostDispatchConfig 0)).result = true := by
  native_decide

theorem reference_host_call_returns_and_updates_memory :
    smallStepHostPhysicalResult
      (runSteps 10 (smallStepHostDispatchConfig 1)).result = true := by
  native_decide

theorem indirect_and_reference_host_calls_match_big_step :
    (runSteps 10 (smallStepHostDispatchConfig 0)).result.values? =
        some (runValues 16 smallStepHostDispatchModule 1
          smallStepHostDispatchModule.initialStore [.i32 41]
          smallStepHostEnv) ∧
      (runSteps 10 (smallStepHostDispatchConfig 1)).result.values? =
        some (runValues 16 smallStepHostDispatchModule 2
          smallStepHostDispatchModule.initialStore [.i32 41]
          smallStepHostEnv) := by
  native_decide

def smallStepGcModule : Module :=
  { gcTypes :=
      [{ comp := .struct [{ storage := .val .i32 }] }]
    funcs :=
      [ { body :=
          [.const 0xFFFFFFFF, .gc .refI31, .gc .i31GetU],
          results := [.i32] },
        { body :=
          [.const 7, .gc (.structNew 0), .gc (.structGet 0 0)],
          results := [.i32] } ] }

def smallStepGcConfig (functionIndex : Nat) : Config Unit :=
  { expr := .running
      { locals := {},
        code := smallStepGcModule.funcs[functionIndex]!.body,
        resultArity := 1, callerRemainder := [] },
    store :=
      { runtime := { module := smallStepGcModule, host := {} },
        wasm := smallStepGcModule.initialStore } }

theorem gc_i31_round_trip :
    (runSteps 6 (smallStepGcConfig 0)).result.values? =
      some [.i32 0x7FFFFFFF] := by
  native_decide

def smallStepGcPhysicalResult : RunnerResult Unit → Bool
  | .success [.i32 7] store => store.wasm.gcHeap.length == 1
  | _ => false

theorem gc_struct_allocation_and_read :
    smallStepGcPhysicalResult
      (runSteps 6 (smallStepGcConfig 1)).result = true := by
  native_decide

theorem gc_struct_relational :
    TerminatesWith (smallStepGcConfig 1) (fun values store =>
      values = [.i32 7] ∧ store.wasm.gcHeap.length = 1) := by
  apply runSteps_success_terminates
    (fuel := 6)
    (values := [.i32 7])
    (store :=
      { (smallStepGcConfig 1).store with
        wasm :=
          { (smallStepGcConfig 1).store.wasm with
            gcHeap := [.struct 0 [.i32 7]] } })
  · rfl
  · decide

/-- GC traps are represented by structural machine reasons rather than an
opaque message inherited from the evaluator. -/
def smallStepGcNullI31Config : Config Unit :=
  { expr := .running
      { locals := {},
        code := [.gc .refNullAny, .gc .i31GetU],
        resultArity := 1, callerRemainder := [] },
    store :=
      { runtime := { module := smallStepGcModule, host := {} },
        wasm := smallStepGcModule.initialStore } }

def isNullI31Trap : RunnerResult α → Bool
  | .trapped .nullI31Reference _ => true
  | _ => false

theorem gc_null_i31_structured_trap :
    isNullI31Trap (runSteps 2 smallStepGcNullI31Config).result = true := by
  native_decide

theorem gc_null_i31_trapsWith :
    TrapsWith smallStepGcNullI31Config .nullI31Reference
      (fun store => store = smallStepGcNullI31Config.store) := by
  apply runSteps_trapped_trapsWith (fuel := 2)
    (store := smallStepGcNullI31Config.store) <;> rfl

theorem gc_examples_match_big_step :
    (runSteps 6 (smallStepGcConfig 0)).result.values? =
        some (runValues 16 smallStepGcModule 0
          smallStepGcModule.initialStore []) ∧
      (runSteps 6 (smallStepGcConfig 1)).result.values? =
        some (runValues 16 smallStepGcModule 1
          smallStepGcModule.initialStore []) := by
  native_decide

def smallStepExceptionModule : Module :=
  { tags := [{ params := [.i32] }]
    funcs :=
      [ { body :=
          [ .block 0 1
              [ .tryTable 0 0 [.catch 0 0]
                  [.const 42, .throwI 0] ] ],
          results := [.i32] },
        { body := [.const 17, .throwI 0] },
        { body := [.const 31, .throwI 0] },
        { body :=
          [ .block 0 1
              [ .tryTable 0 0 [.catch 0 0] [.call 2] ] ],
          results := [.i32] },
        { body :=
          [ .block 0 2
              [ .tryTable 0 0 [.catchRef 0 0]
                  [.const 9, .throwI 0] ],
            .throwRef ] } ] }

def smallStepExceptionConfig (functionIndex : Nat) : Config Unit :=
  { expr := .running
      { locals := {},
        code := smallStepExceptionModule.funcs[functionIndex]!.body,
        resultArity := smallStepExceptionModule.funcs[functionIndex]!.results.length,
        callerRemainder := [] },
    store :=
      { runtime := { module := smallStepExceptionModule, host := {} },
        wasm := smallStepExceptionModule.initialStore } }

theorem exception_is_caught_with_arguments :
    (runSteps 8 (smallStepExceptionConfig 0)).result.values? =
      some [.i32 42] := by
  native_decide

theorem caught_exception_relational :
    TerminatesWith (smallStepExceptionConfig 0)
      (fun values _ => values = [.i32 42]) := by
  apply runSteps_success_terminates
    (fuel := 8)
    (values := [.i32 42])
    (store := (smallStepExceptionConfig 0).store)
  · rfl
  · rfl
theorem uncaught_exception_is_not_a_trap_category :
    (runSteps 4 (smallStepExceptionConfig 1)).result =
      .trapped (.uncaughtException 0 [.i32 17])
        (smallStepExceptionConfig 1).store := by
  rfl
theorem uncaught_exception_trapsWith :
    TrapsWith (smallStepExceptionConfig 1)
      (.uncaughtException 0 [.i32 17])
      (fun store => store = (smallStepExceptionConfig 1).store) := by
  apply runSteps_trapped_trapsWith
    uncaught_exception_is_not_a_trap_category
  rfl
def smallStepThrowRefConfig : Config Unit :=
  { expr := .running
      { locals := { values := [.exnref (some 0)] }
        code := [.throwRef]
        resultArity := 0
        callerRemainder := [] }
    store :=
      { runtime := { module := smallStepExceptionModule, host := {} }
        wasm :=
          { smallStepExceptionModule.initialStore with
            exns := [(0, [.i32 23])] } } }

theorem exception_reference_rethrows_package :
    (runSteps 3 smallStepThrowRefConfig).result =
      .trapped (.uncaughtException 0 [.i32 23])
        smallStepThrowRefConfig.store := by
  rfl
theorem exception_reference_rethrows_trapsWith :
    TrapsWith smallStepThrowRefConfig
      (.uncaughtException 0 [.i32 23])
      (fun store => store = smallStepThrowRefConfig.store) := by
  apply runSteps_trapped_trapsWith exception_reference_rethrows_package
  rfl

/-- Defensive administrative states can contain an older propagation marker
below the currently propagating exception. The current exception wins and the
stale marker is discarded instead of surfacing an interpreter error. -/
def nestedExceptionMarkerConfig : Config Unit :=
  let current : ControlFrame :=
    { kind := .throwing 0 [.i32 23]
      paramArity := 0
      resultArity := 0
      body := []
      continuation := []
      belowStack := [] }
  let stale : ControlFrame :=
    { kind := .throwing 0 [.i32 17]
      paramArity := 0
      resultArity := 0
      body := []
      continuation := []
      belowStack := [] }
  { expr := .running
      { locals := {}
        code := []
        resultArity := 0
        callerRemainder := []
        control := [current, stale] }
    store :=
      { runtime := { module := smallStepExceptionModule, host := {} }
        wasm := smallStepExceptionModule.initialStore } }

theorem nested_exception_marker_unwinds :
    (runSteps 3 nestedExceptionMarkerConfig).result.trapReason? =
      some (.uncaughtException 0 [.i32 23]) := by
  rfl

theorem exception_unwinds_across_call_frame :
    (runSteps 12 (smallStepExceptionConfig 3)).result.values? =
      some [.i32 31] := by
  native_decide

def smallStepCatchRefPhysicalResult : RunnerResult Unit → Bool
  | .trapped (.uncaughtException 0 [.i32 9]) store =>
    store.wasm.exns.length == 1
  | _ => false

theorem catch_ref_registers_and_rethrows_package :
    smallStepCatchRefPhysicalResult
      (runSteps 12 (smallStepExceptionConfig 4)).result = true := by
  native_decide

theorem caught_exception_matches_big_step :
    (runSteps 8 (smallStepExceptionConfig 0)).result.values? =
      some (runValues 20 smallStepExceptionModule 0
        smallStepExceptionModule.initialStore []) := by
  native_decide

end Wasm.Examples.SmallStep
