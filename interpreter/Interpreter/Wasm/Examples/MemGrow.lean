import Interpreter.Wasm.SmallStep

/-! ## Example: memory.size / memory.grow

    Small-step contracts for observing memory size, successful growth, and
    failed growth. Successful growth preserves existing bytes; failure
    returns `-1` and preserves the complete physical store.
-/

namespace Wasm
open SmallStep

def sizeBody : Program := [.memorySize]

def growThenSizeBody : Program := [
  .const 2, .memoryGrow,
  .drop,
  .memorySize
]

def growFailBody : Program := [
  .const 0xFFFFFF00, .memoryGrow,
  .memorySize
]

def growModule : Module :=
  { funcs :=
      [ { body := sizeBody, results := [.i32] }
      , { body := growThenSizeBody, results := [.i32] }
      , { body := growFailBody, results := [.i32, .i32] } ]
    memory := some { pagesMin := 1 } }

/-- Seed a framed word so growth preservation is observable. -/
def growInitialWasmStore : Store Unit :=
  { growModule.initialStore (α := Unit) with
    mem := (growModule.initialStore (α := Unit)).mem.write32 64 0xC0DEC0DE }

def growStore : MachineStore Unit :=
  { runtime := { instances := #[{ module := growModule, host := {} }], entry := ⟨0⟩ }
    wasm := growInitialWasmStore }

private def growConfig (body : Program) (arity : Nat) : Config Unit :=
  { expr := .running
      { locals := {}
        code := body
        resultArity := arity
        callerRemainder := [] }
    store := growStore }

def sizeConfig : Config Unit := growConfig sizeBody 1
def growThenSizeConfig : Config Unit := growConfig growThenSizeBody 1
def growFailConfig : Config Unit := growConfig growFailBody 2

def grownMemory : Mem := { growInitialWasmStore.mem with pages := 3 }

def growSuccessStore : MachineStore Unit :=
  { growStore with
    wasm := { growInitialWasmStore with mem := grownMemory } }

theorem memorySize_reads_pagesMin :
    (runSteps 2 sizeConfig).result =
      .success [.i32 1] growStore := by
  rfl

theorem memorySize_spec :
    TerminatesWith sizeConfig (fun values store =>
      values = [.i32 1] ∧ store = growStore) := by
  apply runSteps_success_terminates memorySize_reads_pagesMin
  exact ⟨rfl, rfl⟩

theorem memoryGrow_bumps_size :
    (runSteps 6 growThenSizeConfig).result =
      .success [.i32 3] growSuccessStore := by
  rfl

/-- Growth changes only the page count and frames the pre-existing word. -/
theorem memoryGrow_spec :
    TerminatesWith growThenSizeConfig (fun values store =>
      values = [.i32 3] ∧
      store.wasm.mem.pages = 3 ∧
      store.wasm.mem.read32 64 = 0xC0DEC0DE) := by
  apply runSteps_success_terminates memoryGrow_bumps_size
  constructor
  · rfl
  constructor <;> native_decide

theorem memoryGrow_partial :
    PartiallyMeets growThenSizeConfig (fun values store =>
      values = [.i32 3] ∧
      store.wasm.mem.pages = 3 ∧
      store.wasm.mem.read32 64 = 0xC0DEC0DE) := by
  apply runSteps_success_partiallyMeets memoryGrow_bumps_size
  constructor
  · rfl
  constructor <;> native_decide

/-- An oversized request returns `-1`, reports the unchanged size, and does
not mutate any component of the machine store. -/
theorem memoryGrow_oversize_returns_neg_one :
    (runSteps 4 growFailConfig).result =
      .success [.i32 1, .i32 0xFFFFFFFF] growStore := by
  rfl

theorem memoryGrow_failure_spec :
    TerminatesWith growFailConfig (fun values store =>
      values = [.i32 1, .i32 0xFFFFFFFF] ∧ store = growStore) := by
  apply runSteps_success_terminates memoryGrow_oversize_returns_neg_one
  exact ⟨rfl, rfl⟩

theorem memoryGrow_failure_partial :
    PartiallyMeets growFailConfig (fun values store =>
      values = [.i32 1, .i32 0xFFFFFFFF] ∧ store = growStore) := by
  apply runSteps_success_partiallyMeets memoryGrow_oversize_returns_neg_one
  exact ⟨rfl, rfl⟩

/-! ### Imported-resource limit ownership

An importing declaration may be more permissive than the resource it imports.
The instantiated memory's cap remains authoritative. This models an exported
`(memory 2 5)` accessed through an importing `(memory 1 6)`: once the shared
resource reaches five pages, another growth must fail. -/

def importingGrowthModule : Module :=
  { funcs := [{ body := [.const 1, .memoryGrow], results := [.i32] }]
    memory := some { pagesMin := 1, pagesMax := some 6 } }

def importedLimitStore : Store Unit :=
  { importingGrowthModule.initialStore with
    mem := { (importingGrowthModule.initialStore (α := Unit)).mem with pages := 5 }
    memoryCaps := [5] }

def importedLimitConfig : Config Unit :=
  { expr := .running
      { locals := {}
        code := importingGrowthModule.funcs[0]!.body
        resultArity := 1
        callerRemainder := [] }
    store :=
      { runtime := { instances := #[{ module := importingGrowthModule, host := {} }], entry := ⟨0⟩ }
        wasm := importedLimitStore } }

theorem imported_memory_retains_exporter_limit :
    (runSteps 3 importedLimitConfig).result =
      .success [.i32 0xFFFFFFFF] importedLimitConfig.store := by
  rfl

end Wasm
