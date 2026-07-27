import Interpreter.Wasm.SmallStep

/-! ## Example: memory.copy

    `memory.copy` pops `[dst, src, len]` (top = `len`) and copies bytes
    with `memmove` semantics. These examples specify both disjoint and
    overlapping copies against the authoritative small-step semantics.
    Out-of-bounds copies trap atomically.
-/

namespace Wasm
open SmallStep

private def initBytes : List UInt8 :=
  [0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88]

def copyDisjointBody : Program := [
  .const 8, .const 0, .const 4,
  .memoryCopy,
  .const 8, .load32 0
]

def copyOverlapBody : Program := [
  .const 2, .const 0, .const 4,
  .memoryCopy,
  .const 0, .load64 0
]

def copyTrapBody : Program := [
  .const 65530, .const 0, .const 100,
  .memoryCopy
]

def copyModule : Module :=
  { funcs :=
      [ { body := copyDisjointBody, results := [.i32] }
      , { body := copyOverlapBody,  results := [.i64] }
      , { body := copyTrapBody } ]
    memory := some { pagesMin := 1, data := [{ offset := some 0, bytes := initBytes }] } }

def copyStore : MachineStore Unit :=
  { runtime := { module := copyModule, host := {} }
    wasm := copyModule.initialStore }

private def copyConfig (body : Program) (arity : Nat) : Config Unit :=
  { expr := .running
      { locals := {}
        code := body
        resultArity := arity
        callerRemainder := [] }
    store := copyStore }

def copyDisjointConfig : Config Unit := copyConfig copyDisjointBody 1
def copyOverlapConfig : Config Unit := copyConfig copyOverlapBody 1
def copyTrapConfig : Config Unit := copyConfig copyTrapBody 0

def copyDisjointFinalStore : MachineStore Unit :=
  { copyStore with
    wasm := { copyStore.wasm with mem := copyStore.wasm.mem.copy 8 0 4 } }

def copyOverlapFinalStore : MachineStore Unit :=
  { copyStore with
    wasm := { copyStore.wasm with mem := copyStore.wasm.mem.copy 2 0 4 } }

theorem copy_disjoint_moves_bytes :
    (runSteps 7 copyDisjointConfig).result =
      .success [.i32 0x44332211] copyDisjointFinalStore := by
  rfl

theorem copy_disjoint_spec :
    TerminatesWith copyDisjointConfig (fun values store =>
      values = [.i32 0x44332211] ∧
      store.wasm.mem.read32 0 = 0x44332211 ∧
      store.wasm.mem.read32 8 = 0x44332211) := by
  apply runSteps_success_terminates copy_disjoint_moves_bytes
  constructor
  · rfl
  constructor <;> native_decide

theorem copy_disjoint_partial :
    PartiallyMeets copyDisjointConfig (fun values store =>
      values = [.i32 0x44332211] ∧ store.wasm.mem.read32 8 = 0x44332211) := by
  apply runSteps_success_partiallyMeets copy_disjoint_moves_bytes
  constructor <;> native_decide

theorem copy_overlap_uses_pre_copy_bytes :
    (runSteps 7 copyOverlapConfig).result =
      .success [.i64 0x8877443322112211] copyOverlapFinalStore := by
  rfl

/-- The copied word at address 2 is read from the pre-copy memory. -/
theorem copy_overlap_spec :
    TerminatesWith copyOverlapConfig (fun values store =>
      values = [.i64 0x8877443322112211] ∧
      store.wasm.mem.read32 2 = 0x44332211) := by
  apply runSteps_success_terminates copy_overlap_uses_pre_copy_bytes
  constructor <;> native_decide

theorem copy_overlap_partial :
    PartiallyMeets copyOverlapConfig (fun values store =>
      values = [.i64 0x8877443322112211] ∧
      store.wasm.mem.read32 2 = 0x44332211) := by
  apply runSteps_success_partiallyMeets copy_overlap_uses_pre_copy_bytes
  constructor <;> native_decide

theorem copy_out_of_bounds_traps :
    (runSteps 4 copyTrapConfig).result =
      .trapped .outOfBoundsMemory copyStore := by
  rfl

/-- Fuel-free trap contract, including atomic preservation of the store. -/
theorem copy_out_of_bounds_trapsWith :
    TrapsWith copyTrapConfig .outOfBoundsMemory
      (fun store => store = copyStore) := by
  apply runSteps_trapped_trapsWith copy_out_of_bounds_traps
  rfl

end Wasm
