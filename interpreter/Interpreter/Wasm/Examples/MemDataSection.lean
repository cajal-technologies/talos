import Interpreter.Wasm.SmallStep

/-! ## Example: literal data-section initialization

    The module declares one page with four bytes at offset zero. Its initial
    machine store exposes those bytes to the authoritative small-step
    execution of a simple function.
-/

namespace Wasm
open SmallStep

def memModule : Module :=
  { funcs := [{ body := [.const 7], results := [.i32] }]
    memory := some
      { pagesMin := 1
        data := [{ offset := some 0, bytes := [0x42, 0x43, 0x44, 0x45] }] } }

theorem memDataSection_read32_zero :
    (memModule.initialStore (α := Unit)).mem.read32 0 = 0x45444342 := by
  native_decide

def memDataStore : MachineStore Unit :=
  { runtime := { instances := #[{ module := memModule, host := {} }], entry := ⟨0⟩ }
    wasm := memModule.initialStore }

def memDataConfig : Config Unit :=
  { expr := .running
      { locals := {}
        code := memModule.funcs[0]!.body
        resultArity := 1
        callerRemainder := [] }
    store := memDataStore }

theorem memDataSection_runs :
    (runSteps 2 memDataConfig).result =
      .success [.i32 7] memDataStore := by
  rfl

theorem memDataSection_spec :
    TerminatesWith memDataConfig (fun values store =>
      values = [.i32 7] ∧
      store.wasm.mem.read32 0 = 0x45444342) := by
  apply runSteps_success_terminates memDataSection_runs
  constructor <;> native_decide

theorem memDataSection_partial :
    PartiallyMeets memDataConfig (fun values store =>
      values = [.i32 7] ∧
      store.wasm.mem.read32 0 = 0x45444342) := by
  apply runSteps_success_partiallyMeets memDataSection_runs
  constructor <;> native_decide

end Wasm
