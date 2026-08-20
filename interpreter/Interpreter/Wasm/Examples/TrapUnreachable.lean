import Interpreter.Wasm.SmallStep

/-! ## Example: TrapUnreachable

`unreachable` takes one instruction step to a structured terminal trap.
-/

namespace Wasm
open SmallStep

def TrapUnreachable : Program := [.unreachable]

def trapUnreachableModule : Module :=
  { funcs := [{ body := TrapUnreachable }] }

def trapUnreachableConfig : Config Unit :=
  { expr := .running
      { locals := {}
        code := TrapUnreachable
        resultArity := 0
        callerRemainder := [] }
    store :=
      { runtime := { instances := #[{ module := trapUnreachableModule, host := {} }], entry := ⟨0⟩ }
        wasm := trapUnreachableModule.initialStore } }

theorem trapUnreachableSpec :
    Steps trapUnreachableConfig
      [(.instruction .unreachable)]
      ⟨.trapped .unreachable, trapUnreachableConfig.store⟩ :=
  Steps.cons .unreachable (Steps.refl _)

theorem trapUnreachable_runs :
    (runSteps 1 trapUnreachableConfig).result =
      .trapped .unreachable trapUnreachableConfig.store :=
  runSteps_finalConfig_of_steps trapUnreachableSpec

/-- Fuel-free public trap specification. -/
theorem trapUnreachable_traps :
    TrapsWith trapUnreachableConfig .unreachable
      (fun store => store = trapUnreachableConfig.store) := by
  apply runSteps_trapped_trapsWith trapUnreachable_runs
  rfl

end Wasm
