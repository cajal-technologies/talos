import Interpreter.Wasm.Host.StdIO

/-!
# Small-step execution helpers for StdIO imports

The executable runner is host-parametric. The two derived rules specialize a
two-step imported call to the standard `read` and `write` functions.
-/

namespace Wasm.SmallStep

def runFunction? (module : Module) (env : HostEnv α) (fuel entry : Nat)
    (store : Store α) (args : List Value) : Option (List Value × Store α) :=
  match initConfig { module, host := env } entry store args with
  | .error _ => none
  | .ok phase =>
      match (runSteps fuel phase).result with
      | .success values finalStore => some (values, finalStore.wasm)
      | _ => none

end Wasm.SmallStep

namespace Wasm.StdIO

open Wasm SmallStep

theorem execute_read (module : Module) (himports : module.imports = imports)
    (store wasm : Store State) (length pointer count : UInt32)
    (hinvoke : readHost.invoke store
      [.i32 length, .i32 pointer] = .Return [.i32 count] wasm) :
    SmallStep.runFunction? module env 2 0 store [.i32 pointer, .i32 length] =
      some ([.i32 count], wasm) := by
  let machine : MachineStore State :=
    { runtime := { instances := #[{ module, host := env }], entry := ⟨0⟩ }
      wasm := store }
  let initial : Config State :=
    { expr := .running
        ⟨⟨[], [], [.i32 pointer, .i32 length]⟩, [.call 0], 1, [], [], []⟩
      store := machine }
  let middle : Config State :=
    { expr := .running
        ⟨⟨[], [], [.i32 count]⟩, [], 1, [], [], []⟩
      store := { machine with wasm } }
  have hcallRaw := Step.callHostReturn
    (store := machine) (functionIndex := 0)
    (imp := imports[0]) (hostFunction := readHost)
    (params := []) (localValues := [])
    (values := [.i32 pointer, .i32 length])
    (results := [.i32 count]) (wasm := wasm)
    (code := []) (arity := 1) (remainder := [])
    (controls := []) (calls := [])
    (by simp [machine, himports, imports])
    (by simp [machine, himports]) rfl hinvoke
  have hcall : Step initial (.host 0) middle := by
    simpa [initial, middle, machine, imports, env] using hcallRaw
  have hfinish : Step middle (.administrative .finish)
      ⟨.done [.i32 count], { machine with wasm }⟩ := Step.finish
  have hrun := runSteps_eq_success_of_steps
    (Steps.cons hcall (Steps.single hfinish))
  have hinit : initConfig { module, host := env } 0 store
      [.i32 pointer, .i32 length] = .ok initial := by
    simp [initConfig, initial, machine, himports, imports, env]
  simp only [SmallStep.runFunction?, hinit]
  rw [show (runSteps 2 initial).result =
      .success [.i32 count] { machine with wasm } by simpa using hrun]

theorem execute_write (module : Module) (himports : module.imports = imports)
    (store wasm : Store State) (length pointer : UInt32)
    (hinvoke : writeHost.invoke store
      [.i32 length, .i32 pointer] = .Return [] wasm) :
    SmallStep.runFunction? module env 2 1 store [.i32 pointer, .i32 length] =
      some ([], wasm) := by
  let machine : MachineStore State :=
    { runtime := { instances := #[{ module, host := env }], entry := ⟨0⟩ }
      wasm := store }
  let initial : Config State :=
    { expr := .running
        ⟨⟨[], [], [.i32 pointer, .i32 length]⟩, [.call 1], 0, [], [], []⟩
      store := machine }
  let middle : Config State :=
    { expr := .running ⟨⟨[], [], []⟩, [], 0, [], [], []⟩
      store := { machine with wasm } }
  have hcallRaw := Step.callHostReturn
    (store := machine) (functionIndex := 1)
    (imp := imports[1]) (hostFunction := writeHost)
    (params := []) (localValues := [])
    (values := [.i32 pointer, .i32 length])
    (results := []) (wasm := wasm)
    (code := []) (arity := 0) (remainder := [])
    (controls := []) (calls := [])
    (by simp [machine, himports, imports])
    (by simp [machine, himports]) rfl hinvoke
  have hcall : Step initial (.host 1) middle := by
    simpa [initial, middle, machine, imports, env] using hcallRaw
  have hfinish : Step middle (.administrative .finish)
      ⟨.done [], { machine with wasm }⟩ := Step.finish
  have hrun := runSteps_eq_success_of_steps
    (Steps.cons hcall (Steps.single hfinish))
  have hinit : initConfig { module, host := env } 1 store
      [.i32 pointer, .i32 length] = .ok initial := by
    simp [initConfig, initial, machine, himports, imports, env]
  simp only [SmallStep.runFunction?, hinit]
  rw [show (runSteps 2 initial).result =
      .success [] { machine with wasm } by simpa using hrun]

end Wasm.StdIO
