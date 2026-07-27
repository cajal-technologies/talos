import Interpreter.Wasm.SmallStep

/-! ## Example: InfiniteLoop

The two reachable machine shapes form a closed invariant: entering the loop
reaches its branch instruction, and `br 0` returns to that same instruction.
Consequently no finite relational trace can reach `.done`.
-/

namespace Wasm
open SmallStep

def InfiniteLoop : Program := [.loop 0 0 [.br 0]]

private def infiniteFrame (values : List Value) : ControlFrame :=
  { kind := .loop
    paramArity := 0
    resultArity := 0
    body := [.br 0]
    continuation := []
    belowStack := values }

def infiniteOuterConfig (m : Module) (st : Store α)
    (locals : Locals) : Config α :=
  { expr := .running
      { locals
        code := InfiniteLoop
        resultArity := 0
        callerRemainder := [] }
    store := { runtime := { module := m, host := {} }, wasm := st } }

def infiniteInnerConfig (m : Module) (st : Store α)
    (locals : Locals) : Config α :=
  { expr := .running
      { locals
        code := [.br 0]
        resultArity := 0
        callerRemainder := []
        control := [infiniteFrame locals.values] }
    store := { runtime := { module := m, host := {} }, wasm := st } }

private theorem infinite_outer_step (m : Module) (st : Store α)
    (locals : Locals) :
    Step (infiniteOuterConfig m st locals)
      (.instruction (.loop 0 0 [.br 0]))
      (infiniteInnerConfig m st locals) :=
  .loop

private theorem infinite_inner_step (m : Module) (st : Store α)
    (locals : Locals) :
    Step (infiniteInnerConfig m st locals)
      (.instruction (.br 0))
      (infiniteInnerConfig m st locals) :=
  .br rfl

private def InfiniteReachable (m : Module) (st : Store α)
    (locals : Locals) (config : Config α) : Prop :=
  config = infiniteOuterConfig m st locals ∨
    config = infiniteInnerConfig m st locals

private theorem infinite_step_preserves
    (m : Module) (st : Store α) (locals : Locals)
    {config next : Config α} {kind : StepKind}
    (reachable : InfiniteReachable m st locals config)
    (step : Step config kind next) :
    InfiniteReachable m st locals next := by
  rcases reachable with rfl | rfl
  · obtain ⟨rfl, rfl⟩ :=
      step_deterministic (infinite_outer_step m st locals) step
    exact .inr rfl
  · obtain ⟨rfl, rfl⟩ :=
      step_deterministic (infinite_inner_step m st locals) step
    exact .inr rfl

private theorem infinite_steps_preserve
    (m : Module) (st : Store α) (locals : Locals)
    {config final : Config α} {trace : List StepKind}
    (reachable : InfiniteReachable m st locals config)
    (steps : Steps config trace final) :
    InfiniteReachable m st locals final := by
  induction steps with
  | refl => exact reachable
  | cons head tail ih =>
      exact ih (infinite_step_preserves m st locals reachable head)

theorem infiniteLoopDiverges (m : Module) (st : Store α)
    (locals : Locals) :
    ¬∃ trace values store,
      Steps (infiniteOuterConfig m st locals) trace ⟨.done values, store⟩ := by
  rintro ⟨trace, values, store, execution⟩
  have reachable :=
    infinite_steps_preserve m st locals (.inl rfl) execution
  rcases reachable with impossible | impossible <;> cases impossible

theorem infiniteLoop_not_terminatesWith (m : Module) (st : Store α)
    (locals : Locals) :
    ¬TerminatesWith (infiniteOuterConfig m st locals) (fun _ _ => True) := by
  rintro ⟨trace, values, store, execution, _⟩
  exact infiniteLoopDiverges m st locals ⟨trace, values, store, execution⟩

end Wasm
