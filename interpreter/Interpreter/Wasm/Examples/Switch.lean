import Interpreter.Wasm.SmallStep

/-! ## Example: Switch

Three-way dispatch via `br_table`. The symbolic trace covers all selector
values and makes the selected branch target and explicit function return
visible in the authoritative relation.
-/

namespace Wasm
open SmallStep

def Switch : Program := [
  .block 0 0 [
    .block 0 0 [
      .block 0 0 [
        .localGet 0,
        .brTable [0, 1] 2
      ],
      .const 10, .ret
    ],
    .const 20, .ret
  ],
  .const 30, .ret
]

def switchModule : Module :=
  { funcs := [{
      params := [.i32]
      results := [.i32]
      body := Switch }] }

def switchConfig (i : UInt32) : Config Unit :=
  { expr := .running
      { locals := { params := [.i32 i] }
        code := Switch
        resultArity := 1
        callerRemainder := [] }
    store :=
      { runtime := { instances := #[{ module := switchModule, host := {} }], entry := ⟨0⟩ }
        wasm := switchModule.initialStore } }

def switchResult (i : UInt32) : UInt32 :=
  if i.toNat = 0 then 10 else if i.toNat = 1 then 20 else 30

private def switchInnerFrame : ControlFrame :=
  { kind := .block
    paramArity := 0
    resultArity := 0
    body := [.localGet 0, .brTable [0, 1] 2]
    continuation := [.const 10, .ret]
    belowStack := [] }

private def switchMiddleFrame : ControlFrame :=
  { kind := .block
    paramArity := 0
    resultArity := 0
    body := [
      .block 0 0 [.localGet 0, .brTable [0, 1] 2],
      .const 10, .ret]
    continuation := [.const 20, .ret]
    belowStack := [] }

private def switchOuterFrame : ControlFrame :=
  { kind := .block
    paramArity := 0
    resultArity := 0
    body := [
      .block 0 0 [
        .block 0 0 [.localGet 0, .brTable [0, 1] 2],
        .const 10, .ret],
      .const 20, .ret]
    continuation := [.const 30, .ret]
    belowStack := [] }

theorem switch_steps (i : UInt32) :
    Steps (switchConfig i)
      [(.instruction (.block 0 0 [
          .block 0 0 [
            .block 0 0 [.localGet 0, .brTable [0, 1] 2],
            .const 10, .ret],
          .const 20, .ret])),
       (.instruction (.block 0 0 [
          .block 0 0 [.localGet 0, .brTable [0, 1] 2],
          .const 10, .ret])),
       (.instruction (.block 0 0 [.localGet 0, .brTable [0, 1] 2])),
       (.instruction (.localGet 0)),
       (.instruction (.brTable [0, 1] 2)),
       (.instruction (.const (switchResult i))),
       (.administrative .returnFromFunction)]
      ⟨.done [.i32 (switchResult i)], (switchConfig i).store⟩ := by
  apply Steps.cons .block
  apply Steps.cons .block
  apply Steps.cons .block
  apply Steps.cons (.localGet rfl)
  rcases hi : i.toNat with _ | j
  · have hbranch :
        branchTarget? 1 0
          [switchInnerFrame, switchMiddleFrame, switchOuterFrame] [] =
          some ([.const 10, .ret],
            [switchMiddleFrame, switchOuterFrame], []) := by
        rfl
    apply Steps.cons (.brTable (by
      simpa [hi, switchInnerFrame, switchMiddleFrame, switchOuterFrame]
        using hbranch))
    simp only [switchResult, hi, if_pos]
    apply Steps.cons .const
    simpa [switchResult, hi, switchConfig] using
      (Steps.cons .returnFromFunction
        (Steps.refl
          (⟨.done [.i32 10], (switchConfig i).store⟩ : Config Unit)))
  · rcases j with _ | j
    · have hbranch :
          branchTarget? 1 1
            [switchInnerFrame, switchMiddleFrame, switchOuterFrame] [] =
            some ([.const 20, .ret], [switchOuterFrame], []) := by
          rfl
      apply Steps.cons (.brTable (by
        simpa [hi, switchInnerFrame, switchMiddleFrame, switchOuterFrame]
          using hbranch))
      simp only [switchResult, hi, if_true]
      apply Steps.cons .const
      simpa [switchResult, hi, switchConfig] using
        (Steps.cons .returnFromFunction
          (Steps.refl
            (⟨.done [.i32 20], (switchConfig i).store⟩ : Config Unit)))
    · have hbranch :
          branchTarget? 1 2
            [switchInnerFrame, switchMiddleFrame, switchOuterFrame] [] =
            some ([.const 30, .ret], [], []) := by
          rfl
      apply Steps.cons (.brTable (by
        simpa [hi, switchInnerFrame, switchMiddleFrame, switchOuterFrame]
          using hbranch))
      simp only [switchResult, hi]
      apply Steps.cons .const
      simpa [switchResult, hi, switchConfig] using
        (Steps.cons .returnFromFunction
          (Steps.refl
            (⟨.done [.i32 30], (switchConfig i).store⟩ : Config Unit)))

theorem switch_runs (i : UInt32) :
    (runSteps 7 (switchConfig i)).result.values? =
      some [.i32 (switchResult i)] :=
  congrArg RunnerResult.values?
    (runSteps_eq_success_of_steps (switch_steps i))

theorem switchSpec (i : UInt32) :
    TerminatesWith (switchConfig i)
      (fun values _ => values = [.i32 (switchResult i)]) :=
  runSteps_values_terminates (switch_runs i)

theorem switch_partial (i : UInt32) :
    PartiallyMeets (switchConfig i)
      (fun values _ => values = [.i32 (switchResult i)]) :=
  runSteps_values_partiallyMeets (switch_runs i)

end Wasm
