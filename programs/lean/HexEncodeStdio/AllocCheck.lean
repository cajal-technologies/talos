import Project.HexStdio.Spec

open Wasm

def universalInstanceA : SmallStep.ModuleInstance Universal.State :=
  { module := Project.HexStdio.«module»
    host := Universal.envFor Project.HexStdio.«module»
    resolvedImports := (Universal.envFor Project.HexStdio.«module»).funcs.toArray.map .host }

def allocTerminal : SmallStep.RunnerResult Universal.State → Prop
  | .success _ _ => True
  | .trapped (.host msg) final =>
      msg = OOM.trapMessage ∧ final.wasm.host.oom.raised = true
  | _ => False

def universalOOMHost : HostFn Universal.State :=
  OOM.oomHost.lift
    { get := Universal.State.oom
      set := fun whole part => { whole with oom := part } }

example : ∃ hf,
    (Universal.envFor Project.HexStdio.«module»).funcs[2]? = some hf ∧
    ∀ st : Store Universal.State,
      hf.invoke st [] = .Trap
        { st with host := { st.host with oom := { raised := true } } }
        OOM.trapMessage := by
  have hsat := Project.HexStdio.Spec.universal_env_satisfies
  have hcontract : (Universal.specFor Project.HexStdio.«module»).contracts[2]? =
      some (fun st args result => result = universalOOMHost.invoke st args) := by
    rfl
  obtain ⟨hf, henv, hsound⟩ :=
    hsat.lookup_contract (i := 2) (by decide) hcontract
  refine ⟨hf, henv, ?_⟩
  intro st
  have h := hsound st []
  simpa [universalOOMHost, HostFn.lift, Store.focus, Store.unfocus, Store.mapHost,
    OOM.oomHost, OOM.oomResult] using h

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 1000000 in
example (st : Store Universal.State) (size : UInt32) : ∃ config,
    SmallStep.initConfig universalInstanceA 15 st [.i32 1, .i32 size] =
      .ok config ∧
    allocTerminal (SmallStep.runSteps 100 config).result := by
  refine ⟨_, rfl, ?_⟩
  simp [allocTerminal, SmallStep.runSteps]
