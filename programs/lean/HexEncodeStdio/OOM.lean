import CodeLib
import Project.HexStdio.Spec

namespace Project.HexEncodeStdio.OOM

open Wasm

/-- The concrete single-module instance used at all relational checkpoints. -/
def universalInstance : SmallStep.ModuleInstance Universal.State :=
  { module := Project.HexStdio.«module»
    host := Universal.envFor Project.HexStdio.«module»
    resolvedImports :=
      (Universal.envFor Project.HexStdio.«module»).funcs.toArray.map .host }

def universalOOMHost : HostFn Universal.State :=
  OOM.oomHost.lift
    { get := Universal.State.oom
      set := fun whole part => { whole with oom := part } }

/-- Resolve the OOM import through the spec's axiom-clean universal-host
satisfaction theorem, and expose only its terminal behavior. -/
theorem universal_oom_resolver : ∃ hf,
    (Universal.envFor Project.HexStdio.«module»).funcs[2]? = some hf ∧
    ∀ st : Store Universal.State,
      hf.invoke st [] = .Trap
        { st with host := { st.host with oom := { raised := true } } }
        OOM.trapMessage := by
  have hsat := Project.HexStdio.Spec.universal_env_satisfies
  have hcontract :
      (Universal.specFor Project.HexStdio.«module»).contracts[2]? =
        some (fun st args result =>
          result = universalOOMHost.invoke st args) := by
    rfl
  obtain ⟨hf, henv, hsound⟩ :=
    hsat.lookup_contract (i := 2) (by decide) hcontract
  refine ⟨hf, henv, ?_⟩
  intro st
  have h := hsound st []
  simpa [universalOOMHost, HostFn.lift, Store.focus, Store.unfocus,
    Store.mapHost, OOM.oomHost, OOM.oomResult] using h

set_option maxRecDepth 100000 in
/-- Generated `func13` (WAT function 16) is exactly the terminal OOM adapter.
The calculation is symbolic in the complete Wasm store: only the typed host
component is updated. -/
theorem func13_traps (st : Store Universal.State) : ∃ config final,
    SmallStep.initConfig universalInstance 16 st [] = .ok config ∧
    (SmallStep.runSteps 5 config).result =
      .trapped (.host OOM.trapMessage) final ∧
    final.wasm.host.oom.raised = true := by
  refine ⟨_, _, rfl, rfl, rfl⟩

end Project.HexEncodeStdio.OOM
