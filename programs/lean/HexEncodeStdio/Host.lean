import Mathlib
import CodeLib
import Project.HexStdio.Spec

namespace Project.HexEncodeStdio.Host

open Wasm

def universalReadHost : HostFn Universal.State :=
  StdIO.readHost.lift
    { get := Universal.State.stdio
      set := fun whole part => { whole with stdio := part } }

def universalWriteHost : HostFn Universal.State :=
  StdIO.writeHost.lift
    { get := Universal.State.stdio
      set := fun whole part => { whole with stdio := part } }

def universalOOMHost : HostFn Universal.State :=
  OOM.oomHost.lift
    { get := Universal.State.oom
      set := fun whole part => { whole with oom := part } }

theorem universal_read_resolver : ∃ hf,
    (Universal.envFor Project.HexStdio.«module»).funcs[0]? = some hf ∧
    ∀ st : Store Universal.State, ∀ args,
      hf.invoke st args = universalReadHost.invoke st args := by
  have hsat := Project.HexStdio.Spec.universal_env_satisfies
  have hcontract :
      (Universal.specFor Project.HexStdio.«module»).contracts[0]? =
        some (fun st args result =>
          result = universalReadHost.invoke st args) := by
    rfl
  obtain ⟨hf, henv, hsound⟩ :=
    hsat.lookup_contract (i := 0) (by decide) hcontract
  exact ⟨hf, henv, fun st args => hsound st args⟩

theorem universal_write_resolver : ∃ hf,
    (Universal.envFor Project.HexStdio.«module»).funcs[1]? = some hf ∧
    ∀ st : Store Universal.State, ∀ args,
      hf.invoke st args = universalWriteHost.invoke st args := by
  have hsat := Project.HexStdio.Spec.universal_env_satisfies
  have hcontract :
      (Universal.specFor Project.HexStdio.«module»).contracts[1]? =
        some (fun st args result =>
          result = universalWriteHost.invoke st args) := by
    rfl
  obtain ⟨hf, henv, hsound⟩ :=
    hsat.lookup_contract (i := 1) (by decide) hcontract
  exact ⟨hf, henv, fun st args => hsound st args⟩

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

end Project.HexEncodeStdio.Host
