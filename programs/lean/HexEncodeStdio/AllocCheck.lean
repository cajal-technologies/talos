import Project.HexStdio.Spec
import HexEncodeStdio.AllocatorOperational

namespace Project.HexEncodeStdio.AllocCheck

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

/-- The allocator requires an initialized memory containing its bump cell.
For arbitrary allocation sizes, its execution returns or signals OOM. -/
theorem allocator_terminates_or_oom
    (store : SmallStep.MachineStore Universal.State) (size : UInt32)
    (hmod : store.runtime.currentModule = Project.HexStdio.«module»)
    (henv : store.runtime.currentHost = Universal.envFor Project.HexStdio.«module»)
    (hbound : 1053964 ≤ store.wasm.mem.pages * 65536)
    (hpages : store.wasm.mem.pages < 4294967295) :
    let config : SmallStep.Config Universal.State :=
      ⟨.running ⟨⟨[], [], [.i32 1, .i32 size]⟩,
        [.call 15], 0, [], [], []⟩, store⟩
    SmallStep.TerminatesWith config (fun _ _ => True) ∨
      SmallStep.TrapsWith config (.host OOM.trapMessage)
        (fun final => final.wasm.host.oom.raised = true) := by
  dsimp only
  rcases allocator_call_outcome store [] [] [] [] 0 [] [] [] size 1
      (store.wasm.mem.read32 1053960) hmod henv rfl hbound hpages with
    (⟨_, _, hreach⟩ | ⟨_, _, _, _, _, hreach⟩) | htrap
  · left
    apply Project.HexEncodeStdio.TerminatesWith.prependReaches hreach
    apply SmallStep.TerminatesWith.prepend SmallStep.Step.finish
    exact SmallStep.TerminatesWith.done trivial
  · left
    apply Project.HexEncodeStdio.TerminatesWith.prependReaches hreach
    apply SmallStep.TerminatesWith.prepend SmallStep.Step.finish
    exact SmallStep.TerminatesWith.done trivial
  · exact Or.inr htrap

end Project.HexEncodeStdio.AllocCheck
