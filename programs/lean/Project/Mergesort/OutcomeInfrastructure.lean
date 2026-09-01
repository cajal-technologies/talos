import Project.Mergesort.WrapperProof
import CodeLib.SepLogic.SmallStepOutcomeAdequacy
import CodeLib.SepLogic.SmallStepOutcomeLanguage
import CodeLib.SepLogic.SmallStepTotalLifting

/-!
# Outcome infrastructure for merge-sort

This file validates the exceptional half of the reviewed function-contract
shape without symbolically executing a merge-sort function body.  The
`talos.oom` import is proved once as a continuation-passing outcome contract;
callers receive the exact trap reason and updated Universal host marker.
-/

namespace Project.Mergesort.OutcomeInfrastructure

open Wasm
open Iris Iris.ProgramLogic Language.Notation
open Wasm.SepLogic Wasm.SmallStep
open scoped Wasm.SmallStep.Outcome

private abbrev oomImport : ImportDecl :=
  { «module» := "talos", name := "oom", params := [], results := [] }

theorem oomImport_index :
    Project.Mergesort.module.imports[2] = oomImport := by
  rfl

/-- Authoritative total-WP contract for reachable calls to import 2,
`talos.oom`.  Its implementation has no return or throw outcome for the valid
zero-argument call. -/
theorem twp_oom_import
    [WasmSmallStepGS hlc Universal.State]
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → IProp (WasmHeapGF Universal.State)}
    (host : Universal.State)
    {locals : Locals} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    hostStateOwn host ∗
      runtimeModuleOwn ⟨0⟩ Project.Mergesort.module ∗
      hostEnvOwn 0 (Universal.envFor Project.Mergesort.module) ∗
      (hostStateOwn (WrapperProof.afterOom host) -∗
        Φ (.trapped (.host OOM.trapMessage))) ⊢
    WP (.running
      ⟨locals, .call 2 :: code, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hhost, Hruntime, Henv, Hterminal⟩
  iapply twp_callHost Project.Mergesort.module 2 oomImport
      WrapperProof.oomHost (by decide) oomImport_index
      (Universal.envFor Project.Mergesort.module)
      WrapperProof.oomHost_resolves
      (iprop(hostStateOwn host ∗
        (hostStateOwn (WrapperProof.afterOom host) -∗
          Φ (.trapped (.host OOM.trapMessage)))))
      (fun _ => iprop(False))
      (iprop(Φ (.trapped (.host OOM.trapMessage))))
      (iprop(False))
      ⟨0⟩
      (fun store ns obs nt _ results postWasm h => by
        simp only [List.length_nil, List.take_zero,
          List.reverse_nil] at h
        rw [WrapperProof.oomHost_invoke] at h
        contradiction)
      (fun store ns obs nt hmodule postWasm msg h => by
        simp only [List.length_nil, List.take_zero,
          List.reverse_nil] at h
        iintro ⟨⟨Hhost, Hterminal⟩, Hstate⟩
        imod WrapperProof.oomTransfer host store ns obs nt hmodule
            postWasm msg h $$ [$Hhost $Hstate] with
            ⟨⟨%_hmsg, Hhost⟩, Hstate⟩
        imodintro
        isplitl [Hhost Hterminal]
        · iapply Hterminal
          iexact Hhost
        · iexact Hstate)
      (fun store ns obs nt _ postWasm tag xs h => by
        simp only [List.length_nil, List.take_zero,
          List.reverse_nil] at h
        rw [WrapperProof.oomHost_invoke] at h
        contradiction)
      (params := locals.params) (localValues := locals.locals)
      (values := locals.values) (code := code) (arity := arity)
      (remainder := remainder) (controls := controls) (calls := calls)
      $$ [$Hhost $Hterminal] Hruntime Henv
  · iintro %preWasm %results %postWasm %h HQ
    simp [WrapperProof.oomHost_invoke] at h
  · iintro %preWasm %postWasm %msg %h Houtcome
    have hmsg : msg = OOM.trapMessage := by
      simp only [List.length_nil, List.take_zero,
        List.reverse_nil] at h
      rw [WrapperProof.oomHost_invoke] at h
      exact (HostResult.Trap.inj h).2.symm
    subst msg
    iapply Wasm.SmallStep.twp_outcome_trapped
    iexact Houtcome
  · iintro %preWasm %postWasm %tag %xs %h HQ
    simp [WrapperProof.oomHost_invoke] at h

/-! ## Closed non-target acceptance caller

This miniature validates the complete architecture before any generated
merge-sort body proof begins.  Its true branch returns seven; its false branch
uses the already-proved `talos.oom` import contract. -/

def acceptanceHost : Universal.State := Universal.State.ofInput []

def acceptanceExpr (flag : Bool) : Expr Universal.State :=
  .running
    { locals :=
        { values := [.i32 (if flag then 1 else 0)] }
      code :=
        [.iff 0 1 [.const 7] [.call 2] [] [.i32]]
      resultArity := 1
      callerRemainder := [] }

private def acceptanceInstance : ModuleInstance Universal.State :=
  { module := Project.Mergesort.module
    host := Universal.envFor Project.Mergesort.module }

def acceptanceConfig (flag : Bool) : Config Universal.State :=
  { expr := acceptanceExpr flag
    store :=
      { runtime := { instances := #[acceptanceInstance], entry := ⟨0⟩ }
        wasm :=
          { (Project.Mergesort.module.initialStore : Store Universal.State) with
            host := acceptanceHost } } }

def acceptancePost (flag : Bool)
    (outcome : ObservableOutcome)
    (store : MachineStore Universal.State) : Prop :=
  if flag then
    outcome = .done [.i32 7] ∧ store.wasm.host = acceptanceHost
  else
    outcome = .trapped (.host OOM.trapMessage) ∧
      store.wasm.host = WrapperProof.afterOom acceptanceHost

/-- One principal caller contract covers normal completion and exact OOM
without reopening the host implementation in the caller. -/
theorem twp_acceptanceCaller
    [WasmSmallStepGS hlc Universal.State]
    (flag : Bool) :
    runtimeModuleOwn ⟨0⟩ Project.Mergesort.module ∗
      hostEnvOwn 0 (Universal.envFor Project.Mergesort.module) ∗
      hostStateOwn acceptanceHost ⊢
    WP (acceptanceExpr flag) @ Stuckness.NotStuck; ⊤
      [{ outcome,
        ∀ (store : MachineStore Universal.State)
            (_observations : List StepKind),
          stateInterp (GF := WasmHeapGF Universal.State) store 0 [] 0 -∗
          ⌜acceptancePost flag outcome store⌝ }] := by
  iintro ⟨Hruntime, Henv, Hhost⟩
  cases flag
  · dsimp only [acceptanceExpr]
    iapply twp_iff (selectedBody := [.call 2]) rfl
    iapply twp_oom_import acceptanceHost
    isplitl [Hhost]
    · iexact Hhost
    isplitl [Hruntime]
    · iexact Hruntime
    isplitl [Henv]
    · iexact Henv
    iintro Hhost
    iintro %store %observations Hstate
    ihave %hhost :
        ⌜store.wasm.host = WrapperProof.afterOom acceptanceHost⌝ $$
        [Hstate Hhost]
    · iapply stateInterp_host_agree store 0 observations 0
      iframe Hstate Hhost
    ipureintro
    exact ⟨rfl, hhost⟩
  · dsimp only [acceptanceExpr]
    iapply twp_iff (selectedBody := [.const 7]) rfl
    iapply twp_const
    iapply twp_exitControl (by rfl)
    iapply twp_finish
    iapply Wasm.SmallStep.twp_outcome_done
    iintro %store %observations Hstate
    ihave %hhost : ⌜store.wasm.host = acceptanceHost⌝ $$ [Hstate Hhost]
    · iapply stateInterp_host_agree store 0 observations 0
      iframe Hstate Hhost
    ipureintro
    exact ⟨rfl, hhost⟩

/-- The acceptance caller has one finite authoritative execution ending in the
normal result selected by `flag`, or in the exact `talos.oom` trap. -/
theorem acceptance_total (flag : Bool) :
    TerminatesWithOutcome (acceptanceConfig flag) (acceptancePost flag) := by
  apply wasm_smallStep_heap_globals_runtime_host_store_terminatesWithOutcome
      (σ := (∅ : WasmHeapMap (Option UInt8)))
      (globalσ := (∅ : WasmGlobalMap Value))
  · exact heapAgreesWithMem_empty _
  · exact heapAddressesInBounds_empty _
  · exact globalHeapAgrees_empty _
  · simp [acceptanceConfig]
  · intro hlc gs
    simp only [BI.BigSepM.bigSepM_empty.to_eq, acceptanceConfig,
      acceptanceInstance, RuntimeEnv.currentModule_mk1,
      RuntimeEnv.currentHost_mk1]
    iintro ⟨_Hheap, _Hglobals, Hruntime, Henv, Hhost⟩
    iapply twp_acceptanceCaller flag
    iframe Hruntime Henv Hhost

theorem acceptance_returns :
    TerminatesWith (acceptanceConfig true)
      (fun values store =>
        values = [.i32 7] ∧ store.wasm.host = acceptanceHost) := by
  have hexec : TerminatesWithOutcome
      (acceptanceConfig true) (acceptancePost true) :=
    acceptance_total true
  rcases hexec with ⟨trace, outcome, store, steps, hpost⟩
  change outcome = .done [.i32 7] ∧
    store.wasm.host = acceptanceHost at hpost
  rcases hpost with ⟨rfl, hhost⟩
  change ∃ trace values store,
    Steps (acceptanceConfig true) trace ⟨.done values, store⟩ ∧
      (values = [.i32 7] ∧ store.wasm.host = acceptanceHost)
  exact ⟨trace, [.i32 7], store, steps, rfl, hhost⟩

theorem acceptance_oom :
    TrapsWith (acceptanceConfig false) (.host OOM.trapMessage)
      (fun store =>
        store.wasm.host = WrapperProof.afterOom acceptanceHost) := by
  have hexec : TerminatesWithOutcome
      (acceptanceConfig false) (acceptancePost false) :=
    acceptance_total false
  rcases hexec with ⟨trace, outcome, store, steps, hpost⟩
  change outcome = .trapped (.host OOM.trapMessage) ∧
    store.wasm.host = WrapperProof.afterOom acceptanceHost at hpost
  rcases hpost with ⟨rfl, hhost⟩
  change ∃ trace store,
    Steps (acceptanceConfig false) trace
      ⟨.trapped (.host OOM.trapMessage), store⟩ ∧
    store.wasm.host = WrapperProof.afterOom acceptanceHost
  exact ⟨trace, store, steps, hhost⟩

end Project.Mergesort.OutcomeInfrastructure
