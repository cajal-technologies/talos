import CodeLib.SepLogic.SmallStepOutcomeAdequacy

/-!
# Total outcome adequacy at an explicit heap frontier

`CodeLib.SepLogic.SmallStepOutcomeAdequacy` gives two frontends for a proof
that opens `Wasm.SmallStep.Outcome`.  The partial one,
`wasm_smallStep_heap_globals_runtime_host_store_adequacy_outcome_at`, hands
the proof `heapFrontierOwn frontier` and `memoryPagesOwn pages`, so a body
that calls the allocator can run under it.  The total one,
`wasm_smallStep_heap_globals_runtime_host_store_terminatesWithOutcome`,
allocates the memory ghosts with the maximally permissive frontier and hands
out neither fragment, so an allocator-aware proof cannot use it.

This module states the total frontend at an explicit frontier.  The proof is
the proof of the existing total frontend with the four initialization steps of
the partial `_at` frontend in place of `wasm_alloc_memory_ghosts`, and two more
frames at the end.

PR #235 states the same two theorems under the names
`wasm_smallStep_heap_globals_runtime_host_stronglyNormalizing_outcome_at` and
`wasm_smallStep_heap_globals_runtime_host_store_terminatesWithOutcome_at`.
The names here carry the suffix `_frontier` so that the two PRs merge in
either order.  Delete this module when that PR lands and call its `_at`
theorems.
-/

namespace Wasm.SmallStep

open Iris OFE COFE BI Iris.BI Iris.Algebra Iris.ProgramLogic
  Language.Notation Std FromMathlib LawfulSet
open Wasm.SepLogic
open scoped Outcome

private instance instOutcomeLanguageNoForkFrontier :
    @LanguageNoFork (Expr α) (MachineStore α) StepKind ObservableOutcome
      outcomeLanguage where
  no_fork h := h.1

/-- Outcome-valued total-WP initialization at an explicit heap frontier. -/
theorem wasm_smallStep_heap_globals_runtime_host_stronglyNormalizing_outcome_frontier
    [WasmSmallStepGpreS α]
    (config : Config α)
    (σ : WasmHeapMap (Option UInt8))
    (globalσ : WasmGlobalMap Value)
    (frontier : Nat)
    (Φ : ObservableOutcome → IProp (WasmHeapGF α))
    (hagree : heapAgreesWithMem σ (storeResolve config.store))
    (hinBounds : heapAddressesInBounds σ (storeResolve config.store))
    (hbelow : HeapBelow σ frontier)
    (hglobals : globalHeapAgrees globalσ config.store.wasm.globals)
    (hwf : config.store.runtime.entry.id < config.store.runtime.instances.size)
    (htwp : ∀ (hlc : HasLC) [WasmSmallStepGS hlc α],
      (([∗map] address ↦ value ∈ σ,
          pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
            address (DFrac.own 1) value) ∗
        ([∗map] index ↦ value ∈ globalσ,
          globalPointsTo index value) ∗
        runtimeModuleOwn config.store.runtime.entry
            config.store.runtime.currentModule ∗
        hostEnvOwn config.store.runtime.entry.id
            config.store.runtime.currentHost ∗
        hostStateOwn config.store.wasm.host ∗
        heapFrontierOwn frontier ∗
        memoryPagesOwn config.store.wasm.mem.pages) ⊢
        WP config.expr @ Stuckness.NotStuck; ⊤ [{ Φ }]) :
    StronglyNormalizing
      (@ExprErasedStep (Expr α) (MachineStore α) StepKind
        ObservableOutcome outcomeLanguage)
      (config.expr, config.store) := by
  apply stronglyNormalizing_expr_of_threadPool
  apply twp_total (hlc := .hasNoLC) (GF := WasmHeapGF α)
    Stuckness.NotStuck config.expr config.store
    (fun _values => iprop(True)) 0 0
  intro inv
  imod genHeap_init (L := MemoryKey) (V := Option UInt8)
      (GF := WasmHeapGF α) (H := WasmHeapMap) σ with
    ⟨%heapGS, Hheap, Hpoints, Hmeta⟩
  imod heapDomain_init_at (α := α) σ frontier hbelow with
    ⟨%heapDomainGS, HheapDomain, HheapFrontier⟩
  letI _ : WasmHeapDomainGS α := heapDomainGS
  imod memoryPages_init (α := α) config.store.wasm.mem.pages with
    ⟨%memoryPagesGS, HmemoryPagesAuth, HmemoryPagesOwn⟩
  letI _ : WasmMemoryPagesGS α := memoryPagesGS
  wasm_alloc_globals_and_empty_heap_maps globalσ
  wasm_install_heap_map_instances
  wasm_alloc_current_runtime_module config
  wasm_alloc_current_host_env config
  wasm_alloc_host_state config
  wasm_alloc_current_instance config
  wasm_alloc_fixed_runtime_resources config
  letI gs : WasmSmallStepGS .hasNoLC α := smallStepGS .hasNoLC inv
  iclear Hmeta
  imodintro
  iexists
    (fun store (_ : Nat) (observations : List StepKind) (_ : Nat) =>
      stateInterp (GF := WasmHeapGF α) store 0 observations 0),
    (fun _ => 0), (fun _ => iprop(True)),
    (fun _ _ _ _ => by
      iintro Hstate
      imodintro; iexact Hstate)
  dsimp only
  wasm_build_machine_aux config
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments
    HruntimeModuleAuth' HruntimeInstances HinstanceState HhostEnvAuth'
    HhostState Hexc]
  · iapply (stateInterp_eq config.store 0 [] 0).mpr
    iexists σ
    iexists globalσ
    iexists (∅ : WasmDataSegmentMap (Option (List UInt8)))
    iexists (∅ : WasmTableMap TableInst)
    iexists (∅ : WasmElementSegmentMap (Option (List (Option Nat))))
    iexists (PartialMap.singleton config.store.runtime.entry.id
      config.store.runtime.currentModule)
    iexists (PartialMap.singleton config.store.runtime.entry.id
      config.store.runtime.currentHost)
    unfold runtimeModuleElem runtimeInstancesOwn hostStateAuth
      currentInstanceAuth currentInstanceAuthN
    simp only [BI.BigSepM.bigSepM_singleton.to_eq]
    iframe Hheap Hglobals Hsegments Htables HelementSegments
      HruntimeModuleAuth' # HruntimeInstances HinstanceState HhostEnvAuth'
      HhostState Hexc
    ipureexact ⟨hagree, hinBounds, hglobals,
      dataSegmentHeapAgrees_empty _, tableHeapAgrees_empty _,
      elementSegmentHeapAgrees_empty _,
      runtimeModuleSingletonAgrees config.store.runtime hwf,
      hostEnvSingletonAgrees config.store.runtime hwf⟩
  · iintro _
    iapply (twp.mono (fun _ => BI.true_intro))
    iapply_splitl_exact htwp .hasNoLC with Hpoints
    · isplitl [HglobalPoints]
      · unfold globalPointsTo
        iexact HglobalPoints
      · isplitl [HruntimeWP HinstanceFrag]
        · unfold runtimeModuleOwn
          isplitl [HruntimeWP]
          · unfold runtimeModuleElem
            iexact HruntimeWP
          · unfold currentInstanceOwnN
            iexact HinstanceFrag
        · isplitl [HhostEnvWP]
          · unfold hostEnvOwn
            iexact HhostEnvWP
          · isplitl [HhostStateFrag]
            · unfold hostStateOwn
              iexact HhostStateFrag
            · isplitl_exact HheapFrontier
              · iexact HmemoryPagesOwn

/-- Frontier-aware store-sensitive total adequacy for outcome-valued Wasm
proofs.  One TWP proof supplies both strong normalization and ordinary safety,
so the reached terminal is a finite authoritative `.done` or `.trapped` trace
and the postcondition observes the actual final machine store. -/
theorem wasm_smallStep_heap_globals_runtime_host_store_terminatesWithOutcome_frontier
    [WasmSmallStepGpreS α]
    (config : Config α)
    (σ : WasmHeapMap (Option UInt8))
    (globalσ : WasmGlobalMap Value)
    (frontier : Nat)
    (post : ObservableOutcome → MachineStore α → Prop)
    (hagree : heapAgreesWithMem σ (storeResolve config.store))
    (hinBounds : heapAddressesInBounds σ (storeResolve config.store))
    (hbelow : HeapBelow σ frontier)
    (hglobals : globalHeapAgrees globalσ config.store.wasm.globals)
    (hwf : config.store.runtime.entry.id < config.store.runtime.instances.size)
    (htwp : ∀ (hlc : HasLC) [WasmSmallStepGS hlc α],
      (([∗map] address ↦ value ∈ σ,
          pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
            address (DFrac.own 1) value) ∗
        ([∗map] index ↦ value ∈ globalσ,
          globalPointsTo index value) ∗
        runtimeModuleOwn config.store.runtime.entry
            config.store.runtime.currentModule ∗
        hostEnvOwn config.store.runtime.entry.id
            config.store.runtime.currentHost ∗
        hostStateOwn config.store.wasm.host ∗
        heapFrontierOwn frontier ∗
        memoryPagesOwn config.store.wasm.mem.pages) ⊢
        WP config.expr @ Stuckness.NotStuck; ⊤
          [{ outcome,
            ∀ (store : MachineStore α) (_observations : List StepKind),
              stateInterp (GF := WasmHeapGF α) store 0 [] 0 -∗
              ⌜post outcome store⌝ }]) :
    TerminatesWithOutcome config post := by
  apply stronglyNormalizing_adequate_outcome config post
  · apply
      wasm_smallStep_heap_globals_runtime_host_stronglyNormalizing_outcome_frontier
        config σ globalσ frontier (fun _outcome => iprop(True))
        hagree hinBounds hbelow hglobals hwf
    intro hlc gs
    iintro Hresources
    iapply (twp.mono (fun _ => BI.true_intro))
    iapply_exact htwp hlc with Hresources
  · apply wasm_smallStep_heap_globals_runtime_host_store_adequacy_outcome_at
      config σ globalσ frontier post hagree hinBounds hbelow hglobals hwf
    intro gs
    iintro Hresources
    iapply twp.to_wp
    iapply_exact htwp .hasLC with Hresources

end Wasm.SmallStep
