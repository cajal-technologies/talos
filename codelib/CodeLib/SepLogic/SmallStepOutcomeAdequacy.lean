import CodeLib.SepLogic.SmallStepAdequacy
import CodeLib.SepLogic.SmallStepOutcomeLanguage

/-!
# Adequacy for outcome-valued Wasm total WPs

The scoped outcome language changes only which terminal expressions count as
values.  This file connects a total WP over that view to one finite
authoritative Wasm trace ending either in `.done` or `.trapped`, while retaining
the final `MachineStore` in the postcondition.
-/

namespace Wasm.SmallStep

open Iris OFE COFE BI Iris.BI Iris.Algebra Iris.ProgramLogic
  Language.Notation Std FromMathlib LawfulSet
open Wasm.SepLogic
open scoped Outcome

private instance instOutcomeLanguageNoFork :
    @LanguageNoFork (Expr α) (MachineStore α) StepKind ObservableOutcome
      outcomeLanguage where
  no_fork h := h.1

/-- Lower outcome-valued Iris adequacy to the authoritative Wasm relational
partial-correctness predicate.  This theorem makes no normalization or
termination claim: it only classifies finite traces which have already reached
an observable terminal expression. -/
theorem adequate_to_partiallyMeetsOutcome
    (config : Config α)
    (post : ObservableOutcome → MachineStore α → Prop)
    (had : adequate Stuckness.NotStuck config.expr config.store post) :
    PartiallyMeetsOutcome config post := by
  intro trace outcome store steps
  apply had.adequate_result [] store outcome
  change ([config.expr], config.store) -·->ₜₚ*
    ([outcome.toExpr], store)
  exact steps.to_languageErasedSteps

/-- Strong normalization plus outcome-valued Iris adequacy reaches exactly one
observable Wasm terminal.  The theorem is deliberately independent of how the
initial Iris resources were allocated, so memory- and host-aware adequacy
frontends can share it. -/
theorem stronglyNormalizing_adequate_outcome
    (config : Config α)
    (post : ObservableOutcome → MachineStore α → Prop)
    (hsn : StronglyNormalizing
      (@ExprErasedStep (Expr α) (MachineStore α) StepKind
        ObservableOutcome outcomeLanguage)
      (config.expr, config.store))
    (had : adequate Stuckness.NotStuck config.expr config.store post) :
    TerminatesWithOutcome config post := by
  obtain ⟨⟨finalExpr, finalStore⟩, hreach, hirred⟩ :=
    stronglyNormalizing_reaches_irreducible hsn
  obtain ⟨trace, hsteps⟩ :=
    exprErasedSteps_to_steps (Terminal := ObservableOutcome) hreach
  have hirisReach : FromMathlib.Relation.ReflTransGen
      (@Language.ErasedStep (Expr α) ObservableOutcome
        (MachineStore α) StepKind outcomeLanguage)
      ([config.expr], config.store) ([finalExpr], finalStore) :=
    hsteps.to_languageErasedSteps
  have hnotStuck := had.adequate_not_stuck
    [finalExpr] finalStore finalExpr rfl hirisReach (by simp)
  rcases hnotStuck with hvalue | hreducible
  · cases hval :
      @toVal (Expr α) ObservableOutcome outcomeToVal finalExpr with
    | none =>
      simp [hval] at hvalue
    | some outcome =>
      have hexpr : finalExpr = outcome.toExpr :=
        (@ToVal.coe_of_toVal_eq_some (Expr α) ObservableOutcome
          outcomeToVal finalExpr outcome hval).symm
      subst finalExpr
      exact ⟨trace, outcome, finalStore, hsteps,
        had.adequate_result [] finalStore outcome hirisReach⟩
  · obtain ⟨κ, nextExpr, nextStore, forks, hprim⟩ := hreducible
    exact False.elim
      (hirred (nextExpr, nextStore) ⟨κ, forks, hprim⟩)

/-- Expose the two semantic terminal predicates already used by public Talos
specifications.  This is pure case analysis; it does not replay execution. -/
theorem TerminatesWithOutcome.to_success_or_trap
    (execution : TerminatesWithOutcome config post) :
    (∃ values, TerminatesWith config
      (fun reached store =>
        reached = values ∧ post (.done values) store)) ∨
    (∃ reason, TrapsWith config reason
      (fun store => post (.trapped reason) store)) := by
  obtain ⟨trace, outcome, store, steps, hpost⟩ := execution
  cases outcome with
  | done values =>
      exact .inl ⟨values, trace, values, store, steps, rfl, hpost⟩
  | trapped reason =>
      exact .inr ⟨reason, trace, store, steps, hpost⟩

/-! ## Store-sensitive outcome frontends -/

/-- Outcome-valued adequacy with the complete physical footprint needed by
stateful generated programs.  In addition to heap, globals, and runtime
identity, the client receives the concrete host environment and the exclusive
host-state fragment, so host calls can update it.  The terminal continuation
then consumes `stateInterp` to relate that fragment to the authoritative final
`MachineStore`. -/
theorem wasm_smallStep_heap_globals_runtime_host_store_adequacy_outcome_at
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
    (hwp : ∀ [WasmSmallStepGS .hasLC α],
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
          {{ outcome,
            ∀ (store : MachineStore α) (_observations : List StepKind),
              stateInterp (GF := WasmHeapGF α) store 0 [] 0 -∗
              ⌜post outcome store⌝ }}) :
    adequate Stuckness.NotStuck config.expr config.store post := by
  refine wp_store_adequacy
    (GF := WasmHeapGF α) Stuckness.NotStuck
    config.expr config.store post ?_
  intro inv κs
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
  letI gs : WasmSmallStepGS .hasLC α := smallStepGS .hasLC inv
  iclear Hmeta
  imodintro
  iexists (fun store _observations =>
    stateInterp (GF := WasmHeapGF α) store 0 [] 0)
  iexists (fun _ => iprop(True))
  dsimp only
  wasm_build_machine_aux config
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth' HruntimeInstances HinstanceState HhostEnvAuth' HhostState Hexc]
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
    unfold runtimeModuleElem runtimeInstancesOwn hostStateAuth currentInstanceAuth currentInstanceAuthN
    simp only [BI.BigSepM.bigSepM_singleton.to_eq]
    iframe Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth' # HruntimeInstances HinstanceState HhostEnvAuth' HhostState Hexc
    ipureexact ⟨hagree, hinBounds, hglobals,
      dataSegmentHeapAgrees_empty _,
      tableHeapAgrees_empty _,
      elementSegmentHeapAgrees_empty _,
      runtimeModuleSingletonAgrees config.store.runtime hwf,
      hostEnvSingletonAgrees config.store.runtime hwf⟩
  · iapply hwp
    isplitl_exact Hpoints
    · isplitl [HglobalPoints]
      · unfold globalPointsTo
        iexact HglobalPoints
      · isplitl [HruntimeWP HinstanceFrag]
        · unfold runtimeModuleOwn
          isplitl [HruntimeWP]
          · unfold runtimeModuleElem; iexact HruntimeWP
          · unfold currentInstanceOwnN; iexact HinstanceFrag
        · isplitl [HhostEnvWP]
          · unfold hostEnvOwn
            iexact HhostEnvWP
          · isplitl [HhostStateFrag]
            · unfold hostStateOwn
              iexact HhostStateFrag
            · isplitl_exact HheapFrontier
              · iexact HmemoryPagesOwn

/-- Backwards-compatible outcome adequacy with the maximally permissive heap
frontier.  Allocator-aware clients should use the `_at` theorem and retain the
exclusive frontier fragment. -/
theorem wasm_smallStep_heap_globals_runtime_host_store_adequacy_outcome
    [WasmSmallStepGpreS α]
    (config : Config α)
    (σ : WasmHeapMap (Option UInt8))
    (globalσ : WasmGlobalMap Value)
    (post : ObservableOutcome → MachineStore α → Prop)
    (hagree : heapAgreesWithMem σ (storeResolve config.store))
    (hinBounds : heapAddressesInBounds σ (storeResolve config.store))
    (hglobals : globalHeapAgrees globalσ config.store.wasm.globals)
    (hwf : config.store.runtime.entry.id < config.store.runtime.instances.size)
    (hwp : ∀ [WasmSmallStepGS .hasLC α],
      (([∗map] address ↦ value ∈ σ,
          pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
            address (DFrac.own 1) value) ∗
        ([∗map] index ↦ value ∈ globalσ,
          globalPointsTo index value) ∗
        runtimeModuleOwn config.store.runtime.entry
            config.store.runtime.currentModule ∗
        hostEnvOwn config.store.runtime.entry.id
            config.store.runtime.currentHost ∗
        hostStateOwn config.store.wasm.host) ⊢
        WP config.expr @ Stuckness.NotStuck; ⊤
          {{ outcome,
            ∀ (store : MachineStore α) (_observations : List StepKind),
              stateInterp (GF := WasmHeapGF α) store 0 [] 0 -∗
              ⌜post outcome store⌝ }}) :
    adequate Stuckness.NotStuck config.expr config.store post := by
  apply wasm_smallStep_heap_globals_runtime_host_store_adequacy_outcome_at
      config σ globalσ UInt32.size post hagree hinBounds
      (heapBelow_uint32Size σ) hglobals hwf
  intro gs
  iintro ⟨Hheap, Hglobals, Hruntime, Henv, Hhost, _Hfrontier, _Hpages⟩
  iapply_frame hwp using [Hheap Hglobals Hruntime Henv Hhost]

/-- Outcome-valued total-WP initialization for the same complete physical
footprint as
`wasm_smallStep_heap_globals_runtime_host_store_adequacy_outcome`. -/
theorem wasm_smallStep_heap_globals_runtime_host_stronglyNormalizing_outcome
    [WasmSmallStepGpreS α]
    (config : Config α)
    (σ : WasmHeapMap (Option UInt8))
    (globalσ : WasmGlobalMap Value)
    (Φ : ObservableOutcome → IProp (WasmHeapGF α))
    (hagree : heapAgreesWithMem σ (storeResolve config.store))
    (hinBounds : heapAddressesInBounds σ (storeResolve config.store))
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
        hostStateOwn config.store.wasm.host) ⊢
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
  wasm_alloc_memory_ghosts config from σ
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
      imodintro
      iexact Hstate)
  dsimp only
  wasm_build_machine_aux config
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth' HruntimeInstances HinstanceState HhostEnvAuth' HhostState Hexc]
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
    unfold runtimeModuleElem runtimeInstancesOwn hostStateAuth currentInstanceAuth currentInstanceAuthN
    simp only [BI.BigSepM.bigSepM_singleton.to_eq]
    iframe Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth' # HruntimeInstances HinstanceState HhostEnvAuth' HhostState Hexc
    ipureexact ⟨hagree, hinBounds, hglobals,
      dataSegmentHeapAgrees_empty _,
      tableHeapAgrees_empty _,
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
          · unfold runtimeModuleElem; iexact HruntimeWP
          · unfold currentInstanceOwnN; iexact HinstanceFrag
        · isplitl [HhostEnvWP]
          · unfold hostEnvOwn
            iexact HhostEnvWP
          · unfold hostStateOwn
            iexact HhostStateFrag

/-- Final store-sensitive total adequacy for outcome-valued Wasm proofs.  One
TWP proof supplies both strong normalization and ordinary safety; the reached
terminal is therefore a finite authoritative `.done` or `.trapped` trace, and
the postcondition observes the actual final machine store. -/
theorem wasm_smallStep_heap_globals_runtime_host_store_terminatesWithOutcome
    [WasmSmallStepGpreS α]
    (config : Config α)
    (σ : WasmHeapMap (Option UInt8))
    (globalσ : WasmGlobalMap Value)
    (post : ObservableOutcome → MachineStore α → Prop)
    (hagree : heapAgreesWithMem σ (storeResolve config.store))
    (hinBounds : heapAddressesInBounds σ (storeResolve config.store))
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
        hostStateOwn config.store.wasm.host) ⊢
        WP config.expr @ Stuckness.NotStuck; ⊤
          [{ outcome,
            ∀ (store : MachineStore α) (_observations : List StepKind),
              stateInterp (GF := WasmHeapGF α) store 0 [] 0 -∗
              ⌜post outcome store⌝ }]) :
    TerminatesWithOutcome config post := by
  apply stronglyNormalizing_adequate_outcome config post
  · apply
      wasm_smallStep_heap_globals_runtime_host_stronglyNormalizing_outcome
        config σ globalσ (fun _outcome => iprop(True))
        hagree hinBounds hglobals hwf
    intro hlc gs
    iintro Hresources
    iapply (twp.mono (fun _ => BI.true_intro))
    iapply_exact htwp hlc with Hresources
  · apply wasm_smallStep_heap_globals_runtime_host_store_adequacy_outcome
      config σ globalσ post hagree hinBounds hglobals hwf
    intro gs
    iintro Hresources
    iapply twp.to_wp
    iapply_exact htwp .hasLC with Hresources

end Wasm.SmallStep
