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
  letI globalMapG : GhostMapG (WasmHeapGF α) GlobalKey Value WasmGlobalMap := by
    constructor
    exists 7
  imod (ghost_map_alloc (GF := WasmHeapGF α) (K := GlobalKey)
      (V := Value) (H := WasmGlobalMap) globalσ) with
    ⟨%globalName, Hglobals, HglobalPoints⟩
  letI dataSegmentMapG :
      GhostMapG (WasmHeapGF α) DataSegmentKey (Option (List UInt8))
        WasmDataSegmentMap := by
    constructor
    exists 9
  imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := DataSegmentKey)
      (V := Option (List UInt8)) (H := WasmDataSegmentMap)) with
    ⟨%dataSegmentName, Hsegments⟩
  letI tableMapG : GhostMapG (WasmHeapGF α) TableKey TableInst WasmTableMap := by
    constructor
    exists 10
  imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := TableKey)
      (V := TableInst) (H := WasmTableMap)) with
    ⟨%tableName, Htables⟩
  letI elementSegmentMapG :
      GhostMapG (WasmHeapGF α) ElementSegmentKey (Option (List (Option Nat)))
        WasmElementSegmentMap := by
    constructor
    exists 11
  imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := ElementSegmentKey)
      (V := Option (List (Option Nat))) (H := WasmElementSegmentMap)) with
    ⟨%elementSegmentName, HelementSegments⟩
  letI wasmHeapGS : WasmHeapGS α :=
    { togenHeapGS := heapGS }
  letI wasmGlobalGS : WasmGlobalGS α :=
    { toGhostMapG := globalMapG
      globalName := globalName }
  letI wasmDataSegmentGS : WasmDataSegmentGS α :=
    { toGhostMapG := dataSegmentMapG
      dataSegmentName := dataSegmentName }
  letI wasmTableGS : WasmTableGS α :=
    { toGhostMapG := tableMapG
      tableName := tableName }
  letI wasmElementSegmentGS : WasmElementSegmentGS α :=
    { toGhostMapG := elementSegmentMapG
      elementSegmentName := elementSegmentName }
  letI runtimeModuleMapG : GhostMapG (WasmHeapGF α) Nat Module WasmRuntimeModuleMap := by
    constructor
    exists 8
  imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := Nat)
      (V := Module) (H := WasmRuntimeModuleMap)) with ⟨%runtimeName, HruntimeModuleAuth⟩
  imod ghost_map_insert_persist (k := config.store.runtime.entry.id)
      (v := config.store.runtime.currentModule)
      (get?_empty config.store.runtime.entry.id) $$ HruntimeModuleAuth with
    ⟨HruntimeModuleAuth', HruntimeWP⟩
  iintuitionistic HruntimeWP
  rw [show insert (∅ : WasmRuntimeModuleMap Module)
      config.store.runtime.entry.id config.store.runtime.currentModule =
      PartialMap.singleton config.store.runtime.entry.id
      config.store.runtime.currentModule from rfl]
  letI runtimeGS : WasmRuntimeModuleGS α :=
    { toGhostMapG := runtimeModuleMapG
      runtimeName }
  letI hostEnvMapG : GhostMapG (WasmHeapGF α) Nat (HostEnv α) WasmHostEnvMap := by
    constructor
    exists 12
  imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := Nat)
      (V := HostEnv α) (H := WasmHostEnvMap)) with ⟨%hostEnvName, HhostEnvAuth⟩
  imod ghost_map_insert_persist (k := config.store.runtime.entry.id)
      (v := config.store.runtime.currentHost)
      (get?_empty config.store.runtime.entry.id) $$ HhostEnvAuth with
    ⟨HhostEnvAuth', HhostEnvWP⟩
  iintuitionistic HhostEnvWP
  rw [show insert (∅ : WasmHostEnvMap (HostEnv α))
      config.store.runtime.entry.id config.store.runtime.currentHost =
      PartialMap.singleton config.store.runtime.entry.id
      config.store.runtime.currentHost from rfl]
  letI hostEnvGS : WasmHostEnvGS α :=
    { toGhostMapG := hostEnvMapG
      hostEnvName }
  letI hostStateElem :
      ElemG (WasmHeapGF α)
        (Auth.AuthRF (OptionOF (Excl.ExclOF (constOF (DiscreteO α))))) := by
    exists 13
  imod (iOwn_alloc (E := hostStateElem)
      (ExclAuth.auth (⟨config.store.wasm.host⟩ : DiscreteO α) •
       ExclAuth.frag (⟨config.store.wasm.host⟩ : DiscreteO α))
      ExclAuth.valid) with
    ⟨%hostStateName, HhostStateAll⟩
  ihave HhostStatePair := iOwn_op.mp $$ HhostStateAll
  icases HhostStatePair with ⟨HhostState, HhostStateFrag⟩
  letI hostStateGS : WasmHostStateGS α :=
    { hostStateElem
      hostStateName }
  letI instanceElem :
      ElemG (WasmHeapGF α)
        (Auth.AuthRF (OptionOF (Excl.ExclOF (constOF (DiscreteO Nat))))) := by
    exists 14
  imod (iOwn_alloc (E := instanceElem)
      (ExclAuth.auth (⟨config.store.runtime.entry.id⟩ : DiscreteO Nat) •
       ExclAuth.frag (⟨config.store.runtime.entry.id⟩ : DiscreteO Nat))
      ExclAuth.valid) with
    ⟨%instanceName, HinstanceAll⟩
  ihave HinstancePair := iOwn_op.mp $$ HinstanceAll
  icases HinstancePair with ⟨HinstanceState, HinstanceFrag⟩
  letI instanceGS : WasmInstanceGS α :=
    { instanceElem
      instanceName }
  letI runtimeInstancesElem :
      ElemG (WasmHeapGF α) (constOF (Agree (DiscreteO (Array (ModuleInstance α))))) := by
    exists 15
  imod (iOwn_alloc (E := runtimeInstancesElem)
      (toAgree ⟨config.store.runtime.instances⟩) (fun _ => trivial)) with
    ⟨%runtimeInstancesName, HruntimeInstances⟩
  letI runtimeInstancesGS : WasmRuntimeInstancesGS α :=
    { runtimeInstancesElem
      runtimeInstancesName }
  letI exceptionMapG :
      GhostMapG (WasmHeapGF α) Nat (Nat × List Value) WasmExceptionMap := by
    constructor
    exists 16
  imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := Nat)
      (V := Nat × List Value) (H := WasmExceptionMap)) with
    ⟨%exceptionName, Hexceptions⟩
  letI wasmExceptionGS : WasmExceptionGS α :=
    { toGhostMapG := exceptionMapG
      exceptionName := exceptionName }
  letI tagTableElem : ElemG (WasmHeapGF α)
      (constOF (Agree (DiscreteO (List Nat)))) := by
    exists 17
  imod (iOwn_alloc (E := tagTableElem)
      (toAgree ⟨config.store.wasm.tagIds⟩) (fun _ => trivial)) with
    ⟨%tagTableName, HtagTable⟩
  letI tagTableGS : WasmTagTableGS α :=
    { tagTableElem
      tagTableName }
  letI gs : WasmSmallStepGS .hasLC α :=
    { toInvGS_gen := inv
      toWasmHeapGS := wasmHeapGS
      heapDomain := heapDomainGS
      memoryPages := memoryPagesGS
      global := wasmGlobalGS
      dataSegment := wasmDataSegmentGS
      table := wasmTableGS
      elementSegment := wasmElementSegmentGS
      exception := wasmExceptionGS
      tagTable := tagTableGS
      runtime := runtimeGS
      hostEnv := hostEnvGS
      hostState := hostStateGS
      instanceGS := instanceGS
      runtimeInstances := runtimeInstancesGS }
  iclear Hmeta
  imodintro
  iexists (fun store _observations =>
    stateInterp (GF := WasmHeapGF α) store 0 [] 0)
  iexists (fun _ => iprop(True))
  dsimp only
  ihave HexceptionInterp : exceptionInterp config.store.wasm.exns config.store.wasm.tagIds $$
      [Hexceptions HtagTable]
  · unfold exceptionInterp tagTableOwn
    isplitl [Hexceptions]
    · iexists (∅ : WasmExceptionMap (Nat × List Value))
      isplitl [Hexceptions]
      · iexact Hexceptions
      · ipureintro
        exact exceptionHeapAgrees_empty _
    · iexists config.store.wasm.tagIds
      isplitl [HtagTable]
      · iexact HtagTable
      · ipureintro
        exact List.prefix_rfl -- The ordinary frontier is installed below.
  ihave Hexc : machineAuxInterp _ config.store.wasm.mem.pages
      config.store.wasm.exns config.store.wasm.tagIds $$
      [HmemoryPagesAuth HheapDomain HexceptionInterp]
  · unfold machineAuxInterp
    iframe HmemoryPagesAuth HheapDomain HexceptionInterp
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
    ipureintro
    exact ⟨hagree, hinBounds, hglobals,
      dataSegmentHeapAgrees_empty _,
      tableHeapAgrees_empty _,
      elementSegmentHeapAgrees_empty _,
      fun id m hm => by
        by_cases h : id = config.store.runtime.entry.id
        · subst h; simp [PartialMap.singleton, get?_insert_eq rfl] at hm; subst hm
          rw [Array.getElem?_eq_getElem hwf]
          simp [RuntimeEnv.currentModule, RuntimeEnv.currentInstance]
          rw [getElem!_pos config.store.runtime.instances config.store.runtime.entry.id hwf]
        · simp [PartialMap.singleton, get?_insert_ne (Ne.symm h), get?_empty] at hm,
      fun id env hm => by
        by_cases h : id = config.store.runtime.entry.id
        · subst h; simp [PartialMap.singleton, get?_insert_eq rfl] at hm; subst hm
          rw [Array.getElem?_eq_getElem hwf, Option.map_some]
          simp [RuntimeEnv.currentHost, RuntimeEnv.currentInstance]
          rw [getElem!_pos config.store.runtime.instances config.store.runtime.entry.id hwf]
        · simp [PartialMap.singleton, get?_insert_ne (Ne.symm h), get?_empty] at hm⟩
  · iapply hwp
    isplitl [Hpoints]
    · iexact Hpoints
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
            · isplitl [HheapFrontier]
              · iexact HheapFrontier
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
  iapply hwp
  iframe Hheap Hglobals Hruntime Henv Hhost

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
  imod genHeap_init (L := MemoryKey) (V := Option UInt8)
      (GF := WasmHeapGF α) (H := WasmHeapMap) σ with
    ⟨%heapGS, Hheap, Hpoints, Hmeta⟩
  imod heapDomain_init (α := α) σ with
    ⟨%heapDomainGS, HheapDomain⟩
  letI _ : WasmHeapDomainGS α := heapDomainGS
  imod memoryPages_init_authority (α := α)
      config.store.wasm.mem.pages with
    ⟨%memoryPagesGS, HmemoryPagesAuth⟩
  letI _ : WasmMemoryPagesGS α := memoryPagesGS
  letI globalMapG : GhostMapG (WasmHeapGF α) GlobalKey Value WasmGlobalMap := by
    constructor
    exists 7
  imod (ghost_map_alloc (GF := WasmHeapGF α) (K := GlobalKey)
      (V := Value) (H := WasmGlobalMap) globalσ) with
    ⟨%globalName, Hglobals, HglobalPoints⟩
  letI dataSegmentMapG :
      GhostMapG (WasmHeapGF α) DataSegmentKey (Option (List UInt8))
        WasmDataSegmentMap := by
    constructor
    exists 9
  imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := DataSegmentKey)
      (V := Option (List UInt8)) (H := WasmDataSegmentMap)) with
    ⟨%dataSegmentName, Hsegments⟩
  letI tableMapG : GhostMapG (WasmHeapGF α) TableKey TableInst WasmTableMap := by
    constructor
    exists 10
  imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := TableKey)
      (V := TableInst) (H := WasmTableMap)) with ⟨%tableName, Htables⟩
  letI elementSegmentMapG :
      GhostMapG (WasmHeapGF α) ElementSegmentKey (Option (List (Option Nat)))
        WasmElementSegmentMap := by
    constructor
    exists 11
  imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := ElementSegmentKey)
      (V := Option (List (Option Nat))) (H := WasmElementSegmentMap)) with
    ⟨%elementSegmentName, HelementSegments⟩
  letI wasmHeapGS : WasmHeapGS α :=
    { togenHeapGS := heapGS }
  letI wasmGlobalGS : WasmGlobalGS α :=
    { toGhostMapG := globalMapG
      globalName := globalName }
  letI wasmDataSegmentGS : WasmDataSegmentGS α :=
    { toGhostMapG := dataSegmentMapG
      dataSegmentName := dataSegmentName }
  letI wasmTableGS : WasmTableGS α :=
    { toGhostMapG := tableMapG
      tableName := tableName }
  letI wasmElementSegmentGS : WasmElementSegmentGS α :=
    { toGhostMapG := elementSegmentMapG
      elementSegmentName := elementSegmentName }
  letI runtimeModuleMapG : GhostMapG (WasmHeapGF α) Nat Module WasmRuntimeModuleMap := by
    constructor
    exists 8
  imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := Nat)
      (V := Module) (H := WasmRuntimeModuleMap)) with ⟨%runtimeName, HruntimeModuleAuth⟩
  imod ghost_map_insert_persist (k := config.store.runtime.entry.id)
      (v := config.store.runtime.currentModule)
      (get?_empty config.store.runtime.entry.id) $$ HruntimeModuleAuth with
    ⟨HruntimeModuleAuth', HruntimeWP⟩
  iintuitionistic HruntimeWP
  rw [show insert (∅ : WasmRuntimeModuleMap Module)
      config.store.runtime.entry.id config.store.runtime.currentModule =
      PartialMap.singleton config.store.runtime.entry.id
      config.store.runtime.currentModule from rfl]
  letI runtimeGS : WasmRuntimeModuleGS α :=
    { toGhostMapG := runtimeModuleMapG
      runtimeName }
  letI hostEnvMapG : GhostMapG (WasmHeapGF α) Nat (HostEnv α) WasmHostEnvMap := by
    constructor
    exists 12
  imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := Nat)
      (V := HostEnv α) (H := WasmHostEnvMap)) with ⟨%hostEnvName, HhostEnvAuth⟩
  imod ghost_map_insert_persist (k := config.store.runtime.entry.id)
      (v := config.store.runtime.currentHost)
      (get?_empty config.store.runtime.entry.id) $$ HhostEnvAuth with
    ⟨HhostEnvAuth', HhostEnvWP⟩
  iintuitionistic HhostEnvWP
  rw [show insert (∅ : WasmHostEnvMap (HostEnv α))
      config.store.runtime.entry.id config.store.runtime.currentHost =
      PartialMap.singleton config.store.runtime.entry.id
      config.store.runtime.currentHost from rfl]
  letI hostEnvGS : WasmHostEnvGS α :=
    { toGhostMapG := hostEnvMapG
      hostEnvName }
  letI hostStateElem :
      ElemG (WasmHeapGF α)
        (Auth.AuthRF (OptionOF (Excl.ExclOF (constOF (DiscreteO α))))) := by
    exists 13
  imod (iOwn_alloc (E := hostStateElem)
      (ExclAuth.auth (⟨config.store.wasm.host⟩ : DiscreteO α) •
       ExclAuth.frag (⟨config.store.wasm.host⟩ : DiscreteO α))
      ExclAuth.valid) with
    ⟨%hostStateName, HhostStateAll⟩
  ihave HhostStatePair := iOwn_op.mp $$ HhostStateAll
  icases HhostStatePair with ⟨HhostState, HhostStateFrag⟩
  letI hostStateGS : WasmHostStateGS α :=
    { hostStateElem
      hostStateName }
  letI instanceElem :
      ElemG (WasmHeapGF α)
        (Auth.AuthRF (OptionOF (Excl.ExclOF (constOF (DiscreteO Nat))))) := by
    exists 14
  imod (iOwn_alloc (E := instanceElem)
      (ExclAuth.auth (⟨config.store.runtime.entry.id⟩ : DiscreteO Nat) •
       ExclAuth.frag (⟨config.store.runtime.entry.id⟩ : DiscreteO Nat))
      ExclAuth.valid) with
    ⟨%instanceName, HinstanceAll⟩
  ihave HinstancePair := iOwn_op.mp $$ HinstanceAll
  icases HinstancePair with ⟨HinstanceState, HinstanceFrag⟩
  letI instanceGS : WasmInstanceGS α :=
    { instanceElem
      instanceName }
  letI runtimeInstancesElem :
      ElemG (WasmHeapGF α) (constOF (Agree (DiscreteO (Array (ModuleInstance α))))) := by
    exists 15
  imod (iOwn_alloc (E := runtimeInstancesElem)
      (toAgree ⟨config.store.runtime.instances⟩) (fun _ => trivial)) with
    ⟨%runtimeInstancesName, HruntimeInstances⟩
  letI runtimeInstancesGS : WasmRuntimeInstancesGS α :=
    { runtimeInstancesElem
      runtimeInstancesName }
  letI exceptionMapG :
      GhostMapG (WasmHeapGF α) Nat (Nat × List Value) WasmExceptionMap := by
    constructor
    exists 16
  imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := Nat)
      (V := Nat × List Value) (H := WasmExceptionMap)) with
    ⟨%exceptionName, Hexceptions⟩
  letI wasmExceptionGS : WasmExceptionGS α :=
    { toGhostMapG := exceptionMapG
      exceptionName := exceptionName }
  letI tagTableElem : ElemG (WasmHeapGF α)
      (constOF (Agree (DiscreteO (List Nat)))) := by
    exists 17
  imod (iOwn_alloc (E := tagTableElem)
      (toAgree ⟨config.store.wasm.tagIds⟩) (fun _ => trivial)) with
    ⟨%tagTableName, HtagTable⟩
  letI tagTableGS : WasmTagTableGS α :=
    { tagTableElem
      tagTableName }
  letI gs : WasmSmallStepGS .hasNoLC α :=
    { toInvGS_gen := inv
      toWasmHeapGS := wasmHeapGS
      heapDomain := heapDomainGS
      memoryPages := memoryPagesGS
      global := wasmGlobalGS
      dataSegment := wasmDataSegmentGS
      table := wasmTableGS
      elementSegment := wasmElementSegmentGS
      exception := wasmExceptionGS
      tagTable := tagTableGS
      runtime := runtimeGS
      hostEnv := hostEnvGS
      hostState := hostStateGS
      instanceGS := instanceGS
      runtimeInstances := runtimeInstancesGS }
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
  ihave HexceptionInterp : exceptionInterp config.store.wasm.exns config.store.wasm.tagIds $$
      [Hexceptions HtagTable]
  · unfold exceptionInterp tagTableOwn
    isplitl [Hexceptions]
    · iexists (∅ : WasmExceptionMap (Nat × List Value))
      isplitl [Hexceptions]
      · iexact Hexceptions
      · ipureintro
        exact exceptionHeapAgrees_empty _
    · iexists config.store.wasm.tagIds
      isplitl [HtagTable]
      · iexact HtagTable
      · ipureintro
        exact List.prefix_rfl -- The ordinary frontier is installed below.
  ihave Hexc : machineAuxInterp _ config.store.wasm.mem.pages
      config.store.wasm.exns config.store.wasm.tagIds $$
      [HmemoryPagesAuth HheapDomain HexceptionInterp]
  · unfold machineAuxInterp
    iframe HmemoryPagesAuth HheapDomain HexceptionInterp
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
    ipureintro
    exact ⟨hagree, hinBounds, hglobals,
      dataSegmentHeapAgrees_empty _,
      tableHeapAgrees_empty _,
      elementSegmentHeapAgrees_empty _,
      fun id m hm => by
        by_cases h : id = config.store.runtime.entry.id
        · subst h; simp [PartialMap.singleton, get?_insert_eq rfl] at hm; subst hm
          rw [Array.getElem?_eq_getElem hwf]
          simp [RuntimeEnv.currentModule, RuntimeEnv.currentInstance]
          rw [getElem!_pos config.store.runtime.instances config.store.runtime.entry.id hwf]
        · simp [PartialMap.singleton, get?_insert_ne (Ne.symm h), get?_empty] at hm,
      fun id env hm => by
        by_cases h : id = config.store.runtime.entry.id
        · subst h; simp [PartialMap.singleton, get?_insert_eq rfl] at hm; subst hm
          rw [Array.getElem?_eq_getElem hwf, Option.map_some]
          simp [RuntimeEnv.currentHost, RuntimeEnv.currentInstance]
          rw [getElem!_pos config.store.runtime.instances
            config.store.runtime.entry.id hwf]
        · simp [PartialMap.singleton, get?_insert_ne (Ne.symm h),
            get?_empty] at hm⟩
  · iintro _
    iapply (twp.mono (fun _ => BI.true_intro))
    iapply htwp .hasNoLC
    isplitl [Hpoints]
    · iexact Hpoints
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
    iapply htwp hlc
    iexact Hresources
  · apply wasm_smallStep_heap_globals_runtime_host_store_adequacy_outcome
      config σ globalσ post hagree hinBounds hglobals hwf
    intro gs
    iintro Hresources
    iapply twp.to_wp
    iapply htwp .hasLC
    iexact Hresources

end Wasm.SmallStep
