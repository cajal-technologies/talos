import CodeLib.SepLogic.SmallStepLifting
import CodeLib.SepLogic.SmallStepTotalLifting
import CodeLib.SepLogic.SmallStepGhostInit
import Iris.ProgramLogic.Adequacy
import Iris.ProgramLogic.TotalAdequacy

/-!
# Adequacy for the Wasm small-step Iris language

This is the public bridge from an iris-lean `WP` proof to the operational
small-step semantics.  Unlike the legacy `wasm_heap_adequacy`, it refers only
to `Wasm.SmallStep.Step` through the iris-lean `Language` instance.
-/

/-! ### Compatibility layer for merged iris-lean#554

`StronglyNormalizing` moved upstream to `Relation.StronglyNormalizing`
(an abbrev for `Acc (flip step)`), and its helpers plus the no-fork
single-expression adequacy bridge were dropped when the PR merged.
Ported verbatim below. -/

namespace Relation.StronglyNormalizing

theorem intro {α : Type _} {step : α → α → Prop} {x : α}
    (H : ∀ y, step x y → Relation.StronglyNormalizing step y) :
    Relation.StronglyNormalizing step x :=
  Acc.intro x H

theorem map {α β : Type _} {stepα : α → α → Prop}
    {stepβ : β → β → Prop} (f : β → α)
    (Hlift : ∀ x y, stepβ x y → stepα (f x) (f y))
    {x : β} (H : Relation.StronglyNormalizing stepα (f x)) :
    Relation.StronglyNormalizing stepβ x := by
  unfold Relation.StronglyNormalizing at H ⊢
  generalize hx : f x = z at H
  induction H generalizing x with
  | intro z Hz IH =>
      subst z
      apply Acc.intro
      intro y Hy
      exact IH (f y) (Hlift x y Hy) rfl

end Relation.StronglyNormalizing

namespace Iris.ProgramLogic

export Relation (StronglyNormalizing)

section
open Iris Language Language.Notation

variable {Expr State Obs Val : Type _} [Λ : Language Expr State Obs Val]

/-- Erased single-expression reduction. -/
def ExprErasedStep : Expr × State → Expr × State → Prop
  | (e₁, σ₁), (e₂, σ₂) =>
      ∃ (κ : List Obs) (efs : List Expr), (e₁, σ₁) -<κ>-> (e₂, σ₂, efs)

/-- A language whose primitive steps do not fork. -/
class LanguageNoFork (Expr State Obs Val : Type _)
    [Language Expr State Obs Val] : Prop where
  no_fork {e₁ e₂ : Expr} {σ₁ σ₂ : State} {κ : List Obs} {efs : List Expr} :
    (e₁, σ₁) -<κ>-> (e₂, σ₂, efs) → efs = []

/-- Derive single-expression normalization from thread-pool normalization. -/
theorem stronglyNormalizing_expr_of_threadPool
    [LanguageNoFork Expr State Obs Val] {e : Expr} {σ : State}
    (H : StronglyNormalizing
      (Language.ErasedStep (Expr := Expr) (State := State) (Obs := Obs))
      ([e], σ)) :
    StronglyNormalizing
      (ExprErasedStep (Expr := Expr) (State := State) (Obs := Obs))
      (e, σ) := by
  apply Relation.StronglyNormalizing.map (fun ρ : Expr × State => ([ρ.1], ρ.2)) ?_ H
  rintro ⟨e₁, σ₁⟩ ⟨e₂, σ₂⟩ ⟨κ, efs, Hstep⟩
  have hefs : efs = [] := LanguageNoFork.no_fork Hstep
  subst efs
  exact ⟨κ, .atomic Hstep [] []⟩

end

end Iris.ProgramLogic

namespace Wasm.SmallStep

open Iris OFE COFE BI Iris.BI Iris.Algebra Iris.ProgramLogic
  Language.Notation Std FromMathlib LawfulSet
open Wasm.SepLogic

variable {α : Type}

/-- State-sensitive variant of iris-lean's convenience adequacy theorem.
`wp_adequacy` deliberately erases the final state from its postcondition. For
stateful Wasm specifications we instead let the WP post retain a continuation
that consumes the final state interpretation. Strong adequacy supplies that
interpretation at the reached value, allowing authoritative ghost ownership
to establish facts about the actual physical `MachineStore`. -/
theorem wp_store_adequacy
    {Expr State Obs Val GF}
    [Language Expr State Obs Val] [InvGpreS GF]
    (s : Stuckness) (e : Expr) (σ : State)
    (φ : Val → State → Prop)
    (Hwp : ∀ [InvGS_gen .hasLC GF] (κs : List Obs),
      ⊢ iprop(|={⊤}=>
        ∃ (stateI : State → List Obs → IProp GF)
          (forkPost : Val → IProp GF),
        letI _ : IrisGS_gen .hasLC Expr GF :=
          .mk (toStateInterp := ⟨fun σ _ κs _ => stateI σ κs⟩)
            (fun _ => 0) forkPost (fun _ _ _ _ => fupd_intro)
        iprop(stateI σ κs ∗
          WP e @ s; ⊤ {{
            value, ∀ (store : State) (observations : List Obs),
              stateI store observations -∗ ⌜φ value store⌝ }}))) :
    adequate s e σ φ := by
  refine (adequate_alt s e σ φ).mpr ?_
  intro t2 σ2 hreach
  obtain ⟨n, κs, hsteps⟩ := (Language.erasedStep_nSteps _ _).mp hreach
  apply wp_strong_adequacy_gen
    (GF := GF) (hlc := .hasLC) s (Hsteps := hsteps)
    (numLaters := fun _ => 0)
  iintro %Hinv
  imod Hwp κs with ⟨%Hst, %Hfork, ⟨Hst, Hwp⟩⟩
  iexists (fun store _ observations _ => Hst store observations),
    [(fun value => iprop%
      ∀ (store : State) (observations : List Obs),
        Hst store observations -∗ ⌜φ value store⌝)],
    Hfork, (fun _ _ _ _ => fupd_intro)
  dsimp only
  imodintro
  iframe
  isplitl [Hwp]
  · iapply_frame BigSepL2.bigSepL2_singleton
  iintro %_ %_ %Heq %_ %HNS Hstate Hwptp _
  iapply fupd_mask_intro_discard empty_subset
  icases BigSepL2.bigSepL2_cons_inv_right $$ Hwptp with
    ⟨%e', %_, %Heq', Hpost, Hrest⟩
  subst Heq' Heq
  dsimp only [List.cons_append, List.length_cons, Nat.pred_eq_sub_one,
    Nat.add_one_sub_one]
  icases BigSepL2.bigSepL2_nil_inv_right $$ Hrest with %Heq
  subst Heq
  cases hvalue : toVal e'
  · ipureintro
    grind
  · dsimp only [Option.elim_some]
    ihave %Hresult := Hpost $$ %σ2 %([] : List Obs) Hstate
    ipureintro
    grind

/-- Ghost resources required before allocating a concrete Wasm small-step
Iris instance. -/
class WasmSmallStepGpreS (α : Type) extends InvGpreS (WasmHeapGF α)

instance instWasmSmallStepGpreS :
    WasmSmallStepGpreS α where
  toWsatGpreS := by
    constructor
    · exists 0
    · exists 1
    · exists 2
  toLcGpreS := by
    constructor
    exists 3

/-- Lower iris-lean adequacy to Talos's public relational partial-correctness
predicate. This is the common operational bridge for generated-body proofs:
the Iris language has one expression and never forks, so a Talos `Steps` trace
is directly admissible as the adequacy execution. -/
theorem adequate_to_partiallyMeets
    (config : Config α)
    (post : List Value → MachineStore α → Prop)
    (had : adequate Stuckness.NotStuck config.expr config.store post) :
    PartiallyMeets config post := by
  intro trace values store steps
  apply had.adequate_result [] store values
  change ([config.expr], config.store) -·->ₜₚ*
    ([Expr.done values], store)
  exact steps.to_languageErasedSteps

/-- A closed iris-lean WP proof is adequate for the authoritative Wasm
small-step semantics.  The empty initial ghost heap is sufficient for closed
proofs that do not require caller-provided memory ownership; owned-memory
adequacy is layered on top by allocating the required physical footprint. -/
theorem wasm_smallStep_adequacy
    [WasmSmallStepGpreS α]
    (config : Config α) (φ : List Value → Prop)
    (hwp : ∀ [WasmSmallStepGS .hasLC α],
      ⊢@{IProp (WasmHeapGF α)}
        (WP config.expr @ Stuckness.NotStuck; ⊤ {{ values, ⌜φ values⌝ }})) :
    adequate Stuckness.NotStuck config.expr config.store
      (fun values _ => φ values) := by
  refine wp_adequacy (GF := WasmHeapGF α) Stuckness.NotStuck
    config.expr config.store φ ?_
  intro inv κs
  wasm_alloc_memory_ghosts config from (∅ : WasmHeapMap (Option UInt8))
  wasm_alloc_empty_heap_maps
  wasm_install_heap_map_instances
  wasm_alloc_empty_runtime_modules
  wasm_alloc_empty_host_envs
  wasm_alloc_host_state config
  iclear HhostStateFrag
  wasm_alloc_current_instance config
  iclear HinstanceFrag
  wasm_alloc_runtime_instances config
  wasm_alloc_exception_map
  wasm_alloc_tag_table config
  letI gs : WasmSmallStepGS .hasLC α := smallStepGS .hasLC inv
  iclear Hpoints Hmeta
  imodintro
  iexists (fun store _observations =>
    stateInterp (GF := WasmHeapGF α) store 0 [] 0)
  iexists (fun _ => iprop(True))
  dsimp only
  wasm_build_machine_aux config
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeInstances HinstanceState HhostEnvAuth HhostState Hexc]
  · iapply (stateInterp_eq config.store 0 [] 0).mpr
    iexists (∅ : WasmHeapMap (Option UInt8))
    iexists (∅ : WasmGlobalMap Value)
    iexists (∅ : WasmDataSegmentMap (Option (List UInt8)))
    iexists (∅ : WasmTableMap TableInst)
    iexists (∅ : WasmElementSegmentMap (Option (List (Option Nat))))
    iexists (∅ : WasmRuntimeModuleMap Module)
    iexists (∅ : WasmHostEnvMap (HostEnv α))
    unfold runtimeModuleElem runtimeInstancesOwn hostStateAuth currentInstanceAuth currentInstanceAuthN
    simp only [BI.BigSepM.bigSepM_empty.to_eq, BI.emp_sep.to_eq]
    iframe Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeInstances HinstanceState HhostEnvAuth HhostState Hexc
    ipureexact ⟨heapAgreesWithMem_empty _,
      heapAddressesInBounds_empty _,
      globalHeapAgrees_empty _,
      dataSegmentHeapAgrees_empty _,
      tableHeapAgrees_empty _,
      elementSegmentHeapAgrees_empty _,
      fun id m hm => by simp [get?_empty] at hm,
      fun id env hm => by simp [get?_empty] at hm⟩
  · exact hwp

/-- Public relational partial-correctness form of closed small-step adequacy.
This is the lightweight entry point for pure generated bodies that need no
caller-provided memory, global, or runtime ownership. -/
theorem wasm_smallStep_partiallyMeets
    [WasmSmallStepGpreS α]
    (config : Config α) (φ : List Value → Prop)
    (hwp : ∀ [WasmSmallStepGS .hasLC α],
      ⊢@{IProp (WasmHeapGF α)}
        (WP config.expr @ Stuckness.NotStuck; ⊤
          {{ values, ⌜φ values⌝ }})) :
    PartiallyMeets config (fun values _store => φ values) :=
  adequate_to_partiallyMeets config (fun values _store => φ values)
    (wasm_smallStep_adequacy config φ hwp)

/-- Start a closed partial-correctness proof and name its Iris instance. -/
macro "wasm_wp_partially_meets " gs:ident : tactic =>
  `(tactic|
    apply Wasm.SmallStep.wasm_smallStep_partiallyMeets <;>
      intro $gs:ident)

instance instWasmLanguageNoFork :
    LanguageNoFork (Expr α) (MachineStore α) StepKind (List Value) where
  no_fork h := h.1

/-- A closed total WP proof strongly normalizes the authoritative Wasm
single-thread machine. The ghost initialization is the total-WP counterpart
of `wasm_smallStep_adequacy`; both use the same `StateInterp`. -/
theorem wasm_smallStep_stronglyNormalizing
    [WasmSmallStepGpreS α]
    (config : Config α) (φ : List Value → Prop)
    (htwp : ∀ [WasmSmallStepGS .hasNoLC α],
      ⊢@{IProp (WasmHeapGF α)}
        (WP config.expr @ Stuckness.NotStuck; ⊤
          [{ values, ⌜φ values⌝ }])) :
    StronglyNormalizing
      (ExprErasedStep (Expr := Expr α)
        (State := MachineStore α) (Obs := StepKind))
      (config.expr, config.store) := by
  apply stronglyNormalizing_expr_of_threadPool
  apply twp_total (hlc := .hasNoLC) (GF := WasmHeapGF α)
    Stuckness.NotStuck config.expr config.store
    (fun values => iprop(⌜φ values⌝)) 0 0
  intro inv
  wasm_alloc_memory_ghosts config from (∅ : WasmHeapMap (Option UInt8))
  wasm_alloc_empty_heap_maps
  wasm_install_heap_map_instances
  wasm_alloc_empty_runtime_modules
  wasm_alloc_empty_host_envs
  wasm_alloc_host_state config
  iclear HhostStateFrag
  wasm_alloc_current_instance config
  iclear HinstanceFrag
  wasm_alloc_runtime_instances config
  wasm_alloc_exception_map
  wasm_alloc_tag_table config
  letI gs : WasmSmallStepGS .hasNoLC α := smallStepGS .hasNoLC inv
  iclear Hpoints Hmeta
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
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeInstances HinstanceState HhostEnvAuth HhostState Hexc]
  · iapply (stateInterp_eq config.store 0 [] 0).mpr
    iexists (∅ : WasmHeapMap (Option UInt8))
    iexists (∅ : WasmGlobalMap Value)
    iexists (∅ : WasmDataSegmentMap (Option (List UInt8)))
    iexists (∅ : WasmTableMap TableInst)
    iexists (∅ : WasmElementSegmentMap (Option (List (Option Nat))))
    iexists (∅ : WasmRuntimeModuleMap Module)
    iexists (∅ : WasmHostEnvMap (HostEnv α))
    unfold runtimeModuleElem runtimeInstancesOwn hostStateAuth currentInstanceAuth currentInstanceAuthN
    simp only [BI.BigSepM.bigSepM_empty.to_eq, BI.emp_sep.to_eq]
    iframe Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeInstances HinstanceState HhostEnvAuth HhostState Hexc
    ipureexact ⟨heapAgreesWithMem_empty _,
      heapAddressesInBounds_empty _,
      globalHeapAgrees_empty _,
      dataSegmentHeapAgrees_empty _,
      tableHeapAgrees_empty _,
      elementSegmentHeapAgrees_empty _,
      fun id m hm => by simp [get?_empty] at hm,
      fun id env hm => by simp [get?_empty] at hm⟩
  · iintro _
    exact htwp

/-- Total-WP strong normalization with authoritative initial memory, globals,
and runtime-module ownership. This is the termination counterpart of
`wasm_smallStep_heap_globals_runtime_store_adequacy`. -/
theorem wasm_smallStep_heap_globals_runtime_tags_stronglyNormalizing
    [WasmSmallStepGpreS α]
    (config : Config α)
    (σ : WasmHeapMap (Option UInt8))
    (globalσ : WasmGlobalMap Value)
    (Φ : List Value → IProp (WasmHeapGF α))
    (hagree : heapAgreesWithMem σ (storeResolve config.store))
    (hinBounds : heapAddressesInBounds σ (storeResolve config.store))
    (hglobals : globalHeapAgrees globalσ config.store.wasm.globals)
    (hwf : config.store.runtime.entry.id < config.store.runtime.instances.size)
    (htwp : ∀ [WasmSmallStepGS .hasNoLC α],
      (([∗map] address ↦ value ∈ σ,
          pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
            address (DFrac.own 1) value) ∗
        ([∗map] index ↦ value ∈ globalσ,
          globalPointsTo index value) ∗
        runtimeModuleOwn config.store.runtime.entry
          config.store.runtime.currentModule ∗
        tagTableOwn config.store.wasm.tagIds) ⊢
        WP config.expr @ Stuckness.NotStuck; ⊤
          [{ Φ }]) :
    StronglyNormalizing
      (ExprErasedStep (Expr := Expr α)
        (State := MachineStore α) (Obs := StepKind))
      (config.expr, config.store) := by
  apply stronglyNormalizing_expr_of_threadPool
  apply twp_total (hlc := .hasNoLC) (GF := WasmHeapGF α)
    Stuckness.NotStuck config.expr config.store
    Φ 0 0
  intro inv
  wasm_alloc_memory_ghosts config from σ
  wasm_alloc_globals_and_empty_heap_maps globalσ
  wasm_install_heap_map_instances
  wasm_alloc_current_runtime_module config
  wasm_alloc_empty_host_envs
  wasm_alloc_host_state config
  iclear HhostStateFrag
  wasm_alloc_current_instance config
  wasm_alloc_runtime_instances config
  wasm_alloc_exception_map
  wasm_alloc_tag_table config
  ihave HtagTableOwn : tagTableOwn config.store.wasm.tagIds $$ [HtagTable]
  · unfold tagTableOwn
    iexact HtagTable
  iintuitionistic HtagTableOwn
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
  ihave HexceptionInterp : exceptionInterp config.store.wasm.exns config.store.wasm.tagIds $$
      [Hexceptions]
  · unfold exceptionInterp
    isplitl [Hexceptions]
    · iexists (∅ : WasmExceptionMap (Nat × List Value))
      isplitl_exact Hexceptions
      · ipureexact exceptionHeapAgrees_empty _
    · iexists config.store.wasm.tagIds
      isplitl []
      · iexact HtagTableOwn
      · ipureexact List.prefix_rfl -- The ordinary frontier is installed below.
  ihave Hexc : machineAuxInterp _ config.store.wasm.mem.pages
      config.store.wasm.exns config.store.wasm.tagIds $$
      [HmemoryPagesAuth HheapDomain HexceptionInterp]
  · unfold machineAuxInterp
    iframe HmemoryPagesAuth HheapDomain HexceptionInterp
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth' HruntimeInstances HinstanceState HhostEnvAuth HhostState Hexc]
  · iapply (stateInterp_eq config.store 0 [] 0).mpr
    iexists σ
    iexists globalσ
    iexists (∅ : WasmDataSegmentMap (Option (List UInt8)))
    iexists (∅ : WasmTableMap TableInst)
    iexists (∅ : WasmElementSegmentMap (Option (List (Option Nat))))
    iexists (PartialMap.singleton config.store.runtime.entry.id
      config.store.runtime.currentModule)
    iexists (∅ : WasmHostEnvMap (HostEnv α))
    unfold runtimeModuleElem runtimeInstancesOwn hostStateAuth currentInstanceAuth currentInstanceAuthN
    simp only [BI.BigSepM.bigSepM_singleton.to_eq]
    iframe Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth' # HruntimeInstances HinstanceState HhostEnvAuth HhostState Hexc
    ipureexact ⟨hagree, hinBounds, hglobals,
      dataSegmentHeapAgrees_empty _,
      tableHeapAgrees_empty _,
      elementSegmentHeapAgrees_empty _,
      runtimeModuleSingletonAgrees config.store.runtime hwf,
      fun id env hm => by simp [get?_empty] at hm⟩
  · iintro _
    iapply htwp
    isplitl_exact Hpoints
    isplitl [HglobalPoints]
    · unfold globalPointsTo
      iexact HglobalPoints
    isplitl [HruntimeWP HinstanceFrag]
    · unfold runtimeModuleOwn
      isplitl [HruntimeWP]
      · unfold runtimeModuleElem; iexact HruntimeWP
      · unfold currentInstanceOwnN; iexact HinstanceFrag
    · iexact HtagTableOwn

/-- Tag-free specialization of
`wasm_smallStep_heap_globals_runtime_tags_stronglyNormalizing`. -/
theorem wasm_smallStep_heap_globals_runtime_stronglyNormalizing
    [WasmSmallStepGpreS α]
    (config : Config α)
    (σ : WasmHeapMap (Option UInt8))
    (globalσ : WasmGlobalMap Value)
    (Φ : List Value → IProp (WasmHeapGF α))
    (hagree : heapAgreesWithMem σ (storeResolve config.store))
    (hinBounds : heapAddressesInBounds σ (storeResolve config.store))
    (hglobals : globalHeapAgrees globalσ config.store.wasm.globals)
    (hwf : config.store.runtime.entry.id < config.store.runtime.instances.size)
    (htwp : ∀ [WasmSmallStepGS .hasNoLC α],
      (([∗map] address ↦ value ∈ σ,
          pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
            address (DFrac.own 1) value) ∗
        ([∗map] index ↦ value ∈ globalσ,
          globalPointsTo index value) ∗
        runtimeModuleOwn config.store.runtime.entry config.store.runtime.currentModule) ⊢
        WP config.expr @ Stuckness.NotStuck; ⊤
          [{ Φ }]) :
    StronglyNormalizing
      (ExprErasedStep (Expr := Expr α)
        (State := MachineStore α) (Obs := StepKind))
      (config.expr, config.store) := by
  apply wasm_smallStep_heap_globals_runtime_tags_stronglyNormalizing
    config σ globalσ Φ hagree hinBounds hglobals hwf
  intro gs
  iintro ⟨Hpoints, Hglobals, Hruntime, Htags⟩
  iclear Htags
  iapply htwp
  isplitl_exacts [Hpoints Hglobals]
  · iexact Hruntime

theorem stronglyNormalizing_reaches_irreducible
    {β : Type _} {step : β → β → Prop} {start : β}
    (hsn : StronglyNormalizing step start) :
    ∃ final,
      Relation.ReflTransGen step start final ∧
      ∀ next, ¬step final next := by
  unfold StronglyNormalizing at hsn
  refine Acc.recOn hsn
    (motive := fun current _ =>
      ∃ final,
        Relation.ReflTransGen step current final ∧
        ∀ next, ¬step final next) ?_
  intro current _ ih
  by_cases hnext : ∃ next, step current next
  · obtain ⟨next, hstep⟩ := hnext
    obtain ⟨final, hsteps, hirred⟩ := ih next hstep
    exact ⟨final,
      (Relation.ReflTransGen.single hstep).trans hsteps, hirred⟩
  · exact ⟨current, .refl, by
      intro next hstep
      exact hnext ⟨next, hstep⟩⟩

section terminalGeneric

variable {Terminal : Type} [view : TerminalView α Terminal]

local instance (priority := high) adequacyTerminalLanguage :
    Language (Expr α) (MachineStore α) StepKind Terminal :=
  TerminalView.canonicalLanguage

theorem exprErasedSteps_to_steps
    {source target : Expr α × MachineStore α}
    (hsteps : Relation.ReflTransGen
      (ExprErasedStep (Expr := Expr α)
        (State := MachineStore α) (Obs := StepKind))
      source target) :
    ∃ trace,
      Steps ⟨source.1, source.2⟩ trace ⟨target.1, target.2⟩ := by
  induction hsteps with
  | refl =>
    exact ⟨[], .refl _⟩
  | tail _ erasedStep ih =>
    obtain ⟨trace, hprefix⟩ := ih
    obtain ⟨κ, forks, hprim⟩ := erasedStep
    rcases hprim with ⟨hforks, kind, hκ, hstep⟩
    exact ⟨trace ++ [kind], hprefix.trans (.single hstep)⟩

end terminalGeneric

/-- Strong normalization plus ordinary Iris safety/partial correctness yields
Talos's finite-trace total-correctness predicate. -/
theorem stronglyNormalizing_adequate_terminates
    (config : Config α)
    (post : List Value → MachineStore α → Prop)
    (hsn : StronglyNormalizing
      (ExprErasedStep (Expr := Expr α)
        (State := MachineStore α) (Obs := StepKind))
      (config.expr, config.store))
    (had : adequate Stuckness.NotStuck config.expr config.store post) :
    TerminatesWith config post := by
  obtain ⟨⟨finalExpr, finalStore⟩, hreach, hirred⟩ :=
    stronglyNormalizing_reaches_irreducible hsn
  obtain ⟨trace, hsteps⟩ := exprErasedSteps_to_steps hreach
  have hirisReach := hsteps.to_languageErasedSteps
  have hnotStuck := had.adequate_not_stuck
    [finalExpr] finalStore finalExpr rfl hirisReach (by simp)
  rcases hnotStuck with hvalue | hreducible
  · cases hval : toVal finalExpr with
    | none =>
      simp [hval] at hvalue
    | some values =>
      have hexpr : finalExpr = (.done values : Expr α) :=
        (ToVal.coe_of_toVal_eq_some hval).symm
      subst finalExpr
      exact ⟨trace, values, finalStore, hsteps,
        had.adequate_result [] finalStore values hirisReach⟩
  · obtain ⟨κ, nextExpr, nextStore, forks, hprim⟩ := hreducible
    exact False.elim
      (hirred (nextExpr, nextStore) ⟨κ, forks, hprim⟩)

/-- Closed total-WP adequacy in Talos's public `TerminatesWith` form. TWP
supplies strong normalization; `twp.to_wp` supplies safety and the result
postcondition. -/
theorem wasm_smallStep_terminates
    [WasmSmallStepGpreS α]
    (config : Config α) (φ : List Value → Prop)
    (htwp : ∀ (hlc : HasLC) [WasmSmallStepGS hlc α],
      ⊢@{IProp (WasmHeapGF α)}
        (WP config.expr @ Stuckness.NotStuck; ⊤
          [{ values, ⌜φ values⌝ }])) :
    TerminatesWith config (fun values _store => φ values) := by
  apply stronglyNormalizing_adequate_terminates config
    (fun values _store => φ values)
    (wasm_smallStep_stronglyNormalizing config φ
      (htwp .hasNoLC))
  apply wasm_smallStep_adequacy config φ
  intro gs
  iapply twp.to_wp
  exact htwp .hasLC

/-- Closed adequacy with persistent knowledge of the concrete runtime module
*and* of the entry instance's tag-identity table.  This is the call-capable
counterpart of `wasm_smallStep_adequacy`, and the only entry point that hands
out `tagTableOwn`, which the exception rules need.  `tagTableOwn` is
persistent, so handing out the initial table costs the state interpretation
nothing. -/
theorem wasm_smallStep_runtime_tags_adequacy
    [WasmSmallStepGpreS α]
    (config : Config α) (φ : List Value → Prop)
    (hwf : config.store.runtime.entry.id < config.store.runtime.instances.size)
    (hwp : ∀ [WasmSmallStepGS .hasLC α],
      runtimeModuleOwn config.store.runtime.entry
        config.store.runtime.currentModule ∗
        tagTableOwn config.store.wasm.tagIds ⊢
        WP config.expr @ Stuckness.NotStuck; ⊤
          {{ values, ⌜φ values⌝ }}) :
    adequate Stuckness.NotStuck config.expr config.store
      (fun values _ => φ values) := by
  refine wp_adequacy (GF := WasmHeapGF α) Stuckness.NotStuck
    config.expr config.store φ ?_
  intro inv κs
  wasm_alloc_memory_ghosts config from (∅ : WasmHeapMap (Option UInt8))
  wasm_alloc_empty_heap_maps
  wasm_install_heap_map_instances
  wasm_alloc_current_runtime_module config
  wasm_alloc_empty_host_envs
  wasm_alloc_host_state config
  iclear HhostStateFrag
  wasm_alloc_current_instance config
  wasm_alloc_runtime_instances config
  wasm_alloc_exception_map
  wasm_alloc_tag_table config
  ihave HtagTableOwn : tagTableOwn config.store.wasm.tagIds $$ [HtagTable]
  · unfold tagTableOwn
    iexact HtagTable
  iintuitionistic HtagTableOwn
  letI gs : WasmSmallStepGS .hasLC α := smallStepGS .hasLC inv
  iclear Hpoints Hmeta
  imodintro
  iexists (fun store _observations =>
    stateInterp (GF := WasmHeapGF α) store 0 [] 0)
  iexists (fun _ => iprop(True))
  dsimp only
  ihave HexceptionInterp : exceptionInterp config.store.wasm.exns config.store.wasm.tagIds $$
      [Hexceptions]
  · unfold exceptionInterp
    isplitl [Hexceptions]
    · iexists (∅ : WasmExceptionMap (Nat × List Value))
      isplitl_exact Hexceptions
      · ipureexact exceptionHeapAgrees_empty _
    · iexists config.store.wasm.tagIds
      isplitl []
      · iexact HtagTableOwn
      · ipureexact List.prefix_rfl -- The ordinary frontier is installed below.
  ihave Hexc : machineAuxInterp _ config.store.wasm.mem.pages
      config.store.wasm.exns config.store.wasm.tagIds $$
      [HmemoryPagesAuth HheapDomain HexceptionInterp]
  · unfold machineAuxInterp
    iframe HmemoryPagesAuth HheapDomain HexceptionInterp
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth' HruntimeInstances HinstanceState HhostEnvAuth HhostState Hexc]
  · iapply (stateInterp_eq config.store 0 [] 0).mpr
    iexists (∅ : WasmHeapMap (Option UInt8))
    iexists (∅ : WasmGlobalMap Value)
    iexists (∅ : WasmDataSegmentMap (Option (List UInt8)))
    iexists (∅ : WasmTableMap TableInst)
    iexists (∅ : WasmElementSegmentMap (Option (List (Option Nat))))
    iexists (PartialMap.singleton config.store.runtime.entry.id
      config.store.runtime.currentModule)
    iexists (∅ : WasmHostEnvMap (HostEnv α))
    unfold runtimeModuleElem runtimeInstancesOwn hostStateAuth currentInstanceAuth currentInstanceAuthN
    simp only [BI.BigSepM.bigSepM_singleton.to_eq]
    iframe Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth' # HruntimeInstances HinstanceState HhostEnvAuth HhostState Hexc
    ipureexact ⟨heapAgreesWithMem_empty _,
      heapAddressesInBounds_empty _,
      globalHeapAgrees_empty _,
      dataSegmentHeapAgrees_empty _,
      tableHeapAgrees_empty _,
      elementSegmentHeapAgrees_empty _,
      runtimeModuleSingletonAgrees config.store.runtime hwf,
      fun id env hm => by simp [get?_empty] at hm⟩
  · iapply hwp
    isplitl [HruntimeWP HinstanceFrag]
    · unfold runtimeModuleOwn
      isplitl [HruntimeWP]
      · unfold runtimeModuleElem; iexact HruntimeWP
      · unfold currentInstanceOwnN; iexact HinstanceFrag
    · iexact HtagTableOwn

/-- Closed adequacy with persistent knowledge of the concrete runtime module.
This is the call-capable counterpart of `wasm_smallStep_adequacy`; it is the
tag-free specialization of `wasm_smallStep_runtime_tags_adequacy`. -/
theorem wasm_smallStep_runtime_adequacy
    [WasmSmallStepGpreS α]
    (config : Config α) (φ : List Value → Prop)
    (hwf : config.store.runtime.entry.id < config.store.runtime.instances.size)
    (hwp : ∀ [WasmSmallStepGS .hasLC α],
      runtimeModuleOwn config.store.runtime.entry
        config.store.runtime.currentModule ⊢
        WP config.expr @ Stuckness.NotStuck; ⊤
          {{ values, ⌜φ values⌝ }}) :
    adequate Stuckness.NotStuck config.expr config.store
      (fun values _ => φ values) := by
  apply wasm_smallStep_runtime_tags_adequacy config φ hwf
  intro gs
  iintro ⟨Hruntime, Htags⟩
  iclear Htags
  iapply hwp
  iexact Hruntime

/-- Relational partial-correctness form of call-capable runtime adequacy. -/
theorem wasm_smallStep_runtime_partiallyMeets
    [WasmSmallStepGpreS α]
    (config : Config α) (φ : List Value → Prop)
    (hwf : config.store.runtime.entry.id < config.store.runtime.instances.size)
    (hwp : ∀ [WasmSmallStepGS .hasLC α],
      runtimeModuleOwn config.store.runtime.entry
        config.store.runtime.currentModule ⊢
        WP config.expr @ Stuckness.NotStuck; ⊤
          {{ values, ⌜φ values⌝ }}) :
    PartiallyMeets config (fun values _store => φ values) :=
  adequate_to_partiallyMeets config (fun values _store => φ values)
    (wasm_smallStep_runtime_adequacy config φ hwf hwp)

/-- Call-capable runtime adequacy that also provides `currentInstanceOwn` to
the WP proof, enabling cross-instance call rules. -/
theorem wasm_smallStep_runtime_instance_adequacy
    [WasmSmallStepGpreS α]
    (config : Config α) (φ : List Value → Prop)
    (hwf : config.store.runtime.entry.id < config.store.runtime.instances.size)
    (hwp : ∀ [WasmSmallStepGS .hasLC α],
      runtimeModuleOwn config.store.runtime.entry
          config.store.runtime.currentModule ∗
        runtimeInstancesOwn config.store.runtime.instances ⊢
        WP config.expr @ Stuckness.NotStuck; ⊤
          {{ values, ⌜φ values⌝ }}) :
    adequate Stuckness.NotStuck config.expr config.store
      (fun values _ => φ values) := by
  refine wp_adequacy (GF := WasmHeapGF α) Stuckness.NotStuck
    config.expr config.store φ ?_
  intro inv κs
  wasm_alloc_memory_ghosts config from (∅ : WasmHeapMap (Option UInt8))
  wasm_alloc_empty_heap_maps
  wasm_install_heap_map_instances
  wasm_alloc_current_runtime_module config
  wasm_alloc_empty_host_envs
  wasm_alloc_host_state config
  iclear HhostStateFrag
  wasm_alloc_current_instance config
  letI runtimeInstancesElem :
      ElemG (WasmHeapGF α) (constOF (Agree (DiscreteO (Array (ModuleInstance α))))) :=
    GhostSlot.runtimeInstancesElem
  let runtimeInstancesValue : Agree (DiscreteO (Array (ModuleInstance α))) :=
    toAgree ⟨config.store.runtime.instances⟩
  imod (iOwn_alloc (E := runtimeInstancesElem)
      (runtimeInstancesValue • runtimeInstancesValue) (fun n =>
        CMRA.valid_iff_validN.mp
          (toAgree_op_valid_iff_eq.mpr rfl) n)) with
    ⟨%runtimeInstancesName, HruntimeInstances⟩
  letI runtimeInstancesGS : WasmRuntimeInstancesGS α :=
    { runtimeInstancesElem
      runtimeInstancesName }
  wasm_alloc_exception_map
  wasm_alloc_tag_table config
  letI gs : WasmSmallStepGS .hasLC α := smallStepGS .hasLC inv
  iclear Hpoints Hmeta
  ihave HruntimeInstancesPair := iOwn_op.mp $$ HruntimeInstances
  icases HruntimeInstancesPair with ⟨HruntimeInstancesState, HruntimeInstancesWP⟩
  imodintro
  iexists (fun store _observations =>
    stateInterp (GF := WasmHeapGF α) store 0 [] 0)
  iexists (fun _ => iprop(True))
  dsimp only
  wasm_build_machine_aux config
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth' HruntimeInstancesState HinstanceState HhostEnvAuth HhostState Hexc]
  · iapply (stateInterp_eq config.store 0 [] 0).mpr
    iexists (∅ : WasmHeapMap (Option UInt8))
    iexists (∅ : WasmGlobalMap Value)
    iexists (∅ : WasmDataSegmentMap (Option (List UInt8)))
    iexists (∅ : WasmTableMap TableInst)
    iexists (∅ : WasmElementSegmentMap (Option (List (Option Nat))))
    iexists (PartialMap.singleton config.store.runtime.entry.id
      config.store.runtime.currentModule)
    iexists (∅ : WasmHostEnvMap (HostEnv α))
    unfold runtimeModuleElem runtimeInstancesOwn hostStateAuth currentInstanceAuth currentInstanceAuthN
    simp only [BI.BigSepM.bigSepM_singleton.to_eq]
    iframe Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth' # HruntimeInstancesState HinstanceState HhostEnvAuth HhostState Hexc
    ipureexact ⟨heapAgreesWithMem_empty _,
      heapAddressesInBounds_empty _,
      globalHeapAgrees_empty _,
      dataSegmentHeapAgrees_empty _,
      tableHeapAgrees_empty _,
      elementSegmentHeapAgrees_empty _,
      runtimeModuleSingletonAgrees config.store.runtime hwf,
      fun id env hm => by simp [get?_empty] at hm⟩
  · iapply hwp
    isplitl [HruntimeWP HinstanceFrag]
    · unfold runtimeModuleOwn
      isplitl [HruntimeWP]
      · unfold runtimeModuleElem
        iexact HruntimeWP
      · unfold currentInstanceOwnN
        iexact HinstanceFrag
    · unfold runtimeInstancesOwn
      iexact HruntimeInstancesWP

/-- Partial-correctness form providing `runtimeModuleOwn` for user proofs. -/
theorem wasm_smallStep_runtime_instance_partiallyMeets
    [WasmSmallStepGpreS α]
    (config : Config α) (φ : List Value → Prop)
    (hwf : config.store.runtime.entry.id < config.store.runtime.instances.size)
    (hwp : ∀ [WasmSmallStepGS .hasLC α],
      runtimeModuleOwn config.store.runtime.entry
          config.store.runtime.currentModule ∗
        runtimeInstancesOwn config.store.runtime.instances ⊢
        WP config.expr @ Stuckness.NotStuck; ⊤
          {{ values, ⌜φ values⌝ }}) :
    PartiallyMeets config (fun values _store => φ values) :=
  adequate_to_partiallyMeets config (fun values _store => φ values)
    (wasm_smallStep_runtime_instance_adequacy config φ hwf hwp)

/-- Combined adequacy for cross-instance proofs that also track host state via
ExclAuth. Provides runtimeModuleOwn, hostEnvOwn, hostStateOwn, currentInstanceOwn,
and runtimeInstancesOwn to the WP proof. Use when a proof exercises both
`wp_callCrossInstance`/`wp_returnFromCallCrossInstance` and `wp_callHost`. -/
theorem wasm_smallStep_instance_host_state_adequacy
    [WasmSmallStepGpreS α]
    (config : Config α) (φ : List Value → Prop)
    (hwf : config.store.runtime.entry.id < config.store.runtime.instances.size)
    (hwp : ∀ [WasmSmallStepGS .hasLC α],
      runtimeModuleOwn config.store.runtime.entry
          config.store.runtime.currentModule ∗
        hostEnvOwn config.store.runtime.entry.id config.store.runtime.currentHost ∗
        hostStateOwn config.store.wasm.host ∗
        runtimeInstancesOwn config.store.runtime.instances ⊢
        WP config.expr @ Stuckness.NotStuck; ⊤
          {{ values, ⌜φ values⌝ }}) :
    adequate Stuckness.NotStuck config.expr config.store
      (fun values _ => φ values) := by
  refine wp_adequacy (GF := WasmHeapGF α) Stuckness.NotStuck
    config.expr config.store φ ?_
  intro inv κs
  wasm_alloc_memory_ghosts config from (∅ : WasmHeapMap (Option UInt8))
  wasm_alloc_empty_heap_maps
  wasm_install_heap_map_instances
  wasm_alloc_current_runtime_module config
  wasm_alloc_current_host_env config
  wasm_alloc_host_state config
  wasm_alloc_current_instance config
  letI runtimeInstancesElem :
      ElemG (WasmHeapGF α) (constOF (Agree (DiscreteO (Array (ModuleInstance α))))) :=
    GhostSlot.runtimeInstancesElem
  let runtimeInstancesValue : Agree (DiscreteO (Array (ModuleInstance α))) :=
    toAgree ⟨config.store.runtime.instances⟩
  imod (iOwn_alloc (E := runtimeInstancesElem)
      (runtimeInstancesValue • runtimeInstancesValue) (fun n =>
        CMRA.valid_iff_validN.mp
          (toAgree_op_valid_iff_eq.mpr rfl) n)) with
    ⟨%runtimeInstancesName, HruntimeInstances⟩
  letI runtimeInstancesGS : WasmRuntimeInstancesGS α :=
    { runtimeInstancesElem
      runtimeInstancesName }
  wasm_alloc_exception_map
  wasm_alloc_tag_table config
  letI gs : WasmSmallStepGS .hasLC α := smallStepGS .hasLC inv
  iclear Hpoints Hmeta
  ihave HruntimeInstancesPair := iOwn_op.mp $$ HruntimeInstances
  icases HruntimeInstancesPair with ⟨HruntimeInstancesState, HruntimeInstancesWP⟩
  imodintro
  iexists (fun store _observations =>
    stateInterp (GF := WasmHeapGF α) store 0 [] 0)
  iexists (fun _ => iprop(True))
  dsimp only
  wasm_build_machine_aux config
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth' HruntimeInstancesState HinstanceState HhostEnvAuth' HhostState Hexc]
  · iapply (stateInterp_eq config.store 0 [] 0).mpr
    iexists (∅ : WasmHeapMap (Option UInt8))
    iexists (∅ : WasmGlobalMap Value)
    iexists (∅ : WasmDataSegmentMap (Option (List UInt8)))
    iexists (∅ : WasmTableMap TableInst)
    iexists (∅ : WasmElementSegmentMap (Option (List (Option Nat))))
    iexists (PartialMap.singleton config.store.runtime.entry.id
      config.store.runtime.currentModule)
    iexists (PartialMap.singleton config.store.runtime.entry.id
      config.store.runtime.currentHost)
    unfold runtimeModuleElem runtimeInstancesOwn hostStateAuth currentInstanceAuth currentInstanceAuthN
    simp only [BI.BigSepM.bigSepM_singleton.to_eq]
    iframe Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth' # HruntimeInstancesState HinstanceState HhostEnvAuth' HhostState Hexc
    ipureexact ⟨heapAgreesWithMem_empty _,
      heapAddressesInBounds_empty _,
      globalHeapAgrees_empty _,
      dataSegmentHeapAgrees_empty _,
      tableHeapAgrees_empty _,
      elementSegmentHeapAgrees_empty _,
      runtimeModuleSingletonAgrees config.store.runtime hwf,
      hostEnvSingletonAgrees config.store.runtime hwf⟩
  · iapply hwp
    isplitl [HruntimeWP HinstanceFrag]
    · unfold runtimeModuleOwn
      isplitl [HruntimeWP]
      · unfold runtimeModuleElem; iexact HruntimeWP
      · unfold currentInstanceOwnN; iexact HinstanceFrag
    · isplitl [HhostEnvWP]
      · unfold hostEnvOwn; iexact HhostEnvWP
      · isplitl [HhostStateFrag]
        · unfold hostStateOwn; iexact HhostStateFrag
        · unfold runtimeInstancesOwn; iexact HruntimeInstancesWP

theorem wasm_smallStep_instance_host_state_partiallyMeets
    [WasmSmallStepGpreS α]
    (config : Config α) (φ : List Value → Prop)
    (hwf : config.store.runtime.entry.id < config.store.runtime.instances.size)
    (hwp : ∀ [WasmSmallStepGS .hasLC α],
      runtimeModuleOwn config.store.runtime.entry
          config.store.runtime.currentModule ∗
        hostEnvOwn config.store.runtime.entry.id config.store.runtime.currentHost ∗
        hostStateOwn config.store.wasm.host ∗
        runtimeInstancesOwn config.store.runtime.instances ⊢
        WP config.expr @ Stuckness.NotStuck; ⊤
          {{ values, ⌜φ values⌝ }}) :
    PartiallyMeets config (fun values _store => φ values) :=
  adequate_to_partiallyMeets config (fun values _store => φ values)
    (wasm_smallStep_instance_host_state_adequacy config φ hwf hwp)

/-- Adequacy with an explicit authoritative byte footprint. `genHeap_init`
allocates both the authoritative map used by `StateInterp` and the matching
per-byte ownership consumed by the WP proof. -/
theorem wasm_smallStep_heap_adequacy
    [WasmSmallStepGpreS α]
    (config : Config α) (σ : WasmHeapMap (Option UInt8))
    (φ : List Value → Prop)
    (hagree : heapAgreesWithMem σ (storeResolve config.store))
    (hinBounds : heapAddressesInBounds σ (storeResolve config.store))
    (hwp : ∀ [WasmSmallStepGS .hasLC α],
      ([∗map] address ↦ value ∈ σ,
        pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
          address (DFrac.own 1) value) ⊢
        WP config.expr @ Stuckness.NotStuck; ⊤
          {{ values, ⌜φ values⌝ }}) :
    adequate Stuckness.NotStuck config.expr config.store
      (fun values _ => φ values) := by
  refine wp_adequacy (GF := WasmHeapGF α) Stuckness.NotStuck
    config.expr config.store φ ?_
  intro inv κs
  wasm_alloc_memory_ghosts config from σ
  wasm_alloc_empty_heap_maps
  wasm_install_heap_map_instances
  wasm_alloc_empty_runtime_modules
  wasm_alloc_empty_host_envs
  wasm_alloc_host_state config
  iclear HhostStateFrag
  wasm_alloc_current_instance config
  iclear HinstanceFrag
  wasm_alloc_runtime_instances config
  wasm_alloc_exception_map
  wasm_alloc_tag_table config
  letI gs : WasmSmallStepGS .hasLC α := smallStepGS .hasLC inv
  iclear Hmeta
  imodintro
  iexists (fun store _observations =>
    stateInterp (GF := WasmHeapGF α) store 0 [] 0)
  iexists (fun _ => iprop(True))
  dsimp only
  wasm_build_machine_aux config
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeInstances HinstanceState HhostEnvAuth HhostState Hexc]
  · iapply (stateInterp_eq config.store 0 [] 0).mpr
    iexists σ
    iexists (∅ : WasmGlobalMap Value)
    iexists (∅ : WasmDataSegmentMap (Option (List UInt8)))
    iexists (∅ : WasmTableMap TableInst)
    iexists (∅ : WasmElementSegmentMap (Option (List (Option Nat))))
    iexists (∅ : WasmRuntimeModuleMap Module)
    iexists (∅ : WasmHostEnvMap (HostEnv α))
    unfold runtimeModuleElem runtimeInstancesOwn hostStateAuth currentInstanceAuth currentInstanceAuthN
    simp only [BI.BigSepM.bigSepM_empty.to_eq, BI.emp_sep.to_eq]
    iframe Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeInstances HinstanceState HhostEnvAuth HhostState Hexc
    ipureexact ⟨hagree, hinBounds,
      globalHeapAgrees_empty _,
      dataSegmentHeapAgrees_empty _,
      tableHeapAgrees_empty _,
      elementSegmentHeapAgrees_empty _,
      fun id m hm => by simp [get?_empty] at hm,
      fun id env hm => by simp [get?_empty] at hm⟩
  · iapply hwp
    iexact Hpoints

/-- Adequacy with authoritative ownership for both physical memory bytes and
instantiated globals. This is the entry point used by generated functions
whose behavior depends on `global.get`; it prevents a proof from assuming a
global value unrelated to the concrete machine store. -/
theorem wasm_smallStep_heap_globals_runtime_adequacy
    [WasmSmallStepGpreS α]
    (config : Config α)
    (σ : WasmHeapMap (Option UInt8))
    (globalσ : WasmGlobalMap Value)
    (φ : List Value → Prop)
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
          config.store.runtime.currentModule) ⊢
        WP config.expr @ Stuckness.NotStuck; ⊤
          {{ values, ⌜φ values⌝ }}) :
    adequate Stuckness.NotStuck config.expr config.store
      (fun values _ => φ values) := by
  refine wp_adequacy (GF := WasmHeapGF α) Stuckness.NotStuck
    config.expr config.store φ ?_
  intro inv κs
  wasm_alloc_memory_ghosts config from σ
  wasm_alloc_globals_and_empty_heap_maps globalσ
  wasm_install_heap_map_instances
  wasm_alloc_current_runtime_module config
  wasm_alloc_empty_host_envs
  wasm_alloc_host_state config
  iclear HhostStateFrag
  wasm_alloc_current_instance config
  wasm_alloc_runtime_instances config
  wasm_alloc_exception_map
  wasm_alloc_tag_table config
  letI gs : WasmSmallStepGS .hasLC α := smallStepGS .hasLC inv
  iclear Hmeta
  imodintro
  iexists (fun store _observations =>
    stateInterp (GF := WasmHeapGF α) store 0 [] 0)
  iexists (fun _ => iprop(True))
  dsimp only
  wasm_build_machine_aux config
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth' HruntimeInstances HinstanceState HhostEnvAuth HhostState Hexc]
  · iapply (stateInterp_eq config.store 0 [] 0).mpr
    iexists σ
    iexists globalσ
    iexists (∅ : WasmDataSegmentMap (Option (List UInt8)))
    iexists (∅ : WasmTableMap TableInst)
    iexists (∅ : WasmElementSegmentMap (Option (List (Option Nat))))
    iexists (PartialMap.singleton config.store.runtime.entry.id
      config.store.runtime.currentModule)
    iexists (∅ : WasmHostEnvMap (HostEnv α))
    unfold runtimeModuleElem runtimeInstancesOwn hostStateAuth currentInstanceAuth currentInstanceAuthN
    simp only [BI.BigSepM.bigSepM_singleton.to_eq]
    iframe Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth' # HruntimeInstances HinstanceState HhostEnvAuth HhostState Hexc
    ipureexact ⟨hagree, hinBounds, hglobals,
      dataSegmentHeapAgrees_empty _,
      tableHeapAgrees_empty _,
      elementSegmentHeapAgrees_empty _,
      runtimeModuleSingletonAgrees config.store.runtime hwf,
      fun id env hm => by simp [get?_empty] at hm⟩
  · iapply hwp
    isplitl_exact Hpoints
    · isplitl [HglobalPoints]
      · unfold globalPointsTo
        iexact HglobalPoints
      · unfold runtimeModuleOwn
        isplitl [HruntimeWP]
        · unfold runtimeModuleElem; iexact HruntimeWP
        · unfold currentInstanceOwnN; iexact HinstanceFrag

/-- State-sensitive authoritative adequacy. Unlike the value-only convenience
wrapper above, the WP post receives the final physical state interpretation
and may use its returned byte/global ownership to prove a predicate about the
actual reached `MachineStore`. -/
theorem wasm_smallStep_heap_globals_runtime_store_adequacy
    [WasmSmallStepGpreS α]
    (config : Config α)
    (σ : WasmHeapMap (Option UInt8))
    (globalσ : WasmGlobalMap Value)
    (post : List Value → MachineStore α → Prop)
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
        hostEnvOwn config.store.runtime.entry.id config.store.runtime.currentHost) ⊢
        WP config.expr @ Stuckness.NotStuck; ⊤
          {{ values,
            ∀ (store : MachineStore α) (_observations : List StepKind),
              stateInterp (GF := WasmHeapGF α) store 0 [] 0 -∗
              ⌜post values store⌝ }}) :
    adequate Stuckness.NotStuck config.expr config.store post := by
  refine wp_store_adequacy
    (GF := WasmHeapGF α) Stuckness.NotStuck
    config.expr config.store post ?_
  intro inv κs
  wasm_alloc_memory_ghosts config from σ
  wasm_alloc_globals_and_empty_heap_maps globalσ
  wasm_install_heap_map_instances
  wasm_alloc_current_runtime_module config
  wasm_alloc_current_host_env config
  wasm_alloc_host_state config
  iclear HhostStateFrag
  wasm_alloc_current_instance config
  wasm_alloc_runtime_instances config
  wasm_alloc_exception_map
  wasm_alloc_tag_table config
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
        · unfold hostEnvOwn
          iexact HhostEnvWP

/-- Total-WP adequacy for programs that own heap memory and globals in Talos's
`TerminatesWith` form. TWP supplies strong normalization; `twp.to_wp` supplies
safety and the result postcondition. -/
theorem wasm_smallStep_heap_globals_runtime_store_terminates
    [WasmSmallStepGpreS α]
    (config : Config α)
    (σ : WasmHeapMap (Option UInt8))
    (globalσ : WasmGlobalMap Value)
    (post : List Value → MachineStore α → Prop)
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
            config.store.runtime.currentModule) ⊢
        WP config.expr @ Stuckness.NotStuck; ⊤
          [{ values,
            ∀ (store : MachineStore α) (_observations : List StepKind),
              stateInterp (GF := WasmHeapGF α) store 0 [] 0 -∗
              ⌜post values store⌝ }]) :
    TerminatesWith config post := by
  apply stronglyNormalizing_adequate_terminates config post
  · apply stronglyNormalizing_expr_of_threadPool
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
    letI globalMapG : GhostMapG (WasmHeapGF α) GlobalKey Value WasmGlobalMap :=
      GhostSlot.globalMap
    imod (ghost_map_alloc (GF := WasmHeapGF α) (K := GlobalKey)
        (V := Value) (H := WasmGlobalMap) globalσ) with
      ⟨%globalName, Hglobals, HglobalPoints⟩
    letI dataSegmentMapG :
        GhostMapG (WasmHeapGF α) DataSegmentKey (Option (List UInt8))
          WasmDataSegmentMap :=
      GhostSlot.dataSegmentMap
    imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := DataSegmentKey)
        (V := Option (List UInt8)) (H := WasmDataSegmentMap)) with
      ⟨%dataSegmentName, Hsegments⟩
    letI tableMapG : GhostMapG (WasmHeapGF α) TableKey TableInst WasmTableMap :=
      GhostSlot.tableMap
    imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := TableKey)
        (V := TableInst) (H := WasmTableMap)) with ⟨%tableName, Htables⟩
    letI elementSegmentMapG :
        GhostMapG (WasmHeapGF α) ElementSegmentKey (Option (List (Option Nat)))
          WasmElementSegmentMap :=
      GhostSlot.elementSegmentMap
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
    letI runtimeModuleMapG : GhostMapG (WasmHeapGF α) Nat Module WasmRuntimeModuleMap :=
      GhostSlot.runtimeModuleMap
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
    letI hostEnvMapG : GhostMapG (WasmHeapGF α) Nat (HostEnv α) WasmHostEnvMap :=
      GhostSlot.hostEnvMap
    imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := Nat)
        (V := HostEnv α) (H := WasmHostEnvMap)) with ⟨%hostEnvName, HhostEnvAuth⟩
    letI hostEnvGS : WasmHostEnvGS α :=
      { toGhostMapG := hostEnvMapG
        hostEnvName }
    letI hostStateElem :
        ElemG (WasmHeapGF α)
          (Auth.AuthRF (OptionOF (Excl.ExclOF (constOF (DiscreteO α))))) :=
      GhostSlot.hostStateElem
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
    iclear HhostStateFrag
    letI instanceElem :
        ElemG (WasmHeapGF α)
          (Auth.AuthRF (OptionOF (Excl.ExclOF (constOF (DiscreteO Nat))))) :=
      GhostSlot.instanceElem
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
        ElemG (WasmHeapGF α) (constOF (Agree (DiscreteO (Array (ModuleInstance α))))) :=
      GhostSlot.runtimeInstancesElem
    imod (iOwn_alloc (E := runtimeInstancesElem)
        (toAgree ⟨config.store.runtime.instances⟩) (fun _ => trivial)) with
      ⟨%runtimeInstancesName, HruntimeInstances⟩
    letI runtimeInstancesGS : WasmRuntimeInstancesGS α :=
      { runtimeInstancesElem
        runtimeInstancesName }
    letI exceptionMapG :
        GhostMapG (WasmHeapGF α) Nat (Nat × List Value) WasmExceptionMap :=
      GhostSlot.exceptionMap
    imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := Nat)
        (V := Nat × List Value) (H := WasmExceptionMap)) with
      ⟨%exceptionName, Hexceptions⟩
    letI wasmExceptionGS : WasmExceptionGS α :=
      { toGhostMapG := exceptionMapG
        exceptionName := exceptionName }
    letI tagTableElem : ElemG (WasmHeapGF α)
        (constOF (Agree (DiscreteO (List Nat)))) :=
      GhostSlot.tagTableElem
    imod (iOwn_alloc (E := tagTableElem)
        (toAgree ⟨config.store.wasm.tagIds⟩) (fun _ => trivial)) with
      ⟨%tagTableName, HtagTable⟩
    letI tagTableGS : WasmTagTableGS α :=
      { tagTableElem
        tagTableName }
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
    isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth' HruntimeInstances HinstanceState HhostEnvAuth HhostState Hexc]
    · iapply (stateInterp_eq config.store 0 [] 0).mpr
      iexists σ
      iexists globalσ
      iexists (∅ : WasmDataSegmentMap (Option (List UInt8)))
      iexists (∅ : WasmTableMap TableInst)
      iexists (∅ : WasmElementSegmentMap (Option (List (Option Nat))))
      iexists (PartialMap.singleton config.store.runtime.entry.id
        config.store.runtime.currentModule)
      iexists (∅ : WasmHostEnvMap (HostEnv α))
      unfold runtimeModuleElem runtimeInstancesOwn hostStateAuth currentInstanceAuth currentInstanceAuthN
      simp only [BI.BigSepM.bigSepM_singleton.to_eq]
      iframe Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth' # HruntimeInstances HinstanceState HhostEnvAuth HhostState Hexc
      ipureexact ⟨hagree, hinBounds, hglobals,
        dataSegmentHeapAgrees_empty _,
        tableHeapAgrees_empty _,
        elementSegmentHeapAgrees_empty _,
        runtimeModuleSingletonAgrees config.store.runtime hwf,
        fun id env hm => by simp [get?_empty] at hm⟩
    · iintro _
      iapply (twp.mono (fun _ => BI.true_intro))
      iapply htwp .hasNoLC
      isplitl_exact Hpoints
      · isplitl [HglobalPoints]
        · unfold globalPointsTo
          iexact HglobalPoints
        · unfold runtimeModuleOwn
          isplitl [HruntimeWP]
          · unfold runtimeModuleElem; iexact HruntimeWP
          · unfold currentInstanceOwnN; iexact HinstanceFrag
  · apply wasm_smallStep_heap_globals_runtime_store_adequacy config σ globalσ post
      hagree hinBounds hglobals hwf
    intro gs
    iintro ⟨Hpoints, Hglobals, HruntimeModule, _HhostEnv⟩
    iapply twp.to_wp
    iapply htwp .hasLC
    isplitl_exact Hpoints
    · isplitl_exact Hglobals
      · iexact HruntimeModule

/-- Relational partial-correctness form of state-sensitive authoritative
adequacy. -/
theorem wasm_smallStep_heap_globals_runtime_store_partiallyMeets
    [WasmSmallStepGpreS α]
    (config : Config α)
    (σ : WasmHeapMap (Option UInt8))
    (globalσ : WasmGlobalMap Value)
    (post : List Value → MachineStore α → Prop)
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
        hostEnvOwn config.store.runtime.entry.id config.store.runtime.currentHost) ⊢
        WP config.expr @ Stuckness.NotStuck; ⊤
          {{ values,
            ∀ (store : MachineStore α) (_observations : List StepKind),
              stateInterp (GF := WasmHeapGF α) store 0 [] 0 -∗
              ⌜post values store⌝ }}) :
    PartiallyMeets config post :=
  adequate_to_partiallyMeets config post
    (wasm_smallStep_heap_globals_runtime_store_adequacy
      config σ globalσ post hagree hinBounds hglobals hwf hwp)

/-- Heap-aware store-sensitive total-WP adequacy. The TWP post must include
`stateInterp -∗ ⌜post values store⌝` so adequacy can read the physical store;
this matches `wasm_smallStep_heap_globals_runtime_store_adequacy`'s WP shape
exactly, so no `wp_mono` wrapper is needed. -/
theorem wasm_smallStep_heap_store_terminates
    [WasmSmallStepGpreS α]
    (config : Config α)
    (σ : WasmHeapMap (Option UInt8))
    (post : List Value → MachineStore α → Prop)
    (hagree : heapAgreesWithMem σ (storeResolve config.store))
    (hinBounds : heapAddressesInBounds σ (storeResolve config.store))
    (hwf : config.store.runtime.entry.id < config.store.runtime.instances.size)
    (htwp : ∀ (hlc : HasLC) [WasmSmallStepGS hlc α],
      (([∗map] address ↦ value ∈ σ,
          pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
            address (DFrac.own 1) value) ∗
        runtimeModuleOwn config.store.runtime.entry config.store.runtime.currentModule) ⊢
        WP config.expr @ Stuckness.NotStuck; ⊤
          [{ values,
            ∀ (store : MachineStore α) (_observations : List StepKind),
              stateInterp (GF := WasmHeapGF α) store 0 [] 0 -∗
              ⌜post values store⌝ }]) :
    TerminatesWith config post := by
  apply stronglyNormalizing_adequate_terminates config post
  · apply stronglyNormalizing_expr_of_threadPool
    apply twp_total (hlc := .hasNoLC) (GF := WasmHeapGF α)
      Stuckness.NotStuck config.expr config.store
      (fun values => iprop(True)) 0 0
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
    letI globalMapG : GhostMapG (WasmHeapGF α) GlobalKey Value WasmGlobalMap :=
      GhostSlot.globalMap
    imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := GlobalKey)
        (V := Value) (H := WasmGlobalMap)) with ⟨%globalName, Hglobals⟩
    letI dataSegmentMapG :
        GhostMapG (WasmHeapGF α) DataSegmentKey (Option (List UInt8))
          WasmDataSegmentMap :=
      GhostSlot.dataSegmentMap
    imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := DataSegmentKey)
        (V := Option (List UInt8)) (H := WasmDataSegmentMap)) with
      ⟨%dataSegmentName, Hsegments⟩
    letI tableMapG : GhostMapG (WasmHeapGF α) TableKey TableInst WasmTableMap :=
      GhostSlot.tableMap
    imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := TableKey)
        (V := TableInst) (H := WasmTableMap)) with ⟨%tableName, Htables⟩
    letI elementSegmentMapG :
        GhostMapG (WasmHeapGF α) ElementSegmentKey (Option (List (Option Nat)))
          WasmElementSegmentMap :=
      GhostSlot.elementSegmentMap
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
    letI runtimeModuleMapG : GhostMapG (WasmHeapGF α) Nat Module WasmRuntimeModuleMap :=
      GhostSlot.runtimeModuleMap
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
    letI hostEnvMapG : GhostMapG (WasmHeapGF α) Nat (HostEnv α) WasmHostEnvMap :=
      GhostSlot.hostEnvMap
    imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := Nat)
        (V := HostEnv α) (H := WasmHostEnvMap)) with ⟨%hostEnvName, HhostEnvAuth⟩
    letI hostEnvGS : WasmHostEnvGS α :=
      { toGhostMapG := hostEnvMapG
        hostEnvName }
    letI hostStateElem :
        ElemG (WasmHeapGF α)
          (Auth.AuthRF (OptionOF (Excl.ExclOF (constOF (DiscreteO α))))) :=
      GhostSlot.hostStateElem
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
    iclear HhostStateFrag
    letI instanceElem :
        ElemG (WasmHeapGF α)
          (Auth.AuthRF (OptionOF (Excl.ExclOF (constOF (DiscreteO Nat))))) :=
      GhostSlot.instanceElem
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
        ElemG (WasmHeapGF α) (constOF (Agree (DiscreteO (Array (ModuleInstance α))))) :=
      GhostSlot.runtimeInstancesElem
    imod (iOwn_alloc (E := runtimeInstancesElem)
        (toAgree ⟨config.store.runtime.instances⟩) (fun _ => trivial)) with
      ⟨%runtimeInstancesName, HruntimeInstances⟩
    letI runtimeInstancesGS : WasmRuntimeInstancesGS α :=
      { runtimeInstancesElem
        runtimeInstancesName }
    letI exceptionMapG :
        GhostMapG (WasmHeapGF α) Nat (Nat × List Value) WasmExceptionMap :=
      GhostSlot.exceptionMap
    imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := Nat)
        (V := Nat × List Value) (H := WasmExceptionMap)) with
      ⟨%exceptionName, Hexceptions⟩
    letI wasmExceptionGS : WasmExceptionGS α :=
      { toGhostMapG := exceptionMapG
        exceptionName := exceptionName }
    letI tagTableElem : ElemG (WasmHeapGF α)
        (constOF (Agree (DiscreteO (List Nat)))) :=
      GhostSlot.tagTableElem
    imod (iOwn_alloc (E := tagTableElem)
        (toAgree ⟨config.store.wasm.tagIds⟩) (fun _ => trivial)) with
      ⟨%tagTableName, HtagTable⟩
    letI tagTableGS : WasmTagTableGS α :=
      { tagTableElem
        tagTableName }
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
    isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth' HruntimeInstances HinstanceState HhostEnvAuth HhostState Hexc]
    · iapply (stateInterp_eq config.store 0 [] 0).mpr
      iexists σ
      iexists (∅ : WasmGlobalMap Value)
      iexists (∅ : WasmDataSegmentMap (Option (List UInt8)))
      iexists (∅ : WasmTableMap TableInst)
      iexists (∅ : WasmElementSegmentMap (Option (List (Option Nat))))
      iexists (PartialMap.singleton config.store.runtime.entry.id
        config.store.runtime.currentModule)
      iexists (∅ : WasmHostEnvMap (HostEnv α))
      unfold runtimeModuleElem runtimeInstancesOwn hostStateAuth currentInstanceAuth currentInstanceAuthN
      simp only [BI.BigSepM.bigSepM_singleton.to_eq]
      iframe Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth' # HruntimeInstances HinstanceState HhostEnvAuth HhostState Hexc
      ipureexact ⟨hagree, hinBounds, globalHeapAgrees_empty _,
        dataSegmentHeapAgrees_empty _,
        tableHeapAgrees_empty _,
        elementSegmentHeapAgrees_empty _,
        runtimeModuleSingletonAgrees config.store.runtime hwf,
        fun id env hm => by simp [get?_empty] at hm⟩
    · iintro _
      iapply (twp.mono (fun _ => BI.true_intro))
      iapply htwp .hasNoLC
      isplitl_exact Hpoints
      · unfold runtimeModuleOwn
        isplitl [HruntimeWP]
        · unfold runtimeModuleElem; iexact HruntimeWP
        · unfold currentInstanceOwnN; iexact HinstanceFrag
  · apply wasm_smallStep_heap_globals_runtime_store_adequacy config σ ∅ post
      hagree hinBounds (globalHeapAgrees_empty _) hwf
    intro gs
    simp only [BI.BigSepM.bigSepM_empty.to_eq]
    iintro ⟨Hpoints, _Hempty, HruntimeModule, _HhostEnv⟩
    iapply twp.to_wp
    iapply htwp .hasLC
    isplitl_exact Hpoints
    · iexact HruntimeModule

/-- Total-correctness runtime entry point that also hands out the entry
instance's tag table.  This is the entry point the exception rules need: they
consume `tagTableOwn` to learn that their tag index is canonical. -/
theorem wasm_smallStep_runtime_tags_terminates
    [WasmSmallStepGpreS α]
    (config : Config α) (φ : List Value → Prop)
    (hwf : config.store.runtime.entry.id < config.store.runtime.instances.size)
    (htwp : ∀ (hlc : HasLC) [WasmSmallStepGS hlc α],
      runtimeModuleOwn config.store.runtime.entry
          config.store.runtime.currentModule ∗
        tagTableOwn config.store.wasm.tagIds ⊢
        WP config.expr @ Stuckness.NotStuck; ⊤
          [{ values, ⌜φ values⌝ }]) :
    TerminatesWith config (fun values _store => φ values) := by
  apply stronglyNormalizing_adequate_terminates config
    (fun values _store => φ values)
  · apply wasm_smallStep_heap_globals_runtime_tags_stronglyNormalizing
      config ∅ ∅ (fun values => iprop(⌜φ values⌝))
      (heapAgreesWithMem_empty _) (heapAddressesInBounds_empty _)
      (globalHeapAgrees_empty _) hwf
    intro gs
    simp only [BI.BigSepM.bigSepM_empty.to_eq]
    iintro ⟨_Hheap, _Hglobals, Hruntime, Htags⟩
    iapply htwp .hasNoLC
    isplitl_exact Hruntime
    · iexact Htags
  · apply wasm_smallStep_runtime_tags_adequacy config φ hwf
    intro gs
    iintro Hboth
    iapply twp.to_wp
    iapply htwp .hasLC
    iexact Hboth

/-- Total-correctness entry point owning only the physical memory bytes, with a
value-only postcondition. -/
theorem wasm_smallStep_heap_terminates
    [WasmSmallStepGpreS α]
    (config : Config α) (σ : WasmHeapMap (Option UInt8))
    (φ : List Value → Prop)
    (hagree : heapAgreesWithMem σ (storeResolve config.store))
    (hinBounds : heapAddressesInBounds σ (storeResolve config.store))
    (hwf : config.store.runtime.entry.id < config.store.runtime.instances.size)
    (htwp : ∀ (hlc : HasLC) [WasmSmallStepGS hlc α],
      ([∗map] address ↦ value ∈ σ,
        pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
          address (DFrac.own 1) value) ⊢
        WP config.expr @ Stuckness.NotStuck; ⊤
          [{ values, ⌜φ values⌝ }]) :
    TerminatesWith config (fun values _store => φ values) := by
  apply wasm_smallStep_heap_store_terminates config σ
    (fun values _store => φ values) hagree hinBounds hwf
  intro hlc _
  iintro ⟨Hpoints, Hruntime⟩
  iclear Hruntime
  iapply (twp.mono (Φ := fun values => iprop(⌜φ values⌝)) ?hmono)
  case hmono =>
    intro values
    iintro %hφ
    iintro %store %observations Hstate
    iclear Hstate
    ipureexact hφ
  iapply htwp hlc
  iexact Hpoints

/-- State-sensitive adequacy with explicit authoritative ownership of passive
data-segment status in addition to memory, globals, and the runtime module. -/
theorem wasm_smallStep_heap_globals_segments_runtime_store_adequacy
    [WasmSmallStepGpreS α]
    (config : Config α)
    (σ : WasmHeapMap (Option UInt8))
    (globalσ : WasmGlobalMap Value)
    (dataSegmentσ : WasmDataSegmentMap (Option (List UInt8)))
    (post : List Value → MachineStore α → Prop)
    (hagree : heapAgreesWithMem σ (storeResolve config.store))
    (hinBounds : heapAddressesInBounds σ (storeResolve config.store))
    (hglobals : globalHeapAgrees globalσ config.store.wasm.globals)
    (hsegments :
      dataSegmentHeapAgrees dataSegmentσ config.store.wasm.dataSegments)
    (hwf : config.store.runtime.entry.id < config.store.runtime.instances.size)
    (hwp : ∀ [WasmSmallStepGS .hasLC α],
      (([∗map] address ↦ value ∈ σ,
          pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
            address (DFrac.own 1) value) ∗
        ([∗map] index ↦ value ∈ globalσ,
          globalPointsTo index value) ∗
        ([∗map] index ↦ value ∈ dataSegmentσ,
          dataSegmentPointsTo index value) ∗
        runtimeModuleOwn config.store.runtime.entry
          config.store.runtime.currentModule) ⊢
        WP config.expr @ Stuckness.NotStuck; ⊤
          {{ values,
            ∀ (store : MachineStore α) (_observations : List StepKind),
              stateInterp (GF := WasmHeapGF α) store 0 [] 0 -∗
              ⌜post values store⌝ }}) :
    adequate Stuckness.NotStuck config.expr config.store post := by
  refine wp_store_adequacy
    (GF := WasmHeapGF α) Stuckness.NotStuck
    config.expr config.store post ?_
  intro inv κs
  wasm_alloc_memory_ghosts config from σ
  letI globalMapG : GhostMapG (WasmHeapGF α) GlobalKey Value WasmGlobalMap :=
    GhostSlot.globalMap
  imod (ghost_map_alloc (GF := WasmHeapGF α) (K := GlobalKey)
      (V := Value) (H := WasmGlobalMap) globalσ) with
    ⟨%globalName, Hglobals, HglobalPoints⟩
  letI dataSegmentMapG :
      GhostMapG (WasmHeapGF α) DataSegmentKey (Option (List UInt8))
        WasmDataSegmentMap :=
    GhostSlot.dataSegmentMap
  imod (ghost_map_alloc (GF := WasmHeapGF α) (K := DataSegmentKey)
      (V := Option (List UInt8)) (H := WasmDataSegmentMap)
      dataSegmentσ) with
    ⟨%dataSegmentName, HsegmentsAuth, HsegmentPoints⟩
  letI tableMapG : GhostMapG (WasmHeapGF α) TableKey TableInst WasmTableMap :=
    GhostSlot.tableMap
  imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := TableKey)
      (V := TableInst) (H := WasmTableMap)) with
    ⟨%tableName, Htables⟩
  letI elementSegmentMapG :
      GhostMapG (WasmHeapGF α) ElementSegmentKey (Option (List (Option Nat)))
        WasmElementSegmentMap :=
    GhostSlot.elementSegmentMap
  imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := ElementSegmentKey)
      (V := Option (List (Option Nat))) (H := WasmElementSegmentMap)) with
    ⟨%elementSegmentName, HelementSegments⟩
  wasm_install_heap_map_instances
  wasm_alloc_current_runtime_module config
  wasm_alloc_empty_host_envs
  wasm_alloc_host_state config
  iclear HhostStateFrag
  wasm_alloc_current_instance config
  wasm_alloc_runtime_instances config
  wasm_alloc_exception_map
  wasm_alloc_tag_table config
  letI gs : WasmSmallStepGS .hasLC α := smallStepGS .hasLC inv
  iclear Hmeta
  imodintro
  iexists (fun store _observations =>
    stateInterp (GF := WasmHeapGF α) store 0 [] 0)
  iexists (fun _ => iprop(True))
  dsimp only
  wasm_build_machine_aux config
  isplitl [Hheap Hglobals HsegmentsAuth Htables HelementSegments HruntimeModuleAuth' HruntimeInstances HinstanceState HhostEnvAuth HhostState Hexc]
  · iapply (stateInterp_eq config.store 0 [] 0).mpr
    iexists σ
    iexists globalσ
    iexists dataSegmentσ
    iexists (∅ : WasmTableMap TableInst)
    iexists (∅ : WasmElementSegmentMap (Option (List (Option Nat))))
    iexists (PartialMap.singleton config.store.runtime.entry.id
      config.store.runtime.currentModule)
    iexists (∅ : WasmHostEnvMap (HostEnv α))
    unfold runtimeModuleElem runtimeInstancesOwn hostStateAuth currentInstanceAuth currentInstanceAuthN
    simp only [BI.BigSepM.bigSepM_singleton.to_eq]
    iframe ∗ #
    ipureexact ⟨hagree, hinBounds, hglobals, hsegments,
      tableHeapAgrees_empty _,
      elementSegmentHeapAgrees_empty _,
      runtimeModuleSingletonAgrees config.store.runtime hwf,
      fun id env hm => by simp [get?_empty] at hm⟩
  · iapply hwp
    isplitl_exact Hpoints
    · isplitl [HglobalPoints]
      · unfold globalPointsTo
        iexact HglobalPoints
      · isplitl [HsegmentPoints]
        · unfold dataSegmentPointsTo
          iexact HsegmentPoints
        · unfold runtimeModuleOwn
          isplitl [HruntimeWP]
          · unfold runtimeModuleElem; iexact HruntimeWP
          · unfold currentInstanceOwnN; iexact HinstanceFrag

theorem wasm_smallStep_heap_globals_segments_runtime_store_partiallyMeets
    [WasmSmallStepGpreS α]
    (config : Config α)
    (σ : WasmHeapMap (Option UInt8))
    (globalσ : WasmGlobalMap Value)
    (dataSegmentσ : WasmDataSegmentMap (Option (List UInt8)))
    (post : List Value → MachineStore α → Prop)
    (hagree : heapAgreesWithMem σ (storeResolve config.store))
    (hinBounds : heapAddressesInBounds σ (storeResolve config.store))
    (hglobals : globalHeapAgrees globalσ config.store.wasm.globals)
    (hsegments :
      dataSegmentHeapAgrees dataSegmentσ config.store.wasm.dataSegments)
    (hwf : config.store.runtime.entry.id < config.store.runtime.instances.size)
    (hwp : ∀ [WasmSmallStepGS .hasLC α],
      (([∗map] address ↦ value ∈ σ,
          pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
            address (DFrac.own 1) value) ∗
        ([∗map] index ↦ value ∈ globalσ,
          globalPointsTo index value) ∗
        ([∗map] index ↦ value ∈ dataSegmentσ,
          dataSegmentPointsTo index value) ∗
        runtimeModuleOwn config.store.runtime.entry
          config.store.runtime.currentModule) ⊢
        WP config.expr @ Stuckness.NotStuck; ⊤
          {{ values,
            ∀ (store : MachineStore α) (_observations : List StepKind),
              stateInterp (GF := WasmHeapGF α) store 0 [] 0 -∗
              ⌜post values store⌝ }}) :
    PartiallyMeets config post :=
  adequate_to_partiallyMeets config post
    (wasm_smallStep_heap_globals_segments_runtime_store_adequacy
      config σ globalσ dataSegmentσ post hagree hinBounds hglobals
      hsegments hwf hwp)

/-- Fully state-sensitive adequacy including authoritative table ownership.
This is the entry point for proofs using `table.get`/`table.set`: each owned
table keeps its stable index while its physical and ghost contents evolve in
lockstep. -/
theorem wasm_smallStep_heap_globals_segments_tables_runtime_store_adequacy
    [WasmSmallStepGpreS α]
    (config : Config α)
    (σ : WasmHeapMap (Option UInt8))
    (globalσ : WasmGlobalMap Value)
    (dataSegmentσ : WasmDataSegmentMap (Option (List UInt8)))
    (tableσ : WasmTableMap TableInst)
    (elementSegmentσ :
      WasmElementSegmentMap (Option (List (Option Nat))))
    (post : List Value → MachineStore α → Prop)
    (hagree : heapAgreesWithMem σ (storeResolve config.store))
    (hinBounds : heapAddressesInBounds σ (storeResolve config.store))
    (hglobals : globalHeapAgrees globalσ config.store.wasm.globals)
    (hsegments :
      dataSegmentHeapAgrees dataSegmentσ config.store.wasm.dataSegments)
    (htables : tableHeapAgrees tableσ config.store.wasm.tables)
    (helementSegments :
      elementSegmentHeapAgrees elementSegmentσ
        config.store.wasm.elementSegments)
    (hwf : config.store.runtime.entry.id < config.store.runtime.instances.size)
    (hwp : ∀ [WasmSmallStepGS .hasLC α],
      (([∗map] address ↦ value ∈ σ,
          pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
            address (DFrac.own 1) value) ∗
        ([∗map] index ↦ value ∈ globalσ,
          globalPointsTo index value) ∗
        ([∗map] index ↦ value ∈ dataSegmentσ,
          dataSegmentPointsTo index value) ∗
        ([∗map] index ↦ table ∈ tableσ,
          tablePointsTo index table) ∗
        ([∗map] index ↦ value ∈ elementSegmentσ,
          elementSegmentPointsTo index value) ∗
        runtimeModuleOwn config.store.runtime.entry
          config.store.runtime.currentModule) ⊢
        WP config.expr @ Stuckness.NotStuck; ⊤
          {{ values,
            ∀ (store : MachineStore α) (_observations : List StepKind),
              stateInterp (GF := WasmHeapGF α) store 0 [] 0 -∗
              ⌜post values store⌝ }}) :
    adequate Stuckness.NotStuck config.expr config.store post := by
  refine wp_store_adequacy
    (GF := WasmHeapGF α) Stuckness.NotStuck
    config.expr config.store post ?_
  intro inv κs
  wasm_alloc_memory_ghosts config from σ
  letI globalMapG : GhostMapG (WasmHeapGF α) GlobalKey Value WasmGlobalMap :=
    GhostSlot.globalMap
  imod (ghost_map_alloc (GF := WasmHeapGF α) (K := GlobalKey)
      (V := Value) (H := WasmGlobalMap) globalσ) with
    ⟨%globalName, Hglobals, HglobalPoints⟩
  letI dataSegmentMapG :
      GhostMapG (WasmHeapGF α) DataSegmentKey (Option (List UInt8))
        WasmDataSegmentMap :=
    GhostSlot.dataSegmentMap
  imod (ghost_map_alloc (GF := WasmHeapGF α) (K := DataSegmentKey)
      (V := Option (List UInt8)) (H := WasmDataSegmentMap)
      dataSegmentσ) with
    ⟨%dataSegmentName, HsegmentsAuth, HsegmentPoints⟩
  letI tableMapG : GhostMapG (WasmHeapGF α) TableKey TableInst WasmTableMap :=
    GhostSlot.tableMap
  imod (ghost_map_alloc (GF := WasmHeapGF α) (K := TableKey)
      (V := TableInst) (H := WasmTableMap) tableσ) with
    ⟨%tableName, HtablesAuth, HtablePoints⟩
  letI elementSegmentMapG :
      GhostMapG (WasmHeapGF α) ElementSegmentKey (Option (List (Option Nat)))
        WasmElementSegmentMap :=
    GhostSlot.elementSegmentMap
  imod (ghost_map_alloc (GF := WasmHeapGF α) (K := ElementSegmentKey)
      (V := Option (List (Option Nat))) (H := WasmElementSegmentMap)
      elementSegmentσ) with
    ⟨%elementSegmentName, HelementSegmentsAuth,
      HelementSegmentPoints⟩
  wasm_install_heap_map_instances
  wasm_alloc_current_runtime_module config
  wasm_alloc_empty_host_envs
  wasm_alloc_host_state config
  iclear HhostStateFrag
  wasm_alloc_current_instance config
  wasm_alloc_runtime_instances config
  wasm_alloc_exception_map
  wasm_alloc_tag_table config
  letI gs : WasmSmallStepGS .hasLC α := smallStepGS .hasLC inv
  iclear Hmeta
  imodintro
  iexists (fun store _observations =>
    stateInterp (GF := WasmHeapGF α) store 0 [] 0)
  iexists (fun _ => iprop(True))
  dsimp only
  wasm_build_machine_aux config
  isplitl [Hheap Hglobals HsegmentsAuth HtablesAuth
      HelementSegmentsAuth HruntimeModuleAuth' HruntimeInstances HinstanceState HhostEnvAuth HhostState Hexc]
  · iapply (stateInterp_eq config.store 0 [] 0).mpr
    iexists σ
    iexists globalσ
    iexists dataSegmentσ
    iexists tableσ
    iexists elementSegmentσ
    iexists (PartialMap.singleton config.store.runtime.entry.id
      config.store.runtime.currentModule)
    iexists (∅ : WasmHostEnvMap (HostEnv α))
    unfold runtimeModuleElem runtimeInstancesOwn hostStateAuth currentInstanceAuth currentInstanceAuthN
    simp only [BI.BigSepM.bigSepM_singleton.to_eq]
    iframe ∗ #
    ipureexact ⟨hagree, hinBounds, hglobals, hsegments,
      htables,
      helementSegments,
      runtimeModuleSingletonAgrees config.store.runtime hwf,
      fun id env hm => by simp [get?_empty] at hm⟩
  · iapply hwp
    isplitl_exact Hpoints
    · isplitl [HglobalPoints]
      · unfold globalPointsTo
        iexact HglobalPoints
      · isplitl [HsegmentPoints]
        · unfold dataSegmentPointsTo
          iexact HsegmentPoints
        · isplitl [HtablePoints]
          · unfold tablePointsTo
            iexact HtablePoints
          · isplitl [HelementSegmentPoints]
            · unfold elementSegmentPointsTo
              iexact HelementSegmentPoints
            · unfold runtimeModuleOwn
              isplitl [HruntimeWP]
              · unfold runtimeModuleElem; iexact HruntimeWP
              · unfold currentInstanceOwnN; iexact HinstanceFrag

theorem wasm_smallStep_heap_globals_segments_tables_runtime_store_partiallyMeets
    [WasmSmallStepGpreS α]
    (config : Config α)
    (σ : WasmHeapMap (Option UInt8))
    (globalσ : WasmGlobalMap Value)
    (dataSegmentσ : WasmDataSegmentMap (Option (List UInt8)))
    (tableσ : WasmTableMap TableInst)
    (elementSegmentσ :
      WasmElementSegmentMap (Option (List (Option Nat))))
    (post : List Value → MachineStore α → Prop)
    (hagree : heapAgreesWithMem σ (storeResolve config.store))
    (hinBounds : heapAddressesInBounds σ (storeResolve config.store))
    (hglobals : globalHeapAgrees globalσ config.store.wasm.globals)
    (hsegments :
      dataSegmentHeapAgrees dataSegmentσ config.store.wasm.dataSegments)
    (htables : tableHeapAgrees tableσ config.store.wasm.tables)
    (helementSegments :
      elementSegmentHeapAgrees elementSegmentσ
        config.store.wasm.elementSegments)
    (hwf : config.store.runtime.entry.id < config.store.runtime.instances.size)
    (hwp : ∀ [WasmSmallStepGS .hasLC α],
      (([∗map] address ↦ value ∈ σ,
          pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
            address (DFrac.own 1) value) ∗
        ([∗map] index ↦ value ∈ globalσ,
          globalPointsTo index value) ∗
        ([∗map] index ↦ value ∈ dataSegmentσ,
          dataSegmentPointsTo index value) ∗
        ([∗map] index ↦ table ∈ tableσ,
          tablePointsTo index table) ∗
        ([∗map] index ↦ value ∈ elementSegmentσ,
          elementSegmentPointsTo index value) ∗
        runtimeModuleOwn config.store.runtime.entry
          config.store.runtime.currentModule) ⊢
        WP config.expr @ Stuckness.NotStuck; ⊤
          {{ values,
            ∀ (store : MachineStore α) (_observations : List StepKind),
              stateInterp (GF := WasmHeapGF α) store 0 [] 0 -∗
              ⌜post values store⌝ }}) :
    PartiallyMeets config post :=
  adequate_to_partiallyMeets config post
    (wasm_smallStep_heap_globals_segments_tables_runtime_store_adequacy
      config σ globalσ dataSegmentσ tableσ elementSegmentσ post
      hagree hinBounds hglobals hsegments htables helementSegments hwf hwp)

/-- Backwards-compatible adequacy rule for clients that do not execute calls. -/
theorem wasm_smallStep_heap_globals_adequacy
    [WasmSmallStepGpreS α]
    (config : Config α)
    (σ : WasmHeapMap (Option UInt8))
    (globalσ : WasmGlobalMap Value)
    (φ : List Value → Prop)
    (hagree : heapAgreesWithMem σ (storeResolve config.store))
    (hinBounds : heapAddressesInBounds σ (storeResolve config.store))
    (hglobals : globalHeapAgrees globalσ config.store.wasm.globals)
    (hwf : config.store.runtime.entry.id < config.store.runtime.instances.size)
    (hwp : ∀ [WasmSmallStepGS .hasLC α],
      (([∗map] address ↦ value ∈ σ,
          pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
            address (DFrac.own 1) value) ∗
        ([∗map] index ↦ value ∈ globalσ,
          globalPointsTo index value)) ⊢
        WP config.expr @ Stuckness.NotStuck; ⊤
          {{ values, ⌜φ values⌝ }}) :
    adequate Stuckness.NotStuck config.expr config.store
      (fun values _ => φ values) := by
  apply wasm_smallStep_heap_globals_runtime_adequacy config σ globalσ φ
    hagree hinBounds hglobals hwf
  intro gs
  iintro ⟨Hheap, Hglobals, Hruntime⟩
  iclear Hruntime
  iapply_frame hwp

/-- Public partial-correctness form of
`wasm_smallStep_heap_globals_adequacy`. Generated-function clients generally
want the Talos relational predicate, while the proof itself is most naturally
written as an Iris WP over authoritative memory and globals. -/
theorem wasm_smallStep_heap_globals_partiallyMeets
    [WasmSmallStepGpreS α]
    (config : Config α)
    (σ : WasmHeapMap (Option UInt8))
    (globalσ : WasmGlobalMap Value)
    (φ : List Value → Prop)
    (hagree : heapAgreesWithMem σ (storeResolve config.store))
    (hinBounds : heapAddressesInBounds σ (storeResolve config.store))
    (hglobals : globalHeapAgrees globalσ config.store.wasm.globals)
    (hwf : config.store.runtime.entry.id < config.store.runtime.instances.size)
    (hwp : ∀ [WasmSmallStepGS .hasLC α],
      (([∗map] address ↦ value ∈ σ,
          pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
            address (DFrac.own 1) value) ∗
        ([∗map] index ↦ value ∈ globalσ,
          globalPointsTo index value)) ⊢
        WP config.expr @ Stuckness.NotStuck; ⊤
          {{ values, ⌜φ values⌝ }}) :
    PartiallyMeets config (fun values _store => φ values) :=
  adequate_to_partiallyMeets config (fun values _store => φ values)
    (wasm_smallStep_heap_globals_adequacy config σ globalσ φ
      hagree hinBounds hglobals hwf hwp)

/-- Call-capable partial-correctness wrapper with authoritative memory,
globals, and persistent ownership of the instantiated runtime module. -/
theorem wasm_smallStep_heap_globals_runtime_partiallyMeets
    [WasmSmallStepGpreS α]
    (config : Config α)
    (σ : WasmHeapMap (Option UInt8))
    (globalσ : WasmGlobalMap Value)
    (φ : List Value → Prop)
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
          config.store.runtime.currentModule) ⊢
        WP config.expr @ Stuckness.NotStuck; ⊤
          {{ values, ⌜φ values⌝ }}) :
    PartiallyMeets config (fun values _store => φ values) :=
  adequate_to_partiallyMeets config (fun values _store => φ values)
    (wasm_smallStep_heap_globals_runtime_adequacy config σ globalσ φ
      hagree hinBounds hglobals hwf hwp)

/-- Call-capable partial-correctness wrapper with authoritative byte footprint,
persistent runtime module ownership, and exclusive instance ownership. -/
theorem wasm_smallStep_heap_runtime_instance_adequacy
    [WasmSmallStepGpreS α]
    (config : Config α)
    (σ : WasmHeapMap (Option UInt8))
    (φ : List Value → Prop)
    (hagree : heapAgreesWithMem σ (storeResolve config.store))
    (hinBounds : heapAddressesInBounds σ (storeResolve config.store))
    (hwf : config.store.runtime.entry.id < config.store.runtime.instances.size)
    (hwp : ∀ [WasmSmallStepGS .hasLC α],
      (([∗map] address ↦ value ∈ σ,
          pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
            address (DFrac.own 1) value) ∗
        runtimeModuleOwn config.store.runtime.entry
            config.store.runtime.currentModule) ⊢
        WP config.expr @ Stuckness.NotStuck; ⊤
          {{ values, ⌜φ values⌝ }}) :
    adequate Stuckness.NotStuck config.expr config.store
      (fun values _ => φ values) := by
  refine wp_adequacy (GF := WasmHeapGF α) Stuckness.NotStuck
    config.expr config.store φ ?_
  intro inv κs
  wasm_alloc_memory_ghosts config from σ
  wasm_alloc_empty_heap_maps
  wasm_install_heap_map_instances
  wasm_alloc_current_runtime_module config
  wasm_alloc_empty_host_envs
  wasm_alloc_host_state config
  iclear HhostStateFrag
  wasm_alloc_current_instance config
  wasm_alloc_runtime_instances config
  wasm_alloc_exception_map
  wasm_alloc_tag_table config
  letI gs : WasmSmallStepGS .hasLC α := smallStepGS .hasLC inv
  iclear Hmeta
  imodintro
  iexists (fun store _observations =>
    stateInterp (GF := WasmHeapGF α) store 0 [] 0)
  iexists (fun _ => iprop(True))
  dsimp only
  wasm_build_machine_aux config
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth' HruntimeInstances HinstanceState HhostEnvAuth HhostState Hexc]
  · iapply (stateInterp_eq config.store 0 [] 0).mpr
    iexists σ
    iexists (∅ : WasmGlobalMap Value)
    iexists (∅ : WasmDataSegmentMap (Option (List UInt8)))
    iexists (∅ : WasmTableMap TableInst)
    iexists (∅ : WasmElementSegmentMap (Option (List (Option Nat))))
    iexists (PartialMap.singleton config.store.runtime.entry.id
      config.store.runtime.currentModule)
    iexists (∅ : WasmHostEnvMap (HostEnv α))
    unfold runtimeModuleElem runtimeInstancesOwn hostStateAuth currentInstanceAuth currentInstanceAuthN
    simp only [BI.BigSepM.bigSepM_singleton.to_eq]
    iframe Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth' # HruntimeInstances HinstanceState HhostEnvAuth HhostState Hexc
    ipureexact ⟨hagree, hinBounds, globalHeapAgrees_empty _,
      dataSegmentHeapAgrees_empty _,
      tableHeapAgrees_empty _,
      elementSegmentHeapAgrees_empty _,
      runtimeModuleSingletonAgrees config.store.runtime hwf,
      fun id env hm => by simp [get?_empty] at hm⟩
  · iapply hwp
    isplitl_exact Hpoints
    · unfold runtimeModuleOwn
      isplitl [HruntimeWP]
      · unfold runtimeModuleElem; iexact HruntimeWP
      · unfold currentInstanceOwnN; iexact HinstanceFrag

/-- Combined heap + runtimeInstances adequacy. Provides heap pointsTo,
runtimeModuleOwn, and runtimeInstancesOwn. Use when a proof needs both
cross-instance dispatch (`wp_callCrossInstance`) and memory access (`wp_store8`). -/
theorem wasm_smallStep_heap_runtime_instances_adequacy
    [WasmSmallStepGpreS α]
    (config : Config α)
    (σ : WasmHeapMap (Option UInt8))
    (φ : List Value → Prop)
    (hagree : heapAgreesWithMem σ (storeResolve config.store))
    (hinBounds : heapAddressesInBounds σ (storeResolve config.store))
    (hwf : config.store.runtime.entry.id < config.store.runtime.instances.size)
    (hwp : ∀ [WasmSmallStepGS .hasLC α],
      (([∗map] address ↦ value ∈ σ,
          pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
            address (DFrac.own 1) value) ∗
        runtimeModuleOwn config.store.runtime.entry
            config.store.runtime.currentModule ∗
        runtimeInstancesOwn config.store.runtime.instances) ⊢
        WP config.expr @ Stuckness.NotStuck; ⊤
          {{ values, ⌜φ values⌝ }}) :
    adequate Stuckness.NotStuck config.expr config.store
      (fun values _ => φ values) := by
  refine wp_adequacy (GF := WasmHeapGF α) Stuckness.NotStuck
    config.expr config.store φ ?_
  intro inv κs
  wasm_alloc_memory_ghosts config from σ
  wasm_alloc_empty_heap_maps
  wasm_install_heap_map_instances
  wasm_alloc_current_runtime_module config
  wasm_alloc_empty_host_envs
  wasm_alloc_host_state config
  iclear HhostStateFrag
  wasm_alloc_current_instance config
  letI runtimeInstancesElem :
      ElemG (WasmHeapGF α) (constOF (Agree (DiscreteO (Array (ModuleInstance α))))) :=
    GhostSlot.runtimeInstancesElem
  let runtimeInstancesValue : Agree (DiscreteO (Array (ModuleInstance α))) :=
    toAgree ⟨config.store.runtime.instances⟩
  imod (iOwn_alloc (E := runtimeInstancesElem)
      (runtimeInstancesValue • runtimeInstancesValue) (fun n =>
        CMRA.valid_iff_validN.mp
          (toAgree_op_valid_iff_eq.mpr rfl) n)) with
    ⟨%runtimeInstancesName, HruntimeInstances⟩
  letI runtimeInstancesGS : WasmRuntimeInstancesGS α :=
    { runtimeInstancesElem
      runtimeInstancesName }
  wasm_alloc_exception_map
  wasm_alloc_tag_table config
  letI gs : WasmSmallStepGS .hasLC α := smallStepGS .hasLC inv
  iclear Hmeta
  ihave HruntimeInstancesPair := iOwn_op.mp $$ HruntimeInstances
  icases HruntimeInstancesPair with ⟨HruntimeInstancesState, HruntimeInstancesWP⟩
  imodintro
  iexists (fun store _observations =>
    stateInterp (GF := WasmHeapGF α) store 0 [] 0)
  iexists (fun _ => iprop(True))
  dsimp only
  wasm_build_machine_aux config
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth' HruntimeInstancesState HinstanceState HhostEnvAuth HhostState Hexc]
  · iapply (stateInterp_eq config.store 0 [] 0).mpr
    iexists σ
    iexists (∅ : WasmGlobalMap Value)
    iexists (∅ : WasmDataSegmentMap (Option (List UInt8)))
    iexists (∅ : WasmTableMap TableInst)
    iexists (∅ : WasmElementSegmentMap (Option (List (Option Nat))))
    iexists (PartialMap.singleton config.store.runtime.entry.id
      config.store.runtime.currentModule)
    iexists (∅ : WasmHostEnvMap (HostEnv α))
    unfold runtimeModuleElem runtimeInstancesOwn hostStateAuth currentInstanceAuth currentInstanceAuthN
    simp only [BI.BigSepM.bigSepM_singleton.to_eq]
    iframe Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth' # HruntimeInstancesState HinstanceState HhostEnvAuth HhostState Hexc
    ipureexact ⟨hagree, hinBounds, globalHeapAgrees_empty _,
      dataSegmentHeapAgrees_empty _,
      tableHeapAgrees_empty _,
      elementSegmentHeapAgrees_empty _,
      runtimeModuleSingletonAgrees config.store.runtime hwf,
      fun id env hm => by simp [get?_empty] at hm⟩
  · iapply hwp
    isplitl_exact Hpoints
    · isplitl [HruntimeWP HinstanceFrag]
      · unfold runtimeModuleOwn
        isplitl [HruntimeWP]
        · unfold runtimeModuleElem; iexact HruntimeWP
        · unfold currentInstanceOwnN; iexact HinstanceFrag
      · unfold runtimeInstancesOwn
        iexact HruntimeInstancesWP

theorem wasm_smallStep_heap_runtime_instances_partiallyMeets
    [WasmSmallStepGpreS α]
    (config : Config α)
    (σ : WasmHeapMap (Option UInt8))
    (φ : List Value → Prop)
    (hagree : heapAgreesWithMem σ (storeResolve config.store))
    (hinBounds : heapAddressesInBounds σ (storeResolve config.store))
    (hwf : config.store.runtime.entry.id < config.store.runtime.instances.size)
    (hwp : ∀ [WasmSmallStepGS .hasLC α],
      (([∗map] address ↦ value ∈ σ,
          pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
            address (DFrac.own 1) value) ∗
        runtimeModuleOwn config.store.runtime.entry
            config.store.runtime.currentModule ∗
        runtimeInstancesOwn config.store.runtime.instances) ⊢
        WP config.expr @ Stuckness.NotStuck; ⊤
          {{ values, ⌜φ values⌝ }}) :
    PartiallyMeets config (fun values _store => φ values) :=
  adequate_to_partiallyMeets config (fun values _store => φ values)
    (wasm_smallStep_heap_runtime_instances_adequacy config σ φ
      hagree hinBounds hwf hwp)

theorem wasm_smallStep_heap_runtime_instance_partiallyMeets
    [WasmSmallStepGpreS α]
    (config : Config α)
    (σ : WasmHeapMap (Option UInt8))
    (φ : List Value → Prop)
    (hagree : heapAgreesWithMem σ (storeResolve config.store))
    (hinBounds : heapAddressesInBounds σ (storeResolve config.store))
    (hwf : config.store.runtime.entry.id < config.store.runtime.instances.size)
    (hwp : ∀ [WasmSmallStepGS .hasLC α],
      (([∗map] address ↦ value ∈ σ,
          pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
            address (DFrac.own 1) value) ∗
        runtimeModuleOwn config.store.runtime.entry
            config.store.runtime.currentModule) ⊢
        WP config.expr @ Stuckness.NotStuck; ⊤
          {{ values, ⌜φ values⌝ }}) :
    PartiallyMeets config (fun values _store => φ values) :=
  adequate_to_partiallyMeets config (fun values _store => φ values)
    (wasm_smallStep_heap_runtime_instance_adequacy config σ φ
      hagree hinBounds hwf hwp)

end Wasm.SmallStep
