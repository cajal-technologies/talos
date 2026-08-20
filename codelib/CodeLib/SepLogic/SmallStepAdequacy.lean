import CodeLib.SepLogic.SmallStepLifting
import CodeLib.SepLogic.SmallStepTotalLifting
import Iris.ProgramLogic.Adequacy
import Iris.ProgramLogic.TotalAdequacy
import Interpreter.Wasm.Decoder.Wat

/-!
# Adequacy for the Wasm small-step Iris language

This is the public bridge from an iris-lean `WP` proof to the operational
small-step semantics.  Unlike the legacy `wasm_heap_adequacy`, it refers only
to `Wasm.SmallStep.Step` through the iris-lean `Language` instance.
-/

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
  suffices ∀ (tp : List Expr × State),
      Acc (flip (Language.ErasedStep (Expr := Expr) (State := State) (Obs := Obs))) tp →
      ∀ (e' : Expr) (σ' : State), tp = ([e'], σ') →
        Acc (flip (ExprErasedStep (Expr := Expr) (State := State) (Obs := Obs))) (e', σ') from
    this _ H _ _ rfl
  intro tp Htp
  induction Htp with
  | intro _ _ ih =>
    intro e' σ' htp
    subst htp
    apply Acc.intro
    rintro ⟨e₂, σ₂⟩ ⟨κ, efs, Hstep⟩
    have hefs : efs = [] := LanguageNoFork.no_fork Hstep
    subst hefs
    exact ih ([e₂], σ₂) ⟨κ, Language.Step.atomic Hstep [] []⟩ e₂ σ₂ rfl

end

end Iris.ProgramLogic

namespace Wasm.SmallStep

open Iris OFE COFE BI Iris.BI Iris.Algebra Iris.ProgramLogic
  Language.Notation Std FromMathlib LawfulSet
open Wasm.SepLogic

variable {α : Type}

private theorem sep_pair_pure_rotate
    (P Q : IProp (WasmHeapGF α)) (φ : Prop) :
    (P ∗ Q) ∗ ⌜φ⌝ ⊢ ⌜φ⌝ ∗ P ∗ Q := by
  iintro ⟨⟨HP, HQ⟩, %hφ⟩
  isplitl []
  · ipureintro
    exact hφ
  · isplitl [HP]
    · iexact HP
    · iexact HQ

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
  · iapply BigSepL2.bigSepL2_singleton
    iframe
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
  imod genHeap_init (L := MemoryKey) (V := Option UInt8)
      (GF := WasmHeapGF α) (H := WasmHeapMap) ∅ with
    ⟨%heapGS, Hheap, Hpoints, Hmeta⟩
  letI globalMapG : GhostMapG (WasmHeapGF α) GlobalKey Value WasmGlobalMap := by
    constructor
    exists 7
  imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := GlobalKey)
      (V := Value) (H := WasmGlobalMap)) with ⟨%globalName, Hglobals⟩
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
  letI exceptionMapG :
      GhostMapG (WasmHeapGF α) Nat (Nat × List Value) WasmExceptionMap := by
    constructor
    exists 13
  imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := Nat)
      (V := Nat × List Value) (H := WasmExceptionMap)) with
    ⟨%exceptionName, Hexceptions⟩
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
<<<<<<< HEAD
  letI wasmExceptionGS : WasmExceptionGS α :=
    { toGhostMapG := exceptionMapG
      exceptionName := exceptionName }
  letI runtimeElem :
      ElemG (WasmHeapGF α) (constOF (Agree (DiscreteO Module))) := by
=======
  letI runtimeModuleMapG : GhostMapG (WasmHeapGF α) Nat Module WasmRuntimeModuleMap := by
    constructor
>>>>>>> origin/main
    exists 8
  imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := Nat)
      (V := Module) (H := WasmRuntimeModuleMap)) with ⟨%runtimeName, HruntimeModuleAuth⟩
  letI runtimeGS : WasmRuntimeModuleGS α :=
    { toGhostMapG := runtimeModuleMapG
      runtimeName }
<<<<<<< HEAD
  letI tagTableElem : ElemG (WasmHeapGF α)
      (constOF (Agree (DiscreteO (List Nat)))) := by
    exists 14
  imod (iOwn_alloc (E := tagTableElem)
      (toAgree ⟨config.store.wasm.tagIds⟩) (fun _ => trivial)) with
    ⟨%tagTableName, HtagTable⟩
  letI tagTableGS : WasmTagTableGS α :=
    { tagTableElem
      tagTableName }
  letI hostElem : ElemG (WasmHeapGF α)
      (ExclAuth.ExclAuthURF (constOF (DiscreteO α))) := by
=======
  letI hostEnvMapG : GhostMapG (WasmHeapGF α) Nat (HostEnv α) WasmHostEnvMap := by
    constructor
>>>>>>> origin/main
    exists 12
  imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := Nat)
      (V := HostEnv α) (H := WasmHostEnvMap)) with ⟨%hostEnvName, HhostEnvAuth⟩
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
  iclear HhostStateFrag
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
  iclear HinstanceFrag
  letI runtimeInstancesElem :
      ElemG (WasmHeapGF α) (constOF (Agree (DiscreteO (Array (ModuleInstance α))))) := by
    exists 15
  imod (iOwn_alloc (E := runtimeInstancesElem)
      (toAgree ⟨config.store.runtime.instances⟩) (fun _ => trivial)) with
    ⟨%runtimeInstancesName, HruntimeInstances⟩
  letI runtimeInstancesGS : WasmRuntimeInstancesGS α :=
    { runtimeInstancesElem
      runtimeInstancesName }
  letI gs : WasmSmallStepGS .hasLC α :=
    { toInvGS_gen := inv
      toWasmHeapGS := wasmHeapGS
      global := wasmGlobalGS
      dataSegment := wasmDataSegmentGS
      table := wasmTableGS
      elementSegment := wasmElementSegmentGS
      exception := wasmExceptionGS
      runtime := runtimeGS
<<<<<<< HEAD
      tagTable := tagTableGS
      host := hostGS }
=======
      hostEnv := hostEnvGS
      hostState := hostStateGS
      instanceGS := instanceGS
      runtimeInstances := runtimeInstancesGS }
>>>>>>> origin/main
  iclear Hpoints Hmeta
  imodintro
  iexists (fun store _observations =>
    stateInterp (GF := WasmHeapGF α) store 0 [] 0)
  iexists (fun _ => iprop(True))
  dsimp only
<<<<<<< HEAD
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments Hexceptions Hruntime HtagTable HhostState]
=======
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeInstances HinstanceState HhostEnvAuth HhostState]
>>>>>>> origin/main
  · iapply (stateInterp_eq config.store 0 [] 0).mpr
    iexists (∅ : WasmHeapMap (Option UInt8))
    iexists (∅ : WasmGlobalMap Value)
    iexists (∅ : WasmDataSegmentMap (Option (List UInt8)))
    iexists (∅ : WasmTableMap TableInst)
    iexists (∅ : WasmElementSegmentMap (Option (List (Option Nat))))
<<<<<<< HEAD
    iexists (∅ : WasmExceptionMap (Nat × List Value))
    unfold runtimeInterp runtimeModuleOwn tagTableOwn
    unfold hostStateAuth
    iframe Hheap Hglobals Hsegments Htables HelementSegments Hexceptions Hruntime HhostState
    isplitl [HtagTable]
    · iexists config.store.wasm.tagIds
      isplitl [HtagTable]
      · iexact HtagTable
      · ipureintro
        exact List.prefix_rfl
=======
    iexists (∅ : WasmRuntimeModuleMap Module)
    iexists (∅ : WasmHostEnvMap (HostEnv α))
    unfold runtimeModuleElem runtimeInstancesOwn hostStateAuth currentInstanceAuth currentInstanceAuthN
    simp only [BI.BigSepM.bigSepM_empty.to_eq, BI.emp_sep.to_eq]
    iframe Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeInstances HinstanceState HhostEnvAuth HhostState
>>>>>>> origin/main
    ipureintro
    exact ⟨heapAgreesWithMem_empty _,
      heapAddressesInBounds_empty _,
      globalHeapAgrees_empty _,
      dataSegmentHeapAgrees_empty _,
<<<<<<< HEAD
      ⟨tableHeapAgrees_empty _, elementSegmentHeapAgrees_empty _,
        exceptionHeapAgrees_empty _⟩⟩
  · iapply hwp
    unfold hostStateOwn
    iexact HhostOwn

/-- Closed compatibility entry point for host-independent proofs. -/
theorem wasm_smallStep_adequacy
    [WasmSmallStepGpreS α]
    (config : Config α) (φ : List Value → Prop)
    (hwp : ∀ [WasmSmallStepGS .hasLC α],
      ⊢@{IProp (WasmHeapGF α)}
        (WP config.expr @ Stuckness.NotStuck; ⊤ {{ values, ⌜φ values⌝ }})) :
    adequate Stuckness.NotStuck config.expr config.store
      (fun values _ => φ values) := by
  apply wasm_smallStep_host_adequacy config φ
  intro _
  iintro _Hhost
  iclear _Hhost
  exact hwp
=======
      tableHeapAgrees_empty _,
      elementSegmentHeapAgrees_empty _,
      fun id m hm => by simp [get?_empty] at hm,
      fun id env hm => by simp [get?_empty] at hm⟩
  · exact hwp
>>>>>>> origin/main

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
    Relation.StronglyNormalizing Language.ErasedStep ([config.expr], config.store) := by
  apply twp_total (hlc := .hasNoLC) (GF := WasmHeapGF α)
    Stuckness.NotStuck config.expr config.store
    (fun values => iprop(⌜φ values⌝)) 0 0
  intro inv
  imod genHeap_init (L := MemoryKey) (V := Option UInt8)
      (GF := WasmHeapGF α) (H := WasmHeapMap) ∅ with
    ⟨%heapGS, Hheap, Hpoints, Hmeta⟩
  letI globalMapG : GhostMapG (WasmHeapGF α) GlobalKey Value WasmGlobalMap := by
    constructor
    exists 7
  imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := GlobalKey)
      (V := Value) (H := WasmGlobalMap)) with ⟨%globalName, Hglobals⟩
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
  letI exceptionMapG :
      GhostMapG (WasmHeapGF α) Nat (Nat × List Value) WasmExceptionMap := by
    constructor
    exists 13
  imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := Nat)
      (V := Nat × List Value) (H := WasmExceptionMap)) with
    ⟨%exceptionName, Hexceptions⟩
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
<<<<<<< HEAD
  letI wasmExceptionGS : WasmExceptionGS α :=
    { toGhostMapG := exceptionMapG
      exceptionName := exceptionName }
  letI runtimeElem :
      ElemG (WasmHeapGF α) (constOF (Agree (DiscreteO Module))) := by
=======
  letI runtimeModuleMapG : GhostMapG (WasmHeapGF α) Nat Module WasmRuntimeModuleMap := by
    constructor
>>>>>>> origin/main
    exists 8
  imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := Nat)
      (V := Module) (H := WasmRuntimeModuleMap)) with ⟨%runtimeName, HruntimeModuleAuth⟩
  letI runtimeGS : WasmRuntimeModuleGS α :=
    { toGhostMapG := runtimeModuleMapG
      runtimeName }
<<<<<<< HEAD
  letI tagTableElem : ElemG (WasmHeapGF α)
      (constOF (Agree (DiscreteO (List Nat)))) := by
    exists 14
  imod (iOwn_alloc (E := tagTableElem)
      (toAgree ⟨config.store.wasm.tagIds⟩) (fun _ => trivial)) with
    ⟨%tagTableName, HtagTable⟩
  letI tagTableGS : WasmTagTableGS α :=
    { tagTableElem
      tagTableName }
  letI hostElem : ElemG (WasmHeapGF α)
      (ExclAuth.ExclAuthURF (constOF (DiscreteO α))) := by
=======
  letI hostEnvMapG : GhostMapG (WasmHeapGF α) Nat (HostEnv α) WasmHostEnvMap := by
    constructor
>>>>>>> origin/main
    exists 12
  imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := Nat)
      (V := HostEnv α) (H := WasmHostEnvMap)) with ⟨%hostEnvName, HhostEnvAuth⟩
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
  iclear HhostStateFrag
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
  iclear HinstanceFrag
  letI runtimeInstancesElem :
      ElemG (WasmHeapGF α) (constOF (Agree (DiscreteO (Array (ModuleInstance α))))) := by
    exists 15
  imod (iOwn_alloc (E := runtimeInstancesElem)
      (toAgree ⟨config.store.runtime.instances⟩) (fun _ => trivial)) with
    ⟨%runtimeInstancesName, HruntimeInstances⟩
  letI runtimeInstancesGS : WasmRuntimeInstancesGS α :=
    { runtimeInstancesElem
      runtimeInstancesName }
  letI gs : WasmSmallStepGS .hasNoLC α :=
    { toInvGS_gen := inv
      toWasmHeapGS := wasmHeapGS
      global := wasmGlobalGS
      dataSegment := wasmDataSegmentGS
      table := wasmTableGS
      elementSegment := wasmElementSegmentGS
      exception := wasmExceptionGS
      runtime := runtimeGS
<<<<<<< HEAD
      tagTable := tagTableGS
      host := hostGS }
=======
      hostEnv := hostEnvGS
      hostState := hostStateGS
      instanceGS := instanceGS
      runtimeInstances := runtimeInstancesGS }
>>>>>>> origin/main
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
<<<<<<< HEAD
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments Hexceptions Hruntime HtagTable HhostState]
=======
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeInstances HinstanceState HhostEnvAuth HhostState]
>>>>>>> origin/main
  · iapply (stateInterp_eq config.store 0 [] 0).mpr
    iexists (∅ : WasmHeapMap (Option UInt8))
    iexists (∅ : WasmGlobalMap Value)
    iexists (∅ : WasmDataSegmentMap (Option (List UInt8)))
    iexists (∅ : WasmTableMap TableInst)
    iexists (∅ : WasmElementSegmentMap (Option (List (Option Nat))))
<<<<<<< HEAD
    iexists (∅ : WasmExceptionMap (Nat × List Value))
    unfold runtimeInterp runtimeModuleOwn tagTableOwn
    unfold hostStateAuth
    iframe Hheap Hglobals Hsegments Htables HelementSegments Hexceptions Hruntime HhostState
    isplitl [HtagTable]
    · iexists config.store.wasm.tagIds
      isplitl [HtagTable]
      · iexact HtagTable
      · ipureintro
        exact List.prefix_rfl
=======
    iexists (∅ : WasmRuntimeModuleMap Module)
    iexists (∅ : WasmHostEnvMap (HostEnv α))
    unfold runtimeModuleElem runtimeInstancesOwn hostStateAuth currentInstanceAuth currentInstanceAuthN
    simp only [BI.BigSepM.bigSepM_empty.to_eq, BI.emp_sep.to_eq]
    iframe Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeInstances HinstanceState HhostEnvAuth HhostState
>>>>>>> origin/main
    ipureintro
    exact ⟨heapAgreesWithMem_empty _,
      heapAddressesInBounds_empty _,
      globalHeapAgrees_empty _,
      dataSegmentHeapAgrees_empty _,
<<<<<<< HEAD
      ⟨tableHeapAgrees_empty _, elementSegmentHeapAgrees_empty _,
        exceptionHeapAgrees_empty _⟩⟩
=======
      tableHeapAgrees_empty _,
      elementSegmentHeapAgrees_empty _,
      fun id m hm => by simp [get?_empty] at hm,
      fun id env hm => by simp [get?_empty] at hm⟩
>>>>>>> origin/main
  · iintro _
    exact htwp

/-- Total-WP strong normalization with authoritative initial memory, globals,
and runtime-module ownership. This is the termination counterpart of
`wasm_smallStep_heap_globals_runtime_store_adequacy`. -/
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
    Relation.StronglyNormalizing Language.ErasedStep ([config.expr], config.store) := by
  apply twp_total (hlc := .hasNoLC) (GF := WasmHeapGF α)
    Stuckness.NotStuck config.expr config.store
    Φ 0 0
  intro inv
  imod genHeap_init (L := MemoryKey) (V := Option UInt8)
      (GF := WasmHeapGF α) (H := WasmHeapMap) σ with
    ⟨%heapGS, Hheap, Hpoints, Hmeta⟩
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
  letI exceptionMapG :
      GhostMapG (WasmHeapGF α) Nat (Nat × List Value) WasmExceptionMap := by
    constructor
    exists 13
  imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := Nat)
      (V := Nat × List Value) (H := WasmExceptionMap)) with
    ⟨%exceptionName, Hexceptions⟩
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
<<<<<<< HEAD
  letI wasmExceptionGS : WasmExceptionGS α :=
    { toGhostMapG := exceptionMapG
      exceptionName := exceptionName }
  letI runtimeElem :
      ElemG (WasmHeapGF α) (constOF (Agree (DiscreteO Module))) := by
=======
  letI runtimeModuleMapG : GhostMapG (WasmHeapGF α) Nat Module WasmRuntimeModuleMap := by
    constructor
>>>>>>> origin/main
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
<<<<<<< HEAD
  letI tagTableElem : ElemG (WasmHeapGF α)
      (constOF (Agree (DiscreteO (List Nat)))) := by
    exists 14
  imod (iOwn_alloc (E := tagTableElem)
      (toAgree ⟨config.store.wasm.tagIds⟩) (fun _ => trivial)) with
    ⟨%tagTableName, HtagTable⟩
  letI tagTableGS : WasmTagTableGS α :=
    { tagTableElem
      tagTableName }
  letI hostElem : ElemG (WasmHeapGF α)
      (ExclAuth.ExclAuthURF (constOF (DiscreteO α))) := by
=======
  letI hostEnvMapG : GhostMapG (WasmHeapGF α) Nat (HostEnv α) WasmHostEnvMap := by
    constructor
>>>>>>> origin/main
    exists 12
  imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := Nat)
      (V := HostEnv α) (H := WasmHostEnvMap)) with ⟨%hostEnvName, HhostEnvAuth⟩
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
  iclear HhostStateFrag
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
  letI gs : WasmSmallStepGS .hasNoLC α :=
    { toInvGS_gen := inv
      toWasmHeapGS := wasmHeapGS
      global := wasmGlobalGS
      dataSegment := wasmDataSegmentGS
      table := wasmTableGS
      elementSegment := wasmElementSegmentGS
      exception := wasmExceptionGS
      runtime := runtimeGS
<<<<<<< HEAD
      tagTable := tagTableGS
      host := hostGS }
=======
      hostEnv := hostEnvGS
      hostState := hostStateGS
      instanceGS := instanceGS
      runtimeInstances := runtimeInstancesGS }
>>>>>>> origin/main
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
<<<<<<< HEAD
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments Hexceptions HruntimeState HtagTable HhostState]
=======
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth' HruntimeInstances HinstanceState HhostEnvAuth HhostState]
>>>>>>> origin/main
  · iapply (stateInterp_eq config.store 0 [] 0).mpr
    iexists σ
    iexists globalσ
    iexists (∅ : WasmDataSegmentMap (Option (List UInt8)))
    iexists (∅ : WasmTableMap TableInst)
    iexists (∅ : WasmElementSegmentMap (Option (List (Option Nat))))
<<<<<<< HEAD
    iexists (∅ : WasmExceptionMap (Nat × List Value))
    unfold runtimeInterp runtimeModuleOwn tagTableOwn
    unfold hostStateAuth
    iframe Hheap Hglobals Hsegments Htables HelementSegments Hexceptions HruntimeState HhostState
    isplitl [HtagTable]
    · iexists config.store.wasm.tagIds
      isplitl [HtagTable]
      · iexact HtagTable
      · ipureintro
        exact List.prefix_rfl
    ipureintro
    exact ⟨hagree, hinBounds, hglobals,
      dataSegmentHeapAgrees_empty _,
      ⟨tableHeapAgrees_empty _, elementSegmentHeapAgrees_empty _,
        exceptionHeapAgrees_empty _⟩⟩
=======
    iexists (PartialMap.singleton config.store.runtime.entry.id
      config.store.runtime.currentModule)
    iexists (∅ : WasmHostEnvMap (HostEnv α))
    unfold runtimeModuleElem runtimeInstancesOwn hostStateAuth currentInstanceAuth currentInstanceAuthN
    simp only [BI.BigSepM.bigSepM_singleton.to_eq]
    iframe Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth' # HruntimeInstances HinstanceState HhostEnvAuth HhostState
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
      fun id env hm => by simp [get?_empty] at hm⟩
>>>>>>> origin/main
  · iintro _
    iapply htwp
    isplitl [Hpoints]
    · iexact Hpoints
<<<<<<< HEAD
    · isplitl [HglobalPoints]
      · unfold globalPointsTo
        iexact HglobalPoints
      · isplitl [HruntimeWP]
        · unfold runtimeModuleOwn
          iexact HruntimeWP
        · unfold hostStateOwn
          iexact HhostOwn

/-- Compatibility wrapper for total proofs that do not use host ownership. -/
theorem wasm_smallStep_heap_globals_runtime_stronglyNormalizing
    [WasmSmallStepGpreS α]
    (config : Config α)
    (σ : WasmHeapMap (Option UInt8))
    (globalσ : WasmGlobalMap Value)
    (Φ : List Value → IProp (WasmHeapGF α))
    (hagree : heapAgreesWithMem σ config.store.wasm.mem)
    (hinBounds : heapAddressesInBounds σ config.store.wasm.mem)
    (hglobals : globalHeapAgrees globalσ config.store.wasm.globals)
    (htwp : ∀ [WasmSmallStepGS .hasNoLC α],
      (([∗map] address ↦ value ∈ σ,
          pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
            address (DFrac.own 1) value) ∗
        ([∗map] index ↦ value ∈ globalσ,
          globalPointsTo index value) ∗
        runtimeModuleOwn config.store.runtime.module) ⊢
        WP config.expr @ Stuckness.NotStuck; ⊤ [{ Φ }]) :
    Relation.StronglyNormalizing Language.ErasedStep ([config.expr], config.store) := by
  apply wasm_smallStep_heap_globals_runtime_host_stronglyNormalizing
    config σ globalσ Φ hagree hinBounds hglobals
  intro gs
  iintro ⟨Hpoints, Hglobals, Hruntime, Hhost⟩
  iclear Hhost
  iapply htwp
  iframe Hpoints Hglobals Hruntime
=======
    isplitl [HglobalPoints]
    · unfold globalPointsTo
      iexact HglobalPoints
    · unfold runtimeModuleOwn
      isplitl [HruntimeWP]
      · unfold runtimeModuleElem; iexact HruntimeWP
      · unfold currentInstanceOwnN; iexact HinstanceFrag
>>>>>>> origin/main

private theorem stronglyNormalizing_reaches_irreducible
    {β : Type _} {step : β → β → Prop} {start : β}
    (hsn : Relation.StronglyNormalizing step start) :
    ∃ final,
      Relation.ReflTransGen step start final ∧
      ∀ next, ¬step final next := by
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

private theorem language_step_singleton
    {e₁ : Expr α} {σ₁ : MachineStore α} {obs}
    {ρ₂ : List (Expr α) × MachineStore α}
    (h : Language.Step ([e₁], σ₁) obs ρ₂) :
    ∃ (e₂ : Expr α) (kind : StepKind),
      ρ₂.1 = [e₂] ∧ Step ⟨e₁, σ₁⟩ kind ⟨e₂, ρ₂.2⟩ := by
  rcases ρ₂ with ⟨pool₂, σ₂⟩
  obtain ⟨e₂, eₜ, hprim, rfl⟩ :
      ∃ (e₂ : Expr α) (eₜ : List (Expr α)),
        (e₁, σ₁) -<obs>-> (e₂, σ₂, eₜ) ∧ pool₂ = e₂ :: eₜ := by
    grind [List.append_eq_singleton_iff]
  have hefs := primStep_no_forks hprim
  subst hefs
  obtain ⟨_, kind, _, hstep⟩ := primStep_iff.mp hprim
  exact ⟨e₂, kind, rfl, hstep⟩

private theorem exprErasedSteps_to_steps
    {e₁ : Expr α} {σ₁ : MachineStore α}
    {ρ₂ : List (Expr α) × MachineStore α}
    (hsteps : Relation.ReflTransGen Language.ErasedStep ([e₁], σ₁) ρ₂) :
    ∃ (e₂ : Expr α) (trace : List StepKind),
      ρ₂.1 = [e₂] ∧ Steps ⟨e₁, σ₁⟩ trace ⟨e₂, ρ₂.2⟩ := by
  induction hsteps with
  | refl => exact ⟨e₁, [], rfl, .refl _⟩
  | tail hmid hstep ih =>
    rename_i ρ_mid
    obtain ⟨pool_mid, σ_mid⟩ := ρ_mid
    obtain ⟨e_mid, trace_mid, hpool_mid, hsteps_mid⟩ := ih
    obtain ⟨obs, hlang⟩ := hstep
    rename_i b_int
    obtain ⟨pool_b, σ_b⟩ := b_int
    subst hpool_mid
    obtain ⟨e₂, kind, hpool₂, hstep₂⟩ := language_step_singleton hlang
    exact ⟨e₂, trace_mid ++ [kind], hpool₂, hsteps_mid.trans (.single hstep₂)⟩

/-- Strong normalization plus ordinary Iris safety/partial correctness yields
Talos's finite-trace total-correctness predicate. -/
theorem stronglyNormalizing_adequate_terminates
    (config : Config α)
    (post : List Value → MachineStore α → Prop)
    (hsn : Relation.StronglyNormalizing Language.ErasedStep ([config.expr], config.store))
    (had : adequate Stuckness.NotStuck config.expr config.store post) :
    TerminatesWith config post := by
  obtain ⟨finalState, hreach, hirred⟩ :=
    stronglyNormalizing_reaches_irreducible hsn
  obtain ⟨e₂, trace, hpool₂, hsteps⟩ := exprErasedSteps_to_steps hreach
  obtain ⟨finalPool, finalStore⟩ := finalState
  subst hpool₂
  have hirisReach := hsteps.to_languageErasedSteps
  have hnotStuck := had.adequate_not_stuck
    [e₂] finalStore e₂ rfl hirisReach (by simp)
  rcases hnotStuck with hvalue | hreducible
  · cases hval : toVal e₂ with
    | none =>
      simp [hval] at hvalue
    | some values =>
      have hexpr : e₂ = (.done values : Expr α) :=
        (ToVal.coe_of_toVal_eq_some hval).symm
      subst hexpr
      exact ⟨trace, values, finalStore, hsteps,
        had.adequate_result [] finalStore values hirisReach⟩
  · obtain ⟨κ, e', σ', efs, hprim⟩ := hreducible
    have hefs := primStep_no_forks hprim
    subst hefs
    exact False.elim
      (hirred ([e'], σ') ⟨κ, Language.Step.atomic hprim [] []⟩)

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

/-- Closed adequacy with persistent knowledge of the concrete runtime module.
This is the call-capable counterpart of `wasm_smallStep_adequacy`. -/
theorem wasm_smallStep_runtime_tags_adequacy
    [WasmSmallStepGpreS α]
    (config : Config α) (φ : List Value → Prop)
    (hwf : config.store.runtime.entry.id < config.store.runtime.instances.size)
    (hwp : ∀ [WasmSmallStepGS .hasLC α],
<<<<<<< HEAD
      runtimeModuleOwn config.store.runtime.module ∗
          tagTableOwn config.store.wasm.tagIds ⊢
=======
      runtimeModuleOwn config.store.runtime.entry
        config.store.runtime.currentModule ⊢
>>>>>>> origin/main
        WP config.expr @ Stuckness.NotStuck; ⊤
          {{ values, ⌜φ values⌝ }}) :
    adequate Stuckness.NotStuck config.expr config.store
      (fun values _ => φ values) := by
  refine wp_adequacy (GF := WasmHeapGF α) Stuckness.NotStuck
    config.expr config.store φ ?_
  intro inv κs
  imod genHeap_init (L := MemoryKey) (V := Option UInt8)
      (GF := WasmHeapGF α) (H := WasmHeapMap) ∅ with
    ⟨%heapGS, Hheap, Hpoints, Hmeta⟩
  letI globalMapG : GhostMapG (WasmHeapGF α) GlobalKey Value WasmGlobalMap := by
    constructor
    exists 7
  imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := GlobalKey)
      (V := Value) (H := WasmGlobalMap)) with ⟨%globalName, Hglobals⟩
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
  letI exceptionMapG :
      GhostMapG (WasmHeapGF α) Nat (Nat × List Value) WasmExceptionMap := by
    constructor
    exists 13
  imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := Nat)
      (V := Nat × List Value) (H := WasmExceptionMap)) with
    ⟨%exceptionName, Hexceptions⟩
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
<<<<<<< HEAD
  letI wasmExceptionGS : WasmExceptionGS α :=
    { toGhostMapG := exceptionMapG
      exceptionName := exceptionName }
  letI runtimeElem :
      ElemG (WasmHeapGF α) (constOF (Agree (DiscreteO Module))) := by
=======
  letI runtimeModuleMapG : GhostMapG (WasmHeapGF α) Nat Module WasmRuntimeModuleMap := by
    constructor
>>>>>>> origin/main
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
<<<<<<< HEAD
  letI tagTableElem : ElemG (WasmHeapGF α)
      (constOF (Agree (DiscreteO (List Nat)))) := by
    exists 14
  let tagTableValue : Agree (DiscreteO (List Nat)) :=
    toAgree ⟨config.store.wasm.tagIds⟩
  imod (iOwn_alloc (E := tagTableElem)
      (tagTableValue • tagTableValue) (fun n =>
        CMRA.valid_iff_validN.mp
          (toAgree_op_valid_iff_eq.mpr rfl) n)) with
    ⟨%tagTableName, HtagTableBoth⟩
  letI tagTableGS : WasmTagTableGS α :=
    { tagTableElem
      tagTableName }
  letI hostElem : ElemG (WasmHeapGF α)
      (ExclAuth.ExclAuthURF (constOF (DiscreteO α))) := by
=======
  letI hostEnvMapG : GhostMapG (WasmHeapGF α) Nat (HostEnv α) WasmHostEnvMap := by
    constructor
>>>>>>> origin/main
    exists 12
  imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := Nat)
      (V := HostEnv α) (H := WasmHostEnvMap)) with ⟨%hostEnvName, HhostEnvAuth⟩
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
  iclear HhostStateFrag
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
  letI gs : WasmSmallStepGS .hasLC α :=
    { toInvGS_gen := inv
      toWasmHeapGS := wasmHeapGS
      global := wasmGlobalGS
      dataSegment := wasmDataSegmentGS
      table := wasmTableGS
      elementSegment := wasmElementSegmentGS
      exception := wasmExceptionGS
      runtime := runtimeGS
<<<<<<< HEAD
      tagTable := tagTableGS
      host := hostGS }
  iclear Hpoints Hmeta
  ihave HruntimePair := iOwn_op.mp $$ Hruntime
  icases HruntimePair with ⟨HruntimeState, HruntimeWP⟩
  ihave HtagPair := iOwn_op.mp $$ HtagTableBoth
  icases HtagPair with ⟨HtagTable, HtagWP⟩
=======
      hostEnv := hostEnvGS
      hostState := hostStateGS
      instanceGS := instanceGS
      runtimeInstances := runtimeInstancesGS }
  iclear Hpoints Hmeta
>>>>>>> origin/main
  imodintro
  iexists (fun store _observations =>
    stateInterp (GF := WasmHeapGF α) store 0 [] 0)
  iexists (fun _ => iprop(True))
  dsimp only
<<<<<<< HEAD
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments Hexceptions HruntimeState HtagTable HhostState]
=======
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth' HruntimeInstances HinstanceState HhostEnvAuth HhostState]
>>>>>>> origin/main
  · iapply (stateInterp_eq config.store 0 [] 0).mpr
    iexists (∅ : WasmHeapMap (Option UInt8))
    iexists (∅ : WasmGlobalMap Value)
    iexists (∅ : WasmDataSegmentMap (Option (List UInt8)))
    iexists (∅ : WasmTableMap TableInst)
    iexists (∅ : WasmElementSegmentMap (Option (List (Option Nat))))
<<<<<<< HEAD
    iexists (∅ : WasmExceptionMap (Nat × List Value))
    unfold runtimeInterp runtimeModuleOwn tagTableOwn
    unfold hostStateAuth
    iframe Hheap Hglobals Hsegments Htables HelementSegments Hexceptions HruntimeState HhostState
    isplitl [HtagTable]
    · iexists config.store.wasm.tagIds
      isplitl [HtagTable]
      · iexact HtagTable
      · ipureintro
        exact List.prefix_rfl
=======
    iexists (PartialMap.singleton config.store.runtime.entry.id
      config.store.runtime.currentModule)
    iexists (∅ : WasmHostEnvMap (HostEnv α))
    unfold runtimeModuleElem runtimeInstancesOwn hostStateAuth currentInstanceAuth currentInstanceAuthN
    simp only [BI.BigSepM.bigSepM_singleton.to_eq]
    iframe Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth' # HruntimeInstances HinstanceState HhostEnvAuth HhostState
>>>>>>> origin/main
    ipureintro
    exact ⟨heapAgreesWithMem_empty _,
      heapAddressesInBounds_empty _,
      globalHeapAgrees_empty _,
      dataSegmentHeapAgrees_empty _,
<<<<<<< HEAD
      ⟨tableHeapAgrees_empty _, elementSegmentHeapAgrees_empty _,
        exceptionHeapAgrees_empty _⟩⟩
  · iapply hwp
    unfold runtimeModuleOwn tagTableOwn
    isplitl [HruntimeWP]
    · iexact HruntimeWP
    · iexact HtagWP

/-- Call-capable runtime adequacy without tag knowledge: the exception-free
entry point used by every generated specification. -/
theorem wasm_smallStep_runtime_adequacy
    [WasmSmallStepGpreS α]
    (config : Config α) (φ : List Value → Prop)
    (hwp : ∀ [WasmSmallStepGS .hasLC α],
      runtimeModuleOwn config.store.runtime.module ⊢
        WP config.expr @ Stuckness.NotStuck; ⊤
          {{ values, ⌜φ values⌝ }}) :
    adequate Stuckness.NotStuck config.expr config.store
      (fun values _ => φ values) := by
  apply wasm_smallStep_runtime_tags_adequacy config φ
  intro _
  iintro ⟨Hruntime, Htags⟩
  iclear Htags
  iapply hwp
  iexact Hruntime
=======
      tableHeapAgrees_empty _,
      elementSegmentHeapAgrees_empty _,
      fun id m hm => by
        by_cases h : id = config.store.runtime.entry.id
        · subst h; simp [PartialMap.singleton, get?_insert_eq rfl] at hm; subst hm
          rw [Array.getElem?_eq_getElem hwf]
          simp [RuntimeEnv.currentModule, RuntimeEnv.currentInstance]
          rw [getElem!_pos config.store.runtime.instances config.store.runtime.entry.id hwf]
        · simp [PartialMap.singleton, get?_insert_ne (Ne.symm h), get?_empty] at hm,
      fun id env hm => by simp [get?_empty] at hm⟩
  · iapply hwp
    unfold runtimeModuleOwn
    isplitl [HruntimeWP]
    · unfold runtimeModuleElem; iexact HruntimeWP
    · unfold currentInstanceOwnN; iexact HinstanceFrag
>>>>>>> origin/main

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

/-- Runtime adequacy with `hostEnvOwn` and `hostStateOwn` forwarded to the WP
proof, enabling host-state ghost updates via ExclAuth. -/
theorem wasm_smallStep_runtime_host_store_adequacy
    [WasmSmallStepGpreS α]
    (config : Config α) (φ : List Value → Prop)
    (hwf : config.store.runtime.entry.id < config.store.runtime.instances.size)
    (hwp : ∀ [WasmSmallStepGS .hasLC α],
      runtimeModuleOwn config.store.runtime.entry
          config.store.runtime.currentModule ∗
        hostEnvOwn config.store.runtime.entry.id config.store.runtime.currentHost ∗
        hostStateOwn config.store.wasm.host ⊢
        WP config.expr @ Stuckness.NotStuck; ⊤
          {{ values, ⌜φ values⌝ }}) :
    adequate Stuckness.NotStuck config.expr config.store
      (fun values _ => φ values) := by
  refine wp_adequacy (GF := WasmHeapGF α) Stuckness.NotStuck
    config.expr config.store φ ?_
  intro inv κs
  imod genHeap_init (L := MemoryKey) (V := Option UInt8)
      (GF := WasmHeapGF α) (H := WasmHeapMap) ∅ with
    ⟨%heapGS, Hheap, Hpoints, Hmeta⟩
  letI globalMapG : GhostMapG (WasmHeapGF α) GlobalKey Value WasmGlobalMap := by
    constructor
    exists 7
  imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := GlobalKey)
      (V := Value) (H := WasmGlobalMap)) with ⟨%globalName, Hglobals⟩
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
  letI gs : WasmSmallStepGS .hasLC α :=
    { toInvGS_gen := inv
      toWasmHeapGS := wasmHeapGS
      global := wasmGlobalGS
      dataSegment := wasmDataSegmentGS
      table := wasmTableGS
      elementSegment := wasmElementSegmentGS
      runtime := runtimeGS
      hostEnv := hostEnvGS
      hostState := hostStateGS
      instanceGS := instanceGS
      runtimeInstances := runtimeInstancesGS }
  iclear Hpoints Hmeta
  imodintro
  iexists (fun store _observations =>
    stateInterp (GF := WasmHeapGF α) store 0 [] 0)
  iexists (fun _ => iprop(True))
  dsimp only
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth' HruntimeInstances HinstanceState HhostEnvAuth' HhostState]
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
    iframe Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth' # HruntimeInstances HinstanceState HhostEnvAuth' HhostState
    ipureintro
    exact ⟨heapAgreesWithMem_empty _,
      heapAddressesInBounds_empty _,
      globalHeapAgrees_empty _,
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
          simp [RuntimeEnv.currentHost, RuntimeEnv.currentInstance,
            getElem!_pos config.store.runtime.instances config.store.runtime.entry.id hwf]
        · simp [PartialMap.singleton, get?_insert_ne (Ne.symm h), get?_empty] at hm⟩
  · iapply hwp
    isplitl [HruntimeWP HinstanceFrag]
    · unfold runtimeModuleOwn
      isplitl [HruntimeWP]
      · unfold runtimeModuleElem; iexact HruntimeWP
      · unfold currentInstanceOwnN; iexact HinstanceFrag
    · isplitl [HhostEnvWP]
      · unfold hostEnvOwn; iexact HhostEnvWP
      · unfold hostStateOwn; iexact HhostStateFrag

theorem wasm_smallStep_runtime_host_store_partiallyMeets
    [WasmSmallStepGpreS α]
    (config : Config α) (φ : List Value → Prop)
    (hwf : config.store.runtime.entry.id < config.store.runtime.instances.size)
    (hwp : ∀ [WasmSmallStepGS .hasLC α],
      runtimeModuleOwn config.store.runtime.entry
          config.store.runtime.currentModule ∗
        hostEnvOwn config.store.runtime.entry.id config.store.runtime.currentHost ∗
        hostStateOwn config.store.wasm.host ⊢
        WP config.expr @ Stuckness.NotStuck; ⊤
          {{ values, ⌜φ values⌝ }}) :
    PartiallyMeets config (fun values _store => φ values) :=
  adequate_to_partiallyMeets config (fun values _store => φ values)
    (wasm_smallStep_runtime_host_store_adequacy config φ hwf hwp)

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
  imod genHeap_init (L := MemoryKey) (V := Option UInt8)
      (GF := WasmHeapGF α) (H := WasmHeapMap) ∅ with
    ⟨%heapGS, Hheap, Hpoints, Hmeta⟩
  letI globalMapG : GhostMapG (WasmHeapGF α) GlobalKey Value WasmGlobalMap := by
    constructor
    exists 7
  imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := GlobalKey)
      (V := Value) (H := WasmGlobalMap)) with ⟨%globalName, Hglobals⟩
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
  iclear HhostStateFrag
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
  letI gs : WasmSmallStepGS .hasLC α :=
    { toInvGS_gen := inv
      toWasmHeapGS := wasmHeapGS
      global := wasmGlobalGS
      dataSegment := wasmDataSegmentGS
      table := wasmTableGS
      elementSegment := wasmElementSegmentGS
      runtime := runtimeGS
      hostEnv := hostEnvGS
      hostState := hostStateGS
      instanceGS := instanceGS
      runtimeInstances := runtimeInstancesGS }
  iclear Hpoints Hmeta
  ihave HruntimeInstancesPair := iOwn_op.mp $$ HruntimeInstances
  icases HruntimeInstancesPair with ⟨HruntimeInstancesState, HruntimeInstancesWP⟩
  imodintro
  iexists (fun store _observations =>
    stateInterp (GF := WasmHeapGF α) store 0 [] 0)
  iexists (fun _ => iprop(True))
  dsimp only
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth' HruntimeInstancesState HinstanceState HhostEnvAuth HhostState]
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
    iframe Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth' # HruntimeInstancesState HinstanceState HhostEnvAuth HhostState
    ipureintro
    exact ⟨heapAgreesWithMem_empty _,
      heapAddressesInBounds_empty _,
      globalHeapAgrees_empty _,
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
  imod genHeap_init (L := MemoryKey) (V := Option UInt8)
      (GF := WasmHeapGF α) (H := WasmHeapMap) ∅ with
    ⟨%heapGS, Hheap, Hpoints, Hmeta⟩
  letI globalMapG : GhostMapG (WasmHeapGF α) GlobalKey Value WasmGlobalMap := by
    constructor
    exists 7
  imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := GlobalKey)
      (V := Value) (H := WasmGlobalMap)) with ⟨%globalName, Hglobals⟩
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
  letI gs : WasmSmallStepGS .hasLC α :=
    { toInvGS_gen := inv
      toWasmHeapGS := wasmHeapGS
      global := wasmGlobalGS
      dataSegment := wasmDataSegmentGS
      table := wasmTableGS
      elementSegment := wasmElementSegmentGS
      runtime := runtimeGS
      hostEnv := hostEnvGS
      hostState := hostStateGS
      instanceGS := instanceGS
      runtimeInstances := runtimeInstancesGS }
  iclear Hpoints Hmeta
  ihave HruntimeInstancesPair := iOwn_op.mp $$ HruntimeInstances
  icases HruntimeInstancesPair with ⟨HruntimeInstancesState, HruntimeInstancesWP⟩
  imodintro
  iexists (fun store _observations =>
    stateInterp (GF := WasmHeapGF α) store 0 [] 0)
  iexists (fun _ => iprop(True))
  dsimp only
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth' HruntimeInstancesState HinstanceState HhostEnvAuth' HhostState]
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
    iframe Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth' # HruntimeInstancesState HinstanceState HhostEnvAuth' HhostState
    ipureintro
    exact ⟨heapAgreesWithMem_empty _,
      heapAddressesInBounds_empty _,
      globalHeapAgrees_empty _,
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
  imod genHeap_init (L := MemoryKey) (V := Option UInt8)
      (GF := WasmHeapGF α) (H := WasmHeapMap) σ with
    ⟨%heapGS, Hheap, Hpoints, Hmeta⟩
  letI globalMapG : GhostMapG (WasmHeapGF α) GlobalKey Value WasmGlobalMap := by
    constructor
    exists 7
  imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := GlobalKey)
      (V := Value) (H := WasmGlobalMap)) with ⟨%globalName, Hglobals⟩
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
  letI exceptionMapG :
      GhostMapG (WasmHeapGF α) Nat (Nat × List Value) WasmExceptionMap := by
    constructor
    exists 13
  imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := Nat)
      (V := Nat × List Value) (H := WasmExceptionMap)) with
    ⟨%exceptionName, Hexceptions⟩
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
<<<<<<< HEAD
  letI wasmExceptionGS : WasmExceptionGS α :=
    { toGhostMapG := exceptionMapG
      exceptionName := exceptionName }
  letI runtimeElem :
      ElemG (WasmHeapGF α) (constOF (Agree (DiscreteO Module))) := by
=======
  letI runtimeModuleMapG : GhostMapG (WasmHeapGF α) Nat Module WasmRuntimeModuleMap := by
    constructor
>>>>>>> origin/main
    exists 8
  imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := Nat)
      (V := Module) (H := WasmRuntimeModuleMap)) with ⟨%runtimeName, HruntimeModuleAuth⟩
  letI runtimeGS : WasmRuntimeModuleGS α :=
    { toGhostMapG := runtimeModuleMapG
      runtimeName }
<<<<<<< HEAD
  letI tagTableElem : ElemG (WasmHeapGF α)
      (constOF (Agree (DiscreteO (List Nat)))) := by
    exists 14
  imod (iOwn_alloc (E := tagTableElem)
      (toAgree ⟨config.store.wasm.tagIds⟩) (fun _ => trivial)) with
    ⟨%tagTableName, HtagTable⟩
  letI tagTableGS : WasmTagTableGS α :=
    { tagTableElem
      tagTableName }
  letI hostElem : ElemG (WasmHeapGF α)
      (ExclAuth.ExclAuthURF (constOF (DiscreteO α))) := by
=======
  letI hostEnvMapG : GhostMapG (WasmHeapGF α) Nat (HostEnv α) WasmHostEnvMap := by
    constructor
>>>>>>> origin/main
    exists 12
  imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := Nat)
      (V := HostEnv α) (H := WasmHostEnvMap)) with ⟨%hostEnvName, HhostEnvAuth⟩
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
  iclear HhostStateFrag
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
  iclear HinstanceFrag
  letI runtimeInstancesElem :
      ElemG (WasmHeapGF α) (constOF (Agree (DiscreteO (Array (ModuleInstance α))))) := by
    exists 15
  imod (iOwn_alloc (E := runtimeInstancesElem)
      (toAgree ⟨config.store.runtime.instances⟩) (fun _ => trivial)) with
    ⟨%runtimeInstancesName, HruntimeInstances⟩
  letI runtimeInstancesGS : WasmRuntimeInstancesGS α :=
    { runtimeInstancesElem
      runtimeInstancesName }
  letI gs : WasmSmallStepGS .hasLC α :=
    { toInvGS_gen := inv
      toWasmHeapGS := wasmHeapGS
      global := wasmGlobalGS
      dataSegment := wasmDataSegmentGS
      table := wasmTableGS
      elementSegment := wasmElementSegmentGS
      exception := wasmExceptionGS
      runtime := runtimeGS
<<<<<<< HEAD
      tagTable := tagTableGS
      host := hostGS }
=======
      hostEnv := hostEnvGS
      hostState := hostStateGS
      instanceGS := instanceGS
      runtimeInstances := runtimeInstancesGS }
>>>>>>> origin/main
  iclear Hmeta
  imodintro
  iexists (fun store _observations =>
    stateInterp (GF := WasmHeapGF α) store 0 [] 0)
  iexists (fun _ => iprop(True))
  dsimp only
<<<<<<< HEAD
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments Hexceptions Hruntime HtagTable HhostState]
=======
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeInstances HinstanceState HhostEnvAuth HhostState]
>>>>>>> origin/main
  · iapply (stateInterp_eq config.store 0 [] 0).mpr
    iexists σ
    iexists (∅ : WasmGlobalMap Value)
    iexists (∅ : WasmDataSegmentMap (Option (List UInt8)))
    iexists (∅ : WasmTableMap TableInst)
    iexists (∅ : WasmElementSegmentMap (Option (List (Option Nat))))
<<<<<<< HEAD
    iexists (∅ : WasmExceptionMap (Nat × List Value))
    unfold runtimeInterp runtimeModuleOwn tagTableOwn
    unfold hostStateAuth
    iframe Hheap Hglobals Hsegments Htables HelementSegments Hexceptions Hruntime HhostState
    isplitl [HtagTable]
    · iexists config.store.wasm.tagIds
      isplitl [HtagTable]
      · iexact HtagTable
      · ipureintro
        exact List.prefix_rfl
=======
    iexists (∅ : WasmRuntimeModuleMap Module)
    iexists (∅ : WasmHostEnvMap (HostEnv α))
    unfold runtimeModuleElem runtimeInstancesOwn hostStateAuth currentInstanceAuth currentInstanceAuthN
    simp only [BI.BigSepM.bigSepM_empty.to_eq, BI.emp_sep.to_eq]
    iframe Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeInstances HinstanceState HhostEnvAuth HhostState
>>>>>>> origin/main
    ipureintro
    exact ⟨hagree, hinBounds,
      globalHeapAgrees_empty _,
      dataSegmentHeapAgrees_empty _,
<<<<<<< HEAD
      ⟨tableHeapAgrees_empty _, elementSegmentHeapAgrees_empty _,
        exceptionHeapAgrees_empty _⟩⟩
=======
      tableHeapAgrees_empty _,
      elementSegmentHeapAgrees_empty _,
      fun id m hm => by simp [get?_empty] at hm,
      fun id env hm => by simp [get?_empty] at hm⟩
>>>>>>> origin/main
  · iapply hwp
    iexact Hpoints

theorem wasm_smallStep_heap_terminates
    [WasmSmallStepGpreS α]
    (config : Config α) (σ : WasmHeapMap (Option UInt8))
    (φ : List Value → Prop)
    (hagree : heapAgreesWithMem σ config.store.wasm.mem)
    (hinBounds : heapAddressesInBounds σ config.store.wasm.mem)
    (htwp : ∀ (hlc : HasLC) [WasmSmallStepGS hlc α],
      ([∗map] address ↦ value ∈ σ,
        pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
          address (DFrac.own 1) value) ⊢
        WP config.expr @ Stuckness.NotStuck; ⊤
          [{ values, ⌜φ values⌝ }]) :
    TerminatesWith config (fun values _store => φ values) := by
  apply stronglyNormalizing_adequate_terminates config
    (fun values _store => φ values)
  · apply twp_total (hlc := .hasNoLC) (GF := WasmHeapGF α)
      Stuckness.NotStuck config.expr config.store
      (fun values => iprop(⌜φ values⌝)) 0 0
    intro inv
    imod genHeap_init (L := UInt32) (V := Option UInt8)
        (GF := WasmHeapGF α) (H := WasmHeapMap) σ with
      ⟨%heapGS, Hheap, Hpoints, Hmeta⟩
    letI globalMapG : GhostMapG (WasmHeapGF α) Nat Value WasmGlobalMap := by
      constructor
      exists 7
    imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := Nat)
        (V := Value) (H := WasmGlobalMap)) with ⟨%globalName, Hglobals⟩
    letI dataSegmentMapG :
        GhostMapG (WasmHeapGF α) Nat (Option (List UInt8))
          WasmDataSegmentMap := by
      constructor
      exists 9
    imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := Nat)
        (V := Option (List UInt8)) (H := WasmDataSegmentMap)) with
      ⟨%dataSegmentName, Hsegments⟩
    letI tableMapG : GhostMapG (WasmHeapGF α) Nat TableInst WasmTableMap := by
      constructor
      exists 10
    imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := Nat)
        (V := TableInst) (H := WasmTableMap)) with
      ⟨%tableName, Htables⟩
    letI elementSegmentMapG :
        GhostMapG (WasmHeapGF α) Nat (Option (List (Option Nat)))
          WasmElementSegmentMap := by
      constructor
      exists 11
    imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := Nat)
        (V := Option (List (Option Nat))) (H := WasmElementSegmentMap)) with
      ⟨%elementSegmentName, HelementSegments⟩
    letI exceptionMapG :
        GhostMapG (WasmHeapGF α) Nat (Nat × List Value) WasmExceptionMap := by
      constructor
      exists 13
    imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := Nat)
        (V := Nat × List Value) (H := WasmExceptionMap)) with
      ⟨%exceptionName, Hexceptions⟩
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
    letI wasmExceptionGS : WasmExceptionGS α :=
      { toGhostMapG := exceptionMapG
        exceptionName := exceptionName }
    letI runtimeElem :
        ElemG (WasmHeapGF α) (constOF (Agree (DiscreteO Module))) := by
      exists 8
    imod (iOwn_alloc (E := runtimeElem)
        (toAgree ⟨config.store.runtime.module⟩) (fun _ => trivial)) with
      ⟨%runtimeName, Hruntime⟩
    letI runtimeGS : WasmRuntimeModuleGS α :=
      { runtimeElem
        runtimeName }
    letI tagTableElem : ElemG (WasmHeapGF α)
        (constOF (Agree (DiscreteO (List Nat)))) := by
      exists 14
    imod (iOwn_alloc (E := tagTableElem)
        (toAgree ⟨config.store.wasm.tagIds⟩) (fun _ => trivial)) with
      ⟨%tagTableName, HtagTable⟩
    letI tagTableGS : WasmTagTableGS α :=
      { tagTableElem
        tagTableName }
    letI hostElem : ElemG (WasmHeapGF α)
        (ExclAuth.ExclAuthURF (constOF (DiscreteO α))) := by
      exists 12
    imod hostState_alloc (elem := hostElem) config.store.wasm.host with
      ⟨%hostName, HhostState, HhostOwn⟩
    letI hostGS : WasmHostGS α :=
      { hostElem
        hostName }
    iclear HhostOwn
    letI gs : WasmSmallStepGS .hasNoLC α :=
      { toInvGS_gen := inv
        toWasmHeapGS := wasmHeapGS
        global := wasmGlobalGS
        dataSegment := wasmDataSegmentGS
        table := wasmTableGS
        elementSegment := wasmElementSegmentGS
        exception := wasmExceptionGS
        runtime := runtimeGS
        tagTable := tagTableGS
        host := hostGS }
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
    isplitl [Hheap Hglobals Hsegments Htables HelementSegments Hexceptions Hruntime HtagTable HhostState]
    · iapply (stateInterp_eq config.store 0 [] 0).mpr
      iexists σ
      iexists (∅ : WasmGlobalMap Value)
      iexists (∅ : WasmDataSegmentMap (Option (List UInt8)))
      iexists (∅ : WasmTableMap TableInst)
      iexists (∅ : WasmElementSegmentMap (Option (List (Option Nat))))
      iexists (∅ : WasmExceptionMap (Nat × List Value))
      unfold runtimeInterp runtimeModuleOwn tagTableOwn
      unfold hostStateAuth
      iframe Hheap Hglobals Hsegments Htables HelementSegments Hexceptions Hruntime HhostState
      isplitl [HtagTable]
      · iexists config.store.wasm.tagIds
        isplitl [HtagTable]
        · iexact HtagTable
        · ipureintro
          exact List.prefix_rfl
      ipureintro
      exact ⟨hagree, hinBounds,
        globalHeapAgrees_empty _,
        dataSegmentHeapAgrees_empty _,
        ⟨tableHeapAgrees_empty _, elementSegmentHeapAgrees_empty _,
          exceptionHeapAgrees_empty _⟩⟩
    · iintro _
      iapply htwp .hasNoLC
      iexact Hpoints
  · exact wasm_smallStep_heap_adequacy config σ φ hagree hinBounds
      (fun [_] => by
        iintro Hpoints
        iapply twp.to_wp
        iapply htwp .hasLC
        iexact Hpoints)

/-- Total-correctness form of `wasm_smallStep_runtime_adequacy`. The TWP proof
provides strong normalization (via `twp_total` with `hasNoLC`) and the
postcondition (via `twp.to_wp` with `hasLC`). Runtime-module ownership is
required for both passes. -/
theorem wasm_smallStep_runtime_tags_terminates
    [WasmSmallStepGpreS α]
    (config : Config α) (φ : List Value → Prop)
    (htwp : ∀ (hlc : HasLC) [WasmSmallStepGS hlc α],
      runtimeModuleOwn config.store.runtime.module ∗
          tagTableOwn config.store.wasm.tagIds ⊢
        WP config.expr @ Stuckness.NotStuck; ⊤
          [{ values, ⌜φ values⌝ }]) :
    TerminatesWith config (fun values _store => φ values) := by
  apply stronglyNormalizing_adequate_terminates config
    (fun values _store => φ values)
  · apply twp_total (hlc := .hasNoLC) (GF := WasmHeapGF α)
      Stuckness.NotStuck config.expr config.store
      (fun values => iprop(⌜φ values⌝)) 0 0
    intro inv
    imod genHeap_init (L := UInt32) (V := Option UInt8)
        (GF := WasmHeapGF α) (H := WasmHeapMap) ∅ with
      ⟨%heapGS, Hheap, Hpoints, Hmeta⟩
    letI globalMapG : GhostMapG (WasmHeapGF α) Nat Value WasmGlobalMap := by
      constructor
      exists 7
    imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := Nat)
        (V := Value) (H := WasmGlobalMap)) with ⟨%globalName, Hglobals⟩
    letI dataSegmentMapG :
        GhostMapG (WasmHeapGF α) Nat (Option (List UInt8))
          WasmDataSegmentMap := by
      constructor
      exists 9
    imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := Nat)
        (V := Option (List UInt8)) (H := WasmDataSegmentMap)) with
      ⟨%dataSegmentName, Hsegments⟩
    letI tableMapG : GhostMapG (WasmHeapGF α) Nat TableInst WasmTableMap := by
      constructor
      exists 10
    imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := Nat)
        (V := TableInst) (H := WasmTableMap)) with
      ⟨%tableName, Htables⟩
    letI elementSegmentMapG :
        GhostMapG (WasmHeapGF α) Nat (Option (List (Option Nat)))
          WasmElementSegmentMap := by
      constructor
      exists 11
    imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := Nat)
        (V := Option (List (Option Nat))) (H := WasmElementSegmentMap)) with
      ⟨%elementSegmentName, HelementSegments⟩
    letI exceptionMapG :
        GhostMapG (WasmHeapGF α) Nat (Nat × List Value) WasmExceptionMap := by
      constructor
      exists 13
    imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := Nat)
        (V := Nat × List Value) (H := WasmExceptionMap)) with
      ⟨%exceptionName, Hexceptions⟩
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
    letI wasmExceptionGS : WasmExceptionGS α :=
      { toGhostMapG := exceptionMapG
        exceptionName := exceptionName }
    letI runtimeElem :
        ElemG (WasmHeapGF α) (constOF (Agree (DiscreteO Module))) := by
      exists 8
    let runtimeValue : Agree (DiscreteO Module) :=
      toAgree ⟨config.store.runtime.module⟩
    imod (iOwn_alloc (E := runtimeElem)
        (runtimeValue • runtimeValue) (fun n =>
          CMRA.valid_iff_validN.mp
            (toAgree_op_valid_iff_eq.mpr rfl) n)) with
      ⟨%runtimeName, Hruntime⟩
    letI runtimeGS : WasmRuntimeModuleGS α :=
      { runtimeElem
        runtimeName }
    letI tagTableElem : ElemG (WasmHeapGF α)
        (constOF (Agree (DiscreteO (List Nat)))) := by
      exists 14
    let tagTableValue : Agree (DiscreteO (List Nat)) :=
      toAgree ⟨config.store.wasm.tagIds⟩
    imod (iOwn_alloc (E := tagTableElem)
        (tagTableValue • tagTableValue) (fun n =>
          CMRA.valid_iff_validN.mp
            (toAgree_op_valid_iff_eq.mpr rfl) n)) with
      ⟨%tagTableName, HtagTableBoth⟩
    letI tagTableGS : WasmTagTableGS α :=
      { tagTableElem
        tagTableName }
    letI hostElem : ElemG (WasmHeapGF α)
        (ExclAuth.ExclAuthURF (constOF (DiscreteO α))) := by
      exists 12
    imod hostState_alloc (elem := hostElem) config.store.wasm.host with
      ⟨%hostName, HhostState, HhostOwn⟩
    letI hostGS : WasmHostGS α :=
      { hostElem
        hostName }
    iclear HhostOwn
    letI gs : WasmSmallStepGS .hasNoLC α :=
      { toInvGS_gen := inv
        toWasmHeapGS := wasmHeapGS
        global := wasmGlobalGS
        dataSegment := wasmDataSegmentGS
        table := wasmTableGS
        elementSegment := wasmElementSegmentGS
        exception := wasmExceptionGS
        runtime := runtimeGS
        tagTable := tagTableGS
        host := hostGS }
    iclear Hmeta Hpoints
    ihave HruntimePair := iOwn_op.mp $$ Hruntime
    icases HruntimePair with ⟨HruntimeState, HruntimeTWP⟩
    ihave HtagPair := iOwn_op.mp $$ HtagTableBoth
    icases HtagPair with ⟨HtagTable, HtagTWP⟩
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
    isplitl [Hheap Hglobals Hsegments Htables HelementSegments Hexceptions HruntimeState HtagTable HhostState]
    · iapply (stateInterp_eq config.store 0 [] 0).mpr
      iexists (∅ : WasmHeapMap (Option UInt8))
      iexists (∅ : WasmGlobalMap Value)
      iexists (∅ : WasmDataSegmentMap (Option (List UInt8)))
      iexists (∅ : WasmTableMap TableInst)
      iexists (∅ : WasmElementSegmentMap (Option (List (Option Nat))))
      iexists (∅ : WasmExceptionMap (Nat × List Value))
      unfold runtimeInterp runtimeModuleOwn tagTableOwn
      unfold hostStateAuth
      iframe Hheap Hglobals Hsegments Htables HelementSegments Hexceptions HruntimeState HhostState
      isplitl [HtagTable]
      · iexists config.store.wasm.tagIds
        isplitl [HtagTable]
        · iexact HtagTable
        · ipureintro
          exact List.prefix_rfl
      ipureintro
      exact ⟨heapAgreesWithMem_empty _,
        heapAddressesInBounds_empty _,
        globalHeapAgrees_empty _,
        dataSegmentHeapAgrees_empty _,
        ⟨tableHeapAgrees_empty _, elementSegmentHeapAgrees_empty _,
          exceptionHeapAgrees_empty _⟩⟩
    · iintro _
      iapply htwp .hasNoLC
      unfold runtimeModuleOwn tagTableOwn
      isplitl [HruntimeTWP]
      · iexact HruntimeTWP
      · iexact HtagTWP
  · exact wasm_smallStep_runtime_tags_adequacy config φ
      (fun [_] => by
        iintro Hboth
        iapply twp.to_wp
        iapply htwp .hasLC
        iexact Hboth)

/-- Total-correctness runtime entry point without tag knowledge. -/
theorem wasm_smallStep_runtime_terminates
    [WasmSmallStepGpreS α]
    (config : Config α) (φ : List Value → Prop)
    (htwp : ∀ (hlc : HasLC) [WasmSmallStepGS hlc α],
      runtimeModuleOwn config.store.runtime.module ⊢
        WP config.expr @ Stuckness.NotStuck; ⊤
          [{ values, ⌜φ values⌝ }]) :
    TerminatesWith config (fun values _store => φ values) := by
  apply wasm_smallStep_runtime_tags_terminates config φ
  intro hlc _
  iintro ⟨Hruntime, Htags⟩
  iclear Htags
  iapply htwp hlc
  iexact Hruntime

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
  imod genHeap_init (L := MemoryKey) (V := Option UInt8)
      (GF := WasmHeapGF α) (H := WasmHeapMap) σ with
    ⟨%heapGS, Hheap, Hpoints, Hmeta⟩
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
  letI exceptionMapG :
      GhostMapG (WasmHeapGF α) Nat (Nat × List Value) WasmExceptionMap := by
    constructor
    exists 13
  imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := Nat)
      (V := Nat × List Value) (H := WasmExceptionMap)) with
    ⟨%exceptionName, Hexceptions⟩
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
<<<<<<< HEAD
  letI wasmExceptionGS : WasmExceptionGS α :=
    { toGhostMapG := exceptionMapG
      exceptionName := exceptionName }
  letI runtimeElem :
      ElemG (WasmHeapGF α) (constOF (Agree (DiscreteO Module))) := by
=======
  letI runtimeModuleMapG : GhostMapG (WasmHeapGF α) Nat Module WasmRuntimeModuleMap := by
    constructor
>>>>>>> origin/main
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
<<<<<<< HEAD
  letI tagTableElem : ElemG (WasmHeapGF α)
      (constOF (Agree (DiscreteO (List Nat)))) := by
    exists 14
  imod (iOwn_alloc (E := tagTableElem)
      (toAgree ⟨config.store.wasm.tagIds⟩) (fun _ => trivial)) with
    ⟨%tagTableName, HtagTable⟩
  letI tagTableGS : WasmTagTableGS α :=
    { tagTableElem
      tagTableName }
  letI hostElem : ElemG (WasmHeapGF α)
      (ExclAuth.ExclAuthURF (constOF (DiscreteO α))) := by
=======
  letI hostEnvMapG : GhostMapG (WasmHeapGF α) Nat (HostEnv α) WasmHostEnvMap := by
    constructor
>>>>>>> origin/main
    exists 12
  imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := Nat)
      (V := HostEnv α) (H := WasmHostEnvMap)) with ⟨%hostEnvName, HhostEnvAuth⟩
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
  iclear HhostStateFrag
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
  letI gs : WasmSmallStepGS .hasLC α :=
    { toInvGS_gen := inv
      toWasmHeapGS := wasmHeapGS
      global := wasmGlobalGS
      dataSegment := wasmDataSegmentGS
      table := wasmTableGS
      elementSegment := wasmElementSegmentGS
      exception := wasmExceptionGS
      runtime := runtimeGS
<<<<<<< HEAD
      tagTable := tagTableGS
      host := hostGS }
=======
      hostEnv := hostEnvGS
      hostState := hostStateGS
      instanceGS := instanceGS
      runtimeInstances := runtimeInstancesGS }
>>>>>>> origin/main
  iclear Hmeta
  imodintro
  iexists (fun store _observations =>
    stateInterp (GF := WasmHeapGF α) store 0 [] 0)
  iexists (fun _ => iprop(True))
  dsimp only
<<<<<<< HEAD
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments Hexceptions HruntimeState HtagTable HhostState]
=======
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth' HruntimeInstances HinstanceState HhostEnvAuth HhostState]
>>>>>>> origin/main
  · iapply (stateInterp_eq config.store 0 [] 0).mpr
    iexists σ
    iexists globalσ
    iexists (∅ : WasmDataSegmentMap (Option (List UInt8)))
    iexists (∅ : WasmTableMap TableInst)
    iexists (∅ : WasmElementSegmentMap (Option (List (Option Nat))))
<<<<<<< HEAD
    iexists (∅ : WasmExceptionMap (Nat × List Value))
    unfold runtimeInterp runtimeModuleOwn tagTableOwn
    unfold hostStateAuth
    iframe Hheap Hglobals Hsegments Htables HelementSegments Hexceptions HruntimeState HhostState
    isplitl [HtagTable]
    · iexists config.store.wasm.tagIds
      isplitl [HtagTable]
      · iexact HtagTable
      · ipureintro
        exact List.prefix_rfl
    ipureintro
    exact ⟨hagree, hinBounds, hglobals,
      dataSegmentHeapAgrees_empty _,
      ⟨tableHeapAgrees_empty _, elementSegmentHeapAgrees_empty _,
        exceptionHeapAgrees_empty _⟩⟩
=======
    iexists (PartialMap.singleton config.store.runtime.entry.id
      config.store.runtime.currentModule)
    iexists (∅ : WasmHostEnvMap (HostEnv α))
    unfold runtimeModuleElem runtimeInstancesOwn hostStateAuth currentInstanceAuth currentInstanceAuthN
    simp only [BI.BigSepM.bigSepM_singleton.to_eq]
    iframe Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth' # HruntimeInstances HinstanceState HhostEnvAuth HhostState
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
      fun id env hm => by simp [get?_empty] at hm⟩
>>>>>>> origin/main
  · iapply hwp
    isplitl [Hpoints]
    · iexact Hpoints
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
  imod genHeap_init (L := MemoryKey) (V := Option UInt8)
      (GF := WasmHeapGF α) (H := WasmHeapMap) σ with
    ⟨%heapGS, Hheap, Hpoints, Hmeta⟩
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
  letI exceptionMapG :
      GhostMapG (WasmHeapGF α) Nat (Nat × List Value) WasmExceptionMap := by
    constructor
    exists 13
  imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := Nat)
      (V := Nat × List Value) (H := WasmExceptionMap)) with
    ⟨%exceptionName, Hexceptions⟩
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
<<<<<<< HEAD
  letI wasmExceptionGS : WasmExceptionGS α :=
    { toGhostMapG := exceptionMapG
      exceptionName := exceptionName }
  letI runtimeElem :
      ElemG (WasmHeapGF α) (constOF (Agree (DiscreteO Module))) := by
=======
  letI runtimeModuleMapG : GhostMapG (WasmHeapGF α) Nat Module WasmRuntimeModuleMap := by
    constructor
>>>>>>> origin/main
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
<<<<<<< HEAD
  letI tagTableElem : ElemG (WasmHeapGF α)
      (constOF (Agree (DiscreteO (List Nat)))) := by
    exists 14
  imod (iOwn_alloc (E := tagTableElem)
      (toAgree ⟨config.store.wasm.tagIds⟩) (fun _ => trivial)) with
    ⟨%tagTableName, HtagTable⟩
  letI tagTableGS : WasmTagTableGS α :=
    { tagTableElem
      tagTableName }
  letI hostElem : ElemG (WasmHeapGF α)
      (ExclAuth.ExclAuthURF (constOF (DiscreteO α))) := by
=======
  letI hostEnvMapG : GhostMapG (WasmHeapGF α) Nat (HostEnv α) WasmHostEnvMap := by
    constructor
>>>>>>> origin/main
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
  iclear HhostStateFrag
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
  letI gs : WasmSmallStepGS .hasLC α :=
    { toInvGS_gen := inv
      toWasmHeapGS := wasmHeapGS
      global := wasmGlobalGS
      dataSegment := wasmDataSegmentGS
      table := wasmTableGS
      elementSegment := wasmElementSegmentGS
      exception := wasmExceptionGS
      runtime := runtimeGS
<<<<<<< HEAD
      tagTable := tagTableGS
      host := hostGS }
=======
      hostEnv := hostEnvGS
      hostState := hostStateGS
      instanceGS := instanceGS
      runtimeInstances := runtimeInstancesGS }
>>>>>>> origin/main
  iclear Hmeta
  imodintro
  iexists (fun store _observations =>
    stateInterp (GF := WasmHeapGF α) store 0 [] 0)
  iexists (fun _ => iprop(True))
  dsimp only
<<<<<<< HEAD
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments Hexceptions HruntimeState HtagTable HhostState]
=======
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth' HruntimeInstances HinstanceState HhostEnvAuth' HhostState]
>>>>>>> origin/main
  · iapply (stateInterp_eq config.store 0 [] 0).mpr
    iexists σ
    iexists globalσ
    iexists (∅ : WasmDataSegmentMap (Option (List UInt8)))
    iexists (∅ : WasmTableMap TableInst)
    iexists (∅ : WasmElementSegmentMap (Option (List (Option Nat))))
<<<<<<< HEAD
    iexists (∅ : WasmExceptionMap (Nat × List Value))
    unfold runtimeInterp runtimeModuleOwn tagTableOwn
    unfold hostStateAuth
    iframe Hheap Hglobals Hsegments Htables HelementSegments Hexceptions HruntimeState HhostState
    isplitl [HtagTable]
    · iexists config.store.wasm.tagIds
      isplitl [HtagTable]
      · iexact HtagTable
      · ipureintro
        exact List.prefix_rfl
    ipureintro
    exact ⟨hagree, hinBounds, hglobals,
      dataSegmentHeapAgrees_empty _,
      ⟨tableHeapAgrees_empty _, elementSegmentHeapAgrees_empty _,
        exceptionHeapAgrees_empty _⟩⟩
=======
    iexists (PartialMap.singleton config.store.runtime.entry.id
      config.store.runtime.currentModule)
    iexists (PartialMap.singleton config.store.runtime.entry.id
      config.store.runtime.currentHost)
    unfold runtimeModuleElem runtimeInstancesOwn hostStateAuth currentInstanceAuth currentInstanceAuthN
    simp only [BI.BigSepM.bigSepM_singleton.to_eq]
    iframe Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth' # HruntimeInstances HinstanceState HhostEnvAuth' HhostState
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
>>>>>>> origin/main
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
  · apply twp_total (hlc := .hasNoLC) (GF := WasmHeapGF α)
      Stuckness.NotStuck config.expr config.store
      (fun _values => iprop(True)) 0 0
    intro inv
    imod genHeap_init (L := MemoryKey) (V := Option UInt8)
        (GF := WasmHeapGF α) (H := WasmHeapMap) σ with
      ⟨%heapGS, Hheap, Hpoints, Hmeta⟩
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
    letI exceptionMapG :
        GhostMapG (WasmHeapGF α) Nat (Nat × List Value) WasmExceptionMap := by
      constructor
      exists 13
    imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := Nat)
        (V := Nat × List Value) (H := WasmExceptionMap)) with
      ⟨%exceptionName, Hexceptions⟩
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
<<<<<<< HEAD
    letI wasmExceptionGS : WasmExceptionGS α :=
      { toGhostMapG := exceptionMapG
        exceptionName := exceptionName }
    letI runtimeElem :
        ElemG (WasmHeapGF α) (constOF (Agree (DiscreteO Module))) := by
=======
    letI runtimeModuleMapG : GhostMapG (WasmHeapGF α) Nat Module WasmRuntimeModuleMap := by
      constructor
>>>>>>> origin/main
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
<<<<<<< HEAD
    letI tagTableElem : ElemG (WasmHeapGF α)
        (constOF (Agree (DiscreteO (List Nat)))) := by
      exists 14
    imod (iOwn_alloc (E := tagTableElem)
        (toAgree ⟨config.store.wasm.tagIds⟩) (fun _ => trivial)) with
      ⟨%tagTableName, HtagTable⟩
    letI tagTableGS : WasmTagTableGS α :=
      { tagTableElem
        tagTableName }
    letI hostElem : ElemG (WasmHeapGF α)
        (ExclAuth.ExclAuthURF (constOF (DiscreteO α))) := by
=======
    letI hostEnvMapG : GhostMapG (WasmHeapGF α) Nat (HostEnv α) WasmHostEnvMap := by
      constructor
>>>>>>> origin/main
      exists 12
    imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := Nat)
        (V := HostEnv α) (H := WasmHostEnvMap)) with ⟨%hostEnvName, HhostEnvAuth⟩
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
    iclear HhostStateFrag
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
    letI gs : WasmSmallStepGS .hasNoLC α :=
      { toInvGS_gen := inv
        toWasmHeapGS := wasmHeapGS
        global := wasmGlobalGS
        dataSegment := wasmDataSegmentGS
        table := wasmTableGS
        elementSegment := wasmElementSegmentGS
        exception := wasmExceptionGS
        runtime := runtimeGS
<<<<<<< HEAD
        tagTable := tagTableGS
        host := hostGS }
=======
        hostEnv := hostEnvGS
        hostState := hostStateGS
        instanceGS := instanceGS
        runtimeInstances := runtimeInstancesGS }
>>>>>>> origin/main
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
<<<<<<< HEAD
    isplitl [Hheap Hglobals Hsegments Htables HelementSegments Hexceptions HruntimeState HtagTable HhostState]
=======
    isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth' HruntimeInstances HinstanceState HhostEnvAuth HhostState]
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
      iframe Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth' # HruntimeInstances HinstanceState HhostEnvAuth HhostState
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
        fun id env hm => by simp [get?_empty] at hm⟩
    · iintro _
      iapply (twp.mono (fun _ => BI.true_intro))
      iapply htwp .hasNoLC
      isplitl [Hpoints]
      · iexact Hpoints
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
    isplitl [Hpoints]
    · iexact Hpoints
    · isplitl [Hglobals]
      · iexact Hglobals
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
    letI globalMapG : GhostMapG (WasmHeapGF α) GlobalKey Value WasmGlobalMap := by
      constructor
      exists 7
    imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := GlobalKey)
        (V := Value) (H := WasmGlobalMap)) with ⟨%globalName, Hglobals⟩
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
    iclear HhostStateFrag
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
    letI gs : WasmSmallStepGS .hasNoLC α :=
      { toInvGS_gen := inv
        toWasmHeapGS := wasmHeapGS
        global := wasmGlobalGS
        dataSegment := wasmDataSegmentGS
        table := wasmTableGS
        elementSegment := wasmElementSegmentGS
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
    isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth' HruntimeInstances HinstanceState HhostEnvAuth HhostState]
>>>>>>> origin/main
    · iapply (stateInterp_eq config.store 0 [] 0).mpr
      iexists σ
      iexists (∅ : WasmGlobalMap Value)
      iexists (∅ : WasmDataSegmentMap (Option (List UInt8)))
      iexists (∅ : WasmTableMap TableInst)
      iexists (∅ : WasmElementSegmentMap (Option (List (Option Nat))))
<<<<<<< HEAD
      iexists (∅ : WasmExceptionMap (Nat × List Value))
      unfold runtimeInterp runtimeModuleOwn tagTableOwn
      unfold hostStateAuth
      iframe Hheap Hglobals Hsegments Htables HelementSegments Hexceptions HruntimeState HhostState
      isplitl [HtagTable]
      · iexists config.store.wasm.tagIds
        isplitl [HtagTable]
        · iexact HtagTable
        · ipureintro
          exact List.prefix_rfl
      ipureintro
      exact ⟨hagree, hinBounds, globalHeapAgrees_empty _,
        dataSegmentHeapAgrees_empty _,
        ⟨tableHeapAgrees_empty _, elementSegmentHeapAgrees_empty _,
          exceptionHeapAgrees_empty _⟩⟩
=======
      iexists (PartialMap.singleton config.store.runtime.entry.id
        config.store.runtime.currentModule)
      iexists (∅ : WasmHostEnvMap (HostEnv α))
      unfold runtimeModuleElem runtimeInstancesOwn hostStateAuth currentInstanceAuth currentInstanceAuthN
      simp only [BI.BigSepM.bigSepM_singleton.to_eq]
      iframe Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth' # HruntimeInstances HinstanceState HhostEnvAuth HhostState
      ipureintro
      exact ⟨hagree, hinBounds, globalHeapAgrees_empty _,
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
        fun id env hm => by simp [get?_empty] at hm⟩
>>>>>>> origin/main
    · iintro _
      iapply (twp.mono (fun _ => BI.true_intro))
      iapply htwp .hasNoLC
      isplitl [Hpoints]
      · iexact Hpoints
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
    isplitl [Hpoints]
    · iexact Hpoints
    · iexact HruntimeModule

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
  imod genHeap_init (L := MemoryKey) (V := Option UInt8)
      (GF := WasmHeapGF α) (H := WasmHeapMap) σ with
    ⟨%heapGS, Hheap, Hpoints, Hmeta⟩
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
  imod (ghost_map_alloc (GF := WasmHeapGF α) (K := DataSegmentKey)
      (V := Option (List UInt8)) (H := WasmDataSegmentMap)
      dataSegmentσ) with
    ⟨%dataSegmentName, HsegmentsAuth, HsegmentPoints⟩
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
  letI exceptionMapG :
      GhostMapG (WasmHeapGF α) Nat (Nat × List Value) WasmExceptionMap := by
    constructor
    exists 13
  imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := Nat)
      (V := Nat × List Value) (H := WasmExceptionMap)) with
    ⟨%exceptionName, Hexceptions⟩
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
<<<<<<< HEAD
  letI wasmExceptionGS : WasmExceptionGS α :=
    { toGhostMapG := exceptionMapG
      exceptionName := exceptionName }
  letI runtimeElem :
      ElemG (WasmHeapGF α) (constOF (Agree (DiscreteO Module))) := by
=======
  letI runtimeModuleMapG : GhostMapG (WasmHeapGF α) Nat Module WasmRuntimeModuleMap := by
    constructor
>>>>>>> origin/main
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
<<<<<<< HEAD
  letI tagTableElem : ElemG (WasmHeapGF α)
      (constOF (Agree (DiscreteO (List Nat)))) := by
    exists 14
  imod (iOwn_alloc (E := tagTableElem)
      (toAgree ⟨config.store.wasm.tagIds⟩) (fun _ => trivial)) with
    ⟨%tagTableName, HtagTable⟩
  letI tagTableGS : WasmTagTableGS α :=
    { tagTableElem
      tagTableName }
  letI hostElem : ElemG (WasmHeapGF α)
      (ExclAuth.ExclAuthURF (constOF (DiscreteO α))) := by
=======
  letI hostEnvMapG : GhostMapG (WasmHeapGF α) Nat (HostEnv α) WasmHostEnvMap := by
    constructor
>>>>>>> origin/main
    exists 12
  imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := Nat)
      (V := HostEnv α) (H := WasmHostEnvMap)) with ⟨%hostEnvName, HhostEnvAuth⟩
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
  iclear HhostStateFrag
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
  letI gs : WasmSmallStepGS .hasLC α :=
    { toInvGS_gen := inv
      toWasmHeapGS := wasmHeapGS
      global := wasmGlobalGS
      dataSegment := wasmDataSegmentGS
      table := wasmTableGS
      elementSegment := wasmElementSegmentGS
      exception := wasmExceptionGS
      runtime := runtimeGS
<<<<<<< HEAD
      tagTable := tagTableGS
      host := hostGS }
=======
      hostEnv := hostEnvGS
      hostState := hostStateGS
      instanceGS := instanceGS
      runtimeInstances := runtimeInstancesGS }
>>>>>>> origin/main
  iclear Hmeta
  imodintro
  iexists (fun store _observations =>
    stateInterp (GF := WasmHeapGF α) store 0 [] 0)
  iexists (fun _ => iprop(True))
  dsimp only
<<<<<<< HEAD
  isplitl [Hheap Hglobals HsegmentsAuth Htables HelementSegments Hexceptions HruntimeState HtagTable HhostState]
=======
  isplitl [Hheap Hglobals HsegmentsAuth Htables HelementSegments HruntimeModuleAuth' HruntimeInstances HinstanceState HhostEnvAuth HhostState]
>>>>>>> origin/main
  · iapply (stateInterp_eq config.store 0 [] 0).mpr
    iexists σ
    iexists globalσ
    iexists dataSegmentσ
    iexists (∅ : WasmTableMap TableInst)
    iexists (∅ : WasmElementSegmentMap (Option (List (Option Nat))))
<<<<<<< HEAD
    iexists (∅ : WasmExceptionMap (Nat × List Value))
    unfold runtimeInterp runtimeModuleOwn tagTableOwn
    unfold hostStateAuth
    iframe
    ipureintro
    exact ⟨List.prefix_rfl, hagree, hinBounds, hglobals, hsegments,
      ⟨tableHeapAgrees_empty _, elementSegmentHeapAgrees_empty _,
        exceptionHeapAgrees_empty _⟩⟩
=======
    iexists (PartialMap.singleton config.store.runtime.entry.id
      config.store.runtime.currentModule)
    iexists (∅ : WasmHostEnvMap (HostEnv α))
    unfold runtimeModuleElem runtimeInstancesOwn hostStateAuth currentInstanceAuth currentInstanceAuthN
    simp only [BI.BigSepM.bigSepM_singleton.to_eq]
    iframe ∗ #
    ipureintro
    exact ⟨hagree, hinBounds, hglobals, hsegments,
      tableHeapAgrees_empty _,
      elementSegmentHeapAgrees_empty _,
      fun id m hm => by
        by_cases h : id = config.store.runtime.entry.id
        · subst h; simp [PartialMap.singleton, get?_insert_eq rfl] at hm; subst hm
          rw [Array.getElem?_eq_getElem hwf]
          simp [RuntimeEnv.currentModule, RuntimeEnv.currentInstance]
          rw [getElem!_pos config.store.runtime.instances config.store.runtime.entry.id hwf]
        · simp [PartialMap.singleton, get?_insert_ne (Ne.symm h), get?_empty] at hm,
      fun id env hm => by simp [get?_empty] at hm⟩
>>>>>>> origin/main
  · iapply hwp
    isplitl [Hpoints]
    · iexact Hpoints
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
  imod genHeap_init (L := MemoryKey) (V := Option UInt8)
      (GF := WasmHeapGF α) (H := WasmHeapMap) σ with
    ⟨%heapGS, Hheap, Hpoints, Hmeta⟩
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
  imod (ghost_map_alloc (GF := WasmHeapGF α) (K := DataSegmentKey)
      (V := Option (List UInt8)) (H := WasmDataSegmentMap)
      dataSegmentσ) with
    ⟨%dataSegmentName, HsegmentsAuth, HsegmentPoints⟩
  letI tableMapG : GhostMapG (WasmHeapGF α) TableKey TableInst WasmTableMap := by
    constructor
    exists 10
  imod (ghost_map_alloc (GF := WasmHeapGF α) (K := TableKey)
      (V := TableInst) (H := WasmTableMap) tableσ) with
    ⟨%tableName, HtablesAuth, HtablePoints⟩
  letI elementSegmentMapG :
      GhostMapG (WasmHeapGF α) ElementSegmentKey (Option (List (Option Nat)))
        WasmElementSegmentMap := by
    constructor
    exists 11
  imod (ghost_map_alloc (GF := WasmHeapGF α) (K := ElementSegmentKey)
      (V := Option (List (Option Nat))) (H := WasmElementSegmentMap)
      elementSegmentσ) with
    ⟨%elementSegmentName, HelementSegmentsAuth,
      HelementSegmentPoints⟩
  letI exceptionMapG :
      GhostMapG (WasmHeapGF α) Nat (Nat × List Value) WasmExceptionMap := by
    constructor
    exists 13
  imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := Nat)
      (V := Nat × List Value) (H := WasmExceptionMap)) with
    ⟨%exceptionName, Hexceptions⟩
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
<<<<<<< HEAD
  letI wasmExceptionGS : WasmExceptionGS α :=
    { toGhostMapG := exceptionMapG
      exceptionName := exceptionName }
  letI runtimeElem :
      ElemG (WasmHeapGF α) (constOF (Agree (DiscreteO Module))) := by
=======
  letI runtimeModuleMapG : GhostMapG (WasmHeapGF α) Nat Module WasmRuntimeModuleMap := by
    constructor
>>>>>>> origin/main
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
<<<<<<< HEAD
  letI tagTableElem : ElemG (WasmHeapGF α)
      (constOF (Agree (DiscreteO (List Nat)))) := by
    exists 14
  imod (iOwn_alloc (E := tagTableElem)
      (toAgree ⟨config.store.wasm.tagIds⟩) (fun _ => trivial)) with
    ⟨%tagTableName, HtagTable⟩
  letI tagTableGS : WasmTagTableGS α :=
    { tagTableElem
      tagTableName }
  letI hostElem : ElemG (WasmHeapGF α)
      (ExclAuth.ExclAuthURF (constOF (DiscreteO α))) := by
=======
  letI hostEnvMapG : GhostMapG (WasmHeapGF α) Nat (HostEnv α) WasmHostEnvMap := by
    constructor
>>>>>>> origin/main
    exists 12
  imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := Nat)
      (V := HostEnv α) (H := WasmHostEnvMap)) with ⟨%hostEnvName, HhostEnvAuth⟩
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
  iclear HhostStateFrag
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
  letI gs : WasmSmallStepGS .hasLC α :=
    { toInvGS_gen := inv
      toWasmHeapGS := wasmHeapGS
      global := wasmGlobalGS
      dataSegment := wasmDataSegmentGS
      table := wasmTableGS
      elementSegment := wasmElementSegmentGS
      exception := wasmExceptionGS
      runtime := runtimeGS
<<<<<<< HEAD
      tagTable := tagTableGS
      host := hostGS }
=======
      hostEnv := hostEnvGS
      hostState := hostStateGS
      instanceGS := instanceGS
      runtimeInstances := runtimeInstancesGS }
>>>>>>> origin/main
  iclear Hmeta
  imodintro
  iexists (fun store _observations =>
    stateInterp (GF := WasmHeapGF α) store 0 [] 0)
  iexists (fun _ => iprop(True))
  dsimp only
  isplitl [Hheap Hglobals HsegmentsAuth HtablesAuth
<<<<<<< HEAD
      HelementSegmentsAuth Hexceptions HruntimeState HtagTable HhostState]
=======
      HelementSegmentsAuth HruntimeModuleAuth' HruntimeInstances HinstanceState HhostEnvAuth HhostState]
>>>>>>> origin/main
  · iapply (stateInterp_eq config.store 0 [] 0).mpr
    iexists σ
    iexists globalσ
    iexists dataSegmentσ
    iexists tableσ
    iexists elementSegmentσ
<<<<<<< HEAD
    iexists (∅ : WasmExceptionMap (Nat × List Value))
    unfold runtimeInterp runtimeModuleOwn tagTableOwn
    unfold hostStateAuth
    iframe
    ipureintro
    exact ⟨List.prefix_rfl, hagree, hinBounds, hglobals, hsegments,
      ⟨htables, helementSegments,
        exceptionHeapAgrees_empty _⟩⟩
=======
    iexists (PartialMap.singleton config.store.runtime.entry.id
      config.store.runtime.currentModule)
    iexists (∅ : WasmHostEnvMap (HostEnv α))
    unfold runtimeModuleElem runtimeInstancesOwn hostStateAuth currentInstanceAuth currentInstanceAuthN
    simp only [BI.BigSepM.bigSepM_singleton.to_eq]
    iframe ∗ #
    ipureintro
    exact ⟨hagree, hinBounds, hglobals, hsegments,
      htables,
      helementSegments,
      fun id m hm => by
        by_cases h : id = config.store.runtime.entry.id
        · subst h; simp [PartialMap.singleton, get?_insert_eq rfl] at hm; subst hm
          rw [Array.getElem?_eq_getElem hwf]
          simp [RuntimeEnv.currentModule, RuntimeEnv.currentInstance]
          rw [getElem!_pos config.store.runtime.instances config.store.runtime.entry.id hwf]
        · simp [PartialMap.singleton, get?_insert_ne (Ne.symm h), get?_empty] at hm,
      fun id env hm => by simp [get?_empty] at hm⟩
>>>>>>> origin/main
  · iapply hwp
    isplitl [Hpoints]
    · iexact Hpoints
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
  iapply hwp
  iframe

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

/-- Call-capable partial correctness with an authoritative byte footprint and
no owned globals. -/
theorem wasm_smallStep_heap_runtime_partiallyMeets
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
    PartiallyMeets config (fun values _store => φ values) := by
  apply wasm_smallStep_heap_globals_runtime_partiallyMeets
    config σ (∅ : WasmGlobalMap Value) φ hagree hinBounds
    (globalHeapAgrees_empty _) hwf
  · intro gs
    simp only [BI.BigSepM.bigSepM_empty.to_eq]
    iintro ⟨Hheap, _Hempty, Hruntime⟩
    iapply hwp
    iframe

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
  imod genHeap_init (L := MemoryKey) (V := Option UInt8)
      (GF := WasmHeapGF α) (H := WasmHeapMap) σ with
    ⟨%heapGS, Hheap, Hpoints, Hmeta⟩
  letI globalMapG : GhostMapG (WasmHeapGF α) GlobalKey Value WasmGlobalMap := by
    constructor
    exists 7
  imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := GlobalKey)
      (V := Value) (H := WasmGlobalMap)) with ⟨%globalName, Hglobals⟩
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
  iclear HhostStateFrag
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
  letI gs : WasmSmallStepGS .hasLC α :=
    { toInvGS_gen := inv
      toWasmHeapGS := wasmHeapGS
      global := wasmGlobalGS
      dataSegment := wasmDataSegmentGS
      table := wasmTableGS
      elementSegment := wasmElementSegmentGS
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
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth' HruntimeInstances HinstanceState HhostEnvAuth HhostState]
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
    iframe Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth' # HruntimeInstances HinstanceState HhostEnvAuth HhostState
    ipureintro
    exact ⟨hagree, hinBounds, globalHeapAgrees_empty _,
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
      fun id env hm => by simp [get?_empty] at hm⟩
  · iapply hwp
    isplitl [Hpoints]
    · iexact Hpoints
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
  imod genHeap_init (L := MemoryKey) (V := Option UInt8)
      (GF := WasmHeapGF α) (H := WasmHeapMap) σ with
    ⟨%heapGS, Hheap, Hpoints, Hmeta⟩
  letI globalMapG : GhostMapG (WasmHeapGF α) GlobalKey Value WasmGlobalMap := by
    constructor
    exists 7
  imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := GlobalKey)
      (V := Value) (H := WasmGlobalMap)) with ⟨%globalName, Hglobals⟩
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
  iclear HhostStateFrag
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
  letI gs : WasmSmallStepGS .hasLC α :=
    { toInvGS_gen := inv
      toWasmHeapGS := wasmHeapGS
      global := wasmGlobalGS
      dataSegment := wasmDataSegmentGS
      table := wasmTableGS
      elementSegment := wasmElementSegmentGS
      runtime := runtimeGS
      hostEnv := hostEnvGS
      hostState := hostStateGS
      instanceGS := instanceGS
      runtimeInstances := runtimeInstancesGS }
  iclear Hmeta
  ihave HruntimeInstancesPair := iOwn_op.mp $$ HruntimeInstances
  icases HruntimeInstancesPair with ⟨HruntimeInstancesState, HruntimeInstancesWP⟩
  imodintro
  iexists (fun store _observations =>
    stateInterp (GF := WasmHeapGF α) store 0 [] 0)
  iexists (fun _ => iprop(True))
  dsimp only
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth' HruntimeInstancesState HinstanceState HhostEnvAuth HhostState]
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
    iframe Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth' # HruntimeInstancesState HinstanceState HhostEnvAuth HhostState
    ipureintro
    exact ⟨hagree, hinBounds, globalHeapAgrees_empty _,
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
      fun id env hm => by simp [get?_empty] at hm⟩
  · iapply hwp
    isplitl [Hpoints]
    · iexact Hpoints
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

private def globalGetAdequacyConfig : Config Unit :=
  let runtimeModule : Module := { funcs := [] }
  let initial : Store Unit := runtimeModule.initialStore
  { expr := .running
      ⟨⟨[], [], []⟩, [.globalGet 0], 1, [], [], []⟩
    store :=
      { runtime := { instances := #[{ module := runtimeModule, host := {} }], entry := ⟨0⟩ }
        wasm :=
          { initial with
            globals := { globals := [.i32 42] } } } }

private def global0Heap : WasmGlobalMap Value :=
  insert ∅ (⟨0, 0⟩ : GlobalKey) (.i32 42)

private theorem global0Heap_agrees :
    globalHeapAgrees global0Heap
      globalGetAdequacyConfig.store.wasm.globals := by
  intro index value hget
  simp only [global0Heap] at hget
  by_cases hindex : index = 0
  · subst index
    simp only [get?_insert_eq rfl] at hget
    obtain rfl := Option.some.inj hget
    rfl
  · rw [get?_insert_ne (fun h => hindex (congrArg GlobalKey.index h).symm),
        get?_empty] at hget
    contradiction

private theorem global0Heap_pointsTo [WasmGlobalGS α] :
    ([∗map] index ↦ value ∈ global0Heap,
      globalPointsTo index value) ⊢
      globalPointsTo ⟨0, 0⟩ (.i32 42) := by
  unfold global0Heap
  rw [(BI.BigSepM.bigSepM_insert (get?_empty (⟨0, 0⟩ : GlobalKey))).to_eq,
    BI.BigSepM.bigSepM_empty.to_eq, BI.sep_emp.to_eq]

/-- A concrete adequacy witness for authoritative globals: the WP may derive
the result of `global.get 0` only from ownership allocated for the matching
physical global in the initial machine store. -/
theorem globalGet_adequate :
    adequate Stuckness.NotStuck
      globalGetAdequacyConfig.expr globalGetAdequacyConfig.store
      (fun values _ => values = [.i32 42]) := by
  apply wasm_smallStep_heap_globals_adequacy (α := Unit)
    (σ := (∅ : WasmHeapMap (Option UInt8)))
    (globalσ := global0Heap)
    (φ := fun values => values = [.i32 42])
  · intro address value hget
    rw [get?_empty] at hget
    contradiction
  · intro address hne
    exact absurd (get?_empty address) hne
  · exact global0Heap_agrees
  · decide
  · intro gs
    simp only [BI.BigSepM.bigSepM_empty.to_eq, BI.emp_sep.to_eq]
    unfold global0Heap
    rw [(BI.BigSepM.bigSepM_insert (get?_empty (⟨0, 0⟩ : GlobalKey))).to_eq,
      BI.BigSepM.bigSepM_empty.to_eq, BI.sep_emp.to_eq]
    iintro Hglobal
    simp only [globalGetAdequacyConfig]
    simp only [← globalPointsToAt_eq]
    iapply wp_globalGet $$ Hglobal
    inext
    iintro Hglobal
    iapply wp_finish
    inext
    iapply wp_value'
    ipureintro
    rfl

def noopCallModule : Module :=
  { funcs := [{ body := [.ret] }] }

def noopCallConfig : Config Unit :=
  let initial : Store Unit := noopCallModule.initialStore
  { expr := .running
      ⟨⟨[], [], []⟩, [.call 0, .ret], 0, [], [], []⟩
    store :=
      { runtime := { instances := #[{ module := noopCallModule, host := {} }], entry := ⟨0⟩ }
        wasm := initial } }

/-- End-to-end adequacy for direct-call entry and administrative return. The
function lookup is justified by immutable runtime ownership, not by a theorem
premise detached from the physical `MachineStore`. -/
theorem noopCall_adequate :
    adequate Stuckness.NotStuck noopCallConfig.expr noopCallConfig.store
      (fun values _ => values = []) := by
  apply wasm_smallStep_runtime_instance_adequacy (α := Unit)
    (φ := fun values => values = [])
  · decide
  · intro gs
    simp only [noopCallConfig, RuntimeEnv.currentModule_mk1]
    iintro ⟨Hruntime, _HruntimeInstances⟩
    iclear _HruntimeInstances
    iapply wp_call noopCallModule 0 ({ body := [.ret] } : Function)
        (by simp [noopCallModule]) rfl ⟨0⟩ $$ Hruntime
    inext
    iintro Hruntime
    simp only [noopCallModule, Function.toLocals, Function.numParams,
      List.take_nil, List.reverse_nil, List.drop_nil, List.length_nil]
    iapply wp_returnFromCallExplicit $$ Hruntime
    inext
    iapply wp_returnFromFunction
    inext
    iapply wp_value'
    ipureintro
    rfl

private def word16Heap (word : UInt32) :
    WasmHeapMap (Option UInt8) :=
  store32Heap ∅ 0 16 word

private theorem word16Heap_pointsTo (word : UInt32) [WasmHeapGS α] :
    ([∗map] address ↦ value ∈ word16Heap word,
      pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        address (DFrac.own 1) value) ⊢
      pointsTo_u32 0 16 word := by
  let σ0 : WasmHeapMap (Option UInt8) := ∅
  let σ1 := insert σ0 (⟨0, 16⟩ : MemoryKey) (some (u32Byte word 0))
  let σ2 := insert σ1 (⟨0, 17⟩ : MemoryKey) (some (u32Byte word 1))
  let σ3 := insert σ2 (⟨0, 18⟩ : MemoryKey) (some (u32Byte word 2))
  have h17 : get? σ1 ⟨0, 17⟩ = none := by
    dsimp [σ1, σ0]
    rw [get?_insert_ne (by decide), get?_empty]
  have h18 : get? σ2 ⟨0, 18⟩ = none := by
    dsimp [σ2, σ1, σ0]
    rw [get?_insert_ne (by decide), get?_insert_ne (by decide), get?_empty]
  have h19 : get? σ3 ⟨0, 19⟩ = none := by
    dsimp [σ3, σ2, σ1, σ0]
    rw [get?_insert_ne (by decide), get?_insert_ne (by decide),
      get?_insert_ne (by decide), get?_empty]
  change
    ([∗map] address ↦ value ∈
      insert σ3 (⟨0, 19⟩ : MemoryKey) (some (u32Byte word 3)),
      pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        address (DFrac.own 1) value) ⊢
      pointsTo_u32 0 16 word
  rw [(BI.BigSepM.bigSepM_insert h19).to_eq]
  rw [(BI.BigSepM.bigSepM_insert h18).to_eq]
  rw [(BI.BigSepM.bigSepM_insert h17).to_eq]
  rw [(BI.BigSepM.bigSepM_insert (get?_empty (⟨0, 16⟩ : MemoryKey))).to_eq]
  rw [BI.BigSepM.bigSepM_empty.to_eq, BI.sep_emp.to_eq]
  unfold pointsTo_u32
  simp only [UInt32.reduceAdd]
  iintro ⟨H19, H18, H17, H16⟩
  iframe

private theorem emptyHeap_agrees (resolve : Nat → Option Mem) :
    heapAgreesWithMem (∅ : WasmHeapMap (Option UInt8)) resolve :=
  heapAgreesWithMem_empty _

private theorem emptyHeap_inBounds (resolve : Nat → Option Mem) :
    heapAddressesInBounds (∅ : WasmHeapMap (Option UInt8)) resolve :=
  heapAddressesInBounds_empty _

/-- Concrete machine used to connect the clean word-roundtrip Iris contract
to iris-lean adequacy. -/
def wordRoundtripAdequacyModule : Module :=
  { funcs :=
      [{ body :=
          [ .const 16, .const 0x12345678, .store32 0,
            .const 16, .load32 0 ],
         results := [.i32] }]
    memory := some { pagesMin := 1 } }

def wordRoundtripAdequacyConfig (oldWord : UInt32) : Config Unit :=
  let initial : Store Unit := wordRoundtripAdequacyModule.initialStore
  { expr := .running
      ⟨⟨[], [], []⟩,
        [ .const 16, .const 0x12345678, .store32 0,
          .const 16, .load32 0 ],
        1, [], [], []⟩
    store :=
      { runtime := { instances := #[{ module := wordRoundtripAdequacyModule, host := {} }], entry := ⟨0⟩ }
        wasm :=
          { initial with
            mem := initial.mem.write32 16 oldWord } } }

/-- The manual 32-bit memory roundtrip is adequate for the authoritative
small-step relation: every Iris value it reaches is the stored word. This is
partial correctness, matching iris-lean's current adequacy support. -/
theorem wordRoundtrip_adequate (oldWord : UInt32) :
    adequate Stuckness.NotStuck
      (wordRoundtripAdequacyConfig oldWord).expr
      (wordRoundtripAdequacyConfig oldWord).store
      (fun values _ => values = [.i32 0x12345678]) := by
  apply wasm_smallStep_heap_adequacy (α := Unit)
    (σ := word16Heap oldWord)
    (φ := fun values => values = [.i32 0x12345678])
  · unfold word16Heap
    apply store32_sound0 (mem := wordRoundtripAdequacyModule.initialStore.mem)
      (h1 := rfl) (h2 := rfl) (h3 := rfl)
    exact emptyHeap_agrees _
  · unfold word16Heap
    apply store32_inBounds0 (mem := wordRoundtripAdequacyModule.initialStore.mem)
      (h1 := rfl) (h2 := rfl) (h3 := rfl)
    · native_decide
    · exact emptyHeap_inBounds _
  · intro gs
    iintro Hbytes
    ihave Hword := word16Heap_pointsTo oldWord $$ Hbytes
    simp only [wordRoundtripAdequacyConfig, wordRoundtripAdequacyModule]
    have hpost : ∀ values : List Value,
        (iprop% ⌜values = [.i32 0x12345678]⌝ ∗
          pointsTo_u32 0 16 0x12345678) ⊢
        (iprop% ⌜values = [.i32 0x12345678]⌝) := by
      intro values
      iintro ⟨%hvalues, _Hword⟩
      ipureintro
      exact hvalues
    iapply wp_mono hpost
    iapply wp_wordRoundtrip
    iexact Hword

/-- State-sensitive adequacy exposes the physical effect of the manual
roundtrip, not only its returned value. -/
theorem wordRoundtrip_store_partiallyMeets (oldWord : UInt32) :
    PartiallyMeets (wordRoundtripAdequacyConfig oldWord)
      (fun values store =>
        values = [.i32 0x12345678] ∧
          store.wasm.mem.read32 16 = 0x12345678) := by
  apply wasm_smallStep_heap_globals_runtime_store_partiallyMeets
    (α := Unit)
    (σ := word16Heap oldWord)
    (globalσ := (∅ : WasmGlobalMap Value))
  · unfold word16Heap
    apply store32_sound0 (mem := wordRoundtripAdequacyModule.initialStore.mem)
      (h1 := rfl) (h2 := rfl) (h3 := rfl)
    exact emptyHeap_agrees _
  · unfold word16Heap
    apply store32_inBounds0 (mem := wordRoundtripAdequacyModule.initialStore.mem)
      (h1 := rfl) (h2 := rfl) (h3 := rfl)
    · native_decide
    · exact emptyHeap_inBounds _
  · intro index value hget
    rw [get?_empty] at hget
    contradiction
  · simp only [wordRoundtripAdequacyConfig]; decide
  · intro gs
    simp only [BI.BigSepM.bigSepM_empty.to_eq]
    iintro ⟨Hbytes, _Hglobals, _Hruntime⟩
    ihave Hword := word16Heap_pointsTo oldWord $$ Hbytes
    simp only [wordRoundtripAdequacyConfig, wordRoundtripAdequacyModule]
    have hpost : ∀ values : List Value,
        (iprop% ⌜values = [.i32 0x12345678]⌝ ∗
          pointsTo_u32 0 16 0x12345678) ⊢
        (iprop% ∀ (store : MachineStore Unit)
            (observations : List StepKind),
          stateInterp (GF := WasmHeapGF Unit) store 0 [] 0 -∗
          ⌜values = [.i32 0x12345678] ∧
            store.wasm.mem.read32 16 = 0x12345678⌝) := by
      intro values
      iintro ⟨%hvalues, Hword⟩ %store %observations Hstate
      imod stateInterp_pointsTo_u32_facts
        store 0 [] 0 16 0x12345678
        (by decide) (by decide) (by decide) $$
          [$Hstate $Hword] with %Hfacts
      ipureintro
      exact ⟨hvalues, Hfacts.1⟩
    iapply wp_mono hpost
    iapply wp_wordRoundtrip
    iexact Hword

/-- Authoritative footprint for the two cells used by `wp_swapWords`. -/
private def swapWordsHeap : WasmHeapMap (Option UInt8) :=
  store32Heap (store32Heap ∅ 0 0 11) 0 4 22

private theorem swapWordsHeap_agrees (mem : Mem) :
    heapAgreesWithMem swapWordsHeap
      (fun id => if id = 0 then some ((mem.write32 0 11).write32 4 22) else none) := by
  unfold swapWordsHeap
  apply store32_sound0 (mem := mem.write32 0 11) (h1 := rfl) (h2 := rfl) (h3 := rfl)
  apply store32_sound0 (mem := mem) (h1 := rfl) (h2 := rfl) (h3 := rfl)
  exact emptyHeap_agrees _

private theorem swapWordsHeap_inBounds (memory : Mem)
    (hpages : 1 ≤ memory.pages) :
    heapAddressesInBounds swapWordsHeap
      (fun id => if id = 0 then some ((memory.write32 0 11).write32 4 22) else none) := by
  unfold swapWordsHeap
  apply store32_inBounds0 (mem := memory.write32 0 11) (h1 := rfl) (h2 := rfl) (h3 := rfl)
  · have hcapacity :
        65536 ≤ memory.pages * 65536 :=
      Nat.mul_le_mul_right 65536 hpages
    simp only [UInt32.toNat_ofNat, Mem.write32]
    omega
  · apply store32_inBounds0 (mem := memory) (h1 := rfl) (h2 := rfl) (h3 := rfl)
    · have hcapacity :
          65536 ≤ memory.pages * 65536 :=
        Nat.mul_le_mul_right 65536 hpages
      simp only [UInt32.toNat_zero, Nat.zero_add]
      omega
    · exact emptyHeap_inBounds _

private theorem swapWordsHeap_pointsTo [WasmHeapGS α] :
    ([∗map] address ↦ value ∈ swapWordsHeap,
      pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        address (DFrac.own 1) value) ⊢
      pointsTo_u32 0 0 11 ∗ pointsTo_u32 0 4 22 := by
  unfold swapWordsHeap store32Heap
  rw [(BI.BigSepM.bigSepM_insert (by native_decide)).to_eq]
  rw [(BI.BigSepM.bigSepM_insert (by native_decide)).to_eq]
  rw [(BI.BigSepM.bigSepM_insert (by native_decide)).to_eq]
  rw [(BI.BigSepM.bigSepM_insert (by native_decide)).to_eq]
  rw [(BI.BigSepM.bigSepM_insert (by native_decide)).to_eq]
  rw [(BI.BigSepM.bigSepM_insert (by native_decide)).to_eq]
  rw [(BI.BigSepM.bigSepM_insert (by native_decide)).to_eq]
  rw [(BI.BigSepM.bigSepM_insert (get?_empty (⟨0, 0⟩ : MemoryKey))).to_eq]
  rw [BI.BigSepM.bigSepM_empty.to_eq, BI.sep_emp.to_eq]
  unfold pointsTo_u32
  simp only [UInt32.reduceAdd]
  iintro ⟨H7, H6, H5, H4, H3, H2, H1, H0⟩
  iframe

def swapWordsAdequacyModule : Module :=
  { funcs :=
      [{ locals := [.i32, .i32]
         body :=
          [ .const 0, .load32 0, .localSet 0,
            .const 4, .load32 0, .localSet 1,
            .const 0, .localGet 1, .store32 0,
            .const 4, .localGet 0, .store32 0,
            .const 0, .load32 0,
            .const 4, .load32 0 ],
         results := [.i32, .i32] }]
    memory := some { pagesMin := 1 } }

def swapWordsAdequacyConfig : Config Unit :=
  let initial : Store Unit := swapWordsAdequacyModule.initialStore
  { expr := .running
      ⟨⟨[], [.i32 0, .i32 0], []⟩,
        [ .const 0, .load32 0, .localSet 0,
          .const 4, .load32 0, .localSet 1,
          .const 0, .localGet 1, .store32 0,
          .const 4, .localGet 0, .store32 0,
          .const 0, .load32 0,
          .const 4, .load32 0 ],
        2, [], [], []⟩
    store :=
      { runtime := { instances := #[{ module := swapWordsAdequacyModule, host := {} }], entry := ⟨0⟩ }
        wasm :=
          { initial with
            mem := (initial.mem.write32 0 11).write32 4 22 } } }

/-- Closed iris-lean adequacy for a genuinely mutating manual example. The
physical store initially contains `[11, 22]`; authoritative byte ownership is
allocated from that store, `wp_swapWords` proves the exchange, and adequacy
exposes the returned post-swap values without assuming any ghost resources. -/
theorem swapWords_adequate :
    adequate Stuckness.NotStuck
      swapWordsAdequacyConfig.expr swapWordsAdequacyConfig.store
      (fun values _ => values = [.i32 11, .i32 22]) := by
  apply wasm_smallStep_heap_adequacy (α := Unit)
    (σ := swapWordsHeap)
    (φ := fun values => values = [.i32 11, .i32 22])
  · apply swapWordsHeap_agrees
  · apply swapWordsHeap_inBounds
    native_decide
  · intro gs
    iintro Hbytes
    ihave Hwords := swapWordsHeap_pointsTo $$ Hbytes
    simp only [swapWordsAdequacyConfig, swapWordsAdequacyModule]
    have hpost : ∀ values : List Value,
        (iprop% ⌜values = [.i32 11, .i32 22]⌝ ∗
          pointsTo_u32 0 0 22 ∗ pointsTo_u32 0 4 11) ⊢
        (iprop% ⌜values = [.i32 11, .i32 22]⌝) := by
      intro values
      iintro ⟨%hvalues, _H0, _H4⟩
      ipureintro
      exact hvalues
    iapply wp_mono hpost
    iapply wp_swapWords
    iexact Hwords

/-- State-sensitive Iris adequacy for the two-word swap.  In addition to the
returned stack, this exposes both exchanged words in the reached physical
memory from one authoritative state interpretation. -/
theorem swapWords_store_partiallyMeets :
    PartiallyMeets swapWordsAdequacyConfig
      (fun values store =>
        values = [.i32 11, .i32 22] ∧
          store.wasm.mem.read32 0 = 22 ∧
          store.wasm.mem.read32 4 = 11) := by
  apply wasm_smallStep_heap_globals_runtime_store_partiallyMeets
    (α := Unit)
    (σ := swapWordsHeap)
    (globalσ := (∅ : WasmGlobalMap Value))
  · apply swapWordsHeap_agrees
  · apply swapWordsHeap_inBounds
    native_decide
  · intro index value hget
    rw [get?_empty] at hget
    contradiction
  · decide
  · intro gs
    simp only [BI.BigSepM.bigSepM_empty.to_eq]
    iintro ⟨Hbytes, _Hglobals, _Hruntime⟩
    ihave Hwords := swapWordsHeap_pointsTo $$ Hbytes
    simp only [swapWordsAdequacyConfig, swapWordsAdequacyModule]
    have hpost : ∀ values : List Value,
        (iprop% ⌜values = [.i32 11, .i32 22]⌝ ∗
          pointsTo_u32 0 0 22 ∗ pointsTo_u32 0 4 11) ⊢
        (iprop% ∀ (store : MachineStore Unit)
            (_observations : List StepKind),
          stateInterp (GF := WasmHeapGF Unit) store 0 [] 0 -∗
          ⌜values = [.i32 11, .i32 22] ∧
            store.wasm.mem.read32 0 = 22 ∧
            store.wasm.mem.read32 4 = 11⌝) := by
      intro values
      iintro ⟨%hvalues, H0, H4⟩ %store %_observations Hstate
      imod stateInterp_pointsTo_u32_facts_frame
        store 0 [] 0 0 22
        (by decide) (by decide) (by decide) $$
          [$Hstate $H0] with ⟨Hstate, _H0, %Hfacts0⟩
      imod stateInterp_pointsTo_u32_facts
        store 0 [] 0 4 11
        (by decide) (by decide) (by decide) $$
          [$Hstate $H4] with %Hfacts4
      ipureintro
      exact ⟨hvalues, Hfacts0.1, Hfacts4.1⟩
    iapply wp_mono hpost
    iapply wp_swapWords
    iexact Hwords

/-! ### Three-word reverse with a framed middle cell -/

private def reverseThreeWordsHeap : WasmHeapMap (Option UInt8) :=
  store32Heap swapWordsHeap 0 8 33

private theorem reverseThreeWordsHeap_agrees (mem : Mem) :
    heapAgreesWithMem reverseThreeWordsHeap
      (fun id => if id = 0 then some (((mem.write32 0 11).write32 4 22).write32 8 33) else none) := by
  unfold reverseThreeWordsHeap
  apply store32_sound0 (mem := (mem.write32 0 11).write32 4 22) (h1 := rfl) (h2 := rfl) (h3 := rfl)
  exact swapWordsHeap_agrees mem

private theorem reverseThreeWordsHeap_inBounds (memory : Mem)
    (hpages : 1 ≤ memory.pages) :
    heapAddressesInBounds reverseThreeWordsHeap
      (fun id => if id = 0 then some (((memory.write32 0 11).write32 4 22).write32 8 33) else none) := by
  unfold reverseThreeWordsHeap
  apply store32_inBounds0 (mem := (memory.write32 0 11).write32 4 22)
    (h1 := rfl) (h2 := rfl) (h3 := rfl)
  · have hcapacity :
        65536 ≤ memory.pages * 65536 :=
      Nat.mul_le_mul_right 65536 hpages
    simp only [UInt32.toNat_ofNat, Mem.write32]
    omega
  · exact swapWordsHeap_inBounds memory hpages

private theorem reverseThreeWordsHeap_pointsTo [WasmHeapGS α] :
    ([∗map] address ↦ value ∈ reverseThreeWordsHeap,
      pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        address (DFrac.own 1) value) ⊢
      pointsTo_u32 0 0 11 ∗ pointsTo_u32 0 4 22 ∗
        pointsTo_u32 0 8 33 := by
  unfold reverseThreeWordsHeap
  iintro Hheap
  ihave H8 := store32Heap_pointsTo swapWordsHeap 0 8 33
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
    (by decide) (by decide) (by decide) $$ Hheap
  icases H8 with ⟨H8, Hheap⟩
  ihave Hwords := swapWordsHeap_pointsTo $$ Hheap
  icases Hwords with ⟨H0, H4⟩
  iframe

def reverseThreeWordsAdequacyModule : Module :=
  { funcs :=
      [{ locals := [.i32, .i32]
         body :=
          [ .const 0, .load32 0, .localSet 0,
            .const 8, .load32 0, .localSet 1,
            .const 0, .localGet 1, .store32 0,
            .const 8, .localGet 0, .store32 0,
            .const 0, .load32 0,
            .const 8, .load32 0 ],
         results := [.i32, .i32] }]
    memory := some { pagesMin := 1 } }

def reverseThreeWordsAdequacyConfig : Config Unit :=
  let initial : Store Unit := reverseThreeWordsAdequacyModule.initialStore
  { expr := .running
      ⟨⟨[], [.i32 0, .i32 0], []⟩,
        [ .const 0, .load32 0, .localSet 0,
          .const 8, .load32 0, .localSet 1,
          .const 0, .localGet 1, .store32 0,
          .const 8, .localGet 0, .store32 0,
          .const 0, .load32 0,
          .const 8, .load32 0 ],
        2, [], [], []⟩
    store :=
      { runtime := { instances := #[{ module := reverseThreeWordsAdequacyModule, host := {} }], entry := ⟨0⟩ }
        wasm :=
          { initial with
            mem :=
              ((initial.mem.write32 0 11).write32 4 22).write32 8 33 } } }

/-- End-to-end Iris partial correctness for reversing three words.  The
endpoint words are exchanged in physical memory and the owned middle word is
framed unchanged. -/
theorem reverseThreeWords_store_partiallyMeets :
    PartiallyMeets reverseThreeWordsAdequacyConfig
      (fun values store =>
        values = [.i32 11, .i32 33] ∧
          store.wasm.mem.read32 0 = 33 ∧
          store.wasm.mem.read32 4 = 22 ∧
          store.wasm.mem.read32 8 = 11) := by
  apply wasm_smallStep_heap_globals_runtime_store_partiallyMeets
    (α := Unit)
    (σ := reverseThreeWordsHeap)
    (globalσ := (∅ : WasmGlobalMap Value))
  · apply reverseThreeWordsHeap_agrees
  · apply reverseThreeWordsHeap_inBounds
    native_decide
  · intro index value hget
    rw [get?_empty] at hget
    contradiction
  · decide
  · intro gs
    simp only [BI.BigSepM.bigSepM_empty.to_eq]
    iintro ⟨Hbytes, _Hglobals, _Hruntime⟩
    ihave Hwords := reverseThreeWordsHeap_pointsTo $$ Hbytes
    simp only [reverseThreeWordsAdequacyConfig,
      reverseThreeWordsAdequacyModule]
    have hpost : ∀ values : List Value,
        (iprop% ⌜values = [.i32 11, .i32 33]⌝ ∗
          pointsTo_u32 0 0 33 ∗ pointsTo_u32 0 4 22 ∗
          pointsTo_u32 0 8 11) ⊢
        (iprop% ∀ (store : MachineStore Unit)
            (_observations : List StepKind),
          stateInterp (GF := WasmHeapGF Unit) store 0 [] 0 -∗
          ⌜values = [.i32 11, .i32 33] ∧
            store.wasm.mem.read32 0 = 33 ∧
            store.wasm.mem.read32 4 = 22 ∧
            store.wasm.mem.read32 8 = 11⌝) := by
      intro values
      iintro ⟨%hvalues, H0, H4, H8⟩
        %store %_observations Hstate
      imod stateInterp_pointsTo_u32_facts_frame
        store 0 [] 0 0 33
        (by decide) (by decide) (by decide) $$
          [$Hstate $H0] with ⟨Hstate, _H0, %Hfacts0⟩
      imod stateInterp_pointsTo_u32_facts_frame
        store 0 [] 0 4 22
        (by decide) (by decide) (by decide) $$
          [$Hstate $H4] with ⟨Hstate, _H4, %Hfacts4⟩
      imod stateInterp_pointsTo_u32_facts
        store 0 [] 0 8 11
        (by decide) (by decide) (by decide) $$
          [$Hstate $H8] with %Hfacts8
      ipureintro
      exact ⟨hvalues, Hfacts0.1, Hfacts4.1, Hfacts8.1⟩
    iapply wp_mono hpost
    iapply wp_reverseThreeWords
    iexact Hwords

/-! ### Three-word partition with a pivot in its final position -/

private def partitionThreeWordsHeap : WasmHeapMap (Option UInt8) :=
  store32Heap (store32Heap (store32Heap ∅ 0 0 33) 0 4 11) 0 8 22

private theorem partitionThreeWordsHeap_agrees (memory : Mem) :
    heapAgreesWithMem partitionThreeWordsHeap
      (fun id => if id = 0 then some (((memory.write32 0 33).write32 4 11).write32 8 22) else none) := by
  unfold partitionThreeWordsHeap
  apply store32_sound0 (mem := (memory.write32 0 33).write32 4 11) (h1 := rfl) (h2 := rfl) (h3 := rfl)
  apply store32_sound0 (mem := memory.write32 0 33) (h1 := rfl) (h2 := rfl) (h3 := rfl)
  apply store32_sound0 (mem := memory) (h1 := rfl) (h2 := rfl) (h3 := rfl)
  exact emptyHeap_agrees _

private theorem partitionThreeWordsHeap_inBounds (memory : Mem)
    (hpages : 1 ≤ memory.pages) :
    heapAddressesInBounds partitionThreeWordsHeap
      (fun id => if id = 0 then some (((memory.write32 0 33).write32 4 11).write32 8 22) else none) := by
  unfold partitionThreeWordsHeap
  have hcapacity :
      65536 ≤ memory.pages * 65536 :=
    Nat.mul_le_mul_right 65536 hpages
  apply store32_inBounds0 (mem := (memory.write32 0 33).write32 4 11)
    (h1 := rfl) (h2 := rfl) (h3 := rfl)
  · simp only [UInt32.toNat_ofNat, Mem.write32]
    omega
  · apply store32_inBounds0 (mem := memory.write32 0 33) (h1 := rfl) (h2 := rfl) (h3 := rfl)
    · simp only [UInt32.toNat_ofNat, Mem.write32]
      omega
    · apply store32_inBounds0 (mem := memory) (h1 := rfl) (h2 := rfl) (h3 := rfl)
      · simp only [UInt32.toNat_ofNat]
        omega
      · exact emptyHeap_inBounds _

private theorem partitionThreeWordsHeap_pointsTo [WasmHeapGS α] :
    ([∗map] address ↦ value ∈ partitionThreeWordsHeap,
      pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        address (DFrac.own 1) value) ⊢
      pointsTo_u32 0 0 33 ∗ pointsTo_u32 0 4 11 ∗
        pointsTo_u32 0 8 22 := by
  unfold partitionThreeWordsHeap
  iintro Hheap
  ihave H8 := store32Heap_pointsTo
    (store32Heap (store32Heap ∅ 0 0 33) 0 4 11) 0 8 22
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
    (by decide) (by decide) (by decide) $$ Hheap
  icases H8 with ⟨H8, Hheap⟩
  ihave H4 := store32Heap_pointsTo (store32Heap ∅ 0 0 33) 0 4 11
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
    (by decide) (by decide) (by decide) $$ Hheap
  icases H4 with ⟨H4, Hheap⟩
  ihave H0 := store32Heap_pointsTo (∅ : WasmHeapMap (Option UInt8)) 0 0 33
    (get?_empty (⟨0, 0⟩ : MemoryKey)) (get?_empty (⟨0, 1⟩ : MemoryKey))
    (get?_empty (⟨0, 2⟩ : MemoryKey)) (get?_empty (⟨0, 3⟩ : MemoryKey))
    (by decide) (by decide) (by decide) $$ Hheap
  icases H0 with ⟨H0, _Hempty⟩
  iframe

def partitionThreeWordsAdequacyModule : Module :=
  { funcs :=
      [{ locals := [.i32, .i32, .i32]
         body :=
          [ .const 0, .load32 0, .localSet 0,
            .const 4, .load32 0, .localSet 1,
            .const 8, .load32 0, .localSet 2,
            .const 0, .localGet 1, .store32 0,
            .const 4, .localGet 2, .store32 0,
            .const 8, .localGet 0, .store32 0 ] }]
    memory := some { pagesMin := 1 } }

def partitionThreeWordsAdequacyConfig : Config Unit :=
  let initial : Store Unit := partitionThreeWordsAdequacyModule.initialStore
  { expr := .running
      ⟨⟨[], [.i32 0, .i32 0, .i32 0], []⟩,
        [ .const 0, .load32 0, .localSet 0,
          .const 4, .load32 0, .localSet 1,
          .const 8, .load32 0, .localSet 2,
          .const 0, .localGet 1, .store32 0,
          .const 4, .localGet 2, .store32 0,
          .const 8, .localGet 0, .store32 0 ],
        0, [], [], []⟩
    store :=
      { runtime := { instances := #[{ module := partitionThreeWordsAdequacyModule, host := {} }], entry := ⟨0⟩ }
        wasm :=
          { initial with
            mem := ((initial.mem.write32 0 33).write32 4 11).write32 8 22 } } }

/-- Closed state-sensitive Iris proof for the first sorting kernel.  The
physical post-state contains the same three words, with pivot `22` at address
four and the unsigned left/right partition predicates established. -/
theorem partitionThreeWords_store_partiallyMeets :
    PartiallyMeets partitionThreeWordsAdequacyConfig
      (fun values store =>
        values = [] ∧
          store.wasm.mem.read32 0 = 11 ∧
          store.wasm.mem.read32 4 = 22 ∧
          store.wasm.mem.read32 8 = 33 ∧
          store.wasm.mem.read32 0 ≤ store.wasm.mem.read32 4 ∧
          store.wasm.mem.read32 4 ≤ store.wasm.mem.read32 8) := by
  apply wasm_smallStep_heap_globals_runtime_store_partiallyMeets
    (α := Unit)
    (σ := partitionThreeWordsHeap)
    (globalσ := (∅ : WasmGlobalMap Value))
  · apply partitionThreeWordsHeap_agrees
  · apply partitionThreeWordsHeap_inBounds
    native_decide
  · intro index value hget
    rw [get?_empty] at hget
    contradiction
  · decide
  · intro gs
    simp only [BI.BigSepM.bigSepM_empty.to_eq]
    iintro ⟨Hbytes, _Hglobals, _Hruntime⟩
    ihave Hwords := partitionThreeWordsHeap_pointsTo $$ Hbytes
    simp only [partitionThreeWordsAdequacyConfig,
      partitionThreeWordsAdequacyModule]
    have hpost : ∀ values : List Value,
        (iprop% ⌜values = []⌝ ∗
          pointsTo_u32 0 0 11 ∗ pointsTo_u32 0 4 22 ∗
          pointsTo_u32 0 8 33) ⊢
        (iprop% ∀ (store : MachineStore Unit)
            (_observations : List StepKind),
          stateInterp (GF := WasmHeapGF Unit) store 0 [] 0 -∗
          ⌜values = [] ∧
            store.wasm.mem.read32 0 = 11 ∧
            store.wasm.mem.read32 4 = 22 ∧
            store.wasm.mem.read32 8 = 33 ∧
            store.wasm.mem.read32 0 ≤ store.wasm.mem.read32 4 ∧
            store.wasm.mem.read32 4 ≤ store.wasm.mem.read32 8⌝) := by
      intro values
      iintro ⟨%hvalues, H0, H4, H8⟩
        %store %_observations Hstate
      imod stateInterp_pointsTo_u32_facts_frame
        store 0 [] 0 0 11
        (by decide) (by decide) (by decide) $$
          [$Hstate $H0] with ⟨Hstate, _H0, %Hfacts0⟩
      imod stateInterp_pointsTo_u32_facts_frame
        store 0 [] 0 4 22
        (by decide) (by decide) (by decide) $$
          [$Hstate $H4] with ⟨Hstate, _H4, %Hfacts4⟩
      imod stateInterp_pointsTo_u32_facts
        store 0 [] 0 8 33
        (by decide) (by decide) (by decide) $$
          [$Hstate $H8] with %Hfacts8
      ipureintro
      exact ⟨hvalues, Hfacts0.1, Hfacts4.1, Hfacts8.1,
        by rw [Hfacts0.1, Hfacts4.1]; decide,
        by rw [Hfacts4.1, Hfacts8.1]; decide⟩
    iapply wp_mono hpost
    iapply wp_partitionThreeWords
    iexact Hwords

/-! ### Merge of two singleton sorted runs -/

private def mergeTwoWordsHeap : WasmHeapMap (Option UInt8) :=
  store32Heap (store32Heap ∅ 0 0 9) 0 4 4

private theorem mergeTwoWordsHeap_agrees (memory : Mem) :
    heapAgreesWithMem mergeTwoWordsHeap
      (fun id => if id = 0 then some ((memory.write32 0 9).write32 4 4) else none) := by
  unfold mergeTwoWordsHeap
  apply store32_sound0 (mem := memory.write32 0 9) (h1 := rfl) (h2 := rfl) (h3 := rfl)
  apply store32_sound0 (mem := memory) (h1 := rfl) (h2 := rfl) (h3 := rfl)
  exact emptyHeap_agrees _

private theorem mergeTwoWordsHeap_inBounds (memory : Mem)
    (hpages : 1 ≤ memory.pages) :
    heapAddressesInBounds mergeTwoWordsHeap
      (fun id => if id = 0 then some ((memory.write32 0 9).write32 4 4) else none) := by
  unfold mergeTwoWordsHeap
  have hcapacity :
      65536 ≤ memory.pages * 65536 :=
    Nat.mul_le_mul_right 65536 hpages
  apply store32_inBounds0 (mem := memory.write32 0 9) (h1 := rfl) (h2 := rfl) (h3 := rfl)
  · simp only [UInt32.toNat_ofNat, Mem.write32]
    omega
  · apply store32_inBounds0 (mem := memory) (h1 := rfl) (h2 := rfl) (h3 := rfl)
    · simp only [UInt32.toNat_zero, Nat.zero_add]
      omega
    · exact emptyHeap_inBounds _

private theorem mergeTwoWordsHeap_pointsTo [WasmHeapGS α] :
    ([∗map] address ↦ value ∈ mergeTwoWordsHeap,
      pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        address (DFrac.own 1) value) ⊢
      pointsTo_u32 0 0 9 ∗ pointsTo_u32 0 4 4 := by
  unfold mergeTwoWordsHeap
  iintro Hheap
  ihave H4 := store32Heap_pointsTo (store32Heap ∅ 0 0 9) 0 4 4
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
    (by decide) (by decide) (by decide) $$ Hheap
  icases H4 with ⟨H4, Hheap⟩
  ihave H0 := store32Heap_pointsTo (∅ : WasmHeapMap (Option UInt8)) 0 0 9
    (get?_empty (⟨0, 0⟩ : MemoryKey)) (get?_empty (⟨0, 1⟩ : MemoryKey))
    (get?_empty (⟨0, 2⟩ : MemoryKey)) (get?_empty (⟨0, 3⟩ : MemoryKey))
    (by decide) (by decide) (by decide) $$ Hheap
  icases H0 with ⟨H0, _Hempty⟩
  iframe

def mergeTwoWordsAdequacyModule : Module :=
  { funcs :=
      [{ locals := [.i32, .i32]
         body :=
          [ .const 0, .load32 0, .localSet 0,
            .const 4, .load32 0, .localSet 1,
            .localGet 0, .localGet 1, .ltU,
            .iff 0 0
              [ .const 0, .localGet 0, .store32 0,
                .const 4, .localGet 1, .store32 0 ]
              [ .const 0, .localGet 1, .store32 0,
                .const 4, .localGet 0, .store32 0 ] ] }]
    memory := some { pagesMin := 1 } }

def mergeTwoWordsAdequacyConfig : Config Unit :=
  let initial : Store Unit := mergeTwoWordsAdequacyModule.initialStore
  { expr := .running
      ⟨⟨[], [.i32 0, .i32 0], []⟩,
        [ .const 0, .load32 0, .localSet 0,
          .const 4, .load32 0, .localSet 1,
          .localGet 0, .localGet 1, .ltU,
          .iff 0 0
            [ .const 0, .localGet 0, .store32 0,
              .const 4, .localGet 1, .store32 0 ]
            [ .const 0, .localGet 1, .store32 0,
              .const 4, .localGet 0, .store32 0 ] ],
        0, [], [], []⟩
    store :=
      { runtime := { instances := #[{ module := mergeTwoWordsAdequacyModule, host := {} }], entry := ⟨0⟩ }
        wasm :=
          { initial with
            mem := (initial.mem.write32 0 9).write32 4 4 } } }

/-- State-sensitive Iris adequacy for a real compare-and-branch merge. The two
singleton input runs are preserved and sorted in the reached physical memory. -/
theorem mergeTwoWords_store_partiallyMeets :
    PartiallyMeets mergeTwoWordsAdequacyConfig
      (fun values store =>
        values = [] ∧
          store.wasm.mem.read32 0 = 4 ∧
          store.wasm.mem.read32 4 = 9 ∧
          store.wasm.mem.read32 0 ≤ store.wasm.mem.read32 4) := by
  apply wasm_smallStep_heap_globals_runtime_store_partiallyMeets
    (α := Unit)
    (σ := mergeTwoWordsHeap)
    (globalσ := (∅ : WasmGlobalMap Value))
  · apply mergeTwoWordsHeap_agrees
  · apply mergeTwoWordsHeap_inBounds
    native_decide
  · intro index value hget
    rw [get?_empty] at hget
    contradiction
  · decide
  · intro gs
    simp only [BI.BigSepM.bigSepM_empty.to_eq]
    iintro ⟨Hbytes, _Hglobals, _Hruntime⟩
    ihave Hwords := mergeTwoWordsHeap_pointsTo $$ Hbytes
    simp only [mergeTwoWordsAdequacyConfig,
      mergeTwoWordsAdequacyModule]
    have hpost : ∀ values : List Value,
        (iprop% ⌜values = []⌝ ∗
          pointsTo_u32 0 0 4 ∗ pointsTo_u32 0 4 9) ⊢
        (iprop% ∀ (store : MachineStore Unit)
            (_observations : List StepKind),
          stateInterp (GF := WasmHeapGF Unit) store 0 [] 0 -∗
          ⌜values = [] ∧
            store.wasm.mem.read32 0 = 4 ∧
            store.wasm.mem.read32 4 = 9 ∧
            store.wasm.mem.read32 0 ≤ store.wasm.mem.read32 4⌝) := by
      intro values
      iintro ⟨%hvalues, H0, H4⟩ %store %_observations Hstate
      imod stateInterp_pointsTo_u32_facts_frame
        store 0 [] 0 0 4
        (by decide) (by decide) (by decide) $$
          [$Hstate $H0] with ⟨Hstate, _H0, %Hfacts0⟩
      imod stateInterp_pointsTo_u32_facts
        store 0 [] 0 4 9
        (by decide) (by decide) (by decide) $$
          [$Hstate $H4] with %Hfacts4
      ipureintro
      exact ⟨hvalues, Hfacts0.1, Hfacts4.1,
        by rw [Hfacts0.1, Hfacts4.1]; decide⟩
    iapply wp_mono hpost
    iapply wp_mergeTwoWords
    iexact Hwords

/-! ### Bulk-memory examples -/

private def fillFourBytesHeap (oldWord : UInt32) :
    WasmHeapMap (Option UInt8) :=
  store32Heap (store32Heap ∅ 0 16 oldWord) 0 32 0x12345678

private theorem fillFourBytesHeap_agrees (memory : Mem)
    (oldWord : UInt32) :
    heapAgreesWithMem (fillFourBytesHeap oldWord)
      (fun id => if id = 0 then some ((memory.write32 16 oldWord).write32 32 0x12345678) else none) := by
  unfold fillFourBytesHeap
  apply store32_sound0 (mem := memory.write32 16 oldWord) (h1 := rfl) (h2 := rfl) (h3 := rfl)
  apply store32_sound0 (mem := memory) (h1 := rfl) (h2 := rfl) (h3 := rfl)
  exact emptyHeap_agrees _

private theorem fillFourBytesHeap_inBounds (memory : Mem)
    (oldWord : UInt32) (hpages : 1 ≤ memory.pages) :
    heapAddressesInBounds (fillFourBytesHeap oldWord)
      (fun id => if id = 0 then some ((memory.write32 16 oldWord).write32 32 0x12345678) else none) := by
  unfold fillFourBytesHeap
  apply store32_inBounds0 (mem := memory.write32 16 oldWord) (h1 := rfl) (h2 := rfl) (h3 := rfl)
  · have hcapacity :
        65536 ≤ memory.pages * 65536 :=
      Nat.mul_le_mul_right 65536 hpages
    simp only [UInt32.toNat_ofNat, Mem.write32]
    omega
  · apply store32_inBounds0 (mem := memory) (h1 := rfl) (h2 := rfl) (h3 := rfl)
    · have hcapacity :
          65536 ≤ memory.pages * 65536 :=
        Nat.mul_le_mul_right 65536 hpages
      simp only [UInt32.toNat_ofNat]
      omega
    · exact emptyHeap_inBounds _

private theorem fillFourBytesHeap_pointsTo (oldWord : UInt32)
    [WasmHeapGS α] :
    ([∗map] address ↦ value ∈ fillFourBytesHeap oldWord,
      pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        address (DFrac.own 1) value) ⊢
      pointsTo_u32 0 16 oldWord ∗ pointsTo_u32 0 32 0x12345678 := by
  unfold fillFourBytesHeap
  iintro Hheap
  have mk_ne : ∀ a b : UInt32, a ≠ b → (⟨0, a⟩ : MemoryKey) ≠ ⟨0, b⟩ :=
    fun a b h hh => h (congrArg MemoryKey.addr hh)
  have hnone (address : UInt32)
      (h0 : 16 ≠ address) (h1 : 16 + 1 ≠ address)
      (h2 : 16 + 2 ≠ address) (h3 : 16 + 3 ≠ address) :
      get? (store32Heap ∅ 0 16 oldWord) ⟨0, address⟩ = none := by
    unfold store32Heap
    rw [get?_insert_ne (mk_ne _ _ h3), get?_insert_ne (mk_ne _ _ h2),
      get?_insert_ne (mk_ne _ _ h1), get?_insert_ne (mk_ne _ _ h0),
      get?_empty]
  ihave H32 := store32Heap_pointsTo
    (store32Heap ∅ 0 16 oldWord) 0 32 0x12345678
    (hnone 32 (by decide) (by decide) (by decide) (by decide))
    (hnone (32 + 1) (by decide) (by decide) (by decide) (by decide))
    (hnone (32 + 2) (by decide) (by decide) (by decide) (by decide))
    (hnone (32 + 3) (by decide) (by decide) (by decide) (by decide))
    (by decide) (by decide) (by decide) $$ Hheap
  icases H32 with ⟨H32, Hheap⟩
  ihave H16 := store32Heap_pointsTo
    (∅ : WasmHeapMap (Option UInt8)) 0 16 oldWord
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
    (by decide) (by decide) (by decide) $$ Hheap
  icases H16 with ⟨H16, _Hempty⟩
  iframe

def fillFourBytesAdequacyModule : Module :=
  { funcs :=
      [{ body :=
          [ .const 16, .const 0xAB, .const 4, .memoryFill,
            .const 16, .load32 0,
            .const 32, .load32 0 ],
         results := [.i32, .i32] }]
    memory := some { pagesMin := 1 } }

def fillFourBytesAdequacyConfig (oldWord : UInt32) : Config Unit :=
  let initial : Store Unit := fillFourBytesAdequacyModule.initialStore
  { expr := .running
      ⟨⟨[], [], []⟩,
        [ .const 16, .const 0xAB, .const 4, .memoryFill,
          .const 16, .load32 0,
          .const 32, .load32 0 ],
        2, [], [], []⟩
    store :=
      { runtime := { instances := #[{ module := fillFourBytesAdequacyModule, host := {} }], entry := ⟨0⟩ }
        wasm :=
          { initial with
            mem := (initial.mem.write32 16 oldWord).write32
              32 0x12345678 } } }

/-- The four-byte fill updates its physical target and frames the disjoint
word at address 32 unchanged. -/
theorem fillFourBytes_store_partiallyMeets (oldWord : UInt32) :
    PartiallyMeets (fillFourBytesAdequacyConfig oldWord)
      (fun values store =>
        values = [.i32 0x12345678, .i32 0xABABABAB] ∧
          store.wasm.mem.read32 16 = 0xABABABAB ∧
          store.wasm.mem.read32 32 = 0x12345678) := by
  apply wasm_smallStep_heap_globals_runtime_store_partiallyMeets
    (α := Unit)
    (σ := fillFourBytesHeap oldWord)
    (globalσ := (∅ : WasmGlobalMap Value))
  · apply fillFourBytesHeap_agrees
  · apply fillFourBytesHeap_inBounds
    native_decide
  · intro index value hget
    rw [get?_empty] at hget
    contradiction
  · simp only [fillFourBytesAdequacyConfig]; decide
  · intro gs
    simp only [BI.BigSepM.bigSepM_empty.to_eq]
    iintro ⟨Hbytes, _Hglobals, _Hruntime⟩
    ihave Hwords := fillFourBytesHeap_pointsTo oldWord $$ Hbytes
    simp only [fillFourBytesAdequacyConfig, fillFourBytesAdequacyModule]
    have hpost : ∀ values : List Value,
        (iprop% ⌜values = [.i32 0x12345678, .i32 0xABABABAB]⌝ ∗
          pointsTo_u32 0 16 0xABABABAB ∗
          pointsTo_u32 0 32 0x12345678) ⊢
        (iprop% ∀ (store : MachineStore Unit)
            (_observations : List StepKind),
          stateInterp (GF := WasmHeapGF Unit) store 0 [] 0 -∗
          ⌜values = [.i32 0x12345678, .i32 0xABABABAB] ∧
            store.wasm.mem.read32 16 = 0xABABABAB ∧
            store.wasm.mem.read32 32 = 0x12345678⌝) := by
      intro values
      iintro ⟨%hvalues, H16, H32⟩
        %store %_observations Hstate
      imod stateInterp_pointsTo_u32_facts_frame
        store 0 [] 0 16 0xABABABAB
        (by decide) (by decide) (by decide) $$
          [$Hstate $H16] with ⟨Hstate, _H16, %Hfacts16⟩
      imod stateInterp_pointsTo_u32_facts
        store 0 [] 0 32 0x12345678
        (by decide) (by decide) (by decide) $$
          [$Hstate $H32] with %Hfacts32
      ipureintro
      exact ⟨hvalues, Hfacts16.1, Hfacts32.1⟩
    iapply wp_mono hpost
    iapply wp_fillFourBytes oldWord
    iexact Hwords

private def copyWordHeap (oldDestination : UInt32) :
    WasmHeapMap (Option UInt8) :=
  store32Heap (store32Heap ∅ 0 0 0x04030201) 0 8 oldDestination

private theorem copyWordHeap_agrees (memory : Mem)
    (oldDestination : UInt32) :
    heapAgreesWithMem (copyWordHeap oldDestination)
      (fun id => if id = 0 then some ((memory.write32 0 0x04030201).write32 8 oldDestination) else none) := by
  unfold copyWordHeap
  apply store32_sound0 (mem := memory.write32 0 0x04030201) (h1 := rfl) (h2 := rfl) (h3 := rfl)
  apply store32_sound0 (mem := memory) (h1 := rfl) (h2 := rfl) (h3 := rfl)
  exact emptyHeap_agrees _

private theorem copyWordHeap_inBounds (memory : Mem)
    (oldDestination : UInt32) (hpages : 1 ≤ memory.pages) :
    heapAddressesInBounds (copyWordHeap oldDestination)
      (fun id => if id = 0 then some ((memory.write32 0 0x04030201).write32 8 oldDestination) else none) := by
  unfold copyWordHeap
  apply store32_inBounds0 (mem := memory.write32 0 0x04030201) (h1 := rfl) (h2 := rfl) (h3 := rfl)
  · have hcapacity :
        65536 ≤ memory.pages * 65536 :=
      Nat.mul_le_mul_right 65536 hpages
    simp only [UInt32.toNat_ofNat, Mem.write32]
    omega
  · apply store32_inBounds0 (mem := memory) (h1 := rfl) (h2 := rfl) (h3 := rfl)
    · have hcapacity :
          65536 ≤ memory.pages * 65536 :=
        Nat.mul_le_mul_right 65536 hpages
      simp only [UInt32.toNat_zero, Nat.zero_add]
      omega
    · exact emptyHeap_inBounds _

private theorem copyWordHeap_pointsTo (oldDestination : UInt32)
    [WasmHeapGS α] :
    ([∗map] address ↦ value ∈ copyWordHeap oldDestination,
      pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        address (DFrac.own 1) value) ⊢
      pointsTo_u32 0 0 0x04030201 ∗ pointsTo_u32 0 8 oldDestination := by
  unfold copyWordHeap
  iintro Hheap
  ihave H8 := store32Heap_pointsTo
    (store32Heap ∅ 0 0 0x04030201) 0 8 oldDestination
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
    (by decide) (by decide) (by decide) $$ Hheap
  icases H8 with ⟨H8, Hheap⟩
  ihave H0 := store32Heap_pointsTo
    (∅ : WasmHeapMap (Option UInt8)) 0 0 0x04030201
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
    (by decide) (by decide) (by decide) $$ Hheap
  icases H0 with ⟨H0, _Hempty⟩
  iframe

def copyWordAdequacyModule : Module :=
  { funcs :=
      [{ body :=
          [ .const 8, .const 0, .const 4, .memoryCopy,
            .const 8, .load32 0 ],
         results := [.i32] }]
    memory := some { pagesMin := 1 } }

def copyWordAdequacyConfig (oldDestination : UInt32) : Config Unit :=
  let initial : Store Unit := copyWordAdequacyModule.initialStore
  { expr := .running
      ⟨⟨[], [], []⟩,
        [ .const 8, .const 0, .const 4, .memoryCopy,
          .const 8, .load32 0 ],
        1, [], [], []⟩
    store :=
      { runtime := { instances := #[{ module := copyWordAdequacyModule, host := {} }], entry := ⟨0⟩ }
        wasm :=
          { initial with
            mem := (initial.mem.write32 0 0x04030201).write32
              8 oldDestination } } }

/-- The aligned copy preserves the physical source word and replaces the
physical destination word with its value. -/
theorem copyWord_store_partiallyMeets (oldDestination : UInt32) :
    PartiallyMeets (copyWordAdequacyConfig oldDestination)
      (fun values store =>
        values = [.i32 0x04030201] ∧
          store.wasm.mem.read32 0 = 0x04030201 ∧
          store.wasm.mem.read32 8 = 0x04030201) := by
  apply wasm_smallStep_heap_globals_runtime_store_partiallyMeets
    (α := Unit)
    (σ := copyWordHeap oldDestination)
    (globalσ := (∅ : WasmGlobalMap Value))
  · apply copyWordHeap_agrees
  · apply copyWordHeap_inBounds
    native_decide
  · intro index value hget
    rw [get?_empty] at hget
    contradiction
  · simp only [copyWordAdequacyConfig]; decide
  · intro gs
    simp only [BI.BigSepM.bigSepM_empty.to_eq]
    iintro ⟨Hbytes, _Hglobals, _Hruntime⟩
    ihave Hwords := copyWordHeap_pointsTo oldDestination $$ Hbytes
    simp only [copyWordAdequacyConfig, copyWordAdequacyModule]
    have hpost : ∀ values : List Value,
        (iprop% ⌜values = [.i32 0x04030201]⌝ ∗
          pointsTo_u32 0 0 0x04030201 ∗
          pointsTo_u32 0 8 0x04030201) ⊢
        (iprop% ∀ (store : MachineStore Unit)
            (_observations : List StepKind),
          stateInterp (GF := WasmHeapGF Unit) store 0 [] 0 -∗
          ⌜values = [.i32 0x04030201] ∧
            store.wasm.mem.read32 0 = 0x04030201 ∧
            store.wasm.mem.read32 8 = 0x04030201⌝) := by
      intro values
      iintro ⟨%hvalues, H0, H8⟩
        %store %_observations Hstate
      imod stateInterp_pointsTo_u32_facts_frame
        store 0 [] 0 0 0x04030201
        (by decide) (by decide) (by decide) $$
          [$Hstate $H0] with ⟨Hstate, _H0, %Hfacts0⟩
      imod stateInterp_pointsTo_u32_facts
        store 0 [] 0 8 0x04030201
        (by decide) (by decide) (by decide) $$
          [$Hstate $H8] with %Hfacts8
      ipureintro
      exact ⟨hvalues, Hfacts0.1, Hfacts8.1⟩
    iapply wp_mono hpost
    iapply wp_copyWord oldDestination
    iexact Hwords

private def copyOverlapWordHeap : WasmHeapMap (Option UInt8) :=
  store64Heap ∅ 0 0 0x8877665544332211

private theorem copyOverlapWordHeap_agrees (memory : Mem) :
    heapAgreesWithMem copyOverlapWordHeap
      (fun id => if id = 0 then some (memory.write64 0 0x8877665544332211) else none) := by
  unfold copyOverlapWordHeap
  apply store64_sound0 (mem := memory)
    (h1 := rfl) (h2 := rfl) (h3 := rfl) (h4 := rfl) (h5 := rfl) (h6 := rfl) (h7 := rfl)
  exact emptyHeap_agrees _

private theorem copyOverlapWordHeap_inBounds (memory : Mem)
    (hpages : 1 ≤ memory.pages) :
    heapAddressesInBounds copyOverlapWordHeap
      (fun id => if id = 0 then some (memory.write64 0 0x8877665544332211) else none) := by
  unfold copyOverlapWordHeap
  apply store64_inBounds0 (mem := memory)
    (h1 := rfl) (h2 := rfl) (h3 := rfl) (h4 := rfl) (h5 := rfl) (h6 := rfl) (h7 := rfl)
  · have hcapacity :
        65536 ≤ memory.pages * 65536 :=
      Nat.mul_le_mul_right 65536 hpages
    simp only [UInt32.toNat_zero, Nat.zero_add]
    omega
  · exact emptyHeap_inBounds _

private theorem copyOverlapWordHeap_pointsTo [WasmHeapGS α] :
    ([∗map] address ↦ value ∈ copyOverlapWordHeap,
      pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        address (DFrac.own 1) value) ⊢
      pointsTo_u64 0 0 0x8877665544332211 := by
  unfold copyOverlapWordHeap
  iintro Hheap
  ihave Hword := store64Heap_pointsTo
    (∅ : WasmHeapMap (Option UInt8)) 0 0 0x8877665544332211
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) $$ Hheap
  icases Hword with ⟨Hword, _Hempty⟩
  iexact Hword

def copyOverlapWordAdequacyModule : Module :=
  { funcs :=
      [{ body :=
          [ .const 2, .const 0, .const 4, .memoryCopy,
            .const 0, .load64 0 ],
         results := [.i64] }]
    memory := some { pagesMin := 1 } }

def copyOverlapWordAdequacyConfig : Config Unit :=
  let initial : Store Unit := copyOverlapWordAdequacyModule.initialStore
  { expr := .running
      ⟨⟨[], [], []⟩,
        [ .const 2, .const 0, .const 4, .memoryCopy,
          .const 0, .load64 0 ],
        1, [], [], []⟩
    store :=
      { runtime := { instances := #[{ module := copyOverlapWordAdequacyModule, host := {} }], entry := ⟨0⟩ }
        wasm :=
          { initial with
            mem := initial.mem.write64 0 0x8877665544332211 } } }

/-- State-sensitive Iris adequacy for overlapping `memory.copy`: the reached
physical word is the memmove result, demonstrating that the source bytes were
snapshotted before the overlapping destination was written. -/
theorem copyOverlapWord_store_partiallyMeets :
    PartiallyMeets copyOverlapWordAdequacyConfig
      (fun values store =>
        values = [.i64 0x8877443322112211] ∧
          store.wasm.mem.read64 0 = 0x8877443322112211) := by
  apply wasm_smallStep_heap_globals_runtime_store_partiallyMeets
    (α := Unit)
    (σ := copyOverlapWordHeap)
    (globalσ := (∅ : WasmGlobalMap Value))
  · apply copyOverlapWordHeap_agrees
  · apply copyOverlapWordHeap_inBounds
    native_decide
  · intro index value hget
    rw [get?_empty] at hget
    contradiction
  · decide
  · intro gs
    simp only [BI.BigSepM.bigSepM_empty.to_eq]
    iintro ⟨Hbytes, _Hglobals, _Hruntime⟩
    ihave Hword := copyOverlapWordHeap_pointsTo $$ Hbytes
    simp only [copyOverlapWordAdequacyConfig,
      copyOverlapWordAdequacyModule]
    have hpost : ∀ values : List Value,
        (iprop% ⌜values = [.i64 0x8877443322112211]⌝ ∗
          pointsTo_u64 0 0 0x8877443322112211) ⊢
        (iprop% ∀ (store : MachineStore Unit)
            (_observations : List StepKind),
          stateInterp (GF := WasmHeapGF Unit) store 0 [] 0 -∗
          ⌜values = [.i64 0x8877443322112211] ∧
            store.wasm.mem.read64 0 = 0x8877443322112211⌝) := by
      intro values
      iintro ⟨%hvalues, Hword⟩
        %store %_observations Hstate
      imod stateInterp_pointsTo_u64_facts
        store 0 [] 0 0 0x8877443322112211
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) $$
          [$Hstate $Hword] with %Hfacts
      ipureintro
      exact ⟨hvalues, Hfacts.1⟩
    iapply wp_mono hpost
    iapply wp_copyOverlapWord
    iexact Hword

private def memoryInitDropHeap : WasmHeapMap (Option UInt8) :=
  store32Heap ∅ 0 16 0

private theorem memoryInitDropHeap_agrees (memory : Mem) :
    heapAgreesWithMem memoryInitDropHeap
      (fun id => if id = 0 then some (memory.write32 16 0) else none) := by
  unfold memoryInitDropHeap
  apply store32_sound0 (mem := memory) (h1 := rfl) (h2 := rfl) (h3 := rfl)
  exact emptyHeap_agrees _

private theorem memoryInitDropHeap_inBounds (memory : Mem)
    (hpages : 1 ≤ memory.pages) :
    heapAddressesInBounds memoryInitDropHeap
      (fun id => if id = 0 then some (memory.write32 16 0) else none) := by
  unfold memoryInitDropHeap
  apply store32_inBounds0 (mem := memory) (h1 := rfl) (h2 := rfl) (h3 := rfl)
  · have hcapacity :
        65536 ≤ memory.pages * 65536 :=
      Nat.mul_le_mul_right 65536 hpages
    simp only [UInt32.toNat_ofNat]
    omega
  · exact emptyHeap_inBounds _

private theorem memoryInitDropHeap_pointsTo [WasmHeapGS α] :
    ([∗map] address ↦ value ∈ memoryInitDropHeap,
      pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        address (DFrac.own 1) value) ⊢
      pointsTo_u32 0 16 0 := by
  unfold memoryInitDropHeap
  iintro Hheap
  ihave Hword := store32Heap_pointsTo
    (∅ : WasmHeapMap (Option UInt8)) 0 16 0
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) $$ Hheap
  icases Hword with ⟨Hword, _Hempty⟩
  iexact Hword

private def memoryInitDropSegments :
    WasmDataSegmentMap (Option (List UInt8)) :=
  insert ∅ (⟨0, 0⟩ : DataSegmentKey) (some [1, 2, 3, 4])

private theorem memoryInitDropSegments_agree :
    dataSegmentHeapAgrees memoryInitDropSegments
      [some [1, 2, 3, 4]] := by
  intro index value hget
  unfold memoryInitDropSegments at hget
  by_cases hindex : index = 0
  · subst index
    simp only [get?_insert_eq rfl, Option.some.injEq] at hget
    subst value
    rfl
  · rw [get?_insert_ne (fun h => hindex (congrArg DataSegmentKey.index h).symm), get?_empty] at hget
    contradiction

private theorem memoryInitDropSegments_pointsTo [WasmDataSegmentGS α] :
    ([∗map] index ↦ value ∈ memoryInitDropSegments,
      dataSegmentPointsTo index value) ⊢
      dataSegmentPointsTo ⟨0, 0⟩ (some [1, 2, 3, 4]) := by
  unfold memoryInitDropSegments
  rw [(BI.BigSepM.bigSepM_insert (get?_empty (⟨0, 0⟩ : DataSegmentKey))).to_eq,
    BI.BigSepM.bigSepM_empty.to_eq, BI.sep_emp.to_eq]

def memoryInitDropAdequacyModule : Module :=
  { funcs :=
      [{ body :=
          [ .const 16, .const 0, .const 4, .memoryInit 0,
            .dataDrop 0, .const 16, .load32 0 ],
         results := [.i32] }]
    memory := some
      { pagesMin := 1
        data := [{ offset := none, bytes := [1, 2, 3, 4] }] } }

def memoryInitDropAdequacyConfig : Config Unit :=
  let initial : Store Unit := memoryInitDropAdequacyModule.initialStore
  { expr := .running
      ⟨⟨[], [], []⟩,
        [ .const 16, .const 0, .const 4, .memoryInit 0,
          .dataDrop 0, .const 16, .load32 0 ],
        1, [], [], []⟩
    store :=
      { runtime := { instances := #[{ module := memoryInitDropAdequacyModule, host := {} }], entry := ⟨0⟩ }
        wasm := { initial with mem := initial.mem.write32 16 0 } } }

/-- Closed physical-state specification for passive data initialization and
consumption. It proves the initialized word and that the segment is dropped
in the reached machine store. -/
theorem memoryInitDrop_store_partiallyMeets :
    PartiallyMeets memoryInitDropAdequacyConfig
      (fun values store =>
        values = [.i32 0x04030201] ∧
          store.wasm.mem.read32 16 = 0x04030201 ∧
          store.wasm.dataSegments[0]? = some none) := by
  apply
    wasm_smallStep_heap_globals_segments_runtime_store_partiallyMeets
      (α := Unit)
      (σ := memoryInitDropHeap)
      (globalσ := (∅ : WasmGlobalMap Value))
      (dataSegmentσ := memoryInitDropSegments)
  · apply memoryInitDropHeap_agrees
  · apply memoryInitDropHeap_inBounds
    native_decide
  · intro index value hget
    rw [get?_empty] at hget
    contradiction
  · exact memoryInitDropSegments_agree
  · decide
  · intro gs
    simp only [BI.BigSepM.bigSepM_empty.to_eq]
    iintro ⟨Hbytes, _Hglobals, Hsegments, _Hruntime⟩
    ihave Hword := memoryInitDropHeap_pointsTo $$ Hbytes
    ihave Hsegment := memoryInitDropSegments_pointsTo $$ Hsegments
    simp only [memoryInitDropAdequacyConfig,
      memoryInitDropAdequacyModule]
    have hpost : ∀ values : List Value,
        (iprop% ⌜values = [.i32 0x04030201]⌝ ∗
          pointsTo_u32 0 16 0x04030201 ∗
          dataSegmentPointsTo ⟨0, 0⟩ none) ⊢
        (iprop% ∀ (store : MachineStore Unit)
            (_observations : List StepKind),
          stateInterp (GF := WasmHeapGF Unit) store 0 [] 0 -∗
          ⌜values = [.i32 0x04030201] ∧
            store.wasm.mem.read32 16 = 0x04030201 ∧
            store.wasm.dataSegments[0]? = some none⌝) := by
      intro values
      iintro ⟨%hvalues, Hword, Hsegment⟩
        %store %_observations Hstate
      imod stateInterp_pointsTo_u32_facts_frame
        store 0 [] 0 16 0x04030201
        (by decide) (by decide) (by decide) $$
          [$Hstate $Hword] with
        ⟨Hstate, Hword, %HwordFacts⟩
      simp only [← dataSegmentPointsToAt_eq]
      imod stateInterp_dataSegment_facts_frame
        store 0 [] 0 0 none $$ [$Hstate $Hsegment] with
        ⟨Hstate, Hsegment, %HsegmentFact⟩
      ipureintro
      constructor
      · exact hvalues
      constructor
      · exact HwordFacts.1
      · exact HsegmentFact
    iapply wp_mono hpost
    iapply wp_memoryInitDrop 0
    iframe

private def tableSetGetMap : WasmTableMap TableInst :=
  insert ∅ (⟨0, 0⟩ : TableKey) [.funcref none]

private theorem tableSetGetMap_agrees :
    tableHeapAgrees tableSetGetMap [[.funcref none]] := by
  intro index table hget
  unfold tableSetGetMap at hget
  by_cases hindex : index = 0
  · subst index
    simp only [get?_insert_eq rfl, Option.some.injEq] at hget
    subst table
    rfl
  · rw [get?_insert_ne (fun h => hindex (congrArg TableKey.index h).symm), get?_empty] at hget
    contradiction

private theorem tableSetGetMap_pointsTo [WasmTableGS α] :
    ([∗map] index ↦ table ∈ tableSetGetMap,
      tablePointsTo index table) ⊢
      tablePointsTo ⟨0, 0⟩ [.funcref none] := by
  unfold tableSetGetMap
  rw [(BI.BigSepM.bigSepM_insert (get?_empty (⟨0, 0⟩ : TableKey))).to_eq,
    BI.BigSepM.bigSepM_empty.to_eq, BI.sep_emp.to_eq]

def tableSetGetAdequacyModule : Module :=
  { funcs :=
      [{ body :=
          [ .const 0, .refFunc 1, .tableSet 0,
            .const 0, .tableGet 0, .refIsNull ],
         results := [.i32] },
       { body := [] }]
    tables := [{ min := 1, max := some 1 }] }

def tableSetGetAdequacyConfig : Config Unit :=
  { expr := .running
      ⟨⟨[], [], []⟩,
        [ .const 0, .refFunc 1, .tableSet 0,
          .const 0, .tableGet 0, .refIsNull ],
        1, [], [], []⟩
    store :=
      { runtime := { instances := #[{ module := tableSetGetAdequacyModule, host := {} }], entry := ⟨0⟩ }
        wasm := tableSetGetAdequacyModule.initialStore } }

/-- End-to-end Iris regression for authoritative tables: write a non-null
function reference, read it back, and prove both the returned null-test result
and the reached physical table contents. -/
theorem tableSetGet_store_partiallyMeets :
    PartiallyMeets tableSetGetAdequacyConfig
      (fun values store =>
        values = [.i32 0] ∧
          store.wasm.tables[0]? = some [.funcref (some 1)]) := by
  apply
    wasm_smallStep_heap_globals_segments_tables_runtime_store_partiallyMeets
      (α := Unit)
      (σ := (∅ : WasmHeapMap (Option UInt8)))
      (globalσ := (∅ : WasmGlobalMap Value))
      (dataSegmentσ :=
        (∅ : WasmDataSegmentMap (Option (List UInt8))))
      (tableσ := tableSetGetMap)
      (elementSegmentσ :=
        (∅ : WasmElementSegmentMap (Option (List (Option Nat)))))
  · exact heapAgreesWithMem_empty _
  · exact heapAddressesInBounds_empty _
  · exact globalHeapAgrees_empty _
  · exact dataSegmentHeapAgrees_empty _
  · exact tableSetGetMap_agrees
  · exact elementSegmentHeapAgrees_empty _
  · decide
  · intro gs
    simp only [BI.BigSepM.bigSepM_empty.to_eq]
    simp only [runtimeModuleOwn]
    iintro ⟨_Hbytes, _Hglobals, _Hsegments, Htables, _HelementSegments, _Hruntime, _HinstFrag⟩
    ihave Htable := tableSetGetMap_pointsTo $$ Htables
    simp only [tableSetGetAdequacyConfig, tableSetGetAdequacyModule]
    have hpost : ∀ values : List Value,
        (iprop% ⌜values = [.i32 0]⌝ ∗
          tablePointsTo ⟨0, 0⟩
            (listSetAt [.funcref none] (UInt32.toNat 0)
              (.funcref (some 1)))) ⊢
        (iprop% ∀ (store : MachineStore Unit)
            (_observations : List StepKind),
          stateInterp (GF := WasmHeapGF Unit) store 0 [] 0 -∗
          ⌜values = [.i32 0] ∧
            store.wasm.tables[0]? =
              some [.funcref (some 1)]⌝) := by
      intro values
      iintro ⟨%hvalues, Htable⟩
        %store %_observations Hstate
      simp only [← tablePointsToAt_eq]
      imod stateInterp_table_facts_frame
        store 0 [] 0 0
          (listSetAt [.funcref none] (UInt32.toNat 0)
            (.funcref (some 1))) $$
          [$Hstate $Htable] with
        ⟨Hstate, Htable, %Hphysical⟩
      ipureintro
      exact ⟨hvalues, by simpa [listSetAt] using Hphysical⟩
    iapply wp_mono hpost
    iapply wp_const
    inext
    iapply wp_pureStep _ _ _ (fun _ => Step.refFunc)
    inext
    simp only [← tablePointsToAt_eq]
    iapply wp_tableSet rfl (by decide) $$ Htable
    inext
    iintro Htable
    iapply wp_const
    inext
    iapply wp_tableGet (value := .funcref (some 1))
      rfl (by simp [listSetAt]) $$ Htable
    inext
    iintro Htable
    iapply wp_mono (fun _ => BI.sep_comm.mp)
    iapply wp_frame_l
    isplitl [Htable]
    · iexact Htable
    iapply wp_refIsNull rfl
    inext
    iapply wp_finish
    inext
    iapply wp_value'
    ipureintro
    rfl

def tableGrowFillAdequacyModule : Module :=
  { funcs :=
      [{ body :=
          [ .tableGrow 0, .const 0, .refFunc 1, .const 3, .tableFill 0,
            .const 0, .tableGet 0, .refIsNull ],
         results := [.i32] },
       { body := [] }]
    tables := [{ min := 1, max := some 3 }] }

def tableGrowFillAdequacyConfig : Config Unit :=
  { expr := .running
      ⟨⟨[], [], [.i32 2, .funcref (some 1)]⟩,
        [ .tableGrow 0, .const 0, .refFunc 1, .const 3, .tableFill 0,
          .const 0, .tableGet 0, .refIsNull ],
        1, [], [], []⟩
    store :=
      { runtime := { instances := #[{ module := tableGrowFillAdequacyModule, host := {} }], entry := ⟨0⟩ }
        wasm := tableGrowFillAdequacyModule.initialStore } }

/-- End-to-end growth regression for authoritative tables. The program grows
the table from one to three entries, fills the complete enlarged range with a
non-null function reference, reads the first entry, and proves the reached
physical table as well as the returned null test. -/
theorem tableGrowFill_store_partiallyMeets :
    PartiallyMeets tableGrowFillAdequacyConfig
      (fun values store =>
        values = [.i32 0] ∧
          store.wasm.tables[0]? =
            some [.funcref (some 1), .funcref (some 1),
              .funcref (some 1)]) := by
  apply
    wasm_smallStep_heap_globals_segments_tables_runtime_store_partiallyMeets
      (α := Unit)
      (σ := (∅ : WasmHeapMap (Option UInt8)))
      (globalσ := (∅ : WasmGlobalMap Value))
      (dataSegmentσ :=
        (∅ : WasmDataSegmentMap (Option (List UInt8))))
      (tableσ := tableSetGetMap)
      (elementSegmentσ :=
        (∅ : WasmElementSegmentMap (Option (List (Option Nat)))))
  · exact heapAgreesWithMem_empty _
  · exact heapAddressesInBounds_empty _
  · exact globalHeapAgrees_empty _
  · exact dataSegmentHeapAgrees_empty _
  · exact tableSetGetMap_agrees
  · exact elementSegmentHeapAgrees_empty _
  · decide
  · intro gs
    simp only [BI.BigSepM.bigSepM_empty.to_eq,
      tableGrowFillAdequacyConfig, RuntimeEnv.currentModule_mk1]
    iintro ⟨_Hbytes, _Hglobals, _Hsegments, Htables, _HelementSegments, HruntimeOwn⟩
    ihave Htable := tableSetGetMap_pointsTo $$ Htables
    have hpost : ∀ values : List Value,
        (iprop% ⌜values = [.i32 0]⌝ ∗
          tablePointsTo ⟨0, 0⟩
            (listWriteAt
              ([.funcref none] ++
                List.replicate (UInt32.toNat 2) (.funcref (some 1)))
              (UInt32.toNat 0)
              (List.replicate (UInt32.toNat 3)
                (.funcref (some 1))))) ⊢
        (iprop% ∀ (store : MachineStore Unit)
            (_observations : List StepKind),
          stateInterp (GF := WasmHeapGF Unit) store 0 [] 0 -∗
          ⌜values = [.i32 0] ∧
            store.wasm.tables[0]? =
              some [.funcref (some 1), .funcref (some 1),
                .funcref (some 1)]⌝) := by
      intro values
      iintro ⟨%hvalues, Htable⟩
        %store %_observations Hstate
      simp only [← tablePointsToAt_eq]
      imod stateInterp_table_facts_frame
        store 0 [] 0 0
          (listWriteAt
            ([.funcref none] ++
              List.replicate (UInt32.toNat 2) (.funcref (some 1)))
            (UInt32.toNat 0)
            (List.replicate (UInt32.toNat 3)
              (.funcref (some 1)))) $$
          [$Hstate $Htable] with
        ⟨Hstate, Htable, %Hphysical⟩
      ipureintro
      exact ⟨hvalues, by
        simpa [listWriteAt] using Hphysical⟩
    simp only [← tablePointsToAt_eq]
    iapply wp_tableGrow32 tableGrowFillAdequacyModule ⟨0⟩
      (tableIndex := 0) (table := [.funcref none])
      (delta := 2) (initial := .funcref (some 1)) (by decide) $$
        [$Htable $HruntimeOwn]
    inext
    iintro Htable _HruntimeOwn
    simp only [tableGrowFillAdequacyModule]
    iapply wp_mono hpost
    simp only [← tablePointsToAt_eq]
    iapply wp_const
    inext
    iapply wp_pureStep _ _ _ (fun _ => Step.refFunc)
    inext
    iapply wp_const
    inext
    iapply wp_tableFill
      (tableIndex := 0) (destination := .i32 0) (length := .i32 3)
      (value := .funcref (some 1))
      (table :=
        [.funcref none] ++
          List.replicate (UInt32.toNat 2) (.funcref (some 1)))
      rfl rfl (by decide) $$ Htable
    inext
    iintro Htable
    iapply wp_const
    inext
    iapply wp_tableGet (value := .funcref (some 1))
      rfl (by simp [listWriteAt]) $$ Htable
    inext
    iintro Htable
    iapply wp_mono (fun _ => BI.sep_comm.mp)
    iapply wp_frame_l
    isplitl [Htable]
    · iexact Htable
    iapply wp_refIsNull rfl
    inext
    iapply wp_finish
    inext
    iapply wp_value'
    ipureintro
    rfl

def tableGrow64FailureAdequacyModule : Module :=
  { funcs :=
      [{ body := [.tableGrow 0, .drop, .tableGrow 0],
         results := [.i64] }]
    tables := [{ min := 1, max := some 3, is64 := true }] }

def tableGrow64FailureAdequacyConfig : Config Unit :=
  { expr := .running
      ⟨⟨[], [],
          [.i64 2, .funcref (some 0), .i64 1, .funcref none]⟩,
        [.tableGrow 0, .drop, .tableGrow 0],
        1, [], [], []⟩
    store :=
      { runtime :=
          { instances := #[{ module := tableGrow64FailureAdequacyModule, host := {} }], entry := ⟨0⟩ }
        wasm := tableGrow64FailureAdequacyModule.initialStore } }

/-- Closed table64 regression covering both growth outcomes. The first grow
extends the table to its declared maximum, the second returns the 64-bit
all-ones failure sentinel, and the authoritative physical table remains at the
successfully grown contents. -/
theorem tableGrow64Failure_store_partiallyMeets :
    PartiallyMeets tableGrow64FailureAdequacyConfig
      (fun values store =>
        values = [.i64 (0xFFFFFFFFFFFFFFFF : UInt64)] ∧
          store.wasm.tables[0]? =
            some [.funcref none, .funcref (some 0),
              .funcref (some 0)]) := by
  apply
    wasm_smallStep_heap_globals_segments_tables_runtime_store_partiallyMeets
      (α := Unit)
      (σ := (∅ : WasmHeapMap (Option UInt8)))
      (globalσ := (∅ : WasmGlobalMap Value))
      (dataSegmentσ :=
        (∅ : WasmDataSegmentMap (Option (List UInt8))))
      (tableσ := tableSetGetMap)
      (elementSegmentσ :=
        (∅ : WasmElementSegmentMap (Option (List (Option Nat)))))
  · exact heapAgreesWithMem_empty _
  · exact heapAddressesInBounds_empty _
  · exact globalHeapAgrees_empty _
  · exact dataSegmentHeapAgrees_empty _
  · exact tableSetGetMap_agrees
  · exact elementSegmentHeapAgrees_empty _
  · decide
  · intro gs
    simp only [BI.BigSepM.bigSepM_empty.to_eq,
      tableGrow64FailureAdequacyConfig, RuntimeEnv.currentModule_mk1]
    iintro ⟨_Hbytes, _Hglobals, _Hsegments, Htables, _HelementSegments, HruntimeOwn⟩
    ihave Htable := tableSetGetMap_pointsTo $$ Htables
    have hpost : ∀ values : List Value,
        (iprop%
          ⌜values = [.i64 (0xFFFFFFFFFFFFFFFF : UInt64)]⌝ ∗
          tablePointsTo ⟨0, 0⟩
            ([.funcref none] ++
              List.replicate (UInt64.toNat 2)
                (.funcref (some 0)))) ⊢
        (iprop% ∀ (store : MachineStore Unit)
            (_observations : List StepKind),
          stateInterp (GF := WasmHeapGF Unit) store 0 [] 0 -∗
          ⌜values = [.i64 (0xFFFFFFFFFFFFFFFF : UInt64)] ∧
            store.wasm.tables[0]? =
              some [.funcref none, .funcref (some 0),
                .funcref (some 0)]⌝) := by
      intro values
      iintro ⟨%hvalues, Htable⟩
        %store %_observations Hstate
      simp only [← tablePointsToAt_eq]
      imod stateInterp_table_facts_frame
        store 0 [] 0 0
          ([.funcref none] ++
            List.replicate (UInt64.toNat 2) (.funcref (some 0))) $$
          [$Hstate $Htable] with
        ⟨Hstate, Htable, %Hphysical⟩
      ipureintro
      exact ⟨hvalues, by simpa using Hphysical⟩
    simp only [← tablePointsToAt_eq]
    iapply wp_tableGrow64 tableGrow64FailureAdequacyModule ⟨0⟩
      (tableIndex := 0) (table := [.funcref none])
      (delta := 2) (initial := .funcref (some 0)) (by decide) $$
        [$Htable $HruntimeOwn]
    inext
    iintro Htable HruntimeOwn
    iapply wp_pureStep _ _ _ (fun _ => Step.drop)
    inext
    iapply wp_tableGrow64Failure tableGrow64FailureAdequacyModule ⟨0⟩
      (tableIndex := 0)
      (table :=
        [.funcref none] ++
          List.replicate (UInt64.toNat 2) (.funcref (some 0)))
      (delta := 1) (initial := .funcref none) (by decide) $$
        [$Htable $HruntimeOwn]
    inext
    iintro Htable _HruntimeOwn
    iapply wp_mono hpost
    simp only [← tablePointsToAt_eq]
    iapply wp_mono (fun _ => BI.sep_comm.mp)
    iapply wp_frame_l
    isplitl [Htable]
    · iexact Htable
    iapply wp_finish
    inext
    iapply wp_value'
    ipureintro
    rfl

private def tableCopyOverlapMap : WasmTableMap TableInst :=
  insert ∅ (⟨0, 0⟩ : TableKey)
    [.funcref none, .funcref (some 0), .funcref (some 1),
      .funcref (some 2)]

private theorem tableCopyOverlapMap_agrees :
    tableHeapAgrees tableCopyOverlapMap
      [[.funcref none, .funcref (some 0), .funcref (some 1),
        .funcref (some 2)]] := by
  intro index table hget
  unfold tableCopyOverlapMap at hget
  by_cases hindex : index = 0
  · subst index
    simp only [get?_insert_eq rfl, Option.some.injEq] at hget
    subst table
    rfl
  · rw [get?_insert_ne (fun h => hindex (congrArg TableKey.index h).symm), get?_empty] at hget
    contradiction

private theorem tableCopyOverlapMap_pointsTo [WasmTableGS α] :
    ([∗map] index ↦ table ∈ tableCopyOverlapMap,
      tablePointsTo index table) ⊢
      tablePointsTo ⟨0, 0⟩
        [.funcref none, .funcref (some 0), .funcref (some 1),
          .funcref (some 2)] := by
  unfold tableCopyOverlapMap
  rw [(BI.BigSepM.bigSepM_insert (get?_empty (⟨0, 0⟩ : TableKey))).to_eq,
    BI.BigSepM.bigSepM_empty.to_eq, BI.sep_emp.to_eq]

def tableCopyOverlapAdequacyModule : Module :=
  { funcs := [{ body := [] }, { body := [] }, { body := [] }]
    tables := [{ min := 4, max := some 4 }] }

def tableCopyOverlapAdequacyConfig : Config Unit :=
  { expr := .running
      ⟨⟨[], [], [.i32 3, .i32 0, .i32 1]⟩,
        [.tableCopy 0 0], 0, [], [], []⟩
    store :=
      { runtime := { instances := #[{ module := tableCopyOverlapAdequacyModule, host := {} }], entry := ⟨0⟩ }
        wasm :=
          { tableCopyOverlapAdequacyModule.initialStore with
            tables :=
              [[.funcref none, .funcref (some 0),
                .funcref (some 1), .funcref (some 2)]] } } }

/-- Closed overlapping `table.copy` regression. Copying entries `[0, 3)` to
offset one must snapshot the old source range rather than cascading writes. -/
theorem tableCopyOverlap_store_partiallyMeets :
    PartiallyMeets tableCopyOverlapAdequacyConfig
      (fun values store =>
        values = [] ∧
          store.wasm.tables[0]? =
            some [.funcref none, .funcref none, .funcref (some 0),
              .funcref (some 1)]) := by
  apply
    wasm_smallStep_heap_globals_segments_tables_runtime_store_partiallyMeets
      (α := Unit)
      (σ := (∅ : WasmHeapMap (Option UInt8)))
      (globalσ := (∅ : WasmGlobalMap Value))
      (dataSegmentσ :=
        (∅ : WasmDataSegmentMap (Option (List UInt8))))
      (tableσ := tableCopyOverlapMap)
      (elementSegmentσ :=
        (∅ : WasmElementSegmentMap (Option (List (Option Nat)))))
  · exact heapAgreesWithMem_empty _
  · exact heapAddressesInBounds_empty _
  · exact globalHeapAgrees_empty _
  · exact dataSegmentHeapAgrees_empty _
  · exact tableCopyOverlapMap_agrees
  · exact elementSegmentHeapAgrees_empty _
  · decide
  · intro gs
    simp only [BI.BigSepM.bigSepM_empty.to_eq,
      tableCopyOverlapAdequacyConfig]
    simp only [runtimeModuleOwn]
    iintro ⟨_Hbytes, _Hglobals, _Hsegments, Htables, _HelementSegments, _Hruntime, _HinstFrag⟩
    ihave Htable := tableCopyOverlapMap_pointsTo $$ Htables
    have hpost : ∀ values : List Value,
        (iprop% ⌜values = []⌝ ∗
          tablePointsTo ⟨0, 0⟩
            (listWriteAt
              [.funcref none, .funcref (some 0),
                .funcref (some 1), .funcref (some 2)]
              (UInt32.toNat 1)
              (([.funcref none, .funcref (some 0),
                  .funcref (some 1), .funcref (some 2)].drop
                    (UInt32.toNat 0)).take (UInt32.toNat 3)))) ⊢
        (iprop% ∀ (store : MachineStore Unit)
            (_observations : List StepKind),
          stateInterp (GF := WasmHeapGF Unit) store 0 [] 0 -∗
          ⌜values = [] ∧
            store.wasm.tables[0]? =
              some [.funcref none, .funcref none, .funcref (some 0),
                .funcref (some 1)]⌝) := by
      intro values
      iintro ⟨%hvalues, Htable⟩
        %store %_observations Hstate
      simp only [← tablePointsToAt_eq]
      imod stateInterp_table_facts_frame
        store 0 [] 0 0
          (listWriteAt
            [.funcref none, .funcref (some 0),
              .funcref (some 1), .funcref (some 2)]
            (UInt32.toNat 1)
            (([.funcref none, .funcref (some 0),
                .funcref (some 1), .funcref (some 2)].drop
                  (UInt32.toNat 0)).take (UInt32.toNat 3))) $$
          [$Hstate $Htable] with
        ⟨Hstate, Htable, %Hphysical⟩
      ipureintro
      exact ⟨hvalues, by simpa [listWriteAt] using Hphysical⟩
    iapply wp_mono hpost
    simp only [← tablePointsToAt_eq]
    iapply wp_tableCopySame
      (tableIndex := 0)
      (table :=
        [.funcref none, .funcref (some 0), .funcref (some 1),
          .funcref (some 2)])
      (destination := .i32 1) (source := .i32 0) (length := .i32 3)
      rfl rfl rfl (by decide) (by decide) $$ Htable
    inext
    iintro Htable
    iapply wp_mono (fun _ => BI.sep_comm.mp)
    iapply wp_frame_l
    isplitl [Htable]
    · iexact Htable
    iapply wp_finish
    inext
    iapply wp_value'
    ipureintro
    rfl

private def tableCopyDistinctMap : WasmTableMap TableInst :=
  insert (insert ∅ (⟨0, 0⟩ : TableKey) [.funcref none, .funcref none, .funcref none])
    (⟨0, 1⟩ : TableKey) [.funcref (some 0), .funcref (some 1), .funcref (some 2)]

private theorem tableCopyDistinctMap_agrees :
    tableHeapAgrees tableCopyDistinctMap
      [[.funcref none, .funcref none, .funcref none],
       [.funcref (some 0), .funcref (some 1), .funcref (some 2)]] := by
  intro index table hget
  unfold tableCopyDistinctMap at hget
  by_cases hindex0 : index = 0
  · subst index
    simp only [get?_insert_ne (show (⟨0, 1⟩ : TableKey) ≠ ⟨0, 0⟩ by decide),
      get?_insert_eq rfl,
      Option.some.injEq] at hget
    subst table
    rfl
  by_cases hindex1 : index = 1
  · subst index
    simp only [get?_insert_eq rfl, Option.some.injEq] at hget
    subst table
    rfl
  rw [get?_insert_ne (fun h => hindex1 (congrArg TableKey.index h).symm),
    get?_insert_ne (fun h => hindex0 (congrArg TableKey.index h).symm), get?_empty] at hget
  contradiction

private theorem tableCopyDistinctMap_pointsTo [WasmTableGS α] :
    ([∗map] index ↦ table ∈ tableCopyDistinctMap,
      tablePointsTo index table) ⊢
      tablePointsTo ⟨0, 0⟩
          [.funcref none, .funcref none, .funcref none] ∗
      tablePointsTo ⟨0, 1⟩
          [.funcref (some 0), .funcref (some 1),
            .funcref (some 2)] := by
  unfold tableCopyDistinctMap
  have hmissing :
      get?
        (insert (∅ : WasmTableMap TableInst) (⟨0, 0⟩ : TableKey)
          ([.funcref none, .funcref none, .funcref none] : TableInst))
        (⟨0, 1⟩ : TableKey) = none := by
    rw [get?_insert_ne (show (⟨0, 0⟩ : TableKey) ≠ ⟨0, 1⟩ by decide), get?_empty]
  rw [(BI.BigSepM.bigSepM_insert hmissing).to_eq,
    (BI.BigSepM.bigSepM_insert (get?_empty (⟨0, 0⟩ : TableKey))).to_eq,
    BI.BigSepM.bigSepM_empty.to_eq, BI.sep_emp.to_eq]
  iintro ⟨Hsource, Hdestination⟩
  isplitl [Hdestination]
  · iexact Hdestination
  · iexact Hsource

def tableCopyDistinctAdequacyModule : Module :=
  { funcs := [{ body := [] }, { body := [] }, { body := [] }]
    tables :=
      [{ min := 3, max := some 3 }, { min := 3, max := some 3 }] }

def tableCopyDistinctAdequacyConfig : Config Unit :=
  { expr := .running
      ⟨⟨[], [], [.i32 2, .i32 1, .i32 0]⟩,
        [.tableCopy 0 1], 0, [], [], []⟩
    store :=
      { runtime := { instances := #[{ module := tableCopyDistinctAdequacyModule, host := {} }], entry := ⟨0⟩ }
        wasm :=
          { tableCopyDistinctAdequacyModule.initialStore with
            tables :=
              [[.funcref none, .funcref none, .funcref none],
               [.funcref (some 0), .funcref (some 1),
                 .funcref (some 2)]] } } }

/-- Closed cross-table copy regression. It proves the destination receives the
selected source slice while the physically separate source table is preserved
exactly. -/
theorem tableCopyDistinct_store_partiallyMeets :
    PartiallyMeets tableCopyDistinctAdequacyConfig
      (fun values store =>
        values = [] ∧
          store.wasm.tables[0]? =
            some [.funcref (some 1), .funcref (some 2), .funcref none] ∧
          store.wasm.tables[1]? =
            some [.funcref (some 0), .funcref (some 1),
              .funcref (some 2)]) := by
  apply
    wasm_smallStep_heap_globals_segments_tables_runtime_store_partiallyMeets
      (α := Unit)
      (σ := (∅ : WasmHeapMap (Option UInt8)))
      (globalσ := (∅ : WasmGlobalMap Value))
      (dataSegmentσ :=
        (∅ : WasmDataSegmentMap (Option (List UInt8))))
      (tableσ := tableCopyDistinctMap)
      (elementSegmentσ :=
        (∅ : WasmElementSegmentMap (Option (List (Option Nat)))))
  · exact heapAgreesWithMem_empty _
  · exact heapAddressesInBounds_empty _
  · exact globalHeapAgrees_empty _
  · exact dataSegmentHeapAgrees_empty _
  · exact tableCopyDistinctMap_agrees
  · exact elementSegmentHeapAgrees_empty _
  · decide
  · intro gs
    simp only [BI.BigSepM.bigSepM_empty.to_eq,
      tableCopyDistinctAdequacyConfig]
    simp only [runtimeModuleOwn]
    iintro ⟨_Hbytes, _Hglobals, _Hsegments, Htables, _HelementSegments, _Hruntime, _HinstFrag⟩
    ihave HtablePair := tableCopyDistinctMap_pointsTo $$ Htables
    icases HtablePair with ⟨Hdestination, Hsource⟩
    have hpost : ∀ values : List Value,
        (iprop% ⌜values = []⌝ ∗
          tablePointsTo ⟨0, 0⟩
            (listWriteAt
              [.funcref none, .funcref none, .funcref none]
              (UInt32.toNat 0)
              (([.funcref (some 0), .funcref (some 1),
                  .funcref (some 2)].drop (UInt32.toNat 1)).take
                    (UInt32.toNat 2))) ∗
          tablePointsTo ⟨0, 1⟩
            [.funcref (some 0), .funcref (some 1),
              .funcref (some 2)]) ⊢
        (iprop% ∀ (store : MachineStore Unit)
            (_observations : List StepKind),
          stateInterp (GF := WasmHeapGF Unit) store 0 [] 0 -∗
          ⌜values = [] ∧
            store.wasm.tables[0]? =
              some [.funcref (some 1), .funcref (some 2),
                .funcref none] ∧
            store.wasm.tables[1]? =
              some [.funcref (some 0), .funcref (some 1),
                .funcref (some 2)]⌝) := by
      intro values
      iintro ⟨%hvalues, Hdestination, Hsource⟩
        %store %_observations Hstate
      simp only [← tablePointsToAt_eq]
      imod stateInterp_table_facts_frame
        store 0 [] 0 0
          (listWriteAt
            [.funcref none, .funcref none, .funcref none]
            (UInt32.toNat 0)
            (([.funcref (some 0), .funcref (some 1),
                .funcref (some 2)].drop (UInt32.toNat 1)).take
                  (UInt32.toNat 2))) $$
          [$Hstate $Hdestination] with
        ⟨Hstate, Hdestination, %HdestinationPhysical⟩
      imod stateInterp_table_facts_frame
        store 0 [] 0 1
          [.funcref (some 0), .funcref (some 1),
            .funcref (some 2)] $$ [$Hstate $Hsource] with
        ⟨Hstate, Hsource, %HsourcePhysical⟩
      ipureintro
      exact ⟨hvalues,
        by simpa [listWriteAt] using HdestinationPhysical,
        HsourcePhysical⟩
    have hframe : ∀ values : List Value,
        (iprop%
          (tablePointsTo ⟨0, 0⟩
              (listWriteAt
                [.funcref none, .funcref none, .funcref none]
                (UInt32.toNat 0)
                (([.funcref (some 0), .funcref (some 1),
                    .funcref (some 2)].drop (UInt32.toNat 1)).take
                      (UInt32.toNat 2))) ∗
            tablePointsTo ⟨0, 1⟩
              [.funcref (some 0), .funcref (some 1),
                .funcref (some 2)]) ∗
          ⌜values = []⌝) ⊢
        (iprop% ⌜values = []⌝ ∗
          (tablePointsTo ⟨0, 0⟩
              (listWriteAt
                [.funcref none, .funcref none, .funcref none]
                (UInt32.toNat 0)
                (([.funcref (some 0), .funcref (some 1),
                    .funcref (some 2)].drop (UInt32.toNat 1)).take
                      (UInt32.toNat 2))) ∗
            tablePointsTo ⟨0, 1⟩
              [.funcref (some 0), .funcref (some 1),
                .funcref (some 2)])) := by
      intro values
      iintro ⟨⟨Hdestination, Hsource⟩, %hvalues⟩
      isplitl []
      · ipureintro
        exact hvalues
      · isplitl [Hdestination]
        · iexact Hdestination
        · iexact Hsource
    iapply wp_mono hpost
    simp only [← tablePointsToAt_eq]
    icombine Hdestination Hsource as HtablePair
    iapply wp_tableCopyDistinct
      (destinationTableIndex := 0) (sourceTableIndex := 1)
      (destinationTable :=
        [.funcref none, .funcref none, .funcref none])
      (sourceTable :=
        [.funcref (some 0), .funcref (some 1), .funcref (some 2)])
      (destination := .i32 0) (source := .i32 1) (length := .i32 2)
      rfl rfl rfl (by decide) (by decide) $$ HtablePair
    inext
    iintro Hdestination Hsource
    simp only [tablePointsToAt_eq]
    iapply wp_mono hframe
    iapply wp_frame_l
    isplitl [Hdestination Hsource]
    · isplitl [Hdestination]
      · iexact Hdestination
      · iexact Hsource
    iapply wp_finish
    inext
    iapply wp_value'
    ipureintro
    rfl

private def tableInitDropTableMap : WasmTableMap TableInst :=
  insert ∅ (⟨0, 0⟩ : TableKey)
    [.funcref none, .funcref none, .funcref none, .funcref none]

private def tableInitDropElementMap :
    WasmElementSegmentMap (Option (List (Option Nat))) :=
  insert ∅ (⟨0, 0⟩ : ElementSegmentKey) (some [some 0, none, some 0])

private theorem tableInitDropTableMap_agrees :
    tableHeapAgrees tableInitDropTableMap
      [[.funcref none, .funcref none, .funcref none,
        .funcref none]] := by
  intro index table hget
  unfold tableInitDropTableMap at hget
  by_cases hindex : index = 0
  · subst index
    simp only [get?_insert_eq rfl, Option.some.injEq] at hget
    subst table
    rfl
  · rw [get?_insert_ne (fun h => hindex (congrArg TableKey.index h).symm), get?_empty] at hget
    contradiction

private theorem tableInitDropElementMap_agrees :
    elementSegmentHeapAgrees tableInitDropElementMap
      [some [some 0, none, some 0]] := by
  intro index value hget
  unfold tableInitDropElementMap at hget
  by_cases hindex : index = 0
  · subst index
    simp only [get?_insert_eq rfl, Option.some.injEq] at hget
    subst value
    rfl
  · rw [get?_insert_ne (fun h => hindex (congrArg ElementSegmentKey.index h).symm), get?_empty] at hget
    contradiction

private theorem tableInitDropTableMap_pointsTo [WasmTableGS α] :
    ([∗map] index ↦ table ∈ tableInitDropTableMap,
      tablePointsTo index table) ⊢
      tablePointsTo ⟨0, 0⟩
        [.funcref none, .funcref none, .funcref none,
          .funcref none] := by
  unfold tableInitDropTableMap
  rw [(BI.BigSepM.bigSepM_insert (get?_empty (⟨0, 0⟩ : TableKey))).to_eq,
    BI.BigSepM.bigSepM_empty.to_eq, BI.sep_emp.to_eq]

private theorem tableInitDropElementMap_pointsTo [WasmElementSegmentGS α] :
    ([∗map] index ↦ value ∈ tableInitDropElementMap,
      elementSegmentPointsTo index value) ⊢
      elementSegmentPointsTo ⟨0, 0⟩ (some [some 0, none, some 0]) := by
  unfold tableInitDropElementMap
  rw [(BI.BigSepM.bigSepM_insert (get?_empty (⟨0, 0⟩ : ElementSegmentKey))).to_eq,
    BI.BigSepM.bigSepM_empty.to_eq, BI.sep_emp.to_eq]

def tableInitDropAdequacyModule : Module :=
  { funcs := [{ body := [] }]
    tables := [{ min := 4, max := some 4 }]
    elements := [{ funcs := [some 0, none, some 0] }] }

def tableInitDropAdequacyConfig : Config Unit :=
  { expr := .running
      ⟨⟨[], [], [.i32 3, .i32 0, .i32 1]⟩,
        [.tableInit 0 0, .elemDrop 0], 0, [], [], []⟩
    store :=
      { runtime := { instances := #[{ module := tableInitDropAdequacyModule, host := {} }], entry := ⟨0⟩ }
        wasm := tableInitDropAdequacyModule.initialStore } }

/-- Closed physical-state regression for element segments. `table.init`
copies the live instantiated values into the table; `elem.drop` then changes
the segment to its authoritative dropped state without changing that table. -/
theorem tableInitDrop_store_partiallyMeets :
    PartiallyMeets tableInitDropAdequacyConfig
      (fun values store =>
        values = [] ∧
          store.wasm.tables[0]? =
            some [.funcref none, .funcref (some 0), .funcref none,
              .funcref (some 0)] ∧
          store.wasm.elementSegments[0]? = some none) := by
  apply
    wasm_smallStep_heap_globals_segments_tables_runtime_store_partiallyMeets
      (α := Unit)
      (σ := (∅ : WasmHeapMap (Option UInt8)))
      (globalσ := (∅ : WasmGlobalMap Value))
      (dataSegmentσ :=
        (∅ : WasmDataSegmentMap (Option (List UInt8))))
      (tableσ := tableInitDropTableMap)
      (elementSegmentσ := tableInitDropElementMap)
  · exact heapAgreesWithMem_empty _
  · exact heapAddressesInBounds_empty _
  · exact globalHeapAgrees_empty _
  · exact dataSegmentHeapAgrees_empty _
  · exact tableInitDropTableMap_agrees
  · exact tableInitDropElementMap_agrees
  · decide
  · intro gs
    simp only [BI.BigSepM.bigSepM_empty.to_eq,
      tableInitDropAdequacyConfig, RuntimeEnv.currentModule_mk1]
    simp only [runtimeModuleOwn]
    iintro
      ⟨_Hbytes, _Hglobals, _HdataSegments, Htables,
        HelementSegments, Hruntime, HinstFrag⟩
    iintuitionistic Hruntime
    ihave Htable := tableInitDropTableMap_pointsTo $$ Htables
    ihave Helement :=
      tableInitDropElementMap_pointsTo $$ HelementSegments
    have hpost : ∀ values : List Value,
        (iprop% ⌜values = []⌝ ∗
          tablePointsTo ⟨0, 0⟩
            (listWriteAt
              [.funcref none, .funcref none, .funcref none,
                .funcref none]
              (UInt32.toNat 1)
              (((tableInitDropAdequacyModule.elements[0]?.map
                  ElementSegment.values).getD []).drop
                    (UInt32.toNat 0) |>.take (UInt32.toNat 3))) ∗
          elementSegmentPointsTo ⟨0, 0⟩ none) ⊢
        (iprop% ∀ (store : MachineStore Unit)
            (_observations : List StepKind),
          stateInterp (GF := WasmHeapGF Unit) store 0 [] 0 -∗
          ⌜values = [] ∧
            store.wasm.tables[0]? =
              some [.funcref none, .funcref (some 0), .funcref none,
                .funcref (some 0)] ∧
            store.wasm.elementSegments[0]? = some none⌝) := by
      intro values
      iintro ⟨%hvalues, Htable, Helement⟩
        %store %_observations Hstate
      simp only [← tablePointsToAt_eq]
      imod stateInterp_table_facts_frame
        store 0 [] 0 0
          (listWriteAt
            [.funcref none, .funcref none, .funcref none,
              .funcref none]
            (UInt32.toNat 1)
            (((tableInitDropAdequacyModule.elements[0]?.map
                ElementSegment.values).getD []).drop
                  (UInt32.toNat 0) |>.take (UInt32.toNat 3))) $$
          [$Hstate $Htable] with
        ⟨Hstate, Htable, %HtablePhysical⟩
      simp only [← elementSegmentPointsToAt_eq]
      imod stateInterp_elementSegment_facts_frame
        store 0 [] 0 0 none $$ [$Hstate $Helement] with
        ⟨Hstate, Helement, %HelementPhysical⟩
      ipureintro
      exact ⟨hvalues,
        by simpa [tableInitDropAdequacyModule,
            ElementSegment.values, ElementSegment.plainValues, listWriteAt]
          using HtablePhysical,
        HelementPhysical⟩
    iapply wp_mono hpost
    simp only [← tablePointsToAt_eq, ← elementSegmentPointsToAt_eq]
    ihave Hresources :
        tablePointsToAt 0 0
            [.funcref none, .funcref none, .funcref none,
              .funcref none] ∗
          elementSegmentPointsToAt 0 0 (some [some 0, none, some 0]) ∗
          runtimeModuleOwn ⟨0⟩ tableInitDropAdequacyModule $$
        [Htable Helement Hruntime HinstFrag]
    · isplitl [Htable]
      · iexact Htable
      · isplitl [Helement]
        · iexact Helement
        · unfold runtimeModuleOwn
          isplitl [Hruntime]
          · unfold runtimeModuleElem; iexact Hruntime
          · unfold currentInstanceOwnN; iexact HinstFrag
    iapply wp_tableInitLive tableInitDropAdequacyModule ⟨0⟩
      (tableIndex := 0) (elementIndex := 0)
      (table :=
        [.funcref none, .funcref none, .funcref none, .funcref none])
      (entries := [some 0, none, some 0])
      (destination := .i32 1) (source := 0) (length := 3)
      rfl (by decide) (by decide) $$ Hresources
    inext
    iintro Htable Helement Hruntime
    iapply wp_elemDrop $$ Helement
    inext
    iintro Helement
    iapply wp_mono (fun _ => sep_pair_pure_rotate _ _ _)
    iapply wp_frame_l
    isplitl [Htable Helement]
    · isplitl [Htable]
      · iexact Htable
      · iexact Helement
    iapply wp_finish
    inext
    iapply wp_value'
    ipureintro
    rfl


private def signedBranchModule : Module :=
  { funcs := [{ params := [.i32, .i32],
                body := [.block 0 0 [.localGet 0, .localGet 1, .geS, .br_if 0, .const 0, .ret],
                          .const 1, .ret]
                results := [.i32] }] }

def signedBranchConfig (a b : UInt32) : Config Unit :=
  { expr := .running ⟨⟨[.i32 a, .i32 b], [], []⟩,
      signedBranchModule.funcs[0]!.body, 1, [], [], []⟩
    store := { runtime := { module := signedBranchModule, host := {} }
               wasm := signedBranchModule.initialStore } }

-- geS on local.get 0 and local.get 1: returns 1 if a ≥ b (signed), 0 otherwise.
theorem signedBranch_terminatesWith (a b : UInt32) :
    TerminatesWith (signedBranchConfig a b)
      (fun values _store => values = [.i32 (if a.toInt32 ≥ b.toInt32 then 1 else 0)]) := by
  apply wasm_smallStep_terminates (signedBranchConfig a b)
    (fun values => values = [.i32 (if a.toInt32 ≥ b.toInt32 then 1 else 0)])

  intro hlc gs
  simp only [signedBranchConfig,
    show signedBranchModule.funcs[0]!.body =
        [.block 0 0 [.localGet 0, .localGet 1, .geS, .br_if 0, .const 0, .ret], .const 1, .ret] from rfl]
  iapply twp_block
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  by_cases h : a.toInt32 ≥ b.toInt32
  · iapply twp_geS (result := 1) (by simp [h])
    iapply twp_brIf (condition := 1) (by decide) rfl
    iapply twp_const
    iapply twp_returnFromFunction
    iapply twp.value rfl
    ipureintro
    simp [h]
  · iapply twp_geS (result := 0) (by simp [h])
    iapply twp_brIfZero
    iapply twp_const
    iapply twp_returnFromFunction
    iapply twp.value rfl
    ipureintro
    simp [h]

/-- Splat conversion for the fill-then-read example: after `memory.fill`
writes `b` into four bytes at address 0, the byte range is the little-endian
layout of the 32-bit word with all four bytes equal to `b`. -/
private theorem splat_bytes_as_u32 [WasmHeapGS Unit] (b : UInt8) :
    pointsToBytes (α := Unit) 0 (List.replicate 4 b) ⊢
      pointsTo_u32 0
        (b.toUInt32 ||| (b.toUInt32 <<< 8) ||| (b.toUInt32 <<< 16) ||| (b.toUInt32 <<< 24)) := by
  have hb0 : u32Byte (b.toUInt32 ||| (b.toUInt32 <<< 8) |||
      (b.toUInt32 <<< 16) ||| (b.toUInt32 <<< 24)) 0 = b := by
    simp only [u32Byte]; bv_decide
  have hb1 : u32Byte (b.toUInt32 ||| (b.toUInt32 <<< 8) |||
      (b.toUInt32 <<< 16) ||| (b.toUInt32 <<< 24)) 1 = b := by
    simp only [u32Byte]; bv_decide
  have hb2 : u32Byte (b.toUInt32 ||| (b.toUInt32 <<< 8) |||
      (b.toUInt32 <<< 16) ||| (b.toUInt32 <<< 24)) 2 = b := by
    simp only [u32Byte]; bv_decide
  have hb3 : u32Byte (b.toUInt32 ||| (b.toUInt32 <<< 8) |||
      (b.toUInt32 <<< 16) ||| (b.toUInt32 <<< 24)) 3 = b := by
    simp only [u32Byte]; bv_decide
  have hl : List.replicate 4 b =
      [u32Byte (b.toUInt32 ||| (b.toUInt32 <<< 8) |||
          (b.toUInt32 <<< 16) ||| (b.toUInt32 <<< 24)) 0,
       u32Byte (b.toUInt32 ||| (b.toUInt32 <<< 8) |||
          (b.toUInt32 <<< 16) ||| (b.toUInt32 <<< 24)) 1,
       u32Byte (b.toUInt32 ||| (b.toUInt32 <<< 8) |||
          (b.toUInt32 <<< 16) ||| (b.toUInt32 <<< 24)) 2,
       u32Byte (b.toUInt32 ||| (b.toUInt32 <<< 8) |||
          (b.toUInt32 <<< 16) ||| (b.toUInt32 <<< 24)) 3] := by
    rw [hb0, hb1, hb2, hb3]
    rfl
  rw [hl]
  exact (pointsTo_u32_as_bytes 0 _).mpr

private def fillThenReadInitialHeap : WasmHeapMap (Option UInt8) :=
  store32Heap ∅ 0 0

private theorem fillThenReadInitialHeap_agrees (memory : Mem) :
    heapAgreesWithMem fillThenReadInitialHeap (memory.write32 0 0) := by
  unfold fillThenReadInitialHeap
  apply store32_sound
  · rfl
  · rfl
  · rfl
  · exact emptyHeap_agrees memory

private theorem fillThenReadInitialHeap_inBounds (memory : Mem)
    (hpages : 1 ≤ memory.pages) :
    heapAddressesInBounds fillThenReadInitialHeap (memory.write32 0 0) := by
  unfold fillThenReadInitialHeap
  apply store32_inBounds
  · rfl
  · rfl
  · rfl
  · exact emptyHeap_inBounds memory
  · simp only [UInt32.toNat_zero]
    have : 65536 ≤ memory.pages * 65536 := Nat.mul_le_mul_right 65536 hpages
    omega

private theorem fillThenReadInitialHeap_pointsTo [WasmHeapGS Unit] :
    ([∗map] address ↦ value ∈ fillThenReadInitialHeap,
      pointsTo (GF := WasmHeapGF Unit) (H := WasmHeapMap)
        address (DFrac.own 1) value) ⊢
      pointsTo_u32 0 0 := by
  unfold fillThenReadInitialHeap
  iintro Hheap
  ihave H0 := store32Heap_pointsTo
    (∅ : WasmHeapMap (Option UInt8)) 0 0
    (by simp [get?_empty]) (by simp [get?_empty])
    (by simp [get?_empty]) (by simp [get?_empty])
    (by decide) (by decide) (by decide) $$ Hheap
  icases H0 with ⟨H0, _⟩
  iexact H0

def fillThenReadModule : Module :=
  { funcs := [{ params := [.i32],
                body := [.const 0, .localGet 0, .const 4, .memoryFill,
                         .const 0, .load32 0],
                results := [.i32] }]
    memory := some { pagesMin := 1 } }

def fillThenReadConfig (val : UInt32) : Config Unit :=
  let initial := fillThenReadModule.initialStore
  { expr := .running ⟨⟨[.i32 val], [], []⟩,
      fillThenReadModule.funcs[0]!.body, 1, [], [], []⟩
    store := { runtime := { module := fillThenReadModule, host := {} }
               wasm := { initial with mem := initial.mem.write32 0 0 } } }

-- load32 with offset=0: uses addr directly in the premise to avoid addr+0 in iris synthesis
private theorem twp_load32_addr
    {params localValues values : List Value}
    {addr : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    [WasmSmallStepGS hlc α] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF α)}
    (word : UInt32)
    (h1 : (addr + 1 : UInt32).toNat = addr.toNat + 1)
    (h2 : (addr + 2 : UInt32).toNat = addr.toNat + 2)
    (h3 : (addr + 3 : UInt32).toNat = addr.toNat + 3) :
    let current : ThreadState α :=
      ⟨⟨params, localValues, .i32 addr :: values⟩,
        .load32 0 :: code, arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨⟨params, localValues, .i32 word :: values⟩,
        code, arity, remainder, controls, calls⟩
    pointsTo_u32 addr word -∗
    (pointsTo_u32 addr word -∗
      WP (Expr.running next : Expr α) @ s; E [{ Φ }]) -∗
      WP (Expr.running current : Expr α) @ s; E [{ Φ }] := by
  dsimp only
  iintro Hword Htwp
  iapply twp_lift_step_no_fork rfl
  iintro %store %ns %obs %nt Hσ
  ihave %Hfacts :
      ⌜store.wasm.mem.read32 addr = word ∧
        addr.toNat + 4 ≤ store.wasm.mem.pages * 65536⌝ $$ [Hσ Hword]
  · imod stateInterp_pointsTo_u32_facts store ns obs nt
      addr word h1 h2 h3 $$ [$Hσ $Hword] with %Hfacts
    ipureintro
    exact Hfacts
  obtain ⟨Hread, HinBounds⟩ := Hfacts
  have hbound : addr.toNat + (0 : UInt32).toNat + 4 ≤
      store.wasm.mem.pages * 65536 := by
    have h0 : (0 : UInt32).toNat = 0 := rfl
    omega
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducibleNoObs]
    exact ⟨.running
        ⟨⟨params, localValues, .i32 word :: values⟩,
          code, arity, remainder, controls, calls⟩,
      store, [], ⟨rfl, .instruction (.load32 0), rfl,
        by simpa only [show (addr + 0 : UInt32) = addr from by simp, Hread]
             using Step.load32 (α := α) hbound⟩⟩
  iintro %κ %e₂ %store₂ %forks %Hstep
  rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst κ
  have expectedStep : Step
      ⟨.running
        ⟨⟨params, localValues, .i32 addr :: values⟩,
          .load32 0 :: code, arity, remainder, controls, calls⟩,
        store⟩
      (.instruction (.load32 0))
      ⟨.running
        ⟨⟨params, localValues, .i32 word :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩ := by
    simpa only [show (addr + 0 : UInt32) = addr from by simp, Hread]
      using Step.load32 (α := α) hbound
  obtain ⟨rfl, hconfig⟩ :=
    step_deterministic expectedStep wasmStep
  have parts := Config.mk.inj hconfig
  have hexpr := parts.1
  have hstore := parts.2
  simp only at hexpr hstore
  subst e₂
  subst store₂
  imod Hclose
  imodintro
  isplit
  · ipureintro
    rfl
  isplit
  · ipureintro
    rfl
  isplitl [Hσ]
  · iexact Hσ
  · iapply Htwp
    iexact Hword

theorem fillThenRead_terminatesWith (val : UInt32) :
    TerminatesWith (fillThenReadConfig val)
      (fun values _store =>
        values = [.i32 (val.toUInt8.toUInt32 ||| (val.toUInt8.toUInt32 <<< 8) |||
                        (val.toUInt8.toUInt32 <<< 16) ||| (val.toUInt8.toUInt32 <<< 24))]) := by
  apply wasm_smallStep_heap_terminates (fillThenReadConfig val)
    fillThenReadInitialHeap
    (fun values =>
      values = [.i32 (val.toUInt8.toUInt32 ||| (val.toUInt8.toUInt32 <<< 8) |||
                      (val.toUInt8.toUInt32 <<< 16) ||| (val.toUInt8.toUInt32 <<< 24))])

  · apply fillThenReadInitialHeap_agrees
  · apply fillThenReadInitialHeap_inBounds
    native_decide
  · intro hlc gs
    simp only [fillThenReadConfig,
      show fillThenReadModule.funcs[0]!.body =
          [.const 0, .localGet 0, .const 4, .memoryFill, .const 0, .load32 0] from rfl]
    iintro Hbytes
    ihave H0 := fillThenReadInitialHeap_pointsTo $$ Hbytes
    ihave Hb := (pointsTo_u32_as_bytes 0 0).mp $$ H0
    iapply twp_const
    iapply twp_localGet rfl
    iapply twp_const
    iapply twp_memoryFill32
        [u32Byte 0 0, u32Byte 0 1, u32Byte 0 2, u32Byte 0 3]
        rfl (by decide) (by decide) $$ Hb
    iintro Hb
    ihave H0 := splat_bytes_as_u32 val.toUInt8 $$ Hb
    iapply twp_const
    iapply twp_load32_addr _ rfl rfl rfl $$ H0
    iintro H0
    iapply twp_finish
        (locals := { params := [.i32 val], locals := [], values := [] })
        (values := [.i32 (val.toUInt8.toUInt32 ||| (val.toUInt8.toUInt32 <<< 8) |||
                          (val.toUInt8.toUInt32 <<< 16) ||| (val.toUInt8.toUInt32 <<< 24))])
        (arity := 1) (remainder := [])
    iapply twp.value rfl
    ipureintro
    rfl

def exceptionLifecycleModule : Module :=
  { tags := [{ params := [.i32] }]
    funcs := [{ params := [.i32],
                body := [.tryTable 0 1 [.catch 0 0] [.localGet 0, .throwI 0],
                          .const 99]
                results := [.i32] }] }

def exceptionLifecycleConfig (arg : UInt32) : Config Unit :=
  { expr := .running ⟨⟨[.i32 arg], [], []⟩, exceptionLifecycleModule.funcs[0]!.body, 1, [], [], []⟩
    store := { runtime := { module := exceptionLifecycleModule, host := {} }
               wasm := exceptionLifecycleModule.initialStore } }

/-- Tag 0 is the first entry of the entry module's tag table, so the
interpreter's tag canonicalisation is the identity on it. -/
private theorem exceptionLifecycle_tagCanonical :
    TagIndexCanonical
      (exceptionLifecycleModule.initialStore : Store Unit).tagIds 0 :=
  ⟨0, by decide, by decide⟩

-- tryTable catches a throwI and returns the thrown value, parametric over arg.
theorem exceptionLifecycle_terminatesWith (arg : UInt32) :
    TerminatesWith (exceptionLifecycleConfig arg)
      (fun values _store => values = [.i32 arg]) := by
  apply wasm_smallStep_runtime_tags_terminates (exceptionLifecycleConfig arg)
    (fun values => values = [.i32 arg])
  intro hlc gs
  simp only [exceptionLifecycleConfig,
    show exceptionLifecycleModule.funcs[0]!.body =
        [.tryTable 0 1 [.catch 0 0] [.localGet 0, .throwI 0], .const 99] from rfl]
  iintro ⟨Hruntime, Htags⟩
  iapply twp_tryTable
  iapply twp_localGet rfl
  iapply (twp_throwI exceptionLifecycleModule 0
    (tagType := { params := [.i32] }) (htag := rfl)
    (tagIds := (exceptionLifecycleModule.initialStore : Store Unit).tagIds)
    (hcanonical := exceptionLifecycle_tagCanonical)
    (hargs := by simp)) $$ Hruntime Htags
  iintro Hruntime'
  iapply twp_catchException
    (clause := .catch 0 0) (targetCode := []) (targetControl := []) (targetValues := [.i32 arg])
    (htarget := fun _ => rfl) (hthrow := rfl) (hmatch := by decide)
  iapply twp_finish
  iapply twp.value rfl
  ipureintro
  rfl

-- decoder agreement for signed_branch.wat
private def signedBranchWat : String := include_str "signed_branch.wat"

private def signedBranchModuleDecoded : Module :=
  match Wasm.Decoder.Wat.decode signedBranchWat with
  | .ok m => m
  | .error _ => default

private def runSignedBranch (fuel : Nat) (m : Module) (a b : UInt32) : Option (List Value) :=
  match initConfig { module := m, host := (default : HostEnv Unit) } 0
      m.initialStore [.i32 a, .i32 b] with
  | .error _ => none
  | .ok config => (runSteps fuel config).result.values?

-- exercises both branch outcomes across varied inputs
theorem signedBranch_decoded_agrees :
    runSignedBranch 10 signedBranchModule 5 3 = runSignedBranch 10 signedBranchModuleDecoded 5 3 ∧
    runSignedBranch 15 signedBranchModule 0 1 = runSignedBranch 15 signedBranchModuleDecoded 0 1 ∧
    runSignedBranch 20 signedBranchModule 100 100 = runSignedBranch 20 signedBranchModuleDecoded 100 100 ∧
    runSignedBranch 50 signedBranchModule 4294967295 0 = runSignedBranch 50 signedBranchModuleDecoded 4294967295 0 ∧
    runSignedBranch 100 signedBranchModule 42 43 = runSignedBranch 100 signedBranchModuleDecoded 42 43 := by
  native_decide

-- decoder agreement for fill_then_read.wat
private def fillThenReadWat : String := include_str "fill_then_read.wat"

private def fillThenReadModuleDecoded : Module :=
  match Wasm.Decoder.Wat.decode fillThenReadWat with
  | .ok m => m
  | .error _ => default

private def runFillThenRead (fuel : Nat) (m : Module) (val : UInt32) : Option (List Value) :=
  match initConfig { module := m, host := (default : HostEnv Unit) } 0
      m.initialStore [.i32 val] with
  | .error _ => none
  | .ok config => (runSteps fuel config).result.values?

theorem fillThenRead_decoded_agrees :
    runFillThenRead 10 fillThenReadModule 0 = runFillThenRead 10 fillThenReadModuleDecoded 0 ∧
    runFillThenRead 15 fillThenReadModule 5 = runFillThenRead 15 fillThenReadModuleDecoded 5 ∧
    runFillThenRead 20 fillThenReadModule 255 = runFillThenRead 20 fillThenReadModuleDecoded 255 ∧
    runFillThenRead 50 fillThenReadModule 171 = runFillThenRead 50 fillThenReadModuleDecoded 171 ∧
    runFillThenRead 100 fillThenReadModule 1000 = runFillThenRead 100 fillThenReadModuleDecoded 1000 := by
  native_decide

-- decoder agreement for exception_lifecycle.wat
private def exceptionLifecycleWat : String := include_str "exception_lifecycle.wat"

private def exceptionLifecycleModuleDecoded : Module :=
  match Wasm.Decoder.Wat.decode exceptionLifecycleWat with
  | .ok m => m
  | .error _ => default

private def runExceptionLifecycle (fuel : Nat) (m : Module) (arg : UInt32) : Option (List Value) :=
  match initConfig { module := m, host := (default : HostEnv Unit) } 0
      m.initialStore [.i32 arg] with
  | .error _ => none
  | .ok config => (runSteps fuel config).result.values?

theorem exceptionLifecycle_decoded_agrees :
    runExceptionLifecycle 10 exceptionLifecycleModule 0 = runExceptionLifecycle 10 exceptionLifecycleModuleDecoded 0 ∧
    runExceptionLifecycle 15 exceptionLifecycleModule 5 = runExceptionLifecycle 15 exceptionLifecycleModuleDecoded 5 ∧
    runExceptionLifecycle 20 exceptionLifecycleModule 100 = runExceptionLifecycle 20 exceptionLifecycleModuleDecoded 100 ∧
    runExceptionLifecycle 50 exceptionLifecycleModule 255 = runExceptionLifecycle 50 exceptionLifecycleModuleDecoded 255 ∧
    runExceptionLifecycle 100 exceptionLifecycleModule 1000 = runExceptionLifecycle 100 exceptionLifecycleModuleDecoded 1000 := by
  native_decide


end Wasm.SmallStep
