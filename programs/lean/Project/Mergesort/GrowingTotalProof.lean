import Project.Mergesort.ExactDriverBody
import Project.Mergesort.GrowingMemoryBounds
import Project.Mergesort.TotalProof
import CodeLib.SepLogic.SmallStepGrowingPages

/-!
# Normal named-export execution with growing memory

The exact driver returns both its updated physical-page resource and the
normal sorted-output postcondition. Replaying that contract over the existing
closed total execution excludes the OOM alternative. The retained page bound
then applies to every prefix of the same canonical named invocation.
-/

namespace Project.Mergesort.GrowingTotalProof

open Wasm Wasm.SmallStep Wasm.SepLogic
open Iris Iris.ProgramLogic Language.Notation Std
open Project.Mergesort.Representations Project.Mergesort.Contracts
open Project.Mergesort.Adequacy Project.Mergesort.AllocationBound
open Project.Mergesort.TotalProof
open Project.Mergesort.MemoryBounds Project.Mergesort.ExactReadLoop
open Project.Mergesort.ExactWorkAllocators
open scoped Wasm.SmallStep.Outcome

/-- The selected cap resource describes the canonical store's actual metadata. -/
theorem entryCaps_agree (input : Spec.Input) :
    capHeapAgrees (PartialMap.singleton 0 Module.memoryHardCap)
      (exportConfig input).store.wasm.mem.pages
      (exportConfig input).store.wasm.memoryCaps := by
  constructor
  · intro index cap hlookup
    by_cases hindex : index = 0
    · subst index
      simp [PartialMap.singleton, get?_insert_eq rfl] at hlookup
      subst cap
      rfl
    · simp [PartialMap.singleton, get?_insert_ne (Ne.symm hindex), get?_empty] at hlookup
  · intro cap hlookup
    simp [PartialMap.singleton, get?_insert_eq rfl] at hlookup
    subst cap
    rw [exportConfig_pages]
    decide

/-- The real export body, with both normal output and a returned page bound. -/
theorem growing_export_twp [WasmSmallStepGS hlc Universal.State]
    (input : Spec.Input)
    (hmode : (inferInstance : WasmMemoryPagesGS Universal.State).stateFrac = (1 : Qp).half)
    (hfit : WorkArraysFit (serialize input).length) :
    InitialMachineClientResources (exportConfig input) entryHeap entryGlobals
        (PartialMap.singleton 0 Module.memoryHardCap) heapBase.toNat ∗
      memoryPagesHalf (exportConfig input).store.wasm.mem.pages ⊢
      WP (exportConfig input).expr @ Stuckness.NotStuck; ⊤
        [{ outcome, iprop(ProgramPages input ∗
          ∀ (store : MachineStore Universal.State) (_observations : List StepKind),
            stateInterp (GF := WasmHeapGF Universal.State) store 0 [] 0 -∗
              ⌜normalResourcePost input outcome store⌝) }] := by
  unfold InitialMachineClientResources
  dsimp only [exportConfig]
  iintro ⟨⟨Hheap, Hglobals, Hruntime, Henv, Hhost, Hfrontier, Hpages, Hcaps⟩, Hexact⟩
  isimp only [BI.BigSepM.bigSepM_singleton.to_eq] at Hcaps
  iintuitionistic Hcaps
  ihave Hruntime' :
      runtimeModuleOwn ⟨0⟩ Project.Mergesort.module $$ [Hruntime]
  · irw_exact [← entryConfig_entry input, ← entryConfig_currentModule input] with Hruntime
  ihave Henv' :
      hostEnvOwn 0 (Universal.envFor Project.Mergesort.module) $$ [Henv]
  · irw_exact [← entryConfig_entry_id input, ← entryConfig_currentHost input] with Henv
  ihave Hhost' :
      hostStateOwn (Universal.State.ofInput (serialize input)) $$ [Hhost]
  · irw_exact [← entryConfig_host input] with Hhost
  ihave Hpages' : memoryPagesOwn
      (Project.Mergesort.module.initialStore : Store Universal.State).mem.pages
      $$ [Hpages]
  · rw [show (Project.Mergesort.module.initialStore : Store Universal.State).mem.pages =
      (entryConfig input).store.wasm.mem.pages by rfl]
    iexact Hpages
  iintuitionistic Hpages'
  ihave Hexact17 : memoryPagesHalf 17 $$ [Hexact]
  · irw_exact [show (entryConfig input).store.wasm.mem.pages = 17
      from exportConfig_pages input] with Hexact
  ihave HreadPages : ReadPages input $$ [Hexact17]
  · unfold ReadPages
    iframe Hcaps
    iexists 17
    iframe_pureexact (Nat.le_max_left 17 _)
  imod initialResources input $$
    [$Hheap $Hglobals $Hruntime' $Henv' $Hhost' $Hfrontier $Hpages'] with
    ⟨%heapId, Hruntime, Hsp, Hstack, Hbump, Hstreams⟩
  iapply ExactDriverBody.body heapId input entryStackBytes entryStackBytes_length
    hmode hfit
  isplitl_exacts [HreadPages Hruntime Hsp Hstack Hbump Hstreams]
  iintro %finalLocals Hpages _Hruntime Hsuccess
  iapply (twp_finish (locals := finalLocals) (values := finalLocals.values)
    (arity := 0) (remainder := []))
  isimp only [List.take_zero, List.nil_append]
  iapply Wasm.SmallStep.twp_outcome_done
  isplitl_exact Hpages
  ihave Hbounded := DriverSuccess_public_bound heapId input $$ Hsuccess
  ihave Hpost := irisBoundedEntryPost_with_cap input (.done []) $$ Hcaps Hbounded
  iintro %store %observations Hstate
  ihave %hpost := Hpost $$ %store %observations Hstate
  ipureexact ⟨rfl, hpost⟩

/-- Replay the exact contract over the independently established finite
terminal execution. Its normal postcondition rules out every trapped outcome. -/
theorem terminal_execution_normal (input : Spec.Input)
    (hfit : WorkArraysFit (serialize input).length)
    {trace : List StepKind} {outcome : ObservableOutcome}
    {store : MachineStore Universal.State}
    (execution : Steps (exportConfig input) trace ⟨outcome.toExpr, store⟩) :
    normalResourcePost input outcome store := by
  apply pure_soundness (PROP := IProp (WasmHeapGF Universal.State))
  apply fupd_soundness .hasLC 0 (E1 := ⊤) (E2 := ⊤)
  intro inv
  iintro _Hcredits
  imod smallStep_init_exact_at_caps (exportConfig input) entryHeap entryGlobals
      (PartialMap.singleton 0 Module.memoryHardCap) heapBase.toNat
      (entryHeap_facts input).1 (entryHeap_facts input).2 entryHeap_below_heapBase
      (entryCaps_agree input) (entryGlobals_agree input) (by simp) with
    ⟨%gs, %hmode, Hstate, Hclient, Hhalf⟩
  rcases hmode with ⟨rfl, hhalf⟩
  letI : WasmSmallStepGS .hasLC Universal.State := gs
  ihave Hwp := growing_export_twp input hhalf hfit $$ [Hclient Hhalf]
  · iframe Hclient Hhalf
  imod twp_replay_value (post := fun outcome : ObservableOutcome => iprop(ProgramPages input ∗
        ∀ (store : MachineStore Universal.State) (_observations : List StepKind),
          stateInterp (GF := WasmHeapGF Universal.State) store 0 [] 0 -∗
            ⌜normalResourcePost input outcome store⌝))
      execution outcome ⟨by rfl⟩ 0 [] 0
      $$ [Hstate Hwp] with ⟨Hstate, _Hpages, Hpost⟩
  · iframe Hstate Hwp
  ihave %hpost := Hpost $$ %store %([] : List StepKind) Hstate
  imodintro
  ipureexact hpost

/-- Actual normal execution, without a supplied execution or allocator outcome. -/
theorem export_returns_normally (input : Spec.Input)
    (hfit : WorkArraysFit (serialize input).length) :
    TerminatesWithOutcome (exportConfig input) (normalResourcePost input) := by
  obtain ⟨trace, outcome, store, execution, _resource⟩ :=
    export_terminates_with_resources input
  exact ⟨trace, outcome, store, execution, terminal_execution_normal input hfit execution⟩

/-- Every configuration reached from the unchanged named export satisfies
its input-dependent physical-page bound. -/
theorem export_pages_bounded_at_every_prefix (input : Spec.Input)
    (hfit : WorkArraysFit (serialize input).length)
    {trace : List StepKind} {reached : Config Universal.State}
    (execution : Steps (exportConfig input) trace reached) :
    reached.store.wasm.mem.pages ≤ programPageBound input := by
  obtain ⟨fullTrace, outcome, store, full, _resource⟩ :=
    export_terminates_with_resources input
  apply bounded_pages_at_every_prefix (Terminal := ObservableOutcome)
      (exportConfig input) entryHeap entryGlobals
      (PartialMap.singleton 0 Module.memoryHardCap) heapBase.toNat
      (programPageBound input)
      (entryHeap_facts input).1 (entryHeap_facts input).2 entryHeap_below_heapBase
      (entryCaps_agree input) (entryGlobals_agree input) (by simp) ?_
      full outcome ⟨by rfl⟩ execution
  intro gs hmode
  iintro Hresources
  iapply (twp.mono (Φ := fun outcome : ObservableOutcome =>
    iprop(ProgramPages input ∗
      ∀ (store : MachineStore Universal.State) (_observations : List StepKind),
        stateInterp (GF := WasmHeapGF Universal.State) store 0 [] 0 -∗
          ⌜normalResourcePost input outcome store⌝)) _)
  · intro outcome
    iintro ⟨Hpages, _Hpost⟩
    isimp only [ProgramPages] at Hpages
    icases Hpages with ⟨_Hcap, Hbound⟩
    iexact Hbound
  · iapply_exact growing_export_twp input hmode hfit with Hresources

/-- Normal sorted output and a numerical all-prefix page budget for the actual
named invocation, with no execution or allocator-success premise. -/
@[proves Project.Mergesort.Spec.PublicGrowingMemorySpecification]
theorem mergesort_growing_memory_correct : Spec.PublicGrowingMemorySpecification := by
  intro input hn
  have hfit := GrowingMemoryBounds.workArraysFit_of_word_count input hn
  constructor
  · obtain ⟨trace, outcome, store, steps, hnormal, hresource⟩ :=
      export_returns_normally input hfit
    rcases hresource.1.1 with hoom | ⟨values, hreturned, hsorted⟩
    · have htrap := hoom.1
      rw [hnormal] at htrap
      cases htrap
    · refine ⟨values, ?_, hsorted⟩
      exact ⟨exportConfig input, startExportConfig_eq input,
        trace, outcome, store, steps, hreturned⟩
  · intro initial hstart trace reached execution
    rw [startExportConfig_eq input] at hstart
    cases Option.some.inj hstart
    simpa only [GrowingMemoryBounds.programPageBound_public_formula,
      Spec.growingPageBound] using export_pages_bounded_at_every_prefix input hfit execution

end Project.Mergesort.GrowingTotalProof
