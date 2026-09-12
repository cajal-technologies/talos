import Project.Mergesort.Proof
import Project.Mergesort.AllocationBound
import CodeLib.SepLogic.CostedStepsStdIO
import CodeLib.SepLogic.SmallStepMemoryCaps

/-!
# Total adequacy for the compiled merge-sort export

The semantic export initializer enters the selected local function body;
the call-site initializer adds a caller frame. Reuse the body proof with
an empty caller stack, initialize its actual resources, and retain total
correctness through the semantic named-export API.
-/

namespace Project.Mergesort.TotalProof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.Mergesort.Representations
open Project.Mergesort.Contracts
open Project.Mergesort.Adequacy
open Project.Mergesort.AllocationBound
open scoped Wasm.SmallStep.Outcome

/-- The exact body configuration selected by the semantic export initializer.
It shares the canonical store with the call-site frontend in `Adequacy`. -/
abbrev exportConfig (input : Spec.Input) : Config Universal.State :=
  { expr := .running
      ⟨Project.Mergesort.func3Def.toLocals [], Project.Mergesort.func3,
        0, [], [], []⟩
    store := (entryConfig input).store }

set_option maxRecDepth 65536 in
/-- The compiled module starts with seventeen physical pages for every input. -/
theorem exportConfig_pages (input : Spec.Input) :
    (exportConfig input).store.wasm.mem.pages = 17 := by
  change (Project.Mergesort.module.initialStore : Store Universal.State).mem.pages = 17
  decide

/-- The public initializer selects this local body using the actual exported
name and checks its argument signature. -/
theorem startExportConfig_eq (input : Spec.Input) :
    startExportConfig? (Universal.envFor Project.Mergesort.module)
      Project.Mergesort.module "mergesort" (Spec.args input) =
      some (exportConfig input) := by
  rw [Spec.args, startExportConfig?_ofHost_zero (by decide :
    ZeroArgumentExport Project.Mergesort.module "mergesort")]
  rfl

/-- The actual terminal store retains the instantiated primary-memory cap. -/
def cappedEntryPost (input : List UInt32) (outcome : ObservableOutcome)
    (store : MachineStore Universal.State) : Prop :=
  entryPost input outcome store ∧
    store.wasm.memoryCaps[0]? = some Module.memoryHardCap

/-- Functional outcome, actual cap, allocation-frontier bound and physical
page validity in the same terminal store. -/
def resourceEntryPost (input : List UInt32) (outcome : ObservableOutcome)
    (store : MachineStore Universal.State) : Prop :=
  cappedEntryPost input outcome store ∧
    allocationFrontier store ≤ workArraysFrontierBound (serialize input).length ∧
    store.wasm.mem.pages ≤ Module.memoryHardCap

/-- The terminal outcome is explicitly normal, with the functional,
cap and allocation-frontier guarantees for the same final store. -/
def normalResourcePost (input : List UInt32) (outcome : ObservableOutcome)
    (store : MachineStore Universal.State) : Prop :=
  outcome = .done [] ∧ resourceEntryPost input outcome store

theorem irisBoundedEntryPost_with_cap [WasmSmallStepGS hlc Universal.State]
    (input : List UInt32) (outcome : ObservableOutcome) :
    memoryCapOwn 0 Module.memoryHardCap -∗
      (∀ (store : MachineStore Universal.State) (observations : List StepKind),
        stateInterp (GF := WasmHeapGF Universal.State) store 0 observations 0 -∗
          ⌜boundedEntryPost input outcome store⌝) -∗
      ∀ (store : MachineStore Universal.State) (observations : List StepKind),
        stateInterp (GF := WasmHeapGF Universal.State) store 0 observations 0 -∗
          ⌜resourceEntryPost input outcome store⌝ := by
  iintro Hcap Hpost %store %observations Hstate
  ihave %hcap : ⌜store.wasm.memoryCaps[0]? = some Module.memoryHardCap ∧
      store.wasm.mem.pages ≤ Module.memoryHardCap⌝ $$
      [Hstate Hcap]
  · iapply stateInterp_memoryCap_primary store 0 observations 0 Module.memoryHardCap
    iframe
  ispecialize Hpost $$ %store %observations Hstate
  icases Hpost with %hpost
  ipureexact ⟨⟨hpost.1, hcap.1⟩, hpost.2, hcap.2⟩

/-- The already-proved driver reaches an actual terminal outcome from the
public export initializer. No execution or allocator contract is assumed. -/
theorem export_terminates_with_resources (input : List UInt32) :
    TerminatesWithOutcome (exportConfig input) (resourceEntryPost input) := by
  apply wasm_smallStep_heap_globals_runtime_host_store_terminatesWithOutcome_at_caps
      (config := exportConfig input) entryHeap entryGlobals
      (PartialMap.singleton 0 Module.memoryHardCap)
      heapBase.toNat (resourceEntryPost input)
  · exact (entryHeap_facts input).1
  · exact (entryHeap_facts input).2
  · exact entryHeap_below_heapBase
  · constructor
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
  · exact entryGlobals_agree input
  · simp
  · intro hlc gs legacyPages
    dsimp only [exportConfig]
    iintro ⟨Hheap, Hglobals, Hruntime, Henv, Hhost, Hfrontier, Hpages, Hcaps⟩
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
    imod initialResources input $$
      [$Hheap $Hglobals $Hruntime' $Henv' $Hhost' $Hfrontier $Hpages'] with
      ⟨%heapId, Hruntime, Hsp, Hstack, Hbump, Hstreams⟩
    have hfunc1 : Func1Spec (hlc := hlc) :=
      Project.Mergesort.Func1Proof.func1_correct_of
        (Project.Mergesort.Func0Proof.func0_correct_of
          Project.Mergesort.Func5Proof.func5_correct
          Project.Mergesort.Func8Proof.func8_correct)
    iapply Project.Mergesort.DriverProof.twp_func3_body hfunc1
      Project.Mergesort.Func5Proof.func5_correct
      Project.Mergesort.Func9Proof.func9_correct
      heapId input entryStackBytes entryStackBytes_length
    isplitl_exacts [Hruntime Hsp Hstack Hbump Hstreams]
    isplitl
    · iintro %finalLocals _Hruntime Hsuccess
      iapply (twp_finish (locals := finalLocals) (values := finalLocals.values)
        (arity := 0) (remainder := []))
      isimp only [List.take_zero, List.nil_append]
      iapply Wasm.SmallStep.twp_outcome_done
      iapply irisBoundedEntryPost_with_cap input (.done []) $$ Hcaps
      iapply_exact DriverSuccess_public_bound heapId input with Hsuccess
    · iintro Hoom
      iapply irisBoundedEntryPost_with_cap input (.trapped (.host OOM.trapMessage)) $$ Hcaps
      iapply_exact DriverOOM_public_bound heapId input with Hoom

/-- Retain the physical-cap interface as a projection of the stronger result. -/
theorem export_terminates_with_cap (input : List UInt32) :
    TerminatesWithOutcome (exportConfig input) (cappedEntryPost input) := by
  obtain ⟨trace, outcome, store, steps, hpost, _hbound⟩ := export_terminates_with_resources input
  exact ⟨trace, outcome, store, steps, hpost⟩

/-- Forget the added physical-cap postcondition while preserving the original
total export interface. -/
theorem export_terminates (input : List UInt32) :
    TerminatesWithOutcome (exportConfig input) (entryPost input) := by
  obtain ⟨trace, outcome, store, steps, hpost, _hcap⟩ := export_terminates_with_cap input
  exact ⟨trace, outcome, store, steps, hpost⟩

/-- Total correctness of the actual compiled named export, including its
precisely identified resource-exhaustion outcome. -/
@[proves Project.Mergesort.Spec.PublicTotalSpecification]
theorem mergesort_total_correct : Spec.PublicTotalSpecification := by
  intro input
  obtain ⟨trace, outcome, store, steps, hpost⟩ := export_terminates input
  rcases hpost with hoom | ⟨values, hreturned, hsorted⟩
  · refine ⟨.outOfMemory, ?_, trivial⟩
    exact ⟨exportConfig input, startExportConfig_eq input,
      trace, outcome, store, steps, hoom⟩
  · refine ⟨.sorted values, ?_, hsorted⟩
    exact ⟨exportConfig input, startExportConfig_eq input,
      trace, outcome, store, steps, hreturned⟩

/-- Attach the shared byte-work model to this compiled export's actual
terminal execution. This proves neither an input-size budget nor an
asymptotic bound: those require a program-specific potential invariant. -/
theorem mergesort_costed_execution (input : Spec.Input) :
    ∃ trace outcome store amount,
      CostedSteps CostedStdIO.work (exportConfig input) trace
        ⟨outcome.toExpr, store⟩ amount ∧
      entryPost input outcome store ∧ trace.length ≤ amount := by
  obtain ⟨trace, outcome, store, amount, execution, hpost⟩ :=
    (export_terminates input).with_cost CostedStdIO.work
  exact ⟨trace, outcome, store, amount, execution, hpost,
    execution.length_le (fun before kind after _ =>
      byteWork_positive CostedStdIO.hostBytes before kind after)⟩

/-- Resource facts and modeled charges describe one actual execution of the
named export. No numerical bound on the whole execution's charge is asserted. -/
theorem mergesort_costed_resource_execution (input : Spec.Input) :
    ∃ initial trace outcome store amount,
      startExportConfig? (Universal.envFor Project.Mergesort.module)
        Project.Mergesort.module "mergesort" (Spec.args input) = some initial ∧
      CostedSteps CostedStdIO.work initial trace ⟨outcome.toExpr, store⟩ amount ∧
      resourceEntryPost input outcome store ∧ trace.length ≤ amount := by
  obtain ⟨trace, outcome, store, amount, execution, hpost⟩ :=
    (export_terminates_with_resources input).with_cost CostedStdIO.work
  exact ⟨exportConfig input, trace, outcome, store, amount,
    startExportConfig_eq input, execution, hpost,
    execution.length_le (fun before kind after _ =>
      byteWork_positive CostedStdIO.hostBytes before kind after)⟩

end Project.Mergesort.TotalProof
