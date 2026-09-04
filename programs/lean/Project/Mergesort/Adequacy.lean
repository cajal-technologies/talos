import Project.Mergesort.Contracts
import CodeLib.SepLogic.SmallStepOutcomeAdequacy

set_option maxRecDepth 8388608
set_option maxHeartbeats 0

/-!
# Partial adequacy for the merge-sort entry call

This file connects the authoritative `Func3Spec` call contract to the public
outcome-sensitive partial-correctness specification.  It deliberately contains
no termination argument: finite normal and trapping traces are classified, but
divergence is not excluded by the current Iris integration.
-/

namespace Project.Mergesort.Adequacy

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.Mergesort.Representations
open Project.Mergesort.Contracts
open scoped Wasm.SmallStep.Outcome

private abbrev HeapIProp := IProp (WasmHeapGF Universal.State)

/-- Initial Wasm state, with only the public input stream varied. -/
def entryInitialStore (input : List UInt32) : Store Universal.State :=
  { (Project.Mergesort.module.initialStore : Store Universal.State) with
    host := Universal.State.ofInput (serialize input) }

private def entryInstance : ModuleInstance Universal.State :=
  { module := Project.Mergesort.module
    host := Universal.envFor Project.Mergesort.module }

/-- The entry configuration is a genuine `.call 6` caller, exactly matching
the shape quantified by `Func3Spec`. -/
abbrev entryConfig (input : List UInt32) : Config Universal.State :=
  { expr := callExpr 6 [] {} [] [] 0 [] [] []
    store :=
      { runtime := { instances := #[entryInstance], entry := ⟨0⟩ }
        wasm := entryInitialStore input } }

@[simp] theorem entryConfig_entry (input : List UInt32) :
    (entryConfig input).store.runtime.entry = ⟨0⟩ := by rfl

@[simp] theorem entryConfig_entry_id (input : List UInt32) :
    (entryConfig input).store.runtime.entry.id = 0 := by rfl

@[simp] theorem entryConfig_currentModule (input : List UInt32) :
    (entryConfig input).store.runtime.currentModule =
      Project.Mergesort.module := by rfl

@[simp] theorem entryConfig_currentHost (input : List UInt32) :
    (entryConfig input).store.runtime.currentHost =
      Universal.envFor Project.Mergesort.module := by rfl

@[simp] theorem entryConfig_host (input : List UInt32) :
    (entryConfig input).store.wasm.host =
      Universal.State.ofInput (serialize input) := by rfl

/-- The public export-call initializer resolves to the same call configuration;
in particular, it does not enter `func3Def.body` directly. -/
theorem startCallConfig_eq (input : List UInt32) :
    startCallConfig? (Universal.envFor Project.Mergesort.module)
      Project.Mergesort.module "mergesort"
      (Universal.State.ofInput (serialize input)) =
      some (entryConfig input) := by
  rfl

/-- Public postcondition before the final machine store is hidden. -/
def entryPost (input : List UInt32) (outcome : ObservableOutcome)
    (store : MachineStore Universal.State) : Prop :=
  let run : Project.Mergesort.Spec.RunOutcome := ⟨outcome, store.wasm.host⟩
  Project.Mergesort.Spec.RanOutOfMemory run ∨
    Project.Mergesort.Spec.Post input run

/-- Public value inputs always produce a whole-word byte stream.  The
body-level proof must use this fact at the `chunks_exact(4)` guard; the adequacy
bridge does not postulate that the compiler's bounds/panic branches return. -/
theorem entryInput_valid (input : List UInt32) :
    (serialize input).length % 4 = 0 := by
  rw [serialize_length]; omega

private abbrev entryMemory : Mem :=
  (Project.Mergesort.module.initialStore : Store Universal.State).mem

def entryStackBytes : List UInt8 :=
  physicalBytes entryMemory entryStackLow 288

private def entryCursorBytes : List UInt8 :=
  physicalBytes entryMemory allocatorCursor 4

private abbrev entryStackHeap : WasmHeapMap (Option UInt8) :=
  insertFreshBytes ∅ entryStackLow entryStackBytes

abbrev entryHeap : WasmHeapMap (Option UInt8) :=
  insertFreshBytes entryStackHeap allocatorCursor entryCursorBytes

def entryGlobals : WasmGlobalMap Value :=
  insert ∅ (⟨0, 0⟩ : GlobalKey) (.i32 entryStackTop)

@[simp] theorem entryStackBytes_length : entryStackBytes.length = 288 := by
  simp [entryStackBytes]

private theorem empty_below_entryStack :
    HeapBelow (∅ : WasmHeapMap (Option UInt8)) entryStackLow.toNat := by
  intro key value hget
  rw [get?_empty] at hget; contradiction

private theorem entryStackHeap_below_cursor :
    HeapBelow entryStackHeap allocatorCursor.toNat := by
  have h := HeapBelow.insertFreshBytes
    (bytes := entryStackBytes) empty_below_entryStack (by
      rw [entryStackBytes_length]
      decide)
  exact h.mono (by decide)

theorem entryHeap_below_heapBase : HeapBelow entryHeap heapBase.toNat := by
  have h := HeapBelow.insertFreshBytes
    (bytes := entryCursorBytes) entryStackHeap_below_cursor (by
      change allocatorCursor.toNat + 4 < UInt32.size
      decide)
  exact h.mono (by decide)

private theorem entryCursorBytes_zero :
    entryCursorBytes = [0, 0, 0, 0] := by
  decide

private theorem entryCursorBytes_u32 :
  entryCursorBytes =
      [u32Byte 0 0, u32Byte 0 1, u32Byte 0 2, u32Byte 0 3] := by
  rw [entryCursorBytes_zero]
  decide

private theorem entryHost_eq (input : List UInt32) :
    Universal.State.ofInput (serialize input) =
      ({ stdio := { input := serialize input, output := [] }
         random := default
         oom := { raised := false } } : Universal.State) := by
  rfl

theorem entryHeap_facts (input : List UInt32) :
    heapAgreesWithMem entryHeap (storeResolve (entryConfig input).store) ∧
      heapAddressesInBounds entryHeap
        (storeResolve (entryConfig input).store) := by
  have hstack := insertFreshPhysicalBytes_facts
    (∅ : WasmHeapMap (Option UInt8))
    (storeResolve (entryConfig input).store) entryMemory entryStackLow 288
    (by rfl)
    (heapAgreesWithMem_empty _)
    (heapAddressesInBounds_empty _)
    (by decide) (by decide)
  have hcursor := insertFreshPhysicalBytes_facts
    entryStackHeap (storeResolve (entryConfig input).store)
    entryMemory allocatorCursor 4 (by rfl) hstack.1 hstack.2
    (by decide) (by decide)
  exact hcursor

theorem entryGlobals_agree (input : List UInt32) :
    globalHeapAgrees entryGlobals (entryConfig input).store.wasm.globals := by
  exact globalHeapAgrees_singleton rfl

private theorem entryGlobals_pointsTo [WasmGlobalGS Universal.State] :
    ([∗map] index ↦ value ∈ entryGlobals,
      globalPointsTo index value) ⊢ StackPointer entryStackTop := by
  unfold entryGlobals StackPointer
  rw [(BI.BigSepM.bigSepM_insert
      (get?_empty (⟨0, 0⟩ : GlobalKey))).to_eq,
    BI.BigSepM.bigSepM_empty.to_eq, BI.sep_emp.to_eq,
    globalPointsToAt_eq]

/-- A stream fragment agrees with the public host fields in the authoritative
final machine state.  The random component remains existential and invisible
to the public postcondition. -/
private theorem Streams_public [WasmSmallStepGS hlc Universal.State]
    (input output : List UInt8) (raised : Bool) :
    Streams input output raised -∗
      ∀ (store : MachineStore Universal.State) (observations : List StepKind),
        stateInterp (GF := WasmHeapGF Universal.State) store 0 observations 0 -∗
        ⌜store.wasm.host.stdio.output = output ∧
          store.wasm.host.oom.raised = raised⌝ := by
  iintro Hstreams
  iunfold Streams at Hstreams
  icases Hstreams with ⟨%random, Hhost⟩
  iintro %store %observations Hstate
  ihave %hhost :
      ⌜store.wasm.host =
        ({ stdio := { input := input, output := output }
           random := random
           oom := { raised := raised } } : Universal.State)⌝ $$
      [Hstate Hhost]
  · iapply stateInterp_host_agree store 0 observations 0
    iframe Hstate Hhost
  ipureintro
  rw [hhost]
  exact ⟨rfl, rfl⟩

/-- Construct exactly the resources consumed by `Func3Spec` from adequacy's
physical initial state.  The allocator metadata name and the Universal random
state are internal existentials. -/
theorem initialResources [WasmSmallStepGS hlc Universal.State]
    (input : List UInt32) :
    (([∗map] address ↦ value ∈ entryHeap,
        pointsTo (GF := WasmHeapGF Universal.State) (H := WasmHeapMap)
          address (DFrac.own 1) value) ∗
      ([∗map] index ↦ value ∈ entryGlobals,
        globalPointsTo index value) ∗
      runtimeModuleOwn ⟨0⟩ Project.Mergesort.module ∗
      hostEnvOwn 0 (Universal.envFor Project.Mergesort.module) ∗
      hostStateOwn (Universal.State.ofInput (serialize input)) ∗
      heapFrontierOwn heapBase.toNat ∗
      memoryPagesOwn entryMemory.pages) ==∗
      ∃ heapId : GName,
        RuntimeContext ∗
        StackPointer entryStackTop ∗
        StackRegion entryStackLow entryStackBytes ∗
        BumpHeap heapId 0 heapBase.toNat AllocationHistory.empty ∗
        Streams (serialize input) [] false := by
  iintro ⟨Hheap, Hglobals, Hruntime, Henv, Hhost, Hfrontier, Hpages⟩
  ihave ⟨HcursorBytes, HstackHeap⟩ :=
    insertFreshBytes_bigSep_pointsToBytes entryStackHeap allocatorCursor
      entryCursorBytes entryStackHeap_below_cursor (by
        change allocatorCursor.toNat + 4 < UInt32.size
        decide) $$ Hheap
  ihave ⟨Hstack, _Hempty⟩ :=
    insertFreshBytes_bigSep_pointsToBytes
      (∅ : WasmHeapMap (Option UInt8)) entryStackLow entryStackBytes
      empty_below_entryStack (by
        rw [entryStackBytes_length]
        decide) $$ HstackHeap
  ihave Hcursor : pointsTo_u32 0 allocatorCursor 0 $$ [HcursorBytes]
  · iapply (pointsTo_u32_as_bytes 0 allocatorCursor 0).mpr
    irw_exact [← entryCursorBytes_u32] with HcursorBytes
  ihave Hsp := entryGlobals_pointsTo $$ Hglobals
  ihave Hstreams : Streams (serialize input) [] false $$ [Hhost]
  · iunfold Streams
    iexists default
    irw_exact [← entryHost_eq input] with Hhost
  imod AllocMetaAuth_alloc_empty (host := Universal.State) with
    ⟨%heapId, Hmetadata⟩
  ihave HbumpResources :
      pointsTo_u32 0 allocatorCursor 0 ∗
        heapFrontierOwn heapBase.toNat ∗
        AllocMetaAuth heapId AllocationHistory.empty ∗
        memoryPagesOwn entryMemory.pages $$
      [Hcursor Hfrontier Hmetadata Hpages]
  · iframe Hcursor Hfrontier Hmetadata Hpages
  ihave Hbump := BumpHeap_empty heapId entryMemory.pages (by decide) $$
    HbumpResources
  imodintro
  iexists heapId
  isplitl [Hruntime Henv]
  · iunfold RuntimeContext
    iframe Hruntime Henv
  isplitl_exact Hsp
  isplitl [Hstack]
  · unfold StackRegion Project.Mergesort.Representations.ByteSlice
    isplitr
    · ipureintro
      rw [entryStackBytes_length]
      decide
    · iexact Hstack
  isplitl_exact Hbump
  · iexact Hstreams

private abbrev irisEntryPost [WasmSmallStepGS hlc Universal.State]
    (input : List UInt32) : ObservableOutcome → HeapIProp :=
  fun outcome => iprop(∀ (store : MachineStore Universal.State)
      (observations : List StepKind),
    stateInterp (GF := WasmHeapGF Universal.State) store 0 observations 0 -∗
      ⌜entryPost input outcome store⌝)

/-- Normal driver resources establish the public sorted-output postcondition;
all stack, allocator, and ghost resources are intentionally hidden. -/
private theorem DriverSuccess_public
    [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (input : List UInt32) :
    DriverSuccess heapId input -∗ irisEntryPost input (.done []) := by
  iintro Hsuccess
  iunfold DriverSuccess at Hsuccess
  icases Hsuccess with
    ⟨%sorted, %stackBytes, %storedCursor, %frontier, %history,
      %hfacts, _Hsp, _Hstack, _Hbump, Hstreams⟩
  iintro %store %observations Hstate
  ihave Hfields := Streams_public [] (serialize sorted) false $$ Hstreams
  ispecialize Hfields $$ %store %observations
  ihave %hfields := Hfields $$ Hstate
  ipureexact Or.inr ⟨sorted, ⟨rfl, hfields.1⟩, hfacts.1⟩

/-- Every phase-classified OOM state contains the precise typed stream marker
installed by the `talos.oom` host call. -/
private theorem DriverOOMState_streams
    [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (input : List UInt32) (phase : DriverOOMPhase) :
    DriverOOMState heapId input phase -∗
      ∃ remaining : List UInt8, Streams remaining [] true := by
  cases phase with
  | reserve =>
      iintro Hoom
      iunfold DriverOOMState at Hoom
      iunfold DriverReserveOOM at Hoom
      icases Hoom with
        ⟨%capacity, %ptr, %appended, %current, %remaining, %chunkTail,
          %outputBytes, %shadow, %storedCursor, %frontier, %history,
          %_hfacts, _Hsp, _Hreserve, _Hframe, _Hbump, Hstreams⟩
      iexists remaining
      iexact Hstreams
  | values =>
      iintro Hoom
      iunfold DriverOOMState at Hoom
      iunfold DriverValuesOOM at Hoom
      icases Hoom with
        ⟨%capacity, %ptr, %chunkBytes, %outputBytes, %shadow,
          %storedCursor, %frontier, %history, %_hfacts,
          _Hsp, _Hreserve, _Hframe, _Hbump, Hstreams⟩
      iexists ([] : List UInt8)
      iexact Hstreams
  | scratch =>
      iintro Hoom
      iunfold DriverOOMState at Hoom
      iunfold DriverScratchOOM at Hoom
      icases Hoom with
        ⟨%capacity, %ptr, %valuesPtr, %valuesId, %chunkBytes,
          %outputBytes, %shadow, %storedCursor, %frontier, %history,
          %_hfacts, _Hsp, _Hreserve, _Hframe, _Hvalues, _Hbump, Hstreams⟩
      iexists ([] : List UInt8)
      iexact Hstreams

/-- The exceptional continuation in `Func3Spec` maps every valid driver OOM
phase to exactly the public `talos.oom` terminal outcome. -/
private theorem DriverOOM_public
    [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (input : List UInt32) :
    (∃ phase : DriverOOMPhase, DriverOOMState heapId input phase) -∗
      irisEntryPost input (.trapped (.host OOM.trapMessage)) := by
  iintro ⟨%phase, Hoom⟩
  ihave ⟨%remaining, Hstreams⟩ := DriverOOMState_streams heapId input phase $$ Hoom
  iintro %store %observations Hstate
  ihave Hfields := Streams_public remaining [] true $$ Hstreams
  ispecialize Hfields $$ %store %observations
  ihave %hfields := Hfields $$ Hstate
  ipureexact Or.inl ⟨rfl, hfields.2⟩

/-- Apply the future main-function correctness theorem at the genuine exported
call site.  This is the only bridge from entry resources to `Func3Spec`. -/
theorem twp_entry_of_func3
    [WasmSmallStepGS hlc Universal.State]
    (hfunc3 : Func3Spec (hlc := hlc)) (input : List UInt32) :
    (([∗map] address ↦ value ∈ entryHeap,
        pointsTo (GF := WasmHeapGF Universal.State) (H := WasmHeapMap)
          address (DFrac.own 1) value) ∗
      ([∗map] index ↦ value ∈ entryGlobals,
        globalPointsTo index value) ∗
      runtimeModuleOwn ⟨0⟩ Project.Mergesort.module ∗
      hostEnvOwn 0 (Universal.envFor Project.Mergesort.module) ∗
      hostStateOwn (Universal.State.ofInput (serialize input)) ∗
      heapFrontierOwn heapBase.toNat ∗
      memoryPagesOwn entryMemory.pages) ⊢
      WP (entryConfig input).expr @ Stuckness.NotStuck; ⊤
        [{ irisEntryPost input }] := by
  iintro Hinitial
  imod initialResources input $$ Hinitial with
    ⟨%heapId, Hruntime, Hsp, Hstack, Hbump, Hstreams⟩
  have hcall := hfunc3 heapId input entryStackBytes
    (callerLocals := {}) (stack := []) (code := []) (arity := 0)
    (remainder := []) (controls := []) (calls := [])
    (s := Stuckness.NotStuck) (E := ⊤) (Φ := irisEntryPost input)
  unfold CallContract at hcall
  iapply hcall
  iframe Hruntime Hsp Hstack Hbump Hstreams
  isplitr_pureexact entryStackBytes_length
  isplitr
  · iintro _Hruntime Hsuccess
    unfold ResumeWP resumeExpr
    isimp only [List.nil_append]
    iapply (twp_finish (locals := ({} : Locals)) (values := [])
      (arity := 0) (remainder := []))
    isimp only [List.take_zero, List.nil_append]
    iapply Wasm.SmallStep.twp_outcome_done
    iapply_exact DriverSuccess_public heapId input with Hsuccess
  · iapply DriverOOM_public heapId input

/-- Generic operational bridge for the concrete entry call.  This theorem is
partial adequacy only: it classifies all finite `.done`/`.trapped` traces and
does not assert strong normalization or exhibit a terminal trace. -/
theorem entry_partiallyMeets_of_func3
    (hfunc3 : ∀ {hlc : HasLC} [WasmSmallStepGS hlc Universal.State],
      Func3Spec (hlc := hlc))
    (input : List UInt32) :
    PartiallyMeetsOutcome (entryConfig input) (entryPost input) := by
  apply adequate_to_partiallyMeetsOutcome
  apply wasm_smallStep_heap_globals_runtime_host_store_adequacy_outcome_at
      (config := entryConfig input) (entryHeap) (entryGlobals)
      heapBase.toNat (entryPost input)
  · exact (entryHeap_facts input).1
  · exact (entryHeap_facts input).2
  · exact entryHeap_below_heapBase
  · exact entryGlobals_agree input
  · simp
  · intro gs
    iintro ⟨Hheap, Hglobals, Hruntime, Henv, Hhost, Hfrontier, Hpages⟩
    ihave Hruntime' :
        runtimeModuleOwn ⟨0⟩ Project.Mergesort.module $$ [Hruntime]
    · irw_exact [← entryConfig_entry input, ← entryConfig_currentModule input] with Hruntime
    ihave Henv' :
        hostEnvOwn 0 (Universal.envFor Project.Mergesort.module) $$ [Henv]
    · irw_exact [← entryConfig_entry_id input, ← entryConfig_currentHost input] with Henv
    ihave Hhost' :
        hostStateOwn (Universal.State.ofInput (serialize input)) $$ [Hhost]
    · irw_exact [← entryConfig_host input] with Hhost
    iapply twp.to_wp
    iapply twp_entry_of_func3 (hfunc3 := hfunc3) input
    ihave Hpages' : memoryPagesOwn entryMemory.pages $$ [Hpages]
    · rw [show entryMemory.pages =
          (entryConfig input).store.wasm.mem.pages by rfl]
      iexact Hpages
    iframe Hheap Hglobals Hruntime' Henv' Hhost' Hfrontier Hpages'

/-- Conditional final adequacy.  Once `func3_correct` is available, the final
public proof is exactly `entry_adequacy_of_func3 func3_correct`. -/
theorem entry_adequacy_of_func3
    (hfunc3 : ∀ {hlc : HasLC} [WasmSmallStepGS hlc Universal.State],
      Func3Spec (hlc := hlc)) :
    Project.Mergesort.Spec.PublicEntrySpecification := by
  unfold Project.Mergesort.Spec.PublicEntrySpecification
  intro input
  unfold Project.Mergesort.Spec.PartiallyRuns
  refine ⟨entryConfig input, ?_, ?_⟩
  · exact startCallConfig_eq input
  · intro trace outcome store hsteps
    have hpublic := entry_partiallyMeets_of_func3 hfunc3 input
      trace outcome store hsteps
    simpa [entryPost, serialize, U32Codec,
      Project.Mergesort.Spec.encodeValues, SortedPermutation] using hpublic

end Project.Mergesort.Adequacy
