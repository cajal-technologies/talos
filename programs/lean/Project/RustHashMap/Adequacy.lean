import Project.RustHashMap.EntryContracts
import CodeLib.SepLogic.SmallStepOutcomeAdequacy
import CodeLib.SepLogic.SmallStepOutcomeAdequacyFrontier

set_option maxRecDepth 8388608
set_option maxHeartbeats 0

/-!
# Adequacy for the hash map export calls

This module connects an `EntrySpec` call contract of one export wrapper to
the two public contracts `Project.RustHashMap.Spec.WritesOrOOM` and
`Project.RustHashMap.Spec.TerminatesWritingOrOOM`.  It is a port of
`Project.Mergesort.Adequacy` with three changes:

* The bridge is generic in the export name, the wrapper index, and the
  expected output function.  One theorem serves the five exports.
* The initial heap owns the whole shadow stack, not one fixed frame, so the
  driver proofs can hand any depth of frames to their callees.
* The initial heap map is sealed behind an opaque constant.  A big
  separating conjunction over an open map makes the kernel fold the one
  mebibyte stack into the tree map, and that check does not finish.

It also adds a total bridge.  The partial bridge classifies the finite
normal and trapping traces.  The total bridge, through the frontier frontend of
`CodeLib.SepLogic.SmallStepOutcomeAdequacyFrontier`, also proves termination.
Both bridges apply the same `EntrySpec`, which is a total-WP contract.
-/

namespace Project.RustHashMap.Adequacy

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open Project.RustHashMap.Allocator
open Project.RustHashMap.EntryContracts
open scoped Wasm.SmallStep.Outcome

/-- Initial Wasm state, with only the public input stream varied. -/
def entryInitialStore (input : List UInt8) : Store Universal.State :=
  { (Project.RustHashMap.«module».initialStore : Store Universal.State) with
    host := Universal.State.ofInput input }

private def entryInstance : ModuleInstance Universal.State :=
  { module := Project.RustHashMap.«module»
    host := Universal.envFor Project.RustHashMap.«module» }

/-- The entry configuration is a genuine `.call index` caller, exactly the
shape that `EntrySpec` quantifies. -/
abbrev entryConfig (index : Nat) (input : List UInt8) :
    Config Universal.State :=
  { expr := callExpr index [] {} [] [] 0 [] [] []
    store :=
      { runtime := { instances := #[entryInstance], entry := ⟨0⟩ }
        wasm := entryInitialStore input } }

@[simp] theorem entryConfig_entry (index : Nat) (input : List UInt8) :
    (entryConfig index input).store.runtime.entry = ⟨0⟩ := by rfl

@[simp] theorem entryConfig_entry_id (index : Nat) (input : List UInt8) :
    (entryConfig index input).store.runtime.entry.id = 0 := by rfl

@[simp] theorem entryConfig_currentModule (index : Nat) (input : List UInt8) :
    (entryConfig index input).store.runtime.currentModule =
      Project.RustHashMap.«module» := by rfl

@[simp] theorem entryConfig_currentHost (index : Nat) (input : List UInt8) :
    (entryConfig index input).store.runtime.currentHost =
      Universal.envFor Project.RustHashMap.«module» := by rfl

@[simp] theorem entryConfig_host (index : Nat) (input : List UInt8) :
    (entryConfig index input).store.wasm.host =
      Universal.State.ofInput input := by rfl

/-! ## The five export starts

The public export-call initializer resolves each name to the call
configuration of its wrapper.  It does not enter a function body directly. -/

theorem startCallConfig_contains_key (input : List UInt8) :
    startCallConfig? (Universal.envFor Project.RustHashMap.«module»)
      Project.RustHashMap.«module» "map_contains_key"
      (Universal.State.ofInput input) =
      some (entryConfig 28 input) := by rfl

theorem startCallConfig_get (input : List UInt8) :
    startCallConfig? (Universal.envFor Project.RustHashMap.«module»)
      Project.RustHashMap.«module» "map_get"
      (Universal.State.ofInput input) =
      some (entryConfig 29 input) := by rfl

theorem startCallConfig_insert (input : List UInt8) :
    startCallConfig? (Universal.envFor Project.RustHashMap.«module»)
      Project.RustHashMap.«module» "map_insert"
      (Universal.State.ofInput input) =
      some (entryConfig 30 input) := by rfl

theorem startCallConfig_len (input : List UInt8) :
    startCallConfig? (Universal.envFor Project.RustHashMap.«module»)
      Project.RustHashMap.«module» "map_len"
      (Universal.State.ofInput input) =
      some (entryConfig 31 input) := by rfl

theorem startCallConfig_remove (input : List UInt8) :
    startCallConfig? (Universal.envFor Project.RustHashMap.«module»)
      Project.RustHashMap.«module» "map_remove"
      (Universal.State.ofInput input) =
      some (entryConfig 32 input) := by rfl

/-- Public postcondition before the final machine store is hidden. -/
def entryPost (expected : List UInt8) (outcome : ObservableOutcome)
    (store : MachineStore Universal.State) : Prop :=
  let run : StdioContract.RunOutcome := ⟨outcome, store.wasm.host⟩
  StdioContract.RanOutOfMemory run ∨ StdioContract.ReturnsOutput run expected

/-! ## Initial heap and globals -/

private abbrev entryMemory : Mem :=
  (Project.RustHashMap.«module».initialStore : Store Universal.State).mem

/-- The initial bytes of the whole shadow stack. -/
def entryStackBytes : List UInt8 :=
  physicalBytes entryMemory 0 stackSize

private def entryCursorBytes : List UInt8 :=
  physicalBytes entryMemory allocatorCursor 4

/-- The initial bytes of the thread-local `RandomState` region. -/
def entryRandomBytes : List UInt8 :=
  physicalBytes entryMemory randomStateCell randomStateSize

/-- The initial bytes of the one data segment.  It starts at the stack top
and ends at the allocator cursor.

The compiled error paths pass pointers into this region, and a body proof
that follows one of them needs the bytes as a resource.  Absolute function
57 copies the message of an `io::Error` out of here with `memory.copy`. -/
def entryDataBytes : List UInt8 :=
  physicalBytes entryMemory entryStackTop dataSegmentSize

private abbrev entryStackHeap : WasmHeapMap (Option UInt8) :=
  insertFreshBytes ∅ 0 entryStackBytes

private abbrev entryDataHeap : WasmHeapMap (Option UInt8) :=
  insertFreshBytes entryStackHeap entryStackTop entryDataBytes

private abbrev entryCursorHeap : WasmHeapMap (Option UInt8) :=
  insertFreshBytes entryDataHeap allocatorCursor entryCursorBytes

/-- The sealed initial heap.  The kernel must not evaluate the one mebibyte
fold into the tree map, so the map lives behind an opaque constant and
`entryHeap_eq` is the only way to open it. -/
private structure EntryHeapSeal where
  heap : WasmHeapMap (Option UInt8)
  heap_eq : heap = insertFreshBytes entryCursorHeap randomStateCell entryRandomBytes

private opaque entryHeapSeal : EntryHeapSeal := ⟨_, rfl⟩

/-- The initial owned heap: the whole shadow stack, the data segment, the
allocator cursor word, and the thread-local `RandomState` region.  Together
they cover every address below `heapBase` that the module can touch. -/
def entryHeap : WasmHeapMap (Option UInt8) := entryHeapSeal.heap

theorem entryHeap_eq :
    entryHeap = insertFreshBytes entryCursorHeap randomStateCell entryRandomBytes :=
  entryHeapSeal.heap_eq

def entryGlobals : WasmGlobalMap Value :=
  insert ∅ (⟨0, 0⟩ : GlobalKey) (.i32 entryStackTop)

@[simp] theorem entryStackBytes_length :
    entryStackBytes.length = stackSize := by
  simp [entryStackBytes]

@[simp] theorem entryRandomBytes_length :
    entryRandomBytes.length = randomStateSize := by
  simp [entryRandomBytes]

@[simp] theorem entryDataBytes_length :
    entryDataBytes.length = dataSegmentSize := by
  simp [entryDataBytes]

private theorem empty_below_entryStack :
    HeapBelow (∅ : WasmHeapMap (Option UInt8)) (0 : UInt32).toNat := by
  intro key value hget
  rw [get?_empty] at hget; contradiction

private theorem entryStackHeap_below_data :
    HeapBelow entryStackHeap entryStackTop.toNat := by
  have h := HeapBelow.insertFreshBytes
    (bytes := entryStackBytes) empty_below_entryStack (by
      rw [entryStackBytes_length]; decide)
  exact h.mono (by rw [entryStackBytes_length]; decide)

private theorem entryDataHeap_below_cursor :
    HeapBelow entryDataHeap allocatorCursor.toNat := by
  have h := HeapBelow.insertFreshBytes
    (bytes := entryDataBytes) entryStackHeap_below_data (by
      rw [entryDataBytes_length]; decide)
  exact h.mono (by rw [entryDataBytes_length]; decide)

private theorem entryCursorHeap_below_random :
    HeapBelow entryCursorHeap randomStateCell.toNat := by
  have h := HeapBelow.insertFreshBytes
    (bytes := entryCursorBytes) entryDataHeap_below_cursor (by
      change allocatorCursor.toNat + 4 < UInt32.size
      decide)
  exact h.mono (by decide)

theorem entryHeap_below_heapBase : HeapBelow entryHeap heapBase.toNat := by
  rw [entryHeap_eq]
  have h := HeapBelow.insertFreshBytes
    (bytes := entryRandomBytes) entryCursorHeap_below_random (by
      rw [entryRandomBytes_length]; decide)
  refine h.mono ?_
  rw [entryRandomBytes_length]
  decide

private theorem entryCursorBytes_zero :
    entryCursorBytes = [0, 0, 0, 0] := by decide

/-- The thread-local state byte of the initial memory.  The cell is `.bss`,
so every byte of it is zero. -/
private theorem entryRandomBytes_state : entryRandomBytes[16]? = some 0 := by
  decide

/-- The state byte is not the drop marker.  `collect_entries` panics on
that value, and the entry contract rules the panic out. -/
private theorem entryRandomBytes_not_dropping :
    entryRandomBytes[16]? ≠ some 2 := by
  rw [entryRandomBytes_state]
  decide

/-- The first 24 bytes of the data segment are the static singleton table:
eight `EMPTY` control bytes, then the control pointer 1048576, the bucket
mask 0, the growth 0 and the item count 0. -/
private theorem entryDataBytes_table :
    entryDataBytes.take 24 = staticTableBytes := by decide

private theorem entryCursorBytes_u32 :
  entryCursorBytes =
      [u32Byte 0 0, u32Byte 0 1, u32Byte 0 2, u32Byte 0 3] := by
  rw [entryCursorBytes_zero]; decide

private theorem entryHost_eq (input : List UInt8) :
    Universal.State.ofInput input =
      ({ stdio := { input := input, output := [] }
         random := default
         oom := { raised := false } } : Universal.State) := by rfl

theorem entryHeap_facts (index : Nat) (input : List UInt8) :
    heapAgreesWithMem entryHeap
        (storeResolve (entryConfig index input).store) ∧
      heapAddressesInBounds entryHeap
        (storeResolve (entryConfig index input).store) := by
  rw [entryHeap_eq]
  have hstack := insertFreshPhysicalBytes_facts
    (∅ : WasmHeapMap (Option UInt8))
    (storeResolve (entryConfig index input).store) entryMemory 0 stackSize
    (by rfl)
    (heapAgreesWithMem_empty _)
    (heapAddressesInBounds_empty _)
    (by decide) (by decide)
  have hdata := insertFreshPhysicalBytes_facts
    entryStackHeap (storeResolve (entryConfig index input).store)
    entryMemory entryStackTop dataSegmentSize (by rfl) hstack.1 hstack.2
    (by decide) (by decide)
  have hcursor := insertFreshPhysicalBytes_facts
    entryDataHeap (storeResolve (entryConfig index input).store)
    entryMemory allocatorCursor 4 (by rfl) hdata.1 hdata.2
    (by decide) (by decide)
  have hrandom := insertFreshPhysicalBytes_facts
    entryCursorHeap (storeResolve (entryConfig index input).store)
    entryMemory randomStateCell randomStateSize (by rfl) hcursor.1 hcursor.2
    (by decide) (by decide)
  exact hrandom

theorem entryGlobals_agree (index : Nat) (input : List UInt8) :
    globalHeapAgrees entryGlobals (entryConfig index input).store.wasm.globals :=
  globalHeapAgrees_singleton rfl

private theorem entryGlobals_pointsTo [WasmGlobalGS Universal.State] :
    ([∗map] index ↦ value ∈ entryGlobals,
      globalPointsTo index value) ⊢ StackPointer entryStackTop := by
  unfold entryGlobals StackPointer
  rw [(BI.BigSepM.bigSepM_insert
      (get?_empty (⟨0, 0⟩ : GlobalKey))).to_eq,
    BI.BigSepM.bigSepM_empty.to_eq, BI.sep_emp.to_eq,
    globalPointsToAt_eq]

/-- A stream fragment agrees with the public host fields in the authoritative
final machine state.  The random component stays existential. -/
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
  · iapply_frame stateInterp_host_agree store 0 observations 0 using [Hstate Hhost]
  ipureexact (by rw [hhost]; exact ⟨rfl, rfl⟩)

/-- Open the sealed initial heap into its two owned byte ranges.  The lemma
composes entailments at the term level, so no proof-mode step holds a big
separating conjunction over an evaluable map. -/
private theorem entryHeap_split [WasmSmallStepGS hlc Universal.State] :
    ([∗map] address ↦ value ∈ entryHeap,
        pointsTo (GF := WasmHeapGF Universal.State) (H := WasmHeapMap)
          address (DFrac.own 1) value) ⊢
      pointsToBytes 0 randomStateCell entryRandomBytes ∗
        pointsToBytes 0 allocatorCursor entryCursorBytes ∗
        pointsToBytes 0 entryStackTop entryDataBytes ∗
        pointsToBytes 0 0 entryStackBytes := by
  rw [entryHeap_eq]
  refine (insertFreshBytes_bigSep_pointsToBytes entryCursorHeap randomStateCell
    entryRandomBytes entryCursorHeap_below_random (by
      rw [entryRandomBytes_length]; decide)).trans ?_
  refine BI.sep_mono_right ?_
  refine (insertFreshBytes_bigSep_pointsToBytes entryDataHeap allocatorCursor
    entryCursorBytes entryDataHeap_below_cursor (by
      change allocatorCursor.toNat + 4 < UInt32.size
      decide)).trans ?_
  refine BI.sep_mono_right ?_
  refine (insertFreshBytes_bigSep_pointsToBytes entryStackHeap entryStackTop
    entryDataBytes entryStackHeap_below_data (by
      rw [entryDataBytes_length]; decide)).trans ?_
  refine BI.sep_mono_right ?_
  refine (insertFreshBytes_bigSep_pointsToBytes
    (∅ : WasmHeapMap (Option UInt8)) 0 entryStackBytes
    empty_below_entryStack (by rw [entryStackBytes_length]; decide)).trans ?_
  exact BI.sep_elim_left

/-- Construct exactly the resources that `EntrySpec` consumes from the
physical initial state.  The allocator metadata name and the Universal random
state are internal existentials. -/
theorem initialResources [WasmSmallStepGS hlc Universal.State]
    (input : List UInt8) :
    (([∗map] address ↦ value ∈ entryHeap,
        pointsTo (GF := WasmHeapGF Universal.State) (H := WasmHeapMap)
          address (DFrac.own 1) value) ∗
      ([∗map] index ↦ value ∈ entryGlobals,
        globalPointsTo index value) ∗
      runtimeModuleOwn ⟨0⟩ Project.RustHashMap.«module» ∗
      hostEnvOwn 0 (Universal.envFor Project.RustHashMap.«module») ∗
      hostStateOwn (Universal.State.ofInput input) ∗
      heapFrontierOwn heapBase.toNat ∗
      memoryPagesOwn entryMemory.pages) ==∗
      ∃ heapId : GName,
        RuntimeContext ∗
        StackPointer entryStackTop ∗
        StackRegion 0 entryStackBytes ∗
        StackRegion entryStackTop entryDataBytes ∗
        StackRegion randomStateCell entryRandomBytes ∗
        BumpHeap heapId 0 heapBase.toNat AllocationHistory.empty ∗
        Streams input [] false := by
  iintro ⟨Hheap, Hglobals, Hruntime, Henv, Hhost, Hfrontier, Hpages⟩
  ihave ⟨HrandomBytes, HcursorBytes, HdataBytes, Hstack⟩ :=
    entryHeap_split $$ Hheap
  ihave Hcursor : pointsTo_u32 0 allocatorCursor 0 $$ [HcursorBytes]
  · iapply (pointsTo_u32_as_bytes 0 allocatorCursor 0).mpr
    irw_exact [← entryCursorBytes_u32] with HcursorBytes
  ihave Hsp := entryGlobals_pointsTo $$ Hglobals
  ihave Hstreams : Streams input [] false $$ [Hhost]
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
  · unfold StackRegion Slices.ByteSlice
    isplitr_pureexact (by rw [entryStackBytes_length]; decide)
    iexact Hstack
  isplitl [HdataBytes]
  · unfold StackRegion Slices.ByteSlice
    isplitr_pureexact (by rw [entryDataBytes_length]; decide)
    iexact HdataBytes
  isplitl [HrandomBytes]
  · unfold StackRegion Slices.ByteSlice
    isplitr_pureexact (by rw [entryRandomBytes_length]; decide)
    iexact HrandomBytes
  isplitl_exact Hbump
  · iexact Hstreams

/-! ## The bridge -/

private abbrev irisEntryPost [WasmSmallStepGS hlc Universal.State]
    (expected : List UInt8) : ObservableOutcome → HeapIProp :=
  fun outcome => iprop(∀ (store : MachineStore Universal.State)
      (observations : List StepKind),
    stateInterp (GF := WasmHeapGF Universal.State) store 0 observations 0 -∗
      ⌜entryPost expected outcome store⌝)

/-- Normal export resources give the public output postcondition. -/
private theorem ExportSuccess_public
    [WasmSmallStepGS hlc Universal.State] (expected : List UInt8) :
    ExportSuccess expected -∗ irisEntryPost expected (.done []) := by
  iintro Hsuccess
  iunfold ExportSuccess at Hsuccess
  icases Hsuccess with ⟨%remaining, Hstreams⟩
  iintro %store %observations Hstate
  ihave Hfields := Streams_public remaining expected false $$ Hstreams
  ispecialize Hfields $$ %store %observations
  ihave %hfields := Hfields $$ Hstate
  ipureexact Or.inr ⟨rfl, hfields.1⟩

/-- The OOM export resources give the public `talos.oom` postcondition. -/
private theorem ExportOOM_public
    [WasmSmallStepGS hlc Universal.State] (expected : List UInt8) :
    ExportOOM -∗ irisEntryPost expected (.trapped (.host OOM.trapMessage)) := by
  iintro Hoom
  iunfold ExportOOM at Hoom
  icases Hoom with ⟨%remaining, %output, Hstreams⟩
  iintro %store %observations Hstate
  ihave Hfields := Streams_public remaining output true $$ Hstreams
  ispecialize Hfields $$ %store %observations
  ihave %hfields := Hfields $$ Hstate
  ipureexact Or.inl ⟨rfl, hfields.2⟩

/-- Apply an export contract at the genuine exported call site.  This is the
only bridge from entry resources to `EntrySpec`. -/
theorem twp_entry_of_spec
    [WasmSmallStepGS hlc Universal.State]
    (index : Nat) (expected : List UInt8 → List UInt8)
    (hspec : EntrySpec (hlc := hlc) index expected) (input : List UInt8) :
    (([∗map] address ↦ value ∈ entryHeap,
        pointsTo (GF := WasmHeapGF Universal.State) (H := WasmHeapMap)
          address (DFrac.own 1) value) ∗
      ([∗map] index ↦ value ∈ entryGlobals,
        globalPointsTo index value) ∗
      runtimeModuleOwn ⟨0⟩ Project.RustHashMap.«module» ∗
      hostEnvOwn 0 (Universal.envFor Project.RustHashMap.«module») ∗
      hostStateOwn (Universal.State.ofInput input) ∗
      heapFrontierOwn heapBase.toNat ∗
      memoryPagesOwn entryMemory.pages) ⊢
      WP (entryConfig index input).expr @ Stuckness.NotStuck; ⊤
        [{ irisEntryPost (expected input) }] := by
  iintro Hinitial
  imod initialResources input $$ Hinitial with
    ⟨%heapId, Hruntime, Hsp, Hstack, Hdata, Hrandom, Hbump, Hstreams⟩
  have hcall := hspec heapId input entryStackBytes entryDataBytes
    entryRandomBytes
    (callerLocals := {}) (stack := []) (code := []) (arity := 0)
    (remainder := []) (controls := []) (calls := [])
    (s := Stuckness.NotStuck) (E := ⊤) (Φ := irisEntryPost (expected input))
  unfold CallContract at hcall
  iapply_frame hcall using [Hruntime Hsp Hstack Hdata Hrandom Hbump Hstreams]
  isplitr_pureexact
    ⟨entryStackBytes_length, entryDataBytes_length, entryRandomBytes_length,
      entryRandomBytes_not_dropping, entryDataBytes_table⟩
  isplitr
  · iintro _Hruntime Hsuccess
    unfold ResumeWP resumeExpr
    isimp only [List.nil_append]
    iapply (twp_finish (locals := ({} : Locals)) (values := [])
      (arity := 0) (remainder := []))
    isimp only [List.take_zero, List.nil_append]
    iapply Wasm.SmallStep.twp_outcome_done
    iapply_exact ExportSuccess_public (expected input) with Hsuccess
  · iapply ExportOOM_public (expected input)

/-- Generic operational bridge for one concrete export call.  This theorem is
partial adequacy only: it classifies all finite `.done` and `.trapped`
traces and does not assert termination. -/
theorem entry_partiallyMeets_of_spec
    (index : Nat) (expected : List UInt8 → List UInt8)
    (hspec : ∀ {hlc : HasLC} [WasmSmallStepGS hlc Universal.State],
      EntrySpec (hlc := hlc) index expected)
    (input : List UInt8) :
    PartiallyMeetsOutcome (entryConfig index input)
      (entryPost (expected input)) := by
  apply adequate_to_partiallyMeetsOutcome
  apply wasm_smallStep_heap_globals_runtime_host_store_adequacy_outcome_at
      (config := entryConfig index input) (entryHeap) (entryGlobals)
      heapBase.toNat (entryPost (expected input))
  · exact (entryHeap_facts index input).1
  · exact (entryHeap_facts index input).2
  · exact entryHeap_below_heapBase
  · exact entryGlobals_agree index input
  · simp
  · intro gs
    iintro ⟨Hheap, Hglobals, Hruntime, Henv, Hhost, Hfrontier, Hpages⟩
    ihave Hruntime' :
        runtimeModuleOwn ⟨0⟩ Project.RustHashMap.«module» $$ [Hruntime]
    · irw_exact [← entryConfig_entry index input,
        ← entryConfig_currentModule index input] with Hruntime
    ihave Henv' :
        hostEnvOwn 0 (Universal.envFor Project.RustHashMap.«module») $$ [Henv]
    · irw_exact [← entryConfig_entry_id index input,
        ← entryConfig_currentHost index input] with Henv
    ihave Hhost' :
        hostStateOwn (Universal.State.ofInput input) $$ [Hhost]
    · irw_exact [← entryConfig_host index input] with Hhost
    iapply twp.to_wp
    iapply twp_entry_of_spec index expected hspec input
    ihave Hpages' : memoryPagesOwn entryMemory.pages $$ [Hpages]
    · rw [show entryMemory.pages =
          (entryConfig index input).store.wasm.mem.pages by rfl]
      iexact Hpages
    iframe Hheap Hglobals Hruntime' Henv' Hhost' Hfrontier Hpages'

/-- The public partial contract of one export follows from its start
configuration and its entry contract. -/
theorem writesOrOOM_of_spec
    (name : String) (index : Nat) (expected : List UInt8 → List UInt8)
    (hstart : ∀ input : List UInt8,
      startCallConfig? (Universal.envFor Project.RustHashMap.«module»)
        Project.RustHashMap.«module» name (Universal.State.ofInput input) =
        some (entryConfig index input))
    (hspec : ∀ {hlc : HasLC} [WasmSmallStepGS hlc Universal.State],
      EntrySpec (hlc := hlc) index expected)
    (input : List UInt8) :
    Project.RustHashMap.Spec.WritesOrOOM name input (expected input) := by
  unfold Project.RustHashMap.Spec.WritesOrOOM StdioContract.WritesOrOOM
    StdioContract.PartiallyRuns PartiallyRunsWithOutcome
  refine ⟨entryConfig index input, hstart input, ?_⟩
  exact entry_partiallyMeets_of_spec index expected hspec input

/-! ## The five public contracts, conditional on the wrapper contracts -/

theorem containsKey_of_func25
    (hspec : ∀ {hlc : HasLC} [WasmSmallStepGS hlc Universal.State],
      Func25Spec (hlc := hlc)) :
    Project.RustHashMap.Spec.MapContainsKeySpec := by
  unfold Project.RustHashMap.Spec.MapContainsKeySpec
  intro bytes
  exact writesOrOOM_of_spec "map_contains_key" 28
    Project.RustHashMap.Spec.containsKeyOutput startCallConfig_contains_key
    (fun {_hlc} [_] => hspec) bytes

theorem get_of_func26
    (hspec : ∀ {hlc : HasLC} [WasmSmallStepGS hlc Universal.State],
      Func26Spec (hlc := hlc)) :
    Project.RustHashMap.Spec.MapGetSpec := by
  unfold Project.RustHashMap.Spec.MapGetSpec
  intro bytes
  exact writesOrOOM_of_spec "map_get" 29
    Project.RustHashMap.Spec.getOutput startCallConfig_get
    (fun {_hlc} [_] => hspec) bytes

theorem insert_of_func27
    (hspec : ∀ {hlc : HasLC} [WasmSmallStepGS hlc Universal.State],
      Func27Spec (hlc := hlc)) :
    Project.RustHashMap.Spec.MapInsertSpec := by
  unfold Project.RustHashMap.Spec.MapInsertSpec
  intro bytes
  exact writesOrOOM_of_spec "map_insert" 30
    Project.RustHashMap.Spec.insertOutput startCallConfig_insert
    (fun {_hlc} [_] => hspec) bytes

theorem len_of_func28
    (hspec : ∀ {hlc : HasLC} [WasmSmallStepGS hlc Universal.State],
      Func28Spec (hlc := hlc)) :
    Project.RustHashMap.Spec.MapLenSpec := by
  unfold Project.RustHashMap.Spec.MapLenSpec
  intro bytes
  exact writesOrOOM_of_spec "map_len" 31
    Project.RustHashMap.Spec.lenOutput startCallConfig_len
    (fun {_hlc} [_] => hspec) bytes

theorem remove_of_func29
    (hspec : ∀ {hlc : HasLC} [WasmSmallStepGS hlc Universal.State],
      Func29Spec (hlc := hlc)) :
    Project.RustHashMap.Spec.MapRemoveSpec := by
  unfold Project.RustHashMap.Spec.MapRemoveSpec
  intro bytes
  exact writesOrOOM_of_spec "map_remove" 32
    Project.RustHashMap.Spec.removeOutput startCallConfig_remove
    (fun {_hlc} [_] => hspec) bytes

/-! ## The total bridge

The same `EntrySpec` gives termination through the frontier frontend.  The
proof of `entry_terminatesWithOutcome_of_spec` is the proof of
`entry_partiallyMeets_of_spec` with three changes.  It applies the frontier
frontend in place of `adequate_to_partiallyMeetsOutcome` and the partial
frontend.  It introduces the `hlc` binder of that frontend.  It omits the
step `twp.to_wp`, which drops the termination half of the total WP. -/

/-- Generic total bridge for one concrete export call: the run terminates in
a `.done` or `.trapped` outcome that `entryPost` classifies. -/
theorem entry_terminatesWithOutcome_of_spec
    (index : Nat) (expected : List UInt8 → List UInt8)
    (hspec : ∀ {hlc : HasLC} [WasmSmallStepGS hlc Universal.State],
      EntrySpec (hlc := hlc) index expected)
    (input : List UInt8) :
    TerminatesWithOutcome (entryConfig index input)
      (entryPost (expected input)) := by
  apply wasm_smallStep_heap_globals_runtime_host_store_terminatesWithOutcome_frontier
      (config := entryConfig index input) (entryHeap) (entryGlobals)
      heapBase.toNat (entryPost (expected input))
  · exact (entryHeap_facts index input).1
  · exact (entryHeap_facts index input).2
  · exact entryHeap_below_heapBase
  · exact entryGlobals_agree index input
  · simp
  · intro hlc gs
    iintro ⟨Hheap, Hglobals, Hruntime, Henv, Hhost, Hfrontier, Hpages⟩
    ihave Hruntime' :
        runtimeModuleOwn ⟨0⟩ Project.RustHashMap.«module» $$ [Hruntime]
    · irw_exact [← entryConfig_entry index input,
        ← entryConfig_currentModule index input] with Hruntime
    ihave Henv' :
        hostEnvOwn 0 (Universal.envFor Project.RustHashMap.«module») $$ [Henv]
    · irw_exact [← entryConfig_entry_id index input,
        ← entryConfig_currentHost index input] with Henv
    ihave Hhost' :
        hostStateOwn (Universal.State.ofInput input) $$ [Hhost]
    · irw_exact [← entryConfig_host index input] with Hhost
    iapply twp_entry_of_spec index expected hspec input
    ihave Hpages' : memoryPagesOwn entryMemory.pages $$ [Hpages]
    · rw [show entryMemory.pages =
          (entryConfig index input).store.wasm.mem.pages by rfl]
      iexact Hpages
    iframe Hheap Hglobals Hruntime' Henv' Hhost' Hfrontier Hpages'

/-- The public total contract of one export follows from its start
configuration and its entry contract. -/
theorem terminatesWritingOrOOM_of_spec
    (name : String) (index : Nat) (expected : List UInt8 → List UInt8)
    (hstart : ∀ input : List UInt8,
      startCallConfig? (Universal.envFor Project.RustHashMap.«module»)
        Project.RustHashMap.«module» name (Universal.State.ofInput input) =
        some (entryConfig index input))
    (hspec : ∀ {hlc : HasLC} [WasmSmallStepGS hlc Universal.State],
      EntrySpec (hlc := hlc) index expected)
    (input : List UInt8) :
    Project.RustHashMap.Spec.TerminatesWritingOrOOM name input
      (expected input) := by
  unfold Project.RustHashMap.Spec.TerminatesWritingOrOOM
    StdioContract.TerminatesWritingOrOOM StdioContract.Runs
  refine ⟨entryConfig index input, hstart input, ?_⟩
  exact entry_terminatesWithOutcome_of_spec index expected hspec input

/-! ## The five public total contracts, conditional on the wrapper contracts -/

theorem containsKey_total_of_func25
    (hspec : ∀ {hlc : HasLC} [WasmSmallStepGS hlc Universal.State],
      Func25Spec (hlc := hlc)) :
    Project.RustHashMap.Spec.MapContainsKeyTotalSpec := by
  unfold Project.RustHashMap.Spec.MapContainsKeyTotalSpec
  intro bytes
  exact terminatesWritingOrOOM_of_spec "map_contains_key" 28
    Project.RustHashMap.Spec.containsKeyOutput startCallConfig_contains_key
    (fun {_hlc} [_] => hspec) bytes

theorem get_total_of_func26
    (hspec : ∀ {hlc : HasLC} [WasmSmallStepGS hlc Universal.State],
      Func26Spec (hlc := hlc)) :
    Project.RustHashMap.Spec.MapGetTotalSpec := by
  unfold Project.RustHashMap.Spec.MapGetTotalSpec
  intro bytes
  exact terminatesWritingOrOOM_of_spec "map_get" 29
    Project.RustHashMap.Spec.getOutput startCallConfig_get
    (fun {_hlc} [_] => hspec) bytes

theorem insert_total_of_func27
    (hspec : ∀ {hlc : HasLC} [WasmSmallStepGS hlc Universal.State],
      Func27Spec (hlc := hlc)) :
    Project.RustHashMap.Spec.MapInsertTotalSpec := by
  unfold Project.RustHashMap.Spec.MapInsertTotalSpec
  intro bytes
  exact terminatesWritingOrOOM_of_spec "map_insert" 30
    Project.RustHashMap.Spec.insertOutput startCallConfig_insert
    (fun {_hlc} [_] => hspec) bytes

theorem len_total_of_func28
    (hspec : ∀ {hlc : HasLC} [WasmSmallStepGS hlc Universal.State],
      Func28Spec (hlc := hlc)) :
    Project.RustHashMap.Spec.MapLenTotalSpec := by
  unfold Project.RustHashMap.Spec.MapLenTotalSpec
  intro bytes
  exact terminatesWritingOrOOM_of_spec "map_len" 31
    Project.RustHashMap.Spec.lenOutput startCallConfig_len
    (fun {_hlc} [_] => hspec) bytes

theorem remove_total_of_func29
    (hspec : ∀ {hlc : HasLC} [WasmSmallStepGS hlc Universal.State],
      Func29Spec (hlc := hlc)) :
    Project.RustHashMap.Spec.MapRemoveTotalSpec := by
  unfold Project.RustHashMap.Spec.MapRemoveTotalSpec
  intro bytes
  exact terminatesWritingOrOOM_of_spec "map_remove" 32
    Project.RustHashMap.Spec.removeOutput startCallConfig_remove
    (fun {_hlc} [_] => hspec) bytes

end Project.RustHashMap.Adequacy
