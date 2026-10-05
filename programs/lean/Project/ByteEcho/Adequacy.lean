import Project.ByteEcho.DriverProof
import CodeLib.SepLogic.SmallStepOutcomeAdequacy

set_option maxRecDepth 8388608
set_option maxHeartbeats 0

/-!
# Total adequacy for the byte-echo entry point

The exported body calls the generated bump allocator once, for one byte with
alignment one.  Unlike the GCD adapter's allocator, this one guards its bump
with `memory.size`.  A total proof must rule out the `memory.grow` path, but the
total adequacy lemma this file uses hands the WP no page resource at all (only
the partial `_at` form carries `memoryPagesOwn`), so nothing about the page
count is available in the WP layer.

The run is therefore split at the configuration immediately after
`memory.size`.  Every instruction before that point leaves the machine store
untouched, so the prefix is given as an explicit `Steps` trace and its end
store is literally the entry store; the physical page count `17` is
then an operand on the stack.  From there on the proof is total Iris WP:
the allocator tail commits the cursor and returns, and the driver suffix of
`DriverProof.lean` finishes the run.  Total outcome adequacy turns that TWP
into the finite trace required by the fuel-free public specification.
-/

namespace Project.ByteEcho.Adequacy

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.ByteEcho.Contracts
open scoped Wasm.SmallStep.Outcome

-- Unfold the definitionally equal generic/outcome Iris instances when matching WPs.
set_option backward.isDefEq.respectTransparency false

private abbrev HeapIProp := IProp (WasmHeapGF Universal.State)

theorem byte_echo_zeroArgument :
    ZeroArgumentExport Project.ByteEcho.module "byte_echo" := by
  decide +kernel

def entryInitialStore (b : UInt8) : Store Universal.State :=
  { (Project.ByteEcho.module.initialStore : Store Universal.State) with
    host := Universal.State.ofInput [b] }

private def entryInstance : ModuleInstance Universal.State :=
  { module := Project.ByteEcho.module
    host := Universal.envFor Project.ByteEcho.module }

def entryStore (b : UInt8) : MachineStore Universal.State :=
  { runtime := { instances := #[entryInstance], entry := ⟨0⟩ }
    wasm := entryInitialStore b }

def entryConfig (b : UInt8) : Config Universal.State :=
  { expr := .running
      { locals := ⟨[], [.i32 0], []⟩
        code := Project.ByteEcho.func0
        resultArity := 0
        callerRemainder := [] }
    store := entryStore b }

theorem startConfig_eq (b : UInt8) :
    startConfig? (Universal.envFor Project.ByteEcho.module)
      Project.ByteEcho.module "byte_echo"
      (Universal.State.ofInput [b]) =
      some (entryConfig b) := by
  rfl

/-! ## The allocator, up to and including `memory.size` -/

def allocArithmeticPrefix : Program :=
  [.localGet 1, .const 0xFFFFFFFF, .add, .localTee 2,
    .const 0, .load32 allocatorCursor, .localTee 3,
    .const heapBase, .localGet 3, .select, .add, .localTee 3,
    .localGet 2, .ltU, .br_if 0,
    .localGet 3, .const 0, .localGet 1, .sub, .and, .localTee 2,
    .localGet 0, .add, .localTee 1,
    .localGet 2, .ltU, .br_if 0,
    .localGet 1, .const 0, .ltS, .br_if 0]

def allocSizeProbe : Program :=
  [.localGet 1, .const 65535, .add, .const 16, .shrU,
    .localTee 3, .memorySize]

def allocGrowthTail : Program :=
  [.localTee 0, .leU, .br_if 1,
    .localGet 3, .localGet 0, .sub, .memoryGrow,
    .const 0xFFFFFFFF, .ne, .br_if 1]

def allocInnerBody : Program :=
  allocArithmeticPrefix ++ allocSizeProbe ++ allocGrowthTail

def allocOuterBody : Program :=
  [.block 0 0 allocInnerBody, .call 6, .unreachable]

def allocCommitTail : Program :=
  [.const 0, .localGet 1, .store32 allocatorCursor, .localGet 2]

def allocInnerFrame : ControlFrame :=
  { kind := .block
    paramArity := 0
    resultArity := 0
    body := allocInnerBody
    continuation := [.call 6, .unreachable]
    belowStack := [] }

def allocOuterFrame : ControlFrame :=
  { kind := .block
    paramArity := 0
    resultArity := 0
    body := allocOuterBody
    continuation := allocCommitTail
    belowStack := [] }

/-- The exported body's frame while the allocator runs. -/
def entryCallFrame : CallFrame :=
  { locals := ⟨[], [.i32 0], []⟩
    continuation := DriverProof.afterAllocBody
    resultArity := 0
    callerRemainder := []
    control := [DriverProof.outerFrame]
    returningInstance := ⟨0⟩ }

/-- The allocator immediately after `memory.size` has pushed the physical page
count `17`, with `requiredPages = 17` below it. -/
def afterSizeExpr : Expr Universal.State := .running
  { locals := ⟨[.i32 1, .i32 allocatedFinish], [.i32 heapBase, .i32 17],
      [.i32 17, .i32 17]⟩
    code := allocGrowthTail
    resultArity := 1
    callerRemainder := []
    control := [allocInnerFrame, allocOuterFrame]
    calls := [entryCallFrame] }

def afterSizeConfig (b : UInt8) : Config Universal.State :=
  { expr := afterSizeExpr
    store := entryStore b }

private abbrev entryMemory : Mem :=
  (Project.ByteEcho.module.initialStore : Store Universal.State).mem

private theorem entryStore_module (b : UInt8) :
    (entryStore b).runtime.currentModule = Project.ByteEcho.module := rfl

private theorem entryStore_mem (b : UInt8) :
    (entryStore b).wasm.mem = entryMemory := rfl

private theorem entryMemory_pages : entryMemory.pages = 17 := by
  decide +kernel

private theorem entryMemory_cursor :
    entryMemory.read32 ((0 : UInt32) + 1048576) = 0 := by
  decide +kernel

/-- The store-preserving prefix, as an explicit trace of authoritative steps:
the wrapper's no-op pre-allocation hook, the allocator's arithmetic guards and
cursor read, and its `memory.size` probe.  No step writes the store, so the
input byte is never inspected. -/
theorem prefix_steps (b : UInt8) :
    ∃ trace, Steps (entryConfig b) trace (afterSizeConfig b) := by
  apply Exists.intro
  simp only [entryConfig, afterSizeConfig, Project.ByteEcho.func0]
  -- `call 4`: the pre-allocation hook, whose body is `return`
  apply Steps.cons (Step.call (functionIndex := 4)
    (fn := Project.ByteEcho.func1Def)
    (by rw [entryStore_module]; decide) (by rw [entryStore_module]; rfl))
  simp only [Project.ByteEcho.func1Def, Project.ByteEcho.func1,
    Function.toLocals, Function.numParams]
  apply Steps.cons (Step.returnFromCallExplicit rfl)
  simp only [resumeCaller]
  -- `block`, then `call 5` with size 1 and alignment 1
  apply Steps.cons Step.block
  wasm_steps [Step.const, Step.const]
  apply Steps.cons (Step.call (functionIndex := 5)
    (fn := Project.ByteEcho.func2Def)
    (by rw [entryStore_module]; decide) (by rw [entryStore_module]; rfl))
  simp only [Project.ByteEcho.func2Def, Project.ByteEcho.func2,
    Function.toLocals, Function.numParams]
  wasm_steps [Step.block, Step.block]
  -- `align - 1`
  wasm_steps [Step.localGet rfl, Step.const, Step.add, Step.localTee rfl]
  -- read the cursor
  apply Steps.cons Step.const
  apply Steps.cons (Step.load32 (memoryAddress?_i32_eq 0) (by
    rw [entryStore_mem, entryMemory_pages]; decide))
  rw [entryStore_mem, entryMemory_cursor]
  wasm_steps [Step.localTee rfl, Step.const, Step.localGet rfl,
    Step.select (selected := .i32 1048592) (by decide), Step.add,
    Step.localTee rfl]
  -- overflow guard on the aligned cursor
  wasm_steps [Step.localGet rfl, Step.ltU (result := 0) (by decide),
    Step.brIfZero]
  -- align down
  wasm_steps [Step.localGet rfl, Step.const, Step.localGet rfl, Step.sub,
    Step.and, Step.localTee rfl]
  -- `finish = base + size` and its overflow guard
  wasm_steps [Step.localGet rfl, Step.add, Step.localTee rfl,
    Step.localGet rfl, Step.ltU (result := 0) (by decide), Step.brIfZero]
  -- signed guard
  wasm_steps [Step.localGet rfl, Step.const,
    Step.ltS (result := 0) (by decide), Step.brIfZero]
  -- required pages, then `memory.size`
  wasm_steps [Step.localGet rfl, Step.const, Step.add, Step.const,
    Step.shrU, Step.localTee rfl, Step.memorySize]
  rw [entryStore_module, entryStore_mem, entryMemory_pages]
  exact Steps.refl _

@[local simp] theorem afterSizeConfig_entry (b : UInt8) :
    (afterSizeConfig b).store.runtime.entry = ⟨0⟩ := by rfl

@[local simp] theorem afterSizeConfig_entry_id (b : UInt8) :
    (afterSizeConfig b).store.runtime.entry.id = 0 := by rfl

@[local simp] theorem afterSizeConfig_currentModule (b : UInt8) :
    (afterSizeConfig b).store.runtime.currentModule =
      Project.ByteEcho.module := by rfl

@[local simp] theorem afterSizeConfig_currentHost (b : UInt8) :
    (afterSizeConfig b).store.runtime.currentHost =
      Universal.envFor Project.ByteEcho.module := by rfl

@[local simp] theorem afterSizeConfig_host (b : UInt8) :
    (afterSizeConfig b).store.wasm.host = Universal.State.ofInput [b] := by rfl

/-! ## Physical resources at the split point -/

private def entryCursorBytes : List UInt8 :=
  physicalBytes entryMemory allocatorCursor 4

private def entryAllocatedBytes : List UInt8 :=
  physicalBytes entryMemory heapBase 1

private abbrev entryCursorHeap : WasmHeapMap (Option UInt8) :=
  insertFreshBytes ∅ allocatorCursor entryCursorBytes

private abbrev entryHeap : WasmHeapMap (Option UInt8) :=
  insertFreshBytes entryCursorHeap heapBase entryAllocatedBytes

private def entryGlobals : WasmGlobalMap Value := ∅

@[simp] private theorem entryCursorBytes_length : entryCursorBytes.length = 4 := by
  simp [entryCursorBytes]

@[simp] private theorem entryAllocatedBytes_length :
    entryAllocatedBytes.length = 1 := by
  simp [entryAllocatedBytes]

private theorem entryBytes_values :
    entryCursorBytes = [0, 0, 0, 0] ∧ entryAllocatedBytes = [0] := by
  decide +kernel

private theorem empty_below_cursor :
    HeapBelow (∅ : WasmHeapMap (Option UInt8)) allocatorCursor.toNat := by
  intro key value hget
  rw [get?_empty] at hget
  contradiction

private theorem cursorHeap_below_heapBase :
    HeapBelow entryCursorHeap heapBase.toNat := by
  have h := HeapBelow.insertFreshBytes
    (bytes := entryCursorBytes) empty_below_cursor (by
      rw [entryCursorBytes_length]
      decide)
  rw [entryCursorBytes_length] at h
  exact h.mono (by decide)

private theorem entryHeap_facts (b : UInt8) :
    heapAgreesWithMem entryHeap (storeResolve (afterSizeConfig b).store) ∧
      heapAddressesInBounds entryHeap
        (storeResolve (afterSizeConfig b).store) := by
  have hcursor := insertFreshPhysicalBytes_facts
    (∅ : WasmHeapMap (Option UInt8))
    (storeResolve (afterSizeConfig b).store) entryMemory allocatorCursor 4
    (by rfl) (heapAgreesWithMem_empty _) (heapAddressesInBounds_empty _)
    (by decide) (by decide)
  exact insertFreshPhysicalBytes_facts entryCursorHeap
    (storeResolve (afterSizeConfig b).store) entryMemory heapBase 1
    (by rfl) hcursor.1 hcursor.2 (by decide) (by decide)

private theorem entryGlobals_agree (b : UInt8) :
    globalHeapAgrees entryGlobals (afterSizeConfig b).store.wasm.globals := by
  intro index value hget
  unfold entryGlobals at hget
  rw [get?_empty] at hget
  contradiction

private theorem entryHost_eq (b : UInt8) :
    Universal.State.ofInput [b] =
      ({ stdio := { input := [b], output := [] }
         random := default
         oom := { raised := false } } : Universal.State) := by
  rfl

private theorem Streams_public [WasmSmallStepGS hlc Universal.State]
    (input output : List UInt8) (raised : Bool) :
    Streams input output raised -∗
      ∀ (store : MachineStore Universal.State) (observations : List StepKind),
        stateInterp (GF := WasmHeapGF Universal.State) store 0 observations 0 -∗
        ⌜store.wasm.host.stdio.output = output ∧
          store.wasm.host.oom.raised = raised⌝ := by
  iintro Hstreams
  iunfold Streams at Hstreams
  iunfold Project.Mergesort.Representations.Streams at Hstreams
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

private theorem initialResources [WasmSmallStepGS hlc Universal.State]
    (b : UInt8) :
    (([∗map] address ↦ value ∈ entryHeap,
        pointsTo (GF := WasmHeapGF Universal.State) (H := WasmHeapMap)
          address (DFrac.own 1) value) ∗
      runtimeModuleOwn ⟨0⟩ Project.ByteEcho.module ∗
      hostEnvOwn 0 (Universal.envFor Project.ByteEcho.module) ∗
      hostStateOwn (Universal.State.ofInput [b])) ⊢
      RuntimeContext ∗
      pointsTo_u32 0 allocatorCursor 0 ∗
      Project.ByteEcho.Contracts.ByteSlice heapBase [0] ∗
      Streams [b] [] false := by
  iintro ⟨Hheap, Hmodule, Henv, Hhost⟩
  ihave HallocatedSplit := insertFreshBytes_bigSep_pointsToBytes
    entryCursorHeap heapBase entryAllocatedBytes cursorHeap_below_heapBase
      (by rw [entryAllocatedBytes_length]; decide) $$ Hheap
  icases HallocatedSplit with ⟨Hallocated, HcursorHeap⟩
  ihave HcursorSplit := insertFreshBytes_bigSep_pointsToBytes
    (∅ : WasmHeapMap (Option UInt8)) allocatorCursor entryCursorBytes
      empty_below_cursor
      (by rw [entryCursorBytes_length]; decide) $$ HcursorHeap
  icases HcursorSplit with ⟨HcursorBytes, _Hempty⟩
  ihave Hcursor : pointsTo_u32 0 allocatorCursor 0 $$ [HcursorBytes]
  · iapply (pointsTo_u32_as_bytes 0 allocatorCursor 0).mpr
    have hbytes : [u32Byte 0 0, u32Byte 0 1, u32Byte 0 2,
        u32Byte 0 3] = [0, 0, 0, 0] := by decide
    rw [hbytes, ← entryBytes_values.1]
    iexact HcursorBytes
  ihave Hstreams : Streams [b] [] false $$ [Hhost]
  · unfold Streams Project.Mergesort.Representations.Streams
    iexists default
    rw [← entryHost_eq b]
    iexact Hhost
  isplitl [Hmodule Henv]
  · unfold RuntimeContext
    iframe Hmodule Henv
  isplitl [Hcursor]
  · iexact Hcursor
  isplitl [Hallocated]
  · unfold Project.ByteEcho.Contracts.ByteSlice
      Project.Mergesort.Representations.ByteSlice
    isplitr
    · ipureintro; decide
    · rw [← entryBytes_values.2]
      iexact Hallocated
  · iexact Hstreams

def entryPost (b : UInt8) (outcome : ObservableOutcome)
    (store : MachineStore Universal.State) : Prop :=
  outcome = .done [] ∧ store.wasm.host.stdio.output = [b]

private abbrev irisEntryPost [WasmSmallStepGS hlc Universal.State]
    (b : UInt8) : ObservableOutcome → HeapIProp :=
  fun outcome => iprop(∀ (store : MachineStore Universal.State)
      (observations : List StepKind),
    stateInterp (GF := WasmHeapGF Universal.State) store 0 observations 0 -∗
      ⌜entryPost b outcome store⌝)

/-- Total WP from the split point: the allocator sees enough pages, commits
its cursor, returns `heapBase`, and the driver suffix takes over. -/
private theorem twp_afterSize [WasmSmallStepGS hlc Universal.State]
    (b : UInt8) : iprop(
      RuntimeContext ∗
      pointsTo_u32 0 allocatorCursor 0 ∗
      Project.ByteEcho.Contracts.ByteSlice heapBase [0] ∗
      Streams [b] [] false) ⊢
      WP (afterSizeConfig b).expr @ Stuckness.NotStuck; ⊤
        [{ irisEntryPost b }] := by
  iintro ⟨Hruntime, Hcursor, Hallocated, Hstreams⟩
  isimp only [RuntimeContext] at Hruntime
  icases Hruntime with ⟨Hmodule, Henv⟩
  simp only [afterSizeConfig, afterSizeExpr, allocGrowthTail]
  iapply twp_localTee rfl
  simp only [List.set]
  iapply twp_leU (result := 1) (by decide)
  iapply twp_brIf (by decide) (by rfl)
  simp only [allocOuterFrame, allocCommitTail, List.take_zero,
    List.nil_append]
  iapply twp_const
  iapply twp_localGet rfl
  ihave HcursorAt : pointsTo_u32 0 ((0 : UInt32) + allocatorCursor) 0 $$
      [Hcursor]
  · rw [UInt32.zero_add]
    iexact Hcursor
  iapply twp_store32 (address := 0) (offset := allocatorCursor)
      (value := allocatedFinish) 0
      (by decide) (by decide) (by decide) (by decide) $$ HcursorAt
  iintro _Hcursor
  iapply twp_localGet rfl
  simp only [entryCallFrame]
  iapply Wasm.SmallStep.twp_returnFromCallFallthrough $$ Hmodule
  iintro Hmodule
  simp only [List.take_succ_cons, List.take_zero, List.cons_append,
    List.nil_append]
  ihave Hruntime : RuntimeContext $$ [Hmodule Henv]
  · unfold RuntimeContext; iframe Hmodule Henv
  have Hsuffix := Project.ByteEcho.DriverProof.twp_afterAlloc (hlc := hlc)
    (s := .NotStuck) (E := ⊤) (Phi := irisEntryPost b) b 0
  simp only [Project.ByteEcho.DriverProof.afterAllocExpr] at Hsuffix
  iapply Hsuffix
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hallocated]
  · iexact Hallocated
  isplitl [Hstreams]
  · iexact Hstreams
  iintro Hruntime Hstreams
  iintro %store %observations Hstate
  ihave Hfields := Streams_public [] [b] false $$ Hstreams
  ispecialize Hfields $$ %store %observations
  ihave %hfields := Hfields $$ Hstate
  ipureintro
  exact ⟨rfl, hfields.1⟩

theorem afterSize_terminatesWithOutcome (b : UInt8) :
    TerminatesWithOutcome (afterSizeConfig b) (entryPost b) := by
  apply wasm_smallStep_heap_globals_runtime_host_store_terminatesWithOutcome
      (config := afterSizeConfig b) entryHeap entryGlobals (entryPost b)
  · exact (entryHeap_facts b).1
  · exact (entryHeap_facts b).2
  · exact entryGlobals_agree b
  · change 0 < 1
    decide
  · intro hlc gs
    iintro ⟨Hheap, _Hglobals, Hmodule, Henv, Hhost⟩
    ihave Hmodule' : runtimeModuleOwn ⟨0⟩ Project.ByteEcho.module $$ [Hmodule]
    · rw [← afterSizeConfig_entry b, ← afterSizeConfig_currentModule b]
      iexact Hmodule
    ihave Henv' : hostEnvOwn 0 (Universal.envFor Project.ByteEcho.module) $$
        [Henv]
    · rw [← afterSizeConfig_entry_id b, ← afterSizeConfig_currentHost b]
      iexact Henv
    ihave Hhost' : hostStateOwn (Universal.State.ofInput [b]) $$ [Hhost]
    · rw [← afterSizeConfig_host b]
      iexact Hhost
    iapply twp_afterSize b
    iapply initialResources b
    iframe Hheap Hmodule' Henv' Hhost'

theorem entry_terminatesWithOutcome (b : UInt8) :
    TerminatesWithOutcome (entryConfig b) (entryPost b) := by
  obtain ⟨prefixTrace, hprefix⟩ := prefix_steps b
  obtain ⟨trace, outcome, store, hsteps, hpost⟩ :=
    afterSize_terminatesWithOutcome b
  exact ⟨_, outcome, store, hprefix.trans hsteps, hpost⟩

theorem entry_terminates (b : UInt8) :
    TerminatesWith (entryConfig b)
      (fun values store => values = [] ∧
        store.wasm.host.stdio.output = [b]) := by
  obtain ⟨trace, outcome, store, hsteps, hpost⟩ :=
    entry_terminatesWithOutcome b
  rcases hpost with ⟨rfl, houtput⟩
  exact ⟨trace, [], store, hsteps, rfl, houtput⟩

theorem entry_adequacy : Project.ByteEcho.Spec.ByteEchoSpec := by
  rintro ⟨b⟩
  refine ⟨b, ?_, rfl⟩
  unfold Project.ByteEcho.Spec.Runs Project.ByteEcho.Spec.args
    Project.ByteEcho.Spec.result Universal.RunsExport RunsExportWith
  refine ⟨entryConfig b, ?_, entry_terminates b⟩
  rw [startExportConfig?_ofHost_zero byte_echo_zeroArgument]
  exact startConfig_eq b

end Project.ByteEcho.Adequacy
