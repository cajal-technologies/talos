import Project.GcdStdio.DriverProof
import CodeLib.SepLogic.SmallStepOutcomeAdequacy

set_option maxRecDepth 8388608
set_option maxHeartbeats 0

/-!
# Total adequacy for the GCD stream entry point

This file supplies the physical initial resources, verifies the generated
wrapper and its one sixteen-byte zeroed allocation, and then applies the
driver suffix proof.  Total outcome adequacy turns that TWP into the finite
trace required by the fuel-free public specification.
-/

namespace Project.GcdStdio.Adequacy

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.GcdStdio.Contracts
open scoped Wasm.SmallStep.Outcome

private abbrev HeapIProp := IProp (WasmHeapGF Universal.State)

def entryInitialStore (a b : UInt64) : Store Universal.State :=
  { (Project.GcdStdio.module.initialStore : Store Universal.State) with
    host := Universal.State.ofInput (Project.GcdStdio.Spec.encodeInput a b) }

private def entryInstance : ModuleInstance Universal.State :=
  { module := Project.GcdStdio.module
    host := Universal.envFor Project.GcdStdio.module }

def entryConfig (a b : UInt64) : Config Universal.State :=
  { expr := .running
      { locals := {}
        code := Project.GcdStdio.func2
        resultArity := 0
        callerRemainder := [] }
    store :=
      { runtime := { instances := #[entryInstance], entry := ⟨0⟩ }
        wasm := entryInitialStore a b } }

@[simp] theorem entryConfig_entry (a b : UInt64) :
    (entryConfig a b).store.runtime.entry = ⟨0⟩ := by rfl

@[simp] theorem entryConfig_entry_id (a b : UInt64) :
    (entryConfig a b).store.runtime.entry.id = 0 := by rfl

@[simp] theorem entryConfig_currentModule (a b : UInt64) :
    (entryConfig a b).store.runtime.currentModule =
      Project.GcdStdio.module := by rfl

@[simp] theorem entryConfig_currentHost (a b : UInt64) :
    (entryConfig a b).store.runtime.currentHost =
      Universal.envFor Project.GcdStdio.module := by rfl

@[simp] theorem entryConfig_host (a b : UInt64) :
    (entryConfig a b).store.wasm.host =
      Universal.State.ofInput (Project.GcdStdio.Spec.encodeInput a b) := by rfl

theorem startConfig_eq (a b : UInt64) :
    startConfig? (Universal.envFor Project.GcdStdio.module)
      Project.GcdStdio.module "gcd"
      (Universal.State.ofInput (Project.GcdStdio.Spec.encodeInput a b)) =
      some (entryConfig a b) := by
  rfl

private abbrev entryMemory : Mem :=
  (Project.GcdStdio.module.initialStore : Store Universal.State).mem

private def entryStackBytes : List UInt8 :=
  physicalBytes entryMemory entryStackLow 16

private def entryCursorBytes : List UInt8 :=
  physicalBytes entryMemory allocatorCursor 4

private def entryAllocatedBytes : List UInt8 :=
  physicalBytes entryMemory heapBase 16

private abbrev entryStackHeap : WasmHeapMap (Option UInt8) :=
  insertFreshBytes ∅ entryStackLow entryStackBytes

private abbrev entryCursorHeap : WasmHeapMap (Option UInt8) :=
  insertFreshBytes entryStackHeap allocatorCursor entryCursorBytes

private abbrev entryHeap : WasmHeapMap (Option UInt8) :=
  insertFreshBytes entryCursorHeap heapBase entryAllocatedBytes

private def entryGlobals : WasmGlobalMap Value :=
  insert ∅ (⟨0, 0⟩ : GlobalKey) (.i32 entryStackTop)

@[simp] private theorem entryStackBytes_length : entryStackBytes.length = 16 := by
  simp [entryStackBytes]

@[simp] private theorem entryCursorBytes_length : entryCursorBytes.length = 4 := by
  simp [entryCursorBytes]

@[simp] private theorem entryAllocatedBytes_length :
    entryAllocatedBytes.length = 16 := by
  simp [entryAllocatedBytes]

private theorem entryBytes_values :
    entryStackBytes = List.replicate 16 0 ∧
      entryCursorBytes = [0, 0, 0, 0] ∧
      entryAllocatedBytes = List.replicate 16 0 := by
  native_decide

private theorem empty_below_stack :
    HeapBelow (∅ : WasmHeapMap (Option UInt8)) entryStackLow.toNat := by
  intro key value hget
  rw [get?_empty] at hget
  contradiction

private theorem stackHeap_below_cursor :
    HeapBelow entryStackHeap allocatorCursor.toNat := by
  have h := HeapBelow.insertFreshBytes
    (bytes := entryStackBytes) empty_below_stack (by
      rw [entryStackBytes_length]
      decide)
  rw [entryStackBytes_length] at h
  exact h.mono (by decide)

private theorem cursorHeap_below_heapBase :
    HeapBelow entryCursorHeap heapBase.toNat := by
  have h := HeapBelow.insertFreshBytes
    (bytes := entryCursorBytes) stackHeap_below_cursor (by
      rw [entryCursorBytes_length]
      decide)
  rw [entryCursorBytes_length] at h
  exact h.mono (by decide)

private theorem entryHeap_facts (a b : UInt64) :
    heapAgreesWithMem entryHeap (storeResolve (entryConfig a b).store) ∧
      heapAddressesInBounds entryHeap
        (storeResolve (entryConfig a b).store) := by
  have hstack := insertFreshPhysicalBytes_facts
    (∅ : WasmHeapMap (Option UInt8))
    (storeResolve (entryConfig a b).store) entryMemory entryStackLow 16
    (by rfl) (heapAgreesWithMem_empty _) (heapAddressesInBounds_empty _)
    (by decide) (by decide)
  have hcursor := insertFreshPhysicalBytes_facts entryStackHeap
    (storeResolve (entryConfig a b).store) entryMemory allocatorCursor 4
    (by rfl) hstack.1 hstack.2 (by decide) (by decide)
  exact insertFreshPhysicalBytes_facts entryCursorHeap
    (storeResolve (entryConfig a b).store) entryMemory heapBase 16
    (by rfl) hcursor.1 hcursor.2 (by decide) (by decide)

private theorem entryGlobals_agree (a b : UInt64) :
    globalHeapAgrees entryGlobals (entryConfig a b).store.wasm.globals := by
  intro index value hget
  unfold entryGlobals at hget
  by_cases hindex : index = 0
  · subst index
    simp only [get?_insert_eq rfl] at hget
    obtain rfl := Option.some.inj hget
    rfl
  · rw [get?_insert_ne (fun h => hindex (congrArg GlobalKey.index h).symm),
      get?_empty] at hget
    contradiction

private theorem entryGlobals_pointsTo [WasmGlobalGS Universal.State] :
    ([∗map] index ↦ value ∈ entryGlobals,
      globalPointsTo index value) ⊢ StackPointer entryStackTop := by
  unfold entryGlobals StackPointer
  rw [(BI.BigSepM.bigSepM_insert
      (get?_empty (⟨0, 0⟩ : GlobalKey))).to_eq,
    BI.BigSepM.bigSepM_empty.to_eq, BI.sep_emp.to_eq,
    globalPointsToAt_eq]

private theorem entryHost_eq (a b : UInt64) :
    Universal.State.ofInput (Project.GcdStdio.Spec.encodeInput a b) =
      ({ stdio :=
          { input := Project.GcdStdio.Spec.encodeInput a b, output := [] }
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
    (a b : UInt64) :
    (([∗map] address ↦ value ∈ entryHeap,
        pointsTo (GF := WasmHeapGF Universal.State) (H := WasmHeapMap)
          address (DFrac.own 1) value) ∗
      ([∗map] index ↦ value ∈ entryGlobals,
        globalPointsTo index value) ∗
      runtimeModuleOwn ⟨0⟩ Project.GcdStdio.module ∗
      hostEnvOwn 0 (Universal.envFor Project.GcdStdio.module) ∗
      hostStateOwn
        (Universal.State.ofInput (Project.GcdStdio.Spec.encodeInput a b))) ⊢
      RuntimeContext ∗ StackPointer entryStackTop ∗
      Project.GcdStdio.Contracts.ByteSlice entryStackLow
        (List.replicate 16 0) ∗
      pointsTo_u32 0 allocatorCursor 0 ∗
      Project.GcdStdio.Contracts.ByteSlice heapBase
        (List.replicate 16 0) ∗
      Streams (Project.GcdStdio.Spec.encodeInput a b) [] false := by
  iintro ⟨Hheap, Hglobals, Hmodule, Henv, Hhost⟩
  ihave HallocatedSplit := insertFreshBytes_bigSep_pointsToBytes
    entryCursorHeap heapBase entryAllocatedBytes cursorHeap_below_heapBase
      (by rw [entryAllocatedBytes_length]; decide) $$ Hheap
  icases HallocatedSplit with ⟨Hallocated, HcursorHeap⟩
  ihave HcursorSplit := insertFreshBytes_bigSep_pointsToBytes
    entryStackHeap allocatorCursor entryCursorBytes stackHeap_below_cursor
      (by rw [entryCursorBytes_length]; decide) $$ HcursorHeap
  icases HcursorSplit with ⟨HcursorBytes, HstackHeap⟩
  ihave HstackSplit := insertFreshBytes_bigSep_pointsToBytes
    (∅ : WasmHeapMap (Option UInt8)) entryStackLow entryStackBytes
      empty_below_stack (by rw [entryStackBytes_length]; decide) $$ HstackHeap
  icases HstackSplit with ⟨Hstack, _Hempty⟩
  ihave Hcursor : pointsTo_u32 0 allocatorCursor 0 $$ [HcursorBytes]
  · iapply (pointsTo_u32_as_bytes 0 allocatorCursor 0).mpr
    have hbytes : [u32Byte 0 0, u32Byte 0 1, u32Byte 0 2,
        u32Byte 0 3] = [0, 0, 0, 0] := by decide
    rw [hbytes, ← entryBytes_values.2.1]
    iexact HcursorBytes
  ihave Hsp := entryGlobals_pointsTo $$ Hglobals
  ihave Hstreams : Streams (Project.GcdStdio.Spec.encodeInput a b) [] false $$
      [Hhost]
  · unfold Streams Project.Mergesort.Representations.Streams
    iexists default
    rw [← entryHost_eq a b]
    iexact Hhost
  isplitl [Hmodule Henv]
  · unfold RuntimeContext
    iframe Hmodule Henv
  isplitl [Hsp]
  · iexact Hsp
  isplitl [Hstack]
  · unfold Project.GcdStdio.Contracts.ByteSlice
      Project.Mergesort.Representations.ByteSlice
    isplitr
    · ipureintro; decide
    · rw [← entryBytes_values.1]
      iexact Hstack
  isplitl [Hcursor]
  · iexact Hcursor
  isplitl [Hallocated]
  · unfold Project.GcdStdio.Contracts.ByteSlice
      Project.Mergesort.Representations.ByteSlice
    isplitr
    · ipureintro; decide
    · rw [← entryBytes_values.2.2]
      iexact Hallocated
  · iexact Hstreams

private theorem func0_index :
    Project.GcdStdio.module.funcs[0]? = some Project.GcdStdio.func0Def := by rfl

private theorem func3_index :
    Project.GcdStdio.module.funcs[3]? = some Project.GcdStdio.func3Def := by rfl

private theorem func6_index :
    Project.GcdStdio.module.funcs[6]? = some Project.GcdStdio.func6Def := by rfl

def entryPost (a b : UInt64) (outcome : ObservableOutcome)
    (store : MachineStore Universal.State) : Prop :=
  outcome = .done [] ∧
    store.wasm.host.stdio.output =
      Project.GcdStdio.Spec.encodeOutput
        (UInt64.ofNat (Nat.gcd a.toNat b.toNat))

private abbrev irisEntryPost [WasmSmallStepGS hlc Universal.State]
    (a b : UInt64) : ObservableOutcome → HeapIProp :=
  fun outcome => iprop(∀ (store : MachineStore Universal.State)
      (observations : List StepKind),
    stateInterp (GF := WasmHeapGF Universal.State) store 0 observations 0 -∗
      ⌜entryPost a b outcome store⌝)

private theorem twp_ltS [WasmSmallStepGS hlc Universal.State]
    {params localValues values : List Value}
    {lhs rhs result : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Phi : ObservableOutcome → HeapIProp}
    (hresult : result = if lhs.toInt32 < rhs.toInt32 then 1 else 0) :
    WP (.running
      ⟨⟨params, localValues, .i32 result :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr Universal.State)
        @ s; E [{ Phi }] ⊢
    WP (.running
      ⟨⟨params, localValues, .i32 rhs :: .i32 lhs :: values⟩,
        .ltS :: code, arity, remainder, controls, calls⟩ :
          Expr Universal.State) @ s; E [{ Phi }] :=
  twp_pureStep _ _ _ (fun _ => Step.ltS hresult)

/-- Total WP for the direct exported body, including its exact allocator call. -/
private theorem twp_entry [WasmSmallStepGS hlc Universal.State]
    (a b : UInt64) : iprop(
      RuntimeContext ∗ StackPointer entryStackTop ∗
      Project.GcdStdio.Contracts.ByteSlice entryStackLow
        (List.replicate 16 0) ∗
      pointsTo_u32 0 allocatorCursor 0 ∗
      Project.GcdStdio.Contracts.ByteSlice heapBase
        (List.replicate 16 0) ∗
      Streams (Project.GcdStdio.Spec.encodeInput a b) [] false) ⊢
      WP (entryConfig a b).expr @ Stuckness.NotStuck; ⊤
        [{ irisEntryPost a b }] := by
  iintro ⟨Hruntime, Hsp, Hstack, Hcursor, Hallocated, Hstreams⟩
  isimp only [RuntimeContext] at Hruntime
  icases Hruntime with ⟨Hmodule, Henv⟩
  simp only [entryConfig, Project.GcdStdio.func2]
  iapply Wasm.SmallStep.twp_call Project.GcdStdio.module 3
      Project.GcdStdio.func0Def (by decide) func0_index $$ Hmodule
  iintro Hmodule
  simp [Project.GcdStdio.func0Def, Project.GcdStdio.func0,
    Function.toLocals, Function.numParams]
  isimp only [StackPointer] at Hsp
  iapply twp_globalGet $$ Hsp
  iintro Hsp
  iapply twp_const
  iapply twp_sub
  rw [show entryStackTop - 16 = entryStackLow by decide]
  iapply twp_localTee rfl
  simp only [List.length_nil, Nat.reduceSub, List.set]
  iapply twp_globalSet $$ Hsp
  iintro Hsp
  iapply Wasm.SmallStep.twp_call Project.GcdStdio.module 6
      Project.GcdStdio.func3Def (by decide) func3_index $$ Hmodule
  iintro Hmodule
  simp [Project.GcdStdio.func3Def, Project.GcdStdio.func3,
    Function.toLocals, Function.numParams]
  iapply Wasm.SmallStep.twp_returnFromCallExplicit $$ Hmodule
  iintro Hmodule
  iapply twp_block
  iapply twp_const
  iapply twp_const
  iapply Wasm.SmallStep.twp_call Project.GcdStdio.module 9
      Project.GcdStdio.func6Def (by decide) func6_index $$ Hmodule
  iintro Hmodule
  simp [Project.GcdStdio.func6Def, Project.GcdStdio.func6,
    Function.toLocals, Function.numParams]
  iapply twp_block
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  norm_num
  iapply twp_localTee rfl
  simp only [List.length]
  iapply twp_const
  ihave HcursorAt : pointsTo_u32 0 ((0 : UInt32) + 1048576) 0 $$ [Hcursor]
  · rw [show (0 : UInt32) + 1048576 = allocatorCursor by decide]
    iexact Hcursor
  iapply twp_load32 (address := 0) (offset := 1048576) 0
      (by decide) (by decide) (by decide) (by decide) $$ HcursorAt
  iintro Hcursor
  iapply twp_localTee rfl
  simp only [List.length]
  iapply twp_const
  iapply twp_localGet rfl
  iapply twp_select (selected := .i32 heapBase) (by decide)
  iapply twp_add
  rw [show heapBase + ((4294967295 : UInt32) + 1) = heapBase by decide]
  iapply twp_localTee rfl
  simp only [List.length]
  iapply twp_localGet rfl
  iapply twp_ltU (result := 0) (by decide)
  iapply twp_brIfZero
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_localGet rfl
  iapply twp_sub
  rw [show (0 : UInt32) - 1 = 4294967295 by decide]
  iapply twp_and
  rw [show heapBase &&& (4294967295 : UInt32) = heapBase by decide]
  iapply twp_localTee rfl
  simp only [List.set]
  iapply twp_localGet rfl
  iapply twp_add
  rw [show (16 : UInt32) + heapBase = allocatedFinish by decide]
  iapply twp_localTee rfl
  simp only [List.length]
  iapply twp_localGet rfl
  iapply twp_ltU (result := 0) (by decide)
  iapply twp_brIfZero
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_ltS (result := 0) (by decide)
  iapply twp_brIfZero
  iapply twp_const
  iapply twp_localGet rfl
  iapply twp_store32 (address := 0) (offset := 1048576)
      (value := allocatedFinish) 0
      (by decide) (by decide) (by decide) (by decide) $$ Hcursor
  iintro Hcursor
  ihave Hcursor' : pointsTo_u32 0 allocatorCursor allocatedFinish $$ [Hcursor]
  · rw [← show (0 : UInt32) + 1048576 = allocatorCursor by decide]
    iexact Hcursor
  iapply twp_block
  iapply twp_localGet rfl
  iapply twp_eqz (result := 0) (by decide)
  iapply twp_brIfZero
  iapply twp_localGet rfl
  iapply twp_eqz (result := 0) (by decide)
  iapply twp_brIfZero
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_localGet rfl
  isimp only [Project.GcdStdio.Contracts.ByteSlice,
    Project.Mergesort.Representations.ByteSlice] at Hallocated
  icases Hallocated with ⟨%hnowrap, Hbytes⟩
  have hzeros : List.replicate 16 (0 : UInt8) =
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide
  ihave HbytesRep : pointsToBytes 0 heapBase (List.replicate 16 0) $$ [Hbytes]
  · rw [hzeros]
    iexact Hbytes
  iapply twp_memoryFill32 (destination := heapBase) (len := 16) (value := 0)
      (List.replicate 16 0)
      (by simp) (by decide) (by simpa using hnowrap) $$ HbytesRep
  iintro Hbytes
  have hzeroByte : (0 : UInt32).toUInt8 = (0 : UInt8) := by decide
  isimp only [List.length_replicate, hzeroByte] at Hbytes
  ihave Hallocated : Project.GcdStdio.Contracts.ByteSlice heapBase
      (List.replicate 16 0) $$ [Hbytes]
  · unfold Project.GcdStdio.Contracts.ByteSlice
      Project.Mergesort.Representations.ByteSlice
    isplitl []
    · ipureintro; exact hnowrap
    · iexact Hbytes
  iapply twp_exitControl (by rfl)
  simp only [List.take_zero, List.nil_append]
  iapply twp_localGet rfl
  iapply Wasm.SmallStep.twp_returnFromCallExplicit $$ Hmodule
  iintro Hmodule
  simp only [List.take_succ_cons, List.take_zero, List.cons_append,
    List.nil_append]
  iapply twp_localTee rfl
  simp only [List.length, List.set]
  iapply twp_eqz (result := 0) (by decide)
  iapply twp_brIfZero
  iapply twp_block
  iapply twp_block
  simp only [List.drop_zero]
  ihave Hruntime : RuntimeContext $$ [Hmodule Henv]
  · unfold RuntimeContext; iframe Hmodule Henv
  have Hsuffix := Project.GcdStdio.DriverProof.twp_afterAlloc (hlc := hlc)
    (s := .NotStuck) (E := ⊤) (Phi := irisEntryPost a b) a b
  simp [Project.GcdStdio.DriverProof.afterAllocExpr,
    Project.GcdStdio.DriverProof.successBody,
    Project.GcdStdio.DriverProof.fallbackBody,
    Project.GcdStdio.DriverProof.restoreBody,
    Project.GcdStdio.DriverProof.oomBody,
    Project.GcdStdio.DriverProof.middleBody,
    Project.GcdStdio.DriverProof.outerBody,
    Project.GcdStdio.DriverProof.innerFrame,
    Project.GcdStdio.DriverProof.middleFrame,
    Project.GcdStdio.DriverProof.outerFrame,
    Project.GcdStdio.DriverProof.wrapperFrame] at Hsuffix
  iapply Hsuffix
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hsp]
  · isimp only [Project.GcdStdio.Contracts.StackPointer]
    iexact Hsp
  isplitl [Hstack]
  · iexact Hstack
  isplitl [Hcursor']
  · iexact Hcursor'
  isplitl [Hallocated]
  · rw [← hzeros]
    iexact Hallocated
  isplitl [Hstreams]
  · iexact Hstreams
  iintro Hruntime Hstreams
  iintro %store %observations Hstate
  ihave Hfields := Streams_public []
      (Project.GcdStdio.Spec.encodeOutput
        (UInt64.ofNat (Nat.gcd a.toNat b.toNat))) false $$ Hstreams
  ispecialize Hfields $$ %store %observations
  ihave %hfields := Hfields $$ Hstate
  ipureintro
  exact ⟨rfl, hfields.1⟩

theorem entry_terminatesWithOutcome (a b : UInt64) :
    TerminatesWithOutcome (entryConfig a b) (entryPost a b) := by
  apply wasm_smallStep_heap_globals_runtime_host_store_terminatesWithOutcome
      (config := entryConfig a b) entryHeap entryGlobals (entryPost a b)
  · exact (entryHeap_facts a b).1
  · exact (entryHeap_facts a b).2
  · exact entryGlobals_agree a b
  · change 0 < 1
    decide
  · intro hlc gs
    iintro ⟨Hheap, Hglobals, Hmodule, Henv, Hhost⟩
    ihave Hmodule' : runtimeModuleOwn ⟨0⟩ Project.GcdStdio.module $$ [Hmodule]
    · rw [← entryConfig_entry a b, ← entryConfig_currentModule a b]
      iexact Hmodule
    ihave Henv' : hostEnvOwn 0 (Universal.envFor Project.GcdStdio.module) $$
        [Henv]
    · rw [← entryConfig_entry_id a b, ← entryConfig_currentHost a b]
      iexact Henv
    ihave Hhost' : hostStateOwn
        (Universal.State.ofInput (Project.GcdStdio.Spec.encodeInput a b)) $$
        [Hhost]
    · rw [← entryConfig_host a b]
      iexact Hhost
    iapply twp_entry a b
    iapply initialResources a b
    iframe Hheap Hglobals Hmodule' Henv' Hhost'

theorem entry_terminates (a b : UInt64) :
    TerminatesWith (entryConfig a b)
      (fun values store => values = [] ∧
        store.wasm.host.stdio.output =
          Project.GcdStdio.Spec.encodeOutput
            (UInt64.ofNat (Nat.gcd a.toNat b.toNat))) := by
  obtain ⟨trace, outcome, store, hsteps, hpost⟩ :=
    entry_terminatesWithOutcome a b
  rcases hpost with ⟨rfl, houtput⟩
  exact ⟨trace, [], store, hsteps, rfl, houtput⟩

theorem entry_adequacy :
    Project.GcdStdio.Spec.PublicEntrySpecification := by
  intro a b
  unfold Project.GcdStdio.Spec.RunsBytes Universal.RunsBytes Universal.Runs
    RunsWith
  exact ⟨entryConfig a b, startConfig_eq a b, entry_terminates a b⟩

end Project.GcdStdio.Adequacy
