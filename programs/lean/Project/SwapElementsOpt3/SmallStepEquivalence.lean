import CodeLib.Equivalence
import Project.SwapElements.Address
import Project.SwapElements.SwapSepLogic
import Project.SwapElementsOpt3.Program

/-!
# Authoritative small-step equivalence smoke test

This compares the real unoptimized exported call chain with the optimized
inlined export.  The observation deliberately contains the caller-visible
two-word array and excludes the unoptimized implementation's private scratch
traffic.
-/

namespace Project.SwapElementsOpt3.SmallStepEquivalence

open Iris Iris.ProgramLogic Language.Notation Std
open Wasm
open Wasm.SepLogic

set_option maxHeartbeats 4000000 in
/-- Universal Iris rule for the optimized inlined export on distinct element
addresses. Both bounds checks, both address calculations, and both physical
loads/stores execute through the authoritative small-step semantics. -/
theorem opt3_func0_distinct_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    (ptr len i j : UInt32) (oldA oldB : UInt64)
    (hi : i < len) (hj : j < len)
    (hroomI : ((i <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296)
    (hroomJ : ((j <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296) :
    let addressI := (i <<< (3 % 32)) + ptr
    let addressJ := (j <<< (3 % 32)) + ptr
    pointsTo_u64 addressI oldA ∗ pointsTo_u64 addressJ oldB ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 ptr, .i32 len, .i32 i, .i32 j], [.i64 0], []⟩,
        Project.SwapElementsOpt3.func0, 0, [], [], []⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E
      {{ values, ⌜values = []⌝ ∗
        pointsTo_u64 addressI oldB ∗ pointsTo_u64 addressJ oldA }} := by
  dsimp only
  let addressI := (i <<< (3 % 32)) + ptr
  let addressJ := (j <<< (3 % 32)) + ptr
  have hroomI' : addressI.toNat + 8 ≤ 4294967296 := by
    simpa [addressI] using hroomI
  have hroomJ' : addressJ.toNat + 8 ≤ 4294967296 := by
    simpa [addressJ] using hroomJ
  have hi1 : (addressI + 1).toNat = addressI.toNat + 1 := by
    simpa using UInt32.add_ofNat_toNat_noWrap addressI 1 (by omega) (by omega)
  have hi2 : (addressI + 2).toNat = addressI.toNat + 2 := by
    simpa using UInt32.add_ofNat_toNat_noWrap addressI 2 (by omega) (by omega)
  have hi3 : (addressI + 3).toNat = addressI.toNat + 3 := by
    simpa using UInt32.add_ofNat_toNat_noWrap addressI 3 (by omega) (by omega)
  have hi4 : (addressI + 4).toNat = addressI.toNat + 4 := by
    simpa using UInt32.add_ofNat_toNat_noWrap addressI 4 (by omega) (by omega)
  have hi5 : (addressI + 5).toNat = addressI.toNat + 5 := by
    simpa using UInt32.add_ofNat_toNat_noWrap addressI 5 (by omega) (by omega)
  have hi6 : (addressI + 6).toNat = addressI.toNat + 6 := by
    simpa using UInt32.add_ofNat_toNat_noWrap addressI 6 (by omega) (by omega)
  have hi7 : (addressI + 7).toNat = addressI.toNat + 7 := by
    simpa using UInt32.add_ofNat_toNat_noWrap addressI 7 (by omega) (by omega)
  have hj1 : (addressJ + 1).toNat = addressJ.toNat + 1 := by
    simpa using UInt32.add_ofNat_toNat_noWrap addressJ 1 (by omega) (by omega)
  have hj2 : (addressJ + 2).toNat = addressJ.toNat + 2 := by
    simpa using UInt32.add_ofNat_toNat_noWrap addressJ 2 (by omega) (by omega)
  have hj3 : (addressJ + 3).toNat = addressJ.toNat + 3 := by
    simpa using UInt32.add_ofNat_toNat_noWrap addressJ 3 (by omega) (by omega)
  have hj4 : (addressJ + 4).toNat = addressJ.toNat + 4 := by
    simpa using UInt32.add_ofNat_toNat_noWrap addressJ 4 (by omega) (by omega)
  have hj5 : (addressJ + 5).toNat = addressJ.toNat + 5 := by
    simpa using UInt32.add_ofNat_toNat_noWrap addressJ 5 (by omega) (by omega)
  have hj6 : (addressJ + 6).toNat = addressJ.toNat + 6 := by
    simpa using UInt32.add_ofNat_toNat_noWrap addressJ 6 (by omega) (by omega)
  have hj7 : (addressJ + 7).toNat = addressJ.toNat + 7 := by
    simpa using UInt32.add_ofNat_toNat_noWrap addressJ 7 (by omega) (by omega)
  iintro ⟨HA, HB⟩
  simp only [Project.SwapElementsOpt3.func0]
  iapply Wasm.SmallStep.wp_block
  inext
  iapply Wasm.SmallStep.wp_block
  inext
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_geU (result := 0)
    (by simp [show ¬i ≥ len from not_le_of_gt hi])
  inext
  iapply Wasm.SmallStep.wp_brIfZero
  inext
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_geU (result := 0)
    (by simp [show ¬j ≥ len from not_le_of_gt hj])
  inext
  iapply Wasm.SmallStep.wp_brIfZero
  inext
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_const
  inext
  iapply Wasm.SmallStep.wp_shl
  inext
  iapply Wasm.SmallStep.wp_add
  inext
  iapply Wasm.SmallStep.wp_localSet rfl
  inext
  simp only [List.set]
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  ihave HALater : ▷ pointsTo_u64 (addressI + 0) oldA $$ [HA]
  · inext
    rw [UInt32.add_zero]
    iexact HA
  iapply Wasm.SmallStep.wp_load64 oldA (by simp)
    (by simpa using hi1) (by simpa using hi2) (by simpa using hi3)
    (by simpa using hi4) (by simpa using hi5) (by simpa using hi6)
    (by simpa using hi7) $$ HALater
  inext
  iintro HA
  iapply Wasm.SmallStep.wp_localSet rfl
  inext
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
    List.set]
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_const
  inext
  iapply Wasm.SmallStep.wp_shl
  inext
  iapply Wasm.SmallStep.wp_add
  inext
  iapply Wasm.SmallStep.wp_localSet rfl
  inext
  simp only [List.set]
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  ihave HBLater : ▷ pointsTo_u64 (addressJ + 0) oldB $$ [HB]
  · inext
    rw [UInt32.add_zero]
    iexact HB
  iapply Wasm.SmallStep.wp_load64 oldB (by simp)
    (by simpa using hj1) (by simpa using hj2) (by simpa using hj3)
    (by simpa using hj4) (by simpa using hj5) (by simpa using hj6)
    (by simpa using hj7) $$ HBLater
  inext
  iintro HB
  ihave HALater : ▷ pointsTo_u64 (addressI + 0) oldA $$ [HA]
  · inext
    rw [UInt32.add_zero]
    iexact HA
  iapply Wasm.SmallStep.wp_store64 oldA (by simp)
    (by simpa using hi1) (by simpa using hi2) (by simpa using hi3)
    (by simpa using hi4) (by simpa using hi5) (by simpa using hi6)
    (by simpa using hi7) $$ HALater
  inext
  iintro HA
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  ihave HBLater : ▷ pointsTo_u64 (addressJ + 0) oldB $$ [HB]
  · inext
    rw [UInt32.add_zero]
    iexact HB
  iapply Wasm.SmallStep.wp_store64 oldB (by simp)
    (by simpa using hj1) (by simpa using hj2) (by simpa using hj3)
    (by simpa using hj4) (by simpa using hj5) (by simpa using hj6)
    (by simpa using hj7) $$ HBLater
  inext
  iintro HB
  iapply Wasm.SmallStep.wp_returnFromFunction
  inext
  iapply wp_value'
  isplitr
  · ipureintro
    rfl
  · rw [show (i <<< (3 % 32)) + ptr = addressI by rfl,
      show (j <<< (3 % 32)) + ptr = addressJ by rfl]
    simp only [UInt32.add_zero]
    iframe

/-- Authoritative entry configuration for the optimized export. -/
def opt3ConfigFromStore (wasm : Store Unit)
    (ptr len i j : UInt32) : Wasm.SmallStep.Config Unit :=
  { expr := .running
      ⟨⟨[.i32 ptr, .i32 len, .i32 i, .i32 j], [.i64 0], []⟩,
        Project.SwapElementsOpt3.func0, 0, [], [], []⟩
    store :=
      { runtime := { module := Project.SwapElementsOpt3.module, host := {} }
        wasm := wasm } }

/-- Universal physical-store partial correctness for the optimized export.
The heap footprint owns exactly the two distinct array elements; globals and
all unrelated memory remain framed. -/
theorem opt3_func0_distinct_store_partiallyMeets
    (wasm : Store Unit) (ptr len i j : UInt32)
    (oldA oldB : UInt64)
    (σ : WasmHeapMap (Option UInt8))
    (globalσ : WasmGlobalMap Value)
    (hi : i < len) (hj : j < len)
    (hroomI : ((i <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296)
    (hroomJ : ((j <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296)
    (hagree : heapAgreesWithMem σ wasm.mem)
    (hinBounds : heapAddressesInBounds σ wasm.mem)
    (hglobals : globalHeapAgrees globalσ wasm.globals)
    (hresources : ∀ [WasmHeapGS],
      ([∗map] address ↦ value ∈ σ,
        pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
          address (DFrac.own 1) value) ⊢
      pointsTo_u64 ((i <<< (3 % 32)) + ptr) oldA ∗
      pointsTo_u64 ((j <<< (3 % 32)) + ptr) oldB) :
    Wasm.SmallStep.PartiallyMeets
      (opt3ConfigFromStore wasm ptr len i j)
      (fun values store =>
        values = [] ∧
          store.wasm.mem.read64 ((i <<< (3 % 32)) + ptr) = oldB ∧
          store.wasm.mem.read64 ((j <<< (3 % 32)) + ptr) = oldA) := by
  let addressI := (i <<< (3 % 32)) + ptr
  let addressJ := (j <<< (3 % 32)) + ptr
  have hroomI' : addressI.toNat + 8 ≤ 4294967296 := by
    simpa [addressI] using hroomI
  have hroomJ' : addressJ.toNat + 8 ≤ 4294967296 := by
    simpa [addressJ] using hroomJ
  have hi1 : (addressI + 1).toNat = addressI.toNat + 1 := by
    simpa using UInt32.add_ofNat_toNat_noWrap addressI 1 (by omega) (by omega)
  have hi2 : (addressI + 2).toNat = addressI.toNat + 2 := by
    simpa using UInt32.add_ofNat_toNat_noWrap addressI 2 (by omega) (by omega)
  have hi3 : (addressI + 3).toNat = addressI.toNat + 3 := by
    simpa using UInt32.add_ofNat_toNat_noWrap addressI 3 (by omega) (by omega)
  have hi4 : (addressI + 4).toNat = addressI.toNat + 4 := by
    simpa using UInt32.add_ofNat_toNat_noWrap addressI 4 (by omega) (by omega)
  have hi5 : (addressI + 5).toNat = addressI.toNat + 5 := by
    simpa using UInt32.add_ofNat_toNat_noWrap addressI 5 (by omega) (by omega)
  have hi6 : (addressI + 6).toNat = addressI.toNat + 6 := by
    simpa using UInt32.add_ofNat_toNat_noWrap addressI 6 (by omega) (by omega)
  have hi7 : (addressI + 7).toNat = addressI.toNat + 7 := by
    simpa using UInt32.add_ofNat_toNat_noWrap addressI 7 (by omega) (by omega)
  have hj1 : (addressJ + 1).toNat = addressJ.toNat + 1 := by
    simpa using UInt32.add_ofNat_toNat_noWrap addressJ 1 (by omega) (by omega)
  have hj2 : (addressJ + 2).toNat = addressJ.toNat + 2 := by
    simpa using UInt32.add_ofNat_toNat_noWrap addressJ 2 (by omega) (by omega)
  have hj3 : (addressJ + 3).toNat = addressJ.toNat + 3 := by
    simpa using UInt32.add_ofNat_toNat_noWrap addressJ 3 (by omega) (by omega)
  have hj4 : (addressJ + 4).toNat = addressJ.toNat + 4 := by
    simpa using UInt32.add_ofNat_toNat_noWrap addressJ 4 (by omega) (by omega)
  have hj5 : (addressJ + 5).toNat = addressJ.toNat + 5 := by
    simpa using UInt32.add_ofNat_toNat_noWrap addressJ 5 (by omega) (by omega)
  have hj6 : (addressJ + 6).toNat = addressJ.toNat + 6 := by
    simpa using UInt32.add_ofNat_toNat_noWrap addressJ 6 (by omega) (by omega)
  have hj7 : (addressJ + 7).toNat = addressJ.toNat + 7 := by
    simpa using UInt32.add_ofNat_toNat_noWrap addressJ 7 (by omega) (by omega)
  apply
    Wasm.SmallStep.wasm_smallStep_heap_globals_runtime_store_partiallyMeets.{0}
      (α := Unit) (σ := σ) (globalσ := globalσ)
  · exact hagree
  · exact hinBounds
  · exact hglobals
  · intro gs
    iintro ⟨Hheap, Hglobals, Hruntime⟩
    ihave Hwords := hresources $$ Hheap
    icases Hwords with ⟨HA, HB⟩
    have hpost : ∀ values : List Value,
        (iprop% ⌜values = []⌝ ∗
          pointsTo_u64 addressI oldB ∗ pointsTo_u64 addressJ oldA) ⊢
        (iprop% ∀ (store : Wasm.SmallStep.MachineStore Unit)
            (_observations : List Wasm.SmallStep.StepKind),
          stateInterp (GF := WasmHeapGF) store 0 [] 0 -∗
          ⌜values = [] ∧ store.wasm.mem.read64 addressI = oldB ∧
            store.wasm.mem.read64 addressJ = oldA⌝) := by
      intro values
      iintro ⟨%hvalues, HA, HB⟩ %store %_observations Hstate
      imod Wasm.SmallStep.stateInterp_pointsTo_u64_facts_frame
        store 0 [] 0 addressI oldB hi1 hi2 hi3 hi4 hi5 hi6 hi7 $$
          [$Hstate $HA] with ⟨Hstate, _HA, %HfactsI⟩
      imod Wasm.SmallStep.stateInterp_pointsTo_u64_facts
        store 0 [] 0 addressJ oldA hj1 hj2 hj3 hj4 hj5 hj6 hj7 $$
          [$Hstate $HB] with %HfactsJ
      ipureintro
      exact ⟨hvalues, HfactsI.1, HfactsJ.1⟩
    iclear Hglobals Hruntime
    iapply wp_mono hpost
    simp only [opt3ConfigFromStore]
    iapply opt3_func0_distinct_smallStep_wp
      ptr len i j oldA oldB hi hj hroomI hroomJ
    iframe

/-- Symbolic finite termination of the optimized straight-line happy path.
This is deliberately separate from the Iris rule: it supplies totality while
the Iris proof supplies the physical-memory postcondition. -/
theorem opt3_func0_terminates
    (wasm : Store Unit) (ptr len i j : UInt32)
    (hi : i < len) (hj : j < len)
    (hboundI :
      ((i <<< (3 % 32)) + ptr).toNat + 8 ≤ wasm.mem.pages * 65536)
    (hboundJ :
      ((j <<< (3 % 32)) + ptr).toNat + 8 ≤ wasm.mem.pages * 65536) :
    Wasm.SmallStep.TerminatesWith
      (opt3ConfigFromStore wasm ptr len i j)
      (fun values _store => values = []) := by
  simp only [opt3ConfigFromStore, Project.SwapElementsOpt3.func0]
  apply Wasm.SmallStep.TerminatesWith.prepend Wasm.SmallStep.Step.block
  apply Wasm.SmallStep.TerminatesWith.prepend Wasm.SmallStep.Step.block
  apply Wasm.SmallStep.TerminatesWith.prepend
    (Wasm.SmallStep.Step.localGet rfl)
  apply Wasm.SmallStep.TerminatesWith.prepend
    (Wasm.SmallStep.Step.localGet rfl)
  apply Wasm.SmallStep.TerminatesWith.prepend
    (Wasm.SmallStep.Step.geU (result := 0) (by simp [not_le_of_gt hi]))
  apply Wasm.SmallStep.TerminatesWith.prepend Wasm.SmallStep.Step.brIfZero
  apply Wasm.SmallStep.TerminatesWith.prepend
    (Wasm.SmallStep.Step.localGet rfl)
  apply Wasm.SmallStep.TerminatesWith.prepend
    (Wasm.SmallStep.Step.localGet rfl)
  apply Wasm.SmallStep.TerminatesWith.prepend
    (Wasm.SmallStep.Step.geU (result := 0) (by simp [not_le_of_gt hj]))
  apply Wasm.SmallStep.TerminatesWith.prepend Wasm.SmallStep.Step.brIfZero
  apply Wasm.SmallStep.TerminatesWith.prepend
    (Wasm.SmallStep.Step.localGet rfl)
  apply Wasm.SmallStep.TerminatesWith.prepend
    (Wasm.SmallStep.Step.localGet rfl)
  apply Wasm.SmallStep.TerminatesWith.prepend Wasm.SmallStep.Step.const
  apply Wasm.SmallStep.TerminatesWith.prepend Wasm.SmallStep.Step.shl
  apply Wasm.SmallStep.TerminatesWith.prepend Wasm.SmallStep.Step.add
  apply Wasm.SmallStep.TerminatesWith.prepend
    (Wasm.SmallStep.Step.localSet rfl)
  simp only [List.set]
  apply Wasm.SmallStep.TerminatesWith.prepend
    (Wasm.SmallStep.Step.localGet rfl)
  apply Wasm.SmallStep.TerminatesWith.prepend
    (Wasm.SmallStep.Step.load64 rfl (by simpa using hboundI))
  apply Wasm.SmallStep.TerminatesWith.prepend
    (Wasm.SmallStep.Step.localSet rfl)
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
    List.set]
  apply Wasm.SmallStep.TerminatesWith.prepend
    (Wasm.SmallStep.Step.localGet rfl)
  apply Wasm.SmallStep.TerminatesWith.prepend
    (Wasm.SmallStep.Step.localGet rfl)
  apply Wasm.SmallStep.TerminatesWith.prepend
    (Wasm.SmallStep.Step.localGet rfl)
  apply Wasm.SmallStep.TerminatesWith.prepend Wasm.SmallStep.Step.const
  apply Wasm.SmallStep.TerminatesWith.prepend Wasm.SmallStep.Step.shl
  apply Wasm.SmallStep.TerminatesWith.prepend Wasm.SmallStep.Step.add
  apply Wasm.SmallStep.TerminatesWith.prepend
    (Wasm.SmallStep.Step.localSet rfl)
  simp only [List.set]
  apply Wasm.SmallStep.TerminatesWith.prepend
    (Wasm.SmallStep.Step.localGet rfl)
  apply Wasm.SmallStep.TerminatesWith.prepend
    (Wasm.SmallStep.Step.load64 rfl (by simpa using hboundJ))
  apply Wasm.SmallStep.TerminatesWith.prepend
    (Wasm.SmallStep.Step.store64 rfl (by simpa using hboundI))
  apply Wasm.SmallStep.TerminatesWith.prepend
    (Wasm.SmallStep.Step.localGet rfl)
  apply Wasm.SmallStep.TerminatesWith.prepend
    (Wasm.SmallStep.Step.localGet rfl)
  apply Wasm.SmallStep.TerminatesWith.prepend
    (Wasm.SmallStep.Step.store64 rfl (by
      simpa [Wasm.SmallStep.setMemory_eq] using hboundJ))
  apply Wasm.SmallStep.TerminatesWith.prepend
    Wasm.SmallStep.Step.returnFromFunction
  simp only [List.take_zero, List.nil_append]
  exact ⟨[], [], _, .refl _, rfl⟩

/-- Universal total correctness for the optimized distinct-index export,
obtained by combining its explicit finite trace with its Iris physical-store
partial correctness theorem. -/
theorem opt3_func0_distinct_store_terminatesWith
    (wasm : Store Unit) (ptr len i j : UInt32)
    (oldA oldB : UInt64)
    (σ : WasmHeapMap (Option UInt8))
    (globalσ : WasmGlobalMap Value)
    (hi : i < len) (hj : j < len)
    (hboundI :
      ((i <<< (3 % 32)) + ptr).toNat + 8 ≤ wasm.mem.pages * 65536)
    (hboundJ :
      ((j <<< (3 % 32)) + ptr).toNat + 8 ≤ wasm.mem.pages * 65536)
    (hroomI : ((i <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296)
    (hroomJ : ((j <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296)
    (hagree : heapAgreesWithMem σ wasm.mem)
    (hinBounds : heapAddressesInBounds σ wasm.mem)
    (hglobals : globalHeapAgrees globalσ wasm.globals)
    (hresources : ∀ [WasmHeapGS],
      ([∗map] address ↦ value ∈ σ,
        pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
          address (DFrac.own 1) value) ⊢
      pointsTo_u64 ((i <<< (3 % 32)) + ptr) oldA ∗
      pointsTo_u64 ((j <<< (3 % 32)) + ptr) oldB) :
    Wasm.SmallStep.TerminatesWith
      (opt3ConfigFromStore wasm ptr len i j)
      (fun values store =>
        values = [] ∧
          store.wasm.mem.read64 ((i <<< (3 % 32)) + ptr) = oldB ∧
          store.wasm.mem.read64 ((j <<< (3 % 32)) + ptr) = oldA) := by
  apply Wasm.SmallStep.TerminatesWith.of_termination_and_partial
    ((opt3_func0_terminates wasm ptr len i j hi hj hboundI hboundJ).mono
      (fun _ _ _ => trivial))
  exact opt3_func0_distinct_store_partiallyMeets
    wasm ptr len i j oldA oldB σ globalσ hi hj hroomI hroomJ
    hagree hinBounds hglobals hresources

abbrev opt0ExampleConfig : Wasm.SmallStep.Config Unit :=
  Project.SwapElements.SwapSepLogic.func4ExampleConfig

/-- The optimized export on the same physical Wasm store and arguments as the
unoptimized two-element example. -/
def opt3ExampleConfig : Wasm.SmallStep.Config Unit :=
  { expr := .running
      ⟨⟨[.i32 0, .i32 2, .i32 0, .i32 1], [.i64 0], []⟩,
        Project.SwapElementsOpt3.func0, 0, [], [], []⟩
    store :=
      { runtime :=
          { module := Project.SwapElementsOpt3.module
            host := {} }
        wasm := opt0ExampleConfig.store.wasm } }

/-- Caller-visible array observation. Private scratch and spill locations are
intentionally absent. -/
def arrayObservation (store : Wasm.SmallStep.MachineStore Unit) :
    UInt64 × UInt64 :=
  (store.wasm.mem.read64 0, store.wasm.mem.read64 8)

theorem opt0Example_terminates_with_observation :
    Wasm.SmallStep.TerminatesWith opt0ExampleConfig
      (fun values store =>
        values = [] ∧ arrayObservation store = (22, 11)) := by
  apply Wasm.SmallStep.TerminatesWith.of_termination_and_partial
    (Project.SwapElements.SwapSepLogic.func4Example_terminates.mono
      (fun _ _ _ => trivial))
  intro trace values store execution
  have h :=
    Project.SwapElements.SwapSepLogic.func4Example_store_smallStep
      trace values store execution
  exact ⟨h.1, Prod.ext h.2.1 h.2.2⟩

theorem opt3Example_terminates_with_observation :
    Wasm.SmallStep.TerminatesWith opt3ExampleConfig
      (fun values store =>
        values = [] ∧ arrayObservation store = (22, 11)) := by
  apply Wasm.SmallStep.runSteps_checked_terminates (fuel := 100)
    (fun values store =>
      (values == []) && (arrayObservation store == (22, 11)))
  · native_decide
  · intro values store h
    simpa [Bool.and_eq_true] using h

/-- The two actual generated exports have exactly the same terminal outcomes
under the caller-visible array observation for the concrete regression. -/
theorem example_observationally_equivalent :
    Wasm.SmallStep.ObservationallyEquivOn
      opt0ExampleConfig opt3ExampleConfig arrayObservation :=
  Wasm.SmallStep.ObservationallyEquivOn.of_common_outcome
    opt0Example_terminates_with_observation
    opt3Example_terminates_with_observation

end Project.SwapElementsOpt3.SmallStepEquivalence
