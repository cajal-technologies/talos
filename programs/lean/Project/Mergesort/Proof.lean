import Project.Mergesort.Spec
import CodeLib.Examples.SelectionSort.StdIOProof

/-!
# End-to-end correctness of generated merge sort

The proof follows the generated program's three semantic phases:

1. `read_raw` places the packed input in `WORK`;
2. `mergesort_raw` sorts that array using the adjacent half as scratch;
3. `write_raw` emits the sorted bytes.

The middle phase is discharged by the compositional function contracts in
`CoreProof`; the two boundary phases use the exact deterministic StdIO host.
-/

namespace Project.Mergesort.Proof

open Wasm SepLogic SmallStep
open Iris Iris.Std

private theorem take_eq_self_of_length_le {β : Type} (xs : List β) (n : Nat)
    (h : xs.length ≤ n) : xs.take n = xs := by
  induction xs generalizing n with
  | nil => simp
  | cons x xs ih =>
      cases n with
      | zero => simp at h
      | succ n =>
          simp only [List.take_succ_cons, List.length_cons] at h ⊢
          rw [ih n (Nat.le_of_succ_le_succ h)]

@[simp] theorem encodeValues_eq_serialize (values : List UInt64) :
    Pure.encodeValues values =
      Wasm.Examples.SelectionSort.StdIO.serialize values := by
  rfl

/-- Concrete store immediately after the bounded read. -/
def afterRead (input : List UInt64) : Store Wasm.StdIO.State :=
  { Project.Mergesort.StdIO.initialStore (Pure.encodeValues input) with
    mem :=
      (Project.Mergesort.StdIO.initialStore
        (Pure.encodeValues input)).mem.writeBytes
        Project.Mergesort.StdIO.source.toNat (Pure.encodeValues input)
    host := { input := [], output := [] } }

@[simp] private theorem initialStore_host (input : List UInt8) :
    (Project.Mergesort.StdIO.initialStore input).host =
      Wasm.StdIO.State.ofInput input := rfl

private theorem initial_byteCapacity (input : List UInt8) :
    Wasm.StdIO.byteCapacity
      (Project.Mergesort.StdIO.initialStore input) = 17 * 65536 := by
  rfl

theorem read_fits (input : List UInt64)
    (hfit : Spec.Fits input) :
    TerminatesWith
      (FunctionSpecs.callConfig 7
        (Project.Mergesort.StdIO.initialStore (Pure.encodeValues input))
        [.i32 Project.Mergesort.StdIO.source,
         .i32 (UInt32.ofNat Project.Mergesort.StdIO.bufferBytes)])
      (fun values final =>
        values = [.i32 (UInt32.ofNat (Pure.encodeValues input).length)] ∧
        final.wasm = afterRead input) := by
  have htake : (Pure.encodeValues input).take
      Project.Mergesort.StdIO.bufferBytes = Pure.encodeValues input := by
    apply take_eq_self_of_length_le
    simpa only [Spec.Fits, Spec.maxValues,
      Project.Mergesort.StdIO.bufferBytes, Pure.encodeValues_length] using
      Nat.mul_le_mul_left 8 hfit
  apply FunctionSpecs.read_raw_correct
  simp only [Wasm.StdIO.readHost, Wasm.StdIO.readResult, initialStore_host,
    Wasm.StdIO.State.ofInput]
  rw [show (UInt32.ofNat Project.Mergesort.StdIO.bufferBytes).toNat =
      Project.Mergesort.StdIO.bufferBytes by decide]
  rw [htake]
  rw [if_pos]
  · simp [afterRead, Project.Mergesort.StdIO.initialStore]
  · simp only [Wasm.StdIO.rangeInBounds, initial_byteCapacity]
    apply decide_eq_true
    simp only [Project.Mergesort.StdIO.source, UInt32.reduceToNat,
      Pure.encodeValues_length]
    simp only [Spec.Fits, Spec.maxValues] at hfit
    omega

theorem encodedLength_toNat (input : List UInt64) (hfit : Spec.Fits input) :
    (UInt32.ofNat (Pure.encodeValues input).length).toNat =
      (Pure.encodeValues input).length := by
  apply UInt32.toNat_ofNat_of_lt'
  simp only [Pure.encodeValues_length, UInt32.size]
  simp only [Spec.Fits, Spec.maxValues] at hfit
  omega

theorem encodedLength_count (input : List UInt64) (hfit : Spec.Fits input) :
    UInt32.ofNat (Pure.encodeValues input).length >>> 3 =
      UInt32.ofNat input.length := by
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_shiftRight, encodedLength_toNat input hfit]
  simp only [Pure.encodeValues_length, UInt32.reduceToNat, Nat.reduceMod,
    Nat.shiftRight_eq_div_pow, Nat.reducePow]
  rw [Nat.mul_div_cancel_left _ (by decide : 0 < 8)]
  symm
  apply UInt32.toNat_ofNat_of_lt'
  simp only [UInt32.size]
  simp only [Spec.Fits, Spec.maxValues] at hfit
  omega

theorem scratch_toNat (input : List UInt64) (hfit : Spec.Fits input) :
    (Project.Mergesort.StdIO.scratch (UInt32.ofNat input.length)).toNat =
      Project.Mergesort.StdIO.source.toNat + 8 * input.length := by
  unfold Project.Mergesort.StdIO.scratch
  rw [UInt32.toNat_add]
  rw [UInt32.toNat_shiftLeft]
  have hlength : (UInt32.ofNat input.length).toNat = input.length := by
    apply UInt32.toNat_ofNat_of_lt'
    simp only [UInt32.size]
    simp only [Spec.Fits, Spec.maxValues] at hfit
    omega
  rw [hlength]
  simp only [UInt32.reduceToNat, Nat.reduceMod, Nat.shiftLeft_eq,
    Nat.reducePow, Project.Mergesort.StdIO.source, UInt32.reduceToNat]
  rw [Nat.mod_eq_of_lt (by
    simp only [Spec.Fits, Spec.maxValues] at hfit
    omega)]
  rw [Nat.mod_eq_of_lt]
  · omega
  · simp only [Spec.Fits, Spec.maxValues] at hfit
    omega

theorem scratch_eq_wordOffset (input : List UInt64) :
    Project.Mergesort.StdIO.scratch (UInt32.ofNat input.length) =
      Project.Mergesort.StdIO.source + 8 * UInt32.ofNat input.length := by
  unfold Project.Mergesort.StdIO.scratch
  have hshift : UInt32.ofNat input.length <<< 3 =
      8 * UInt32.ofNat input.length := by
    bv_decide
  rw [hshift]

def scratchValues (input : List UInt64) : List UInt64 :=
  Wasm.Examples.SelectionSort.StdIO.readWordArray64 (afterRead input).mem
    (Project.Mergesort.StdIO.scratch (UInt32.ofNat input.length)) input.length

/-- One owned word immediately before `WORK`.  It is never touched by merge
sort; retaining it gives the postcondition a nonempty in-bounds witness even
for the empty input. -/
def boundary : UInt32 := 1048568

def boundaryValues (input : List UInt64) : List UInt64 :=
  Wasm.Examples.SelectionSort.StdIO.readWordArray64
    (Project.Mergesort.StdIO.initialStore (Pure.encodeValues input)).mem
    boundary 1

def baseHeap (input : List UInt64) : WasmHeapMap (Option UInt8) :=
  Wasm.Examples.SelectionSort.StdIO.heap64Aux ∅ boundary
    (boundaryValues input)

def sourceHeap (input : List UInt64) : WasmHeapMap (Option UInt8) :=
  Wasm.Examples.SelectionSort.StdIO.heap64Aux (baseHeap input)
    Project.Mergesort.StdIO.source input

def sortHeap (input : List UInt64) : WasmHeapMap (Option UInt8) :=
  Wasm.Examples.SelectionSort.StdIO.heap64Aux (sourceHeap input)
    (Project.Mergesort.StdIO.scratch (UInt32.ofNat input.length))
    (scratchValues input)

theorem scratchValues_length (input : List UInt64) :
    (scratchValues input).length = input.length := by
  have aux (mem : Mem) (base : UInt32) (count : Nat) :
      (Wasm.Examples.SelectionSort.StdIO.readWordArray64 mem base count).length =
        count := by
    induction count generalizing base with
    | zero => rfl
    | succ count ih =>
        simp only [Wasm.Examples.SelectionSort.StdIO.readWordArray64,
          List.length_cons]
        rw [ih]
  exact aux _ _ _

@[simp] theorem boundaryValues_length (input : List UInt64) :
    (boundaryValues input).length = 1 := by
  rfl

private theorem empty_agrees (mem : Mem) :
    heapAgreesWithMem (∅ : WasmHeapMap (Option UInt8)) mem := by
  intro address byte hget
  rw [get?_empty] at hget
  contradiction

private theorem empty_inBounds (mem : Mem) :
    heapAddressesInBounds (∅ : WasmHeapMap (Option UInt8)) mem := by
  intro address byte hget
  rw [get?_empty] at hget
  contradiction

theorem afterRead_mem_eq (input : List UInt64) (hfit : Spec.Fits input) :
    (afterRead input).mem =
      Wasm.Examples.SelectionSort.StdIO.writeWordArray64
        (Project.Mergesort.StdIO.initialStore
          (Pure.encodeValues input)).mem
        Project.Mergesort.StdIO.source input := by
  unfold afterRead
  simp only
  rw [encodeValues_eq_serialize]
  apply Wasm.Examples.SelectionSort.StdIO.writeBytes_serialize
  simp only [Project.Mergesort.StdIO.source, UInt32.reduceToNat,
    UInt32.size, Spec.Fits, Spec.maxValues] at hfit ⊢
  omega

theorem Mem.write64_read64 (mem : Mem) (base : UInt32) :
    mem.write64 base (mem.read64 base) = mem := by
  cases mem with
  | mk pages bytes =>
    simp only [Mem.write64, Mem.read64]
    congr
    funext i
    by_cases h0 : i = base.toNat
    · subst i; simp only [if_pos]; bv_decide
    by_cases h1 : i = base.toNat + 1
    · subst i; simp only [if_neg h0, if_pos]; bv_decide
    by_cases h2 : i = base.toNat + 2
    · subst i; simp only [if_neg h0, if_neg h1, if_pos]; bv_decide
    by_cases h3 : i = base.toNat + 3
    · subst i; simp only [if_neg h0, if_neg h1, if_neg h2, if_pos]; bv_decide
    by_cases h4 : i = base.toNat + 4
    · subst i
      simp only [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_pos]
      bv_decide
    by_cases h5 : i = base.toNat + 5
    · subst i
      simp only [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4,
        if_pos]
      bv_decide
    by_cases h6 : i = base.toNat + 6
    · subst i
      simp only [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4,
        if_neg h5, if_pos]
      bv_decide
    by_cases h7 : i = base.toNat + 7
    · subst i
      simp only [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4,
        if_neg h5, if_neg h6, if_pos]
      bv_decide
    simp [h0, h1, h2, h3, h4, h5, h6, h7]

theorem writeWordArray64_readWordArray64 (mem : Mem) (base : UInt32)
    (count : Nat) :
    Wasm.Examples.SelectionSort.StdIO.writeWordArray64 mem base
        (Wasm.Examples.SelectionSort.StdIO.readWordArray64 mem base count) =
      mem := by
  induction count generalizing base with
  | zero => rfl
  | succ count ih =>
      simp only [Wasm.Examples.SelectionSort.StdIO.readWordArray64,
        Wasm.Examples.SelectionSort.StdIO.writeWordArray64]
      rw [Mem.write64_read64, ih]

theorem baseHeap_agrees_initial (input : List UInt64) :
    heapAgreesWithMem (baseHeap input)
      (Project.Mergesort.StdIO.initialStore (Pure.encodeValues input)).mem := by
  have hbase := Wasm.Examples.SelectionSort.StdIO.heap64Aux_agrees
    (∅ : WasmHeapMap (Option UInt8))
    (Project.Mergesort.StdIO.initialStore (Pure.encodeValues input)).mem
    boundary (boundaryValues input)
    (empty_agrees _) (by simp [boundary, UInt32.size])
  simp only [boundaryValues] at hbase
  rw [writeWordArray64_readWordArray64] at hbase
  simpa only [baseHeap, boundaryValues] using hbase

theorem sourceHeap_agrees (input : List UInt64) (hfit : Spec.Fits input) :
    heapAgreesWithMem (sourceHeap input) (afterRead input).mem := by
  rw [afterRead_mem_eq input hfit]
  unfold sourceHeap
  apply Wasm.Examples.SelectionSort.StdIO.heap64Aux_agrees
  · apply baseHeap_agrees_initial
  · simp only [Project.Mergesort.StdIO.source, UInt32.reduceToNat,
      UInt32.size, Spec.Fits, Spec.maxValues] at hfit ⊢
    omega

private theorem afterRead_pages (input : List UInt64) :
    (afterRead input).mem.pages = 17 := by
  rfl

theorem sortHeap_agrees (input : List UInt64) (hfit : Spec.Fits input) :
    heapAgreesWithMem (sortHeap input) (afterRead input).mem := by
  have hscratch :=
    Wasm.Examples.SelectionSort.StdIO.heap64Aux_agrees
      (sourceHeap input) (afterRead input).mem
      (Project.Mergesort.StdIO.scratch (UInt32.ofNat input.length))
      (scratchValues input) (sourceHeap_agrees input hfit)
      (by
        rw [scratchValues_length, scratch_toNat input hfit]
        simp only [Project.Mergesort.StdIO.source, UInt32.reduceToNat,
          UInt32.size, Spec.Fits, Spec.maxValues] at hfit ⊢
        omega)
  simp only [scratchValues] at hscratch
  rw [writeWordArray64_readWordArray64] at hscratch
  simpa only [sortHeap, scratchValues] using hscratch

theorem baseHeap_inBounds_initial (input : List UInt64) :
    heapAddressesInBounds (baseHeap input)
      (Project.Mergesort.StdIO.initialStore (Pure.encodeValues input)).mem := by
  have hbase := Wasm.Examples.SelectionSort.StdIO.heap64Aux_inBounds
    (∅ : WasmHeapMap (Option UInt8))
    (Project.Mergesort.StdIO.initialStore (Pure.encodeValues input)).mem
    boundary (boundaryValues input)
    (empty_inBounds _) (by simp [boundary, UInt32.size])
    (by
      rw [show
        (Project.Mergesort.StdIO.initialStore
          (Pure.encodeValues input)).mem.pages = 17 by rfl]
      simp [boundary])
  simp only [boundaryValues] at hbase
  rw [writeWordArray64_readWordArray64] at hbase
  simpa only [baseHeap, boundaryValues] using hbase

theorem sourceHeap_inBounds (input : List UInt64) (hfit : Spec.Fits input) :
    heapAddressesInBounds (sourceHeap input) (afterRead input).mem := by
  rw [afterRead_mem_eq input hfit]
  unfold sourceHeap
  apply Wasm.Examples.SelectionSort.StdIO.heap64Aux_inBounds
  · apply baseHeap_inBounds_initial
  · simp only [Project.Mergesort.StdIO.source, UInt32.reduceToNat,
      UInt32.size, Spec.Fits, Spec.maxValues] at hfit ⊢
    omega
  · rw [show
      (Project.Mergesort.StdIO.initialStore
        (Pure.encodeValues input)).mem.pages = 17 by rfl]
    simp only [Project.Mergesort.StdIO.source, UInt32.reduceToNat,
      Nat.reduceMul, Spec.Fits, Spec.maxValues] at hfit ⊢
    omega

theorem sortHeap_inBounds (input : List UInt64) (hfit : Spec.Fits input) :
    heapAddressesInBounds (sortHeap input) (afterRead input).mem := by
  have hscratch :=
    Wasm.Examples.SelectionSort.StdIO.heap64Aux_inBounds
      (sourceHeap input) (afterRead input).mem
      (Project.Mergesort.StdIO.scratch (UInt32.ofNat input.length))
      (scratchValues input) (sourceHeap_inBounds input hfit)
      (by
        rw [scratchValues_length, scratch_toNat input hfit]
        simp only [Project.Mergesort.StdIO.source, UInt32.reduceToNat,
          UInt32.size, Spec.Fits, Spec.maxValues] at hfit ⊢
        omega)
      (by
        rw [scratchValues_length, scratch_toNat input hfit,
          afterRead_pages]
        simp only [Project.Mergesort.StdIO.source, UInt32.reduceToNat,
          Nat.reduceMul, Spec.Fits, Spec.maxValues] at hfit ⊢
        omega)
  simp only [scratchValues] at hscratch
  rw [writeWordArray64_readWordArray64] at hscratch
  simpa only [sortHeap, scratchValues] using hscratch

theorem heap64Aux_addresses_lt
    (heap : WasmHeapMap (Option UInt8)) (base : UInt32)
    (values : List UInt64) (limit : Nat)
    (hheap : ∀ address byte, get? heap address = some byte →
      address.toNat < base.toNat)
    (hfit : base.toNat + 8 * values.length ≤ limit)
    (hlimit : limit < UInt32.size) :
    ∀ address byte,
      get? (Wasm.Examples.SelectionSort.StdIO.heap64Aux heap base values)
          address = some byte →
      address.toNat < limit := by
  induction values generalizing heap base with
  | nil =>
      intro address byte hget
      exact Nat.lt_of_lt_of_le (hheap address byte hget) (by simpa using hfit)
  | cons value values ih =>
      simp only [Wasm.Examples.SelectionSort.StdIO.heap64Aux,
        List.length_cons] at *
      have hn (n : Nat) (hn : n ≤ 8) :
          (base + UInt32.ofNat n).toNat = base.toNat + n := by
        apply UInt32.add_ofNat_toNat_noWrap base n
        · omega
        · simp only [UInt32.size] at hlimit
          omega
      have h1 : (base + 1 : UInt32).toNat = base.toNat + 1 := by
        simpa using hn 1 (by omega)
      have h2 : (base + 2 : UInt32).toNat = base.toNat + 2 := by
        simpa using hn 2 (by omega)
      have h3 : (base + 3 : UInt32).toNat = base.toNat + 3 := by
        simpa using hn 3 (by omega)
      have h4 : (base + 4 : UInt32).toNat = base.toNat + 4 := by
        simpa using hn 4 (by omega)
      have h5 : (base + 5 : UInt32).toNat = base.toNat + 5 := by
        simpa using hn 5 (by omega)
      have h6 : (base + 6 : UInt32).toNat = base.toNat + 6 := by
        simpa using hn 6 (by omega)
      have h7 : (base + 7 : UInt32).toNat = base.toNat + 7 := by
        simpa using hn 7 (by omega)
      have h8 : (base + 8 : UInt32).toNat = base.toNat + 8 := by
        simpa using hn 8 (by omega)
      apply ih (store64Heap heap base value) (base + 8)
      · intro address byte hget
        rw [h8]
        by_cases ha7 : address = base + 7
        · subst address; rw [h7]; omega
        by_cases ha6 : address = base + 6
        · subst address; rw [h6]; omega
        by_cases ha5 : address = base + 5
        · subst address; rw [h5]; omega
        by_cases ha4 : address = base + 4
        · subst address; rw [h4]; omega
        by_cases ha3 : address = base + 3
        · subst address; rw [h3]; omega
        by_cases ha2 : address = base + 2
        · subst address; rw [h2]; omega
        by_cases ha1 : address = base + 1
        · subst address; rw [h1]; omega
        by_cases ha0 : address = base
        · subst address; omega
        simp only [store64Heap, get?_insert_ne (Ne.symm ha7),
          get?_insert_ne (Ne.symm ha6), get?_insert_ne (Ne.symm ha5),
          get?_insert_ne (Ne.symm ha4), get?_insert_ne (Ne.symm ha3),
          get?_insert_ne (Ne.symm ha2), get?_insert_ne (Ne.symm ha1),
          get?_insert_ne (Ne.symm ha0)] at hget
        exact Nat.lt_trans (hheap address byte hget) (by omega)
      · rw [h8]
        omega

set_option maxHeartbeats 6000000 in
theorem sortHeap_pointsTo [WasmHeapGS]
    (input : List UInt64) (hfit : Spec.Fits input) :
    (([∗map] address ↦ value ∈ sortHeap input,
        pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
          address (DFrac.own 1) value) ⊢
      array64At boundary (boundaryValues input) ∗
      array64At Project.Mergesort.StdIO.source input ∗
      array64At
        (Project.Mergesort.StdIO.scratch (UInt32.ofNat input.length))
        (scratchValues input)) := by
  have hempty : ∀ address byte,
      get? (∅ : WasmHeapMap (Option UInt8)) address = some byte →
      address.toNat < boundary.toNat := by
    intro address byte hget
    rw [get?_empty] at hget
    contradiction
  have hboundaryFit : boundary.toNat +
      8 * (boundaryValues input).length < UInt32.size := by
    simp [boundary, UInt32.size]
  have hbaseDisjoint : ∀ address byte,
      get? (Wasm.Examples.SelectionSort.StdIO.heap64Aux ∅ boundary
        (boundaryValues input)) address = some byte →
      address.toNat < Project.Mergesort.StdIO.source.toNat := by
    apply heap64Aux_addresses_lt ∅ boundary (boundaryValues input)
      Project.Mergesort.StdIO.source.toNat hempty
    · simp [boundary, Project.Mergesort.StdIO.source]
    · simp [Project.Mergesort.StdIO.source, UInt32.size]
  have hsourceFit : Project.Mergesort.StdIO.source.toNat +
      8 * input.length < UInt32.size := by
    simp only [Project.Mergesort.StdIO.source, UInt32.reduceToNat,
      UInt32.size, Spec.Fits, Spec.maxValues] at hfit ⊢
    omega
  have hscratchFit :
      (Project.Mergesort.StdIO.scratch
          (UInt32.ofNat input.length)).toNat +
        8 * (scratchValues input).length < UInt32.size := by
    rw [scratchValues_length, scratch_toNat input hfit]
    simp only [Project.Mergesort.StdIO.source, UInt32.reduceToNat,
      UInt32.size, Spec.Fits, Spec.maxValues] at hfit ⊢
    omega
  have hdisjoint : ∀ address byte,
      get? (Wasm.Examples.SelectionSort.StdIO.heap64Aux (baseHeap input)
        Project.Mergesort.StdIO.source input) address = some byte →
      address.toNat <
        (Project.Mergesort.StdIO.scratch
          (UInt32.ofNat input.length)).toNat := by
    apply heap64Aux_addresses_lt
      (Wasm.Examples.SelectionSort.StdIO.heap64Aux ∅ boundary
        (boundaryValues input))
      Project.Mergesort.StdIO.source input
      (Project.Mergesort.StdIO.scratch
        (UInt32.ofNat input.length)).toNat hbaseDisjoint
    · rw [scratch_toNat input hfit]
    · rw [scratch_toNat input hfit]
      simp only [Project.Mergesort.StdIO.source, UInt32.reduceToNat,
        UInt32.size, Spec.Fits, Spec.maxValues] at hfit ⊢
      omega
  simp only [sortHeap, sourceHeap, baseHeap]
  iintro Hheap
  ihave Hscratch :=
    Wasm.Examples.SelectionSort.StdIO.heap64Aux_pointsTo
      (Wasm.Examples.SelectionSort.StdIO.heap64Aux
        (Wasm.Examples.SelectionSort.StdIO.heap64Aux ∅ boundary
          (boundaryValues input)) Project.Mergesort.StdIO.source input)
      (Project.Mergesort.StdIO.scratch (UInt32.ofNat input.length))
      (scratchValues input) hdisjoint hscratchFit $$ Hheap
  icases Hscratch with ⟨Hscratch, HsourceHeap⟩
  ihave Hsource :=
    Wasm.Examples.SelectionSort.StdIO.heap64Aux_pointsTo
      (Wasm.Examples.SelectionSort.StdIO.heap64Aux ∅ boundary
        (boundaryValues input)) Project.Mergesort.StdIO.source input
      hbaseDisjoint hsourceFit $$ HsourceHeap
  icases Hsource with ⟨Hsource, HbaseHeap⟩
  ihave Hbase :=
    Wasm.Examples.SelectionSort.StdIO.heap64Aux_pointsTo
      ∅ boundary (boundaryValues input) hempty hboundaryFit $$ HbaseHeap
  icases Hbase with ⟨Hboundary, _Hempty⟩
  isplitl [Hboundary]
  · iexact Hboundary
  isplitl [Hsource]
  · iexact Hsource
  · iexact Hscratch

theorem validLayout (input : List UInt64) (hfit : Spec.Fits input) :
    CoreProof.ValidLayout Project.Mergesort.StdIO.source
      (Project.Mergesort.StdIO.scratch (UInt32.ofNat input.length))
      input.length := by
  constructor
  · simp only [Project.Mergesort.StdIO.source, UInt32.reduceToNat,
      UInt32.size, Spec.Fits, Spec.maxValues] at hfit ⊢
    omega
  · rw [scratch_toNat input hfit]
    simp only [Project.Mergesort.StdIO.source, UInt32.reduceToNat,
      UInt32.size, Spec.Fits, Spec.maxValues] at hfit ⊢
    omega

def CorePost (input : List UInt64)
    (values : List Value) (store : MachineStore Unit) : Prop :=
  values = [] ∧ ∃ (output scratchOutput : List UInt64),
    output.length = input.length ∧
    scratchOutput.length = input.length ∧
    Pure.SortedPermutation input output ∧
    Wasm.Examples.SelectionSort.StdIO.readWordArray64 store.wasm.mem
      Project.Mergesort.StdIO.source input.length = output ∧
    Project.Mergesort.StdIO.source.toNat + 8 * input.length ≤
      store.wasm.mem.pages * 65536

set_option maxHeartbeats 12000000 in
theorem twp_core [WasmSmallStepGS hlc]
    (input : List UInt64) (hfit : Spec.Fits input) :
    (([∗map] address ↦ value ∈ sortHeap input,
        pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
          address (DFrac.own 1) value) ∗
      ([∗map] index ↦ value ∈ (∅ : WasmGlobalMap Value),
        globalPointsTo index value) ∗
      runtimeModuleOwn
        (Project.Mergesort.StdIO.coreConfig (afterRead input)
          (UInt32.ofNat input.length)).store.runtime.module) ⊢
      WP (Project.Mergesort.StdIO.coreConfig (afterRead input)
          (UInt32.ofNat input.length)).expr
        @ Stuckness.NotStuck; ⊤
        [{ values,
          ∀ (store : MachineStore Unit) (_observations : List StepKind),
            stateInterp (GF := WasmHeapGF) store 0 [] 0 -∗
            ⌜CorePost input values store⌝ }] := by
  iintro ⟨Hheap, _Hglobals, Hruntime⟩
  ihave Harrays := sortHeap_pointsTo input hfit $$ Hheap
  icases Harrays with ⟨Hboundary, Hsource, Hscratch⟩
  simp only [Project.Mergesort.StdIO.coreConfig]
  iapply CoreProof.twp_mergesortRaw
    Project.Mergesort.StdIO.source
    (Project.Mergesort.StdIO.scratch (UInt32.ofNat input.length))
    input (scratchValues input) (scratchValues_length input)
    (validLayout input hfit)
    (callerLocals := ⟨[], [], []⟩) (stack := []) (code := [])
    (arity := 0) (remainder := []) (controls := []) (calls := [])
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hsource]
  · iexact Hsource
  isplitl [Hscratch]
  · iexact Hscratch
  · iintro %output %scratchOutput %hpure Hruntime Hsource Hscratch
    iapply Wasm.SmallStep.twp_finish
    iapply twp.value rfl
    iintro %store %observations Hstate
    have houtFit : Project.Mergesort.StdIO.source.toNat +
        8 * output.length < UInt32.size := by
      rw [hpure.1]
      simp only [Project.Mergesort.StdIO.source, UInt32.reduceToNat,
        UInt32.size, Spec.Fits, Spec.maxValues] at hfit ⊢
      omega
    imod Wasm.Examples.SelectionSort.StdIO.array64At_words
      store 0 [] 0 Project.Mergesort.StdIO.source output houtFit $$
      [$Hstate $Hsource] with ⟨Hstate, Hsource, %hwords⟩
    ihave HboundaryWord := array64At_get boundary (boundaryValues input)
      0 (by simp) $$ Hboundary
    icases HboundaryWord with ⟨HboundaryWord, HrestoreBoundary⟩
    let boundarySlot := boundary + 8 * UInt32.ofNat 0
    have hslot : boundarySlot = boundary := by decide
    have hn (n : Nat) (hn : n ≤ 7) :
        (boundarySlot + UInt32.ofNat n).toNat = boundarySlot.toNat + n := by
      apply UInt32.add_ofNat_toNat_noWrap boundarySlot n
      · omega
      · rw [hslot]
        simp only [boundary, UInt32.reduceToNat]
        omega
    imod stateInterp_pointsTo_u64_facts_frame
      store 0 [] 0 boundarySlot (boundaryValues input)[0]
      (by simpa using hn 1 (by omega))
      (by simpa using hn 2 (by omega))
      (by simpa using hn 3 (by omega))
      (by simpa using hn 4 (by omega))
      (by simpa using hn 5 (by omega))
      (by simpa using hn 6 (by omega))
      (by simpa using hn 7 (by omega)) $$
      [$Hstate $HboundaryWord] with
      ⟨Hstate, HboundaryWord, %hboundaryCapacity⟩
    have hsourceBase : Project.Mergesort.StdIO.source.toNat ≤
        store.wasm.mem.pages * 65536 := by
      have hsource : Project.Mergesort.StdIO.source.toNat =
          boundarySlot.toNat + 8 := by simp [boundarySlot, boundary,
            Project.Mergesort.StdIO.source]
      rw [hsource]
      exact hboundaryCapacity.2
    imod Wasm.Examples.SelectionSort.StdIO.array64At_capacity
      store 0 [] 0 Project.Mergesort.StdIO.source output houtFit hsourceBase $$
      [$Hstate $Hsource] with ⟨_Hstate, _Hsource, %hcapacity⟩
    ipureintro
    exact ⟨rfl, output, scratchOutput, hpure.1, hpure.2.1, hpure.2.2,
      by simpa [hpure.1] using hwords,
      by simpa [hpure.1] using hcapacity⟩

private theorem readBytes_eight_add (mem : Mem) (offset n : Nat) :
    mem.readBytes offset (8 + n) =
      [mem.bytes offset, mem.bytes (offset + 1), mem.bytes (offset + 2),
       mem.bytes (offset + 3), mem.bytes (offset + 4),
       mem.bytes (offset + 5), mem.bytes (offset + 6),
       mem.bytes (offset + 7)] ++ mem.readBytes (offset + 8) n := by
  unfold Mem.readBytes
  rw [List.range_add]
  simp only [List.map_append, List.range_succ, List.range_zero,
    List.map_cons, List.map_nil, List.nil_append]
  congr 1
  simp [Nat.add_assoc]

theorem encodeWord_read64 (mem : Mem) (base : UInt32) :
    Wasm.Examples.SelectionSort.StdIO.encodeWord (mem.read64 base) =
      [mem.bytes base.toNat, mem.bytes (base.toNat + 1),
       mem.bytes (base.toNat + 2), mem.bytes (base.toNat + 3),
       mem.bytes (base.toNat + 4), mem.bytes (base.toNat + 5),
       mem.bytes (base.toNat + 6), mem.bytes (base.toNat + 7)] := by
  simp only [Mem.read64]
  generalize mem.bytes base.toNat = b0
  generalize mem.bytes (base.toNat + 1) = b1
  generalize mem.bytes (base.toNat + 2) = b2
  generalize mem.bytes (base.toNat + 3) = b3
  generalize mem.bytes (base.toNat + 4) = b4
  generalize mem.bytes (base.toNat + 5) = b5
  generalize mem.bytes (base.toNat + 6) = b6
  generalize mem.bytes (base.toNat + 7) = b7
  simp only [Wasm.Examples.SelectionSort.StdIO.encodeWord, List.cons.injEq]
  constructor <;> bv_decide

theorem readBytes64_eq_serialize (mem : Mem) (base : UInt32) (count : Nat)
    (hfit : base.toNat + 8 * count < UInt32.size) :
    mem.readBytes base.toNat (8 * count) =
      Wasm.Examples.SelectionSort.StdIO.serialize
        (Wasm.Examples.SelectionSort.StdIO.readWordArray64 mem base count) := by
  induction count generalizing base with
  | zero => rfl
  | succ count ih =>
      rw [show 8 * (count + 1) = 8 + 8 * count by omega]
      rw [readBytes_eight_add]
      simp only [Wasm.Examples.SelectionSort.StdIO.readWordArray64,
        Wasm.Examples.SelectionSort.StdIO.serialize, List.flatMap_cons]
      rw [encodeWord_read64]
      have hbase : (base + 8).toNat = base.toNat + 8 := by
        apply UInt32.add_ofNat_toNat_noWrap base 8 (by decide)
        simp only [UInt32.size] at hfit ⊢
        omega
      rw [← hbase, ih]
      · rfl
      · rw [hbase]
        omega

theorem core_stronglyNormalizing (input : List UInt64)
    (hfit : Spec.Fits input) :
    Iris.ProgramLogic.StronglyNormalizing
      (Iris.ProgramLogic.ExprErasedStep (Expr := Expr Unit)
        (State := MachineStore Unit) (Obs := StepKind))
      ((Project.Mergesort.StdIO.coreConfig (afterRead input)
          (UInt32.ofNat input.length)).expr,
       (Project.Mergesort.StdIO.coreConfig (afterRead input)
          (UInt32.ofNat input.length)).store) := by
  apply Wasm.SmallStep.wasm_smallStep_heap_globals_runtime_stronglyNormalizing.{0}
    (Project.Mergesort.StdIO.coreConfig (afterRead input)
      (UInt32.ofNat input.length)) (sortHeap input) ∅
    (fun _values => iprop(True))
  · exact sortHeap_agrees input hfit
  · exact sortHeap_inBounds input hfit
  · exact globalHeapAgrees_empty _
  · intro _
    iintro Hresources
    ihave Hcore := twp_core input hfit $$ Hresources
    iapply twp.mono (fun _values => ?_) $$ Hcore
    iintro _Hpost
    itrivial

theorem core_terminatesWith (input : List UInt64)
    (hfit : Spec.Fits input) :
    TerminatesWith
      (Project.Mergesort.StdIO.coreConfig (afterRead input)
        (UInt32.ofNat input.length))
      (CorePost input) := by
  apply Wasm.SmallStep.stronglyNormalizing_adequate_terminates
    (Project.Mergesort.StdIO.coreConfig (afterRead input)
      (UInt32.ofNat input.length)) (CorePost input)
    (core_stronglyNormalizing input hfit)
  apply wasm_smallStep_heap_globals_runtime_store_adequacy.{0}
    (Project.Mergesort.StdIO.coreConfig (afterRead input)
      (UInt32.ofNat input.length))
    (sortHeap input) ∅ (CorePost input)
  · exact sortHeap_agrees input hfit
  · exact sortHeap_inBounds input hfit
  · exact globalHeapAgrees_empty _
  · intro _
    iintro Hresources
    iapply twp.to_wp
    iapply twp_core input hfit
    iexact Hresources

def writtenStore (store : Store Wasm.StdIO.State) (pointer length : UInt32) :
    Store Wasm.StdIO.State :=
  { store with
    host :=
      { input := store.host.input
        output := store.host.output ++
          store.mem.readBytes pointer.toNat length.toNat } }

theorem write_raw_bytes (store : Store Wasm.StdIO.State)
    (pointer length : UInt32)
    (hbound : pointer.toNat + length.toNat ≤ Wasm.StdIO.byteCapacity store) :
    TerminatesWith
      (FunctionSpecs.callConfig 8 store [.i32 pointer, .i32 length])
      (fun values final =>
        values = [] ∧ final.wasm = writtenStore store pointer length) := by
  apply FunctionSpecs.write_raw_correct
  simp only [Wasm.StdIO.writeHost, Wasm.StdIO.writeResult]
  rw [if_pos]
  · rfl
  · simp only [Wasm.StdIO.rangeInBounds]
    exact decide_eq_true hbound

set_option maxRecDepth 10000 in
@[proves Project.Mergesort.Spec.MergesortSpec]
theorem mergesort_correct : Spec.MergesortSpec := by
  intro input hfit
  have hread := read_fits input hfit
  rcases core_terminatesWith input hfit with
    ⟨trace, values, final, hsteps, hpost⟩
  rcases hpost with
    ⟨hvalues, output, scratchOutput, houtputLength, _hscratchLength,
      hsorted, hreadWords, hcapacity⟩
  let afterCore : Store Unit := final.wasm
  have hcore : TerminatesWith
      (Project.Mergesort.StdIO.coreConfig (afterRead input)
        (UInt32.ofNat input.length))
      (fun result finalStore =>
        result = [] ∧ finalStore.wasm = afterCore) :=
    ⟨trace, values, final, hsteps, hvalues, rfl⟩
  let byteLength := UInt32.ofNat (Pure.encodeValues input).length
  let afterSort : Store Wasm.StdIO.State :=
    Project.Mergesort.StdIO.replaceHost afterCore (afterRead input).host
  have hbyteLength : byteLength.toNat = 8 * input.length := by
    change (UInt32.ofNat (Pure.encodeValues input).length).toNat =
      8 * input.length
    rw [encodedLength_toNat input hfit, Pure.encodeValues_length]
  have hwriteBound : Project.Mergesort.StdIO.source.toNat +
      byteLength.toNat ≤ Wasm.StdIO.byteCapacity afterSort := by
    simp only [afterSort, Project.Mergesort.StdIO.replaceHost,
      Wasm.StdIO.byteCapacity, hbyteLength]
    exact hcapacity
  have hwrite := write_raw_bytes afterSort Project.Mergesort.StdIO.source
    byteLength hwriteBound
  let afterWrite :=
    writtenStore afterSort Project.Mergesort.StdIO.source byteLength
  have hbytes : afterWrite.host.output = Pure.encodeValues output := by
    have hserialized := readBytes64_eq_serialize afterCore.mem
      Project.Mergesort.StdIO.source input.length
      (by
        simp only [Project.Mergesort.StdIO.source, UInt32.reduceToNat,
          UInt32.size, Spec.Fits, Spec.maxValues] at hfit ⊢
        omega)
    rw [hreadWords] at hserialized
    simp only [afterWrite, writtenStore, afterSort,
      Project.Mergesort.StdIO.replaceHost, afterRead, List.nil_append,
      hbyteLength]
    rw [hserialized]
    rfl
  refine ⟨output, ?_, hsorted⟩
  unfold Spec.RunsValues Spec.RunsBytes Project.Mergesort.StdIO.RunsBytes
  refine ⟨byteLength, afterRead input, afterWrite, afterCore, hread, ?_, ?_,
    hbytes⟩
  · simpa only [byteLength, encodedLength_count input hfit] using hcore
  · simpa only [afterSort, afterWrite] using hwrite

end Project.Mergesort.Proof
