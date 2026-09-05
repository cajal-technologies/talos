import CodeLib.Examples.UInt32Array
import Interpreter.Wasm.Decoder.ProofEval
import Mathlib.Data.List.Sort

kernel_decoder
attribute [local irreducible] Wasm.Decoder.Wat.decode

/-!
# Quicksort

A handwritten Wasm implementation of Lomuto partition quicksort.
-/

namespace Wasm.Examples.Quicksort

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic
open Wasm.SmallStep
open Wasm.Examples.UInt32Array

def swapAt (base a b tmp : Nat) : Program :=
  loadAt base a ++ [.localSet tmp] ++
  storeAt base a (loadAt base b) ++
  storeAt base b [.localGet tmp]

-- partition: arr=local0, lo=local1, hi=local2
-- pivot=local3, i=local4, j=local5, hiMinusOne=local6, tmp=local7

def partitionInit : Program :=
  [.localGet 2, .const 1, .sub, .localSet 6] ++
  loadAt 0 6 ++ [.localSet 3] ++
  [.localGet 1, .localSet 4,
   .localGet 1, .localSet 5]

def partitionScanCondition : Program := lessLocal 5 6

def partitionScanStep : Program :=
  [.localGet 3] ++ loadAt 0 5 ++ [.ltU,
   .iff 0 0 [] (swapAt 0 4 5 7 ++ increment 4)] ++
  increment 5

def partitionPlacePivot : Program :=
  swapAt 0 4 6 7 ++ [.localGet 4]

def partitionBody : Program :=
  partitionInit ++
  whileDo partitionScanCondition partitionScanStep ++
  partitionPlacePivot ++
  [.ret]

def partitionFunction : Function :=
  { params := [.i32, .i32, .i32]
    locals := [.i32, .i32, .i32, .i32, .i32]
    results := [.i32]
    body := partitionBody }

-- quicksort: arr=local0, lo=local1, hi=local2, pivotIdx=local3

def quicksortBaseCheck : Program :=
  [.localGet 2, .localGet 1, .sub, .const 2, .ltU,
   .iff 0 0 [.ret] []]

def quicksortPartitionCall (partitionIndex : Nat) : Program :=
  [.localGet 0, .localGet 1, .localGet 2, .call partitionIndex, .localSet 3]

def quicksortLeftCall (quicksortIndex : Nat) : Program :=
  [.localGet 0, .localGet 1, .localGet 3, .call quicksortIndex]

def quicksortRightCall (quicksortIndex : Nat) : Program :=
  [.localGet 0, .localGet 3, .const 1, .add, .localGet 2, .call quicksortIndex]

def quicksortBody (partitionIndex quicksortIndex : Nat) : Program :=
  quicksortBaseCheck ++
  quicksortPartitionCall partitionIndex ++
  quicksortLeftCall quicksortIndex ++
  quicksortRightCall quicksortIndex ++
  [.ret]

def quicksortFunction (partitionIndex quicksortIndex : Nat) : Function :=
  { params := [.i32, .i32, .i32]
    locals := [.i32]
    body := quicksortBody partitionIndex quicksortIndex }

def quicksortModule : Module :=
  { funcs := [partitionFunction, quicksortFunction 0 1]
    memory := some { pagesMin := 1 } }

/-! ## Public specification -/

def Sorted (values : List UInt32) : Prop :=
  values.Pairwise (· ≤ ·)

def SortedPermutation (input output : List UInt32) : Prop :=
  Sorted output ∧ List.Perm input output

abbrev segment (values : List UInt32) (start stop : Nat) :=
  (values.drop start).take (stop - start)

def arrayByteRange (base : UInt32) (length : Nat) : Nat × Nat :=
  (base.toNat, base.toNat + 4 * length)

def ValidQuicksortLayout (arr : UInt32) (length : Nat) : Prop :=
  arr.toNat + 4 * length ≤ UInt32.size

def PartitionRange (input output : List UInt32) (lo hi pivotIndex : Nat) : Prop :=
  lo ≤ pivotIndex ∧ pivotIndex < hi ∧ hi ≤ input.length ∧
  output.length = input.length ∧
  output.take lo = input.take lo ∧
  output.drop hi = input.drop hi ∧
  List.Perm (segment input lo hi) (segment output lo hi) ∧
  (∀ x ∈ segment output lo pivotIndex, x ≤ output[pivotIndex]!) ∧
  (∀ x ∈ segment output (pivotIndex + 1) hi, x > output[pivotIndex]!)

def quicksortPre [WasmHeapGS α]
    (arr : UInt32) (values : List UInt32) (lo hi : Nat) : IProp (WasmHeapGF α) :=
  iprop% arrayAt 0 arr values ∗
    ⌜lo ≤ hi ∧ hi ≤ values.length ∧ ValidQuicksortLayout arr values.length⌝

def quicksortPost [WasmHeapGS α]
    (arr : UInt32) (input : List UInt32) (lo hi : Nat) : IProp (WasmHeapGF α) :=
  iprop% ∃ output : List UInt32,
    ⌜output.length = input.length ∧
     output.take lo = input.take lo ∧
     output.drop hi = input.drop hi ∧
     Sorted (segment output lo hi) ∧
     List.Perm (segment input lo hi) (segment output lo hi)⌝ ∗
    arrayAt 0 arr output

/-! ## Executable regressions -/

abbrev writeWordArray := Mem.writeWords32

abbrev readWordArray := Mem.readWords32

def quicksortExampleStore (arr : UInt32) (input : List UInt32) : Store Unit :=
  let initial := quicksortModule.initialStore (α := Unit)
  { initial with mem := writeWordArray initial.mem arr input }

def quicksortArguments (arr : UInt32) (length : Nat) (stack : List Value) : List Value :=
  .i32 (UInt32.ofNat length) :: .i32 0 :: .i32 arr :: stack

private def runQuicksortModule (m : Module) (fuel : Nat) (arr : UInt32)
    (input : List UInt32) : Option (List UInt32) :=
  match SmallStep.initConfig
      { module := m, host := {} } 1
      (quicksortExampleStore arr input)
      (quicksortArguments arr input.length []) with
  | .error _ => none
  | .ok config =>
      match (SmallStep.runSteps fuel config).result with
      | .success _ store =>
          some (readWordArray store.wasm.mem arr input.length)
      | _ => none

def runQuicksortExample (fuel : Nat) (arr : UInt32) (input : List UInt32) :
    Option (List UInt32) := runQuicksortModule quicksortModule fuel arr input

theorem quicksort_exec_empty :
    runQuicksortExample 100 0 [] = some [] := by decide +kernel

theorem quicksort_exec_singleton :
    runQuicksortExample 200 0 [42] = some [42] := by decide +kernel

theorem quicksort_exec_five :
    runQuicksortExample 15000 0 [5, 1, 4, 2, 3] = some [1, 2, 3, 4, 5] := by decide +kernel

theorem quicksort_exec_duplicates :
    runQuicksortExample 18000 0 [4, 1, 4, 2, 1, 3] = some [1, 1, 2, 3, 4, 4] := by decide +kernel

theorem quicksort_exec_sorted :
    runQuicksortExample 10000 0 [1, 2, 3, 4] = some [1, 2, 3, 4] := by decide +kernel

/-! ## TerminatesWith witnesses -/

private def configDefault : Config Unit :=
  { expr := .done []
    store :=
      { runtime := { instances := #[{ module := default, host := {} }], entry := ⟨0⟩ }
        wasm := { globals := default, mem := default, host := () } } }

private def quicksortExampleConfig (arr : UInt32) (input : List UInt32) : Config Unit :=
  (SmallStep.initConfig
      { module := quicksortModule, host := {} } 1
      (quicksortExampleStore arr input)
      (quicksortArguments arr input.length [])).toOption.getD configDefault

theorem quicksort_terminates_empty :
    SmallStep.TerminatesWith (quicksortExampleConfig 0 [])
        (fun _ store => readWordArray store.wasm.mem 0 0 = []) := by
  apply SmallStep.runSteps_checked_terminates (fuel := 100)
      (fun _ store => readWordArray store.wasm.mem 0 0 == [])
  · decide +kernel
  · intro _ store h; simp only [beq_iff_eq] at h; exact h

theorem quicksort_terminates_singleton :
    SmallStep.TerminatesWith (quicksortExampleConfig 0 [42])
        (fun _ store => readWordArray store.wasm.mem 0 1 = [42]) := by
  apply SmallStep.runSteps_checked_terminates (fuel := 200)
      (fun _ store => readWordArray store.wasm.mem 0 1 == [42])
  · decide +kernel
  · intro _ store h; simp only [beq_iff_eq] at h; exact h

theorem quicksort_terminates_five :
    SmallStep.TerminatesWith (quicksortExampleConfig 0 [5, 1, 4, 2, 3])
        (fun _ store => readWordArray store.wasm.mem 0 5 = [1, 2, 3, 4, 5]) := by
  apply SmallStep.runSteps_checked_terminates (fuel := 15000)
      (fun _ store => readWordArray store.wasm.mem 0 5 == [1, 2, 3, 4, 5])
  · decide +kernel
  · intro _ store h; simp only [beq_iff_eq] at h; exact h

theorem quicksort_terminates_duplicates :
    SmallStep.TerminatesWith (quicksortExampleConfig 0 [4, 1, 4, 2, 1, 3])
        (fun _ store => readWordArray store.wasm.mem 0 6 = [1, 1, 2, 3, 4, 4]) := by
  apply SmallStep.runSteps_checked_terminates (fuel := 18000)
      (fun _ store => readWordArray store.wasm.mem 0 6 == [1, 1, 2, 3, 4, 4])
  · decide +kernel
  · intro _ store h; simp only [beq_iff_eq] at h; exact h

theorem quicksort_terminates_sorted :
    SmallStep.TerminatesWith (quicksortExampleConfig 0 [1, 2, 3, 4])
        (fun _ store => readWordArray store.wasm.mem 0 4 = [1, 2, 3, 4]) := by
  apply SmallStep.runSteps_checked_terminates (fuel := 10000)
      (fun _ store => readWordArray store.wasm.mem 0 4 == [1, 2, 3, 4])
  · decide +kernel
  · intro _ store h; simp only [beq_iff_eq] at h; exact h

/-! ## Differential check -/

def runQuicksortLegacy (fuel : Nat) (arr : UInt32) (input : List UInt32) :
    Option (List UInt32) :=
  match Wasm.run fuel quicksortModule 1
      (quicksortExampleStore arr input)
      (quicksortArguments arr input.length []) with
  | .Success _ store => some (readWordArray store.mem arr input.length)
  | _ => none

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem quicksort_small_large_agree :
    runQuicksortExample 15000 0 [5, 1, 4, 2, 3] =
    runQuicksortLegacy 5000 0 [5, 1, 4, 2, 3] := by
  have hsmall : runQuicksortLegacy 64 0 [5, 1, 4, 2, 3] =
      some [1, 2, 3, 4, 5] := by cbv
  rw [quicksort_exec_five]
  unfold runQuicksortLegacy at hsmall ⊢
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd] at hsmall ⊢
  have hne : Wasm.run 64 quicksortModule 1
      (quicksortExampleStore 0 [5, 1, 4, 2, 3])
      (quicksortArguments 0 5 []) ≠ .OutOfFuel := by
    intro h
    simp [h] at hsmall
  rw [Wasm.run_fuel_mono (show 64 ≤ 5000 by decide) hne]
  exact hsmall.symm

/-! ## Mutation tests -/

private def partitionFunctionMutated1 : Function :=
  { params := [.i32, .i32, .i32]
    locals := [.i32, .i32, .i32, .i32, .i32]
    results := [.i32]
    body :=
      partitionInit ++
      whileDo partitionScanCondition
        ([.localGet 3] ++ loadAt 0 5 ++ [.geU,
          .iff 0 0 [] (swapAt 0 4 5 7 ++ increment 4)] ++
         increment 5) ++
      partitionPlacePivot ++
      [.ret] }

private def quicksortModuleMutated1 : Module :=
  { funcs := [partitionFunctionMutated1, quicksortFunction 0 1]
    memory := some { pagesMin := 1 } }

def runQuicksortMutated1 (fuel : Nat) (arr : UInt32) (input : List UInt32) :
    Option (List UInt32) :=
  match SmallStep.initConfig
      { module := quicksortModuleMutated1, host := {} } 1
      (quicksortExampleStore arr input)
      (quicksortArguments arr input.length []) with
  | .error _ => none
  | .ok config =>
      match (SmallStep.runSteps fuel config).result with
      | .success _ store => some (readWordArray store.wasm.mem arr input.length)
      | _ => none

theorem quicksort_mutation_comparison :
    runQuicksortMutated1 15000 0 [5, 1, 4, 2, 3] ≠ some [1, 2, 3, 4, 5] := by decide +kernel

private def partitionFunctionMutated2 : Function :=
  { params := [.i32, .i32, .i32]
    locals := [.i32, .i32, .i32, .i32, .i32]
    results := [.i32]
    body :=
      partitionInit ++
      whileDo partitionScanCondition partitionScanStep ++
      swapAt 0 5 6 7 ++ [.localGet 4] ++
      [.ret] }

private def quicksortModuleMutated2 : Module :=
  { funcs := [partitionFunctionMutated2, quicksortFunction 0 1]
    memory := some { pagesMin := 1 } }

def runQuicksortMutated2 (fuel : Nat) (arr : UInt32) (input : List UInt32) :
    Option (List UInt32) :=
  match SmallStep.initConfig
      { module := quicksortModuleMutated2, host := {} } 1
      (quicksortExampleStore arr input)
      (quicksortArguments arr input.length []) with
  | .error _ => none
  | .ok config =>
      match (SmallStep.runSteps fuel config).result with
      | .success _ store => some (readWordArray store.wasm.mem arr input.length)
      | _ => none

theorem quicksort_mutation_index :
    runQuicksortMutated2 15000 0 [5, 1, 4, 2, 3] ≠ some [1, 2, 3, 4, 5] := by decide +kernel

private def quicksortFunctionMutated3 : Function :=
  { params := [.i32, .i32, .i32]
    locals := [.i32]
    body :=
      [.localGet 2, .localGet 1, .sub, .const 3, .ltU,
       .iff 0 0 [.ret] []] ++
      quicksortPartitionCall 0 ++
      quicksortLeftCall 1 ++
      quicksortRightCall 1 ++
      [.ret] }

private def quicksortModuleMutated3 : Module :=
  { funcs := [partitionFunction, quicksortFunctionMutated3]
    memory := some { pagesMin := 1 } }

def runQuicksortMutated3 (fuel : Nat) (arr : UInt32) (input : List UInt32) :
    Option (List UInt32) :=
  match SmallStep.initConfig
      { module := quicksortModuleMutated3, host := {} } 1
      (quicksortExampleStore arr input)
      (quicksortArguments arr input.length []) with
  | .error _ => none
  | .ok config =>
      match (SmallStep.runSteps fuel config).result with
      | .success _ store => some (readWordArray store.wasm.mem arr input.length)
      | _ => none

theorem quicksort_mutation_bound :
    runQuicksortMutated3 15000 0 [5, 1, 4, 2, 3] ≠ some [1, 2, 3, 4, 5] := by decide +kernel

private def partitionFunctionMutated4 : Function :=
  { params := [.i32, .i32, .i32]
    locals := [.i32, .i32, .i32, .i32, .i32]
    results := [.i32]
    body :=
      partitionInit ++
      whileDo partitionScanCondition
        ([.localGet 3] ++ loadAt 0 5 ++ [.ltU,
          .iff 0 0 [] (storeAt 0 4 [.const 0] ++ increment 4)] ++
         increment 5) ++
      partitionPlacePivot ++
      [.ret] }

private def quicksortModuleMutated4 : Module :=
  { funcs := [partitionFunctionMutated4, quicksortFunction 0 1]
    memory := some { pagesMin := 1 } }

def runQuicksortMutated4 (fuel : Nat) (arr : UInt32) (input : List UInt32) :
    Option (List UInt32) :=
  match SmallStep.initConfig
      { module := quicksortModuleMutated4, host := {} } 1
      (quicksortExampleStore arr input)
      (quicksortArguments arr input.length []) with
  | .error _ => none
  | .ok config =>
      match (SmallStep.runSteps fuel config).result with
      | .success _ store => some (readWordArray store.wasm.mem arr input.length)
      | _ => none

theorem quicksort_mutation_store :
    runQuicksortMutated4 15000 0 [5, 1, 4, 2, 3] ≠ some [1, 2, 3, 4, 5] := by decide +kernel

/-! ## Oracle agreement -/

theorem quicksort_oracle_empty :
    runQuicksortExample 100 0 [] =
    some (List.mergeSort []) := by decide +kernel

theorem quicksort_oracle_singleton :
    runQuicksortExample 200 0 [42] =
    some (List.mergeSort [42]) := by decide +kernel

theorem quicksort_oracle_five :
    runQuicksortExample 15000 0 [5, 1, 4, 2, 3] =
    some (List.mergeSort [5, 1, 4, 2, 3]) := by
  rw [quicksort_exec_five]
  cbv

theorem quicksort_oracle_duplicates :
    runQuicksortExample 18000 0 [4, 1, 4, 2, 1, 3] =
    some (List.mergeSort [4, 1, 4, 2, 1, 3]) := by
  rw [quicksort_exec_duplicates]
  cbv

theorem quicksort_oracle_sorted :
    runQuicksortExample 10000 0 [1, 2, 3, 4] =
    some (List.mergeSort [1, 2, 3, 4]) := by
  rw [quicksort_exec_sorted]
  cbv

/-! ## Adequacy infrastructure -/

def quicksortHeapAux (σ : WasmHeapMap (Option UInt8)) (base : UInt32) :
    List UInt32 → WasmHeapMap (Option UInt8)
  | [] => σ
  | x :: xs => quicksortHeapAux (store32Heap σ 0 base x) (base + 4) xs

def quicksortHeap (arr : UInt32) (input : List UInt32) :
    WasmHeapMap (Option UInt8) :=
  quicksortHeapAux ∅ arr input

def quicksortConfig (arr : UInt32) (input : List UInt32) : Config Unit :=
  let initial := quicksortModule.initialStore (α := Unit)
  { expr := .running
      ⟨⟨[], [], [.i32 (UInt32.ofNat input.length), .i32 0, .i32 arr]⟩,
        [.call 1], 0, [], [], []⟩
    store :=
      { runtime := { instances := #[{ module := quicksortModule, host := {} }], entry := ⟨0⟩ }
        wasm := { initial with mem := writeWordArray initial.mem arr input } } }

theorem quicksortHeapAux_agrees
    (σ : WasmHeapMap (Option UInt8)) (mem : Mem) (base : UInt32) (xs : List UInt32)
    (hagree : heapAgreesWithMem σ (fun id => if id = 0 then some mem else none))
    (hfit : base.toNat + 4 * xs.length ≤ UInt32.size) :
    heapAgreesWithMem (quicksortHeapAux σ base xs)
      (fun id => if id = 0 then some (writeWordArray mem base xs) else none) := by
  induction xs generalizing σ mem base with
  | nil => simpa [quicksortHeapAux, writeWordArray]
  | cons x xs ih =>
    simp only [quicksortHeapAux, writeWordArray, List.length_cons] at *
    simp only [UInt32.size] at hfit
    have h4_le : (base + 4 : UInt32).toNat ≤ base.toNat + 4 := by
      have h := UInt32.toNat_add base 4
      simp only [show (4 : UInt32).toNat = 4 from by decide] at h
      rw [h]; exact Nat.mod_le _ _
    obtain ⟨h1, h2, h3⟩ := UInt32.addSteps4 base (by omega)
    apply ih
    · exact store32_sound0 σ mem base x h1 h2 h3 hagree
    · simp only [UInt32.size]; omega

theorem quicksortHeap_agrees (arr : UInt32) (input : List UInt32)
    (hfit : arr.toNat + 4 * input.length ≤ UInt32.size) :
    heapAgreesWithMem (quicksortHeap arr input)
      (storeResolve (quicksortConfig arr input).store) := by
  unfold quicksortHeap
  have h := quicksortHeapAux_agrees ∅ (quicksortModule.initialStore (α := Unit)).mem
    arr input
    (by intro key value hget; simp [get?_empty] at hget)
    hfit
  have heq := singleMemoryResolve_eq_storeResolve (quicksortConfig arr input).store
    (writeWordArray (quicksortModule.initialStore (α := Unit)).mem arr input) rfl
    (show (quicksortModule.initialStore (α := Unit)).extraMems = [] from by decide +kernel)
  rw [heq] at h; exact h

theorem quicksortHeapAux_inBounds
    (σ : WasmHeapMap (Option UInt8)) (mem : Mem) (base : UInt32) (xs : List UInt32)
    (hinBounds : heapAddressesInBounds σ (fun id => if id = 0 then some mem else none))
    (hfit : base.toNat + 4 * xs.length ≤ UInt32.size)
    (hmem : base.toNat + 4 * xs.length ≤ mem.pages * 65536) :
    heapAddressesInBounds (quicksortHeapAux σ base xs)
      (fun id => if id = 0 then some (writeWordArray mem base xs) else none) := by
  induction xs generalizing σ mem base with
  | nil => simpa [quicksortHeapAux, writeWordArray]
  | cons x xs ih =>
    simp only [quicksortHeapAux, writeWordArray, List.length_cons] at *
    simp only [UInt32.size] at hfit
    have h4_le : (base + 4 : UInt32).toNat ≤ base.toNat + 4 := by
      have h := UInt32.toNat_add base 4
      simp only [show (4 : UInt32).toNat = 4 from by decide] at h
      rw [h]; exact Nat.mod_le _ _
    have hpages : (mem.write32 base x).pages = mem.pages := by simp [Mem.write32]
    obtain ⟨h1, h2, h3⟩ := UInt32.addSteps4 base (by omega)
    apply ih
    · exact store32_inBounds0 σ mem base x h1 h2 h3 (by omega) hinBounds
    · simp only [UInt32.size]; omega
    · rw [hpages]; omega

theorem quicksortHeap_inBounds (arr : UInt32) (input : List UInt32)
    (hfit : arr.toNat + 4 * input.length ≤ UInt32.size)
    (hmem : arr.toNat + 4 * input.length ≤ 65536) :
    heapAddressesInBounds (quicksortHeap arr input)
      (storeResolve (quicksortConfig arr input).store) := by
  unfold quicksortHeap
  have h := quicksortHeapAux_inBounds ∅ (quicksortModule.initialStore (α := Unit)).mem
    arr input
    (by intro key hget; simp [get?_empty] at hget)
    hfit
    (by have hpages : (quicksortModule.initialStore (α := Unit)).mem.pages = 1 := by decide
        simp only [hpages]; exact hmem)
  have heq := singleMemoryResolve_eq_storeResolve (quicksortConfig arr input).store
    (writeWordArray (quicksortModule.initialStore (α := Unit)).mem arr input) rfl
    (show (quicksortModule.initialStore (α := Unit)).extraMems = [] from by decide +kernel)
  rw [heq] at h; exact h

theorem quicksortHeapAux_pointsTo [WasmHeapGS α]
    (σ : WasmHeapMap (Option UInt8)) (base : UInt32) (xs : List UInt32)
    (hdisjoint : ∀ a b, get? σ a = some b → a.addr.toNat < base.toNat)
    (hfit : base.toNat + 4 * xs.length < UInt32.size) :
    ([∗map] address ↦ value ∈ quicksortHeapAux σ base xs,
        pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap) address (DFrac.own 1) value) ⊢
      arrayAt 0 base xs ∗
      ([∗map] address ↦ value ∈ σ,
          pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap) address (DFrac.own 1) value) := by
  induction xs generalizing σ base with
  | nil =>
    simp only [quicksortHeapAux, arrayAt, BI.emp_sep.to_eq]
    iintro Hσ; iexact Hσ
  | cons x xs ih =>
    simp only [quicksortHeapAux, List.length_cons] at *
    simp only [UInt32.size] at hfit
    have h4 : (base + 4 : UInt32).toNat = base.toNat + 4 :=
      UInt32.add_ofNat_toNat_noWrap base 4 (by decide) (by omega)
    have hfit' : (base + 4).toNat + 4 * xs.length < UInt32.size := by
      simp only [UInt32.size]; omega
    obtain ⟨hn1, hn2, hn3⟩ := UInt32.addSteps4 base (by omega)
    have hget0 : get? σ ⟨0, base⟩ = none := by
      by_contra h; obtain ⟨v, hget⟩ := Option.ne_none_iff_exists.mp h
      have hlt := hdisjoint (⟨0, base⟩ : MemoryKey) v hget.symm
      change base.toNat < base.toNat at hlt; exact absurd hlt (Nat.lt_irrefl _)
    have hget1 : get? σ ⟨0, base + 1⟩ = none := by
      by_contra h; obtain ⟨v, hget⟩ := Option.ne_none_iff_exists.mp h
      have hlt := hdisjoint (⟨0, base + 1⟩ : MemoryKey) v hget.symm
      change (base + 1).toNat < base.toNat at hlt; rw [hn1] at hlt; omega
    have hget2 : get? σ ⟨0, base + 2⟩ = none := by
      by_contra h; obtain ⟨v, hget⟩ := Option.ne_none_iff_exists.mp h
      have hlt := hdisjoint (⟨0, base + 2⟩ : MemoryKey) v hget.symm
      change (base + 2).toNat < base.toNat at hlt; rw [hn2] at hlt; omega
    have hget3 : get? σ ⟨0, base + 3⟩ = none := by
      by_contra h; obtain ⟨v, hget⟩ := Option.ne_none_iff_exists.mp h
      have hlt := hdisjoint (⟨0, base + 3⟩ : MemoryKey) v hget.symm
      change (base + 3).toNat < base.toNat at hlt; rw [hn3] at hlt; omega
    have hdisjoint' : ∀ a b, get? (store32Heap σ 0 base x) a = some b →
        a.addr.toNat < (base + 4).toNat := by
      rw [h4]
      intro a b hget
      by_cases h3 : a = ⟨0, base + 3⟩
      · subst h3; change (base + 3).toNat < base.toNat + 4; rw [hn3]; omega
      by_cases h2 : a = ⟨0, base + 2⟩
      · subst h2; change (base + 2).toNat < base.toNat + 4; rw [hn2]; omega
      by_cases h1 : a = ⟨0, base + 1⟩
      · subst h1; change (base + 1).toNat < base.toNat + 4; rw [hn1]; omega
      by_cases h0 : a = ⟨0, base⟩
      · subst h0; change base.toNat < base.toNat + 4; omega
      · simp only [store32Heap, get?_insert_ne (Ne.symm h3), get?_insert_ne (Ne.symm h2),
            get?_insert_ne (Ne.symm h1), get?_insert_ne (Ne.symm h0)] at hget
        have hlt := hdisjoint a b hget; omega
    iintro Hheap
    ihave ⟨Hxs, Hstore32⟩ := ih (store32Heap σ 0 base x) (base + 4) hdisjoint' hfit' $$ Hheap
    ihave ⟨Hword, Hσ⟩ :=
      store32Heap_pointsTo σ 0 base x hget0 hget1 hget2 hget3 hn1 hn2 hn3 $$ Hstore32
    simp only [arrayAt]
    isplitl [Hword Hxs]
    · isplitl_exact Hword; iexact Hxs
    · iexact Hσ

theorem quicksortHeap_pointsTo [WasmHeapGS α]
    (arr : UInt32) (input : List UInt32)
    (hfit : arr.toNat + 4 * input.length < UInt32.size) :
    ([∗map] address ↦ value ∈ quicksortHeap arr input,
        pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap) address (DFrac.own 1) value) ⊢
      arrayAt 0 arr input := by
  unfold quicksortHeap
  iintro Hheap
  ihave ⟨Harray, _Hemp⟩ := quicksortHeapAux_pointsTo ∅ arr input
    (fun a b hget => by simp [get?_empty] at hget) hfit $$ Hheap
  iexact Harray

/-! ## WAT decoder agreement -/

private def quicksortWat : String := include_str "quicksort.wat"

private def moduleOfDecoded (result : Except String Module) : Module :=
  match result with
  | .ok m => m
  | .error _ => default

private def quicksortModuleDecoded : Module :=
  moduleOfDecoded (Wasm.Decoder.Wat.decode quicksortWat)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem quicksort_decode_eq :
    Wasm.Decoder.Wat.decode quicksortWat = .ok quicksortModule := by cbv

def runQuicksortDecoded (fuel : Nat) (arr : UInt32) (input : List UInt32) :
    Option (List UInt32) := runQuicksortModule quicksortModuleDecoded fuel arr input

set_option maxRecDepth 100000 in
private theorem quicksortModuleDecoded_eq : quicksortModuleDecoded = quicksortModule :=
  congrArg moduleOfDecoded quicksort_decode_eq

set_option maxRecDepth 100000 in
private theorem runQuicksortDecoded_eq (fuel : Nat) (arr : UInt32) (input : List UInt32) :
    runQuicksortDecoded fuel arr input = runQuicksortExample fuel arr input :=
  congrArg (fun m => runQuicksortModule m fuel arr input) quicksortModuleDecoded_eq

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem quicksort_decoded_agrees :
    runQuicksortDecoded 15000 0 [5, 1, 4, 2, 3] =
      runQuicksortExample 15000 0 [5, 1, 4, 2, 3] ∧
    runQuicksortDecoded 15000 0 [] = runQuicksortExample 15000 0 [] ∧
    runQuicksortDecoded 15000 0 [7] = runQuicksortExample 15000 0 [7] ∧
    runQuicksortDecoded 15000 0 [4, 3, 2, 1] =
      runQuicksortExample 15000 0 [4, 3, 2, 1] ∧
    runQuicksortDecoded 20 0 [3, 2, 1] =
      runQuicksortExample 20 0 [3, 2, 1] := by
  exact ⟨runQuicksortDecoded_eq .., runQuicksortDecoded_eq ..,
    runQuicksortDecoded_eq .., runQuicksortDecoded_eq .., runQuicksortDecoded_eq ..⟩

end Wasm.Examples.Quicksort
