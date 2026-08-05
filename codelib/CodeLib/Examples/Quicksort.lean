import CodeLib.SepLogic.SmallStepAdequacy
import Interpreter.Wasm.Decoder.Wat
import Mathlib.Data.List.Sort

/-!
# Quicksort

A handwritten Wasm implementation of Lomuto partition quicksort.
-/

namespace Wasm.Examples.Quicksort

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic
open Wasm.SmallStep

def increment (index : Nat) : Program :=
  [.localGet index, .const 1, .add, .localSet index]

def address (base index : Nat) : Program :=
  [.localGet base, .localGet index, .const 4, .mul, .add]

def loadAt (base index : Nat) : Program :=
  address base index ++ [.load32 0]

def storeAt (base index : Nat) (value : Program) : Program :=
  address base index ++ value ++ [.store32 0]

def whileLoopCode (condition body : Program) : Program :=
  condition ++ [.eqz, .br_if 1] ++ body ++ [.br 0]

def whileDo (condition body : Program) : Program :=
  [.block 0 0 [.loop 0 0 (whileLoopCode condition body)]]

def lessLocal (lhs rhs : Nat) : Program :=
  [.localGet lhs, .localGet rhs, .ltU]

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

def segment (values : List UInt32) (start stop : Nat) : List UInt32 :=
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

def quicksortPre [WasmHeapGS]
    (arr : UInt32) (values : List UInt32) (lo hi : Nat) : IProp WasmHeapGF :=
  iprop% arrayAt arr values ∗
    ⌜lo ≤ hi ∧ hi ≤ values.length ∧ ValidQuicksortLayout arr values.length⌝

def quicksortPost [WasmHeapGS]
    (arr : UInt32) (input : List UInt32) (lo hi : Nat) : IProp WasmHeapGF :=
  iprop% ∃ output : List UInt32,
    ⌜output.length = input.length ∧
     output.take lo = input.take lo ∧
     output.drop hi = input.drop hi ∧
     Sorted (segment output lo hi) ∧
     List.Perm (segment input lo hi) (segment output lo hi)⌝ ∗
    arrayAt arr output

/-! ## Executable regressions -/

def writeWordArray : Mem → UInt32 → List UInt32 → Mem
  | memory, _, [] => memory
  | memory, address, value :: values =>
      writeWordArray (memory.write32 address value) (address + 4) values

def readWordArray : Mem → UInt32 → Nat → List UInt32
  | _, _, 0 => []
  | memory, address, count + 1 =>
      memory.read32 address ::
        readWordArray memory (address + 4) count

def quicksortExampleStore (arr : UInt32) (input : List UInt32) : Store Unit :=
  let initial := quicksortModule.initialStore (α := Unit)
  { initial with mem := writeWordArray initial.mem arr input }

def quicksortArguments (arr : UInt32) (length : Nat) (stack : List Value) : List Value :=
  .i32 (UInt32.ofNat length) :: .i32 0 :: .i32 arr :: stack

def runQuicksortExample (fuel : Nat) (arr : UInt32) (input : List UInt32) :
    Option (List UInt32) :=
  match SmallStep.initConfig
      { module := quicksortModule, host := {} } 1
      (quicksortExampleStore arr input)
      (quicksortArguments arr input.length []) with
  | .error _ => none
  | .ok config =>
      match (SmallStep.runSteps fuel config).result with
      | .success _ store =>
          some (readWordArray store.wasm.mem arr input.length)
      | _ => none

theorem quicksort_exec_empty :
    runQuicksortExample 100 0 [] = some [] := by native_decide

theorem quicksort_exec_singleton :
    runQuicksortExample 200 0 [42] = some [42] := by native_decide

theorem quicksort_exec_five :
    runQuicksortExample 15000 0 [5, 1, 4, 2, 3] = some [1, 2, 3, 4, 5] := by
  native_decide

theorem quicksort_exec_duplicates :
    runQuicksortExample 18000 0 [4, 1, 4, 2, 1, 3] = some [1, 1, 2, 3, 4, 4] := by
  native_decide

theorem quicksort_exec_sorted :
    runQuicksortExample 10000 0 [1, 2, 3, 4] = some [1, 2, 3, 4] := by native_decide

/-! ## TerminatesWith witnesses -/

private def configDefault : Config Unit :=
  { expr := .done []
    store :=
      { runtime := { module := default, host := {} }
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
  · native_decide
  · intro _ store h; simp only [beq_iff_eq] at h; exact h

theorem quicksort_terminates_singleton :
    SmallStep.TerminatesWith (quicksortExampleConfig 0 [42])
        (fun _ store => readWordArray store.wasm.mem 0 1 = [42]) := by
  apply SmallStep.runSteps_checked_terminates (fuel := 200)
      (fun _ store => readWordArray store.wasm.mem 0 1 == [42])
  · native_decide
  · intro _ store h; simp only [beq_iff_eq] at h; exact h

theorem quicksort_terminates_five :
    SmallStep.TerminatesWith (quicksortExampleConfig 0 [5, 1, 4, 2, 3])
        (fun _ store => readWordArray store.wasm.mem 0 5 = [1, 2, 3, 4, 5]) := by
  apply SmallStep.runSteps_checked_terminates (fuel := 15000)
      (fun _ store => readWordArray store.wasm.mem 0 5 == [1, 2, 3, 4, 5])
  · native_decide
  · intro _ store h; simp only [beq_iff_eq] at h; exact h

theorem quicksort_terminates_duplicates :
    SmallStep.TerminatesWith (quicksortExampleConfig 0 [4, 1, 4, 2, 1, 3])
        (fun _ store => readWordArray store.wasm.mem 0 6 = [1, 1, 2, 3, 4, 4]) := by
  apply SmallStep.runSteps_checked_terminates (fuel := 18000)
      (fun _ store => readWordArray store.wasm.mem 0 6 == [1, 1, 2, 3, 4, 4])
  · native_decide
  · intro _ store h; simp only [beq_iff_eq] at h; exact h

theorem quicksort_terminates_sorted :
    SmallStep.TerminatesWith (quicksortExampleConfig 0 [1, 2, 3, 4])
        (fun _ store => readWordArray store.wasm.mem 0 4 = [1, 2, 3, 4]) := by
  apply SmallStep.runSteps_checked_terminates (fuel := 10000)
      (fun _ store => readWordArray store.wasm.mem 0 4 == [1, 2, 3, 4])
  · native_decide
  · intro _ store h; simp only [beq_iff_eq] at h; exact h

/-! ## Differential check -/

def runQuicksortLegacy (fuel : Nat) (arr : UInt32) (input : List UInt32) :
    Option (List UInt32) :=
  match Wasm.run fuel quicksortModule 1
      (quicksortExampleStore arr input)
      (quicksortArguments arr input.length []) with
  | .Success _ store => some (readWordArray store.mem arr input.length)
  | _ => none

theorem quicksort_small_large_agree :
    runQuicksortExample 15000 0 [5, 1, 4, 2, 3] =
    runQuicksortLegacy 5000 0 [5, 1, 4, 2, 3] := by native_decide

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
    runQuicksortMutated1 15000 0 [5, 1, 4, 2, 3] ≠ some [1, 2, 3, 4, 5] := by
  native_decide

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
    runQuicksortMutated2 15000 0 [5, 1, 4, 2, 3] ≠ some [1, 2, 3, 4, 5] := by
  native_decide

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
    runQuicksortMutated3 15000 0 [5, 1, 4, 2, 3] ≠ some [1, 2, 3, 4, 5] := by
  native_decide

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
    runQuicksortMutated4 15000 0 [5, 1, 4, 2, 3] ≠ some [1, 2, 3, 4, 5] := by
  native_decide

/-! ## Oracle agreement -/

theorem quicksort_oracle_empty :
    runQuicksortExample 100 0 [] =
    some (List.mergeSort []) := by native_decide

theorem quicksort_oracle_singleton :
    runQuicksortExample 200 0 [42] =
    some (List.mergeSort [42]) := by native_decide

theorem quicksort_oracle_five :
    runQuicksortExample 15000 0 [5, 1, 4, 2, 3] =
    some (List.mergeSort [5, 1, 4, 2, 3]) := by native_decide

theorem quicksort_oracle_duplicates :
    runQuicksortExample 18000 0 [4, 1, 4, 2, 1, 3] =
    some (List.mergeSort [4, 1, 4, 2, 1, 3]) := by native_decide

theorem quicksort_oracle_sorted :
    runQuicksortExample 10000 0 [1, 2, 3, 4] =
    some (List.mergeSort [1, 2, 3, 4]) := by native_decide

/-! ## Adequacy infrastructure -/

private def quicksortHeapAux (σ : WasmHeapMap (Option UInt8)) (base : UInt32) :
    List UInt32 → WasmHeapMap (Option UInt8)
  | [] => σ
  | x :: xs => quicksortHeapAux (store32Heap σ base x) (base + 4) xs

def quicksortHeap (arr : UInt32) (input : List UInt32) :
    WasmHeapMap (Option UInt8) :=
  quicksortHeapAux ∅ arr input

def quicksortConfig (arr : UInt32) (input : List UInt32) : Config Unit :=
  let initial := quicksortModule.initialStore (α := Unit)
  { expr := .running
      ⟨⟨[], [], [.i32 (UInt32.ofNat input.length), .i32 0, .i32 arr]⟩,
        [.call 1], 0, [], [], []⟩
    store :=
      { runtime := { module := quicksortModule, host := {} }
        wasm := { initial with mem := writeWordArray initial.mem arr input } } }

private theorem quicksortHeapAux_agrees
    (σ : WasmHeapMap (Option UInt8)) (mem : Mem) (base : UInt32) (xs : List UInt32)
    (hagree : heapAgreesWithMem σ mem)
    (hfit : base.toNat + 4 * xs.length ≤ UInt32.size) :
    heapAgreesWithMem (quicksortHeapAux σ base xs) (writeWordArray mem base xs) := by
  induction xs generalizing σ mem base with
  | nil => simpa [quicksortHeapAux, writeWordArray]
  | cons x xs ih =>
    simp only [quicksortHeapAux, writeWordArray, List.length_cons] at *
    simp only [UInt32.size] at hfit
    have h4_le : (base + 4 : UInt32).toNat ≤ base.toNat + 4 := by
      have h := UInt32.toNat_add base 4
      simp only [show (4 : UInt32).toNat = 4 from by decide] at h
      rw [h]; exact Nat.mod_le _ _
    apply ih
    · apply store32_sound
      · exact UInt32.add_ofNat_toNat_noWrap base 1 (by decide) (by omega)
      · exact UInt32.add_ofNat_toNat_noWrap base 2 (by decide) (by omega)
      · exact UInt32.add_ofNat_toNat_noWrap base 3 (by decide) (by omega)
      · exact hagree
    · simp only [UInt32.size]; omega

theorem quicksortHeap_agrees (arr : UInt32) (input : List UInt32)
    (hfit : arr.toNat + 4 * input.length ≤ UInt32.size) :
    heapAgreesWithMem (quicksortHeap arr input)
      (writeWordArray (quicksortModule.initialStore (α := Unit)).mem arr input) := by
  unfold quicksortHeap
  apply quicksortHeapAux_agrees
  · intro addr byte hget; simp [get?_empty] at hget
  · exact hfit

private theorem quicksortHeapAux_inBounds
    (σ : WasmHeapMap (Option UInt8)) (mem : Mem) (base : UInt32) (xs : List UInt32)
    (hinBounds : heapAddressesInBounds σ mem)
    (hfit : base.toNat + 4 * xs.length ≤ UInt32.size)
    (hmem : base.toNat + 4 * xs.length ≤ mem.pages * 65536) :
    heapAddressesInBounds (quicksortHeapAux σ base xs) (writeWordArray mem base xs) := by
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
    apply ih
    · apply store32_inBounds
      · exact UInt32.add_ofNat_toNat_noWrap base 1 (by decide) (by omega)
      · exact UInt32.add_ofNat_toNat_noWrap base 2 (by decide) (by omega)
      · exact UInt32.add_ofNat_toNat_noWrap base 3 (by decide) (by omega)
      · exact hinBounds
      · omega
    · simp only [UInt32.size]; omega
    · rw [hpages]; omega

theorem quicksortHeap_inBounds (arr : UInt32) (input : List UInt32)
    (hfit : arr.toNat + 4 * input.length ≤ UInt32.size)
    (hmem : arr.toNat + 4 * input.length ≤ 65536) :
    heapAddressesInBounds (quicksortHeap arr input)
      (writeWordArray (quicksortModule.initialStore (α := Unit)).mem arr input) := by
  unfold quicksortHeap
  apply quicksortHeapAux_inBounds
  · intro a b hget; simp [get?_empty] at hget
  · exact hfit
  · have hpages : (quicksortModule.initialStore (α := Unit)).mem.pages = 1 := by native_decide
    simp only [hpages]
    exact hmem

private theorem quicksortHeapAux_pointsTo [WasmHeapGS]
    (σ : WasmHeapMap (Option UInt8)) (base : UInt32) (xs : List UInt32)
    (hdisjoint : ∀ a b, get? σ a = some b → a.toNat < base.toNat)
    (hfit : base.toNat + 4 * xs.length < UInt32.size) :
    ([∗map] address ↦ value ∈ quicksortHeapAux σ base xs,
        pointsTo (GF := WasmHeapGF) (H := WasmHeapMap) address (DFrac.own 1) value) ⊢
      arrayAt base xs ∗
      ([∗map] address ↦ value ∈ σ,
          pointsTo (GF := WasmHeapGF) (H := WasmHeapMap) address (DFrac.own 1) value) := by
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
    have hn1 : (base + 1).toNat = base.toNat + 1 :=
      UInt32.add_ofNat_toNat_noWrap base 1 (by decide) (by omega)
    have hn2 : (base + 2).toNat = base.toNat + 2 :=
      UInt32.add_ofNat_toNat_noWrap base 2 (by decide) (by omega)
    have hn3 : (base + 3).toNat = base.toNat + 3 :=
      UInt32.add_ofNat_toNat_noWrap base 3 (by decide) (by omega)
    have hget0 : get? σ base = none := by
      by_contra h; obtain ⟨_, hget⟩ := Option.ne_none_iff_exists.mp h
      exact absurd (hdisjoint _ _ hget.symm) (by omega)
    have hget1 : get? σ (base + 1) = none := by
      by_contra h; obtain ⟨_, hget⟩ := Option.ne_none_iff_exists.mp h
      exact absurd (hdisjoint _ _ hget.symm) (by rw [hn1]; omega)
    have hget2 : get? σ (base + 2) = none := by
      by_contra h; obtain ⟨_, hget⟩ := Option.ne_none_iff_exists.mp h
      exact absurd (hdisjoint _ _ hget.symm) (by rw [hn2]; omega)
    have hget3 : get? σ (base + 3) = none := by
      by_contra h; obtain ⟨_, hget⟩ := Option.ne_none_iff_exists.mp h
      exact absurd (hdisjoint _ _ hget.symm) (by rw [hn3]; omega)
    have hdisjoint' : ∀ a b, get? (store32Heap σ base x) a = some b →
        a.toNat < (base + 4).toNat := by
      rw [h4]
      intro a b hget
      by_cases h3 : a = base + 3
      · subst h3; rw [hn3]; omega
      by_cases h2 : a = base + 2
      · subst h2; rw [hn2]; omega
      by_cases h1 : a = base + 1
      · subst h1; rw [hn1]; omega
      by_cases h0 : a = base
      · subst h0; omega
      · simp only [store32Heap, get?_insert_ne (Ne.symm h3), get?_insert_ne (Ne.symm h2),
            get?_insert_ne (Ne.symm h1), get?_insert_ne (Ne.symm h0)] at hget
        have hlt := hdisjoint a b hget; omega
    iintro Hheap
    ihave Hsplit := ih (store32Heap σ base x) (base + 4) hdisjoint' hfit' $$ Hheap
    icases Hsplit with ⟨Hxs, Hstore32⟩
    ihave Hdecomp :=
      store32Heap_pointsTo σ base x hget0 hget1 hget2 hget3 hn1 hn2 hn3 $$ Hstore32
    icases Hdecomp with ⟨Hword, Hσ⟩
    simp only [arrayAt]
    isplitl [Hword Hxs]
    · isplitl [Hword]; iexact Hword; iexact Hxs
    · iexact Hσ

theorem quicksortHeap_pointsTo [WasmHeapGS]
    (arr : UInt32) (input : List UInt32)
    (hfit : arr.toNat + 4 * input.length < UInt32.size) :
    ([∗map] address ↦ value ∈ quicksortHeap arr input,
        pointsTo (GF := WasmHeapGF) (H := WasmHeapMap) address (DFrac.own 1) value) ⊢
      arrayAt arr input := by
  unfold quicksortHeap
  iintro Hheap
  ihave Hsplit := quicksortHeapAux_pointsTo ∅ arr input
    (fun a b hget => by simp [get?_empty] at hget) hfit $$ Hheap
  icases Hsplit with ⟨Harray, _Hemp⟩
  iexact Harray

theorem arrayAt_readWordArray [WasmSmallStepGS hlc]
    (store : MachineStore α) (steps : Nat) (obs : List StepKind) (threads : Nat)
    (arr : UInt32) (output : List UInt32)
    (hfit : arr.toNat + 4 * output.length ≤ UInt32.size) :
    stateInterp (GF := WasmHeapGF) store steps obs threads ∗ arrayAt arr output ==∗
      stateInterp (GF := WasmHeapGF) store steps obs threads ∗ arrayAt arr output ∗
      ⌜readWordArray store.wasm.mem arr output.length = output⌝ := by
  induction output generalizing arr with
  | nil =>
    simp only [arrayAt, List.length_nil, readWordArray]
    iintro ⟨Hstate, Hemp⟩
    imodintro
    isplitl [Hstate]; iexact Hstate
    isplitl [Hemp]; iexact Hemp
    ipureintro; trivial
  | cons x xs ih =>
    simp only [arrayAt, List.length_cons]
    simp only [List.length_cons, UInt32.size] at hfit
    have h4_le : (arr + 4 : UInt32).toNat ≤ arr.toNat + 4 := by
      have h := UInt32.toNat_add arr 4
      simp only [show (4 : UInt32).toNat = 4 from by decide] at h
      rw [h]; exact Nat.mod_le _ _
    have hfit' : (arr + 4).toNat + 4 * xs.length ≤ UInt32.size := by
      simp only [UInt32.size]; omega
    iintro ⟨Hstate, Hword, Hxs⟩
    imod stateInterp_pointsTo_u32_facts_frame store steps obs threads arr x
      (UInt32.add_ofNat_toNat_noWrap arr 1 (by decide) (by omega))
      (UInt32.add_ofNat_toNat_noWrap arr 2 (by decide) (by omega))
      (UInt32.add_ofNat_toNat_noWrap arr 3 (by decide) (by omega)) $$
        [$Hstate $Hword] with ⟨Hstate, Hword, %hfacts⟩
    imod ih (arr + 4) hfit' $$ [$Hstate $Hxs] with ⟨Hstate, Hxs, %hread⟩
    imodintro
    isplitl [Hstate]; iexact Hstate
    isplitl [Hword Hxs]
    · isplitl [Hword]; iexact Hword; iexact Hxs
    ipureintro
    unfold readWordArray
    rw [hfacts.1, hread]

/-! ## WAT decoder agreement -/

-- keep in sync with quicksort.wat
private def quicksortWat : String := "
(module
  (memory 1)
  (func (param i32 i32 i32) (result i32) (local i32 i32 i32 i32 i32)
    local.get 2
    i32.const 1
    i32.sub
    local.set 6
    local.get 0
    local.get 6
    i32.const 4
    i32.mul
    i32.add
    i32.load
    local.set 3
    local.get 1
    local.set 4
    local.get 1
    local.set 5
    block
      loop
        local.get 5
        local.get 6
        i32.lt_u
        i32.eqz
        br_if 1
        local.get 3
        local.get 0
        local.get 5
        i32.const 4
        i32.mul
        i32.add
        i32.load
        i32.lt_u
        if
        else
          local.get 0
          local.get 4
          i32.const 4
          i32.mul
          i32.add
          i32.load
          local.set 7
          local.get 0
          local.get 4
          i32.const 4
          i32.mul
          i32.add
          local.get 0
          local.get 5
          i32.const 4
          i32.mul
          i32.add
          i32.load
          i32.store
          local.get 0
          local.get 5
          i32.const 4
          i32.mul
          i32.add
          local.get 7
          i32.store
          local.get 4
          i32.const 1
          i32.add
          local.set 4
        end
        local.get 5
        i32.const 1
        i32.add
        local.set 5
        br 0
      end
    end
    local.get 0
    local.get 4
    i32.const 4
    i32.mul
    i32.add
    i32.load
    local.set 7
    local.get 0
    local.get 4
    i32.const 4
    i32.mul
    i32.add
    local.get 0
    local.get 6
    i32.const 4
    i32.mul
    i32.add
    i32.load
    i32.store
    local.get 0
    local.get 6
    i32.const 4
    i32.mul
    i32.add
    local.get 7
    i32.store
    local.get 4
    return)
  (func (param i32 i32 i32) (local i32)
    local.get 2
    local.get 1
    i32.sub
    i32.const 2
    i32.lt_u
    if
      return
    end
    local.get 0
    local.get 1
    local.get 2
    call 0
    local.set 3
    local.get 0
    local.get 1
    local.get 3
    call 1
    local.get 0
    local.get 3
    i32.const 1
    i32.add
    local.get 2
    call 1
    return))
"

private def quicksortModuleDecoded : Module :=
  match Wasm.Decoder.Wat.decode quicksortWat with
  | .ok m => m
  | .error _ => default

def runQuicksortDecoded (fuel : Nat) (arr : UInt32) (input : List UInt32) :
    Option (List UInt32) :=
  match SmallStep.initConfig
      { module := quicksortModuleDecoded, host := {} } 1
      (quicksortExampleStore arr input)
      (quicksortArguments arr input.length []) with
  | .error _ => none
  | .ok config =>
      match (SmallStep.runSteps fuel config).result with
      | .success _ store => some (readWordArray store.wasm.mem arr input.length)
      | _ => none

theorem quicksort_decoded_agrees :
    runQuicksortDecoded 15000 0 [5, 1, 4, 2, 3] =
    runQuicksortExample 15000 0 [5, 1, 4, 2, 3] := by
  native_decide

end Wasm.Examples.Quicksort
