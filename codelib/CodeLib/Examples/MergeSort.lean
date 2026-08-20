import CodeLib.SepLogic.SmallStepAdequacy
import Mathlib.Data.List.Sort

/-!
# Bottom-up merge sort

A handwritten Wasm implementation of iterative merge sort.  The public
contract owns a source array and an equally-sized disjoint scratch array.  On
return, the source is a sorted permutation of its original contents and both
arrays remain owned by the caller.
-/

namespace Wasm.Examples.MergeSort

open Wasm
open Iris Iris.ProgramLogic Language.Notation
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

/- Parameters: source, scratch, left, mid, right.
   Locals: i, j, k. -/
def mergeMainCondition : Program :=
  lessLocal 5 3 ++ lessLocal 6 4 ++ [.mul]

def mergeMainStep : Program :=
  loadAt 0 5 ++ loadAt 0 6 ++
    [.ltU, .iff 0 0
      (storeAt 1 7 (loadAt 0 5) ++ increment 5)
      (storeAt 1 7 (loadAt 0 6) ++ increment 6)] ++
    increment 7

def mergeLeftCondition : Program := lessLocal 5 3
def mergeLeftStep : Program :=
  storeAt 1 7 (loadAt 0 5) ++ increment 5 ++ increment 7

def mergeRightCondition : Program := lessLocal 6 4
def mergeRightStep : Program :=
  storeAt 1 7 (loadAt 0 6) ++ increment 6 ++ increment 7

def mergeCopyCondition : Program := lessLocal 7 4
def mergeCopyStep : Program :=
  storeAt 0 7 (loadAt 1 7) ++ increment 7

def mergeBody : Program :=
  [.localGet 2, .localSet 5,
   .localGet 3, .localSet 6,
   .localGet 2, .localSet 7] ++
  whileDo mergeMainCondition mergeMainStep ++
  whileDo mergeLeftCondition mergeLeftStep ++
  whileDo mergeRightCondition mergeRightStep ++
  [.localGet 2, .localSet 7] ++
  whileDo mergeCopyCondition mergeCopyStep ++
  [.ret]

def mergeFunction : Function :=
  { params := [.i32, .i32, .i32, .i32, .i32]
    locals := [.i32, .i32, .i32]
    body := mergeBody }

def mergeSortInnerCondition : Program := lessLocal 4 2

def mergeSortPrepare : Program :=
  [.localGet 4, .localGet 3, .add, .localSet 5,
   .localGet 5, .localGet 2, .ltU,
   .iff 0 0 [] [.localGet 2, .localSet 5],
   .localGet 4, .localGet 3, .const 2, .mul, .add, .localSet 6,
   .localGet 6, .localGet 2, .ltU,
   .iff 0 0 [] [.localGet 2, .localSet 6]]

def mergeSortCallAdvance (mergeIndex : Nat) : Program :=
  [.localGet 0, .localGet 1, .localGet 4, .localGet 5, .localGet 6,
   .call mergeIndex,
   .localGet 4, .localGet 3, .const 2, .mul, .add, .localSet 4]

def mergeSortInnerStep (mergeIndex : Nat) : Program :=
  mergeSortPrepare ++ mergeSortCallAdvance mergeIndex

def mergeSortOuterCondition : Program := lessLocal 3 2

def mergeSortOuterStep (mergeIndex : Nat) : Program :=
  [.const 0, .localSet 4] ++
  whileDo mergeSortInnerCondition (mergeSortInnerStep mergeIndex) ++
  [.localGet 3, .const 2, .mul, .localSet 3]

/- Parameters: source, scratch, length.
   Locals: width, left, mid, right. -/
def mergeSortBody (mergeIndex : Nat) : Program :=
  [.const 1, .localSet 3] ++
  whileDo mergeSortOuterCondition (mergeSortOuterStep mergeIndex) ++
  [.ret]

def mergeSortFunction (mergeIndex : Nat) : Function :=
  { params := [.i32, .i32, .i32]
    locals := [.i32, .i32, .i32, .i32]
    body := mergeSortBody mergeIndex }

def mergeSortModule : Module :=
  { funcs := [mergeSortFunction 1, mergeFunction]
    memory := some { pagesMin := 1 } }

/-! ## Public specification -/

def Sorted (values : List UInt32) : Prop :=
  values.Pairwise (· ≤ ·)

def SortedPermutation (input output : List UInt32) : Prop :=
  Sorted output ∧ List.Perm input output

theorem SortedPermutation.sorted
    {input output : List UInt32}
    (h : SortedPermutation input output) : Sorted output := h.1

theorem SortedPermutation.perm
    {input output : List UInt32}
    (h : SortedPermutation input output) : List.Perm input output := h.2

theorem SortedPermutation.length_eq
    {input output : List UInt32}
    (h : SortedPermutation input output) :
    output.length = input.length := h.perm.length_eq.symm

def referenceSort (values : List UInt32) : List UInt32 :=
  values.mergeSort fun a b => decide (a ≤ b)

theorem sorted_referenceSort (values : List UInt32) :
    Sorted (referenceSort values) := by
  unfold Sorted referenceSort
  simpa only [decide_eq_true_eq] using
    List.pairwise_mergeSort
      (le := fun a b : UInt32 => decide (a ≤ b))
      (by
        intro a b c hab hbc
        simp only [decide_eq_true_eq] at hab hbc ⊢
        change a.toNat ≤ b.toNat at hab
        change b.toNat ≤ c.toNat at hbc
        change a.toNat ≤ c.toNat
        exact Nat.le_trans hab hbc)
      (by
        intro a b
        simp only [decide_eq_true_eq, Bool.or_eq_true]
        exact UInt32.le_total a b)
      values

theorem perm_referenceSort (values : List UInt32) :
    List.Perm values (referenceSort values) :=
  (List.mergeSort_perm values _).symm

theorem sortedPermutation_referenceSort (values : List UInt32) :
    SortedPermutation values (referenceSort values) :=
  ⟨sorted_referenceSort values, perm_referenceSort values⟩

def arrayByteRange (base : UInt32) (length : Nat) : Nat × Nat :=
  (base.toNat, base.toNat + 4 * length)

def ValidLayout (source temporary : UInt32) (length : Nat) : Prop :=
  let sourceRange := arrayByteRange source length
  let temporaryRange := arrayByteRange temporary length
  sourceRange.2 ≤ UInt32.size ∧
  temporaryRange.2 ≤ UInt32.size ∧
  (sourceRange.2 ≤ temporaryRange.1 ∨
    temporaryRange.2 ≤ sourceRange.1)

def mergeSortPre [WasmHeapGS α]
    (source temporary : UInt32)
    (input scratch : List UInt32) : IProp (WasmHeapGF α) :=
  iprop% arrayAt 0 source input ∗ arrayAt 0 temporary scratch ∗
    ⌜scratch.length = input.length⌝ ∗
    ⌜ValidLayout source temporary input.length⌝

def mergeSortPost [WasmHeapGS α]
    (source temporary : UInt32)
    (input : List UInt32) : IProp (WasmHeapGF α) :=
  iprop% ∃ output scratch : List UInt32,
    ⌜SortedPermutation input output⌝ ∗
    ⌜scratch.length = input.length⌝ ∗
    arrayAt 0 source output ∗ arrayAt 0 temporary scratch

def mergeSortArguments
    (source temporary : UInt32) (length : Nat)
    (stack : List Value) : List Value :=
  .i32 (UInt32.ofNat length) :: .i32 temporary :: .i32 source :: stack

def mergePre [WasmHeapGS α]
    (source temporary : UInt32) (input scratch : List UInt32)
    (left mid right : Nat) : IProp (WasmHeapGF α) :=
  iprop% arrayAt 0 source input ∗ arrayAt 0 temporary scratch ∗
    ⌜scratch.length = input.length⌝ ∗
    ⌜ValidLayout source temporary input.length⌝ ∗
    ⌜left ≤ mid ∧ mid ≤ right ∧ right ≤ input.length⌝

def segment (values : List UInt32) (start stop : Nat) : List UInt32 :=
  (values.drop start).take (stop - start)

inductive MergeRel : List UInt32 → List UInt32 → List UInt32 → Prop where
  | leftNil (right) : MergeRel [] right right
  | rightNil (left) : MergeRel left [] left
  | takeLeft {x y xs ys output}
      (hxy : x < y) (tail : MergeRel xs (y :: ys) output) :
      MergeRel (x :: xs) (y :: ys) (x :: output)
  | takeRight {x y xs ys output}
      (hxy : ¬x < y) (tail : MergeRel (x :: xs) ys output) :
      MergeRel (x :: xs) (y :: ys) (y :: output)

def MergeRange (input output : List UInt32)
    (left mid right : Nat) : Prop :=
  left ≤ mid ∧ mid ≤ right ∧ right ≤ input.length ∧
  output.length = input.length ∧
  output.take left = input.take left ∧
  output.drop right = input.drop right ∧
  MergeRel (segment input left mid) (segment input mid right)
    (segment output left right)

theorem MergeRange.bounds
    {input output : List UInt32} {left mid right : Nat}
    (h : MergeRange input output left mid right) :
    left ≤ mid ∧ mid ≤ right ∧ right ≤ input.length :=
  ⟨h.1, h.2.1, h.2.2.1⟩

theorem MergeRange.length_eq
    {input output : List UInt32} {left mid right : Nat}
    (h : MergeRange input output left mid right) :
    output.length = input.length := h.2.2.2.1

def mergePost [WasmHeapGS α]
    (source temporary : UInt32) (input : List UInt32)
    (left mid right : Nat) : IProp (WasmHeapGF α) :=
  iprop% ∃ output scratch : List UInt32,
    ⌜MergeRange input output left mid right⌝ ∗
    ⌜scratch.length = input.length⌝ ∗
    arrayAt 0 source output ∗ arrayAt 0 temporary scratch

/-! ## Executable regressions

These checks execute the same handwritten module used by the proofs.  They are
not a second implementation of merge sort: `runSteps` iterates the
authoritative small-step function. -/

def writeWordArray : Mem → UInt32 → List UInt32 → Mem
  | memory, _, [] => memory
  | memory, address, value :: values =>
      writeWordArray (memory.write32 address value) (address + 4) values

def readWordArray : Mem → UInt32 → Nat → List UInt32
  | _, _, 0 => []
  | memory, address, count + 1 =>
      memory.read32 address ::
        readWordArray memory (address + 4) count

def mergeSortExampleStore
    (source temporary : UInt32)
    (input scratch : List UInt32) : Store Unit :=
  let initial := mergeSortModule.initialStore (α := Unit)
  { initial with
    mem :=
      writeWordArray
        (writeWordArray initial.mem source input)
        temporary scratch }

def runMergeSortExample
    (fuel : Nat) (source temporary : UInt32)
    (input scratch : List UInt32) : Option (List UInt32) :=
  match SmallStep.initConfig
      { module := mergeSortModule, host := {} } 0
      (mergeSortExampleStore source temporary input scratch)
      (mergeSortArguments source temporary input.length []) with
  | .error _ => none
  | .ok config =>
      match (SmallStep.runSteps fuel config).result with
      | .success _ store =>
          some (readWordArray store.wasm.mem source input.length)
      | _ => none

theorem mergeSort_exec_empty :
    runMergeSortExample 100 0 64 [] [] = some [] := by
  native_decide

theorem mergeSort_exec_five :
    runMergeSortExample 10000 0 64
      [5, 1, 4, 2, 3] [0, 0, 0, 0, 0] =
        some [1, 2, 3, 4, 5] := by
  native_decide

theorem mergeSort_exec_duplicates :
    runMergeSortExample 12000 0 128
      [4, 1, 4, 2, 1, 3] [0, 0, 0, 0, 0, 0] =
        some [1, 1, 2, 3, 4, 4] := by
  native_decide

end Wasm.Examples.MergeSort
