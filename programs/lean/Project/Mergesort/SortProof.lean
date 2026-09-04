import Project.Mergesort.Spec
import CodeLib.Examples.MergeSort.TotalProof
import CodeLib.Examples.MergeSort.Laws
import CodeLib.RustStd.Region
import CodeLib.SepLogic.SmallStepTotalLifting

/-!
# Total Iris contract for the generated recursive merge-sort body

The public export calls absolute function index 5 (`func2Def`) with parameters
`source`, `length`, `scratch`, and `scratchLength`.  This file develops that
internal contract independently of the stream/allocator wrapper.
-/

namespace Project.Mergesort.SortProof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep

/- The generated-body proof is independent of how terminal expressions are
observed.  Install the canonical language and Iris instances for the selected
`TerminalView` so the same proof supports both ordinary result-valued WP and
the outcome-valued contracts used by the public formalization. -/
local instance (priority := high) sortTerminalLanguage
    {alpha Terminal : Type} [TerminalView alpha Terminal] :
    Language (Expr alpha) (MachineStore alpha) StepKind Terminal :=
  TerminalView.canonicalLanguage

local instance (priority := high) sortTerminalIrisGS
    {hlc : outParam HasLC} {alpha Terminal : Type}
    [WasmSmallStepGS hlc alpha] [TerminalView alpha Terminal] :
    @IrisGS_gen hlc (Expr alpha) Terminal (MachineStore alpha) StepKind
      sortTerminalLanguage (WasmHeapGF alpha) where
  numLatersPerStep _ := 0
  forkPost _ := iprop(True)
  stateInterp_mono _ _ _ _ := by iintro $

set_option maxHeartbeats 4000000

/-- Terminal-polymorphic form of the well-founded loop-family rule used by the
generated merge loops.  The CodeLib example predates outcome-valued terminals
and fixes its postcondition to `List Value`; keeping the rule local avoids
changing that example while allowing this body proof to be reused by the
authoritative observable-outcome contracts. -/
theorem twp_loop_wf_family_from_terminal
    [WasmSmallStepGS hlc α]
    {Terminal : Type} [TerminalView α Terminal]
    {s : Stuckness} {E : CoPset}
    {Φ : Terminal → IProp (WasmHeapGF α)}
    {ι : Type} (measure : ι → Nat)
    (locals : ι → Locals) (I : ι → IProp (WasmHeapGF α))
    (initial : ι) (initialLocals : Locals)
    {paramArity resultArity arity : Nat}
    {body code : Program} {remainder belowStack : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (hinitial : locals initial = initialLocals)
    (hbelow : belowStack = (locals initial).values.drop paramArity)
    (body_closes : ∀ i,
      ⊢@{IProp (WasmHeapGF α)} (iprop%
        (∀ (j : ι), ⌜measure j < measure i⌝ -∗ I j -∗
          WP (loopBodyExpr (α := α) (locals j)
            paramArity resultArity arity body code remainder belowStack
            controls calls) @ s; E [{ Φ }]) -∗
        I i -∗
          WP (loopBodyExpr (α := α) (locals i)
            paramArity resultArity arity body code remainder belowStack
            controls calls) @ s; E [{ Φ }])) :
    I initial ⊢
      WP (.running
        ⟨initialLocals, .loop paramArity resultArity body :: code,
          arity, remainder, controls, calls⟩ : Expr α)
        @ s; E [{ Φ }] := by
  have closes : ∀ i,
      I i ⊢
        WP (loopBodyExpr (α := α) (locals i)
          paramArity resultArity arity body code remainder belowStack
          controls calls) @ s; E [{ Φ }] := by
    intro current
    induction hmeasure : measure current using Nat.strongRecOn
        generalizing current with
    | ind n ih =>
      subst n
      iintro HI
      iapply body_closes current
      · iintro %j %hji Hj
        ihave Hih := ih (measure j) hji j rfl $$ Hj
        iexact Hih
      · iexact HI
  simp only [loopBodyExpr] at closes
  subst initialLocals
  iintro HI
  iapply twp_loop (Terminal := Terminal) (α := α)
  rw [← hbelow]
  ihave Hbody := closes initial $$ HI
  iexact Hbody

/-! ## Pure merge relation used by the generated loop

The handwritten CodeLib example chooses the right element when two heads are
equal.  Rust's `left[i] <= right[j]` chooses the left one instead, so the
machine invariant below uses the corresponding relation explicitly.
-/

inductive MergeLE : List UInt32 → List UInt32 → List UInt32 → Prop where
  | leftNil (right) : MergeLE [] right right
  | rightNil (left) : MergeLE left [] left
  | takeLeft {x y xs ys output}
      (hxy : x ≤ y) (tail : MergeLE xs (y :: ys) output) :
      MergeLE (x :: xs) (y :: ys) (x :: output)
  | takeRight {x y xs ys output}
      (hxy : ¬x ≤ y) (tail : MergeLE (x :: xs) ys output) :
      MergeLE (x :: xs) (y :: ys) (y :: output)

theorem perm_of_mergeLE {left right output}
    (hmerge : MergeLE left right output) :
    List.Perm (left ++ right) output := by
  induction hmerge with
  | leftNil => simp
  | rightNil => simp
  | takeLeft hxy tail ih =>
      simp only [List.cons_append]; exact List.Perm.cons _ ih
  | takeRight hxy tail ih =>
      exact (List.Perm.cons _ List.perm_middle).trans
        ((List.Perm.swap _ _ _).symm.trans (List.Perm.cons _ ih))

private theorem u32_le_trans {a b c : UInt32}
    (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  change a.toNat ≤ b.toNat at hab
  change b.toNat ≤ c.toNat at hbc
  change a.toNat ≤ c.toNat
  omega

private theorem u32_le_of_not_le {a b : UInt32} (h : ¬a ≤ b) : b ≤ a := by
  change ¬a.toNat ≤ b.toNat at h
  change b.toNat ≤ a.toNat
  omega

theorem sorted_of_mergeLE {left right output}
    (hmerge : MergeLE left right output)
    (hleft : Wasm.Examples.MergeSort.Sorted left)
    (hright : Wasm.Examples.MergeSort.Sorted right) :
    Wasm.Examples.MergeSort.Sorted output := by
  induction hmerge with
  | leftNil => exact hright
  | rightNil => exact hleft
  | @takeLeft x y xs ys output hxy tail ih =>
      have hxs : Wasm.Examples.MergeSort.Sorted xs := hleft.tail
      have hyr : Wasm.Examples.MergeSort.Sorted (y :: ys) := hright
      simp only [Wasm.Examples.MergeSort.Sorted, List.pairwise_cons] at hleft hright ⊢
      constructor
      · intro z hz
        have hz' : z ∈ xs ++ y :: ys :=
          (perm_of_mergeLE tail).mem_iff.mpr hz
        simp only [List.mem_append, List.mem_cons] at hz'
        rcases hz' with hxs | rfl | hys
        · exact hleft.1 z hxs
        · exact hxy
        · exact u32_le_trans hxy (hright.1 z hys)
      · exact ih hxs hyr
  | @takeRight x y xs ys output hxy tail ih =>
      have hxl : Wasm.Examples.MergeSort.Sorted (x :: xs) := hleft
      have hys : Wasm.Examples.MergeSort.Sorted ys := hright.tail
      simp only [Wasm.Examples.MergeSort.Sorted, List.pairwise_cons] at hleft hright ⊢
      constructor
      · intro z hz
        have hz' : z ∈ x :: xs ++ ys :=
          (perm_of_mergeLE tail).mem_iff.mpr hz
        simp only [List.cons_append, List.mem_cons, List.mem_append] at hz'
        rcases hz' with rfl | hxs | hys
        · exact u32_le_of_not_le hxy
        · exact u32_le_trans (u32_le_of_not_le hxy) (hleft.1 z hxs)
        · exact hright.1 z hys
      · exact ih hxl hys

theorem sortedPermutation_of_mergeLE {left right output}
    (hmerge : MergeLE left right output)
    (hleft : Wasm.Examples.MergeSort.Sorted left)
    (hright : Wasm.Examples.MergeSort.Sorted right) :
    Wasm.Examples.MergeSort.SortedPermutation (left ++ right) output :=
  ⟨sorted_of_mergeLE hmerge hleft hright, perm_of_mergeLE hmerge⟩

/-- A continuation-form invariant for the prefix already emitted by the
generated merge loop. -/
def MergeProgress (left right emitted remainingLeft remainingRight :
    List UInt32) : Prop :=
  ∀ tail, MergeLE remainingLeft remainingRight tail →
    MergeLE left right (emitted ++ tail)

@[simp] theorem mergeProgress_start (left right : List UInt32) :
    MergeProgress left right [] left right := by
  intro tail htail
  simpa using htail

theorem MergeProgress.takeLeft
    {left right emitted xs ys : List UInt32} {x y : UInt32}
    (hprogress : MergeProgress left right emitted (x :: xs) (y :: ys))
    (hxy : x ≤ y) :
    MergeProgress left right (emitted ++ [x]) xs (y :: ys) := by
  intro tail htail
  simpa [List.append_assoc] using hprogress (x :: tail) (.takeLeft hxy htail)

theorem MergeProgress.takeRight
    {left right emitted xs ys : List UInt32} {x y : UInt32}
    (hprogress : MergeProgress left right emitted (x :: xs) (y :: ys))
    (hxy : ¬x ≤ y) :
    MergeProgress left right (emitted ++ [y]) (x :: xs) ys := by
  intro tail htail
  simpa [List.append_assoc] using hprogress (y :: tail) (.takeRight hxy htail)

theorem MergeProgress.finishLeft
    {left right emitted remaining : List UInt32}
    (hprogress : MergeProgress left right emitted remaining []) :
    MergeLE left right (emitted ++ remaining) :=
  hprogress remaining (.rightNil remaining)

theorem MergeProgress.finishRight
    {left right emitted remaining : List UInt32}
    (hprogress : MergeProgress left right emitted [] remaining) :
    MergeLE left right (emitted ++ remaining) :=
  hprogress remaining (.leftNil remaining)

private theorem mergeLE_right_nil_eq {left output : List UInt32}
    (h : MergeLE left [] output) : output = left := by
  cases h <;> simp_all

private theorem mergeLE_left_nil_eq {right output : List UInt32}
    (h : MergeLE [] right output) : output = right := by
  cases h <;> simp_all

theorem MergeProgress.takeRemainingLeft
    {left right emitted xs : List UInt32} {x : UInt32}
    (hprogress : MergeProgress left right emitted (x :: xs) []) :
    MergeProgress left right (emitted ++ [x]) xs [] := by
  intro tail htail
  have htailEq : tail = xs := mergeLE_right_nil_eq htail
  subst tail
  simpa [List.append_assoc] using
    hprogress (x :: xs) (.rightNil (x :: xs))

theorem MergeProgress.takeRemainingRight
    {left right emitted ys : List UInt32} {y : UInt32}
    (hprogress : MergeProgress left right emitted [] (y :: ys)) :
    MergeProgress left right (emitted ++ [y]) [] ys := by
  intro tail htail
  have htailEq : tail = ys := mergeLE_left_nil_eq htail
  subst tail
  simpa [List.append_assoc] using
    hprogress (y :: ys) (.leftNil (y :: ys))

/-- Pure state of the generated main merge loop.  Indices are absolute in the
source array; `k` is the number of words already written to scratch. -/
def MergeLoopInvariant
    (input scratchValues : List UInt32) (mid i j k : Nat)
    (emitted : List UInt32) : Prop :=
  0 ≤ i ∧ i ≤ mid ∧ mid ≤ j ∧ j ≤ input.length ∧
  scratchValues.length = input.length ∧
  k = emitted.length ∧
  emitted.length = i + (j - mid) ∧
  scratchValues.take k = emitted ∧
  MergeProgress
    (Wasm.Examples.MergeSort.segment input 0 mid)
    (Wasm.Examples.MergeSort.segment input mid input.length)
    emitted
    (Wasm.Examples.MergeSort.segment input i mid)
    (Wasm.Examples.MergeSort.segment input j input.length)

theorem mergeLoopInvariant_start
    {input scratchValues : List UInt32} {mid : Nat}
    (hmid : mid ≤ input.length)
    (hlength : scratchValues.length = input.length) :
    MergeLoopInvariant input scratchValues mid 0 mid 0 [] := by
  simp [MergeLoopInvariant, hmid, hlength, mergeProgress_start,
    Wasm.Examples.MergeSort.segment]

theorem MergeLoopInvariant.k_lt
    {input scratchValues : List UInt32} {mid i j k : Nat}
    {emitted : List UInt32}
    (h : MergeLoopInvariant input scratchValues mid i j k emitted)
    (hi : i < mid) (hj : j < input.length) :
    k < input.length := by
  unfold MergeLoopInvariant at h
  omega

theorem MergeLoopInvariant.takeLeft
    {input scratchValues : List UInt32} {mid i j k : Nat}
    {emitted : List UInt32} {x y : UInt32}
    (h : MergeLoopInvariant input scratchValues mid i j k emitted)
    (hi : i < mid) (hj : j < input.length)
    (hx : input[i]? = some x) (hy : input[j]? = some y)
    (hxy : x ≤ y) :
    MergeLoopInvariant input (scratchValues.set k x)
      mid (i + 1) j (k + 1) (emitted ++ [x]) := by
  unfold MergeLoopInvariant at h ⊢
  rcases h with
    ⟨hzero, him, hmj, hjr, hlength, hk, hemitted, htake, hprogress⟩
  have hklen : k < scratchValues.length := by rw [hlength]; omega
  have hleftSegment :
      Wasm.Examples.MergeSort.segment input i mid =
        x :: Wasm.Examples.MergeSort.segment input (i + 1) mid :=
    Wasm.Examples.MergeSort.segment_cons hi (by omega) hx
  have hrightSegment :
      Wasm.Examples.MergeSort.segment input j input.length =
        y :: Wasm.Examples.MergeSort.segment input (j + 1) input.length :=
    Wasm.Examples.MergeSort.segment_cons hj (by omega) hy
  rw [hleftSegment, hrightSegment] at hprogress
  refine ⟨by omega, by omega, hmj, hjr, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hlength]
  · simp; omega
  · simp; omega
  · rw [Wasm.Examples.MergeSort.take_set_succ hklen, htake]
  · rw [hrightSegment]; exact hprogress.takeLeft hxy

theorem MergeLoopInvariant.takeRight
    {input scratchValues : List UInt32} {mid i j k : Nat}
    {emitted : List UInt32} {x y : UInt32}
    (h : MergeLoopInvariant input scratchValues mid i j k emitted)
    (hi : i < mid) (hj : j < input.length)
    (hx : input[i]? = some x) (hy : input[j]? = some y)
    (hxy : ¬x ≤ y) :
    MergeLoopInvariant input (scratchValues.set k y)
      mid i (j + 1) (k + 1) (emitted ++ [y]) := by
  unfold MergeLoopInvariant at h ⊢
  rcases h with
    ⟨hzero, him, hmj, hjr, hlength, hk, hemitted, htake, hprogress⟩
  have hklen : k < scratchValues.length := by rw [hlength]; omega
  have hleftSegment :
      Wasm.Examples.MergeSort.segment input i mid =
        x :: Wasm.Examples.MergeSort.segment input (i + 1) mid :=
    Wasm.Examples.MergeSort.segment_cons hi (by omega) hx
  have hrightSegment :
      Wasm.Examples.MergeSort.segment input j input.length =
        y :: Wasm.Examples.MergeSort.segment input (j + 1) input.length :=
    Wasm.Examples.MergeSort.segment_cons hj (by omega) hy
  rw [hleftSegment, hrightSegment] at hprogress
  refine ⟨hzero, him, by omega, by omega, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hlength]
  · simp; omega
  · simp; omega
  · rw [Wasm.Examples.MergeSort.take_set_succ hklen, htake]
  · rw [hleftSegment]; exact hprogress.takeRight hxy

theorem MergeLoopInvariant.takeRemainingLeft
    {input scratchValues : List UInt32} {mid i k : Nat}
    {emitted : List UInt32} {x : UInt32}
    (h : MergeLoopInvariant input scratchValues mid i input.length k emitted)
    (hi : i < mid) (hx : input[i]? = some x) :
    MergeLoopInvariant input (scratchValues.set k x)
      mid (i + 1) input.length (k + 1) (emitted ++ [x]) := by
  unfold MergeLoopInvariant at h ⊢
  rcases h with
    ⟨hzero, him, hmj, hjr, hlength, hk, hemitted, htake, hprogress⟩
  have hklen : k < scratchValues.length := by rw [hlength]; omega
  have hleftSegment :
      Wasm.Examples.MergeSort.segment input i mid =
        x :: Wasm.Examples.MergeSort.segment input (i + 1) mid :=
    Wasm.Examples.MergeSort.segment_cons hi (by omega) hx
  have hrightSegment :
      Wasm.Examples.MergeSort.segment input input.length input.length = [] := by
    simp [Wasm.Examples.MergeSort.segment]
  rw [hleftSegment, hrightSegment] at hprogress
  refine ⟨by omega, by omega, hmj, hjr, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hlength]
  · simp; omega
  · simp; omega
  · rw [Wasm.Examples.MergeSort.take_set_succ hklen, htake]
  · rw [hrightSegment]; exact hprogress.takeRemainingLeft

theorem MergeLoopInvariant.takeRemainingRight
    {input scratchValues : List UInt32} {mid j k : Nat}
    {emitted : List UInt32} {y : UInt32}
    (h : MergeLoopInvariant input scratchValues mid mid j k emitted)
    (hj : j < input.length) (hy : input[j]? = some y) :
    MergeLoopInvariant input (scratchValues.set k y)
      mid mid (j + 1) (k + 1) (emitted ++ [y]) := by
  unfold MergeLoopInvariant at h ⊢
  rcases h with
    ⟨hzero, him, hmj, hjr, hlength, hk, hemitted, htake, hprogress⟩
  have hklen : k < scratchValues.length := by rw [hlength]; omega
  have hrightSegment :
      Wasm.Examples.MergeSort.segment input j input.length =
        y :: Wasm.Examples.MergeSort.segment input (j + 1) input.length :=
    Wasm.Examples.MergeSort.segment_cons hj (by omega) hy
  have hleftSegment :
      Wasm.Examples.MergeSort.segment input mid mid = [] := by
    simp [Wasm.Examples.MergeSort.segment]
  rw [hleftSegment, hrightSegment] at hprogress
  refine ⟨hzero, him, by omega, by omega, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hlength]
  · simp; omega
  · simp; omega
  · rw [Wasm.Examples.MergeSort.take_set_succ hklen, htake]
  · rw [hleftSegment]; exact hprogress.takeRemainingRight

theorem MergeLoopInvariant.finished
    {input scratchValues : List UInt32} {mid k : Nat}
    {emitted : List UInt32}
    (h : MergeLoopInvariant input scratchValues mid mid input.length k emitted) :
    k = input.length ∧ scratchValues = emitted ∧
    MergeLE
      (Wasm.Examples.MergeSort.segment input 0 mid)
      (Wasm.Examples.MergeSort.segment input mid input.length)
      emitted := by
  unfold MergeLoopInvariant at h
  rcases h with
    ⟨_, _, _, _, hlength, hk, hemitted, htake, hprogress⟩
  have hkLength : k = input.length := by omega
  have hscratch : scratchValues = emitted := by
    calc
      scratchValues = scratchValues.take scratchValues.length :=
        List.take_length.symm
      _ = scratchValues.take input.length := by rw [hlength]
      _ = scratchValues.take k := by rw [hkLength]
      _ = emitted := htake
  have hleft : Wasm.Examples.MergeSort.segment input mid mid = [] := by
    simp [Wasm.Examples.MergeSort.segment]
  have hright :
      Wasm.Examples.MergeSort.segment input input.length input.length = [] := by
    simp [Wasm.Examples.MergeSort.segment]
  rw [hleft, hright] at hprogress
  exact ⟨hkLength, hscratch, by simpa using hprogress [] (.leftNil [])⟩

/-- The Wasm operand-stack order for a call to generated function index 5. -/
def sortArguments (source scratch : UInt32)
    (length scratchLength : Nat) (stack : List Value) : List Value :=
  .i32 (UInt32.ofNat scratchLength) :: .i32 scratch ::
    .i32 (UInt32.ofNat length) :: .i32 source :: stack

/-- Named view of the four parameters, nine compiler locals, and operand
stack used by generated function 5. -/
def sortLocals (source scratch length scratchLength : UInt32)
    (v4 v5 v6 v7 v8 v9 v10 v11 v12 : UInt32)
    (stack : List Value) : Locals :=
  ⟨[.i32 source, .i32 length, .i32 scratch, .i32 scratchLength],
    [.i32 v4, .i32 v5, .i32 v6, .i32 v7, .i32 v8,
      .i32 v9, .i32 v10, .i32 v11, .i32 v12], stack⟩

def wordBytes (value : UInt32) : List UInt8 :=
  [u32Byte value 0, u32Byte value 1, u32Byte value 2, u32Byte value 3]

def arrayBytes (values : List UInt32) : List UInt8 :=
  values.flatMap wordBytes

@[simp] theorem wordBytes_length (value : UInt32) :
    (wordBytes value).length = 4 := by
  rfl

@[simp] theorem arrayBytes_length (values : List UInt32) :
    (arrayBytes values).length = 4 * values.length := by
  simp [arrayBytes, Nat.mul_comm]

theorem arrayAt_as_bytes [WasmHeapGS α] (memId : Nat) (ptr : UInt32)
    (values : List UInt32) :
    arrayAt memId ptr values ⊣⊢ pointsToBytes memId ptr (arrayBytes values) := by
  induction values generalizing ptr with
  | nil => exact .rfl
  | cons value rest ih =>
      simp only [arrayAt, arrayBytes, List.flatMap_cons]; exact (BI.sep_congr
          (pointsTo_u32_as_bytes memId ptr value)
          (by simpa [wordBytes] using ih (ptr + 4))).trans
        (pointsToBytes_append memId ptr (wordBytes value)
          (arrayBytes rest)).symm

private theorem validLayout_prefix
    {source scratch : UInt32} {length mid : Nat}
    (hlayout : Wasm.Examples.MergeSort.ValidLayout source scratch length)
    (hmid : mid ≤ length) :
    Wasm.Examples.MergeSort.ValidLayout source scratch mid := by
  unfold Wasm.Examples.MergeSort.ValidLayout
    Wasm.Examples.MergeSort.arrayByteRange at hlayout ⊢
  rcases hlayout with ⟨hsource, hscratch, hdisjoint⟩
  constructor
  · omega
  constructor
  · omega
  rcases hdisjoint with h | h
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

private theorem validLayout_suffix
    {source scratch : UInt32} {length mid : Nat}
    (hlayout : Wasm.Examples.MergeSort.ValidLayout source scratch length)
    (hmid : mid < length) :
    Wasm.Examples.MergeSort.ValidLayout
      (source + 4 * UInt32.ofNat mid)
      (scratch + 4 * UInt32.ofNat mid) (length - mid) := by
  have hsourceAddress :
      (source + 4 * UInt32.ofNat mid).toNat = source.toNat + 4 * mid := by
    simpa [UInt32.mul_comm] using
      Wasm.Examples.MergeSort.arrayAddress_toNat source
        hlayout.source_fits hmid
  have hscratchAddress :
      (scratch + 4 * UInt32.ofNat mid).toNat = scratch.toNat + 4 * mid := by
    simpa [UInt32.mul_comm] using
      Wasm.Examples.MergeSort.arrayAddress_toNat scratch
        hlayout.temporary_fits hmid
  unfold Wasm.Examples.MergeSort.ValidLayout
    Wasm.Examples.MergeSort.arrayByteRange at hlayout ⊢
  rw [hsourceAddress, hscratchAddress]
  rcases hlayout with ⟨hsource, hscratch, hdisjoint⟩
  constructor
  · omega
  constructor
  · omega
  rcases hdisjoint with h | h
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

private theorem mul4_ofNat_toNat {n : Nat}
    (h : 4 * n < UInt32.size) :
    (4 * UInt32.ofNat n : UInt32).toNat = 4 * n := by
  rw [show (4 : UInt32) = UInt32.ofNat 4 from rfl,
    Wasm.Examples.MergeSort.u32_ofNat_mul h,
    UInt32.toNat_ofNat_of_lt' h]

private theorem ofNat_shr_one {n : Nat} (h : n < UInt32.size) :
    UInt32.ofNat n >>> (1 : UInt32) = UInt32.ofNat (n / 2) := by
  apply UInt32.toNat.inj
  rw [UInt32.toNat_shiftRight,
    UInt32.toNat_ofNat_of_lt' h,
    UInt32.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt (Nat.div_le_self n 2) h)]
  rw [Nat.shiftRight_eq_div_pow]
  change n / 2 ^ 1 = n / 2
  simp

private theorem u32_ofNat_sub {a b : Nat} (hle : b ≤ a)
    (ha : a < UInt32.size) :
    UInt32.ofNat a - UInt32.ofNat b = UInt32.ofNat (a - b) := by
  apply UInt32.toNat.inj
  rw [UInt32.toNat_sub,
    UInt32.toNat_ofNat_of_lt' ha,
    UInt32.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt hle ha),
    UInt32.toNat_ofNat_of_lt'
      (Nat.lt_of_le_of_lt (Nat.sub_le a b) ha)]
  have htoNatLt := (UInt32.ofNat a).toNat_lt
  rw [UInt32.toNat_ofNat_of_lt' ha] at htoNatLt; omega

/-- Reducible projections keep compiler-created block bodies named without
copying hundreds of generated instructions into this proof file. -/
def blockBodyAt (program : Program) (index : Nat) : Program :=
  match program[index]? with
  | some (.block _ _ body _ _) => body
  | _ => []

def loopBodyAt (program : Program) (index : Nat) : Program :=
  match program[index]? with
  | some (.loop _ _ body _ _) => body
  | _ => []

def sortBlock1 : Program := blockBodyAt Project.Mergesort.func2 0
def sortBlock2 : Program := blockBodyAt sortBlock1 0
def sortBlock3 : Program := blockBodyAt sortBlock2 0
def sortBlock4 : Program := blockBodyAt sortBlock3 0
def sortRecursiveGuard : Program := blockBodyAt sortBlock4 4
def sortRecursiveBody : Program := blockBodyAt sortRecursiveGuard 0
def mergeMainLoopBody : Program := loopBodyAt sortRecursiveBody 38
def mergeMainOuterBody : Program := blockBodyAt mergeMainLoopBody 0
def mergeMainChoiceBody : Program := blockBodyAt mergeMainOuterBody 0
def mergeMainCompareBody : Program := blockBodyAt mergeMainChoiceBody 0
def mergeMainLeftBody : Program := blockBodyAt mergeMainChoiceBody 1
def mergeLeftRemainderBody : Program := blockBodyAt sortBlock4 5
def mergeRightRemainderBody : Program := blockBodyAt sortBlock4 6
def mergeLeftLoopBody : Program := loopBodyAt mergeLeftRemainderBody 23
def mergeRightLoopBody : Program := loopBodyAt mergeRightRemainderBody 33

def emptyBlockFrame (body continuation : Program) : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body, continuation, belowStack := [] }

def emptyLoopFrame (body continuation : Program) : ControlFrame :=
  { kind := .loop, paramArity := 0, resultArity := 0,
    body, continuation, belowStack := [] }

def sortRecursiveBodyFrame : ControlFrame :=
  emptyBlockFrame sortRecursiveBody (sortRecursiveGuard.drop 1)

def sortRecursiveGuardFrame : ControlFrame :=
  emptyBlockFrame sortRecursiveGuard (sortBlock4.drop 5)

def sortBlock4Frame : ControlFrame :=
  emptyBlockFrame sortBlock4 (sortBlock3.drop 1)

def sortBlock3Frame : ControlFrame :=
  emptyBlockFrame sortBlock3 (sortBlock2.drop 1)

def sortBlock2Frame : ControlFrame :=
  emptyBlockFrame sortBlock2 (sortBlock1.drop 1)

def sortBlock1Frame : ControlFrame :=
  emptyBlockFrame sortBlock1 (Project.Mergesort.func2.drop 1)

private theorem right_slot_address (source : UInt32) {mid j : Nat}
    (hmj : mid ≤ j) :
    (UInt32.ofNat (j - mid) <<< (2 % 32 : UInt32)) +
        (source + 4 * UInt32.ofNat mid) =
      source + 4 * UInt32.ofNat j := by
  rw [MemRegion.shl2_eq_mul4]
  have hj : j = mid + (j - mid) := by omega
  conv_rhs => rw [hj, UInt32.ofNat_add, UInt32.mul_add]
  ac_rfl

private theorem next_slot_address (base : UInt32) (k : Nat) :
    base + 4 * UInt32.ofNat k + 4 =
      base + 4 * UInt32.ofNat (k + 1) := by
  rw [UInt32.ofNat_add, UInt32.mul_add]
  simp
  ac_rfl

private theorem u32_sub_eq_neg_iff_sum_eq {a b r : Nat}
    (hsum : a + r < UInt32.size) (hb : b < UInt32.size) :
    UInt32.ofNat a - UInt32.ofNat b = 0 - UInt32.ofNat r ↔
      a + r = b := by
  constructor
  · intro h
    have hu :
        UInt32.ofNat a + UInt32.ofNat r = UInt32.ofNat b := by
      calc
        UInt32.ofNat a + UInt32.ofNat r =
            (UInt32.ofNat a - UInt32.ofNat b) +
              UInt32.ofNat b + UInt32.ofNat r := by
                rw [UInt32.sub_add_cancel]
        _ = (0 - UInt32.ofNat r) +
              UInt32.ofNat b + UInt32.ofNat r := by rw [h]
        _ = (0 - UInt32.ofNat r) +
              UInt32.ofNat r + UInt32.ofNat b := by ac_rfl
        _ = UInt32.ofNat b := by
          rw [UInt32.sub_add_cancel, UInt32.zero_add]
    rw [Wasm.Examples.MergeSort.u32_ofNat_add hsum] at hu
    have hnat := congrArg UInt32.toNat hu
    rw [UInt32.toNat_ofNat_of_lt' hsum,
      UInt32.toNat_ofNat_of_lt' hb] at hnat
    exact hnat
  · intro h
    rw [← h, ← Wasm.Examples.MergeSort.u32_ofNat_add hsum]
    calc
      UInt32.ofNat a -
          (UInt32.ofNat a + UInt32.ofNat r) =
        UInt32.ofNat a +
          -(UInt32.ofNat a + UInt32.ofNat r) := UInt32.sub_eq_add_neg _ _
      _ = UInt32.ofNat a +
          (-UInt32.ofNat a - UInt32.ofNat r) := by rw [UInt32.neg_add]
      _ = UInt32.ofNat a +
          (-UInt32.ofNat a + -UInt32.ofNat r) := by
            rw [UInt32.sub_eq_add_neg]
      _ = (UInt32.ofNat a + -UInt32.ofNat a) +
          -UInt32.ofNat r := by ac_rfl
      _ = (UInt32.ofNat a - UInt32.ofNat a) +
          -UInt32.ofNat r := by
            congr 1
            exact UInt32.add_neg_eq_sub
      _ = (UInt32.ofNat a - UInt32.ofNat a) -
          UInt32.ofNat r := by
            symm
            exact UInt32.sub_eq_add_neg _ _
      _ = 0 - UInt32.ofNat r := by rw [UInt32.sub_self]

private theorem u32_neg_counter_step {r : Nat}
    (h : r + 1 < UInt32.size) :
    (0 - UInt32.ofNat r) + 4294967295 =
      0 - UInt32.ofNat (r + 1) := by
  have hmax : (4294967295 : UInt32) = 0 - 1 := by decide
  rw [hmax, ← Wasm.Examples.MergeSort.u32_ofNat_succ h,
    UInt32.zero_sub, UInt32.zero_sub, UInt32.zero_sub,
    UInt32.neg_add, UInt32.sub_eq_add_neg]

private theorem u32_neg_counter_increment {q : Nat}
    (hq : 0 < q) (hsize : q < UInt32.size) :
    (0 - UInt32.ofNat q) + 1 = 0 - UInt32.ofNat (q - 1) := by
  have hpred : q - 1 + 1 = q := by omega
  have hpredSize : q - 1 + 1 < UInt32.size := by omega
  have hof : UInt32.ofNat q = UInt32.ofNat (q - 1) + 1 := by
    rw [Wasm.Examples.MergeSort.u32_ofNat_succ hpredSize, hpred]
  rw [hof, UInt32.zero_sub, UInt32.zero_sub, UInt32.neg_add,
    UInt32.sub_add_cancel]

private theorem right_counter_init {mid j length : Nat}
    (hmj : mid ≤ j) (hjl : j ≤ length)
    (hlength : length < UInt32.size) :
    UInt32.ofNat (j - mid) +
        (UInt32.ofNat mid - UInt32.ofNat length) =
      0 - UInt32.ofNat (length - j) := by
  have hj : mid + (j - mid) = j := by omega
  calc
    UInt32.ofNat (j - mid) +
        (UInt32.ofNat mid - UInt32.ofNat length) =
      (UInt32.ofNat mid + UInt32.ofNat (j - mid)) -
        UInt32.ofNat length := by
          rw [UInt32.sub_eq_add_neg, UInt32.sub_eq_add_neg]
          ac_rfl
    _ = UInt32.ofNat j - UInt32.ofNat length := by
      rw [Wasm.Examples.MergeSort.u32_ofNat_add (by omega), hj]
    _ = 0 - UInt32.ofNat (length - j) :=
      (u32_sub_eq_neg_iff_sum_eq (by omega) hlength).mpr (by omega)

theorem mergeMainLoopBody_shape :
    mergeMainLoopBody =
      .block 0 0 mergeMainOuterBody :: mergeMainLoopBody.drop 1 := by
  rfl

theorem mergeMainLoopBody_tail :
    mergeMainLoopBody.drop 1 =
      [.localGet 8, .const 4, .add, .localSet 8,
       .localGet 5, .const 1, .add, .localSet 5,
       .localGet 9, .localGet 4, .geU, .localTee 11, .br_if 2,
       .localGet 10, .localGet 7, .ltU, .br_if 0, .br 2] := by
  rfl

theorem mergeMainOuterBody_shape :
    mergeMainOuterBody =
      .block 0 0 mergeMainChoiceBody :: mergeMainOuterBody.drop 1 := by
  rfl

theorem mergeMainChoiceBody_shape :
    mergeMainChoiceBody =
      .block 0 0 mergeMainCompareBody ::
      .block 0 0 mergeMainLeftBody ::
      [.localGet 5, .localGet 3, .const 1049048, .call 52,
        .unreachable] := by
  rfl

theorem mergeMainCompareBody_load1 :
    mergeMainCompareBody =
      [.localGet 0, .localGet 9, .const 2, .shl, .add, .load32 0] ++
        mergeMainCompareBody.drop 6 := by
  rfl

theorem mergeMainCompareBody_load2 :
    mergeMainCompareBody.drop 7 =
      [.localGet 6, .localGet 10, .const 2, .shl, .add, .load32 0] ++
        mergeMainCompareBody.drop 13 := by
  rfl

theorem mergeMainCompareBody_afterLoad1 :
    mergeMainCompareBody.drop 6 =
      .localTee 11 :: mergeMainCompareBody.drop 7 := by
  rfl

theorem mergeMainCompareBody_afterLoad2 :
    mergeMainCompareBody.drop 13 =
      .localTee 12 :: .leU :: .br_if 0 :: mergeMainCompareBody.drop 16 := by
  rfl

theorem mergeMainCompareBody_rightGuard :
    mergeMainCompareBody.drop 16 =
      [.localGet 5, .localGet 3, .geU, .br_if 1] ++
        mergeMainCompareBody.drop 20 := by
  rfl

theorem mergeMainLeftBody_guard :
    mergeMainLeftBody =
      [.localGet 5, .localGet 3, .geU, .br_if 0] ++
        mergeMainLeftBody.drop 4 := by
  rfl

theorem mergeMainLeftBody_store :
    mergeMainLeftBody.drop 4 =
      [.localGet 8, .localGet 11, .store32 0] ++
        mergeMainLeftBody.drop 7 := by
  rfl

theorem mergeMainLeftBody_advance :
    mergeMainLeftBody.drop 7 =
      [.localGet 9, .const 1, .add, .localSet 9, .br 2] := by
  rfl

theorem mergeMainCompareBody_rightStore :
    mergeMainCompareBody.drop 20 =
      [.localGet 8, .localGet 12, .store32 0] ++
        mergeMainCompareBody.drop 23 := by
  rfl

theorem mergeMainCompareBody_rightAdvance :
    mergeMainCompareBody.drop 23 =
      [.localGet 10, .const 1, .add, .localSet 10, .br 2] := by
  rfl

theorem sortBlock4_remainder_shape :
    sortBlock4.drop 5 =
      .block 0 0 mergeLeftRemainderBody ::
      .block 0 0 mergeRightRemainderBody :: sortBlock4.drop 7 := by
  rfl

theorem sortBlock4_after_merge :
    sortBlock4.drop 7 =
      [.localGet 1, .localGet 3, .ne, .br_if 3,
       .localGet 1, .const 2, .shl, .localTee 5, .eqz, .br_if 0,
       .localGet 0, .localGet 2, .localGet 5, .memoryCopy] := by
  rfl

theorem mergeLeftRemainderBody_shape :
    mergeLeftRemainderBody =
      [.localGet 11, .br_if 0,
       .localGet 9, .localGet 4, .sub, .localSet 6,
       .localGet 0, .localGet 9, .const 2, .shl, .add, .localSet 11,
       .localGet 5, .localGet 3, .localGet 5, .localGet 3, .localGet 5,
       .gtU, .select, .sub, .localSet 12,
       .const 0, .localSet 9,
       .loop 0 0 mergeLeftLoopBody,
       .localGet 5, .localGet 9, .sub, .localSet 5] := by
  rfl

theorem mergeLeftLoopBody_shape :
    mergeLeftLoopBody =
      [.localGet 12, .localGet 9, .eq, .br_if 4,
       .localGet 8, .localGet 11, .load32 0, .store32 0,
       .localGet 8, .const 4, .add, .localSet 8,
       .localGet 11, .const 4, .add, .localSet 11,
       .localGet 6, .localGet 9, .const 4294967295, .add,
       .localTee 9, .ne, .br_if 0] := by
  rfl

theorem mergeRightRemainderBody_shape :
    mergeRightRemainderBody =
      [.localGet 10, .localGet 7, .geU, .br_if 0,
       .localGet 0, .localGet 4, .const 2, .shl, .add,
       .localGet 10, .const 2, .shl, .add, .localSet 8,
       .localGet 5, .localGet 3, .localGet 5, .localGet 3,
       .gtU, .select, .localSet 11,
       .localGet 2, .localGet 5, .const 2, .shl, .add, .localSet 9,
       .localGet 4, .localGet 1, .sub, .localGet 10, .add,
       .localSet 10,
       .loop 0 0 mergeRightLoopBody] := by
  rfl

theorem mergeRightLoopBody_shape :
    mergeRightLoopBody =
      [.localGet 11, .localGet 5, .eq, .br_if 3,
       .localGet 9, .localGet 8, .load32 0, .store32 0,
       .localGet 9, .const 4, .add, .localSet 9,
       .localGet 8, .const 4, .add, .localSet 8,
       .localGet 5, .const 1, .add, .localSet 5,
       .localGet 10, .const 1, .add, .localTee 10, .br_if 0] := by
  rfl

/-! ## Array access patterns emitted by LLVM -/

set_option maxHeartbeats 2000000 in
theorem twp_loadShlAt
    [WasmSmallStepGS hlc α]
    {Terminal : Type} [TerminalView α Terminal]
    {s : Stuckness} {E : CoPset}
    {Φ : Terminal → IProp (WasmHeapGF α)}
    {params localValues stack : List Value}
    {baseIndex elementIndex : Nat}
    {physicalBase computedBase computedIndex : UInt32}
    {input : List UInt32} {k : Nat}
    (hk : k < input.length)
    (hfit : physicalBase.toNat + 4 * input.length ≤ UInt32.size)
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (hbase : (⟨params, localValues, stack⟩ : Locals).get baseIndex =
      some (.i32 computedBase))
    (helement : (⟨params, localValues, stack⟩ : Locals).get elementIndex =
      some (.i32 computedIndex))
    (haddress :
      (computedIndex <<< (2 % 32 : UInt32)) + computedBase =
        physicalBase + 4 * UInt32.ofNat k) :
    arrayAt 0 physicalBase input ∗
      (arrayAt 0 physicalBase input -∗
        WP (.running
          ⟨⟨params, localValues, .i32 input[k] :: stack⟩,
            code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨params, localValues, stack⟩,
        [.localGet baseIndex, .localGet elementIndex, .const 2, .shl,
          .add, .load32 0] ++ code,
        arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  let address := physicalBase + 4 * UInt32.ofNat k
  have hslot : address.toNat = physicalBase.toNat + 4 * k := by
    dsimp only [address]
    simpa [UInt32.mul_comm] using
      Wasm.Examples.MergeSort.arrayAddress_toNat physicalBase hfit hk
  have hroom : address.toNat + 4 ≤ UInt32.size := by rw [hslot]; omega
  have hroom' : address.toNat + 4 ≤ 4294967296 := by
    simpa only [UInt32.size] using hroom
  obtain ⟨h1, h2, h3⟩ := UInt32.addSteps4 address hroom'
  iintro ⟨Harray, Hcont⟩
  ihave ⟨Hword, Hclose⟩ := arrayAt_get 0 physicalBase input k hk $$ Harray
  simp only [List.cons_append, List.nil_append]
  iapply twp_localGet hbase
  iapply twp_localGet (by simpa [Locals.get] using helement)
  wasm_twp_pures [twp_const twp_shl twp_add] rewriting [haddress]
  ihave Hword' : pointsTo_u32 0 (address + 0) input[k] $$ [Hword]
  · simp only [address, UInt32.add_zero]
    iexact Hword
  iapply twp_load32 (address := address) (offset := 0) input[k]
    (by simp) (by simpa using h1) (by simpa using h2)
    (by simpa using h3) $$ Hword'
  iintro Hword
  iapply Hcont
  iapply Hclose
  ihave Hword'' :
      pointsTo_u32 0 (physicalBase + 4 * UInt32.ofNat k) input[k] $$ [Hword]
  · rw [show physicalBase + 4 * UInt32.ofNat k = address + 0 by
      simp [address]]
    iexact Hword
  iexact Hword''

set_option maxHeartbeats 2000000 in
theorem twp_storeCurrentAt
    [WasmSmallStepGS hlc α]
    {Terminal : Type} [TerminalView α Terminal]
    {s : Stuckness} {E : CoPset}
    {Φ : Terminal → IProp (WasmHeapGF α)}
    {params localValues stack : List Value}
    {addressIndex valueIndex : Nat}
    {physicalBase currentAddress newWord : UInt32}
    {values : List UInt32} {k : Nat}
    (hk : k < values.length)
    (hfit : physicalBase.toNat + 4 * values.length ≤ UInt32.size)
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (haddressGet : (⟨params, localValues, stack⟩ : Locals).get addressIndex =
      some (.i32 currentAddress))
    (hvalueGet : (⟨params, localValues, stack⟩ : Locals).get valueIndex =
      some (.i32 newWord))
    (haddress : currentAddress = physicalBase + 4 * UInt32.ofNat k) :
    arrayAt 0 physicalBase values ∗
      (arrayAt 0 physicalBase (values.set k newWord) -∗
        WP (.running
          ⟨⟨params, localValues, stack⟩,
            code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨params, localValues, stack⟩,
        [.localGet addressIndex, .localGet valueIndex, .store32 0] ++ code,
        arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  let address := physicalBase + 4 * UInt32.ofNat k
  have hslot : address.toNat = physicalBase.toNat + 4 * k := by
    dsimp only [address]
    simpa [UInt32.mul_comm] using
      Wasm.Examples.MergeSort.arrayAddress_toNat physicalBase hfit hk
  have hroom : address.toNat + 4 ≤ UInt32.size := by rw [hslot]; omega
  have hroom' : address.toNat + 4 ≤ 4294967296 := by
    simpa only [UInt32.size] using hroom
  obtain ⟨h1, h2, h3⟩ := UInt32.addSteps4 address hroom'
  iintro ⟨Harray, Hcont⟩
  ihave ⟨Hword, Hclose⟩ := arrayAt_set 0 physicalBase values k newWord hk $$ Harray
  simp only [List.cons_append, List.nil_append]
  iapply twp_localGet haddressGet
  iapply twp_localGet (by simpa [Locals.get] using hvalueGet)
  rw [haddress]
  ihave Hword' : pointsTo_u32 0 (address + 0) values[k] $$ [Hword]
  · simp only [address, UInt32.add_zero]
    iexact Hword
  iapply twp_store32 (address := address) (offset := 0)
    (value := newWord) values[k] (by simp)
    (by simpa using h1) (by simpa using h2) (by simpa using h3) $$ Hword'
  iintro Hword
  iapply Hcont
  iapply Hclose
  ihave Hword'' :
      pointsTo_u32 0 (physicalBase + 4 * UInt32.ofNat k) newWord $$ [Hword]
  · rw [show physicalBase + 4 * UInt32.ofNat k = address + 0 by
      simp [address]]
    iexact Hword
  iexact Hword''

set_option maxHeartbeats 3000000 in
theorem twp_copyPointerAt
    [WasmSmallStepGS hlc α]
    {Terminal : Type} [TerminalView α Terminal]
    {s : Stuckness} {E : CoPset}
    {Φ : Terminal → IProp (WasmHeapGF α)}
    {params localValues stack : List Value}
    {destinationLocal sourceLocal : Nat}
    {source scratch sourceAddress destinationAddress : UInt32}
    {input scratchValues : List UInt32} {i k : Nat}
    (hi : i < input.length) (hk : k < scratchValues.length)
    (hsourceFit : source.toNat + 4 * input.length ≤ UInt32.size)
    (hscratchFit :
      scratch.toNat + 4 * scratchValues.length ≤ UInt32.size)
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (hdestination :
      (⟨params, localValues, stack⟩ : Locals).get destinationLocal =
        some (.i32 destinationAddress))
    (hsource :
      (⟨params, localValues, stack⟩ : Locals).get sourceLocal =
        some (.i32 sourceAddress))
    (hsourceAddress :
      sourceAddress = source + 4 * UInt32.ofNat i)
    (hdestinationAddress :
      destinationAddress = scratch + 4 * UInt32.ofNat k) :
    arrayAt 0 source input ∗ arrayAt 0 scratch scratchValues ∗
      (arrayAt 0 source input ∗
        arrayAt 0 scratch (scratchValues.set k input[i]) -∗
        WP (.running
          ⟨⟨params, localValues, stack⟩,
            code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨params, localValues, stack⟩,
        .localGet destinationLocal :: .localGet sourceLocal ::
          .load32 0 :: .store32 0 :: code,
        arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  have hsourceSlot :
      sourceAddress.toNat = source.toNat + 4 * i := by
    rw [hsourceAddress]
    simpa [UInt32.mul_comm] using
      Wasm.Examples.MergeSort.arrayAddress_toNat source hsourceFit hi
  have hdestinationSlot :
      destinationAddress.toNat = scratch.toNat + 4 * k := by
    rw [hdestinationAddress]
    simpa [UInt32.mul_comm] using
      Wasm.Examples.MergeSort.arrayAddress_toNat scratch hscratchFit hk
  have hsourceRoom : sourceAddress.toNat + 4 ≤ UInt32.size := by
    omega
  have hdestinationRoom :
      destinationAddress.toNat + 4 ≤ UInt32.size := by
    omega
  have hsourceRoom' : sourceAddress.toNat + 4 ≤ 4294967296 := by
    simpa only [UInt32.size] using hsourceRoom
  have hdestinationRoom' : destinationAddress.toNat + 4 ≤ 4294967296 := by
    simpa only [UInt32.size] using hdestinationRoom
  obtain ⟨hs1, hs2, hs3⟩ := UInt32.addSteps4 sourceAddress hsourceRoom'
  obtain ⟨hd1, hd2, hd3⟩ := UInt32.addSteps4 destinationAddress hdestinationRoom'
  iintro ⟨Hsource, Hscratch, Hcont⟩
  ihave ⟨HsourceCell, HsourceClose⟩ := arrayAt_get 0 source input i hi $$ Hsource
  ihave ⟨HscratchCell, HscratchClose⟩ :=
    arrayAt_set 0 scratch scratchValues k input[i] hk $$ Hscratch
  iapply twp_localGet hdestination
  iapply twp_localGet (by simpa [Locals.get] using hsource)
  ihave HsourceCellLater :
      pointsTo_u32 0 (sourceAddress + 0) input[i] $$ [HsourceCell]
  · irw_exact [UInt32.add_zero, hsourceAddress] with HsourceCell
  wasm_twp_bind Wasm.SmallStep.twp_load32
    (address := sourceAddress) (offset := 0) input[i]
    (by simp) (by simpa using hs1) (by simpa using hs2)
    (by simpa using hs3) with HsourceCellLater => HsourceCell
  ihave HscratchCellLater :
      pointsTo_u32 0 (destinationAddress + 0) scratchValues[k] $$
        [HscratchCell]
  · irw_exact [UInt32.add_zero, hdestinationAddress] with HscratchCell
  wasm_twp_bind Wasm.SmallStep.twp_store32
    (address := destinationAddress) (offset := 0)
    (value := input[i]) scratchValues[k]
    (by simp) (by simpa using hd1) (by simpa using hd2)
    (by simpa using hd3) with HscratchCellLater => HscratchCell
  ihave HsourceCell' :
      pointsTo_u32 0 (source + 4 * UInt32.ofNat i) input[i] $$
        [HsourceCell]
  · irw_exact [← hsourceAddress, UInt32.add_zero] with HsourceCell
  ihave HsourceArray := HsourceClose $$ HsourceCell'
  ihave HscratchCell' :
      pointsTo_u32 0 (scratch + 4 * UInt32.ofNat k) input[i] $$
        [HscratchCell]
  · irw_exact [← hdestinationAddress, UInt32.add_zero] with HscratchCell
  ihave HscratchArray := HscratchClose $$ HscratchCell'
  iapply_frame Hcont

/-! ## Generated main merge loop -/

set_option maxHeartbeats 4000000 in
theorem twp_mergeMainChoice
    [WasmSmallStepGS hlc α]
    {Terminal : Type} [TerminalView α Terminal]
    {s : Stuckness} {E : CoPset}
    {Φ : Terminal → IProp (WasmHeapGF α)}
    (source scratch : UInt32) (input scratchValues : List UInt32)
    (mid i j k : Nat)
    (oldLeft oldRight : UInt32)
    (hi : i < mid) (hj : j < input.length)
    (hk : k < scratchValues.length)
    (hmj : mid ≤ j)
    (hlayout : Wasm.Examples.MergeSort.ValidLayout
      source scratch input.length)
    (hscratchLength : scratchValues.length = input.length)
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    arrayAt 0 source input ∗ arrayAt 0 scratch scratchValues ∗
      ((⌜input[i] ≤ input[j]⌝ ∗ arrayAt 0 source input ∗
          arrayAt 0 scratch (scratchValues.set k input[i]) -∗
          WP (.running
            ⟨sortLocals source scratch
                (UInt32.ofNat input.length) (UInt32.ofNat input.length)
                (UInt32.ofNat mid) (UInt32.ofNat k)
                (source + 4 * UInt32.ofNat mid)
                (UInt32.ofNat (input.length - mid))
                (scratch + 4 * UInt32.ofNat k)
                (UInt32.ofNat (i + 1)) (UInt32.ofNat (j - mid))
                input[i] input[j] [],
              mergeMainLoopBody.drop 1, arity, remainder,
              controls, calls⟩ : Expr α) @ s; E [{ Φ }]) ∧
       (⌜¬input[i] ≤ input[j]⌝ ∗ arrayAt 0 source input ∗
          arrayAt 0 scratch (scratchValues.set k input[j]) -∗
          WP (.running
            ⟨sortLocals source scratch
                (UInt32.ofNat input.length) (UInt32.ofNat input.length)
                (UInt32.ofNat mid) (UInt32.ofNat k)
                (source + 4 * UInt32.ofNat mid)
                (UInt32.ofNat (input.length - mid))
                (scratch + 4 * UInt32.ofNat k)
                (UInt32.ofNat i) (UInt32.ofNat (j + 1 - mid))
                input[i] input[j] [],
              mergeMainLoopBody.drop 1, arity, remainder,
              controls, calls⟩ : Expr α) @ s; E [{ Φ }])) ⊢
    WP (.running
      ⟨sortLocals source scratch
          (UInt32.ofNat input.length) (UInt32.ofNat input.length)
          (UInt32.ofNat mid) (UInt32.ofNat k)
          (source + 4 * UInt32.ofNat mid)
          (UInt32.ofNat (input.length - mid))
          (scratch + 4 * UInt32.ofNat k)
          (UInt32.ofNat i) (UInt32.ofNat (j - mid))
          oldLeft oldRight [],
        mergeMainLoopBody, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  have hmidLen : mid < input.length := by omega
  have hiLen : i < input.length := by omega
  have hlengthLt := hlayout.length_lt
  have hkLen : k < input.length := by omega
  have hkU : UInt32.ofNat k < UInt32.ofNat input.length := by
    rw [UInt32.lt_iff_toNat_lt,
      UInt32.toNat_ofNat_of_lt' (by omega : k < UInt32.size),
      UInt32.toNat_ofNat_of_lt' hlengthLt]
    exact hkLen
  have hiValue :
      1 + UInt32.ofNat i = UInt32.ofNat (i + 1) := by
    rw [UInt32.add_comm,
      Wasm.Examples.MergeSort.u32_ofNat_succ (by omega)]
  have hjValue :
      1 + UInt32.ofNat (j - mid) = UInt32.ofNat (j + 1 - mid) := by
    rw [UInt32.add_comm,
      Wasm.Examples.MergeSort.u32_ofNat_succ (by omega)]
    congr 1
    omega
  iintro ⟨Hsource, Hscratch, Hbranches⟩
  rw [mergeMainLoopBody_shape]
  wasm_twp_pures [twp_block] rewriting [mergeMainOuterBody_shape]
  wasm_twp_pures [twp_block] rewriting [mergeMainChoiceBody_shape]
  wasm_twp_pures [twp_block] rewriting [mergeMainCompareBody_load1]
  simp only [sortLocals, List.drop_zero]
  iapply twp_loadShlAt
    (physicalBase := source) (computedBase := source)
    (computedIndex := UInt32.ofNat i) (input := input) (k := i)
    hiLen hlayout.source_fits
    (by rfl) (by rfl)
    (by rw [MemRegion.shl2_eq_mul4, UInt32.add_comm])
  iframe; iintro Hsource
  rw [mergeMainCompareBody_afterLoad1]
  wasm_twp_pures [twp_localTee] rewriting [mergeMainCompareBody_load2]
  iapply twp_loadShlAt
    (physicalBase := source)
    (computedBase := source + 4 * UInt32.ofNat mid)
    (computedIndex := UInt32.ofNat (j - mid))
    (input := input) (k := j) hj hlayout.source_fits
    (by rfl) (by rfl) (right_slot_address source hmj)
  iframe; iintro Hsource
  rw [mergeMainCompareBody_afterLoad2]
  wasm_twp_localTee [List.length, List.set]
  by_cases hle : input[i] ≤ input[j]
  · iapply twp_leU (result := 1) (by simp [hle])
    iapply twp_brIf (by decide) (by rfl)
    simp only [List.take_nil, List.nil_append]
    wasm_twp_pures [twp_block] rewriting [mergeMainLeftBody_guard]
    simp only [List.cons_append, List.nil_append]
    wasm_twp_pures [twp_localGet twp_localGet]
    iapply twp_geU (result := 0) (by simp [UInt32.not_le.mpr hkU])
    wasm_twp_pures [twp_brIfZero] rewriting [mergeMainLeftBody_store]
    iapply twp_storeCurrentAt
      (physicalBase := scratch)
      (currentAddress := scratch + 4 * UInt32.ofNat k)
      (newWord := input[i]) (values := scratchValues) (k := k)
      hk (by simpa [hscratchLength] using hlayout.temporary_fits)
      (by rfl) (by rfl) rfl
    iframe; iintro Hscratch
    rw [mergeMainLeftBody_advance]
    wasm_twp_pures [twp_localGet twp_const twp_add] rewriting [hiValue]
    wasm_twp_pures [twp_localSet twp_br]
    simp only [List.take_nil, List.nil_append, List.length, List.set, List.drop]
    ihave Hleft := BI.and_elim_l $$ Hbranches
    iapply Hleft
    isplitr_pureexact hle
    iframe
  · iapply twp_leU (result := 0) (by simp [hle])
    wasm_twp_pures [twp_brIfZero] rewriting [mergeMainCompareBody_rightGuard]
    simp only [List.cons_append, List.nil_append]
    wasm_twp_pures [twp_localGet twp_localGet]
    iapply twp_geU (result := 0) (by simp [UInt32.not_le.mpr hkU])
    wasm_twp_pures [twp_brIfZero] rewriting [mergeMainCompareBody_rightStore]
    iapply twp_storeCurrentAt
      (physicalBase := scratch)
      (currentAddress := scratch + 4 * UInt32.ofNat k)
      (newWord := input[j]) (values := scratchValues) (k := k)
      hk (by simpa [hscratchLength] using hlayout.temporary_fits)
      (by rfl) (by rfl) rfl
    iframe; iintro Hscratch
    rw [mergeMainCompareBody_rightAdvance]
    wasm_twp_pures [twp_localGet twp_const twp_add] rewriting [hjValue]
    wasm_twp_pures [twp_localSet twp_br]
    simp only [List.take_nil, List.nil_append, List.length, List.set, List.drop]
    ihave Hright := BI.and_elim_r $$ Hbranches
    iapply Hright
    isplitr_pureexact hle
    iframe

structure GeneratedMergeState where
  scratchValues : List UInt32
  i : Nat
  j : Nat
  k : Nat
  emitted : List UInt32
  lastLeft : UInt32
  lastRight : UInt32

structure LeftCopyState where
  scratchValues : List UInt32
  r : Nat
  emitted : List UInt32

structure RightCopyState where
  scratchValues : List UInt32
  r : Nat
  emitted : List UInt32

set_option maxHeartbeats 8000000 in
theorem twp_mergeMainLoop
    [WasmSmallStepGS hlc α]
    {Terminal : Type} [TerminalView α Terminal]
    {s : Stuckness} {E : CoPset}
    {Φ : Terminal → IProp (WasmHeapGF α)}
    (source scratch : UInt32) (input scratchValues : List UInt32)
    (mid i j k : Nat) (emitted : List UInt32)
    (lastLeft lastRight : UInt32)
    (hinv : MergeLoopInvariant input scratchValues mid i j k emitted)
    (hi : i < mid) (hj : j < input.length)
    (hlayout : Wasm.Examples.MergeSort.ValidLayout
      source scratch input.length)
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    arrayAt 0 source input ∗ arrayAt 0 scratch scratchValues ∗
      (∀ (scratch' : List UInt32) (i' j' k' : Nat)
          (emitted' : List UInt32) (flag last : UInt32),
        ⌜MergeLoopInvariant input scratch' mid i' j' k' emitted'⌝ -∗
        ⌜(flag = 1 ∧ i' = mid) ∨
          (flag = 0 ∧ i' < mid ∧ j' = input.length)⌝ -∗
        arrayAt 0 source input -∗ arrayAt 0 scratch scratch' -∗
        WP (.running
          ⟨sortLocals source scratch
              (UInt32.ofNat input.length) (UInt32.ofNat input.length)
              (UInt32.ofNat mid) (UInt32.ofNat k')
              (source + 4 * UInt32.ofNat mid)
              (UInt32.ofNat (input.length - mid))
              (scratch + 4 * UInt32.ofNat k')
              (UInt32.ofNat i') (UInt32.ofNat (j' - mid))
              flag last [],
            sortBlock4.drop 5, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨sortLocals source scratch
          (UInt32.ofNat input.length) (UInt32.ofNat input.length)
          (UInt32.ofNat mid) (UInt32.ofNat k)
          (source + 4 * UInt32.ofNat mid)
          (UInt32.ofNat (input.length - mid))
          (scratch + 4 * UInt32.ofNat k)
          (UInt32.ofNat i) (UInt32.ofNat (j - mid))
          lastLeft lastRight [],
        [.loop 0 0 mergeMainLoopBody], arity, remainder,
        sortRecursiveBodyFrame :: sortRecursiveGuardFrame :: controls,
        calls⟩ : Expr α) @ s; E [{ Φ }] := by
  let Finish : IProp (WasmHeapGF α) := iprop%
    ∀ (scratch' : List UInt32) (i' j' k' : Nat)
        (emitted' : List UInt32) (flag last : UInt32),
      ⌜MergeLoopInvariant input scratch' mid i' j' k' emitted'⌝ -∗
      ⌜(flag = 1 ∧ i' = mid) ∨
        (flag = 0 ∧ i' < mid ∧ j' = input.length)⌝ -∗
      arrayAt 0 source input -∗ arrayAt 0 scratch scratch' -∗
      WP (.running
        ⟨sortLocals source scratch
            (UInt32.ofNat input.length) (UInt32.ofNat input.length)
            (UInt32.ofNat mid) (UInt32.ofNat k')
            (source + 4 * UInt32.ofNat mid)
            (UInt32.ofNat (input.length - mid))
            (scratch + 4 * UInt32.ofNat k')
            (UInt32.ofNat i') (UInt32.ofNat (j' - mid))
            flag last [],
          sortBlock4.drop 5, arity, remainder, controls, calls⟩ : Expr α)
        @ s; E [{ Φ }]
  let Inv : GeneratedMergeState → IProp (WasmHeapGF α) := fun state => iprop%
    ⌜MergeLoopInvariant input state.scratchValues mid
      state.i state.j state.k state.emitted⌝ ∗
    ⌜state.i < mid ∧ state.j < input.length⌝ ∗
    arrayAt 0 source input ∗ arrayAt 0 scratch state.scratchValues ∗ Finish
  iintro ⟨Hsource, Hscratch, Hfinish⟩
  iapply twp_loop_wf_family_from_terminal
    (ι := GeneratedMergeState)
    (measure := fun state =>
      (mid - state.i) + (input.length - state.j))
    (locals := fun state =>
      sortLocals source scratch
        (UInt32.ofNat input.length) (UInt32.ofNat input.length)
        (UInt32.ofNat mid) (UInt32.ofNat state.k)
        (source + 4 * UInt32.ofNat mid)
        (UInt32.ofNat (input.length - mid))
        (scratch + 4 * UInt32.ofNat state.k)
        (UInt32.ofNat state.i) (UInt32.ofNat (state.j - mid))
        state.lastLeft state.lastRight [])
    (I := Inv)
    (initial := ⟨scratchValues, i, j, k, emitted, lastLeft, lastRight⟩)
    (initialLocals :=
      sortLocals source scratch
        (UInt32.ofNat input.length) (UInt32.ofNat input.length)
        (UInt32.ofNat mid) (UInt32.ofNat k)
        (source + 4 * UInt32.ofNat mid)
        (UInt32.ofNat (input.length - mid))
        (scratch + 4 * UInt32.ofNat k)
        (UInt32.ofNat i) (UInt32.ofNat (j - mid))
        lastLeft lastRight [])
    (body := mergeMainLoopBody) (code := []) (belowStack := [])
    rfl rfl
  · intro state
    simp only [Inv, Wasm.SmallStep.loopBodyExpr]
    iintro Hrec Hinv
    icases Hinv with
      ⟨%hstate, %hactive, Hsource, Hscratch, Hfinish⟩
    rcases hactive with ⟨hiState, hjState⟩
    have hdata := hstate
    unfold MergeLoopInvariant at hdata
    have hkInput := hstate.k_lt hiState hjState
    have hkScratch : state.k < state.scratchValues.length := by
      simpa only [hdata.2.2.2.2.1] using hkInput
    iapply twp_mergeMainChoice source scratch input state.scratchValues
      mid state.i state.j state.k state.lastLeft state.lastRight
      hiState hjState hkScratch hdata.2.2.1 hlayout
      hdata.2.2.2.2.1
    isplitl_exacts [Hsource Hscratch]
    isplit
    · iintro ⟨%hle, Hsource, Hscratch⟩
      have hiLen : state.i < input.length := by omega
      have hnext := hstate.takeLeft hiState hjState
        (List.getElem?_eq_getElem hiLen)
        (List.getElem?_eq_getElem hjState) hle
      have hkSucc : state.k + 1 < UInt32.size := by
        have := hlayout.length_lt; omega
      have hkValue :
          1 + UInt32.ofNat state.k = UInt32.ofNat (state.k + 1) := by
        rw [UInt32.add_comm,
          Wasm.Examples.MergeSort.u32_ofNat_succ hkSucc]
      rw [mergeMainLoopBody_tail]
      wasm_twp_pures [twp_localGet twp_const twp_add]
      rw [UInt32.add_comm (4 : UInt32), next_slot_address]
      wasm_twp_pures [twp_localSet]
      wasm_twp_pures [twp_localGet twp_const twp_add] rewriting [hkValue]
      wasm_twp_pures [twp_localSet]
      wasm_twp_pures [twp_localGet twp_localGet]
      by_cases hiNext : state.i + 1 < mid
      · have hmidSize : mid < UInt32.size := by
          have := hlayout.length_lt; omega
        have hiNextU :
            UInt32.ofNat (state.i + 1) < UInt32.ofNat mid := by
          rw [UInt32.lt_iff_toNat_lt,
            UInt32.toNat_ofNat_of_lt' (by omega),
            UInt32.toNat_ofNat_of_lt' hmidSize]
          exact hiNext
        iapply twp_geU (result := 0)
          (by rw [if_neg (UInt32.not_le.mpr hiNextU)])
        wasm_twp_pures [twp_localTee]
        wasm_twp_pures [twp_brIfZero twp_localGet twp_localGet]
        have hlengthLt := hlayout.length_lt
        have hjDiffSize : state.j - mid < UInt32.size := by omega
        have hlengthDiffSize : input.length - mid < UInt32.size := by omega
        have hjRelative :
            UInt32.ofNat (state.j - mid) <
              UInt32.ofNat (input.length - mid) := by
          rw [UInt32.lt_iff_toNat_lt,
            UInt32.toNat_ofNat_of_lt' hjDiffSize,
            UInt32.toNat_ofNat_of_lt' hlengthDiffSize]
          omega
        iapply twp_ltU (result := 1) (by simp [hjRelative])
        iapply twp_brIf (by decide) (by rfl)
        simp only [sortLocals, List.length, List.set, List.take_zero,
          List.nil_append]
        ispecialize Hrec $$
          %(⟨state.scratchValues.set state.k input[state.i],
              state.i + 1, state.j, state.k + 1,
              state.emitted ++ [input[state.i]],
              0, input[state.j]⟩ : GeneratedMergeState)
        iapply_pure Hrec =>
          dsimp only [GeneratedMergeState.i, GeneratedMergeState.j]; omega
        isplitr_pureexacts [hnext, ⟨hiNext, hjState⟩]
        iframe
      · have hiEq : state.i + 1 = mid := by omega
        have hge :
            UInt32.ofNat (state.i + 1) ≥ UInt32.ofNat mid := by
          rw [hiEq]; exact le_refl (UInt32.ofNat mid)
        iapply twp_geU (result := 1) (by rw [if_pos hge])
        wasm_twp_pures [twp_localTee]
        iapply twp_brIf (by decide) (by rfl)
        simp only [sortLocals, List.length, List.set, List.take_zero,
          List.nil_append, sortRecursiveGuardFrame, emptyBlockFrame]
        have hexit :
            ((1 : UInt32) = 1 ∧ state.i + 1 = mid) ∨
              ((1 : UInt32) = 0 ∧ state.i + 1 < mid ∧
                state.j = input.length) :=
          Or.inl ⟨rfl, hiEq⟩
        ihave Hdone := Hfinish $$
          %(state.scratchValues.set state.k input[state.i])
          %(state.i + 1) %state.j %(state.k + 1)
          %(state.emitted ++ [input[state.i]]) %(1 : UInt32)
          %input[state.j] %hnext %hexit Hsource Hscratch
        isimp only [sortLocals] at Hdone
        iexact Hdone
    · iintro ⟨%hle, Hsource, Hscratch⟩
      have hiLen : state.i < input.length := by omega
      have hnext := hstate.takeRight hiState hjState
        (List.getElem?_eq_getElem hiLen)
        (List.getElem?_eq_getElem hjState) hle
      have hkSucc : state.k + 1 < UInt32.size := by
        have := hlayout.length_lt; omega
      have hkValue :
          1 + UInt32.ofNat state.k = UInt32.ofNat (state.k + 1) := by
        rw [UInt32.add_comm,
          Wasm.Examples.MergeSort.u32_ofNat_succ hkSucc]
      rw [mergeMainLoopBody_tail]
      wasm_twp_pures [twp_localGet twp_const twp_add]
      rw [UInt32.add_comm (4 : UInt32), next_slot_address]
      wasm_twp_pures [twp_localSet]
      wasm_twp_pures [twp_localGet twp_const twp_add] rewriting [hkValue]
      wasm_twp_pures [twp_localSet]
      wasm_twp_pures [twp_localGet twp_localGet]
      have hmidSize : mid < UInt32.size := by
        have := hlayout.length_lt; omega
      have hiU : UInt32.ofNat state.i < UInt32.ofNat mid := by
        rw [UInt32.lt_iff_toNat_lt,
          UInt32.toNat_ofNat_of_lt' (by omega),
          UInt32.toNat_ofNat_of_lt' hmidSize]
        exact hiState
      iapply twp_geU (result := 0)
        (by rw [if_neg (UInt32.not_le.mpr hiU)])
      wasm_twp_pures [twp_localTee]
      wasm_twp_pures [twp_brIfZero twp_localGet twp_localGet]
      by_cases hjNext : state.j + 1 < input.length
      · have hlengthLt := hlayout.length_lt
        have hjDiffSize : state.j + 1 - mid < UInt32.size := by omega
        have hlengthDiffSize : input.length - mid < UInt32.size := by omega
        have hjRelative :
            UInt32.ofNat (state.j + 1 - mid) <
              UInt32.ofNat (input.length - mid) := by
          rw [UInt32.lt_iff_toNat_lt,
            UInt32.toNat_ofNat_of_lt' hjDiffSize,
            UInt32.toNat_ofNat_of_lt' hlengthDiffSize]
          omega
        iapply twp_ltU (result := 1) (by simp [hjRelative])
        iapply twp_brIf (by decide) (by rfl)
        simp only [sortLocals, List.length, List.set, List.take_zero,
          List.nil_append]
        ispecialize Hrec $$
          %(⟨state.scratchValues.set state.k input[state.j],
              state.i, state.j + 1, state.k + 1,
              state.emitted ++ [input[state.j]],
              0, input[state.j]⟩ : GeneratedMergeState)
        iapply_pure Hrec =>
          dsimp only [GeneratedMergeState.i, GeneratedMergeState.j]; omega
        isplitr_pureexacts [hnext, ⟨hiState, hjNext⟩]
        iframe
      · have hjEq : state.j + 1 = input.length := by omega
        have hnotRelative :
            ¬UInt32.ofNat (state.j + 1 - mid) <
              UInt32.ofNat (input.length - mid) := by
          rw [hjEq]
          rw [UInt32.lt_iff_toNat_lt]; exact Nat.lt_irrefl _
        iapply twp_ltU (result := 0) (by rw [if_neg hnotRelative])
        wasm_twp_pures [twp_brIfZero twp_br]
        simp only [sortLocals, List.length, List.set, List.take_zero,
          List.nil_append, sortRecursiveGuardFrame, emptyBlockFrame]
        have hexit :
            ((0 : UInt32) = 1 ∧ state.i = mid) ∨
              ((0 : UInt32) = 0 ∧ state.i < mid ∧
                state.j + 1 = input.length) :=
          Or.inr ⟨rfl, hiState, hjEq⟩
        ihave Hdone := Hfinish $$
          %(state.scratchValues.set state.k input[state.j])
          %state.i %(state.j + 1) %(state.k + 1)
          %(state.emitted ++ [input[state.j]]) %(0 : UInt32)
          %input[state.j] %hnext %hexit Hsource Hscratch
        isimp only [sortLocals] at Hdone
        iexact Hdone
  · simp only [Inv, Finish]
    isplitr_pureexacts [hinv, ⟨hi, hj⟩]
    iframe

set_option maxHeartbeats 8000000 in
theorem twp_mergeLeftRemainder
    [WasmSmallStepGS hlc α]
    {Terminal : Type} [TerminalView α Terminal]
    {s : Stuckness} {E : CoPset}
    {Φ : Terminal → IProp (WasmHeapGF α)}
    (source scratch : UInt32) (input scratchValues : List UInt32)
    (mid i j k : Nat) (emitted : List UInt32)
    (flag last : UInt32)
    (hinv : MergeLoopInvariant input scratchValues mid i j k emitted)
    (hexit : (flag = 1 ∧ i = mid) ∨
      (flag = 0 ∧ i < mid ∧ j = input.length))
    (hlayout : Wasm.Examples.MergeSort.ValidLayout
      source scratch input.length)
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    arrayAt 0 source input ∗ arrayAt 0 scratch scratchValues ∗
      (∀ (scratch' : List UInt32) (j' k' : Nat)
          (emitted' : List UInt32)
          (aux6 aux8 aux9 aux11 aux12 : UInt32),
        ⌜MergeLoopInvariant input scratch' mid mid j' k' emitted'⌝ -∗
        arrayAt 0 source input -∗ arrayAt 0 scratch scratch' -∗
        WP (.running
          ⟨sortLocals source scratch
              (UInt32.ofNat input.length) (UInt32.ofNat input.length)
              (UInt32.ofNat mid) (UInt32.ofNat k') aux6
              (UInt32.ofNat (input.length - mid)) aux8
              aux9 (UInt32.ofNat (j' - mid))
              aux11 aux12 [],
            .block 0 0 mergeRightRemainderBody :: sortBlock4.drop 7,
            arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨sortLocals source scratch
          (UInt32.ofNat input.length) (UInt32.ofNat input.length)
          (UInt32.ofNat mid) (UInt32.ofNat k)
          (source + 4 * UInt32.ofNat mid)
          (UInt32.ofNat (input.length - mid))
          (scratch + 4 * UInt32.ofNat k)
          (UInt32.ofNat i) (UInt32.ofNat (j - mid)) flag last [],
        sortBlock4.drop 5, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hsource, Hscratch, Hfinish⟩
  rw [sortBlock4_remainder_shape]
  wasm_twp_pures [twp_block] rewriting [mergeLeftRemainderBody_shape]
  wasm_twp_pures [twp_localGet]
  rcases hexit with ⟨hflag, hiEq⟩ | ⟨hflag, hiRemain, hjEq⟩
  · subst flag
    iapply twp_brIf (by decide) (by rfl)
    simp only [List.take_zero, List.nil_append, List.drop_zero,
      sortLocals, hiEq]
    ihave Hdone := Hfinish $$ %scratchValues %j %k %emitted
      %(source + 4 * UInt32.ofNat mid)
      %(scratch + 4 * UInt32.ofNat k) %(UInt32.ofNat mid)
      %(1 : UInt32) %last
      %(by simpa [hiEq] using hinv) Hsource Hscratch
    iexact Hdone
  · subst flag
    wasm_twp_pures [twp_brIfZero]
    have hdata := hinv
    unfold MergeLoopInvariant at hdata
    rw [hjEq] at hdata
    rcases hdata with
      ⟨_, him, hmj, hjr, hscratchLength, hkEmitted,
        hemittedLength, htake, hprogress⟩
    have hkLt : k < input.length := by
      rw [hkEmitted, hemittedLength]; omega
    have hkU : UInt32.ofNat k < UInt32.ofNat input.length := by
      rw [UInt32.lt_iff_toNat_lt,
        UInt32.toNat_ofNat_of_lt' (Nat.lt_trans hkLt hlayout.length_lt),
        UInt32.toNat_ofNat_of_lt' hlayout.length_lt]
      exact hkLt
    wasm_twp_pures [twp_localGet twp_localGet twp_sub twp_localSet]
    simp only
    wasm_twp_pures [twp_localGet twp_localGet twp_const twp_shl twp_add]
    rw [MemRegion.shl2_eq_mul4, UInt32.add_comm]
    wasm_twp_pures [twp_localSet]
    wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet twp_localGet]
    have hnotGt :
        ¬UInt32.ofNat input.length < UInt32.ofNat k := by
      rw [UInt32.lt_iff_toNat_lt,
        UInt32.toNat_ofNat_of_lt' hlayout.length_lt,
        UInt32.toNat_ofNat_of_lt' (Nat.lt_trans hkLt hlayout.length_lt)]
      omega
    iapply twp_gtU (result := 1) (by rw [if_pos hkU])
    iapply twp_select (selected := .i32 (UInt32.ofNat input.length))
      (by simp)
    wasm_twp_pures [twp_sub twp_localSet]
    simp only
    wasm_twp_pures [twp_const twp_localSet] using [sortLocals, List.length, List.set, hjEq]
    let n := mid - i
    have hiN : i + n = mid := by
      dsimp only [n]; omega
    have hkN : k + n = input.length := by
      rw [hkEmitted, hemittedLength]
      dsimp only [n]; omega
    let Finish : IProp (WasmHeapGF α) := iprop%
      ∀ (scratch' : List UInt32) (emitted' : List UInt32)
          (aux6 aux8 aux9 aux11 aux12 : UInt32),
        ⌜MergeLoopInvariant input scratch' mid mid input.length
          input.length emitted'⌝ -∗
        arrayAt 0 source input -∗ arrayAt 0 scratch scratch' -∗
        WP (.running
          ⟨sortLocals source scratch
              (UInt32.ofNat input.length) (UInt32.ofNat input.length)
              (UInt32.ofNat mid) (UInt32.ofNat input.length) aux6
              (UInt32.ofNat (input.length - mid)) aux8
              aux9
              (UInt32.ofNat (input.length - mid)) aux11 aux12 [],
            .block 0 0 mergeRightRemainderBody :: sortBlock4.drop 7,
            arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]
    let Inv : LeftCopyState → IProp (WasmHeapGF α) := fun state => iprop%
      ⌜state.r < n⌝ ∗
      ⌜MergeLoopInvariant input state.scratchValues mid
        (i + state.r) input.length (k + state.r) state.emitted⌝ ∗
      arrayAt 0 source input ∗ arrayAt 0 scratch state.scratchValues ∗ Finish
    iapply twp_loop_wf_family_from_terminal
      (ι := LeftCopyState) (measure := fun state => n - state.r)
      (locals := fun state =>
        (⟨[.i32 source, .i32 (UInt32.ofNat input.length), .i32 scratch,
            .i32 (UInt32.ofNat input.length)],
          [.i32 (UInt32.ofNat mid), .i32 (UInt32.ofNat k),
            .i32 (UInt32.ofNat i - UInt32.ofNat mid),
            .i32 (UInt32.ofNat (input.length - mid)),
            .i32 (scratch + 4 * UInt32.ofNat (k + state.r)),
            .i32 (0 - UInt32.ofNat state.r),
            .i32 (UInt32.ofNat (input.length - mid)),
            .i32 (4 * UInt32.ofNat (i + state.r) + source),
            .i32 (UInt32.ofNat k - UInt32.ofNat input.length)], []⟩ : Locals))
      (I := Inv)
      (initial := ⟨scratchValues, 0, emitted⟩)
      (initialLocals :=
        (⟨[.i32 source, .i32 (UInt32.ofNat input.length), .i32 scratch,
            .i32 (UInt32.ofNat input.length)],
          [.i32 (UInt32.ofNat mid), .i32 (UInt32.ofNat k),
            .i32 (UInt32.ofNat i - UInt32.ofNat mid),
            .i32 (UInt32.ofNat (input.length - mid)),
            .i32 (scratch + 4 * UInt32.ofNat k), .i32 0,
            .i32 (UInt32.ofNat (input.length - mid)),
            .i32 (4 * UInt32.ofNat i + source),
            .i32 (UInt32.ofNat k - UInt32.ofNat input.length)], []⟩ : Locals))
      (body := mergeLeftLoopBody)
      (code := [.localGet 5, .localGet 9, .sub, .localSet 5])
      (paramArity := 0) (resultArity := 0)
      (arity := arity) (remainder := remainder) (calls := calls)
      (belowStack := []) (by simp) (by simp)
    · intro state
      simp only [Inv, Wasm.SmallStep.loopBodyExpr]
      iintro Hrec Hinv
      icases Hinv with ⟨%hr, %hstate, Hsource, Hscratch, Hfinish⟩
      have hdataState := hstate
      unfold MergeLoopInvariant at hdataState
      rcases hdataState with
        ⟨_, himState, hmjState, hjrState, hstateLen, hkState,
          hemittedState, htakeState, hprogressState⟩
      have hiCurrent : i + state.r < mid := by
        dsimp only [n] at hr; omega
      have hiCurrentLen : i + state.r < input.length := by omega
      have hkCurrent : k + state.r < input.length := by
        rw [hkState, hemittedState]; omega
      have hkCurrentScratch : k + state.r < state.scratchValues.length := by
        simpa only [hstateLen] using hkCurrent
      have hsumSize : k + state.r < UInt32.size :=
        Nat.lt_trans hkCurrent hlayout.length_lt
      have hcounterNe :
          UInt32.ofNat k - UInt32.ofNat input.length ≠
            0 - UInt32.ofNat state.r := by
        intro hcounter
        have := (u32_sub_eq_neg_iff_sum_eq hsumSize
          hlayout.length_lt).mp hcounter
        omega
      have hcounterNe' :
          UInt32.ofNat k - UInt32.ofNat input.length ≠
            -UInt32.ofNat state.r := by
        simpa [UInt32.zero_sub] using hcounterNe
      have hnext := hstate.takeRemainingLeft hiCurrent
        (List.getElem?_eq_getElem hiCurrentLen)
      rw [mergeLeftLoopBody_shape]
      wasm_twp_pures [twp_localGet twp_localGet]
      iapply twp_eq (result := 0) (by rw [if_neg hcounterNe])
      wasm_twp_pures [twp_brIfZero]
      iapply twp_copyPointerAt
        (params := [.i32 source, .i32 (UInt32.ofNat input.length),
          .i32 scratch, .i32 (UInt32.ofNat input.length)])
        (localValues := [.i32 (UInt32.ofNat mid), .i32 (UInt32.ofNat k),
          .i32 (UInt32.ofNat i - UInt32.ofNat mid),
          .i32 (UInt32.ofNat (input.length - mid)),
          .i32 (scratch + 4 * UInt32.ofNat (k + state.r)),
          .i32 (0 - UInt32.ofNat state.r),
          .i32 (UInt32.ofNat (input.length - mid)),
          .i32 (4 * UInt32.ofNat (i + state.r) + source),
          .i32 (UInt32.ofNat k - UInt32.ofNat input.length)])
        (stack := [])
        (destinationLocal := 8) (sourceLocal := 11)
        (source := source) (scratch := scratch)
        (sourceAddress := 4 * UInt32.ofNat (i + state.r) + source)
        (destinationAddress := scratch + 4 * UInt32.ofNat (k + state.r))
        (input := input) (scratchValues := state.scratchValues)
        (i := i + state.r) (k := k + state.r)
        (code := [.localGet 8, .const 4, .add, .localSet 8,
          .localGet 11, .const 4, .add, .localSet 11,
          .localGet 6, .localGet 9, .const 4294967295, .add,
          .localTee 9, .ne, .br_if 0])
        (arity := arity) (remainder := remainder) (calls := calls)
        (controls :=
          ControlFrame.mk .loop 0 0
            [.localGet 12, .localGet 9, .eq, .br_if 4,
              .localGet 8, .localGet 11, .load32 0, .store32 0,
              .localGet 8, .const 4, .add, .localSet 8,
              .localGet 11, .const 4, .add, .localSet 11,
              .localGet 6, .localGet 9, .const 4294967295, .add,
              .localTee 9, .ne, .br_if 0]
            [.localGet 5, .localGet 9, .sub, .localSet 5] [] ::
          ControlFrame.mk .block 0 0
            [.localGet 11, .br_if 0,
              .localGet 9, .localGet 4, .sub, .localSet 6,
              .localGet 0, .localGet 9, .const 2, .shl, .add, .localSet 11,
              .localGet 5, .localGet 3, .localGet 5, .localGet 3,
              .localGet 5, .gtU, .select, .sub, .localSet 12,
              .const 0, .localSet 9,
              .loop 0 0 [.localGet 12, .localGet 9, .eq, .br_if 4,
                .localGet 8, .localGet 11, .load32 0, .store32 0,
                .localGet 8, .const 4, .add, .localSet 8,
                .localGet 11, .const 4, .add, .localSet 11,
                .localGet 6, .localGet 9, .const 4294967295, .add,
                .localTee 9, .ne, .br_if 0],
              .localGet 5, .localGet 9, .sub, .localSet 5]
            (.block 0 0 mergeRightRemainderBody :: sortBlock4.drop 7)
            (List.drop 0 []) :: controls)
        hiCurrentLen hkCurrentScratch hlayout.source_fits
        (by simpa [hstateLen] using hlayout.temporary_fits)
        (by rfl) (by rfl) (by rw [UInt32.add_comm]) (by rfl)
      isplitl_exacts [Hsource Hscratch]
      iintro ⟨Hsource, Hscratch⟩
      have hmidSize : mid < UInt32.size := by
        exact Nat.lt_of_le_of_lt hmjState hlayout.length_lt
      have hrSuccSize : state.r + 1 < UInt32.size := by
        have : state.r + 1 ≤ n := by omega
        omega
      have hsourceNext :
          4 * UInt32.ofNat (i + state.r) + source + 4 =
            4 * UInt32.ofNat (i + (state.r + 1)) + source := by
        rw [UInt32.add_comm (4 * UInt32.ofNat (i + state.r)) source,
          next_slot_address, UInt32.add_comm source]
        congr 3
      have hleftCounterEq :
          UInt32.ofNat i - UInt32.ofNat mid =
              0 - UInt32.ofNat (state.r + 1) ↔
            state.r + 1 = n := by
        have hiSuccSize : i + (state.r + 1) < UInt32.size := by
          have : i + (state.r + 1) ≤ mid := by omega
          omega
        rw [u32_sub_eq_neg_iff_sum_eq hiSuccSize hmidSize]; omega
      wasm_twp_pures [twp_localGet twp_const twp_add]
      rw [UInt32.add_comm (4 : UInt32), next_slot_address]
      wasm_twp_localSet [List.length, List.set]
      wasm_twp_pures [twp_localGet twp_const twp_add]
      rw [UInt32.add_comm (4 : UInt32), hsourceNext]
      wasm_twp_localSet [List.length, List.set]
      wasm_twp_pures [twp_localGet twp_localGet twp_const twp_add]
      rw [UInt32.add_comm (4294967295 : UInt32),
        u32_neg_counter_step hrSuccSize]
      wasm_twp_localTee [List.length, List.set]
      by_cases hmore : state.r + 1 < n
      · have hne :
            UInt32.ofNat i - UInt32.ofNat mid ≠
              0 - UInt32.ofNat (state.r + 1) := by
          intro heq
          exact (Nat.ne_of_lt hmore) (hleftCounterEq.mp heq)
        have hneActual :
            UInt32.ofNat i - UInt32.ofNat mid ≠
              -(UInt32.ofNat state.r + 1) := by
          rw [Wasm.Examples.MergeSort.u32_ofNat_succ hrSuccSize]
          simpa [UInt32.zero_sub] using hne
        iapply twp_ne (result := 1) (by rw [if_pos hne])
        iapply twp_brIf (by decide) (by rfl)
        simp only [List.take_zero, List.nil_append]
        ispecialize Hrec $$
          %(⟨state.scratchValues.set (k + state.r) input[i + state.r],
            state.r + 1, state.emitted ++ [input[i + state.r]]⟩ :
              LeftCopyState)
        iapply_pure Hrec =>
          dsimp only [LeftCopyState.r]; omega
        isplitr_pureexacts [hmore, by simpa [Nat.add_assoc] using hnext]
        iframe
      · have heqR : state.r + 1 = n := by omega
        have heq := hleftCounterEq.mpr heqR
        have heqActual :
            UInt32.ofNat i - UInt32.ofNat mid =
              -(UInt32.ofNat state.r + 1) := by
          rw [Wasm.Examples.MergeSort.u32_ofNat_succ hrSuccSize]
          simpa [UInt32.zero_sub] using heq
        have hnotne : ¬(
            UInt32.ofNat i - UInt32.ofNat mid ≠
              0 - UInt32.ofNat (state.r + 1)) := by
          intro hne
          exact hne heq
        iapply twp_ne (result := 0) (by rw [if_neg hnotne])
        wasm_twp_pures [twp_brIfZero]
        iapply Wasm.SmallStep.twp_exitControl (α := α) rfl
        simp only [List.take_zero, List.nil_append]
        have hfinalK :
            UInt32.ofNat k - (0 - UInt32.ofNat (state.r + 1)) =
              UInt32.ofNat input.length := by
          rw [heqR, UInt32.sub_eq_add_neg, UInt32.zero_sub,
            UInt32.neg_neg,
            Wasm.Examples.MergeSort.u32_ofNat_add (by
              rw [hkN]; exact hlayout.length_lt), hkN]
        wasm_twp_pures [twp_localGet twp_localGet twp_sub] rewriting [hfinalK]
        wasm_twp_localSet [List.length, List.set]
        iapply Wasm.SmallStep.twp_exitControl (α := α) rfl
        simp only [List.take_zero, List.nil_append]
        have hiFinal : i + state.r + 1 = mid := by omega
        have hkFinal : k + state.r + 1 = input.length := by omega
        have hfinalInv :
            MergeLoopInvariant input
              (state.scratchValues.set (k + state.r) input[i + state.r])
              mid mid input.length input.length
              (state.emitted ++ [input[i + state.r]]) := by
          simpa only [hiFinal, hkFinal] using hnext
        ihave Hdone := Hfinish $$
          %(state.scratchValues.set (k + state.r) input[i + state.r])
          %(state.emitted ++ [input[i + state.r]])
          %(UInt32.ofNat i - UInt32.ofNat mid)
          %(scratch + 4 * UInt32.ofNat (k + state.r + 1))
          %(0 - UInt32.ofNat (state.r + 1))
          %(4 * UInt32.ofNat (i + (state.r + 1)) + source)
          %(UInt32.ofNat k - UInt32.ofNat input.length)
          %hfinalInv Hsource Hscratch
        isimp only [sortLocals] at Hdone
        simp only [List.drop_zero]
        iexact Hdone
    · simp only [Inv, Finish, sortLocals]
      isplitr
      · ipureintro
        dsimp only [n]; omega
      isplitr_pureexact (by simpa [hjEq] using hinv)
      isplitl_exacts [Hsource Hscratch]
      iintro %scratch' %emitted' %aux6 %aux8 %aux9 %aux11 %aux12
        %hinv' Hsource Hscratch
      ihave Hdone := Hfinish $$ %scratch' %input.length %input.length
        %emitted' %aux6 %aux8 %aux9 %aux11 %aux12 %hinv'
        Hsource Hscratch
      iexact Hdone

set_option maxHeartbeats 8000000 in
theorem twp_mergeRightRemainder
    [WasmSmallStepGS hlc α]
    {Terminal : Type} [TerminalView α Terminal]
    {s : Stuckness} {E : CoPset}
    {Φ : Terminal → IProp (WasmHeapGF α)}
    (source scratch : UInt32) (input scratchValues : List UInt32)
    (mid j k : Nat) (emitted : List UInt32)
    (aux6 aux8 aux9 aux11 aux12 : UInt32)
    (hinv : MergeLoopInvariant input scratchValues mid mid j k emitted)
    (hlayout : Wasm.Examples.MergeSort.ValidLayout
      source scratch input.length)
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    arrayAt 0 source input ∗ arrayAt 0 scratch scratchValues ∗
      (∀ (scratch' : List UInt32) (emitted' : List UInt32)
          (v6 v8 v9 v10 v11 v12 : UInt32),
        ⌜MergeLoopInvariant input scratch' mid mid input.length
          input.length emitted'⌝ -∗
        arrayAt 0 source input -∗ arrayAt 0 scratch scratch' -∗
        WP (.running
          ⟨sortLocals source scratch
              (UInt32.ofNat input.length) (UInt32.ofNat input.length)
              (UInt32.ofNat mid) (UInt32.ofNat input.length) v6
              (UInt32.ofNat (input.length - mid)) v8 v9 v10 v11 v12 [],
            sortBlock4.drop 7, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨sortLocals source scratch
          (UInt32.ofNat input.length) (UInt32.ofNat input.length)
          (UInt32.ofNat mid) (UInt32.ofNat k) aux6
          (UInt32.ofNat (input.length - mid)) aux8 aux9
          (UInt32.ofNat (j - mid)) aux11 aux12 [],
        .block 0 0 mergeRightRemainderBody :: sortBlock4.drop 7,
        arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hsource, Hscratch, Hfinish⟩
  have hdata := hinv
  unfold MergeLoopInvariant at hdata
  rcases hdata with
    ⟨_, him, hmj, hjl, hscratchLength, hkEmitted,
      hemittedLength, htake, hprogress⟩
  have hmidSize : mid < UInt32.size := by
    exact Nat.lt_of_le_of_lt (Nat.le_trans hmj hjl) hlayout.length_lt
  have hjSize : j < UInt32.size := by
    exact Nat.lt_of_le_of_lt hjl hlayout.length_lt
  have hjDiffSize : j - mid < UInt32.size := by omega
  have hlengthDiffSize : input.length - mid < UInt32.size :=
    Nat.lt_of_le_of_lt (Nat.sub_le _ _) hlayout.length_lt
  rw [mergeRightRemainderBody_shape]
  wasm_twp_pures [twp_block twp_localGet twp_localGet]
  by_cases hjDone : j = input.length
  · subst j
    have hkDone : k = input.length := by omega
    have hinvDone :
        MergeLoopInvariant input scratchValues mid mid input.length
          input.length emitted := by
      simpa [hkDone] using hinv
    iapply twp_geU (result := 1) (by simp)
    iapply twp_brIf (by decide) (by rfl)
    simp only [List.take_zero, List.nil_append, List.drop_zero, sortLocals,
      hkDone]
    ihave Hdone := Hfinish $$ %scratchValues %emitted %aux6 %aux8
      %aux9 %(UInt32.ofNat (input.length - mid)) %aux11 %aux12
      %hinvDone Hsource Hscratch
    iexact Hdone
  · have hjRemain : j < input.length := by omega
    have hjRelative :
        UInt32.ofNat (j - mid) <
          UInt32.ofNat (input.length - mid) := by
      rw [UInt32.lt_iff_toNat_lt,
        UInt32.toNat_ofNat_of_lt' hjDiffSize,
        UInt32.toNat_ofNat_of_lt' hlengthDiffSize]
      omega
    iapply twp_geU (result := 0)
      (by rw [if_neg (UInt32.not_le.mpr hjRelative)])
    wasm_twp_pures [twp_brIfZero]
    have hkEqJ : k = j := by omega
    have hkLt : k < input.length := by omega
    have hkU : UInt32.ofNat k < UInt32.ofNat input.length := by
      rw [UInt32.lt_iff_toNat_lt,
        UInt32.toNat_ofNat_of_lt' (by omega),
        UInt32.toNat_ofNat_of_lt' hlayout.length_lt]
      exact hkLt
    wasm_twp_pures [twp_localGet twp_localGet twp_const twp_shl] rewriting [MemRegion.shl2_eq_mul4]
    wasm_twp_pures [twp_add] rewriting [UInt32.add_comm]
    wasm_twp_pures [twp_localGet twp_const twp_shl] rewriting [MemRegion.shl2_eq_mul4]
    wasm_twp_pures [twp_add]
    have hsourceAddress :
        4 * UInt32.ofNat (j - mid) +
            (source + 4 * UInt32.ofNat mid) =
          source + 4 * UInt32.ofNat j := by
      have h := right_slot_address source hmj
      rw [MemRegion.shl2_eq_mul4] at h; exact h
    rw [hsourceAddress]
    wasm_twp_pures [twp_localSet]
    wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet]
    have hnotGt :
        ¬UInt32.ofNat input.length < UInt32.ofNat k := by
      rw [UInt32.lt_iff_toNat_lt,
        UInt32.toNat_ofNat_of_lt' hlayout.length_lt,
        UInt32.toNat_ofNat_of_lt' (by omega)]
      omega
    iapply twp_gtU (result := 0) (by rw [if_neg hnotGt])
    iapply twp_select (selected := .i32 (UInt32.ofNat input.length))
      (by simp)
    wasm_twp_pures [twp_localSet]
    wasm_twp_pures [twp_localGet twp_localGet twp_const twp_shl] rewriting [MemRegion.shl2_eq_mul4]
    wasm_twp_pures [twp_add] rewriting [UInt32.add_comm]
    wasm_twp_pures [twp_localSet]
    wasm_twp_pures [twp_localGet twp_localGet twp_sub twp_localGet twp_add]
    rw [right_counter_init hmj hjl hlayout.length_lt]
    wasm_twp_localSet [sortLocals, List.length, List.set]
    let n := input.length - j
    have hjN : j + n = input.length := by
      dsimp only [n]; omega
    have hkN : k + n = input.length := by omega
    let Finish : IProp (WasmHeapGF α) := iprop%
      ∀ (scratch' : List UInt32) (emitted' : List UInt32)
          (v6 v8 v9 v10 v11 v12 : UInt32),
        ⌜MergeLoopInvariant input scratch' mid mid input.length
          input.length emitted'⌝ -∗
        arrayAt 0 source input -∗ arrayAt 0 scratch scratch' -∗
        WP (.running
          ⟨sortLocals source scratch
              (UInt32.ofNat input.length) (UInt32.ofNat input.length)
              (UInt32.ofNat mid) (UInt32.ofNat input.length) v6
              (UInt32.ofNat (input.length - mid)) v8 v9 v10 v11 v12 [],
            sortBlock4.drop 7, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]
    let Inv : RightCopyState → IProp (WasmHeapGF α) := fun state => iprop%
      ⌜state.r < n⌝ ∗
      ⌜MergeLoopInvariant input state.scratchValues mid mid
        (j + state.r) (k + state.r) state.emitted⌝ ∗
      arrayAt 0 source input ∗ arrayAt 0 scratch state.scratchValues ∗ Finish
    iapply twp_loop_wf_family_from_terminal
      (ι := RightCopyState) (measure := fun state => n - state.r)
      (locals := fun state =>
        (⟨[.i32 source, .i32 (UInt32.ofNat input.length), .i32 scratch,
            .i32 (UInt32.ofNat input.length)],
          [.i32 (UInt32.ofNat mid), .i32 (UInt32.ofNat (k + state.r)),
            .i32 aux6, .i32 (UInt32.ofNat (input.length - mid)),
            .i32 (4 * UInt32.ofNat (j + state.r) + source),
            .i32 (4 * UInt32.ofNat (k + state.r) + scratch),
            .i32 (0 - UInt32.ofNat (n - state.r)),
            .i32 (UInt32.ofNat input.length), .i32 aux12], []⟩ : Locals))
      (I := Inv) (initial := ⟨scratchValues, 0, emitted⟩)
      (initialLocals :=
        (⟨[.i32 source, .i32 (UInt32.ofNat input.length), .i32 scratch,
            .i32 (UInt32.ofNat input.length)],
          [.i32 (UInt32.ofNat mid), .i32 (UInt32.ofNat k), .i32 aux6,
            .i32 (UInt32.ofNat (input.length - mid)),
            .i32 (4 * UInt32.ofNat j + source),
            .i32 (4 * UInt32.ofNat k + scratch),
            .i32 (0 - UInt32.ofNat n),
            .i32 (UInt32.ofNat input.length), .i32 aux12], []⟩ : Locals))
      (body := mergeRightLoopBody) (code := [])
      (paramArity := 0) (resultArity := 0)
      (arity := arity) (remainder := remainder) (calls := calls)
      (controls :=
        ControlFrame.mk .block 0 0
          [.localGet 10, .localGet 7, .geU, .br_if 0,
           .localGet 0, .localGet 4, .const 2, .shl, .add,
           .localGet 10, .const 2, .shl, .add, .localSet 8,
           .localGet 5, .localGet 3, .localGet 5, .localGet 3,
           .gtU, .select, .localSet 11,
           .localGet 2, .localGet 5, .const 2, .shl, .add, .localSet 9,
           .localGet 4, .localGet 1, .sub, .localGet 10, .add,
           .localSet 10, .loop 0 0 mergeRightLoopBody]
          (sortBlock4.drop 7) (List.drop 0 []) :: controls)
      (belowStack := []) (by simp) (by simp)
    · intro state
      simp only [Inv, Wasm.SmallStep.loopBodyExpr]
      iintro Hrec Hinv
      icases Hinv with ⟨%hr, %hstate, Hsource, Hscratch, Hfinish⟩
      have hdataState := hstate
      unfold MergeLoopInvariant at hdataState
      rcases hdataState with
        ⟨_, himState, hmjState, hjlState, hstateLen, hkState,
          hemittedState, htakeState, hprogressState⟩
      have hjCurrent : j + state.r < input.length := by
        dsimp only [n] at hr; omega
      have hkCurrent : k + state.r < input.length := by
        rw [hkState, hemittedState]; omega
      have hkCurrentScratch : k + state.r < state.scratchValues.length := by
        simpa only [hstateLen] using hkCurrent
      have hcounterNe :
          UInt32.ofNat input.length ≠ UInt32.ofNat (k + state.r) := by
        intro heq
        have hnat := congrArg UInt32.toNat heq
        rw [UInt32.toNat_ofNat_of_lt' hlayout.length_lt,
          UInt32.toNat_ofNat_of_lt'
            (Nat.lt_trans hkCurrent hlayout.length_lt)] at hnat
        omega
      have hnext := hstate.takeRemainingRight hjCurrent
        (List.getElem?_eq_getElem hjCurrent)
      rw [mergeRightLoopBody_shape]
      wasm_twp_pures [twp_localGet twp_localGet]
      iapply twp_eq (result := 0) (by rw [if_neg hcounterNe])
      wasm_twp_pures [twp_brIfZero]
      iapply twp_copyPointerAt
        (params := [.i32 source, .i32 (UInt32.ofNat input.length),
          .i32 scratch, .i32 (UInt32.ofNat input.length)])
        (localValues :=
          [.i32 (UInt32.ofNat mid),
            .i32 (UInt32.ofNat (k + state.r)), .i32 aux6,
            .i32 (UInt32.ofNat (input.length - mid)),
            .i32 (4 * UInt32.ofNat (j + state.r) + source),
            .i32 (4 * UInt32.ofNat (k + state.r) + scratch),
            .i32 (0 - UInt32.ofNat (n - state.r)),
            .i32 (UInt32.ofNat input.length), .i32 aux12])
        (stack := []) (destinationLocal := 9) (sourceLocal := 8)
        (source := source) (scratch := scratch)
        (sourceAddress := 4 * UInt32.ofNat (j + state.r) + source)
        (destinationAddress :=
          4 * UInt32.ofNat (k + state.r) + scratch)
        (input := input) (scratchValues := state.scratchValues)
        (i := j + state.r) (k := k + state.r)
        (code := [.localGet 9, .const 4, .add, .localSet 9,
          .localGet 8, .const 4, .add, .localSet 8,
          .localGet 5, .const 1, .add, .localSet 5,
          .localGet 10, .const 1, .add, .localTee 10, .br_if 0])
        (arity := arity) (remainder := remainder) (calls := calls)
        (controls :=
          ControlFrame.mk .loop 0 0
            [.localGet 11, .localGet 5, .eq, .br_if 3,
             .localGet 9, .localGet 8, .load32 0, .store32 0,
             .localGet 9, .const 4, .add, .localSet 9,
             .localGet 8, .const 4, .add, .localSet 8,
             .localGet 5, .const 1, .add, .localSet 5,
             .localGet 10, .const 1, .add, .localTee 10, .br_if 0]
            [] [] ::
          ControlFrame.mk .block 0 0
            [.localGet 10, .localGet 7, .geU, .br_if 0,
             .localGet 0, .localGet 4, .const 2, .shl, .add,
             .localGet 10, .const 2, .shl, .add, .localSet 8,
             .localGet 5, .localGet 3, .localGet 5, .localGet 3,
             .gtU, .select, .localSet 11,
             .localGet 2, .localGet 5, .const 2, .shl, .add, .localSet 9,
             .localGet 4, .localGet 1, .sub, .localGet 10, .add,
             .localSet 10,
             .loop 0 0
               [.localGet 11, .localGet 5, .eq, .br_if 3,
                .localGet 9, .localGet 8, .load32 0, .store32 0,
                .localGet 9, .const 4, .add, .localSet 9,
                .localGet 8, .const 4, .add, .localSet 8,
                .localGet 5, .const 1, .add, .localSet 5,
                .localGet 10, .const 1, .add, .localTee 10, .br_if 0]]
            (sortBlock4.drop 7) (List.drop 0 []) :: controls)
        hjCurrent hkCurrentScratch hlayout.source_fits
        (by simpa [hstateLen] using hlayout.temporary_fits)
        (by rfl) (by rfl) (by rw [UInt32.add_comm])
        (by rw [UInt32.add_comm])
      isplitl_exacts [Hsource Hscratch]
      iintro ⟨Hsource, Hscratch⟩
      have hrSuccSize : state.r + 1 < UInt32.size := by
        have : state.r + 1 ≤ n := by omega
        dsimp only [n] at this; omega
      have hsourceNext :
          4 * UInt32.ofNat (j + state.r) + source + 4 =
            4 * UInt32.ofNat (j + (state.r + 1)) + source := by
        rw [UInt32.add_comm (4 * UInt32.ofNat (j + state.r)) source,
          next_slot_address, UInt32.add_comm source]
        congr 3
      have hdestinationNext :
          4 * UInt32.ofNat (k + state.r) + scratch + 4 =
            4 * UInt32.ofNat (k + (state.r + 1)) + scratch := by
        rw [UInt32.add_comm (4 * UInt32.ofNat (k + state.r)) scratch,
          next_slot_address, UInt32.add_comm scratch]
        congr 3
      have hkStep :
          UInt32.ofNat (k + state.r) + 1 =
            UInt32.ofNat (k + (state.r + 1)) := by
        have hkSuccSize : k + state.r + 1 < UInt32.size := by
          calc
            k + state.r + 1 ≤ input.length := Nat.succ_le_of_lt hkCurrent
            _ < UInt32.size := hlayout.length_lt
        rw [Wasm.Examples.MergeSort.u32_ofNat_succ hkSuccSize]
        congr 1
      have hq : 0 < n - state.r := by omega
      have hqSize : n - state.r < UInt32.size := by
        dsimp only [n]; omega
      have hcounterStep :
          (0 - UInt32.ofNat (n - state.r)) + 1 =
            0 - UInt32.ofNat (n - (state.r + 1)) := by
        rw [u32_neg_counter_increment hq hqSize]
        congr 2
      wasm_twp_pures [twp_localGet twp_const twp_add]
      rw [UInt32.add_comm (4 : UInt32), hdestinationNext]
      wasm_twp_localSet [List.length, List.set]
      wasm_twp_pures [twp_localGet twp_const twp_add]
      rw [UInt32.add_comm (4 : UInt32), hsourceNext]
      wasm_twp_localSet [List.length, List.set]
      wasm_twp_pures [twp_localGet twp_const twp_add]
      rw [UInt32.add_comm (1 : UInt32), hkStep]
      wasm_twp_localSet [List.length, List.set]
      wasm_twp_pures [twp_localGet twp_const twp_add]
      rw [UInt32.add_comm (1 : UInt32), hcounterStep]
      wasm_twp_localTee [List.length, List.set]
      by_cases hmore : state.r + 1 < n
      · have hnextCounterSize : n - (state.r + 1) < UInt32.size := by
          dsimp only [n]; omega
        have hcounterNextNe :
            0 - UInt32.ofNat (n - (state.r + 1)) ≠ 0 := by
          intro hz
          have hzeroEq :
              UInt32.ofNat 0 - UInt32.ofNat 0 =
                0 - UInt32.ofNat (n - (state.r + 1)) := by
            simpa using hz.symm
          have hnat := (u32_sub_eq_neg_iff_sum_eq
            (by simpa using hnextCounterSize) (by decide)).mp hzeroEq
          omega
        iapply twp_brIf hcounterNextNe (by rfl)
        simp only [List.take_zero, List.nil_append]
        ispecialize Hrec $$
          %(⟨state.scratchValues.set (k + state.r) input[j + state.r],
            state.r + 1, state.emitted ++ [input[j + state.r]]⟩ :
              RightCopyState)
        iapply_pure Hrec =>
          dsimp only [RightCopyState.r]; omega
        isplitr_pureexacts [hmore, by simpa [Nat.add_assoc] using hnext]
        iframe
      · have heqR : state.r + 1 = n := by omega
        have hcounterZero :
            0 - UInt32.ofNat (n - (state.r + 1)) = 0 := by
          simp [heqR]
        rw [hcounterZero]
        wasm_twp_pures [twp_brIfZero]
        iapply Wasm.SmallStep.twp_exitControl (α := α) rfl
        simp only [List.take_zero, List.nil_append]
        iapply Wasm.SmallStep.twp_exitControl (α := α) rfl
        simp only [List.take_zero, List.nil_append]
        have hjFinal : j + state.r + 1 = input.length := by omega
        have hkFinal : k + state.r + 1 = input.length := by omega
        have hkFinal' : k + (state.r + 1) = input.length := by
          simpa [Nat.add_assoc] using hkFinal
        have hfinalInv :
            MergeLoopInvariant input
              (state.scratchValues.set (k + state.r) input[j + state.r])
              mid mid input.length input.length
              (state.emitted ++ [input[j + state.r]]) := by
          simpa only [hjFinal, hkFinal] using hnext
        ihave Hdone := Hfinish $$
          %(state.scratchValues.set (k + state.r) input[j + state.r])
          %(state.emitted ++ [input[j + state.r]]) %aux6
          %(4 * UInt32.ofNat (j + (state.r + 1)) + source)
          %(4 * UInt32.ofNat (k + (state.r + 1)) + scratch) %0
          %(UInt32.ofNat input.length) %aux12
          %hfinalInv Hsource Hscratch
        isimp only [sortLocals] at Hdone
        simp only [List.drop_zero]
        irw_exact [hkFinal'] with Hdone
    · simp only [Inv, Finish, sortLocals]
      isplitr
      · ipureintro
        dsimp only [n]; omega
      isplitr_pureexact (by simpa using hinv)
      isplitl_exacts [Hsource Hscratch]
      iintro %scratch' %emitted' %v6 %v8 %v9 %v10 %v11 %v12
        %hinv' Hsource Hscratch
      ihave Hdone := Hfinish $$ %scratch' %emitted' %v6 %v8 %v9
        %v10 %v11 %v12 %hinv' Hsource Hscratch
      iexact Hdone

set_option maxHeartbeats 8000000 in
theorem twp_generated_merge
    [WasmSmallStepGS hlc α]
    {Terminal : Type} [TerminalView α Terminal]
    {s : Stuckness} {E : CoPset}
    {Φ : Terminal → IProp (WasmHeapGF α)}
    (source scratch : UInt32) (input scratchValues : List UInt32)
    (mid : Nat) (hmidPos : 0 < mid) (hmidLt : mid < input.length)
    (hscratchLength : scratchValues.length = input.length)
    (hlayout : Wasm.Examples.MergeSort.ValidLayout
      source scratch input.length)
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    arrayAt 0 source input ∗ arrayAt 0 scratch scratchValues ∗
      (∀ (output : List UInt32) (v6 v8 v9 v10 v11 v12 : UInt32),
        ⌜MergeLE
          (Wasm.Examples.MergeSort.segment input 0 mid)
          (Wasm.Examples.MergeSort.segment input mid input.length)
          output⌝ -∗
        arrayAt 0 source input -∗ arrayAt 0 scratch output -∗
        WP (.running
          ⟨sortLocals source scratch
              (UInt32.ofNat input.length) (UInt32.ofNat input.length)
              (UInt32.ofNat mid) (UInt32.ofNat input.length)
              v6 (UInt32.ofNat (input.length - mid))
              v8 v9 v10 v11 v12 [],
            sortBlock4.drop 7, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨sortLocals source scratch
          (UInt32.ofNat input.length) (UInt32.ofNat input.length)
          (UInt32.ofNat mid) (UInt32.ofNat 0)
          (source + 4 * UInt32.ofNat mid)
          (UInt32.ofNat (input.length - mid))
          (scratch + 4 * UInt32.ofNat 0)
          (UInt32.ofNat 0) (UInt32.ofNat (mid - mid)) 0 0 [],
        [.loop 0 0 mergeMainLoopBody], arity, remainder,
        sortRecursiveBodyFrame :: sortRecursiveGuardFrame :: controls,
        calls⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro ⟨Hsource, Hscratch, Hfinish⟩
  have hinvStart :
      MergeLoopInvariant input scratchValues mid 0 mid 0 [] :=
    mergeLoopInvariant_start (Nat.le_of_lt hmidLt) hscratchLength
  iapply twp_mergeMainLoop source scratch input scratchValues
    mid 0 mid 0 [] 0 0 hinvStart hmidPos hmidLt hlayout
  isplitl_exacts [Hsource Hscratch]
  iintro %scratch' %i %j %k %emitted %flag %last
    %hinv %hexit Hsource Hscratch
  iapply twp_mergeLeftRemainder source scratch input scratch'
    mid i j k emitted flag last hinv hexit hlayout
  isplitl_exacts [Hsource Hscratch]
  iintro %scratch'' %j' %k' %emitted'
    %aux6 %aux8 %aux9 %aux11 %aux12
    %hinv' Hsource Hscratch
  iapply twp_mergeRightRemainder source scratch input scratch''
    mid j' k' emitted' aux6 aux8 aux9 aux11 aux12 hinv' hlayout
  isplitl_exacts [Hsource Hscratch]
  iintro %scratchFinal %emittedFinal
    %v6 %v8 %v9 %v10 %v11 %v12
    %hfinal Hsource Hscratch
  rcases hfinal.finished with ⟨_, hscratchFinal, hmerge⟩
  subst scratchFinal
  ihave Hdone := Hfinish $$ %emittedFinal %v6 %v8 %v9 %v10 %v11 %v12
    %hmerge Hsource Hscratch
  isimp only [sortLocals] at Hdone
  isimp only [sortLocals]
  iexact Hdone

/-- Entry form of `twp_generated_merge` with compiler locals unfolded.  This
is convenient after symbolically executing the generated local assignments. -/
theorem twp_generated_merge_unfolded
    [WasmSmallStepGS hlc α]
    {Terminal : Type} [TerminalView α Terminal]
    {s : Stuckness} {E : CoPset}
    {Φ : Terminal → IProp (WasmHeapGF α)}
    (source scratch : UInt32) (input scratchValues : List UInt32)
    (mid : Nat) (hmidPos : 0 < mid) (hmidLt : mid < input.length)
    (hscratchLength : scratchValues.length = input.length)
    (hlayout : Wasm.Examples.MergeSort.ValidLayout
      source scratch input.length)
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    arrayAt 0 source input ∗ arrayAt 0 scratch scratchValues ∗
      (∀ (output : List UInt32) (v6 v8 v9 v10 v11 v12 : UInt32),
        ⌜MergeLE
          (Wasm.Examples.MergeSort.segment input 0 mid)
          (Wasm.Examples.MergeSort.segment input mid input.length)
          output⌝ -∗
        arrayAt 0 source input -∗ arrayAt 0 scratch output -∗
        WP (.running
          ⟨sortLocals source scratch
              (UInt32.ofNat input.length) (UInt32.ofNat input.length)
              (UInt32.ofNat mid) (UInt32.ofNat input.length)
              v6 (UInt32.ofNat (input.length - mid))
              v8 v9 v10 v11 v12 [],
            sortBlock4.drop 7, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 source, .i32 (UInt32.ofNat input.length), .i32 scratch,
            .i32 (UInt32.ofNat input.length)],
          [.i32 (UInt32.ofNat mid), .i32 0,
            .i32 (source + 4 * UInt32.ofNat mid),
            .i32 (UInt32.ofNat (input.length - mid)), .i32 scratch,
            .i32 0, .i32 0, .i32 0, .i32 0], []⟩,
        [.loop 0 0 mergeMainLoopBody], arity, remainder,
        sortRecursiveBodyFrame :: sortRecursiveGuardFrame :: controls,
        calls⟩ : Expr α) @ s; E [{ Φ }] := by
  simpa [sortLocals] using
    twp_generated_merge source scratch input scratchValues mid hmidPos
      hmidLt hscratchLength hlayout

/-- Base case of the generated recursive function.  When `length < 2`, its
four nested guards branch directly to `return` without touching memory. -/
theorem twp_sort_base
    [WasmSmallStepGS hlc Universal.State]
    {Terminal : Type} [TerminalView Universal.State Terminal]
    {s : Stuckness} {E : CoPset}
    {Φ : Terminal → IProp (WasmHeapGF Universal.State)}
    (source scratch : UInt32) (length scratchLength : Nat)
    (hbase : length < 2)
    (hlength : length < UInt32.size)
    (_hscratchLength : scratchLength < UInt32.size)
    {callerLocals : Locals}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {stack : List Value} :
    runtimeModuleOwn ⟨0⟩ Project.Mergesort.module ∗
      (runtimeModuleOwn ⟨0⟩ Project.Mergesort.module -∗
        WP (.running
          ⟨{ callerLocals with values := stack }, code, arity, remainder,
            controls, calls⟩ : Expr Universal.State) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with
          values := .i32 (UInt32.ofNat scratchLength) :: .i32 scratch ::
            .i32 (UInt32.ofNat length) :: .i32 source :: stack },
        .call 5 :: code, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hcont⟩
  wasm_twp_rebind Wasm.SmallStep.twp_call Project.Mergesort.module 5
    Project.Mergesort.func2Def (by decide) (by rfl) with Hruntime
  simp [Project.Mergesort.func2Def, Function.toLocals,
    Function.numParams, ValueType.zero]
  have hlt : UInt32.ofNat length < 2 := by
    rw [UInt32.lt_iff_toNat_lt, UInt32.toNat_ofNat_of_lt' hlength]; exact hbase
  simp only [Project.Mergesort.func2]
  wasm_twp_pures [twp_block twp_block twp_block twp_block twp_localGet twp_const]
  iapply twp_ltU (result := 1) (by simp [hlt])
  iapply twp_brIf (by decide) (by rfl)
  simp only [List.drop_zero, List.take_nil, List.nil_append]
  wasm_twp_return_from_call Hruntime [List.take_zero, List.nil_append]
  iapply Hcont $$ Hruntime

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 10000 in
theorem twp_sort
    [WasmSmallStepGS hlc Universal.State]
    {Terminal : Type} [TerminalView Universal.State Terminal]
    {s : Stuckness} {E : CoPset}
    {Φ : Terminal → IProp (WasmHeapGF Universal.State)}
    (source scratch : UInt32) (input scratchValues : List UInt32)
    (hscratchLength : scratchValues.length = input.length)
    (hlayout : Wasm.Examples.MergeSort.ValidLayout
      source scratch input.length)
    (hsourceStrict : source.toNat + 4 * input.length < UInt32.size)
    (hscratchStrict : scratch.toNat + 4 * input.length < UInt32.size)
    {callerLocals : Locals}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {stack : List Value} :
    runtimeModuleOwn ⟨0⟩ Project.Mergesort.module ∗
      arrayAt 0 source input ∗ arrayAt 0 scratch scratchValues ∗
      (∀ (output scratch' : List UInt32),
        ⌜Wasm.Examples.MergeSort.SortedPermutation input output⌝ -∗
        ⌜scratch'.length = input.length⌝ -∗
        ⌜scratch' = if input.length ≤ 1 then scratchValues else output⌝ -∗
        runtimeModuleOwn ⟨0⟩ Project.Mergesort.module -∗
        arrayAt 0 source output -∗ arrayAt 0 scratch scratch' -∗
        WP (.running
          ⟨{ callerLocals with values := stack }, code, arity, remainder,
            controls, calls⟩ : Expr Universal.State) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with
          values := .i32 (UInt32.ofNat input.length) :: .i32 scratch ::
            .i32 (UInt32.ofNat input.length) :: .i32 source :: stack },
        .call 5 :: code, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsource, Hscratch, Hfinish⟩
  by_cases hbase : input.length < 2
  · iapply twp_sort_base (length := input.length)
      (scratchLength := input.length) source scratch
      hbase hlayout.length_lt
      hlayout.length_lt
    iframe; iintro Hruntime
    have hsorted : Wasm.Examples.MergeSort.Sorted input := by
      cases input with
      | nil => simp [Wasm.Examples.MergeSort.Sorted]
      | cons head tail =>
          cases tail with
          | nil => simp [Wasm.Examples.MergeSort.Sorted]
          | cons head' tail => simp at hbase
    ihave Hdone := Hfinish $$ %input %scratchValues
      %(⟨hsorted, List.Perm.refl input⟩ :
        Wasm.Examples.MergeSort.SortedPermutation input input)
      %hscratchLength %(by simp [show input.length ≤ 1 by omega])
      Hruntime Hsource Hscratch
    iexact Hdone
  · have hlengthTwo : 2 ≤ input.length := by omega
    have hlengthSize := hlayout.length_lt
    wasm_twp_rebind Wasm.SmallStep.twp_call Project.Mergesort.module 5
      Project.Mergesort.func2Def (by decide) (by rfl) with Hruntime
    simp [Project.Mergesort.func2Def, Function.toLocals,
      Function.numParams, ValueType.zero]
    simp only [Project.Mergesort.func2]
    wasm_twp_pures [twp_block twp_block twp_block twp_block twp_localGet twp_const]
    have hnotLt : ¬UInt32.ofNat input.length < 2 := by
      rw [UInt32.lt_iff_toNat_lt,
        UInt32.toNat_ofNat_of_lt' hlengthSize,
        show (2 : UInt32).toNat = 2 by decide]
      omega
    iapply twp_ltU (result := 0) (by simp [hnotLt])
    wasm_twp_pures [twp_brIfZero]
    let mid := input.length / 2
    let left := input.take mid
    let right := input.drop mid
    let scratchLeft := scratchValues.take mid
    let scratchRight := scratchValues.drop mid
    have hmidPos : 0 < mid := by
      dsimp only [mid]; omega
    have hmidLt : mid < input.length := by
      dsimp only [mid]; omega
    have hmidLe : mid ≤ input.length := Nat.le_of_lt hmidLt
    have hleftLength : left.length = mid := by
      simp [left, Nat.min_eq_left hmidLe]
    have hrightLength : right.length = input.length - mid := by
      simp [right]
    have hscratchLeftLength : scratchLeft.length = mid := by
      simp [scratchLeft, hscratchLength, Nat.min_eq_left hmidLe]
    have hscratchRightLength :
        scratchRight.length = input.length - mid := by
      simp [scratchRight, hscratchLength]
    have hinputSplit : input = left ++ right := by
      simp [left, right]
    have hscratchSplit : scratchValues = scratchLeft ++ scratchRight := by
      simp [scratchLeft, scratchRight]
    ihave HsourceSplit :
        arrayAt 0 source left ∗
          arrayAt 0 (source + 4 * UInt32.ofNat left.length) right $$
          [Hsource]
    · iapply (arrayAt_append 0 source left right).mp
      irw_exact [← hinputSplit] with Hsource
    icases HsourceSplit with ⟨HsourceLeft, HsourceRight⟩
    ihave HscratchSplit :
        arrayAt 0 scratch scratchLeft ∗
          arrayAt 0 (scratch + 4 * UInt32.ofNat scratchLeft.length)
            scratchRight $$ [Hscratch]
    · iapply (arrayAt_append 0 scratch scratchLeft scratchRight).mp
      irw_exact [← hscratchSplit] with Hscratch
    icases HscratchSplit with ⟨HscratchLeft, HscratchRight⟩
    wasm_twp_pures [twp_block twp_block twp_localGet twp_localGet twp_const twp_shrU]
    rw [show (1 % 32 : UInt32) = 1 by decide,
      ofNat_shr_one hlengthSize]
    wasm_twp_localTee [List.length]
    have hscratchNotLt :
        ¬UInt32.ofNat input.length < UInt32.ofNat mid := by
      rw [UInt32.lt_iff_toNat_lt,
        UInt32.toNat_ofNat_of_lt' hlengthSize,
        UInt32.toNat_ofNat_of_lt' (Nat.lt_trans hmidLt hlengthSize)]
      omega
    iapply twp_ltU (result := 0) (by rw [if_neg hscratchNotLt])
    wasm_twp_pures [twp_brIfZero twp_localGet twp_localGet twp_localGet twp_localGet]
    have hleftLength' : left.length = input.length / 2 := by
      simpa only [mid] using hleftLength
    rw [← hleftLength']
    iapply twp_sort
      (callerLocals := ⟨
        [.i32 source, .i32 (UInt32.ofNat input.length), .i32 scratch,
          .i32 (UInt32.ofNat input.length)],
        ([.i32 0, .i32 0, .i32 0, .i32 0, .i32 0,
          .i32 0, .i32 0, .i32 0, .i32 0]).set
          (4 - (0 + 1 + 1 + 1 + 1)) (.i32 (UInt32.ofNat left.length)), []⟩)
      (stack := []) source scratch left scratchLeft
      (by rw [hscratchLeftLength, hleftLength])
      (validLayout_prefix hlayout (by rw [hleftLength]; exact hmidLe))
      (by
        rw [hleftLength]; omega)
      (by
        rw [hleftLength]; omega)
    isplitl_exacts [Hruntime HsourceLeft HscratchLeft]
    iintro %leftOutput %leftScratch %hleftSorted
      %hleftScratchLength %hleftScratchExact Hruntime HsourceLeft HscratchLeft
    have hleftLt : left.length < input.length := by
      simpa only [hleftLength] using hmidLt
    have hscratchLeftEq : scratchLeft.length = left.length := by
      rw [hscratchLeftLength, hleftLength]
    ihave HscratchRight' :
        arrayAt 0 (scratch + 4 * UInt32.ofNat left.length) scratchRight $$
          [HscratchRight]
    · irw_exact [← hscratchLeftEq] with HscratchRight
    wasm_twp_pures [twp_localGet twp_localGet twp_const twp_shl] rewriting [MemRegion.shl2_eq_mul4]
    wasm_twp_localTee [List.length]
    wasm_twp_pures [twp_add] rewriting [UInt32.add_comm]
    wasm_twp_localTee [List.length]
    wasm_twp_pures [twp_localGet twp_localGet twp_sub]
    rw [u32_ofNat_sub (Nat.le_of_lt hleftLt) hlengthSize]
    wasm_twp_localTee [List.length]
    wasm_twp_pures [twp_localGet twp_localGet twp_add] rewriting [UInt32.add_comm]
    wasm_twp_pures [twp_localGet twp_localGet twp_sub]
    rw [u32_ofNat_sub (Nat.le_of_lt hleftLt) hlengthSize]
    have hrightLengthLeft :
        right.length = input.length - left.length := by
      rw [hrightLength, hleftLength]
    rw [← hrightLengthLeft]
    have hsourceAddress :
        (source + 4 * UInt32.ofNat left.length).toNat =
          source.toNat + 4 * left.length := by
      simpa [UInt32.mul_comm] using
        Wasm.Examples.MergeSort.arrayAddress_toNat source
          hlayout.source_fits hleftLt
    have hscratchAddress :
        (scratch + 4 * UInt32.ofNat left.length).toNat =
          scratch.toNat + 4 * left.length := by
      simpa [UInt32.mul_comm] using
        Wasm.Examples.MergeSort.arrayAddress_toNat scratch
          hlayout.temporary_fits hleftLt
    iapply twp_sort
      (callerLocals := ⟨
        [.i32 source, .i32 (UInt32.ofNat input.length), .i32 scratch,
          .i32 (UInt32.ofNat input.length)],
        ((([.i32 0, .i32 0, .i32 0, .i32 0, .i32 0,
          .i32 0, .i32 0, .i32 0, .i32 0]).set
            (4 - (0 + 1 + 1 + 1 + 1))
            (.i32 (UInt32.ofNat left.length))).set
          (5 - (0 + 1 + 1 + 1 + 1))
          (.i32 (4 * UInt32.ofNat left.length))).set
          (6 - (0 + 1 + 1 + 1 + 1))
          (.i32 (source + 4 * UInt32.ofNat left.length)) |>.set
          (7 - (0 + 1 + 1 + 1 + 1))
          (.i32 (UInt32.ofNat right.length)), []⟩)
      (stack := [])
      (source + 4 * UInt32.ofNat left.length)
      (4 * UInt32.ofNat left.length + scratch)
      right scratchRight
      (by rw [hscratchRightLength, hrightLength])
      (by simpa [UInt32.add_comm, hrightLengthLeft] using
        validLayout_suffix hlayout hleftLt)
      (by rw [hsourceAddress, hrightLengthLeft]; omega)
      (by
        rw [UInt32.add_comm, hscratchAddress, hrightLengthLeft]; omega)
    isplitl_exacts [Hruntime HsourceRight]
    isplitl_rw_exact [UInt32.add_comm] with HscratchRight'
    iintro %rightOutput %rightScratch %hrightSorted
      %hrightScratchLength %hrightScratchExact Hruntime HsourceRight HscratchRight
    have hleftOutputLength : leftOutput.length = left.length :=
      hleftSorted.2.length_eq.symm
    have hrightOutputLength : rightOutput.length = right.length :=
      hrightSorted.2.length_eq.symm
    let combined := leftOutput ++ rightOutput
    let scratchCombined := leftScratch ++ rightScratch
    have hcombinedLength : combined.length = input.length := by
      dsimp only [combined]
      simp only [List.length_append, hleftOutputLength,
        hrightOutputLength]
      rw [hleftLength, hrightLength]; omega
    have hscratchCombinedLength :
        scratchCombined.length = combined.length := by
      dsimp only [scratchCombined, combined]
      simp only [List.length_append, hleftScratchLength,
        hrightScratchLength, hleftOutputLength, hrightOutputLength]
    ihave HsourceCombined : arrayAt 0 source combined $$
        [HsourceLeft HsourceRight]
    · dsimp only [combined]
      iapply_splitl_exact (arrayAt_append 0 source leftOutput rightOutput).mpr with HsourceLeft
      irw_exact [hleftOutputLength] with HsourceRight
    ihave HscratchCombined : arrayAt 0 scratch scratchCombined $$
        [HscratchLeft HscratchRight]
    · dsimp only [scratchCombined]
      iapply_splitl_exact (arrayAt_append 0 scratch leftScratch rightScratch).mpr with HscratchLeft
      irw_exact [hleftScratchLength, UInt32.add_comm] with HscratchRight
    wasm_twp_pures [twp_const twp_localSet] using [List.length]
    wasm_twp_pures [twp_localGet twp_localSet] using [List.length]
    wasm_twp_pures [twp_const twp_localSet] using [List.length]
    wasm_twp_pures [twp_const twp_localSet] using [List.length]
    have hleftPositive : 0 < left.length := by
      simpa only [hleftLength] using hmidPos
    have hleftCombinedLt : left.length < combined.length := by
      simpa only [hcombinedLength] using hleftLt
    have hrightCombined :
        right.length = combined.length - left.length := by
      simpa only [hcombinedLength] using hrightLengthLeft
    rw [← hcombinedLength, hrightCombined]
    simp
    ihave HmergeStart :
        WP (.running
          ⟨⟨[.i32 source, .i32 (UInt32.ofNat combined.length),
                .i32 scratch, .i32 (UInt32.ofNat combined.length)],
              [.i32 (UInt32.ofNat left.length), .i32 0,
                .i32 (source + 4 * UInt32.ofNat left.length),
                .i32 (UInt32.ofNat (combined.length - left.length)),
                .i32 scratch, .i32 0, .i32 0, .i32 0, .i32 0], []⟩,
            [.loop 0 0 mergeMainLoopBody], 0, [],
            [sortRecursiveBodyFrame, sortRecursiveGuardFrame,
              sortBlock4Frame, sortBlock3Frame, sortBlock2Frame,
              sortBlock1Frame],
            { locals := { callerLocals with values := stack },
                continuation := code, resultArity := arity,
                callerRemainder := remainder, control := controls,
                returningInstance := ⟨0⟩ } :: calls⟩ :
            Expr Universal.State) @ s; E [{ Φ }] $$
          [HsourceCombined HscratchCombined Hfinish Hruntime]
    · iapply twp_generated_merge_unfolded source scratch combined
        scratchCombined left.length hleftPositive hleftCombinedLt
        hscratchCombinedLength (by rw [hcombinedLength]; exact hlayout)
      isplitl_exacts [HsourceCombined HscratchCombined]
      iintro %output %v6 %v8 %v9 %v10 %v11 %v12 %hmerge
        HsourceCombined HscratchOutput
      have hsegmentLeft :
          Wasm.Examples.MergeSort.segment combined 0 left.length =
            leftOutput := by
        simp [Wasm.Examples.MergeSort.segment, combined,
          hleftOutputLength]
      have hsegmentRight :
          Wasm.Examples.MergeSort.segment combined left.length
              combined.length = rightOutput := by
        simp [Wasm.Examples.MergeSort.segment, combined,
          hleftOutputLength, hrightOutputLength]
      have hmergeOutputs : MergeLE leftOutput rightOutput output := by
        rw [hsegmentLeft, hsegmentRight] at hmerge; exact hmerge
      have hcombinedSorted :
          Wasm.Examples.MergeSort.SortedPermutation combined output := by
        dsimp only [combined]; exact sortedPermutation_of_mergeLE hmergeOutputs
          hleftSorted.1 hrightSorted.1
      have hinputPermCombined : List.Perm input combined := by
        rw [hinputSplit]
        dsimp only [combined]; exact hleftSorted.2.append hrightSorted.2
      have hsortedOutput :
          Wasm.Examples.MergeSort.SortedPermutation input output :=
        ⟨hcombinedSorted.1,
          hinputPermCombined.trans hcombinedSorted.2⟩
      have houtputLength : output.length = combined.length :=
        hcombinedSorted.2.length_eq.symm
      rw [sortBlock4_after_merge]
      wasm_twp_pures [twp_localGet twp_localGet]
      iapply twp_ne (result := 0) (by simp)
      wasm_twp_pures [twp_brIfZero twp_localGet twp_const twp_shl]
      rw [MemRegion.shl2_eq_mul4]
      wasm_twp_pures [twp_localTee]
      have hfourFits : 4 * combined.length < UInt32.size := by
        omega
      have hbyteLengthPositive :
          0 < (4 * UInt32.ofNat combined.length : UInt32).toNat := by
        rw [mul4_ofNat_toNat hfourFits]; omega
      have hbyteLengthNonzero :
          (4 * UInt32.ofNat combined.length : UInt32) ≠ 0 := by
        intro hz
        have := congrArg UInt32.toNat hz; rw [mul4_ofNat_toNat hfourFits] at this
        simp at this
        rw [this] at hleftCombinedLt
        simp at hleftCombinedLt
      iapply twp_eqz (result := 0) (by simp [hbyteLengthNonzero])
      wasm_twp_pures [twp_brIfZero twp_localGet twp_localGet twp_localGet]
      ihave HsourceBytes :
          pointsToBytes 0 source (arrayBytes combined) $$ [HsourceCombined]
      · iapply_exact (arrayAt_as_bytes 0 source combined).mp with HsourceCombined
      ihave HscratchBytes :
          pointsToBytes 0 scratch (arrayBytes output) $$ [HscratchOutput]
      · iapply_exact (arrayAt_as_bytes 0 scratch output).mp with HscratchOutput
      ihave Hcopy := (Wasm.SmallStep.twp_memoryCopy32
        (arrayBytes combined) (arrayBytes output)
        (by
          simp only [arrayBytes_length]
          rw [mul4_ofNat_toNat hfourFits])
        (by
          simp only [arrayBytes_length, houtputLength]
          rw [mul4_ofNat_toNat hfourFits])
        hbyteLengthPositive
        (by
          rw [mul4_ofNat_toNat hfourFits]
          rw [hcombinedLength]
          simpa [UInt32.size] using hsourceStrict)
        (by
          rw [mul4_ofNat_toNat hfourFits]
          rw [hcombinedLength]
          simpa [UInt32.size] using hscratchStrict)) $$
        HscratchBytes HsourceBytes
      iapply Hcopy
      iintro HscratchBytes HsourceBytes
      ihave HsourceOutput : arrayAt 0 source output $$ [HsourceBytes]
      · iapply_exact (arrayAt_as_bytes 0 source output).mpr with HsourceBytes
      ihave HscratchOutput : arrayAt 0 scratch output $$ [HscratchBytes]
      · iapply_exact (arrayAt_as_bytes 0 scratch output).mpr with HscratchBytes
      wasm_twp_pures [twp_exitControl]
      isimp [sortBlock4Frame, emptyBlockFrame, sortBlock4, sortBlock3,
        sortBlock2, sortBlock1, blockBodyAt, Project.Mergesort.func2]
      wasm_twp_return_from_call Hruntime
      ihave Hdone := Hfinish $$ %output %output %hsortedOutput
        %houtputLength
        %(by simp [show ¬combined.length ≤ 1 by omega])
        Hruntime HsourceOutput HscratchOutput
      isimp [List.take_zero, List.nil_append]
      iexact Hdone
    isimp [mergeMainLoopBody, sortRecursiveBodyFrame,
      sortRecursiveGuardFrame, sortBlock4Frame, sortBlock3Frame,
      sortBlock2Frame, sortBlock1Frame, emptyBlockFrame, loopBodyAt,
      sortRecursiveBody, sortRecursiveGuard, sortBlock4, sortBlock3,
      sortBlock2, sortBlock1, blockBodyAt, Project.Mergesort.func2] at HmergeStart
    iexact HmergeStart
termination_by input.length

end Project.Mergesort.SortProof
