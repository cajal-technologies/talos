import Project.Mergesort.Machine

/-!
# Function proofs for the merge-sort core

The core is split into four generated functions, mirroring the Rust source:

* `func0`: recursively merge two sorted adjacent ranges into scratch;
* `func3`: recursively copy scratch back;
* `func2`: compose merge and copy;
* `func1`: recursively sort the two halves and call `func2`.
-/

namespace Project.Mergesort.CoreProof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic
open Wasm.SmallStep
open Project.Mergesort.Pure
open Project.Mergesort.Machine

/- `UInt64` exposes the usual order operations but not the bundled proof
interface required by the generic merge invariants.  Bundle that same order
locally, keeping Wasm comparisons definitionally aligned with the proofs. -/
local instance : LinearOrder UInt64 where
  le := @LE.le UInt64 instLEUInt64
  lt := @LT.lt UInt64 instLTUInt64
  le_refl := by intro a; rw [UInt64.le_iff_toNat_le]
  le_trans := by
    intro a b c hab hbc
    rw [UInt64.le_iff_toNat_le] at hab hbc ⊢
    omega
  le_antisymm := by
    intro a b hab hba
    apply UInt64.toNat.inj
    rw [UInt64.le_iff_toNat_le] at hab hba
    omega
  lt_iff_le_not_ge := by
    intro a b
    rw [UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le,
      UInt64.le_iff_toNat_le]
    omega
  le_total := by
    intro a b
    rw [UInt64.le_iff_toNat_le, UInt64.le_iff_toNat_le]
    omega
  toDecidableLE := UInt64.decLe
  toDecidableEq := instDecidableEqUInt64
  toDecidableLT := UInt64.decLt

/-- Pure address assumptions shared by all core helpers. -/
structure ValidLayout (source scratch : UInt32) (length : Nat) : Prop where
  source_fits : source.toNat + 8 * length ≤ UInt32.size
  scratch_fits : scratch.toNat + 8 * length ≤ UInt32.size

def mergeIntoLocals (source : UInt32) (length mid : Nat)
    (scratch : UInt32) (i j k : Nat) (stack : List Value := []) : Locals :=
  ⟨[.i32 source, .i32 (UInt32.ofNat length), .i32 (UInt32.ofNat mid),
      .i32 scratch, .i32 (UInt32.ofNat i), .i32 (UInt32.ofNat j),
      .i32 (UInt32.ofNat k)],
    [.i64 0, .i64 0, .i64 0, .i64 0], stack⟩

def copyBackLocals (source scratch : UInt32) (length index : Nat)
    (stack : List Value := []) : Locals :=
  ⟨[.i32 source, .i32 scratch, .i32 (UInt32.ofNat length),
      .i32 (UInt32.ofNat index)], [.i64 0], stack⟩

def sortLocals (source : UInt32) (length : Nat) (scratch : UInt32)
    (mid : Nat := 0) (stack : List Value := []) : Locals :=
  ⟨[.i32 source, .i32 (UInt32.ofNat length), .i32 scratch],
    [.i32 (UInt32.ofNat mid)], stack⟩

theorem twp_leUI64
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {params localValues values : List Value}
    {lhs rhs : UInt64} {result : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    (hresult : result = if lhs ≤ rhs then 1 else 0) :
    WP (.running
      ⟨⟨params, localValues, .i32 result :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, .i64 rhs :: .i64 lhs :: values⟩,
        .leUI64 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.leUI64 hresult)

theorem twp_and
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {params localValues values : List Value}
    {lhs rhs : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    WP (.running
      ⟨⟨params, localValues, .i32 (lhs &&& rhs) :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, .i32 rhs :: .i32 lhs :: values⟩,
        .and :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.and)

theorem twp_leU
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {params localValues values : List Value}
    {lhs rhs result : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    (hresult : result = if lhs ≤ rhs then 1 else 0) :
    WP (.running
      ⟨⟨params, localValues, .i32 result :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, .i32 rhs :: .i32 lhs :: values⟩,
        .leU :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.leU hresult)

theorem twp_shrU
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {params localValues values : List Value}
    {lhs rhs : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    WP (.running
      ⟨⟨params, localValues, .i32 (lhs >>> (rhs % 32)) :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, .i32 rhs :: .i32 lhs :: values⟩,
        .shrU :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.shrU)

private theorem twp_copyBack_aux
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (source scratch : UInt32) (current scratchValues : List UInt64)
    (index : Nat)
    (hinv : CopyBackInvariant current scratchValues index)
    (hlayout : ValidLayout source scratch scratchValues.length)
    (n : Nat) (hmeasure : scratchValues.length - index ≤ n)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      array64At source current ∗ array64At scratch scratchValues ∗
      (runtimeModuleOwn «module» -∗
        array64At source scratchValues -∗
        array64At scratch scratchValues -∗
        WP (.running ⟨{ callerLocals with values := stack },
          code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running ⟨{ callerLocals with values :=
      (
        .i32 (UInt32.ofNat index) :: .i32 (UInt32.ofNat scratchValues.length) ::
          .i32 scratch :: .i32 source :: stack) },
      .call 5 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  induction n generalizing current index callerLocals stack code arity
      remainder controls calls with
  | zero =>
      have hfinished : index = current.length := by
        rcases hinv with ⟨hlength, hindex, _⟩
        omega
      subst index
      iintro ⟨Hruntime, Hsource, Hscratch, Hcont⟩
      ihave HruntimeLater : runtimeModuleOwn «module» $$ [Hruntime]
      · iexact Hruntime
      iapply Wasm.SmallStep.twp_call «module» 5 func3Def
        (by decide) (by rfl) $$ HruntimeLater
      iintro Hruntime
      simp [func3Def, Function.toLocals, Function.numParams,
        ValueType.zero, func3]
      iapply Wasm.SmallStep.twp_block
      iapply Wasm.SmallStep.twp_localGet rfl
      iapply Wasm.SmallStep.twp_localGet rfl
      iapply Wasm.SmallStep.twp_ltU (result := 0) (by
        rw [← hinv.1]
        simp)
      iapply Wasm.SmallStep.twp_const
      iapply twp_and
      iapply Wasm.SmallStep.twp_eqz rfl
      iapply Wasm.SmallStep.twp_brIf (by decide) rfl
      iapply Wasm.SmallStep.twp_returnFromCallExplicit
      simp only [List.take_zero, List.nil_append]
      have houtput := hinv.finished
      subst current
      iapply Hcont $$ Hruntime Hsource Hscratch
  | succ n ih =>
      iintro ⟨Hruntime, Hsource, Hscratch, Hcont⟩
      let callerFrame : CallFrame :=
        { locals := { callerLocals with values := stack }
          continuation := code
          resultArity := arity
          callerRemainder := remainder
          control := controls }
      ihave HruntimeLater : runtimeModuleOwn «module» $$ [Hruntime]
      · iexact Hruntime
      iapply Wasm.SmallStep.twp_call «module» 5 func3Def
        (by decide) (by rfl) $$ HruntimeLater
      iintro Hruntime
      simp [func3Def, Function.toLocals, Function.numParams,
        ValueType.zero, func3]
      iapply Wasm.SmallStep.twp_block
      iapply Wasm.SmallStep.twp_localGet rfl
      iapply Wasm.SmallStep.twp_localGet rfl
      have hlength : current.length = scratchValues.length := hinv.1
      have hlengthSize : scratchValues.length < UInt32.size := by
        have hfit := hlayout.source_fits
        simp only [UInt32.size] at hfit ⊢
        omega
      have hindexSize : index < UInt32.size := by
        have := hinv.2.1
        omega
      by_cases hindex : index < scratchValues.length
      · have hsourceIndex : index < current.length := by omega
        iapply Wasm.SmallStep.twp_ltU (result := 1) (by
          have hu32 : UInt32.ofNat index < UInt32.ofNat scratchValues.length := by
            simpa [UInt32.lt_iff_toNat_lt,
              UInt32.toNat_ofNat_of_lt' hindexSize,
              UInt32.toNat_ofNat_of_lt' hlengthSize] using hindex
          simp [hu32])
        iapply Wasm.SmallStep.twp_const
        iapply twp_and
        iapply Wasm.SmallStep.twp_eqz (result := 0) (by decide)
        iapply Wasm.SmallStep.twp_brIfZero
        iapply twp_load64AtShift_raw
          (baseIndex := 1) (elementIndex := 3) (base := scratch)
          (input := scratchValues) (index := index)
          hindex hlayout.scratch_fits rfl rfl
        isplitl [Hscratch]
        · iexact Hscratch
        iintro Hscratch
        iapply Wasm.SmallStep.twp_localSet rfl
        simp only [List.length_cons, List.length_nil, Nat.reduceAdd,
          Nat.reduceSub, List.set]
        iapply twp_store64AtShift_raw
          (baseIndex := 0) (elementIndex := 3) (valueIndex := 4)
          (base := source) (input := current) (index := index)
          (value := scratchValues[index])
          hsourceIndex (by simpa [hlength] using hlayout.source_fits) rfl rfl rfl
        isplitl [Hsource]
        · iexact Hsource
        iintro Hsource
        iapply Wasm.SmallStep.twp_localGet rfl
        iapply Wasm.SmallStep.twp_localGet rfl
        iapply Wasm.SmallStep.twp_localGet rfl
        iapply Wasm.SmallStep.twp_localGet rfl
        iapply Wasm.SmallStep.twp_const
        iapply Wasm.SmallStep.twp_add
        have hnextSize : index + 1 < UInt32.size := by omega
        have hnext : 1 + UInt32.ofNat index = UInt32.ofNat (index + 1) := by
          apply UInt32.toNat.inj
          simp [UInt32.toNat_add, UInt32.toNat_ofNat_of_lt' hindexSize,
            Nat.add_comm]
        rw [hnext]
        have hnextInv : CopyBackInvariant
            (current.set index scratchValues[index]) scratchValues
            (index + 1) := by
          exact hinv.step hsourceIndex hindex
        have hnextMeasure : scratchValues.length - (index + 1) ≤ n := by
          omega
        iapply ih (current.set index scratchValues[index]) (index + 1)
          hnextInv hnextMeasure
          (callerLocals :=
            ⟨[.i32 source, .i32 scratch,
                .i32 (UInt32.ofNat scratchValues.length),
                .i32 (UInt32.ofNat index)],
              [.i64 scratchValues[index]], []⟩)
          (stack := []) (code := []) (arity := 0) (remainder := [])
        isplitl [Hruntime]
        · iexact Hruntime
        isplitl [Hsource]
        · iexact Hsource
        isplitl [Hscratch]
        · iexact Hscratch
        iintro Hruntime Hsource Hscratch
        iapply Wasm.SmallStep.twp_exitControl rfl
        iapply Wasm.SmallStep.twp_returnFromCallExplicit
        simp only [List.take_zero, List.nil_append]
        iapply Hcont $$ Hruntime Hsource Hscratch
      · have hfinished : index = current.length := by
          have := hinv.2.1
          omega
        iapply Wasm.SmallStep.twp_ltU (result := 0) (by
          have hu32 : ¬UInt32.ofNat index <
              UInt32.ofNat scratchValues.length := by
            simpa [UInt32.lt_iff_toNat_lt,
              UInt32.toNat_ofNat_of_lt' hindexSize,
              UInt32.toNat_ofNat_of_lt' hlengthSize] using hindex
          simp [hu32])
        iapply Wasm.SmallStep.twp_const
        iapply twp_and
        iapply Wasm.SmallStep.twp_eqz (result := 1) (by decide)
        iapply Wasm.SmallStep.twp_brIf (by decide) rfl
        iapply Wasm.SmallStep.twp_returnFromCallExplicit
        simp only [List.take_zero, List.nil_append]
        have hinv' : CopyBackInvariant current scratchValues current.length := by
          simpa [hfinished] using hinv
        have houtput := hinv'.finished
        subst current
        iapply Hcont $$ Hruntime Hsource Hscratch

/-- Contract for generated `copy_back`: copy the entire scratch slice back to
the source while preserving both array lengths. -/
theorem twp_copyBack
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (source scratch : UInt32) (current scratchValues : List UInt64)
    (index : Nat)
    (hinv : CopyBackInvariant current scratchValues index)
    (hlayout : ValidLayout source scratch current.length)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      array64At source current ∗ array64At scratch scratchValues ∗
      (runtimeModuleOwn «module» -∗
        array64At source scratchValues -∗
        array64At scratch scratchValues -∗
        WP (.running ⟨{ callerLocals with values := stack },
          code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running ⟨{ callerLocals with values :=
      (
        .i32 (UInt32.ofNat index) :: .i32 (UInt32.ofNat current.length) ::
          .i32 scratch :: .i32 source :: stack) },
      .call 5 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] :=
  by
    simpa only [hinv.1] using
      (twp_copyBack_aux source scratch current scratchValues index hinv
        (by simpa only [hinv.1] using hlayout)
        (scratchValues.length - index) (Nat.le_refl _))

set_option maxHeartbeats 8000000 in
private theorem twp_mergeInto_aux
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (source scratch : UInt32) (input scratchValues : List UInt64)
    (mid i j k : Nat) (emitted : List UInt64)
    (hinv : MergeLoopInvariant input scratchValues 0 mid input.length
      i j k emitted)
    (hlayout : ValidLayout source scratch input.length)
    (n : Nat) (hmeasure : (mid - i) + (input.length - j) ≤ n)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      array64At source input ∗ array64At scratch scratchValues ∗
      (∀ (output result : List UInt64),
        ⌜MergeLoopInvariant input output 0 mid input.length
          mid input.length input.length result⌝ -∗
        runtimeModuleOwn «module» -∗
        array64At source input -∗ array64At scratch output -∗
        WP (.running ⟨{ callerLocals with values := stack },
          code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running ⟨{ callerLocals with values :=
      (.i32 (UInt32.ofNat k) :: .i32 (UInt32.ofNat j) ::
        .i32 (UInt32.ofNat i) :: .i32 scratch ::
        .i32 (UInt32.ofNat mid) :: .i32 (UInt32.ofNat input.length) ::
        .i32 source :: stack) },
      .call 2 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  induction n generalizing scratchValues i j k emitted callerLocals stack
      code arity remainder controls calls with
  | zero =>
      have hi : i = mid := by
        unfold MergeLoopInvariant at hinv
        omega
      have hj : j = input.length := by
        unfold MergeLoopInvariant at hinv
        omega
      subst i
      subst j
      have hk : k = input.length := (hinv.finished).1
      subst k
      iintro ⟨Hruntime, Hsource, Hscratch, Hcont⟩
      ihave HruntimeLater : runtimeModuleOwn «module» $$ [Hruntime]
      · iexact Hruntime
      iapply Wasm.SmallStep.twp_call «module» 2 func0Def
        (by decide) (by rfl) $$ HruntimeLater
      iintro Hruntime
      simp [func0Def, Function.toLocals, Function.numParams,
        ValueType.zero, func0]
      iapply Wasm.SmallStep.twp_block
      iapply Wasm.SmallStep.twp_block
      iapply Wasm.SmallStep.twp_localGet rfl
      iapply Wasm.SmallStep.twp_localGet rfl
      iapply Wasm.SmallStep.twp_ltU (result := 0) (by simp)
      iapply Wasm.SmallStep.twp_const
      iapply twp_and
      iapply Wasm.SmallStep.twp_eqz (result := 1) (by decide)
      iapply Wasm.SmallStep.twp_brIf (by decide) rfl
      iapply Wasm.SmallStep.twp_block
      iapply Wasm.SmallStep.twp_block
      iapply Wasm.SmallStep.twp_localGet rfl
      iapply Wasm.SmallStep.twp_localGet rfl
      iapply Wasm.SmallStep.twp_ltU (result := 0) (by simp)
      iapply Wasm.SmallStep.twp_const
      iapply twp_and
      rw [UInt32.zero_and]
      iapply Wasm.SmallStep.twp_brIfZero
      iapply Wasm.SmallStep.twp_localGet rfl
      iapply Wasm.SmallStep.twp_localGet rfl
      iapply Wasm.SmallStep.twp_ltU (result := 0) (by simp)
      iapply Wasm.SmallStep.twp_const
      iapply twp_and
      rw [UInt32.zero_and]
      iapply Wasm.SmallStep.twp_brIfZero
      iapply Wasm.SmallStep.twp_br rfl
      iapply Wasm.SmallStep.twp_returnFromCallExplicit
      simp only [List.take_zero, List.nil_append]
      iapply Hcont $$ %scratchValues %emitted %hinv Hruntime Hsource Hscratch
  | succ n ih =>
      have hdata := hinv
      unfold MergeLoopInvariant at hdata
      have hlength : scratchValues.length = input.length := hdata.2.2.2.2.2.1
      have him : i ≤ mid := hdata.2.1
      have hmj : mid ≤ j := hdata.2.2.1
      have hjr : j ≤ input.length := hdata.2.2.2.1
      have hlengthSize : input.length < UInt32.size := by
        have hfit := hlayout.source_fits
        simp only [UInt32.size] at hfit ⊢
        omega
      have hmidSize : mid < UInt32.size := by omega
      have hiSize : i < UInt32.size := by omega
      have hjSize : j < UInt32.size := by omega
      iintro ⟨Hruntime, Hsource, Hscratch, Hcont⟩
      ihave HruntimeLater : runtimeModuleOwn «module» $$ [Hruntime]
      · iexact Hruntime
      iapply Wasm.SmallStep.twp_call «module» 2 func0Def
        (by decide) (by rfl) $$ HruntimeLater
      iintro Hruntime
      simp [func0Def, Function.toLocals, Function.numParams,
        ValueType.zero, func0]
      iapply Wasm.SmallStep.twp_block
      iapply Wasm.SmallStep.twp_block
      iapply Wasm.SmallStep.twp_localGet rfl
      iapply Wasm.SmallStep.twp_localGet rfl
      by_cases hi : i < mid
      · iapply Wasm.SmallStep.twp_ltU (result := 1) (by
          have hu32 : UInt32.ofNat i < UInt32.ofNat mid := by
            simpa [UInt32.lt_iff_toNat_lt,
              UInt32.toNat_ofNat_of_lt' hiSize,
              UInt32.toNat_ofNat_of_lt' hmidSize] using hi
          simp [hu32])
        iapply Wasm.SmallStep.twp_const
        iapply twp_and
        iapply Wasm.SmallStep.twp_eqz (result := 0) (by decide)
        iapply Wasm.SmallStep.twp_brIfZero
        iapply Wasm.SmallStep.twp_localGet rfl
        iapply Wasm.SmallStep.twp_localGet rfl
        by_cases hj : j < input.length
        · iapply Wasm.SmallStep.twp_ltU (result := 1) (by
            have hu32 : UInt32.ofNat j < UInt32.ofNat input.length := by
              simpa [UInt32.lt_iff_toNat_lt,
                UInt32.toNat_ofNat_of_lt' hjSize,
                UInt32.toNat_ofNat_of_lt' hlengthSize] using hj
            simp [hu32])
          iapply Wasm.SmallStep.twp_const
          iapply twp_and
          iapply Wasm.SmallStep.twp_eqz (result := 0) (by decide)
          iapply Wasm.SmallStep.twp_brIfZero
          have hiLen : i < input.length := by omega
          iapply twp_load64AtShift_raw
            (baseIndex := 0) (elementIndex := 4) (base := source)
            (input := input) (index := i) hiLen hlayout.source_fits rfl rfl
          isplitl [Hsource]
          · iexact Hsource
          iintro Hsource
          iapply Wasm.SmallStep.twp_localSet rfl
          simp only [List.length_cons, List.length_nil, Nat.reduceAdd,
            Nat.reduceSub, List.set]
          iapply twp_load64AtShift_raw
            (baseIndex := 0) (elementIndex := 5) (base := source)
            (input := input) (index := j) hj hlayout.source_fits rfl rfl
          isplitl [Hsource]
          · iexact Hsource
          iintro Hsource
          iapply Wasm.SmallStep.twp_localSet rfl
          simp only [List.length_cons, List.length_nil, Nat.reduceAdd,
            Nat.reduceSub, List.set]
          iapply Wasm.SmallStep.twp_block
          iapply Wasm.SmallStep.twp_localGet rfl
          iapply Wasm.SmallStep.twp_localGet rfl
          by_cases hxy : input[i] ≤ input[j]
          · iapply twp_leUI64 (result := 1) (by simp [hxy])
            iapply Wasm.SmallStep.twp_const
            iapply twp_and
            rw [show (1 : UInt32) &&& 1 = 1 by decide]
            iapply Wasm.SmallStep.twp_brIf (by decide) rfl
            simp only [List.take_zero, List.nil_append, List.drop_zero]
            have hkLen : k < scratchValues.length := by
              rw [hlength]
              exact hinv.k_lt hi hj
            iapply twp_store64AtShift_raw
              (baseIndex := 3) (elementIndex := 6) (valueIndex := 7)
              (base := scratch) (input := scratchValues) (index := k)
              (value := input[i]) hkLen
              (by simpa [hlength] using hlayout.scratch_fits) rfl rfl rfl
            isplitl [Hscratch]
            · iexact Hscratch
            iintro Hscratch
            iapply Wasm.SmallStep.twp_localGet rfl
            iapply Wasm.SmallStep.twp_localGet rfl
            iapply Wasm.SmallStep.twp_localGet rfl
            iapply Wasm.SmallStep.twp_localGet rfl
            iapply Wasm.SmallStep.twp_localGet rfl
            iapply Wasm.SmallStep.twp_const
            iapply Wasm.SmallStep.twp_add
            have hiNextSize : i + 1 < UInt32.size := by omega
            have hiNext : 1 + UInt32.ofNat i = UInt32.ofNat (i + 1) := by
              apply UInt32.toNat.inj
              simp [UInt32.toNat_add, UInt32.toNat_ofNat_of_lt' hiSize,
                Nat.add_comm]
            rw [hiNext]
            iapply Wasm.SmallStep.twp_localGet rfl
            iapply Wasm.SmallStep.twp_localGet rfl
            iapply Wasm.SmallStep.twp_const
            iapply Wasm.SmallStep.twp_add
            have hkSize : k < UInt32.size := by omega
            have hkNextSize : k + 1 < UInt32.size := by omega
            have hkNext : 1 + UInt32.ofNat k = UInt32.ofNat (k + 1) := by
              apply UInt32.toNat.inj
              simp [UInt32.toNat_add, UInt32.toNat_ofNat_of_lt' hkSize,
                Nat.add_comm]
            rw [hkNext]
            have hnextInv : MergeLoopInvariant input
                (scratchValues.set k input[i]) 0 mid input.length
                (i + 1) j (k + 1) (emitted ++ [input[i]]) := by
              exact hinv.takeLeft hi hj
                (List.getElem?_eq_getElem hiLen)
                (List.getElem?_eq_getElem hj) hxy
            have hnextMeasure :
                (mid - (i + 1)) + (input.length - j) ≤ n := by omega
            iapply ih (scratchValues.set k input[i]) (i + 1) j (k + 1)
              (emitted ++ [input[i]]) hnextInv hnextMeasure
              (callerLocals :=
                ⟨[.i32 source, .i32 (UInt32.ofNat input.length),
                    .i32 (UInt32.ofNat mid), .i32 scratch,
                    .i32 (UInt32.ofNat i), .i32 (UInt32.ofNat j),
                    .i32 (UInt32.ofNat k)],
                  [.i64 input[i], .i64 input[j], .i64 0, .i64 0], []⟩)
              (stack := []) (code := [.br 1]) (arity := 0)
              (remainder := [])
            isplitl [Hruntime]
            · iexact Hruntime
            isplitl [Hsource]
            · iexact Hsource
            isplitl [Hscratch]
            · iexact Hscratch
            iintro %output %result %hfinal Hruntime Hsource Hscratch
            iapply Wasm.SmallStep.twp_br rfl
            iapply Wasm.SmallStep.twp_returnFromCallExplicit
            simp only [List.take_zero, List.nil_append]
            iapply Hcont $$ %output %result %hfinal Hruntime Hsource Hscratch
          · iapply twp_leUI64 (result := 0) (by simp [hxy])
            iapply Wasm.SmallStep.twp_const
            iapply twp_and
            rw [UInt32.zero_and]
            iapply Wasm.SmallStep.twp_brIfZero
            have hkLen : k < scratchValues.length := by
              rw [hlength]
              exact hinv.k_lt hi hj
            iapply twp_store64AtShift_raw
              (baseIndex := 3) (elementIndex := 6) (valueIndex := 8)
              (base := scratch) (input := scratchValues) (index := k)
              (value := input[j]) hkLen
              (by simpa [hlength] using hlayout.scratch_fits) rfl rfl rfl
            isplitl [Hscratch]
            · iexact Hscratch
            iintro Hscratch
            iapply Wasm.SmallStep.twp_localGet rfl
            iapply Wasm.SmallStep.twp_localGet rfl
            iapply Wasm.SmallStep.twp_localGet rfl
            iapply Wasm.SmallStep.twp_localGet rfl
            iapply Wasm.SmallStep.twp_localGet rfl
            iapply Wasm.SmallStep.twp_localGet rfl
            iapply Wasm.SmallStep.twp_const
            iapply Wasm.SmallStep.twp_add
            have hjNextSize : j + 1 < UInt32.size := by omega
            have hjNext : 1 + UInt32.ofNat j = UInt32.ofNat (j + 1) := by
              apply UInt32.toNat.inj
              simp [UInt32.toNat_add, UInt32.toNat_ofNat_of_lt' hjSize,
                Nat.add_comm]
            rw [hjNext]
            iapply Wasm.SmallStep.twp_localGet rfl
            iapply Wasm.SmallStep.twp_const
            iapply Wasm.SmallStep.twp_add
            have hkSize : k < UInt32.size := by omega
            have hkNextSize : k + 1 < UInt32.size := by omega
            have hkNext : 1 + UInt32.ofNat k = UInt32.ofNat (k + 1) := by
              apply UInt32.toNat.inj
              simp [UInt32.toNat_add, UInt32.toNat_ofNat_of_lt' hkSize,
                Nat.add_comm]
            rw [hkNext]
            have hnextInv : MergeLoopInvariant input
                (scratchValues.set k input[j]) 0 mid input.length
                i (j + 1) (k + 1) (emitted ++ [input[j]]) := by
              exact hinv.takeRight hi hj
                (List.getElem?_eq_getElem hiLen)
                (List.getElem?_eq_getElem hj) hxy
            have hnextMeasure :
                (mid - i) + (input.length - (j + 1)) ≤ n := by omega
            iapply ih (scratchValues.set k input[j]) i (j + 1) (k + 1)
              (emitted ++ [input[j]]) hnextInv hnextMeasure
              (callerLocals :=
                ⟨[.i32 source, .i32 (UInt32.ofNat input.length),
                    .i32 (UInt32.ofNat mid), .i32 scratch,
                    .i32 (UInt32.ofNat i), .i32 (UInt32.ofNat j),
                    .i32 (UInt32.ofNat k)],
                  [.i64 input[i], .i64 input[j], .i64 0, .i64 0], []⟩)
              (stack := []) (code := [.br 2]) (arity := 0)
              (remainder := [])
            isplitl [Hruntime]
            · iexact Hruntime
            isplitl [Hsource]
            · iexact Hsource
            isplitl [Hscratch]
            · iexact Hscratch
            iintro %output %result %hfinal Hruntime Hsource Hscratch
            iapply Wasm.SmallStep.twp_br rfl
            iapply Wasm.SmallStep.twp_returnFromCallExplicit
            simp only [List.take_zero, List.nil_append]
            iapply Hcont $$ %output %result %hfinal Hruntime Hsource Hscratch
        · have hjEq : j = input.length := by omega
          subst j
          iapply Wasm.SmallStep.twp_ltU (result := 0) (by
            have hu32 : ¬UInt32.ofNat input.length <
                UInt32.ofNat input.length := by simp
            simp [hu32])
          iapply Wasm.SmallStep.twp_const
          iapply twp_and
          iapply Wasm.SmallStep.twp_eqz (result := 1) (by decide)
          iapply Wasm.SmallStep.twp_brIf (by decide) rfl
          simp only [List.take_zero, List.nil_append, List.drop_zero]
          iapply Wasm.SmallStep.twp_block
          iapply Wasm.SmallStep.twp_block
          iapply Wasm.SmallStep.twp_localGet rfl
          iapply Wasm.SmallStep.twp_localGet rfl
          iapply Wasm.SmallStep.twp_ltU (result := 1) (by
            have hu32 : UInt32.ofNat i < UInt32.ofNat mid := by
              simpa [UInt32.lt_iff_toNat_lt,
                UInt32.toNat_ofNat_of_lt' hiSize,
                UInt32.toNat_ofNat_of_lt' hmidSize] using hi
            simp [hu32])
          iapply Wasm.SmallStep.twp_const
          iapply twp_and
          rw [show (1 : UInt32) &&& 1 = 1 by decide]
          iapply Wasm.SmallStep.twp_brIf (by decide) rfl
          simp only [List.take_zero, List.nil_append, List.drop_zero]
          have hiLen : i < input.length := by omega
          iapply twp_load64AtShift_raw
            (baseIndex := 0) (elementIndex := 4) (base := source)
            (input := input) (index := i) hiLen hlayout.source_fits rfl rfl
          isplitl [Hsource]
          · iexact Hsource
          iintro Hsource
          iapply Wasm.SmallStep.twp_localSet rfl
          simp only [List.length_cons, List.length_nil, Nat.reduceAdd,
            Nat.reduceSub, List.set]
          have hkLen : k < scratchValues.length := by
            rw [hlength]
            unfold MergeLoopInvariant at hinv
            omega
          iapply twp_store64AtShift_raw
            (baseIndex := 3) (elementIndex := 6) (valueIndex := 9)
            (base := scratch) (input := scratchValues) (index := k)
            (value := input[i]) hkLen
            (by simpa [hlength] using hlayout.scratch_fits) rfl rfl rfl
          isplitl [Hscratch]
          · iexact Hscratch
          iintro Hscratch
          iapply Wasm.SmallStep.twp_localGet rfl
          iapply Wasm.SmallStep.twp_localGet rfl
          iapply Wasm.SmallStep.twp_localGet rfl
          iapply Wasm.SmallStep.twp_localGet rfl
          iapply Wasm.SmallStep.twp_localGet rfl
          iapply Wasm.SmallStep.twp_const
          iapply Wasm.SmallStep.twp_add
          have hiNextSize : i + 1 < UInt32.size := by omega
          have hiNext : 1 + UInt32.ofNat i = UInt32.ofNat (i + 1) := by
            apply UInt32.toNat.inj
            simp [UInt32.toNat_add, UInt32.toNat_ofNat_of_lt' hiSize,
              Nat.add_comm]
          rw [hiNext]
          iapply Wasm.SmallStep.twp_localGet rfl
          iapply Wasm.SmallStep.twp_localGet rfl
          iapply Wasm.SmallStep.twp_const
          iapply Wasm.SmallStep.twp_add
          have hkSize : k < UInt32.size := by omega
          have hkNextSize : k + 1 < UInt32.size := by omega
          have hkNext : 1 + UInt32.ofNat k = UInt32.ofNat (k + 1) := by
            apply UInt32.toNat.inj
            simp [UInt32.toNat_add, UInt32.toNat_ofNat_of_lt' hkSize,
              Nat.add_comm]
          rw [hkNext]
          have hnextInv : MergeLoopInvariant input
              (scratchValues.set k input[i]) 0 mid input.length
              (i + 1) input.length (k + 1)
              (emitted ++ [input[i]]) := by
            exact hinv.takeRemainingLeft hi
              (List.getElem?_eq_getElem hiLen)
          have hnextMeasure :
              (mid - (i + 1)) + (input.length - input.length) ≤ n := by
            omega
          iapply ih (scratchValues.set k input[i]) (i + 1) input.length
            (k + 1) (emitted ++ [input[i]]) hnextInv hnextMeasure
            (callerLocals :=
              ⟨[.i32 source, .i32 (UInt32.ofNat input.length),
                  .i32 (UInt32.ofNat mid), .i32 scratch,
                  .i32 (UInt32.ofNat i),
                  .i32 (UInt32.ofNat input.length),
                  .i32 (UInt32.ofNat k)],
                [.i64 0, .i64 0, .i64 input[i], .i64 0], []⟩)
            (stack := []) (code := [.br 1]) (arity := 0)
            (remainder := [])
          isplitl [Hruntime]
          · iexact Hruntime
          isplitl [Hsource]
          · iexact Hsource
          isplitl [Hscratch]
          · iexact Hscratch
          iintro %output %result %hfinal Hruntime Hsource Hscratch
          iapply Wasm.SmallStep.twp_br rfl
          iapply Wasm.SmallStep.twp_returnFromCallExplicit
          simp only [List.take_zero, List.nil_append]
          iapply Hcont $$ %output %result %hfinal Hruntime Hsource Hscratch
      · have hiEq : i = mid := by omega
        subst i
        iapply Wasm.SmallStep.twp_ltU (result := 0) (by simp)
        iapply Wasm.SmallStep.twp_const
        iapply twp_and
        iapply Wasm.SmallStep.twp_eqz (result := 1) (by decide)
        iapply Wasm.SmallStep.twp_brIf (by decide) rfl
        simp only [List.take_zero, List.nil_append, List.drop_zero]
        iapply Wasm.SmallStep.twp_block
        iapply Wasm.SmallStep.twp_block
        iapply Wasm.SmallStep.twp_localGet rfl
        iapply Wasm.SmallStep.twp_localGet rfl
        iapply Wasm.SmallStep.twp_ltU (result := 0) (by simp)
        iapply Wasm.SmallStep.twp_const
        iapply twp_and
        rw [UInt32.zero_and]
        iapply Wasm.SmallStep.twp_brIfZero
        iapply Wasm.SmallStep.twp_localGet rfl
        iapply Wasm.SmallStep.twp_localGet rfl
        by_cases hj : j < input.length
        · iapply Wasm.SmallStep.twp_ltU (result := 1) (by
            have hu32 : UInt32.ofNat j < UInt32.ofNat input.length := by
              simpa [UInt32.lt_iff_toNat_lt,
                UInt32.toNat_ofNat_of_lt' hjSize,
                UInt32.toNat_ofNat_of_lt' hlengthSize] using hj
            simp [hu32])
          iapply Wasm.SmallStep.twp_const
          iapply twp_and
          rw [show (1 : UInt32) &&& 1 = 1 by decide]
          iapply Wasm.SmallStep.twp_brIf (by decide) rfl
          simp only [List.take_zero, List.nil_append, List.drop_zero]
          iapply twp_load64AtShift_raw
            (baseIndex := 0) (elementIndex := 5) (base := source)
            (input := input) (index := j) hj hlayout.source_fits rfl rfl
          isplitl [Hsource]
          · iexact Hsource
          iintro Hsource
          iapply Wasm.SmallStep.twp_localSet rfl
          simp only [List.length_cons, List.length_nil, Nat.reduceAdd,
            Nat.reduceSub, List.set]
          have hkLen : k < scratchValues.length := by
            rw [hlength]
            unfold MergeLoopInvariant at hinv
            omega
          iapply twp_store64AtShift_raw
            (baseIndex := 3) (elementIndex := 6) (valueIndex := 10)
            (base := scratch) (input := scratchValues) (index := k)
            (value := input[j]) hkLen
            (by simpa [hlength] using hlayout.scratch_fits) rfl rfl rfl
          isplitl [Hscratch]
          · iexact Hscratch
          iintro Hscratch
          iapply Wasm.SmallStep.twp_localGet rfl
          iapply Wasm.SmallStep.twp_localGet rfl
          iapply Wasm.SmallStep.twp_localGet rfl
          iapply Wasm.SmallStep.twp_localGet rfl
          iapply Wasm.SmallStep.twp_localGet rfl
          iapply Wasm.SmallStep.twp_localGet rfl
          iapply Wasm.SmallStep.twp_const
          iapply Wasm.SmallStep.twp_add
          have hjNextSize : j + 1 < UInt32.size := by omega
          have hjNext : 1 + UInt32.ofNat j = UInt32.ofNat (j + 1) := by
            apply UInt32.toNat.inj
            simp [UInt32.toNat_add, UInt32.toNat_ofNat_of_lt' hjSize,
              Nat.add_comm]
          rw [hjNext]
          iapply Wasm.SmallStep.twp_localGet rfl
          iapply Wasm.SmallStep.twp_const
          iapply Wasm.SmallStep.twp_add
          have hkSize : k < UInt32.size := by omega
          have hkNextSize : k + 1 < UInt32.size := by omega
          have hkNext : 1 + UInt32.ofNat k = UInt32.ofNat (k + 1) := by
            apply UInt32.toNat.inj
            simp [UInt32.toNat_add, UInt32.toNat_ofNat_of_lt' hkSize,
              Nat.add_comm]
          rw [hkNext]
          have hnextInv : MergeLoopInvariant input
              (scratchValues.set k input[j]) 0 mid input.length
              mid (j + 1) (k + 1) (emitted ++ [input[j]]) := by
            exact hinv.takeRemainingRight hj
              (List.getElem?_eq_getElem hj)
          have hnextMeasure :
              (mid - mid) + (input.length - (j + 1)) ≤ n := by omega
          iapply ih (scratchValues.set k input[j]) mid (j + 1) (k + 1)
            (emitted ++ [input[j]]) hnextInv hnextMeasure
            (callerLocals :=
              ⟨[.i32 source, .i32 (UInt32.ofNat input.length),
                  .i32 (UInt32.ofNat mid), .i32 scratch,
                  .i32 (UInt32.ofNat mid), .i32 (UInt32.ofNat j),
                  .i32 (UInt32.ofNat k)],
                [.i64 0, .i64 0, .i64 0, .i64 input[j]], []⟩)
            (stack := []) (code := []) (arity := 0) (remainder := [])
          isplitl [Hruntime]
          · iexact Hruntime
          isplitl [Hsource]
          · iexact Hsource
          isplitl [Hscratch]
          · iexact Hscratch
          iintro %output %result %hfinal Hruntime Hsource Hscratch
          iapply Wasm.SmallStep.twp_exitControl rfl
          iapply Wasm.SmallStep.twp_returnFromCallExplicit
          simp only [List.take_zero, List.nil_append]
          iapply Hcont $$ %output %result %hfinal Hruntime Hsource Hscratch
        · have hjEq : j = input.length := by omega
          subst j
          iapply Wasm.SmallStep.twp_ltU (result := 0) (by simp)
          iapply Wasm.SmallStep.twp_const
          iapply twp_and
          rw [UInt32.zero_and]
          iapply Wasm.SmallStep.twp_brIfZero
          iapply Wasm.SmallStep.twp_br rfl
          iapply Wasm.SmallStep.twp_returnFromCallExplicit
          simp only [List.take_zero, List.nil_append]
          have hk : k = input.length := (hinv.finished).1
          subst k
          iapply Hcont $$ %scratchValues %emitted %hinv Hruntime Hsource Hscratch

/-- Contract for generated `merge_into`: scratch becomes the stable merge of
the two adjacent source halves. -/
theorem twp_mergeInto
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (source scratch : UInt32) (input scratchValues : List UInt64)
    (mid : Nat) (hmid : mid ≤ input.length)
    (hscratchLength : scratchValues.length = input.length)
    (hlayout : ValidLayout source scratch input.length)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      array64At source input ∗ array64At scratch scratchValues ∗
      (∀ output : List UInt64,
        ⌜output.length = input.length ∧
          MergeRel (input.take mid) (input.drop mid) output⌝ -∗
        runtimeModuleOwn «module» -∗
        array64At source input -∗ array64At scratch output -∗
        WP (.running ⟨{ callerLocals with values := stack },
          code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running ⟨{ callerLocals with values :=
      (.i32 0 :: .i32 (UInt32.ofNat mid) :: .i32 0 :: .i32 scratch ::
        .i32 (UInt32.ofNat mid) :: .i32 (UInt32.ofNat input.length) ::
        .i32 source :: stack) },
      .call 2 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  have hinv : MergeLoopInvariant input scratchValues 0 mid input.length
      0 mid 0 [] :=
    mergeLoopInvariant_start ⟨by omega, hmid, by simp⟩ hscratchLength
  iintro ⟨Hruntime, Hsource, Hscratch, Hcont⟩
  iapply twp_mergeInto_aux source scratch input scratchValues mid 0 mid 0 []
    hinv hlayout (mid + (input.length - mid)) (Nat.le_refl _)
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hsource]
  · iexact Hsource
  isplitl [Hscratch]
  · iexact Hscratch
  iintro %scratchOutput %result %hfinal Hruntime Hsource Hscratch
  have hfinished := hfinal.finished
  have houtputLength : scratchOutput.length = input.length := by
    unfold MergeLoopInvariant at hfinal
    exact hfinal.2.2.2.2.2.1
  have houtput : scratchOutput = result := by
    have htake := hfinished.2.1
    simp only [List.take_zero, List.nil_append] at htake
    rw [← houtputLength, List.take_length] at htake
    exact htake
  subst scratchOutput
  have hmerge : MergeRel (input.take mid) (input.drop mid) result := by
    have htakeDrop : (input.drop mid).take (input.length - mid) =
        input.drop mid := by
      rw [← List.length_drop]
      exact List.take_length
    simpa [Pure.segment, htakeDrop] using hfinished.2.2
  iapply Hcont $$ %result %⟨houtputLength, hmerge⟩ Hruntime Hsource Hscratch

/-- Contract for generated `merge_raw`: merge into scratch, then copy the
merged result back over the source slice. -/
theorem twp_mergeRaw
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (source scratch : UInt32) (input scratchValues : List UInt64)
    (length : Nat) (hinputLength : input.length = length)
    (mid : Nat) (hmid : mid ≤ input.length)
    (hscratchLength : scratchValues.length = input.length)
    (hlayout : ValidLayout source scratch input.length)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      array64At source input ∗ array64At scratch scratchValues ∗
      (∀ output : List UInt64,
        ⌜output.length = input.length ∧
          MergeRel (input.take mid) (input.drop mid) output⌝ -∗
        runtimeModuleOwn «module» -∗
        array64At source output -∗ array64At scratch output -∗
        WP (.running ⟨{ callerLocals with values := stack },
          code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running ⟨{ callerLocals with values :=
      (.i32 scratch :: .i32 (UInt32.ofNat mid) ::
        .i32 (UInt32.ofNat length) :: .i32 source :: stack) },
      .call 4 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  subst length
  iintro ⟨Hruntime, Hsource, Hscratch, Hcont⟩
  ihave HruntimeLater : runtimeModuleOwn «module» $$ [Hruntime]
  · iexact Hruntime
  iapply Wasm.SmallStep.twp_call «module» 4 func2Def
    (by decide) (by rfl) $$ HruntimeLater
  iintro Hruntime
  simp [func2Def, Function.toLocals, Function.numParams,
    ValueType.zero, func2]
  iapply Wasm.SmallStep.twp_const
  iapply Wasm.SmallStep.twp_localSet rfl
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  iapply Wasm.SmallStep.twp_localGet rfl
  iapply Wasm.SmallStep.twp_localGet rfl
  iapply Wasm.SmallStep.twp_localGet rfl
  iapply Wasm.SmallStep.twp_localGet rfl
  iapply Wasm.SmallStep.twp_localGet rfl
  iapply Wasm.SmallStep.twp_localGet rfl
  iapply Wasm.SmallStep.twp_localGet rfl
  iapply twp_mergeInto source scratch input scratchValues mid hmid
    hscratchLength hlayout
    (callerLocals :=
      ⟨[.i32 source, .i32 (UInt32.ofNat input.length),
          .i32 (UInt32.ofNat mid), .i32 scratch], [.i32 0], []⟩)
    (stack := [])
    (code := [.localGet 0, .localGet 3, .localGet 1, .const 0,
      .call 5, .ret]) (arity := 0) (remainder := [])
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hsource]
  · iexact Hsource
  isplitl [Hscratch]
  · iexact Hscratch
  iintro %output %houtput Hruntime Hsource Hscratch
  iapply Wasm.SmallStep.twp_localGet rfl
  iapply Wasm.SmallStep.twp_localGet rfl
  iapply Wasm.SmallStep.twp_localGet rfl
  iapply Wasm.SmallStep.twp_const
  have hcopyInv : CopyBackInvariant input output 0 := by
    exact ⟨by omega, by simp, by simp⟩
  iapply twp_copyBack source scratch input output 0 hcopyInv hlayout
    (callerLocals :=
      ⟨[.i32 source, .i32 (UInt32.ofNat input.length),
          .i32 (UInt32.ofNat mid), .i32 scratch], [.i32 0], []⟩)
    (stack := []) (code := [.ret]) (arity := 0) (remainder := [])
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hsource]
  · iexact Hsource
  isplitl [Hscratch]
  · iexact Hscratch
  iintro Hruntime Hsource Hscratch
  iapply Wasm.SmallStep.twp_returnFromCallExplicit
  simp only [List.take_zero, List.nil_append]
  iapply Hcont $$ %output %houtput Hruntime Hsource Hscratch

private theorem twp_mergesortRaw_base
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (source scratch : UInt32) (input scratchValues : List UInt64)
    (hbase : input.length ≤ 1)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      array64At source input ∗ array64At scratch scratchValues ∗
      (∀ (output scratchOutput : List UInt64),
        ⌜output.length = input.length ∧
          scratchOutput.length = scratchValues.length ∧
          SortedPermutation input output⌝ -∗
        runtimeModuleOwn «module» -∗
        array64At source output -∗ array64At scratch scratchOutput -∗
        WP (.running ⟨{ callerLocals with values := stack },
          code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running ⟨{ callerLocals with values :=
      (.i32 scratch :: .i32 (UInt32.ofNat input.length) ::
        .i32 source :: stack) },
      .call 3 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsource, Hscratch, Hcont⟩
  ihave HruntimeLater : runtimeModuleOwn «module» $$ [Hruntime]
  · iexact Hruntime
  iapply Wasm.SmallStep.twp_call «module» 3 func1Def
    (by decide) (by rfl) $$ HruntimeLater
  iintro Hruntime
  simp [func1Def, Function.toLocals, Function.numParams,
    ValueType.zero, func1]
  iapply Wasm.SmallStep.twp_block
  iapply Wasm.SmallStep.twp_localGet rfl
  iapply Wasm.SmallStep.twp_const
  iapply twp_leU (result := 1) (by
    have hu32 : UInt32.ofNat input.length ≤ 1 := by
      interval_cases input.length <;> decide
    simp [hu32])
  iapply Wasm.SmallStep.twp_const
  iapply twp_and
  rw [show (1 : UInt32) &&& 1 = 1 by decide]
  iapply Wasm.SmallStep.twp_brIf (by decide) rfl
  iapply Wasm.SmallStep.twp_returnFromCallExplicit
  simp only [List.take_zero, List.nil_append]
  have hpure : input.length = input.length ∧
      scratchValues.length = scratchValues.length ∧
      SortedPermutation input input :=
    ⟨rfl, rfl, Pure.sorted_of_length_le_one hbase, List.Perm.refl _⟩
  iapply Hcont $$ %input %scratchValues %hpure Hruntime Hsource Hscratch

set_option maxHeartbeats 12000000 in
private theorem twp_mergesortRaw_aux
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (source scratch : UInt32) (input scratchValues : List UInt64)
    (length : Nat) (hinputLength : input.length = length)
    (hscratchLength : scratchValues.length = input.length)
    (hlayout : ValidLayout source scratch input.length)
    (n : Nat) (hmeasure : input.length ≤ n)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      array64At source input ∗ array64At scratch scratchValues ∗
      (∀ (output scratchOutput : List UInt64),
        ⌜output.length = input.length ∧
          scratchOutput.length = input.length ∧
          SortedPermutation input output⌝ -∗
        runtimeModuleOwn «module» -∗
        array64At source output -∗ array64At scratch scratchOutput -∗
        WP (.running ⟨{ callerLocals with values := stack },
          code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running ⟨{ callerLocals with values :=
      (.i32 scratch :: .i32 (UInt32.ofNat length) ::
        .i32 source :: stack) },
      .call 3 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  induction n generalizing source scratch input scratchValues length callerLocals
      stack code arity remainder controls calls with
  | zero =>
      subst length
      have hbase : input.length ≤ 1 := by omega
      iintro ⟨Hruntime, Hsource, Hscratch, Hcont⟩
      iapply twp_mergesortRaw_base source scratch input scratchValues hbase
      isplitl [Hruntime]
      · iexact Hruntime
      isplitl [Hsource]
      · iexact Hsource
      isplitl [Hscratch]
      · iexact Hscratch
      iintro %output %scratchOutput %hpure Hruntime Hsource Hscratch
      iapply Hcont $$ %output %scratchOutput
        %⟨hpure.1, by omega, hpure.2.2⟩ Hruntime Hsource Hscratch
  | succ n ih =>
      subst length
      by_cases hbase : input.length ≤ 1
      · iintro ⟨Hruntime, Hsource, Hscratch, Hcont⟩
        iapply twp_mergesortRaw_base source scratch input scratchValues hbase
        isplitl [Hruntime]
        · iexact Hruntime
        isplitl [Hsource]
        · iexact Hsource
        isplitl [Hscratch]
        · iexact Hscratch
        iintro %output %scratchOutput %hpure Hruntime Hsource Hscratch
        iapply Hcont $$ %output %scratchOutput
          %⟨hpure.1, by omega, hpure.2.2⟩ Hruntime Hsource Hscratch
      · let mid := input.length / 2
        have hmidPos : 0 < mid := by simp [mid]; omega
        have hmidLt : mid < input.length := by simp [mid]; omega
        have hmidLe : mid ≤ input.length := Nat.le_of_lt hmidLt
        have hlengthSize : input.length < UInt32.size := by
          have hfit := hlayout.source_fits
          simp only [UInt32.size] at hfit ⊢
          omega
        have hmidSize : mid < UInt32.size := by omega
        have hmidValue : UInt32.ofNat input.length >>> (1 % 32) =
            UInt32.ofNat mid := by
          apply UInt32.toNat.inj
          simp [UInt32.toNat_shiftRight, UInt32.toNat_ofNat_of_lt' hlengthSize,
            UInt32.toNat_ofNat_of_lt' hmidSize, Nat.shiftRight_one, mid]
        have hsubValue : UInt32.ofNat input.length - UInt32.ofNat mid =
            UInt32.ofNat (input.length - mid) := by
          apply UInt32.toNat.inj
          rw [UInt32.toNat_sub,
            UInt32.toNat_ofNat_of_lt' hlengthSize,
            UInt32.toNat_ofNat_of_lt' hmidSize]
          have hdiffSize : input.length - mid < UInt32.size := by omega
          rw [UInt32.toNat_ofNat_of_lt' hdiffSize]
          have hnatLt := (UInt32.ofNat input.length).toNat_lt
          rw [UInt32.toNat_ofNat_of_lt' hlengthSize] at hnatLt
          omega
        have hsourceOffset :
            (UInt32.ofNat mid <<< (3 % 32)) + source =
              source + 8 * UInt32.ofNat mid :=
          shiftAddress64_eq source mid
        have hscratchOffset :
            (UInt32.ofNat mid <<< (3 % 32)) + scratch =
              scratch + 8 * UInt32.ofNat mid :=
          shiftAddress64_eq scratch mid
        let leftInput := input.take mid
        let rightInput := input.drop mid
        let leftScratch := scratchValues.take mid
        let rightScratch := scratchValues.drop mid
        have hleftLength : leftInput.length = mid := by
          simp [leftInput, List.length_take, Nat.min_eq_left hmidLe]
        have hrightLength : rightInput.length = input.length - mid := by
          simp [rightInput]
        have hleftScratchLength : leftScratch.length = leftInput.length := by
          simp [leftScratch, leftInput, List.length_take,
            Nat.min_eq_left hmidLe, hscratchLength]
        have hrightScratchLength : rightScratch.length = rightInput.length := by
          simp [rightScratch, rightInput, hscratchLength]
        have hleftMeasure : leftInput.length ≤ n := by omega
        have hrightMeasure : rightInput.length ≤ n := by omega
        have hleftLayout : ValidLayout source scratch leftInput.length := by
          constructor
          · rw [hleftLength]
            exact (Nat.add_le_add_left (Nat.mul_le_mul_left 8 hmidLe)
              source.toNat).trans hlayout.source_fits
          · rw [hleftLength]
            exact (Nat.add_le_add_left (Nat.mul_le_mul_left 8 hmidLe)
              scratch.toNat).trans hlayout.scratch_fits
        have hsourceOffsetNat :
            (source + 8 * UInt32.ofNat mid).toNat =
              source.toNat + 8 * mid :=
          offset64_toNat source input.length mid hlayout.source_fits hmidLt
        have hscratchOffsetNat :
            (scratch + 8 * UInt32.ofNat mid).toNat =
              scratch.toNat + 8 * mid :=
          offset64_toNat scratch input.length mid hlayout.scratch_fits hmidLt
        have hrightLayout : ValidLayout
            (source + 8 * UInt32.ofNat mid)
            (scratch + 8 * UInt32.ofNat mid) rightInput.length := by
          constructor
          · calc
              (source + 8 * UInt32.ofNat mid).toNat +
                    8 * rightInput.length =
                  source.toNat + 8 * mid +
                    8 * (input.length - mid) := by
                      rw [hsourceOffsetNat, hrightLength]
              _ = source.toNat + 8 * input.length := by omega
              _ ≤ UInt32.size := hlayout.source_fits
          · calc
              (scratch + 8 * UInt32.ofNat mid).toNat +
                    8 * rightInput.length =
                  scratch.toNat + 8 * mid +
                    8 * (input.length - mid) := by
                      rw [hscratchOffsetNat, hrightLength]
              _ = scratch.toNat + 8 * input.length := by omega
              _ ≤ UInt32.size := hlayout.scratch_fits
        iintro ⟨Hruntime, Hsource, Hscratch, Hcont⟩
        ihave HruntimeLater : runtimeModuleOwn «module» $$ [Hruntime]
        · iexact Hruntime
        iapply Wasm.SmallStep.twp_call «module» 3 func1Def
          (by decide) (by rfl) $$ HruntimeLater
        iintro Hruntime
        simp [func1Def, Function.toLocals, Function.numParams,
          ValueType.zero, func1]
        iapply Wasm.SmallStep.twp_block
        iapply Wasm.SmallStep.twp_localGet rfl
        iapply Wasm.SmallStep.twp_const
        iapply twp_leU (result := 0) (by
          have hu32 : ¬UInt32.ofNat input.length ≤ 1 := by
            rw [UInt32.le_iff_toNat_le,
              UInt32.toNat_ofNat_of_lt' hlengthSize]
            simp
            omega
          simp [hu32])
        iapply Wasm.SmallStep.twp_const
        iapply twp_and
        rw [UInt32.zero_and]
        iapply Wasm.SmallStep.twp_brIfZero
        iapply Wasm.SmallStep.twp_localGet rfl
        iapply Wasm.SmallStep.twp_const
        iapply twp_shrU
        rw [hmidValue]
        iapply Wasm.SmallStep.twp_localSet rfl
        simp only [List.length_cons, List.length_nil, Nat.reduceAdd,
          Nat.reduceSub, List.set]
        ihave HsourceParts :=
          (array64At_splitAt source input mid hmidLe).mp $$ Hsource
        icases HsourceParts with ⟨HsourceLeft, HsourceRight⟩
        ihave HscratchParts :=
          (array64At_splitAt scratch scratchValues mid
            (by omega)).mp $$ Hscratch
        icases HscratchParts with ⟨HscratchLeft, HscratchRight⟩
        iapply Wasm.SmallStep.twp_localGet rfl
        iapply Wasm.SmallStep.twp_localGet rfl
        iapply Wasm.SmallStep.twp_localGet rfl
        iapply ih source scratch leftInput leftScratch mid hleftLength
          hleftScratchLength hleftLayout hleftMeasure
          (callerLocals :=
            ⟨[.i32 source, .i32 (UInt32.ofNat input.length), .i32 scratch],
              [.i32 (UInt32.ofNat mid)], []⟩)
          (stack := [])
          (code := [.localGet 0, .localGet 3, .const 3, .shl, .add,
            .localGet 1, .localGet 3, .sub, .localGet 2, .localGet 3,
            .const 3, .shl, .add, .call 3, .localGet 0, .localGet 1,
            .localGet 3, .localGet 2, .call 4])
          (arity := 0) (remainder := [])
        isplitl [Hruntime]
        · iexact Hruntime
        isplitl [HsourceLeft]
        · iexact HsourceLeft
        isplitl [HscratchLeft]
        · iexact HscratchLeft
        iintro %leftOutput %leftScratchOutput %hleft
          Hruntime HsourceLeft HscratchLeft
        iapply Wasm.SmallStep.twp_localGet rfl
        iapply Wasm.SmallStep.twp_localGet rfl
        iapply Wasm.SmallStep.twp_const
        iapply Wasm.SmallStep.twp_shl
        iapply Wasm.SmallStep.twp_add
        rw [hsourceOffset]
        iapply Wasm.SmallStep.twp_localGet rfl
        iapply Wasm.SmallStep.twp_localGet rfl
        iapply Wasm.SmallStep.twp_sub
        rw [hsubValue]
        iapply Wasm.SmallStep.twp_localGet rfl
        iapply Wasm.SmallStep.twp_localGet rfl
        iapply Wasm.SmallStep.twp_const
        iapply Wasm.SmallStep.twp_shl
        iapply Wasm.SmallStep.twp_add
        rw [hscratchOffset]
        iapply ih (source + 8 * UInt32.ofNat mid)
          (scratch + 8 * UInt32.ofNat mid) rightInput rightScratch
          (input.length - mid) hrightLength hrightScratchLength
          hrightLayout hrightMeasure
          (callerLocals :=
            ⟨[.i32 source, .i32 (UInt32.ofNat input.length), .i32 scratch],
              [.i32 (UInt32.ofNat mid)], []⟩)
          (stack := [])
          (code := [.localGet 0, .localGet 1, .localGet 3,
            .localGet 2, .call 4]) (arity := 0) (remainder := [])
        isplitl [Hruntime]
        · iexact Hruntime
        isplitl [HsourceRight]
        · iexact HsourceRight
        isplitl [HscratchRight]
        · iexact HscratchRight
        iintro %rightOutput %rightScratchOutput %hright
          Hruntime HsourceRight HscratchRight
        iapply Wasm.SmallStep.twp_localGet rfl
        iapply Wasm.SmallStep.twp_localGet rfl
        iapply Wasm.SmallStep.twp_localGet rfl
        iapply Wasm.SmallStep.twp_localGet rfl
        ihave HsourceFull : array64At source (leftOutput ++ rightOutput) $$
            [HsourceLeft HsourceRight]
        · iapply (array64At_append source leftOutput rightOutput).mpr
          isplitl [HsourceLeft]
          · iexact HsourceLeft
          · rw [hleft.1, hleftLength]
            iexact HsourceRight
        ihave HscratchFull :
            array64At scratch (leftScratchOutput ++ rightScratchOutput) $$
            [HscratchLeft HscratchRight]
        · iapply (array64At_append scratch leftScratchOutput
              rightScratchOutput).mpr
          isplitl [HscratchLeft]
          · iexact HscratchLeft
          · rw [hleft.2.1, hleftLength]
            iexact HscratchRight
        have hcombinedLength : (leftOutput ++ rightOutput).length =
            input.length := by
          simp only [List.length_append, hleft.1, hright.1,
            hleftLength, hrightLength]
          omega
        have hcombinedScratchLength :
            (leftScratchOutput ++ rightScratchOutput).length =
              (leftOutput ++ rightOutput).length := by
          simp only [List.length_append, hleft.1, hleft.2.1,
            hright.1, hright.2.1]
        have hcombinedLayout : ValidLayout source scratch
            (leftOutput ++ rightOutput).length := by
          simpa only [hcombinedLength] using hlayout
        iapply twp_mergeRaw source scratch (leftOutput ++ rightOutput)
          (leftScratchOutput ++ rightScratchOutput) input.length
          hcombinedLength mid
          (by simp [hleft.1, hleftLength]) hcombinedScratchLength
          hcombinedLayout
          (callerLocals :=
            ⟨[.i32 source, .i32 (UInt32.ofNat input.length), .i32 scratch],
              [.i32 (UInt32.ofNat mid)], []⟩)
          (stack := []) (code := []) (arity := 0) (remainder := [])
        isplitl [Hruntime]
        · iexact Hruntime
        isplitl [HsourceFull]
        · iexact HsourceFull
        isplitl [HscratchFull]
        · iexact HscratchFull
        iintro %output %hmerge Hruntime Hsource Hscratch
        have hmerge' : MergeRel leftOutput rightOutput output := by
          simpa [hleft.1, hleftLength] using hmerge.2
        have hsorted : SortedPermutation input output :=
          sortedPermutation_of_split_merge input leftOutput rightOutput
            output mid hleft.2.2 hright.2.2 hmerge'
        iapply Wasm.SmallStep.twp_exitControl rfl
        iapply Wasm.SmallStep.twp_returnFromCallExplicit
        simp only [List.take_zero, List.nil_append]
        have hpure : output.length = input.length ∧
            output.length = input.length ∧ SortedPermutation input output :=
          ⟨by omega, by omega, hsorted⟩
        iapply Hcont $$ %output %output %hpure Hruntime Hsource Hscratch

/-- Public contract for generated `mergesort_raw`. -/
theorem twp_mergesortRaw
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (source scratch : UInt32) (input scratchValues : List UInt64)
    (hscratchLength : scratchValues.length = input.length)
    (hlayout : ValidLayout source scratch input.length)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      array64At source input ∗ array64At scratch scratchValues ∗
      (∀ (output scratchOutput : List UInt64),
        ⌜output.length = input.length ∧
          scratchOutput.length = input.length ∧
          SortedPermutation input output⌝ -∗
        runtimeModuleOwn «module» -∗
        array64At source output -∗ array64At scratch scratchOutput -∗
        WP (.running ⟨{ callerLocals with values := stack },
          code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running ⟨{ callerLocals with values :=
      (.i32 scratch :: .i32 (UInt32.ofNat input.length) ::
        .i32 source :: stack) },
      .call 3 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] :=
  twp_mergesortRaw_aux source scratch input scratchValues input.length rfl
    hscratchLength hlayout input.length (Nat.le_refl _)

end Project.Mergesort.CoreProof
