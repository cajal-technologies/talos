import CodeLib.Examples.Quicksort.Laws

/-!
# Iris verification of the handwritten quicksort

This file connects the pure list invariants to the small-step Wasm WP rules.
-/

namespace Wasm.Examples.Quicksort

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic
open Wasm.SmallStep

def partitionLocals
    (arr : UInt32) (lo hi : Nat) (pivot : UInt32) (i j hiMinusOne : Nat)
    (tmp : UInt32) (stack : List Value := []) : Locals :=
  ⟨[.i32 arr, .i32 (UInt32.ofNat lo), .i32 (UInt32.ofNat hi)],
    [.i32 pivot, .i32 (UInt32.ofNat i), .i32 (UInt32.ofNat j),
     .i32 (UInt32.ofNat hiMinusOne), .i32 tmp],
    stack⟩

set_option maxHeartbeats 4000000 in
theorem wp_partitionScanStep
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (arr : UInt32) (input current : List UInt32)
    (lo hi i j hiMinusOne : Nat) (pivot tmp : UInt32)
    (_hinv : PartitionLoopInvariant input current lo hi i j pivot)
    (_hj : j < hiMinusOne)
    (hjLen : j < current.length)
    (hiLen : i < current.length)
    (hfit : arr.toNat + 4 * current.length ≤ UInt32.size)
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    arrayAt arr current ∗
      ((⌜pivot < current[j]'hjLen⌝ ∗
          arrayAt arr current -∗
          WP (.running ⟨partitionLocals arr lo hi pivot i (j + 1) hiMinusOne tmp [],
            code, arity, remainder, controls, calls⟩ : Expr Unit)
            @ s; E {{ Φ }}) ∧
       (⌜¬ pivot < current[j]'hjLen⌝ ∗
          arrayAt arr (swapElems current i j) -∗
          WP (.running ⟨partitionLocals arr lo hi pivot (i + 1) (j + 1) hiMinusOne
              (current[i]'hiLen) [],
            code, arity, remainder, controls, calls⟩ : Expr Unit)
            @ s; E {{ Φ }})) ⊢
    WP (.running ⟨partitionLocals arr lo hi pivot i j hiMinusOne tmp [],
        partitionScanStep ++ code, arity, remainder, controls, calls⟩ : Expr Unit)
        @ s; E {{ Φ }} := by
  have hjSucc : j + 1 < UInt32.size := by
    have : 4 * current.length ≤ UInt32.size := by omega
    omega
  have hiSucc : i + 1 < UInt32.size := by
    have : 4 * current.length ≤ UInt32.size := by omega
    omega
  iintro ⟨Harray, Hbranches⟩
  simp only [partitionScanStep, List.append_assoc, List.cons_append, List.nil_append]
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply wp_loadAt hjLen hfit rfl rfl
  isplitl [Harray]
  · iexact Harray
  iintro Harray
  iapply Wasm.SmallStep.wp_ltU rfl
  inext
  by_cases hlt : pivot < current[j]'hjLen
  · simp only [if_pos hlt]
    iapply Wasm.SmallStep.wp_iff rfl
    inext
    simp only [if_pos (by decide : (1 : UInt32) ≠ 0)]
    ihave Hthen := BI.and_elim_l $$ Hbranches
    iapply Wasm.SmallStep.wp_exitControl rfl
    inext
    have hjValue : 1 + UInt32.ofNat j = UInt32.ofNat (j + 1) := by
      rw [UInt32.add_comm, u32_ofNat_succ hjSucc]
    have hsetJ :
        (partitionLocals arr lo hi pivot i j hiMinusOne tmp
            [.i32 (1 + UInt32.ofNat j)]).set?
            5 (.i32 (1 + UInt32.ofNat j)) =
          some (partitionLocals arr lo hi pivot i (j + 1) hiMinusOne tmp
            [.i32 (1 + UInt32.ofNat j)]) := by
      rw [hjValue]; rfl
    simp only [partitionLocals, List.take_zero, List.nil_append, List.drop_zero]
    iapply wp_increment rfl hsetJ
    inext
    simp only [partitionLocals]
    iapply Hthen
    isplitr
    · ipureintro; exact hlt
    iframe
  · simp only [if_neg hlt]
    iapply Wasm.SmallStep.wp_iff rfl
    inext
    simp only [if_neg (by decide : ¬(0 : UInt32) ≠ 0)]
    ihave Helse := BI.and_elim_r $$ Hbranches
    have htmp_set :
        (partitionLocals arr lo hi pivot i j hiMinusOne tmp
            [.i32 (current[i]'hiLen)]).set?
            7 (.i32 (current[i]'hiLen)) =
          some (partitionLocals arr lo hi pivot i j hiMinusOne
            (current[i]'hiLen) [.i32 (current[i]'hiLen)]) := rfl
    simp only [partitionLocals, List.drop_zero]
    iapply wp_swapAt hiLen hjLen hfit rfl rfl htmp_set rfl rfl rfl rfl
    isplitl [Harray]
    · iexact Harray
    iintro Harray
    have hiValue : 1 + UInt32.ofNat i = UInt32.ofNat (i + 1) := by
      rw [UInt32.add_comm, u32_ofNat_succ hiSucc]
    have hsetI :
        (partitionLocals arr lo hi pivot i j hiMinusOne (current[i]'hiLen)
            [.i32 (1 + UInt32.ofNat i)]).set?
            4 (.i32 (1 + UInt32.ofNat i)) =
          some (partitionLocals arr lo hi pivot (i + 1) j hiMinusOne (current[i]'hiLen)
            [.i32 (1 + UInt32.ofNat i)]) := by
      rw [hiValue]; rfl
    simp only [partitionLocals]
    iapply wp_increment_nil rfl hsetI
    inext
    iapply Wasm.SmallStep.wp_exitControl rfl
    inext
    simp only [partitionLocals, List.take_zero, List.nil_append]
    have hjValue : 1 + UInt32.ofNat j = UInt32.ofNat (j + 1) := by
      rw [UInt32.add_comm, u32_ofNat_succ hjSucc]
    have hsetJ :
        (partitionLocals arr lo hi pivot (i + 1) j hiMinusOne (current[i]'hiLen)
            [.i32 (1 + UInt32.ofNat j)]).set?
            5 (.i32 (1 + UInt32.ofNat j)) =
          some (partitionLocals arr lo hi pivot (i + 1) (j + 1) hiMinusOne (current[i]'hiLen)
            [.i32 (1 + UInt32.ofNat j)]) := by
      rw [hjValue]; rfl
    iapply wp_increment rfl hsetJ
    inext
    simp only [partitionLocals]
    iapply Helse
    isplitr
    · ipureintro; exact hlt
    iframe

structure PartitionState where
  values : List UInt32
  i : Nat
  j : Nat
  tmp : UInt32

set_option maxHeartbeats 4000000 in
theorem wp_partitionScanLoop
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (arr : UInt32) (input current : List UInt32)
    (lo hi i j hiMinusOne : Nat) (pivot tmp : UInt32)
    (hinv : PartitionLoopInvariant input current lo hi i j pivot)
    (hhim1 : hiMinusOne + 1 = hi)
    (hfit : arr.toNat + 4 * input.length ≤ UInt32.size)
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    arrayAt arr current ∗
      (∀ (current' : List UInt32) (i' j' : Nat) (tmp' : UInt32),
        ⌜PartitionLoopInvariant input current' lo hi i' j' pivot⌝ -∗
        ⌜j' = hiMinusOne⌝ -∗
        arrayAt arr current' -∗
        WP (.running ⟨partitionLocals arr lo hi pivot i' j' hiMinusOne tmp' [],
          code, arity, remainder, controls, calls⟩ : Expr Unit)
          @ s; E {{ Φ }}) ⊢
    WP (.running ⟨partitionLocals arr lo hi pivot i j hiMinusOne tmp [],
        whileDo partitionScanCondition partitionScanStep ++ code,
        arity, remainder, controls, calls⟩ : Expr Unit)
        @ s; E {{ Φ }} := by
  let Finish : IProp WasmHeapGF := iprop%
    ∀ (current' : List UInt32) (i' j' : Nat) (tmp' : UInt32),
      ⌜PartitionLoopInvariant input current' lo hi i' j' pivot⌝ -∗
      ⌜j' = hiMinusOne⌝ -∗
      arrayAt arr current' -∗
      WP (.running ⟨partitionLocals arr lo hi pivot i' j' hiMinusOne tmp' [],
        code, arity, remainder, controls, calls⟩ : Expr Unit)
        @ s; E {{ Φ }}
  let Inv : PartitionState → IProp WasmHeapGF := fun state => iprop%
    ⌜PartitionLoopInvariant input state.values lo hi state.i state.j pivot⌝ ∗
    arrayAt arr state.values ∗ Finish
  iintro ⟨Harray, Hfinish⟩
  simp only [whileDo, List.cons_append, List.nil_append]
  iapply Wasm.SmallStep.wp_block
  inext
  iapply wp_loop_löb_family_from
    (ι := PartitionState)
    (locals := fun state =>
      partitionLocals arr lo hi pivot state.i state.j hiMinusOne state.tmp [])
    (I := Inv)
    (initial := ⟨current, i, j, tmp⟩)
    (initialLocals := partitionLocals arr lo hi pivot i j hiMinusOne tmp [])
    (body := whileLoopCode partitionScanCondition partitionScanStep)
    (code := [])
    (belowStack := [])
    rfl
    rfl
  · intro state
    simp only [Inv, Wasm.SmallStep.loopBodyExpr]
    iintro Hrec Hinv
    icases Hinv with ⟨%hstate, Harray, Hfinish⟩
    have hdata := hstate
    unfold PartitionLoopInvariant at hdata
    obtain ⟨hli, hij, hjhim1, hhilen, hlen, -, -, -, -, -, -⟩ := hdata
    have hjLen : state.j < state.values.length := by omega
    have hiLen : state.i < state.values.length := by omega
    have hlenEq : state.values.length = input.length := hstate.2.2.2.2.1
    have hfitState : arr.toNat + 4 * state.values.length ≤ UInt32.size := by
      rw [hlenEq]; exact hfit
    have hjSize : state.j < UInt32.size := by
      have : 4 * input.length ≤ UInt32.size := by omega
      omega
    have hiMinOneSize : hiMinusOne < UInt32.size := by
      have : 4 * input.length ≤ UInt32.size := by omega
      omega
    have hjCmp :
        (UInt32.ofNat state.j < UInt32.ofNat hiMinusOne) ↔ state.j < hiMinusOne := by
      change (UInt32.ofNat state.j).toNat < (UInt32.ofNat hiMinusOne).toNat ↔ _
      rw [UInt32.toNat_ofNat_of_lt' hjSize, UInt32.toNat_ofNat_of_lt' hiMinOneSize]
    simp only [whileLoopCode, partitionScanCondition, List.append_assoc]
    iapply wp_lessLocal rfl rfl
    inext
    simp only [List.cons_append, List.nil_append]
    iapply Wasm.SmallStep.wp_eqz rfl
    inext
    by_cases hj : state.j < hiMinusOne
    · have hlt := hjCmp.mpr hj
      simp only [if_pos hlt]
      simp only [if_neg (by decide : (1 : UInt32) ≠ 0)]
      iapply Wasm.SmallStep.wp_brIfZero
      inext
      iapply wp_partitionScanStep arr input state.values lo hi state.i state.j hiMinusOne
        pivot state.tmp hstate hj hjLen hiLen hfitState
      isplitl [Harray]
      · iexact Harray
      isplit
      · iintro ⟨%hlt, Harray⟩
        iapply Wasm.SmallStep.wp_br rfl
        inext
        simp only [partitionLocals, List.take_zero, List.nil_append]
        ispecialize Hrec $$
          %(⟨state.values, state.i, state.j + 1, state.tmp⟩ : PartitionState)
        iapply Hrec
        isplitr
        · ipureintro
          exact hstate.skipStep (by omega) (by rwa [getElem!_pos state.values state.j hjLen])
        iframe
        simp only [Finish, partitionLocals]
        iexact Hfinish
      · iintro ⟨%hlt, Harray⟩
        iapply Wasm.SmallStep.wp_br rfl
        inext
        simp only [partitionLocals, List.take_zero, List.nil_append]
        ispecialize Hrec $$
          %(⟨swapElems state.values state.i state.j, state.i + 1, state.j + 1,
              state.values[state.i]'hiLen⟩ : PartitionState)
        iapply Hrec
        isplitr
        · ipureintro
          exact hstate.swapStep (by omega) (by rwa [getElem!_pos state.values state.j hjLen])
        iframe
        simp only [Finish, partitionLocals]
        iexact Hfinish
    · have hlt := mt hjCmp.mp hj
      simp only [if_neg hlt]
      have hjEq : state.j = hiMinusOne := by omega
      iapply Wasm.SmallStep.wp_brIf (by decide) rfl
      inext
      simp only [partitionLocals, List.take_zero, List.nil_append, List.drop_zero]
      iapply Hfinish $$ %state.values %state.i %state.j %state.tmp %hstate %hjEq Harray
  · simp only [Inv]
    isplitr
    · ipureintro
      exact hinv
    iframe

set_option maxHeartbeats 4000000 in
theorem wp_partitionBody
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (arr : UInt32) (input : List UInt32) (lo hi : Nat)
    (hbounds : lo < hi ∧ hi ≤ input.length)
    (hfit : arr.toNat + 4 * input.length ≤ UInt32.size)
    {calls : List CallFrame} :
    arrayAt arr input ∗
      (∀ (output : List UInt32) (pivotIdx : Nat) (tmp : UInt32),
        ⌜PartitionRange input output lo hi pivotIdx⌝ -∗
        arrayAt arr output -∗
        WP (.running ⟨partitionLocals arr lo hi (input[hi - 1]!) pivotIdx (hi - 1) (hi - 1) tmp
              [.i32 (UInt32.ofNat pivotIdx)],
            [.ret], 1, [], [], calls⟩ : Expr Unit)
            @ s; E {{ Φ }}) ⊢
    WP (.running ⟨⟨[.i32 arr, .i32 (UInt32.ofNat lo), .i32 (UInt32.ofNat hi)],
        [.i32 0, .i32 0, .i32 0, .i32 0, .i32 0], []⟩,
      partitionBody, 1, [], [], calls⟩ : Expr Unit)
      @ s; E {{ Φ }} := by
  iintro ⟨Harray, Hfinish⟩
  simp only [partitionBody, partitionInit, partitionPlacePivot,
    List.cons_append, List.nil_append, List.append_assoc]
  have hiPos : 0 < hi := by omega
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_const
  inext
  iapply Wasm.SmallStep.wp_sub
  inext
  have hiMinus1 : UInt32.ofNat hi - 1 = UInt32.ofNat (hi - 1) := by
    have hiSize : hi < UInt32.size := by
      have := hbounds.2; simp only [UInt32.size] at hfit ⊢; omega
    apply UInt32.toNat.inj
    rw [UInt32.toNat_sub, show (1 : UInt32).toNat = 1 from rfl,
        UInt32.toNat_ofNat_of_lt' hiSize,
        UInt32.toNat_ofNat_of_lt' (show hi - 1 < UInt32.size by omega)]
    have := (UInt32.ofNat hi).toNat_lt
    rw [UInt32.toNat_ofNat_of_lt' hiSize] at this
    omega
  have hset6 :
      (⟨[.i32 arr, .i32 (UInt32.ofNat lo), .i32 (UInt32.ofNat hi)],
        [.i32 0, .i32 0, .i32 0, .i32 0, .i32 0],
        [.i32 (UInt32.ofNat hi - 1)]⟩ : Locals).set?
        6 (.i32 (UInt32.ofNat hi - 1)) =
      some (partitionLocals arr lo hi 0 0 0 (hi - 1) 0 [.i32 (UInt32.ofNat hi - 1)]) := by
    rw [hiMinus1]; rfl
  iapply Wasm.SmallStep.wp_localSet hset6
  inext
  have hjm1 : hi - 1 < input.length := by omega
  simp only [partitionLocals]
  iapply wp_loadAt hjm1 hfit rfl rfl
  isplitl [Harray]
  · iexact Harray
  iintro Harray
  simp only [← getElem!_pos input (hi - 1) hjm1]
  have hset3 :
      (partitionLocals arr lo hi 0 0 0 (hi - 1) 0 [.i32 (input[hi - 1]!)]).set?
        3 (.i32 (input[hi - 1]!)) =
      some (partitionLocals arr lo hi (input[hi - 1]!) 0 0 (hi - 1) 0
          [.i32 (input[hi - 1]!)]) := rfl
  iapply Wasm.SmallStep.wp_localSet hset3
  inext
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  have hset4 :
      (partitionLocals arr lo hi (input[hi - 1]!) 0 0 (hi - 1) 0
          [.i32 (UInt32.ofNat lo)]).set?
        4 (.i32 (UInt32.ofNat lo)) =
      some (partitionLocals arr lo hi (input[hi - 1]!) lo 0 (hi - 1) 0
          [.i32 (UInt32.ofNat lo)]) := rfl
  simp only [partitionLocals]
  iapply Wasm.SmallStep.wp_localSet hset4
  inext
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  have hset5 :
      (partitionLocals arr lo hi (input[hi - 1]!) lo 0 (hi - 1) 0
          [.i32 (UInt32.ofNat lo)]).set?
        5 (.i32 (UInt32.ofNat lo)) =
      some (partitionLocals arr lo hi (input[hi - 1]!) lo lo (hi - 1) 0
          [.i32 (UInt32.ofNat lo)]) := rfl
  simp only [partitionLocals]
  iapply Wasm.SmallStep.wp_localSet hset5
  inext
  simp only [partitionLocals]
  have hfold :
      ({ params := [Value.i32 arr, Value.i32 (UInt32.ofNat lo), Value.i32 (UInt32.ofNat hi)],
         locals := [Value.i32 (input[hi - 1]!), Value.i32 (UInt32.ofNat lo),
                    Value.i32 (UInt32.ofNat lo), Value.i32 (UInt32.ofNat (hi - 1)),
                    Value.i32 0],
         values := [] } : Locals) =
      partitionLocals arr lo hi (input[hi - 1]!) lo lo (hi - 1) 0 [] := rfl
  rw [hfold]
  iapply wp_partitionScanLoop arr input input lo hi lo lo (hi - 1) (input[hi - 1]!) 0
    (partitionLoopInvariant_start input lo hi (input[hi - 1]!) hbounds rfl)
    (by omega) hfit
  isplitl [Harray]
  · iexact Harray
  iintro %current' %i' %j' %tmp' %hinv' %hjEq Harray
  subst hjEq
  have hinv'_orig := hinv'
  rcases hinv' with ⟨hli, hij, -, hhilen, hlen, -, -, -, -, -, -⟩
  have hiLen' : i' < current'.length := by omega
  have hjm1Len' : hi - 1 < current'.length := by omega
  have hfitCurrent : arr.toNat + 4 * current'.length ≤ UInt32.size := by
    rw [hlen]; exact hfit
  have htmp_set :
      (partitionLocals arr lo hi (input[hi - 1]!) i' (hi - 1) (hi - 1) tmp'
          [.i32 (current'[i']'hiLen')]).set?
        7 (.i32 (current'[i']'hiLen')) =
      some (partitionLocals arr lo hi (input[hi - 1]!) i' (hi - 1) (hi - 1)
          (current'[i']'hiLen') [.i32 (current'[i']'hiLen')]) := rfl
  simp only [partitionLocals]
  iapply wp_swapAt hiLen' hjm1Len' hfitCurrent rfl rfl htmp_set rfl rfl rfl rfl
  isplitl [Harray]
  · iexact Harray
  iintro Harray
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  have hplacePivot : PartitionRange input (swapElems current' i' (hi - 1)) lo hi i' :=
    PartitionLoopInvariant.placePivot hinv'_orig (by omega)
  simp only [partitionLocals]
  iapply Hfinish $$ %(swapElems current' i' (hi - 1)) %i' %(current'[i']'hiLen')
    %hplacePivot Harray

theorem wp_partitionBody_from
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (actualLocals : Locals)
    (arr : UInt32) (input : List UInt32) (lo hi : Nat)
    (hbounds : lo < hi ∧ hi ≤ input.length)
    (hfit : arr.toNat + 4 * input.length ≤ UInt32.size)
    (hlocals : actualLocals = ⟨[.i32 arr, .i32 (UInt32.ofNat lo), .i32 (UInt32.ofNat hi)],
        [.i32 0, .i32 0, .i32 0, .i32 0, .i32 0], []⟩)
    {calls : List CallFrame} :
    arrayAt arr input ∗
      (∀ (output : List UInt32) (pivotIdx : Nat) (tmp : UInt32),
        ⌜PartitionRange input output lo hi pivotIdx⌝ -∗
        arrayAt arr output -∗
        WP (.running ⟨partitionLocals arr lo hi (input[hi - 1]!) pivotIdx (hi - 1) (hi - 1) tmp
              [.i32 (UInt32.ofNat pivotIdx)],
            [.ret], 1, [], [], calls⟩ : Expr Unit)
            @ s; E {{ Φ }}) ⊢
    WP (.running ⟨actualLocals, partitionBody, 1, [], [], calls⟩ : Expr Unit)
        @ s; E {{ Φ }} := by
  subst hlocals
  exact wp_partitionBody arr input lo hi hbounds hfit

set_option maxHeartbeats 4000000 in
theorem wp_partition
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (runtimeModule : Module) (partitionIdx : Nat)
    (himports : ¬partitionIdx < runtimeModule.imports.length)
    (hfunction : runtimeModule.funcs[partitionIdx - runtimeModule.imports.length]? =
        some partitionFunction)
    (arr : UInt32) (input : List UInt32) (lo hi : Nat)
    (hbounds : lo < hi ∧ hi ≤ input.length)
    (hfit : arr.toNat + 4 * input.length ≤ UInt32.size)
    {callerLocals : Locals}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {stack : List Value} :
    runtimeModuleOwn runtimeModule ∗
      arrayAt arr input ∗
      (∀ (output : List UInt32) (pivotIdx : Nat),
        runtimeModuleOwn runtimeModule -∗
        ⌜PartitionRange input output lo hi pivotIdx⌝ -∗
        arrayAt arr output -∗
        WP (.running ⟨{ callerLocals with values := .i32 (UInt32.ofNat pivotIdx) :: stack },
          code, arity, remainder, controls, calls⟩ : Expr Unit)
          @ s; E {{ Φ }}) ⊢
    WP (.running ⟨{ callerLocals with
          values := .i32 (UInt32.ofNat hi) :: .i32 (UInt32.ofNat lo) :: .i32 arr :: stack },
        .call partitionIdx :: code, arity, remainder, controls, calls⟩ : Expr Unit)
        @ s; E {{ Φ }} := by
  iintro ⟨Hruntime, Harray, Hcont⟩
  ihave HruntimeLater : ▷ runtimeModuleOwn runtimeModule $$ [Hruntime]
  · inext
    iexact Hruntime
  iapply Wasm.SmallStep.wp_call runtimeModule partitionIdx partitionFunction
    himports hfunction $$ HruntimeLater
  inext
  iintro Hruntime
  simp [partitionFunction, Function.toLocals, Function.numParams, ValueType.zero]
  iapply wp_partitionBody_from
    (⟨[.i32 arr, .i32 (UInt32.ofNat lo), .i32 (UInt32.ofNat hi)],
      [.i32 0, .i32 0, .i32 0, .i32 0, .i32 0], []⟩ : Locals)
    arr input lo hi hbounds hfit rfl
  isplitl [Harray]
  · iexact Harray
  iintro %output %pivotIdx %tmp %hrange Harray
  iapply Wasm.SmallStep.wp_returnFromCallExplicit
  inext
  simp only [partitionLocals, List.take_succ_cons, List.take_zero, List.nil_append,
    List.cons_append]
  iapply Hcont $$ %output %pivotIdx Hruntime %hrange Harray

def quicksortLocals (arr : UInt32) (lo hi : Nat) (pivotIdx : Nat)
    (stack : List Value := []) : Locals :=
  ⟨[.i32 arr, .i32 (UInt32.ofNat lo), .i32 (UInt32.ofNat hi)],
    [.i32 (UInt32.ofNat pivotIdx)],
    stack⟩

set_option maxHeartbeats 8000000 in
private theorem wp_quicksortBody_aux
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (runtimeModule : Module) (partitionIdx quicksortIdx : Nat)
    (himports_p : ¬partitionIdx < runtimeModule.imports.length)
    (hfunction_p : runtimeModule.funcs[partitionIdx - runtimeModule.imports.length]? =
        some partitionFunction)
    (himports_q : ¬quicksortIdx < runtimeModule.imports.length)
    (hfunction_q : runtimeModule.funcs[quicksortIdx - runtimeModule.imports.length]? =
        some (quicksortFunction partitionIdx quicksortIdx))
    (arr : UInt32) (input : List UInt32) (lo hi : Nat)
    (hlohi : lo ≤ hi)
    (hhilen : hi ≤ input.length)
    (hfit : arr.toNat + 4 * input.length ≤ UInt32.size)
    (n : Nat) (hn : hi - lo ≤ n)
    {callerLocals : Locals}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {stack : List Value} :
    runtimeModuleOwn runtimeModule ∗
      arrayAt arr input ∗
      (∀ (output : List UInt32),
        runtimeModuleOwn runtimeModule -∗
        ⌜output.length = input.length ∧ output.take lo = input.take lo ∧
          output.drop hi = input.drop hi ∧ Sorted (segment output lo hi) ∧
          List.Perm (segment input lo hi) (segment output lo hi)⌝ -∗
        arrayAt arr output -∗
        WP (.running ⟨{ callerLocals with values := stack },
              code, arity, remainder, controls, calls⟩ : Expr Unit)
            @ s; E {{ Φ }}) ⊢
    WP (.running ⟨{ callerLocals with
          values := .i32 (UInt32.ofNat hi) :: .i32 (UInt32.ofNat lo) :: .i32 arr :: stack },
        .call quicksortIdx :: code, arity, remainder, controls, calls⟩ : Expr Unit)
        @ s; E {{ Φ }} := by
  induction n generalizing input lo hi callerLocals code arity remainder controls calls stack with
  | zero =>
    have heq : hi = lo := by omega
    subst heq
    iintro ⟨Hruntime, Harray, Hcont⟩
    ihave HruntimeLater : ▷ runtimeModuleOwn runtimeModule $$ [Hruntime]
    · inext; iexact Hruntime
    iapply Wasm.SmallStep.wp_call runtimeModule quicksortIdx
        (quicksortFunction partitionIdx quicksortIdx)
        himports_q hfunction_q $$ HruntimeLater
    inext; iintro Hruntime
    simp [quicksortFunction, Function.toLocals, Function.numParams, ValueType.zero]
    simp only [quicksortBody, quicksortBaseCheck, List.append_assoc, List.cons_append,
      List.nil_append]
    iapply Wasm.SmallStep.wp_localGet rfl; inext
    iapply Wasm.SmallStep.wp_localGet rfl; inext
    iapply Wasm.SmallStep.wp_sub; inext
    have hloSub : UInt32.ofNat hi - UInt32.ofNat hi = 0 := by simp
    simp only [hloSub]
    iapply Wasm.SmallStep.wp_const; inext
    iapply Wasm.SmallStep.wp_ltU rfl; inext
    simp only [if_pos (by decide : (0 : UInt32) < 2)]
    iapply Wasm.SmallStep.wp_iff rfl; inext
    simp only [if_pos (by decide : (1 : UInt32) ≠ 0)]
    iapply Wasm.SmallStep.wp_returnFromCallExplicit; inext
    simp only [List.take_zero, List.nil_append]
    have hpure0 : input.length = input.length ∧ input.take hi = input.take hi ∧
        input.drop hi = input.drop hi ∧ Sorted (segment input hi hi) ∧
        List.Perm (segment input hi hi) (segment input hi hi) :=
      ⟨rfl, rfl, rfl, quicksort_base input hi hi hhilen (by omega), List.Perm.refl _⟩
    iapply Hcont $$ %input Hruntime %hpure0 Harray
  | succ n ih =>
    iintro ⟨Hruntime, Harray, Hcont⟩
    have hiSize : hi < UInt32.size := by
      have : UInt32.size = 4294967296 := rfl; omega
    have hdiffSize : hi - lo < UInt32.size := Nat.lt_of_le_of_lt (Nat.sub_le hi lo) hiSize
    have hsubEq : UInt32.ofNat hi - UInt32.ofNat lo = UInt32.ofNat (hi - lo) := by
      have hloSize : lo < UInt32.size := Nat.lt_of_le_of_lt hlohi hiSize
      apply UInt32.toNat.inj
      rw [UInt32.toNat_sub, UInt32.toNat_ofNat_of_lt' hiSize,
          UInt32.toNat_ofNat_of_lt' hloSize, UInt32.toNat_ofNat_of_lt' hdiffSize]
      have := (UInt32.ofNat hi).toNat_lt
      rw [UInt32.toNat_ofNat_of_lt' hiSize] at this
      omega
    ihave HruntimeLater : ▷ runtimeModuleOwn runtimeModule $$ [Hruntime]
    · inext; iexact Hruntime
    iapply Wasm.SmallStep.wp_call runtimeModule quicksortIdx
        (quicksortFunction partitionIdx quicksortIdx)
        himports_q hfunction_q $$ HruntimeLater
    inext; iintro Hruntime
    simp [quicksortFunction, Function.toLocals, Function.numParams, ValueType.zero]
    simp only [quicksortBody, quicksortBaseCheck, quicksortPartitionCall, quicksortLeftCall,
      quicksortRightCall, List.cons_append, List.nil_append]
    iapply Wasm.SmallStep.wp_localGet rfl; inext
    iapply Wasm.SmallStep.wp_localGet rfl; inext
    iapply Wasm.SmallStep.wp_sub; inext
    simp only [hsubEq]
    iapply Wasm.SmallStep.wp_const; inext
    iapply Wasm.SmallStep.wp_ltU rfl; inext
    by_cases hbase : hi - lo < 2
    · have h_lt_u32 : UInt32.ofNat (hi - lo) < 2 := by
        have h2 : (2 : UInt32).toNat = 2 := rfl
        rw [UInt32.lt_iff_toNat_lt, UInt32.toNat_ofNat_of_lt' hdiffSize, h2]; exact hbase
      simp only [if_pos h_lt_u32]
      iapply Wasm.SmallStep.wp_iff rfl; inext
      simp only [if_pos (by decide : (1 : UInt32) ≠ 0)]
      iapply Wasm.SmallStep.wp_returnFromCallExplicit; inext
      simp only [List.take_zero, List.nil_append]
      have hpure_base : input.length = input.length ∧ input.take lo = input.take lo ∧
          input.drop hi = input.drop hi ∧ Sorted (segment input lo hi) ∧
          List.Perm (segment input lo hi) (segment input lo hi) :=
        ⟨rfl, rfl, rfl, quicksort_base input lo hi hhilen hbase, List.Perm.refl _⟩
      iapply Hcont $$ %input Hruntime %hpure_base Harray
    · have h_not_lt : ¬UInt32.ofNat (hi - lo) < 2 := by
        have h2 : (2 : UInt32).toNat = 2 := rfl
        rw [UInt32.lt_iff_toNat_lt, UInt32.toNat_ofNat_of_lt' hdiffSize, h2]; omega
      have hlohi_strict : lo < hi := by omega
      simp only [if_neg h_not_lt]
      iapply Wasm.SmallStep.wp_iff rfl; inext
      simp only [if_neg (by decide : ¬(0 : UInt32) ≠ 0)]
      iapply Wasm.SmallStep.wp_exitControl rfl; inext
      simp only [List.take_zero, List.nil_append, List.drop_zero]
      iapply Wasm.SmallStep.wp_localGet rfl; inext
      iapply Wasm.SmallStep.wp_localGet rfl; inext
      iapply Wasm.SmallStep.wp_localGet rfl; inext
      ihave HruntimeLater_p : ▷ runtimeModuleOwn runtimeModule $$ [Hruntime]
      · inext; iexact Hruntime
      iapply Wasm.SmallStep.wp_call runtimeModule partitionIdx partitionFunction himports_p
          hfunction_p $$ HruntimeLater_p
      inext; iintro Hruntime_p
      simp [partitionFunction, Function.toLocals, Function.numParams, ValueType.zero]
      iapply wp_partitionBody_from
          (⟨[.i32 arr, .i32 (UInt32.ofNat lo), .i32 (UInt32.ofNat hi)],
            [.i32 0, .i32 0, .i32 0, .i32 0, .i32 0], []⟩ : Locals)
          arr input lo hi ⟨hlohi_strict, hhilen⟩ hfit rfl
      isplitl [Harray]
      · iexact Harray
      iintro %output_p %pivotIdx %tmp %hpart Harray_p
      obtain ⟨hlo, hphi, hhilen_p, hlen_p, htake_p, hdrop_p, hperm_p, hleft_p, hright_p⟩ := hpart
      iapply Wasm.SmallStep.wp_returnFromCallExplicit; inext
      simp only [partitionLocals, List.take_succ_cons, List.take_zero, List.nil_append,
        List.cons_append]
      have hset_piv :
          (⟨[.i32 arr, .i32 (UInt32.ofNat lo), .i32 (UInt32.ofNat hi)], [.i32 0],
            [.i32 (UInt32.ofNat pivotIdx)]⟩ : Locals).set?
            3 (.i32 (UInt32.ofNat pivotIdx)) =
          some ⟨[.i32 arr, .i32 (UInt32.ofNat lo), .i32 (UInt32.ofNat hi)],
                [.i32 (UInt32.ofNat pivotIdx)], [.i32 (UInt32.ofNat pivotIdx)]⟩ := rfl
      iapply Wasm.SmallStep.wp_localSet hset_piv; inext
      iapply Wasm.SmallStep.wp_localGet rfl; inext
      iapply Wasm.SmallStep.wp_localGet rfl; inext
      iapply Wasm.SmallStep.wp_localGet rfl; inext
      have hhilen_left : pivotIdx ≤ output_p.length := by omega
      have hfit_left : arr.toNat + 4 * output_p.length ≤ UInt32.size := by rw [hlen_p]; exact hfit
      have hn_left : pivotIdx - lo ≤ n := by omega
      iapply ih output_p lo pivotIdx hlo hhilen_left hfit_left hn_left
      isplitl [Hruntime_p]
      · iexact Hruntime_p
      isplitl [Harray_p]
      · iexact Harray_p
      iintro %out_l Hruntime_l %hpure_l Harray_l
      obtain ⟨hlen_l, htake_l, hdrop_l, hsorted_l, hperm_l⟩ := hpure_l
      iapply Wasm.SmallStep.wp_localGet rfl; inext
      iapply Wasm.SmallStep.wp_localGet rfl; inext
      iapply Wasm.SmallStep.wp_const; inext
      iapply Wasm.SmallStep.wp_add; inext
      have hpivSuccSize : pivotIdx + 1 < UInt32.size := by
        have : UInt32.size = 4294967296 := rfl; omega
      have hpivValue : 1 + UInt32.ofNat pivotIdx = UInt32.ofNat (pivotIdx + 1) := by
        rw [UInt32.add_comm, u32_ofNat_succ hpivSuccSize]
      simp only [hpivValue]
      iapply Wasm.SmallStep.wp_localGet rfl; inext
      have hlohi_right : pivotIdx + 1 ≤ hi := by omega
      have hhilen_right : hi ≤ out_l.length := by omega
      have hfit_right : arr.toNat + 4 * out_l.length ≤ UInt32.size := by
        rw [hlen_l, hlen_p]; exact hfit
      have hn_right : hi - (pivotIdx + 1) ≤ n := by omega
      iapply (ih (callerLocals := ⟨[.i32 arr, .i32 (UInt32.ofNat lo), .i32 (UInt32.ofNat hi)],
          [.i32 (UInt32.ofNat pivotIdx)], []⟩)
        out_l (pivotIdx + 1) hi hlohi_right hhilen_right hfit_right hn_right)
      isplitl [Hruntime_l]
      · iexact Hruntime_l
      isplitl [Harray_l]
      · iexact Harray_l
      iintro %out_r Hruntime_r %hpure_r Harray_r
      obtain ⟨hlen_r, htake_r, hdrop_r, hsorted_r, hperm_r⟩ := hpure_r
      iapply Wasm.SmallStep.wp_returnFromCallExplicit; inext
      simp only [List.take_zero, List.nil_append]
      have hpart_final : PartitionRange input out_r lo hi pivotIdx :=
        partitionRange_after_sorts
          ⟨hlo, hphi, hhilen_p, hlen_p, htake_p, hdrop_p, hperm_p, hleft_p, hright_p⟩
          hlen_l htake_l hdrop_l hperm_l hlen_r htake_r hdrop_r hperm_r
      have hleft_r : Sorted (segment out_r lo pivotIdx) :=
        segment_sorted_of_take_eq (by omega) (by omega) htake_r hsorted_l
      have hcomp := quicksort_compose input out_r lo hi pivotIdx hpart_final hleft_r hsorted_r
      have htake_r_lo : out_r.take lo = out_l.take lo := by
        have := congr_arg (·.take lo) htake_r
        simp only [List.take_take, Nat.min_eq_left (by omega : lo ≤ pivotIdx + 1)] at this
        exact this
      have hdrop_l_hi : out_l.drop hi = output_p.drop hi := by
        rw [show out_l.drop hi = (out_l.drop pivotIdx).drop (hi - pivotIdx) from by
              rw [List.drop_drop]; congr 1; omega,
            show output_p.drop hi = (output_p.drop pivotIdx).drop (hi - pivotIdx) from by
              rw [List.drop_drop]; congr 1; omega,
            hdrop_l]
      have hpure_final : out_r.length = input.length ∧ out_r.take lo = input.take lo ∧
          out_r.drop hi = input.drop hi ∧ Sorted (segment out_r lo hi) ∧
          List.Perm (segment input lo hi) (segment out_r lo hi) :=
        ⟨by omega, by rw [htake_r_lo, htake_l, htake_p],
          by rw [hdrop_r, hdrop_l_hi, hdrop_p], hcomp.1, hcomp.2⟩
      iapply Hcont $$ %out_r Hruntime_r %hpure_final Harray_r

theorem wp_quicksortBody
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (runtimeModule : Module) (partitionIdx quicksortIdx : Nat)
    (himports_p : ¬partitionIdx < runtimeModule.imports.length)
    (hfunction_p : runtimeModule.funcs[partitionIdx - runtimeModule.imports.length]? =
        some partitionFunction)
    (himports_q : ¬quicksortIdx < runtimeModule.imports.length)
    (hfunction_q : runtimeModule.funcs[quicksortIdx - runtimeModule.imports.length]? =
        some (quicksortFunction partitionIdx quicksortIdx))
    (arr : UInt32) (input : List UInt32) (lo hi : Nat)
    (hlohi : lo ≤ hi)
    (hhilen : hi ≤ input.length)
    (hfit : arr.toNat + 4 * input.length ≤ UInt32.size)
    {callerLocals : Locals}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {stack : List Value} :
    runtimeModuleOwn runtimeModule ∗
      arrayAt arr input ∗
      (∀ (output : List UInt32),
        runtimeModuleOwn runtimeModule -∗
        ⌜output.length = input.length ∧ output.take lo = input.take lo ∧
          output.drop hi = input.drop hi ∧ Sorted (segment output lo hi) ∧
          List.Perm (segment input lo hi) (segment output lo hi)⌝ -∗
        arrayAt arr output -∗
        WP (.running ⟨{ callerLocals with values := stack },
              code, arity, remainder, controls, calls⟩ : Expr Unit)
            @ s; E {{ Φ }}) ⊢
    WP (.running ⟨{ callerLocals with
          values := .i32 (UInt32.ofNat hi) :: .i32 (UInt32.ofNat lo) :: .i32 arr :: stack },
        .call quicksortIdx :: code, arity, remainder, controls, calls⟩ : Expr Unit)
        @ s; E {{ Φ }} :=
  wp_quicksortBody_aux runtimeModule partitionIdx quicksortIdx himports_p hfunction_p
    himports_q hfunction_q arr input lo hi hlohi hhilen hfit input.length
    (Nat.le_trans (Nat.sub_le hi lo) hhilen)

set_option maxHeartbeats 5000000 in
theorem wp_quicksort
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (runtimeModule : Module) (partitionIdx quicksortIdx : Nat)
    (himports_p : ¬partitionIdx < runtimeModule.imports.length)
    (hfunction_p : runtimeModule.funcs[partitionIdx - runtimeModule.imports.length]? =
        some partitionFunction)
    (himports_q : ¬quicksortIdx < runtimeModule.imports.length)
    (hfunction_q : runtimeModule.funcs[quicksortIdx - runtimeModule.imports.length]? =
        some (quicksortFunction partitionIdx quicksortIdx))
    (arr : UInt32) (input : List UInt32) (lo hi : Nat)
    (hlohi : lo ≤ hi)
    (hhilen : hi ≤ input.length)
    (hfit : arr.toNat + 4 * input.length ≤ UInt32.size)
    {callerLocals : Locals}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {stack : List Value} :
    runtimeModuleOwn runtimeModule ∗
      arrayAt arr input ∗
      (∀ (output : List UInt32),
        runtimeModuleOwn runtimeModule -∗
        ⌜output.length = input.length ∧ output.take lo = input.take lo ∧
          output.drop hi = input.drop hi ∧ Sorted (segment output lo hi) ∧
          List.Perm (segment input lo hi) (segment output lo hi)⌝ -∗
        arrayAt arr output -∗
        WP (.running ⟨{ callerLocals with values := stack },
              code, arity, remainder, controls, calls⟩ : Expr Unit)
            @ s; E {{ Φ }}) ⊢
    WP (.running ⟨{ callerLocals with
          values := .i32 (UInt32.ofNat hi) :: .i32 (UInt32.ofNat lo) :: .i32 arr :: stack },
        .call quicksortIdx :: code, arity, remainder, controls, calls⟩ : Expr Unit)
        @ s; E {{ Φ }} :=
  wp_quicksortBody runtimeModule partitionIdx quicksortIdx himports_p hfunction_p
    himports_q hfunction_q arr input lo hi hlohi hhilen hfit

theorem quicksort_partiallyMeets (arr : UInt32) (input : List UInt32)
    (hfit : arr.toNat + 4 * input.length ≤ UInt32.size)
    (hmem : arr.toNat + 4 * input.length ≤ 65536) :
    PartiallyMeets (quicksortConfig arr input)
      (fun values store =>
        values = [] ∧ ∃ output : List UInt32,
          output.length = input.length ∧ Sorted output ∧
          List.Perm input output ∧
          readWordArray store.wasm.mem arr input.length = output) := by
  apply wasm_smallStep_heap_globals_runtime_store_partiallyMeets.{0}
    (α := Unit) (σ := quicksortHeap arr input) (globalσ := ∅)
  · exact quicksortHeap_agrees arr input hfit
  · exact quicksortHeap_inBounds arr input hfit hmem
  · intro index value hget; simp [get?_empty] at hget
  · intro gs
    simp only [BI.BigSepM.bigSepM_empty.to_eq]
    iintro ⟨Hbytes, _Hemp, Hruntime⟩
    have hfitStrict : arr.toNat + 4 * input.length < UInt32.size := by
      simp only [UInt32.size]; omega
    ihave Harray := quicksortHeap_pointsTo arr input hfitStrict $$ Hbytes
    simp only [quicksortConfig]
    iapply wp_quicksort quicksortModule 0 1
      (himports_p := by decide) (hfunction_p := rfl)
      (himports_q := by decide) (hfunction_q := rfl)
      (arr := arr) (input := input) (lo := 0) (hi := input.length)
      (hlohi := Nat.zero_le _) (hhilen := Nat.le_refl _) (hfit := hfit)
      (callerLocals := ⟨[], [], []⟩) (stack := []) (code := [])
      (arity := 0) (remainder := []) (controls := []) (calls := [])
    isplitl [Hruntime]
    · iexact Hruntime
    isplitl [Harray]
    · iexact Harray
    iintro %output Hruntime_out %hpure Harray_out
    iapply wp_finish
    inext
    iapply wp_value'
    iintro %store %_obs Hstate
    imod arrayAt_readWordArray store 0 [] 0 arr output
      (by rw [hpure.1]; exact hfit) $$
        [$Hstate $Harray_out] with ⟨_Hstate, _Harray_out, %hread⟩
    ipureintro
    have hseq_out : segment output 0 input.length = output := by
      simp only [segment, List.drop_zero, Nat.sub_zero]
      rw [← hpure.1]; exact List.take_length (l := output)
    have hseq_in : segment input 0 input.length = input := by
      simp only [segment, List.drop_zero, Nat.sub_zero]
      exact List.take_length (l := input)
    exact ⟨rfl, output, hpure.1,
      hseq_out ▸ hpure.2.2.2.1,
      hseq_in ▸ hseq_out ▸ hpure.2.2.2.2,
      by rw [← hpure.1]; exact hread⟩

end Wasm.Examples.Quicksort
