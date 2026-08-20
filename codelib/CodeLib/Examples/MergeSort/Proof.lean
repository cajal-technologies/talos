import CodeLib.Examples.MergeSort.Laws

/-!
# Iris verification of the handwritten merge sort

This file connects the pure list invariants to the small-step Wasm WP rules.
-/

namespace Wasm.Examples.MergeSort

open Wasm
open Iris Iris.ProgramLogic Language.Notation
open Wasm.SepLogic
open Wasm.SmallStep

def mergeLocals
    (source temporary : UInt32) (left mid right i j k : Nat)
    (stack : List Value := []) : Locals :=
  ⟨[.i32 source, .i32 temporary, .i32 (UInt32.ofNat left),
      .i32 (UInt32.ofNat mid), .i32 (UInt32.ofNat right)],
    [.i32 (UInt32.ofNat i), .i32 (UInt32.ofNat j),
      .i32 (UInt32.ofNat k)],
    stack⟩

def sortLocals
    (source temporary : UInt32) (count width left mid right : Nat)
    (stack : List Value := []) : Locals :=
  ⟨[.i32 source, .i32 temporary, .i32 (UInt32.ofNat count)],
    [.i32 (UInt32.ofNat width), .i32 (UInt32.ofNat left),
      .i32 (UInt32.ofNat mid), .i32 (UInt32.ofNat right)],
    stack⟩

def mergeArguments
    (source temporary : UInt32) (left mid right : Nat)
    (stack : List Value) : List Value :=
  [.i32 (UInt32.ofNat right), .i32 (UInt32.ofNat mid),
    .i32 (UInt32.ofNat left), .i32 temporary, .i32 source] ++ stack

structure MergeLoopState where
  scratch : List UInt32
  i : Nat
  j : Nat
  k : Nat
  emitted : List UInt32

structure CopyLoopState where
  current : List UInt32
  copied : List UInt32
  k : Nat

structure SortInnerState where
  current : List UInt32
  scratch : List UInt32
  pass : Nat
  mid : Nat
  right : Nat

structure SortOuterState where
  current : List UInt32
  scratch : List UInt32
  width : Nat
  left : Nat
  mid : Nat
  right : Nat

set_option maxHeartbeats 4000000 in
theorem wp_mergeMainStep
    [WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (source temporary : UInt32) (input scratch : List UInt32)
    (left mid right i j k : Nat) (emitted : List UInt32)
    (hinv : MergeLoopInvariant input scratch left mid right i j k emitted)
    (_hi : i < mid) (_hj : j < right)
    (hiLen : i < input.length) (hjLen : j < input.length)
    (hkLen : k < scratch.length)
    (hlayout : ValidLayout source temporary input.length)
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {stack : List Value} :
    arrayAt 0 source input ∗ arrayAt 0 temporary scratch ∗
      ((⌜input[i]'hiLen < input[j]'hjLen⌝ ∗
          arrayAt 0 source input ∗
          arrayAt 0 temporary (scratch.set k (input[i]'hiLen)) -∗
          WP (.running
            ⟨mergeLocals source temporary left mid right
                (i + 1) j (k + 1) stack,
              code, arity, remainder, controls, calls⟩ : Expr Unit)
            @ s; E {{ Φ }}) ∧
       (⌜¬input[i]'hiLen < input[j]'hjLen⌝ ∗
          arrayAt 0 source input ∗
          arrayAt 0 temporary (scratch.set k (input[j]'hjLen)) -∗
          WP (.running
            ⟨mergeLocals source temporary left mid right
                i (j + 1) (k + 1) stack,
              code, arity, remainder, controls, calls⟩ : Expr Unit)
            @ s; E {{ Φ }})) ⊢
    WP (.running
      ⟨mergeLocals source temporary left mid right i j k stack,
        mergeMainStep ++ code, arity, remainder, controls, calls⟩ :
        Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨Hsource, Htemporary, Hbranches⟩
  simp only [mergeMainStep, List.append_assoc]
  iapply wp_loadAt hiLen hlayout.source_fits rfl rfl
  isplitl [Hsource]
  · iexact Hsource
  iintro Hsource
  iapply wp_loadAt hjLen hlayout.source_fits rfl rfl
  isplitl [Hsource]
  · iexact Hsource
  iintro Hsource
  simp only [List.cons_append, List.nil_append]
  iapply Wasm.SmallStep.wp_ltU rfl
  inext
  by_cases hxy : input[i]'hiLen < input[j]'hjLen
  · simp only [if_pos hxy]
    iapply Wasm.SmallStep.wp_iff rfl
    inext
    simp only [if_pos (by decide : (1 : UInt32) ≠ 0)]
    ihave Hthen := BI.and_elim_l $$ Hbranches
    iapply wp_copyAt hiLen hkLen hlayout.source_fits
      (by simpa [hinv.2.2.2.2.2] using hlayout.temporary_fits)
      rfl rfl rfl rfl
    isplitl [Hsource]
    · iexact Hsource
    isplitl [Htemporary]
    · iexact Htemporary
    iintro ⟨Hsource, Htemporary⟩
    have hiSucc : i + 1 < UInt32.size := by
      have := hlayout.length_lt
      omega
    have hkSucc : k + 1 < UInt32.size := by
      have hscratchLength := hinv.2.2.2.2.2
      have := hlayout.length_lt
      omega
    have hiValue :
        1 + UInt32.ofNat i = UInt32.ofNat (i + 1) := by
      rw [UInt32.add_comm, u32_ofNat_succ hiSucc]
    have hkValue :
        1 + UInt32.ofNat k = UInt32.ofNat (k + 1) := by
      rw [UInt32.add_comm, u32_ofNat_succ hkSucc]
    have hsetI :
        (mergeLocals source temporary left mid right i j k
            (.i32 (1 + UInt32.ofNat i) :: stack)).set?
            5 (.i32 (1 + UInt32.ofNat i)) =
          some (mergeLocals source temporary left mid right
            (i + 1) j k
            (.i32 (1 + UInt32.ofNat i) :: stack)) := by
      rw [hiValue]
      rfl
    simp only [mergeLocals, List.drop_zero]
    iapply wp_increment_nil rfl hsetI
    inext
    iapply Wasm.SmallStep.wp_exitControl rfl
    inext
    simp only [mergeLocals, List.take_zero, List.nil_append]
    have hsetK :
        (mergeLocals source temporary left mid right
            (i + 1) j k
            (.i32 (1 + UInt32.ofNat k) :: stack)).set?
            7 (.i32 (1 + UInt32.ofNat k)) =
          some (mergeLocals source temporary left mid right
            (i + 1) j (k + 1)
            (.i32 (1 + UInt32.ofNat k) :: stack)) := by
      rw [hkValue]
      rfl
    iapply wp_increment rfl hsetK
    inext
    simp only [mergeLocals]
    iapply Hthen
    isplitr
    · ipureintro
      exact hxy
    iframe
  · simp only [if_neg hxy]
    iapply Wasm.SmallStep.wp_iff rfl
    inext
    simp only [if_neg (by decide : ¬(0 : UInt32) ≠ 0)]
    ihave Helse := BI.and_elim_r $$ Hbranches
    iapply wp_copyAt hjLen hkLen hlayout.source_fits
      (by simpa [hinv.2.2.2.2.2] using hlayout.temporary_fits)
      rfl rfl rfl rfl
    isplitl [Hsource]
    · iexact Hsource
    isplitl [Htemporary]
    · iexact Htemporary
    iintro ⟨Hsource, Htemporary⟩
    have hjSucc : j + 1 < UInt32.size := by
      have := hlayout.length_lt
      omega
    have hkSucc : k + 1 < UInt32.size := by
      have hscratchLength := hinv.2.2.2.2.2
      have := hlayout.length_lt
      omega
    have hjValue :
        1 + UInt32.ofNat j = UInt32.ofNat (j + 1) := by
      rw [UInt32.add_comm, u32_ofNat_succ hjSucc]
    have hkValue :
        1 + UInt32.ofNat k = UInt32.ofNat (k + 1) := by
      rw [UInt32.add_comm, u32_ofNat_succ hkSucc]
    have hsetJ :
        (mergeLocals source temporary left mid right i j k
            (.i32 (1 + UInt32.ofNat j) :: stack)).set?
            6 (.i32 (1 + UInt32.ofNat j)) =
          some (mergeLocals source temporary left mid right
            i (j + 1) k
            (.i32 (1 + UInt32.ofNat j) :: stack)) := by
      rw [hjValue]
      rfl
    simp only [mergeLocals, List.drop_zero]
    iapply wp_increment_nil rfl hsetJ
    inext
    iapply Wasm.SmallStep.wp_exitControl rfl
    inext
    simp only [mergeLocals, List.take_zero, List.nil_append]
    have hsetK :
        (mergeLocals source temporary left mid right
            i (j + 1) k
            (.i32 (1 + UInt32.ofNat k) :: stack)).set?
            7 (.i32 (1 + UInt32.ofNat k)) =
          some (mergeLocals source temporary left mid right
            i (j + 1) (k + 1)
            (.i32 (1 + UInt32.ofNat k) :: stack)) := by
      rw [hkValue]
      rfl
    iapply wp_increment rfl hsetK
    inext
    simp only [mergeLocals]
    iapply Helse
    isplitr
    · ipureintro
      exact hxy
    iframe

set_option maxHeartbeats 4000000 in
theorem wp_mergeMainLoop
    [WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (source temporary : UInt32) (input scratch : List UInt32)
    (left mid right i j k : Nat) (emitted : List UInt32)
    (hinv : MergeLoopInvariant input scratch left mid right i j k emitted)
    (hlayout : ValidLayout source temporary input.length)
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {stack : List Value} :
    arrayAt 0 source input ∗ arrayAt 0 temporary scratch ∗
      (∀ (scratch' : List UInt32) (i' j' k' : Nat)
          (emitted' : List UInt32),
        ⌜MergeLoopInvariant input scratch' left mid right
          i' j' k' emitted'⌝ -∗
        ⌜i' = mid ∨ j' = right⌝ -∗
        arrayAt 0 source input -∗ arrayAt 0 temporary scratch' -∗
        WP (.running
          ⟨mergeLocals source temporary left mid right
              i' j' k' stack,
            code, arity, remainder, controls, calls⟩ : Expr Unit)
          @ s; E {{ Φ }}) ⊢
    WP (.running
      ⟨mergeLocals source temporary left mid right i j k stack,
        whileDo mergeMainCondition mergeMainStep ++ code,
        arity, remainder, controls, calls⟩ : Expr Unit)
      @ s; E {{ Φ }} := by
  let Finish : IProp (WasmHeapGF Unit) := iprop%
    ∀ (scratch' : List UInt32) (i' j' k' : Nat)
        (emitted' : List UInt32),
      ⌜MergeLoopInvariant input scratch' left mid right
        i' j' k' emitted'⌝ -∗
      ⌜i' = mid ∨ j' = right⌝ -∗
      arrayAt 0 source input -∗ arrayAt 0 temporary scratch' -∗
      WP (.running
        ⟨mergeLocals source temporary left mid right
            i' j' k' stack,
          code, arity, remainder, controls, calls⟩ : Expr Unit)
        @ s; E {{ Φ }}
  let Inv : MergeLoopState → IProp (WasmHeapGF Unit) := fun state => iprop%
    ⌜MergeLoopInvariant input state.scratch left mid right
      state.i state.j state.k state.emitted⌝ ∗
    arrayAt 0 source input ∗ arrayAt 0 temporary state.scratch ∗ Finish
  let blockFrame : ControlFrame :=
    { kind := .block
      paramArity := 0
      resultArity := 0
      body := [.loop 0 0
        (whileLoopCode mergeMainCondition mergeMainStep)]
      continuation := code
      belowStack := stack }
  iintro ⟨Hsource, Htemporary, Hfinish⟩
  simp only [whileDo, List.cons_append, List.nil_append]
  iapply Wasm.SmallStep.wp_block
  inext
  iapply wp_loop_löb_family_from
    (ι := MergeLoopState)
    (locals := fun state =>
      mergeLocals source temporary left mid right
        state.i state.j state.k stack)
    (I := Inv)
    (initial := ⟨scratch, i, j, k, emitted⟩)
    (initialLocals :=
      mergeLocals source temporary left mid right i j k stack)
    (body := whileLoopCode mergeMainCondition mergeMainStep)
    (code := [])
    (belowStack := stack)
    rfl
    rfl
  · intro state
    simp only [Inv, Wasm.SmallStep.loopBodyExpr]
    iintro Hrec Hinv
    icases Hinv with ⟨%hstate, Hsource, Htemporary, Hfinish⟩
    have hdata := hstate
    unfold MergeLoopInvariant at hdata
    have hiSize : state.i < UInt32.size := by
      have := hlayout.length_lt
      omega
    have hjSize : state.j < UInt32.size := by
      have := hlayout.length_lt
      omega
    have hmidSize : mid < UInt32.size := by
      have := hlayout.length_lt
      omega
    have hrightSize : right < UInt32.size := by
      have := hlayout.length_lt
      omega
    have hiCmp :
        (UInt32.ofNat state.i < UInt32.ofNat mid) ↔ state.i < mid := by
      change (UInt32.ofNat state.i).toNat <
          (UInt32.ofNat mid).toNat ↔ state.i < mid
      rw [UInt32.toNat_ofNat_of_lt' hiSize,
        UInt32.toNat_ofNat_of_lt' hmidSize]
    have hjCmp :
        (UInt32.ofNat state.j < UInt32.ofNat right) ↔
          state.j < right := by
      change (UInt32.ofNat state.j).toNat <
          (UInt32.ofNat right).toNat ↔ state.j < right
      rw [UInt32.toNat_ofNat_of_lt' hjSize,
        UInt32.toNat_ofNat_of_lt' hrightSize]
    simp only [whileLoopCode, mergeMainCondition, List.append_assoc]
    iapply wp_lessLocal rfl rfl
    inext
    iapply wp_lessLocal rfl rfl
    inext
    simp only [List.cons_append, List.nil_append]
    iapply Wasm.SmallStep.wp_mul
    inext
    iapply Wasm.SmallStep.wp_eqz rfl
    inext
    by_cases hi : state.i < mid
    · by_cases hj : state.j < right
      · simp only [hiCmp, hjCmp, if_pos hi, if_pos hj]
        have hiLen : state.i < input.length := by omega
        have hjLen : state.j < input.length := by omega
        have hkInput : state.k < input.length :=
          MergeLoopInvariant.k_lt hstate hi hj
        have hkLen : state.k < state.scratch.length := by
          rw [hdata.2.2.2.2.2.1]
          exact hkInput
        simp only [UInt32.mul_one,
          if_neg (by decide : (1 : UInt32) ≠ 0)]
        iapply Wasm.SmallStep.wp_brIfZero
        inext
        iapply wp_mergeMainStep source temporary input state.scratch
          left mid right state.i state.j state.k state.emitted
          hstate hi hj hiLen hjLen hkLen hlayout
        isplitl [Hsource]
        · iexact Hsource
        isplitl [Htemporary]
        · iexact Htemporary
        isplit
        · iintro ⟨%hxy, Hsource, Htemporary⟩
          iapply Wasm.SmallStep.wp_br rfl
          inext
          simp only [mergeLocals, List.take_zero, List.nil_append]
          ispecialize Hrec $$
            %(⟨state.scratch.set state.k input[state.i],
                state.i + 1, state.j, state.k + 1,
                state.emitted ++ [input[state.i]]⟩ : MergeLoopState)
          iapply Hrec
          isplitr
          · ipureintro
            exact hstate.takeLeft hi hj
              (List.getElem?_eq_getElem hiLen)
              (List.getElem?_eq_getElem hjLen) hxy
          iframe
        · iintro ⟨%hxy, Hsource, Htemporary⟩
          iapply Wasm.SmallStep.wp_br rfl
          inext
          simp only [mergeLocals, List.take_zero, List.nil_append]
          ispecialize Hrec $$
            %(⟨state.scratch.set state.k input[state.j],
                state.i, state.j + 1, state.k + 1,
                state.emitted ++ [input[state.j]]⟩ : MergeLoopState)
          iapply Hrec
          isplitr
          · ipureintro
            exact hstate.takeRight hi hj
              (List.getElem?_eq_getElem hiLen)
              (List.getElem?_eq_getElem hjLen) hxy
          iframe
      · simp only [hiCmp, hjCmp, if_pos hi, if_neg hj]
        have hjEq : state.j = right := by omega
        simp only [UInt32.zero_mul]
        iapply Wasm.SmallStep.wp_brIf (by decide) rfl
        inext
        simp only [mergeLocals, List.take_zero, List.nil_append,
          List.drop_zero]
        isimp only [Finish, mergeLocals] at Hfinish
        iapply Hfinish $$ %state.scratch %state.i %state.j
          %state.k %state.emitted %hstate %(Or.inr hjEq)
          Hsource Htemporary
    · simp only [hiCmp, if_neg hi]
      have hiEq : state.i = mid := by omega
      simp only [UInt32.mul_zero]
      iapply Wasm.SmallStep.wp_brIf (by decide) rfl
      inext
      simp only [mergeLocals, List.take_zero, List.nil_append,
        List.drop_zero]
      isimp only [Finish, mergeLocals] at Hfinish
      iapply Hfinish $$ %state.scratch %state.i %state.j
        %state.k %state.emitted %hstate %(Or.inl hiEq)
        Hsource Htemporary
  · simp only [Inv]
    isplitr
    · ipureintro
      exact hinv
    iframe

theorem wp_mergeMainLoop_from
    [WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (actualLocals : Locals) (stack : List Value)
    (source temporary : UInt32) (input scratch : List UInt32)
    (left mid right i j k : Nat) (emitted : List UInt32)
    (hinv : MergeLoopInvariant input scratch left mid right i j k emitted)
    (hlayout : ValidLayout source temporary input.length)
    (hlocals :
      actualLocals =
        mergeLocals source temporary left mid right i j k stack)
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    arrayAt 0 source input ∗ arrayAt 0 temporary scratch ∗
      (∀ (scratch' : List UInt32) (i' j' k' : Nat)
          (emitted' : List UInt32),
        ⌜MergeLoopInvariant input scratch' left mid right
          i' j' k' emitted'⌝ -∗
        ⌜i' = mid ∨ j' = right⌝ -∗
        arrayAt 0 source input -∗ arrayAt 0 temporary scratch' -∗
        WP (.running
          ⟨mergeLocals source temporary left mid right
              i' j' k' stack,
            code, arity, remainder, controls, calls⟩ : Expr Unit)
          @ s; E {{ Φ }}) ⊢
    WP (.running
      ⟨actualLocals, whileDo mergeMainCondition mergeMainStep ++ code,
        arity, remainder, controls, calls⟩ : Expr Unit)
      @ s; E {{ Φ }} := by
  subst actualLocals
  exact wp_mergeMainLoop source temporary input scratch
    left mid right i j k emitted hinv hlayout

set_option maxHeartbeats 3000000 in
theorem wp_mergeLeftStep
    [WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (source temporary : UInt32) (input scratch : List UInt32)
    (left mid right i j k : Nat)
    (hiLen : i < input.length) (hkLen : k < scratch.length)
    (hscratchLength : scratch.length = input.length)
    (hlayout : ValidLayout source temporary input.length)
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {stack : List Value} :
    arrayAt 0 source input ∗ arrayAt 0 temporary scratch ∗
      (arrayAt 0 source input ∗
        arrayAt 0 temporary (scratch.set k input[i]) -∗
        WP (.running
          ⟨mergeLocals source temporary left mid right
              (i + 1) j (k + 1) stack,
            code, arity, remainder, controls, calls⟩ : Expr Unit)
          @ s; E {{ Φ }}) ⊢
    WP (.running
      ⟨mergeLocals source temporary left mid right i j k stack,
        mergeLeftStep ++ code, arity, remainder, controls, calls⟩ :
        Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨Hsource, Htemporary, Hcont⟩
  simp only [mergeLeftStep, List.append_assoc]
  iapply wp_copyAt hiLen hkLen hlayout.source_fits
    (by simpa [hscratchLength] using hlayout.temporary_fits)
    rfl rfl rfl rfl
  isplitl [Hsource]
  · iexact Hsource
  isplitl [Htemporary]
  · iexact Htemporary
  iintro ⟨Hsource, Htemporary⟩
  have hiSucc : i + 1 < UInt32.size := by
    have := hlayout.length_lt
    omega
  have hkSucc : k + 1 < UInt32.size := by
    have := hlayout.length_lt
    rw [hscratchLength] at hkLen
    omega
  have hiValue :
      1 + UInt32.ofNat i = UInt32.ofNat (i + 1) := by
    rw [UInt32.add_comm, u32_ofNat_succ hiSucc]
  have hkValue :
      1 + UInt32.ofNat k = UInt32.ofNat (k + 1) := by
    rw [UInt32.add_comm, u32_ofNat_succ hkSucc]
  have hsetI :
      (mergeLocals source temporary left mid right i j k
          (.i32 (1 + UInt32.ofNat i) :: stack)).set?
          5 (.i32 (1 + UInt32.ofNat i)) =
        some (mergeLocals source temporary left mid right
          (i + 1) j k
          (.i32 (1 + UInt32.ofNat i) :: stack)) := by
    rw [hiValue]
    rfl
  simp only [mergeLocals]
  iapply wp_increment rfl hsetI
  inext
  simp only [mergeLocals]
  have hsetK :
      (mergeLocals source temporary left mid right
          (i + 1) j k
          (.i32 (1 + UInt32.ofNat k) :: stack)).set?
          7 (.i32 (1 + UInt32.ofNat k)) =
        some (mergeLocals source temporary left mid right
          (i + 1) j (k + 1)
          (.i32 (1 + UInt32.ofNat k) :: stack)) := by
    rw [hkValue]
    rfl
  iapply wp_increment rfl hsetK
  inext
  simp only [mergeLocals]
  iapply Hcont
  iframe

set_option maxHeartbeats 3000000 in
theorem wp_mergeRightStep
    [WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (source temporary : UInt32) (input scratch : List UInt32)
    (left mid right i j k : Nat)
    (hjLen : j < input.length) (hkLen : k < scratch.length)
    (hscratchLength : scratch.length = input.length)
    (hlayout : ValidLayout source temporary input.length)
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {stack : List Value} :
    arrayAt 0 source input ∗ arrayAt 0 temporary scratch ∗
      (arrayAt 0 source input ∗
        arrayAt 0 temporary (scratch.set k input[j]) -∗
        WP (.running
          ⟨mergeLocals source temporary left mid right
              i (j + 1) (k + 1) stack,
            code, arity, remainder, controls, calls⟩ : Expr Unit)
          @ s; E {{ Φ }}) ⊢
    WP (.running
      ⟨mergeLocals source temporary left mid right i j k stack,
        mergeRightStep ++ code, arity, remainder, controls, calls⟩ :
        Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨Hsource, Htemporary, Hcont⟩
  simp only [mergeRightStep, List.append_assoc]
  iapply wp_copyAt hjLen hkLen hlayout.source_fits
    (by simpa [hscratchLength] using hlayout.temporary_fits)
    rfl rfl rfl rfl
  isplitl [Hsource]
  · iexact Hsource
  isplitl [Htemporary]
  · iexact Htemporary
  iintro ⟨Hsource, Htemporary⟩
  have hjSucc : j + 1 < UInt32.size := by
    have := hlayout.length_lt
    omega
  have hkSucc : k + 1 < UInt32.size := by
    have := hlayout.length_lt
    rw [hscratchLength] at hkLen
    omega
  have hjValue :
      1 + UInt32.ofNat j = UInt32.ofNat (j + 1) := by
    rw [UInt32.add_comm, u32_ofNat_succ hjSucc]
  have hkValue :
      1 + UInt32.ofNat k = UInt32.ofNat (k + 1) := by
    rw [UInt32.add_comm, u32_ofNat_succ hkSucc]
  have hsetJ :
      (mergeLocals source temporary left mid right i j k
          (.i32 (1 + UInt32.ofNat j) :: stack)).set?
          6 (.i32 (1 + UInt32.ofNat j)) =
        some (mergeLocals source temporary left mid right
          i (j + 1) k
          (.i32 (1 + UInt32.ofNat j) :: stack)) := by
    rw [hjValue]
    rfl
  simp only [mergeLocals]
  iapply wp_increment rfl hsetJ
  inext
  simp only [mergeLocals]
  have hsetK :
      (mergeLocals source temporary left mid right
          i (j + 1) k
          (.i32 (1 + UInt32.ofNat k) :: stack)).set?
          7 (.i32 (1 + UInt32.ofNat k)) =
        some (mergeLocals source temporary left mid right
          i (j + 1) (k + 1)
          (.i32 (1 + UInt32.ofNat k) :: stack)) := by
    rw [hkValue]
    rfl
  iapply wp_increment rfl hsetK
  inext
  simp only [mergeLocals]
  iapply Hcont
  iframe

set_option maxHeartbeats 4000000 in
theorem wp_mergeLeftLoop
    [WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (source temporary : UInt32) (input scratch : List UInt32)
    (left mid right i j k : Nat) (emitted : List UInt32)
    (hinv : MergeLoopInvariant input scratch left mid right i j k emitted)
    (hexhausted : i = mid ∨ j = right)
    (hlayout : ValidLayout source temporary input.length)
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {stack : List Value} :
    arrayAt 0 source input ∗ arrayAt 0 temporary scratch ∗
      (∀ (scratch' : List UInt32) (j' k' : Nat)
          (emitted' : List UInt32),
        ⌜MergeLoopInvariant input scratch' left mid right
          mid j' k' emitted'⌝ -∗
        arrayAt 0 source input -∗ arrayAt 0 temporary scratch' -∗
        WP (.running
          ⟨mergeLocals source temporary left mid right
              mid j' k' stack,
            code, arity, remainder, controls, calls⟩ : Expr Unit)
          @ s; E {{ Φ }}) ⊢
    WP (.running
      ⟨mergeLocals source temporary left mid right i j k stack,
        whileDo mergeLeftCondition mergeLeftStep ++ code,
        arity, remainder, controls, calls⟩ : Expr Unit)
      @ s; E {{ Φ }} := by
  let Finish : IProp (WasmHeapGF Unit) := iprop%
    ∀ (scratch' : List UInt32) (j' k' : Nat)
        (emitted' : List UInt32),
      ⌜MergeLoopInvariant input scratch' left mid right
        mid j' k' emitted'⌝ -∗
      arrayAt 0 source input -∗ arrayAt 0 temporary scratch' -∗
      WP (.running
        ⟨mergeLocals source temporary left mid right
            mid j' k' stack,
          code, arity, remainder, controls, calls⟩ : Expr Unit)
        @ s; E {{ Φ }}
  let Inv : MergeLoopState → IProp (WasmHeapGF Unit) := fun state => iprop%
    ⌜MergeLoopInvariant input state.scratch left mid right
      state.i state.j state.k state.emitted⌝ ∗
    ⌜state.i = mid ∨ state.j = right⌝ ∗
    arrayAt 0 source input ∗ arrayAt 0 temporary state.scratch ∗ Finish
  iintro ⟨Hsource, Htemporary, Hfinish⟩
  simp only [whileDo, List.cons_append, List.nil_append]
  iapply Wasm.SmallStep.wp_block
  inext
  iapply wp_loop_löb_family_from
    (ι := MergeLoopState)
    (locals := fun state =>
      mergeLocals source temporary left mid right
        state.i state.j state.k stack)
    (I := Inv)
    (initial := ⟨scratch, i, j, k, emitted⟩)
    (initialLocals :=
      mergeLocals source temporary left mid right i j k stack)
    (body := whileLoopCode mergeLeftCondition mergeLeftStep)
    (code := [])
    (belowStack := stack)
    rfl
    rfl
  · intro state
    simp only [Inv, Wasm.SmallStep.loopBodyExpr]
    iintro Hrec Hinv
    icases Hinv with
      ⟨%hstate, %hstateExhausted, Hsource, Htemporary, Hfinish⟩
    have hdata := hstate
    unfold MergeLoopInvariant at hdata
    have hiSize : state.i < UInt32.size := by
      have := hlayout.length_lt
      omega
    have hmidSize : mid < UInt32.size := by
      have := hlayout.length_lt
      omega
    have hiCmp :
        (UInt32.ofNat state.i < UInt32.ofNat mid) ↔ state.i < mid := by
      change (UInt32.ofNat state.i).toNat <
          (UInt32.ofNat mid).toNat ↔ state.i < mid
      rw [UInt32.toNat_ofNat_of_lt' hiSize,
        UInt32.toNat_ofNat_of_lt' hmidSize]
    simp only [whileLoopCode, mergeLeftCondition, List.append_assoc]
    iapply wp_lessLocal rfl rfl
    inext
    simp only [List.cons_append, List.nil_append]
    iapply Wasm.SmallStep.wp_eqz rfl
    inext
    by_cases hi : state.i < mid
    · simp only [hiCmp, if_pos hi]
      have hjEq : state.j = right := by
        rcases hstateExhausted with hEq | hEq
        · omega
        · exact hEq
      have hstateRight :
          MergeLoopInvariant input state.scratch left mid right
            state.i right state.k state.emitted := by
        simpa [hjEq] using hstate
      have hiLen : state.i < input.length := by omega
      have hkInput : state.k < input.length := by
        omega
      have hkLen : state.k < state.scratch.length := by
        rw [hdata.2.2.2.2.2.1]
        exact hkInput
      simp only [if_neg (by decide : (1 : UInt32) ≠ 0)]
      iapply Wasm.SmallStep.wp_brIfZero
      inext
      iapply wp_mergeLeftStep source temporary input state.scratch
        left mid right state.i state.j state.k
        hiLen hkLen hdata.2.2.2.2.2.1 hlayout
      isplitl [Hsource]
      · iexact Hsource
      isplitl [Htemporary]
      · iexact Htemporary
      iintro ⟨Hsource, Htemporary⟩
      iapply Wasm.SmallStep.wp_br rfl
      inext
      simp only [mergeLocals, List.take_zero, List.nil_append]
      ispecialize Hrec $$
        %(⟨state.scratch.set state.k input[state.i],
            state.i + 1, state.j, state.k + 1,
            state.emitted ++ [input[state.i]]⟩ : MergeLoopState)
      iapply Hrec
      isplitr
      · ipureintro
        simpa [hjEq] using hstateRight.takeRemainingLeft hi
          (List.getElem?_eq_getElem hiLen)
      isplitr
      · ipureintro
        exact Or.inr hjEq
      iframe
    · simp only [hiCmp, if_neg hi]
      have hiEq : state.i = mid := by omega
      subst mid
      iapply Wasm.SmallStep.wp_brIf (by decide) rfl
      inext
      simp only [mergeLocals, List.take_zero, List.nil_append,
        List.drop_zero]
      isimp only [Finish, mergeLocals] at Hfinish
      iapply Hfinish $$ %state.scratch %state.j %state.k
        %state.emitted %hstate Hsource Htemporary
  · simp only [Inv]
    isplitr
    · ipureintro
      exact hinv
    isplitr
    · ipureintro
      exact hexhausted
    iframe

set_option maxHeartbeats 4000000 in
theorem wp_mergeRightLoop
    [WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (source temporary : UInt32) (input scratch : List UInt32)
    (left mid right j k : Nat) (emitted : List UInt32)
    (hinv :
      MergeLoopInvariant input scratch left mid right mid j k emitted)
    (hlayout : ValidLayout source temporary input.length)
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {stack : List Value} :
    arrayAt 0 source input ∗ arrayAt 0 temporary scratch ∗
      (∀ (scratch' : List UInt32) (k' : Nat)
          (emitted' : List UInt32),
        ⌜MergeLoopInvariant input scratch' left mid right
          mid right k' emitted'⌝ -∗
        arrayAt 0 source input -∗ arrayAt 0 temporary scratch' -∗
        WP (.running
          ⟨mergeLocals source temporary left mid right
              mid right k' stack,
            code, arity, remainder, controls, calls⟩ : Expr Unit)
          @ s; E {{ Φ }}) ⊢
    WP (.running
      ⟨mergeLocals source temporary left mid right mid j k stack,
        whileDo mergeRightCondition mergeRightStep ++ code,
        arity, remainder, controls, calls⟩ : Expr Unit)
      @ s; E {{ Φ }} := by
  let Finish : IProp (WasmHeapGF Unit) := iprop%
    ∀ (scratch' : List UInt32) (k' : Nat)
        (emitted' : List UInt32),
      ⌜MergeLoopInvariant input scratch' left mid right
        mid right k' emitted'⌝ -∗
      arrayAt 0 source input -∗ arrayAt 0 temporary scratch' -∗
      WP (.running
        ⟨mergeLocals source temporary left mid right
            mid right k' stack,
          code, arity, remainder, controls, calls⟩ : Expr Unit)
        @ s; E {{ Φ }}
  let Inv : MergeLoopState → IProp (WasmHeapGF Unit) := fun state => iprop%
    ⌜MergeLoopInvariant input state.scratch left mid right
      mid state.j state.k state.emitted⌝ ∗
    arrayAt 0 source input ∗ arrayAt 0 temporary state.scratch ∗ Finish
  iintro ⟨Hsource, Htemporary, Hfinish⟩
  simp only [whileDo, List.cons_append, List.nil_append]
  iapply Wasm.SmallStep.wp_block
  inext
  iapply wp_loop_löb_family_from
    (ι := MergeLoopState)
    (locals := fun state =>
      mergeLocals source temporary left mid right
        mid state.j state.k stack)
    (I := Inv)
    (initial := ⟨scratch, mid, j, k, emitted⟩)
    (initialLocals :=
      mergeLocals source temporary left mid right mid j k stack)
    (body := whileLoopCode mergeRightCondition mergeRightStep)
    (code := [])
    (belowStack := stack)
    rfl
    rfl
  · intro state
    simp only [Inv, Wasm.SmallStep.loopBodyExpr]
    iintro Hrec Hinv
    icases Hinv with ⟨%hstate, Hsource, Htemporary, Hfinish⟩
    have hdata := hstate
    unfold MergeLoopInvariant at hdata
    have hjSize : state.j < UInt32.size := by
      have := hlayout.length_lt
      omega
    have hrightSize : right < UInt32.size := by
      have := hlayout.length_lt
      omega
    have hjCmp :
        (UInt32.ofNat state.j < UInt32.ofNat right) ↔
          state.j < right := by
      change (UInt32.ofNat state.j).toNat <
          (UInt32.ofNat right).toNat ↔ state.j < right
      rw [UInt32.toNat_ofNat_of_lt' hjSize,
        UInt32.toNat_ofNat_of_lt' hrightSize]
    simp only [whileLoopCode, mergeRightCondition, List.append_assoc]
    iapply wp_lessLocal rfl rfl
    inext
    simp only [List.cons_append, List.nil_append]
    iapply Wasm.SmallStep.wp_eqz rfl
    inext
    by_cases hj : state.j < right
    · simp only [hjCmp, if_pos hj,
        if_neg (by decide : (1 : UInt32) ≠ 0)]
      have hjLen : state.j < input.length := by omega
      have hkInput : state.k < input.length := by omega
      have hkLen : state.k < state.scratch.length := by
        rw [hdata.2.2.2.2.2.1]
        exact hkInput
      iapply Wasm.SmallStep.wp_brIfZero
      inext
      iapply wp_mergeRightStep source temporary input state.scratch
        left mid right mid state.j state.k
        hjLen hkLen hdata.2.2.2.2.2.1 hlayout
      isplitl [Hsource]
      · iexact Hsource
      isplitl [Htemporary]
      · iexact Htemporary
      iintro ⟨Hsource, Htemporary⟩
      iapply Wasm.SmallStep.wp_br rfl
      inext
      simp only [mergeLocals, List.take_zero, List.nil_append]
      ispecialize Hrec $$
        %(⟨state.scratch.set state.k input[state.j],
            mid, state.j + 1, state.k + 1,
            state.emitted ++ [input[state.j]]⟩ : MergeLoopState)
      iapply Hrec
      isplitr
      · ipureintro
        exact hstate.takeRemainingRight hj
          (List.getElem?_eq_getElem hjLen)
      iframe
    · simp only [hjCmp, if_neg hj]
      have hjEq : state.j = right := by omega
      subst right
      iapply Wasm.SmallStep.wp_brIf (by decide) rfl
      inext
      simp only [mergeLocals, List.take_zero, List.nil_append,
        List.drop_zero]
      isimp only [Finish, mergeLocals] at Hfinish
      iapply Hfinish $$ %state.scratch %state.k
        %state.emitted %hstate Hsource Htemporary
  · simp only [Inv]
    isplitr
    · ipureintro
      exact hinv
    iframe

set_option maxHeartbeats 3000000 in
theorem wp_mergeCopyStep
    [WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (source temporary : UInt32) (current scratch : List UInt32)
    (left mid right k : Nat)
    (hkCurrent : k < current.length) (hkScratch : k < scratch.length)
    (hscratchLength : scratch.length = current.length)
    (hlayout : ValidLayout source temporary current.length)
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {stack : List Value} :
    arrayAt 0 source current ∗ arrayAt 0 temporary scratch ∗
      (arrayAt 0 source (current.set k scratch[k]) ∗
        arrayAt 0 temporary scratch -∗
        WP (.running
          ⟨mergeLocals source temporary left mid right
              mid right (k + 1) stack,
            code, arity, remainder, controls, calls⟩ : Expr Unit)
          @ s; E {{ Φ }}) ⊢
    WP (.running
      ⟨mergeLocals source temporary left mid right mid right k stack,
        mergeCopyStep ++ code, arity, remainder, controls, calls⟩ :
        Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨Hsource, Htemporary, Hcont⟩
  simp only [mergeCopyStep, List.append_assoc]
  iapply wp_copyAt hkScratch hkCurrent
    (by simpa [hscratchLength] using hlayout.temporary_fits)
    hlayout.source_fits
    rfl rfl rfl rfl
  isplitl [Htemporary]
  · iexact Htemporary
  isplitl [Hsource]
  · iexact Hsource
  iintro ⟨Htemporary, Hsource⟩
  have hkSucc : k + 1 < UInt32.size := by
    have := hlayout.length_lt
    omega
  have hkValue :
      1 + UInt32.ofNat k = UInt32.ofNat (k + 1) := by
    rw [UInt32.add_comm, u32_ofNat_succ hkSucc]
  have hsetK :
      (mergeLocals source temporary left mid right mid right k
          (.i32 (1 + UInt32.ofNat k) :: stack)).set?
          7 (.i32 (1 + UInt32.ofNat k)) =
        some (mergeLocals source temporary left mid right
          mid right (k + 1)
          (.i32 (1 + UInt32.ofNat k) :: stack)) := by
    rw [hkValue]
    rfl
  simp only [mergeLocals]
  iapply wp_increment rfl hsetK
  inext
  simp only [mergeLocals]
  iapply Hcont
  isplitl [Hsource]
  · iexact Hsource
  iexact Htemporary

set_option maxHeartbeats 5000000 in
theorem wp_mergeCopyLoop
    [WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (source temporary : UInt32)
    (input current scratch merged copied : List UInt32)
    (left mid right k : Nat)
    (hcopy : CopyLoopInvariant input current left right k copied)
    (hcopied : copied = merged.take (k - left))
    (hscratchLength : scratch.length = input.length)
    (htemporary : scratch.take right = scratch.take left ++ merged)
    (hmergedLength : merged.length = right - left)
    (hlayout : ValidLayout source temporary input.length)
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {stack : List Value} :
    arrayAt 0 source current ∗ arrayAt 0 temporary scratch ∗
      (∀ output : List UInt32,
        ⌜CopyLoopInvariant input output left right right merged⌝ -∗
        arrayAt 0 source output -∗ arrayAt 0 temporary scratch -∗
        WP (.running
          ⟨mergeLocals source temporary left mid right
              mid right right stack,
            code, arity, remainder, controls, calls⟩ : Expr Unit)
          @ s; E {{ Φ }}) ⊢
    WP (.running
      ⟨mergeLocals source temporary left mid right mid right k stack,
        whileDo mergeCopyCondition mergeCopyStep ++ code,
        arity, remainder, controls, calls⟩ : Expr Unit)
      @ s; E {{ Φ }} := by
  let Finish : IProp (WasmHeapGF Unit) := iprop%
    ∀ output : List UInt32,
      ⌜CopyLoopInvariant input output left right right merged⌝ -∗
      arrayAt 0 source output -∗ arrayAt 0 temporary scratch -∗
      WP (.running
        ⟨mergeLocals source temporary left mid right
            mid right right stack,
          code, arity, remainder, controls, calls⟩ : Expr Unit)
        @ s; E {{ Φ }}
  let Inv : CopyLoopState → IProp (WasmHeapGF Unit) := fun state => iprop%
    ⌜CopyLoopInvariant input state.current left right
      state.k state.copied⌝ ∗
    ⌜state.copied = merged.take (state.k - left)⌝ ∗
    arrayAt 0 source state.current ∗ arrayAt 0 temporary scratch ∗ Finish
  iintro ⟨Hsource, Htemporary, Hfinish⟩
  simp only [whileDo, List.cons_append, List.nil_append]
  iapply Wasm.SmallStep.wp_block
  inext
  iapply wp_loop_löb_family_from
    (ι := CopyLoopState)
    (locals := fun state =>
      mergeLocals source temporary left mid right
        mid right state.k stack)
    (I := Inv)
    (initial := ⟨current, copied, k⟩)
    (initialLocals :=
      mergeLocals source temporary left mid right mid right k stack)
    (body := whileLoopCode mergeCopyCondition mergeCopyStep)
    (code := [])
    (belowStack := stack)
    rfl
    rfl
  · intro state
    simp only [Inv, Wasm.SmallStep.loopBodyExpr]
    iintro Hrec Hinv
    icases Hinv with
      ⟨%hcopyState, %hcopiedState, Hsource, Htemporary, Hfinish⟩
    have hcopyData := hcopyState
    unfold CopyLoopInvariant at hcopyData
    have hkSize : state.k < UInt32.size := by
      have := hlayout.length_lt
      omega
    have hrightSize : right < UInt32.size := by
      have := hlayout.length_lt
      omega
    have hkCmp :
        (UInt32.ofNat state.k < UInt32.ofNat right) ↔
          state.k < right := by
      change (UInt32.ofNat state.k).toNat <
          (UInt32.ofNat right).toNat ↔ state.k < right
      rw [UInt32.toNat_ofNat_of_lt' hkSize,
        UInt32.toNat_ofNat_of_lt' hrightSize]
    simp only [whileLoopCode, mergeCopyCondition, List.append_assoc]
    iapply wp_lessLocal rfl rfl
    inext
    simp only [List.cons_append, List.nil_append]
    iapply Wasm.SmallStep.wp_eqz rfl
    inext
    by_cases hk : state.k < right
    · simp only [hkCmp, if_pos hk,
        if_neg (by decide : (1 : UInt32) ≠ 0)]
      have hkInput : state.k < input.length := by omega
      have hkCurrent := hcopyState.k_lt_length hk
      have hkScratch : state.k < scratch.length := by
        rw [hscratchLength]
        exact hkInput
      have hkMerged : state.k - left < merged.length := by omega
      have hlookup :
          scratch[state.k]? = some merged[state.k - left] := by
        rw [getElem?_of_take_eq_append
          (values := scratch) (pref := scratch.take left)
          (merged := merged) (left := left) (right := right)
          (k := state.k) (by omega) rfl htemporary (by omega) hk]
        exact List.getElem?_eq_getElem hkMerged
      have hscratchValue :
          scratch[state.k] = merged[state.k - left] := by
        have hactual :
            scratch[state.k]? = some scratch[state.k] :=
          List.getElem?_eq_getElem hkScratch
        rw [hactual] at hlookup
        exact Option.some.inj hlookup
      iapply Wasm.SmallStep.wp_brIfZero
      inext
      iapply wp_mergeCopyStep source temporary
        state.current scratch left mid right state.k
        hkCurrent hkScratch
        (by simpa [hcopyData.2.2.2.1] using hscratchLength)
        (by simpa [hcopyData.2.2.2.1] using hlayout)
      isplitl [Hsource]
      · iexact Hsource
      isplitl [Htemporary]
      · iexact Htemporary
      iintro ⟨Hsource, Htemporary⟩
      iapply Wasm.SmallStep.wp_br rfl
      inext
      simp only [mergeLocals, List.take_zero, List.nil_append]
      ispecialize Hrec $$
        %(⟨state.current.set state.k scratch[state.k],
            state.copied ++ [scratch[state.k]],
            state.k + 1⟩ : CopyLoopState)
      iapply Hrec
      isplitr
      · ipureintro
        exact hcopyState.step hk
      isplitr
      · ipureintro
        rw [hcopiedState, hscratchValue]
        have hsub :
            state.k + 1 - left = (state.k - left) + 1 := by omega
        rw [hsub, take_succ_eq_append_getElem hkMerged]
      iframe
    · simp only [hkCmp, if_neg hk]
      have hkEq : state.k = right := by omega
      have hcopiedEq : state.copied = merged := by
        rw [hcopiedState, hkEq, ← hmergedLength, List.take_length]
      have hcopyFinished :
          CopyLoopInvariant input state.current left right right merged := by
        simpa [hkEq, hcopiedEq] using hcopyState
      subst right
      iapply Wasm.SmallStep.wp_brIf (by decide) rfl
      inext
      simp only [mergeLocals, List.take_zero, List.nil_append,
        List.drop_zero]
      isimp only [Finish, mergeLocals] at Hfinish
      iapply Hfinish $$ %state.current %hcopyFinished
        Hsource Htemporary
  · simp only [Inv]
    isplitr
    · ipureintro
      exact hcopy
    isplitr
    · ipureintro
      exact hcopied
    iframe

theorem wp_mergeCopyLoop_from
    [WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (actualLocals : Locals) (stack : List Value)
    (source temporary : UInt32)
    (input current scratch merged copied : List UInt32)
    (left mid right k : Nat)
    (hcopy : CopyLoopInvariant input current left right k copied)
    (hcopied : copied = merged.take (k - left))
    (hscratchLength : scratch.length = input.length)
    (htemporary : scratch.take right = scratch.take left ++ merged)
    (hmergedLength : merged.length = right - left)
    (hlayout : ValidLayout source temporary input.length)
    (hlocals :
      actualLocals =
        mergeLocals source temporary left mid right mid right k stack)
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    arrayAt 0 source current ∗ arrayAt 0 temporary scratch ∗
      (∀ output : List UInt32,
        ⌜CopyLoopInvariant input output left right right merged⌝ -∗
        arrayAt 0 source output -∗ arrayAt 0 temporary scratch -∗
        WP (.running
          ⟨mergeLocals source temporary left mid right
              mid right right stack,
            code, arity, remainder, controls, calls⟩ : Expr Unit)
          @ s; E {{ Φ }}) ⊢
    WP (.running
      ⟨actualLocals, whileDo mergeCopyCondition mergeCopyStep ++ code,
        arity, remainder, controls, calls⟩ : Expr Unit)
      @ s; E {{ Φ }} := by
  subst actualLocals
  exact wp_mergeCopyLoop source temporary input current scratch
    merged copied left mid right k hcopy hcopied hscratchLength
    htemporary hmergedLength hlayout

set_option maxHeartbeats 8000000 in
theorem wp_mergeBody
    [WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (source temporary : UInt32) (input scratch : List UInt32)
    (left mid right : Nat)
    {calls : List CallFrame} :
    mergePre source temporary input scratch left mid right ∗
      (∀ (output scratch' : List UInt32),
        ⌜MergeRange input output left mid right⌝ -∗
        ⌜scratch'.length = input.length⌝ -∗
        arrayAt 0 source output -∗ arrayAt 0 temporary scratch' -∗
        WP (.running
          ⟨mergeLocals source temporary left mid right
              mid right right [],
            [.ret], 0, [], [], calls⟩ : Expr Unit)
          @ s; E {{ Φ }}) ⊢
    WP (.running
      ⟨mergeLocals source temporary left mid right 0 0 0 [],
        mergeBody, 0, [], [], calls⟩ : Expr Unit)
      @ s; E {{ Φ }} := by
  simp only [mergePre]
  iintro ⟨Hpre, Hfinish⟩
  icases Hpre with
    ⟨Hsource, Htemporary, %hscratchLength, %hlayout, %hbounds⟩
  simp only [mergeBody, List.cons_append, List.nil_append]
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_localSet rfl
  inext
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_localSet rfl
  inext
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_localSet rfl
  inext
  simp [mergeLocals, List.set]
  have hinvStart :
      MergeLoopInvariant input scratch left mid right
        left mid left [] :=
    mergeLoopInvariant_start hbounds hscratchLength
  iapply wp_mergeMainLoop_from
    (⟨[.i32 source, .i32 temporary, .i32 (UInt32.ofNat left),
        .i32 (UInt32.ofNat mid), .i32 (UInt32.ofNat right)],
      [.i32 (UInt32.ofNat left), .i32 (UInt32.ofNat mid),
        .i32 (UInt32.ofNat left)], []⟩ : Locals)
    [] source temporary input scratch
    left mid right left mid left [] hinvStart hlayout rfl
  isplitl [Hsource]
  · iexact Hsource
  isplitl [Htemporary]
  · iexact Htemporary
  iintro %scratch' %i' %j' %k' %emitted'
    %hinv' %hexhausted Hsource Htemporary
  iapply wp_mergeLeftLoop source temporary input scratch'
    left mid right i' j' k' emitted' hinv' hexhausted hlayout
  isplitl [Hsource]
  · iexact Hsource
  isplitl [Htemporary]
  · iexact Htemporary
  iintro %scratch'' %j'' %k'' %emitted''
    %hinv'' Hsource Htemporary
  iapply wp_mergeRightLoop source temporary input scratch''
    left mid right j'' k'' emitted'' hinv'' hlayout
  isplitl [Hsource]
  · iexact Hsource
  isplitl [Htemporary]
  · iexact Htemporary
  iintro %scratchFinal %kFinal %merged
    %hinvFinal Hsource Htemporary
  rcases hinvFinal.finished with
    ⟨hkFinal, htemporary, hmerge⟩
  subst kFinal
  have hscratchFinalLength :
      scratchFinal.length = input.length :=
    hinvFinal.2.2.2.2.2.1
  have hmergedLength : merged.length = right - left := by
    have hlength := (perm_of_mergeRel hmerge).length_eq
    simp [segment, List.length_take, List.length_drop] at hlength
    omega
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_localSet rfl
  inext
  simp [mergeLocals, List.set]
  have hcopyStart :
      CopyLoopInvariant input input left right left [] :=
    copyLoopInvariant_start
      (Nat.le_trans hbounds.1 hbounds.2.1) hbounds.2.2
  iapply wp_mergeCopyLoop_from
    (⟨[.i32 source, .i32 temporary, .i32 (UInt32.ofNat left),
        .i32 (UInt32.ofNat mid), .i32 (UInt32.ofNat right)],
      [.i32 (UInt32.ofNat mid), .i32 (UInt32.ofNat right),
        .i32 (UInt32.ofNat left)], []⟩ : Locals)
    [] source temporary
    input input scratchFinal merged []
    left mid right left hcopyStart (by simp)
    hscratchFinalLength htemporary hmergedLength hlayout rfl
  isplitl [Hsource]
  · iexact Hsource
  isplitl [Htemporary]
  · iexact Htemporary
  iintro %output %hcopy Hsource Htemporary
  have hmergeRange : MergeRange input output left mid right :=
    hcopy.finish hbounds.1 hbounds.2.1 hmerge
  simp only [mergeLocals]
  iapply Hfinish $$ %output %scratchFinal
    %hmergeRange %hscratchFinalLength Hsource Htemporary

theorem wp_mergeBody_from
    [WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (actualLocals : Locals)
    (source temporary : UInt32) (input scratch : List UInt32)
    (left mid right : Nat)
    (hlocals :
      actualLocals =
        mergeLocals source temporary left mid right 0 0 0 [])
    {calls : List CallFrame} :
    mergePre source temporary input scratch left mid right ∗
      (∀ (output scratch' : List UInt32),
        ⌜MergeRange input output left mid right⌝ -∗
        ⌜scratch'.length = input.length⌝ -∗
        arrayAt 0 source output -∗ arrayAt 0 temporary scratch' -∗
        WP (.running
          ⟨mergeLocals source temporary left mid right
              mid right right [],
            [.ret], 0, [], [], calls⟩ : Expr Unit)
          @ s; E {{ Φ }}) ⊢
    WP (.running
      ⟨actualLocals, mergeBody, 0, [], [], calls⟩ : Expr Unit)
      @ s; E {{ Φ }} := by
  subst actualLocals
  exact wp_mergeBody source temporary input scratch left mid right

set_option maxHeartbeats 4000000 in
theorem wp_merge
    [WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (runtimeModule : Module) (mergeIndex : Nat)
    (himports : ¬mergeIndex < runtimeModule.imports.length)
    (hfunction :
      runtimeModule.funcs[mergeIndex - runtimeModule.imports.length]? =
        some mergeFunction)
    (source temporary : UInt32) (input scratch : List UInt32)
    (left mid right : Nat)
    {callerLocals : Locals}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {stack : List Value} :
    runtimeModuleOwn ⟨0⟩ runtimeModule ∗
      mergePre source temporary input scratch left mid right ∗
      (runtimeModuleOwn ⟨0⟩ runtimeModule -∗
        mergePost source temporary input left mid right -∗
        WP (.running
          ⟨{ callerLocals with values := stack },
            code, arity, remainder, controls, calls⟩ : Expr Unit)
          @ s; E {{ Φ }}) ⊢
    WP (.running
      ⟨{ callerLocals with
          values :=
            mergeArguments source temporary left mid right stack },
        .call mergeIndex :: code, arity, remainder, controls, calls⟩ :
        Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨Hruntime, Hpre, Hcont⟩
  ihave HruntimeLater : ▷ runtimeModuleOwn ⟨0⟩ runtimeModule $$ [Hruntime]
  · inext
    iexact Hruntime
  iapply Wasm.SmallStep.wp_call runtimeModule mergeIndex mergeFunction
    himports hfunction $$ HruntimeLater
  inext
  iintro Hruntime
  simp [mergeFunction, mergeArguments, Function.toLocals,
    Function.numParams, ValueType.zero]
  iapply wp_mergeBody_from
    (⟨[.i32 source, .i32 temporary, .i32 (UInt32.ofNat left),
        .i32 (UInt32.ofNat mid), .i32 (UInt32.ofNat right)],
      [.i32 0, .i32 0, .i32 0], []⟩ : Locals)
    source temporary input scratch left mid right rfl
  isplitl [Hpre]
  · iexact Hpre
  iintro %output %scratch' %hmergeRange %hscratchLength
    Hsource Htemporary
  ihave HruntimeLater2 : ▷ runtimeModuleOwn ⟨0⟩ runtimeModule $$ [Hruntime]
  · inext
    iexact Hruntime
  iapply Wasm.SmallStep.wp_returnFromCallExplicit' $$ HruntimeLater2
  inext
  iintro Hruntime
  simp only [mergeLocals, List.take_zero, List.nil_append]
  iapply Hcont $$ Hruntime
  unfold mergePost
  iexists output, scratch'
  isplitr
  · ipureintro
    exact hmergeRange
  isplitr
  · ipureintro
    exact hscratchLength
  iframe

theorem mergePost_elim
    [WasmHeapGS α]
    (source temporary : UInt32) (input : List UInt32)
    (left mid right : Nat) :
    mergePost source temporary input left mid right ⊢
      (iprop% ∃ output scratch : List UInt32,
        ⌜MergeRange input output left mid right⌝ ∗
        ⌜scratch.length = input.length⌝ ∗
        arrayAt 0 source output ∗ arrayAt 0 temporary scratch) := by
  unfold mergePost
  iintro Hpost
  iexact Hpost

theorem mergeSortPre_elim
    [WasmHeapGS α]
    (source temporary : UInt32)
    (input scratch : List UInt32) :
    mergeSortPre source temporary input scratch ⊢
      (iprop% arrayAt 0 source input ∗ arrayAt 0 temporary scratch ∗
        ⌜scratch.length = input.length⌝ ∗
        ⌜ValidLayout source temporary input.length⌝) := by
  unfold mergeSortPre
  iintro Hpre
  iexact Hpre

set_option maxHeartbeats 3000000 in
theorem wp_mergeSortPrepareRight
    [WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (source temporary : UInt32)
    (count width left mid oldRight : Nat)
    (_htwoWidth : width * 2 < UInt32.size)
    (hrightCandidate : left + width * 2 < UInt32.size)
    (hcountSize : count < UInt32.size)
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {stack : List Value} :
    ▷ WP (.running
      ⟨(⟨[.i32 source, .i32 temporary, .i32 (UInt32.ofNat count)],
          [.i32 (UInt32.ofNat width), .i32 (UInt32.ofNat left),
            .i32 (UInt32.ofNat mid),
            .i32 (UInt32.ofNat (min (left + width * 2) count))],
          stack⟩ : Locals),
        code, arity, remainder, controls, calls⟩ : Expr Unit)
      @ s; E {{ Φ }} ⊢
  WP (.running
      ⟨sortLocals source temporary count width left mid oldRight stack,
        [.localGet 4, .localGet 3, .const 2, .mul, .add, .localSet 6,
         .localGet 6, .localGet 2, .ltU,
         .iff 0 0 [] [.localGet 2, .localSet 6]] ++ code,
        arity, remainder, controls, calls⟩ : Expr Unit)
      @ s; E {{ Φ }} := by
  iintro Hcont
  simp only [List.cons_append, List.nil_append]
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_const
  inext
  iapply Wasm.SmallStep.wp_mul
  inext
  have hmul :
      (2 : UInt32) * UInt32.ofNat width =
        UInt32.ofNat (width * 2) := by
    rw [UInt32.mul_comm]
    exact u32_ofNat_mul (a := width) (b := 2) _htwoWidth
  rw [hmul]
  iapply Wasm.SmallStep.wp_add
  inext
  have hrightValue :
      UInt32.ofNat (width * 2) + UInt32.ofNat left =
        UInt32.ofNat (left + width * 2) := by
    rw [UInt32.add_comm, u32_ofNat_add hrightCandidate]
  rw [hrightValue]
  iapply Wasm.SmallStep.wp_localSet rfl
  inext
  simp [sortLocals, List.set]
  have hmul' :
      UInt32.ofNat width * 2 = UInt32.ofNat (width * 2) := by
    exact u32_ofNat_mul (a := width) (b := 2) _htwoWidth
  rw [hmul', u32_ofNat_add hrightCandidate]
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_ltU rfl
  inext
  have hcandidateCmp :
      (UInt32.ofNat (left + width * 2) < UInt32.ofNat count) ↔
        left + width * 2 < count := by
    change (UInt32.ofNat (left + width * 2)).toNat <
        (UInt32.ofNat count).toNat ↔ left + width * 2 < count
    rw [UInt32.toNat_ofNat_of_lt' hrightCandidate,
      UInt32.toNat_ofNat_of_lt' hcountSize]
  by_cases hright : left + width * 2 < count
  · simp only [hcandidateCmp, if_pos hright]
    iapply Wasm.SmallStep.wp_iff rfl
    inext
    simp only [if_pos (by decide : (1 : UInt32) ≠ 0)]
    iapply Wasm.SmallStep.wp_exitControl rfl
    inext
    simp only [List.take_zero, List.nil_append,
      Nat.min_eq_left (Nat.le_of_lt hright)]
    simp only [List.drop_zero]
    iexact Hcont
  · simp only [hcandidateCmp, if_neg hright]
    iapply Wasm.SmallStep.wp_iff rfl
    inext
    simp only [if_neg (by decide : ¬(0 : UInt32) ≠ 0)]
    iapply Wasm.SmallStep.wp_localGet rfl
    inext
    iapply Wasm.SmallStep.wp_localSet rfl
    inext
    simp only [
      Nat.min_eq_right (by omega : count ≤ left + width * 2)]
    iapply Wasm.SmallStep.wp_exitControl rfl
    inext
    simp only [List.take_zero, List.nil_append]
    simp [List.set, List.drop_zero]
    iexact Hcont

theorem wp_mergeSortPrepareRight_from
    [WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (actualLocals : Locals) (stack : List Value)
    (source temporary : UInt32)
    (count width left mid oldRight : Nat)
    (htwoWidth : width * 2 < UInt32.size)
    (hrightCandidate : left + width * 2 < UInt32.size)
    (hcountSize : count < UInt32.size)
    (hlocals :
      actualLocals =
        sortLocals source temporary count width left mid oldRight stack)
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    ▷ WP (.running
      ⟨(⟨[.i32 source, .i32 temporary, .i32 (UInt32.ofNat count)],
          [.i32 (UInt32.ofNat width), .i32 (UInt32.ofNat left),
            .i32 (UInt32.ofNat mid),
            .i32 (UInt32.ofNat (min (left + width * 2) count))],
          stack⟩ : Locals),
        code, arity, remainder, controls, calls⟩ : Expr Unit)
      @ s; E {{ Φ }} ⊢
    WP (.running
      ⟨actualLocals,
        .localGet 4 :: .localGet 3 :: .const 2 :: .mul :: .add ::
          .localSet 6 :: .localGet 6 :: .localGet 2 :: .ltU ::
          .iff 0 0 [] [.localGet 2, .localSet 6] :: code,
        arity, remainder, controls, calls⟩ : Expr Unit)
      @ s; E {{ Φ }} := by
  subst actualLocals
  simpa only [List.cons_append, List.nil_append] using
    (wp_mergeSortPrepareRight source temporary count width left
      mid oldRight htwoWidth hrightCandidate hcountSize :
      ▷ WP (.running
        ⟨(⟨[.i32 source, .i32 temporary, .i32 (UInt32.ofNat count)],
            [.i32 (UInt32.ofNat width), .i32 (UInt32.ofNat left),
              .i32 (UInt32.ofNat mid),
              .i32 (UInt32.ofNat (min (left + width * 2) count))],
            stack⟩ : Locals),
          code, arity, remainder, controls, calls⟩ : Expr Unit)
        @ s; E {{ Φ }} ⊢
      WP (.running
        ⟨sortLocals source temporary count width left mid oldRight stack,
          [.localGet 4, .localGet 3, .const 2, .mul, .add, .localSet 6,
           .localGet 6, .localGet 2, .ltU,
           .iff 0 0 [] [.localGet 2, .localSet 6]] ++ code,
          arity, remainder, controls, calls⟩ : Expr Unit)
        @ s; E {{ Φ }})

set_option maxHeartbeats 5000000 in
theorem wp_mergeSortPrepare
    [WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (source temporary : UInt32)
    (count width left oldMid oldRight : Nat)
    (hleftWidth : left + width < UInt32.size)
    (htwoWidth : width * 2 < UInt32.size)
    (hrightCandidate : left + width * 2 < UInt32.size)
    (hcountSize : count < UInt32.size)
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {stack : List Value} :
    ▷ WP (.running
      ⟨(⟨[.i32 source, .i32 temporary, .i32 (UInt32.ofNat count)],
          [.i32 (UInt32.ofNat width), .i32 (UInt32.ofNat left),
            .i32 (UInt32.ofNat (min (left + width) count)),
            .i32 (UInt32.ofNat (min (left + width * 2) count))],
          stack⟩ : Locals),
        code, arity, remainder, controls, calls⟩ : Expr Unit)
      @ s; E {{ Φ }} ⊢
    WP (.running
      ⟨sortLocals source temporary count width left oldMid oldRight stack,
        mergeSortPrepare ++ code,
        arity, remainder, controls, calls⟩ : Expr Unit)
      @ s; E {{ Φ }} := by
  iintro Hcont
  simp only [mergeSortPrepare, List.cons_append, List.nil_append]
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_add
  inext
  have hleftValue :
      UInt32.ofNat width + UInt32.ofNat left =
        UInt32.ofNat (left + width) := by
    rw [UInt32.add_comm, u32_ofNat_add hleftWidth]
  rw [hleftValue]
  iapply Wasm.SmallStep.wp_localSet rfl
  inext
  simp [sortLocals, List.set]
  rw [u32_ofNat_add hleftWidth]
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_ltU rfl
  inext
  have hcandidateCmp :
      (UInt32.ofNat (left + width) < UInt32.ofNat count) ↔
        left + width < count := by
    change (UInt32.ofNat (left + width)).toNat <
        (UInt32.ofNat count).toNat ↔ left + width < count
    rw [UInt32.toNat_ofNat_of_lt' hleftWidth,
      UInt32.toNat_ofNat_of_lt' hcountSize]
  by_cases hmid : left + width < count
  · simp only [hcandidateCmp, if_pos hmid]
    iapply Wasm.SmallStep.wp_iff rfl
    inext
    simp only [if_pos (by decide : (1 : UInt32) ≠ 0)]
    iapply Wasm.SmallStep.wp_exitControl rfl
    inext
    simp only [List.take_zero, List.nil_append,
      Nat.min_eq_left (Nat.le_of_lt hmid)]
    simp only [List.drop_zero]
    iapply wp_mergeSortPrepareRight_from
      (⟨[.i32 source, .i32 temporary, .i32 (UInt32.ofNat count)],
        [.i32 (UInt32.ofNat width), .i32 (UInt32.ofNat left),
          .i32 (UInt32.ofNat (left + width)),
          .i32 (UInt32.ofNat oldRight)], stack⟩ : Locals)
      stack source temporary
      count width left (left + width) oldRight
      htwoWidth hrightCandidate hcountSize rfl
    iexact Hcont
  · simp only [hcandidateCmp, if_neg hmid]
    iapply Wasm.SmallStep.wp_iff rfl
    inext
    simp only [if_neg (by decide : ¬(0 : UInt32) ≠ 0)]
    iapply Wasm.SmallStep.wp_localGet rfl
    inext
    iapply Wasm.SmallStep.wp_localSet rfl
    inext
    simp only [Nat.min_eq_right (by omega : count ≤ left + width)]
    iapply Wasm.SmallStep.wp_exitControl rfl
    inext
    simp only [List.take_zero, List.nil_append]
    simp [List.set]
    iapply wp_mergeSortPrepareRight_from
      (⟨[.i32 source, .i32 temporary, .i32 (UInt32.ofNat count)],
        [.i32 (UInt32.ofNat width), .i32 (UInt32.ofNat left),
          .i32 (UInt32.ofNat count),
          .i32 (UInt32.ofNat oldRight)], stack⟩ : Locals)
      stack source temporary
      count width left count oldRight
      htwoWidth hrightCandidate hcountSize rfl
    iexact Hcont

set_option maxHeartbeats 4000000 in
theorem wp_mergeSortCallAdvance
    [WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (runtimeModule : Module) (mergeIndex : Nat)
    (himports : ¬mergeIndex < runtimeModule.imports.length)
    (hfunction :
      runtimeModule.funcs[mergeIndex - runtimeModule.imports.length]? =
        some mergeFunction)
    (source temporary : UInt32) (input scratch : List UInt32)
    (count width left mid right : Nat)
    (hrightCandidate : left + width * 2 < UInt32.size)
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {stack : List Value} :
    runtimeModuleOwn ⟨0⟩ runtimeModule ∗
      mergePre source temporary input scratch left mid right ∗
      (runtimeModuleOwn ⟨0⟩ runtimeModule -∗
        mergePost source temporary input left mid right -∗
        WP (.running
          ⟨sortLocals source temporary count width
              (left + width * 2) mid right stack,
            code, arity, remainder, controls, calls⟩ : Expr Unit)
          @ s; E {{ Φ }}) ⊢
    WP (.running
      ⟨sortLocals source temporary count width left mid right stack,
        mergeSortCallAdvance mergeIndex ++ code,
        arity, remainder, controls, calls⟩ : Expr Unit)
      @ s; E {{ Φ }} := by
  iintro ⟨Hruntime, Hpre, Hcont⟩
  simp only [mergeSortCallAdvance, List.cons_append, List.nil_append]
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  simp only [sortLocals]
  have HmergeCall := wp_merge runtimeModule mergeIndex himports hfunction
    source temporary input scratch left mid right
    (s := s) (E := E) (Φ := Φ)
    (callerLocals :=
      (⟨[.i32 source, .i32 temporary, .i32 (UInt32.ofNat count)],
        [.i32 (UInt32.ofNat width), .i32 (UInt32.ofNat left),
          .i32 (UInt32.ofNat mid), .i32 (UInt32.ofNat right)],
        stack⟩ : Locals))
    (stack := stack)
    (code :=
      .localGet 4 :: .localGet 3 :: .const 2 :: .mul :: .add ::
        .localSet 4 :: code)
    (arity := arity) (remainder := remainder)
    (controls := controls) (calls := calls)
  simp only [mergeArguments, List.cons_append, List.nil_append]
    at HmergeCall
  iapply HmergeCall
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hpre]
  · iexact Hpre
  iintro Hruntime Hpost
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_const
  inext
  iapply Wasm.SmallStep.wp_mul
  inext
  have hmul :
      (2 : UInt32) * UInt32.ofNat width =
        UInt32.ofNat (width * 2) := by
    rw [UInt32.mul_comm]
    exact u32_ofNat_mul (a := width) (b := 2) (by omega)
  rw [hmul]
  iapply Wasm.SmallStep.wp_add
  inext
  have hadd :
      UInt32.ofNat (width * 2) + UInt32.ofNat left =
        UInt32.ofNat (left + width * 2) := by
    rw [UInt32.add_comm, u32_ofNat_add hrightCandidate]
  rw [hadd]
  iapply Wasm.SmallStep.wp_localSet rfl
  inext
  simp [List.set]
  iapply Hcont $$ Hruntime Hpost

set_option maxHeartbeats 8000000 in
theorem wp_mergeSortInnerLoop
    [WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (runtimeModule : Module) (mergeIndex : Nat)
    (himports : ¬mergeIndex < runtimeModule.imports.length)
    (hfunction :
      runtimeModule.funcs[mergeIndex - runtimeModule.imports.length]? =
        some mergeFunction)
    (source temporary : UInt32)
    (original current scratch : List UInt32)
    (count width pass mid right : Nat)
    (hinv : MergePassInvariant original current width pass)
    (hcurrent : current.length = count)
    (hscratch : scratch.length = count)
    (hwidthCount : width < count)
    (hleftSize : pass * (2 * width) < UInt32.size)
    (hlayout : ValidLayout source temporary count)
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {stack : List Value} :
    runtimeModuleOwn ⟨0⟩ runtimeModule ∗
      arrayAt 0 source current ∗ arrayAt 0 temporary scratch ∗
      (∀ (output scratch' : List UInt32) (pass' mid' right' : Nat),
        ⌜MergePassInvariant original output width pass'⌝ -∗
        ⌜output.length = count⌝ -∗
        ⌜scratch'.length = count⌝ -∗
        ⌜count ≤ pass' * (2 * width)⌝ -∗
        runtimeModuleOwn ⟨0⟩ runtimeModule -∗
        arrayAt 0 source output -∗ arrayAt 0 temporary scratch' -∗
        WP (.running
          ⟨sortLocals source temporary count width
              (pass' * (2 * width)) mid' right' stack,
            code, arity, remainder, controls, calls⟩ : Expr Unit)
          @ s; E {{ Φ }}) ⊢
    WP (.running
      ⟨sortLocals source temporary count width
          (pass * (2 * width)) mid right stack,
        whileDo mergeSortInnerCondition
          (mergeSortInnerStep mergeIndex) ++ code,
        arity, remainder, controls, calls⟩ : Expr Unit)
      @ s; E {{ Φ }} := by
  let Finish : IProp (WasmHeapGF Unit) := iprop%
    ∀ (output scratch' : List UInt32) (pass' mid' right' : Nat),
      ⌜MergePassInvariant original output width pass'⌝ -∗
      ⌜output.length = count⌝ -∗
      ⌜scratch'.length = count⌝ -∗
      ⌜count ≤ pass' * (2 * width)⌝ -∗
      runtimeModuleOwn ⟨0⟩ runtimeModule -∗
      arrayAt 0 source output -∗ arrayAt 0 temporary scratch' -∗
      WP (.running
        ⟨sortLocals source temporary count width
            (pass' * (2 * width)) mid' right' stack,
          code, arity, remainder, controls, calls⟩ : Expr Unit)
        @ s; E {{ Φ }}
  let Inv : SortInnerState → IProp (WasmHeapGF Unit) := fun state => iprop%
    ⌜MergePassInvariant original state.current width state.pass⌝ ∗
    ⌜state.current.length = count⌝ ∗
    ⌜state.scratch.length = count⌝ ∗
    ⌜state.pass * (2 * width) < UInt32.size⌝ ∗
    runtimeModuleOwn ⟨0⟩ runtimeModule ∗
    arrayAt 0 source state.current ∗ arrayAt 0 temporary state.scratch ∗ Finish
  let blockFrame : ControlFrame :=
    { kind := .block
      paramArity := 0
      resultArity := 0
      body := [.loop 0 0
        (lessLocal 4 2 ++ .eqz :: .br_if 1 ::
          (mergeSortPrepare ++
            (mergeSortCallAdvance mergeIndex ++ [.br 0])))]
      continuation := code
      belowStack := List.drop 0 stack }
  let loopFrame : ControlFrame :=
    { kind := .loop
      paramArity := 0
      resultArity := 0
      body := lessLocal 4 2 ++ .eqz :: .br_if 1 ::
        (mergeSortPrepare ++
          (mergeSortCallAdvance mergeIndex ++ [.br 0]))
      continuation := []
      belowStack := stack }
  iintro ⟨Hruntime, Hsource, Htemporary, Hfinish⟩
  simp only [whileDo, List.cons_append, List.nil_append]
  iapply Wasm.SmallStep.wp_block
  inext
  iapply wp_loop_löb_family_from
    (ι := SortInnerState)
    (locals := fun state =>
      sortLocals source temporary count width
        (state.pass * (2 * width)) state.mid state.right stack)
    (I := Inv)
    (initial := ⟨current, scratch, pass, mid, right⟩)
    (initialLocals :=
      sortLocals source temporary count width
        (pass * (2 * width)) mid right stack)
    (body := whileLoopCode mergeSortInnerCondition
      (mergeSortInnerStep mergeIndex))
    (code := []) (belowStack := stack) rfl rfl
  · intro state
    simp only [Inv, Wasm.SmallStep.loopBodyExpr]
    iintro Hrec Hinv
    icases Hinv with
      ⟨%hpass, %hvaluesLength, %hscratchLength, %hleftBound,
        Hruntime, Hsource, Htemporary, Hfinish⟩
    let left := state.pass * (2 * width)
    have hcountSize : count < UInt32.size := hlayout.length_lt
    have hleftSize' : left < UInt32.size := by
      simpa only [left] using hleftBound
    have hleftCmp :
        (UInt32.ofNat left < UInt32.ofNat count) ↔ left < count := by
      change (UInt32.ofNat left).toNat <
          (UInt32.ofNat count).toNat ↔ left < count
      rw [UInt32.toNat_ofNat_of_lt' hleftSize',
        UInt32.toNat_ofNat_of_lt' hcountSize]
    simp only [whileLoopCode, mergeSortInnerCondition,
      List.append_assoc]
    iapply wp_lessLocal rfl rfl
    inext
    simp only [sortLocals, List.cons_append, List.nil_append]
    iapply Wasm.SmallStep.wp_eqz rfl
    inext
    by_cases hleftCount : left < count
    · have hcmp :
          UInt32.ofNat (state.pass * (2 * width)) <
            UInt32.ofNat count := by
        simpa only [left] using hleftCmp.mpr hleftCount
      simp only [if_pos hcmp,
        if_neg (by decide : (1 : UInt32) ≠ 0)]
      iapply Wasm.SmallStep.wp_brIfZero
      inext
      have hfourCount := hlayout.source_fits
      have hleftWidth : left + width < UInt32.size := by omega
      have htwoWidth : width * 2 < UInt32.size := by omega
      have hrightCandidate : left + width * 2 < UInt32.size := by
        omega
      let newMid := min (left + width) count
      let newRight := min (left + width * 2) count
      simp only [mergeSortInnerStep, List.append_assoc]
      have Hprepare := wp_mergeSortPrepare source temporary count width left
        state.mid state.right hleftWidth htwoWidth hrightCandidate
        hcountSize
        (s := s) (E := E) (Φ := Φ)
        (code := mergeSortCallAdvance mergeIndex ++ [.br 0])
        (arity := arity) (remainder := remainder)
        (controls := loopFrame :: blockFrame :: controls)
        (calls := calls)
        (stack := stack)
      simp only [sortLocals, left, loopFrame, blockFrame] at Hprepare
      iapply Hprepare
      inext
      have hbounds :
          left ≤ newMid ∧ newMid ≤ newRight ∧ newRight ≤ count := by
        dsimp only [newMid, newRight]
        omega
      have Hadvance := wp_mergeSortCallAdvance
        runtimeModule mergeIndex himports hfunction source temporary
        state.current state.scratch count width left newMid newRight
        hrightCandidate
        (s := s) (E := E) (Φ := Φ)
        (code := [.br 0]) (arity := arity) (remainder := remainder)
        (controls := loopFrame :: blockFrame :: controls) (calls := calls)
        (stack := stack)
      simp only [sortLocals, left, newMid, newRight,
        loopFrame, blockFrame] at Hadvance
      iapply Hadvance
      isplitl [Hruntime]
      · iexact Hruntime
      isplitl [Hsource Htemporary]
      · unfold mergePre
        iframe
        isplitr
        · ipureintro
          exact hscratchLength.trans hvaluesLength.symm
        isplitr
        · ipureintro
          simpa only [hvaluesLength] using hlayout
        · ipureintro
          rw [hvaluesLength]
          exact hbounds
      iintro Hruntime Hpost
      ihave Hpost' := mergePost_elim source temporary state.current
        left newMid newRight $$ Hpost
      icases Hpost' with
        ⟨%output, %nextScratch, %hmergeRange,
          %hnextScratchLength, Hsource, Htemporary⟩
      iapply Wasm.SmallStep.wp_br rfl
      inext
      simp only [List.take_zero, List.nil_append]
      have hnextPass :
          left + width * 2 = (state.pass + 1) * (2 * width) := by
        simp only [left]
        rw [Nat.add_mul]
        simp [Nat.mul_comm]
      have hpassNext :
          MergePassInvariant original output width (state.pass + 1) := by
        apply hpass.step
        · simpa only [left, hvaluesLength] using hleftCount
        · simpa only [left, newMid, newRight, Nat.mul_comm,
            hvaluesLength, Nat.add_comm, Nat.add_left_comm,
            Nat.add_assoc] using hmergeRange
      rw [hnextPass]
      ispecialize Hrec $$
        %(⟨output, nextScratch, state.pass + 1,
          newMid, newRight⟩ : SortInnerState)
      simp only [newMid, newRight, left, hnextPass]
      iapply Hrec
      isplitr
      · ipureintro
        exact hpassNext
      isplitr
      · ipureintro
        exact hmergeRange.length_eq.trans hvaluesLength
      isplitr
      · ipureintro
        exact hnextScratchLength.trans hvaluesLength
      isplitr
      · ipureintro
        rw [← hnextPass]
        exact hrightCandidate
      iframe
    · have hcmp :
          ¬UInt32.ofNat (state.pass * (2 * width)) <
            UInt32.ofNat count := by
        simpa only [left] using (mt hleftCmp.mp hleftCount)
      simp only [if_neg hcmp]
      iapply Wasm.SmallStep.wp_brIf (by decide) rfl
      inext
      simp only [List.take_zero, List.nil_append,
        List.drop_zero]
      isimp only [Finish, sortLocals] at Hfinish
      iapply Hfinish $$ %state.current %state.scratch %state.pass
        %state.mid %state.right %hpass %hvaluesLength
        %hscratchLength %(by
          simpa only [left] using Nat.le_of_not_gt hleftCount)
        Hruntime Hsource Htemporary
  · simp only [Inv]
    isplitr
    · ipureintro
      exact hinv
    isplitr
    · ipureintro
      exact hcurrent
    isplitr
    · ipureintro
      exact hscratch
    isplitr
    · ipureintro
      exact hleftSize
    iframe

set_option maxHeartbeats 10000000 in
theorem wp_mergeSortOuterLoop
    [WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (runtimeModule : Module) (mergeIndex : Nat)
    (himports : ¬mergeIndex < runtimeModule.imports.length)
    (hfunction :
      runtimeModule.funcs[mergeIndex - runtimeModule.imports.length]? =
        some mergeFunction)
    (source temporary : UInt32)
    (input current scratch : List UInt32)
    (count width left mid right : Nat)
    (hruns : SortedRuns current width)
    (hperm : List.Perm input current)
    (hcurrent : current.length = count)
    (hscratch : scratch.length = count)
    (hwidthPositive : 0 < width)
    (hwidthSize : width < UInt32.size)
    (hlayout : ValidLayout source temporary count)
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {stack : List Value} :
    runtimeModuleOwn ⟨0⟩ runtimeModule ∗
      arrayAt 0 source current ∗ arrayAt 0 temporary scratch ∗
      (∀ (output scratch' : List UInt32)
          (width' left' mid' right' : Nat),
        ⌜SortedRuns output width'⌝ -∗
        ⌜List.Perm input output⌝ -∗
        ⌜output.length = count⌝ -∗
        ⌜scratch'.length = count⌝ -∗
        ⌜count ≤ width'⌝ -∗
        runtimeModuleOwn ⟨0⟩ runtimeModule -∗
        arrayAt 0 source output -∗ arrayAt 0 temporary scratch' -∗
        WP (.running
          ⟨sortLocals source temporary count width'
              left' mid' right' stack,
            code, arity, remainder, controls, calls⟩ : Expr Unit)
          @ s; E {{ Φ }}) ⊢
    WP (.running
      ⟨sortLocals source temporary count width left mid right stack,
        whileDo mergeSortOuterCondition
          (mergeSortOuterStep mergeIndex) ++ code,
        arity, remainder, controls, calls⟩ : Expr Unit)
      @ s; E {{ Φ }} := by
  let Finish : IProp (WasmHeapGF Unit) := iprop%
    ∀ (output scratch' : List UInt32)
        (width' left' mid' right' : Nat),
      ⌜SortedRuns output width'⌝ -∗
      ⌜List.Perm input output⌝ -∗
      ⌜output.length = count⌝ -∗
      ⌜scratch'.length = count⌝ -∗
      ⌜count ≤ width'⌝ -∗
      runtimeModuleOwn ⟨0⟩ runtimeModule -∗
      arrayAt 0 source output -∗ arrayAt 0 temporary scratch' -∗
      WP (.running
        ⟨sortLocals source temporary count width'
            left' mid' right' stack,
          code, arity, remainder, controls, calls⟩ : Expr Unit)
        @ s; E {{ Φ }}
  let Inv : SortOuterState → IProp (WasmHeapGF Unit) := fun state => iprop%
    ⌜SortedRuns state.current state.width⌝ ∗
    ⌜List.Perm input state.current⌝ ∗
    ⌜state.current.length = count⌝ ∗
    ⌜state.scratch.length = count⌝ ∗
    ⌜0 < state.width⌝ ∗
    ⌜state.width < UInt32.size⌝ ∗
    runtimeModuleOwn ⟨0⟩ runtimeModule ∗
    arrayAt 0 source state.current ∗ arrayAt 0 temporary state.scratch ∗ Finish
  let blockFrame : ControlFrame :=
    { kind := .block
      paramArity := 0
      resultArity := 0
      body := [.loop 0 0
        (lessLocal 3 2 ++ .eqz :: .br_if 1 :: .const 0 ::
          .localSet 4 ::
            (whileDo mergeSortInnerCondition
              (mergeSortInnerStep mergeIndex) ++
              [.localGet 3, .const 2, .mul, .localSet 3, .br 0]))]
      continuation := code
      belowStack := stack }
  let loopFrame : ControlFrame :=
    { kind := .loop
      paramArity := 0
      resultArity := 0
      body := lessLocal 3 2 ++ .eqz :: .br_if 1 :: .const 0 ::
        .localSet 4 ::
          (whileDo mergeSortInnerCondition
            (mergeSortInnerStep mergeIndex) ++
            [.localGet 3, .const 2, .mul, .localSet 3, .br 0])
      continuation := []
      belowStack := stack }
  iintro ⟨Hruntime, Hsource, Htemporary, Hfinish⟩
  simp only [whileDo, List.cons_append, List.nil_append]
  iapply Wasm.SmallStep.wp_block
  inext
  iapply wp_loop_löb_family_from
    (ι := SortOuterState)
    (locals := fun state =>
      sortLocals source temporary count state.width
        state.left state.mid state.right stack)
    (I := Inv)
    (initial := ⟨current, scratch, width, left, mid, right⟩)
    (initialLocals :=
      sortLocals source temporary count width left mid right stack)
    (body := whileLoopCode mergeSortOuterCondition
      (mergeSortOuterStep mergeIndex))
    (code := []) (belowStack := stack) rfl rfl
  · intro state
    simp only [Inv, Wasm.SmallStep.loopBodyExpr]
    iintro Hrec Hinv
    icases Hinv with
      ⟨%hruns', %hperm', %hvaluesLength, %hscratchLength,
        %hwidthPositive', %hwidthBound, Hruntime,
        Hsource, Htemporary, Hfinish⟩
    have hcountSize : count < UInt32.size := hlayout.length_lt
    have hwidthCmp :
        (UInt32.ofNat state.width < UInt32.ofNat count) ↔
          state.width < count := by
      change (UInt32.ofNat state.width).toNat <
          (UInt32.ofNat count).toNat ↔ state.width < count
      rw [UInt32.toNat_ofNat_of_lt' hwidthBound,
        UInt32.toNat_ofNat_of_lt' hcountSize]
    simp only [whileLoopCode, mergeSortOuterCondition,
      List.append_assoc]
    iapply wp_lessLocal rfl rfl
    inext
    simp only [sortLocals, List.cons_append, List.nil_append]
    iapply Wasm.SmallStep.wp_eqz rfl
    inext
    by_cases hwidthCount' : state.width < count
    · have hcmp :
          UInt32.ofNat state.width < UInt32.ofNat count :=
        hwidthCmp.mpr hwidthCount'
      simp only [if_pos hcmp,
        if_neg (by decide : (1 : UInt32) ≠ 0)]
      iapply Wasm.SmallStep.wp_brIfZero
      inext
      simp only [mergeSortOuterStep, List.cons_append,
        List.nil_append, List.append_assoc]
      iapply Wasm.SmallStep.wp_const
      inext
      iapply Wasm.SmallStep.wp_localSet rfl
      inext
      simp [List.set]
      have hpassStart :
          MergePassInvariant state.current state.current
            state.width 0 :=
        mergePassInvariant_start hwidthPositive'
          (List.Perm.refl _) hruns'
      have Hinner := wp_mergeSortInnerLoop
        runtimeModule mergeIndex himports hfunction
        source temporary state.current state.current state.scratch
        count state.width 0 state.mid state.right hpassStart
        hvaluesLength hscratchLength hwidthCount'
        (by simp [UInt32.size]) hlayout
        (s := s) (E := E) (Φ := Φ)
        (code :=
          [.localGet 3, .const 2, .mul, .localSet 3, .br 0])
        (arity := arity) (remainder := remainder)
        (controls := loopFrame :: blockFrame :: controls)
        (calls := calls) (stack := stack)
      simp only [sortLocals, Nat.zero_mul, loopFrame, blockFrame]
        at Hinner
      iapply Hinner
      isplitl [Hruntime]
      · iexact Hruntime
      isplitl [Hsource]
      · iexact Hsource
      isplitl [Htemporary]
      · iexact Htemporary
      iintro %output %nextScratch %pass' %nextMid %nextRight
        %hpass %houtputLength %hnextScratchLength %hpassFinished
        Hruntime Hsource Htemporary
      have hnextRuns : SortedRuns output (2 * state.width) :=
        hpass.finished (by
          rw [houtputLength]
          exact hpassFinished)
      have hnextPerm : List.Perm input output :=
        hperm'.trans hpass.2.2.1
      have hdoubleSize : state.width * 2 < UInt32.size := by
        have hfourCount := hlayout.source_fits
        omega
      iapply Wasm.SmallStep.wp_localGet rfl
      inext
      iapply Wasm.SmallStep.wp_const
      inext
      iapply Wasm.SmallStep.wp_mul
      inext
      have hmul :
          (2 : UInt32) * UInt32.ofNat state.width =
            UInt32.ofNat (state.width * 2) := by
        rw [UInt32.mul_comm]
        exact u32_ofNat_mul hdoubleSize
      rw [hmul]
      iapply Wasm.SmallStep.wp_localSet rfl
      inext
      simp
      iapply Wasm.SmallStep.wp_br rfl
      inext
      simp only [List.take_zero, List.nil_append]
      ispecialize Hrec $$
        %(⟨output, nextScratch, state.width * 2,
          pass' * (2 * state.width), nextMid, nextRight⟩ :
          SortOuterState)
      simp only [UInt32.ofNat_mul]
      iapply Hrec
      isplitr
      · ipureintro
        simpa [Nat.mul_comm] using hnextRuns
      isplitr
      · ipureintro
        exact hnextPerm
      isplitr
      · ipureintro
        exact houtputLength
      isplitr
      · ipureintro
        exact hnextScratchLength
      isplitr
      · ipureintro
        omega
      isplitr
      · ipureintro
        exact hdoubleSize
      iframe
    · have hcmp :
          ¬UInt32.ofNat state.width < UInt32.ofNat count :=
        mt hwidthCmp.mp hwidthCount'
      simp only [if_neg hcmp]
      iapply Wasm.SmallStep.wp_brIf (by decide) rfl
      inext
      simp only [List.take_zero, List.nil_append,
        List.drop_zero]
      isimp only [Finish, sortLocals] at Hfinish
      iapply Hfinish $$ %state.current %state.scratch %state.width
        %state.left %state.mid %state.right %hruns' %hperm'
        %hvaluesLength %hscratchLength
        %(Nat.le_of_not_gt hwidthCount')
        Hruntime Hsource Htemporary
  · simp only [Inv]
    isplitr
    · ipureintro
      exact hruns
    isplitr
    · ipureintro
      exact hperm
    isplitr
    · ipureintro
      exact hcurrent
    isplitr
    · ipureintro
      exact hscratch
    isplitr
    · ipureintro
      exact hwidthPositive
    isplitr
    · ipureintro
      exact hwidthSize
    iframe

set_option maxHeartbeats 6000000 in
theorem wp_mergeSortBody
    [WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (runtimeModule : Module) (mergeIndex : Nat)
    (himports : ¬mergeIndex < runtimeModule.imports.length)
    (hfunction :
      runtimeModule.funcs[mergeIndex - runtimeModule.imports.length]? =
        some mergeFunction)
    (source temporary : UInt32) (input scratch : List UInt32)
    {calls : List CallFrame} :
    runtimeModuleOwn ⟨0⟩ runtimeModule ∗
      mergeSortPre source temporary input scratch ∗
      (∀ (width left mid right : Nat),
        runtimeModuleOwn ⟨0⟩ runtimeModule -∗
        mergeSortPost source temporary input -∗
        WP (.running
          ⟨sortLocals source temporary input.length
              width left mid right [],
            [.ret], 0, [], [], calls⟩ : Expr Unit)
          @ s; E {{ Φ }}) ⊢
    WP (.running
      ⟨sortLocals source temporary input.length
          0 0 0 0 [],
        mergeSortBody mergeIndex, 0, [], [], calls⟩ : Expr Unit)
      @ s; E {{ Φ }} := by
  iintro ⟨Hruntime, Hpre, Hcont⟩
  simp only [mergeSortBody, List.cons_append, List.nil_append]
  iapply Wasm.SmallStep.wp_const
  inext
  iapply Wasm.SmallStep.wp_localSet rfl
  inext
  simp [sortLocals]
  ihave Hpre' := mergeSortPre_elim source temporary input scratch $$ Hpre
  icases Hpre' with
    ⟨Hsource, Htemporary, %hscratchLength, %hlayout⟩
  have Houter := wp_mergeSortOuterLoop runtimeModule mergeIndex
    himports hfunction source temporary input input scratch
    input.length 1 0 0 0
    (sortedRuns_one input) (List.Perm.refl input) rfl
    hscratchLength (by omega) (by decide) hlayout
    (s := s) (E := E) (Φ := Φ)
    (code := [.ret]) (arity := 0) (remainder := [])
    (controls := []) (calls := calls) (stack := [])
  simp only [sortLocals] at Houter
  iapply Houter
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hsource]
  · iexact Hsource
  isplitl [Htemporary]
  · iexact Htemporary
  iintro %output %scratchFinal %width %left %mid %right
    %hruns %hperm %houtputLength %hscratchFinalLength
    %hwidth Hruntime Hsource Htemporary
  have hsorted : Sorted output :=
    sorted_of_sortedRuns_cover hruns (by
      rw [houtputLength]
      exact hwidth)
  iapply Hcont $$ %width %left %mid %right Hruntime
  unfold mergeSortPost
  iexists output, scratchFinal
  isplitr
  · ipureintro
    exact ⟨hsorted, hperm⟩
  isplitr
  · ipureintro
    exact hscratchFinalLength
  iframe

set_option maxHeartbeats 5000000 in
theorem wp_mergeSort
    [WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (runtimeModule : Module) (sortIndex mergeIndex : Nat)
    (hsortImports : ¬sortIndex < runtimeModule.imports.length)
    (hsortFunction :
      runtimeModule.funcs[sortIndex - runtimeModule.imports.length]? =
        some (mergeSortFunction mergeIndex))
    (hmergeImports : ¬mergeIndex < runtimeModule.imports.length)
    (hmergeFunction :
      runtimeModule.funcs[mergeIndex - runtimeModule.imports.length]? =
        some mergeFunction)
    (source temporary : UInt32) (input scratch : List UInt32)
    {callerLocals : Locals}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {stack : List Value} :
    runtimeModuleOwn ⟨0⟩ runtimeModule ∗
      mergeSortPre source temporary input scratch ∗
      (runtimeModuleOwn ⟨0⟩ runtimeModule -∗
        mergeSortPost source temporary input -∗
        WP (.running
          ⟨{ callerLocals with values := stack },
            code, arity, remainder, controls, calls⟩ : Expr Unit)
          @ s; E {{ Φ }}) ⊢
    WP (.running
      ⟨{ callerLocals with
          values :=
            mergeSortArguments source temporary input.length stack },
        .call sortIndex :: code, arity, remainder, controls, calls⟩ :
        Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨Hruntime, Hpre, Hcont⟩
  ihave HruntimeLater : ▷ runtimeModuleOwn ⟨0⟩ runtimeModule $$ [Hruntime]
  · inext
    iexact Hruntime
  iapply Wasm.SmallStep.wp_call runtimeModule sortIndex
    (mergeSortFunction mergeIndex) hsortImports hsortFunction $$
      HruntimeLater
  inext
  iintro Hruntime
  simp [mergeSortFunction, mergeSortArguments, Function.toLocals,
    Function.numParams, ValueType.zero]
  have Hbody := wp_mergeSortBody runtimeModule mergeIndex
    hmergeImports hmergeFunction source temporary input scratch
    (s := s) (E := E) (Φ := Φ)
    (calls :=
      { locals :=
          ⟨callerLocals.params, callerLocals.locals, stack⟩
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls
        returningInstance := ⟨0⟩ } :: calls)
  simp only [sortLocals] at Hbody
  iapply Hbody
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hpre]
  · iexact Hpre
  iintro %width %left %mid %right Hruntime Hpost
  ihave HruntimeLater2 : ▷ runtimeModuleOwn ⟨0⟩ runtimeModule $$ [Hruntime]
  · inext
    iexact Hruntime
  iapply Wasm.SmallStep.wp_returnFromCallExplicit' $$ HruntimeLater2
  inext
  iintro Hruntime
  simp only [List.take_zero, List.nil_append]
  iapply Hcont $$ Hruntime Hpost

end Wasm.Examples.MergeSort
