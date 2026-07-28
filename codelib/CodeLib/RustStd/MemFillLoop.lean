import CodeLib.RustStd.MemArray
import CodeLib.SepLogic.SmallStepLifting

/-!
# A universally-quantified loop-over-memory proof

The canonical fill loop writes `v` to each of the `n` u64 slots of
`[base, base + 8n)`.  Its iris-lean proof owns the entire physical region,
splits the completed prefix from the remaining suffix, and uses Löb induction
over the real small-step control frames.  An arbitrary Iris resource is framed
through every instruction, so the rule composes with neighbouring memory.
-/

namespace Wasm

/-- Fill loop. Params `base : i32`, `n : i32`, `v : i64`; local `i : i32`.
Writes `v` to `mem[base + 8*i]` for `i = 0 … n-1`. Structure mirrors the
`SimpleLoop` example's while-loop idiom. -/
def FillWords : Program := [
  .const 0, .localSet 3,
  .loop 0 0 [
    .block 0 0 [
      .block 0 0 [
        .localGet 3, .localGet 1, .ltU, .br_if 0,
        .br 1
      ],
      .localGet 0, .localGet 3, .const 3, .shl, .add,
      .localGet 2, .store64 0,
      .localGet 3, .const 1, .add, .localSet 3,
      .br 1 ] ]
]

/-! ## Authoritative small-step loop body

This is the stateful core of one `FillWords` iteration.  It connects the
prefix/suffix ownership algebra to the real generated address calculation and
`i64.store`; the guard, increment, and back-edge are composed around this rule
by the family-indexed loop invariant.
-/

open Iris Iris.ProgramLogic Language.Notation
open Wasm.SepLogic

/-- Address calculation and store performed by one fill-loop iteration. -/
def FillWordsStoreIteration : Program := [
  .localGet 0, .localGet 3, .const 3, .shl, .add,
  .localGet 2, .store64 0
]

def FillWordsIncrementBackedge : Program := [
  .localGet 3, .const 1, .add, .localSet 3, .br 1
]

def FillWordsInnerGuard : Program := [
  .localGet 3, .localGet 1, .ltU, .br_if 0, .br 1
]

def FillWordsOuterBody : Program :=
  [.block 0 0 FillWordsInnerGuard] ++
    FillWordsStoreIteration ++ FillWordsIncrementBackedge

def FillWordsLoopBody : Program := [
  .block 0 0 FillWordsOuterBody
]

def fillWordsLoopFrame (continuation : Program) :
    Wasm.SmallStep.ControlFrame :=
  { kind := .loop
    paramArity := 0
    resultArity := 0
    body := FillWordsLoopBody
    continuation
    belowStack := [] }

def fillWordsOuterFrame : Wasm.SmallStep.ControlFrame :=
  { kind := .block
    paramArity := 0
    resultArity := 0
    body := FillWordsOuterBody
    continuation := []
    belowStack := [] }

def fillWordsInnerFrame : Wasm.SmallStep.ControlFrame :=
  { kind := .block
    paramArity := 0
    resultArity := 0
    body := FillWordsInnerGuard
    continuation :=
      FillWordsStoreIteration ++ FillWordsIncrementBackedge
    belowStack := [] }

theorem FillWords_eq_structured :
    FillWords = [.const 0, .localSet 3,
      .loop 0 0 FillWordsLoopBody] := by
  rfl

/-- One real small-step fill iteration extends the authoritatively owned
filled prefix by one word and frames an arbitrary Iris resource `R`. -/
theorem fillWords_storeIteration_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {α : Type} (R : IProp WasmHeapGF)
    (base n i : UInt32) (value old : UInt64)
    (suffix : List UInt64)
    (code : Program) (arity : Nat) (remainder : List Value)
    (controls : List Wasm.SmallStep.ControlFrame)
    (calls : List Wasm.SmallStep.CallFrame)
    (hroom : base.toNat + 8 * (i.toNat + 1) ≤ 4294967296)
    (hcontinue :
      R ∗ array64At base
          (List.replicate (i.toNat + 1) value ++ suffix) ⊢
        WP (Wasm.SmallStep.Expr.running
          ⟨⟨[.i32 base, .i32 n, .i64 value], [.i32 i], []⟩,
            code, arity, remainder, controls, calls⟩ :
          Wasm.SmallStep.Expr α) @ s; E {{ Φ }}) :
    R ∗ array64At base
        (List.replicate i.toNat value ++ old :: suffix) ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 base, .i32 n, .i64 value], [.i32 i], []⟩,
          FillWordsStoreIteration ++ code,
          arity, remainder, controls, calls⟩ :
        Wasm.SmallStep.Expr α) @ s; E {{ Φ }} := by
  let address : UInt32 := base + 8 * UInt32.ofNat i.toNat
  have hi : UInt32.ofNat i.toNat = i := by
    simp [UInt32.ofNat_toNat]
  have haddr :
      (i <<< (3 % 32 : UInt32)) + base = address := by
    rw [MemRegion.shl3_eq_mul8]
    dsimp only [address]
    rw [hi]
    exact UInt32.add_comm _ _
  have haddrNat : address.toNat = base.toNat + 8 * i.toNat := by
    exact Mem.words64_slotAddr_toNat base i.toNat (by omega)
  have hstep (k : Nat) (hk : k < 4294967296)
      (hfit : address.toNat + k < 4294967296) :
      (address + UInt32.ofNat k).toNat = address.toNat + k :=
    UInt32.add_ofNat_toNat_noWrap address k hk hfit
  have h1 : (address + 1).toNat = address.toNat + 1 := by
    simpa using hstep 1 (by decide) (by omega)
  have h2 : (address + 2).toNat = address.toNat + 2 := by
    simpa using hstep 2 (by decide) (by omega)
  have h3 : (address + 3).toNat = address.toNat + 3 := by
    simpa using hstep 3 (by decide) (by omega)
  have h4 : (address + 4).toNat = address.toNat + 4 := by
    simpa using hstep 4 (by decide) (by omega)
  have h5 : (address + 5).toNat = address.toNat + 5 := by
    simpa using hstep 5 (by decide) (by omega)
  have h6 : (address + 6).toNat = address.toNat + 6 := by
    simpa using hstep 6 (by decide) (by omega)
  have h7 : (address + 7).toNat = address.toNat + 7 := by
    simpa using hstep 7 (by decide) (by omega)
  iintro ⟨HR, Harray⟩
  icases array64At_fill_next base i.toNat value old suffix $$ Harray with
    ⟨Hold, Hreassemble⟩
  simp only [FillWordsStoreIteration, List.cons_append, List.nil_append]
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
  rw [haddr]
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  ihave HoldLater : ▷ pointsTo_u64 (address + 0) old $$ [Hold]
  · inext
    simp only [UInt32.add_zero, address]
    iexact Hold
  iapply Wasm.SmallStep.wp_store64
      (address := address) (offset := 0) (value := value) old
      (by simp) (by simpa using h1) (by simpa using h2)
      (by simpa using h3) (by simpa using h4) (by simpa using h5)
      (by simpa using h6) (by simpa using h7) $$ HoldLater
  inext
  iintro Hnew
  ihave Hnew' :
      pointsTo_u64 (base + 8 * UInt32.ofNat i.toNat) value $$ [Hnew]
  · simp only [UInt32.add_zero, address]
    iexact Hnew
  ihave Harray' :
      array64At base
        (List.replicate (i.toNat + 1) value ++ suffix) $$
      [Hreassemble Hnew']
  · iapply Hreassemble
    iexact Hnew'
  iapply hcontinue
  iframe

/-- The generated index increment and `br 1` really target the surrounding
loop frame, with the updated local and no operand-stack leakage. -/
theorem fillWords_incrementBackedge_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {α : Type}
    (base n i : UInt32) (value : UInt64)
    (afterLoop : Program) (arity : Nat) (remainder : List Value)
    (outerControls : List Wasm.SmallStep.ControlFrame)
    (calls : List Wasm.SmallStep.CallFrame) :
    ▷ WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 base, .i32 n, .i64 value], [.i32 (i + 1)], []⟩,
          FillWordsLoopBody, arity, remainder,
          fillWordsLoopFrame afterLoop :: outerControls, calls⟩ :
        Wasm.SmallStep.Expr α) @ s; E {{ Φ }} ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 base, .i32 n, .i64 value], [.i32 i], []⟩,
        FillWordsIncrementBackedge, arity, remainder,
        fillWordsOuterFrame :: fillWordsLoopFrame afterLoop ::
          outerControls,
        calls⟩ : Wasm.SmallStep.Expr α) @ s; E {{ Φ }} := by
  iintro Hcontinue
  simp only [FillWordsIncrementBackedge]
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_const
  inext
  iapply Wasm.SmallStep.wp_add
  inext
  rw [UInt32.add_comm 1 i]
  iapply Wasm.SmallStep.wp_localSet rfl
  inext
  iapply Wasm.SmallStep.wp_br (by rfl)
  inext
  simp only [fillWordsLoopFrame, List.length_cons,
    List.length_nil, Nat.reduceAdd, Nat.reduceSub, List.set, List.take_nil,
    List.nil_append]
  iexact Hcontinue

/-- Compose the authoritative store with the generated increment/back-edge.
The premise is exactly the guarded family hypothesis for iteration `i + 1`. -/
theorem fillWords_bodyTail_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {α : Type} (R : IProp WasmHeapGF)
    (base n i : UInt32) (value old : UInt64)
    (suffix : List UInt64)
    (afterLoop : Program) (arity : Nat) (remainder : List Value)
    (outerControls : List Wasm.SmallStep.ControlFrame)
    (calls : List Wasm.SmallStep.CallFrame)
    (hroom : base.toNat + 8 * (i.toNat + 1) ≤ 4294967296)
    (hback :
      R ∗ array64At base
          (List.replicate (i.toNat + 1) value ++ suffix) ⊢
        ▷ WP (Wasm.SmallStep.Expr.running
          ⟨⟨[.i32 base, .i32 n, .i64 value], [.i32 (i + 1)], []⟩,
            FillWordsLoopBody, arity, remainder,
            fillWordsLoopFrame afterLoop :: outerControls, calls⟩ :
          Wasm.SmallStep.Expr α) @ s; E {{ Φ }}) :
    R ∗ array64At base
        (List.replicate i.toNat value ++ old :: suffix) ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 base, .i32 n, .i64 value], [.i32 i], []⟩,
          FillWordsStoreIteration ++ FillWordsIncrementBackedge,
          arity, remainder,
          fillWordsOuterFrame :: fillWordsLoopFrame afterLoop ::
            outerControls,
          calls⟩ : Wasm.SmallStep.Expr α) @ s; E {{ Φ }} := by
  iapply fillWords_storeIteration_wp R base n i value old suffix
      FillWordsIncrementBackedge arity remainder
      (fillWordsOuterFrame :: fillWordsLoopFrame afterLoop :: outerControls)
      calls hroom
  iintro Hresources
  iapply fillWords_incrementBackedge_wp base n i value afterLoop arity
    remainder outerControls calls
  iapply hback
  iexact Hresources

/-- The two generated blocks implement the loop guard: `i < n` exposes the
stateful body tail, while `i ≥ n` exits first the outer block and then the
loop frame into `afterLoop`. -/
theorem fillWords_guard_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {α : Type} (P : IProp WasmHeapGF)
    (base n i : UInt32) (value : UInt64)
    (afterLoop : Program) (arity : Nat) (remainder : List Value)
    (outerControls : List Wasm.SmallStep.ControlFrame)
    (calls : List Wasm.SmallStep.CallFrame)
    (hbody : i < n →
      P ⊢ WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 base, .i32 n, .i64 value], [.i32 i], []⟩,
          FillWordsStoreIteration ++ FillWordsIncrementBackedge,
          arity, remainder,
          fillWordsOuterFrame :: fillWordsLoopFrame afterLoop ::
            outerControls,
          calls⟩ : Wasm.SmallStep.Expr α) @ s; E {{ Φ }})
    (hexit : ¬ i < n →
      P ⊢ WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 base, .i32 n, .i64 value], [.i32 i], []⟩,
          afterLoop, arity, remainder, outerControls, calls⟩ :
          Wasm.SmallStep.Expr α) @ s; E {{ Φ }}) :
    P ⊢ WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 base, .i32 n, .i64 value], [.i32 i], []⟩,
        FillWordsLoopBody, arity, remainder,
        fillWordsLoopFrame afterLoop :: outerControls, calls⟩ :
      Wasm.SmallStep.Expr α) @ s; E {{ Φ }} := by
  simp only [fillWordsOuterFrame, FillWordsOuterBody,
    FillWordsInnerGuard, List.cons_append, List.nil_append] at hbody
  iintro HP
  simp only [FillWordsLoopBody]
  iapply Wasm.SmallStep.wp_block
  inext
  simp only [FillWordsOuterBody, List.cons_append, List.nil_append]
  iapply Wasm.SmallStep.wp_block
  inext
  simp only [FillWordsInnerGuard]
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  by_cases hlt : i < n
  · iapply Wasm.SmallStep.wp_ltU (result := 1) (by simp [hlt])
    inext
    iapply Wasm.SmallStep.wp_brIf (by decide) (by rfl)
    inext
    simp only [List.drop_zero, List.take_nil, List.nil_append]
    iapply hbody hlt
    iexact HP
  · iapply Wasm.SmallStep.wp_ltU (result := 0) (by simp [hlt])
    inext
    iapply Wasm.SmallStep.wp_brIfZero
    inext
    iapply Wasm.SmallStep.wp_br (by rfl)
    inext
    iapply Wasm.SmallStep.wp_exitControl rfl
    inext
    simp only [fillWordsLoopFrame, List.drop_zero, List.take_nil,
      List.nil_append]
    iapply hexit hlt
    iexact HP

/-- Universal Iris loop invariant.  `suffix` is the not-yet-written part of
the original array, so `i + suffix.length = n`; ownership is exactly the
filled prefix followed by that suffix. -/
theorem fillWords_loopBody_invariant_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {α : Type} (R : IProp WasmHeapGF)
    (base n i : UInt32) (value : UInt64) (suffix : List UInt64)
    (afterLoop : Program) (arity : Nat) (remainder : List Value)
    (outerControls : List Wasm.SmallStep.ControlFrame)
    (calls : List Wasm.SmallStep.CallFrame)
    (htotal : base.toNat + 8 * n.toNat ≤ 4294967296)
    (hinv : i.toNat + suffix.length = n.toNat)
    (hfinish :
      R ∗ array64At base (List.replicate n.toNat value) ⊢
        WP (Wasm.SmallStep.Expr.running
          ⟨⟨[.i32 base, .i32 n, .i64 value], [.i32 n], []⟩,
            afterLoop, arity, remainder, outerControls, calls⟩ :
          Wasm.SmallStep.Expr α) @ s; E {{ Φ }}) :
    R ∗ array64At base
        (List.replicate i.toNat value ++ suffix) ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 base, .i32 n, .i64 value], [.i32 i], []⟩,
          FillWordsLoopBody, arity, remainder,
          fillWordsLoopFrame afterLoop :: outerControls, calls⟩ :
        Wasm.SmallStep.Expr α) @ s; E {{ Φ }} := by
  iloeb as IH generalizing %i %suffix %hinv
  let Kloop : IProp WasmHeapGF := iprop(
    ▷ ∀ (j : UInt32) (tail : List UInt64),
      ⌜j.toNat + tail.length = n.toNat⌝ -∗
      R ∗ array64At base
          (List.replicate j.toNat value ++ tail) -∗
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 base, .i32 n, .i64 value], [.i32 j], []⟩,
          FillWordsLoopBody, arity, remainder,
          fillWordsLoopFrame afterLoop :: outerControls, calls⟩ :
        Wasm.SmallStep.Expr α) @ s; E {{ Φ }})
  ihave IHtyped : □ Kloop $$ [IH]
  · simp only [Kloop]
    iexact IH
  let P : IProp WasmHeapGF :=
    iprop% □ Kloop ∗ R ∗ array64At base
      (List.replicate i.toNat value ++ suffix)
  iintro ⟨HR, Harray⟩
  iapply fillWords_guard_wp P
      base n i value afterLoop arity remainder outerControls calls
  · intro hlt
    simp only [P]
    cases suffix with
    | nil =>
        have hltNat : i.toNat < n.toNat := hlt
        simp only [List.length_nil, Nat.add_zero] at hinv
        omega
    | cons old tail =>
        have hltNat : i.toNat < n.toNat := hlt
        have hnext :
            (i + 1).toNat = i.toNat + 1 := by
          rw [UInt32.toNat_add]
          simp only [UInt32.reduceToNat]
          rw [Nat.mod_eq_of_lt
            (lt_of_le_of_lt (by omega) n.toNat_lt)]
        have hinvNext :
            (i + 1).toNat + tail.length = n.toNat := by
          simp only [List.length_cons] at hinv
          omega
        let Rloop : IProp WasmHeapGF := iprop% □ Kloop ∗ R
        iintro Hcurrent
        icases Hcurrent with ⟨#IHcurrent, HcurrentRest⟩
        icases HcurrentRest with ⟨HRcurrent, HarrayCurrent⟩
        iapply fillWords_bodyTail_wp Rloop base n i value old tail
          afterLoop arity remainder outerControls calls
        · omega
        · iintro Hresources
          ihave Hexpanded :
              (□ Kloop ∗ R) ∗
                array64At base
                  (List.replicate ((i + 1).toNat) value ++ tail) $$
              [Hresources]
          · simp only [Rloop]
            rw [hnext]
            iexact Hresources
          icases Hexpanded with ⟨Hloop, Harray'⟩
          icases Hloop with ⟨#IH', HR'⟩
          ispecialize IH' $$ %(i + 1) %tail %hinvNext
          iapply IH'
          iframe
        · simp only [Rloop]
          isplitl [IHcurrent HRcurrent]
          · isplitl [IHcurrent]
            · iexact IHcurrent
            · iexact HRcurrent
          · iexact HarrayCurrent
  · intro hnlt
    simp only [P]
    have hnltNat : ¬ i.toNat < n.toNat := by
      simpa only [UInt32.lt_iff_toNat_lt] using hnlt
    have hiEq : i.toNat = n.toNat := by omega
    have hiWord : i = n := UInt32.toNat_inj.mp hiEq
    subst i
    have hsuffix : suffix = [] := by
      apply List.eq_nil_of_length_eq_zero
      omega
    subst suffix
    iintro ⟨#_IH', Hrest⟩
    icases Hrest with ⟨HR', Harray'⟩
    iapply hfinish
    isplitl [HR']
    · iexact HR'
    · simp only [List.append_nil]
      iexact Harray'
  · simp only [P]
    iframe

/-- Enter the generated `.loop` with an arbitrary original u64 array. -/
theorem fillWords_loop_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {α : Type} (R : IProp WasmHeapGF)
    (base n : UInt32) (value : UInt64) (original : List UInt64)
    (afterLoop : Program) (arity : Nat) (remainder : List Value)
    (outerControls : List Wasm.SmallStep.ControlFrame)
    (calls : List Wasm.SmallStep.CallFrame)
    (hlength : original.length = n.toNat)
    (htotal : base.toNat + 8 * n.toNat ≤ 4294967296)
    (hfinish :
      R ∗ array64At base (List.replicate n.toNat value) ⊢
        WP (Wasm.SmallStep.Expr.running
          ⟨⟨[.i32 base, .i32 n, .i64 value], [.i32 n], []⟩,
            afterLoop, arity, remainder, outerControls, calls⟩ :
          Wasm.SmallStep.Expr α) @ s; E {{ Φ }}) :
    R ∗ array64At base original ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 base, .i32 n, .i64 value], [.i32 0], []⟩,
          [.loop 0 0 FillWordsLoopBody] ++ afterLoop,
          arity, remainder, outerControls, calls⟩ :
        Wasm.SmallStep.Expr α) @ s; E {{ Φ }} := by
  iintro Hresources
  simp only [List.cons_append, List.nil_append]
  iapply Wasm.SmallStep.wp_loop
  inext
  have hframe :
      ({ kind := .loop
         paramArity := 0
         resultArity := 0
         body := FillWordsLoopBody
         continuation := afterLoop
         belowStack :=
           (⟨[.i32 base, .i32 n, .i64 value], [.i32 0], []⟩ :
             Locals).values.drop 0 } :
        Wasm.SmallStep.ControlFrame) =
      fillWordsLoopFrame afterLoop := by
    rfl
  rw [hframe]
  have hbody := fillWords_loopBody_invariant_wp R base n 0 value
    original afterLoop arity remainder outerControls calls htotal
    (by simpa using hlength) hfinish
  iapply hbody
  simp only [UInt32.reduceToNat, List.replicate_zero, List.nil_append]
  iexact Hresources

/-- Full symbolic Iris rule for `FillWords`, including initialization of the
loop index local.  The postcondition owns the entire filled u64 region. -/
theorem fillWords_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {α : Type} (R : IProp WasmHeapGF)
    (base n initialIndex : UInt32) (value : UInt64)
    (original : List UInt64)
    (afterLoop : Program) (arity : Nat) (remainder : List Value)
    (controls : List Wasm.SmallStep.ControlFrame)
    (calls : List Wasm.SmallStep.CallFrame)
    (hlength : original.length = n.toNat)
    (htotal : base.toNat + 8 * n.toNat ≤ 4294967296)
    (hfinish :
      R ∗ array64At base (List.replicate n.toNat value) ⊢
        WP (Wasm.SmallStep.Expr.running
          ⟨⟨[.i32 base, .i32 n, .i64 value], [.i32 n], []⟩,
            afterLoop, arity, remainder, controls, calls⟩ :
          Wasm.SmallStep.Expr α) @ s; E {{ Φ }}) :
    R ∗ array64At base original ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 base, .i32 n, .i64 value],
            [.i32 initialIndex], []⟩,
          FillWords ++ afterLoop,
          arity, remainder, controls, calls⟩ :
        Wasm.SmallStep.Expr α) @ s; E {{ Φ }} := by
  iintro Hresources
  rw [FillWords_eq_structured]
  simp only [List.cons_append, List.nil_append]
  iapply Wasm.SmallStep.wp_const
  inext
  iapply Wasm.SmallStep.wp_localSet rfl
  inext
  simp only [List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub, List.set]
  have hloop := fillWords_loop_wp R base n value original afterLoop arity
    remainder controls calls hlength htotal hfinish
  simp only [List.cons_append, List.nil_append] at hloop
  iapply hloop
  iexact Hresources

end Wasm
