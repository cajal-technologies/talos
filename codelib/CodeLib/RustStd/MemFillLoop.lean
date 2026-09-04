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
      .loop 0 0 FillWordsLoopBody] := by rfl

/-- One real small-step fill iteration extends the authoritatively owned
filled prefix by one word and frames an arbitrary Iris resource `R`. -/
theorem fillWords_storeIteration_wp
    {α : Type} [Wasm.SmallStep.WasmSmallStepGS hlc α]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF α)}
    (R : IProp (WasmHeapGF α))
    (base n i : UInt32) (value old : UInt64)
    (suffix : List UInt64)
    (code : Program) (arity : Nat) (remainder : List Value)
    (controls : List Wasm.SmallStep.ControlFrame)
    (calls : List Wasm.SmallStep.CallFrame)
    (hroom : base.toNat + 8 * (i.toNat + 1) ≤ 4294967296)
    (hcontinue :
      R ∗ array64At 0 base
          (List.replicate (i.toNat + 1) value ++ suffix) ⊢
        WP (Wasm.SmallStep.Expr.running
          ⟨⟨[.i32 base, .i32 n, .i64 value], [.i32 i], []⟩,
            code, arity, remainder, controls, calls⟩ :
          Wasm.SmallStep.Expr α) @ s; E {{ Φ }}) :
    R ∗ array64At 0 base
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
    rw [hi]; exact UInt32.add_comm _ _
  have haddrNat : address.toNat = base.toNat + 8 * i.toNat :=
    Mem.words64_slotAddr_toNat base i.toNat (by omega)
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ :=
    UInt32.addSteps8 address (by omega)
  iintro ⟨HR, Harray⟩
  icases array64At_fill_next 0 base i.toNat value old suffix $$ Harray with
    ⟨Hold, Hreassemble⟩
  simp only [FillWordsStoreIteration, List.cons_append, List.nil_append]
  wasm_wp_pures [wp_localGet wp_localGet wp_const wp_shl wp_add] rewriting [haddr]
  wasm_wp_pures [wp_localGet]
  ihave HoldLater : ▷ pointsTo_u64 0 (address + 0) old $$ [Hold]
  · inext
    simp only [UInt32.add_zero, address]
    iexact Hold
  wasm_wp_next_bind Wasm.SmallStep.wp_store64
      (address := address) (offset := 0) (value := value) old
      (by simp) (by simpa using h1) (by simpa using h2)
      (by simpa using h3) (by simpa using h4) (by simpa using h5)
      (by simpa using h6) (by simpa using h7) with HoldLater => Hnew
  ihave Hnew' :
      pointsTo_u64 0 (base + 8 * UInt32.ofNat i.toNat) value $$ [Hnew]
  · simp only [UInt32.add_zero, address]
    iexact Hnew
  ihave Harray' :
      array64At 0 base
        (List.replicate (i.toNat + 1) value ++ suffix) $$
      [Hreassemble Hnew']
  · iapply_exact Hreassemble with Hnew'
  iapply_frame hcontinue

/-- The generated index increment and `br 1` really target the surrounding
loop frame, with the updated local and no operand-stack leakage. -/
theorem fillWords_incrementBackedge_wp
    {α : Type} [Wasm.SmallStep.WasmSmallStepGS hlc α]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF α)}
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
  wasm_wp_pures [wp_localGet wp_const wp_add] rewriting [UInt32.add_comm 1 i]
  wasm_wp_pures [wp_localSet wp_br] using [fillWordsLoopFrame, List.length_cons,
    List.length_nil, Nat.reduceAdd, Nat.reduceSub, List.set, List.take_nil,
    List.nil_append]
  iexact Hcontinue

/-- Compose the authoritative store with the generated increment/back-edge.
The premise is exactly the guarded family hypothesis for iteration `i + 1`. -/
theorem fillWords_bodyTail_wp
    {α : Type} [Wasm.SmallStep.WasmSmallStepGS hlc α]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF α)}
    (R : IProp (WasmHeapGF α))
    (base n i : UInt32) (value old : UInt64)
    (suffix : List UInt64)
    (afterLoop : Program) (arity : Nat) (remainder : List Value)
    (outerControls : List Wasm.SmallStep.ControlFrame)
    (calls : List Wasm.SmallStep.CallFrame)
    (hroom : base.toNat + 8 * (i.toNat + 1) ≤ 4294967296)
    (hback :
      R ∗ array64At 0 base
          (List.replicate (i.toNat + 1) value ++ suffix) ⊢
        ▷ WP (Wasm.SmallStep.Expr.running
          ⟨⟨[.i32 base, .i32 n, .i64 value], [.i32 (i + 1)], []⟩,
            FillWordsLoopBody, arity, remainder,
            fillWordsLoopFrame afterLoop :: outerControls, calls⟩ :
          Wasm.SmallStep.Expr α) @ s; E {{ Φ }}) :
    R ∗ array64At 0 base
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
  iapply_exact hback with Hresources

/-- The two generated blocks implement the loop guard: `i < n` exposes the
stateful body tail, while `i ≥ n` exits first the outer block and then the
loop frame into `afterLoop`. -/
theorem fillWords_guard_wp
    {α : Type} [Wasm.SmallStep.WasmSmallStepGS hlc α]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF α)}
    (P : IProp (WasmHeapGF α))
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
  wasm_wp_pures [wp_block] using [FillWordsOuterBody, List.cons_append, List.nil_append]
  wasm_wp_pures [wp_block] using [FillWordsInnerGuard]
  wasm_wp_pures [wp_localGet wp_localGet]
  by_cases hlt : i < n
  · wasm_wp_next Wasm.SmallStep.wp_ltU (result := 1) (by simp [hlt])
    wasm_wp_next Wasm.SmallStep.wp_brIf (by decide) (by rfl)
    simp only [List.drop_zero, List.take_nil, List.nil_append]
    iapply_exact hbody hlt with HP
  · wasm_wp_next Wasm.SmallStep.wp_ltU (result := 0) (by simp [hlt])
    wasm_wp_pures [wp_brIfZero wp_br wp_exitControl]
    simp only [fillWordsLoopFrame, List.drop_zero, List.take_nil,
      List.nil_append]
    iapply_exact hexit hlt with HP

/-- Universal Iris loop invariant.  `suffix` is the not-yet-written part of
the original array, so `i + suffix.length = n`; ownership is exactly the
filled prefix followed by that suffix. -/
theorem fillWords_loopBody_invariant_wp
    {α : Type} [Wasm.SmallStep.WasmSmallStepGS hlc α]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF α)}
    (R : IProp (WasmHeapGF α))
    (base n i : UInt32) (value : UInt64) (suffix : List UInt64)
    (afterLoop : Program) (arity : Nat) (remainder : List Value)
    (outerControls : List Wasm.SmallStep.ControlFrame)
    (calls : List Wasm.SmallStep.CallFrame)
    (htotal : base.toNat + 8 * n.toNat ≤ 4294967296)
    (hinv : i.toNat + suffix.length = n.toNat)
    (hfinish :
      R ∗ array64At 0 base (List.replicate n.toNat value) ⊢
        WP (Wasm.SmallStep.Expr.running
          ⟨⟨[.i32 base, .i32 n, .i64 value], [.i32 n], []⟩,
            afterLoop, arity, remainder, outerControls, calls⟩ :
          Wasm.SmallStep.Expr α) @ s; E {{ Φ }}) :
    R ∗ array64At 0 base
        (List.replicate i.toNat value ++ suffix) ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 base, .i32 n, .i64 value], [.i32 i], []⟩,
          FillWordsLoopBody, arity, remainder,
          fillWordsLoopFrame afterLoop :: outerControls, calls⟩ :
        Wasm.SmallStep.Expr α) @ s; E {{ Φ }} := by
  iloeb as IH generalizing %i %suffix %hinv
  let Kloop : IProp (WasmHeapGF α) := iprop(
    ▷ ∀ (j : UInt32) (tail : List UInt64),
      ⌜j.toNat + tail.length = n.toNat⌝ -∗
      R ∗ array64At 0 base
          (List.replicate j.toNat value ++ tail) -∗
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 base, .i32 n, .i64 value], [.i32 j], []⟩,
          FillWordsLoopBody, arity, remainder,
          fillWordsLoopFrame afterLoop :: outerControls, calls⟩ :
        Wasm.SmallStep.Expr α) @ s; E {{ Φ }})
  ihave IHtyped : □ Kloop $$ [IH]
  · simp only [Kloop]
    iexact IH
  let P : IProp (WasmHeapGF α) :=
    iprop% □ Kloop ∗ R ∗ array64At 0 base
      (List.replicate i.toNat value ++ suffix)
  iintro ⟨HR, Harray⟩
  iapply fillWords_guard_wp P
      base n i value afterLoop arity remainder outerControls calls
  · intro hlt
    simp only [P]
    cases suffix with
    | nil =>
        have hltNat : i.toNat < n.toNat := hlt
        simp only [List.length_nil, Nat.add_zero] at hinv; omega
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
          simp only [List.length_cons] at hinv; omega
        let Rloop : IProp (WasmHeapGF α) := iprop% □ Kloop ∗ R
        iintro ⟨#IHcurrent, HcurrentRest⟩
        icases HcurrentRest with ⟨HRcurrent, HarrayCurrent⟩
        iapply fillWords_bodyTail_wp Rloop base n i value old tail
          afterLoop arity remainder outerControls calls
        · omega
        · iintro Hresources
          ihave Hexpanded :
              (□ Kloop ∗ R) ∗
                array64At 0 base
                  (List.replicate ((i + 1).toNat) value ++ tail) $$
              [Hresources]
          · simp only [Rloop]
            irw_exact [hnext] with Hresources
          icases Hexpanded with ⟨Hloop, Harray'⟩
          icases Hloop with ⟨#IH', HR'⟩
          ispecialize IH' $$ %(i + 1) %tail %hinvNext
          iapply_frame IH'
        · simp only [Rloop]
          isplitl [IHcurrent HRcurrent]
          · isplitl_exact IHcurrent
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
    iapply_splitl_exact hfinish with HR'
    · simp only [List.append_nil]
      iexact Harray'
  · simp only [P]
    iframe

/-- Enter the generated `.loop` with an arbitrary original u64 array. -/
theorem fillWords_loop_wp
    {α : Type} [Wasm.SmallStep.WasmSmallStepGS hlc α]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF α)}
    (R : IProp (WasmHeapGF α))
    (base n : UInt32) (value : UInt64) (original : List UInt64)
    (afterLoop : Program) (arity : Nat) (remainder : List Value)
    (outerControls : List Wasm.SmallStep.ControlFrame)
    (calls : List Wasm.SmallStep.CallFrame)
    (hlength : original.length = n.toNat)
    (htotal : base.toNat + 8 * n.toNat ≤ 4294967296)
    (hfinish :
      R ∗ array64At 0 base (List.replicate n.toNat value) ⊢
        WP (Wasm.SmallStep.Expr.running
          ⟨⟨[.i32 base, .i32 n, .i64 value], [.i32 n], []⟩,
            afterLoop, arity, remainder, outerControls, calls⟩ :
          Wasm.SmallStep.Expr α) @ s; E {{ Φ }}) :
    R ∗ array64At 0 base original ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 base, .i32 n, .i64 value], [.i32 0], []⟩,
          [.loop 0 0 FillWordsLoopBody] ++ afterLoop,
          arity, remainder, outerControls, calls⟩ :
        Wasm.SmallStep.Expr α) @ s; E {{ Φ }} := by
  iintro Hresources
  simp only [List.cons_append, List.nil_append]
  wasm_wp_next Wasm.SmallStep.wp_loop
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
    {α : Type} [Wasm.SmallStep.WasmSmallStepGS hlc α]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF α)}
    (R : IProp (WasmHeapGF α))
    (base n initialIndex : UInt32) (value : UInt64)
    (original : List UInt64)
    (afterLoop : Program) (arity : Nat) (remainder : List Value)
    (controls : List Wasm.SmallStep.ControlFrame)
    (calls : List Wasm.SmallStep.CallFrame)
    (hlength : original.length = n.toNat)
    (htotal : base.toNat + 8 * n.toNat ≤ 4294967296)
    (hfinish :
      R ∗ array64At 0 base (List.replicate n.toNat value) ⊢
        WP (Wasm.SmallStep.Expr.running
          ⟨⟨[.i32 base, .i32 n, .i64 value], [.i32 n], []⟩,
            afterLoop, arity, remainder, controls, calls⟩ :
          Wasm.SmallStep.Expr α) @ s; E {{ Φ }}) :
    R ∗ array64At 0 base original ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 base, .i32 n, .i64 value],
            [.i32 initialIndex], []⟩,
          FillWords ++ afterLoop,
          arity, remainder, controls, calls⟩ :
        Wasm.SmallStep.Expr α) @ s; E {{ Φ }} := by
  iintro Hresources
  rw [FillWords_eq_structured]
  simp only [List.cons_append, List.nil_append]
  wasm_wp_pures [wp_const wp_localSet] using [List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub, List.set]
  have hloop := fillWords_loop_wp R base n value original afterLoop arity
    remainder controls calls hlength htotal hfinish
  simp only [List.cons_append, List.nil_append] at hloop
  iapply_exact hloop with Hresources

end Wasm
