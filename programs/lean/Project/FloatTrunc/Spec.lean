import Project.FloatTrunc.Program

/-!
# Specification for `float_trunc`

The exported `check` function asserts that `naive_trunc` (NaN/range checks + cast)
and `sat_trunc` (Rust's saturating `x as i32`) agree on every `f32` bit pattern.
The proof shows `check` always terminates normally with empty result.
-/

namespace Project.FloatTrunc.Spec

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SmallStep
open Wasm.SepLogic

set_option maxRecDepth 1048576

/-! ## Efficient `∀ x : UInt32` decidability -/

/-- Countdown from n: true iff p holds for every UInt32 with toNat < n. -/
private def forallUInt32Aux (p : UInt32 → Bool) : Nat → Bool
  | 0     => true
  | n + 1 => if p (UInt32.ofNat n) then forallUInt32Aux p n else false

private theorem forallUInt32Aux_iff (p : UInt32 → Bool) (n : Nat) :
    forallUInt32Aux p n = true ↔ ∀ k : UInt32, k.toNat < n → p k = true := by
  induction n with
  | zero => simp [forallUInt32Aux]
  | succ n ih =>
    simp only [forallUInt32Aux]
    rcases Bool.eq_false_or_eq_true (p (UInt32.ofNat n)) with ht | hf
    · -- ht : p (UInt32.ofNat n) = true
      simp only [ht, ite_true, ih]
      constructor
      · intro hall k hk
        rcases (by omega : k.toNat < n ∨ k.toNat = n) with hlt | hkn
        · exact hall k hlt
        · have hke : k = UInt32.ofNat n := by
            have h0 := UInt32.ofNat_toNat (x := k)
            rw [hkn] at h0; exact h0.symm
          rw [hke]; exact ht
      · intro hall k hlt
        exact hall k (Nat.lt_succ_of_lt hlt)
    · -- hf : p (UInt32.ofNat n) = false
      simp only [hf, ite_false, Bool.false_eq_true, false_iff]
      intro hall
      have hlt : (UInt32.ofNat n).toNat < n + 1 := by
        have h1 : (UInt32.ofNat n).toNat = n % 2 ^ 32 := UInt32.toNat_ofNat'
        have h2 : n % 2 ^ 32 ≤ n := Nat.mod_le n _
        omega
      have hval := hall (UInt32.ofNat n) hlt
      simp [hf] at hval

/-- `native_decide` can decide `∀ x : UInt32, P x` via a 4B-iteration countdown. -/
private instance decidableForallUInt32 {P : UInt32 → Prop} [DecidablePred P] :
    Decidable (∀ x : UInt32, P x) :=
  let p := fun x => decide (P x)
  if h : forallUInt32Aux p UInt32.size then
    isTrue fun x =>
      of_decide_eq_true
        ((forallUInt32Aux_iff p UInt32.size).mp h x (UInt32.toNat_lt_size x))
  else
    isFalse fun hall =>
      h ((forallUInt32Aux_iff p UInt32.size).mpr fun k _ => decide_eq_true (hall k))

/-! ## Float math helpers -/

/-- Expose `private satI32S` body; provable by `rfl` since the kernel reduces it. -/
private theorem i32TruncSatF32S_expand (x : UInt32) :
    i32TruncSatF32S x =
    let f := (Float32.ofBits x).toFloat
    if f.isNaN then 0
    else let t := if f < 0.0 then f.ceil else f.floor
         if t ≤ (-2147483648.0 : Float) then 0x80000000
         else if t ≥ (2147483647.0 : Float) then 0x7FFFFFFF
         else t.toInt64.toUInt64.toUInt32 := rfl

/-- IEEE 754: `f32Ne x x = true` iff `x` encodes a NaN.
`f32Ne x x = !(f == f)` and `Float.isNaN f = !(f == f)` (both opaque externs);
checked for all 2^32 bit patterns by native evaluation. -/
private theorem f32Ne_self_iff_isNaN (x : UInt32) :
    f32Ne x x = (Float32.ofBits x).toFloat.isNaN :=
  IEEE32Exec.f32Ne_self_iff_isNaN x

private theorem i32TruncSatF32S_nan {x : UInt32}
    (h : (Float32.ofBits x).toFloat.isNaN) : i32TruncSatF32S x = 0 := by
  simp [i32TruncSatF32S_expand, h]

/-- `2^31` as a `Float32` bit pattern is `0x4F000000 = 1325400064`. When
`f ≥ 2^31`, `floor f ≥ 2^31 > 2147483647`, so `satI32S` saturates to `MAX`.
Checked for all 2^32 bit patterns by native evaluation. -/
private theorem i32TruncSatF32S_large_pos {x : UInt32}
    (hnan : f32Ne x x = false)
    (hge : f32Ge x 1325400064 = true) :
    i32TruncSatF32S x = 0x7FFFFFFF :=
  IEEE32Exec.i32TruncSatF32S_large_pos hnan hge

/-- `-2^31` as a `Float32` bit pattern is `0xCF000000 = 3472883712`. When
`f < -2^31`, `ceil f ≤ -2^31 ≤ -2147483648`, so `satI32S` saturates to `MIN`.
Checked for all 2^32 bit patterns by native evaluation. -/
private theorem i32TruncSatF32S_large_neg {x : UInt32}
    (hnan : f32Ne x x = false)
    (hlt : f32Lt x 3472883712 = true) :
    i32TruncSatF32S x = 0x80000000 :=
  IEEE32Exec.i32TruncSatF32S_large_neg hnan hlt

/-! ## Per-function termination -/

/-- Small-step entry configuration for the pure saturating-conversion leaf. -/
def func1Config (x : UInt32) : Config Unit :=
  { expr := .running
      ⟨⟨[.f32 x], [], []⟩, func1, 1, [], [], []⟩
    store :=
      { runtime := { instances := #[{ module := «module», host := {} }], entry := ⟨0⟩ }
        wasm := «module».initialStore } }

/-- Contextual body rule for callers of the saturating-conversion leaf.  It
stops immediately before the generated `ret`, so the same rule works both at
top level and beneath an arbitrary saved call stack. -/
theorem func1_body_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (Wasm.SepLogic.WasmHeapGF Unit)}
    (x : UInt32) (calls : List CallFrame) :
    ▷ WP (.running
      ⟨⟨[.f32 x], [], [.i32 (i32TruncSatF32S x)]⟩,
        [.ret], 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }} ⊢
    WP (.running
      ⟨⟨[.f32 x], [], []⟩,
        func1, 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }} := by
  simp only [func1]
  iintro Hret
  iapply wp_localGet rfl
  inext
  iapply wp_scalarFloat1 rfl rfl
  iexact Hret

/-- iris-lean partial-correctness proof for the generated
`i32.trunc_sat_f32_s` leaf. -/
theorem func1_smallStep (x : UInt32) :
    PartiallyMeets (func1Config x)
      (fun rs _store => rs = [.i32 (i32TruncSatF32S x)]) := by
  apply wasm_smallStep_partiallyMeets (α := Unit)
  intro gs
  simp only [func1Config]
  iapply func1_body_smallStep_wp x []
  inext
  iapply wp_returnFromFunction
  inext
  iapply wp_value'
  ipureintro
  rfl

/-- Small-step entry state for generated `naive_trunc`. -/
def func0Config (x : UInt32) : Config Unit :=
  { expr := .running
      ⟨⟨[.f32 x], [.i32 0], []⟩, func0, 1, [], [], []⟩
    store :=
      { runtime := { instances := #[{ module := «module», host := {} }], entry := ⟨0⟩ }
        wasm := «module».initialStore } }

/-- The one physical word used by `naive_trunc`'s shadow-stack slot. -/
def func0Heap : WasmHeapMap (Option UInt8) :=
  store32Heap ∅ 0 1048572 0

/-- Authoritative stack-pointer global used to derive the scratch address. -/
def func0Globals : WasmGlobalMap Value :=
  insert ∅ ⟨0, 0⟩ (.i32 1048576)

theorem func0Heap_agrees :
    heapAgreesWithMem func0Heap (storeResolve (func0Config 0).store) := by
  unfold func0Heap
  have h := store32_sound0 (∅ : WasmHeapMap (Option UInt8))
      («module».initialStore : Store Unit).mem 1048572 0
      (by decide) (by decide) (by decide)
      (heapAgreesWithMem_empty _)
  rw [Mem.write32_eq_self (by decide) (by decide) (by decide) (by decide)] at h
  have hresolveEq : (fun id : Nat => if id = 0 then some («module».initialStore : Store Unit).mem else none) =
      storeResolve (func0Config 0).store := by
    funext id; by_cases h0 : id = 0
    · simp [h0, storeResolve, func0Config]
    · simp [h0, storeResolve, func0Config,
        show («module».initialStore : Store Unit).extraMems = [] from by native_decide]
  rw [← hresolveEq]
  exact h

theorem func0Heap_inBounds :
    heapAddressesInBounds func0Heap (storeResolve (func0Config 0).store) := by
  unfold func0Heap
  have h := store32_inBounds0 (∅ : WasmHeapMap (Option UInt8))
      («module».initialStore : Store Unit).mem 1048572 0
      (by decide) (by decide) (by decide) (by decide)
      (heapAddressesInBounds_empty _)
  rw [Mem.write32_eq_self (by decide) (by decide) (by decide) (by decide)] at h
  have hresolveEq : (fun id : Nat => if id = 0 then some («module».initialStore : Store Unit).mem else none) =
      storeResolve (func0Config 0).store := by
    funext id; by_cases h0 : id = 0
    · simp [h0, storeResolve, func0Config]
    · simp [h0, storeResolve, func0Config,
        show («module».initialStore : Store Unit).extraMems = [] from by native_decide]
  rw [← hresolveEq]
  exact h

theorem func0Globals_agree :
    globalHeapAgrees func0Globals (func0Config 0).store.wasm.globals := by
  intro index value hget
  simp only [func0Globals] at hget
  by_cases hindex : index = 0
  · subst index
    simp only [get?_insert_eq rfl] at hget
    obtain rfl := Option.some.inj hget
    rfl
  · rw [get?_insert_ne (show (⟨0, 0⟩ : GlobalKey) ≠ ⟨0, index⟩ from
          fun h => hindex (congrArg GlobalKey.index h).symm),
        get?_empty] at hget
    contradiction

theorem func0Heap_pointsTo [WasmHeapGS Unit] :
    ([∗map] address ↦ value ∈ func0Heap,
      pointsTo (GF := WasmHeapGF Unit) (H := WasmHeapMap)
        address (DFrac.own 1) value) ⊢
      pointsTo_u32 0 1048572 0 := by
  unfold func0Heap
  simpa only [BI.BigSepM.bigSepM_empty.to_eq, BI.sep_emp.to_eq] using
    (store32Heap_pointsTo (∅ : WasmHeapMap (Option UInt8))
      0 1048572 0
      (get?_empty _) (get?_empty _) (get?_empty _) (get?_empty _)
      (by decide) (by decide) (by decide))

theorem func0Globals_pointsTo [WasmGlobalGS Unit] :
    ([∗map] index ↦ value ∈ func0Globals,
      globalPointsTo index value) ⊢
      globalPointsToAt 0 0 (.i32 1048576) := by
  unfold func0Globals
  rw [(BI.BigSepM.bigSepM_insert (get?_empty (⟨0, 0⟩ : GlobalKey))).to_eq,
    BI.BigSepM.bigSepM_empty.to_eq, BI.sep_emp.to_eq]
  simp only [globalPointsToAt_eq]
  rfl

/-- Call-stack-polymorphic form of the common scratch load tail.  `R` frames
all unrelated ownership, and the continuation decides whether the generated
`ret` returns from a nested call or from the top-level invocation. -/
theorem func0_tail_to_ret_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit)) (x word : UInt32) (calls : List CallFrame) :
    R ∗ pointsTo_u32 0 1048572 word ∗
      ▷ (R ∗ pointsTo_u32 0 1048572 word -∗
        WP (.running
          ⟨⟨[.f32 x], [.i32 1048560], [.i32 word]⟩,
            [.ret], 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }}) ⊢
      WP (.running
        ⟨⟨[.f32 x], [.i32 1048560], []⟩,
          [.localGet 1, .load32 12, .ret], 1, [], [], calls⟩ :
          Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨HR, Hword, Hret⟩
  iapply wp_localGet rfl
  inext
  have heffective : (1048560 : UInt32) + 12 = 1048572 := by decide
  ihave HwordLater :
      ▷ pointsTo_u32 0 ((1048560 : UInt32) + 12) word $$ [Hword]
  · inext
    rw [heffective]
    iexact Hword
  iapply wp_load32 word (by decide) (by decide) (by decide) (by decide) $$
    HwordLater
  inext
  iintro Hword
  iapply Hret
  isplitl [HR]
  · iexact HR
  · rw [heffective]
    iexact Hword

/-- Common load-and-return tail after one of `naive_trunc`'s four branches
has written the authoritative scratch word. -/
theorem func0_tail_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    (x word : UInt32) :
    pointsTo_u32 0 1048572 word ⊢
      WP (.running
        ⟨⟨[.f32 x], [.i32 1048560], []⟩,
          [.localGet 1, .load32 12, .ret], 1, [], [], []⟩ :
          Expr Unit) @ s; E
        {{ rs, ⌜rs = [.i32 word]⌝ }} := by
  iintro Hword
  iapply func0_tail_to_ret_smallStep_wp (iprop(True)) x word []
  isplitr
  · itrivial
  isplitl [Hword]
  · iexact Hword
  · inext
    iintro ⟨_Htrue, Hword⟩
    iapply wp_returnFromFunction
    inext
    iapply wp_value'
    iclear Hword
    ipureintro
    rfl

/-- Specialized authoritative store rule for `func0`'s concrete
`1048560 + 12 = 1048572` scratch address. -/
theorem func0_store32_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    {params localValues values : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (oldWord newWord : UInt32) :
    pointsTo_u32 0 1048572 oldWord ∗
      ▷ (pointsTo_u32 0 1048572 newWord -∗
        WP (.running
          ⟨⟨params, localValues, values⟩,
            code, arity, remainder, controls, calls⟩ : Expr Unit) @ s; E
          {{ Φ }}) ⊢
      WP (.running
        ⟨⟨params, localValues,
            .i32 newWord :: .i32 1048560 :: values⟩,
          .store32 12 :: code, arity, remainder, controls, calls⟩ :
          Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨Hword, Hnext⟩
  have heffective : (1048560 : UInt32) + 12 = 1048572 := by decide
  ihave HwordLater :
      ▷ pointsTo_u32 0 ((1048560 : UInt32) + 12) oldWord $$ [Hword]
  · inext
    rw [heffective]
    iexact Hword
  iapply wp_store32 oldWord (by decide) (by decide) (by decide) (by decide) $$
    HwordLater
  inext
  iintro Hword
  iapply Hnext
  rw [heffective]
  iexact Hword

/-- Call-stack-polymorphic body rule for generated `naive_trunc`.  The four
control-flow paths write the same value as Rust's saturating cast and join
immediately before the generated `ret`. -/
theorem func0_body_to_ret_smallStep_wp
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit)) (x : UInt32) (calls : List CallFrame)
    (hreturn : ∀ word : UInt32,
      word = i32TruncSatF32S x →
      R ∗ globalPointsToAt 0 0 (.i32 1048576) ∗ pointsTo_u32 0 1048572 word ⊢
        WP (.running
          ⟨⟨[.f32 x], [.i32 1048560], [.i32 word]⟩,
            [.ret], 1, [], [], calls⟩ : Expr Unit) @ s; E {{ Φ }}) :
    R ∗ globalPointsToAt 0 0 (.i32 1048576) ∗ pointsTo_u32 0 1048572 0 ⊢
      WP (.running
        ⟨⟨[.f32 x], [.i32 0], []⟩, func0, 1, [], [], calls⟩ :
          Expr Unit) @ s; E {{ Φ }} := by
    iintro ⟨HR, Hglobal, Hword⟩
    let Rglobal : IProp (WasmHeapGF Unit) :=
      iprop(R ∗ globalPointsToAt 0 0 (.i32 1048576))
    simp only [func0]
    iapply wp_globalGet $$ Hglobal
    inext
    iintro Hglobal
    iapply wp_const
    inext
    iapply wp_sub
    inext
    iapply wp_localSet rfl
    inext
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
      List.set, UInt32.reduceSub]
    iapply wp_block
    inext
    iapply wp_block
    inext
    iapply wp_block
    inext
    iapply wp_block
    inext
    iapply wp_block
    inext
    iapply wp_block
    inext
    iapply wp_localGet rfl
    inext
    iapply wp_localGet rfl
    inext
    cases hnan : f32Ne x x
    · iapply wp_scalarFloat2 rfl rfl rfl
      inext
      simp only [hnan, Bool.false_eq_true, if_false]
      iapply wp_const
      inext
      iapply wp_and
      inext
      rw [show (0 &&& 1 : UInt32) = 0 by decide]
      iapply wp_brIfZero
      inext
      iapply wp_localGet rfl
      inext
      iapply wp_scalarFloat0 rfl
      inext
      cases hge : f32Ge x 1325400064
      · iapply wp_scalarFloat2 rfl rfl rfl
        inext
        simp only [hge, Bool.false_eq_true, if_false]
        iapply wp_const
        inext
        iapply wp_and
        inext
        rw [show (0 &&& 1 : UInt32) = 0 by decide]
        iapply wp_brIfZero
        inext
        iapply wp_br rfl
        inext
        simp only [List.take, List.drop, List.nil_append]
        iapply wp_localGet rfl
        inext
        iapply wp_scalarFloat0 rfl
        inext
        cases hlt : f32Lt x 3472883712
        · iapply wp_scalarFloat2 rfl rfl rfl
          inext
          simp only [hlt, Bool.false_eq_true, if_false]
          iapply wp_const
          inext
          iapply wp_and
          inext
          rw [show (0 &&& 1 : UInt32) = 0 by decide]
          iapply wp_brIfZero
          inext
          iapply wp_br rfl
          inext
          simp only [List.take, List.nil_append]
          iapply wp_localGet rfl
          inext
          iapply wp_localGet rfl
          inext
          iapply wp_scalarFloat1 rfl rfl
          inext
          iapply func0_store32_smallStep_wp 0 (i32TruncSatF32S x)
          isplitl [Hword]
          · iexact Hword
          · inext
            iintro Hword
            iapply wp_br rfl
            inext
            simp only [List.take, List.nil_append]
            iapply func0_tail_to_ret_smallStep_wp
              Rglobal x (i32TruncSatF32S x) calls
            isplitl [HR Hglobal]
            · simp only [Rglobal]
              iframe
            isplitl [Hword]
            · iexact Hword
            · inext
              iintro ⟨⟨HR, Hglobal⟩, Hword⟩
              iapply hreturn (i32TruncSatF32S x) rfl
              iframe
        · iapply wp_scalarFloat2 rfl rfl rfl
          inext
          simp only [hlt, if_true]
          iapply wp_const
          inext
          iapply wp_and
          inext
          rw [show (1 &&& 1 : UInt32) = 1 by decide]
          iapply wp_brIf (by decide) rfl
          inext
          simp only [List.take, List.nil_append]
          iapply wp_localGet rfl
          inext
          iapply wp_const
          inext
          iapply func0_store32_smallStep_wp 0 2147483648
          isplitl [Hword]
          · iexact Hword
          · inext
            iintro Hword
            iapply wp_exitControl rfl
            inext
            simp only [List.take, List.nil_append]
            have heq := i32TruncSatF32S_large_neg hnan hlt
            iapply func0_tail_to_ret_smallStep_wp
              Rglobal x 2147483648 calls
            isplitl [HR Hglobal]
            · simp only [Rglobal]
              iframe
            isplitl [Hword]
            · iexact Hword
            · inext
              iintro ⟨⟨HR, Hglobal⟩, Hword⟩
              iapply hreturn 2147483648 heq.symm
              iframe
      · iapply wp_scalarFloat2 rfl rfl rfl
        inext
        simp only [hge, if_true]
        iapply wp_const
        inext
        iapply wp_and
        inext
        rw [show (1 &&& 1 : UInt32) = 1 by decide]
        iapply wp_brIf (by decide) rfl
        inext
        simp only [List.take, List.drop, List.nil_append]
        iapply wp_localGet rfl
        inext
        iapply wp_const
        inext
        iapply func0_store32_smallStep_wp 0 2147483647
        isplitl [Hword]
        · iexact Hword
        · inext
          iintro Hword
          iapply wp_br rfl
          inext
          simp only [List.take, List.nil_append]
          have heq := i32TruncSatF32S_large_pos hnan hge
          iapply func0_tail_to_ret_smallStep_wp
            Rglobal x 2147483647 calls
          isplitl [HR Hglobal]
          · simp only [Rglobal]
            iframe
          isplitl [Hword]
          · iexact Hword
          · inext
            iintro ⟨⟨HR, Hglobal⟩, Hword⟩
            iapply hreturn 2147483647 heq.symm
            iframe
    · iapply wp_scalarFloat2 rfl rfl rfl
      inext
      simp only [hnan, if_true]
      iapply wp_const
      inext
      iapply wp_and
      inext
      rw [show (1 &&& 1 : UInt32) = 1 by decide]
      iapply wp_brIf (by decide) rfl
      inext
      simp only [List.take, List.drop, List.nil_append]
      iapply wp_localGet rfl
      inext
      iapply wp_const
      inext
      iapply func0_store32_smallStep_wp 0 0
      isplitl [Hword]
      · iexact Hword
      · inext
        iintro Hword
        iapply wp_br rfl
        inext
        simp only [List.take, List.nil_append]
        have hisNaN : (Float32.ofBits x).toFloat.isNaN = true :=
          (f32Ne_self_iff_isNaN x).symm.trans hnan
        have heq := i32TruncSatF32S_nan hisNaN
        iapply func0_tail_to_ret_smallStep_wp
          Rglobal x 0 calls
        isplitl [HR Hglobal]
        · simp only [Rglobal]
          iframe
        isplitl [Hword]
        · iexact Hword
        · inext
          iintro ⟨⟨HR, Hglobal⟩, Hword⟩
          iapply hreturn 0 heq.symm
          iframe

/-- Complete authoritative small-step proof for generated `naive_trunc`. -/
theorem func0_smallStep (x : UInt32) :
    PartiallyMeets (func0Config x)
      (fun rs _store => rs = [.i32 (i32TruncSatF32S x)]) := by
  apply wasm_smallStep_heap_globals_partiallyMeets
      (α := Unit)
      (σ := func0Heap)
      (globalσ := func0Globals)
      (φ := fun rs => rs = [.i32 (i32TruncSatF32S x)])
  · simpa [func0Config] using func0Heap_agrees
  · simpa [func0Config] using func0Heap_inBounds
  · simpa [func0Config] using func0Globals_agree
  · simp only [func0Config]; decide
  · intro gs
    have hreturn : ∀ word : UInt32,
        word = i32TruncSatF32S x →
        iprop(True) ∗ globalPointsToAt 0 0 (.i32 1048576) ∗
            pointsTo_u32 0 1048572 word ⊢
          WP (.running
            ⟨⟨[.f32 x], [.i32 1048560], [.i32 word]⟩,
              [.ret], 1, [], [], []⟩ : Expr Unit)
            {{ rs, ⌜rs = [.i32 (i32TruncSatF32S x)]⌝ }} := by
      intro word heq
      iintro ⟨_Htrue, Hglobal, Hword⟩
      iapply wp_returnFromFunction
      inext
      iapply wp_value'
      iclear Hglobal Hword
      ipureintro
      simp [heq]
    iintro ⟨Hbytes, Hglobals⟩
    ihave Hword := func0Heap_pointsTo $$ Hbytes
    ihave Hglobal := func0Globals_pointsTo $$ Hglobals
    simp only [func0Config]
    iapply func0_body_to_ret_smallStep_wp (iprop(True)) x [] hreturn
    iframe

/-! ## Total WP helpers (no `▷` on continuations) -/

theorem twp_func1_body
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (x : UInt32) (calls : List CallFrame) :
    WP (.running
      ⟨⟨[.f32 x], [], [.i32 (i32TruncSatF32S x)]⟩,
        [.ret], 1, [], [], calls⟩ : Expr Unit) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨[.f32 x], [], []⟩,
        func1, 1, [], [], calls⟩ : Expr Unit) @ s; E [{ Φ }] := by
  simp only [func1]
  iintro Hret
  iapply twp_localGet rfl
  iapply twp_scalarFloat1 rfl rfl
  iexact Hret

theorem twp_func0_tail_to_ret
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit)) (x word : UInt32) (calls : List CallFrame) :
    R ∗ pointsTo_u32 0 1048572 word ∗
      (R ∗ pointsTo_u32 0 1048572 word -∗
        WP (.running
          ⟨⟨[.f32 x], [.i32 1048560], [.i32 word]⟩,
            [.ret], 1, [], [], calls⟩ : Expr Unit) @ s; E [{ Φ }]) ⊢
      WP (.running
        ⟨⟨[.f32 x], [.i32 1048560], []⟩,
          [.localGet 1, .load32 12, .ret], 1, [], [], calls⟩ :
          Expr Unit) @ s; E [{ Φ }] := by
  iintro ⟨HR, Hword, Hcont⟩
  iapply twp_localGet rfl
  have heffective : (1048560 : UInt32) + 12 = 1048572 := by decide
  ihave Hword' :
      pointsTo_u32 0 ((1048560 : UInt32) + 12) word $$ [Hword]
  · rw [heffective]
    iexact Hword
  iapply twp_load32 word (by decide) (by decide) (by decide) (by decide) $$ Hword'
  iintro Hword
  iapply Hcont
  isplitl [HR]
  · iexact HR
  · rw [heffective]
    iexact Hword

theorem twp_func0_store32
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    {params localValues values : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (oldWord newWord : UInt32) :
    pointsTo_u32 0 1048572 oldWord ∗
      (pointsTo_u32 0 1048572 newWord -∗
        WP (.running
          ⟨⟨params, localValues, values⟩,
            code, arity, remainder, controls, calls⟩ : Expr Unit) @ s; E
          [{ Φ }]) ⊢
      WP (.running
        ⟨⟨params, localValues,
            .i32 newWord :: .i32 1048560 :: values⟩,
          .store32 12 :: code, arity, remainder, controls, calls⟩ :
          Expr Unit) @ s; E [{ Φ }] := by
  iintro ⟨Hword, Hcont⟩
  have heffective : (1048560 : UInt32) + 12 = 1048572 := by decide
  ihave Hword' :
      pointsTo_u32 0 ((1048560 : UInt32) + 12) oldWord $$ [Hword]
  · rw [heffective]
    iexact Hword
  iapply twp_store32 oldWord (by decide) (by decide) (by decide) (by decide) $$ Hword'
  iintro Hword
  iapply Hcont
  rw [heffective]
  iexact Hword

theorem twp_func0_body_to_ret
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit)) (x : UInt32) (calls : List CallFrame)
    (hreturn : ∀ word : UInt32,
      word = i32TruncSatF32S x →
      R ∗ globalPointsToAt 0 0 (.i32 1048576) ∗ pointsTo_u32 0 1048572 word ⊢
        WP (.running
          ⟨⟨[.f32 x], [.i32 1048560], [.i32 word]⟩,
            [.ret], 1, [], [], calls⟩ : Expr Unit) @ s; E [{ Φ }]) :
    R ∗ globalPointsToAt 0 0 (.i32 1048576) ∗ pointsTo_u32 0 1048572 0 ⊢
      WP (.running
        ⟨⟨[.f32 x], [.i32 0], []⟩, func0, 1, [], [], calls⟩ :
          Expr Unit) @ s; E [{ Φ }] := by
  iintro ⟨HR, Hglobal, Hword⟩
  let Rglobal : IProp (WasmHeapGF Unit) :=
    iprop(R ∗ globalPointsToAt 0 0 (.i32 1048576))
  simp only [func0]
  iapply twp_globalGet $$ Hglobal
  iintro Hglobal
  iapply twp_const
  iapply twp_sub
  iapply twp_localSet rfl
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
    List.set, UInt32.reduceSub]
  iapply twp_block
  iapply twp_block
  iapply twp_block
  iapply twp_block
  iapply twp_block
  iapply twp_block
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  cases hnan : f32Ne x x
  · iapply twp_scalarFloat2 rfl rfl rfl
    simp only [hnan, Bool.false_eq_true, if_false]
    iapply twp_const
    iapply twp_and
    rw [show (0 &&& 1 : UInt32) = 0 by decide]
    iapply twp_brIfZero
    iapply twp_localGet rfl
    iapply twp_scalarFloat0 rfl
    cases hge : f32Ge x 1325400064
    · iapply twp_scalarFloat2 rfl rfl rfl
      simp only [hge, Bool.false_eq_true, if_false]
      iapply twp_const
      iapply twp_and
      rw [show (0 &&& 1 : UInt32) = 0 by decide]
      iapply twp_brIfZero
      iapply twp_br rfl
      simp only [List.take, List.drop, List.nil_append]
      iapply twp_localGet rfl
      iapply twp_scalarFloat0 rfl
      cases hlt : f32Lt x 3472883712
      · iapply twp_scalarFloat2 rfl rfl rfl
        simp only [hlt, Bool.false_eq_true, if_false]
        iapply twp_const
        iapply twp_and
        rw [show (0 &&& 1 : UInt32) = 0 by decide]
        iapply twp_brIfZero
        iapply twp_br rfl
        simp only [List.take, List.nil_append]
        iapply twp_localGet rfl
        iapply twp_localGet rfl
        iapply twp_scalarFloat1 rfl rfl
        iapply twp_func0_store32 0 (i32TruncSatF32S x)
        isplitl [Hword]
        · iexact Hword
        · iintro Hword
          iapply twp_br rfl
          simp only [List.take, List.nil_append]
          iapply twp_func0_tail_to_ret Rglobal x (i32TruncSatF32S x) calls
          isplitl [HR Hglobal]
          · simp only [Rglobal]
            iframe
          isplitl [Hword]
          · iexact Hword
          · iintro ⟨⟨HR, Hglobal⟩, Hword⟩
            iapply hreturn (i32TruncSatF32S x) rfl
            iframe
      · iapply twp_scalarFloat2 rfl rfl rfl
        simp only [hlt, if_true]
        iapply twp_const
        iapply twp_and
        rw [show (1 &&& 1 : UInt32) = 1 by decide]
        iapply twp_brIf (by decide) rfl
        simp only [List.take, List.nil_append]
        iapply twp_localGet rfl
        iapply twp_const
        iapply twp_func0_store32 0 2147483648
        isplitl [Hword]
        · iexact Hword
        · iintro Hword
          iapply twp_exitControl rfl
          simp only [List.take, List.nil_append]
          have heq := i32TruncSatF32S_large_neg hnan hlt
          iapply twp_func0_tail_to_ret Rglobal x 2147483648 calls
          isplitl [HR Hglobal]
          · simp only [Rglobal]
            iframe
          isplitl [Hword]
          · iexact Hword
          · iintro ⟨⟨HR, Hglobal⟩, Hword⟩
            iapply hreturn 2147483648 heq.symm
            iframe
    · iapply twp_scalarFloat2 rfl rfl rfl
      simp only [hge, if_true]
      iapply twp_const
      iapply twp_and
      rw [show (1 &&& 1 : UInt32) = 1 by decide]
      iapply twp_brIf (by decide) rfl
      simp only [List.take, List.drop, List.nil_append]
      iapply twp_localGet rfl
      iapply twp_const
      iapply twp_func0_store32 0 2147483647
      isplitl [Hword]
      · iexact Hword
      · iintro Hword
        iapply twp_br rfl
        simp only [List.take, List.nil_append]
        have heq := i32TruncSatF32S_large_pos hnan hge
        iapply twp_func0_tail_to_ret Rglobal x 2147483647 calls
        isplitl [HR Hglobal]
        · simp only [Rglobal]
          iframe
        isplitl [Hword]
        · iexact Hword
        · iintro ⟨⟨HR, Hglobal⟩, Hword⟩
          iapply hreturn 2147483647 heq.symm
          iframe
  · iapply twp_scalarFloat2 rfl rfl rfl
    simp only [hnan, if_true]
    iapply twp_const
    iapply twp_and
    rw [show (1 &&& 1 : UInt32) = 1 by decide]
    iapply twp_brIf (by decide) rfl
    simp only [List.take, List.drop, List.nil_append]
    iapply twp_localGet rfl
    iapply twp_const
    iapply twp_func0_store32 0 0
    isplitl [Hword]
    · iexact Hword
    · iintro Hword
      iapply twp_br rfl
      simp only [List.take, List.nil_append]
      have hisNaN : (Float32.ofBits x).toFloat.isNaN = true :=
        (f32Ne_self_iff_isNaN x).symm.trans hnan
      have heq := i32TruncSatF32S_nan hisNaN
      iapply twp_func0_tail_to_ret Rglobal x 0 calls
      isplitl [HR Hglobal]
      · simp only [Rglobal]
        iframe
      isplitl [Hword]
      · iexact Hword
      · iintro ⟨⟨HR, Hglobal⟩, Hword⟩
        iapply hreturn 0 heq.symm
        iframe

/-! ## Top-level spec -/

/-- Small-step entry configuration for the exported agreement check. -/
def checkConfig (x : UInt32) : Config Unit :=
  { expr := .running
      ⟨⟨[.f32 x], [], []⟩, func2, 0, [], [], []⟩
    store :=
      { runtime := { instances := #[{ module := «module», host := {} }], entry := ⟨0⟩ }
        wasm := «module».initialStore } }

theorem twp_check
    [WasmSmallStepGS hlc Unit] {s : Stuckness} {E : CoPset}
    (x : UInt32) :
    runtimeModuleOwn ⟨0⟩ «module» ∗ globalPointsToAt 0 0 (.i32 1048576) ∗
      pointsTo_u32 0 1048572 0 ⊢
      WP (.running ⟨⟨[.f32 x], [], []⟩, func2, 0, [], [], []⟩ : Expr Unit) @ s; E
        [{ rs, ∀ (store : MachineStore Unit) (_obs : List StepKind),
            stateInterp (GF := WasmHeapGF Unit) store 0 [] 0 -∗
            ⌜rs = []⌝ }] := by
  iintro ⟨Hruntime, Hglobal, Hword⟩
  simp only [func2]
  iapply twp_block
  iapply twp_localGet rfl
  iapply twp_call «module» 0 func0Def
    (by simp [«module»]) (by simp [«module»]) $$ Hruntime
  iintro Hruntime
  simp [func0Def, Function.toLocals, Function.numParams, ValueType.zero]
  iapply twp_func0_body_to_ret
    (runtimeModuleOwn ⟨0⟩ «module») x _
    (fun word heq => by
      iintro ⟨Hruntime, Hglobal, Hword⟩
      iapply twp_returnFromCallExplicit $$ Hruntime
      iintro Hruntime
      iapply twp_localGet rfl
      iapply twp_call «module» 1 func1Def
        (by simp [«module»]) (by simp [«module»]) $$ Hruntime
      iintro Hruntime
      simp [func1Def, Function.toLocals, Function.numParams]
      iapply twp_func1_body x _
      iapply twp_returnFromCallExplicit $$ Hruntime
      iintro Hruntime
      simp only [List.take, List.singleton_append]
      rw [heq]
      iapply twp_ne (result := 0) (by simp)
      iapply twp_const
      iapply twp_and
      rw [show (0 &&& 1 : UInt32) = 0 by decide]
      iapply twp_brIfZero
      iapply twp_returnFromFunction
      iapply twp.value rfl
      iintro %store %obs _Hstate
      iclear Hruntime Hglobal Hword
      ipureintro
      rfl)
  iframe

theorem check_terminatesWith (x : UInt32) :
    Wasm.SmallStep.TerminatesWith (checkConfig x)
      (fun rs _store => rs = []) := by
  apply wasm_smallStep_heap_globals_runtime_store_terminates
    (α := Unit)
    (σ := func0Heap) (globalσ := func0Globals)
    (post := fun rs _store => rs = [])
  · simpa [checkConfig, func0Config] using func0Heap_agrees
  · simpa [checkConfig, func0Config] using func0Heap_inBounds
  · simpa [checkConfig, func0Config] using func0Globals_agree
  · simp only [checkConfig]; decide
  · intro _hlc _gs
    simp only [checkConfig, RuntimeEnv.currentModule_mk1]
    iintro ⟨Hbytes, Hglobals, Hruntime⟩
    ihave Hword := func0Heap_pointsTo $$ Hbytes
    ihave Hglobal := func0Globals_pointsTo $$ Hglobals
    iapply twp_check x
    iframe

/-- Iris partial-correctness proof for the exported agreement check. -/
theorem check_smallStep (x : UInt32) :
    PartiallyMeets (checkConfig x) (fun rs _store => rs = []) := by
  apply wasm_smallStep_heap_globals_runtime_partiallyMeets
      (α := Unit) (σ := func0Heap) (globalσ := func0Globals)
      (φ := fun rs => rs = [])
  · simpa [checkConfig, func0Config] using func0Heap_agrees
  · simpa [checkConfig, func0Config] using func0Heap_inBounds
  · simpa [checkConfig, func0Config] using func0Globals_agree
  · simp only [checkConfig]; decide
  · intro gs
    simp only [checkConfig, RuntimeEnv.currentModule_mk1]
    iintro ⟨Hbytes, Hglobals, Hruntime⟩
    ihave Hword := func0Heap_pointsTo $$ Hbytes
    ihave Hglobal := func0Globals_pointsTo $$ Hglobals
    simp only [func2]
    iapply wp_block
    inext
    iapply wp_localGet rfl
    inext
    iapply wp_call «module» 0 func0Def
      (by simp [«module»]) (by simp [«module»]) $$ Hruntime
    inext
    iintro Hruntime
    simp [func0Def, Function.toLocals, Function.numParams, ValueType.zero]
    iapply func0_body_to_ret_smallStep_wp
      (runtimeModuleOwn ⟨0⟩ «module») x _
      (fun word heq => by
        iintro ⟨Hruntime, Hglobal, Hword⟩
        iapply wp_returnFromCallExplicit' $$ Hruntime
        inext
        iintro Hruntime
        iapply wp_localGet rfl
        inext
        iapply wp_call «module» 1 func1Def
          (by simp [«module»]) (by simp [«module»]) $$ Hruntime
        inext
        iintro Hruntime
        simp [func1Def, Function.toLocals, Function.numParams]
        iapply func1_body_smallStep_wp x _
        inext
        iapply wp_returnFromCallExplicit' $$ Hruntime
        inext
        iintro Hruntime
        simp only [List.take, List.singleton_append]
        rw [heq]
        iapply wp_ne (result := 0) (by simp)
        inext
        iapply wp_const
        inext
        iapply wp_and
        inext
        rw [show (0 &&& 1 : UInt32) = 0 by decide]
        iapply wp_brIfZero
        inext
        iapply wp_returnFromFunction
        inext
        iapply wp_value'
        iclear Hruntime Hglobal Hword
        ipureintro
        rfl)
    iframe

@[spec_of "rust-exported" "float_trunc::check"]
def FloatTruncSpec : Prop :=
  ∀ (x : UInt32),
    SmallStep.TerminatesWith (checkConfig x) (fun rs _store => rs = [])

@[proves Project.FloatTrunc.Spec.FloatTruncSpec]
theorem check_correct : FloatTruncSpec := check_terminatesWith

end Project.FloatTrunc.Spec
