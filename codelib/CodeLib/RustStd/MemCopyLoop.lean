import CodeLib.RustStd.MemArray
import CodeLib.SepLogic.SmallStepLifting
import CodeLib.SepLogic.SmallStepTotalLoop

/-!
# A verified copy loop over a `u32` array

The canonical word-by-word loop reads the `n` u32 words of the source and
writes them to a separately owned destination. Its iris-lean proof grows a
shared copied prefix while preserving both authoritative physical regions.
Exclusive ownership enforces disjointness, and an arbitrary Iris resource is
framed through every generated instruction.
-/

namespace Wasm

/-- Copy loop. Params `dst : i32`, `src : i32`, `n : i32`; local `i : i32`.
Copies `mem[src + 4*i]` to `mem[dst + 4*i]` for `i = 0 … n-1`. -/
def CopyWords : Program := [
  .const 0, .localSet 3,
  .loop 0 0 [
    .block 0 0 [
      .block 0 0 [
        .localGet 3, .localGet 2, .ltU, .br_if 0,
        .br 1
      ],
      .localGet 0, .localGet 3, .const 2, .shl, .add,
      .localGet 1, .localGet 3, .const 2, .shl, .add,
      .load32 0, .store32 0,
      .localGet 3, .const 1, .add, .localSet 3,
      .br 1 ] ]
]

/-! ## Authoritative small-step loop body -/

open Iris Iris.ProgramLogic Language.Notation
open Wasm.SepLogic

/-- Address calculations, load, and store performed by one copy iteration. -/
def CopyWordsLoadStoreIteration : Program := [
  .localGet 0, .localGet 3, .const 2, .shl, .add,
  .localGet 1, .localGet 3, .const 2, .shl, .add,
  .load32 0, .store32 0
]

def CopyWordsIncrementBackedge : Program := [
  .localGet 3, .const 1, .add, .localSet 3, .br 1
]

def CopyWordsInnerGuard : Program := [
  .localGet 3, .localGet 2, .ltU, .br_if 0, .br 1
]

def CopyWordsOuterBody : Program :=
  [.block 0 0 CopyWordsInnerGuard] ++
    CopyWordsLoadStoreIteration ++ CopyWordsIncrementBackedge

def CopyWordsLoopBody : Program := [
  .block 0 0 CopyWordsOuterBody
]

def copyWordsLoopFrame (continuation : Program) :
    Wasm.SmallStep.ControlFrame :=
  { kind := .loop
    paramArity := 0
    resultArity := 0
    body := CopyWordsLoopBody
    continuation
    belowStack := [] }

def copyWordsOuterFrame : Wasm.SmallStep.ControlFrame :=
  { kind := .block
    paramArity := 0
    resultArity := 0
    body := CopyWordsOuterBody
    continuation := []
    belowStack := [] }

def copyWordsInnerFrame : Wasm.SmallStep.ControlFrame :=
  { kind := .block
    paramArity := 0
    resultArity := 0
    body := CopyWordsInnerGuard
    continuation :=
      CopyWordsLoadStoreIteration ++ CopyWordsIncrementBackedge
    belowStack := [] }

theorem CopyWords_eq_structured :
    CopyWords = [.const 0, .localSet 3,
      .loop 0 0 CopyWordsLoopBody] := by
  rfl

/-- One real small-step copy iteration reads the next authoritative source
word, writes the destination, and preserves source ownership. -/
theorem copyWords_loadStoreIteration_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {α : Type} (R : IProp WasmHeapGF)
    (dst src n i : UInt32) (pre : List UInt32)
    (oldDst value : UInt32) (dstSuffix srcSuffix : List UInt32)
    (code : Program) (arity : Nat) (remainder : List Value)
    (controls : List Wasm.SmallStep.ControlFrame)
    (calls : List Wasm.SmallStep.CallFrame)
    (hpre : pre.length = i.toNat)
    (hdstRoom : dst.toNat + 4 * (i.toNat + 1) ≤ 4294967296)
    (hsrcRoom : src.toNat + 4 * (i.toNat + 1) ≤ 4294967296)
    (hcontinue :
      R ∗ arrayAt dst (pre ++ value :: dstSuffix) ∗
          arrayAt src (pre ++ value :: srcSuffix) ⊢
        WP (Wasm.SmallStep.Expr.running
          ⟨⟨[.i32 dst, .i32 src, .i32 n], [.i32 i], []⟩,
            code, arity, remainder, controls, calls⟩ :
          Wasm.SmallStep.Expr α) @ s; E {{ Φ }}) :
    R ∗ arrayAt dst (pre ++ oldDst :: dstSuffix) ∗
        arrayAt src (pre ++ value :: srcSuffix) ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 dst, .i32 src, .i32 n], [.i32 i], []⟩,
          CopyWordsLoadStoreIteration ++ code,
          arity, remainder, controls, calls⟩ :
        Wasm.SmallStep.Expr α) @ s; E {{ Φ }} := by
  let dstAddress : UInt32 := dst + 4 * UInt32.ofNat i.toNat
  let srcAddress : UInt32 := src + 4 * UInt32.ofNat i.toNat
  have hi : UInt32.ofNat i.toNat = i := by
    simp [UInt32.ofNat_toNat]
  have hdstAddress :
      (i <<< (2 % 32 : UInt32)) + dst = dstAddress := by
    rw [MemRegion.shl2_eq_mul4]
    dsimp only [dstAddress]
    rw [hi]
    exact UInt32.add_comm _ _
  have hsrcAddress :
      (i <<< (2 % 32 : UInt32)) + src = srcAddress := by
    rw [MemRegion.shl2_eq_mul4]
    dsimp only [srcAddress]
    rw [hi]
    exact UInt32.add_comm _ _
  have hdstNat : dstAddress.toNat = dst.toNat + 4 * i.toNat :=
    Mem.words32_slotAddr_toNat dst i.toNat (by omega)
  have hsrcNat : srcAddress.toNat = src.toNat + 4 * i.toNat :=
    Mem.words32_slotAddr_toNat src i.toNat (by omega)
  have addressSteps (address : UInt32)
      (hroom : address.toNat + 4 ≤ 4294967296) :
      (address + 1).toNat = address.toNat + 1 ∧
      (address + 2).toNat = address.toNat + 2 ∧
      (address + 3).toNat = address.toNat + 3 := by
    have step (k : Nat) (hk : k < 4294967296)
        (hfit : address.toNat + k < 4294967296) :
        (address + UInt32.ofNat k).toNat = address.toNat + k :=
      UInt32.add_ofNat_toNat_noWrap address k hk hfit
    exact ⟨by simpa using step 1 (by decide) (by omega),
      by simpa using step 2 (by decide) (by omega),
      by simpa using step 3 (by decide) (by omega)⟩
  obtain ⟨hd1, hd2, hd3⟩ :=
    addressSteps dstAddress (by rw [hdstNat]; omega)
  obtain ⟨hs1, hs2, hs3⟩ :=
    addressSteps srcAddress (by rw [hsrcNat]; omega)
  iintro ⟨HR, Hdst, Hsrc⟩
  ihave Hfocused :
      pointsTo_u32 (src + 4 * UInt32.ofNat pre.length) value ∗
      pointsTo_u32 (dst + 4 * UInt32.ofNat pre.length) oldDst ∗
      (pointsTo_u32 (src + 4 * UInt32.ofNat pre.length) value ∗
        pointsTo_u32 (dst + 4 * UInt32.ofNat pre.length) value -∗
        arrayAt dst (pre ++ value :: dstSuffix) ∗
          arrayAt src (pre ++ value :: srcSuffix)) $$ [Hdst Hsrc]
  · iapply arrayAt_copy_next dst src pre oldDst value dstSuffix srcSuffix
    iframe
  icases Hfocused with ⟨HsrcCell, Hrest⟩
  icases Hrest with ⟨HdstCell, Hreassemble⟩
  ihave HsrcCell' : pointsTo_u32 srcAddress value $$ [HsrcCell]
  · simp only [srcAddress]
    rw [← hpre]
    iexact HsrcCell
  ihave HdstCell' : pointsTo_u32 dstAddress oldDst $$ [HdstCell]
  · simp only [dstAddress]
    rw [← hpre]
    iexact HdstCell
  simp only [CopyWordsLoadStoreIteration, List.cons_append, List.nil_append]
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
  rw [hdstAddress]
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
  rw [hsrcAddress]
  ihave HsrcLater : ▷ pointsTo_u32 (srcAddress + 0) value $$ [HsrcCell']
  · inext
    simp only [UInt32.add_zero]
    iexact HsrcCell'
  iapply Wasm.SmallStep.wp_load32
      (address := srcAddress) (offset := 0) value
      (by simp) (by simpa using hs1) (by simpa using hs2)
      (by simpa using hs3) $$ HsrcLater
  inext
  iintro HsrcCell
  ihave HdstLater : ▷ pointsTo_u32 (dstAddress + 0) oldDst $$ [HdstCell']
  · inext
    simp only [UInt32.add_zero]
    iexact HdstCell'
  iapply Wasm.SmallStep.wp_store32
      (address := dstAddress) (offset := 0) (value := value) oldDst
      (by simp) (by simpa using hd1) (by simpa using hd2)
      (by simpa using hd3) $$ HdstLater
  inext
  iintro HdstCell
  ihave HsrcCell'' :
      pointsTo_u32 (src + 4 * UInt32.ofNat pre.length) value $$
      [HsrcCell]
  · simp only [UInt32.add_zero, srcAddress]
    rw [hpre]
    iexact HsrcCell
  ihave HdstCell'' :
      pointsTo_u32 (dst + 4 * UInt32.ofNat pre.length) value $$
      [HdstCell]
  · simp only [UInt32.add_zero, dstAddress]
    rw [hpre]
    iexact HdstCell
  ihave Harrays :
      arrayAt dst (pre ++ value :: dstSuffix) ∗
        arrayAt src (pre ++ value :: srcSuffix) $$
      [Hreassemble HsrcCell'' HdstCell'']
  · iapply Hreassemble
    iframe
  iapply hcontinue
  iframe

theorem copyWords_incrementBackedge_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {α : Type}
    (dst src n i : UInt32)
    (afterLoop : Program) (arity : Nat) (remainder : List Value)
    (outerControls : List Wasm.SmallStep.ControlFrame)
    (calls : List Wasm.SmallStep.CallFrame) :
    ▷ WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 dst, .i32 src, .i32 n], [.i32 (i + 1)], []⟩,
          CopyWordsLoopBody, arity, remainder,
          copyWordsLoopFrame afterLoop :: outerControls, calls⟩ :
        Wasm.SmallStep.Expr α) @ s; E {{ Φ }} ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 dst, .i32 src, .i32 n], [.i32 i], []⟩,
        CopyWordsIncrementBackedge, arity, remainder,
        copyWordsOuterFrame :: copyWordsLoopFrame afterLoop ::
          outerControls,
        calls⟩ : Wasm.SmallStep.Expr α) @ s; E {{ Φ }} := by
  iintro Hcontinue
  simp only [CopyWordsIncrementBackedge]
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
  simp only [copyWordsLoopFrame, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub, List.set, List.take_nil,
    List.nil_append]
  iexact Hcontinue

theorem copyWords_bodyTail_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {α : Type} (R : IProp WasmHeapGF)
    (dst src n i : UInt32) (pre : List UInt32)
    (oldDst value : UInt32) (dstSuffix srcSuffix : List UInt32)
    (afterLoop : Program) (arity : Nat) (remainder : List Value)
    (outerControls : List Wasm.SmallStep.ControlFrame)
    (calls : List Wasm.SmallStep.CallFrame)
    (hpre : pre.length = i.toNat)
    (hdstRoom : dst.toNat + 4 * (i.toNat + 1) ≤ 4294967296)
    (hsrcRoom : src.toNat + 4 * (i.toNat + 1) ≤ 4294967296)
    (hback :
      R ∗ arrayAt dst (pre ++ value :: dstSuffix) ∗
          arrayAt src (pre ++ value :: srcSuffix) ⊢
        ▷ WP (Wasm.SmallStep.Expr.running
          ⟨⟨[.i32 dst, .i32 src, .i32 n], [.i32 (i + 1)], []⟩,
            CopyWordsLoopBody, arity, remainder,
            copyWordsLoopFrame afterLoop :: outerControls, calls⟩ :
          Wasm.SmallStep.Expr α) @ s; E {{ Φ }}) :
    R ∗ arrayAt dst (pre ++ oldDst :: dstSuffix) ∗
        arrayAt src (pre ++ value :: srcSuffix) ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 dst, .i32 src, .i32 n], [.i32 i], []⟩,
          CopyWordsLoadStoreIteration ++ CopyWordsIncrementBackedge,
          arity, remainder,
          copyWordsOuterFrame :: copyWordsLoopFrame afterLoop ::
            outerControls,
          calls⟩ : Wasm.SmallStep.Expr α) @ s; E {{ Φ }} := by
  iapply copyWords_loadStoreIteration_wp R dst src n i pre oldDst value
    dstSuffix srcSuffix CopyWordsIncrementBackedge arity remainder
    (copyWordsOuterFrame :: copyWordsLoopFrame afterLoop :: outerControls)
    calls hpre hdstRoom hsrcRoom
  iintro Hresources
  iapply copyWords_incrementBackedge_wp dst src n i afterLoop arity
    remainder outerControls calls
  iapply hback
  iexact Hresources

theorem copyWords_guard_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {α : Type} (P : IProp WasmHeapGF)
    (dst src n i : UInt32)
    (afterLoop : Program) (arity : Nat) (remainder : List Value)
    (outerControls : List Wasm.SmallStep.ControlFrame)
    (calls : List Wasm.SmallStep.CallFrame)
    (hbody : i < n →
      P ⊢ WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 dst, .i32 src, .i32 n], [.i32 i], []⟩,
          CopyWordsLoadStoreIteration ++ CopyWordsIncrementBackedge,
          arity, remainder,
          copyWordsOuterFrame :: copyWordsLoopFrame afterLoop ::
            outerControls,
          calls⟩ : Wasm.SmallStep.Expr α) @ s; E {{ Φ }})
    (hexit : ¬ i < n →
      P ⊢ WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 dst, .i32 src, .i32 n], [.i32 i], []⟩,
          afterLoop, arity, remainder, outerControls, calls⟩ :
          Wasm.SmallStep.Expr α) @ s; E {{ Φ }}) :
    P ⊢ WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 dst, .i32 src, .i32 n], [.i32 i], []⟩,
        CopyWordsLoopBody, arity, remainder,
        copyWordsLoopFrame afterLoop :: outerControls, calls⟩ :
      Wasm.SmallStep.Expr α) @ s; E {{ Φ }} := by
  simp only [copyWordsOuterFrame, CopyWordsOuterBody,
    CopyWordsInnerGuard, List.cons_append, List.nil_append] at hbody
  iintro HP
  simp only [CopyWordsLoopBody]
  iapply Wasm.SmallStep.wp_block
  inext
  simp only [CopyWordsOuterBody, List.cons_append, List.nil_append]
  iapply Wasm.SmallStep.wp_block
  inext
  simp only [CopyWordsInnerGuard]
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
    simp only [copyWordsLoopFrame, List.drop_zero, List.take_nil,
      List.nil_append]
    iapply hexit hlt
    iexact HP

/-- Universal copy invariant: `pre` is already equal in both arrays;
`dstSuffix` and `srcSuffix` are the unprocessed tails, and their concatenation
with `pre` still denotes the original source sequence. -/
theorem copyWords_loopBody_invariant_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {α : Type} (R : IProp WasmHeapGF)
    (dst src n i : UInt32)
    (source pre dstSuffix srcSuffix : List UInt32)
    (afterLoop : Program) (arity : Nat) (remainder : List Value)
    (outerControls : List Wasm.SmallStep.ControlFrame)
    (calls : List Wasm.SmallStep.CallFrame)
    (hdstTotal : dst.toNat + 4 * n.toNat ≤ 4294967296)
    (hsrcTotal : src.toNat + 4 * n.toNat ≤ 4294967296)
    (hsourceLength : source.length = n.toNat)
    (hpre : pre.length = i.toNat)
    (hdstInv : pre.length + dstSuffix.length = n.toNat)
    (hsource : source = pre ++ srcSuffix)
    (hfinish :
      R ∗ arrayAt dst source ∗ arrayAt src source ⊢
        WP (Wasm.SmallStep.Expr.running
          ⟨⟨[.i32 dst, .i32 src, .i32 n], [.i32 n], []⟩,
            afterLoop, arity, remainder, outerControls, calls⟩ :
          Wasm.SmallStep.Expr α) @ s; E {{ Φ }}) :
    R ∗ arrayAt dst (pre ++ dstSuffix) ∗
        arrayAt src (pre ++ srcSuffix) ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 dst, .i32 src, .i32 n], [.i32 i], []⟩,
          CopyWordsLoopBody, arity, remainder,
          copyWordsLoopFrame afterLoop :: outerControls, calls⟩ :
        Wasm.SmallStep.Expr α) @ s; E {{ Φ }} := by
  iloeb as IH generalizing
    %i %pre %dstSuffix %srcSuffix %hpre %hdstInv %hsource
  let Kloop : IProp WasmHeapGF := iprop(
    ▷ ∀ (j : UInt32) (copied dstTail srcTail : List UInt32),
      ⌜copied.length = j.toNat⌝ -∗
      ⌜copied.length + dstTail.length = n.toNat⌝ -∗
      ⌜source = copied ++ srcTail⌝ -∗
      R ∗ arrayAt dst (copied ++ dstTail) ∗
          arrayAt src (copied ++ srcTail) -∗
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 dst, .i32 src, .i32 n], [.i32 j], []⟩,
          CopyWordsLoopBody, arity, remainder,
          copyWordsLoopFrame afterLoop :: outerControls, calls⟩ :
        Wasm.SmallStep.Expr α) @ s; E {{ Φ }})
  ihave IHtyped : □ Kloop $$ [IH]
  · simp only [Kloop]
    iexact IH
  let P : IProp WasmHeapGF :=
    iprop% □ Kloop ∗ R ∗ arrayAt dst (pre ++ dstSuffix) ∗
      arrayAt src (pre ++ srcSuffix)
  iintro ⟨HR, Harrays⟩
  icases Harrays with ⟨Hdst, Hsrc⟩
  iapply copyWords_guard_wp P dst src n i afterLoop arity remainder
    outerControls calls
  · intro hlt
    simp only [P]
    cases dstSuffix with
    | nil =>
        have hltNat : i.toNat < n.toNat := hlt
        simp only [List.length_nil, Nat.add_zero] at hdstInv
        omega
    | cons oldDst dstTail =>
      cases srcSuffix with
      | nil =>
          have hltNat : i.toNat < n.toNat := hlt
          have hsourceLen := congrArg List.length hsource
          simp only [List.length_append, List.length_nil, Nat.add_zero,
            hsourceLength] at hsourceLen
          omega
      | cons value srcTail =>
        have hltNat : i.toNat < n.toNat := hlt
        have hnext :
            (i + 1).toNat = i.toNat + 1 := by
          rw [UInt32.toNat_add]
          simp only [UInt32.reduceToNat]
          rw [Nat.mod_eq_of_lt
            (lt_of_le_of_lt (by omega) n.toNat_lt)]
        let copied' : List UInt32 := pre ++ [value]
        have hpreNext : copied'.length = (i + 1).toNat := by
          simp only [copied', List.length_append, List.length_singleton,
            hpre, hnext]
        have hdstNext :
            copied'.length + dstTail.length = n.toNat := by
          simp only [List.length_cons] at hdstInv
          omega
        have hsourceNext : source = copied' ++ srcTail := by
          rw [hsource]
          simp only [copied', List.append_assoc, List.singleton_append]
        let Rloop : IProp WasmHeapGF := iprop% □ Kloop ∗ R
        iintro Hcurrent
        icases Hcurrent with ⟨#IHcurrent, HcurrentRest⟩
        icases HcurrentRest with ⟨HRcurrent, HarraysCurrent⟩
        icases HarraysCurrent with ⟨HdstCurrent, HsrcCurrent⟩
        iapply copyWords_bodyTail_wp Rloop dst src n i pre oldDst value
          dstTail srcTail afterLoop arity remainder outerControls calls hpre
        · omega
        · omega
        · iintro Hresources
          ihave Hexpanded :
              (□ Kloop ∗ R) ∗
                arrayAt dst (pre ++ value :: dstTail) ∗
                arrayAt src (pre ++ value :: srcTail) $$ [Hresources]
          · simp only [Rloop]
            iexact Hresources
          icases Hexpanded with ⟨Hloop, Harrays'⟩
          icases Hloop with ⟨#IH', HR'⟩
          icases Harrays' with ⟨Hdst', Hsrc'⟩
          ispecialize IH' $$ %(i + 1) %copied' %dstTail %srcTail
            %hpreNext %hdstNext %hsourceNext
          iapply IH'
          isplitl [HR']
          · iexact HR'
          isplitl [Hdst']
          · simp only [copied', List.append_assoc, List.singleton_append]
            iexact Hdst'
          · simp only [copied', List.append_assoc, List.singleton_append]
            iexact Hsrc'
        · simp only [Rloop]
          isplitl [IHcurrent HRcurrent]
          · isplitl [IHcurrent]
            · iexact IHcurrent
            · iexact HRcurrent
          isplitl [HdstCurrent]
          · iexact HdstCurrent
          · iexact HsrcCurrent
  · intro hnlt
    simp only [P]
    have hnltNat : ¬ i.toNat < n.toNat := by
      simpa only [UInt32.lt_iff_toNat_lt] using hnlt
    have hiNat : i.toNat = n.toNat := by
      rw [← hpre] at hnltNat
      omega
    have hi : i = n := UInt32.toNat_inj.mp hiNat
    subst i
    have hpreLen : pre.length = n.toNat := hpre
    have hdstNil : dstSuffix = [] := by
      apply List.eq_nil_of_length_eq_zero
      omega
    have hsrcNil : srcSuffix = [] := by
      have hsourceLen := congrArg List.length hsource
      simp only [List.length_append, hsourceLength] at hsourceLen
      exact List.eq_nil_of_length_eq_zero (by omega)
    subst dstSuffix
    subst srcSuffix
    have hpreSource : pre = source := by
      simpa using hsource.symm
    subst pre
    iintro ⟨#_IH', Hrest⟩
    icases Hrest with ⟨HR', Harrays'⟩
    icases Harrays' with ⟨Hdst', Hsrc'⟩
    iapply hfinish
    isplitl [HR']
    · iexact HR'
    isplitl [Hdst']
    · simp only [List.append_nil]
      iexact Hdst'
    · simp only [List.append_nil]
      iexact Hsrc'
  · simp only [P]
    iframe

theorem copyWords_loop_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {α : Type} (R : IProp WasmHeapGF)
    (dst src n : UInt32)
    (destination source : List UInt32)
    (afterLoop : Program) (arity : Nat) (remainder : List Value)
    (outerControls : List Wasm.SmallStep.ControlFrame)
    (calls : List Wasm.SmallStep.CallFrame)
    (hdestinationLength : destination.length = n.toNat)
    (hsourceLength : source.length = n.toNat)
    (hdstTotal : dst.toNat + 4 * n.toNat ≤ 4294967296)
    (hsrcTotal : src.toNat + 4 * n.toNat ≤ 4294967296)
    (hfinish :
      R ∗ arrayAt dst source ∗ arrayAt src source ⊢
        WP (Wasm.SmallStep.Expr.running
          ⟨⟨[.i32 dst, .i32 src, .i32 n], [.i32 n], []⟩,
            afterLoop, arity, remainder, outerControls, calls⟩ :
          Wasm.SmallStep.Expr α) @ s; E {{ Φ }}) :
    R ∗ arrayAt dst destination ∗ arrayAt src source ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 dst, .i32 src, .i32 n], [.i32 0], []⟩,
          [.loop 0 0 CopyWordsLoopBody] ++ afterLoop,
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
         body := CopyWordsLoopBody
         continuation := afterLoop
         belowStack :=
           (⟨[.i32 dst, .i32 src, .i32 n], [.i32 0], []⟩ :
             Locals).values.drop 0 } :
        Wasm.SmallStep.ControlFrame) =
      copyWordsLoopFrame afterLoop := by
    rfl
  rw [hframe]
  have hbody := copyWords_loopBody_invariant_wp R dst src n 0 source
    [] destination source afterLoop arity remainder outerControls calls
    hdstTotal hsrcTotal hsourceLength
    (by simp) (by simpa using hdestinationLength) (by simp) hfinish
  iapply hbody
  simp only [List.nil_append]
  iexact Hresources

/-- Full universal Iris rule for the generated disjoint u32 copy loop. -/
theorem copyWords_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {α : Type} (R : IProp WasmHeapGF)
    (dst src n initialIndex : UInt32)
    (destination source : List UInt32)
    (afterLoop : Program) (arity : Nat) (remainder : List Value)
    (controls : List Wasm.SmallStep.ControlFrame)
    (calls : List Wasm.SmallStep.CallFrame)
    (hdestinationLength : destination.length = n.toNat)
    (hsourceLength : source.length = n.toNat)
    (hdstTotal : dst.toNat + 4 * n.toNat ≤ 4294967296)
    (hsrcTotal : src.toNat + 4 * n.toNat ≤ 4294967296)
    (hfinish :
      R ∗ arrayAt dst source ∗ arrayAt src source ⊢
        WP (Wasm.SmallStep.Expr.running
          ⟨⟨[.i32 dst, .i32 src, .i32 n], [.i32 n], []⟩,
            afterLoop, arity, remainder, controls, calls⟩ :
          Wasm.SmallStep.Expr α) @ s; E {{ Φ }}) :
    R ∗ arrayAt dst destination ∗ arrayAt src source ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 dst, .i32 src, .i32 n],
            [.i32 initialIndex], []⟩,
          CopyWords ++ afterLoop,
          arity, remainder, controls, calls⟩ :
        Wasm.SmallStep.Expr α) @ s; E {{ Φ }} := by
  iintro Hresources
  rw [CopyWords_eq_structured]
  simp only [List.cons_append, List.nil_append]
  iapply Wasm.SmallStep.wp_const
  inext
  iapply Wasm.SmallStep.wp_localSet rfl
  inext
  simp only [List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub, List.set]
  have hloop := copyWords_loop_wp R dst src n destination source
    afterLoop arity remainder controls calls hdestinationLength hsourceLength
    hdstTotal hsrcTotal hfinish
  simp only [List.cons_append, List.nil_append] at hloop
  iapply hloop
  iexact Hresources

/-! ## Total small-step correctness

The rules above are partial: Löb induction proves that the loop copies
correctly *if* it finishes. The total layer below replays the same local
reasoning with `twp` rules and closes the loop with the well-founded variant
`n - i`, so it also proves the loop finishes. -/

/-- Family index for the total copy loop: the loop counter together with the
copied prefix and the two unprocessed tails. -/
structure CopyWordsLoopState where
  index : UInt32
  copied : List UInt32
  dstTail : List UInt32
  srcTail : List UInt32

/-- Total counterpart of `copyWords_loadStoreIteration_wp`. -/
theorem copyWords_loadStoreIteration_twp
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {α : Type} (R : IProp WasmHeapGF)
    (dst src n i : UInt32) (pre : List UInt32)
    (oldDst value : UInt32) (dstSuffix srcSuffix : List UInt32)
    (code : Program) (arity : Nat) (remainder : List Value)
    (controls : List Wasm.SmallStep.ControlFrame)
    (calls : List Wasm.SmallStep.CallFrame)
    (hpre : pre.length = i.toNat)
    (hdstRoom : dst.toNat + 4 * (i.toNat + 1) ≤ 4294967296)
    (hsrcRoom : src.toNat + 4 * (i.toNat + 1) ≤ 4294967296)
    (hcontinue :
      R ∗ arrayAt dst (pre ++ value :: dstSuffix) ∗
          arrayAt src (pre ++ value :: srcSuffix) ⊢
        WP (Wasm.SmallStep.Expr.running
          ⟨⟨[.i32 dst, .i32 src, .i32 n], [.i32 i], []⟩,
            code, arity, remainder, controls, calls⟩ :
          Wasm.SmallStep.Expr α) @ s; E [{ Φ }]) :
    R ∗ arrayAt dst (pre ++ oldDst :: dstSuffix) ∗
        arrayAt src (pre ++ value :: srcSuffix) ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 dst, .i32 src, .i32 n], [.i32 i], []⟩,
          CopyWordsLoadStoreIteration ++ code,
          arity, remainder, controls, calls⟩ :
        Wasm.SmallStep.Expr α) @ s; E [{ Φ }] := by
  let dstAddress : UInt32 := dst + 4 * UInt32.ofNat i.toNat
  let srcAddress : UInt32 := src + 4 * UInt32.ofNat i.toNat
  have hi : UInt32.ofNat i.toNat = i := by
    simp [UInt32.ofNat_toNat]
  have hdstAddress :
      (i <<< (2 % 32 : UInt32)) + dst = dstAddress := by
    rw [MemRegion.shl2_eq_mul4]
    dsimp only [dstAddress]
    rw [hi]
    exact UInt32.add_comm _ _
  have hsrcAddress :
      (i <<< (2 % 32 : UInt32)) + src = srcAddress := by
    rw [MemRegion.shl2_eq_mul4]
    dsimp only [srcAddress]
    rw [hi]
    exact UInt32.add_comm _ _
  have hdstNat : dstAddress.toNat = dst.toNat + 4 * i.toNat :=
    Mem.words32_slotAddr_toNat dst i.toNat (by omega)
  have hsrcNat : srcAddress.toNat = src.toNat + 4 * i.toNat :=
    Mem.words32_slotAddr_toNat src i.toNat (by omega)
  have addressSteps (address : UInt32)
      (hroom : address.toNat + 4 ≤ 4294967296) :
      (address + 1).toNat = address.toNat + 1 ∧
      (address + 2).toNat = address.toNat + 2 ∧
      (address + 3).toNat = address.toNat + 3 := by
    have step (k : Nat) (hk : k < 4294967296)
        (hfit : address.toNat + k < 4294967296) :
        (address + UInt32.ofNat k).toNat = address.toNat + k :=
      UInt32.add_ofNat_toNat_noWrap address k hk hfit
    exact ⟨by simpa using step 1 (by decide) (by omega),
      by simpa using step 2 (by decide) (by omega),
      by simpa using step 3 (by decide) (by omega)⟩
  obtain ⟨hd1, hd2, hd3⟩ :=
    addressSteps dstAddress (by rw [hdstNat]; omega)
  obtain ⟨hs1, hs2, hs3⟩ :=
    addressSteps srcAddress (by rw [hsrcNat]; omega)
  iintro ⟨HR, Hdst, Hsrc⟩
  ihave Hfocused :
      pointsTo_u32 (src + 4 * UInt32.ofNat pre.length) value ∗
      pointsTo_u32 (dst + 4 * UInt32.ofNat pre.length) oldDst ∗
      (pointsTo_u32 (src + 4 * UInt32.ofNat pre.length) value ∗
        pointsTo_u32 (dst + 4 * UInt32.ofNat pre.length) value -∗
        arrayAt dst (pre ++ value :: dstSuffix) ∗
          arrayAt src (pre ++ value :: srcSuffix)) $$ [Hdst Hsrc]
  · iapply arrayAt_copy_next dst src pre oldDst value dstSuffix srcSuffix
    iframe
  icases Hfocused with ⟨HsrcCell, Hrest⟩
  icases Hrest with ⟨HdstCell, Hreassemble⟩
  ihave HsrcCell' : pointsTo_u32 srcAddress value $$ [HsrcCell]
  · simp only [srcAddress]
    rw [← hpre]
    iexact HsrcCell
  ihave HdstCell' : pointsTo_u32 dstAddress oldDst $$ [HdstCell]
  · simp only [dstAddress]
    rw [← hpre]
    iexact HdstCell
  simp only [CopyWordsLoadStoreIteration, List.cons_append, List.nil_append]
  iapply Wasm.SmallStep.twp_localGet rfl
  iapply Wasm.SmallStep.twp_localGet rfl
  iapply Wasm.SmallStep.twp_const
  iapply Wasm.SmallStep.twp_shl
  iapply Wasm.SmallStep.twp_add
  rw [hdstAddress]
  iapply Wasm.SmallStep.twp_localGet rfl
  iapply Wasm.SmallStep.twp_localGet rfl
  iapply Wasm.SmallStep.twp_const
  iapply Wasm.SmallStep.twp_shl
  iapply Wasm.SmallStep.twp_add
  rw [hsrcAddress]
  ihave HsrcAt : pointsTo_u32 (srcAddress + 0) value $$ [HsrcCell']
  · simp only [UInt32.add_zero]
    iexact HsrcCell'
  iapply Wasm.SmallStep.twp_load32
      (address := srcAddress) (offset := 0) value
      (by simp) (by simpa using hs1) (by simpa using hs2)
      (by simpa using hs3) $$ HsrcAt
  iintro HsrcCell
  ihave HdstAt : pointsTo_u32 (dstAddress + 0) oldDst $$ [HdstCell']
  · simp only [UInt32.add_zero]
    iexact HdstCell'
  iapply Wasm.SmallStep.twp_store32
      (address := dstAddress) (offset := 0) (value := value) oldDst
      (by simp) (by simpa using hd1) (by simpa using hd2)
      (by simpa using hd3) $$ HdstAt
  iintro HdstCell
  ihave HsrcCell'' :
      pointsTo_u32 (src + 4 * UInt32.ofNat pre.length) value $$
      [HsrcCell]
  · simp only [UInt32.add_zero, srcAddress]
    rw [hpre]
    iexact HsrcCell
  ihave HdstCell'' :
      pointsTo_u32 (dst + 4 * UInt32.ofNat pre.length) value $$
      [HdstCell]
  · simp only [UInt32.add_zero, dstAddress]
    rw [hpre]
    iexact HdstCell
  ihave Harrays :
      arrayAt dst (pre ++ value :: dstSuffix) ∗
        arrayAt src (pre ++ value :: srcSuffix) $$
      [Hreassemble HsrcCell'' HdstCell'']
  · iapply Hreassemble
    iframe
  iapply hcontinue
  iframe

/-- Total counterpart of `copyWords_incrementBackedge_wp`. -/
theorem copyWords_incrementBackedge_twp
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {α : Type}
    (dst src n i : UInt32)
    (afterLoop : Program) (arity : Nat) (remainder : List Value)
    (outerControls : List Wasm.SmallStep.ControlFrame)
    (calls : List Wasm.SmallStep.CallFrame) :
    WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 dst, .i32 src, .i32 n], [.i32 (i + 1)], []⟩,
          CopyWordsLoopBody, arity, remainder,
          copyWordsLoopFrame afterLoop :: outerControls, calls⟩ :
        Wasm.SmallStep.Expr α) @ s; E [{ Φ }] ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 dst, .i32 src, .i32 n], [.i32 i], []⟩,
        CopyWordsIncrementBackedge, arity, remainder,
        copyWordsOuterFrame :: copyWordsLoopFrame afterLoop ::
          outerControls,
        calls⟩ : Wasm.SmallStep.Expr α) @ s; E [{ Φ }] := by
  iintro Hcontinue
  simp only [CopyWordsIncrementBackedge]
  iapply Wasm.SmallStep.twp_localGet rfl
  iapply Wasm.SmallStep.twp_const
  iapply Wasm.SmallStep.twp_add
  rw [UInt32.add_comm 1 i]
  iapply Wasm.SmallStep.twp_localSet rfl
  iapply Wasm.SmallStep.twp_br (by rfl)
  simp only [copyWordsLoopFrame, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub, List.set, List.take_nil,
    List.nil_append]
  iexact Hcontinue

/-- Total counterpart of `copyWords_bodyTail_wp`. -/
theorem copyWords_bodyTail_twp
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {α : Type} (R : IProp WasmHeapGF)
    (dst src n i : UInt32) (pre : List UInt32)
    (oldDst value : UInt32) (dstSuffix srcSuffix : List UInt32)
    (afterLoop : Program) (arity : Nat) (remainder : List Value)
    (outerControls : List Wasm.SmallStep.ControlFrame)
    (calls : List Wasm.SmallStep.CallFrame)
    (hpre : pre.length = i.toNat)
    (hdstRoom : dst.toNat + 4 * (i.toNat + 1) ≤ 4294967296)
    (hsrcRoom : src.toNat + 4 * (i.toNat + 1) ≤ 4294967296)
    (hback :
      R ∗ arrayAt dst (pre ++ value :: dstSuffix) ∗
          arrayAt src (pre ++ value :: srcSuffix) ⊢
        WP (Wasm.SmallStep.Expr.running
          ⟨⟨[.i32 dst, .i32 src, .i32 n], [.i32 (i + 1)], []⟩,
            CopyWordsLoopBody, arity, remainder,
            copyWordsLoopFrame afterLoop :: outerControls, calls⟩ :
          Wasm.SmallStep.Expr α) @ s; E [{ Φ }]) :
    R ∗ arrayAt dst (pre ++ oldDst :: dstSuffix) ∗
        arrayAt src (pre ++ value :: srcSuffix) ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 dst, .i32 src, .i32 n], [.i32 i], []⟩,
          CopyWordsLoadStoreIteration ++ CopyWordsIncrementBackedge,
          arity, remainder,
          copyWordsOuterFrame :: copyWordsLoopFrame afterLoop ::
            outerControls,
          calls⟩ : Wasm.SmallStep.Expr α) @ s; E [{ Φ }] := by
  iapply copyWords_loadStoreIteration_twp R dst src n i pre oldDst value
    dstSuffix srcSuffix CopyWordsIncrementBackedge arity remainder
    (copyWordsOuterFrame :: copyWordsLoopFrame afterLoop :: outerControls)
    calls hpre hdstRoom hsrcRoom
  iintro Hresources
  iapply copyWords_incrementBackedge_twp dst src n i afterLoop arity
    remainder outerControls calls
  iapply hback
  iexact Hresources

/-- Total counterpart of `copyWords_guard_wp`. -/
theorem copyWords_guard_twp
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {α : Type} (P : IProp WasmHeapGF)
    (dst src n i : UInt32)
    (afterLoop : Program) (arity : Nat) (remainder : List Value)
    (outerControls : List Wasm.SmallStep.ControlFrame)
    (calls : List Wasm.SmallStep.CallFrame)
    (hbody : i < n →
      P ⊢ WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 dst, .i32 src, .i32 n], [.i32 i], []⟩,
          CopyWordsLoadStoreIteration ++ CopyWordsIncrementBackedge,
          arity, remainder,
          copyWordsOuterFrame :: copyWordsLoopFrame afterLoop ::
            outerControls,
          calls⟩ : Wasm.SmallStep.Expr α) @ s; E [{ Φ }])
    (hexit : ¬ i < n →
      P ⊢ WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 dst, .i32 src, .i32 n], [.i32 i], []⟩,
          afterLoop, arity, remainder, outerControls, calls⟩ :
          Wasm.SmallStep.Expr α) @ s; E [{ Φ }]) :
    P ⊢ WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 dst, .i32 src, .i32 n], [.i32 i], []⟩,
        CopyWordsLoopBody, arity, remainder,
        copyWordsLoopFrame afterLoop :: outerControls, calls⟩ :
      Wasm.SmallStep.Expr α) @ s; E [{ Φ }] := by
  simp only [copyWordsOuterFrame, CopyWordsOuterBody,
    CopyWordsInnerGuard, List.cons_append, List.nil_append] at hbody
  iintro HP
  simp only [CopyWordsLoopBody]
  iapply Wasm.SmallStep.twp_block
  simp only [CopyWordsOuterBody, List.cons_append, List.nil_append]
  iapply Wasm.SmallStep.twp_block
  simp only [CopyWordsInnerGuard]
  iapply Wasm.SmallStep.twp_localGet rfl
  iapply Wasm.SmallStep.twp_localGet rfl
  by_cases hlt : i < n
  · iapply Wasm.SmallStep.twp_ltU (result := 1) (by simp [hlt])
    iapply Wasm.SmallStep.twp_brIf (by decide) (by rfl)
    simp only [List.drop_zero, List.take_nil, List.nil_append]
    iapply hbody hlt
    iexact HP
  · iapply Wasm.SmallStep.twp_ltU (result := 0) (by simp [hlt])
    iapply Wasm.SmallStep.twp_brIfZero
    iapply Wasm.SmallStep.twp_br (by rfl)
    iapply Wasm.SmallStep.twp_exitControl rfl
    simp only [copyWordsLoopFrame, List.drop_zero, List.take_nil,
      List.nil_append]
    iapply hexit hlt
    iexact HP

/-- The copy loop terminates and copies: `n - i` strictly decreases across the
back edge, so the well-founded family rule closes the proof without a
later. -/
theorem copyWords_loop_twp
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {α : Type} (R : IProp WasmHeapGF)
    (dst src n : UInt32)
    (destination source : List UInt32)
    (afterLoop : Program) (arity : Nat) (remainder : List Value)
    (outerControls : List Wasm.SmallStep.ControlFrame)
    (calls : List Wasm.SmallStep.CallFrame)
    (hdestinationLength : destination.length = n.toNat)
    (hsourceLength : source.length = n.toNat)
    (hdstTotal : dst.toNat + 4 * n.toNat ≤ 4294967296)
    (hsrcTotal : src.toNat + 4 * n.toNat ≤ 4294967296)
    (hfinish :
      R ∗ arrayAt dst source ∗ arrayAt src source ⊢
        WP (Wasm.SmallStep.Expr.running
          ⟨⟨[.i32 dst, .i32 src, .i32 n], [.i32 n], []⟩,
            afterLoop, arity, remainder, outerControls, calls⟩ :
          Wasm.SmallStep.Expr α) @ s; E [{ Φ }]) :
    R ∗ arrayAt dst destination ∗ arrayAt src source ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 dst, .i32 src, .i32 n], [.i32 0], []⟩,
          [.loop 0 0 CopyWordsLoopBody] ++ afterLoop,
          arity, remainder, outerControls, calls⟩ :
        Wasm.SmallStep.Expr α) @ s; E [{ Φ }] := by
  let Inv : CopyWordsLoopState → IProp WasmHeapGF := fun state => iprop%
    ⌜state.copied.length = state.index.toNat⌝ ∗
    ⌜state.copied.length + state.dstTail.length = n.toNat⌝ ∗
    ⌜source = state.copied ++ state.srcTail⌝ ∗
    R ∗ arrayAt dst (state.copied ++ state.dstTail) ∗
      arrayAt src (state.copied ++ state.srcTail)
  simp only [List.cons_append, List.nil_append]
  iintro ⟨HR, Hdst, Hsrc⟩
  iapply Wasm.SmallStep.twp_loop_wf_family
    (ι := CopyWordsLoopState)
    (measure := fun state => n.toNat - state.index.toNat)
    (locals := fun state =>
      ⟨[.i32 dst, .i32 src, .i32 n], [.i32 state.index], []⟩)
    (I := Inv)
    (initial := ⟨0, [], destination, source⟩)
    (initialLocals := ⟨[.i32 dst, .i32 src, .i32 n], [.i32 0], []⟩)
    (body := CopyWordsLoopBody)
    (code := afterLoop)
    rfl rfl
  · intro state
    simp only [Inv]
    iintro IH ⟨%hcopied, %hdstInv, %hsource, HR, Hdst, Hsrc⟩
    simp only [Wasm.SmallStep.loopBodyExpr, List.drop_zero]
    have hframe :
        ({ kind := .loop
           paramArity := 0
           resultArity := 0
           body := CopyWordsLoopBody
           continuation := afterLoop
           belowStack := ([] : List Value) } :
          Wasm.SmallStep.ControlFrame) =
        copyWordsLoopFrame afterLoop := rfl
    rw [hframe]
    iapply copyWords_guard_twp
      (iprop% (∀ (j : CopyWordsLoopState),
          ⌜n.toNat - j.index.toNat < n.toNat - state.index.toNat⌝ -∗
          Inv j -∗
          WP (Wasm.SmallStep.Expr.running
            ⟨⟨[.i32 dst, .i32 src, .i32 n], [.i32 j.index], []⟩,
              CopyWordsLoopBody, arity, remainder,
              copyWordsLoopFrame afterLoop :: outerControls, calls⟩ :
            Wasm.SmallStep.Expr α) @ s; E [{ Φ }]) ∗
        R ∗ arrayAt dst (state.copied ++ state.dstTail) ∗
          arrayAt src (state.copied ++ state.srcTail))
      dst src n state.index afterLoop arity remainder outerControls calls
    · intro hlt
      have hltNat : state.index.toNat < n.toNat := hlt
      cases hdst : state.dstTail with
      | nil =>
          rw [hdst] at hdstInv
          simp only [List.length_nil, Nat.add_zero] at hdstInv
          omega
      | cons oldDst dstTail =>
        cases hsrc : state.srcTail with
        | nil =>
            have hsourceLen := congrArg List.length hsource
            rw [hsrc] at hsourceLen
            simp only [List.length_append, List.length_nil, Nat.add_zero,
              hsourceLength] at hsourceLen
            omega
        | cons value srcTail =>
          have hnext : (state.index + 1).toNat = state.index.toNat + 1 := by
            rw [UInt32.toNat_add]
            simp only [UInt32.reduceToNat]
            rw [Nat.mod_eq_of_lt
              (lt_of_le_of_lt (by omega) n.toNat_lt)]
          let next : CopyWordsLoopState :=
            ⟨state.index + 1, state.copied ++ [value], dstTail, srcTail⟩
          have hcopiedNext :
              next.copied.length = next.index.toNat := by
            simp only [next, List.length_append, List.length_singleton,
              hcopied, hnext]
          have hdstNext :
              next.copied.length + next.dstTail.length = n.toNat := by
            rw [hdst] at hdstInv
            simp only [List.length_cons] at hdstInv
            simp only [next, List.length_append, List.length_singleton,
              hcopied]
            omega
          have hsourceNext : source = next.copied ++ next.srcTail := by
            rw [hsource, hsrc]
            simp only [next, List.append_assoc, List.singleton_append]
          have hmeasure :
              n.toNat - next.index.toNat < n.toNat - state.index.toNat := by
            simp only [next, hnext]
            omega
          iintro ⟨IHcurrent, HRcurrent, HdstCurrent, HsrcCurrent⟩
          iapply copyWords_bodyTail_twp
            (iprop% (∀ (j : CopyWordsLoopState),
                ⌜n.toNat - j.index.toNat <
                  n.toNat - state.index.toNat⌝ -∗
                Inv j -∗
                WP (Wasm.SmallStep.Expr.running
                  ⟨⟨[.i32 dst, .i32 src, .i32 n], [.i32 j.index], []⟩,
                    CopyWordsLoopBody, arity, remainder,
                    copyWordsLoopFrame afterLoop :: outerControls, calls⟩ :
                  Wasm.SmallStep.Expr α) @ s; E [{ Φ }]) ∗ R)
            dst src n state.index state.copied oldDst value dstTail srcTail
            afterLoop arity remainder outerControls calls hcopied
            (by omega) (by omega)
          · iintro ⟨⟨IH', HR'⟩, Hdst', Hsrc'⟩
            ispecialize IH' $$ %next %hmeasure
            iapply IH'
            simp only [Inv, next]
            isplitr
            · ipureintro
              exact hcopiedNext
            isplitr
            · ipureintro
              exact hdstNext
            isplitr
            · ipureintro
              exact hsourceNext
            isplitl [HR']
            · iexact HR'
            isplitl [Hdst']
            · simp only [List.append_assoc, List.singleton_append]
              iexact Hdst'
            · simp only [List.append_assoc, List.singleton_append]
              iexact Hsrc'
          · isplitl [IHcurrent HRcurrent]
            · isplitl [IHcurrent]
              · iexact IHcurrent
              · iexact HRcurrent
            isplitl [HdstCurrent]
            · iexact HdstCurrent
            · iexact HsrcCurrent
    · intro hnlt
      have hnltNat : ¬ state.index.toNat < n.toNat := by
        simpa only [UInt32.lt_iff_toNat_lt] using hnlt
      have hindexNat : state.index.toNat = n.toNat := by
        rw [← hcopied] at hnltNat
        omega
      have hindex : state.index = n := UInt32.toNat_inj.mp hindexNat
      have hdstNil : state.dstTail = [] := by
        apply List.eq_nil_of_length_eq_zero
        omega
      have hsrcNil : state.srcTail = [] := by
        have hsourceLen := congrArg List.length hsource
        simp only [List.length_append, hsourceLength] at hsourceLen
        exact List.eq_nil_of_length_eq_zero (by omega)
      have hcopiedSource : state.copied = source := by
        rw [hsource, hsrcNil, List.append_nil]
      rw [hindex, hdstNil, hsrcNil]
      simp only [List.append_nil]
      rw [hcopiedSource]
      iintro ⟨_IH, HR', Hdst', Hsrc'⟩
      iapply hfinish
      isplitl [HR']
      · iexact HR'
      isplitl [Hdst']
      · iexact Hdst'
      · iexact Hsrc'
    · simp only [Inv]
      iframe
  · simp only [Inv]
    isplitr
    · ipureintro
      simp
    isplitr
    · ipureintro
      simpa using hdestinationLength
    isplitr
    · ipureintro
      simp
    isplitl [HR]
    · iexact HR
    isplitl [Hdst]
    · simp only [List.nil_append]
      iexact Hdst
    · simp only [List.nil_append]
      iexact Hsrc

/-- Total Iris rule for the generated disjoint u32 copy loop: the loop always
finishes, and on finishing the destination holds the source words. -/
theorem copyWords_smallStep_twp
    [Wasm.SmallStep.WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {α : Type} (R : IProp WasmHeapGF)
    (dst src n initialIndex : UInt32)
    (destination source : List UInt32)
    (afterLoop : Program) (arity : Nat) (remainder : List Value)
    (controls : List Wasm.SmallStep.ControlFrame)
    (calls : List Wasm.SmallStep.CallFrame)
    (hdestinationLength : destination.length = n.toNat)
    (hsourceLength : source.length = n.toNat)
    (hdstTotal : dst.toNat + 4 * n.toNat ≤ 4294967296)
    (hsrcTotal : src.toNat + 4 * n.toNat ≤ 4294967296)
    (hfinish :
      R ∗ arrayAt dst source ∗ arrayAt src source ⊢
        WP (Wasm.SmallStep.Expr.running
          ⟨⟨[.i32 dst, .i32 src, .i32 n], [.i32 n], []⟩,
            afterLoop, arity, remainder, controls, calls⟩ :
          Wasm.SmallStep.Expr α) @ s; E [{ Φ }]) :
    R ∗ arrayAt dst destination ∗ arrayAt src source ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 dst, .i32 src, .i32 n],
            [.i32 initialIndex], []⟩,
          CopyWords ++ afterLoop,
          arity, remainder, controls, calls⟩ :
        Wasm.SmallStep.Expr α) @ s; E [{ Φ }] := by
  iintro Hresources
  rw [CopyWords_eq_structured]
  simp only [List.cons_append, List.nil_append]
  iapply Wasm.SmallStep.twp_const
  iapply Wasm.SmallStep.twp_localSet rfl
  simp only [List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub, List.set]
  have hloop := copyWords_loop_twp R dst src n destination source
    afterLoop arity remainder controls calls hdestinationLength hsourceLength
    hdstTotal hsrcTotal hfinish
  simp only [List.cons_append, List.nil_append] at hloop
  iapply hloop
  iexact Hresources

end Wasm
