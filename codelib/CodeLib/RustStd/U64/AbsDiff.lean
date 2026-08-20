import CodeLib.SepLogic.SmallStepAdequacy

/-!
# `u64::abs_diff` — reusable body theorem

The inner `core::num::<impl u64>::abs_diff`, compiled at `opt-level = 0`: a real,
separately-called function, so other crates reuse this theorem through the `call`
rule. Its reusable contract is stated with iris-lean's WP over the authoritative
small-step language and is closed to `SmallStep.PartiallyMeets` by adequacy.
-/

namespace Wasm.RustStd.U64

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic

/-- Verbatim opt-0 body of `absDiff`. -/
def absDiffBody : Program :=
  [
  .globalGet 0,
  .const (16 : UInt32),
  .sub,
  .localSet 2,
  .block 0 0 [
    .block 0 0 [
      .localGet 0,
      .localGet 1,
      .ltUI64,
      .const (1 : UInt32),
      .and,
      .br_if 0,
      .localGet 2,
      .localGet 0,
      .localGet 1,
      .subI64,
      .store64 (8 : UInt32),
      .br 1
    ],
    .localGet 2,
    .localGet 1,
    .localGet 0,
    .subI64,
    .store64 (8 : UInt32)
  ],
  .localGet 2,
  .load64 (8 : UInt32),
  .ret
]

def absDiffFunc : Function :=
  { params := [.i64, .i64], locals := [.i32], body := absDiffBody, results := [.i64] }

set_option maxHeartbeats 4000000 in
/-- Iris/small-step specification of the same body. The scratch word is tied
to physical memory through authoritative byte ownership; no legacy
interpreter or custom WP definition occurs in this theorem. -/
theorem absDiff_smallStep_wp_to_return
    [Wasm.SmallStep.WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit))
    (calls : List Wasm.SmallStep.CallFrame)
    (sp : UInt32) (a b oldScratch : UInt64)
    (hlo : 16 ≤ sp.toNat)
    (hroom : (sp - 16).toNat + 16 ≤ 4294967296)
    (hreturn :
      R ∗ globalPointsToAt 0 0 (.i32 sp) ∗
        pointsTo_u64 0 ((sp - 16) + 8)
          (if a < b then b - a else a - b) ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i64 a, .i64 b], [.i32 (sp - 16)],
            [.i64 (if a < b then b - a else a - b)]⟩,
          [.ret], 1, [], [], calls⟩ :
          Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }}) :
    R ∗ globalPointsToAt 0 0 (.i32 sp) ∗
      pointsTo_u64 0 ((sp - 16) + 8) oldScratch ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i64 a, .i64 b], [.i32 0], []⟩,
        absDiffBody, 1, [], [], calls⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E
      {{ Φ }} := by
  have hle : (16 : UInt32) ≤ sp :=
    UInt32.le_iff_toNat_le.mpr (by simpa using hlo)
  have hsub : (sp - 16).toNat = sp.toNat - 16 :=
    UInt32.toNat_sub_of_le sp 16 hle
  have h8 : ((sp - 16) + 8).toNat = (sp - 16).toNat + 8 := by
    simpa using UInt32.add_ofNat_toNat_noWrap (sp - 16) 8
      (by omega) (by omega)
  have h9 : (((sp - 16) + 8) + 1).toNat =
      ((sp - 16) + 8).toNat + 1 := by
    simpa using UInt32.add_ofNat_toNat_noWrap ((sp - 16) + 8) 1
      (by omega) (by omega)
  have h10 : (((sp - 16) + 8) + 2).toNat =
      ((sp - 16) + 8).toNat + 2 := by
    simpa using UInt32.add_ofNat_toNat_noWrap ((sp - 16) + 8) 2
      (by omega) (by omega)
  have h11 : (((sp - 16) + 8) + 3).toNat =
      ((sp - 16) + 8).toNat + 3 := by
    simpa using UInt32.add_ofNat_toNat_noWrap ((sp - 16) + 8) 3
      (by omega) (by omega)
  have h12 : (((sp - 16) + 8) + 4).toNat =
      ((sp - 16) + 8).toNat + 4 := by
    simpa using UInt32.add_ofNat_toNat_noWrap ((sp - 16) + 8) 4
      (by omega) (by omega)
  have h13 : (((sp - 16) + 8) + 5).toNat =
      ((sp - 16) + 8).toNat + 5 := by
    simpa using UInt32.add_ofNat_toNat_noWrap ((sp - 16) + 8) 5
      (by omega) (by omega)
  have h14 : (((sp - 16) + 8) + 6).toNat =
      ((sp - 16) + 8).toNat + 6 := by
    simpa using UInt32.add_ofNat_toNat_noWrap ((sp - 16) + 8) 6
      (by omega) (by omega)
  have h15 : (((sp - 16) + 8) + 7).toNat =
      ((sp - 16) + 8).toNat + 7 := by
    simpa using UInt32.add_ofNat_toNat_noWrap ((sp - 16) + 8) 7
      (by omega) (by omega)
  iintro ⟨HR, Hglobal, Hscratch⟩
  simp only [absDiffBody]
  iapply Wasm.SmallStep.wp_globalGet $$ Hglobal
  inext
  iintro Hglobal
  iapply Wasm.SmallStep.wp_const
  inext
  iapply Wasm.SmallStep.wp_sub
  inext
  iapply Wasm.SmallStep.wp_localSet rfl
  inext
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
    List.set]
  iapply Wasm.SmallStep.wp_block
  inext
  iapply Wasm.SmallStep.wp_block
  inext
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  iapply Wasm.SmallStep.wp_localGet rfl
  inext
  by_cases hab : a < b
  · iapply Wasm.SmallStep.wp_ltUI64 (result := 1) (by simp [hab])
    inext
    iapply Wasm.SmallStep.wp_const
    inext
    iapply Wasm.SmallStep.wp_and
    inext
    rw [show (1 &&& 1 : UInt32) = 1 by decide]
    iapply Wasm.SmallStep.wp_brIf (by decide) rfl
    inext
    simp only [List.take_nil, List.drop_nil, List.nil_append]
    iapply Wasm.SmallStep.wp_localGet rfl
    inext
    iapply Wasm.SmallStep.wp_localGet rfl
    inext
    iapply Wasm.SmallStep.wp_localGet rfl
    inext
    iapply Wasm.SmallStep.wp_subI64
    inext
    ihave HscratchLater :
        ▷ pointsTo_u64 0 ((sp - 16) + 8) oldScratch $$ [Hscratch]
    · inext
      iexact Hscratch
    iapply Wasm.SmallStep.wp_store64 oldScratch h8 h9 h10 h11 h12 h13 h14 h15 $$
      HscratchLater
    inext
    iintro Hscratch
    iapply Wasm.SmallStep.wp_exitControl rfl
    inext
    iapply Wasm.SmallStep.wp_localGet rfl
    inext
    ihave HscratchLater :
        ▷ pointsTo_u64 0 ((sp - 16) + 8) (b - a) $$ [Hscratch]
    · inext
      iexact Hscratch
    iapply Wasm.SmallStep.wp_load64 (b - a) h8 h9 h10 h11 h12 h13 h14 h15 $$
      HscratchLater
    inext
    iintro Hscratch
    simp only [List.take_nil, List.nil_append]
    simp only [hab, if_true] at hreturn
    iapply hreturn
    iframe
  · iapply Wasm.SmallStep.wp_ltUI64 (result := 0) (by simp [hab])
    inext
    iapply Wasm.SmallStep.wp_const
    inext
    iapply Wasm.SmallStep.wp_and
    inext
    rw [show (0 &&& 1 : UInt32) = 0 by decide]
    iapply Wasm.SmallStep.wp_brIfZero
    inext
    iapply Wasm.SmallStep.wp_localGet rfl
    inext
    iapply Wasm.SmallStep.wp_localGet rfl
    inext
    iapply Wasm.SmallStep.wp_localGet rfl
    inext
    iapply Wasm.SmallStep.wp_subI64
    inext
    ihave HscratchLater :
        ▷ pointsTo_u64 0 ((sp - 16) + 8) oldScratch $$ [Hscratch]
    · inext
      iexact Hscratch
    iapply Wasm.SmallStep.wp_store64 oldScratch h8 h9 h10 h11 h12 h13 h14 h15 $$
      HscratchLater
    inext
    iintro Hscratch
    iapply Wasm.SmallStep.wp_br rfl
    inext
    simp only [List.take_nil, List.drop_nil, List.nil_append]
    iapply Wasm.SmallStep.wp_localGet rfl
    inext
    ihave HscratchLater :
        ▷ pointsTo_u64 0 ((sp - 16) + 8) (a - b) $$ [Hscratch]
    · inext
      iexact Hscratch
    iapply Wasm.SmallStep.wp_load64 (a - b) h8 h9 h10 h11 h12 h13 h14 h15 $$
      HscratchLater
    inext
    iintro Hscratch
    simp only [hab, if_false] at hreturn
    iapply hreturn
    iframe

set_option maxHeartbeats 4000000 in
/-- Top-level corollary of the contextual body rule. -/
theorem absDiff_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    (sp : UInt32) (a b oldScratch : UInt64)
    (hlo : 16 ≤ sp.toNat)
    (hroom : (sp - 16).toNat + 16 ≤ 4294967296) :
    globalPointsToAt 0 0 (.i32 sp) ∗
      pointsTo_u64 0 ((sp - 16) + 8) oldScratch ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i64 a, .i64 b], [.i32 0], []⟩,
        absDiffBody, 1, [], [], []⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E
      {{ result,
        ⌜result = [.i64 (if a < b then b - a else a - b)]⌝ ∗
        globalPointsToAt 0 0 (.i32 sp) ∗
        pointsTo_u64 0 ((sp - 16) + 8)
          (if a < b then b - a else a - b) }} := by
  iintro Hresources
  iapply absDiff_smallStep_wp_to_return (iprop(True)) [] sp a b oldScratch hlo hroom
  · iintro ⟨_Htrue, Hresources⟩
    iapply Wasm.SmallStep.wp_returnFromFunction
    inext
    iapply wp_value'
    isplitr
    · ipureintro
      rfl
    · iexact Hresources
  · isplitr
    · itrivial
    · iexact Hresources

/-! ## Closed operational contract

The definitions below instantiate the reusable body with the same stack
pointer used by generated Rust modules. They provide a small, independent
adequacy fixture: one 17-page memory, one mutable stack-pointer global, and
the eight scratch bytes touched by `absDiffBody`. -/

def absDiffAdequacyModule : Module :=
  { funcs := [absDiffFunc]
    memory := some { pagesMin := 17 }
    globals := [{ init := .i32 1048576 }] }

def absDiffBodyConfig (runtimeModule : Module) (initial : Store Unit)
    (a b oldScratch : UInt64) : Wasm.SmallStep.Config Unit :=
  { expr := .running
      ⟨⟨[.i64 a, .i64 b], [.i32 0], []⟩,
        absDiffBody, 1, [], [], []⟩
    store :=
      { runtime := { instances := #[{ module := runtimeModule, host := {} }], entry := ⟨0⟩ }
        wasm :=
          { initial with
            mem := initial.mem.write64 1048568 oldScratch } } }

def absDiffAdequacyConfig (a b oldScratch : UInt64) :
    Wasm.SmallStep.Config Unit :=
  absDiffBodyConfig absDiffAdequacyModule
    absDiffAdequacyModule.initialStore a b oldScratch

def absDiffHeap (oldScratch : UInt64) :
    WasmHeapMap (Option UInt8) :=
  store64Heap ∅ 0 1048568 oldScratch

def absDiffGlobals : WasmGlobalMap Value :=
  insert ∅ ⟨0, 0⟩ (.i32 1048576)

theorem absDiffHeap_pointsTo (oldScratch : UInt64) [WasmHeapGS Unit] :
    ([∗map] address ↦ value ∈ absDiffHeap oldScratch,
      pointsTo (GF := WasmHeapGF Unit) (H := WasmHeapMap)
        address (DFrac.own 1) value) ⊢
      pointsTo_u64 0 1048568 oldScratch := by
  let σ0 : WasmHeapMap (Option UInt8) := ∅
  let σ1 := insert σ0 (⟨0, 1048568⟩ : MemoryKey) (some (u64Byte oldScratch 0))
  let σ2 := insert σ1 (⟨0, 1048569⟩ : MemoryKey) (some (u64Byte oldScratch 1))
  let σ3 := insert σ2 (⟨0, 1048570⟩ : MemoryKey) (some (u64Byte oldScratch 2))
  let σ4 := insert σ3 (⟨0, 1048571⟩ : MemoryKey) (some (u64Byte oldScratch 3))
  let σ5 := insert σ4 (⟨0, 1048572⟩ : MemoryKey) (some (u64Byte oldScratch 4))
  let σ6 := insert σ5 (⟨0, 1048573⟩ : MemoryKey) (some (u64Byte oldScratch 5))
  let σ7 := insert σ6 (⟨0, 1048574⟩ : MemoryKey) (some (u64Byte oldScratch 6))
  have h1 : get? σ1 (⟨0, 1048569⟩ : MemoryKey) = none := by
    dsimp [σ1, σ0]
    rw [get?_insert_ne (by decide), get?_empty]
  have h2 : get? σ2 (⟨0, 1048570⟩ : MemoryKey) = none := by
    dsimp [σ2, σ1, σ0]
    rw [get?_insert_ne (by decide), get?_insert_ne (by decide), get?_empty]
  have h3 : get? σ3 (⟨0, 1048571⟩ : MemoryKey) = none := by
    dsimp [σ3, σ2, σ1, σ0]
    rw [get?_insert_ne (by decide), get?_insert_ne (by decide),
      get?_insert_ne (by decide), get?_empty]
  have h4 : get? σ4 (⟨0, 1048572⟩ : MemoryKey) = none := by
    dsimp [σ4, σ3, σ2, σ1, σ0]
    rw [get?_insert_ne (by decide), get?_insert_ne (by decide),
      get?_insert_ne (by decide), get?_insert_ne (by decide), get?_empty]
  have h5 : get? σ5 (⟨0, 1048573⟩ : MemoryKey) = none := by
    dsimp [σ5, σ4, σ3, σ2, σ1, σ0]
    rw [get?_insert_ne (by decide), get?_insert_ne (by decide),
      get?_insert_ne (by decide), get?_insert_ne (by decide),
      get?_insert_ne (by decide), get?_empty]
  have h6 : get? σ6 (⟨0, 1048574⟩ : MemoryKey) = none := by
    dsimp [σ6, σ5, σ4, σ3, σ2, σ1, σ0]
    rw [get?_insert_ne (by decide), get?_insert_ne (by decide),
      get?_insert_ne (by decide), get?_insert_ne (by decide),
      get?_insert_ne (by decide), get?_insert_ne (by decide), get?_empty]
  have h7 : get? σ7 (⟨0, 1048575⟩ : MemoryKey) = none := by
    dsimp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, σ0]
    rw [get?_insert_ne (by decide), get?_insert_ne (by decide),
      get?_insert_ne (by decide), get?_insert_ne (by decide),
      get?_insert_ne (by decide), get?_insert_ne (by decide),
      get?_insert_ne (by decide), get?_empty]
  change
    ([∗map] address ↦ value ∈
      insert σ7 (⟨0, 1048575⟩ : MemoryKey) (some (u64Byte oldScratch 7)),
      pointsTo (GF := WasmHeapGF Unit) (H := WasmHeapMap)
        address (DFrac.own 1) value) ⊢
      pointsTo_u64 0 1048568 oldScratch
  rw [(BI.BigSepM.bigSepM_insert h7).to_eq]
  rw [(BI.BigSepM.bigSepM_insert h6).to_eq]
  rw [(BI.BigSepM.bigSepM_insert h5).to_eq]
  rw [(BI.BigSepM.bigSepM_insert h4).to_eq]
  rw [(BI.BigSepM.bigSepM_insert h3).to_eq]
  rw [(BI.BigSepM.bigSepM_insert h2).to_eq]
  rw [(BI.BigSepM.bigSepM_insert h1).to_eq]
  rw [(BI.BigSepM.bigSepM_insert (get?_empty (⟨0, 1048568⟩ : MemoryKey))).to_eq]
  rw [BI.BigSepM.bigSepM_empty.to_eq, BI.sep_emp.to_eq]
  unfold pointsTo_u64
  simp only [UInt32.reduceAdd]
  iintro ⟨H7, H6, H5, H4, H3, H2, H1, H0⟩
  iframe

theorem absDiffGlobals_pointsTo [WasmGlobalGS Unit] :
    ([∗map] index ↦ value ∈ absDiffGlobals,
      globalPointsTo index value) ⊢
      globalPointsToAt 0 0 (.i32 1048576) := by
  unfold absDiffGlobals
  rw [(BI.BigSepM.bigSepM_insert (get?_empty (⟨0, 0⟩ : GlobalKey))).to_eq,
    BI.BigSepM.bigSepM_empty.to_eq, BI.sep_emp.to_eq]
  unfold globalPointsToAt
  iintro h; iexact h

theorem absDiffBodyHeap_agrees
    (runtimeModule : Module) (initial : Store Unit)
    (a b oldScratch : UInt64) :
    heapAgreesWithMem (absDiffHeap oldScratch)
      (Wasm.SmallStep.storeResolve (absDiffBodyConfig runtimeModule initial a b oldScratch).store) := by
  have hempty : heapAgreesWithMem (∅ : WasmHeapMap (Option UInt8))
      (fun id : Nat => if id = 0 then some initial.mem else initial.extraMems[id - 1]?) := by
    intro key value hget; rw [get?_empty] at hget; contradiction
  have h := store64_sound (∅ : WasmHeapMap (Option UInt8))
      (fun id : Nat => if id = 0 then some initial.mem else initial.extraMems[id - 1]?)
      0 initial.mem 1048568 oldScratch
      (by simp) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) hempty
  have heq : (fun id => if id = 0 then some (initial.mem.write64 1048568 oldScratch)
      else (fun id' : Nat => if id' = 0 then some initial.mem else initial.extraMems[id' - 1]?) id) =
      Wasm.SmallStep.storeResolve (absDiffBodyConfig runtimeModule initial a b oldScratch).store := by
    funext id
    by_cases hid : id = 0 <;> simp [hid, Wasm.SmallStep.storeResolve, absDiffBodyConfig]
  unfold absDiffHeap
  rw [heq] at h
  exact h

theorem absDiffBodyHeap_inBounds
    (runtimeModule : Module) (initial : Store Unit)
    (a b oldScratch : UInt64)
    (hpages : 1048576 ≤ initial.mem.pages * 65536) :
    heapAddressesInBounds (absDiffHeap oldScratch)
      (Wasm.SmallStep.storeResolve (absDiffBodyConfig runtimeModule initial a b oldScratch).store) := by
  have hempty : heapAddressesInBounds (∅ : WasmHeapMap (Option UInt8))
      (fun id : Nat => if id = 0 then some initial.mem else initial.extraMems[id - 1]?) := by
    intro key hget; rw [get?_empty] at hget; contradiction
  have h := store64_inBounds (∅ : WasmHeapMap (Option UInt8))
      (fun id : Nat => if id = 0 then some initial.mem else initial.extraMems[id - 1]?)
      0 initial.mem 1048568 oldScratch
      (by simp) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) hempty
      (by simpa using hpages)
  have heq : (fun id => if id = 0 then some (initial.mem.write64 1048568 oldScratch)
      else (fun id' : Nat => if id' = 0 then some initial.mem else initial.extraMems[id' - 1]?) id) =
      Wasm.SmallStep.storeResolve (absDiffBodyConfig runtimeModule initial a b oldScratch).store := by
    funext id
    by_cases hid : id = 0 <;> simp [hid, Wasm.SmallStep.storeResolve, absDiffBodyConfig]
  unfold absDiffHeap
  rw [heq] at h
  exact h

theorem absDiffBodyGlobals_agree
    (runtimeModule : Module) (initial : Store Unit)
    (a b oldScratch : UInt64)
    (hglobal : initial.globals.globals[0]? = some (.i32 1048576)) :
    globalHeapAgrees absDiffGlobals
      (absDiffBodyConfig runtimeModule initial a b oldScratch).store.wasm.globals := by
  intro index value hget
  simp only [absDiffGlobals] at hget
  by_cases hindex : index = 0
  · subst hindex
    simp only [get?_insert_eq rfl] at hget
    obtain rfl := Option.some.inj hget
    exact hglobal
  · rw [get?_insert_ne (fun h => hindex (congrArg GlobalKey.index h).symm), get?_empty] at hget
    contradiction

set_option maxHeartbeats 4000000 in
/-- Generated-module form of the reusable Iris body proof. It works over any
runtime module and base store whose stack-pointer global and memory capacity
match the generated Rust ABI. Only the scratch word is overwritten in the
initial physical memory used by this body-level contract. -/
theorem absDiff_smallStep_partiallyMeets_of_store
    (runtimeModule : Module) (initial : Store Unit)
    (a b oldScratch : UInt64)
    (hglobal : initial.globals.globals[0]? = some (.i32 1048576))
    (hpages : 1048576 ≤ initial.mem.pages * 65536) :
    Wasm.SmallStep.PartiallyMeets
      (absDiffBodyConfig runtimeModule initial a b oldScratch)
      (fun result _store =>
        result = [.i64 (if a < b then b - a else a - b)]) := by
  apply Wasm.SmallStep.wasm_smallStep_heap_globals_partiallyMeets
      (α := Unit)
      (σ := absDiffHeap oldScratch)
      (globalσ := absDiffGlobals)
      (φ := fun result =>
        result = [.i64 (if a < b then b - a else a - b)])
  · exact absDiffBodyHeap_agrees runtimeModule initial a b oldScratch
  · exact absDiffBodyHeap_inBounds runtimeModule initial a b oldScratch hpages
  · exact absDiffBodyGlobals_agree runtimeModule initial a b oldScratch hglobal
  · simp [absDiffBodyConfig]
  · intro gs
    iintro ⟨Hbytes, Hglobals⟩
    ihave Hscratch := absDiffHeap_pointsTo oldScratch $$ Hbytes
    ihave Hglobal := absDiffGlobals_pointsTo $$ Hglobals
    have hpost : ∀ result : List Value,
        (iprop%
          ⌜result = [.i64 (if a < b then b - a else a - b)]⌝ ∗
          globalPointsToAt 0 0 (.i32 1048576) ∗
          pointsTo_u64 0 1048568
            (if a < b then b - a else a - b)) ⊢
        (iprop% ⌜result =
          [.i64 (if a < b then b - a else a - b)]⌝) := by
      intro result
      iintro ⟨%hresult, _Hglobal, _Hscratch⟩
      ipureintro
      exact hresult
    simp only [absDiffBodyConfig]
    iapply wp_mono hpost
    have hwp := absDiff_smallStep_wp
      (s := Stuckness.NotStuck) (E := ⊤)
      1048576 a b oldScratch (by decide) (by decide)
    simp only [UInt32.reduceSub, UInt32.reduceAdd] at hwp
    iapply hwp
    iframe

/-- Closed instance of `absDiff_smallStep_partiallyMeets_of_store`. The
theorem starts from a concrete physical memory/global store and assumes no
ghost resources. -/
theorem absDiff_smallStep_partiallyMeets
    (a b oldScratch : UInt64) :
    Wasm.SmallStep.PartiallyMeets
      (absDiffAdequacyConfig a b oldScratch)
      (fun result _store =>
        result = [.i64 (if a < b then b - a else a - b)]) := by
  apply absDiff_smallStep_partiallyMeets_of_store
  · rfl
  · decide

end Wasm.RustStd.U64
