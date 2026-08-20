import CodeLib.SepLogic.WasmHeap
import Interpreter.Wasm.Mem

/-! # Bridge: Talos Mem ↔ iris-lean GenHeap

Defines `heapAgreesWithMem` — the agreement predicate between an abstract
GenHeap state σ and physical memory — together with per-byte load/store
soundness lemmas for it, stated against the interpreter's `Mem.read8` /
`Mem.write8` API so they apply directly to interpreter-produced states.

The small-step Iris `StateInterp` maintains both predicates across every
migrated memory transition, so byte ownership determines the corresponding
physical memory contents and allocated bounds.
-/

namespace Wasm.SepLogic

open Iris Wasm Std

/-! Agreement: wherever GenHeap has an entry, Mem agrees. -/

def heapAgreesWithMem (σ : WasmHeapMap (Option UInt8)) (resolve : Nat → Option Mem) : Prop :=
  ∀ (key : MemoryKey) (v : UInt8),
    get? σ key = some (some v) →
    ∃ mem, resolve key.memId = some mem ∧ mem.read8 key.addr = v

/-- Every byte represented by the authoritative ghost heap names a physical
address in the currently allocated linear memory. -/
def heapAddressesInBounds (σ : WasmHeapMap (Option UInt8)) (resolve : Nat → Option Mem) : Prop :=
  ∀ (key : MemoryKey),
    get? σ key ≠ none →
    ∃ mem, resolve key.memId = some mem ∧ key.addr.toNat < mem.pages * 65536

/-- Agreement between an authoritative ghost fragment for globals and the
physical instantiated global array. Only owned indices need appear in the
ghost map. -/
def globalHeapAgrees
    (σ : WasmGlobalMap Value) (globals : Globals) : Prop :=
  ∀ (index : Nat) (value : Value),
    get? σ ⟨0, index⟩ = some value → globals.globals[index]? = some value

/-- Agreement between owned passive-data-segment entries and the instantiated
segment-status list. `none` is an owned, observable dropped segment; absence
from the ghost map means that a proof owns no fact about that index. -/
def dataSegmentHeapAgrees
    (σ : WasmDataSegmentMap (Option (List UInt8)))
    (segments : List (Option (List UInt8))) : Prop :=
  ∀ (index : Nat) (value : Option (List UInt8)),
    get? σ ⟨0, index⟩ = some value → segments[index]? = some value

/-- Agreement between owned table identities and physical instantiated tables.
The ghost key is the stable table index; the fragment owns the complete
current table contents. -/
def tableHeapAgrees
    (σ : WasmTableMap TableInst) (tables : List TableInst) : Prop :=
  ∀ (index : Nat) (table : TableInst),
    get? σ ⟨0, index⟩ = some table → tables[index]? = some table

/-- Agreement for live/dropped instantiated element segments. As with passive
data segments, `none` is an owned dropped state rather than absence of
ownership. -/
def elementSegmentHeapAgrees
    (σ : WasmElementSegmentMap (Option (List (Option Nat))))
    (segments : List (Option (List (Option Nat)))) : Prop :=
  ∀ (index : Nat) (value : Option (List (Option Nat))),
    get? σ ⟨0, index⟩ = some value → segments[index]? = some value

theorem heapAgreesWithMem_empty (resolve : Nat → Option Mem) :
    heapAgreesWithMem (∅ : WasmHeapMap (Option UInt8)) resolve := by
  intro key value hget
  rw [LawfulPartialMap.get?_empty] at hget
  contradiction

theorem heapAddressesInBounds_empty (resolve : Nat → Option Mem) :
    heapAddressesInBounds (∅ : WasmHeapMap (Option UInt8)) resolve := by
  intro key hne
  simp [LawfulPartialMap.get?_empty] at hne

theorem globalHeapAgrees_empty (globals : Globals) :
    globalHeapAgrees (∅ : WasmGlobalMap Value) globals := by
  intro index value hget
  rw [LawfulPartialMap.get?_empty] at hget
  contradiction

theorem dataSegmentHeapAgrees_empty
    (segments : List (Option (List UInt8))) :
    dataSegmentHeapAgrees
      (∅ : WasmDataSegmentMap (Option (List UInt8))) segments := by
  intro index value hget
  rw [LawfulPartialMap.get?_empty] at hget
  contradiction

theorem tableHeapAgrees_empty (tables : List TableInst) :
    tableHeapAgrees (∅ : WasmTableMap TableInst) tables := by
  intro index table hget
  rw [LawfulPartialMap.get?_empty] at hget
  contradiction

theorem elementSegmentHeapAgrees_empty
    (segments : List (Option (List (Option Nat)))) :
    elementSegmentHeapAgrees
      (∅ : WasmElementSegmentMap (Option (List (Option Nat))))
      segments := by
  intro index value hget
  rw [LawfulPartialMap.get?_empty] at hget
  contradiction

def exceptionHeapAgrees
    (σ : WasmExceptionMap (Nat × List Value))
    (exns : List (Nat × List Value)) : Prop :=
  ∀ (k : Nat) (v : Nat × List Value),
    get? σ k = some v → exns[k]? = some v

theorem exceptionHeapAgrees_empty (exns : List (Nat × List Value)) :
    exceptionHeapAgrees (∅ : WasmExceptionMap (Nat × List Value)) exns := by
  intro k v hget
  rw [LawfulPartialMap.get?_empty] at hget
  contradiction

theorem exceptionHeapAgrees_append {σ : WasmExceptionMap (Nat × List Value)}
    {exns : List (Nat × List Value)} {entry : Nat × List Value}
    (h : exceptionHeapAgrees σ exns) : exceptionHeapAgrees σ (exns ++ [entry]) := by
  intro k v hget
  have hv := h k v hget
  obtain ⟨hlt, _⟩ := getElem?_eq_some_iff.mp hv
  rwa [List.getElem?_append_left hlt]

/-- Updating an owned global in both the authoritative ghost map and the
physical global array preserves their agreement. All owned entries use
`instanceId = 0`, so index equality is the only collision condition. -/
theorem global_store_sound
    (σ : WasmGlobalMap Value) (globals : Globals)
    (index : Nat) (oldValue newValue : Value)
    (hagree : globalHeapAgrees σ globals)
    (hlookup : get? σ ⟨0, index⟩ = some oldValue) :
    globalHeapAgrees (insert σ ⟨0, index⟩ newValue)
      { globals := globals.globals.set index newValue } := by
  have hphysical := hagree index oldValue hlookup
  obtain ⟨hindex, _⟩ := getElem?_eq_some_iff.mp hphysical
  intro idx value hother
  by_cases heq : idx = index
  · subst idx
    simp only [get?_insert_eq rfl, Option.some.injEq] at hother
    subst value
    exact List.getElem?_set_self hindex
  · have hne : (⟨0, idx⟩ : GlobalKey) ≠ ⟨0, index⟩ := fun h =>
      heq (congrArg GlobalKey.index h)
    rw [get?_insert_ne (Ne.symm hne)] at hother
    rw [List.getElem?_set_ne (Ne.symm heq)]
    exact hagree idx value hother

/-- Dropping an owned data segment in both the authoritative map and physical
store preserves their agreement. -/
theorem dataSegment_store_sound
    (σ : WasmDataSegmentMap (Option (List UInt8)))
    (segments : List (Option (List UInt8)))
    (index : Nat) (oldValue newValue : Option (List UInt8))
    (hagree : dataSegmentHeapAgrees σ segments)
    (hlookup : get? σ ⟨0, index⟩ = some oldValue) :
    dataSegmentHeapAgrees (insert σ ⟨0, index⟩ newValue)
      (segments.set index newValue) := by
  have hphysical := hagree index oldValue hlookup
  obtain ⟨hindex, _⟩ := getElem?_eq_some_iff.mp hphysical
  intro idx value hother
  by_cases heq : idx = index
  · subst idx
    simp only [get?_insert_eq rfl, Option.some.injEq] at hother
    subst value
    exact List.getElem?_set_self hindex
  · have hne : (⟨0, idx⟩ : DataSegmentKey) ≠ ⟨0, index⟩ := fun h =>
      heq (congrArg DataSegmentKey.index h)
    rw [get?_insert_ne (Ne.symm hne)] at hother
    rw [List.getElem?_set_ne (Ne.symm heq)]
    exact hagree idx value hother

/-- Dropping an owned element segment preserves physical/ghost agreement and
does not change the stable indices of any other segment. -/
theorem elementSegment_store_sound
    (σ : WasmElementSegmentMap (Option (List (Option Nat))))
    (segments : List (Option (List (Option Nat))))
    (index : Nat)
    (oldValue newValue : Option (List (Option Nat)))
    (hagree : elementSegmentHeapAgrees σ segments)
    (hlookup : get? σ ⟨0, index⟩ = some oldValue) :
    elementSegmentHeapAgrees (insert σ ⟨0, index⟩ newValue)
      (segments.set index newValue) := by
  have hphysical := hagree index oldValue hlookup
  obtain ⟨hindex, _⟩ := getElem?_eq_some_iff.mp hphysical
  intro idx value hother
  by_cases heq : idx = index
  · subst idx
    simp only [get?_insert_eq rfl, Option.some.injEq] at hother
    subst value
    exact List.getElem?_set_self hindex
  · have hne : (⟨0, idx⟩ : ElementSegmentKey) ≠ ⟨0, index⟩ := fun h =>
      heq (congrArg ElementSegmentKey.index h)
    rw [get?_insert_ne (Ne.symm hne)] at hother
    rw [List.getElem?_set_ne (Ne.symm heq)]
    exact hagree idx value hother

/-- Updating one owned table in the authoritative map and physical table list
preserves agreement without renumbering or changing unrelated tables. -/
theorem table_store_sound
    (σ : WasmTableMap TableInst) (tables : List TableInst)
    (index : Nat) (oldTable newTable : TableInst)
    (hagree : tableHeapAgrees σ tables)
    (hlookup : get? σ ⟨0, index⟩ = some oldTable) :
    tableHeapAgrees (insert σ ⟨0, index⟩ newTable)
      (tables.set index newTable) := by
  have hphysical := hagree index oldTable hlookup
  obtain ⟨hindex, _⟩ := getElem?_eq_some_iff.mp hphysical
  intro idx table hother
  by_cases heq : idx = index
  · subst idx
    simp only [get?_insert_eq rfl, Option.some.injEq] at hother
    subst table
    exact List.getElem?_set_self hindex
  · have hne : (⟨0, idx⟩ : TableKey) ≠ ⟨0, index⟩ := fun h =>
      heq (congrArg TableKey.index h)
    rw [get?_insert_ne (Ne.symm hne)] at hother
    rw [List.getElem?_set_ne (Ne.symm heq)]
    exact hagree idx table hother

theorem listSetAt_eq_set (values : List α) (index : Nat) (value : α)
    (hindex : index < values.length) :
    listSetAt values index value = values.set index value := by
  induction values generalizing index with
  | nil => simp at hindex
  | cons head tail ih =>
      cases index with
      | zero => rfl
      | succ index =>
          simp only [List.length_cons, Nat.succ_lt_succ_iff] at hindex
          simp [listSetAt, ih index hindex]

theorem table_store_listSetAt_sound
    (σ : WasmTableMap TableInst) (tables : List TableInst)
    (index : Nat) (oldTable newTable : TableInst)
    (hagree : tableHeapAgrees σ tables)
    (hlookup : get? σ ⟨0, index⟩ = some oldTable) :
    tableHeapAgrees (insert σ ⟨0, index⟩ newTable)
      (listSetAt tables index newTable) := by
  have hphysical := hagree index oldTable hlookup
  obtain ⟨hindex, _⟩ := getElem?_eq_some_iff.mp hphysical
  rw [listSetAt_eq_set tables index newTable hindex]
  exact table_store_sound σ tables index oldTable newTable hagree hlookup

/-! Soundness of load:
If GenHeap says key ↦ v and σ agrees with resolve,
then the memory for key.memId reads v at key.addr. -/

theorem load_sound (σ : WasmHeapMap (Option UInt8)) (resolve : Nat → Option Mem)
    (key : MemoryKey) (v : UInt8)
    (h_agree : heapAgreesWithMem σ resolve)
    (h_own : get? σ key = some (some v)) :
    ∃ mem, resolve key.memId = some mem ∧ mem.read8 key.addr = v :=
  h_agree key v h_own

/-! Soundness of store:
After Mem.write8, the updated σ still agrees with the updated resolver. -/

theorem store_sound (σ : WasmHeapMap (Option UInt8)) (resolve : Nat → Option Mem)
    (memId : Nat) (mem : Mem) (addr : UInt32) (new_v : UInt8)
    (h_resolve : resolve memId = some mem)
    (h_agree : heapAgreesWithMem σ resolve) :
    heapAgreesWithMem (insert σ ⟨memId, addr⟩ (some new_v))
      (fun id => if id = memId then some (mem.write8 addr new_v) else resolve id) := by
  intro key v h_get
  by_cases heq : key = ⟨memId, addr⟩
  · subst key
    simp only [get?_insert_eq rfl, Option.some.injEq] at h_get
    rw [← h_get]
    refine ⟨mem.write8 addr new_v, ?_, ?_⟩
    · simp
    · simp [Mem.write8, Mem.read8]
  · rw [get?_insert_ne (Ne.symm heq)] at h_get
    obtain ⟨m, hm, hread⟩ := h_agree key v h_get
    by_cases hid : key.memId = memId
    · have hm_eq : m = mem := Option.some.inj ((hid ▸ hm).symm.trans h_resolve)
      have haddr : key.addr ≠ addr := fun h =>
        heq (show key = ⟨memId, addr⟩ from by cases key; simp_all)
      have haddr_ne : key.addr.toNat ≠ addr.toNat :=
        fun h => haddr (UInt32.toNat_inj.mp h)
      refine ⟨mem.write8 addr new_v, ?_, ?_⟩
      · simp [hid]
      · simpa [Mem.write8, Mem.read8, haddr_ne, hm_eq] using hread
    · exact ⟨m, by simp [if_neg hid, hm], hread⟩

theorem store_inBounds (σ : WasmHeapMap (Option UInt8)) (resolve : Nat → Option Mem)
    (memId : Nat) (mem : Mem) (addr : UInt32) (new_v : UInt8)
    (h_resolve : resolve memId = some mem)
    (h_addresses : heapAddressesInBounds σ resolve)
    (h_addr : addr.toNat < mem.pages * 65536) :
    heapAddressesInBounds (insert σ ⟨memId, addr⟩ (some new_v))
      (fun id => if id = memId then some (mem.write8 addr new_v) else resolve id) := by
  intro key hne
  by_cases heq : key = ⟨memId, addr⟩
  · subst key
    refine ⟨mem.write8 addr new_v, ?_, ?_⟩
    · simp
    · simpa [Mem.write8] using h_addr
  · rw [get?_insert_ne (Ne.symm heq)] at hne
    obtain ⟨m, hm, hlt⟩ := h_addresses key hne
    by_cases hid : key.memId = memId
    · have hm_eq : m = mem := Option.some.inj ((hid ▸ hm).symm.trans h_resolve)
      refine ⟨mem.write8 addr new_v, ?_, ?_⟩
      · simp [hid]
      · simpa [Mem.write8, hm_eq] using hlt
    · exact ⟨m, by simp [if_neg hid, hm], hlt⟩

/-- `Mem.grow` preserves every physical byte, so the same authoritative
ghost heap continues to agree with the grown memory under the updated resolver. -/
theorem grow_sound (σ : WasmHeapMap (Option UInt8)) (resolve : Nat → Option Mem)
    (memId : Nat) (mem memory : Mem)
    (delta : UInt32) (cap previousPages : Nat)
    (hgrow : mem.grow delta cap = some (memory, previousPages))
    (h_resolve : resolve memId = some mem)
    (h_agree : heapAgreesWithMem σ resolve) :
    heapAgreesWithMem σ (fun id => if id = memId then some memory else resolve id) := by
  intro key v h_get
  obtain ⟨m, hm, hread⟩ := h_agree key v h_get
  by_cases hid : key.memId = memId
  · have hm_eq : m = mem := Option.some.inj ((hid ▸ hm).symm.trans h_resolve)
    simp only [Mem.grow] at hgrow
    split at hgrow
    · obtain ⟨hmemory, _⟩ := Prod.mk.inj (Option.some.inj hgrow)
      refine ⟨memory, by simp [hid], ?_⟩
      have hbytes : memory.bytes = mem.bytes := by rw [← hmemory]
      simpa [Mem.read8, hbytes, ← hm_eq] using hread
    · contradiction
  · exact ⟨m, by simp [if_neg hid, hm], hread⟩

set_option maxRecDepth 4000 in
/-- Existing ghost addresses stay in bounds after successful growth. -/
theorem grow_inBounds (σ : WasmHeapMap (Option UInt8)) (resolve : Nat → Option Mem)
    (memId : Nat) (mem memory : Mem)
    (delta : UInt32) (cap previousPages : Nat)
    (hgrow : mem.grow delta cap = some (memory, previousPages))
    (h_resolve : resolve memId = some mem)
    (h_addresses : heapAddressesInBounds σ resolve) :
    heapAddressesInBounds σ (fun id => if id = memId then some memory else resolve id) := by
  intro key hne
  obtain ⟨m, hm, hlt⟩ := h_addresses key hne
  by_cases hid : key.memId = memId
  · have hm_eq : m = mem := Option.some.inj ((hid ▸ hm).symm.trans h_resolve)
    simp only [Mem.grow] at hgrow
    split at hgrow
    · obtain ⟨hmemory, _⟩ := Prod.mk.inj (Option.some.inj hgrow)
      have hpages : memory.pages = mem.pages + delta.toNat := by rw [← hmemory]
      refine ⟨memory, by simp [hid], ?_⟩
      rw [hm_eq] at hlt
      have hle : mem.pages ≤ memory.pages :=
        hpages.symm ▸ Nat.le_add_right mem.pages delta.toNat
      exact Nat.lt_of_lt_of_le hlt (Nat.mul_le_mul_right 65536 hle)
    · contradiction
  · exact ⟨m, by simp [if_neg hid, hm], hlt⟩

/-- The concrete four-byte fill used by the manual small-step example is the
same physical update as storing the repeated byte as a little-endian word. -/
theorem fill16_four_AB_eq_write32 (mem : Mem) :
    mem.fill 16 4 0xAB = mem.write32 16 0xABABABAB := by
  cases mem with
  | mk pages bytes =>
    simp only [Mem.fill, Mem.write32, UInt32.toNat_ofNat]
    congr
    funext i
    by_cases h0 : i = 16
    · subst i
      simp
      bv_decide
    by_cases h1 : i = 17
    · subst i
      simp
      bv_decide
    by_cases h2 : i = 18
    · subst i
      simp
      bv_decide
    by_cases h3 : i = 19
    · subst i
      simp
      bv_decide
    simp [h0, h1, h2, h3]
    omega

/-- The concrete passive-segment initialization used by the handwritten Iris
example is exactly a little-endian 32-bit store. -/
theorem init16_four_eq_write32 (mem : Mem) :
    mem.writeBytesFrom 16 [1, 2, 3, 4] 0 4 =
      mem.write32 16 0x04030201 := by
  cases mem with
  | mk pages bytes =>
    simp only [Mem.writeBytesFrom, Mem.write32]
    congr
    funext i
    by_cases h0 : i = 16
    · subst i
      simp
      bv_decide
    by_cases h1 : i = 17
    · subst i
      simp
      bv_decide
    by_cases h2 : i = 18
    · subst i
      simp
      bv_decide
    by_cases h3 : i = 19
    · subst i
      simp
      bv_decide
    simp [h0, h1, h2, h3]
    omega

/-- Copying the concrete source word used by the aligned manual example is
physically the same update as storing that word at the destination. -/
theorem copy8_zero_four_eq_write32 (mem : Mem)
    (hread : mem.read32 0 = 0x04030201) :
    mem.copy 8 0 4 = mem.write32 8 0x04030201 := by
  have hb0 : mem.bytes 0 = 0x01 := by
    simp only [Mem.read32, UInt32.toNat_ofNat] at hread
    bv_decide
  have hb1 : mem.bytes 1 = 0x02 := by
    simp only [Mem.read32, UInt32.toNat_ofNat] at hread
    bv_decide
  have hb2 : mem.bytes 2 = 0x03 := by
    simp only [Mem.read32, UInt32.toNat_ofNat] at hread
    bv_decide
  have hb3 : mem.bytes 3 = 0x04 := by
    simp only [Mem.read32, UInt32.toNat_ofNat] at hread
    bv_decide
  cases mem with
  | mk pages bytes =>
    simp only [Mem.copy, Mem.write32, UInt32.toNat_ofNat] at hb0 hb1 hb2 hb3 ⊢
    congr
    funext i
    by_cases h8 : i = 8
    · subst i
      simp [hb0]
      bv_decide
    by_cases h9 : i = 9
    · subst i
      simp [hb1]
      bv_decide
    by_cases h10 : i = 10
    · subst i
      simp [hb2]
      bv_decide
    by_cases h11 : i = 11
    · subst i
      simp [hb3]
      bv_decide
    simp [h8, h9, h10, h11]
    omega

/-- The overlapping manual copy has memmove semantics: source bytes are read
from the pre-copy memory before the overlapping destination is updated. -/
theorem copy2_zero_four_eq_write64 (mem : Mem)
    (hread : mem.read64 0 = 0x8877665544332211) :
    mem.copy 2 0 4 =
      (((mem.write8 2 0x11).write8 3 0x22).write8 4 0x33).write8 5 0x44 := by
  have hb0 : mem.bytes 0 = 0x11 := by
    simp only [Mem.read64, UInt32.toNat_ofNat] at hread
    bv_decide
  have hb1 : mem.bytes 1 = 0x22 := by
    simp only [Mem.read64, UInt32.toNat_ofNat] at hread
    bv_decide
  have hb2 : mem.bytes 2 = 0x33 := by
    simp only [Mem.read64, UInt32.toNat_ofNat] at hread
    bv_decide
  have hb3 : mem.bytes 3 = 0x44 := by
    simp only [Mem.read64, UInt32.toNat_ofNat] at hread
    bv_decide
  cases mem with
  | mk pages bytes =>
    simp only [Mem.copy, Mem.write8, UInt32.toNat_ofNat] at hb0 hb1 hb2 hb3 ⊢
    congr
    funext i
    by_cases h2 : i = 2
    · subst i
      simp [hb0]
    by_cases h3 : i = 3
    · subst i
      simp [hb1]
    by_cases h4 : i = 4
    · subst i
      simp [hb2]
    by_cases h5 : i = 5
    · subst i
      simp [hb3]
    simp [h2, h3, h4, h5]
    omega

def store16Heap (σ : WasmHeapMap (Option UInt8)) (memId : Nat) (addr value : UInt32) :
    WasmHeapMap (Option UInt8) :=
  insert
    (insert σ ⟨memId, addr⟩ (some (u32Byte value 0)))
    ⟨memId, addr + 1⟩ (some (u32Byte value 1))

theorem store16_sound (σ : WasmHeapMap (Option UInt8)) (resolve : Nat → Option Mem)
    (memId : Nat) (mem : Mem) (addr value : UInt32)
    (h_resolve : resolve memId = some mem)
    (h1 : (addr + 1).toNat = addr.toNat + 1)
    (h_agree : heapAgreesWithMem σ resolve) :
    heapAgreesWithMem (store16Heap σ memId addr value)
      (fun id => if id = memId then some (mem.write16 addr value) else resolve id) := by
  intro key byte h_get
  by_cases e1 : key = ⟨memId, addr + 1⟩
  · subst key
    simp [store16Heap, get?_insert_eq] at h_get
    rw [← h_get]
    refine ⟨mem.write16 addr value, ?_, ?_⟩
    · simp
    · simp [Mem.write16, Mem.read8, h1, u32Byte]; bv_decide
  by_cases e0 : key = ⟨memId, addr⟩
  · subst key
    simp [store16Heap, get?_insert_ne (Ne.symm e1), get?_insert_eq] at h_get
    rw [← h_get]
    refine ⟨mem.write16 addr value, ?_, ?_⟩
    · simp
    · simp [Mem.write16, Mem.read8, u32Byte]; bv_decide
  · simp [store16Heap, get?_insert_ne (Ne.symm e1),
      get?_insert_ne (Ne.symm e0)] at h_get
    obtain ⟨m, hm, hread⟩ := h_agree key byte h_get
    by_cases hid : key.memId = memId
    · have hm_eq : m = mem := Option.some.inj ((hid ▸ hm).symm.trans h_resolve)
      have n0 : key.addr.toNat ≠ addr.toNat :=
        fun h => e0 (show key = ⟨memId, addr⟩ from by
          cases key; simp only [MemoryKey.mk.injEq]; exact ⟨hid, UInt32.toNat_inj.mp h⟩)
      have n1 : key.addr.toNat ≠ addr.toNat + 1 := by
        rw [← h1]
        exact fun h => e1 (show key = ⟨memId, addr + 1⟩ from by
          cases key; simp only [MemoryKey.mk.injEq]; exact ⟨hid, UInt32.toNat_inj.mp h⟩)
      refine ⟨mem.write16 addr value, ?_, ?_⟩
      · simp [hid]
      · simpa [Mem.write16, Mem.read8, n0, n1, hm_eq] using hread
    · exact ⟨m, by simp [if_neg hid, hm], hread⟩

theorem store16_inBounds (σ : WasmHeapMap (Option UInt8)) (resolve : Nat → Option Mem)
    (memId : Nat) (mem : Mem) (addr value : UInt32)
    (h_resolve : resolve memId = some mem)
    (h1 : (addr + 1).toNat = addr.toNat + 1)
    (h_addresses : heapAddressesInBounds σ resolve)
    (h_addr : addr.toNat + 2 ≤ mem.pages * 65536) :
    heapAddressesInBounds (store16Heap σ memId addr value)
      (fun id => if id = memId then some (mem.write16 addr value) else resolve id) := by
  intro key h_get
  by_cases e1 : key = ⟨memId, addr + 1⟩
  · subst key
    refine ⟨mem.write16 addr value, ?_, ?_⟩; · simp
    · simp [Mem.write16, h1]; omega
  by_cases e0 : key = ⟨memId, addr⟩
  · subst key
    refine ⟨mem.write16 addr value, ?_, ?_⟩; · simp
    · simp [Mem.write16]; omega
  · simp [store16Heap, get?_insert_ne (Ne.symm e1),
      get?_insert_ne (Ne.symm e0)] at h_get
    obtain ⟨m, hm, hlt⟩ := h_addresses key h_get
    by_cases hid : key.memId = memId
    · have hm_eq : m = mem := Option.some.inj ((hid ▸ hm).symm.trans h_resolve)
      refine ⟨mem.write16 addr value, ?_, ?_⟩
      · simp [hid]
      · simpa [Mem.write16, hm_eq] using hlt
    · exact ⟨m, by simp [if_neg hid, hm], hlt⟩

def store32Heap (σ : WasmHeapMap (Option UInt8)) (memId : Nat) (addr value : UInt32) :
    WasmHeapMap (Option UInt8) :=
  insert
    (insert
      (insert
        (insert σ ⟨memId, addr⟩ (some (u32Byte value 0)))
        ⟨memId, addr + 1⟩ (some (u32Byte value 1)))
      ⟨memId, addr + 2⟩ (some (u32Byte value 2)))
    ⟨memId, addr + 3⟩ (some (u32Byte value 3))

theorem Mem.read32_byte0 {m : Mem} {addr value : UInt32}
    (hread : m.read32 addr = value) :
    m.read8 addr = u32Byte value 0 := by
  have hlow (b0 b1 b2 b3 : UInt8) :
      (b0.toUInt32 ||| (b1.toUInt32 <<< 8) ||| (b2.toUInt32 <<< 16) |||
        (b3.toUInt32 <<< 24)).toUInt8 = b0 := by bv_decide
  have h := congrArg UInt32.toUInt8 hread
  unfold Mem.read32 at h
  rw [hlow] at h
  simpa [Mem.read8, u32Byte] using h

theorem Mem.read32_byte1 {m : Mem} {addr value : UInt32}
    (hread : m.read32 addr = value)
    (h1 : (addr + 1).toNat = addr.toNat + 1) :
    m.read8 (addr + 1) = u32Byte value 1 := by
  have hbyte (b0 b1 b2 b3 : UInt8) :
      ((b0.toUInt32 ||| (b1.toUInt32 <<< 8) ||| (b2.toUInt32 <<< 16) |||
        (b3.toUInt32 <<< 24)) >>> 8).toUInt8 = b1 := by bv_decide
  have h := congrArg (fun word : UInt32 => (word >>> 8).toUInt8) hread
  unfold Mem.read32 at h
  rw [hbyte] at h
  simpa [Mem.read8, u32Byte, h1] using h

theorem Mem.read32_byte2 {m : Mem} {addr value : UInt32}
    (hread : m.read32 addr = value)
    (h2 : (addr + 2).toNat = addr.toNat + 2) :
    m.read8 (addr + 2) = u32Byte value 2 := by
  have hbyte (b0 b1 b2 b3 : UInt8) :
      ((b0.toUInt32 ||| (b1.toUInt32 <<< 8) ||| (b2.toUInt32 <<< 16) |||
        (b3.toUInt32 <<< 24)) >>> 16).toUInt8 = b2 := by bv_decide
  have h := congrArg (fun word : UInt32 => (word >>> 16).toUInt8) hread
  unfold Mem.read32 at h
  rw [hbyte] at h
  simpa [Mem.read8, u32Byte, h2] using h

theorem Mem.read32_byte3 {m : Mem} {addr value : UInt32}
    (hread : m.read32 addr = value)
    (h3 : (addr + 3).toNat = addr.toNat + 3) :
    m.read8 (addr + 3) = u32Byte value 3 := by
  have hbyte (b0 b1 b2 b3 : UInt8) :
      ((b0.toUInt32 ||| (b1.toUInt32 <<< 8) ||| (b2.toUInt32 <<< 16) |||
        (b3.toUInt32 <<< 24)) >>> 24).toUInt8 = b3 := by bv_decide
  have h := congrArg (fun word : UInt32 => (word >>> 24).toUInt8) hread
  unfold Mem.read32 at h
  rw [hbyte] at h
  simpa [Mem.read8, u32Byte, h3] using h

theorem Mem.write32_eq_self {m : Mem} {addr value : UInt32}
    (hread : m.read32 addr = value)
    (h1 : (addr + 1).toNat = addr.toNat + 1)
    (h2 : (addr + 2).toNat = addr.toNat + 2)
    (h3 : (addr + 3).toNat = addr.toNat + 3) :
    m.write32 addr value = m := by
  have hb0 := Mem.read32_byte0 hread
  have hb1 := Mem.read32_byte1 hread h1
  have hb2 := Mem.read32_byte2 hread h2
  have hb3 := Mem.read32_byte3 hread h3
  cases m with
  | mk pages bytes =>
    unfold Mem.write32
    dsimp only
    congr
    funext index
    split <;> rename_i heq
    · subst index
      simp [Mem.read8, u32Byte] at hb0
      rw [hb0]
      bv_decide
    split <;> rename_i heq
    · subst index
      simp [Mem.read8, u32Byte, h1] at hb1
      rw [hb1]
      bv_decide
    split <;> rename_i heq
    · subst index
      simp [Mem.read8, u32Byte, h2] at hb2
      rw [hb2]
      bv_decide
    split <;> rename_i heq
    · subst index
      simp [Mem.read8, u32Byte, h3] at hb3
      rw [hb3]
      bv_decide
    · rfl

theorem store32Heap_pointsTo {α : Type} [WasmHeapGS α]
    (σ : WasmHeapMap (Option UInt8)) (memId : Nat) (addr value : UInt32)
    (h0 : get? σ ⟨memId, addr⟩ = none)
    (h1 : get? σ ⟨memId, addr + 1⟩ = none)
    (h2 : get? σ ⟨memId, addr + 2⟩ = none)
    (h3 : get? σ ⟨memId, addr + 3⟩ = none)
    (_hn1 : (addr + 1).toNat = addr.toNat + 1)
    (_hn2 : (addr + 2).toNat = addr.toNat + 2)
    (_hn3 : (addr + 3).toNat = addr.toNat + 3) :
    ([∗map] address ↦ byte ∈ store32Heap σ memId addr value,
      pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        address (DFrac.own 1) byte) ⊢
      pointsTo_u32 memId addr value ∗
      ([∗map] address ↦ byte ∈ σ,
        pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
          address (DFrac.own 1) byte) := by
  have h01 : (⟨memId, addr + 1⟩ : MemoryKey) ≠ ⟨memId, addr⟩ := fun h =>
    absurd (congrArg MemoryKey.addr h) (by intro h'; simp at h')
  have h02 : (⟨memId, addr + 2⟩ : MemoryKey) ≠ ⟨memId, addr⟩ := fun h =>
    absurd (congrArg MemoryKey.addr h) (by intro h'; simp at h')
  have h03 : (⟨memId, addr + 3⟩ : MemoryKey) ≠ ⟨memId, addr⟩ := fun h =>
    absurd (congrArg MemoryKey.addr h) (by intro h'; simp at h')
  have h12 : (⟨memId, addr + 2⟩ : MemoryKey) ≠ ⟨memId, addr + 1⟩ := fun h =>
    absurd (congrArg MemoryKey.addr h) (by intro h'; simp at h')
  have h13 : (⟨memId, addr + 3⟩ : MemoryKey) ≠ ⟨memId, addr + 1⟩ := fun h =>
    absurd (congrArg MemoryKey.addr h) (by intro h'; simp at h')
  have h23 : (⟨memId, addr + 3⟩ : MemoryKey) ≠ ⟨memId, addr + 2⟩ := fun h =>
    absurd (congrArg MemoryKey.addr h) (by intro h'; simp at h')
  unfold store32Heap
  rw [(BI.BigSepM.bigSepM_insert (by
    simp only [get?_insert_ne (Ne.symm h23), get?_insert_ne (Ne.symm h13),
      get?_insert_ne (Ne.symm h03), h3])).to_eq]
  rw [(BI.BigSepM.bigSepM_insert (by
    simp only [get?_insert_ne (Ne.symm h12), get?_insert_ne (Ne.symm h02), h2])).to_eq]
  rw [(BI.BigSepM.bigSepM_insert (by
    simp only [get?_insert_ne (Ne.symm h01), h1])).to_eq]
  rw [(BI.BigSepM.bigSepM_insert h0).to_eq]
  unfold pointsTo_u32
  iintro ⟨H3, H2, H1, H0, Hrest⟩
  iframe

theorem store32_sound (σ : WasmHeapMap (Option UInt8)) (resolve : Nat → Option Mem)
    (memId : Nat) (mem : Mem) (addr value : UInt32)
    (h_resolve : resolve memId = some mem)
    (h1 : (addr + 1).toNat = addr.toNat + 1)
    (h2 : (addr + 2).toNat = addr.toNat + 2)
    (h3 : (addr + 3).toNat = addr.toNat + 3)
    (h_agree : heapAgreesWithMem σ resolve) :
    heapAgreesWithMem (store32Heap σ memId addr value)
      (fun id => if id = memId then some (mem.write32 addr value) else resolve id) := by
  intro key byte h_get
  by_cases e3 : key = ⟨memId, addr + 3⟩
  · subst key
    simp [store32Heap, get?_insert_eq] at h_get
    rw [← h_get]
    refine ⟨mem.write32 addr value, ?_, ?_⟩
    · simp
    · simp [Mem.write32, Mem.read8, h3, u32Byte]; bv_decide
  by_cases e2 : key = ⟨memId, addr + 2⟩
  · subst key
    simp [store32Heap, get?_insert_ne (Ne.symm e3), get?_insert_eq] at h_get
    rw [← h_get]
    refine ⟨mem.write32 addr value, ?_, ?_⟩
    · simp
    · simp [Mem.write32, Mem.read8, h2, u32Byte]; bv_decide
  by_cases e1 : key = ⟨memId, addr + 1⟩
  · subst key
    simp [store32Heap, get?_insert_ne (Ne.symm e3),
      get?_insert_ne (Ne.symm e2), get?_insert_eq] at h_get
    rw [← h_get]
    refine ⟨mem.write32 addr value, ?_, ?_⟩
    · simp
    · simp [Mem.write32, Mem.read8, h1, u32Byte]; bv_decide
  by_cases e0 : key = ⟨memId, addr⟩
  · subst key
    simp [store32Heap, get?_insert_ne (Ne.symm e3),
      get?_insert_ne (Ne.symm e2), get?_insert_ne (Ne.symm e1),
      get?_insert_eq] at h_get
    rw [← h_get]
    refine ⟨mem.write32 addr value, ?_, ?_⟩
    · simp
    · simp [Mem.write32, Mem.read8, u32Byte]; bv_decide
  · simp [store32Heap, get?_insert_ne (Ne.symm e3),
      get?_insert_ne (Ne.symm e2), get?_insert_ne (Ne.symm e1),
      get?_insert_ne (Ne.symm e0)] at h_get
    obtain ⟨m, hm, hread⟩ := h_agree key byte h_get
    by_cases hid : key.memId = memId
    · have hm_eq : m = mem := Option.some.inj ((hid ▸ hm).symm.trans h_resolve)
      have n0 : key.addr.toNat ≠ addr.toNat :=
        fun h => e0 (show key = ⟨memId, addr⟩ from by
          cases key; simp only [MemoryKey.mk.injEq]; exact ⟨hid, UInt32.toNat_inj.mp h⟩)
      have n1 : key.addr.toNat ≠ addr.toNat + 1 := by
        rw [← h1]
        exact fun h => e1 (show key = ⟨memId, addr + 1⟩ from by
          cases key; simp only [MemoryKey.mk.injEq]; exact ⟨hid, UInt32.toNat_inj.mp h⟩)
      have n2 : key.addr.toNat ≠ addr.toNat + 2 := by
        rw [← h2]
        exact fun h => e2 (show key = ⟨memId, addr + 2⟩ from by
          cases key; simp only [MemoryKey.mk.injEq]; exact ⟨hid, UInt32.toNat_inj.mp h⟩)
      have n3 : key.addr.toNat ≠ addr.toNat + 3 := by
        rw [← h3]
        exact fun h => e3 (show key = ⟨memId, addr + 3⟩ from by
          cases key; simp only [MemoryKey.mk.injEq]; exact ⟨hid, UInt32.toNat_inj.mp h⟩)
      refine ⟨mem.write32 addr value, ?_, ?_⟩
      · simp [hid]
      · simpa [Mem.write32, Mem.read8, n0, n1, n2, n3, hm_eq] using hread
    · exact ⟨m, by simp [if_neg hid, hm], hread⟩

theorem store32_inBounds (σ : WasmHeapMap (Option UInt8)) (resolve : Nat → Option Mem)
    (memId : Nat) (mem : Mem) (addr value : UInt32)
    (h_resolve : resolve memId = some mem)
    (h1 : (addr + 1).toNat = addr.toNat + 1)
    (h2 : (addr + 2).toNat = addr.toNat + 2)
    (h3 : (addr + 3).toNat = addr.toNat + 3)
    (h_addresses : heapAddressesInBounds σ resolve)
    (h_addr : addr.toNat + 4 ≤ mem.pages * 65536) :
    heapAddressesInBounds (store32Heap σ memId addr value)
      (fun id => if id = memId then some (mem.write32 addr value) else resolve id) := by
  intro key h_get
  by_cases e3 : key = ⟨memId, addr + 3⟩
  · subst key
    refine ⟨mem.write32 addr value, ?_, ?_⟩; · simp
    · simp [Mem.write32, h3]; omega
  by_cases e2 : key = ⟨memId, addr + 2⟩
  · subst key
    refine ⟨mem.write32 addr value, ?_, ?_⟩; · simp
    · simp [Mem.write32, h2]; omega
  by_cases e1 : key = ⟨memId, addr + 1⟩
  · subst key
    refine ⟨mem.write32 addr value, ?_, ?_⟩; · simp
    · simp [Mem.write32, h1]; omega
  by_cases e0 : key = ⟨memId, addr⟩
  · subst key
    refine ⟨mem.write32 addr value, ?_, ?_⟩; · simp
    · simp [Mem.write32]; omega
  · simp [store32Heap, get?_insert_ne (Ne.symm e3),
      get?_insert_ne (Ne.symm e2), get?_insert_ne (Ne.symm e1),
      get?_insert_ne (Ne.symm e0)] at h_get
    obtain ⟨m, hm, hlt⟩ := h_addresses key h_get
    by_cases hid : key.memId = memId
    · have hm_eq : m = mem := Option.some.inj ((hid ▸ hm).symm.trans h_resolve)
      refine ⟨mem.write32 addr value, ?_, ?_⟩
      · simp [hid]
      · simpa [Mem.write32, hm_eq] using hlt
    · exact ⟨m, by simp [if_neg hid, hm], hlt⟩

def store64Heap (σ : WasmHeapMap (Option UInt8)) (memId : Nat) (addr : UInt32)
    (value : UInt64) : WasmHeapMap (Option UInt8) :=
  insert
    (insert
      (insert
        (insert
          (insert
            (insert
              (insert
                (insert σ ⟨memId, addr⟩ (some (u64Byte value 0)))
                ⟨memId, addr + 1⟩ (some (u64Byte value 1)))
              ⟨memId, addr + 2⟩ (some (u64Byte value 2)))
            ⟨memId, addr + 3⟩ (some (u64Byte value 3)))
          ⟨memId, addr + 4⟩ (some (u64Byte value 4)))
        ⟨memId, addr + 5⟩ (some (u64Byte value 5)))
      ⟨memId, addr + 6⟩ (some (u64Byte value 6)))
    ⟨memId, addr + 7⟩ (some (u64Byte value 7))

theorem store64Heap_pointsTo {α : Type} [WasmHeapGS α]
    (σ : WasmHeapMap (Option UInt8)) (memId : Nat) (addr : UInt32) (value : UInt64)
    (h0 : get? σ ⟨memId, addr⟩ = none)
    (h1 : get? (insert σ ⟨memId, addr⟩ (some (u64Byte value 0))) ⟨memId, addr + 1⟩ = none)
    (h2 : get?
      (insert (insert σ ⟨memId, addr⟩ (some (u64Byte value 0)))
        ⟨memId, addr + 1⟩ (some (u64Byte value 1))) ⟨memId, addr + 2⟩ = none)
    (h3 : get?
      (insert
        (insert (insert σ ⟨memId, addr⟩ (some (u64Byte value 0)))
          ⟨memId, addr + 1⟩ (some (u64Byte value 1)))
        ⟨memId, addr + 2⟩ (some (u64Byte value 2))) ⟨memId, addr + 3⟩ = none)
    (h4 : get?
      (insert
        (insert
          (insert (insert σ ⟨memId, addr⟩ (some (u64Byte value 0)))
            ⟨memId, addr + 1⟩ (some (u64Byte value 1)))
          ⟨memId, addr + 2⟩ (some (u64Byte value 2)))
        ⟨memId, addr + 3⟩ (some (u64Byte value 3))) ⟨memId, addr + 4⟩ = none)
    (h5 : get?
      (insert
        (insert
          (insert
            (insert (insert σ ⟨memId, addr⟩ (some (u64Byte value 0)))
              ⟨memId, addr + 1⟩ (some (u64Byte value 1)))
            ⟨memId, addr + 2⟩ (some (u64Byte value 2)))
          ⟨memId, addr + 3⟩ (some (u64Byte value 3)))
        ⟨memId, addr + 4⟩ (some (u64Byte value 4))) ⟨memId, addr + 5⟩ = none)
    (h6 : get?
      (insert
        (insert
          (insert
            (insert
              (insert (insert σ ⟨memId, addr⟩ (some (u64Byte value 0)))
                ⟨memId, addr + 1⟩ (some (u64Byte value 1)))
              ⟨memId, addr + 2⟩ (some (u64Byte value 2)))
            ⟨memId, addr + 3⟩ (some (u64Byte value 3)))
          ⟨memId, addr + 4⟩ (some (u64Byte value 4)))
        ⟨memId, addr + 5⟩ (some (u64Byte value 5))) ⟨memId, addr + 6⟩ = none)
    (h7 : get?
      (insert
        (insert
          (insert
            (insert
              (insert
                (insert (insert σ ⟨memId, addr⟩ (some (u64Byte value 0)))
                  ⟨memId, addr + 1⟩ (some (u64Byte value 1)))
                ⟨memId, addr + 2⟩ (some (u64Byte value 2)))
              ⟨memId, addr + 3⟩ (some (u64Byte value 3)))
            ⟨memId, addr + 4⟩ (some (u64Byte value 4)))
          ⟨memId, addr + 5⟩ (some (u64Byte value 5)))
        ⟨memId, addr + 6⟩ (some (u64Byte value 6))) ⟨memId, addr + 7⟩ = none) :
    ([∗map] address ↦ byte ∈ store64Heap σ memId addr value,
      pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        address (DFrac.own 1) byte) ⊢
      pointsTo_u64 memId addr value ∗
      ([∗map] address ↦ byte ∈ σ,
        pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
          address (DFrac.own 1) byte) := by
  unfold store64Heap
  rw [(BI.BigSepM.bigSepM_insert h7).to_eq]
  rw [(BI.BigSepM.bigSepM_insert h6).to_eq]
  rw [(BI.BigSepM.bigSepM_insert h5).to_eq]
  rw [(BI.BigSepM.bigSepM_insert h4).to_eq]
  rw [(BI.BigSepM.bigSepM_insert h3).to_eq]
  rw [(BI.BigSepM.bigSepM_insert h2).to_eq]
  rw [(BI.BigSepM.bigSepM_insert h1).to_eq]
  rw [(BI.BigSepM.bigSepM_insert h0).to_eq]
  unfold pointsTo_u64
  iintro ⟨H7, H6, H5, H4, H3, H2, H1, H0, Hrest⟩
  iframe

theorem store64_sound (σ : WasmHeapMap (Option UInt8)) (resolve : Nat → Option Mem)
    (memId : Nat) (mem : Mem) (addr : UInt32) (value : UInt64)
    (h_resolve : resolve memId = some mem)
    (h1 : (addr + 1).toNat = addr.toNat + 1)
    (h2 : (addr + 2).toNat = addr.toNat + 2)
    (h3 : (addr + 3).toNat = addr.toNat + 3)
    (h4 : (addr + 4).toNat = addr.toNat + 4)
    (h5 : (addr + 5).toNat = addr.toNat + 5)
    (h6 : (addr + 6).toNat = addr.toNat + 6)
    (h7 : (addr + 7).toNat = addr.toNat + 7)
    (h_agree : heapAgreesWithMem σ resolve) :
    heapAgreesWithMem (store64Heap σ memId addr value)
      (fun id => if id = memId then some (mem.write64 addr value) else resolve id) := by
  intro key byte h_get
  by_cases e7 : key = ⟨memId, addr + 7⟩
  · subst key
    simp [store64Heap, get?_insert_eq] at h_get; rw [← h_get]
    refine ⟨mem.write64 addr value, ?_, ?_⟩; · simp
    · simp [Mem.write64, Mem.read8, h7, u64Byte]; bv_decide
  by_cases e6 : key = ⟨memId, addr + 6⟩
  · subst key
    simp [store64Heap, get?_insert_ne (Ne.symm e7), get?_insert_eq] at h_get; rw [← h_get]
    refine ⟨mem.write64 addr value, ?_, ?_⟩; · simp
    · simp [Mem.write64, Mem.read8, h6, u64Byte]; bv_decide
  by_cases e5 : key = ⟨memId, addr + 5⟩
  · subst key
    simp [store64Heap, get?_insert_ne (Ne.symm e7),
      get?_insert_ne (Ne.symm e6), get?_insert_eq] at h_get; rw [← h_get]
    refine ⟨mem.write64 addr value, ?_, ?_⟩; · simp
    · simp [Mem.write64, Mem.read8, h5, u64Byte]; bv_decide
  by_cases e4 : key = ⟨memId, addr + 4⟩
  · subst key
    simp [store64Heap, get?_insert_ne (Ne.symm e7),
      get?_insert_ne (Ne.symm e6), get?_insert_ne (Ne.symm e5),
      get?_insert_eq] at h_get; rw [← h_get]
    refine ⟨mem.write64 addr value, ?_, ?_⟩; · simp
    · simp [Mem.write64, Mem.read8, h4, u64Byte]; bv_decide
  by_cases e3 : key = ⟨memId, addr + 3⟩
  · subst key
    simp [store64Heap, get?_insert_ne (Ne.symm e7),
      get?_insert_ne (Ne.symm e6), get?_insert_ne (Ne.symm e5),
      get?_insert_ne (Ne.symm e4), get?_insert_eq] at h_get; rw [← h_get]
    refine ⟨mem.write64 addr value, ?_, ?_⟩; · simp
    · simp [Mem.write64, Mem.read8, h3, u64Byte]; bv_decide
  by_cases e2 : key = ⟨memId, addr + 2⟩
  · subst key
    simp [store64Heap, get?_insert_ne (Ne.symm e7),
      get?_insert_ne (Ne.symm e6), get?_insert_ne (Ne.symm e5),
      get?_insert_ne (Ne.symm e4), get?_insert_ne (Ne.symm e3),
      get?_insert_eq] at h_get; rw [← h_get]
    refine ⟨mem.write64 addr value, ?_, ?_⟩; · simp
    · simp [Mem.write64, Mem.read8, h2, u64Byte]; bv_decide
  by_cases e1 : key = ⟨memId, addr + 1⟩
  · subst key
    simp [store64Heap, get?_insert_ne (Ne.symm e7),
      get?_insert_ne (Ne.symm e6), get?_insert_ne (Ne.symm e5),
      get?_insert_ne (Ne.symm e4), get?_insert_ne (Ne.symm e3),
      get?_insert_ne (Ne.symm e2), get?_insert_eq] at h_get; rw [← h_get]
    refine ⟨mem.write64 addr value, ?_, ?_⟩; · simp
    · simp [Mem.write64, Mem.read8, h1, u64Byte]; bv_decide
  by_cases e0 : key = ⟨memId, addr⟩
  · subst key
    simp [store64Heap, get?_insert_ne (Ne.symm e7),
      get?_insert_ne (Ne.symm e6), get?_insert_ne (Ne.symm e5),
      get?_insert_ne (Ne.symm e4), get?_insert_ne (Ne.symm e3),
      get?_insert_ne (Ne.symm e2), get?_insert_ne (Ne.symm e1),
      get?_insert_eq] at h_get; rw [← h_get]
    refine ⟨mem.write64 addr value, ?_, ?_⟩; · simp
    · simp [Mem.write64, Mem.read8, u64Byte]; bv_decide
  · simp [store64Heap, get?_insert_ne (Ne.symm e7),
      get?_insert_ne (Ne.symm e6), get?_insert_ne (Ne.symm e5),
      get?_insert_ne (Ne.symm e4), get?_insert_ne (Ne.symm e3),
      get?_insert_ne (Ne.symm e2), get?_insert_ne (Ne.symm e1),
      get?_insert_ne (Ne.symm e0)] at h_get
    obtain ⟨m, hm, hread⟩ := h_agree key byte h_get
    by_cases hid : key.memId = memId
    · have hm_eq : m = mem := Option.some.inj ((hid ▸ hm).symm.trans h_resolve)
      have n0 : key.addr.toNat ≠ addr.toNat :=
        fun h => e0 (show key = ⟨memId, addr⟩ from by
          cases key; simp only [MemoryKey.mk.injEq]; exact ⟨hid, UInt32.toNat_inj.mp h⟩)
      have n1 : key.addr.toNat ≠ addr.toNat + 1 := by
        rw [← h1]
        exact fun h => e1 (show key = ⟨memId, addr + 1⟩ from by
          cases key; simp only [MemoryKey.mk.injEq]; exact ⟨hid, UInt32.toNat_inj.mp h⟩)
      have n2 : key.addr.toNat ≠ addr.toNat + 2 := by
        rw [← h2]
        exact fun h => e2 (show key = ⟨memId, addr + 2⟩ from by
          cases key; simp only [MemoryKey.mk.injEq]; exact ⟨hid, UInt32.toNat_inj.mp h⟩)
      have n3 : key.addr.toNat ≠ addr.toNat + 3 := by
        rw [← h3]
        exact fun h => e3 (show key = ⟨memId, addr + 3⟩ from by
          cases key; simp only [MemoryKey.mk.injEq]; exact ⟨hid, UInt32.toNat_inj.mp h⟩)
      have n4 : key.addr.toNat ≠ addr.toNat + 4 := by
        rw [← h4]
        exact fun h => e4 (show key = ⟨memId, addr + 4⟩ from by
          cases key; simp only [MemoryKey.mk.injEq]; exact ⟨hid, UInt32.toNat_inj.mp h⟩)
      have n5 : key.addr.toNat ≠ addr.toNat + 5 := by
        rw [← h5]
        exact fun h => e5 (show key = ⟨memId, addr + 5⟩ from by
          cases key; simp only [MemoryKey.mk.injEq]; exact ⟨hid, UInt32.toNat_inj.mp h⟩)
      have n6 : key.addr.toNat ≠ addr.toNat + 6 := by
        rw [← h6]
        exact fun h => e6 (show key = ⟨memId, addr + 6⟩ from by
          cases key; simp only [MemoryKey.mk.injEq]; exact ⟨hid, UInt32.toNat_inj.mp h⟩)
      have n7 : key.addr.toNat ≠ addr.toNat + 7 := by
        rw [← h7]
        exact fun h => e7 (show key = ⟨memId, addr + 7⟩ from by
          cases key; simp only [MemoryKey.mk.injEq]; exact ⟨hid, UInt32.toNat_inj.mp h⟩)
      refine ⟨mem.write64 addr value, ?_, ?_⟩
      · simp [hid]
      · simpa [Mem.write64, Mem.read8, n0, n1, n2, n3, n4, n5, n6, n7, hm_eq] using hread
    · exact ⟨m, by simp [if_neg hid, hm], hread⟩

theorem store64_inBounds (σ : WasmHeapMap (Option UInt8)) (resolve : Nat → Option Mem)
    (memId : Nat) (mem : Mem) (addr : UInt32) (value : UInt64)
    (h_resolve : resolve memId = some mem)
    (h1 : (addr + 1).toNat = addr.toNat + 1)
    (h2 : (addr + 2).toNat = addr.toNat + 2)
    (h3 : (addr + 3).toNat = addr.toNat + 3)
    (h4 : (addr + 4).toNat = addr.toNat + 4)
    (h5 : (addr + 5).toNat = addr.toNat + 5)
    (h6 : (addr + 6).toNat = addr.toNat + 6)
    (h7 : (addr + 7).toNat = addr.toNat + 7)
    (h_addresses : heapAddressesInBounds σ resolve)
    (h_addr : addr.toNat + 8 ≤ mem.pages * 65536) :
    heapAddressesInBounds (store64Heap σ memId addr value)
      (fun id => if id = memId then some (mem.write64 addr value) else resolve id) := by
  intro key h_get
  by_cases e7 : key = ⟨memId, addr + 7⟩
  · subst key; refine ⟨mem.write64 addr value, ?_, ?_⟩; · simp
    · simp [Mem.write64, h7]; omega
  by_cases e6 : key = ⟨memId, addr + 6⟩
  · subst key; refine ⟨mem.write64 addr value, ?_, ?_⟩; · simp
    · simp [Mem.write64, h6]; omega
  by_cases e5 : key = ⟨memId, addr + 5⟩
  · subst key; refine ⟨mem.write64 addr value, ?_, ?_⟩; · simp
    · simp [Mem.write64, h5]; omega
  by_cases e4 : key = ⟨memId, addr + 4⟩
  · subst key; refine ⟨mem.write64 addr value, ?_, ?_⟩; · simp
    · simp [Mem.write64, h4]; omega
  by_cases e3 : key = ⟨memId, addr + 3⟩
  · subst key; refine ⟨mem.write64 addr value, ?_, ?_⟩; · simp
    · simp [Mem.write64, h3]; omega
  by_cases e2 : key = ⟨memId, addr + 2⟩
  · subst key; refine ⟨mem.write64 addr value, ?_, ?_⟩; · simp
    · simp [Mem.write64, h2]; omega
  by_cases e1 : key = ⟨memId, addr + 1⟩
  · subst key; refine ⟨mem.write64 addr value, ?_, ?_⟩; · simp
    · simp [Mem.write64, h1]; omega
  by_cases e0 : key = ⟨memId, addr⟩
  · subst key; refine ⟨mem.write64 addr value, ?_, ?_⟩; · simp
    · simp [Mem.write64]; omega
  · simp [store64Heap, get?_insert_ne (Ne.symm e7),
      get?_insert_ne (Ne.symm e6), get?_insert_ne (Ne.symm e5),
      get?_insert_ne (Ne.symm e4), get?_insert_ne (Ne.symm e3),
      get?_insert_ne (Ne.symm e2), get?_insert_ne (Ne.symm e1),
      get?_insert_ne (Ne.symm e0)] at h_get
    obtain ⟨m, hm, hlt⟩ := h_addresses key h_get
    by_cases hid : key.memId = memId
    · have hm_eq : m = mem := Option.some.inj ((hid ▸ hm).symm.trans h_resolve)
      refine ⟨mem.write64 addr value, ?_, ?_⟩
      · simp [hid]
      · simpa [Mem.write64, hm_eq] using hlt
    · exact ⟨m, by simp [if_neg hid, hm], hlt⟩

-- single-memory-0 wrappers for the common case where resolve = (fun id => if id = 0 then some mem else none)
theorem store32_sound0 (σ : WasmHeapMap (Option UInt8))
    (mem : Mem) (addr value : UInt32)
    (h1 : (addr + 1).toNat = addr.toNat + 1)
    (h2 : (addr + 2).toNat = addr.toNat + 2)
    (h3 : (addr + 3).toNat = addr.toNat + 3)
    (h_agree : heapAgreesWithMem σ (fun id => if id = 0 then some mem else none)) :
    heapAgreesWithMem (store32Heap σ 0 addr value)
      (fun id => if id = 0 then some (mem.write32 addr value) else none) := by
  have h := store32_sound σ (fun id => if id = 0 then some mem else none) 0 mem addr value rfl h1 h2 h3 h_agree
  have heq : (fun id : Nat => if id = 0 then some (mem.write32 addr value)
      else if id = 0 then some mem else none) =
      fun id => if id = 0 then some (mem.write32 addr value) else none := by
    funext id; by_cases hid : id = 0 <;> simp [hid]
  rwa [heq] at h

theorem store32_inBounds0 (σ : WasmHeapMap (Option UInt8))
    (mem : Mem) (addr value : UInt32)
    (h1 : (addr + 1).toNat = addr.toNat + 1)
    (h2 : (addr + 2).toNat = addr.toNat + 2)
    (h3 : (addr + 3).toNat = addr.toNat + 3)
    (h_addr : addr.toNat + 4 ≤ mem.pages * 65536)
    (h_addresses : heapAddressesInBounds σ (fun id => if id = 0 then some mem else none)) :
    heapAddressesInBounds (store32Heap σ 0 addr value)
      (fun id => if id = 0 then some (mem.write32 addr value) else none) := by
  have h := store32_inBounds σ (fun id => if id = 0 then some mem else none) 0 mem addr value rfl h1 h2 h3 h_addresses h_addr
  have heq : (fun id : Nat => if id = 0 then some (mem.write32 addr value)
      else if id = 0 then some mem else none) =
      fun id => if id = 0 then some (mem.write32 addr value) else none := by
    funext id; by_cases hid : id = 0 <;> simp [hid]
  rwa [heq] at h

theorem store64_sound0 (σ : WasmHeapMap (Option UInt8))
    (mem : Mem) (addr : UInt32) (value : UInt64)
    (h1 : (addr + 1).toNat = addr.toNat + 1)
    (h2 : (addr + 2).toNat = addr.toNat + 2)
    (h3 : (addr + 3).toNat = addr.toNat + 3)
    (h4 : (addr + 4).toNat = addr.toNat + 4)
    (h5 : (addr + 5).toNat = addr.toNat + 5)
    (h6 : (addr + 6).toNat = addr.toNat + 6)
    (h7 : (addr + 7).toNat = addr.toNat + 7)
    (h_agree : heapAgreesWithMem σ (fun id => if id = 0 then some mem else none)) :
    heapAgreesWithMem (store64Heap σ 0 addr value)
      (fun id => if id = 0 then some (mem.write64 addr value) else none) := by
  have h := store64_sound σ (fun id => if id = 0 then some mem else none) 0 mem addr value rfl h1 h2 h3 h4 h5 h6 h7 h_agree
  have heq : (fun id : Nat => if id = 0 then some (mem.write64 addr value)
      else if id = 0 then some mem else none) =
      fun id => if id = 0 then some (mem.write64 addr value) else none := by
    funext id; by_cases hid : id = 0 <;> simp [hid]
  rwa [heq] at h

theorem store64_inBounds0 (σ : WasmHeapMap (Option UInt8))
    (mem : Mem) (addr : UInt32) (value : UInt64)
    (h1 : (addr + 1).toNat = addr.toNat + 1)
    (h2 : (addr + 2).toNat = addr.toNat + 2)
    (h3 : (addr + 3).toNat = addr.toNat + 3)
    (h4 : (addr + 4).toNat = addr.toNat + 4)
    (h5 : (addr + 5).toNat = addr.toNat + 5)
    (h6 : (addr + 6).toNat = addr.toNat + 6)
    (h7 : (addr + 7).toNat = addr.toNat + 7)
    (h_addr : addr.toNat + 8 ≤ mem.pages * 65536)
    (h_addresses : heapAddressesInBounds σ (fun id => if id = 0 then some mem else none)) :
    heapAddressesInBounds (store64Heap σ 0 addr value)
      (fun id => if id = 0 then some (mem.write64 addr value) else none) := by
  have h := store64_inBounds σ (fun id => if id = 0 then some mem else none) 0 mem addr value rfl h1 h2 h3 h4 h5 h6 h7 h_addresses h_addr
  have heq : (fun id : Nat => if id = 0 then some (mem.write64 addr value)
      else if id = 0 then some mem else none) =
      fun id => if id = 0 then some (mem.write64 addr value) else none := by
    funext id; by_cases hid : id = 0 <;> simp [hid]
  rwa [heq] at h

end Wasm.SepLogic
