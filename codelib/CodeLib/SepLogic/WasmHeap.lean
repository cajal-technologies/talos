import Iris.ProofMode
import Iris.Instances.Lib.FUpd
import Iris.BI.Lib.GenHeap
import Interpreter.Wasm.Mem
import Interpreter.Wasm.Syntax
import Std.Tactic.BVDecide
/-! # Wasm Memory as an Iris GenHeap
Instantiates iris-lean's GenHeap for Wasm byte-level memory.
Location = UInt32 (byte address), Value = Option UInt8 (byte).
-/
namespace Wasm.SepLogic
open Iris Std
abbrev WasmHeapMap := fun V => ExtTreeMap UInt32 V compare
abbrev WasmGlobalMap := fun V => ExtTreeMap Nat V compare
abbrev WasmDataSegmentMap := fun V => ExtTreeMap Nat V compare
abbrev WasmTableMap := fun V => ExtTreeMap Nat V compare
abbrev WasmElementSegmentMap := fun V => ExtTreeMap Nat V compare
abbrev WasmHeapGF : BundledGFunctors
  | 0 => ⟨InvMapF, by infer_instance⟩
  | 1 => ⟨constOF (DisjointLeibnizSet CoPset), by infer_instance⟩
  | 2 => ⟨constOF (DisjointLeibnizSet PosSet), by infer_instance⟩
  | 3 => ⟨Auth.AuthURF (constOF Credit), by infer_instance⟩
  | 4 => ⟨constOF (HeapView UInt32 (Agree (DiscreteO (Option UInt8))) WasmHeapMap), by infer_instance⟩
  | 5 => ⟨constOF (HeapView UInt32 (Agree (DiscreteO GName)) WasmHeapMap), by infer_instance⟩
  | 6 => ⟨constOF MetaUR, by infer_instance⟩
  | 7 => ⟨constOF (HeapView Nat (Agree (DiscreteO Value)) WasmGlobalMap),
      by infer_instance⟩
  | 8 => ⟨constOF (Agree (DiscreteO Module)), by infer_instance⟩
  | 9 => ⟨constOF
      (HeapView Nat (Agree (DiscreteO (Option (List UInt8))))
        WasmDataSegmentMap), by infer_instance⟩
  | 10 => ⟨constOF
      (HeapView Nat (Agree (DiscreteO TableInst)) WasmTableMap),
      by infer_instance⟩
  | 11 => ⟨constOF
      (HeapView Nat (Agree (DiscreteO (Option (List (Option Nat)))))
        WasmElementSegmentMap), by infer_instance⟩
  | _ => ⟨constOF Unit, by infer_instance⟩
-- Wire genHeapPreS (following HeapLang's instHeapLangGS_HeapLangS)
instance instWasmHeapPreS : genHeapPreS UInt32 (Option UInt8) WasmHeapGF WasmHeapMap where
  heap := by constructor; exists 4
  metaInfo := by constructor; exists 5
  metaData := by exists 6
-- The full genHeap instance with ghost names
class WasmHeapGS extends genHeapGS UInt32 (Option UInt8) WasmHeapGF WasmHeapMap

/-- Globals use a directly named ghost map instead of a second `genHeapGS`.
All identifying parameters of `genHeapGS` are output parameters, so two
simultaneous GenHeap instances are ambiguous to typeclass search. -/
class WasmGlobalGS extends GhostMapG WasmHeapGF Nat Value WasmGlobalMap where
  globalName : GName

attribute [instance] WasmGlobalGS.toGhostMapG

/-- Passive data segments use their own named authoritative ghost map.  An
entry remains present after `data.drop`, but its value changes from
`some bytes` to `none`, mirroring the instantiated store exactly at every
owned segment index. -/
class WasmDataSegmentGS extends
    GhostMapG WasmHeapGF Nat (Option (List UInt8)) WasmDataSegmentMap where
  dataSegmentName : GName

attribute [instance] WasmDataSegmentGS.toGhostMapG

/-- Instantiated tables use stable table indices as authoritative ghost-map
keys.  A fragment owns one complete table; element-level rules preserve or
update that fragment together with the physical table. -/
class WasmTableGS extends
    GhostMapG WasmHeapGF Nat TableInst WasmTableMap where
  tableName : GName

attribute [instance] WasmTableGS.toGhostMapG

/-- Instantiated element segments retain stable indices after `elem.drop`.
Their optional payload is authoritative so `table.init` reads the physical
live segment and `elem.drop` changes both views to `none`. -/
class WasmElementSegmentGS extends
    GhostMapG WasmHeapGF Nat (Option (List (Option Nat)))
      WasmElementSegmentMap where
  elementSegmentName : GName

attribute [instance] WasmElementSegmentGS.toGhostMapG

class WasmRuntimeModuleGS where
  runtimeElem :
    ElemG WasmHeapGF.{0} (constOF (Agree (DiscreteO Module)))
  runtimeName : GName

attribute [reducible, instance] WasmRuntimeModuleGS.runtimeElem

def globalPointsTo [gs : WasmGlobalGS] (index : Nat) (value : Value) :
    IProp WasmHeapGF :=
  ghost_map_elem gs.globalName (DFrac.own 1) index value

instance [WasmGlobalGS] (index : Nat) (value : Value) :
    BI.Timeless (globalPointsTo index value) := by
  unfold globalPointsTo
  infer_instance

theorem globalPointsTo_lookup [gs : WasmGlobalGS]
    (σ : WasmGlobalMap Value) (index : Nat) (value : Value) :
    ghost_map_auth gs.globalName (DFrac.own 1) σ -∗
      globalPointsTo index value -∗
      iprop(⌜get? σ index = some value⌝) := by
  unfold globalPointsTo
  iapply ghost_map_lookup

/-- Authoritative update for one owned global entry. -/
theorem globalPointsTo_update [gs : WasmGlobalGS]
    (σ : WasmGlobalMap Value) (index : Nat)
    (oldValue newValue : Value) :
    ghost_map_auth gs.globalName (DFrac.own 1) σ -∗
      globalPointsTo index oldValue ==∗
      ghost_map_auth gs.globalName (DFrac.own 1)
        (insert σ index newValue) ∗
      globalPointsTo index newValue := by
  unfold globalPointsTo
  iapply ghost_map_update

def dataSegmentPointsTo [gs : WasmDataSegmentGS]
    (index : Nat) (value : Option (List UInt8)) : IProp WasmHeapGF :=
  ghost_map_elem gs.dataSegmentName (DFrac.own 1) index value

instance [WasmDataSegmentGS] (index : Nat)
    (value : Option (List UInt8)) :
    BI.Timeless (dataSegmentPointsTo index value) := by
  unfold dataSegmentPointsTo
  infer_instance

theorem dataSegmentPointsTo_lookup [gs : WasmDataSegmentGS]
    (σ : WasmDataSegmentMap (Option (List UInt8)))
    (index : Nat) (value : Option (List UInt8)) :
    ghost_map_auth gs.dataSegmentName (DFrac.own 1) σ -∗
      dataSegmentPointsTo index value -∗
      iprop(⌜get? σ index = some value⌝) := by
  unfold dataSegmentPointsTo
  iapply ghost_map_lookup

theorem dataSegmentPointsTo_update [gs : WasmDataSegmentGS]
    (σ : WasmDataSegmentMap (Option (List UInt8)))
    (index : Nat) (oldValue newValue : Option (List UInt8)) :
    ghost_map_auth gs.dataSegmentName (DFrac.own 1) σ -∗
      dataSegmentPointsTo index oldValue ==∗
      ghost_map_auth gs.dataSegmentName (DFrac.own 1)
        (insert σ index newValue) ∗
      dataSegmentPointsTo index newValue := by
  unfold dataSegmentPointsTo
  iapply ghost_map_update

def tablePointsTo [gs : WasmTableGS]
    (index : Nat) (table : TableInst) : IProp WasmHeapGF :=
  ghost_map_elem gs.tableName (DFrac.own 1) index table

instance [WasmTableGS] (index : Nat) (table : TableInst) :
    BI.Timeless (tablePointsTo index table) := by
  unfold tablePointsTo
  infer_instance

theorem tablePointsTo_lookup [gs : WasmTableGS]
    (σ : WasmTableMap TableInst) (index : Nat) (table : TableInst) :
    ghost_map_auth gs.tableName (DFrac.own 1) σ -∗
      tablePointsTo index table -∗
      iprop(⌜get? σ index = some table⌝) := by
  unfold tablePointsTo
  iapply ghost_map_lookup

theorem tablePointsTo_update [gs : WasmTableGS]
    (σ : WasmTableMap TableInst) (index : Nat)
    (oldTable newTable : TableInst) :
    ghost_map_auth gs.tableName (DFrac.own 1) σ -∗
      tablePointsTo index oldTable ==∗
      ghost_map_auth gs.tableName (DFrac.own 1)
        (insert σ index newTable) ∗
      tablePointsTo index newTable := by
  unfold tablePointsTo
  iapply ghost_map_update

def elementSegmentPointsTo [gs : WasmElementSegmentGS]
    (index : Nat) (value : Option (List (Option Nat))) :
    IProp WasmHeapGF :=
  ghost_map_elem gs.elementSegmentName (DFrac.own 1) index value

instance [WasmElementSegmentGS] (index : Nat)
    (value : Option (List (Option Nat))) :
    BI.Timeless (elementSegmentPointsTo index value) := by
  unfold elementSegmentPointsTo
  infer_instance

theorem elementSegmentPointsTo_lookup [gs : WasmElementSegmentGS]
    (σ : WasmElementSegmentMap (Option (List (Option Nat))))
    (index : Nat) (value : Option (List (Option Nat))) :
    ghost_map_auth gs.elementSegmentName (DFrac.own 1) σ -∗
      elementSegmentPointsTo index value -∗
      iprop(⌜get? σ index = some value⌝) := by
  unfold elementSegmentPointsTo
  iapply ghost_map_lookup

theorem elementSegmentPointsTo_update [gs : WasmElementSegmentGS]
    (σ : WasmElementSegmentMap (Option (List (Option Nat))))
    (index : Nat) (oldValue newValue : Option (List (Option Nat))) :
    ghost_map_auth gs.elementSegmentName (DFrac.own 1) σ -∗
      elementSegmentPointsTo index oldValue ==∗
      ghost_map_auth gs.elementSegmentName (DFrac.own 1)
        (insert σ index newValue) ∗
      elementSegmentPointsTo index newValue := by
  unfold elementSegmentPointsTo
  iapply ghost_map_update

/-- Persistent knowledge of the immutable instantiated module. Agreement with
the copy held by `StateInterp` lets call rules justify function-table lookups
against the actual machine runtime. -/
def runtimeModuleOwn [gs : WasmRuntimeModuleGS] (m : Module) :
    IProp WasmHeapGF.{0} :=
  iOwn (E := gs.runtimeElem) gs.runtimeName (toAgree ⟨m⟩)

instance [WasmRuntimeModuleGS] (m : Module) :
    BI.Persistent (runtimeModuleOwn m) := by
  unfold runtimeModuleOwn
  infer_instance

instance [WasmRuntimeModuleGS] (m : Module) :
    BI.Timeless (runtimeModuleOwn m) := by
  unfold runtimeModuleOwn
  infer_instance

theorem runtimeModuleOwn_agree [gs : WasmRuntimeModuleGS]
    (actual expected : Module) :
    runtimeModuleOwn actual ∗ runtimeModuleOwn expected ⊢
      iprop(⌜actual = expected⌝) := by
  unfold runtimeModuleOwn
  iintro ⟨Hactual, Hexpected⟩
  icombine Hactual Hexpected gives %Hvalid
  ipureintro
  exact congrArg DiscreteO.car (toAgree_op_valid_iff_eq.mp Hvalid)
/-! ## Points-to assertions

Byte-level `↦w` plus multi-byte and array derived forms.

**Address arithmetic caveat:** the multi-byte assertions below compute
their footprint with `UInt32` addition (`addr + 1`, …), which wraps
mod 2^32, whereas the interpreter's `Mem.read64`/`write64` index bytes at
`addr.toNat + k : Nat` with no wraparound. The two footprints agree only
when the access does not overflow the 32-bit address space (e.g.
`addr.toNat + 8 ≤ 2^32` for `pointsTo_u64`, and
`ptr.toNat + 4 * xs.length ≤ 2^32` for `arrayAt`). Any future rule
bridging these assertions to `Mem.read*/write*` must carry such a
no-overflow side condition — without it the ghost footprint at high
addresses wraps to low addresses and the bridge would be unprovable (or
unsound if forced). -/
section PointsTo
variable [inst : WasmHeapGS]
-- Notation for Wasm points-to (scoped: available inside this namespace
-- and via `open Wasm.SepLogic`, without leaking through the CodeLib umbrella)
scoped notation:50 addr:50 " ↦w " v:50 => pointsTo (L := UInt32) (V := Option UInt8)
    (GF := WasmHeapGF) (H := WasmHeapMap) addr (DFrac.own 1) (some v)
/-- The `n`th little-endian byte of a 64-bit word. Values above seven select
the final byte; all uses in a word footprint pass an index in `[0, 7]`. -/
def u64Byte (v : UInt64) (n : Nat) : UInt8 :=
  match n with
  | 0 => v.toUInt8
  | 1 => (v >>> 8).toUInt8
  | 2 => (v >>> 16).toUInt8
  | 3 => (v >>> 24).toUInt8
  | 4 => (v >>> 32).toUInt8
  | 5 => (v >>> 40).toUInt8
  | 6 => (v >>> 48).toUInt8
  | _ => (v >>> 56).toUInt8

omit inst in
theorem u64Byte_reassemble (v : UInt64) :
    (u64Byte v 0).toUInt64 ||| ((u64Byte v 1).toUInt64 <<< 8) |||
      ((u64Byte v 2).toUInt64 <<< 16) |||
      ((u64Byte v 3).toUInt64 <<< 24) |||
      ((u64Byte v 4).toUInt64 <<< 32) |||
      ((u64Byte v 5).toUInt64 <<< 40) |||
      ((u64Byte v 6).toUInt64 <<< 48) |||
      ((u64Byte v 7).toUInt64 <<< 56) = v := by
  unfold u64Byte
  bv_decide

-- Multi-byte: u64 as 8 consecutive owned bytes (little-endian)
def pointsTo_u64 (addr : UInt32) (v : UInt64) : IProp WasmHeapGF :=
  iprop%
    (addr ↦w u64Byte v 0) ∗ ((addr + 1) ↦w u64Byte v 1) ∗
    ((addr + 2) ↦w u64Byte v 2) ∗ ((addr + 3) ↦w u64Byte v 3) ∗
    ((addr + 4) ↦w u64Byte v 4) ∗ ((addr + 5) ↦w u64Byte v 5) ∗
    ((addr + 6) ↦w u64Byte v 6) ∗ ((addr + 7) ↦w u64Byte v 7)

theorem pointsTo_u64_eq (addr : UInt32) (v : UInt64) :
    pointsTo_u64 addr v ⊣⊢
      (iprop%
        (addr ↦w u64Byte v 0) ∗ ((addr + 1) ↦w u64Byte v 1) ∗
        ((addr + 2) ↦w u64Byte v 2) ∗ ((addr + 3) ↦w u64Byte v 3) ∗
        ((addr + 4) ↦w u64Byte v 4) ∗ ((addr + 5) ↦w u64Byte v 5) ∗
        ((addr + 6) ↦w u64Byte v 6) ∗ ((addr + 7) ↦w u64Byte v 7)) :=
  .rfl

instance instTimelessPointsToU64 (addr : UInt32) (v : UInt64) :
    BI.Timeless (pointsTo_u64 addr v) := by
  unfold pointsTo_u64
  infer_instance

omit inst in
theorem UInt32.add_ofNat_toNat_noWrap (addr : UInt32) (n : Nat)
    (hn : n < 4294967296) (hroom : addr.toNat + n < 4294967296) :
    (addr + UInt32.ofNat n).toNat = addr.toNat + n := by
  rw [UInt32.toNat_add,
    UInt32.toNat_ofNat_of_lt' (by simpa only [UInt32.size] using hn)]
  omega

/-- The `n`th little-endian byte of a 32-bit word. -/
def u32Byte (v : UInt32) (n : Nat) : UInt8 :=
  match n with
  | 0 => v.toUInt8
  | 1 => (v >>> 8).toUInt8
  | 2 => (v >>> 16).toUInt8
  | _ => (v >>> 24).toUInt8

omit inst in
theorem u32Byte_reassemble (v : UInt32) :
    (u32Byte v 0).toUInt32 ||| ((u32Byte v 1).toUInt32 <<< 8) |||
      ((u32Byte v 2).toUInt32 <<< 16) |||
      ((u32Byte v 3).toUInt32 <<< 24) = v := by
  unfold u32Byte
  bv_decide

-- Multi-byte: u32 as 4 consecutive owned bytes (little-endian)
def pointsTo_u32 (addr : UInt32) (v : UInt32) : IProp WasmHeapGF :=
  iprop%
    (addr ↦w u32Byte v 0) ∗ ((addr + 1) ↦w u32Byte v 1) ∗
    ((addr + 2) ↦w u32Byte v 2) ∗ ((addr + 3) ↦w u32Byte v 3)

theorem pointsTo_u32_eq (addr v : UInt32) :
    pointsTo_u32 addr v ⊣⊢
      (iprop% (addr ↦w u32Byte v 0) ∗
        ((addr + 1) ↦w u32Byte v 1) ∗
        ((addr + 2) ↦w u32Byte v 2) ∗
        ((addr + 3) ↦w u32Byte v 3)) :=
  .rfl

instance instTimelessPointsToU32 (addr v : UInt32) :
    BI.Timeless (pointsTo_u32 addr v) := by
  unfold pointsTo_u32
  infer_instance
-- Array ownership: n consecutive u32 elements at ptr
-- arrayAt ptr [x₀, x₁, ..., xₙ₋₁] = pointsTo_u32 ptr x₀ ∗ pointsTo_u32 (ptr+4) x₁ ∗ ...
def arrayAt (ptr : UInt32) (xs : List UInt32) : IProp WasmHeapGF :=
  match xs with
  | [] => iprop% emp
  | x :: rest => iprop% (pointsTo_u32 ptr x) ∗ (arrayAt (ptr + 4) rest)

instance instTimelessArrayAt (ptr : UInt32) (xs : List UInt32) :
    BI.Timeless (arrayAt ptr xs) := by
  induction xs generalizing ptr with
  | nil =>
      simp only [arrayAt]
      infer_instance
  | cons x rest ih =>
      simp only [arrayAt]
      letI := ih (ptr + 4)
      infer_instance
-- element-offset arithmetic shared by the arrayAt lemmas: stepping past
-- the head element shifts the base by one 4-byte stride
omit inst in
private theorem elem_offset_succ (ptr : UInt32) (k : Nat) :
    ptr + 4 * UInt32.ofNat (k + 1) = (ptr + 4) + 4 * UInt32.ofNat k := by
  symm
  rw [UInt32.ofNat_add, show UInt32.ofNat 1 = 1 from rfl, UInt32.mul_add, UInt32.mul_one]
  rw [UInt32.add_assoc ptr 4, UInt32.add_comm 4, ← UInt32.add_assoc]

-- arrayAt splits across ++ : ownership of a concatenation is
-- ownership of both halves (merge_sort_into splits data at mid)
theorem arrayAt_append (ptr : UInt32) (xs ys : List UInt32) :
    arrayAt ptr (xs ++ ys) ⊣⊢
    arrayAt ptr xs ∗ arrayAt (ptr + 4 * UInt32.ofNat xs.length) ys := by
  induction xs generalizing ptr with
  | nil => simp [arrayAt]; exact BI.emp_sep.symm
  | cons x rest ih =>
    simp only [List.cons_append, List.length_cons, arrayAt]
    rw [elem_offset_succ]
    exact (BI.sep_congr_right (ih (ptr + 4))).trans BI.sep_assoc.symm

/-- Split a u32 array into a prefix, its next cell, and the suffix. -/
theorem arrayAt_append_cons (ptr : UInt32) (pre : List UInt32)
    (x : UInt32) (suffix : List UInt32) :
    arrayAt ptr (pre ++ x :: suffix) ⊣⊢
      arrayAt ptr pre ∗
        pointsTo_u32 (ptr + 4 * UInt32.ofNat pre.length) x ∗
        arrayAt ((ptr + 4 * UInt32.ofNat pre.length) + 4) suffix := by
  simpa only [arrayAt] using arrayAt_append ptr pre (x :: suffix)

/-- Focus the next source and destination words of a copy loop.  Returning
both cells to the continuation preserves the source and extends the copied
destination prefix by one word.  Exclusive byte ownership enforces that the
two focused footprints are disjoint. -/
theorem arrayAt_copy_next (dst src : UInt32) (pre : List UInt32)
    (oldDst value : UInt32) (dstSuffix srcSuffix : List UInt32) :
    arrayAt dst (pre ++ oldDst :: dstSuffix) ∗
      arrayAt src (pre ++ value :: srcSuffix) ⊢
      pointsTo_u32 (src + 4 * UInt32.ofNat pre.length) value ∗
      pointsTo_u32 (dst + 4 * UInt32.ofNat pre.length) oldDst ∗
      (pointsTo_u32 (src + 4 * UInt32.ofNat pre.length) value ∗
        pointsTo_u32 (dst + 4 * UInt32.ofNat pre.length) value -∗
        arrayAt dst (pre ++ value :: dstSuffix) ∗
          arrayAt src (pre ++ value :: srcSuffix)) := by
  iintro ⟨Hdst, Hsrc⟩
  icases (arrayAt_append_cons dst pre oldDst dstSuffix).mp $$ Hdst with
    ⟨HdstPre, HdstRest⟩
  icases HdstRest with ⟨HdstCell, HdstSuffix⟩
  icases (arrayAt_append_cons src pre value srcSuffix).mp $$ Hsrc with
    ⟨HsrcPre, HsrcRest⟩
  icases HsrcRest with ⟨HsrcCell, HsrcSuffix⟩
  isplitl [HsrcCell]
  · iexact HsrcCell
  isplitl [HdstCell]
  · iexact HdstCell
  iintro ⟨HsrcCell, HdstCell⟩
  isplitl [HdstPre HdstCell HdstSuffix]
  · iapply (arrayAt_append_cons dst pre value dstSuffix).mpr
    iframe
  · iapply (arrayAt_append_cons src pre value srcSuffix).mpr
    iframe

-- update element k: give back a cell with a NEW value,
-- own the updated array (merge writes out[k] = v)
theorem arrayAt_set (ptr : UInt32) (xs : List UInt32) (k : Nat)
    (v : UInt32) (hk : k < xs.length) :
    arrayAt ptr xs ⊢
    pointsTo_u32 (ptr + 4 * UInt32.ofNat k) xs[k] ∗
    (pointsTo_u32 (ptr + 4 * UInt32.ofNat k) v -∗ arrayAt ptr (xs.set k v)) := by
  induction xs generalizing ptr k with
  | nil => simp at hk
  | cons x rest ih =>
    cases k with
    | zero =>
      simp only [List.getElem_cons_zero, List.set_cons_zero, arrayAt]
      rw [show ptr + 4 * UInt32.ofNat 0 = ptr from by simp [UInt32.ofNat]]
      exact BI.sep_mono .rfl (BI.wand_intro BI.sep_symm)
    | succ k' =>
      simp only [List.length_cons] at hk
      have hk' : k' < rest.length := by omega
      simp only [List.getElem_cons_succ, List.set_cons_succ, arrayAt]
      rw [elem_offset_succ]
      exact (BI.sep_mono_right (ih (ptr + 4) k' hk')).trans
        (BI.sep_left_comm.mp.trans (BI.sep_mono_right
          (BI.wand_intro (BI.sep_assoc.mp.trans (BI.sep_mono_right BI.wand_elim_left)))))

-- extract element k: whole-array ownership gives the single
-- cell plus everything else (merge reads left[i], right[j]).
-- The special case of arrayAt_set that writes back the value just read.
theorem arrayAt_get (ptr : UInt32) (xs : List UInt32) (k : Nat)
    (hk : k < xs.length) :
    arrayAt ptr xs ⊢
    pointsTo_u32 (ptr + 4 * UInt32.ofNat k) xs[k] ∗
    (pointsTo_u32 (ptr + 4 * UInt32.ofNat k) xs[k] -∗ arrayAt ptr xs) := by
  have h := arrayAt_set ptr xs k xs[k] hk
  rwa [List.set_getElem_self] at h

/-! ## Owned arrays of 64-bit words

`array64At` is the u64 counterpart of `arrayAt`.  In particular,
`array64At_append` is the separation-logic form of the prefix/suffix split
used by a fill-loop invariant, while `array64At_set` gives a loop body the
current destination cell and a continuation that reassembles the updated
region.
-/

/-- Ownership of consecutive little-endian u64 words beginning at `ptr`. -/
def array64At (ptr : UInt32) (xs : List UInt64) : IProp WasmHeapGF :=
  match xs with
  | [] => iprop% emp
  | x :: rest => iprop% (pointsTo_u64 ptr x) ∗ (array64At (ptr + 8) rest)

instance instTimelessArray64At (ptr : UInt32) (xs : List UInt64) :
    BI.Timeless (array64At ptr xs) := by
  induction xs generalizing ptr with
  | nil =>
      simp only [array64At]
      infer_instance
  | cons x rest ih =>
      simp only [array64At]
      letI := ih (ptr + 8)
      infer_instance

omit inst in
private theorem elem64_offset_succ (ptr : UInt32) (k : Nat) :
    ptr + 8 * UInt32.ofNat (k + 1) =
      (ptr + 8) + 8 * UInt32.ofNat k := by
  symm
  rw [UInt32.ofNat_add, show UInt32.ofNat 1 = 1 from rfl,
    UInt32.mul_add, UInt32.mul_one]
  rw [UInt32.add_assoc ptr 8, UInt32.add_comm 8, ← UInt32.add_assoc]

/-- Split ownership of a u64 array at a list concatenation boundary. -/
theorem array64At_append (ptr : UInt32) (xs ys : List UInt64) :
    array64At ptr (xs ++ ys) ⊣⊢
      array64At ptr xs ∗
        array64At (ptr + 8 * UInt32.ofNat xs.length) ys := by
  induction xs generalizing ptr with
  | nil => simp [array64At]; exact BI.emp_sep.symm
  | cons x rest ih =>
    simp only [List.cons_append, List.length_cons, array64At]
    rw [elem64_offset_succ]
    exact (BI.sep_congr_right (ih (ptr + 8))).trans BI.sep_assoc.symm

/-- Split a u64 array into a prefix, its next cell, and the suffix. -/
theorem array64At_append_cons (ptr : UInt32) (pre : List UInt64)
    (x : UInt64) (suffix : List UInt64) :
    array64At ptr (pre ++ x :: suffix) ⊣⊢
      array64At ptr pre ∗
        pointsTo_u64 (ptr + 8 * UInt32.ofNat pre.length) x ∗
        array64At ((ptr + 8 * UInt32.ofNat pre.length) + 8) suffix := by
  simpa only [array64At] using array64At_append ptr pre (x :: suffix)

/-- Focus the first unfilled u64 slot and return a continuation that extends
the filled prefix by one word.  This is the spatial update performed by one
iteration of a symbolic fill loop. -/
theorem array64At_fill_next (ptr : UInt32) (i : Nat)
    (value old : UInt64) (suffix : List UInt64) :
    array64At ptr (List.replicate i value ++ old :: suffix) ⊢
      pointsTo_u64 (ptr + 8 * UInt32.ofNat i) old ∗
      (pointsTo_u64 (ptr + 8 * UInt32.ofNat i) value -∗
        array64At ptr (List.replicate (i + 1) value ++ suffix)) := by
  iintro Harray
  icases (array64At_append_cons ptr (List.replicate i value) old suffix).mp $$
      Harray with ⟨Hpre, Hrest⟩
  icases Hrest with ⟨Hcell, Hsuffix⟩
  ihave Hcell' : pointsTo_u64 (ptr + 8 * UInt32.ofNat i) old $$ [Hcell]
  · rw [List.length_replicate]
    iexact Hcell
  ihave Hsuffix' :
      array64At ((ptr + 8 * UInt32.ofNat i) + 8) suffix $$ [Hsuffix]
  · rw [List.length_replicate]
    iexact Hsuffix
  isplitl [Hcell']
  · iexact Hcell'
  iintro Hcell
  have hrep :
      List.replicate (i + 1) value =
        List.replicate i value ++ [value] := by
    induction i with
    | zero => rfl
    | succ i ih =>
        change value :: List.replicate (i + 1) value =
          value :: (List.replicate i value ++ [value])
        exact congrArg (List.cons value) ih
  rw [hrep]
  rw [List.append_assoc, List.singleton_append]
  iapply (array64At_append_cons ptr (List.replicate i value)
    value suffix).mpr
  isplitl [Hpre]
  · iexact Hpre
  isplitl [Hcell]
  · rw [List.length_replicate]
    iexact Hcell
  · rw [List.length_replicate]
    iexact Hsuffix'

/-- Extract a u64 cell and a continuation accepting its replacement. -/
theorem array64At_set (ptr : UInt32) (xs : List UInt64) (k : Nat)
    (v : UInt64) (hk : k < xs.length) :
    array64At ptr xs ⊢
      pointsTo_u64 (ptr + 8 * UInt32.ofNat k) xs[k] ∗
      (pointsTo_u64 (ptr + 8 * UInt32.ofNat k) v -∗
        array64At ptr (xs.set k v)) := by
  induction xs generalizing ptr k with
  | nil => simp at hk
  | cons x rest ih =>
    cases k with
    | zero =>
      simp only [List.getElem_cons_zero, List.set_cons_zero, array64At]
      rw [show ptr + 8 * UInt32.ofNat 0 = ptr from by simp [UInt32.ofNat]]
      exact BI.sep_mono .rfl (BI.wand_intro BI.sep_symm)
    | succ k' =>
      simp only [List.length_cons] at hk
      have hk' : k' < rest.length := by omega
      simp only [List.getElem_cons_succ, List.set_cons_succ, array64At]
      rw [elem64_offset_succ]
      exact (BI.sep_mono_right (ih (ptr + 8) k' hk')).trans
        (BI.sep_left_comm.mp.trans (BI.sep_mono_right
          (BI.wand_intro
            (BI.sep_assoc.mp.trans (BI.sep_mono_right BI.wand_elim_left)))))

/-- Extract a u64 cell and a continuation restoring the unchanged array. -/
theorem array64At_get (ptr : UInt32) (xs : List UInt64) (k : Nat)
    (hk : k < xs.length) :
    array64At ptr xs ⊢
      pointsTo_u64 (ptr + 8 * UInt32.ofNat k) xs[k] ∗
      (pointsTo_u64 (ptr + 8 * UInt32.ofNat k) xs[k] -∗
        array64At ptr xs) := by
  have h := array64At_set ptr xs k xs[k] hk
  rwa [List.set_getElem_self] at h
end PointsTo
end Wasm.SepLogic
