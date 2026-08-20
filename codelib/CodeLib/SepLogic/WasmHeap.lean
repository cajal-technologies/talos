import Iris.ProofMode
import Iris.Instances.Lib.FUpd
import Iris.BI.Lib.GenHeap
import Iris.Algebra.Lib.ExclAuth
import Interpreter.Wasm.Mem
import Interpreter.Wasm.Syntax
import Interpreter.Wasm.Host
import Interpreter.Wasm.SmallStep
import Std.Tactic.BVDecide
/-! # Wasm Memory as an Iris GenHeap
Instantiates iris-lean's GenHeap for Wasm byte-level memory.
Location = MemoryKey (memory id × byte address), Value = Option UInt8 (byte).
-/
namespace Wasm.SepLogic
open Iris Std
open Wasm.SmallStep (ModuleInstance)

-- Named key types for multi-module ghost maps.
-- ExtTreeMap requires Ord + OrientedCmp + TransCmp + LawfulEqCmp.
-- `deriving Ord` provides Ord; the three Cmp classes are proved below.
structure MemoryKey where
  memId : Nat
  addr  : UInt32
  deriving DecidableEq, Ord, BEq, Repr

structure GlobalKey where
  instanceId : Nat
  index      : Nat
  deriving DecidableEq, Ord, BEq, Repr

structure DataSegmentKey where
  instanceId : Nat
  index      : Nat
  deriving DecidableEq, Ord, BEq, Repr

structure TableKey where
  instanceId : Nat
  index      : Nat
  deriving DecidableEq, Ord, BEq, Repr

structure ElementSegmentKey where
  instanceId : Nat
  index      : Nat
  deriving DecidableEq, Ord, BEq, Repr

-- The derived Ord for a 2-field struct {f1 : α, f2 : β} gives
--   compare a b = (compare a.f1 b.f1).then ((compare a.f2 b.f2).then .eq)
-- and since x.then .eq = x, this equals (compare a.f1 b.f1).then (compare a.f2 b.f2).
private theorem ord_then_eq_self (x : Ordering) : x.then .eq = x := by
  rcases x with _ | _ | _ <;> rfl

-- Reduction: compare on each key = .then of its two field comparisons.
private theorem memKey_compare_eq (a b : MemoryKey) :
    compare a b = (compare a.memId b.memId).then (compare a.addr b.addr) := by
  simp only [compare, Ord.compare, instOrdMemoryKey.ord, ord_then_eq_self]

private theorem globalKey_compare_eq (a b : GlobalKey) :
    compare a b = (compare a.instanceId b.instanceId).then (compare a.index b.index) := by
  simp only [compare, Ord.compare, instOrdGlobalKey.ord, ord_then_eq_self]

private theorem dataSegKey_compare_eq (a b : DataSegmentKey) :
    compare a b = (compare a.instanceId b.instanceId).then (compare a.index b.index) := by
  simp only [compare, Ord.compare, instOrdDataSegmentKey.ord, ord_then_eq_self]

private theorem tableKey_compare_eq (a b : TableKey) :
    compare a b = (compare a.instanceId b.instanceId).then (compare a.index b.index) := by
  simp only [compare, Ord.compare, instOrdTableKey.ord, ord_then_eq_self]

private theorem elemSegKey_compare_eq (a b : ElementSegmentKey) :
    compare a b = (compare a.instanceId b.instanceId).then (compare a.index b.index) := by
  simp only [compare, Ord.compare, instOrdElementSegmentKey.ord, ord_then_eq_self]

-- Concrete Ordering reductions (true by iota reduction, so rfl works).
private theorem ord_gt_then (x : Ordering) : Ordering.gt.then x = .gt := rfl
private theorem ord_eq_then (x : Ordering) : Ordering.eq.then x = x := rfl
private theorem ord_lt_then (x : Ordering) : Ordering.lt.then x = .lt := rfl
private theorem ord_isLE_gt : Ordering.gt.isLE = false := rfl
private theorem ord_isLE_lt : Ordering.lt.isLE = true := rfl

-- Generic: the .then form of two OrientedCmp comparisons is oriented.
private theorem then_orient {α β : Type} [Ord α] [Ord β]
    [OrientedCmp (compare (α := α))] [OrientedCmp (compare (α := β))]
    (a1 b1 : α) (a2 b2 : β) :
    (compare a1 b1).then (compare a2 b2) =
      ((compare b1 a1).then (compare b2 a2)).swap := by
  rw [OrientedCmp.eq_swap (cmp := compare (α := α)) (a := a1) (b := b1)]
  rw [OrientedCmp.eq_swap (cmp := compare (α := β)) (a := a2) (b := b2)]
  rcases compare b1 a1 with _ | _ | _ <;>
  rcases compare b2 a2 with _ | _ | _ <;>
  rfl

-- Generic: the .then form of two transitive comparisons is transitive.
-- Proves isLE_trans for all 9 cases of (compare a1 b1, compare b1 c1).
private theorem then_isLE_trans {α β : Type} [Ord α] [Ord β]
    [OrientedCmp (compare (α := α))]
    [TransCmp (compare (α := α))] [LawfulEqCmp (compare (α := α))]
    [TransCmp (compare (α := β))]
    (a1 b1 c1 : α) (a2 b2 c2 : β)
    (hab : ((compare a1 b1).then (compare a2 b2)).isLE = true)
    (hbc : ((compare b1 c1).then (compare b2 c2)).isLE = true) :
    ((compare a1 c1).then (compare a2 c2)).isLE = true := by
  rcases h₁ : compare a1 b1 with _ | _ | _ <;> rcases h₂ : compare b1 c1 with _ | _ | _
  -- lt.lt
  · have hac := TransCmp.isLE_trans (cmp := compare (α := α)) (b := b1)
      (show (compare a1 b1).isLE = true from by rw [h₁]; exact ord_isLE_lt)
      (show (compare b1 c1).isLE = true from by rw [h₂]; exact ord_isLE_lt)
    rcases h₃ : compare a1 c1 with _ | _ | _
    · simp
    · exfalso
      have hac_eq := LawfulEqCmp.eq_of_compare (cmp := compare (α := α)) h₃
      rw [← hac_eq] at h₂
      have h1s := OrientedCmp.eq_swap (cmp := compare (α := α)) (a := a1) (b := b1)
      rw [h₁, h₂] at h1s
      exact absurd h1s (by decide)
    · rw [h₃, ord_isLE_gt] at hac
      exact absurd hac (by decide)
  -- lt.eq: b1 = c1, so compare a1 c1 = .lt
  · have heq := LawfulEqCmp.eq_of_compare (cmp := compare (α := α)) h₂
    simp [← heq, h₁]
  -- lt.gt: hbc is false
  · simp only [h₂, ord_gt_then, ord_isLE_gt] at hbc
    exact absurd hbc (by decide)
  -- eq.lt: a1 = b1, so compare a1 c1 = .lt
  · have heq := LawfulEqCmp.eq_of_compare (cmp := compare (α := α)) h₁
    rw [← heq] at h₂
    simp [h₂]
  -- eq.eq: a1 = b1 = c1, recurse on second component
  · simp only [h₁, h₂, ord_eq_then] at hab hbc
    have hac : compare a1 c1 = .eq := by
      rw [(LawfulEqCmp.eq_of_compare (cmp := compare (α := α)) h₁).trans
          (LawfulEqCmp.eq_of_compare (cmp := compare (α := α)) h₂)]
      exact ReflCmp.compare_self
    rw [hac, ord_eq_then]
    exact TransCmp.isLE_trans hab hbc
  -- eq.gt: hbc is false
  · simp only [h₂, ord_gt_then, ord_isLE_gt] at hbc
    exact absurd hbc (by decide)
  -- gt.*: hab is false in all three
  · simp only [h₁, ord_gt_then, ord_isLE_gt] at hab; exact absurd hab (by decide)
  · simp only [h₁, ord_gt_then, ord_isLE_gt] at hab; exact absurd hab (by decide)
  · simp only [h₁, ord_gt_then, ord_isLE_gt] at hab; exact absurd hab (by decide)

-- MemoryKey: OrientedCmp, TransCmp, LawfulEqCmp
instance instOrientedCmpMemoryKey : OrientedCmp (compare (α := MemoryKey)) where
  eq_swap {a b} := by
    rw [memKey_compare_eq a b, memKey_compare_eq b a]
    exact then_orient a.memId b.memId a.addr b.addr

instance instTransCmpMemoryKey : TransCmp (compare (α := MemoryKey)) where
  isLE_trans {a b c} hab hbc := by
    rw [memKey_compare_eq] at hab hbc ⊢
    exact then_isLE_trans a.memId b.memId c.memId a.addr b.addr c.addr hab hbc

instance instLawfulEqCmpMemoryKey : LawfulEqCmp (compare (α := MemoryKey)) where
  compare_self {a} := by
    rw [memKey_compare_eq]; simp [ReflCmp.compare_self]
  eq_of_compare {a b} h := by
    rw [memKey_compare_eq] at h
    rcases h₁ : compare a.memId b.memId with _ | _ | _ <;>
    simp only [h₁, ord_lt_then, ord_eq_then, ord_gt_then] at h
    · exact absurd h (by decide)
    · have hmem := LawfulEqCmp.eq_of_compare (cmp := compare (α := Nat)) h₁
      have haddr := LawfulEqCmp.eq_of_compare (cmp := compare (α := UInt32)) h
      cases a; cases b; simp_all
    · exact absurd h (by decide)

-- GlobalKey: OrientedCmp, TransCmp, LawfulEqCmp
instance instOrientedCmpGlobalKey : OrientedCmp (compare (α := GlobalKey)) where
  eq_swap {a b} := by
    rw [globalKey_compare_eq a b, globalKey_compare_eq b a]
    exact then_orient a.instanceId b.instanceId a.index b.index

instance instTransCmpGlobalKey : TransCmp (compare (α := GlobalKey)) where
  isLE_trans {a b c} hab hbc := by
    rw [globalKey_compare_eq] at hab hbc ⊢
    exact then_isLE_trans a.instanceId b.instanceId c.instanceId a.index b.index c.index hab hbc

instance instLawfulEqCmpGlobalKey : LawfulEqCmp (compare (α := GlobalKey)) where
  compare_self {a} := by
    rw [globalKey_compare_eq]; simp [ReflCmp.compare_self]
  eq_of_compare {a b} h := by
    rw [globalKey_compare_eq] at h
    rcases h₁ : compare a.instanceId b.instanceId with _ | _ | _ <;>
    simp only [h₁, ord_lt_then, ord_eq_then, ord_gt_then] at h
    · exact absurd h (by decide)
    · have hi := LawfulEqCmp.eq_of_compare (cmp := compare (α := Nat)) h₁
      have hj := LawfulEqCmp.eq_of_compare (cmp := compare (α := Nat)) h
      cases a; cases b; simp_all
    · exact absurd h (by decide)

-- DataSegmentKey: OrientedCmp, TransCmp, LawfulEqCmp
instance instOrientedCmpDataSegmentKey : OrientedCmp (compare (α := DataSegmentKey)) where
  eq_swap {a b} := by
    rw [dataSegKey_compare_eq a b, dataSegKey_compare_eq b a]
    exact then_orient a.instanceId b.instanceId a.index b.index

instance instTransCmpDataSegmentKey : TransCmp (compare (α := DataSegmentKey)) where
  isLE_trans {a b c} hab hbc := by
    rw [dataSegKey_compare_eq] at hab hbc ⊢
    exact then_isLE_trans a.instanceId b.instanceId c.instanceId a.index b.index c.index hab hbc

instance instLawfulEqCmpDataSegmentKey : LawfulEqCmp (compare (α := DataSegmentKey)) where
  compare_self {a} := by
    rw [dataSegKey_compare_eq]; simp [ReflCmp.compare_self]
  eq_of_compare {a b} h := by
    rw [dataSegKey_compare_eq] at h
    rcases h₁ : compare a.instanceId b.instanceId with _ | _ | _ <;>
    simp only [h₁, ord_lt_then, ord_eq_then, ord_gt_then] at h
    · exact absurd h (by decide)
    · have hi := LawfulEqCmp.eq_of_compare (cmp := compare (α := Nat)) h₁
      have hj := LawfulEqCmp.eq_of_compare (cmp := compare (α := Nat)) h
      cases a; cases b; simp_all
    · exact absurd h (by decide)

-- TableKey: OrientedCmp, TransCmp, LawfulEqCmp
instance instOrientedCmpTableKey : OrientedCmp (compare (α := TableKey)) where
  eq_swap {a b} := by
    rw [tableKey_compare_eq a b, tableKey_compare_eq b a]
    exact then_orient a.instanceId b.instanceId a.index b.index

instance instTransCmpTableKey : TransCmp (compare (α := TableKey)) where
  isLE_trans {a b c} hab hbc := by
    rw [tableKey_compare_eq] at hab hbc ⊢
    exact then_isLE_trans a.instanceId b.instanceId c.instanceId a.index b.index c.index hab hbc

instance instLawfulEqCmpTableKey : LawfulEqCmp (compare (α := TableKey)) where
  compare_self {a} := by
    rw [tableKey_compare_eq]; simp [ReflCmp.compare_self]
  eq_of_compare {a b} h := by
    rw [tableKey_compare_eq] at h
    rcases h₁ : compare a.instanceId b.instanceId with _ | _ | _ <;>
    simp only [h₁, ord_lt_then, ord_eq_then, ord_gt_then] at h
    · exact absurd h (by decide)
    · have hi := LawfulEqCmp.eq_of_compare (cmp := compare (α := Nat)) h₁
      have hj := LawfulEqCmp.eq_of_compare (cmp := compare (α := Nat)) h
      cases a; cases b; simp_all
    · exact absurd h (by decide)

-- ElementSegmentKey: OrientedCmp, TransCmp, LawfulEqCmp
instance instOrientedCmpElementSegmentKey : OrientedCmp (compare (α := ElementSegmentKey)) where
  eq_swap {a b} := by
    rw [elemSegKey_compare_eq a b, elemSegKey_compare_eq b a]
    exact then_orient a.instanceId b.instanceId a.index b.index

instance instTransCmpElementSegmentKey : TransCmp (compare (α := ElementSegmentKey)) where
  isLE_trans {a b c} hab hbc := by
    rw [elemSegKey_compare_eq] at hab hbc ⊢
    exact then_isLE_trans a.instanceId b.instanceId c.instanceId a.index b.index c.index hab hbc

instance instLawfulEqCmpElementSegmentKey : LawfulEqCmp (compare (α := ElementSegmentKey)) where
  compare_self {a} := by
    rw [elemSegKey_compare_eq]; simp [ReflCmp.compare_self]
  eq_of_compare {a b} h := by
    rw [elemSegKey_compare_eq] at h
    rcases h₁ : compare a.instanceId b.instanceId with _ | _ | _ <;>
    simp only [h₁, ord_lt_then, ord_eq_then, ord_gt_then] at h
    · exact absurd h (by decide)
    · have hi := LawfulEqCmp.eq_of_compare (cmp := compare (α := Nat)) h₁
      have hj := LawfulEqCmp.eq_of_compare (cmp := compare (α := Nat)) h
      cases a; cases b; simp_all
    · exact absurd h (by decide)

abbrev WasmHeapMap := fun V => ExtTreeMap MemoryKey V compare
abbrev WasmGlobalMap := fun V => ExtTreeMap GlobalKey V compare
abbrev WasmDataSegmentMap := fun V => ExtTreeMap DataSegmentKey V compare
abbrev WasmTableMap := fun V => ExtTreeMap TableKey V compare
abbrev WasmElementSegmentMap := fun V => ExtTreeMap ElementSegmentKey V compare
abbrev WasmRuntimeModuleMap := fun V => ExtTreeMap Nat V compare
abbrev WasmHostEnvMap := fun V => ExtTreeMap Nat V compare
abbrev WasmExceptionMap := fun V => ExtTreeMap Nat V compare
abbrev WasmHeapGF (α : Type 0) : BundledGFunctors
  | 0 => ⟨InvMapF, by infer_instance⟩
  | 1 => ⟨constOF (DisjointLeibnizSet CoPset), by infer_instance⟩
  | 2 => ⟨constOF (DisjointLeibnizSet PosSet), by infer_instance⟩
  | 3 => ⟨Auth.AuthURF (constOF Credit), by infer_instance⟩
  | 4 => ⟨constOF (HeapView MemoryKey (Agree (DiscreteO (Option UInt8))) WasmHeapMap), by infer_instance⟩
  | 5 => ⟨constOF (HeapView MemoryKey (Agree (DiscreteO GName)) WasmHeapMap), by infer_instance⟩
  | 6 => ⟨constOF MetaUR, by infer_instance⟩
  | 7 => ⟨constOF (HeapView GlobalKey (Agree (DiscreteO Value)) WasmGlobalMap),
      by infer_instance⟩
  | 8 => ⟨constOF (HeapView Nat (Agree (DiscreteO Module)) WasmRuntimeModuleMap),
      by infer_instance⟩
  | 9 => ⟨constOF
      (HeapView DataSegmentKey (Agree (DiscreteO (Option (List UInt8))))
        WasmDataSegmentMap), by infer_instance⟩
  | 10 => ⟨constOF
      (HeapView TableKey (Agree (DiscreteO TableInst)) WasmTableMap),
      by infer_instance⟩
  | 11 => ⟨constOF
      (HeapView ElementSegmentKey (Agree (DiscreteO (Option (List (Option Nat)))))
        WasmElementSegmentMap), by infer_instance⟩
  | 12 => ⟨constOF (HeapView Nat (Agree (DiscreteO (HostEnv α))) WasmHostEnvMap), by infer_instance⟩
  | 13 => ⟨Auth.AuthRF (OptionOF (Excl.ExclOF (constOF (DiscreteO α)))), by infer_instance⟩
  | 14 => ⟨Auth.AuthRF (OptionOF (Excl.ExclOF (constOF (DiscreteO Nat)))), by infer_instance⟩
  | 15 => ⟨constOF (Agree (DiscreteO (Array (ModuleInstance α)))), by infer_instance⟩
  | 16 => ⟨constOF
      (HeapView Nat (Agree (DiscreteO (Nat × List Value)))
        WasmExceptionMap), by infer_instance⟩
  | 17 => ⟨constOF (Agree (DiscreteO (List Nat))), by infer_instance⟩
  | _ => ⟨constOF Unit, by infer_instance⟩
-- Wire genHeapPreS (following HeapLang's instHeapLangGS_HeapLangS)
instance instWasmHeapPreS (α : Type) :
    genHeapPreS MemoryKey (Option UInt8) (WasmHeapGF α) WasmHeapMap where
  heap := by constructor; exists 4
  metaInfo := by constructor; exists 5
  metaData := by exists 6
-- The full genHeap instance with ghost names
class WasmHeapGS (α : outParam Type) extends
    genHeapGS MemoryKey (Option UInt8) (WasmHeapGF α) WasmHeapMap

/-- Globals use a directly named ghost map instead of a second `genHeapGS`.
All identifying parameters of `genHeapGS` are output parameters, so two
simultaneous GenHeap instances are ambiguous to typeclass search. -/
class WasmGlobalGS (α : outParam Type) extends
    GhostMapG (WasmHeapGF α) GlobalKey Value WasmGlobalMap where
  globalName : GName

attribute [instance] WasmGlobalGS.toGhostMapG

/-- Passive data segments use their own named authoritative ghost map.  An
entry remains present after `data.drop`, but its value changes from
`some bytes` to `none`, mirroring the instantiated store exactly at every
owned segment index. -/
class WasmDataSegmentGS (α : outParam Type) extends
    GhostMapG (WasmHeapGF α) DataSegmentKey (Option (List UInt8)) WasmDataSegmentMap where
  dataSegmentName : GName

attribute [instance] WasmDataSegmentGS.toGhostMapG

/-- Instantiated tables use stable table indices as authoritative ghost-map
keys.  A fragment owns one complete table; element-level rules preserve or
update that fragment together with the physical table. -/
class WasmTableGS (α : outParam Type) extends
    GhostMapG (WasmHeapGF α) TableKey TableInst WasmTableMap where
  tableName : GName

attribute [instance] WasmTableGS.toGhostMapG

/-- Instantiated element segments retain stable indices after `elem.drop`.
Their optional payload is authoritative so `table.init` reads the physical
live segment and `elem.drop` changes both views to `none`. -/
class WasmElementSegmentGS (α : outParam Type) extends
    GhostMapG (WasmHeapGF α) ElementSegmentKey (Option (List (Option Nat)))
      WasmElementSegmentMap where
  elementSegmentName : GName

attribute [instance] WasmElementSegmentGS.toGhostMapG

class WasmRuntimeModuleGS (α : outParam Type) extends
    GhostMapG (WasmHeapGF α) Nat Module WasmRuntimeModuleMap where
  runtimeName : GName

attribute [instance] WasmRuntimeModuleGS.toGhostMapG

class WasmRuntimeInstancesGS (α : outParam Type) where
  runtimeInstancesElem :
    ElemG (WasmHeapGF α) (constOF (Agree (DiscreteO (Array (ModuleInstance α)))))
  runtimeInstancesName : GName

attribute [reducible, instance] WasmRuntimeInstancesGS.runtimeInstancesElem

/-- Thrown-exception payloads, keyed by their index in `MachineStore.wasm.exns`. -/
class WasmExceptionGS (α : outParam Type) extends
    GhostMapG (WasmHeapGF α) Nat (Nat × List Value) WasmExceptionMap where
  exceptionName : GName

attribute [instance] WasmExceptionGS.toGhostMapG

/-- Ghost knowledge about the tag-identity table of the *entry* instance.

Tag identity is needed only by the exception rules, so it is kept in its own
persistent ghost variable instead of being asserted as an invariant of the
state interpretation.  The state interpretation only requires the agreed list
to be a *prefix* of `MachineStore.wasm.tagIds`, which keeps it valid for the
linked, multi-instance stores introduced by module linking: registering
further modules can only extend the tag table, never rewrite the prefix the
entry instance already owns. -/
class WasmTagTableGS (α : outParam Type) where
  tagTableElem :
    ElemG (WasmHeapGF α) (constOF (Agree (DiscreteO (List Nat))))
  tagTableName : GName

attribute [reducible, instance] WasmTagTableGS.tagTableElem

class WasmHostEnvGS (α : outParam Type) extends
    GhostMapG (WasmHeapGF α) Nat (HostEnv α) WasmHostEnvMap where
  hostEnvName : GName

attribute [instance] WasmHostEnvGS.toGhostMapG

class WasmHostStateGS (α : outParam Type) where
  hostStateElem :
    ElemG (WasmHeapGF α) (Auth.AuthRF (OptionOF (Excl.ExclOF (constOF (DiscreteO α)))))
  hostStateName : GName

attribute [reducible, instance] WasmHostStateGS.hostStateElem

/-- Authoritative ghost cell for the current module instance id (`runtime.entry`).
Uses ExclAuth so it can be updated on cross-instance call/return. -/
class WasmInstanceGS (α : outParam Type) where
  instanceElem :
    ElemG (WasmHeapGF α) (Auth.AuthRF (OptionOF (Excl.ExclOF (constOF (DiscreteO Nat)))))
  instanceName : GName

attribute [reducible, instance] WasmInstanceGS.instanceElem

def globalPointsTo {α : Type} [gs : WasmGlobalGS α] (key : GlobalKey) (value : Value) :
    IProp (WasmHeapGF α) :=
  ghost_map_elem gs.globalName (DFrac.own 1) key value

def globalPointsToAt {α : Type} [gs : WasmGlobalGS α] (instanceId : Nat) (index : Nat)
    (value : Value) : IProp (WasmHeapGF α) :=
  globalPointsTo ⟨instanceId, index⟩ value

theorem globalPointsToAt_eq {α : Type} [WasmGlobalGS α] (i j : Nat) (v : Value) :
    globalPointsToAt i j v = globalPointsTo ⟨i, j⟩ v := rfl

instance {α : Type} [WasmGlobalGS α] (key : GlobalKey) (value : Value) :
    BI.Timeless (globalPointsTo key value) := by
  unfold globalPointsTo
  infer_instance

theorem globalPointsTo_lookup {α : Type} [gs : WasmGlobalGS α]
    (σ : WasmGlobalMap Value) (key : GlobalKey) (value : Value) :
    ghost_map_auth gs.globalName (DFrac.own 1) σ -∗
      globalPointsTo key value -∗
      iprop(⌜get? σ key = some value⌝) := by
  unfold globalPointsTo
  iapply ghost_map_lookup

/-- Authoritative update for one owned global entry. -/
theorem globalPointsTo_update {α : Type} [gs : WasmGlobalGS α]
    (σ : WasmGlobalMap Value) (key : GlobalKey)
    (oldValue newValue : Value) :
    ghost_map_auth gs.globalName (DFrac.own 1) σ -∗
      globalPointsTo key oldValue ==∗
      ghost_map_auth gs.globalName (DFrac.own 1)
        (insert σ key newValue) ∗
      globalPointsTo key newValue := by
  unfold globalPointsTo
  iapply ghost_map_update

def dataSegmentPointsTo {α : Type} [gs : WasmDataSegmentGS α]
    (key : DataSegmentKey) (value : Option (List UInt8)) : IProp (WasmHeapGF α) :=
  ghost_map_elem gs.dataSegmentName (DFrac.own 1) key value

def dataSegmentPointsToAt {α : Type} [gs : WasmDataSegmentGS α]
    (instanceId : Nat) (index : Nat) (value : Option (List UInt8)) :
    IProp (WasmHeapGF α) :=
  dataSegmentPointsTo ⟨instanceId, index⟩ value

theorem dataSegmentPointsToAt_eq {α : Type} [WasmDataSegmentGS α] (i j : Nat) (v : Option (List UInt8)) :
    dataSegmentPointsToAt i j v = dataSegmentPointsTo ⟨i, j⟩ v := rfl

instance {α : Type} [WasmDataSegmentGS α] (key : DataSegmentKey)
    (value : Option (List UInt8)) :
    BI.Timeless (dataSegmentPointsTo key value) := by
  unfold dataSegmentPointsTo
  infer_instance

instance {α : Type} [WasmDataSegmentGS α] (instanceId index : Nat)
    (value : Option (List UInt8)) :
    BI.Timeless (dataSegmentPointsToAt (α := α) instanceId index value) := by
  unfold dataSegmentPointsToAt
  infer_instance

theorem dataSegmentPointsTo_lookup {α : Type} [gs : WasmDataSegmentGS α]
    (σ : WasmDataSegmentMap (Option (List UInt8)))
    (key : DataSegmentKey) (value : Option (List UInt8)) :
    ghost_map_auth gs.dataSegmentName (DFrac.own 1) σ -∗
      dataSegmentPointsTo key value -∗
      iprop(⌜get? σ key = some value⌝) := by
  unfold dataSegmentPointsTo
  iapply ghost_map_lookup

theorem dataSegmentPointsTo_update {α : Type} [gs : WasmDataSegmentGS α]
    (σ : WasmDataSegmentMap (Option (List UInt8)))
    (key : DataSegmentKey) (oldValue newValue : Option (List UInt8)) :
    ghost_map_auth gs.dataSegmentName (DFrac.own 1) σ -∗
      dataSegmentPointsTo key oldValue ==∗
      ghost_map_auth gs.dataSegmentName (DFrac.own 1)
        (insert σ key newValue) ∗
      dataSegmentPointsTo key newValue := by
  unfold dataSegmentPointsTo
  iapply ghost_map_update

def tablePointsTo {α : Type} [gs : WasmTableGS α]
    (key : TableKey) (table : TableInst) : IProp (WasmHeapGF α) :=
  ghost_map_elem gs.tableName (DFrac.own 1) key table

def tablePointsToAt {α : Type} [gs : WasmTableGS α]
    (instanceId : Nat) (index : Nat) (table : TableInst) :
    IProp (WasmHeapGF α) :=
  tablePointsTo ⟨instanceId, index⟩ table

theorem tablePointsToAt_eq {α : Type} [WasmTableGS α] (i j : Nat) (t : TableInst) :
    tablePointsToAt i j t = tablePointsTo ⟨i, j⟩ t := rfl

instance {α : Type} [WasmTableGS α] (key : TableKey) (table : TableInst) :
    BI.Timeless (tablePointsTo key table) := by
  unfold tablePointsTo
  infer_instance

theorem tablePointsTo_lookup {α : Type} [gs : WasmTableGS α]
    (σ : WasmTableMap TableInst) (key : TableKey) (table : TableInst) :
    ghost_map_auth gs.tableName (DFrac.own 1) σ -∗
      tablePointsTo key table -∗
      iprop(⌜get? σ key = some table⌝) := by
  unfold tablePointsTo
  iapply ghost_map_lookup

theorem tablePointsTo_update {α : Type} [gs : WasmTableGS α]
    (σ : WasmTableMap TableInst) (key : TableKey)
    (oldTable newTable : TableInst) :
    ghost_map_auth gs.tableName (DFrac.own 1) σ -∗
      tablePointsTo key oldTable ==∗
      ghost_map_auth gs.tableName (DFrac.own 1)
        (insert σ key newTable) ∗
      tablePointsTo key newTable := by
  unfold tablePointsTo
  iapply ghost_map_update

def elementSegmentPointsTo {α : Type} [gs : WasmElementSegmentGS α]
    (key : ElementSegmentKey) (value : Option (List (Option Nat))) :
    IProp (WasmHeapGF α) :=
  ghost_map_elem gs.elementSegmentName (DFrac.own 1) key value

def elementSegmentPointsToAt {α : Type} [gs : WasmElementSegmentGS α]
    (instanceId : Nat) (index : Nat) (value : Option (List (Option Nat))) :
    IProp (WasmHeapGF α) :=
  elementSegmentPointsTo ⟨instanceId, index⟩ value

theorem elementSegmentPointsToAt_eq {α : Type} [WasmElementSegmentGS α] (i j : Nat)
    (v : Option (List (Option Nat))) :
    elementSegmentPointsToAt i j v = elementSegmentPointsTo ⟨i, j⟩ v := rfl

instance {α : Type} [WasmElementSegmentGS α] (key : ElementSegmentKey)
    (value : Option (List (Option Nat))) :
    BI.Timeless (elementSegmentPointsTo key value) := by
  unfold elementSegmentPointsTo
  infer_instance

theorem elementSegmentPointsTo_lookup {α : Type} [gs : WasmElementSegmentGS α]
    (σ : WasmElementSegmentMap (Option (List (Option Nat))))
    (key : ElementSegmentKey) (value : Option (List (Option Nat))) :
    ghost_map_auth gs.elementSegmentName (DFrac.own 1) σ -∗
      elementSegmentPointsTo key value -∗
      iprop(⌜get? σ key = some value⌝) := by
  unfold elementSegmentPointsTo
  iapply ghost_map_lookup

theorem elementSegmentPointsTo_update {α : Type} [gs : WasmElementSegmentGS α]
    (σ : WasmElementSegmentMap (Option (List (Option Nat))))
    (key : ElementSegmentKey) (oldValue newValue : Option (List (Option Nat))) :
    ghost_map_auth gs.elementSegmentName (DFrac.own 1) σ -∗
      elementSegmentPointsTo key oldValue ==∗
      ghost_map_auth gs.elementSegmentName (DFrac.own 1)
        (insert σ key newValue) ∗
      elementSegmentPointsTo key newValue := by
  unfold elementSegmentPointsTo
  iapply ghost_map_update

-- raw ghost_map_elem for a module instance; used internally in stateInterp bigOpL
def exceptionPointsTo [gs : WasmExceptionGS α]
    (index : Nat) (dq : DFrac) (tagAndArgs : Nat × List Value) :
    IProp (WasmHeapGF α) :=
  ghost_map_elem gs.exceptionName dq index tagAndArgs

instance [WasmExceptionGS α] (index : Nat) (dq : DFrac)
    (tagAndArgs : Nat × List Value) :
    BI.Timeless (exceptionPointsTo (α := α) index dq tagAndArgs) := by
  unfold exceptionPointsTo
  infer_instance

theorem exceptionPointsTo_lookup [gs : WasmExceptionGS α]
    (σ : WasmExceptionMap (Nat × List Value))
    (index : Nat) (dq : DFrac) (tagAndArgs : Nat × List Value) :
    ghost_map_auth gs.exceptionName (DFrac.own 1) σ -∗
      exceptionPointsTo index dq tagAndArgs -∗
      iprop(⌜get? σ index = some tagAndArgs⌝) := by
  unfold exceptionPointsTo
  iapply ghost_map_lookup

theorem exceptionPointsTo_update [gs : WasmExceptionGS α]
    (σ : WasmExceptionMap (Nat × List Value))
    (index : Nat) (oldVal newVal : Nat × List Value) :
    ghost_map_auth gs.exceptionName (DFrac.own 1) σ -∗
      exceptionPointsTo index (DFrac.own 1) oldVal ==∗
      ghost_map_auth gs.exceptionName (DFrac.own 1)
        (insert σ index newVal) ∗
      exceptionPointsTo index (DFrac.own 1) newVal := by
  unfold exceptionPointsTo
  iapply ghost_map_update

/-- Persistent knowledge of the entry instance's tag-identity table.  Only the
exception rules need it; every other rule is oblivious to tags. -/
def tagTableOwn [gs : WasmTagTableGS α] (ids : List Nat) :
    IProp (WasmHeapGF α) :=
  iOwn (E := gs.tagTableElem) gs.tagTableName (toAgree ⟨ids⟩)

instance [WasmTagTableGS α] (ids : List Nat) :
    BI.Persistent (tagTableOwn (α := α) ids) := by
  unfold tagTableOwn
  infer_instance

instance [WasmTagTableGS α] (ids : List Nat) :
    BI.Timeless (tagTableOwn (α := α) ids) := by
  unfold tagTableOwn
  infer_instance

theorem tagTableOwn_agree [gs : WasmTagTableGS α]
    (actual expected : List Nat) :
    tagTableOwn (α := α) actual ∗ tagTableOwn expected ⊢
      iprop(⌜actual = expected⌝) := by
  unfold tagTableOwn
  iintro ⟨Hactual, Hexpected⟩
  icombine Hactual Hexpected gives %Hvalid
  ipureintro
  exact congrArg DiscreteO.car (toAgree_op_valid_iff_eq.mp Hvalid)

def runtimeModuleElem {α : Type} [gs : WasmRuntimeModuleGS α]
    (id : Nat) (m : Module) : IProp (WasmHeapGF α) :=
  ghost_map_elem gs.runtimeName DFrac.discard id m

instance {α : Type} [WasmRuntimeModuleGS α] (id : Nat) (m : Module) :
    BI.Persistent (runtimeModuleElem id m) := by
  unfold runtimeModuleElem; infer_instance

instance {α : Type} [WasmRuntimeModuleGS α] (id : Nat) (m : Module) :
    BI.Timeless (runtimeModuleElem id m) := by
  unfold runtimeModuleElem; infer_instance

theorem runtimeModuleElem_lookup {α : Type} [gs : WasmRuntimeModuleGS α]
    (σ : WasmRuntimeModuleMap Module) (id : Nat) (m : Module) :
    ghost_map_auth gs.runtimeName (DFrac.own 1) σ -∗
      runtimeModuleElem id m -∗
      iprop(⌜get? σ id = some m⌝) := by
  unfold runtimeModuleElem
  iapply ghost_map_lookup

/-- Persistent knowledge of the immutable instances array. Agreement with the
copy held by `StateInterp` lets cross-instance call rules verify instance
lookups against the actual machine. -/
def runtimeInstancesOwn {α : Type} [gs : WasmRuntimeInstancesGS α]
    (instances : Array (ModuleInstance α)) : IProp (WasmHeapGF α) :=
  iOwn (E := gs.runtimeInstancesElem) gs.runtimeInstancesName (toAgree ⟨instances⟩)

instance {α : Type} [WasmRuntimeInstancesGS α] (instances : Array (ModuleInstance α)) :
    BI.Persistent (runtimeInstancesOwn instances) := by
  unfold runtimeInstancesOwn
  infer_instance

instance {α : Type} [WasmRuntimeInstancesGS α] (instances : Array (ModuleInstance α)) :
    BI.Timeless (runtimeInstancesOwn instances) := by
  unfold runtimeInstancesOwn
  infer_instance

theorem runtimeInstancesOwn_agree {α : Type} [gs : WasmRuntimeInstancesGS α]
    (actual expected : Array (ModuleInstance α)) :
    runtimeInstancesOwn actual ∗ runtimeInstancesOwn expected ⊢
      iprop(⌜actual = expected⌝) := by
  unfold runtimeInstancesOwn
  iintro ⟨Hactual, Hexpected⟩
  icombine Hactual Hexpected gives %Hvalid
  ipureintro
  exact congrArg DiscreteO.car (toAgree_op_valid_iff_eq.mp Hvalid)

/-- Persistent knowledge of the host environment for a given instance. -/
def hostEnvOwn {α : Type} [gs : WasmHostEnvGS α] (instanceId : Nat) (env : HostEnv α) :
    IProp (WasmHeapGF α) :=
  ghost_map_elem gs.hostEnvName DFrac.discard instanceId env

instance {α : Type} [WasmHostEnvGS α] (instanceId : Nat) (env : HostEnv α) :
    BI.Persistent (hostEnvOwn instanceId env) := by
  unfold hostEnvOwn; infer_instance

instance {α : Type} [WasmHostEnvGS α] (instanceId : Nat) (env : HostEnv α) :
    BI.Timeless (hostEnvOwn instanceId env) := by
  unfold hostEnvOwn; infer_instance

theorem hostEnvOwn_lookup {α : Type} [gs : WasmHostEnvGS α]
    (σ : WasmHostEnvMap (HostEnv α)) (instanceId : Nat) (env : HostEnv α) :
    ghost_map_auth gs.hostEnvName (DFrac.own 1) σ -∗
      hostEnvOwn instanceId env -∗
      iprop(⌜get? σ instanceId = some env⌝) := by
  unfold hostEnvOwn
  iapply ghost_map_lookup

/-- Authoritative ownership of the mutable host state. Held by `StateInterp`. -/
def hostStateAuth {α : Type} [gs : WasmHostStateGS α] (st : α) :
    IProp (WasmHeapGF α) :=
  iOwn (E := gs.hostStateElem) gs.hostStateName
    (ExclAuth.auth (⟨st⟩ : DiscreteO α))

/-- Fragment ownership of the mutable host state. Given to WP proofs. -/
def hostStateOwn {α : Type} [gs : WasmHostStateGS α] (st : α) :
    IProp (WasmHeapGF α) :=
  iOwn (E := gs.hostStateElem) gs.hostStateName
    (ExclAuth.frag (⟨st⟩ : DiscreteO α))

theorem hostStateOwn_agree {α : Type} [gs : WasmHostStateGS α]
    (actual expected : α) :
    hostStateAuth actual ∗ hostStateOwn expected ⊢
      iprop(⌜actual = expected⌝) := by
  unfold hostStateAuth hostStateOwn
  iintro ⟨Hauth, Hfrag⟩
  icombine Hauth Hfrag gives %Hvalid
  ipureintro
  exact congrArg DiscreteO.car (ExclAuth.agree (A := DiscreteO α) Hvalid)

theorem hostStateOwn_update {α : Type} [gs : WasmHostStateGS α]
    (old new' : α) :
    hostStateAuth old ∗ hostStateOwn old ==∗
      hostStateAuth new' ∗ hostStateOwn new' := by
  unfold hostStateAuth hostStateOwn
  iintro ⟨Hauth, Hfrag⟩
  imod iOwn_update_op (E := gs.hostStateElem)
      (ExclAuth.update (A := DiscreteO α) (a := (⟨old⟩ : DiscreteO α))
        (b := ⟨old⟩) (a' := ⟨new'⟩))
      $$ [Hauth Hfrag] with Hboth
  · iframe
  imodintro
  icases iOwn_op $$ Hboth with ⟨H1, H2⟩
  iframe

def currentInstanceAuthN {α : Type} [gs : WasmInstanceGS α] (n : Nat) :
    IProp (WasmHeapGF α) :=
  iOwn (E := gs.instanceElem) gs.instanceName
    (ExclAuth.auth (⟨n⟩ : DiscreteO Nat))

def currentInstanceOwnN {α : Type} [gs : WasmInstanceGS α] (n : Nat) :
    IProp (WasmHeapGF α) :=
  iOwn (E := gs.instanceElem) gs.instanceName
    (ExclAuth.frag (⟨n⟩ : DiscreteO Nat))

instance {α : Type} [WasmInstanceGS α] (n : Nat) :
    BI.Timeless (currentInstanceAuthN (α := α) n) := by
  unfold currentInstanceAuthN; infer_instance

instance {α : Type} [WasmInstanceGS α] (n : Nat) :
    BI.Timeless (currentInstanceOwnN (α := α) n) := by
  unfold currentInstanceOwnN; infer_instance

section
open Wasm.SmallStep

/-- Module instance ownership: persistent module knowledge paired with exclusive
current-instance token. The exclusive part lets call rules verify that the
caller's instance id agrees with the machine's current instance. -/
def runtimeModuleOwn {α : Type} [gs : WasmRuntimeModuleGS α] [WasmInstanceGS α]
    (instanceId : ModuleInstanceId) (m : Module) : IProp (WasmHeapGF α) :=
  iprop(runtimeModuleElem instanceId.id m ∗ currentInstanceOwnN instanceId.id)

instance {α : Type} [gs : WasmRuntimeModuleGS α] [WasmInstanceGS α]
    (instanceId : ModuleInstanceId) (m : Module) :
    BI.Timeless (runtimeModuleOwn (α := α) instanceId m) := by
  unfold runtimeModuleOwn; infer_instance

theorem runtimeModuleOwn_lookup {α : Type} [gs : WasmRuntimeModuleGS α] [WasmInstanceGS α]
    (σ : WasmRuntimeModuleMap Module) (instanceId : ModuleInstanceId) (m : Module) :
    ghost_map_auth gs.runtimeName (DFrac.own 1) σ -∗
      runtimeModuleOwn instanceId m -∗
      ⌜get? σ instanceId.id = some m⌝ := by
  simp only [runtimeModuleOwn]
  iintro Hauth ⟨Helem, _⟩
  iapply runtimeModuleElem_lookup $$ Hauth Helem

end

theorem currentInstanceOwnN_agree {α : Type} [gs : WasmInstanceGS α]
    (actual expected : Nat) :
    currentInstanceAuthN (α := α) actual ∗ currentInstanceOwnN expected ⊢
      iprop(⌜actual = expected⌝) := by
  unfold currentInstanceAuthN currentInstanceOwnN
  iintro ⟨Hauth, Hfrag⟩
  icombine Hauth Hfrag gives %Hvalid
  ipureintro
  exact congrArg DiscreteO.car (ExclAuth.agree (A := DiscreteO Nat) Hvalid)

theorem currentInstanceOwnN_update {α : Type} [gs : WasmInstanceGS α]
    (old new' : Nat) :
    currentInstanceAuthN (α := α) old ∗ currentInstanceOwnN old ==∗
      currentInstanceAuthN new' ∗ currentInstanceOwnN new' := by
  unfold currentInstanceAuthN currentInstanceOwnN
  iintro ⟨Hauth, Hfrag⟩
  imod iOwn_update_op (E := gs.instanceElem)
      (ExclAuth.update (A := DiscreteO Nat) (a := (⟨old⟩ : DiscreteO Nat))
        (b := ⟨old⟩) (a' := ⟨new'⟩))
      $$ [Hauth Hfrag] with Hboth
  · iframe
  imodintro
  icases iOwn_op $$ Hboth with ⟨H1, H2⟩
  iframe

theorem currentInstanceOwnN_update_of_any {α : Type} [gs : WasmInstanceGS α]
    (actual expected new' : Nat) :
    currentInstanceAuthN (α := α) actual ∗ currentInstanceOwnN expected ==∗
      currentInstanceAuthN new' ∗ currentInstanceOwnN new' ∗ ⌜actual = expected⌝ := by
  unfold currentInstanceAuthN currentInstanceOwnN
  iintro ⟨Hauth, Hfrag⟩
  ihave %heq : ⌜actual = expected⌝ $$ [Hauth Hfrag]
  · icombine Hauth Hfrag gives %Hvalid
    ipureintro
    exact congrArg DiscreteO.car (ExclAuth.agree (A := DiscreteO Nat) Hvalid)
  imod iOwn_update_op (E := gs.instanceElem)
      (ExclAuth.update (A := DiscreteO Nat)
        (a := (⟨actual⟩ : DiscreteO Nat))
        (b := ⟨expected⟩)
        (a' := ⟨new'⟩))
      $$ [Hauth Hfrag] with Hboth
  · iframe
  imodintro
  icases iOwn_op $$ Hboth with ⟨H1, H2⟩
  isplitl [H1]
  · iexact H1
  isplitl [H2]
  · iexact H2
  · ipureintro
    exact heq

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
variable {α : Type} [inst : WasmHeapGS α]
-- Notation for Wasm points-to (scoped: available inside this namespace
-- and via `open Wasm.SepLogic`, without leaking through the CodeLib umbrella)
scoped notation:50 addr:50 " ↦w " v:50 => pointsTo (L := MemoryKey) (V := Option UInt8)
    (H := WasmHeapMap) addr (DFrac.own 1) (some v)

def memPointsTo (memId : Nat) (addr : UInt32) (dfrac : DFrac)
    (value : Option UInt8) : IProp (WasmHeapGF α) :=
  pointsTo (L := MemoryKey) (V := Option UInt8)
    (H := WasmHeapMap) ⟨memId, addr⟩ dfrac value

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
def pointsTo_u64 (memId : Nat) (addr : UInt32) (v : UInt64) : IProp (WasmHeapGF α) :=
  iprop%
    (⟨memId, addr⟩ ↦w u64Byte v 0) ∗ (⟨memId, addr + 1⟩ ↦w u64Byte v 1) ∗
    (⟨memId, addr + 2⟩ ↦w u64Byte v 2) ∗ (⟨memId, addr + 3⟩ ↦w u64Byte v 3) ∗
    (⟨memId, addr + 4⟩ ↦w u64Byte v 4) ∗ (⟨memId, addr + 5⟩ ↦w u64Byte v 5) ∗
    (⟨memId, addr + 6⟩ ↦w u64Byte v 6) ∗ (⟨memId, addr + 7⟩ ↦w u64Byte v 7)

theorem pointsTo_u64_eq (memId : Nat) (addr : UInt32) (v : UInt64) :
    pointsTo_u64 memId addr v ⊣⊢
      (iprop%
        (⟨memId, addr⟩ ↦w u64Byte v 0) ∗ (⟨memId, addr + 1⟩ ↦w u64Byte v 1) ∗
        (⟨memId, addr + 2⟩ ↦w u64Byte v 2) ∗ (⟨memId, addr + 3⟩ ↦w u64Byte v 3) ∗
        (⟨memId, addr + 4⟩ ↦w u64Byte v 4) ∗ (⟨memId, addr + 5⟩ ↦w u64Byte v 5) ∗
        (⟨memId, addr + 6⟩ ↦w u64Byte v 6) ∗ (⟨memId, addr + 7⟩ ↦w u64Byte v 7)) :=
  .rfl

instance instTimelessPointsToU64 (memId : Nat) (addr : UInt32) (v : UInt64) :
    BI.Timeless (pointsTo_u64 memId addr v) := by
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
def pointsTo_u32 (memId : Nat) (addr : UInt32) (v : UInt32) : IProp (WasmHeapGF α) :=
  iprop%
    (⟨memId, addr⟩ ↦w u32Byte v 0) ∗ (⟨memId, addr + 1⟩ ↦w u32Byte v 1) ∗
    (⟨memId, addr + 2⟩ ↦w u32Byte v 2) ∗ (⟨memId, addr + 3⟩ ↦w u32Byte v 3)

theorem pointsTo_u32_eq (memId : Nat) (addr v : UInt32) :
    pointsTo_u32 memId addr v ⊣⊢
      (iprop% (⟨memId, addr⟩ ↦w u32Byte v 0) ∗
        (⟨memId, addr + 1⟩ ↦w u32Byte v 1) ∗
        (⟨memId, addr + 2⟩ ↦w u32Byte v 2) ∗
        (⟨memId, addr + 3⟩ ↦w u32Byte v 3)) :=
  .rfl

instance instTimelessPointsToU32 (memId : Nat) (addr v : UInt32) :
    BI.Timeless (pointsTo_u32 memId addr v) := by
  unfold pointsTo_u32
  infer_instance

-- Multi-byte: u16 as 2 consecutive owned bytes (little-endian)
def pointsTo_u16 (memId : Nat) (addr : UInt32) (v : UInt32) : IProp (WasmHeapGF α) :=
  iprop%
    (⟨memId, addr⟩ ↦w u32Byte v 0) ∗ (⟨memId, addr + 1⟩ ↦w u32Byte v 1)

theorem pointsTo_u16_eq (memId : Nat) (addr v : UInt32) :
    pointsTo_u16 memId addr v ⊣⊢
      (iprop% (⟨memId, addr⟩ ↦w u32Byte v 0) ∗
        (⟨memId, addr + 1⟩ ↦w u32Byte v 1)) :=
  .rfl

instance instTimelessPointsToU16 (memId : Nat) (addr v : UInt32) :
    BI.Timeless (pointsTo_u16 memId addr v) := by
  unfold pointsTo_u16
  infer_instance

/-- The `n`th little-endian byte of a 16-bit value (low 2 bytes of a UInt32). -/
def u16Byte (v : UInt32) (n : Nat) : UInt8 :=
  match n with
  | 0 => v.toUInt8
  | _ => (v >>> 8).toUInt8

omit inst in
theorem u16Byte_reassemble (v : UInt32) :
    (u16Byte v 0).toUInt32 ||| ((u16Byte v 1).toUInt32 <<< 8) = v &&& 0xFFFF := by
  unfold u16Byte
  bv_decide

-- Byte-range ownership: n consecutive bytes at `addr` in memory `memId`.
def pointsToBytes (memId : Nat) (addr : UInt32) (bytes : List UInt8) :
    IProp (WasmHeapGF α) :=
  match bytes with
  | [] => iprop% emp
  | b :: rest => iprop% (⟨memId, addr⟩ ↦w b) ∗ (pointsToBytes memId (addr + 1) rest)

instance instTimelessPointsToBytes (memId : Nat) (addr : UInt32)
    (bytes : List UInt8) :
    BI.Timeless (pointsToBytes (α := α) memId addr bytes) := by
  induction bytes generalizing addr with
  | nil =>
      simp only [pointsToBytes]
      infer_instance
  | cons b rest ih =>
      simp only [pointsToBytes]
      letI := ih (addr + 1)
      infer_instance

theorem pointsToBytes_nil (memId : Nat) (addr : UInt32) :
    pointsToBytes (α := α) memId addr [] ⊣⊢ emp := .rfl

theorem pointsToBytes_cons (memId : Nat) (addr : UInt32) (b : UInt8)
    (rest : List UInt8) :
    pointsToBytes (α := α) memId addr (b :: rest) ⊣⊢
      (⟨memId, addr⟩ ↦w b) ∗ pointsToBytes memId (addr + 1) rest := .rfl

omit inst in
theorem byte_offset_succ (addr : UInt32) (k : Nat) :
    addr + UInt32.ofNat (k + 1) = (addr + 1) + UInt32.ofNat k := by
  symm
  rw [UInt32.ofNat_add, show UInt32.ofNat 1 = 1 from rfl]
  rw [UInt32.add_assoc addr 1, UInt32.add_comm 1]

theorem pointsToBytes_append (memId : Nat) (addr : UInt32) (xs ys : List UInt8) :
    pointsToBytes (α := α) memId addr (xs ++ ys) ⊣⊢
    pointsToBytes memId addr xs ∗
      pointsToBytes memId (addr + UInt32.ofNat xs.length) ys := by
  induction xs generalizing addr with
  | nil => simp [pointsToBytes]; exact BI.emp_sep.symm
  | cons x rest ih =>
    simp only [List.cons_append, List.length_cons, pointsToBytes]
    rw [byte_offset_succ]
    exact (BI.sep_congr_right (ih (addr + 1))).trans BI.sep_assoc.symm

/-- Owning a 32-bit word is the same as owning its four little-endian bytes. -/
theorem pointsTo_u32_as_bytes (memId : Nat) (addr v : UInt32) :
    pointsTo_u32 (α := α) memId addr v ⊣⊢
      pointsToBytes memId addr
        [u32Byte v 0, u32Byte v 1, u32Byte v 2, u32Byte v 3] := by
  have e11 : (1 + 1 : UInt32) = 2 := by decide
  have e21 : (2 + 1 : UInt32) = 3 := by decide
  have e2 : addr + 1 + 1 = addr + 2 := by rw [UInt32.add_assoc, e11]
  have e3 : addr + 2 + 1 = addr + 3 := by rw [UInt32.add_assoc, e21]
  simp only [pointsTo_u32, pointsToBytes, e2, e3,
    (BI.sep_emp (PROP := IProp (WasmHeapGF α))).to_eq]
  exact .rfl

-- Array ownership: n consecutive u32 elements at ptr
-- arrayAt memId ptr [x₀, x₁, ..., xₙ₋₁] =
--   pointsTo_u32 memId ptr x₀ ∗ pointsTo_u32 memId (ptr+4) x₁ ∗ ...
def arrayAt (memId : Nat) (ptr : UInt32) (xs : List UInt32) : IProp (WasmHeapGF α) :=
  match xs with
  | [] => iprop% emp
  | x :: rest => iprop% (pointsTo_u32 memId ptr x) ∗ (arrayAt memId (ptr + 4) rest)

instance instTimelessArrayAt (memId : Nat) (ptr : UInt32) (xs : List UInt32) :
    BI.Timeless (arrayAt memId ptr xs) := by
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
theorem arrayAt_append (memId : Nat) (ptr : UInt32) (xs ys : List UInt32) :
    arrayAt memId ptr (xs ++ ys) ⊣⊢
    arrayAt memId ptr xs ∗ arrayAt memId (ptr + 4 * UInt32.ofNat xs.length) ys := by
  induction xs generalizing ptr with
  | nil => simp [arrayAt]; exact BI.emp_sep.symm
  | cons x rest ih =>
    simp only [List.cons_append, List.length_cons, arrayAt]
    rw [elem_offset_succ]
    exact (BI.sep_congr_right (ih (ptr + 4))).trans BI.sep_assoc.symm

/-- Split a u32 array into a prefix, its next cell, and the suffix. -/
theorem arrayAt_append_cons (memId : Nat) (ptr : UInt32) (pre : List UInt32)
    (x : UInt32) (suffix : List UInt32) :
    arrayAt memId ptr (pre ++ x :: suffix) ⊣⊢
      arrayAt memId ptr pre ∗
        pointsTo_u32 memId (ptr + 4 * UInt32.ofNat pre.length) x ∗
        arrayAt memId ((ptr + 4 * UInt32.ofNat pre.length) + 4) suffix := by
  simpa only [arrayAt] using arrayAt_append memId ptr pre (x :: suffix)

/-- Focus the next source and destination words of a copy loop.  Returning
both cells to the continuation preserves the source and extends the copied
destination prefix by one word.  Exclusive byte ownership enforces that the
two focused footprints are disjoint. -/
theorem arrayAt_copy_next (memId : Nat) (dst src : UInt32) (pre : List UInt32)
    (oldDst value : UInt32) (dstSuffix srcSuffix : List UInt32) :
    arrayAt memId dst (pre ++ oldDst :: dstSuffix) ∗
      arrayAt memId src (pre ++ value :: srcSuffix) ⊢
      pointsTo_u32 memId (src + 4 * UInt32.ofNat pre.length) value ∗
      pointsTo_u32 memId (dst + 4 * UInt32.ofNat pre.length) oldDst ∗
      (pointsTo_u32 memId (src + 4 * UInt32.ofNat pre.length) value ∗
        pointsTo_u32 memId (dst + 4 * UInt32.ofNat pre.length) value -∗
        arrayAt memId dst (pre ++ value :: dstSuffix) ∗
          arrayAt memId src (pre ++ value :: srcSuffix)) := by
  iintro ⟨Hdst, Hsrc⟩
  icases (arrayAt_append_cons memId dst pre oldDst dstSuffix).mp $$ Hdst with
    ⟨HdstPre, HdstRest⟩
  icases HdstRest with ⟨HdstCell, HdstSuffix⟩
  icases (arrayAt_append_cons memId src pre value srcSuffix).mp $$ Hsrc with
    ⟨HsrcPre, HsrcRest⟩
  icases HsrcRest with ⟨HsrcCell, HsrcSuffix⟩
  isplitl [HsrcCell]
  · iexact HsrcCell
  isplitl [HdstCell]
  · iexact HdstCell
  iintro ⟨HsrcCell, HdstCell⟩
  isplitl [HdstPre HdstCell HdstSuffix]
  · iapply (arrayAt_append_cons memId dst pre value dstSuffix).mpr
    iframe
  · iapply (arrayAt_append_cons memId src pre value srcSuffix).mpr
    iframe

-- update element k: give back a cell with a NEW value,
-- own the updated array (merge writes out[k] = v)
theorem arrayAt_set (memId : Nat) (ptr : UInt32) (xs : List UInt32) (k : Nat)
    (v : UInt32) (hk : k < xs.length) :
    arrayAt memId ptr xs ⊢
    pointsTo_u32 memId (ptr + 4 * UInt32.ofNat k) xs[k] ∗
    (pointsTo_u32 memId (ptr + 4 * UInt32.ofNat k) v -∗
      arrayAt memId ptr (xs.set k v)) := by
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
theorem arrayAt_get (memId : Nat) (ptr : UInt32) (xs : List UInt32) (k : Nat)
    (hk : k < xs.length) :
    arrayAt memId ptr xs ⊢
    pointsTo_u32 memId (ptr + 4 * UInt32.ofNat k) xs[k] ∗
    (pointsTo_u32 memId (ptr + 4 * UInt32.ofNat k) xs[k] -∗ arrayAt memId ptr xs) := by
  have h := arrayAt_set memId ptr xs k xs[k] hk
  rwa [List.set_getElem_self] at h

/-! ## Owned arrays of 64-bit words

`array64At` is the u64 counterpart of `arrayAt`.  In particular,
`array64At_append` is the separation-logic form of the prefix/suffix split
used by a fill-loop invariant, while `array64At_set` gives a loop body the
current destination cell and a continuation that reassembles the updated
region.
-/

/-- Ownership of consecutive little-endian u64 words beginning at `ptr`. -/
def array64At (memId : Nat) (ptr : UInt32) (xs : List UInt64) : IProp (WasmHeapGF α) :=
  match xs with
  | [] => iprop% emp
  | x :: rest => iprop% (pointsTo_u64 memId ptr x) ∗ (array64At memId (ptr + 8) rest)

instance instTimelessArray64At (memId : Nat) (ptr : UInt32) (xs : List UInt64) :
    BI.Timeless (array64At memId ptr xs) := by
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
theorem array64At_append (memId : Nat) (ptr : UInt32) (xs ys : List UInt64) :
    array64At memId ptr (xs ++ ys) ⊣⊢
      array64At memId ptr xs ∗
        array64At memId (ptr + 8 * UInt32.ofNat xs.length) ys := by
  induction xs generalizing ptr with
  | nil => simp [array64At]; exact BI.emp_sep.symm
  | cons x rest ih =>
    simp only [List.cons_append, List.length_cons, array64At]
    rw [elem64_offset_succ]
    exact (BI.sep_congr_right (ih (ptr + 8))).trans BI.sep_assoc.symm

/-- Split a u64 array into a prefix, its next cell, and the suffix. -/
theorem array64At_append_cons (memId : Nat) (ptr : UInt32) (pre : List UInt64)
    (x : UInt64) (suffix : List UInt64) :
    array64At memId ptr (pre ++ x :: suffix) ⊣⊢
      array64At memId ptr pre ∗
        pointsTo_u64 memId (ptr + 8 * UInt32.ofNat pre.length) x ∗
        array64At memId ((ptr + 8 * UInt32.ofNat pre.length) + 8) suffix := by
  simpa only [array64At] using array64At_append memId ptr pre (x :: suffix)

/-- Focus the first unfilled u64 slot and return a continuation that extends
the filled prefix by one word.  This is the spatial update performed by one
iteration of a symbolic fill loop. -/
theorem array64At_fill_next (memId : Nat) (ptr : UInt32) (i : Nat)
    (value old : UInt64) (suffix : List UInt64) :
    array64At memId ptr (List.replicate i value ++ old :: suffix) ⊢
      pointsTo_u64 memId (ptr + 8 * UInt32.ofNat i) old ∗
      (pointsTo_u64 memId (ptr + 8 * UInt32.ofNat i) value -∗
        array64At memId ptr (List.replicate (i + 1) value ++ suffix)) := by
  iintro Harray
  icases (array64At_append_cons memId ptr (List.replicate i value) old suffix).mp $$
      Harray with ⟨Hpre, Hrest⟩
  icases Hrest with ⟨Hcell, Hsuffix⟩
  ihave Hcell' : pointsTo_u64 memId (ptr + 8 * UInt32.ofNat i) old $$ [Hcell]
  · rw [List.length_replicate]
    iexact Hcell
  ihave Hsuffix' :
      array64At memId ((ptr + 8 * UInt32.ofNat i) + 8) suffix $$ [Hsuffix]
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
  iapply (array64At_append_cons memId ptr (List.replicate i value)
    value suffix).mpr
  isplitl [Hpre]
  · iexact Hpre
  isplitl [Hcell]
  · rw [List.length_replicate]
    iexact Hcell
  · rw [List.length_replicate]
    iexact Hsuffix'

/-- Extract a u64 cell and a continuation accepting its replacement. -/
theorem array64At_set (memId : Nat) (ptr : UInt32) (xs : List UInt64) (k : Nat)
    (v : UInt64) (hk : k < xs.length) :
    array64At memId ptr xs ⊢
      pointsTo_u64 memId (ptr + 8 * UInt32.ofNat k) xs[k] ∗
      (pointsTo_u64 memId (ptr + 8 * UInt32.ofNat k) v -∗
        array64At memId ptr (xs.set k v)) := by
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
theorem array64At_get (memId : Nat) (ptr : UInt32) (xs : List UInt64) (k : Nat)
    (hk : k < xs.length) :
    array64At memId ptr xs ⊢
      pointsTo_u64 memId (ptr + 8 * UInt32.ofNat k) xs[k] ∗
      (pointsTo_u64 memId (ptr + 8 * UInt32.ofNat k) xs[k] -∗
        array64At memId ptr xs) := by
  have h := array64At_set memId ptr xs k xs[k] hk
  rwa [List.set_getElem_self] at h
end PointsTo
end Wasm.SepLogic
