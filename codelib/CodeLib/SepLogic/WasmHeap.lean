import CodeLib.SepLogic.Tactics
import Iris.Instances.Lib.FUpd
import Iris.BI.Lib.GenHeap
import Iris.BI.Lib.MonoNat
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

/-- The key shape shared by every ghost map that is indexed by a module
instance together with an index inside that instance: globals, data segments,
tables and element segments.  Those four keys are the same pair of naturals,
so there is one structure here and the `Ord` bundle below is proved once. -/
structure InstanceIndexKey where
  instanceId : Nat
  index      : Nat
  deriving DecidableEq, Ord, BEq, Repr

/-- Key of the globals ghost map: instance id + global index. -/
abbrev GlobalKey := InstanceIndexKey
/-- Key of the passive-data-segment ghost map: instance id + segment index. -/
abbrev DataSegmentKey := InstanceIndexKey
/-- Key of the tables ghost map: instance id + table index. -/
abbrev TableKey := InstanceIndexKey
/-- Key of the element-segment ghost map: instance id + segment index. -/
abbrev ElementSegmentKey := InstanceIndexKey

-- The projections are also used as bare constants (`congrArg GlobalKey.index h`),
-- and a bare `GlobalKey.index` does not resolve through an `abbrev`.  These
-- aliases keep every such spelling pointing at the one real projection.
namespace GlobalKey
export InstanceIndexKey (instanceId index)
end GlobalKey

namespace DataSegmentKey
export InstanceIndexKey (instanceId index)
end DataSegmentKey

namespace TableKey
export InstanceIndexKey (instanceId index)
end TableKey

namespace ElementSegmentKey
export InstanceIndexKey (instanceId index)
end ElementSegmentKey

-- The derived Ord for a 2-field struct {f1 : α, f2 : β} gives
--   compare a b = (compare a.f1 b.f1).then ((compare a.f2 b.f2).then .eq)
-- and since x.then .eq = x, this equals (compare a.f1 b.f1).then (compare a.f2 b.f2).
private theorem ord_then_eq_self (x : Ordering) : x.then .eq = x := by
  rcases x with _ | _ | _ <;> rfl

-- Reduction: compare on each key = .then of its two field comparisons.
private theorem memKey_compare_eq (a b : MemoryKey) :
    compare a b = (compare a.memId b.memId).then (compare a.addr b.addr) := by
  simp only [compare, Ord.compare, instOrdMemoryKey.ord, ord_then_eq_self]

private theorem instanceIndexKey_compare_eq (a b : InstanceIndexKey) :
    compare a b = (compare a.instanceId b.instanceId).then (compare a.index b.index) := by
  simp only [compare, Ord.compare, instOrdInstanceIndexKey.ord, ord_then_eq_self]

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

-- InstanceIndexKey: OrientedCmp, TransCmp, LawfulEqCmp.  One bundle serves
-- GlobalKey, DataSegmentKey, TableKey and ElementSegmentKey alike.
instance instOrientedCmpInstanceIndexKey :
    OrientedCmp (compare (α := InstanceIndexKey)) where
  eq_swap {a b} := by
    rw [instanceIndexKey_compare_eq a b, instanceIndexKey_compare_eq b a]
    exact then_orient a.instanceId b.instanceId a.index b.index

instance instTransCmpInstanceIndexKey : TransCmp (compare (α := InstanceIndexKey)) where
  isLE_trans {a b c} hab hbc := by
    rw [instanceIndexKey_compare_eq] at hab hbc ⊢
    exact then_isLE_trans a.instanceId b.instanceId c.instanceId a.index b.index c.index hab hbc

instance instLawfulEqCmpInstanceIndexKey :
    LawfulEqCmp (compare (α := InstanceIndexKey)) where
  compare_self {a} := by
    rw [instanceIndexKey_compare_eq]; simp [ReflCmp.compare_self]
  eq_of_compare {a b} h := by
    rw [instanceIndexKey_compare_eq] at h
    rcases h₁ : compare a.instanceId b.instanceId with _ | _ | _ <;>
    simp only [h₁, ord_lt_then, ord_eq_then, ord_gt_then] at h
    · exact absurd h (by decide)
    · have hi := LawfulEqCmp.eq_of_compare (cmp := compare (α := Nat)) h₁
      have hj := LawfulEqCmp.eq_of_compare (cmp := compare (α := Nat)) h
      cases a; cases b; simp_all
    · exact absurd h (by decide)

abbrev WasmHeapMap := fun V => ExtTreeMap MemoryKey V compare
abbrev WasmInstanceIndexMap := fun V => ExtTreeMap InstanceIndexKey V compare
abbrev WasmGlobalMap := WasmInstanceIndexMap
abbrev WasmDataSegmentMap := WasmInstanceIndexMap
abbrev WasmTableMap := WasmInstanceIndexMap
abbrev WasmElementSegmentMap := WasmInstanceIndexMap
abbrev WasmRuntimeModuleMap := fun V => ExtTreeMap Nat V compare
abbrev WasmHostEnvMap := fun V => ExtTreeMap Nat V compare
abbrev WasmExceptionMap := fun V => ExtTreeMap Nat V compare

/-- Generic metadata carried by allocator ghost maps.  It intentionally
contains only representation-independent allocation facts; project-specific
histories may refine it with additional pure invariants. -/
inductive AllocationMetaStatus where
  | live
  | retired
  deriving Repr, DecidableEq

structure AllocationMeta where
  ptr : UInt32
  size : Nat
  alignment : Nat
  status : AllocationMetaStatus
  deriving Repr, DecidableEq

abbrev WasmAllocationMap := fun V => ExtTreeMap Nat V compare

/-- Every authoritative byte in primary memory lies strictly below a logical
frontier.  Other memories are deliberately outside this allocator-domain
invariant. -/
def HeapBelow (σ : WasmHeapMap (Option UInt8)) (frontier : Nat) : Prop :=
  ∀ key value, get? σ key = some value → key.memId = 0 →
    key.addr.toNat < frontier

theorem heapBelow_uint32Size (σ : WasmHeapMap (Option UInt8)) :
    HeapBelow σ UInt32.size := by
  intro key value _ _
  simpa only [UInt32.size] using key.addr.toNat_lt

/-- Raising a sparse-domain frontier preserves the domain invariant. -/
theorem HeapBelow.mono {σ : WasmHeapMap (Option UInt8)}
    {frontier frontier' : Nat} (hbelow : HeapBelow σ frontier)
    (hle : frontier ≤ frontier') : HeapBelow σ frontier' := by
  intro key value hget hmemory
  exact Nat.lt_of_lt_of_le (hbelow key value hget hmemory) hle

/-- A primary-memory key at or above the frontier is absent from the
authoritative sparse heap. -/
theorem HeapBelow.get?_eq_none_of_le
    {σ : WasmHeapMap (Option UInt8)} {frontier : Nat}
    (hbelow : HeapBelow σ frontier) (key : MemoryKey)
    (hmemory : key.memId = 0) (hle : frontier ≤ key.addr.toNat) :
    get? σ key = none := by
  cases hget : get? σ key with
  | none => rfl
  | some value =>
      have := hbelow key value hget hmemory
      omega

/-- Updating the value of an existing authoritative byte preserves every
sparse-domain frontier bound. -/
theorem HeapBelow.insert_existing
    {σ : WasmHeapMap (Option UInt8)} {frontier : Nat}
    (hbelow : HeapBelow σ frontier) (key : MemoryKey)
    (value : Option UInt8)
    (hexists : ∃ oldValue, get? σ key = some oldValue) :
    HeapBelow (insert σ key value) frontier := by
  intro query queryValue hquery hmemory
  by_cases hkey : query = key
  · subst query
    obtain ⟨oldValue, hold⟩ := hexists
    exact hbelow key oldValue hold hmemory
  · apply hbelow query queryValue _ hmemory
    rwa [get?_insert_ne (Ne.symm hkey)] at hquery

/-- Inserting a genuinely fresh key preserves the frontier invariant exactly
when that key is itself below the frontier (for primary memory). -/
theorem HeapBelow.insert_fresh
    {σ : WasmHeapMap (Option UInt8)} {frontier : Nat}
    (hbelow : HeapBelow σ frontier) (key : MemoryKey)
    (value : Option UInt8)
    (hkey : key.memId = 0 → key.addr.toNat < frontier) :
    HeapBelow (insert σ key value) frontier := by
  intro query queryValue hquery hmemory
  by_cases heq : query = key
  · subst query; exact hkey hmemory
  · apply hbelow query queryValue _ hmemory
    rwa [get?_insert_ne (Ne.symm heq)] at hquery

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
  | 18 => ⟨Auth.AuthRF
      (OptionOF (Excl.ExclOF (constOF (DiscreteO Nat)))), by infer_instance⟩
  | 19 => ⟨constOF
      (HeapView Nat (Agree (DiscreteO AllocationMeta))
        WasmAllocationMap), by infer_instance⟩
  | 20 => ⟨MonoNatRF, by infer_instance⟩
  | _ => ⟨constOF Unit, by infer_instance⟩
-- Wire genHeapPreS (following HeapLang's instHeapLangGS_HeapLangS)
instance instWasmHeapPreS (α : Type) :
    genHeapPreS MemoryKey (Option UInt8) (WasmHeapGF α) WasmHeapMap where
  heap := by constructor; exists 4
  metaInfo := by constructor; exists 5
  metaData := by exists 6

/-- Allocator metadata uses explicit ghost names as heap identities, so the
GF slot can be provided globally without adding another name to
`WasmSmallStepGS`. -/
instance instWasmAllocationGhostMapG (α : Type) :
    GhostMapG (WasmHeapGF α) Nat AllocationMeta WasmAllocationMap := by
  constructor
  exists 19
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

/-- Exclusive authoritative agreement on the upper bound of the sparse
primary-memory heap domain.  The authority is held by `stateInterp`; allocator
clients receive the fragment. -/
class WasmHeapDomainGS (α : outParam Type) where
  heapFrontierElem :
    ElemG (WasmHeapGF α)
      (Auth.AuthRF (OptionOF (Excl.ExclOF (constOF (DiscreteO Nat)))))
  heapFrontierName : GName

attribute [reducible, instance] WasmHeapDomainGS.heapFrontierElem

/-- Monotone authority for the number of pages in the primary memory.

The authority records the exact physical page count held by `stateInterp`.
Client snapshots are persistent lower bounds: they remain sound across an
unobserved successful `memory.grow`, while `memory.size` and the tracked grow
rules can issue a fresh snapshot at the exact current count. -/
class WasmMemoryPagesGS (α : outParam Type) where
  memoryPagesElem : ElemG (WasmHeapGF α) MonoNatRF
  memoryPagesName : GName

attribute [reducible, instance] WasmMemoryPagesGS.memoryPagesElem

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
  ipureexact congrArg DiscreteO.car (toAgree_op_valid_iff_eq.mp Hvalid)

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
  ipureexact congrArg DiscreteO.car (toAgree_op_valid_iff_eq.mp Hvalid)

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
  ipureexact congrArg DiscreteO.car (ExclAuth.agree (A := DiscreteO α) Hvalid)

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

/-- Authoritative sparse-heap frontier, held inside `stateInterp`. -/
def heapFrontierAuth {α : Type} [gs : WasmHeapDomainGS α]
    (frontier : Nat) : IProp (WasmHeapGF α) :=
  iOwn (E := gs.heapFrontierElem) gs.heapFrontierName
    (ExclAuth.auth (⟨frontier⟩ : DiscreteO Nat))

/-- Exclusive allocator-client fragment agreeing with the sparse-heap
frontier protected by `stateInterp`. -/
def heapFrontierOwn {α : Type} [gs : WasmHeapDomainGS α]
    (frontier : Nat) : IProp (WasmHeapGF α) :=
  iOwn (E := gs.heapFrontierElem) gs.heapFrontierName
    (ExclAuth.frag (⟨frontier⟩ : DiscreteO Nat))

theorem heapFrontierOwn_agree {α : Type} [gs : WasmHeapDomainGS α]
    (actual expected : Nat) :
    heapFrontierAuth (α := α) actual ∗ heapFrontierOwn expected ⊢
      iprop(⌜actual = expected⌝) := by
  unfold heapFrontierAuth heapFrontierOwn
  iintro ⟨Hauth, Hfrag⟩
  icombine Hauth Hfrag gives %Hvalid
  ipureexact congrArg DiscreteO.car
    (ExclAuth.agree (A := DiscreteO Nat) Hvalid)

theorem heapFrontierOwn_update {α : Type} [gs : WasmHeapDomainGS α]
    (old new' : Nat) :
    heapFrontierAuth (α := α) old ∗ heapFrontierOwn old ==∗
      heapFrontierAuth new' ∗ heapFrontierOwn new' := by
  unfold heapFrontierAuth heapFrontierOwn
  iintro ⟨Hauth, Hfrag⟩
  imod iOwn_update_op (E := gs.heapFrontierElem)
      (ExclAuth.update (A := DiscreteO Nat)
        (a := (⟨old⟩ : DiscreteO Nat)) (b := ⟨old⟩) (a' := ⟨new'⟩))
      $$ [Hauth Hfrag] with Hboth
  · iframe
  imodintro
  icases iOwn_op $$ Hboth with ⟨H1, H2⟩
  iframe

/-- Exact authoritative primary-memory page count, held inside `stateInterp`. -/
def memoryPagesAuth {α : Type} [gs : WasmMemoryPagesGS α]
    (pages : Nat) : IProp (WasmHeapGF α) :=
  iOwn (E := gs.memoryPagesElem) gs.memoryPagesName
    (MonoNat.auth (DFrac.own 1) (MaxNat.ofNat pages))

/-- Persistent knowledge that the primary memory has at least `pages` pages. -/
def memoryPagesOwn {α : Type} [gs : WasmMemoryPagesGS α]
    (pages : Nat) : IProp (WasmHeapGF α) :=
  iOwn (E := gs.memoryPagesElem) gs.memoryPagesName
    (MonoNat.lb (MaxNat.ofNat pages))

instance {α : Type} [WasmMemoryPagesGS α] (pages : Nat) :
    BI.Timeless (memoryPagesAuth (α := α) pages) := by
  unfold memoryPagesAuth
  infer_instance

instance {α : Type} [WasmMemoryPagesGS α] (pages : Nat) :
    BI.Timeless (memoryPagesOwn (α := α) pages) := by
  unfold memoryPagesOwn
  infer_instance

instance {α : Type} [WasmMemoryPagesGS α] (pages : Nat) :
    BI.Persistent (memoryPagesOwn (α := α) pages) := by
  unfold memoryPagesOwn
  infer_instance

/-- A page snapshot is a lower bound on the exact authoritative count. -/
theorem memoryPagesOwn_agree {α : Type} [gs : WasmMemoryPagesGS α]
    (actual expected : Nat) :
    memoryPagesAuth (α := α) actual ∗ memoryPagesOwn expected ⊢
      iprop(⌜expected ≤ actual⌝) := by
  unfold memoryPagesAuth memoryPagesOwn
  iintro ⟨Hauth, Hsnapshot⟩
  icombine Hauth Hsnapshot gives %Hvalid
  ipureexact (MonoNat.both_valid
    (MaxNat.ofNat actual) (MaxNat.ofNat expected)).mp Hvalid

/-- Obtain an exact persistent snapshot from the page-count authority. -/
theorem memoryPagesOwn_snapshot {α : Type} [gs : WasmMemoryPagesGS α]
    (pages : Nat) :
    memoryPagesAuth (α := α) pages ⊢ memoryPagesOwn pages := by
  unfold memoryPagesAuth memoryPagesOwn
  iintro Hauth
  iapply iOwn_mono $$ Hauth
  exact MonoNat.included _ _

/-- Advance the exact page-count authority and issue an exact new snapshot. -/
theorem memoryPagesAuth_update {α : Type} [gs : WasmMemoryPagesGS α]
    (old new' : Nat) (hmono : old ≤ new') :
    memoryPagesAuth (α := α) old ==∗
      memoryPagesAuth new' ∗ memoryPagesOwn new' := by
  unfold memoryPagesAuth memoryPagesOwn
  iintro Hauth
  imod iOwn_update $$ Hauth with Hauth
  · exact MonoNat.update (MaxNat.ofNat new') hmono
  imodintro
  iunfold MonoNat.auth at Hauth
  iunfold MonoNat.auth
  iunfold MonoNat.lb
  icases iOwn_op $$ Hauth with ⟨Hauthority, #Hsnapshot⟩
  isplitl [Hauthority Hsnapshot]
  · icombine Hauthority Hsnapshot as Hauth
    iexact Hauth
  · iexact Hsnapshot

/-- Allocate only the page-count authority.  Legacy adequacy frontends that
do not expose page snapshots use this form. -/
theorem memoryPages_init_authority {α : Type} (pages : Nat) :
    ⊢@{IProp (WasmHeapGF α)} |==>
      ∃ gs : WasmMemoryPagesGS α,
        @memoryPagesAuth α gs pages := by
  letI memoryPagesElem : ElemG (WasmHeapGF α) MonoNatRF := by
    exists 20
  imod (iOwn_alloc (E := memoryPagesElem)
      (MonoNat.auth (DFrac.own 1) (MaxNat.ofNat pages))
      (MonoNat.auth_valid (MaxNat.ofNat pages))) with
    ⟨%memoryPagesName, Hauth⟩
  let gs : WasmMemoryPagesGS α :=
    { memoryPagesElem
      memoryPagesName }
  imodintro
  iexists gs
  unfold memoryPagesAuth
  iexact Hauth

/-- Allocate page-count authority together with an exact persistent snapshot.
Allocator-aware adequacy frontends expose the snapshot to their client proof. -/
theorem memoryPages_init {α : Type} (pages : Nat) :
    ⊢@{IProp (WasmHeapGF α)} |==>
      ∃ gs : WasmMemoryPagesGS α,
        @memoryPagesAuth α gs pages ∗
          @memoryPagesOwn α gs pages := by
  letI memoryPagesElem : ElemG (WasmHeapGF α) MonoNatRF := by
    exists 20
  imod (iOwn_alloc (E := memoryPagesElem)
      (MonoNat.auth (DFrac.own 1) (MaxNat.ofNat pages) •
        MonoNat.lb (MaxNat.ofNat pages))
      (by simpa using
        (MonoNat.both_valid
          (MaxNat.ofNat pages) (MaxNat.ofNat pages)).mpr (Nat.le_refl pages))) with
    ⟨%memoryPagesName, Hboth⟩
  icases iOwn_op $$ Hboth with ⟨Hauth, Hsnapshot⟩
  let gs : WasmMemoryPagesGS α :=
    { memoryPagesElem
      memoryPagesName }
  imodintro
  iexists gs
  unfold memoryPagesAuth memoryPagesOwn
  iframe Hauth Hsnapshot

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
  ipureexact congrArg DiscreteO.car (ExclAuth.agree (A := DiscreteO Nat) Hvalid)

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
    ipureexact congrArg DiscreteO.car (ExclAuth.agree (A := DiscreteO Nat) Hvalid)
  imod iOwn_update_op (E := gs.instanceElem)
      (ExclAuth.update (A := DiscreteO Nat)
        (a := (⟨actual⟩ : DiscreteO Nat))
        (b := ⟨expected⟩)
        (a' := ⟨new'⟩))
      $$ [Hauth Hfrag] with Hboth
  · iframe
  imodintro
  icases iOwn_op $$ Hboth with ⟨H1, H2⟩
  isplitl_exacts [H1 H2]
  · ipureexact heq

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
private theorem reassemble32_nat (n : Nat) (h : n < 2 ^ 32) :
    n % 2 ^ 8 ||| (((n >>> 8) % 2 ^ 8) <<< 8) % 2 ^ 32 |||
      (((n >>> 16) % 2 ^ 8) <<< 16) % 2 ^ 32 |||
      (((n >>> 24) % 2 ^ 8) <<< 24) % 2 ^ 32 = n := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_or, Nat.testBit_mod_two_pow,
    Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  by_cases hi8 : i < 8
  · simp [hi8, show i < 32 by omega, show ¬i ≥ 8 by omega,
      show ¬i ≥ 16 by omega, show ¬i ≥ 24 by omega]
  by_cases hi16 : i < 16
  · have heq : 8 + (i - 8) = i := by omega
    simp [hi8, heq, show i ≥ 8 by omega, show i < 32 by omega,
      show i - 8 < 8 by omega, show ¬i ≥ 16 by omega, show ¬i ≥ 24 by omega]
  by_cases hi24 : i < 24
  · have heq : 16 + (i - 16) = i := by omega
    simp [hi8, heq, show i ≥ 16 by omega, show i < 32 by omega,
      show ¬i - 8 < 8 by omega, show i - 16 < 8 by omega, show ¬i ≥ 24 by omega]
  by_cases hi32 : i < 32
  · have heq : 24 + (i - 24) = i := by omega
    simp [hi8, hi32, heq, show i ≥ 24 by omega, show ¬i - 8 < 8 by omega,
      show ¬i - 16 < 8 by omega, show i - 24 < 8 by omega]
  · have hibound : n.testBit i = false :=
      Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [hi8, hibound, show ¬i < 32 by omega, show ¬i - 8 < 8 by omega,
      show ¬i - 16 < 8 by omega, show ¬i - 24 < 8 by omega]

private theorem reassemble64_nat (n : Nat) (h : n < 2 ^ 64) :
    n % 2 ^ 8 ||| (((n >>> 8) % 2 ^ 8) <<< 8) % 2 ^ 64 |||
      (((n >>> 16) % 2 ^ 8) <<< 16) % 2 ^ 64 |||
      (((n >>> 24) % 2 ^ 8) <<< 24) % 2 ^ 64 |||
      (((n >>> 32) % 2 ^ 8) <<< 32) % 2 ^ 64 |||
      (((n >>> 40) % 2 ^ 8) <<< 40) % 2 ^ 64 |||
      (((n >>> 48) % 2 ^ 8) <<< 48) % 2 ^ 64 |||
      (((n >>> 56) % 2 ^ 8) <<< 56) % 2 ^ 64 = n := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_or, Nat.testBit_mod_two_pow,
    Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  by_cases h8 : i < 8
  · simp [h8, show i < 64 by omega, show ¬ i ≥ 8 by omega, show ¬ i ≥ 16 by omega,
      show ¬ i ≥ 24 by omega, show ¬ i ≥ 32 by omega, show ¬ i ≥ 40 by omega,
      show ¬ i ≥ 48 by omega, show ¬ i ≥ 56 by omega]
  by_cases h16 : i < 16
  · have heq : 8 + (i - 8) = i := by omega
    simp [h8, heq, show i ≥ 8 by omega, show i < 64 by omega, show i - 8 < 8 by omega,
      show ¬ i ≥ 16 by omega, show ¬ i ≥ 24 by omega, show ¬ i ≥ 32 by omega,
      show ¬ i ≥ 40 by omega, show ¬ i ≥ 48 by omega, show ¬ i ≥ 56 by omega]
  by_cases h24 : i < 24
  · have heq : 16 + (i - 16) = i := by omega
    simp [h8, heq, show i ≥ 16 by omega, show i < 64 by omega, show ¬ i - 8 < 8 by omega,
      show i - 16 < 8 by omega, show ¬ i ≥ 24 by omega, show ¬ i ≥ 32 by omega,
      show ¬ i ≥ 40 by omega, show ¬ i ≥ 48 by omega, show ¬ i ≥ 56 by omega]
  by_cases h32 : i < 32
  · have heq : 24 + (i - 24) = i := by omega
    simp [h8, heq, show i ≥ 24 by omega, show i < 64 by omega, show ¬ i - 8 < 8 by omega,
      show ¬ i - 16 < 8 by omega, show i - 24 < 8 by omega, show ¬ i ≥ 32 by omega,
      show ¬ i ≥ 40 by omega, show ¬ i ≥ 48 by omega, show ¬ i ≥ 56 by omega]
  by_cases h40 : i < 40
  · have heq : 32 + (i - 32) = i := by omega
    simp [h8, heq, show i ≥ 32 by omega, show i < 64 by omega, show ¬ i - 8 < 8 by omega,
      show ¬ i - 16 < 8 by omega, show ¬ i - 24 < 8 by omega, show i - 32 < 8 by omega,
      show ¬ i ≥ 40 by omega, show ¬ i ≥ 48 by omega, show ¬ i ≥ 56 by omega]
  by_cases h48 : i < 48
  · have heq : 40 + (i - 40) = i := by omega
    simp [h8, heq, show i ≥ 40 by omega, show i < 64 by omega, show ¬ i - 8 < 8 by omega,
      show ¬ i - 16 < 8 by omega, show ¬ i - 24 < 8 by omega, show ¬ i - 32 < 8 by omega,
      show i - 40 < 8 by omega, show ¬ i ≥ 48 by omega, show ¬ i ≥ 56 by omega]
  by_cases h56 : i < 56
  · have heq : 48 + (i - 48) = i := by omega
    simp [h8, heq, show i ≥ 48 by omega, show i < 64 by omega, show ¬ i - 8 < 8 by omega,
      show ¬ i - 16 < 8 by omega, show ¬ i - 24 < 8 by omega, show ¬ i - 32 < 8 by omega,
      show ¬ i - 40 < 8 by omega, show i - 48 < 8 by omega, show ¬ i ≥ 56 by omega]
  by_cases h64 : i < 64
  · have heq : 56 + (i - 56) = i := by omega
    simp [h8, heq, show i ≥ 56 by omega, show i < 64 by omega, show ¬ i - 8 < 8 by omega,
      show ¬ i - 16 < 8 by omega, show ¬ i - 24 < 8 by omega, show ¬ i - 32 < 8 by omega,
      show ¬ i - 40 < 8 by omega, show ¬ i - 48 < 8 by omega, show i - 56 < 8 by omega]
  · have hibound : n.testBit i = false :=
      Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [h8, hibound, show ¬ i < 64 by omega, show ¬ i - 8 < 8 by omega,
      show ¬ i - 16 < 8 by omega, show ¬ i - 24 < 8 by omega, show ¬ i - 32 < 8 by omega,
      show ¬ i - 40 < 8 by omega, show ¬ i - 48 < 8 by omega, show ¬ i - 56 < 8 by omega]

theorem u64Byte_reassemble (v : UInt64) :
    (u64Byte v 0).toUInt64 ||| ((u64Byte v 1).toUInt64 <<< 8) |||
      ((u64Byte v 2).toUInt64 <<< 16) |||
      ((u64Byte v 3).toUInt64 <<< 24) |||
      ((u64Byte v 4).toUInt64 <<< 32) |||
      ((u64Byte v 5).toUInt64 <<< 40) |||
      ((u64Byte v 6).toUInt64 <<< 48) |||
      ((u64Byte v 7).toUInt64 <<< 56) = v := by
  apply UInt64.toNat_inj.mp
  unfold u64Byte
  simp only [UInt64.toNat_or, UInt64.toNat_shiftLeft,
    UInt8.toNat_toUInt64, UInt64.toNat_toUInt8, UInt64.toNat_shiftRight]
  exact reassemble64_nat v.toNat (UInt64.toNat_lt v)

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

omit inst in
/-- Address ladder for a 4-byte access at `addr`: given room for the whole
word, none of `addr + 1 … addr + 3` wraps, so each `toNat` is the obvious sum.
Stated with numerals (`addr + 1`, not `addr + UInt32.ofNat 1`) because that is
the shape the `load32` / `store32` rules and their callers write. -/
theorem UInt32.addSteps4 (addr : UInt32) (hroom : addr.toNat + 4 ≤ 4294967296) :
    (addr + 1).toNat = addr.toNat + 1 ∧
    (addr + 2).toNat = addr.toNat + 2 ∧
    (addr + 3).toNat = addr.toNat + 3 :=
  ⟨by simpa using UInt32.add_ofNat_toNat_noWrap addr 1 (by decide) (by omega),
    by simpa using UInt32.add_ofNat_toNat_noWrap addr 2 (by decide) (by omega),
    by simpa using UInt32.add_ofNat_toNat_noWrap addr 3 (by decide) (by omega)⟩

omit inst in
/-- Address ladder for an 8-byte access at `addr`: given room for the whole
word, none of `addr + 1 … addr + 7` wraps. The numeral form matches the
`load64` / `store64` premises. -/
theorem UInt32.addSteps8 (addr : UInt32) (hroom : addr.toNat + 8 ≤ 4294967296) :
    (addr + 1).toNat = addr.toNat + 1 ∧
    (addr + 2).toNat = addr.toNat + 2 ∧
    (addr + 3).toNat = addr.toNat + 3 ∧
    (addr + 4).toNat = addr.toNat + 4 ∧
    (addr + 5).toNat = addr.toNat + 5 ∧
    (addr + 6).toNat = addr.toNat + 6 ∧
    (addr + 7).toNat = addr.toNat + 7 :=
  ⟨by simpa using UInt32.add_ofNat_toNat_noWrap addr 1 (by decide) (by omega),
    by simpa using UInt32.add_ofNat_toNat_noWrap addr 2 (by decide) (by omega),
    by simpa using UInt32.add_ofNat_toNat_noWrap addr 3 (by decide) (by omega),
    by simpa using UInt32.add_ofNat_toNat_noWrap addr 4 (by decide) (by omega),
    by simpa using UInt32.add_ofNat_toNat_noWrap addr 5 (by decide) (by omega),
    by simpa using UInt32.add_ofNat_toNat_noWrap addr 6 (by decide) (by omega),
    by simpa using UInt32.add_ofNat_toNat_noWrap addr 7 (by decide) (by omega)⟩

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
  apply UInt32.toNat_inj.mp
  unfold u32Byte
  simp only [UInt32.toNat_or, UInt32.toNat_shiftLeft,
    UInt8.toNat_toUInt32, UInt32.toNat_toUInt8, UInt32.toNat_shiftRight]
  exact reassemble32_nat v.toNat (UInt32.toNat_lt v)

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
  isplitl_exacts [HsrcCell HdstCell]
  iintro ⟨HsrcCell, HdstCell⟩
  isplitl [HdstPre HdstCell HdstSuffix]
  · iapply_frame (arrayAt_append_cons memId dst pre value dstSuffix).mpr
  · iapply_frame (arrayAt_append_cons memId src pre value srcSuffix).mpr

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
  · irw_exact [List.length_replicate] with Hcell
  ihave Hsuffix' :
      array64At memId ((ptr + 8 * UInt32.ofNat i) + 8) suffix $$ [Hsuffix]
  · irw_exact [List.length_replicate] with Hsuffix
  isplitl_exact Hcell'
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
  isplitl_exact Hpre
  isplitl_rw_exact [List.length_replicate] with Hcell
  · irw_exact [List.length_replicate] with Hsuffix'

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
