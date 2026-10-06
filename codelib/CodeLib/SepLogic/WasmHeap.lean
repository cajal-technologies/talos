import CodeLib.SepLogic.Tactics
import CodeLib.ByteReassembly
import Iris.Instances.Lib.FUpd
import Iris.BI.Lib.GenHeap
import Iris.BI.Lib.MonoNat
import Iris.Algebra.Lib.ExclAuth
import Interpreter.Wasm.Mem
import Interpreter.Wasm.Syntax
import Interpreter.Wasm.Host
import Interpreter.Wasm.SmallStep
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
      rw [h₁, h₂] at h1s; exact absurd h1s (by decide)
    · rw [h₃, ord_isLE_gt] at hac; exact absurd hac (by decide)
  -- lt.eq: b1 = c1, so compare a1 c1 = .lt
  · have heq := LawfulEqCmp.eq_of_compare (cmp := compare (α := α)) h₂
    simp [← heq, h₁]
  -- lt.gt: hbc is false
  · simp only [h₂, ord_gt_then, ord_isLE_gt] at hbc; exact absurd hbc (by decide)
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
    rw [hac, ord_eq_then]; exact TransCmp.isLE_trans hab hbc
  -- eq.gt: hbc is false
  · simp only [h₂, ord_gt_then, ord_isLE_gt] at hbc; exact absurd hbc (by decide)
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

attribute [reducible, instance 50] WasmHeapDomainGS.heapFrontierElem
attribute [reducible] WasmHeapDomainGS.heapFrontierName

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

/-- Ghost-name providers — one per ghost-map component.  Each is a thin
wrapper around `GName`; `WasmGS` (priority 200) and the per-component
concrete classes (priority 100) provide instances. -/
class WasmGlobalGhostName (GF : BundledGFunctors) where
  globalName : GName

class WasmDataSegmentGhostName (GF : BundledGFunctors) where
  dataSegmentName : GName

class WasmTableGhostName (GF : BundledGFunctors) where
  tableName : GName

class WasmElementSegmentGhostName (GF : BundledGFunctors) where
  elementSegmentName : GName

class WasmExceptionGhostName (GF : BundledGFunctors) where
  exceptionName : GName

class WasmTagTableGhostName (GF : BundledGFunctors) where
  tagTableName : GName

/-- Carries both names needed by `runtimeModuleOwn`. -/
class WasmRuntimeModuleGhostNames (GF : BundledGFunctors) where
  runtimeName  : GName
  instanceName : GName
  instanceElem : ElemG GF (Auth.AuthRF (OptionOF (Excl.ExclOF (constOF (DiscreteO Nat)))))

class WasmRuntimeInstancesGhostName (GF : BundledGFunctors) where
  runtimeInstancesName : GName

class WasmHostEnvGhostName (GF : BundledGFunctors) where
  hostEnvName : GName

class WasmHostStateGhostName (GF : BundledGFunctors) (α : outParam Type) where
  hostStateName : GName
  hostStateElem : ElemG GF (Auth.AuthRF (OptionOF (Excl.ExclOF (constOF (DiscreteO α)))))

attribute [reducible, instance] WasmHostStateGhostName.hostStateElem

class WasmHeapFrontierGhostName (GF : BundledGFunctors) where
  heapFrontierName : GName
  heapFrontierElem : ElemG GF (Auth.AuthRF (OptionOF (Excl.ExclOF (constOF (DiscreteO Nat)))))

attribute [reducible, instance] WasmHeapFrontierGhostName.heapFrontierElem
-- Must be registered after heapFrontierElem so it wins for bare [ElemG GF (Auth.AuthRF ...)]
-- synthesis in [WasmGS] context (currentInstance* resources live at this slot).
attribute [reducible, instance] WasmRuntimeModuleGhostNames.instanceElem

class WasmMemoryPagesGhostName (GF : BundledGFunctors) where
  memoryPagesName : GName

-- Instances from concrete component classes (priority 100)
@[reducible] instance (priority := 100) instWasmGlobalGhostName_of_WasmGlobalGS
    {α : Type} [g : WasmGlobalGS α] : WasmGlobalGhostName (WasmHeapGF α) :=
  ⟨g.globalName⟩

@[reducible] instance (priority := 100) instWasmDataSegmentGhostName_of_WasmDataSegmentGS
    {α : Type} [g : WasmDataSegmentGS α] : WasmDataSegmentGhostName (WasmHeapGF α) :=
  ⟨g.dataSegmentName⟩

@[reducible] instance (priority := 100) instWasmTableGhostName_of_WasmTableGS
    {α : Type} [g : WasmTableGS α] : WasmTableGhostName (WasmHeapGF α) :=
  ⟨g.tableName⟩

@[reducible] instance (priority := 100) instWasmElementSegmentGhostName_of_WasmElementSegmentGS
    {α : Type} [g : WasmElementSegmentGS α] : WasmElementSegmentGhostName (WasmHeapGF α) :=
  ⟨g.elementSegmentName⟩

@[reducible] instance (priority := 100) instWasmExceptionGhostName_of_WasmExceptionGS
    {α : Type} [g : WasmExceptionGS α] : WasmExceptionGhostName (WasmHeapGF α) :=
  ⟨g.exceptionName⟩

@[reducible] instance (priority := 100) instWasmTagTableGhostName_of_WasmTagTableGS
    {α : Type} [g : WasmTagTableGS α] : WasmTagTableGhostName (WasmHeapGF α) :=
  ⟨g.tagTableName⟩

@[reducible] instance (priority := 100) instWasmRuntimeModuleGhostNames_of_concrete
    {α : Type} [r : WasmRuntimeModuleGS α] [i : WasmInstanceGS α] :
    WasmRuntimeModuleGhostNames (WasmHeapGF α) :=
  ⟨r.runtimeName, i.instanceName, i.instanceElem⟩

@[reducible] instance (priority := 100) instWasmRuntimeInstancesGhostName_of_WasmRuntimeInstancesGS
    {α : Type} [g : WasmRuntimeInstancesGS α] : WasmRuntimeInstancesGhostName (WasmHeapGF α) :=
  ⟨g.runtimeInstancesName⟩

@[reducible] instance (priority := 100) instWasmHostEnvGhostName_of_WasmHostEnvGS
    {α : Type} [g : WasmHostEnvGS α] : WasmHostEnvGhostName (WasmHeapGF α) :=
  ⟨g.hostEnvName⟩

@[reducible] instance (priority := 100) instWasmHostStateGhostName_of_WasmHostStateGS
    {α : Type} [g : WasmHostStateGS α] : WasmHostStateGhostName (WasmHeapGF α) α :=
  ⟨g.hostStateName, g.hostStateElem⟩

@[reducible] instance (priority := 100) instWasmHeapFrontierGhostName_of_WasmHeapDomainGS
    {α : Type} [g : WasmHeapDomainGS α] : WasmHeapFrontierGhostName (WasmHeapGF α) :=
  ⟨g.heapFrontierName, g.heapFrontierElem⟩

@[reducible] instance (priority := 100) instWasmMemoryPagesGhostName_of_WasmMemoryPagesGS
    {α : Type} [g : WasmMemoryPagesGS α] : WasmMemoryPagesGhostName (WasmHeapGF α) :=
  ⟨g.memoryPagesName⟩

def globalPointsTo {GF : BundledGFunctors} [GhostMapG GF GlobalKey Value WasmGlobalMap]
    [gn : WasmGlobalGhostName GF] (key : GlobalKey) (value : Value) : IProp GF :=
  ghost_map_elem gn.globalName (DFrac.own 1) key value

def globalPointsToAt {GF : BundledGFunctors} [GhostMapG GF GlobalKey Value WasmGlobalMap]
    [WasmGlobalGhostName GF] (instanceId : Nat) (index : Nat) (value : Value) : IProp GF :=
  globalPointsTo ⟨instanceId, index⟩ value

theorem globalPointsToAt_eq {GF : BundledGFunctors} [GhostMapG GF GlobalKey Value WasmGlobalMap]
    [WasmGlobalGhostName GF] (i j : Nat) (v : Value) :
    globalPointsToAt (GF := GF) i j v = globalPointsTo ⟨i, j⟩ v := rfl

instance {GF : BundledGFunctors} [GhostMapG GF GlobalKey Value WasmGlobalMap]
    [WasmGlobalGhostName GF] (key : GlobalKey) (value : Value) :
    BI.Timeless (globalPointsTo (GF := GF) key value) := by
  unfold globalPointsTo
  infer_instance

theorem globalPointsTo_lookup {GF : BundledGFunctors} [GhostMapG GF GlobalKey Value WasmGlobalMap]
    [gn : WasmGlobalGhostName GF] (σ : WasmGlobalMap Value) (key : GlobalKey) (value : Value) :
    ghost_map_auth (GF := GF) gn.globalName (DFrac.own 1) σ -∗
      globalPointsTo key value -∗
      iprop(⌜get? σ key = some value⌝) := by
  unfold globalPointsTo
  iapply ghost_map_lookup

/-- Authoritative update for one owned global entry. -/
theorem globalPointsTo_update {GF : BundledGFunctors} [GhostMapG GF GlobalKey Value WasmGlobalMap]
    [gn : WasmGlobalGhostName GF] (σ : WasmGlobalMap Value) (key : GlobalKey)
    (oldValue newValue : Value) :
    ghost_map_auth (GF := GF) gn.globalName (DFrac.own 1) σ -∗
      globalPointsTo key oldValue ==∗
      ghost_map_auth gn.globalName (DFrac.own 1)
        (insert σ key newValue) ∗
      globalPointsTo key newValue := by
  unfold globalPointsTo
  iapply ghost_map_update

def dataSegmentPointsTo {GF : BundledGFunctors}
    [GhostMapG GF DataSegmentKey (Option (List UInt8)) WasmDataSegmentMap]
    [gn : WasmDataSegmentGhostName GF] (key : DataSegmentKey) (value : Option (List UInt8)) :
    IProp GF :=
  ghost_map_elem gn.dataSegmentName (DFrac.own 1) key value

def dataSegmentPointsToAt {GF : BundledGFunctors}
    [GhostMapG GF DataSegmentKey (Option (List UInt8)) WasmDataSegmentMap]
    [WasmDataSegmentGhostName GF] (instanceId : Nat) (index : Nat) (value : Option (List UInt8)) :
    IProp GF :=
  dataSegmentPointsTo ⟨instanceId, index⟩ value

theorem dataSegmentPointsToAt_eq {GF : BundledGFunctors}
    [GhostMapG GF DataSegmentKey (Option (List UInt8)) WasmDataSegmentMap]
    [WasmDataSegmentGhostName GF] (i j : Nat) (v : Option (List UInt8)) :
    dataSegmentPointsToAt (GF := GF) i j v = dataSegmentPointsTo ⟨i, j⟩ v := rfl

instance {GF : BundledGFunctors}
    [GhostMapG GF DataSegmentKey (Option (List UInt8)) WasmDataSegmentMap]
    [WasmDataSegmentGhostName GF] (key : DataSegmentKey) (value : Option (List UInt8)) :
    BI.Timeless (dataSegmentPointsTo (GF := GF) key value) := by
  unfold dataSegmentPointsTo
  infer_instance

instance {GF : BundledGFunctors}
    [GhostMapG GF DataSegmentKey (Option (List UInt8)) WasmDataSegmentMap]
    [WasmDataSegmentGhostName GF] (instanceId index : Nat) (value : Option (List UInt8)) :
    BI.Timeless (dataSegmentPointsToAt (GF := GF) instanceId index value) := by
  unfold dataSegmentPointsToAt
  infer_instance

theorem dataSegmentPointsTo_lookup {GF : BundledGFunctors}
    [GhostMapG GF DataSegmentKey (Option (List UInt8)) WasmDataSegmentMap]
    [gn : WasmDataSegmentGhostName GF] (σ : WasmDataSegmentMap (Option (List UInt8)))
    (key : DataSegmentKey) (value : Option (List UInt8)) :
    ghost_map_auth (GF := GF) gn.dataSegmentName (DFrac.own 1) σ -∗
      dataSegmentPointsTo key value -∗
      iprop(⌜get? σ key = some value⌝) := by
  unfold dataSegmentPointsTo
  iapply ghost_map_lookup

theorem dataSegmentPointsTo_update {GF : BundledGFunctors}
    [GhostMapG GF DataSegmentKey (Option (List UInt8)) WasmDataSegmentMap]
    [gn : WasmDataSegmentGhostName GF] (σ : WasmDataSegmentMap (Option (List UInt8)))
    (key : DataSegmentKey) (oldValue newValue : Option (List UInt8)) :
    ghost_map_auth (GF := GF) gn.dataSegmentName (DFrac.own 1) σ -∗
      dataSegmentPointsTo key oldValue ==∗
      ghost_map_auth gn.dataSegmentName (DFrac.own 1)
        (insert σ key newValue) ∗
      dataSegmentPointsTo key newValue := by
  unfold dataSegmentPointsTo
  iapply ghost_map_update

def tablePointsTo {GF : BundledGFunctors} [GhostMapG GF TableKey TableInst WasmTableMap]
    [gn : WasmTableGhostName GF] (key : TableKey) (table : TableInst) : IProp GF :=
  ghost_map_elem gn.tableName (DFrac.own 1) key table

def tablePointsToAt {GF : BundledGFunctors} [GhostMapG GF TableKey TableInst WasmTableMap]
    [WasmTableGhostName GF] (instanceId : Nat) (index : Nat) (table : TableInst) :
    IProp GF :=
  tablePointsTo ⟨instanceId, index⟩ table

theorem tablePointsToAt_eq {GF : BundledGFunctors} [GhostMapG GF TableKey TableInst WasmTableMap]
    [WasmTableGhostName GF] (i j : Nat) (t : TableInst) :
    tablePointsToAt (GF := GF) i j t = tablePointsTo ⟨i, j⟩ t := rfl

instance {GF : BundledGFunctors} [GhostMapG GF TableKey TableInst WasmTableMap]
    [WasmTableGhostName GF] (key : TableKey) (table : TableInst) :
    BI.Timeless (tablePointsTo (GF := GF) key table) := by
  unfold tablePointsTo
  infer_instance

theorem tablePointsTo_lookup {GF : BundledGFunctors} [GhostMapG GF TableKey TableInst WasmTableMap]
    [gn : WasmTableGhostName GF] (σ : WasmTableMap TableInst) (key : TableKey) (table : TableInst) :
    ghost_map_auth (GF := GF) gn.tableName (DFrac.own 1) σ -∗
      tablePointsTo key table -∗
      iprop(⌜get? σ key = some table⌝) := by
  unfold tablePointsTo
  iapply ghost_map_lookup

theorem tablePointsTo_update {GF : BundledGFunctors} [GhostMapG GF TableKey TableInst WasmTableMap]
    [gn : WasmTableGhostName GF] (σ : WasmTableMap TableInst) (key : TableKey)
    (oldTable newTable : TableInst) :
    ghost_map_auth (GF := GF) gn.tableName (DFrac.own 1) σ -∗
      tablePointsTo key oldTable ==∗
      ghost_map_auth gn.tableName (DFrac.own 1)
        (insert σ key newTable) ∗
      tablePointsTo key newTable := by
  unfold tablePointsTo
  iapply ghost_map_update

def elementSegmentPointsTo {GF : BundledGFunctors}
    [GhostMapG GF ElementSegmentKey (Option (List (Option Nat))) WasmElementSegmentMap]
    [gn : WasmElementSegmentGhostName GF] (key : ElementSegmentKey)
    (value : Option (List (Option Nat))) : IProp GF :=
  ghost_map_elem gn.elementSegmentName (DFrac.own 1) key value

def elementSegmentPointsToAt {GF : BundledGFunctors}
    [GhostMapG GF ElementSegmentKey (Option (List (Option Nat))) WasmElementSegmentMap]
    [WasmElementSegmentGhostName GF] (instanceId : Nat) (index : Nat)
    (value : Option (List (Option Nat))) : IProp GF :=
  elementSegmentPointsTo ⟨instanceId, index⟩ value

theorem elementSegmentPointsToAt_eq {GF : BundledGFunctors}
    [GhostMapG GF ElementSegmentKey (Option (List (Option Nat))) WasmElementSegmentMap]
    [WasmElementSegmentGhostName GF] (i j : Nat) (v : Option (List (Option Nat))) :
    elementSegmentPointsToAt (GF := GF) i j v = elementSegmentPointsTo ⟨i, j⟩ v := rfl

instance {GF : BundledGFunctors}
    [GhostMapG GF ElementSegmentKey (Option (List (Option Nat))) WasmElementSegmentMap]
    [WasmElementSegmentGhostName GF] (key : ElementSegmentKey)
    (value : Option (List (Option Nat))) :
    BI.Timeless (elementSegmentPointsTo (GF := GF) key value) := by
  unfold elementSegmentPointsTo
  infer_instance

theorem elementSegmentPointsTo_lookup {GF : BundledGFunctors}
    [GhostMapG GF ElementSegmentKey (Option (List (Option Nat))) WasmElementSegmentMap]
    [gn : WasmElementSegmentGhostName GF] (σ : WasmElementSegmentMap (Option (List (Option Nat))))
    (key : ElementSegmentKey) (value : Option (List (Option Nat))) :
    ghost_map_auth (GF := GF) gn.elementSegmentName (DFrac.own 1) σ -∗
      elementSegmentPointsTo key value -∗
      iprop(⌜get? σ key = some value⌝) := by
  unfold elementSegmentPointsTo
  iapply ghost_map_lookup

theorem elementSegmentPointsTo_update {GF : BundledGFunctors}
    [GhostMapG GF ElementSegmentKey (Option (List (Option Nat))) WasmElementSegmentMap]
    [gn : WasmElementSegmentGhostName GF] (σ : WasmElementSegmentMap (Option (List (Option Nat))))
    (key : ElementSegmentKey) (oldValue newValue : Option (List (Option Nat))) :
    ghost_map_auth (GF := GF) gn.elementSegmentName (DFrac.own 1) σ -∗
      elementSegmentPointsTo key oldValue ==∗
      ghost_map_auth gn.elementSegmentName (DFrac.own 1)
        (insert σ key newValue) ∗
      elementSegmentPointsTo key newValue := by
  unfold elementSegmentPointsTo
  iapply ghost_map_update

-- raw ghost_map_elem for a module instance; used internally in stateInterp bigOpL
def exceptionPointsTo {GF : BundledGFunctors}
    [GhostMapG GF Nat (Nat × List Value) WasmExceptionMap]
    (ghostName : GName) (index : Nat) (dq : DFrac) (tagAndArgs : Nat × List Value) :
    IProp GF :=
  ghost_map_elem ghostName dq index tagAndArgs

instance {GF : BundledGFunctors} [GhostMapG GF Nat (Nat × List Value) WasmExceptionMap]
    (ghostName : GName) (index : Nat) (dq : DFrac) (tagAndArgs : Nat × List Value) :
    BI.Timeless (exceptionPointsTo (GF := GF) ghostName index dq tagAndArgs) := by
  unfold exceptionPointsTo
  infer_instance

theorem exceptionPointsTo_lookup {GF : BundledGFunctors}
    [GhostMapG GF Nat (Nat × List Value) WasmExceptionMap]
    (ghostName : GName) (σ : WasmExceptionMap (Nat × List Value))
    (index : Nat) (dq : DFrac) (tagAndArgs : Nat × List Value) :
    ghost_map_auth (GF := GF) ghostName (DFrac.own 1) σ -∗
      exceptionPointsTo ghostName index dq tagAndArgs -∗
      iprop(⌜get? σ index = some tagAndArgs⌝) := by
  unfold exceptionPointsTo
  iapply ghost_map_lookup

theorem exceptionPointsTo_update {GF : BundledGFunctors}
    [GhostMapG GF Nat (Nat × List Value) WasmExceptionMap]
    (ghostName : GName) (σ : WasmExceptionMap (Nat × List Value))
    (index : Nat) (oldVal newVal : Nat × List Value) :
    ghost_map_auth (GF := GF) ghostName (DFrac.own 1) σ -∗
      exceptionPointsTo ghostName index (DFrac.own 1) oldVal ==∗
      ghost_map_auth ghostName (DFrac.own 1)
        (insert σ index newVal) ∗
      exceptionPointsTo ghostName index (DFrac.own 1) newVal := by
  unfold exceptionPointsTo
  iapply ghost_map_update

/-- Persistent knowledge of the entry instance's tag-identity table.  Only the
exception rules need it; every other rule is oblivious to tags. -/
@[reducible] def tagTableOwn {GF : BundledGFunctors}
    [E : ElemG GF (constOF (Agree (DiscreteO (List Nat))))]
    [gn : WasmTagTableGhostName GF] (ids : List Nat) : IProp GF :=
  iOwn (E := E) gn.tagTableName (toAgree ⟨ids⟩)

instance {GF : BundledGFunctors} [ElemG GF (constOF (Agree (DiscreteO (List Nat))))]
    [WasmTagTableGhostName GF] (ids : List Nat) :
    BI.Persistent (tagTableOwn (GF := GF) ids) := by
  unfold tagTableOwn
  infer_instance

instance {GF : BundledGFunctors} [ElemG GF (constOF (Agree (DiscreteO (List Nat))))]
    [WasmTagTableGhostName GF] (ids : List Nat) :
    BI.Timeless (tagTableOwn (GF := GF) ids) := by
  unfold tagTableOwn
  infer_instance

theorem tagTableOwn_agree {GF : BundledGFunctors}
    [ElemG GF (constOF (Agree (DiscreteO (List Nat))))]
    [WasmTagTableGhostName GF] (actual expected : List Nat) :
    tagTableOwn (GF := GF) actual ∗ tagTableOwn expected ⊢
      iprop(⌜actual = expected⌝) := by
  unfold tagTableOwn
  iintro ⟨Hactual, Hexpected⟩
  icombine Hactual Hexpected gives %Hvalid
  ipureexact congrArg DiscreteO.car (toAgree_op_valid_iff_eq.mp Hvalid)

def runtimeModuleElem {GF : BundledGFunctors}
    [GhostMapG GF Nat Module WasmRuntimeModuleMap]
    (ghostName : GName) (id : Nat) (m : Module) : IProp GF :=
  ghost_map_elem ghostName DFrac.discard id m

instance {GF : BundledGFunctors} [GhostMapG GF Nat Module WasmRuntimeModuleMap]
    (ghostName : GName) (id : Nat) (m : Module) :
    BI.Persistent (runtimeModuleElem (GF := GF) ghostName id m) := by
  unfold runtimeModuleElem; infer_instance

instance {GF : BundledGFunctors} [GhostMapG GF Nat Module WasmRuntimeModuleMap]
    (ghostName : GName) (id : Nat) (m : Module) :
    BI.Timeless (runtimeModuleElem (GF := GF) ghostName id m) := by
  unfold runtimeModuleElem; infer_instance

theorem runtimeModuleElem_lookup {GF : BundledGFunctors}
    [GhostMapG GF Nat Module WasmRuntimeModuleMap]
    (ghostName : GName) (σ : WasmRuntimeModuleMap Module) (id : Nat) (m : Module) :
    ghost_map_auth (GF := GF) ghostName (DFrac.own 1) σ -∗
      runtimeModuleElem ghostName id m -∗
      iprop(⌜get? σ id = some m⌝) := by
  unfold runtimeModuleElem
  iapply ghost_map_lookup

/-- Persistent knowledge of the immutable instances array. Agreement with the
copy held by `StateInterp` lets cross-instance call rules verify instance
lookups against the actual machine. -/
def runtimeInstancesOwn {α : Type} {GF : BundledGFunctors}
    [E : ElemG GF (constOF (Agree (DiscreteO (Array (ModuleInstance α)))))]
    [gn : WasmRuntimeInstancesGhostName GF] (instances : Array (ModuleInstance α)) : IProp GF :=
  iOwn (E := E) gn.runtimeInstancesName (toAgree ⟨instances⟩)

instance {α : Type} {GF : BundledGFunctors}
    [ElemG GF (constOF (Agree (DiscreteO (Array (ModuleInstance α)))))]
    [WasmRuntimeInstancesGhostName GF] (instances : Array (ModuleInstance α)) :
    BI.Persistent (runtimeInstancesOwn (GF := GF) instances) := by
  unfold runtimeInstancesOwn
  infer_instance

instance {α : Type} {GF : BundledGFunctors}
    [ElemG GF (constOF (Agree (DiscreteO (Array (ModuleInstance α)))))]
    [WasmRuntimeInstancesGhostName GF] (instances : Array (ModuleInstance α)) :
    BI.Timeless (runtimeInstancesOwn (GF := GF) instances) := by
  unfold runtimeInstancesOwn
  infer_instance

theorem runtimeInstancesOwn_agree {α : Type} {GF : BundledGFunctors}
    [ElemG GF (constOF (Agree (DiscreteO (Array (ModuleInstance α)))))]
    [WasmRuntimeInstancesGhostName GF] (actual expected : Array (ModuleInstance α)) :
    runtimeInstancesOwn (GF := GF) actual ∗ runtimeInstancesOwn expected ⊢
      iprop(⌜actual = expected⌝) := by
  unfold runtimeInstancesOwn
  iintro ⟨Hactual, Hexpected⟩
  icombine Hactual Hexpected gives %Hvalid
  ipureexact congrArg DiscreteO.car (toAgree_op_valid_iff_eq.mp Hvalid)

/-- Persistent knowledge of the host environment for a given instance. -/
@[reducible] def hostEnvOwn {α : Type} {GF : BundledGFunctors}
    [GhostMapG GF Nat (HostEnv α) WasmHostEnvMap]
    [gn : WasmHostEnvGhostName GF] (instanceId : Nat) (env : HostEnv α) : IProp GF :=
  ghost_map_elem gn.hostEnvName DFrac.discard instanceId env

instance {α : Type} {GF : BundledGFunctors} [GhostMapG GF Nat (HostEnv α) WasmHostEnvMap]
    [WasmHostEnvGhostName GF] (instanceId : Nat) (env : HostEnv α) :
    BI.Persistent (hostEnvOwn (GF := GF) instanceId env) := by
  unfold hostEnvOwn; infer_instance

instance {α : Type} {GF : BundledGFunctors} [GhostMapG GF Nat (HostEnv α) WasmHostEnvMap]
    [WasmHostEnvGhostName GF] (instanceId : Nat) (env : HostEnv α) :
    BI.Timeless (hostEnvOwn (GF := GF) instanceId env) := by
  unfold hostEnvOwn; infer_instance

theorem hostEnvOwn_lookup {α : Type} {GF : BundledGFunctors}
    [GhostMapG GF Nat (HostEnv α) WasmHostEnvMap]
    [gn : WasmHostEnvGhostName GF] (σ : WasmHostEnvMap (HostEnv α))
    (instanceId : Nat) (env : HostEnv α) :
    ghost_map_auth (GF := GF) gn.hostEnvName (DFrac.own 1) σ -∗
      hostEnvOwn instanceId env -∗
      iprop(⌜get? σ instanceId = some env⌝) := by
  unfold hostEnvOwn
  iapply ghost_map_lookup

/-- Authoritative ownership of the mutable host state. Held by `StateInterp`. -/
def hostStateAuth {α : Type} {GF : BundledGFunctors}
    [gn : WasmHostStateGhostName GF α] (ghostName : GName) (st : α) : IProp GF :=
  iOwn (E := gn.hostStateElem) ghostName (ExclAuth.auth (⟨st⟩ : DiscreteO α))

/-- Fragment ownership of the mutable host state. Given to WP proofs. -/
def hostStateOwn {α : Type} {GF : BundledGFunctors}
    [gn : WasmHostStateGhostName GF α] (st : α) : IProp GF :=
  iOwn (E := gn.hostStateElem) gn.hostStateName (ExclAuth.frag (⟨st⟩ : DiscreteO α))

theorem hostStateOwn_agree {α : Type} {GF : BundledGFunctors}
    [gn : WasmHostStateGhostName GF α] (actual expected : α) :
    hostStateAuth (GF := GF) gn.hostStateName actual ∗ hostStateOwn expected ⊢
      iprop(⌜actual = expected⌝) := by
  unfold hostStateAuth hostStateOwn
  iintro ⟨Hauth, Hfrag⟩
  icombine Hauth Hfrag gives %Hvalid
  ipureexact congrArg DiscreteO.car (ExclAuth.agree (A := DiscreteO α) Hvalid)

theorem hostStateOwn_update {α : Type} {GF : BundledGFunctors}
    [gn : WasmHostStateGhostName GF α] (old new' : α) :
    hostStateAuth (GF := GF) gn.hostStateName old ∗ hostStateOwn old ==∗
      hostStateAuth gn.hostStateName new' ∗ hostStateOwn new' := by
  unfold hostStateAuth hostStateOwn
  iintro ⟨Hauth, Hfrag⟩
  imod iOwn_update_op (E := gn.hostStateElem)
      (ExclAuth.update (A := DiscreteO α) (a := (⟨old⟩ : DiscreteO α))
        (b := ⟨old⟩) (a' := ⟨new'⟩))
      $$ [Hauth Hfrag] with Hboth
  · iframe
  imodintro
  icases iOwn_op $$ Hboth with ⟨H1, H2⟩; iframe

/-- Authoritative sparse-heap frontier, held inside `stateInterp`. -/
@[reducible] def heapFrontierAuth {GF : BundledGFunctors}
    [gn : WasmHeapFrontierGhostName GF] (frontier : Nat) : IProp GF :=
  iOwn (E := gn.heapFrontierElem) gn.heapFrontierName (ExclAuth.auth (⟨frontier⟩ : DiscreteO Nat))

/-- Exclusive allocator-client fragment agreeing with the sparse-heap
frontier protected by `stateInterp`. -/
@[reducible] def heapFrontierOwn {GF : BundledGFunctors}
    [gn : WasmHeapFrontierGhostName GF] (frontier : Nat) : IProp GF :=
  iOwn (E := gn.heapFrontierElem) gn.heapFrontierName (ExclAuth.frag (⟨frontier⟩ : DiscreteO Nat))

theorem heapFrontierOwn_agree {GF : BundledGFunctors}
    [gn : WasmHeapFrontierGhostName GF] (actual expected : Nat) :
    heapFrontierAuth (GF := GF) actual ∗ heapFrontierOwn expected ⊢
      iprop(⌜actual = expected⌝) := by
  unfold heapFrontierAuth heapFrontierOwn
  iintro ⟨Hauth, Hfrag⟩
  icombine Hauth Hfrag gives %Hvalid
  ipureexact congrArg DiscreteO.car
    (ExclAuth.agree (A := DiscreteO Nat) Hvalid)

theorem heapFrontierOwn_update {GF : BundledGFunctors}
    [gn : WasmHeapFrontierGhostName GF] (old new' : Nat) :
    heapFrontierAuth (GF := GF) old ∗ heapFrontierOwn old ==∗
      heapFrontierAuth new' ∗ heapFrontierOwn new' := by
  unfold heapFrontierAuth heapFrontierOwn
  iintro ⟨Hauth, Hfrag⟩
  imod iOwn_update_op (E := gn.heapFrontierElem)
      (ExclAuth.update (A := DiscreteO Nat)
        (a := (⟨old⟩ : DiscreteO Nat)) (b := ⟨old⟩) (a' := ⟨new'⟩))
      $$ [Hauth Hfrag] with Hboth
  · iframe
  imodintro
  icases iOwn_op $$ Hboth with ⟨H1, H2⟩; iframe

/-- Exact authoritative primary-memory page count, held inside `stateInterp`. -/
@[reducible] def memoryPagesAuth {GF : BundledGFunctors} [E : ElemG GF MonoNatRF]
    (ghostName : GName) (pages : Nat) : IProp GF :=
  iOwn (E := E) ghostName (MonoNat.auth (DFrac.own 1) (MaxNat.ofNat pages))

/-- Persistent knowledge that the primary memory has at least `pages` pages. -/
@[reducible] def memoryPagesOwn {GF : BundledGFunctors} [E : ElemG GF MonoNatRF]
    [gn : WasmMemoryPagesGhostName GF] (pages : Nat) : IProp GF :=
  iOwn (E := E) gn.memoryPagesName (MonoNat.lb (MaxNat.ofNat pages))

instance {GF : BundledGFunctors} [ElemG GF MonoNatRF] (ghostName : GName) (pages : Nat) :
    BI.Timeless (memoryPagesAuth (GF := GF) ghostName pages) := by
  unfold memoryPagesAuth
  infer_instance

instance {GF : BundledGFunctors} [ElemG GF MonoNatRF]
    [WasmMemoryPagesGhostName GF] (pages : Nat) :
    BI.Timeless (memoryPagesOwn (GF := GF) pages) := by
  unfold memoryPagesOwn
  infer_instance

instance {GF : BundledGFunctors} [ElemG GF MonoNatRF]
    [WasmMemoryPagesGhostName GF] (pages : Nat) :
    BI.Persistent (memoryPagesOwn (GF := GF) pages) := by
  unfold memoryPagesOwn
  infer_instance

/-- A page snapshot is a lower bound on the exact authoritative count. -/
theorem memoryPagesOwn_agree {GF : BundledGFunctors} [ElemG GF MonoNatRF]
    [gn : WasmMemoryPagesGhostName GF] (actual expected : Nat) :
    memoryPagesAuth (GF := GF) gn.memoryPagesName actual ∗ memoryPagesOwn expected ⊢
      iprop(⌜expected ≤ actual⌝) := by
  unfold memoryPagesAuth memoryPagesOwn
  iintro ⟨Hauth, Hsnapshot⟩
  icombine Hauth Hsnapshot gives %Hvalid
  ipureexact (MonoNat.both_valid
    (MaxNat.ofNat actual) (MaxNat.ofNat expected)).mp Hvalid

/-- Obtain an exact persistent snapshot from the page-count authority. -/
theorem memoryPagesOwn_snapshot {GF : BundledGFunctors} [ElemG GF MonoNatRF]
    [gn : WasmMemoryPagesGhostName GF] (pages : Nat) :
    memoryPagesAuth (GF := GF) gn.memoryPagesName pages ⊢ memoryPagesOwn pages := by
  unfold memoryPagesAuth memoryPagesOwn
  iintro Hauth
  iapply iOwn_mono $$ Hauth
  exact MonoNat.included _ _

/-- Advance the exact page-count authority and issue an exact new snapshot. -/
theorem memoryPagesAuth_update {GF : BundledGFunctors} [E : ElemG GF MonoNatRF]
    (ghostName : GName) (old new' : Nat) (hmono : old ≤ new') :
    memoryPagesAuth (GF := GF) ghostName old ==∗
      memoryPagesAuth ghostName new' ∗
        @memoryPagesOwn GF E ⟨ghostName⟩ new' := by
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
        memoryPagesAuth (GF := WasmHeapGF α) (E := gs.memoryPagesElem)
          (@WasmMemoryPagesGhostName.memoryPagesName (WasmHeapGF α) ⟨gs.memoryPagesName⟩)
          pages := by
  letI memoryPagesElem : ElemG (WasmHeapGF α) MonoNatRF := by
    exists 20
  imod (iOwn_alloc (E := memoryPagesElem)
      (MonoNat.auth (DFrac.own 1) (MaxNat.ofNat pages))
      (MonoNat.auth_valid (MaxNat.ofNat pages))) with
    ⟨%memoryPagesName, Hauth⟩
  let gs : WasmMemoryPagesGS α :=
    { memoryPagesElem
      memoryPagesName }
  letI : WasmMemoryPagesGS α := gs
  imodintro
  iexists gs
  unfold memoryPagesAuth
  iexact Hauth

/-- Allocate page-count authority together with an exact persistent snapshot.
Allocator-aware adequacy frontends expose the snapshot to their client proof. -/
theorem memoryPages_init {α : Type} (pages : Nat) :
    ⊢@{IProp (WasmHeapGF α)} |==>
      ∃ gs : WasmMemoryPagesGS α,
        memoryPagesAuth (GF := WasmHeapGF α) (E := gs.memoryPagesElem)
          (@WasmMemoryPagesGhostName.memoryPagesName (WasmHeapGF α) ⟨gs.memoryPagesName⟩)
          pages ∗
          @memoryPagesOwn (WasmHeapGF α) gs.memoryPagesElem ⟨gs.memoryPagesName⟩
            pages := by
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
  letI : WasmMemoryPagesGS α := gs
  imodintro
  iexists gs
  unfold memoryPagesAuth memoryPagesOwn
  iframe Hauth Hsnapshot

def currentInstanceAuthN {GF : BundledGFunctors}
    [E : ElemG GF (Auth.AuthRF (OptionOF (Excl.ExclOF (constOF (DiscreteO Nat)))))]
    (ghostName : GName) (n : Nat) : IProp GF :=
  iOwn (E := E) ghostName (ExclAuth.auth (⟨n⟩ : DiscreteO Nat))

def currentInstanceOwnN {GF : BundledGFunctors}
    [E : ElemG GF (Auth.AuthRF (OptionOF (Excl.ExclOF (constOF (DiscreteO Nat)))))]
    (ghostName : GName) (n : Nat) : IProp GF :=
  iOwn (E := E) ghostName (ExclAuth.frag (⟨n⟩ : DiscreteO Nat))

instance {GF : BundledGFunctors}
    [ElemG GF (Auth.AuthRF (OptionOF (Excl.ExclOF (constOF (DiscreteO Nat)))))]
    (ghostName : GName) (n : Nat) :
    BI.Timeless (currentInstanceAuthN (GF := GF) ghostName n) := by
  unfold currentInstanceAuthN; infer_instance

instance {GF : BundledGFunctors}
    [ElemG GF (Auth.AuthRF (OptionOF (Excl.ExclOF (constOF (DiscreteO Nat)))))]
    (ghostName : GName) (n : Nat) :
    BI.Timeless (currentInstanceOwnN (GF := GF) ghostName n) := by
  unfold currentInstanceOwnN; infer_instance

section
open Wasm.SmallStep

/-- Module instance ownership: persistent module knowledge paired with exclusive
current-instance token. The exclusive part lets call rules verify that the
caller's instance id agrees with the machine's current instance. -/
@[reducible] def runtimeModuleOwn {GF : BundledGFunctors}
    [gn : WasmRuntimeModuleGhostNames GF]
    [GhostMapG GF Nat Module WasmRuntimeModuleMap]
    (instanceId : ModuleInstanceId) (m : Module) : IProp GF :=
  iprop(runtimeModuleElem gn.runtimeName instanceId.id m ∗
    currentInstanceOwnN gn.instanceName instanceId.id)

instance {GF : BundledGFunctors}
    [WasmRuntimeModuleGhostNames GF]
    [GhostMapG GF Nat Module WasmRuntimeModuleMap]
    (instanceId : ModuleInstanceId) (m : Module) :
    BI.Timeless (runtimeModuleOwn (GF := GF) instanceId m) := by
  infer_instance

theorem runtimeModuleOwn_lookup {GF : BundledGFunctors}
    [gn : WasmRuntimeModuleGhostNames GF]
    [GhostMapG GF Nat Module WasmRuntimeModuleMap]
    (σ : WasmRuntimeModuleMap Module) (instanceId : ModuleInstanceId) (m : Module) :
    ghost_map_auth (GF := GF) gn.runtimeName (DFrac.own 1) σ -∗
      runtimeModuleOwn instanceId m -∗
      ⌜get? σ instanceId.id = some m⌝ := by
  simp only [runtimeModuleOwn]
  iintro Hauth ⟨Helem, _⟩
  iapply runtimeModuleElem_lookup $$ Hauth Helem

end

theorem currentInstanceOwnN_agree {GF : BundledGFunctors}
    [ElemG GF (Auth.AuthRF (OptionOF (Excl.ExclOF (constOF (DiscreteO Nat)))))]
    (ghostName : GName) (actual expected : Nat) :
    currentInstanceAuthN (GF := GF) ghostName actual ∗ currentInstanceOwnN ghostName expected ⊢
      iprop(⌜actual = expected⌝) := by
  unfold currentInstanceAuthN currentInstanceOwnN
  iintro ⟨Hauth, Hfrag⟩
  icombine Hauth Hfrag gives %Hvalid
  ipureexact congrArg DiscreteO.car (ExclAuth.agree (A := DiscreteO Nat) Hvalid)

theorem currentInstanceOwnN_update {GF : BundledGFunctors}
    [E : ElemG GF (Auth.AuthRF (OptionOF (Excl.ExclOF (constOF (DiscreteO Nat)))))]
    (ghostName : GName) (old new' : Nat) :
    currentInstanceAuthN (GF := GF) ghostName old ∗ currentInstanceOwnN ghostName old ==∗
      currentInstanceAuthN ghostName new' ∗ currentInstanceOwnN ghostName new' := by
  unfold currentInstanceAuthN currentInstanceOwnN
  iintro ⟨Hauth, Hfrag⟩
  imod iOwn_update_op (E := E)
      (ExclAuth.update (A := DiscreteO Nat) (a := (⟨old⟩ : DiscreteO Nat))
        (b := ⟨old⟩) (a' := ⟨new'⟩))
      $$ [Hauth Hfrag] with Hboth
  · iframe
  imodintro
  icases iOwn_op $$ Hboth with ⟨H1, H2⟩; iframe

theorem currentInstanceOwnN_update_of_any {GF : BundledGFunctors}
    [E : ElemG GF (Auth.AuthRF (OptionOF (Excl.ExclOF (constOF (DiscreteO Nat)))))]
    (ghostName : GName) (actual expected new' : Nat) :
    currentInstanceAuthN (GF := GF) ghostName actual ∗ currentInstanceOwnN ghostName expected ==∗
      currentInstanceAuthN ghostName new' ∗ currentInstanceOwnN ghostName new' ∗
        ⌜actual = expected⌝ := by
  unfold currentInstanceAuthN currentInstanceOwnN
  iintro ⟨Hauth, Hfrag⟩
  ihave %heq : ⌜actual = expected⌝ $$ [Hauth Hfrag]
  · icombine Hauth Hfrag gives %Hvalid
    ipureexact congrArg DiscreteO.car (ExclAuth.agree (A := DiscreteO Nat) Hvalid)
  imod iOwn_update_op (E := E)
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
variable {GF : BundledGFunctors} [inst : genHeapGS MemoryKey (Option UInt8) GF WasmHeapMap]
-- Notation for Wasm points-to (scoped: available inside this namespace
-- and via `open Wasm.SepLogic`, without leaking through the CodeLib umbrella)
scoped notation:50 addr:50 " ↦w " v:50 => pointsTo (L := MemoryKey) (V := Option UInt8)
    (H := WasmHeapMap) addr (DFrac.own 1) (some v)

def memPointsTo (memId : Nat) (addr : UInt32) (dfrac : DFrac)
    (value : Option UInt8) : IProp GF :=
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
  exact Nat.reassemble64_of_lt v.toNat (UInt64.toNat_lt v)

-- Multi-byte: u64 as 8 consecutive owned bytes (little-endian)
def pointsTo_u64 (memId : Nat) (addr : UInt32) (v : UInt64) : IProp GF :=
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
  exact Nat.reassemble32_of_lt v.toNat (UInt32.toNat_lt v)

-- Multi-byte: u32 as 4 consecutive owned bytes (little-endian)
def pointsTo_u32 (memId : Nat) (addr : UInt32) (v : UInt32) : IProp GF :=
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
def pointsTo_u16 (memId : Nat) (addr : UInt32) (v : UInt32) : IProp GF :=
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
  apply UInt32.toNat.inj
  simp only [UInt32.toNat_or, UInt32.toNat_shiftLeft, UInt8.toNat_toUInt32,
    UInt32.toNat_toUInt8, UInt32.toNat_shiftRight, UInt32.toNat_and]
  change v.toNat % 2^8 ||| (((v.toNat >>> 8) % 2^8) <<< 8) % 2^32 =
    v.toNat &&& (2^16 - 1)
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_or, Nat.testBit_and, Nat.testBit_mod_two_pow,
    Nat.testBit_shiftLeft, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]
  by_cases h8 : i < 8
  · simp [h8, show i < 16 by omega, show ¬ i ≥ 8 by omega]
  by_cases h16 : i < 16
  · simp [h8, h16, show i < 32 by omega, show i ≥ 8 by omega,
      show i - 8 < 8 by omega, show 8 + (i - 8) = i by omega]
  · simp [h8, h16, show ¬ i - 8 < 8 by omega]

-- Byte-range ownership: n consecutive bytes at `addr` in memory `memId`.
def pointsToBytes (memId : Nat) (addr : UInt32) (bytes : List UInt8) :
    IProp GF :=
  match bytes with
  | [] => iprop% emp
  | b :: rest => iprop% (⟨memId, addr⟩ ↦w b) ∗ (pointsToBytes memId (addr + 1) rest)

instance instTimelessPointsToBytes (memId : Nat) (addr : UInt32)
    (bytes : List UInt8) :
    BI.Timeless (pointsToBytes (GF := GF) memId addr bytes) := by
  induction bytes generalizing addr with
  | nil =>
      simp only [pointsToBytes]
      infer_instance
  | cons b rest ih =>
      simp only [pointsToBytes]
      letI := ih (addr + 1)
      infer_instance

theorem pointsToBytes_nil (memId : Nat) (addr : UInt32) :
    pointsToBytes (GF := GF) memId addr [] ⊣⊢ emp := .rfl

theorem pointsToBytes_cons (memId : Nat) (addr : UInt32) (b : UInt8)
    (rest : List UInt8) :
    pointsToBytes (GF := GF) memId addr (b :: rest) ⊣⊢
      (⟨memId, addr⟩ ↦w b) ∗ pointsToBytes memId (addr + 1) rest := .rfl

omit inst in
theorem byte_offset_succ (addr : UInt32) (k : Nat) :
    addr + UInt32.ofNat (k + 1) = (addr + 1) + UInt32.ofNat k := by
  symm
  rw [UInt32.ofNat_add, show UInt32.ofNat 1 = 1 from rfl]
  rw [UInt32.add_assoc addr 1, UInt32.add_comm 1]

theorem pointsToBytes_append (memId : Nat) (addr : UInt32) (xs ys : List UInt8) :
    pointsToBytes (GF := GF) memId addr (xs ++ ys) ⊣⊢
    pointsToBytes memId addr xs ∗
      pointsToBytes memId (addr + UInt32.ofNat xs.length) ys := by
  induction xs generalizing addr with
  | nil => simp [pointsToBytes]; exact BI.emp_sep.symm
  | cons x rest ih =>
    simp only [List.cons_append, List.length_cons, pointsToBytes]
    rw [byte_offset_succ]; exact (BI.sep_congr_right (ih (addr + 1))).trans BI.sep_assoc.symm

/-- Owning a 32-bit word is the same as owning its four little-endian bytes. -/
theorem pointsTo_u32_as_bytes (memId : Nat) (addr v : UInt32) :
    pointsTo_u32 (GF := GF) memId addr v ⊣⊢
      pointsToBytes memId addr
        [u32Byte v 0, u32Byte v 1, u32Byte v 2, u32Byte v 3] := by
  have e11 : (1 + 1 : UInt32) = 2 := by decide
  have e21 : (2 + 1 : UInt32) = 3 := by decide
  have e2 : addr + 1 + 1 = addr + 2 := by rw [UInt32.add_assoc, e11]
  have e3 : addr + 2 + 1 = addr + 3 := by rw [UInt32.add_assoc, e21]
  simp only [pointsTo_u32, pointsToBytes, e2, e3,
    (BI.sep_emp (PROP := IProp GF)).to_eq]
  exact .rfl

-- Array ownership: n consecutive u32 elements at ptr
-- arrayAt memId ptr [x₀, x₁, ..., xₙ₋₁] =
--   pointsTo_u32 memId ptr x₀ ∗ pointsTo_u32 memId (ptr+4) x₁ ∗ ...
def arrayAt (memId : Nat) (ptr : UInt32) (xs : List UInt32) : IProp GF :=
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
    rw [elem_offset_succ]; exact (BI.sep_congr_right (ih (ptr + 4))).trans BI.sep_assoc.symm

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
      rw [elem_offset_succ]; exact (BI.sep_mono_right (ih (ptr + 4) k' hk')).trans
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
def array64At (memId : Nat) (ptr : UInt32) (xs : List UInt64) : IProp GF :=
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
    rw [elem64_offset_succ]; exact (BI.sep_congr_right (ih (ptr + 8))).trans BI.sep_assoc.symm

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
      rw [elem64_offset_succ]; exact (BI.sep_mono_right (ih (ptr + 8) k' hk')).trans
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
