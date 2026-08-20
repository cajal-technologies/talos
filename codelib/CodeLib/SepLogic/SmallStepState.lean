import CodeLib.SepLogic.SmallStepLanguage
import CodeLib.SepLogic.WasmRules
import Iris.ProgramLogic.WeakestPre

/-!
# Iris state interpretation for the Wasm small-step machine

The authoritative GenHeap map is existentially hidden by the state
interpretation and is required to agree with the physical bytes in
`MachineStore`. Unlike the legacy `wp_wasm` setup, the ghost heap is therefore
not a free-floating resource: any owned byte must describe the corresponding
physical memory byte.
-/

namespace Wasm.SmallStep

open Iris Iris.ProgramLogic Std
open Wasm.SepLogic

/-- Authoritative ownership of the current module instance id.
Wraps `currentInstanceAuthN` to take `ModuleInstanceId` directly. -/
def currentInstanceAuth {α : Type} [gs : WasmInstanceGS α]
    (id : ModuleInstanceId) : IProp (WasmHeapGF α) :=
  currentInstanceAuthN id.id

/-- Fragment ownership of the current module instance id.
Wraps `currentInstanceOwnN` to take `ModuleInstanceId` directly. -/
@[reducible] def currentInstanceOwn {α : Type} [gs : WasmInstanceGS α]
    (id : ModuleInstanceId) : IProp (WasmHeapGF α) :=
  currentInstanceOwnN id.id

instance {α : Type} [WasmInstanceGS α] (id : ModuleInstanceId) :
    BI.Timeless (currentInstanceAuth (α := α) id) := by
  unfold currentInstanceAuth; infer_instance

instance {α : Type} [WasmInstanceGS α] (id : ModuleInstanceId) :
    BI.Timeless (currentInstanceOwn (α := α) id) := by
  unfold currentInstanceOwn; infer_instance

theorem currentInstanceOwn_agree {α : Type} [gs : WasmInstanceGS α]
    (actual expected : ModuleInstanceId) :
    currentInstanceAuth (α := α) actual ∗ currentInstanceOwn expected ⊢
      iprop(⌜actual = expected⌝) := by
  unfold currentInstanceAuth currentInstanceOwn currentInstanceAuthN currentInstanceOwnN
  iintro ⟨Hauth, Hfrag⟩
  icombine Hauth Hfrag gives %Hvalid
  ipureintro
  have : actual.id = expected.id :=
    congrArg DiscreteO.car (ExclAuth.agree (A := DiscreteO Nat) Hvalid)
  cases actual; cases expected; cases this; rfl

theorem currentInstanceOwn_update {α : Type} [gs : WasmInstanceGS α]
    (old new' : ModuleInstanceId) :
    currentInstanceAuth (α := α) old ∗ currentInstanceOwn old ==∗
      currentInstanceAuth new' ∗ currentInstanceOwn new' := by
  unfold currentInstanceAuth currentInstanceOwn
  iapply currentInstanceOwnN_update

theorem currentInstanceOwn_update_of_any {α : Type} [gs : WasmInstanceGS α]
    (actual calleeId newId : ModuleInstanceId) :
    currentInstanceAuth (α := α) actual ∗ currentInstanceOwn calleeId ==∗
      currentInstanceAuth newId ∗ currentInstanceOwn newId ∗ ⌜actual = calleeId⌝ := by
  unfold currentInstanceAuth currentInstanceOwn currentInstanceAuthN currentInstanceOwnN
  iintro ⟨Hauth, Hfrag⟩
  ihave %heq_id : ⌜actual.id = calleeId.id⌝ $$ [Hauth Hfrag]
  · icombine Hauth Hfrag gives %Hvalid
    ipureintro
    exact congrArg DiscreteO.car (ExclAuth.agree (A := DiscreteO Nat) Hvalid)
  imod iOwn_update_op (E := gs.instanceElem)
      (ExclAuth.update (A := DiscreteO Nat)
        (a := (⟨actual.id⟩ : DiscreteO Nat))
        (b := ⟨calleeId.id⟩)
        (a' := ⟨newId.id⟩))
      $$ [Hauth Hfrag] with Hboth
  · iframe
  imodintro
  icases iOwn_op $$ Hboth with ⟨H1, H2⟩
  isplitl [H1]
  · iexact H1
  isplitl [H2]
  · iexact H2
  · ipureintro
    cases actual; cases calleeId; cases heq_id; rfl

class WasmSmallStepGS (hlc : outParam HasLC) (α : outParam Type) extends
    InvGS_gen hlc (WasmHeapGF α), WasmHeapGS α where
  global : WasmGlobalGS α
  dataSegment : WasmDataSegmentGS α
  table : WasmTableGS α
  elementSegment : WasmElementSegmentGS α
  exception : WasmExceptionGS α
  runtime : WasmRuntimeModuleGS α
<<<<<<< HEAD
  tagTable : WasmTagTableGS α
  host : WasmHostGS α
=======
  hostEnv : WasmHostEnvGS α
  hostState : WasmHostStateGS α
  instanceGS : WasmInstanceGS α
  runtimeInstances : WasmRuntimeInstancesGS α
>>>>>>> origin/main

attribute [instance] WasmSmallStepGS.toInvGS_gen
attribute [instance] WasmSmallStepGS.toWasmHeapGS
attribute [reducible, instance] WasmSmallStepGS.global
attribute [reducible, instance] WasmSmallStepGS.dataSegment
attribute [reducible, instance] WasmSmallStepGS.table
attribute [reducible, instance] WasmSmallStepGS.elementSegment
attribute [reducible, instance] WasmSmallStepGS.exception
attribute [reducible, instance] WasmSmallStepGS.runtime
<<<<<<< HEAD
attribute [reducible, instance] WasmSmallStepGS.tagTable
attribute [reducible, instance] WasmSmallStepGS.host
=======
attribute [reducible, instance] WasmSmallStepGS.hostEnv
attribute [reducible, instance] WasmSmallStepGS.hostState
attribute [reducible, instance] WasmSmallStepGS.instanceGS
attribute [reducible, instance] WasmSmallStepGS.runtimeInstances

variable {α : Type}

/-- Resolver that maps memory id 0 to the primary memory and ids ≥ 1 to
extra memories. Used to bridge single-Mem stateInterp facts to the
multi-memory heapAgreesWithMem API. -/
def storeResolve (store : MachineStore α) : Nat → Option Mem :=
  fun i => if i = 0 then some store.wasm.mem else store.wasm.extraMems[i - 1]?


private theorem storeResolve_zero (store : MachineStore α) :
    storeResolve store 0 = some store.wasm.mem := by simp [storeResolve]


private theorem storeResolve_update_mem0 (store : MachineStore α) (newMem : Mem) :
    (fun id => if id = 0 then some newMem else storeResolve store id) =
    storeResolve { store with wasm := { store.wasm with mem := newMem } } := by
  funext id; simp only [storeResolve]; by_cases h : id = 0 <;> simp [h]


private theorem fromResolver (store : MachineStore α) {σ : WasmHeapMap (Option UInt8)}
    (hag : heapAgreesWithMem σ (storeResolve store))
    (addr : UInt32) (v : UInt8)
    (hl : get? σ ⟨0, addr⟩ = some (some v)) :
    store.wasm.mem.read8 addr = v := by
  obtain ⟨m, hm, hr⟩ := hag ⟨0, addr⟩ v hl
  exact (Option.some.inj ((storeResolve_zero store).symm.trans hm)) ▸ hr


private theorem fromResolverBounds (store : MachineStore α) {σ : WasmHeapMap (Option UInt8)}
    (hbn : heapAddressesInBounds σ (storeResolve store))
    (addr : UInt32) (hne : get? σ ⟨0, addr⟩ ≠ none) :
    addr.toNat < store.wasm.mem.pages * 65536 := by
  obtain ⟨m, hm, hlt⟩ := hbn ⟨0, addr⟩ hne
  exact (Option.some.inj ((storeResolve_zero store).symm.trans hm)) ▸ hlt
>>>>>>> origin/main

/-- The runtime-identity component of the state interpretation.

It pins the immutable instantiated module and, separately, records ghost
knowledge about the tag-identity table.  The tag component only claims that
the agreed list is a *prefix* of `store.wasm.tagIds`; nothing here constrains
the physical store, so linked stores whose tag table carries entries from
additional registered modules satisfy it unchanged. -/
def runtimeInterp [WasmRuntimeModuleGS α] [WasmTagTableGS α]
    (m : Module) (tagIds : List Nat) : IProp (WasmHeapGF α) := iprop%
  runtimeModuleOwn m ∗
    ∃ ids : List Nat, tagTableOwn ids ∗ ⌜ids.IsPrefix tagIds⌝

theorem runtimeInterp_module [WasmRuntimeModuleGS α] [WasmTagTableGS α]
    (m : Module) (tagIds : List Nat) :
    runtimeInterp m tagIds ⊢ runtimeModuleOwn m := by
  unfold runtimeInterp
  iintro ⟨Hmodule, Htags⟩
  iclear Htags
  iexact Hmodule

theorem runtimeInterp_tagPrefix [WasmRuntimeModuleGS α] [WasmTagTableGS α]
    (m : Module) (tagIds ids : List Nat) :
    runtimeInterp m tagIds ∗ tagTableOwn ids ⊢
      iprop(⌜ids.IsPrefix tagIds⌝) := by
  unfold runtimeInterp
  iintro ⟨⟨Hmodule, %ids', Hactual, %Hprefix⟩, Howned⟩
  iclear Hmodule
  ihave %heq := tagTableOwn_agree ids' ids $$ [$Hactual $Howned]
  ipureintro
  exact heq ▸ Hprefix

/-- A tag index is canonical for `ids` when it is the first position holding
its identity; this is what the interpreter's tag canonicalisation collapses
to, and it is decidable for a concrete tag table. -/
def TagIndexCanonical (ids : List Nat) (index : Nat) : Prop :=
  ∃ id, ids[index]? = some id ∧ ids.findIdx? (· = id) = some index

instance instStateInterp [WasmSmallStepGS hlc α] :
    StateInterp (MachineStore α) StepKind (WasmHeapGF α) where
  stateInterp store _ _ _ := iprop%
    ∃ σ : WasmHeapMap (Option UInt8),
      ∃ globalσ : WasmGlobalMap Value,
      ∃ dataSegmentσ : WasmDataSegmentMap (Option (List UInt8)),
      ∃ tableσ : WasmTableMap TableInst,
      ∃ elementSegmentσ :
        WasmElementSegmentMap (Option (List (Option Nat))),
<<<<<<< HEAD
      ∃ exceptionσ : WasmExceptionMap (Nat × List Value),
=======
      ∃ runtimeModuleσ : WasmRuntimeModuleMap Module,
      ∃ hostEnvσ : WasmHostEnvMap (HostEnv α),
>>>>>>> origin/main
      genHeapInterp σ ∗
        ghost_map_auth WasmSmallStepGS.global.globalName
          (DFrac.own 1) globalσ ∗
        ghost_map_auth WasmSmallStepGS.dataSegment.dataSegmentName
          (DFrac.own 1) dataSegmentσ ∗
        ghost_map_auth WasmSmallStepGS.table.tableName
          (DFrac.own 1) tableσ ∗
        ghost_map_auth
          WasmSmallStepGS.elementSegment.elementSegmentName
          (DFrac.own 1) elementSegmentσ ∗
<<<<<<< HEAD
        ghost_map_auth WasmSmallStepGS.exception.exceptionName
          (DFrac.own 1) exceptionσ ∗
        runtimeInterp store.runtime.module store.wasm.tagIds ∗
=======
        ghost_map_auth WasmSmallStepGS.runtime.runtimeName
          (DFrac.own 1) runtimeModuleσ ∗
        ([∗map] id ↦ m ∈ runtimeModuleσ, runtimeModuleElem id m) ∗
        runtimeInstancesOwn store.runtime.instances ∗
        currentInstanceAuth store.runtime.entry ∗
        ghost_map_auth WasmSmallStepGS.hostEnv.hostEnvName
          (DFrac.own 1) hostEnvσ ∗
>>>>>>> origin/main
        hostStateAuth store.wasm.host ∗
      ⌜heapAgreesWithMem σ (storeResolve store) ∧
        heapAddressesInBounds σ (storeResolve store) ∧
        globalHeapAgrees globalσ store.wasm.globals ∧
        dataSegmentHeapAgrees dataSegmentσ store.wasm.dataSegments ∧
        tableHeapAgrees tableσ store.wasm.tables ∧
        elementSegmentHeapAgrees elementSegmentσ
          store.wasm.elementSegments ∧
<<<<<<< HEAD
        exceptionHeapAgrees exceptionσ store.wasm.exns⌝
=======
        (∀ id m, get? runtimeModuleσ id = some m →
          store.runtime.instances[id]?.map (·.module) = some m) ∧
        ∀ id env, get? hostEnvσ id = some env →
          store.runtime.instances[id]?.map (·.host) = some env⌝
>>>>>>> origin/main

theorem stateInterp_eq [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ⊣⊢
      (iprop% ∃ σ : WasmHeapMap (Option UInt8),
        ∃ globalσ : WasmGlobalMap Value,
        ∃ dataSegmentσ : WasmDataSegmentMap (Option (List UInt8)),
        ∃ tableσ : WasmTableMap TableInst,
        ∃ elementSegmentσ :
          WasmElementSegmentMap (Option (List (Option Nat))),
<<<<<<< HEAD
        ∃ exceptionσ : WasmExceptionMap (Nat × List Value),
=======
        ∃ runtimeModuleσ : WasmRuntimeModuleMap Module,
        ∃ hostEnvσ : WasmHostEnvMap (HostEnv α),
>>>>>>> origin/main
        genHeapInterp σ ∗
          ghost_map_auth WasmSmallStepGS.global.globalName
            (DFrac.own 1) globalσ ∗
          ghost_map_auth WasmSmallStepGS.dataSegment.dataSegmentName
            (DFrac.own 1) dataSegmentσ ∗
          ghost_map_auth WasmSmallStepGS.table.tableName
            (DFrac.own 1) tableσ ∗
          ghost_map_auth
            WasmSmallStepGS.elementSegment.elementSegmentName
            (DFrac.own 1) elementSegmentσ ∗
<<<<<<< HEAD
          ghost_map_auth WasmSmallStepGS.exception.exceptionName
            (DFrac.own 1) exceptionσ ∗
          runtimeInterp store.runtime.module store.wasm.tagIds ∗
=======
          ghost_map_auth WasmSmallStepGS.runtime.runtimeName
            (DFrac.own 1) runtimeModuleσ ∗
          ([∗map] id ↦ m ∈ runtimeModuleσ, runtimeModuleElem id m) ∗
          runtimeInstancesOwn store.runtime.instances ∗
          currentInstanceAuth store.runtime.entry ∗
          ghost_map_auth WasmSmallStepGS.hostEnv.hostEnvName
            (DFrac.own 1) hostEnvσ ∗
>>>>>>> origin/main
          hostStateAuth store.wasm.host ∗
        ⌜heapAgreesWithMem σ (storeResolve store) ∧
          heapAddressesInBounds σ (storeResolve store) ∧
          globalHeapAgrees globalσ store.wasm.globals ∧
          dataSegmentHeapAgrees dataSegmentσ store.wasm.dataSegments ∧
          tableHeapAgrees tableσ store.wasm.tables ∧
          elementSegmentHeapAgrees elementSegmentσ
            store.wasm.elementSegments ∧
<<<<<<< HEAD
          exceptionHeapAgrees exceptionσ store.wasm.exns⌝) :=
=======
          (∀ id m, get? runtimeModuleσ id = some m →
            store.runtime.instances[id]?.map (·.module) = some m) ∧
          ∀ id env, get? hostEnvσ id = some env →
            store.runtime.instances[id]?.map (·.host) = some env⌝) :=
>>>>>>> origin/main
  .rfl

theorem stateInterp_pointsTo_read8 [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (address : UInt32) (value : UInt8) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        ⟨0, address⟩ (DFrac.own 1) (some value) ==∗
      ⌜store.wasm.mem.read8 address = value⌝ := by
  iintro ⟨Hstate, Hpointsto⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
<<<<<<< HEAD
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %exceptionσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hexceptions, Hruntime, Hhost, %Hfacts⟩
=======
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %runtimeModuleσ, %hostEnvσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, HruntimeModuleAuth, HruntimeModuleBigSep, HruntimeInstances, HinstanceAuth, HhostEnvAuth, Hstate_auth, %Hfacts⟩
>>>>>>> origin/main
  icases genHeap_valid $$ [$Hheap $Hpointsto] with >%hlookup
  ipureintro
  exact fromResolver store Hfacts.1 address value hlookup

theorem stateInterp_pointsTo_inBounds [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (address : UInt32) (value : UInt8) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        ⟨0, address⟩ (DFrac.own 1) (some value) ==∗
      ⌜address.toNat < store.wasm.mem.pages * 65536⌝ := by
  iintro ⟨Hstate, Hpointsto⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
<<<<<<< HEAD
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %exceptionσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hexceptions, Hruntime, Hhost, %Hfacts⟩
=======
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %runtimeModuleσ, %hostEnvσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, HruntimeModuleAuth, HruntimeModuleBigSep, HruntimeInstances, HinstanceAuth, HhostEnvAuth, Hstate_auth, %Hfacts⟩
>>>>>>> origin/main
  icases genHeap_valid $$ [$Hheap $Hpointsto] with >%hlookup
  ipureintro
  exact fromResolverBounds store Hfacts.2.1 address (by simp [hlookup])

theorem stateInterp_pointsTo_facts [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (address : UInt32) (value : UInt8) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        ⟨0, address⟩ (DFrac.own 1) (some value) ==∗
      ⌜store.wasm.mem.read8 address = value ∧
        address.toNat < store.wasm.mem.pages * 65536⌝ := by
  iintro ⟨Hstate, Hpointsto⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
<<<<<<< HEAD
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %exceptionσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hexceptions, Hruntime, Hhost, %Hfacts⟩
=======
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %runtimeModuleσ, %hostEnvσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, HruntimeModuleAuth, HruntimeModuleBigSep, HruntimeInstances, HinstanceAuth, HhostEnvAuth, Hstate_auth, %Hfacts⟩
>>>>>>> origin/main
  icases genHeap_valid $$ [$Hheap $Hpointsto] with >%hlookup
  ipureintro
  exact ⟨fromResolver store Hfacts.1 address value hlookup,
    fromResolverBounds store Hfacts.2.1 address (by simp [hlookup])⟩

/-- Changing `Store.host` requires exchanging `hostStateOwn` because
`stateInterp` holds the authoritative `hostStateAuth`. The caller supplies
the old fragment and receives the new one. -/
theorem stateInterp_host_set [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat) (host : α) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      hostStateOwn store.wasm.host ==∗
      stateInterp (GF := WasmHeapGF α)
        { store with wasm := { store.wasm with host } }
<<<<<<< HEAD
        steps observations threads ∗ hostStateOwn host := by
  iintro ⟨Hstate, Hown⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %exceptionσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hexceptions, Hruntime, Hhost, %Hfacts⟩
  imod hostState_update store.wasm.host host $$ [$Hhost $Hown] with
    ⟨Hhost, Hown⟩
  imodintro
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments Hexceptions Hruntime Hhost]
  · iapply (stateInterp_eq
      { store with wasm := { store.wasm with host } }
      steps observations threads).mpr
    iexists σ
    iexists globalσ
    iexists dataSegmentσ
    iexists tableσ
    iexists elementSegmentσ
    iexists exceptionσ
    iframe Hheap Hglobals Hsegments Htables HelementSegments Hexceptions Hruntime Hhost
    ipureintro
    exact Hfacts
  · iexact Hown

/-- Regression lemma: the client fragment cannot describe a host state that
differs from the physical state protected by `StateInterp`. -/
theorem stateInterp_host_agree [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat) (host : α) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      hostStateOwn host ⊢ ⌜store.wasm.host = host⌝ := by
  iintro ⟨Hstate, Hown⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%heap, %globals, %segments, %tables, %elements, %exceptions,
      Hheap, Hglobals, Hsegments, Htables, Helements, Hexceptions, Hruntime, Hhost, %Hfacts⟩
  iapply hostState_agree store.wasm.host host
  iframe Hhost Hown
=======
        steps observations threads ∗
      hostStateOwn host := by
  iintro ⟨Hσ, HP⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hσ with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %runtimeModuleσ, %hostEnvσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, HruntimeModuleAuth, HruntimeModuleBigSep,
      HruntimeInstances, HinstanceAuth, HhostEnvAuth, Hstate_auth, %Hfacts⟩
  imod hostStateOwn_update store.wasm.host host $$ [$Hstate_auth $HP] with ⟨Hauth', HP'⟩
  imodintro
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth HhostEnvAuth Hauth']
  · iapply (stateInterp_eq
      { store with wasm := { store.wasm with host } }
      steps observations threads).mpr
    iexists σ; iexists globalσ; iexists dataSegmentσ; iexists tableσ
    iexists elementSegmentσ; iexists runtimeModuleσ; iexists hostEnvσ
    iframe Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth HhostEnvAuth Hauth'
    ipureintro
    exact Hfacts
  · iexact HP'
>>>>>>> origin/main

theorem stateInterp_pointsToBytes_agree [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (addr : UInt32) (bytes : List UInt8) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      pointsToBytes addr bytes ==∗
      ⌜∀ i b, bytes[i]? = some b →
          store.wasm.mem.read8 (addr + UInt32.ofNat i) = b ∧
          (addr + UInt32.ofNat i).toNat < store.wasm.mem.pages * 65536⌝ := by
  induction bytes generalizing addr with
  | nil =>
      iintro ⟨-, -⟩
      ipureintro
      intro i b h
      simp at h
  | cons b rest ih =>
      iintro ⟨Hstate, Hbytes⟩
      ihave Hbytes := (pointsToBytes_cons addr b rest).mp $$ Hbytes
      icases Hbytes with ⟨Hhead, Hrest⟩
      ihave %hhead :
          ⌜store.wasm.mem.read8 addr = b ∧
            addr.toNat < store.wasm.mem.pages * 65536⌝ $$ [Hstate Hhead]
      · imod stateInterp_pointsTo_facts store steps observations threads addr b $$
            [$Hstate $Hhead] with %hhead
        ipureintro; exact hhead
      ihave %hrest :
          ⌜∀ i b', rest[i]? = some b' →
            store.wasm.mem.read8 ((addr + 1) + UInt32.ofNat i) = b' ∧
            ((addr + 1) + UInt32.ofNat i).toNat <
              store.wasm.mem.pages * 65536⌝ $$ [Hstate Hrest]
      · imod (ih (addr + 1)) $$ [$Hstate $Hrest] with %hrest
        ipureintro; exact hrest
      ipureintro
      intro i b' hget
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
          subst hget
          simpa using hhead
      | succ j =>
          simp only [List.getElem?_cons_succ] at hget
          obtain ⟨hmem, hbound⟩ := hrest j b' hget
          rw [← byte_offset_succ addr j] at hmem hbound
          exact ⟨hmem, hbound⟩

/-- Whole-range bound from the per-byte physical facts produced by
`stateInterp_pointsToBytes_agree`: a nonempty owned byte range that does not
wrap around the 32-bit address space pins `addr + bytes.length` within the
physical memory size. -/
theorem pointsToBytes_facts_bound {addr : UInt32} {bytes : List UInt8}
    {mem : Mem}
    (hfacts : ∀ i b, bytes[i]? = some b →
        mem.read8 (addr + UInt32.ofNat i) = b ∧
        (addr + UInt32.ofNat i).toNat < mem.pages * 65536)
    (hpos : 0 < bytes.length)
    (hnowrap : addr.toNat + bytes.length < 4294967296) :
    addr.toNat + bytes.length ≤ mem.pages * 65536 := by
  have hidx : bytes.length - 1 < bytes.length := by omega
  obtain ⟨-, hb⟩ :=
    hfacts (bytes.length - 1) (bytes[bytes.length - 1]'hidx)
      (List.getElem?_eq_getElem hidx)
  rw [UInt32.add_ofNat_toNat_noWrap addr (bytes.length - 1)
    (by omega) (by omega)] at hb
  omega

private def fillSigma (σ : WasmHeapMap (Option UInt8)) (addr : UInt32)
    (bytes : List UInt8) (val : UInt8) : WasmHeapMap (Option UInt8) :=
  match bytes with
  | [] => σ
  | _ :: rest => fillSigma (insert σ addr (some val)) (addr + 1) rest val

private theorem fillSigma_ghost [WasmSmallStepGS hlc α]
    (σ : WasmHeapMap (Option UInt8)) (addr : UInt32)
    (bytes : List UInt8) (val : UInt8) :
    genHeapInterp σ ∗ pointsToBytes addr bytes ==∗
    genHeapInterp (fillSigma σ addr bytes val) ∗
    pointsToBytes addr (List.replicate bytes.length val) := by
  induction bytes generalizing σ addr with
  | nil =>
      show genHeapInterp σ ∗ pointsToBytes addr [] ==∗
           genHeapInterp σ ∗ pointsToBytes addr []
      iintro ⟨Hheap, Hempty⟩
      imodintro
      isplitl [Hheap]
      · iexact Hheap
      · iexact Hempty
  | cons b rest ih =>
      show genHeapInterp σ ∗ pointsToBytes addr (b :: rest) ==∗
           genHeapInterp (fillSigma (insert σ addr (some val)) (addr + 1) rest val) ∗
           pointsToBytes addr (val :: List.replicate rest.length val)
      iintro ⟨Hheap, Hbytes⟩
      ihave Hbytes := (pointsToBytes_cons addr b rest).mp $$ Hbytes
      icases Hbytes with ⟨Hhead, Hrest⟩
      imod genHeap_update (v₂ := some val) $$ [$Hheap $Hhead] with ⟨Hheap, Hhead⟩
      imod (ih (insert σ addr (some val)) (addr + 1)) $$ [$Hheap $Hrest] with ⟨Hheap, Hrest⟩
      imodintro
      isplitl [Hheap]
      · iexact Hheap
      · iapply (pointsToBytes_cons addr val (List.replicate rest.length val)).mpr
        isplitl [Hhead]
        · iexact Hhead
        · iexact Hrest

private theorem fillSigma_agrees
    (σ : WasmHeapMap (Option UInt8)) (mem : Mem)
    (addr : UInt32) (bytes : List UInt8) (val : UInt8)
    (hagree : heapAgreesWithMem σ mem)
    (hnowrap : addr.toNat + bytes.length < 4294967296) :
    heapAgreesWithMem (fillSigma σ addr bytes val)
      (mem.fill addr.toNat bytes.length val) := by
  induction bytes generalizing σ addr mem with
  | nil => simp only [fillSigma, List.length_nil, Mem.fill_zero]; exact hagree
  | cons b rest ih =>
      have h1 : (addr + 1).toNat = addr.toNat + 1 := by
        simp only [UInt32.toNat_add, show (1 : UInt32).toNat = 1 from rfl]
        simp only [List.length_cons] at hnowrap; omega
      have hnowrap' : (addr + 1).toNat + rest.length < 4294967296 := by
        rw [h1]; simp only [List.length_cons] at hnowrap; omega
      have ih' := ih (insert σ addr (some val)) (mem.write8 addr val) (addr + 1)
          (store_sound σ mem addr val hagree) hnowrap'
      rw [h1, Mem.write8_fill_eq] at ih'
      exact ih'

private theorem fillSigma_inBounds
    (σ : WasmHeapMap (Option UInt8)) (mem : Mem)
    (addr : UInt32) (bytes : List UInt8) (val : UInt8)
    (hinBounds : heapAddressesInBounds σ mem)
    (hbound : addr.toNat + bytes.length ≤ mem.pages * 65536)
    (hnowrap : addr.toNat + bytes.length < 4294967296) :
    heapAddressesInBounds (fillSigma σ addr bytes val)
      (mem.fill addr.toNat bytes.length val) := by
  induction bytes generalizing σ addr mem with
  | nil => simp only [fillSigma, List.length_nil, Mem.fill_zero]; exact hinBounds
  | cons b rest ih =>
      have h1 : (addr + 1).toNat = addr.toNat + 1 := by
        simp only [UInt32.toNat_add, show (1 : UInt32).toNat = 1 from rfl]
        simp only [List.length_cons] at hnowrap; omega
      have hnowrap' : (addr + 1).toNat + rest.length < 4294967296 := by
        rw [h1]; simp only [List.length_cons] at hnowrap; omega
      have hbound' : (addr + 1).toNat + rest.length ≤ (mem.write8 addr val).pages * 65536 := by
        have : (mem.write8 addr val).pages = mem.pages := rfl
        rw [this, h1]; simp only [List.length_cons] at hbound; omega
      have ih' := ih (insert σ addr (some val)) (mem.write8 addr val) (addr + 1)
          (store_inBounds σ mem addr val hinBounds
            (by simp only [List.length_cons] at hbound; omega))
          hbound' hnowrap'
      rw [h1, Mem.write8_fill_eq] at ih'
      exact ih'

/-- Ghost update for a bulk memory fill: given ownership of all bytes in the
fill range, updates the stateInterp and returns ownership of the same range
filled with `val`. -/
theorem stateInterp_fill_bytes [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (addr : UInt32) (oldBytes : List UInt8) (val : UInt8)
    (hbound : addr.toNat + oldBytes.length ≤ store.wasm.mem.pages * 65536)
    (hnowrap : addr.toNat + oldBytes.length < 4294967296) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      pointsToBytes addr oldBytes ==∗
      stateInterp (GF := WasmHeapGF α)
        { store with wasm :=
            { store.wasm with mem :=
                store.wasm.mem.fill addr.toNat oldBytes.length val } }
        steps observations threads ∗
      pointsToBytes addr (List.replicate oldBytes.length val) := by
  iintro ⟨Hstate, Hbytes⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %exceptionσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hexceptions, Hruntime, Hhost, %Hfacts⟩
  imod fillSigma_ghost σ addr oldBytes val $$ [$Hheap $Hbytes] with ⟨Hheap, Hbytes⟩
  imodintro
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments Hexceptions Hruntime Hhost]
  · iapply (stateInterp_eq
        { store with wasm :=
            { store.wasm with mem :=
                store.wasm.mem.fill addr.toNat oldBytes.length val } }
        steps observations threads).mpr
    iexists fillSigma σ addr oldBytes val
    iexists globalσ
    iexists dataSegmentσ
    iexists tableσ
    iexists elementSegmentσ
    iexists exceptionσ
    iframe Hheap Hglobals Hsegments Htables HelementSegments Hexceptions Hruntime Hhost
    ipureintro
    exact ⟨fillSigma_agrees σ store.wasm.mem addr oldBytes val Hfacts.1 hnowrap,
      fillSigma_inBounds σ store.wasm.mem addr oldBytes val Hfacts.2.1 hbound hnowrap,
      Hfacts.2.2⟩
  · iexact Hbytes

-- ghost map updated by a bulk copy: oldBytes[k] replaced by srcBytes[k] at dst+k
private def copySigma (σ : WasmHeapMap (Option UInt8)) (dst : UInt32)
    (oldBytes srcBytes : List UInt8) : WasmHeapMap (Option UInt8) :=
  match oldBytes, srcBytes with
  | _ :: oldRest, s :: srcRest => copySigma (insert σ dst (some s)) (dst + 1) oldRest srcRest
  | _, _ => σ

-- get? outside [dst, dst+oldBytes.length) is unchanged
private theorem copySigma_get?_out
    (σ : WasmHeapMap (Option UInt8)) (dst : UInt32)
    (oldBytes srcBytes : List UInt8) (addr : UInt32)
    (hlen : srcBytes.length = oldBytes.length)
    (hnowrap : dst.toNat + oldBytes.length < 4294967296)
    (hout : addr.toNat < dst.toNat ∨ dst.toNat + oldBytes.length ≤ addr.toNat) :
    get? (copySigma σ dst oldBytes srcBytes) addr = get? σ addr := by
  induction oldBytes generalizing σ dst srcBytes with
  | nil => simp [copySigma]
  | cons b bRest ih =>
      cases srcBytes with
      | nil => simp at hlen
      | cons s sRest =>
          simp only [copySigma]
          have hlen' : sRest.length = bRest.length := by simpa [List.length_cons] using hlen
          have h1 : (dst + 1).toNat = dst.toNat + 1 := by
            simp only [UInt32.toNat_add, show (1 : UInt32).toNat = 1 from rfl]
            simp only [List.length_cons] at hnowrap; omega
          have hnowrap' : (dst + 1).toNat + bRest.length < 4294967296 := by
            rw [h1]; simp only [List.length_cons] at hnowrap; omega
          have hne : addr ≠ dst := by
            intro heq; subst heq; simp only [List.length_cons] at hout; omega
          have hout' : addr.toNat < (dst + 1).toNat ∨ (dst + 1).toNat + bRest.length ≤ addr.toNat := by
            rw [h1]; simp only [List.length_cons] at hout; omega
          rw [ih (insert σ dst (some s)) (dst + 1) sRest hlen' hnowrap' hout',
              get?_insert_ne hne.symm]

-- get? at dst + ofNat j gives some (some srcBytes[j])
private theorem copySigma_get?_in
    (σ : WasmHeapMap (Option UInt8)) (dst : UInt32)
    (oldBytes srcBytes : List UInt8) (j : Nat)
    (hlen : srcBytes.length = oldBytes.length)
    (hj : j < srcBytes.length)
    (hnowrap : dst.toNat + srcBytes.length < 4294967296) :
    get? (copySigma σ dst oldBytes srcBytes) (dst + UInt32.ofNat j) =
    some (some (srcBytes[j]'hj)) := by
  induction srcBytes generalizing σ dst oldBytes j with
  | nil => simp at hj
  | cons s sRest ih =>
      cases oldBytes with
      | nil => simp at hlen
      | cons b bRest =>
          simp only [copySigma]
          have hlen' : sRest.length = bRest.length := by simpa [List.length_cons] using hlen
          have h1 : (dst + 1).toNat = dst.toNat + 1 := by
            simp only [UInt32.toNat_add, show (1 : UInt32).toNat = 1 from rfl]
            simp only [List.length_cons] at hnowrap; omega
          have hnowrap' : (dst + 1).toNat + sRest.length < 4294967296 := by
            rw [h1]; simp only [List.length_cons] at hnowrap; omega
          cases j with
          | zero =>
              have h0 : dst + UInt32.ofNat 0 = dst := by
                apply UInt32.toNat_inj.mp
                simp only [UInt32.toNat_add,
                           show (UInt32.ofNat 0 : UInt32).toNat = 0 from rfl]
                simp only [List.length_cons] at hnowrap; omega
              rw [h0]
              simp only [List.getElem_cons_zero]
              rw [copySigma_get?_out (insert σ dst (some s)) (dst + 1) bRest sRest dst
                    hlen' (by omega) (Or.inl (by rw [h1]; omega)),
                  get?_insert_eq rfl]
          | succ j' =>
              have hj' : j' < sRest.length := by simpa [List.length_cons] using hj
              rw [byte_offset_succ dst j',
                  ih (insert σ dst (some s)) (dst + 1) bRest j' hlen' hj' hnowrap']
              simp [List.getElem_cons_succ]

-- Iris ghost update: pointsToBytes dst oldBytes → pointsToBytes dst srcBytes
private theorem copySigma_ghost [WasmSmallStepGS hlc α]
    (σ : WasmHeapMap (Option UInt8)) (dst : UInt32)
    (oldBytes srcBytes : List UInt8)
    (hlen : srcBytes.length = oldBytes.length) :
    genHeapInterp σ ∗ pointsToBytes dst oldBytes ==∗
    genHeapInterp (copySigma σ dst oldBytes srcBytes) ∗
    pointsToBytes dst srcBytes := by
  induction oldBytes generalizing σ dst srcBytes with
  | nil =>
      cases srcBytes with
      | nil =>
          show genHeapInterp σ ∗ pointsToBytes dst [] ==∗
               genHeapInterp σ ∗ pointsToBytes dst []
          iintro ⟨Hheap, Hempty⟩
          imodintro
          isplitl [Hheap]
          · iexact Hheap
          · iexact Hempty
      | cons => simp at hlen
  | cons b bRest ih =>
      cases srcBytes with
      | nil => simp at hlen
      | cons s sRest =>
          show genHeapInterp σ ∗ pointsToBytes dst (b :: bRest) ==∗
               genHeapInterp (copySigma (insert σ dst (some s)) (dst + 1) bRest sRest) ∗
               pointsToBytes dst (s :: sRest)
          iintro ⟨Hheap, Hbytes⟩
          ihave Hbytes := (pointsToBytes_cons dst b bRest).mp $$ Hbytes
          icases Hbytes with ⟨Hhead, Hrest⟩
          imod genHeap_update (v₂ := some s) $$ [$Hheap $Hhead] with ⟨Hheap, Hhead⟩
          imod (ih (insert σ dst (some s)) (dst + 1) sRest
                  (by simpa [List.length_cons] using hlen)) $$
              [$Hheap $Hrest] with ⟨Hheap, Hrest⟩
          imodintro
          isplitl [Hheap]
          · iexact Hheap
          · iapply (pointsToBytes_cons dst s sRest).mpr
            isplitl [Hhead]
            · iexact Hhead
            · iexact Hrest

-- heapAgreesWithMem for copySigma, parameterized by the new physical memory
private theorem copySigma_agrees_of_read_eq
    (σ : WasmHeapMap (Option UInt8)) (mem newMem : Mem)
    (dst : UInt32) (oldBytes srcBytes : List UInt8)
    (hlen : srcBytes.length = oldBytes.length)
    (hagree : heapAgreesWithMem σ mem)
    (hnowrap : dst.toNat + oldBytes.length < 4294967296)
    (h_in : ∀ k b, srcBytes[k]? = some b → newMem.read8 (dst + UInt32.ofNat k) = b)
    (h_out : ∀ addr,
        addr.toNat < dst.toNat ∨ dst.toNat + oldBytes.length ≤ addr.toNat →
        newMem.read8 addr = mem.read8 addr) :
    heapAgreesWithMem (copySigma σ dst oldBytes srcBytes) newMem := by
  intro addr v hlookup
  by_cases hrange : dst.toNat ≤ addr.toNat ∧ addr.toNat < dst.toNat + oldBytes.length
  · obtain ⟨hle, hlt⟩ := hrange
    let k : Nat := addr.toNat - dst.toNat
    have hk : k < srcBytes.length := by omega
    have hget : srcBytes[k]? = some (srcBytes[k]'hk) := List.getElem?_eq_getElem hk
    have h_addr_eq : addr = dst + UInt32.ofNat k := by
      apply UInt32.toNat_inj.mp
      rw [UInt32.toNat_add]; show addr.toNat = (dst.toNat + k % 2 ^ 32) % 2 ^ 32; omega
    rw [h_addr_eq] at hlookup
    rw [copySigma_get?_in σ dst oldBytes srcBytes k hlen hk (hlen ▸ hnowrap)] at hlookup
    have hv : srcBytes[k]'hk = v := Option.some.inj (Option.some.inj hlookup)
    rw [h_addr_eq]
    exact (h_in k (srcBytes[k]'hk) hget).trans hv
  · have hout : addr.toNat < dst.toNat ∨ dst.toNat + oldBytes.length ≤ addr.toNat := by omega
    rw [copySigma_get?_out σ dst oldBytes srcBytes addr hlen hnowrap hout] at hlookup
    rw [h_out addr hout]
    exact hagree addr v hlookup

-- heapAddressesInBounds for copySigma
private theorem copySigma_inBounds
    (σ : WasmHeapMap (Option UInt8)) (mem newMem : Mem)
    (dst : UInt32) (oldBytes srcBytes : List UInt8)
    (hlen : srcBytes.length = oldBytes.length)
    (hinBounds : heapAddressesInBounds σ mem)
    (hbound : dst.toNat + oldBytes.length ≤ mem.pages * 65536)
    (hnowrap : dst.toNat + oldBytes.length < 4294967296)
    (h_pages : newMem.pages = mem.pages) :
    heapAddressesInBounds (copySigma σ dst oldBytes srcBytes) newMem := by
  intro addr v hlookup
  rw [h_pages]
  by_cases hrange : dst.toNat ≤ addr.toNat ∧ addr.toNat < dst.toNat + oldBytes.length
  · omega
  · have hout : addr.toNat < dst.toNat ∨ dst.toNat + oldBytes.length ≤ addr.toNat := by omega
    rw [copySigma_get?_out σ dst oldBytes srcBytes addr hlen hnowrap hout] at hlookup
    exact hinBounds addr v hlookup

-- helper: (dst + UInt32.ofNat k).toNat = dst.toNat + k when sum < 2^32
private theorem add_ofNat_toNat (dst : UInt32) (k : Nat) (h : dst.toNat + k < 2 ^ 32) :
    (dst + UInt32.ofNat k).toNat = dst.toNat + k := by
  rw [UInt32.toNat_add]; show (dst.toNat + k % 2 ^ 32) % 2 ^ 32 = dst.toNat + k; omega

/-- Ghost update for a bulk memory copy: given ownership of source and
destination byte ranges, updates the stateInterp and returns the destination
range filled with the source bytes (memmove semantics). -/
theorem stateInterp_copy_bytes [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (dst src : UInt32) (oldDstBytes srcBytes : List UInt8)
    (hlen : srcBytes.length = oldDstBytes.length)
    (hdst_bound : dst.toNat + oldDstBytes.length ≤ store.wasm.mem.pages * 65536)
    (hdst_nowrap : dst.toNat + oldDstBytes.length < 4294967296)
    (_hsrc_bound : src.toNat + srcBytes.length ≤ store.wasm.mem.pages * 65536)
    (hsrc_nowrap : src.toNat + srcBytes.length < 4294967296) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      pointsToBytes src srcBytes ∗
      pointsToBytes dst oldDstBytes ==∗
      stateInterp (GF := WasmHeapGF α)
        { store with wasm :=
            { store.wasm with mem :=
                store.wasm.mem.copy dst.toNat src.toNat oldDstBytes.length } }
        steps observations threads ∗
      pointsToBytes src srcBytes ∗
      pointsToBytes dst srcBytes := by
  iintro ⟨Hstate, Hsrc, Hdst⟩
  ihave %hagree :
      ⌜∀ i b, srcBytes[i]? = some b →
          store.wasm.mem.read8 (src + UInt32.ofNat i) = b ∧
          (src + UInt32.ofNat i).toNat < store.wasm.mem.pages * 65536⌝ $$ [Hstate Hsrc]
  · imod stateInterp_pointsToBytes_agree store steps observations threads src srcBytes $$
        [$Hstate $Hsrc] with %hagree
    ipureintro; exact hagree
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %exceptionσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hexceptions, Hruntime, Hhost, %Hfacts⟩
  imod copySigma_ghost σ dst oldDstBytes srcBytes hlen $$ [$Hheap $Hdst] with ⟨Hheap, Hdst⟩
  imodintro
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments Hexceptions Hruntime Hhost]
  · iapply (stateInterp_eq
        { store with wasm :=
            { store.wasm with mem :=
                store.wasm.mem.copy dst.toNat src.toNat oldDstBytes.length } }
        steps observations threads).mpr
    iexists copySigma σ dst oldDstBytes srcBytes
    iexists globalσ; iexists dataSegmentσ; iexists tableσ; iexists elementSegmentσ
    iframe Hheap Hglobals Hsegments Htables HelementSegments Hexceptions Hruntime Hhost
    ipureintro
    refine ⟨copySigma_agrees_of_read_eq σ store.wasm.mem
                (store.wasm.mem.copy dst.toNat src.toNat oldDstBytes.length)
                dst oldDstBytes srcBytes hlen Hfacts.1 hdst_nowrap
                (fun k b hget => ?h_in) (fun addr hout => ?h_out),
            copySigma_inBounds σ store.wasm.mem
                (store.wasm.mem.copy dst.toNat src.toNat oldDstBytes.length)
                dst oldDstBytes srcBytes hlen Hfacts.2.1 hdst_bound hdst_nowrap
                (Mem.copy_pages store.wasm.mem dst.toNat src.toNat oldDstBytes.length),
            Hfacts.2.2⟩
    case h_in =>
      have hk : k < srcBytes.length := by
        suffices h : ¬ srcBytes.length ≤ k by omega
        intro hle
        simp [List.getElem?_eq_none hle] at hget
      have h_dst_k := add_ofNat_toNat dst k (by rw [hlen] at hk; omega)
      have h_src_k := add_ofNat_toNat src k (by omega)
      have h_copy := Mem.copy_read8_in store.wasm.mem dst.toNat src.toNat oldDstBytes.length
          (dst + UInt32.ofNat k) ⟨by omega, by rw [hlen] at hk; omega⟩
      rw [h_dst_k, Nat.add_sub_cancel_left] at h_copy
      have h_src_read := (hagree k b hget).1
      simp only [Mem.read8, h_src_k] at h_src_read
      exact h_copy.trans h_src_read
    case h_out =>
      exact Mem.copy_read8_out store.wasm.mem dst.toNat src.toNat oldDstBytes.length addr (by omega)
  · isplitl [Hsrc]
    · iexact Hsrc
    · iexact Hdst

/-- Ghost update for a bulk memory init: given ownership of the destination
byte range, updates the stateInterp and returns the range filled with
the corresponding slice of the segment bytes. The segment ghost ownership
is preserved. -/
theorem stateInterp_init_bytes [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (dst : UInt32) (srcOff len : Nat) (segmentIndex : Nat)
    (oldDstBytes : List UInt8) (segmentBytes : List UInt8)
    (hlen : oldDstBytes.length = len)
    (hdst_bound : dst.toNat + len ≤ store.wasm.mem.pages * 65536)
    (hdst_nowrap : dst.toNat + len < 4294967296)
    (hsource : srcOff + len ≤ segmentBytes.length) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      dataSegmentPointsTo segmentIndex (some segmentBytes) ∗
      pointsToBytes dst oldDstBytes ==∗
      stateInterp (GF := WasmHeapGF α)
        { store with wasm :=
            { store.wasm with mem :=
                store.wasm.mem.writeBytesFrom dst.toNat segmentBytes srcOff len } }
        steps observations threads ∗
      dataSegmentPointsTo segmentIndex (some segmentBytes) ∗
      pointsToBytes dst ((segmentBytes.drop srcOff).take len) := by
  let newDstBytes := (segmentBytes.drop srcOff).take len
  have hlen_new : newDstBytes.length = len := by
    simp only [newDstBytes, List.length_take, List.length_drop]; omega
  have hlen_eq : newDstBytes.length = oldDstBytes.length := by omega
  iintro ⟨Hstate, Hseg, Hdst⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %exceptionσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hexceptions, Hruntime, Hhost, %Hfacts⟩
  imod copySigma_ghost σ dst oldDstBytes newDstBytes hlen_eq $$
      [$Hheap $Hdst] with ⟨Hheap, Hdst⟩
  imodintro
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments Hexceptions Hruntime Hhost]
  · iapply (stateInterp_eq
        { store with wasm :=
            { store.wasm with mem :=
                store.wasm.mem.writeBytesFrom dst.toNat segmentBytes srcOff len } }
        steps observations threads).mpr
    iexists copySigma σ dst oldDstBytes newDstBytes
    iexists globalσ; iexists dataSegmentσ; iexists tableσ; iexists elementSegmentσ
    iframe Hheap Hglobals Hsegments Htables HelementSegments Hexceptions Hruntime Hhost
    ipureintro
    refine ⟨copySigma_agrees_of_read_eq σ store.wasm.mem
                (store.wasm.mem.writeBytesFrom dst.toNat segmentBytes srcOff len)
                dst oldDstBytes newDstBytes hlen_eq Hfacts.1 (hlen ▸ hdst_nowrap)
                (fun k b hget => ?h_in) (fun addr hout => ?h_out),
            copySigma_inBounds σ store.wasm.mem
                (store.wasm.mem.writeBytesFrom dst.toNat segmentBytes srcOff len)
                dst oldDstBytes newDstBytes hlen_eq Hfacts.2.1 (hlen ▸ hdst_bound)
                (hlen ▸ hdst_nowrap)
                (Mem.writeBytesFrom_pages store.wasm.mem dst.toNat segmentBytes srcOff len),
            Hfacts.2.2⟩
    case h_in =>
      have hk : k < newDstBytes.length := by
        suffices h : ¬ newDstBytes.length ≤ k by omega
        intro hle
        simp [List.getElem?_eq_none hle] at hget
      have hk_len : k < len := by omega
      have h_dst_k := add_ofNat_toNat dst k (by omega)
      have hbound_seg : srcOff + k < segmentBytes.length := by omega
      have hin : dst.toNat ≤ (dst + UInt32.ofNat k).toNat ∧
                 (dst + UInt32.ofNat k).toNat < dst.toNat + len := by
        rw [h_dst_k]; constructor <;> omega
      have hbound_actual : srcOff + ((dst + UInt32.ofNat k).toNat - dst.toNat) <
          segmentBytes.length := by
        rw [h_dst_k, Nat.add_sub_cancel_left]; exact hbound_seg
      rw [Mem.writeBytesFrom_read8_in _ _ _ _ _ _ hin hbound_actual]
      have hidx : srcOff + ((dst + UInt32.ofNat k).toNat - dst.toNat) = srcOff + k := by
        rw [h_dst_k, Nat.add_sub_cancel_left]
      have hget_some : newDstBytes[k]? = some (newDstBytes[k]'hk) := List.getElem?_eq_getElem hk
      have hb : b = newDstBytes[k]'hk := Option.some.inj (hget.symm.trans hget_some)
      have hval : newDstBytes[k]'hk = segmentBytes[srcOff + k]'hbound_seg := by
        simp [newDstBytes, List.getElem_take, List.getElem_drop]
      have hboth : segmentBytes[srcOff + ((dst + UInt32.ofNat k).toNat - dst.toNat)]? =
                   segmentBytes[srcOff + k]? := by rw [hidx]
      have hg_actual := List.getElem?_eq_getElem (l := segmentBytes)
                          (i := srcOff + ((dst + UInt32.ofNat k).toNat - dst.toNat)) hbound_actual
      have hg_k := List.getElem?_eq_getElem (l := segmentBytes) (i := srcOff + k) hbound_seg
      exact (Option.some.inj (hg_actual.symm.trans (hboth.trans hg_k))).trans
            (hval.symm.trans hb.symm)
    case h_out =>
      exact Mem.writeBytesFrom_read8_out store.wasm.mem dst.toNat segmentBytes srcOff len addr
          (by omega)
  · isplitl [Hseg]
    · iexact Hseg
    · iexact Hdst

/-- Owned global state determines the corresponding physical instantiated
global. -/
theorem stateInterp_global_facts [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (index : Nat) (value : Value) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      globalPointsToAt 0 index value ==∗
      ⌜store.wasm.globals.globals[index]? = some value⌝ := by
  iintro ⟨Hstate, Hglobal⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
<<<<<<< HEAD
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %exceptionσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hexceptions, Hruntime, Hhost, %Hfacts⟩
  ihave %hlookup := globalPointsTo_lookup globalσ index value $$ Hglobals Hglobal
=======
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %runtimeModuleσ, %hostEnvσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, HruntimeModuleAuth, HruntimeModuleBigSep, HruntimeInstances, HinstanceAuth, HhostEnvAuth, Hstate_auth, %Hfacts⟩
  simp only [globalPointsToAt]
  ihave %hlookup := globalPointsTo_lookup globalσ ⟨0, index⟩ value $$ Hglobals Hglobal
>>>>>>> origin/main
  ipureintro
  exact Hfacts.2.2.1 index value hlookup

/-- Owned table state determines the corresponding physical instantiated table.
Uses the unfolded `tablePointsTo` form so `iframe` can match without going through the
`tablePointsToAt` def. Call after `simp only [tablePointsToAt]` to unfold the hypothesis. -/
theorem stateInterp_table_facts [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (tableIndex : Nat) (table : TableInst) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      tablePointsTo (⟨0, tableIndex⟩ : TableKey) table ==∗
      ⌜store.wasm.tables[tableIndex]? = some table⌝ := by
  iintro ⟨Hstate, Htable⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %runtimeModuleσ, %hostEnvσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, HruntimeModuleAuth, HruntimeModuleBigSep, HruntimeInstances, HinstanceAuth, HhostEnvAuth, Hstate_auth, %Hfacts⟩
  ihave %hlookup := tablePointsTo_lookup tableσ ⟨0, tableIndex⟩ table $$ Htables Htable
  ipureintro
  exact Hfacts.2.2.2.2.1 tableIndex table hlookup

/-- Updating an owned global updates both the authoritative ghost map and the
physical instantiated global array in lockstep. -/
theorem stateInterp_global_set [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (index : Nat) (oldValue newValue : Value) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      globalPointsToAt 0 index oldValue ==∗
      stateInterp (GF := WasmHeapGF α)
        { store with wasm :=
            { store.wasm with globals :=
                { globals := store.wasm.globals.globals.set index newValue } } }
        steps observations threads ∗
      globalPointsToAt 0 index newValue := by
  iintro ⟨Hstate, Hglobal⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
<<<<<<< HEAD
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %exceptionσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hexceptions, Hruntime, Hhost, %Hfacts⟩
=======
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %runtimeModuleσ, %hostEnvσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, HruntimeModuleAuth, HruntimeModuleBigSep, HruntimeInstances, HinstanceAuth, HhostEnvAuth, Hstate_auth, %Hfacts⟩
  simp only [globalPointsToAt]
>>>>>>> origin/main
  ihave %hlookup :=
    globalPointsTo_lookup globalσ ⟨0, index⟩ oldValue $$ Hglobals Hglobal
  imod globalPointsTo_update globalσ ⟨0, index⟩ oldValue newValue $$
      Hglobals Hglobal with
    ⟨Hglobals, Hglobal⟩
  imodintro
<<<<<<< HEAD
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments Hexceptions Hruntime Hhost]
=======
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth HhostEnvAuth Hstate_auth]
>>>>>>> origin/main
  · iapply (stateInterp_eq
      { store with wasm :=
          { store.wasm with globals :=
              { globals := store.wasm.globals.globals.set index newValue } } }
      steps observations threads).mpr
    iexists σ
    iexists insert globalσ ⟨0, index⟩ newValue
    iexists dataSegmentσ
    iexists tableσ
    iexists elementSegmentσ
<<<<<<< HEAD
    iexists exceptionσ
    iframe Hheap Hglobals Hsegments Htables HelementSegments Hexceptions Hruntime Hhost
=======
    iexists runtimeModuleσ
    iexists hostEnvσ
    iframe Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth HhostEnvAuth Hstate_auth
>>>>>>> origin/main
    ipureintro
    exact ⟨Hfacts.1, Hfacts.2.1,
      ⟨global_store_sound globalσ store.wasm.globals
          index oldValue newValue Hfacts.2.2.1 hlookup,
        Hfacts.2.2.2⟩⟩
  · iexact Hglobal

/-- Owned passive-segment state determines the corresponding physical
instantiated segment entry. The framed form keeps both resources available for
a following `memory.init` or `data.drop` transition. -/
theorem stateInterp_dataSegment_facts_frame [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (index : Nat) (value : Option (List UInt8)) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      dataSegmentPointsToAt 0 index value ==∗
      stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      dataSegmentPointsToAt 0 index value ∗
      ⌜store.wasm.dataSegments[index]? = some value⌝ := by
  iintro ⟨Hstate, Hsegment⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
<<<<<<< HEAD
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %exceptionσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hexceptions, Hruntime, Hhost, %Hfacts⟩
=======
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %runtimeModuleσ, %hostEnvσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, HruntimeModuleAuth, HruntimeModuleBigSep, HruntimeInstances, HinstanceAuth, HhostEnvAuth, Hstate_auth, %Hfacts⟩
  simp only [dataSegmentPointsToAt]
>>>>>>> origin/main
  ihave %hlookup :=
    dataSegmentPointsTo_lookup dataSegmentσ ⟨0, index⟩ value $$
      Hsegments Hsegment
  imodintro
<<<<<<< HEAD
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments Hexceptions Hruntime Hhost]
=======
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth HhostEnvAuth Hstate_auth]
>>>>>>> origin/main
  · iapply (stateInterp_eq store steps observations threads).mpr
    iexists σ
    iexists globalσ
    iexists dataSegmentσ
    iexists tableσ
    iexists elementSegmentσ
<<<<<<< HEAD
    iexists exceptionσ
=======
    iexists runtimeModuleσ
    iexists hostEnvσ
>>>>>>> origin/main
    iframe
    ipureintro
    exact Hfacts
  · isplitl [Hsegment]
    · iexact Hsegment
    · ipureintro
      exact Hfacts.2.2.2.1 index value hlookup

/-- `data.drop` updates the physical segment status and its authoritative
ghost entry in lockstep. -/
theorem stateInterp_dataSegment_drop [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (index : Nat) (oldValue : Option (List UInt8)) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      dataSegmentPointsToAt 0 index oldValue ==∗
      stateInterp (GF := WasmHeapGF α)
        { store with wasm :=
            { store.wasm with
              dataSegments := store.wasm.dataSegments.set index none } }
        steps observations threads ∗
      dataSegmentPointsToAt 0 index none := by
  iintro ⟨Hstate, Hsegment⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
<<<<<<< HEAD
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %exceptionσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hexceptions, Hruntime, Hhost, %Hfacts⟩
=======
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %runtimeModuleσ, %hostEnvσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, HruntimeModuleAuth, HruntimeModuleBigSep, HruntimeInstances, HinstanceAuth, HhostEnvAuth, Hstate_auth, %Hfacts⟩
  simp only [dataSegmentPointsToAt]
>>>>>>> origin/main
  ihave %hlookup :=
    dataSegmentPointsTo_lookup dataSegmentσ ⟨0, index⟩ oldValue $$
      Hsegments Hsegment
  imod dataSegmentPointsTo_update dataSegmentσ ⟨0, index⟩ oldValue none $$
      Hsegments Hsegment with
    ⟨Hsegments, Hsegment⟩
  imodintro
<<<<<<< HEAD
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments Hexceptions Hruntime Hhost]
=======
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth HhostEnvAuth Hstate_auth]
>>>>>>> origin/main
  · iapply (stateInterp_eq
      { store with wasm :=
          { store.wasm with
            dataSegments := store.wasm.dataSegments.set index none } }
      steps observations threads).mpr
    iexists σ
    iexists globalσ
    iexists insert dataSegmentσ ⟨0, index⟩ none
    iexists tableσ
    iexists elementSegmentσ
<<<<<<< HEAD
    iexists exceptionσ
=======
    iexists runtimeModuleσ
    iexists hostEnvσ
>>>>>>> origin/main
    iframe
    ipureintro
    exact ⟨Hfacts.1, Hfacts.2.1, Hfacts.2.2.1,
      dataSegment_store_sound dataSegmentσ store.wasm.dataSegments
        index oldValue none Hfacts.2.2.2.1 hlookup,
      Hfacts.2.2.2.2⟩
  · iexact Hsegment

/-- Element-segment ownership identifies the live or dropped state at the
corresponding stable physical segment index. -/
theorem stateInterp_elementSegment_facts_frame [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (index : Nat) (value : Option (List (Option Nat))) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      elementSegmentPointsToAt 0 index value ==∗
      stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      elementSegmentPointsToAt 0 index value ∗
      ⌜store.wasm.elementSegments[index]? = some value⌝ := by
  iintro ⟨Hstate, Hsegment⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
<<<<<<< HEAD
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %exceptionσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hexceptions, Hruntime, Hhost, %Hfacts⟩
=======
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %runtimeModuleσ, %hostEnvσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, HruntimeModuleAuth, HruntimeModuleBigSep, HruntimeInstances, HinstanceAuth, HhostEnvAuth, Hstate_auth, %Hfacts⟩
  simp only [elementSegmentPointsToAt]
>>>>>>> origin/main
  ihave %hlookup :=
    elementSegmentPointsTo_lookup elementSegmentσ ⟨0, index⟩ value $$
      HelementSegments Hsegment
  imodintro
<<<<<<< HEAD
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments Hexceptions Hruntime Hhost]
=======
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth HhostEnvAuth Hstate_auth]
>>>>>>> origin/main
  · iapply (stateInterp_eq store steps observations threads).mpr
    iexists σ
    iexists globalσ
    iexists dataSegmentσ
    iexists tableσ
    iexists elementSegmentσ
<<<<<<< HEAD
    iexists exceptionσ
=======
    iexists runtimeModuleσ
    iexists hostEnvσ
>>>>>>> origin/main
    iframe
    ipureintro
    exact Hfacts
  · isplitl [Hsegment]
    · iexact Hsegment
    · ipureintro
      exact Hfacts.2.2.2.2.2.1 index value hlookup

/-- `elem.drop` changes the physical segment status and authoritative ghost
entry to `none` without renumbering any segment. -/
theorem stateInterp_elementSegment_drop [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (index : Nat) (oldValue : Option (List (Option Nat))) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      elementSegmentPointsToAt 0 index oldValue ==∗
      stateInterp (GF := WasmHeapGF α)
        { store with wasm :=
            { store.wasm with
              elementSegments :=
                store.wasm.elementSegments.set index none } }
        steps observations threads ∗
      elementSegmentPointsToAt 0 index none := by
  iintro ⟨Hstate, Hsegment⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
<<<<<<< HEAD
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %exceptionσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hexceptions, Hruntime, Hhost, %Hfacts⟩
=======
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %runtimeModuleσ, %hostEnvσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, HruntimeModuleAuth, HruntimeModuleBigSep, HruntimeInstances, HinstanceAuth, HhostEnvAuth, Hstate_auth, %Hfacts⟩
  simp only [elementSegmentPointsToAt]
>>>>>>> origin/main
  ihave %hlookup :=
    elementSegmentPointsTo_lookup elementSegmentσ ⟨0, index⟩ oldValue $$
      HelementSegments Hsegment
  imod elementSegmentPointsTo_update
      elementSegmentσ ⟨0, index⟩ oldValue none $$
      HelementSegments Hsegment with
    ⟨HelementSegments, Hsegment⟩
  imodintro
<<<<<<< HEAD
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments Hexceptions Hruntime Hhost]
=======
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth HhostEnvAuth Hstate_auth]
>>>>>>> origin/main
  · iapply (stateInterp_eq
      { store with wasm :=
          { store.wasm with
            elementSegments :=
              store.wasm.elementSegments.set index none } }
      steps observations threads).mpr
    iexists σ
    iexists globalσ
    iexists dataSegmentσ
    iexists tableσ
<<<<<<< HEAD
    iexists insert elementSegmentσ index none
    iexists exceptionσ
=======
    iexists insert elementSegmentσ ⟨0, index⟩ none
    iexists runtimeModuleσ
    iexists hostEnvσ
>>>>>>> origin/main
    iframe
    ipureintro
    exact ⟨Hfacts.1, Hfacts.2.1, Hfacts.2.2.1,
      Hfacts.2.2.2.1,
      ⟨Hfacts.2.2.2.2.1,
        elementSegment_store_sound elementSegmentσ
          store.wasm.elementSegments index oldValue none
          Hfacts.2.2.2.2.2.1 hlookup,
<<<<<<< HEAD
        Hfacts.2.2.2.2.2.2⟩⟩
=======
      Hfacts.2.2.2.2.2.2.1, Hfacts.2.2.2.2.2.2.2⟩⟩
>>>>>>> origin/main
  · iexact Hsegment

/-- Owning a table fragment identifies the complete physical instantiated
table at its stable table index. -/
theorem stateInterp_table_facts_frame [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (index : Nat) (table : TableInst) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      tablePointsToAt 0 index table ==∗
      stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      tablePointsToAt 0 index table ∗
      ⌜store.wasm.tables[index]? = some table⌝ := by
  iintro ⟨Hstate, Htable⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
<<<<<<< HEAD
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %exceptionσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hexceptions, Hruntime, Hhost, %Hfacts⟩
=======
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %runtimeModuleσ, %hostEnvσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, HruntimeModuleAuth, HruntimeModuleBigSep, HruntimeInstances, HinstanceAuth, HhostEnvAuth, Hstate_auth, %Hfacts⟩
  simp only [tablePointsToAt]
>>>>>>> origin/main
  ihave %hlookup :=
    tablePointsTo_lookup tableσ ⟨0, index⟩ table $$ Htables Htable
  imodintro
<<<<<<< HEAD
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments Hexceptions Hruntime Hhost]
=======
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth HhostEnvAuth Hstate_auth]
>>>>>>> origin/main
  · iapply (stateInterp_eq store steps observations threads).mpr
    iexists σ
    iexists globalσ
    iexists dataSegmentσ
    iexists tableσ
    iexists elementSegmentσ
<<<<<<< HEAD
    iexists exceptionσ
=======
    iexists runtimeModuleσ
    iexists hostEnvσ
>>>>>>> origin/main
    iframe
    ipureintro
    exact Hfacts
  · isplitl [Htable]
    · iexact Htable
    · ipureintro
      exact Hfacts.2.2.2.2.1 index table hlookup

/-- Replacing an owned table preserves its stable identity and updates the
authoritative ghost map and physical table list in lockstep. -/
theorem stateInterp_table_set [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (index : Nat) (oldTable newTable : TableInst) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      tablePointsToAt 0 index oldTable ==∗
      stateInterp (GF := WasmHeapGF α)
        { store with wasm :=
            { store.wasm with
              tables := listSetAt store.wasm.tables index newTable } }
        steps observations threads ∗
      tablePointsToAt 0 index newTable := by
  iintro ⟨Hstate, Htable⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
<<<<<<< HEAD
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %exceptionσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hexceptions, Hruntime, Hhost, %Hfacts⟩
=======
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %runtimeModuleσ, %hostEnvσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, HruntimeModuleAuth, HruntimeModuleBigSep, HruntimeInstances, HinstanceAuth, HhostEnvAuth, Hstate_auth, %Hfacts⟩
  simp only [tablePointsToAt]
>>>>>>> origin/main
  ihave %hlookup :=
    tablePointsTo_lookup tableσ ⟨0, index⟩ oldTable $$ Htables Htable
  imod tablePointsTo_update tableσ ⟨0, index⟩ oldTable newTable $$
      Htables Htable with
    ⟨Htables, Htable⟩
  imodintro
<<<<<<< HEAD
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments Hexceptions Hruntime Hhost]
=======
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth HhostEnvAuth Hstate_auth]
>>>>>>> origin/main
  · iapply (stateInterp_eq
      { store with wasm :=
          { store.wasm with
            tables := listSetAt store.wasm.tables index newTable } }
      steps observations threads).mpr
    iexists σ
    iexists globalσ
    iexists dataSegmentσ
    iexists insert tableσ ⟨0, index⟩ newTable
    iexists elementSegmentσ
<<<<<<< HEAD
    iexists exceptionσ
=======
    iexists runtimeModuleσ
    iexists hostEnvσ
>>>>>>> origin/main
    iframe
    ipureintro
    exact ⟨Hfacts.1, Hfacts.2.1, Hfacts.2.2.1,
      Hfacts.2.2.2.1,
      ⟨table_store_listSetAt_sound tableσ store.wasm.tables
          index oldTable newTable Hfacts.2.2.2.2.1 hlookup,
        Hfacts.2.2.2.2.2⟩⟩
  · iexact Htable

theorem stateInterp_runtimeModule_agree [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (instanceId : ModuleInstanceId) (m : Module) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      runtimeModuleOwn instanceId m ==∗
      ⌜store.runtime.currentModule = m⌝ := by
  simp only [runtimeModuleOwn]
  iintro ⟨Hstate, Hmod, Hid⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %runtimeModuleσ, %hostEnvσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, HruntimeModuleAuth, HruntimeModuleBigSep, HruntimeInstances, HinstanceAuth, HhostEnvAuth, Hstate_auth, %Hfacts⟩
  icombine HinstanceAuth Hid as Hentry
  ihave %hentry := currentInstanceOwn_agree store.runtime.entry instanceId $$ Hentry
  ihave %hlookup := runtimeModuleElem_lookup $$ HruntimeModuleAuth Hmod
  ipureintro
  have hma := Hfacts.2.2.2.2.2.2.1 instanceId.id m hlookup
  have hid : store.runtime.entry.id = instanceId.id := congrArg (·.id) hentry
  rw [← hid] at hma
  simp only [RuntimeEnv.currentModule, RuntimeEnv.currentInstance]
  rcases h : store.runtime.instances[store.runtime.entry.id]? with _ | inst
  · rw [h, Option.map_none] at hma; simp at hma
  · rw [h, Option.map_some, Option.some.injEq] at hma
    have hget : store.runtime.instances[store.runtime.entry.id]! = inst := by
      simp only [getElem!_def, h]
    rw [hget]; exact hma

theorem stateInterp_instances_agree [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (instances : Array (ModuleInstance α)) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      runtimeInstancesOwn instances ==∗
      ⌜store.runtime.instances = instances⌝ := by
  iintro ⟨Hstate, Hexpected⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
<<<<<<< HEAD
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %exceptionσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hexceptions, Hactual, Hhost,
      %Hfacts⟩
  ihave Hactual :=
    runtimeInterp_module store.runtime.module store.wasm.tagIds $$ Hactual
  icombine Hactual Hexpected as Hmodules
  ihave %hagrees :=
    runtimeModuleOwn_agree store.runtime.module m $$ Hmodules
  ipureintro
  exact hagrees

theorem stateInterp_exception_facts [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (index : Nat) (dq : DFrac) (tagAndArgs : Nat × List Value) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      exceptionPointsTo index dq tagAndArgs ==∗
      ⌜store.wasm.exns[index]? = some tagAndArgs⌝ := by
  iintro ⟨Hstate, Hexception⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %exceptionσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hexceptions, Hruntime, Hhost, %Hfacts⟩
  ihave %hlookup := exceptionPointsTo_lookup exceptionσ index dq tagAndArgs $$
      Hexceptions Hexception
  ipureintro
  exact Hfacts.2.2.2.2.2.2 index tagAndArgs hlookup

/-- Ghost knowledge of the entry instance's tag table is a prefix of the
physical tag table.  This is the *only* channel through which a rule may learn
anything about tags; the state interpretation itself constrains nothing. -/
theorem stateInterp_tagTable_prefix [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat) (ids : List Nat) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      tagTableOwn ids ==∗
      ⌜ids.IsPrefix store.wasm.tagIds⌝ := by
  iintro ⟨Hstate, Howned⟩
  imodintro
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %exceptionσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hexceptions, Hruntime, Hhost, %Hfacts⟩
  ihave %hprefix :=
    runtimeInterp_tagPrefix store.runtime.module store.wasm.tagIds ids $$
      [$Hruntime $Howned]
  ipureintro
  exact hprefix

/-- The interpreter's tag canonicalisation is the identity on indices that are
canonical in a prefix of the physical tag table.  Entries appended by other
registered modules cannot interfere: `findIdx?` stops at the first match. -/
theorem canonicalTagIndex_of_prefix (store : MachineStore α)
    (ids : List Nat) (index : Nat)
    (hprefix : ids.IsPrefix store.wasm.tagIds)
    (hcanonical : TagIndexCanonical ids index) :
    (match store.wasm.tagIds[index]? with
      | some id => (store.wasm.tagIds.findIdx? (· = id)).getD index
      | none => index) = index := by
  obtain ⟨rest, hrest⟩ := hprefix
  obtain ⟨id, hget, hfind⟩ := hcanonical
  have hlt : index < ids.length := (List.getElem?_eq_some_iff.mp hget).1
  have hget' : store.wasm.tagIds[index]? = some id := by
    rw [← hrest, List.getElem?_append_left hlt]
    exact hget
  have hfind' : store.wasm.tagIds.findIdx? (· = id) = some index := by
    rw [← hrest, List.findIdx?_append, hfind]
    simp
  simp only [hget', hfind', Option.getD_some]
=======
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %runtimeModuleσ, %hostEnvσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, HruntimeModuleAuth, HruntimeModuleBigSep, HruntimeInstances, HinstanceAuth, HhostEnvAuth, Hstate_auth, %Hfacts⟩
  icombine HruntimeInstances Hexpected as Hinst
  ihave %hagrees := runtimeInstancesOwn_agree store.runtime.instances instances $$ Hinst
  ipureintro
  exact hagrees

/-- Owned fragment for the current instance id agrees with the stateInterp value. -/
theorem stateInterp_currentInstance_agree [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (id : ModuleInstanceId) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      currentInstanceOwn id ==∗
      ⌜store.runtime.entry = id⌝ := by
  iintro ⟨Hstate, Hfrag⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %runtimeModuleσ, %hostEnvσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, HruntimeModuleAuth, HruntimeModuleBigSep, HruntimeInstances, HinstanceAuth, HhostEnvAuth, Hstate_auth, %Hfacts⟩
  icombine HinstanceAuth Hfrag as Hcombined
  ihave %hagrees := currentInstanceOwn_agree store.runtime.entry id $$ Hcombined
  ipureintro
  exact hagrees

/-- Update the current instance id in both stateInterp and the owned fragment.
`hch` asserts the new instance has the same host as the current one,
so the `hostEnvOwn` resource remains valid. -/
theorem stateInterp_currentInstance_update [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (newId : ModuleInstanceId) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      currentInstanceOwn store.runtime.entry ==∗
      stateInterp (GF := WasmHeapGF α)
        { store with runtime := { store.runtime with entry := newId } }
        steps observations threads ∗
      currentInstanceOwn newId := by
  iintro ⟨Hstate, Hfrag⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %runtimeModuleσ, %hostEnvσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, HruntimeModuleAuth, HruntimeModuleBigSep, HruntimeInstances, HinstanceAuth, HhostEnvAuth, Hstate_auth, %Hfacts⟩
  imod currentInstanceOwn_update store.runtime.entry newId $$ [$HinstanceAuth $Hfrag] with ⟨HinstanceAuth', Hfrag'⟩
  imodintro
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth' HhostEnvAuth Hstate_auth]
  · iapply (stateInterp_eq
      { store with runtime := { store.runtime with entry := newId } }
      steps observations threads).mpr
    iexists σ; iexists globalσ; iexists dataSegmentσ; iexists tableσ; iexists elementSegmentσ; iexists runtimeModuleσ; iexists hostEnvσ
    have hres : storeResolve { store with runtime := { store.runtime with entry := newId } } = storeResolve store := rfl
    simp only [hres]
    iframe Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth' HhostEnvAuth Hstate_auth
    ipureintro
    exact Hfacts
  · iexact Hfrag'

theorem stateInterp_currentInstance_update_of_any [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (calleeId newId : ModuleInstanceId) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      currentInstanceOwn calleeId ==∗
      stateInterp (GF := WasmHeapGF α)
        { store with runtime := { store.runtime with entry := newId } }
        steps observations threads ∗
      currentInstanceOwn newId ∗
      ⌜store.runtime.entry = calleeId⌝ := by
  iintro ⟨Hstate, Hfrag⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %runtimeModuleσ, %hostEnvσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, HruntimeModuleAuth, HruntimeModuleBigSep, HruntimeInstances, HinstanceAuth, HhostEnvAuth, Hstate_auth, %Hfacts⟩
  imod currentInstanceOwn_update_of_any store.runtime.entry calleeId newId $$
      [$HinstanceAuth $Hfrag] with ⟨HinstanceAuth', Hfrag', %heq⟩
  imodintro
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth' HhostEnvAuth Hstate_auth]
  · iapply (stateInterp_eq
        { store with runtime := { store.runtime with entry := newId } }
        steps observations threads).mpr
    iexists σ; iexists globalσ; iexists dataSegmentσ; iexists tableσ; iexists elementSegmentσ; iexists runtimeModuleσ; iexists hostEnvσ
    have hres : storeResolve { store with runtime := { store.runtime with entry := newId } } = storeResolve store := rfl
    simp only [hres]
    iframe Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth' HhostEnvAuth Hstate_auth
    ipureintro
    exact Hfacts
  isplitl [Hfrag']
  · iexact Hfrag'
  · ipureintro; exact heq

-- push doesn't affect elements before the pushed index
private theorem currentInstance_push_lt (re : RuntimeEnv α) (inst : ModuleInstance α)
    (h : re.entry.id < re.instances.size) :
    ({ re with instances := re.instances.push inst } : RuntimeEnv α).currentInstance =
        re.currentInstance := by
  simp only [RuntimeEnv.currentInstance]
  unfold GetElem?.getElem!
  show (re.instances.push inst).getD re.entry.id default = re.instances.getD re.entry.id default
  unfold Array.getD
  have h2 : re.entry.id < (re.instances.push inst).size := by
    simp only [Array.size_push]; omega
  rw [dif_pos h2, dif_pos h]
  exact Array.getElem_push_lt h

/-- Adding a new instance to the runtime table preserves stateInterp given
ownership of the new instances array. `runtimeInstancesOwn` is Agree-based
(frozen snapshot), so the caller must supply ownership of the pushed array;
`currentInstance_push_lt` ensures the current module and host are unchanged. -/
theorem instantiate_preserves_stateInterp [WasmSmallStepGS hlc α]
    (config : Config α) (newInst : ModuleInstance α)
    (hvalid : config.store.runtime.entry.id < config.store.runtime.instances.size)
    (steps : Nat) (obs : List StepKind) (threads : Nat) :
    stateInterp (GF := WasmHeapGF α) config.store steps obs threads ∗
      runtimeInstancesOwn (config.store.runtime.instances.push newInst) ⊢
      stateInterp (GF := WasmHeapGF α)
        { config.store with runtime := { config.store.runtime with
            instances := config.store.runtime.instances.push newInst } }
        steps obs threads := by
  have hci := currentInstance_push_lt config.store.runtime newInst hvalid
  have hch := congrArg (·.host) hci
  have hres : storeResolve { config.store with runtime := { config.store.runtime with
        instances := config.store.runtime.instances.push newInst } } =
      storeResolve config.store := rfl
  iintro ⟨Hstate, HruntimeInstances'⟩
  icases (stateInterp_eq config.store steps obs threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %runtimeModuleσ, %hostEnvσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, HruntimeModuleAuth, HruntimeModuleBigSep, HruntimeInstances, HinstanceAuth, HhostEnvAuth, Hstate_auth, %Hfacts⟩
  iclear HruntimeInstances
  iapply (stateInterp_eq { config.store with runtime := { config.store.runtime with
      instances := config.store.runtime.instances.push newInst } } steps obs threads).mpr
  iexists σ; iexists globalσ; iexists dataSegmentσ; iexists tableσ; iexists elementSegmentσ; iexists runtimeModuleσ; iexists hostEnvσ
  simp only [hres]
  iframe Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances' HinstanceAuth HhostEnvAuth Hstate_auth
  ipureintro
  refine ⟨Hfacts.1, Hfacts.2.1, Hfacts.2.2.1, Hfacts.2.2.2.1, Hfacts.2.2.2.2.1, Hfacts.2.2.2.2.2.1,
    fun id m hlookup => ?_, fun id env hlookup => ?_⟩
  · have hold := Hfacts.2.2.2.2.2.2.1 id m hlookup
    rw [Array.getElem?_push]
    by_cases h_eq : id = config.store.runtime.instances.size
    · rw [h_eq] at hold; simp at hold
    · rw [if_neg h_eq]; exact hold
  · have hold := Hfacts.2.2.2.2.2.2.2 id env hlookup
    rw [Array.getElem?_push]
    by_cases h_eq : id = config.store.runtime.instances.size
    · rw [h_eq] at hold; simp at hold
    · rw [if_neg h_eq]; exact hold

/-- pointsTo is ghost state — adding an instance doesn't affect existing
byte ownership. Stated explicitly to document the design invariant. -/
theorem instantiate_pointsTo_preserved [WasmSmallStepGS hlc α]
    (key : MemoryKey) (dfrac : DFrac) (value : Option UInt8) :
    (pointsTo (GF := WasmHeapGF α) key dfrac value) ⊢
    (pointsTo (GF := WasmHeapGF α) key dfrac value) := by
  iintro H; iexact H
>>>>>>> origin/main

/-- Four-byte ownership determines the physical little-endian word and proves
the complete access is in bounds. The address equalities exclude UInt32
wraparound in the derived byte footprint. -/
theorem stateInterp_pointsTo_u32_facts [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (address value : UInt32)
    (h1 : (address + 1).toNat = address.toNat + 1)
    (h2 : (address + 2).toNat = address.toNat + 2)
    (h3 : (address + 3).toNat = address.toNat + 3) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      pointsTo_u32 0 address value ==∗
      ⌜store.wasm.mem.read32 address = value ∧
        address.toNat + 4 ≤ store.wasm.mem.pages * 65536⌝ := by
  iintro ⟨Hstate, Hword⟩
  ihave Hword := (pointsTo_u32_eq 0 address value).mp $$ Hword
  icases Hword with ⟨H0, H1, H2, H3⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
<<<<<<< HEAD
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %exceptionσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hexceptions, Hruntime, Hhost, %Hfacts⟩
=======
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %runtimeModuleσ, %hostEnvσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, HruntimeModuleAuth, HruntimeModuleBigSep, HruntimeInstances, HinstanceAuth, HhostEnvAuth, Hstate_auth, %Hfacts⟩
>>>>>>> origin/main
  ihave %hg0 :
      ⌜get? σ ⟨0, address⟩ = some (some (u32Byte value 0))⌝ $$ [Hheap H0]
  · imod genHeap_valid $$ [$Hheap $H0] with %hg0
    ipureintro
    exact hg0
  ihave %hg1 :
      ⌜get? σ ⟨0, address + 1⟩ = some (some (u32Byte value 1))⌝ $$ [Hheap H1]
  · imod genHeap_valid $$ [$Hheap $H1] with %hg1
    ipureintro
    exact hg1
  ihave %hg2 :
      ⌜get? σ ⟨0, address + 2⟩ = some (some (u32Byte value 2))⌝ $$ [Hheap H2]
  · imod genHeap_valid $$ [$Hheap $H2] with %hg2
    ipureintro
    exact hg2
  ihave %hg3 :
      ⌜get? σ ⟨0, address + 3⟩ = some (some (u32Byte value 3))⌝ $$ [Hheap H3]
  · imod genHeap_valid $$ [$Hheap $H3] with %hg3
    ipureintro
    exact hg3
  have hr0 := fromResolver store Hfacts.1 address (u32Byte value 0) hg0
  have hr1 := fromResolver store Hfacts.1 (address + 1) (u32Byte value 1) hg1
  have hr2 := fromResolver store Hfacts.1 (address + 2) (u32Byte value 2) hg2
  have hr3 := fromResolver store Hfacts.1 (address + 3) (u32Byte value 3) hg3
  have hb3 := fromResolverBounds store Hfacts.2.1 (address + 3) (by simp [hg3])
  ipureintro
  constructor
  · simp only [Mem.read8] at hr0 hr1 hr2 hr3
    simp only [Mem.read32]
    rw [hr0, ← h1, hr1, ← h2, hr2, ← h3, hr3]
    exact u32Byte_reassemble value
  · rw [h3] at hb3
    omega

/-- Framed form of `stateInterp_pointsTo_u32_facts`. It preserves both the
state interpretation and word ownership, so clients can extract physical
facts for multiple disjoint words sequentially. -/
theorem stateInterp_pointsTo_u32_facts_frame [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (address value : UInt32)
    (h1 : (address + 1).toNat = address.toNat + 1)
    (h2 : (address + 2).toNat = address.toNat + 2)
    (h3 : (address + 3).toNat = address.toNat + 3) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      pointsTo_u32 0 address value ==∗
      stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      pointsTo_u32 0 address value ∗
      ⌜store.wasm.mem.read32 address = value ∧
        address.toNat + 4 ≤ store.wasm.mem.pages * 65536⌝ := by
  iintro ⟨Hstate, Hword⟩
  ihave Hword := (pointsTo_u32_eq 0 address value).mp $$ Hword
  icases Hword with ⟨H0, H1, H2, H3⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
<<<<<<< HEAD
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %exceptionσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hexceptions, Hruntime, Hhost, %Hfacts⟩
=======
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %runtimeModuleσ, %hostEnvσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, HruntimeModuleAuth, HruntimeModuleBigSep, HruntimeInstances, HinstanceAuth, HhostEnvAuth, Hstate_auth, %Hfacts⟩
>>>>>>> origin/main
  ihave %hg0 :
      ⌜get? σ ⟨0, address⟩ = some (some (u32Byte value 0))⌝ $$ [Hheap H0]
  · imod genHeap_valid $$ [$Hheap $H0] with %hg0
    ipureintro
    exact hg0
  ihave %hg1 :
      ⌜get? σ ⟨0, address + 1⟩ = some (some (u32Byte value 1))⌝ $$ [Hheap H1]
  · imod genHeap_valid $$ [$Hheap $H1] with %hg1
    ipureintro
    exact hg1
  ihave %hg2 :
      ⌜get? σ ⟨0, address + 2⟩ = some (some (u32Byte value 2))⌝ $$ [Hheap H2]
  · imod genHeap_valid $$ [$Hheap $H2] with %hg2
    ipureintro
    exact hg2
  ihave %hg3 :
      ⌜get? σ ⟨0, address + 3⟩ = some (some (u32Byte value 3))⌝ $$ [Hheap H3]
  · imod genHeap_valid $$ [$Hheap $H3] with %hg3
    ipureintro
    exact hg3
  have hr0 := fromResolver store Hfacts.1 address (u32Byte value 0) hg0
  have hr1 := fromResolver store Hfacts.1 (address + 1) (u32Byte value 1) hg1
  have hr2 := fromResolver store Hfacts.1 (address + 2) (u32Byte value 2) hg2
  have hr3 := fromResolver store Hfacts.1 (address + 3) (u32Byte value 3) hg3
  have hb3 := fromResolverBounds store Hfacts.2.1 (address + 3) (by simp [hg3])
  have hread : store.wasm.mem.read32 address = value := by
    simp only [Mem.read8] at hr0 hr1 hr2 hr3
    simp only [Mem.read32]
    rw [hr0, ← h1, hr1, ← h2, hr2, ← h3, hr3]
    exact u32Byte_reassemble value
  have hbound :
      address.toNat + 4 ≤ store.wasm.mem.pages * 65536 := by
    rw [h3] at hb3
    omega
  imodintro
<<<<<<< HEAD
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments Hexceptions Hruntime Hhost]
=======
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth HhostEnvAuth Hstate_auth]
>>>>>>> origin/main
  · iapply (stateInterp_eq store steps observations threads).mpr
    iexists σ
    iexists globalσ
    iexists dataSegmentσ
    iexists tableσ
    iexists elementSegmentσ
<<<<<<< HEAD
    iexists exceptionσ
=======
    iexists runtimeModuleσ
    iexists hostEnvσ
>>>>>>> origin/main
    iframe
    ipureintro
    exact Hfacts
  · isplitl [H0 H1 H2 H3]
    · iapply (pointsTo_u32_eq 0 address value).mpr
      iframe
    · ipureintro
      exact ⟨hread, hbound⟩

theorem stateInterp_pointsTo_u16_facts [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (address value : UInt32)
    (h1 : (address + 1).toNat = address.toNat + 1) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      pointsTo_u16 address value ==∗
      ⌜store.wasm.mem.read16 address = value &&& 0xFFFF ∧
        address.toNat + 2 ≤ store.wasm.mem.pages * 65536⌝ := by
  iintro ⟨Hstate, Hword⟩
  ihave Hword := (pointsTo_u16_eq address value).mp $$ Hword
  icases Hword with ⟨H0, H1⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %exceptionσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hexceptions, Hruntime, Hhost, %Hfacts⟩
  ihave %hg0 :
      ⌜get? σ address = some (some (u16Byte value 0))⌝ $$ [Hheap H0]
  · imod genHeap_valid $$ [$Hheap $H0] with %hg0
    ipureintro
    exact hg0
  ihave %hg1 :
      ⌜get? σ (address + 1) = some (some (u16Byte value 1))⌝ $$ [Hheap H1]
  · imod genHeap_valid $$ [$Hheap $H1] with %hg1
    ipureintro
    exact hg1
  have hr0 := Hfacts.1 address (u16Byte value 0) hg0
  have hr1 := Hfacts.1 (address + 1) (u16Byte value 1) hg1
  have hb1 := Hfacts.2.1 (address + 1) (u16Byte value 1) hg1
  ipureintro
  constructor
  · simp only [Mem.read8] at hr0 hr1
    simp only [Mem.read16]
    rw [hr0, ← h1, hr1]
    exact u16Byte_reassemble value
  · rw [h1] at hb1
    omega

/-- Eight-byte ownership determines the physical little-endian word and proves
the complete access is in bounds. The address equalities exclude UInt32
wraparound in the derived byte footprint. -/
theorem stateInterp_pointsTo_u64_facts [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (address : UInt32) (value : UInt64)
    (h1 : (address + 1).toNat = address.toNat + 1)
    (h2 : (address + 2).toNat = address.toNat + 2)
    (h3 : (address + 3).toNat = address.toNat + 3)
    (h4 : (address + 4).toNat = address.toNat + 4)
    (h5 : (address + 5).toNat = address.toNat + 5)
    (h6 : (address + 6).toNat = address.toNat + 6)
    (h7 : (address + 7).toNat = address.toNat + 7) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      pointsTo_u64 0 address value ==∗
      ⌜store.wasm.mem.read64 address = value ∧
        address.toNat + 8 ≤ store.wasm.mem.pages * 65536⌝ := by
  iintro ⟨Hstate, Hword⟩
  ihave Hword := (pointsTo_u64_eq 0 address value).mp $$ Hword
  icases Hword with ⟨H0, H1, H2, H3, H4, H5, H6, H7⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
<<<<<<< HEAD
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %exceptionσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hexceptions, Hruntime, Hhost, %Hfacts⟩
=======
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %runtimeModuleσ, %hostEnvσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, HruntimeModuleAuth, HruntimeModuleBigSep, HruntimeInstances, HinstanceAuth, HhostEnvAuth, Hstate_auth, %Hfacts⟩
>>>>>>> origin/main
  ihave %hg0 :
      ⌜get? σ ⟨0, address⟩ = some (some (u64Byte value 0))⌝ $$ [Hheap H0]
  · imod genHeap_valid $$ [$Hheap $H0] with %hg0
    ipureintro; exact hg0
  ihave %hg1 :
      ⌜get? σ ⟨0, address + 1⟩ = some (some (u64Byte value 1))⌝ $$ [Hheap H1]
  · imod genHeap_valid $$ [$Hheap $H1] with %hg1
    ipureintro; exact hg1
  ihave %hg2 :
      ⌜get? σ ⟨0, address + 2⟩ = some (some (u64Byte value 2))⌝ $$ [Hheap H2]
  · imod genHeap_valid $$ [$Hheap $H2] with %hg2
    ipureintro; exact hg2
  ihave %hg3 :
      ⌜get? σ ⟨0, address + 3⟩ = some (some (u64Byte value 3))⌝ $$ [Hheap H3]
  · imod genHeap_valid $$ [$Hheap $H3] with %hg3
    ipureintro; exact hg3
  ihave %hg4 :
      ⌜get? σ ⟨0, address + 4⟩ = some (some (u64Byte value 4))⌝ $$ [Hheap H4]
  · imod genHeap_valid $$ [$Hheap $H4] with %hg4
    ipureintro; exact hg4
  ihave %hg5 :
      ⌜get? σ ⟨0, address + 5⟩ = some (some (u64Byte value 5))⌝ $$ [Hheap H5]
  · imod genHeap_valid $$ [$Hheap $H5] with %hg5
    ipureintro; exact hg5
  ihave %hg6 :
      ⌜get? σ ⟨0, address + 6⟩ = some (some (u64Byte value 6))⌝ $$ [Hheap H6]
  · imod genHeap_valid $$ [$Hheap $H6] with %hg6
    ipureintro; exact hg6
  ihave %hg7 :
      ⌜get? σ ⟨0, address + 7⟩ = some (some (u64Byte value 7))⌝ $$ [Hheap H7]
  · imod genHeap_valid $$ [$Hheap $H7] with %hg7
    ipureintro; exact hg7
  have hr0 := fromResolver store Hfacts.1 address (u64Byte value 0) hg0
  have hr1 := fromResolver store Hfacts.1 (address + 1) (u64Byte value 1) hg1
  have hr2 := fromResolver store Hfacts.1 (address + 2) (u64Byte value 2) hg2
  have hr3 := fromResolver store Hfacts.1 (address + 3) (u64Byte value 3) hg3
  have hr4 := fromResolver store Hfacts.1 (address + 4) (u64Byte value 4) hg4
  have hr5 := fromResolver store Hfacts.1 (address + 5) (u64Byte value 5) hg5
  have hr6 := fromResolver store Hfacts.1 (address + 6) (u64Byte value 6) hg6
  have hr7 := fromResolver store Hfacts.1 (address + 7) (u64Byte value 7) hg7
  have hb7 := fromResolverBounds store Hfacts.2.1 (address + 7) (by simp [hg7])
  ipureintro
  constructor
  · simp only [Mem.read8] at hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7
    simp only [Mem.read64]
    rw [hr0, ← h1, hr1, ← h2, hr2, ← h3, hr3, ← h4, hr4,
      ← h5, hr5, ← h6, hr6, ← h7, hr7]
    exact u64Byte_reassemble value
  · rw [h7] at hb7
    omega

/-- Framed form of `stateInterp_pointsTo_u64_facts`. It returns both the
authoritative state interpretation and the word ownership, allowing a client
to establish physical facts for several disjoint words sequentially. -/
theorem stateInterp_pointsTo_u64_facts_frame [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (address : UInt32) (value : UInt64)
    (h1 : (address + 1).toNat = address.toNat + 1)
    (h2 : (address + 2).toNat = address.toNat + 2)
    (h3 : (address + 3).toNat = address.toNat + 3)
    (h4 : (address + 4).toNat = address.toNat + 4)
    (h5 : (address + 5).toNat = address.toNat + 5)
    (h6 : (address + 6).toNat = address.toNat + 6)
    (h7 : (address + 7).toNat = address.toNat + 7) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      pointsTo_u64 0 address value ==∗
      stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      pointsTo_u64 0 address value ∗
      ⌜store.wasm.mem.read64 address = value ∧
        address.toNat + 8 ≤ store.wasm.mem.pages * 65536⌝ := by
  iintro ⟨Hstate, Hword⟩
  ihave Hword := (pointsTo_u64_eq 0 address value).mp $$ Hword
  icases Hword with ⟨H0, H1, H2, H3, H4, H5, H6, H7⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
<<<<<<< HEAD
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %exceptionσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hexceptions, Hruntime, Hhost, %Hfacts⟩
=======
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %runtimeModuleσ, %hostEnvσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, HruntimeModuleAuth, HruntimeModuleBigSep, HruntimeInstances, HinstanceAuth, HhostEnvAuth, Hstate_auth, %Hfacts⟩
>>>>>>> origin/main
  ihave %hg0 :
      ⌜get? σ ⟨0, address⟩ = some (some (u64Byte value 0))⌝ $$ [Hheap H0]
  · imod genHeap_valid $$ [$Hheap $H0] with %hg0
    ipureintro; exact hg0
  ihave %hg1 :
      ⌜get? σ ⟨0, address + 1⟩ = some (some (u64Byte value 1))⌝ $$ [Hheap H1]
  · imod genHeap_valid $$ [$Hheap $H1] with %hg1
    ipureintro; exact hg1
  ihave %hg2 :
      ⌜get? σ ⟨0, address + 2⟩ = some (some (u64Byte value 2))⌝ $$ [Hheap H2]
  · imod genHeap_valid $$ [$Hheap $H2] with %hg2
    ipureintro; exact hg2
  ihave %hg3 :
      ⌜get? σ ⟨0, address + 3⟩ = some (some (u64Byte value 3))⌝ $$ [Hheap H3]
  · imod genHeap_valid $$ [$Hheap $H3] with %hg3
    ipureintro; exact hg3
  ihave %hg4 :
      ⌜get? σ ⟨0, address + 4⟩ = some (some (u64Byte value 4))⌝ $$ [Hheap H4]
  · imod genHeap_valid $$ [$Hheap $H4] with %hg4
    ipureintro; exact hg4
  ihave %hg5 :
      ⌜get? σ ⟨0, address + 5⟩ = some (some (u64Byte value 5))⌝ $$ [Hheap H5]
  · imod genHeap_valid $$ [$Hheap $H5] with %hg5
    ipureintro; exact hg5
  ihave %hg6 :
      ⌜get? σ ⟨0, address + 6⟩ = some (some (u64Byte value 6))⌝ $$ [Hheap H6]
  · imod genHeap_valid $$ [$Hheap $H6] with %hg6
    ipureintro; exact hg6
  ihave %hg7 :
      ⌜get? σ ⟨0, address + 7⟩ = some (some (u64Byte value 7))⌝ $$ [Hheap H7]
  · imod genHeap_valid $$ [$Hheap $H7] with %hg7
    ipureintro; exact hg7
  have hr0 := fromResolver store Hfacts.1 address (u64Byte value 0) hg0
  have hr1 := fromResolver store Hfacts.1 (address + 1) (u64Byte value 1) hg1
  have hr2 := fromResolver store Hfacts.1 (address + 2) (u64Byte value 2) hg2
  have hr3 := fromResolver store Hfacts.1 (address + 3) (u64Byte value 3) hg3
  have hr4 := fromResolver store Hfacts.1 (address + 4) (u64Byte value 4) hg4
  have hr5 := fromResolver store Hfacts.1 (address + 5) (u64Byte value 5) hg5
  have hr6 := fromResolver store Hfacts.1 (address + 6) (u64Byte value 6) hg6
  have hr7 := fromResolver store Hfacts.1 (address + 7) (u64Byte value 7) hg7
  have hb7 := fromResolverBounds store Hfacts.2.1 (address + 7) (by simp [hg7])
  have hread : store.wasm.mem.read64 address = value := by
    simp only [Mem.read8] at hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7
    simp only [Mem.read64]
    rw [hr0, ← h1, hr1, ← h2, hr2, ← h3, hr3, ← h4, hr4,
      ← h5, hr5, ← h6, hr6, ← h7, hr7]
    exact u64Byte_reassemble value
  have hbound :
      address.toNat + 8 ≤ store.wasm.mem.pages * 65536 := by
    rw [h7] at hb7
    omega
  imodintro
<<<<<<< HEAD
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments Hexceptions Hruntime Hhost]
=======
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth HhostEnvAuth Hstate_auth]
>>>>>>> origin/main
  · iapply (stateInterp_eq store steps observations threads).mpr
    iexists σ
    iexists globalσ
    iexists dataSegmentσ
    iexists tableσ
    iexists elementSegmentσ
<<<<<<< HEAD
    iexists exceptionσ
=======
    iexists runtimeModuleσ
    iexists hostEnvσ
>>>>>>> origin/main
    iframe
    ipureintro
    exact Hfacts
  · isplitl [H0 H1 H2 H3 H4 H5 H6 H7]
    · iapply (pointsTo_u64_eq 0 address value).mpr
      iframe
    · ipureintro
      exact ⟨hread, hbound⟩

theorem stateInterp_store8 [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (address : UInt32) (oldValue newValue : UInt8)
    (hbound : address.toNat < store.wasm.mem.pages * 65536) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        ⟨0, address⟩ (DFrac.own 1) (some oldValue) ==∗
      stateInterp (GF := WasmHeapGF α)
        { store with wasm :=
            { store.wasm with mem := store.wasm.mem.write8 address newValue } }
        steps observations threads ∗
      pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        ⟨0, address⟩ (DFrac.own 1) (some newValue) := by
  iintro ⟨Hstate, Hpointsto⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
<<<<<<< HEAD
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %exceptionσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hexceptions, Hruntime, Hhost, %Hfacts⟩
  imod genHeap_update (v₂ := some newValue) $$ [$Hheap $Hpointsto] with
    ⟨Hheap, Hpointsto⟩
  imodintro
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments Hexceptions Hruntime Hhost]
=======
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %runtimeModuleσ, %hostEnvσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, HruntimeModuleAuth, HruntimeModuleBigSep, HruntimeInstances, HinstanceAuth, HhostEnvAuth, Hstate_auth, %Hfacts⟩
  imod genHeap_update (v₂ := some newValue) $$ [$Hheap $Hpointsto] with
    ⟨Hheap, Hpointsto⟩
  imodintro
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth HhostEnvAuth Hstate_auth]
>>>>>>> origin/main
  · iapply (stateInterp_eq
      { store with wasm :=
          { store.wasm with mem := store.wasm.mem.write8 address newValue } }
      steps observations threads).mpr
    iexists insert σ ⟨0, address⟩ (some newValue)
    iexists globalσ
    iexists dataSegmentσ
    iexists tableσ
    iexists elementSegmentσ
<<<<<<< HEAD
    iexists exceptionσ
    iframe Hheap Hglobals Hsegments Htables HelementSegments Hexceptions Hruntime Hhost
=======
    iexists runtimeModuleσ
    iexists hostEnvσ
    iframe Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth HhostEnvAuth Hstate_auth
>>>>>>> origin/main
    ipureintro
    have h_ag := store_sound σ (storeResolve store) 0 store.wasm.mem address newValue
        (storeResolve_zero store) Hfacts.1
    rw [storeResolve_update_mem0] at h_ag
    have h_bn := store_inBounds σ (storeResolve store) 0 store.wasm.mem address newValue
        (storeResolve_zero store) Hfacts.2.1 hbound
    rw [storeResolve_update_mem0] at h_bn
    exact ⟨h_ag, h_bn, Hfacts.2.2⟩
  · iexact Hpointsto

theorem stateInterp_pointsTo_u16_facts [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (address value : UInt32)
    (h1 : (address + 1).toNat = address.toNat + 1) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      pointsTo_u16 0 address value ==∗
      ⌜address.toNat + 2 ≤ store.wasm.mem.pages * 65536⌝ := by
  iintro ⟨Hstate, Hword⟩
  ihave Hword := (pointsTo_u16_eq 0 address value).mp $$ Hword
  icases Hword with ⟨H0, H1⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %runtimeModuleσ, %hostEnvσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, HruntimeModuleAuth, HruntimeModuleBigSep, HruntimeInstances, HinstanceAuth, HhostEnvAuth, Hstate_auth, %Hfacts⟩
  ihave %hg1 :
      ⌜get? σ ⟨0, address + 1⟩ = some (some (u32Byte value 1))⌝ $$ [Hheap H1]
  · imod genHeap_valid $$ [$Hheap $H1] with %hg1
    ipureintro
    exact hg1
  have hb1 := fromResolverBounds store Hfacts.2.1 (address + 1) (by simp [hg1])
  ipureintro
  rw [h1] at hb1
  omega

theorem stateInterp_store16 [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (address oldValue newValue : UInt32)
    (h1 : (address + 1).toNat = address.toNat + 1)
    (hbound : address.toNat + 2 ≤ store.wasm.mem.pages * 65536) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      pointsTo_u16 0 address oldValue ==∗
      stateInterp (GF := WasmHeapGF α)
        { store with wasm :=
            { store.wasm with mem := store.wasm.mem.write16 address newValue } }
        steps observations threads ∗
      pointsTo_u16 0 address newValue := by
  iintro ⟨Hstate, Hword⟩
  ihave Hword := (pointsTo_u16_eq 0 address oldValue).mp $$ Hword
  icases Hword with ⟨H0, H1⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %runtimeModuleσ, %hostEnvσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, HruntimeModuleAuth, HruntimeModuleBigSep, HruntimeInstances, HinstanceAuth, HhostEnvAuth, Hstate_auth, %Hfacts⟩
  imod genHeap_update (v₂ := some (u32Byte newValue 0)) $$
      [$Hheap $H0] with ⟨Hheap, H0⟩
  imod genHeap_update (v₂ := some (u32Byte newValue 1)) $$
      [$Hheap $H1] with ⟨Hheap, H1⟩
  imodintro
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth HhostEnvAuth Hstate_auth]
  · iapply (stateInterp_eq
      { store with wasm :=
          { store.wasm with mem := store.wasm.mem.write16 address newValue } }
      steps observations threads).mpr
    iexists store16Heap σ 0 address newValue
    iexists globalσ
    iexists dataSegmentσ
    iexists tableσ
    iexists elementSegmentσ
    iexists runtimeModuleσ
    iexists hostEnvσ
    unfold store16Heap
    iframe Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth HhostEnvAuth Hstate_auth
    ipureintro
    have h_ag := store16_sound σ (storeResolve store) 0 store.wasm.mem address newValue
        (storeResolve_zero store) h1 Hfacts.1
    rw [storeResolve_update_mem0] at h_ag
    have h_bn := store16_inBounds σ (storeResolve store) 0 store.wasm.mem address newValue
        (storeResolve_zero store) h1 Hfacts.2.1 hbound
    rw [storeResolve_update_mem0] at h_bn
    exact ⟨h_ag, h_bn, Hfacts.2.2⟩
  · iapply (pointsTo_u16_eq 0 address newValue).mpr
    iframe

theorem stateInterp_store32 [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (address oldValue newValue : UInt32)
    (h1 : (address + 1).toNat = address.toNat + 1)
    (h2 : (address + 2).toNat = address.toNat + 2)
    (h3 : (address + 3).toNat = address.toNat + 3)
    (hbound : address.toNat + 4 ≤ store.wasm.mem.pages * 65536) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      pointsTo_u32 0 address oldValue ==∗
      stateInterp (GF := WasmHeapGF α)
        { store with wasm :=
            { store.wasm with mem := store.wasm.mem.write32 address newValue } }
        steps observations threads ∗
      pointsTo_u32 0 address newValue := by
  iintro ⟨Hstate, Hword⟩
  ihave Hword := (pointsTo_u32_eq 0 address oldValue).mp $$ Hword
  icases Hword with ⟨H0, H1, H2, H3⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
<<<<<<< HEAD
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %exceptionσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hexceptions, Hruntime, Hhost, %Hfacts⟩
=======
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %runtimeModuleσ, %hostEnvσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, HruntimeModuleAuth, HruntimeModuleBigSep, HruntimeInstances, HinstanceAuth, HhostEnvAuth, Hstate_auth, %Hfacts⟩
>>>>>>> origin/main
  imod genHeap_update (v₂ := some (u32Byte newValue 0)) $$
      [$Hheap $H0] with ⟨Hheap, H0⟩
  imod genHeap_update (v₂ := some (u32Byte newValue 1)) $$
      [$Hheap $H1] with ⟨Hheap, H1⟩
  imod genHeap_update (v₂ := some (u32Byte newValue 2)) $$
      [$Hheap $H2] with ⟨Hheap, H2⟩
  imod genHeap_update (v₂ := some (u32Byte newValue 3)) $$
      [$Hheap $H3] with ⟨Hheap, H3⟩
  imodintro
<<<<<<< HEAD
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments Hexceptions Hruntime Hhost]
=======
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth HhostEnvAuth Hstate_auth]
>>>>>>> origin/main
  · iapply (stateInterp_eq
      { store with wasm :=
          { store.wasm with mem := store.wasm.mem.write32 address newValue } }
      steps observations threads).mpr
    iexists store32Heap σ 0 address newValue
    iexists globalσ
    iexists dataSegmentσ
    iexists tableσ
    iexists elementSegmentσ
<<<<<<< HEAD
    iexists exceptionσ
    iframe Hheap Hglobals Hsegments Htables HelementSegments Hexceptions Hruntime Hhost
=======
    iexists runtimeModuleσ
    iexists hostEnvσ
    unfold store32Heap
    iframe Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth HhostEnvAuth Hstate_auth
>>>>>>> origin/main
    ipureintro
    have h_ag := store32_sound σ (storeResolve store) 0 store.wasm.mem address newValue
        (storeResolve_zero store) h1 h2 h3 Hfacts.1
    rw [storeResolve_update_mem0] at h_ag
    have h_bn := store32_inBounds σ (storeResolve store) 0 store.wasm.mem address newValue
        (storeResolve_zero store) h1 h2 h3 Hfacts.2.1 hbound
    rw [storeResolve_update_mem0] at h_bn
    exact ⟨h_ag, h_bn, Hfacts.2.2⟩
  · iapply (pointsTo_u32_eq 0 address newValue).mpr
    iframe

theorem stateInterp_store16 [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (address oldValue newValue : UInt32)
    (h1 : (address + 1).toNat = address.toNat + 1)
    (hbound : address.toNat + 2 ≤ store.wasm.mem.pages * 65536) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      pointsTo_u16 address oldValue ==∗
      stateInterp (GF := WasmHeapGF α)
        { store with wasm :=
            { store.wasm with mem := store.wasm.mem.write16 address newValue } }
        steps observations threads ∗
      pointsTo_u16 address newValue := by
  iintro ⟨Hstate, Hword⟩
  ihave Hword := (pointsTo_u16_eq address oldValue).mp $$ Hword
  icases Hword with ⟨H0, H1⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %exceptionσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hexceptions, Hruntime, Hhost, %Hfacts⟩
  imod genHeap_update (v₂ := some (u16Byte newValue 0)) $$
      [$Hheap $H0] with ⟨Hheap, H0⟩
  imod genHeap_update (v₂ := some (u16Byte newValue 1)) $$
      [$Hheap $H1] with ⟨Hheap, H1⟩
  imodintro
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments Hexceptions Hruntime Hhost]
  · iapply (stateInterp_eq
      { store with wasm :=
          { store.wasm with mem := store.wasm.mem.write16 address newValue } }
      steps observations threads).mpr
    iexists insert (insert σ address (some (u16Byte newValue 0)))
      (address + 1) (some (u16Byte newValue 1))
    iexists globalσ
    iexists dataSegmentσ
    iexists tableσ
    iexists elementSegmentσ
    iexists exceptionσ
    iframe Hheap Hglobals Hsegments Htables HelementSegments Hexceptions Hruntime Hhost
    ipureintro
    exact ⟨
        (store16_sound σ store.wasm.mem address newValue h1 Hfacts.1)
        , (store16_inBounds σ store.wasm.mem address newValue h1
          Hfacts.2.1 hbound)
        , Hfacts.2.2⟩
  · iapply (pointsTo_u16_eq address newValue).mpr
    iframe

theorem stateInterp_store64 [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (address : UInt32) (oldValue newValue : UInt64)
    (h1 : (address + 1).toNat = address.toNat + 1)
    (h2 : (address + 2).toNat = address.toNat + 2)
    (h3 : (address + 3).toNat = address.toNat + 3)
    (h4 : (address + 4).toNat = address.toNat + 4)
    (h5 : (address + 5).toNat = address.toNat + 5)
    (h6 : (address + 6).toNat = address.toNat + 6)
    (h7 : (address + 7).toNat = address.toNat + 7)
    (hbound : address.toNat + 8 ≤ store.wasm.mem.pages * 65536) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      pointsTo_u64 0 address oldValue ==∗
      stateInterp (GF := WasmHeapGF α)
        { store with wasm :=
            { store.wasm with mem := store.wasm.mem.write64 address newValue } }
        steps observations threads ∗
      pointsTo_u64 0 address newValue := by
  iintro ⟨Hstate, Hword⟩
  ihave Hword := (pointsTo_u64_eq 0 address oldValue).mp $$ Hword
  icases Hword with ⟨H0, H1, H2, H3, H4, H5, H6, H7⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
<<<<<<< HEAD
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %exceptionσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hexceptions, Hruntime, Hhost, %Hfacts⟩
=======
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %runtimeModuleσ, %hostEnvσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, HruntimeModuleAuth, HruntimeModuleBigSep, HruntimeInstances, HinstanceAuth, HhostEnvAuth, Hstate_auth, %Hfacts⟩
>>>>>>> origin/main
  imod genHeap_update (v₂ := some (u64Byte newValue 0)) $$
      [$Hheap $H0] with ⟨Hheap, H0⟩
  imod genHeap_update (v₂ := some (u64Byte newValue 1)) $$
      [$Hheap $H1] with ⟨Hheap, H1⟩
  imod genHeap_update (v₂ := some (u64Byte newValue 2)) $$
      [$Hheap $H2] with ⟨Hheap, H2⟩
  imod genHeap_update (v₂ := some (u64Byte newValue 3)) $$
      [$Hheap $H3] with ⟨Hheap, H3⟩
  imod genHeap_update (v₂ := some (u64Byte newValue 4)) $$
      [$Hheap $H4] with ⟨Hheap, H4⟩
  imod genHeap_update (v₂ := some (u64Byte newValue 5)) $$
      [$Hheap $H5] with ⟨Hheap, H5⟩
  imod genHeap_update (v₂ := some (u64Byte newValue 6)) $$
      [$Hheap $H6] with ⟨Hheap, H6⟩
  imod genHeap_update (v₂ := some (u64Byte newValue 7)) $$
      [$Hheap $H7] with ⟨Hheap, H7⟩
  imodintro
<<<<<<< HEAD
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments Hexceptions Hruntime Hhost]
=======
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth HhostEnvAuth Hstate_auth]
>>>>>>> origin/main
  · iapply (stateInterp_eq
      { store with wasm :=
          { store.wasm with mem := store.wasm.mem.write64 address newValue } }
      steps observations threads).mpr
    iexists store64Heap σ 0 address newValue
    iexists globalσ
    iexists dataSegmentσ
    iexists tableσ
    iexists elementSegmentσ
<<<<<<< HEAD
    iexists exceptionσ
    unfold store64Heap
    iframe Hheap Hglobals Hsegments Htables HelementSegments Hexceptions Hruntime Hhost
=======
    iexists runtimeModuleσ
    iexists hostEnvσ
    unfold store64Heap
    iframe Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth HhostEnvAuth Hstate_auth
>>>>>>> origin/main
    ipureintro
    have h_ag := store64_sound σ (storeResolve store) 0 store.wasm.mem address newValue
        (storeResolve_zero store) h1 h2 h3 h4 h5 h6 h7 Hfacts.1
    rw [storeResolve_update_mem0] at h_ag
    have h_bn := store64_inBounds σ (storeResolve store) 0 store.wasm.mem address newValue
        (storeResolve_zero store) h1 h2 h3 h4 h5 h6 h7 Hfacts.2.1 hbound
    rw [storeResolve_update_mem0] at h_bn
    exact ⟨h_ag, h_bn, Hfacts.2.2⟩
  · iapply (pointsTo_u64_eq 0 address newValue).mpr
    iframe

/-- Successful memory growth preserves the authoritative byte heap unchanged:
physical bytes are identical and every previously owned address remains in
bounds because the page count only increases. -/
theorem stateInterp_memoryGrow [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (delta : UInt32) (memory : Mem) (previousPages : Nat)
    (hgrow : store.wasm.mem.grow delta store.runtime.currentModule.memoryCap =
      some (memory, previousPages)) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ⊢
      stateInterp (GF := WasmHeapGF α)
        { store with wasm := { store.wasm with mem := memory } }
        steps observations threads := by
  iintro Hstate
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
<<<<<<< HEAD
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %exceptionσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hexceptions, Hruntime, Hhost, %Hfacts⟩
=======
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %runtimeModuleσ, %hostEnvσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, HruntimeModuleAuth, HruntimeModuleBigSep, HruntimeInstances, HinstanceAuth, HhostEnvAuth, Hstate_auth, %Hfacts⟩
>>>>>>> origin/main
  iapply (stateInterp_eq
    { store with wasm := { store.wasm with mem := memory } }
    steps observations threads).mpr
  iexists σ
  iexists globalσ
  iexists dataSegmentσ
  iexists tableσ
  iexists elementSegmentσ
<<<<<<< HEAD
  iexists exceptionσ
  iframe Hheap Hglobals Hsegments Htables HelementSegments Hexceptions Hruntime Hhost
=======
  iexists runtimeModuleσ
  iexists hostEnvσ
  iframe Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth HhostEnvAuth Hstate_auth
>>>>>>> origin/main
  ipureintro
  have h_ag := grow_sound σ (storeResolve store) 0 store.wasm.mem memory delta
      store.runtime.currentModule.memoryCap previousPages hgrow (storeResolve_zero store) Hfacts.1
  rw [storeResolve_update_mem0] at h_ag
  have h_bn := grow_inBounds σ (storeResolve store) 0 store.wasm.mem memory delta
      store.runtime.currentModule.memoryCap previousPages hgrow (storeResolve_zero store) Hfacts.2.1
  rw [storeResolve_update_mem0] at h_bn
  exact ⟨h_ag, h_bn, Hfacts.2.2⟩

/-- After a host-call `.Return`, the store's `wasm` field is replaced by the
host-returned store. `runtime` is unchanged and the host's mutable state is
unchanged (`h_host`), so all ghost authorities are preserved; agreement must be
re-established by the caller for each component that the host may have
modified. -/
theorem stateInterp_hostCallReturn [WasmSmallStepGS hlc α]
    (store : MachineStore α) (newWasm : Store α)
    (steps : Nat) (observations : List StepKind) (threads : Nat)
    (h_host : newWasm.host = store.wasm.host) :
    (∀ σ, heapAgreesWithMem σ (storeResolve store) →
          heapAgreesWithMem σ (storeResolve { store with wasm := newWasm })) →
    (∀ σ, heapAddressesInBounds σ (storeResolve store) →
          heapAddressesInBounds σ (storeResolve { store with wasm := newWasm })) →
    (∀ σ, globalHeapAgrees σ store.wasm.globals →
          globalHeapAgrees σ newWasm.globals) →
    (∀ σ, dataSegmentHeapAgrees σ store.wasm.dataSegments →
          dataSegmentHeapAgrees σ newWasm.dataSegments) →
    (∀ σ, tableHeapAgrees σ store.wasm.tables →
          tableHeapAgrees σ newWasm.tables) →
    (∀ σ, elementSegmentHeapAgrees σ store.wasm.elementSegments →
          elementSegmentHeapAgrees σ newWasm.elementSegments) →
    stateInterp (GF := WasmHeapGF α) store steps observations threads ⊢
      stateInterp (GF := WasmHeapGF α) { store with wasm := newWasm }
        steps observations threads := by
  intro hMem hBounds hGlobals hData hTables hElems
  iintro Hstate
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %runtimeModuleσ, %hostEnvσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, HruntimeModuleAuth, HruntimeModuleBigSep, HruntimeInstances, HinstanceAuth, HhostEnvAuth, Hstate_auth, %Hfacts⟩
  iapply (stateInterp_eq
    { store with wasm := newWasm }
    steps observations threads).mpr
  iexists σ
  iexists globalσ
  iexists dataSegmentσ
  iexists tableσ
  iexists elementSegmentσ
  iexists runtimeModuleσ
  iexists hostEnvσ
  ihave Hstate_auth' : hostStateAuth newWasm.host $$ [Hstate_auth]
  · rw [h_host]; iexact Hstate_auth
  iframe Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth HhostEnvAuth Hstate_auth'
  ipureintro
  exact ⟨hMem σ Hfacts.1, hBounds σ Hfacts.2.1, hGlobals globalσ Hfacts.2.2.1,
    hData dataSegmentσ Hfacts.2.2.2.1, hTables tableσ Hfacts.2.2.2.2.1,
    hElems elementSegmentσ Hfacts.2.2.2.2.2.1, Hfacts.2.2.2.2.2.2.1, Hfacts.2.2.2.2.2.2.2⟩

private theorem currentInstanceAuth_ownN_agree {α : Type} [gs : WasmInstanceGS α]
    (id : ModuleInstanceId) (n : Nat) :
    currentInstanceAuth (α := α) id ∗ currentInstanceOwnN n ⊢ ⌜id.id = n⌝ := by
  unfold currentInstanceAuth; exact currentInstanceOwnN_agree id.id n

/-- Extract the host env agreement from stateInterp by combining with a
`hostEnvOwn` witness. -/
theorem stateInterp_hostEnv [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (instanceId : Nat) (env : HostEnv α) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      currentInstanceOwnN (α := α) instanceId ∗ hostEnvOwn instanceId env ==∗
      ⌜store.runtime.currentHost = env⌝ := by
  iintro ⟨Hstate, Hid, Henv_expected⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %runtimeModuleσ, %hostEnvσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, HruntimeModuleAuth, HruntimeModuleBigSep, HruntimeInstances, HinstanceAuth, HhostEnvAuth, Hstate_auth, %Hfacts⟩
  icombine HinstanceAuth Hid as Hentry
  ihave %hentry := currentInstanceAuth_ownN_agree store.runtime.entry instanceId $$ Hentry
  ihave %hlookup := hostEnvOwn_lookup $$ HhostEnvAuth Henv_expected
  ipureintro
  have hinst := Hfacts.2.2.2.2.2.2.2 instanceId env hlookup
  rw [← hentry] at hinst
  simp only [RuntimeEnv.currentHost, RuntimeEnv.currentInstance]
  rcases h : store.runtime.instances[store.runtime.entry.id]? with _ | inst
  · rw [h, Option.map_none] at hinst; simp at hinst
  · rw [h, Option.map_some, Option.some.injEq] at hinst
    have hget : store.runtime.instances[store.runtime.entry.id]! = inst := by
      simp only [getElem!_def, h]
    rw [hget]; exact hinst

/-- Four-byte fill update used by the manual memory example. Ownership of the
whole affected range is required and is updated atomically. -/
theorem stateInterp_fill16_four_AB [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (oldWord : UInt32)
    (hbound : 20 ≤ store.wasm.mem.pages * 65536) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      pointsTo_u32 0 16 oldWord ==∗
      stateInterp (GF := WasmHeapGF α)
        { store with wasm :=
            { store.wasm with mem := store.wasm.mem.fill 16 4 0xAB } }
        steps observations threads ∗
      pointsTo_u32 0 16 0xABABABAB := by
  iintro ⟨Hstate, Hword⟩
  imod stateInterp_store32 store steps observations threads
      16 oldWord 0xABABABAB rfl rfl rfl hbound $$
      [$Hstate $Hword] with ⟨Hstate, Hword⟩
  imodintro
  isplitl [Hstate]
  · rw [fill16_four_AB_eq_write32]
    iexact Hstate
  · iexact Hword

/-- Four-byte passive-segment initialization used by the manual Iris example.
The segment itself is read-only during `memory.init`; only the destination
word changes. -/
theorem stateInterp_init16_four [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (oldWord : UInt32)
    (hbound : 20 ≤ store.wasm.mem.pages * 65536) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      pointsTo_u32 0 16 oldWord ==∗
      stateInterp (GF := WasmHeapGF α)
        { store with wasm :=
            { store.wasm with mem :=
                store.wasm.mem.writeBytesFrom 16 [1, 2, 3, 4] 0 4 } }
        steps observations threads ∗
      pointsTo_u32 0 16 0x04030201 := by
  iintro ⟨Hstate, Hword⟩
  imod stateInterp_store32 store steps observations threads
      16 oldWord 0x04030201 rfl rfl rfl hbound $$
      [$Hstate $Hword] with ⟨Hstate, Hword⟩
  imodintro
  isplitl [Hstate]
  · rw [init16_four_eq_write32]
    iexact Hstate
  · iexact Hword

/-- Aligned four-byte copy used by the manual Iris example. Source ownership
is framed, while complete destination ownership is updated atomically. -/
theorem stateInterp_copy8_zero_four [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (oldDestination : UInt32) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      pointsTo_u32 0 0 0x04030201 ∗ pointsTo_u32 0 8 oldDestination ==∗
      stateInterp (GF := WasmHeapGF α)
        { store with wasm :=
            { store.wasm with mem := store.wasm.mem.copy 8 0 4 } }
        steps observations threads ∗
      pointsTo_u32 0 0 0x04030201 ∗ pointsTo_u32 0 8 0x04030201 := by
  iintro ⟨Hstate, Hsource, Hdestination⟩
  ihave %HsourceFacts :
      ⌜store.wasm.mem.read32 0 = 0x04030201 ∧
        4 ≤ store.wasm.mem.pages * 65536⌝ $$ [Hstate Hsource]
  · imod stateInterp_pointsTo_u32_facts store steps observations threads
      0 0x04030201 rfl rfl rfl $$ [$Hstate $Hsource] with %HsourceFacts
    ipureintro
    exact HsourceFacts
  ihave %HdestinationFacts :
      ⌜store.wasm.mem.read32 8 = oldDestination ∧
        12 ≤ store.wasm.mem.pages * 65536⌝ $$ [Hstate Hdestination]
  · imod stateInterp_pointsTo_u32_facts store steps observations threads
      8 oldDestination rfl rfl rfl $$ [$Hstate $Hdestination]
      with %HdestinationFacts
    ipureintro
    exact HdestinationFacts
  imod stateInterp_store32 store steps observations threads
      8 oldDestination 0x04030201 rfl rfl rfl HdestinationFacts.2 $$
      [$Hstate $Hdestination] with ⟨Hstate, Hdestination⟩
  imodintro
  isplitl [Hstate]
  · rw [copy8_zero_four_eq_write32 store.wasm.mem HsourceFacts.1]
    iexact Hstate
  · iframe

/-- Overlapping four-byte copy from address 0 to address 2.  One eight-byte
owner covers the overlapping source and destination, and the ghost update
uses the pre-copy source bytes, matching WebAssembly memmove semantics. -/
theorem stateInterp_copy2_zero_four [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      pointsTo_u64 0 0 0x8877665544332211 ==∗
      stateInterp (GF := WasmHeapGF α)
        { store with wasm :=
            { store.wasm with mem := store.wasm.mem.copy 2 0 4 } }
        steps observations threads ∗
      pointsTo_u64 0 0 0x8877443322112211 := by
  iintro ⟨Hstate, Hword⟩
  imod stateInterp_pointsTo_u64_facts_frame
      store steps observations threads
      0 0x8877665544332211 rfl rfl rfl rfl rfl rfl rfl $$
      [$Hstate $Hword] with ⟨Hstate, Hword, %Hfacts⟩
  ihave Hword :=
    (pointsTo_u64_eq 0 0 0x8877665544332211).mp $$ Hword
  icases Hword with ⟨H0, H1, H2, H3, H4, H5, H6, H7⟩
  ihave H2At :
      pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        ⟨0, 2⟩ (DFrac.own 1) (some (u64Byte 0x8877665544332211 2)) $$ [H2]
  · rw [show (⟨0, (0 : UInt32) + 2⟩ : MemoryKey) = ⟨0, 2⟩ by decide]
    iexact H2
  ihave H3At :
      pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        ⟨0, 3⟩ (DFrac.own 1) (some (u64Byte 0x8877665544332211 3)) $$ [H3]
  · rw [show (⟨0, (0 : UInt32) + 3⟩ : MemoryKey) = ⟨0, 3⟩ by decide]
    iexact H3
  ihave H4At :
      pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        ⟨0, 4⟩ (DFrac.own 1) (some (u64Byte 0x8877665544332211 4)) $$ [H4]
  · rw [show (⟨0, (0 : UInt32) + 4⟩ : MemoryKey) = ⟨0, 4⟩ by decide]
    iexact H4
  ihave H5At :
      pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        ⟨0, 5⟩ (DFrac.own 1) (some (u64Byte 0x8877665544332211 5)) $$ [H5]
  · rw [show (⟨0, (0 : UInt32) + 5⟩ : MemoryKey) = ⟨0, 5⟩ by decide]
    iexact H5
  imod stateInterp_store8 store steps observations threads
      2 (u64Byte 0x8877665544332211 2) 0x11 (by
        simp only [UInt32.toNat_ofNat] at Hfacts ⊢
        omega) $$
      [$Hstate $H2At] with ⟨Hstate, H2⟩
  imod stateInterp_store8
      { store with wasm :=
          { store.wasm with mem := store.wasm.mem.write8 2 0x11 } }
      steps observations threads 3
        (u64Byte 0x8877665544332211 3) 0x22 (by
        simp only [Mem.write8]
        simp only [UInt32.toNat_ofNat] at Hfacts ⊢
        omega) $$ [$Hstate $H3At] with ⟨Hstate, H3⟩
  imod stateInterp_store8
      { store with wasm :=
          { store.wasm with mem :=
              (store.wasm.mem.write8 2 0x11).write8 3 0x22 } }
      steps observations threads 4
        (u64Byte 0x8877665544332211 4) 0x33 (by
        simp only [Mem.write8]
        simp only [UInt32.toNat_ofNat] at Hfacts ⊢
        omega) $$ [$Hstate $H4At] with ⟨Hstate, H4⟩
  imod stateInterp_store8
      { store with wasm :=
          { store.wasm with mem :=
              ((store.wasm.mem.write8 2 0x11).write8 3 0x22).write8 4 0x33 } }
      steps observations threads 5
        (u64Byte 0x8877665544332211 5) 0x44 (by
        simp only [Mem.write8]
        simp only [UInt32.toNat_ofNat] at Hfacts ⊢
        omega) $$ [$Hstate $H5At] with ⟨Hstate, H5⟩
  imodintro
  isplitl [Hstate]
  · rw [copy2_zero_four_eq_write64 store.wasm.mem Hfacts.1]
    iexact Hstate
  · iapply (pointsTo_u64_eq 0 0 0x8877443322112211).mpr
    rw [show u64Byte 0x8877443322112211 0 =
        u64Byte 0x8877665544332211 0 by decide]
    rw [show u64Byte 0x8877443322112211 1 =
        u64Byte 0x8877665544332211 1 by decide]
    rw [show u64Byte 0x8877443322112211 2 = (0x11 : UInt8) by decide]
    rw [show u64Byte 0x8877443322112211 3 = (0x22 : UInt8) by decide]
    rw [show u64Byte 0x8877443322112211 4 = (0x33 : UInt8) by decide]
    rw [show u64Byte 0x8877443322112211 5 = (0x44 : UInt8) by decide]
    rw [show u64Byte 0x8877443322112211 6 =
        u64Byte 0x8877665544332211 6 by decide]
    rw [show u64Byte 0x8877443322112211 7 =
        u64Byte 0x8877665544332211 7 by decide]
    simp only [UInt32.reduceAdd]
    iframe

theorem stateInterp_writeV128 [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (addr : UInt32) (lo_old hi_old lo hi : UInt64)
    (hnowrap : addr.toNat + 16 < 4294967296)
    (hbound : addr.toNat + 16 ≤ store.wasm.mem.pages * 65536) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      pointsTo_u64 addr lo_old ∗ pointsTo_u64 (addr + 8) hi_old ==∗
      stateInterp (GF := WasmHeapGF α)
        { store with wasm := { store.wasm with mem :=
            (store.wasm.mem.write64 addr lo).write64 (addr + 8) hi } }
        steps observations threads ∗
      pointsTo_u64 addr lo ∗ pointsTo_u64 (addr + 8) hi := by
  have hbound_lo : addr.toNat + 8 ≤ store.wasm.mem.pages * 65536 := by omega
  have h1 : (addr + 1).toNat = addr.toNat + 1 := by
    simp only [UInt32.toNat_add, show (1 : UInt32).toNat = 1 from rfl]; omega
  have h2 : (addr + 2).toNat = addr.toNat + 2 := by
    simp only [UInt32.toNat_add, show (2 : UInt32).toNat = 2 from rfl]; omega
  have h3 : (addr + 3).toNat = addr.toNat + 3 := by
    simp only [UInt32.toNat_add, show (3 : UInt32).toNat = 3 from rfl]; omega
  have h4 : (addr + 4).toNat = addr.toNat + 4 := by
    simp only [UInt32.toNat_add, show (4 : UInt32).toNat = 4 from rfl]; omega
  have h5 : (addr + 5).toNat = addr.toNat + 5 := by
    simp only [UInt32.toNat_add, show (5 : UInt32).toNat = 5 from rfl]; omega
  have h6 : (addr + 6).toNat = addr.toNat + 6 := by
    simp only [UInt32.toNat_add, show (6 : UInt32).toNat = 6 from rfl]; omega
  have h7 : (addr + 7).toNat = addr.toNat + 7 := by
    simp only [UInt32.toNat_add, show (7 : UInt32).toNat = 7 from rfl]; omega
  have h8 : (addr + 8).toNat = addr.toNat + 8 := by
    simp only [UInt32.toNat_add, show (8 : UInt32).toNat = 8 from rfl]; omega
  have h81 : (addr + 8 + 1).toNat = (addr + 8).toNat + 1 := by
    simp only [UInt32.toNat_add, show (1 : UInt32).toNat = 1 from rfl,
               show (8 : UInt32).toNat = 8 from rfl]; omega
  have h82 : (addr + 8 + 2).toNat = (addr + 8).toNat + 2 := by
    simp only [UInt32.toNat_add, show (2 : UInt32).toNat = 2 from rfl,
               show (8 : UInt32).toNat = 8 from rfl]; omega
  have h83 : (addr + 8 + 3).toNat = (addr + 8).toNat + 3 := by
    simp only [UInt32.toNat_add, show (3 : UInt32).toNat = 3 from rfl,
               show (8 : UInt32).toNat = 8 from rfl]; omega
  have h84 : (addr + 8 + 4).toNat = (addr + 8).toNat + 4 := by
    simp only [UInt32.toNat_add, show (4 : UInt32).toNat = 4 from rfl,
               show (8 : UInt32).toNat = 8 from rfl]; omega
  have h85 : (addr + 8 + 5).toNat = (addr + 8).toNat + 5 := by
    simp only [UInt32.toNat_add, show (5 : UInt32).toNat = 5 from rfl,
               show (8 : UInt32).toNat = 8 from rfl]; omega
  have h86 : (addr + 8 + 6).toNat = (addr + 8).toNat + 6 := by
    simp only [UInt32.toNat_add, show (6 : UInt32).toNat = 6 from rfl,
               show (8 : UInt32).toNat = 8 from rfl]; omega
  have h87 : (addr + 8 + 7).toNat = (addr + 8).toNat + 7 := by
    simp only [UInt32.toNat_add, show (7 : UInt32).toNat = 7 from rfl,
               show (8 : UInt32).toNat = 8 from rfl]; omega
  let store1 := { store with wasm := { store.wasm with mem := store.wasm.mem.write64 addr lo } }
  have hbound_hi : (addr + 8).toNat + 8 ≤ store1.wasm.mem.pages * 65536 := by
    show (addr + 8).toNat + 8 ≤ store.wasm.mem.pages * 65536; rw [h8]; omega
  iintro ⟨Hσ, Hlo, Hhi⟩
  imod stateInterp_store64 store steps observations threads addr lo_old lo
      h1 h2 h3 h4 h5 h6 h7 hbound_lo $$ [$Hσ $Hlo] with ⟨Hσ1, Hlo⟩
  imod stateInterp_store64 store1 steps observations threads (addr + 8) hi_old hi
      h81 h82 h83 h84 h85 h86 h87 hbound_hi $$ [$Hσ1 $Hhi] with ⟨Hσ2, Hhi⟩
  imodintro
  isplitl [Hσ2]
  · iexact Hσ2
  isplitl [Hlo]
  · iexact Hlo
  · iexact Hhi

instance instIrisGS [WasmSmallStepGS hlc α] :
    IrisGS_gen hlc (Expr α) (WasmHeapGF α) where
  numLatersPerStep _ := 0
  forkPost _ := iprop(True)
  stateInterp_mono _ _ _ _ := by iintro $

end Wasm.SmallStep
