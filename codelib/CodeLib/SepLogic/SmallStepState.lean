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

/-- A singleton logical module map agrees with the entry runtime instance. -/
theorem runtimeModuleSingletonAgrees
    (runtime : RuntimeEnv α)
    (hwf : runtime.entry.id < runtime.instances.size) :
    ∀ (id : Nat) (m : Module),
      get? (PartialMap.singleton runtime.entry.id runtime.currentModule :
        WasmRuntimeModuleMap Module) id = some m →
      runtime.instances[id]?.map (·.module) = some m := by
  intro id m hm
  by_cases h : id = runtime.entry.id
  · subst h
    simp [PartialMap.singleton, get?_insert_eq rfl] at hm
    subst hm
    rw [Array.getElem?_eq_getElem hwf]
    simp [RuntimeEnv.currentModule, RuntimeEnv.currentInstance]
    rw [getElem!_pos runtime.instances runtime.entry.id hwf]
  · simp [PartialMap.singleton, get?_insert_ne (Ne.symm h), get?_empty] at hm

/-- A singleton logical host map agrees with the entry runtime instance. -/
theorem hostEnvSingletonAgrees
    (runtime : RuntimeEnv α)
    (hwf : runtime.entry.id < runtime.instances.size) :
    ∀ (id : Nat) (env : HostEnv α),
      get? (PartialMap.singleton runtime.entry.id runtime.currentHost :
        WasmHostEnvMap (HostEnv α)) id = some env →
      runtime.instances[id]?.map (·.host) = some env := by
  intro id env hm
  by_cases h : id = runtime.entry.id
  · subst h
    simp [PartialMap.singleton, get?_insert_eq rfl] at hm
    subst hm
    rw [Array.getElem?_eq_getElem hwf, Option.map_some]
    simp [RuntimeEnv.currentHost, RuntimeEnv.currentInstance]
    rw [getElem!_pos runtime.instances runtime.entry.id hwf]
  · simp [PartialMap.singleton, get?_insert_ne (Ne.symm h), get?_empty] at hm

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
  heapDomain : WasmHeapDomainGS α
  memoryPages : WasmMemoryPagesGS α
  global : WasmGlobalGS α
  dataSegment : WasmDataSegmentGS α
  table : WasmTableGS α
  elementSegment : WasmElementSegmentGS α
  exception : WasmExceptionGS α
  runtime : WasmRuntimeModuleGS α
  tagTable : WasmTagTableGS α
  hostEnv : WasmHostEnvGS α
  hostState : WasmHostStateGS α
  instanceGS : WasmInstanceGS α
  runtimeInstances : WasmRuntimeInstancesGS α

attribute [instance] WasmSmallStepGS.toInvGS_gen
attribute [instance] WasmSmallStepGS.toWasmHeapGS
attribute [reducible, instance] WasmSmallStepGS.heapDomain
attribute [reducible, instance] WasmSmallStepGS.memoryPages
attribute [reducible, instance] WasmSmallStepGS.global
attribute [reducible, instance] WasmSmallStepGS.dataSegment
attribute [reducible, instance] WasmSmallStepGS.table
attribute [reducible, instance] WasmSmallStepGS.elementSegment
attribute [reducible, instance] WasmSmallStepGS.exception
attribute [reducible, instance] WasmSmallStepGS.runtime
attribute [reducible, instance] WasmSmallStepGS.tagTable
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

/-- The exception-and-tag component of the state interpretation.

It records the authoritative exception-store ghost map (which must agree with
the physical `store.wasm.exns`) together with ghost knowledge about the
tag-identity table.  The tag component only claims that the agreed list is a
*prefix* of `store.wasm.tagIds`; nothing here constrains the physical store,
so linked stores whose tag table carries entries from additional registered
modules satisfy it unchanged.  In particular there is deliberately **no**
tag-count invariant: that would be false for the multi-instance stores
introduced by module linking.

Keeping this bundled in one definition means that the vast majority of the
lifting rules — which touch neither exceptions nor tags — can simply frame it
across a store update, because `store.wasm.exns` and `store.wasm.tagIds`
reduce definitionally through a `{ store with wasm := { store.wasm with … } }`
record update of any other field.  Taking the two physical lists as explicit
arguments (rather than the whole store) is what makes that framing work: after
a record update of an unrelated field, `{ store with wasm := … }.wasm.exns`
reduces to `store.wasm.exns`, so the framed proposition is recovered
syntactically. -/
def exceptionInterp [WasmExceptionGS α] [WasmTagTableGS α]
    (exns : List (Nat × List Value)) (tagIds : List Nat) :
    IProp (WasmHeapGF α) := iprop%
  (∃ exceptionσ : WasmExceptionMap (Nat × List Value),
      ghost_map_auth WasmExceptionGS.exceptionName (DFrac.own 1) exceptionσ ∗
        ⌜exceptionHeapAgrees exceptionσ exns⌝) ∗
    ∃ ids : List Nat, tagTableOwn ids ∗ ⌜ids.IsPrefix tagIds⌝

/-- Sparse primary-memory domain authority carried with the state
interpretation.  The existential frontier is fixed for ordinary instructions;
allocator commit rules can update it only while holding the exclusive client
fragment. -/
def heapDomainInterp [WasmHeapDomainGS α]
    (σ : WasmHeapMap (Option UInt8)) : IProp (WasmHeapGF α) := iprop%
  ∃ frontier : Nat, heapFrontierAuth frontier ∗ ⌜HeapBelow σ frontier⌝

/-- Allocate the ordinary, maximally permissive sparse-heap frontier.

Legacy adequacy frontends use `UInt32.size`, which imposes no restriction
beyond the address type itself.  Allocator-aware frontends instead allocate a
tighter frontier and retain its fragment so that fresh ranges can be committed
soundly. -/
theorem heapDomain_init (σ : WasmHeapMap (Option UInt8)) :
    ⊢@{IProp (WasmHeapGF α)} |==>
      ∃ gs : WasmHeapDomainGS α,
        @heapDomainInterp α gs σ := by
  letI heapFrontierElem :
      ElemG (WasmHeapGF α)
        (Auth.AuthRF (OptionOF (Excl.ExclOF (constOF (DiscreteO Nat))))) := by
    exists 18
  imod (iOwn_alloc (E := heapFrontierElem)
      (ExclAuth.auth (⟨UInt32.size⟩ : DiscreteO Nat))
      (CMRA.valid_iff_validN.mpr (fun n => CMRA.validN_op_l
        (CMRA.valid_iff_validN.mp
          (ExclAuth.valid
            (a := (⟨UInt32.size⟩ : DiscreteO Nat))) n)))) with
    ⟨%heapFrontierName, HheapFrontierAuth⟩
  let gs : WasmHeapDomainGS α :=
    { heapFrontierElem
      heapFrontierName }
  imodintro
  iexists gs
  unfold heapDomainInterp heapFrontierAuth
  iexists UInt32.size
  iframe HheapFrontierAuth
  ipureintro
  exact heapBelow_uint32Size σ

/-- Allocate a tight sparse-domain frontier and expose the matching exclusive
client fragment.  Callers must prove that the initial authoritative sparse
heap lies below this frontier; unlike `heapDomain_init`, this resource is meant
to be advanced by allocator commit rules. -/
theorem heapDomain_init_at (σ : WasmHeapMap (Option UInt8))
    (frontier : Nat) (hbelow : HeapBelow σ frontier) :
    ⊢@{IProp (WasmHeapGF α)} |==>
      ∃ gs : WasmHeapDomainGS α,
        @heapDomainInterp α gs σ ∗
          @heapFrontierOwn α gs frontier := by
  letI heapFrontierElem :
      ElemG (WasmHeapGF α)
        (Auth.AuthRF (OptionOF (Excl.ExclOF (constOF (DiscreteO Nat))))) := by
    exists 18
  imod (iOwn_alloc (E := heapFrontierElem)
      (ExclAuth.auth (⟨frontier⟩ : DiscreteO Nat) •
       ExclAuth.frag (⟨frontier⟩ : DiscreteO Nat))
      ExclAuth.valid) with
    ⟨%heapFrontierName, HheapFrontierAll⟩
  ihave HheapFrontierPair := iOwn_op.mp $$ HheapFrontierAll
  icases HheapFrontierPair with
    ⟨HheapFrontierAuth, HheapFrontierOwn⟩
  let gs : WasmHeapDomainGS α :=
    { heapFrontierElem
      heapFrontierName }
  imodintro
  iexists gs
  isplitl [HheapFrontierAuth]
  · unfold heapDomainInterp heapFrontierAuth
    iexists frontier
    iframe HheapFrontierAuth
    ipureintro
    exact hbelow
  · unfold heapFrontierOwn
    iexact HheapFrontierOwn

/-- State components that are normally framed opaquely by lifting rules.  The
heap-domain invariant is bundled with exception state so extending the sparse
heap does not perturb the main state-interpretation resource tuple. -/
def machineAuxInterp [WasmHeapDomainGS α] [WasmMemoryPagesGS α]
    [WasmExceptionGS α] [WasmTagTableGS α]
    (σ : WasmHeapMap (Option UInt8))
    (pages : Nat)
    (exns : List (Nat × List Value)) (tagIds : List Nat) :
    IProp (WasmHeapGF α) :=
  iprop(memoryPagesAuth pages ∗ heapDomainInterp σ ∗
    exceptionInterp exns tagIds)

theorem machineAuxInterp_heap_mono [WasmHeapDomainGS α]
    [WasmMemoryPagesGS α]
    [WasmExceptionGS α] [WasmTagTableGS α]
    {σ σ' : WasmHeapMap (Option UInt8)}
    {pages : Nat}
    {exns : List (Nat × List Value)} {tagIds : List Nat}
    (hbelow : ∀ frontier, HeapBelow σ frontier → HeapBelow σ' frontier) :
    machineAuxInterp (α := α) σ pages exns tagIds ⊢
      machineAuxInterp σ' pages exns tagIds := by
  unfold machineAuxInterp heapDomainInterp
  iintro ⟨Hpages, ⟨%frontier, Hfrontier, %Hbelow⟩, Hexceptions⟩
  isplitl [Hpages]
  · iexact Hpages
  · isplitl [Hfrontier]
    · iexists frontier
      iframe Hfrontier
      ipureintro
      exact hbelow frontier Hbelow
    · iexact Hexceptions

/-- Ghost knowledge of an exception entry pins the physical entry. -/
theorem exceptionInterp_lookup [WasmExceptionGS α] [WasmTagTableGS α]
    (exns : List (Nat × List Value)) (tagIds : List Nat)
    (index : Nat) (dq : DFrac) (tagAndArgs : Nat × List Value) :
    exceptionInterp (α := α) exns tagIds ∗ exceptionPointsTo index dq tagAndArgs ⊢
      iprop(⌜exns[index]? = some tagAndArgs⌝) := by
  unfold exceptionInterp
  iintro ⟨⟨⟨%exceptionσ, Hauth, %hag⟩, Htags⟩, Helem⟩
  iclear Htags
  ihave %hlookup := exceptionPointsTo_lookup exceptionσ index dq tagAndArgs $$
    Hauth Helem
  ipureintro
  exact hag index tagAndArgs hlookup

/-- Ghost knowledge of the tag table is a prefix of the physical tag table.
This is the *only* channel through which a rule may learn anything about
tags; the state interpretation itself constrains nothing. -/
theorem exceptionInterp_tagPrefix [WasmExceptionGS α] [WasmTagTableGS α]
    (exns : List (Nat × List Value)) (tagIds ids : List Nat) :
    exceptionInterp (α := α) exns tagIds ∗ tagTableOwn ids ⊢
      iprop(⌜ids.IsPrefix tagIds⌝) := by
  unfold exceptionInterp
  iintro ⟨⟨Hexn, %ids', Hactual, %Hprefix⟩, Howned⟩
  iclear Hexn
  ihave %heq := tagTableOwn_agree ids' ids $$ [$Hactual $Howned]
  ipureintro
  exact heq ▸ Hprefix

/-- Monotonicity of `exceptionInterp` along the two physical lists.  Used when
a rule replaces the whole `Store` (host-call return, instantiation) and only
knows that the exception/tag facts are preserved rather than that the lists are
literally unchanged. -/
theorem exceptionInterp_mono [WasmExceptionGS α] [WasmTagTableGS α]
    {exns exns' : List (Nat × List Value)} {tagIds tagIds' : List Nat}
    (hexns : ∀ σ : WasmExceptionMap (Nat × List Value),
      exceptionHeapAgrees σ exns → exceptionHeapAgrees σ exns')
    (htags : ∀ ids : List Nat, ids.IsPrefix tagIds → ids.IsPrefix tagIds') :
    exceptionInterp (α := α) exns tagIds ⊢ exceptionInterp exns' tagIds' := by
  unfold exceptionInterp
  iintro ⟨⟨%exceptionσ, Hauth, %hag⟩, %ids, Htags, %hpre⟩
  isplitl [Hauth]
  · iexists exceptionσ
    iframe Hauth
    ipureintro
    exact hexns exceptionσ hag
  · iexists ids
    iframe Htags
    ipureintro
    exact htags ids hpre

theorem machineAuxInterp_exception_mono [WasmHeapDomainGS α]
    [WasmMemoryPagesGS α]
    [WasmExceptionGS α] [WasmTagTableGS α]
    {σ : WasmHeapMap (Option UInt8)}
    {pages : Nat}
    {exns exns' : List (Nat × List Value)} {tagIds tagIds' : List Nat}
    (hexns : ∀ exceptionσ : WasmExceptionMap (Nat × List Value),
      exceptionHeapAgrees exceptionσ exns →
        exceptionHeapAgrees exceptionσ exns')
    (htags : ∀ ids : List Nat, ids.IsPrefix tagIds → ids.IsPrefix tagIds') :
    machineAuxInterp (α := α) σ pages exns tagIds ⊢
      machineAuxInterp σ pages exns' tagIds' := by
  unfold machineAuxInterp
  iintro ⟨Hpages, Hdomain, Hexceptions⟩
  isplitl [Hpages]
  · iexact Hpages
  isplitl [Hdomain]
  · iexact Hdomain
  · iapply exceptionInterp_mono hexns htags
    iexact Hexceptions

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
      ∃ runtimeModuleσ : WasmRuntimeModuleMap Module,
      ∃ hostEnvσ : WasmHostEnvMap (HostEnv α),
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
        ghost_map_auth WasmSmallStepGS.runtime.runtimeName
          (DFrac.own 1) runtimeModuleσ ∗
        ([∗map] id ↦ m ∈ runtimeModuleσ, runtimeModuleElem id m) ∗
        runtimeInstancesOwn store.runtime.instances ∗
        currentInstanceAuth store.runtime.entry ∗
        ghost_map_auth WasmSmallStepGS.hostEnv.hostEnvName
          (DFrac.own 1) hostEnvσ ∗
        hostStateAuth store.wasm.host ∗
      ⌜heapAgreesWithMem σ (storeResolve store) ∧
        heapAddressesInBounds σ (storeResolve store) ∧
        globalHeapAgrees globalσ store.wasm.globals ∧
        dataSegmentHeapAgrees dataSegmentσ store.wasm.dataSegments ∧
        tableHeapAgrees tableσ store.wasm.tables ∧
        elementSegmentHeapAgrees elementSegmentσ
          store.wasm.elementSegments ∧
        (∀ id m, get? runtimeModuleσ id = some m →
          store.runtime.instances[id]?.map (·.module) = some m) ∧
        ∀ id env, get? hostEnvσ id = some env →
          store.runtime.instances[id]?.map (·.host) = some env⌝ ∗
      machineAuxInterp σ store.wasm.mem.pages
        store.wasm.exns store.wasm.tagIds

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
        ∃ runtimeModuleσ : WasmRuntimeModuleMap Module,
        ∃ hostEnvσ : WasmHostEnvMap (HostEnv α),
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
          ghost_map_auth WasmSmallStepGS.runtime.runtimeName
            (DFrac.own 1) runtimeModuleσ ∗
          ([∗map] id ↦ m ∈ runtimeModuleσ, runtimeModuleElem id m) ∗
          runtimeInstancesOwn store.runtime.instances ∗
          currentInstanceAuth store.runtime.entry ∗
          ghost_map_auth WasmSmallStepGS.hostEnv.hostEnvName
            (DFrac.own 1) hostEnvσ ∗
          hostStateAuth store.wasm.host ∗
        ⌜heapAgreesWithMem σ (storeResolve store) ∧
          heapAddressesInBounds σ (storeResolve store) ∧
          globalHeapAgrees globalσ store.wasm.globals ∧
          dataSegmentHeapAgrees dataSegmentσ store.wasm.dataSegments ∧
          tableHeapAgrees tableσ store.wasm.tables ∧
          elementSegmentHeapAgrees elementSegmentσ
            store.wasm.elementSegments ∧
          (∀ id m, get? runtimeModuleσ id = some m →
            store.runtime.instances[id]?.map (·.module) = some m) ∧
          ∀ id env, get? hostEnvσ id = some env →
            store.runtime.instances[id]?.map (·.host) = some env⌝ ∗
        machineAuxInterp σ store.wasm.mem.pages
          store.wasm.exns store.wasm.tagIds) :=
  .rfl

/-- Open the standard components and physical invariants of `stateInterp`. -/
syntax "iopen_state " specPat : tactic

set_option hygiene false in
macro_rules
  | `(tactic| iopen_state $state:specPat) =>
    `(tactic|
      icases (stateInterp_eq store steps observations threads).mp $$ $state with
        ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ,
          %runtimeModuleσ, %hostEnvσ, Hheap, Hglobals, Hsegments, Htables,
          HelementSegments, HruntimeModuleAuth, HruntimeModuleBigSep,
          HruntimeInstances, HinstanceAuth, HhostEnvAuth, Hstate_auth,
          %Hfacts, Hexc⟩)

/-- The exact physical primary-memory page count is available as a persistent
lower-bound snapshot without changing the physical or ghost state. -/
theorem stateInterp_memoryPages_snapshot [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ==∗
      stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
        memoryPagesOwn store.wasm.mem.pages := by
  iintro Hstate
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ,
      %runtimeModuleσ, %hostEnvσ, Hheap, Hglobals, Hsegments, Htables,
      HelementSegments, HruntimeModuleAuth, HruntimeModuleBigSep,
      HruntimeInstances, HinstanceAuth, HhostEnvAuth, HstateAuth, %Hfacts,
      Haux⟩
  iunfold machineAuxInterp at Haux
  icases Haux with ⟨Hpages, Hdomain, Hexceptions⟩
  ihave #Hsnapshot := memoryPagesOwn_snapshot store.wasm.mem.pages $$ Hpages
  imodintro
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments
      HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth
      HhostEnvAuth HstateAuth Hpages Hdomain Hexceptions]
  · iapply (stateInterp_eq store steps observations threads).mpr
    iexists σ
    iexists globalσ
    iexists dataSegmentσ
    iexists tableσ
    iexists elementSegmentσ
    iexists runtimeModuleσ
    iexists hostEnvσ
    iframe Hheap Hglobals Hsegments Htables HelementSegments
      HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth
      HhostEnvAuth HstateAuth
    isplit
    · ipureintro
      exact Hfacts
    · unfold machineAuxInterp
      iframe Hpages Hdomain Hexceptions
  · iexact Hsnapshot

/-- Frame-preserving form of `stateInterp_memoryPages_snapshot`. This is useful
inside lifting rules that must retain a linear client resource while the page
authority is opened to mint an exact snapshot. -/
theorem stateInterp_memoryPages_snapshot_frame [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    {P : IProp (WasmHeapGF α)} :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗ P ==∗
      (stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
        memoryPagesOwn store.wasm.mem.pages) ∗ P := by
  iintro ⟨Hstate, HP⟩
  iapply bupd_frame_right
  isplitl [Hstate]
  · iapply stateInterp_memoryPages_snapshot
    iexact Hstate
  · iexact HP

/-- A client page snapshot is a sound lower bound on the current physical
primary-memory size recorded by `stateInterp`. -/
theorem stateInterp_memoryPages_agree [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads ownedPages : Nat) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      memoryPagesOwn ownedPages ==∗
      stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      memoryPagesOwn ownedPages ∗
      ⌜ownedPages ≤ store.wasm.mem.pages⌝ := by
  iintro ⟨Hstate, Hsnapshot⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ,
      %runtimeModuleσ, %hostEnvσ, Hheap, Hglobals, Hsegments, Htables,
      HelementSegments, HruntimeModuleAuth, HruntimeModuleBigSep,
      HruntimeInstances, HinstanceAuth, HhostEnvAuth, HstateAuth, %Hfacts,
      Haux⟩
  iunfold machineAuxInterp at Haux
  icases Haux with ⟨Hpages, Hdomain, Hexceptions⟩
  ihave %hle := memoryPagesOwn_agree
    store.wasm.mem.pages ownedPages $$ [Hpages Hsnapshot]
  · iframe Hpages Hsnapshot
  imodintro
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments
      HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth
      HhostEnvAuth HstateAuth Hpages Hdomain Hexceptions]
  · iapply (stateInterp_eq store steps observations threads).mpr
    iexists σ
    iexists globalσ
    iexists dataSegmentσ
    iexists tableσ
    iexists elementSegmentσ
    iexists runtimeModuleσ
    iexists hostEnvσ
    iframe Hheap Hglobals Hsegments Htables HelementSegments
      HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth
      HhostEnvAuth HstateAuth
    isplit
    · ipureintro
      exact Hfacts
    · unfold machineAuxInterp
      iframe Hpages Hdomain Hexceptions
  isplitl [Hsnapshot]
  · iexact Hsnapshot
  · ipureintro
    exact hle

theorem stateInterp_pointsTo_read8 [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (address : UInt32) (value : UInt8) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        ⟨0, address⟩ (DFrac.own 1) (some value) ==∗
      ⌜store.wasm.mem.read8 address = value⌝ := by
  iintro ⟨Hstate, Hpointsto⟩
  iopen_state Hstate
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
  iopen_state Hstate
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
  iopen_state Hstate
  icases genHeap_valid $$ [$Hheap $Hpointsto] with >%hlookup
  ipureintro
  exact ⟨fromResolver store Hfacts.1 address value hlookup,
    fromResolverBounds store Hfacts.2.1 address (by simp [hlookup])⟩

/-- Regression lemma: the client fragment cannot describe a host state that
differs from the physical state protected by `StateInterp`. -/
theorem stateInterp_host_agree [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat) (host : α) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      hostStateOwn host ⊢ ⌜store.wasm.host = host⌝ := by
  iintro ⟨Hstate, Hown⟩
  iopen_state Hstate
  iapply hostStateOwn_agree store.wasm.host host
  iframe Hstate_auth Hown

/-- Obtain a pure fact from an update while preserving the selected Iris
resources in the surrounding proof context. -/
syntax "ihave_pure " ident " : " term " using " term
  " $$ " specPat : tactic

set_option hygiene false in
macro_rules
  | `(tactic| ihave_pure $fact:ident : $claim:term using $proof:term
        $$ $resources:specPat) =>
    `(tactic|
      (ihave %$fact : $claim $$ $resources
       · imod ($proof) $$ [$] with %$fact
         ipureintro
         exact $fact))

/-- Extract a pure lookup from generic heap authority and ownership. -/
syntax "ihave_heap_valid " ident " : " term " $$ " specPat : tactic

macro_rules
  | `(tactic| ihave_heap_valid $fact:ident : $claim:term
        $$ $resources:specPat) =>
    `(tactic|
      ihave_pure $fact : $claim using genHeap_valid $$ $resources)

/-- Ownership of a byte range in the primary memory determines every physical
byte in it, and bounds every address in it. -/
theorem stateInterp_pointsToBytes_agree [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (addr : UInt32) (bytes : List UInt8) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      pointsToBytes 0 addr bytes ==∗
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
      ihave Hbytes := (pointsToBytes_cons 0 addr b rest).mp $$ Hbytes
      icases Hbytes with ⟨Hhead, Hrest⟩
      ihave_pure hhead :
          ⌜store.wasm.mem.read8 addr = b ∧
            addr.toNat < store.wasm.mem.pages * 65536⌝ using
        stateInterp_pointsTo_facts store steps observations threads addr b $$
          [Hstate Hhead]
      ihave_pure hrest :
          ⌜∀ i b', rest[i]? = some b' →
            store.wasm.mem.read8 ((addr + 1) + UInt32.ofNat i) = b' ∧
            ((addr + 1) + UInt32.ofNat i).toNat <
              store.wasm.mem.pages * 65536⌝ using
        ih (addr + 1) $$ [Hstate Hrest]
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

/-- Derive physical byte facts for an owned range in a lifting proof. -/
syntax "wasm_points_to_bytes_agree " ident ", " term ", " term ", " term
  " $$ " specPat : tactic

set_option hygiene false in
macro_rules
  | `(tactic| wasm_points_to_bytes_agree $facts:ident, $addr:term,
        $bytes:term, $observations:term $$ $resources:specPat) =>
    `(tactic|
      ihave_pure $facts : ⌜∀ i b, $bytes[i]? = some b →
          store.wasm.mem.read8 ($addr + UInt32.ofNat i) = b ∧
          ($addr + UInt32.ofNat i).toNat <
            store.wasm.mem.pages * 65536⌝ using
        stateInterp_pointsToBytes_agree store ns $observations nt $addr $bytes
        $$ $resources)

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

/-- Pointwise agreement for an owned byte range determines the corresponding
physical `readBytes` slice. -/
theorem pointsToBytes_facts_readBytes {addr : UInt32}
    {bytes : List UInt8} {mem : Mem}
    (hfacts : ∀ i b, bytes[i]? = some b →
      mem.read8 (addr + UInt32.ofNat i) = b)
    (hnowrap : addr.toNat + bytes.length < UInt32.size) :
    mem.readBytes addr.toNat bytes.length = bytes := by
  apply List.ext_getElem
  · simp [Mem.readBytes]
  · intro i hi _
    have hi' : i < bytes.length := by
      simpa [Mem.readBytes] using hi
    have haddr : (addr + UInt32.ofNat i).toNat = addr.toNat + i := by
      have hiSize : i < UInt32.size := by omega
      rw [UInt32.toNat_add, UInt32.toNat_ofNat_of_lt' hiSize]
      simp only [UInt32.size] at hnowrap ⊢
      omega
    have hfact := hfacts i bytes[i] (List.getElem?_eq_getElem hi')
    simpa [Mem.readBytes, Mem.read8, haddr] using hfact

/-! ## Fresh sparse-range insertion -/

/-- Insert concrete bytes into an authoritative sparse heap at successive
primary-memory addresses.  This is the logical allocation commit map; it does
not modify physical memory. -/
def insertFreshBytes (σ : WasmHeapMap (Option UInt8))
    (addr : UInt32) (bytes : List UInt8) :
    WasmHeapMap (Option UInt8) :=
  match bytes with
  | [] => σ
  | byte :: rest =>
      insertFreshBytes (insert σ ⟨0, addr⟩ (some byte))
        (addr + 1) rest

/-- Allocate GenHeap fragments for a consecutive range known to begin at the
current sparse-domain boundary.  The resulting authority covers exactly the
old domain plus the inserted byte keys, and the new domain lies below the end
of the range. -/
theorem genHeap_alloc_freshBytes [WasmHeapGS α]
    (σ : WasmHeapMap (Option UInt8)) (addr : UInt32)
    (bytes : List UInt8)
    (hbelow : HeapBelow σ addr.toNat)
    (hnowrap : addr.toNat + bytes.length < UInt32.size) :
    genHeapInterp σ ==∗
      genHeapInterp (insertFreshBytes σ addr bytes) ∗
      pointsToBytes 0 addr bytes ∗
      ⌜HeapBelow (insertFreshBytes σ addr bytes)
        (addr.toNat + bytes.length)⌝ := by
  induction bytes generalizing σ addr with
  | nil =>
      change genHeapInterp σ ==∗
        genHeapInterp σ ∗ pointsToBytes 0 addr [] ∗
          ⌜HeapBelow σ addr.toNat⌝
      iintro Hheap
      imodintro
      isplitl [Hheap]
      · iexact Hheap
      isplit
      · iapply (pointsToBytes_nil 0 addr).mpr
        itrivial
      · ipureintro
        exact hbelow
  | cons byte rest ih =>
      have hlookup : get? σ (⟨0, addr⟩ : MemoryKey) = none :=
        hbelow.get?_eq_none_of_le ⟨0, addr⟩ rfl (Nat.le_refl _)
      have hsucc : (addr + 1).toNat = addr.toNat + 1 := by
        simpa using UInt32.add_ofNat_toNat_noWrap addr 1 (by decide) (by
          simp only [List.length_cons, UInt32.size] at hnowrap
          omega)
      have hbelow' :
          HeapBelow (insert σ ⟨0, addr⟩ (some byte))
            (addr + 1).toNat := by
        apply HeapBelow.insert_fresh
          (hbelow.mono (by rw [hsucc]; omega))
        intro _
        rw [hsucc]
        exact Nat.lt_succ_self _
      have hnowrap' :
          (addr + 1).toNat + rest.length < UInt32.size := by
        rw [hsucc]
        simp only [List.length_cons] at hnowrap
        omega
      iintro Hheap
      imod genHeap_alloc hlookup $$ Hheap with
        ⟨Hheap, Hhead, Hmeta⟩
      iclear Hmeta
      imod ih (insert σ ⟨0, addr⟩ (some byte)) (addr + 1)
          hbelow' hnowrap' $$ Hheap with
        ⟨Hheap, Hrest, %HbelowFinal⟩
      isimp only [insertFreshBytes]
      imodintro
      isplitl [Hheap]
      · iexact Hheap
      isplitl [Hhead Hrest]
      · iapply (pointsToBytes_cons 0 addr byte rest).mpr
        isplitl [Hhead]
        · iexact Hhead
        · iexact Hrest
      · ipureintro
        simpa only [List.length_cons, hsucc, Nat.add_assoc,
          Nat.add_comm 1 rest.length] using HbelowFinal

/-- Pure domain fact for the same fresh-range construction. -/
theorem HeapBelow.insertFreshBytes
    { σ : WasmHeapMap (Option UInt8)} {addr : UInt32}
    {bytes : List UInt8}
    (hbelow : HeapBelow σ addr.toNat)
    (hnowrap : addr.toNat + bytes.length < UInt32.size) :
    HeapBelow (insertFreshBytes σ addr bytes)
      (addr.toNat + bytes.length) := by
  induction bytes generalizing σ addr with
  | nil =>
      change HeapBelow σ addr.toNat
      exact hbelow
  | cons byte rest ih =>
      have hsucc : (addr + 1).toNat = addr.toNat + 1 := by
        simpa using UInt32.add_ofNat_toNat_noWrap addr 1 (by decide) (by
          simp only [List.length_cons, UInt32.size] at hnowrap
          omega)
      have hbelow' :
          HeapBelow (insert σ ⟨0, addr⟩ (some byte))
            (addr + 1).toNat := by
        apply HeapBelow.insert_fresh
          (hbelow.mono (by rw [hsucc]; omega))
        intro _
        rw [hsucc]
        exact Nat.lt_succ_self _
      have hnowrap' :
          (addr + 1).toNat + rest.length < UInt32.size := by
        rw [hsucc]
        simp only [List.length_cons] at hnowrap
        omega
      change HeapBelow
        (SmallStep.insertFreshBytes (insert σ ⟨0, addr⟩ (some byte))
          (addr + 1) rest)
        (addr.toNat + (byte :: rest).length)
      simpa only [List.length_cons, hsucc, Nat.add_assoc,
        Nat.add_comm 1 rest.length] using ih hbelow' hnowrap'

/-- Split the fragments supplied by adequacy for a freshly inserted byte
range into the corresponding contiguous byte slice and the fragments of the
old sparse heap.  This is the initialization-side counterpart of
`genHeap_alloc_freshBytes`: no ghost update occurs because adequacy has already
allocated the final map. -/
theorem insertFreshBytes_bigSep_pointsToBytes [WasmHeapGS α]
    (σ : WasmHeapMap (Option UInt8)) (addr : UInt32)
    (bytes : List UInt8)
    (hbelow : HeapBelow σ addr.toNat)
    (hnowrap : addr.toNat + bytes.length < UInt32.size) :
    ([∗map] address ↦ value ∈ insertFreshBytes σ addr bytes,
        pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
          address (DFrac.own 1) value) ⊢
      pointsToBytes 0 addr bytes ∗
      ([∗map] address ↦ value ∈ σ,
        pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
          address (DFrac.own 1) value) := by
  induction bytes generalizing σ addr with
  | nil =>
      simp only [insertFreshBytes, pointsToBytes]
      iintro Hheap
      iframe Hheap
  | cons byte rest ih =>
      have hlookup : get? σ (⟨0, addr⟩ : MemoryKey) = none :=
        hbelow.get?_eq_none_of_le ⟨0, addr⟩ rfl (Nat.le_refl _)
      have hsucc : (addr + 1).toNat = addr.toNat + 1 := by
        simpa using UInt32.add_ofNat_toNat_noWrap addr 1 (by decide) (by
          simp only [List.length_cons, UInt32.size] at hnowrap
          omega)
      have hbelow' :
          HeapBelow (insert σ ⟨0, addr⟩ (some byte))
            (addr + 1).toNat := by
        apply HeapBelow.insert_fresh
          (hbelow.mono (by rw [hsucc]; omega))
        intro _
        rw [hsucc]
        exact Nat.lt_succ_self _
      have hnowrap' :
          (addr + 1).toNat + rest.length < UInt32.size := by
        rw [hsucc]
        simp only [List.length_cons] at hnowrap
        omega
      simp only [insertFreshBytes]
      iintro Hheap
      ihave Hsplit := ih (insert σ ⟨0, addr⟩ (some byte)) (addr + 1)
          hbelow' hnowrap' $$ Hheap
      icases Hsplit with ⟨Hrest, Hinsert⟩
      ihave Hinsert' :=
        (BI.BigSepM.bigSepM_insert hlookup).mp $$ Hinsert
      icases Hinsert' with ⟨Hhead, Hprevious⟩
      isplitl [Hhead Hrest]
      · iapply (pointsToBytes_cons 0 addr byte rest).mpr
        iframe Hhead Hrest
      · iexact Hprevious

/-- The concrete current contents of a non-wrapping physical range, expressed
with the same successor-address recursion as `pointsToBytes`. -/
def physicalBytes (mem : Mem) (addr : UInt32) : Nat → List UInt8
  | 0 => []
  | size + 1 => mem.read8 addr :: physicalBytes mem (addr + 1) size

@[simp] theorem physicalBytes_length (mem : Mem) (addr : UInt32)
    (size : Nat) : (physicalBytes mem addr size).length = size := by
  induction size generalizing addr with
  | zero => rfl
  | succ size ih => simp [physicalBytes, ih]

/-- Inserting `physicalBytes` into the sparse ghost map preserves both
physical-byte agreement and allocation bounds. -/
theorem insertFreshPhysicalBytes_facts
    (σ : WasmHeapMap (Option UInt8)) (resolve : Nat → Option Mem)
    (mem : Mem) (addr : UInt32) (size : Nat)
    (hresolve : resolve 0 = some mem)
    (hagree : heapAgreesWithMem σ resolve)
    (hinBounds : heapAddressesInBounds σ resolve)
    (hbound : addr.toNat + size ≤ mem.pages * 65536)
    (hnowrap : addr.toNat + size < UInt32.size) :
    heapAgreesWithMem
        (insertFreshBytes σ addr (physicalBytes mem addr size)) resolve ∧
      heapAddressesInBounds
        (insertFreshBytes σ addr (physicalBytes mem addr size)) resolve := by
  induction size generalizing σ addr with
  | zero =>
      simpa [physicalBytes, insertFreshBytes] using
        And.intro hagree hinBounds
  | succ size ih =>
      have hsucc : (addr + 1).toNat = addr.toNat + 1 := by
        simpa using UInt32.add_ofNat_toNat_noWrap addr 1 (by decide) (by
          simp only [UInt32.size] at hnowrap
          omega)
      have haddrBound : addr.toNat < mem.pages * 65536 := by
        omega
      have hagree' :
          heapAgreesWithMem
            (insert σ ⟨0, addr⟩ (some (mem.read8 addr))) resolve :=
        insert_physical_byte_sound σ resolve 0 mem addr
          (mem.read8 addr) hresolve hagree rfl
      have hinBounds' :
          heapAddressesInBounds
            (insert σ ⟨0, addr⟩ (some (mem.read8 addr))) resolve :=
        insert_physical_byte_inBounds σ resolve 0 mem addr
          (mem.read8 addr) hresolve hinBounds haddrBound
      have hbound' :
          (addr + 1).toNat + size ≤ mem.pages * 65536 := by
        rw [hsucc]
        omega
      have hnowrap' :
          (addr + 1).toNat + size < UInt32.size := by
        rw [hsucc]
        omega
      simpa only [physicalBytes, insertFreshBytes] using
        ih (insert σ ⟨0, addr⟩ (some (mem.read8 addr)))
          (addr + 1) hagree' hinBounds' hbound' hnowrap'

/-- Commit a fresh physical primary-memory range to the authoritative sparse
heap and advance its exclusive logical frontier.  Physical memory is unchanged;
the returned fragments name exactly the bytes already present in the range.
This is the core ownership rule used at a bump allocator's cursor commit. -/
theorem stateInterp_alloc_freshRange [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (frontier : Nat) (base : UInt32) (size : Nat)
    (hbase : frontier ≤ base.toNat)
    (hbound : base.toNat + size ≤ store.wasm.mem.pages * 65536)
    (hnowrap : base.toNat + size < UInt32.size) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      heapFrontierOwn frontier ==∗
      stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      heapFrontierOwn (base.toNat + size) ∗
      pointsToBytes 0 base (physicalBytes store.wasm.mem base size) := by
  iintro ⟨Hstate, HfrontierOwn⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ,
      %runtimeModuleσ, %hostEnvσ, Hheap, Hglobals, Hsegments,
      Htables, HelementSegments, HruntimeModuleAuth,
      HruntimeModuleBigSep, HruntimeInstances, HinstanceAuth,
      HhostEnvAuth, HstateAuth, %Hfacts, Haux⟩
  iunfold machineAuxInterp at Haux
  icases Haux with ⟨Hpages, Hdomain, HexceptionInterp⟩
  iunfold heapDomainInterp at Hdomain
  icases Hdomain with
    ⟨%actualFrontier, HfrontierAuth, %Hbelow⟩
  icombine HfrontierAuth HfrontierOwn as Hfrontier
  ihave %hfrontierEq := heapFrontierOwn_agree
      actualFrontier frontier $$ Hfrontier
  subst actualFrontier
  let bytes := physicalBytes store.wasm.mem base size
  have hbytesLength : bytes.length = size := by
    simp [bytes]
  have hbelowBase : HeapBelow σ base.toNat :=
    Hbelow.mono hbase
  have hfacts' := insertFreshPhysicalBytes_facts σ
    (storeResolve store) store.wasm.mem base size
    (storeResolve_zero store) Hfacts.1 Hfacts.2.1 hbound hnowrap
  imod genHeap_alloc_freshBytes σ base bytes hbelowBase (by
      rw [hbytesLength]
      exact hnowrap) $$ Hheap with
    ⟨Hheap, Hbytes, %HbelowFinal⟩
  imod heapFrontierOwn_update frontier (base.toNat + size) $$
      Hfrontier with
    ⟨HfrontierAuth, HfrontierOwn⟩
  ihave Haux : machineAuxInterp
      (insertFreshBytes σ base bytes)
      store.wasm.mem.pages
      store.wasm.exns store.wasm.tagIds $$
      [Hpages HfrontierAuth HexceptionInterp]
  · unfold machineAuxInterp heapDomainInterp
    isplitl [Hpages]
    · iexact Hpages
    · isplitl [HfrontierAuth]
      · iexists base.toNat + size
        iframe HfrontierAuth
        ipureintro
        simpa [hbytesLength] using HbelowFinal
      · iexact HexceptionInterp
  ihave HstateAndBytes :
      stateInterp (GF := WasmHeapGF α)
          store steps observations threads ∗
        pointsToBytes 0 base
          (physicalBytes store.wasm.mem base size) $$
      [Hheap Hglobals Hsegments Htables HelementSegments
        HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances
        HinstanceAuth HhostEnvAuth HstateAuth Haux Hbytes]
  · isplitl [Hheap Hglobals Hsegments Htables HelementSegments
        HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances
        HinstanceAuth HhostEnvAuth HstateAuth Haux]
    · iapply (stateInterp_eq store steps observations threads).mpr
      iexists insertFreshBytes σ base bytes
      iexists globalσ
      iexists dataSegmentσ
      iexists tableσ
      iexists elementSegmentσ
      iexists runtimeModuleσ
      iexists hostEnvσ
      iframe Hheap Hglobals Hsegments Htables HelementSegments
        HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances
        HinstanceAuth HhostEnvAuth HstateAuth Haux
      ipureintro
      exact ⟨by simpa [bytes] using hfacts'.1,
        by simpa [bytes] using hfacts'.2,
        Hfacts.2.2⟩
    · isimp only [bytes] at Hbytes
      iexact Hbytes
  icases HstateAndBytes with ⟨Hstate, Hbytes⟩
  imodintro
  isplitl [Hstate]
  · iexact Hstate
  isplitl [HfrontierOwn]
  · iexact HfrontierOwn
  · iexact Hbytes

/-- Allocate a fresh range using only a persistent lower-bound snapshot of the
primary-memory page count.  This is the allocator-facing form: it keeps the
physical-store existential hidden while exposing exactly the bound needed by
`stateInterp_alloc_freshRange`. -/
theorem stateInterp_alloc_freshRange_owned [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (frontier ownedPages : Nat) (base : UInt32) (size : Nat)
    (hbase : frontier ≤ base.toNat)
    (hbound : base.toNat + size ≤ ownedPages * 65536)
    (hnowrap : base.toNat + size < UInt32.size) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      heapFrontierOwn frontier ∗ memoryPagesOwn ownedPages ==∗
      stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      heapFrontierOwn (base.toNat + size) ∗
      memoryPagesOwn ownedPages ∗
      pointsToBytes 0 base (physicalBytes store.wasm.mem base size) := by
  iintro ⟨Hstate, Hfrontier, Hpages⟩
  imod stateInterp_memoryPages_agree
      store steps observations threads ownedPages $$ [Hstate Hpages] with
      ⟨Hstate, Hpages, %hpages⟩
  · iframe Hstate Hpages
  have hboundPhysical :
      base.toNat + size ≤ store.wasm.mem.pages * 65536 := by
    exact Nat.le_trans hbound (Nat.mul_le_mul_right 65536 hpages)
  imod stateInterp_alloc_freshRange store steps observations threads
      frontier base size hbase hboundPhysical hnowrap $$
      [Hstate Hfrontier] with ⟨Hstate, Hfrontier, Hbytes⟩
  · iframe Hstate Hfrontier
  imodintro
  isplitl [Hstate]
  · iexact Hstate
  isplitl [Hfrontier]
  · iexact Hfrontier
  isplitl [Hpages]
  · iexact Hpages
  · iexact Hbytes

-- ghost map updated by a bulk fill of the primary memory
private def fillSigma (σ : WasmHeapMap (Option UInt8)) (addr : UInt32)
    (bytes : List UInt8) (val : UInt8) : WasmHeapMap (Option UInt8) :=
  match bytes with
  | [] => σ
  | _ :: rest => fillSigma (insert σ ⟨0, addr⟩ (some val)) (addr + 1) rest val

private theorem fillSigma_ghost [WasmSmallStepGS hlc α]
    (σ : WasmHeapMap (Option UInt8)) (addr : UInt32)
    (bytes : List UInt8) (val : UInt8) :
    genHeapInterp σ ∗ pointsToBytes 0 addr bytes ==∗
    genHeapInterp (fillSigma σ addr bytes val) ∗
    pointsToBytes 0 addr (List.replicate bytes.length val) ∗
    ⌜∀ frontier, HeapBelow σ frontier →
      HeapBelow (fillSigma σ addr bytes val) frontier⌝ := by
  induction bytes generalizing σ addr with
  | nil =>
      show genHeapInterp σ ∗ pointsToBytes 0 addr [] ==∗
           genHeapInterp σ ∗ pointsToBytes 0 addr [] ∗
             ⌜∀ frontier, HeapBelow σ frontier → HeapBelow σ frontier⌝
      iintro ⟨Hheap, Hempty⟩
      imodintro
      isplitl [Hheap]
      · iexact Hheap
      isplitl [Hempty]
      · iexact Hempty
      · ipureintro
        intro frontier Hbelow
        exact Hbelow
  | cons b rest ih =>
      show genHeapInterp σ ∗ pointsToBytes 0 addr (b :: rest) ==∗
           genHeapInterp (fillSigma (insert σ ⟨0, addr⟩ (some val)) (addr + 1) rest val) ∗
           pointsToBytes 0 addr (val :: List.replicate rest.length val) ∗
           ⌜∀ frontier, HeapBelow σ frontier →
             HeapBelow
               (fillSigma (insert σ ⟨0, addr⟩ (some val))
                 (addr + 1) rest val) frontier⌝
      iintro ⟨Hheap, Hbytes⟩
      ihave Hbytes := (pointsToBytes_cons 0 addr b rest).mp $$ Hbytes
      icases Hbytes with ⟨Hhead, Hrest⟩
      ihave_heap_valid hlookup :
          ⌜get? σ ⟨0, addr⟩ = some (some b)⌝ $$ [Hheap Hhead]
      imod genHeap_update (v₂ := some val) $$ [$Hheap $Hhead] with ⟨Hheap, Hhead⟩
      imod (ih (insert σ ⟨0, addr⟩ (some val)) (addr + 1)) $$ [$Hheap $Hrest] with
        ⟨Hheap, Hrest, %HbelowRest⟩
      imodintro
      isplitl [Hheap]
      · iexact Hheap
      isplitl [Hhead Hrest]
      · iapply (pointsToBytes_cons 0 addr val (List.replicate rest.length val)).mpr
        isplitl [Hhead]
        · iexact Hhead
        · iexact Hrest
      · ipureintro
        intro frontier Hbelow
        apply HbelowRest frontier
        exact HeapBelow.insert_existing Hbelow ⟨0, addr⟩ (some val)
          ⟨some b, hlookup⟩

private theorem fillSigma_agrees
    (σ : WasmHeapMap (Option UInt8)) (resolve : Nat → Option Mem) (mem : Mem)
    (addr : UInt32) (bytes : List UInt8) (val : UInt8)
    (hresolve : resolve 0 = some mem)
    (hagree : heapAgreesWithMem σ resolve)
    (hnowrap : addr.toNat + bytes.length < 4294967296) :
    heapAgreesWithMem (fillSigma σ addr bytes val)
      (fun id => if id = 0 then some (mem.fill addr.toNat bytes.length val)
        else resolve id) := by
  induction bytes generalizing σ addr mem resolve with
  | nil =>
      simp only [fillSigma, List.length_nil, Mem.fill_zero]
      have hfun : (fun id => if id = 0 then some mem else resolve id) = resolve := by
        funext id; by_cases h : id = 0 <;> simp [h, hresolve]
      rw [hfun]; exact hagree
  | cons b rest ih =>
      have h1 : (addr + 1).toNat = addr.toNat + 1 := by
        simp only [UInt32.toNat_add, show (1 : UInt32).toNat = 1 from rfl]
        simp only [List.length_cons] at hnowrap; omega
      have hnowrap' : (addr + 1).toNat + rest.length < 4294967296 := by
        rw [h1]; simp only [List.length_cons] at hnowrap; omega
      have ih' := ih (insert σ ⟨0, addr⟩ (some val))
          (fun id => if id = 0 then some (mem.write8 addr val) else resolve id)
          (mem.write8 addr val) (addr + 1) (by simp)
          (store_sound σ resolve 0 mem addr val hresolve hagree) hnowrap'
      rw [h1, Mem.write8_fill_eq] at ih'
      have hfun : (fun id => if id = 0 then some (mem.fill addr.toNat (rest.length + 1) val)
          else (if id = 0 then some (mem.write8 addr val) else resolve id)) =
          (fun id => if id = 0 then some (mem.fill addr.toNat (b :: rest).length val)
            else resolve id) := by
        funext id; by_cases h : id = 0 <;> simp [h]
      rw [hfun] at ih'
      simp only [fillSigma]
      exact ih'

private theorem fillSigma_inBounds
    (σ : WasmHeapMap (Option UInt8)) (resolve : Nat → Option Mem) (mem : Mem)
    (addr : UInt32) (bytes : List UInt8) (val : UInt8)
    (hresolve : resolve 0 = some mem)
    (hinBounds : heapAddressesInBounds σ resolve)
    (hbound : addr.toNat + bytes.length ≤ mem.pages * 65536)
    (hnowrap : addr.toNat + bytes.length < 4294967296) :
    heapAddressesInBounds (fillSigma σ addr bytes val)
      (fun id => if id = 0 then some (mem.fill addr.toNat bytes.length val)
        else resolve id) := by
  induction bytes generalizing σ addr mem resolve with
  | nil =>
      simp only [fillSigma, List.length_nil, Mem.fill_zero]
      have hfun : (fun id => if id = 0 then some mem else resolve id) = resolve := by
        funext id; by_cases h : id = 0 <;> simp [h, hresolve]
      rw [hfun]; exact hinBounds
  | cons b rest ih =>
      have h1 : (addr + 1).toNat = addr.toNat + 1 := by
        simp only [UInt32.toNat_add, show (1 : UInt32).toNat = 1 from rfl]
        simp only [List.length_cons] at hnowrap; omega
      have hnowrap' : (addr + 1).toNat + rest.length < 4294967296 := by
        rw [h1]; simp only [List.length_cons] at hnowrap; omega
      have hbound' : (addr + 1).toNat + rest.length ≤ (mem.write8 addr val).pages * 65536 := by
        have hp : (mem.write8 addr val).pages = mem.pages := rfl
        rw [hp, h1]; simp only [List.length_cons] at hbound; omega
      have ih' := ih (insert σ ⟨0, addr⟩ (some val))
          (fun id => if id = 0 then some (mem.write8 addr val) else resolve id)
          (mem.write8 addr val) (addr + 1) (by simp)
          (store_inBounds σ resolve 0 mem addr val hresolve hinBounds
            (by simp only [List.length_cons] at hbound; omega))
          hbound' hnowrap'
      rw [h1, Mem.write8_fill_eq] at ih'
      have hfun : (fun id => if id = 0 then some (mem.fill addr.toNat (rest.length + 1) val)
          else (if id = 0 then some (mem.write8 addr val) else resolve id)) =
          (fun id => if id = 0 then some (mem.fill addr.toNat (b :: rest).length val)
            else resolve id) := by
        funext id; by_cases h : id = 0 <;> simp [h]
      rw [hfun] at ih'
      simp only [fillSigma]
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
      pointsToBytes 0 addr oldBytes ==∗
      stateInterp (GF := WasmHeapGF α)
        { store with wasm :=
            { store.wasm with mem :=
                store.wasm.mem.fill addr.toNat oldBytes.length val } }
        steps observations threads ∗
      pointsToBytes 0 addr (List.replicate oldBytes.length val) := by
  iintro ⟨Hstate, Hbytes⟩
  iopen_state Hstate
  imod fillSigma_ghost σ addr oldBytes val $$ [$Hheap $Hbytes] with
    ⟨Hheap, Hbytes, %Hbelow⟩
  ihave Hexc' : machineAuxInterp (fillSigma σ addr oldBytes val)
      store.wasm.mem.pages
      store.wasm.exns store.wasm.tagIds $$ [Hexc]
  · iapply machineAuxInterp_heap_mono Hbelow
    iexact Hexc
  imodintro
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth HhostEnvAuth Hstate_auth Hexc']
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
    iexists runtimeModuleσ
    iexists hostEnvσ
    iframe Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth HhostEnvAuth Hstate_auth
    isplitr [Hexc']
    · ipureintro
      have h_ag := fillSigma_agrees σ (storeResolve store) store.wasm.mem addr oldBytes val
        (storeResolve_zero store) Hfacts.1 hnowrap
      rw [storeResolve_update_mem0] at h_ag
      have h_bn := fillSigma_inBounds σ (storeResolve store) store.wasm.mem addr oldBytes val
        (storeResolve_zero store) Hfacts.2.1 hbound hnowrap
      rw [storeResolve_update_mem0] at h_bn
      exact ⟨h_ag, h_bn, Hfacts.2.2⟩
    · simp only [Mem.fill_pages]
      iexact Hexc'
  · iexact Hbytes

-- ghost map updated by a bulk copy: oldBytes[k] replaced by srcBytes[k] at dst+k
private def copySigma (σ : WasmHeapMap (Option UInt8)) (dst : UInt32)
    (oldBytes srcBytes : List UInt8) : WasmHeapMap (Option UInt8) :=
  match oldBytes, srcBytes with
  | _ :: oldRest, s :: srcRest =>
      copySigma (insert σ ⟨0, dst⟩ (some s)) (dst + 1) oldRest srcRest
  | _, _ => σ

-- get? outside memory 0's [dst, dst+oldBytes.length) is unchanged
private theorem copySigma_get?_out
    (σ : WasmHeapMap (Option UInt8)) (dst : UInt32)
    (oldBytes srcBytes : List UInt8) (key : MemoryKey)
    (hlen : srcBytes.length = oldBytes.length)
    (hnowrap : dst.toNat + oldBytes.length < 4294967296)
    (hout : key.memId ≠ 0 ∨
      key.addr.toNat < dst.toNat ∨ dst.toNat + oldBytes.length ≤ key.addr.toNat) :
    get? (copySigma σ dst oldBytes srcBytes) key = get? σ key := by
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
          have hne : key ≠ ⟨0, dst⟩ := by
            intro heq
            rcases hout with hm | hr
            · exact hm (by rw [heq])
            · rw [heq] at hr; simp only [List.length_cons] at hr; omega
          have hout' : key.memId ≠ 0 ∨
              key.addr.toNat < (dst + 1).toNat ∨
              (dst + 1).toNat + bRest.length ≤ key.addr.toNat := by
            rcases hout with hm | hr
            · exact Or.inl hm
            · refine Or.inr ?_
              rw [h1]; simp only [List.length_cons] at hr; omega
          rw [ih (insert σ ⟨0, dst⟩ (some s)) (dst + 1) sRest hlen' hnowrap' hout',
              get?_insert_ne hne.symm]

-- get? at memory 0's dst + ofNat j gives some (some srcBytes[j])
private theorem copySigma_get?_in
    (σ : WasmHeapMap (Option UInt8)) (dst : UInt32)
    (oldBytes srcBytes : List UInt8) (j : Nat)
    (hlen : srcBytes.length = oldBytes.length)
    (hj : j < srcBytes.length)
    (hnowrap : dst.toNat + srcBytes.length < 4294967296) :
    get? (copySigma σ dst oldBytes srcBytes) ⟨0, dst + UInt32.ofNat j⟩ =
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
              rw [copySigma_get?_out (insert σ ⟨0, dst⟩ (some s)) (dst + 1) bRest sRest
                    ⟨0, dst⟩ hlen' (by omega)
                    (Or.inr (Or.inl (by show dst.toNat < (dst + 1).toNat; rw [h1]; omega))),
                  get?_insert_eq rfl]
          | succ j' =>
              have hj' : j' < sRest.length := by simpa [List.length_cons] using hj
              rw [byte_offset_succ dst j',
                  ih (insert σ ⟨0, dst⟩ (some s)) (dst + 1) bRest j' hlen' hj' hnowrap']
              simp [List.getElem_cons_succ]

-- Iris ghost update: pointsToBytes 0 dst oldBytes → pointsToBytes 0 dst srcBytes
private theorem copySigma_ghost [WasmSmallStepGS hlc α]
    (σ : WasmHeapMap (Option UInt8)) (dst : UInt32)
    (oldBytes srcBytes : List UInt8)
    (hlen : srcBytes.length = oldBytes.length) :
    genHeapInterp σ ∗ pointsToBytes 0 dst oldBytes ==∗
    genHeapInterp (copySigma σ dst oldBytes srcBytes) ∗
    pointsToBytes 0 dst srcBytes ∗
    ⌜∀ frontier, HeapBelow σ frontier →
      HeapBelow (copySigma σ dst oldBytes srcBytes) frontier⌝ := by
  induction oldBytes generalizing σ dst srcBytes with
  | nil =>
      cases srcBytes with
      | nil =>
          show genHeapInterp σ ∗ pointsToBytes 0 dst [] ==∗
               genHeapInterp σ ∗ pointsToBytes 0 dst [] ∗
                 ⌜∀ frontier, HeapBelow σ frontier → HeapBelow σ frontier⌝
          iintro ⟨Hheap, Hempty⟩
          imodintro
          isplitl [Hheap]
          · iexact Hheap
          isplitl [Hempty]
          · iexact Hempty
          · ipureintro
            intro frontier Hbelow
            exact Hbelow
      | cons => simp at hlen
  | cons b bRest ih =>
      cases srcBytes with
      | nil => simp at hlen
      | cons s sRest =>
          show genHeapInterp σ ∗ pointsToBytes 0 dst (b :: bRest) ==∗
               genHeapInterp (copySigma (insert σ ⟨0, dst⟩ (some s)) (dst + 1) bRest sRest) ∗
               pointsToBytes 0 dst (s :: sRest) ∗
               ⌜∀ frontier, HeapBelow σ frontier →
                 HeapBelow
                   (copySigma (insert σ ⟨0, dst⟩ (some s))
                     (dst + 1) bRest sRest) frontier⌝
          iintro ⟨Hheap, Hbytes⟩
          ihave Hbytes := (pointsToBytes_cons 0 dst b bRest).mp $$ Hbytes
          icases Hbytes with ⟨Hhead, Hrest⟩
          ihave_heap_valid hlookup :
              ⌜get? σ ⟨0, dst⟩ = some (some b)⌝ $$ [Hheap Hhead]
          imod genHeap_update (v₂ := some s) $$ [$Hheap $Hhead] with ⟨Hheap, Hhead⟩
          imod (ih (insert σ ⟨0, dst⟩ (some s)) (dst + 1) sRest
                  (by simpa [List.length_cons] using hlen)) $$
              [$Hheap $Hrest] with ⟨Hheap, Hrest, %HbelowRest⟩
          imodintro
          isplitl [Hheap]
          · iexact Hheap
          isplitl [Hhead Hrest]
          · iapply (pointsToBytes_cons 0 dst s sRest).mpr
            isplitl [Hhead]
            · iexact Hhead
            · iexact Hrest
          · ipureintro
            intro frontier Hbelow
            apply HbelowRest frontier
            exact HeapBelow.insert_existing Hbelow ⟨0, dst⟩ (some s)
              ⟨some b, hlookup⟩

-- heapAgreesWithMem for copySigma, parameterized by the new physical memory
private theorem copySigma_agrees_of_read_eq
    (σ : WasmHeapMap (Option UInt8)) (resolve : Nat → Option Mem) (mem newMem : Mem)
    (dst : UInt32) (oldBytes srcBytes : List UInt8)
    (hlen : srcBytes.length = oldBytes.length)
    (hresolve : resolve 0 = some mem)
    (hagree : heapAgreesWithMem σ resolve)
    (hnowrap : dst.toNat + oldBytes.length < 4294967296)
    (h_in : ∀ k b, srcBytes[k]? = some b → newMem.read8 (dst + UInt32.ofNat k) = b)
    (h_out : ∀ addr : UInt32,
        addr.toNat < dst.toNat ∨ dst.toNat + oldBytes.length ≤ addr.toNat →
        newMem.read8 addr = mem.read8 addr) :
    heapAgreesWithMem (copySigma σ dst oldBytes srcBytes)
      (fun id => if id = 0 then some newMem else resolve id) := by
  intro key v hlookup
  by_cases hmem : key.memId = 0
  · by_cases hrange : dst.toNat ≤ key.addr.toNat ∧
        key.addr.toNat < dst.toNat + oldBytes.length
    · obtain ⟨hle, hlt⟩ := hrange
      let k : Nat := key.addr.toNat - dst.toNat
      have hk : k < srcBytes.length := by omega
      have hget : srcBytes[k]? = some (srcBytes[k]'hk) := List.getElem?_eq_getElem hk
      have h_addr_eq : key.addr = dst + UInt32.ofNat k := by
        apply UInt32.toNat_inj.mp
        rw [UInt32.toNat_add]
        show key.addr.toNat = (dst.toNat + k % 2 ^ 32) % 2 ^ 32
        omega
      have hkey : key = (⟨0, dst + UInt32.ofNat k⟩ : MemoryKey) := by
        cases key; simp_all
      rw [hkey] at hlookup
      rw [copySigma_get?_in σ dst oldBytes srcBytes k hlen hk (hlen ▸ hnowrap)] at hlookup
      have hv : srcBytes[k]'hk = v := Option.some.inj (Option.some.inj hlookup)
      refine ⟨newMem, by simp [hmem], ?_⟩
      rw [h_addr_eq]
      exact (h_in k (srcBytes[k]'hk) hget).trans hv
    · have hout : key.addr.toNat < dst.toNat ∨
          dst.toNat + oldBytes.length ≤ key.addr.toNat := by omega
      rw [copySigma_get?_out σ dst oldBytes srcBytes key hlen hnowrap (Or.inr hout)] at hlookup
      obtain ⟨m, hm, hr⟩ := hagree key v hlookup
      rw [hmem] at hm
      have hmeq : m = mem := Option.some.inj (hm.symm.trans hresolve)
      subst hmeq
      exact ⟨newMem, by simp [hmem], (h_out key.addr hout).trans hr⟩
  · rw [copySigma_get?_out σ dst oldBytes srcBytes key hlen hnowrap (Or.inl hmem)] at hlookup
    obtain ⟨m, hm, hr⟩ := hagree key v hlookup
    exact ⟨m, by simp [hmem, hm], hr⟩

-- heapAddressesInBounds for copySigma
private theorem copySigma_inBounds
    (σ : WasmHeapMap (Option UInt8)) (resolve : Nat → Option Mem) (mem newMem : Mem)
    (dst : UInt32) (oldBytes srcBytes : List UInt8)
    (hlen : srcBytes.length = oldBytes.length)
    (hresolve : resolve 0 = some mem)
    (hinBounds : heapAddressesInBounds σ resolve)
    (hbound : dst.toNat + oldBytes.length ≤ mem.pages * 65536)
    (hnowrap : dst.toNat + oldBytes.length < 4294967296)
    (h_pages : newMem.pages = mem.pages) :
    heapAddressesInBounds (copySigma σ dst oldBytes srcBytes)
      (fun id => if id = 0 then some newMem else resolve id) := by
  intro key hlookup
  by_cases hmem : key.memId = 0
  · refine ⟨newMem, by simp [hmem], ?_⟩
    rw [h_pages]
    by_cases hrange : dst.toNat ≤ key.addr.toNat ∧
        key.addr.toNat < dst.toNat + oldBytes.length
    · omega
    · have hout : key.addr.toNat < dst.toNat ∨
          dst.toNat + oldBytes.length ≤ key.addr.toNat := by omega
      rw [copySigma_get?_out σ dst oldBytes srcBytes key hlen hnowrap (Or.inr hout)] at hlookup
      obtain ⟨m, hm, hlt⟩ := hinBounds key hlookup
      rw [hmem] at hm
      have hmeq : m = mem := Option.some.inj (hm.symm.trans hresolve)
      exact hmeq ▸ hlt
  · rw [copySigma_get?_out σ dst oldBytes srcBytes key hlen hnowrap (Or.inl hmem)] at hlookup
    obtain ⟨m, hm, hlt⟩ := hinBounds key hlookup
    exact ⟨m, by simp [hmem, hm], hlt⟩

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
      pointsToBytes 0 src srcBytes ∗
      pointsToBytes 0 dst oldDstBytes ==∗
      stateInterp (GF := WasmHeapGF α)
        { store with wasm :=
            { store.wasm with mem :=
                store.wasm.mem.copy dst.toNat src.toNat oldDstBytes.length } }
        steps observations threads ∗
      pointsToBytes 0 src srcBytes ∗
      pointsToBytes 0 dst srcBytes := by
  iintro ⟨Hstate, Hsrc, Hdst⟩
  ihave_pure hagree :
      ⌜∀ i b, srcBytes[i]? = some b →
          store.wasm.mem.read8 (src + UInt32.ofNat i) = b ∧
          (src + UInt32.ofNat i).toNat < store.wasm.mem.pages * 65536⌝ using
    stateInterp_pointsToBytes_agree store steps observations threads src srcBytes $$
      [Hstate Hsrc]
  iopen_state Hstate
  imod copySigma_ghost σ dst oldDstBytes srcBytes hlen $$ [$Hheap $Hdst] with
    ⟨Hheap, Hdst, %Hbelow⟩
  ihave Hexc' : machineAuxInterp (copySigma σ dst oldDstBytes srcBytes)
      store.wasm.mem.pages
      store.wasm.exns store.wasm.tagIds $$ [Hexc]
  · iapply machineAuxInterp_heap_mono Hbelow
    iexact Hexc
  imodintro
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth HhostEnvAuth Hstate_auth Hexc']
  · iapply (stateInterp_eq
        { store with wasm :=
            { store.wasm with mem :=
                store.wasm.mem.copy dst.toNat src.toNat oldDstBytes.length } }
        steps observations threads).mpr
    iexists copySigma σ dst oldDstBytes srcBytes
    iexists globalσ; iexists dataSegmentσ; iexists tableσ; iexists elementSegmentσ
    iexists runtimeModuleσ; iexists hostEnvσ
    iframe Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth HhostEnvAuth Hstate_auth
    isplitr [Hexc']
    · ipureintro
      have h_ag :=
        copySigma_agrees_of_read_eq σ (storeResolve store) store.wasm.mem
          (store.wasm.mem.copy dst.toNat src.toNat oldDstBytes.length)
          dst oldDstBytes srcBytes hlen (storeResolve_zero store) Hfacts.1 hdst_nowrap
          (fun k b hget => by
            have hk : k < srcBytes.length := by
              suffices h : ¬ srcBytes.length ≤ k by omega
              intro hle
              simp [List.getElem?_eq_none hle] at hget
            have h_dst_k := add_ofNat_toNat dst k (by rw [hlen] at hk; omega)
            have h_src_k := add_ofNat_toNat src k (by omega)
            have h_copy := Mem.copy_read8_in store.wasm.mem dst.toNat src.toNat
                oldDstBytes.length (dst + UInt32.ofNat k)
                ⟨by omega, by rw [hlen] at hk; omega⟩
            rw [h_dst_k, Nat.add_sub_cancel_left] at h_copy
            have h_src_read := (hagree k b hget).1
            simp only [Mem.read8, h_src_k] at h_src_read
            exact h_copy.trans h_src_read)
          (fun addr hout =>
            Mem.copy_read8_out store.wasm.mem dst.toNat src.toNat oldDstBytes.length addr
              (by omega))
      rw [storeResolve_update_mem0] at h_ag
      have h_bn :=
        copySigma_inBounds σ (storeResolve store) store.wasm.mem
          (store.wasm.mem.copy dst.toNat src.toNat oldDstBytes.length)
          dst oldDstBytes srcBytes hlen (storeResolve_zero store) Hfacts.2.1
          hdst_bound hdst_nowrap
          (Mem.copy_pages store.wasm.mem dst.toNat src.toNat oldDstBytes.length)
      rw [storeResolve_update_mem0] at h_bn
      exact ⟨h_ag, h_bn, Hfacts.2.2⟩
    · simp only [Mem.copy_pages]
      iexact Hexc'
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
      dataSegmentPointsToAt 0 segmentIndex (some segmentBytes) ∗
      pointsToBytes 0 dst oldDstBytes ==∗
      stateInterp (GF := WasmHeapGF α)
        { store with wasm :=
            { store.wasm with mem :=
                store.wasm.mem.writeBytesFrom dst.toNat segmentBytes srcOff len } }
        steps observations threads ∗
      dataSegmentPointsToAt 0 segmentIndex (some segmentBytes) ∗
      pointsToBytes 0 dst ((segmentBytes.drop srcOff).take len) := by
  let newDstBytes := (segmentBytes.drop srcOff).take len
  have hlen_new : newDstBytes.length = len := by
    simp only [newDstBytes, List.length_take, List.length_drop]; omega
  have hlen_eq : newDstBytes.length = oldDstBytes.length := by omega
  iintro ⟨Hstate, Hseg, Hdst⟩
  iopen_state Hstate
  imod copySigma_ghost σ dst oldDstBytes newDstBytes hlen_eq $$
      [$Hheap $Hdst] with ⟨Hheap, Hdst, %Hbelow⟩
  ihave Hexc' : machineAuxInterp (copySigma σ dst oldDstBytes newDstBytes)
      store.wasm.mem.pages
      store.wasm.exns store.wasm.tagIds $$ [Hexc]
  · iapply machineAuxInterp_heap_mono Hbelow
    iexact Hexc
  imodintro
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth HhostEnvAuth Hstate_auth Hexc']
  · iapply (stateInterp_eq
        { store with wasm :=
            { store.wasm with mem :=
                store.wasm.mem.writeBytesFrom dst.toNat segmentBytes srcOff len } }
        steps observations threads).mpr
    iexists copySigma σ dst oldDstBytes newDstBytes
    iexists globalσ; iexists dataSegmentσ; iexists tableσ; iexists elementSegmentσ
    iexists runtimeModuleσ; iexists hostEnvσ
    iframe Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth HhostEnvAuth Hstate_auth
    isplitr [Hexc']
    · ipureintro
      have h_ag :=
        copySigma_agrees_of_read_eq σ (storeResolve store) store.wasm.mem
          (store.wasm.mem.writeBytesFrom dst.toNat segmentBytes srcOff len)
          dst oldDstBytes newDstBytes hlen_eq (storeResolve_zero store) Hfacts.1
          (hlen ▸ hdst_nowrap)
          (fun k b hget => by
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
          have hget_some : newDstBytes[k]? = some (newDstBytes[k]'hk) :=
            List.getElem?_eq_getElem hk
          have hb : b = newDstBytes[k]'hk := Option.some.inj (hget.symm.trans hget_some)
          have hval : newDstBytes[k]'hk = segmentBytes[srcOff + k]'hbound_seg := by
            simp [newDstBytes, List.getElem_take, List.getElem_drop]
          have hboth : segmentBytes[srcOff + ((dst + UInt32.ofNat k).toNat - dst.toNat)]? =
                       segmentBytes[srcOff + k]? := by rw [hidx]
          have hg_actual := List.getElem?_eq_getElem (l := segmentBytes)
                              (i := srcOff + ((dst + UInt32.ofNat k).toNat - dst.toNat))
                              hbound_actual
          have hg_k := List.getElem?_eq_getElem (l := segmentBytes) (i := srcOff + k)
                          hbound_seg
          exact (Option.some.inj (hg_actual.symm.trans (hboth.trans hg_k))).trans
                (hval.symm.trans hb.symm))
          (fun addr hout =>
            Mem.writeBytesFrom_read8_out store.wasm.mem dst.toNat segmentBytes srcOff len addr
              (by omega))
      rw [storeResolve_update_mem0] at h_ag
      have h_bn :=
        copySigma_inBounds σ (storeResolve store) store.wasm.mem
          (store.wasm.mem.writeBytesFrom dst.toNat segmentBytes srcOff len)
          dst oldDstBytes newDstBytes hlen_eq (storeResolve_zero store) Hfacts.2.1
          (hlen ▸ hdst_bound) (hlen ▸ hdst_nowrap)
          (Mem.writeBytesFrom_pages store.wasm.mem dst.toNat segmentBytes srcOff len)
      rw [storeResolve_update_mem0] at h_bn
      exact ⟨h_ag, h_bn, Hfacts.2.2⟩
    · simp only [Mem.writeBytesFrom_pages]
      iexact Hexc'
  · isplitl [Hseg]
    · iexact Hseg
    · iexact Hdst

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
        steps observations threads ∗
      hostStateOwn host := by
  iintro ⟨Hσ, HP⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hσ with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %runtimeModuleσ, %hostEnvσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, HruntimeModuleAuth, HruntimeModuleBigSep,
      HruntimeInstances, HinstanceAuth, HhostEnvAuth, Hstate_auth, %Hfacts, Hexc⟩
  imod hostStateOwn_update store.wasm.host host $$ [$Hstate_auth $HP] with ⟨Hauth', HP'⟩
  imodintro
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth HhostEnvAuth Hauth' Hexc]
  · iapply (stateInterp_eq
      { store with wasm := { store.wasm with host } }
      steps observations threads).mpr
    iexists σ; iexists globalσ; iexists dataSegmentσ; iexists tableσ
    iexists elementSegmentσ; iexists runtimeModuleσ; iexists hostEnvσ
    iframe Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth HhostEnvAuth Hauth' Hexc
    ipureintro
    exact Hfacts
  · iexact HP'

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
  iopen_state Hstate
  simp only [globalPointsToAt]
  ihave %hlookup := globalPointsTo_lookup globalσ ⟨0, index⟩ value $$ Hglobals Hglobal
  ipureintro
  exact Hfacts.2.2.1 index value hlookup

/-- Owned table state determines the corresponding physical instantiated table. -/
theorem stateInterp_table_facts [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (tableIndex : Nat) (table : TableInst) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      tablePointsToAt 0 tableIndex table ==∗
      ⌜store.wasm.tables[tableIndex]? = some table⌝ := by
  iintro ⟨Hstate, Htable⟩
  iopen_state Hstate
  simp only [tablePointsToAt]
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
  iopen_state Hstate
  simp only [globalPointsToAt]
  ihave %hlookup :=
    globalPointsTo_lookup globalσ ⟨0, index⟩ oldValue $$ Hglobals Hglobal
  imod globalPointsTo_update globalσ ⟨0, index⟩ oldValue newValue $$
      Hglobals Hglobal with
    ⟨Hglobals, Hglobal⟩
  imodintro
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth HhostEnvAuth Hstate_auth Hexc]
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
    iexists runtimeModuleσ
    iexists hostEnvσ
    iframe Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth HhostEnvAuth Hstate_auth Hexc
    ipureintro
    exact ⟨Hfacts.1, Hfacts.2.1,
      ⟨global_store_sound globalσ store.wasm.globals
          index oldValue newValue Hfacts.2.2.1 hlookup,
        Hfacts.2.2.2⟩⟩
  · iexact Hglobal

/-- Owned passive-segment state determines the corresponding physical entry. -/
theorem stateInterp_dataSegment_facts [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (index : Nat) (value : Option (List UInt8)) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      dataSegmentPointsToAt 0 index value ==∗
      ⌜store.wasm.dataSegments[index]? = some value⌝ := by
  iintro ⟨Hstate, Hsegment⟩
  iopen_state Hstate
  simp only [dataSegmentPointsToAt]
  ihave %hlookup :=
    dataSegmentPointsTo_lookup dataSegmentσ ⟨0, index⟩ value $$
      Hsegments Hsegment
  ipureintro
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
  iopen_state Hstate
  simp only [dataSegmentPointsToAt]
  ihave %hlookup :=
    dataSegmentPointsTo_lookup dataSegmentσ ⟨0, index⟩ oldValue $$
      Hsegments Hsegment
  imod dataSegmentPointsTo_update dataSegmentσ ⟨0, index⟩ oldValue none $$
      Hsegments Hsegment with
    ⟨Hsegments, Hsegment⟩
  imodintro
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth HhostEnvAuth Hstate_auth Hexc]
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
    iexists runtimeModuleσ
    iexists hostEnvσ
    iframe
    ipureintro
    exact ⟨Hfacts.1, Hfacts.2.1, Hfacts.2.2.1,
      dataSegment_store_sound dataSegmentσ store.wasm.dataSegments
        index oldValue none Hfacts.2.2.2.1 hlookup,
      Hfacts.2.2.2.2⟩
  · iexact Hsegment

/-- Element-segment ownership identifies its physical live or dropped state. -/
theorem stateInterp_elementSegment_facts [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (index : Nat) (value : Option (List (Option Nat))) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      elementSegmentPointsToAt 0 index value ==∗
      ⌜store.wasm.elementSegments[index]? = some value⌝ := by
  iintro ⟨Hstate, Hsegment⟩
  iopen_state Hstate
  simp only [elementSegmentPointsToAt]
  ihave %hlookup :=
    elementSegmentPointsTo_lookup elementSegmentσ ⟨0, index⟩ value $$
      HelementSegments Hsegment
  ipureintro
  exact Hfacts.2.2.2.2.2.1 index value hlookup

syntax "wasm_data_segment_agree " ident ", " term ", " term ", " term
  " $$ " specPat : tactic

set_option hygiene false in
macro_rules
  | `(tactic| wasm_data_segment_agree $fact:ident, $index:term,
        $value:term, $observations:term $$ $resources:specPat) =>
    `(tactic|
      ihave_pure $fact :
          ⌜store.wasm.dataSegments[$index]? = some $value⌝ using
        stateInterp_dataSegment_facts store ns $observations nt $index $value
          $$ $resources)

syntax "wasm_element_segment_agree " ident ", " term ", " term ", " term
  " $$ " specPat : tactic

set_option hygiene false in
macro_rules
  | `(tactic| wasm_element_segment_agree $fact:ident, $index:term,
        $value:term, $observations:term $$ $resources:specPat) =>
    `(tactic|
      ihave_pure $fact :
          ⌜store.wasm.elementSegments[$index]? = some $value⌝ using
        stateInterp_elementSegment_facts store ns $observations nt $index $value
          $$ $resources)

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
  iopen_state Hstate
  simp only [elementSegmentPointsToAt]
  ihave %hlookup :=
    elementSegmentPointsTo_lookup elementSegmentσ ⟨0, index⟩ oldValue $$
      HelementSegments Hsegment
  imod elementSegmentPointsTo_update
      elementSegmentσ ⟨0, index⟩ oldValue none $$
      HelementSegments Hsegment with
    ⟨HelementSegments, Hsegment⟩
  imodintro
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth HhostEnvAuth Hstate_auth Hexc]
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
    iexists insert elementSegmentσ ⟨0, index⟩ none
    iexists runtimeModuleσ
    iexists hostEnvσ
    iframe
    ipureintro
    exact ⟨Hfacts.1, Hfacts.2.1, Hfacts.2.2.1,
      Hfacts.2.2.2.1,
      ⟨Hfacts.2.2.2.2.1,
        elementSegment_store_sound elementSegmentσ
          store.wasm.elementSegments index oldValue none
          Hfacts.2.2.2.2.2.1 hlookup,
      Hfacts.2.2.2.2.2.2.1, Hfacts.2.2.2.2.2.2.2⟩⟩
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
  ihave_pure Hphysical : ⌜store.wasm.tables[index]? = some table⌝ using
    stateInterp_table_facts store steps observations threads index table $$
      [Hstate Htable]
  imodintro
  iframe
  ipureintro
  exact Hphysical

/-- Derive the physical table associated with an owned table fragment. -/
syntax "wasm_table_agree " ident ", " term ", " term ", " term
  " $$ " specPat : tactic

set_option hygiene false in
macro_rules
  | `(tactic| wasm_table_agree $fact:ident, $index:term, $table:term,
        $observations:term $$ $resources:specPat) =>
    `(tactic|
      ihave_pure $fact : ⌜store.wasm.tables[$index]? = some $table⌝ using
        stateInterp_table_facts store ns $observations nt $index $table $$
          $resources)

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
  iopen_state Hstate
  simp only [tablePointsToAt]
  ihave %hlookup :=
    tablePointsTo_lookup tableσ ⟨0, index⟩ oldTable $$ Htables Htable
  imod tablePointsTo_update tableσ ⟨0, index⟩ oldTable newTable $$
      Htables Htable with
    ⟨Htables, Htable⟩
  imodintro
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth HhostEnvAuth Hstate_auth Hexc]
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
    iexists runtimeModuleσ
    iexists hostEnvσ
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
  iopen_state Hstate
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

/-- Derive the current runtime module from its Iris ownership and the physical
state, using the lifting proof's conventional context names. -/
syntax "wasm_runtime_module_agree " term ", " term ", " term
  " $$ " specPat : tactic

set_option hygiene false in
macro_rules
  | `(tactic| wasm_runtime_module_agree $observations:term,
        $instanceId:term, $module:term $$ $resources:specPat) =>
    `(tactic|
      (ihave %Hmodule : ⌜store.runtime.currentModule = $module⌝ $$
          [Hσ Hruntime]
       · imod stateInterp_runtimeModule_agree store ns $observations nt
           $instanceId $module $$ $resources with %Hmodule
         ipureintro
         exact Hmodule))

/-- Owned exception state determines the corresponding physical exception
entry in the store's exception table. -/
theorem stateInterp_exception_facts [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (index : Nat) (dq : DFrac) (tagAndArgs : Nat × List Value) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      exceptionPointsTo index dq tagAndArgs ==∗
      ⌜store.wasm.exns[index]? = some tagAndArgs⌝ := by
  iintro ⟨Hstate, Hexception⟩
  imodintro
  iopen_state Hstate
  iunfold machineAuxInterp at Hexc
  icases Hexc with ⟨Hpages, Hdomain, Hexceptions⟩
  ihave %hlookup :=
    exceptionInterp_lookup store.wasm.exns store.wasm.tagIds index dq tagAndArgs $$
      [$Hexceptions $Hexception]
  ipureintro
  exact hlookup

/-- Ghost knowledge of the tag table is a prefix of the physical tag table.
This is the *only* channel through which a rule may learn anything about
tags; the state interpretation itself constrains nothing, which is what keeps
it valid for the linked, multi-instance stores introduced by module linking. -/
theorem stateInterp_tagTable_prefix [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat) (ids : List Nat) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      tagTableOwn ids ==∗
      ⌜ids.IsPrefix store.wasm.tagIds⌝ := by
  iintro ⟨Hstate, Howned⟩
  imodintro
  iopen_state Hstate
  iunfold machineAuxInterp at Hexc
  icases Hexc with ⟨Hpages, Hdomain, Hexceptions⟩
  ihave %hprefix :=
    exceptionInterp_tagPrefix store.wasm.exns store.wasm.tagIds ids $$
      [$Hexceptions $Howned]
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

theorem stateInterp_instances_agree [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (instances : Array (ModuleInstance α)) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      runtimeInstancesOwn instances ==∗
      ⌜store.runtime.instances = instances⌝ := by
  iintro ⟨Hstate, Hexpected⟩
  iopen_state Hstate
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
  iopen_state Hstate
  icombine HinstanceAuth Hfrag as Hcombined
  ihave %hagrees := currentInstanceOwn_agree store.runtime.entry id $$ Hcombined
  ipureintro
  exact hagrees

/-- Derive the current instance id from its Iris ownership and the physical
state, using the lifting proof's conventional context names. -/
syntax "wasm_current_instance_agree " term ", " term
  " $$ " specPat : tactic

set_option hygiene false in
macro_rules
  | `(tactic| wasm_current_instance_agree $observations:term,
        $instanceId:term $$ $resources:specPat) =>
    `(tactic|
      (ihave %Hentry : ⌜store.runtime.entry = $instanceId⌝ $$
          [Hσ HinstanceOwn]
       · imod stateInterp_currentInstance_agree store ns $observations nt
           $instanceId $$ $resources with %Hentry
         ipureintro
         exact Hentry))

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
  iopen_state Hstate
  imod currentInstanceOwn_update store.runtime.entry newId $$ [$HinstanceAuth $Hfrag] with ⟨HinstanceAuth', Hfrag'⟩
  imodintro
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth' HhostEnvAuth Hstate_auth Hexc]
  · iapply (stateInterp_eq
      { store with runtime := { store.runtime with entry := newId } }
      steps observations threads).mpr
    iexists σ; iexists globalσ; iexists dataSegmentσ; iexists tableσ; iexists elementSegmentσ; iexists runtimeModuleσ; iexists hostEnvσ
    have hres : storeResolve { store with runtime := { store.runtime with entry := newId } } = storeResolve store := rfl
    simp only [hres]
    iframe Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth' HhostEnvAuth Hstate_auth Hexc
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
  iopen_state Hstate
  imod currentInstanceOwn_update_of_any store.runtime.entry calleeId newId $$
      [$HinstanceAuth $Hfrag] with ⟨HinstanceAuth', Hfrag', %heq⟩
  imodintro
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth' HhostEnvAuth Hstate_auth Hexc]
  · iapply (stateInterp_eq
        { store with runtime := { store.runtime with entry := newId } }
        steps observations threads).mpr
    iexists σ; iexists globalσ; iexists dataSegmentσ; iexists tableσ; iexists elementSegmentσ; iexists runtimeModuleσ; iexists hostEnvσ
    have hres : storeResolve { store with runtime := { store.runtime with entry := newId } } = storeResolve store := rfl
    simp only [hres]
    iframe Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth' HhostEnvAuth Hstate_auth Hexc
    ipureintro
    exact Hfacts
  isplitl [Hfrag']
  · iexact Hfrag'
  · ipureintro; exact heq

-- push doesn't affect elements before the pushed index

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
  iopen_state Hstate
  ihave_heap_valid hg0 :
      ⌜get? σ ⟨0, address⟩ = some (some (u32Byte value 0))⌝ $$ [Hheap H0]
  ihave_heap_valid hg1 :
      ⌜get? σ ⟨0, address + 1⟩ = some (some (u32Byte value 1))⌝ $$ [Hheap H1]
  ihave_heap_valid hg2 :
      ⌜get? σ ⟨0, address + 2⟩ = some (some (u32Byte value 2))⌝ $$ [Hheap H2]
  ihave_heap_valid hg3 :
      ⌜get? σ ⟨0, address + 3⟩ = some (some (u32Byte value 3))⌝ $$ [Hheap H3]
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
  ihave_pure Hfacts :
      ⌜store.wasm.mem.read32 address = value ∧
        address.toNat + 4 ≤ store.wasm.mem.pages * 65536⌝ using
    stateInterp_pointsTo_u32_facts store steps observations threads
      address value h1 h2 h3 $$ [Hstate Hword]
  imodintro
  iframe
  ipureintro
  exact Hfacts

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
  iopen_state Hstate
  ihave_heap_valid hg0 :
      ⌜get? σ ⟨0, address⟩ = some (some (u64Byte value 0))⌝ $$ [Hheap H0]
  ihave_heap_valid hg1 :
      ⌜get? σ ⟨0, address + 1⟩ = some (some (u64Byte value 1))⌝ $$ [Hheap H1]
  ihave_heap_valid hg2 :
      ⌜get? σ ⟨0, address + 2⟩ = some (some (u64Byte value 2))⌝ $$ [Hheap H2]
  ihave_heap_valid hg3 :
      ⌜get? σ ⟨0, address + 3⟩ = some (some (u64Byte value 3))⌝ $$ [Hheap H3]
  ihave_heap_valid hg4 :
      ⌜get? σ ⟨0, address + 4⟩ = some (some (u64Byte value 4))⌝ $$ [Hheap H4]
  ihave_heap_valid hg5 :
      ⌜get? σ ⟨0, address + 5⟩ = some (some (u64Byte value 5))⌝ $$ [Hheap H5]
  ihave_heap_valid hg6 :
      ⌜get? σ ⟨0, address + 6⟩ = some (some (u64Byte value 6))⌝ $$ [Hheap H6]
  ihave_heap_valid hg7 :
      ⌜get? σ ⟨0, address + 7⟩ = some (some (u64Byte value 7))⌝ $$ [Hheap H7]
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
  ihave_pure Hfacts :
      ⌜store.wasm.mem.read64 address = value ∧
        address.toNat + 8 ≤ store.wasm.mem.pages * 65536⌝ using
    stateInterp_pointsTo_u64_facts store steps observations threads
      address value h1 h2 h3 h4 h5 h6 h7 $$ [Hstate Hword]
  imodintro
  iframe
  ipureintro
  exact Hfacts

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
  iopen_state Hstate
  ihave_heap_valid hlookup :
      ⌜get? σ ⟨0, address⟩ = some (some oldValue)⌝ $$ [Hheap Hpointsto]
  imod genHeap_update (v₂ := some newValue) $$ [$Hheap $Hpointsto] with
    ⟨Hheap, Hpointsto⟩
  ihave Hexc' : machineAuxInterp (insert σ ⟨0, address⟩ (some newValue))
      store.wasm.mem.pages
      store.wasm.exns store.wasm.tagIds $$ [Hexc]
  · iapply machineAuxInterp_heap_mono
      (fun frontier Hbelow =>
        HeapBelow.insert_existing Hbelow ⟨0, address⟩ (some newValue)
          ⟨some oldValue, hlookup⟩)
    iexact Hexc
  imodintro
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth HhostEnvAuth Hstate_auth Hexc']
  · iapply (stateInterp_eq
      { store with wasm :=
          { store.wasm with mem := store.wasm.mem.write8 address newValue } }
      steps observations threads).mpr
    iexists insert σ ⟨0, address⟩ (some newValue)
    iexists globalσ
    iexists dataSegmentσ
    iexists tableσ
    iexists elementSegmentσ
    iexists runtimeModuleσ
    iexists hostEnvσ
    iframe Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth HhostEnvAuth Hstate_auth
    isplitr [Hexc']
    · ipureintro
      have h_ag := store_sound σ (storeResolve store) 0 store.wasm.mem address newValue
          (storeResolve_zero store) Hfacts.1
      rw [storeResolve_update_mem0] at h_ag
      have h_bn := store_inBounds σ (storeResolve store) 0 store.wasm.mem address newValue
          (storeResolve_zero store) Hfacts.2.1 hbound
      rw [storeResolve_update_mem0] at h_bn
      exact ⟨h_ag, h_bn, Hfacts.2.2⟩
    · simp only [Mem.write8]
      iexact Hexc'
  · iexact Hpointsto

/-- Ghost update for a host-style bulk byte write.  Unlike `memory.fill`, the
new byte sequence is arbitrary; ownership of an equal-length destination
range is exchanged for ownership of its new contents. -/
theorem stateInterp_write_bytes [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (addr : UInt32) (oldBytes newBytes : List UInt8)
    (hlength : oldBytes.length = newBytes.length)
    (hbound : addr.toNat + newBytes.length ≤
      store.wasm.mem.pages * 65536)
    (hnowrap : addr.toNat + newBytes.length < UInt32.size) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      pointsToBytes 0 addr oldBytes ==∗
      stateInterp (GF := WasmHeapGF α)
        { store with wasm :=
            { store.wasm with mem :=
                store.wasm.mem.writeBytes addr.toNat newBytes } }
        steps observations threads ∗
      pointsToBytes 0 addr newBytes := by
  induction oldBytes generalizing store addr newBytes with
  | nil =>
      cases newBytes with
      | nil =>
          iintro ⟨Hstate, Hbytes⟩
          simp only [Mem.writeBytes_nil]
          imodintro
          isplitl [Hstate]
          · iexact Hstate
          · iexact Hbytes
      | cons b rest => simp at hlength
  | cons old oldRest ih =>
      cases newBytes with
      | nil => simp at hlength
      | cons new newRest =>
          simp only [List.length_cons, Nat.succ.injEq] at hlength
          have h1 : (addr + 1).toNat = addr.toNat + 1 := by
            apply UInt32.add_ofNat_toNat_noWrap addr 1 (by decide)
            simp only [List.length_cons, UInt32.size] at hnowrap ⊢
            omega
          have hheadBound : addr.toNat <
              store.wasm.mem.pages * 65536 := by
            simp only [List.length_cons] at hbound
            omega
          have htailBound : (addr + 1).toNat + newRest.length ≤
              (store.wasm.mem.write8 addr new).pages * 65536 := by
            rw [h1]
            change addr.toNat + 1 + newRest.length ≤
              store.wasm.mem.pages * 65536
            simp only [List.length_cons] at hbound
            omega
          have htailNoWrap : (addr + 1).toNat + newRest.length <
              UInt32.size := by
            rw [h1]
            simp only [List.length_cons] at hnowrap
            omega
          have haddr : UInt32.ofNat addr.toNat = addr := by
            exact UInt32.ofNat_toNat
          have hmem :
              (store.wasm.mem.write8 addr new).writeBytes
                  (addr + 1).toNat newRest =
                store.wasm.mem.writeBytes addr.toNat (new :: newRest) := by
            symm
            rw [Mem.writeBytes_cons store.wasm.mem addr.toNat new newRest
              (by
                simp only [List.length_cons] at hnowrap
                omega)]
            rw [haddr, h1]
          iintro ⟨Hstate, Hbytes⟩
          ihave Hbytes := (pointsToBytes_cons 0 addr old oldRest).mp $$ Hbytes
          icases Hbytes with ⟨Hhead, Hrest⟩
          imod stateInterp_store8 store steps observations threads addr old new
              hheadBound $$ [$Hstate $Hhead] with ⟨Hstate, Hhead⟩
          imod ih
              { store with wasm :=
                  { store.wasm with mem := store.wasm.mem.write8 addr new } }
              (addr + 1) newRest hlength htailBound htailNoWrap $$
              [$Hstate $Hrest] with ⟨Hstate, Hrest⟩
          isimp only [hmem] at Hstate
          imodintro
          isplitl [Hstate]
          · iexact Hstate
          · iapply (pointsToBytes_cons 0 addr new newRest).mpr
            isplitl [Hhead]
            · iexact Hhead
            · iexact Hrest

theorem stateInterp_pointsTo_u16_facts [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (address value : UInt32)
    (h1 : (address + 1).toNat = address.toNat + 1) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      pointsTo_u16 0 address value ==∗
      ⌜store.wasm.mem.read16 address = value &&& 0xFFFF ∧
        address.toNat + 2 ≤ store.wasm.mem.pages * 65536⌝ := by
  iintro ⟨Hstate, Hword⟩
  ihave Hword := (pointsTo_u16_eq 0 address value).mp $$ Hword
  icases Hword with ⟨H0, H1⟩
  iopen_state Hstate
  ihave_heap_valid hg0 :
      ⌜get? σ ⟨0, address⟩ = some (some (u32Byte value 0))⌝ $$ [Hheap H0]
  ihave_heap_valid hg1 :
      ⌜get? σ ⟨0, address + 1⟩ = some (some (u32Byte value 1))⌝ $$ [Hheap H1]
  have hr0 := fromResolver store Hfacts.1 address (u32Byte value 0) hg0
  have hr1 := fromResolver store Hfacts.1 (address + 1) (u32Byte value 1) hg1
  have hb1 := fromResolverBounds store Hfacts.2.1 (address + 1) (by simp [hg1])
  ipureintro
  refine ⟨?_, by rw [h1] at hb1; omega⟩
  simp only [Mem.read8] at hr0 hr1
  simp only [Mem.read16]
  rw [hr0, ← h1, hr1]
  exact u16Byte_reassemble value

private theorem heapBelow_store16
    {σ : WasmHeapMap (Option UInt8)} {frontier : Nat}
    (address oldValue newValue : UInt32)
    (Hbelow : HeapBelow σ frontier)
    (h0 : get? σ ⟨0, address⟩ = some (some (u32Byte oldValue 0)))
    (h1 : get? σ ⟨0, address + 1⟩ =
      some (some (u32Byte oldValue 1))) :
    HeapBelow (store16Heap σ 0 address newValue) frontier := by
  unfold store16Heap
  apply HeapBelow.insert_fresh
    (HeapBelow.insert_fresh Hbelow ⟨0, address⟩
      (some (u32Byte newValue 0))
      (fun hmem => Hbelow ⟨0, address⟩ (some (u32Byte oldValue 0)) h0 hmem))
  exact fun hmem =>
    Hbelow ⟨0, address + 1⟩ (some (u32Byte oldValue 1)) h1 hmem

private theorem heapBelow_store32
    {σ : WasmHeapMap (Option UInt8)} {frontier : Nat}
    (address oldValue newValue : UInt32)
    (Hbelow : HeapBelow σ frontier)
    (h0 : get? σ ⟨0, address⟩ = some (some (u32Byte oldValue 0)))
    (h1 : get? σ ⟨0, address + 1⟩ = some (some (u32Byte oldValue 1)))
    (h2 : get? σ ⟨0, address + 2⟩ = some (some (u32Byte oldValue 2)))
    (h3 : get? σ ⟨0, address + 3⟩ = some (some (u32Byte oldValue 3))) :
    HeapBelow (store32Heap σ 0 address newValue) frontier := by
  unfold store32Heap
  apply HeapBelow.insert_fresh
    (HeapBelow.insert_fresh
      (HeapBelow.insert_fresh
        (HeapBelow.insert_fresh Hbelow ⟨0, address⟩
          (some (u32Byte newValue 0))
          (fun hmem =>
            Hbelow ⟨0, address⟩ (some (u32Byte oldValue 0)) h0 hmem))
        ⟨0, address + 1⟩ (some (u32Byte newValue 1))
        (fun hmem =>
          Hbelow ⟨0, address + 1⟩ (some (u32Byte oldValue 1)) h1 hmem))
      ⟨0, address + 2⟩ (some (u32Byte newValue 2))
      (fun hmem =>
        Hbelow ⟨0, address + 2⟩ (some (u32Byte oldValue 2)) h2 hmem))
  exact fun hmem =>
    Hbelow ⟨0, address + 3⟩ (some (u32Byte oldValue 3)) h3 hmem

private theorem heapBelow_store64
    {σ : WasmHeapMap (Option UInt8)} {frontier : Nat}
    (address : UInt32) (oldValue newValue : UInt64)
    (Hbelow : HeapBelow σ frontier)
    (h0 : get? σ ⟨0, address⟩ = some (some (u64Byte oldValue 0)))
    (h1 : get? σ ⟨0, address + 1⟩ = some (some (u64Byte oldValue 1)))
    (h2 : get? σ ⟨0, address + 2⟩ = some (some (u64Byte oldValue 2)))
    (h3 : get? σ ⟨0, address + 3⟩ = some (some (u64Byte oldValue 3)))
    (h4 : get? σ ⟨0, address + 4⟩ = some (some (u64Byte oldValue 4)))
    (h5 : get? σ ⟨0, address + 5⟩ = some (some (u64Byte oldValue 5)))
    (h6 : get? σ ⟨0, address + 6⟩ = some (some (u64Byte oldValue 6)))
    (h7 : get? σ ⟨0, address + 7⟩ = some (some (u64Byte oldValue 7))) :
    HeapBelow (store64Heap σ 0 address newValue) frontier := by
  unfold store64Heap
  apply HeapBelow.insert_fresh
    (HeapBelow.insert_fresh
      (HeapBelow.insert_fresh
        (HeapBelow.insert_fresh
          (HeapBelow.insert_fresh
            (HeapBelow.insert_fresh
              (HeapBelow.insert_fresh
                (HeapBelow.insert_fresh Hbelow ⟨0, address⟩
                  (some (u64Byte newValue 0))
                  (fun hmem => Hbelow ⟨0, address⟩
                    (some (u64Byte oldValue 0)) h0 hmem))
                ⟨0, address + 1⟩ (some (u64Byte newValue 1))
                (fun hmem => Hbelow ⟨0, address + 1⟩
                  (some (u64Byte oldValue 1)) h1 hmem))
              ⟨0, address + 2⟩ (some (u64Byte newValue 2))
              (fun hmem => Hbelow ⟨0, address + 2⟩
                (some (u64Byte oldValue 2)) h2 hmem))
            ⟨0, address + 3⟩ (some (u64Byte newValue 3))
            (fun hmem => Hbelow ⟨0, address + 3⟩
              (some (u64Byte oldValue 3)) h3 hmem))
          ⟨0, address + 4⟩ (some (u64Byte newValue 4))
          (fun hmem => Hbelow ⟨0, address + 4⟩
            (some (u64Byte oldValue 4)) h4 hmem))
        ⟨0, address + 5⟩ (some (u64Byte newValue 5))
        (fun hmem => Hbelow ⟨0, address + 5⟩
          (some (u64Byte oldValue 5)) h5 hmem))
      ⟨0, address + 6⟩ (some (u64Byte newValue 6))
      (fun hmem => Hbelow ⟨0, address + 6⟩
        (some (u64Byte oldValue 6)) h6 hmem))
  exact fun hmem => Hbelow ⟨0, address + 7⟩
    (some (u64Byte oldValue 7)) h7 hmem

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
  iopen_state Hstate
  ihave_heap_valid hg0 :
      ⌜get? σ ⟨0, address⟩ = some (some (u32Byte oldValue 0))⌝ $$ [Hheap H0]
  ihave_heap_valid hg1 :
      ⌜get? σ ⟨0, address + 1⟩ = some (some (u32Byte oldValue 1))⌝ $$
        [Hheap H1]
  imod genHeap_update (v₂ := some (u32Byte newValue 0)) $$
      [$Hheap $H0] with ⟨Hheap, H0⟩
  imod genHeap_update (v₂ := some (u32Byte newValue 1)) $$
      [$Hheap $H1] with ⟨Hheap, H1⟩
  ihave Hexc' : machineAuxInterp (store16Heap σ 0 address newValue)
      store.wasm.mem.pages
      store.wasm.exns store.wasm.tagIds $$ [Hexc]
  · iapply machineAuxInterp_heap_mono
      (fun frontier Hbelow =>
        heapBelow_store16 address oldValue newValue Hbelow hg0 hg1)
    iexact Hexc
  imodintro
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth HhostEnvAuth Hstate_auth Hexc']
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
    isplitr [Hexc']
    · ipureintro
      have h_ag := store16_sound σ (storeResolve store) 0 store.wasm.mem address newValue
          (storeResolve_zero store) h1 Hfacts.1
      rw [storeResolve_update_mem0] at h_ag
      have h_bn := store16_inBounds σ (storeResolve store) 0 store.wasm.mem address newValue
          (storeResolve_zero store) h1 Hfacts.2.1 hbound
      rw [storeResolve_update_mem0] at h_bn
      exact ⟨h_ag, h_bn, Hfacts.2.2⟩
    · simp only [Mem.write16]
      iexact Hexc'
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
  iopen_state Hstate
  ihave_heap_valid hg0 :
      ⌜get? σ ⟨0, address⟩ = some (some (u32Byte oldValue 0))⌝ $$ [Hheap H0]
  ihave_heap_valid hg1 :
      ⌜get? σ ⟨0, address + 1⟩ = some (some (u32Byte oldValue 1))⌝ $$
        [Hheap H1]
  ihave_heap_valid hg2 :
      ⌜get? σ ⟨0, address + 2⟩ = some (some (u32Byte oldValue 2))⌝ $$
        [Hheap H2]
  ihave_heap_valid hg3 :
      ⌜get? σ ⟨0, address + 3⟩ = some (some (u32Byte oldValue 3))⌝ $$
        [Hheap H3]
  imod genHeap_update (v₂ := some (u32Byte newValue 0)) $$
      [$Hheap $H0] with ⟨Hheap, H0⟩
  imod genHeap_update (v₂ := some (u32Byte newValue 1)) $$
      [$Hheap $H1] with ⟨Hheap, H1⟩
  imod genHeap_update (v₂ := some (u32Byte newValue 2)) $$
      [$Hheap $H2] with ⟨Hheap, H2⟩
  imod genHeap_update (v₂ := some (u32Byte newValue 3)) $$
      [$Hheap $H3] with ⟨Hheap, H3⟩
  ihave Hexc' : machineAuxInterp (store32Heap σ 0 address newValue)
      store.wasm.mem.pages
      store.wasm.exns store.wasm.tagIds $$ [Hexc]
  · iapply machineAuxInterp_heap_mono
      (fun frontier Hbelow =>
        heapBelow_store32 address oldValue newValue Hbelow hg0 hg1 hg2 hg3)
    iexact Hexc
  imodintro
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth HhostEnvAuth Hstate_auth Hexc']
  · iapply (stateInterp_eq
      { store with wasm :=
          { store.wasm with mem := store.wasm.mem.write32 address newValue } }
      steps observations threads).mpr
    iexists store32Heap σ 0 address newValue
    iexists globalσ
    iexists dataSegmentσ
    iexists tableσ
    iexists elementSegmentσ
    iexists runtimeModuleσ
    iexists hostEnvσ
    unfold store32Heap
    iframe Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth HhostEnvAuth Hstate_auth
    isplitr [Hexc']
    · ipureintro
      have h_ag := store32_sound σ (storeResolve store) 0 store.wasm.mem address newValue
          (storeResolve_zero store) h1 h2 h3 Hfacts.1
      rw [storeResolve_update_mem0] at h_ag
      have h_bn := store32_inBounds σ (storeResolve store) 0 store.wasm.mem address newValue
          (storeResolve_zero store) h1 h2 h3 Hfacts.2.1 hbound
      rw [storeResolve_update_mem0] at h_bn
      exact ⟨h_ag, h_bn, Hfacts.2.2⟩
    · simp only [Mem.write32]
      iexact Hexc'
  · iapply (pointsTo_u32_eq 0 address newValue).mpr
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
  iopen_state Hstate
  ihave_heap_valid hg0 :
      ⌜get? σ ⟨0, address⟩ = some (some (u64Byte oldValue 0))⌝ $$ [Hheap H0]
  ihave_heap_valid hg1 :
      ⌜get? σ ⟨0, address + 1⟩ = some (some (u64Byte oldValue 1))⌝ $$
        [Hheap H1]
  ihave_heap_valid hg2 :
      ⌜get? σ ⟨0, address + 2⟩ = some (some (u64Byte oldValue 2))⌝ $$
        [Hheap H2]
  ihave_heap_valid hg3 :
      ⌜get? σ ⟨0, address + 3⟩ = some (some (u64Byte oldValue 3))⌝ $$
        [Hheap H3]
  ihave_heap_valid hg4 :
      ⌜get? σ ⟨0, address + 4⟩ = some (some (u64Byte oldValue 4))⌝ $$
        [Hheap H4]
  ihave_heap_valid hg5 :
      ⌜get? σ ⟨0, address + 5⟩ = some (some (u64Byte oldValue 5))⌝ $$
        [Hheap H5]
  ihave_heap_valid hg6 :
      ⌜get? σ ⟨0, address + 6⟩ = some (some (u64Byte oldValue 6))⌝ $$
        [Hheap H6]
  ihave_heap_valid hg7 :
      ⌜get? σ ⟨0, address + 7⟩ = some (some (u64Byte oldValue 7))⌝ $$
        [Hheap H7]
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
  ihave Hexc' : machineAuxInterp (store64Heap σ 0 address newValue)
      store.wasm.mem.pages
      store.wasm.exns store.wasm.tagIds $$ [Hexc]
  · iapply machineAuxInterp_heap_mono
      (fun frontier Hbelow =>
        heapBelow_store64 address oldValue newValue Hbelow
          hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7)
    iexact Hexc
  imodintro
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth HhostEnvAuth Hstate_auth Hexc']
  · iapply (stateInterp_eq
      { store with wasm :=
          { store.wasm with mem := store.wasm.mem.write64 address newValue } }
      steps observations threads).mpr
    iexists store64Heap σ 0 address newValue
    iexists globalσ
    iexists dataSegmentσ
    iexists tableσ
    iexists elementSegmentσ
    iexists runtimeModuleσ
    iexists hostEnvσ
    unfold store64Heap
    iframe Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth HhostEnvAuth Hstate_auth
    isplitr [Hexc']
    · ipureintro
      have h_ag := store64_sound σ (storeResolve store) 0 store.wasm.mem address newValue
          (storeResolve_zero store) h1 h2 h3 h4 h5 h6 h7 Hfacts.1
      rw [storeResolve_update_mem0] at h_ag
      have h_bn := store64_inBounds σ (storeResolve store) 0 store.wasm.mem address newValue
          (storeResolve_zero store) h1 h2 h3 h4 h5 h6 h7 Hfacts.2.1 hbound
      rw [storeResolve_update_mem0] at h_bn
      exact ⟨h_ag, h_bn, Hfacts.2.2⟩
    · simp only [Mem.write64]
      iexact Hexc'
  · iapply (pointsTo_u64_eq 0 address newValue).mpr
    iframe

/-- A 16-byte (v128) store as two consecutive 8-byte stores. -/
theorem stateInterp_writeV128 [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (addr : UInt32) (lo_old hi_old lo hi : UInt64)
    (hnowrap : addr.toNat + 16 < 4294967296)
    (hbound : addr.toNat + 16 ≤ store.wasm.mem.pages * 65536) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      pointsTo_u64 0 addr lo_old ∗ pointsTo_u64 0 (addr + 8) hi_old ==∗
      stateInterp (GF := WasmHeapGF α)
        { store with wasm := { store.wasm with mem :=
            (store.wasm.mem.write64 addr lo).write64 (addr + 8) hi } }
        steps observations threads ∗
      pointsTo_u64 0 addr lo ∗ pointsTo_u64 0 (addr + 8) hi := by
  have hbound_lo : addr.toNat + 8 ≤ store.wasm.mem.pages * 65536 := by omega
  have hroomLo : addr.toNat + 8 ≤ 4294967296 := by omega
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := UInt32.addSteps8 addr hroomLo
  have h8 : (addr + 8).toNat = addr.toNat + 8 := by
    simp only [UInt32.toNat_add, show (8 : UInt32).toNat = 8 from rfl]; omega
  have hroomHi : (addr + 8).toNat + 8 ≤ 4294967296 := by
    rw [h8]
    omega
  obtain ⟨h81, h82, h83, h84, h85, h86, h87⟩ :=
    UInt32.addSteps8 (addr + 8) hroomHi
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

/-- Successful memory growth preserves the authoritative byte heap unchanged:
physical bytes are identical and every previously owned address remains in
bounds because the page count only increases. -/
theorem stateInterp_memoryGrow [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (delta : UInt32) (cap : Nat) (memory : Mem) (previousPages : Nat)
    (hgrow : store.wasm.mem.grow delta cap = some (memory, previousPages)) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ==∗
      stateInterp (GF := WasmHeapGF α)
        { store with wasm := { store.wasm with mem := memory } }
        steps observations threads := by
  have hmemoryPages :
      memory.pages = store.wasm.mem.pages + delta.toNat := by
    simp only [Mem.grow] at hgrow
    split at hgrow
    · have hinj := Prod.mk.inj (Option.some.inj hgrow)
      exact (congrArg (fun result : Mem => result.pages) hinj.1).symm
    · contradiction
  have hpagesMono : store.wasm.mem.pages ≤ memory.pages := by
    rw [hmemoryPages]
    exact Nat.le_add_right _ _
  iintro Hstate
  iopen_state Hstate
  iunfold machineAuxInterp at Hexc
  icases Hexc with ⟨Hpages, Hdomain, Hexceptions⟩
  imod memoryPagesAuth_update store.wasm.mem.pages memory.pages hpagesMono $$
      Hpages with ⟨Hpages, -⟩
  imodintro
  iapply (stateInterp_eq
      { store with wasm := { store.wasm with mem := memory } }
      steps observations threads).mpr
  iexists σ
  iexists globalσ
  iexists dataSegmentσ
  iexists tableσ
  iexists elementSegmentσ
  iexists runtimeModuleσ
  iexists hostEnvσ
  iframe Hheap Hglobals Hsegments Htables HelementSegments
    HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth
    HhostEnvAuth Hstate_auth
  isplitr [Hpages Hdomain Hexceptions]
  · ipureintro
    have h_ag := grow_sound σ (storeResolve store) 0 store.wasm.mem memory delta
        cap previousPages hgrow (storeResolve_zero store) Hfacts.1
    rw [storeResolve_update_mem0] at h_ag
    have h_bn := grow_inBounds σ (storeResolve store) 0 store.wasm.mem memory delta
        cap previousPages hgrow (storeResolve_zero store) Hfacts.2.1
    rw [storeResolve_update_mem0] at h_bn
    exact ⟨h_ag, h_bn, Hfacts.2.2⟩
  · unfold machineAuxInterp
    iframe Hpages Hdomain Hexceptions

/-- Tracked successful growth additionally exposes an exact snapshot of the
new physical page count and the concrete old/new page equations. -/
theorem stateInterp_memoryGrow_tracked [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (delta : UInt32) (cap : Nat) (memory : Mem) (previousPages : Nat)
    (hgrow : store.wasm.mem.grow delta cap = some (memory, previousPages)) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ==∗
      stateInterp (GF := WasmHeapGF α)
          { store with wasm := { store.wasm with mem := memory } }
          steps observations threads ∗
      memoryPagesOwn memory.pages ∗
      ⌜previousPages = store.wasm.mem.pages ∧
        memory.pages = previousPages + delta.toNat⌝ := by
  have hfacts : previousPages = store.wasm.mem.pages ∧
      memory.pages = previousPages + delta.toNat := by
    simp only [Mem.grow] at hgrow
    split at hgrow
    · have hinj := Prod.mk.inj (Option.some.inj hgrow)
      exact ⟨hinj.2.symm,
        (congrArg (fun result : Mem => result.pages) hinj.1).symm.trans
          (by rw [hinj.2])⟩
    · contradiction
  iintro Hstate
  imod stateInterp_memoryGrow store steps observations threads delta cap
      memory previousPages hgrow $$ Hstate with Hstate
  imod stateInterp_memoryPages_snapshot
      { store with wasm := { store.wasm with mem := memory } }
      steps observations threads $$ Hstate with ⟨Hstate, Hpages⟩
  imodintro
  isplitl [Hstate]
  · iexact Hstate
  isplitl [Hpages]
  · iexact Hpages
  · ipureintro
    exact hfacts

/-- Frame-preserving form of `stateInterp_memoryGrow_tracked`, for lifting
rules that prepare a continuation before updating the hidden page authority. -/
theorem stateInterp_memoryGrow_tracked_frame [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (delta : UInt32) (cap : Nat) (memory : Mem) (previousPages : Nat)
    (hgrow : store.wasm.mem.grow delta cap = some (memory, previousPages))
    {P : IProp (WasmHeapGF α)} :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗ P ==∗
      (stateInterp (GF := WasmHeapGF α)
          { store with wasm := { store.wasm with mem := memory } }
          steps observations threads ∗
        memoryPagesOwn memory.pages ∗
        ⌜previousPages = store.wasm.mem.pages ∧
          memory.pages = previousPages + delta.toNat⌝) ∗ P := by
  iintro ⟨Hstate, HP⟩
  iapply bupd_frame_right
  isplitl [Hstate]
  · iapply stateInterp_memoryGrow_tracked store steps observations threads
      delta cap memory previousPages hgrow
    iexact Hstate
  · iexact HP

/-- After a host-call `.Return`, the store's `wasm` field is replaced by the
host-returned store. `runtime` is unchanged and the host's mutable state is
unchanged (`h_host`), so all ghost authorities are preserved; agreement must be
re-established by the caller for each component that the host may have
modified. -/
theorem stateInterp_hostCallReturn [WasmSmallStepGS hlc α]
    (store : MachineStore α) (newWasm : Store α)
    (steps : Nat) (observations : List StepKind) (threads : Nat)
    (h_host : newWasm.host = store.wasm.host)
    (h_pages : store.wasm.mem.pages ≤ newWasm.mem.pages) :
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
    (∀ σ, exceptionHeapAgrees σ store.wasm.exns →
          exceptionHeapAgrees σ newWasm.exns) →
    (∀ ids : List Nat, ids.IsPrefix store.wasm.tagIds →
          ids.IsPrefix newWasm.tagIds) →
    stateInterp (GF := WasmHeapGF α) store steps observations threads ==∗
      stateInterp (GF := WasmHeapGF α) { store with wasm := newWasm }
        steps observations threads := by
  intro hMem hBounds hGlobals hData hTables hElems hExns hTagIds
  iintro Hstate
  iopen_state Hstate
  iunfold machineAuxInterp at Hexc
  icases Hexc with ⟨Hpages, Hdomain, Hexceptions⟩
  imod memoryPagesAuth_update store.wasm.mem.pages newWasm.mem.pages h_pages $$
      Hpages with ⟨Hpages, -⟩
  imodintro
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
  ihave Hexc' : machineAuxInterp σ newWasm.mem.pages
      newWasm.exns newWasm.tagIds $$ [Hpages Hdomain Hexceptions]
  · unfold machineAuxInterp
    isplitl [Hpages]
    · iexact Hpages
    isplitl [Hdomain]
    · iexact Hdomain
    · iapply exceptionInterp_mono hExns hTagIds
      iexact Hexceptions
  iframe Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth HhostEnvAuth Hstate_auth' Hexc'
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
  iopen_state Hstate
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
  ihave_pure HsourceFacts :
      ⌜store.wasm.mem.read32 0 = 0x04030201 ∧
        4 ≤ store.wasm.mem.pages * 65536⌝ using
    stateInterp_pointsTo_u32_facts store steps observations threads
      0 0x04030201 rfl rfl rfl $$ [Hstate Hsource]
  ihave_pure HdestinationFacts :
      ⌜store.wasm.mem.read32 8 = oldDestination ∧
        12 ≤ store.wasm.mem.pages * 65536⌝ using
    stateInterp_pointsTo_u32_facts store steps observations threads
      8 oldDestination rfl rfl rfl $$ [Hstate Hdestination]
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

instance instIrisGS [WasmSmallStepGS hlc α] :
    IrisGS_gen hlc (Expr α) (WasmHeapGF α) where
  numLatersPerStep _ := 0
  forkPost _ := iprop(True)
  stateInterp_mono _ _ _ _ := by iintro $

end Wasm.SmallStep
