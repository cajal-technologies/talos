import CodeLib.SepLogic.SmallStepState

/-!
# Shared pieces of the small-step ghost-state initialisation

Every adequacy entry point in `CodeLib.SepLogic.SmallStepAdequacy` opens with
the same preamble: allocate one ghost resource per `WasmHeapGF` slot, then
bundle the results into a `WasmSmallStepGS`.  The parts of that preamble that
are *literally* the same everywhere live here.

* `GhostSlot.*` names the `WasmHeapGF` slot each ghost map or element lives in.
  Previously every entry point repeated the raw slot numbers, and several
  functors occur at more than one slot (`Auth.AuthRF (OptionOF (Excl.ExclOF
  (constOF (DiscreteO Nat))))` sits at both 14 and 18), so a transposed number
  still type-checks and only shows up as a mysteriously failing proof.  Each
  number is now written exactly once.
* `smallStepGS` performs the final field-by-field assembly of the fifteen
  component ghost states, which is byte-identical at every site.
* The `wasm_alloc_*` tactics allocate memory and fixed runtime resources, and
  `wasm_install_heap_map_instances` installs the map instances. They expose
  the same local instances and hypotheses used by the adequacy proofs.

The parts that genuinely differ between entry points — which maps start empty
and which start populated, whether the runtime module and host env maps get an
entry for the entry instance, whether the exclusive fragments are kept or
cleared — stay at their call sites.
-/

namespace Wasm.SmallStep

open Iris Iris.ProgramLogic Std
open Wasm.SepLogic

variable {α : Type}

namespace GhostSlot

/-- Ghost map of Wasm globals: `WasmHeapGF` slot 7. -/
@[reducible] def globalMap :
    GhostMapG (WasmHeapGF α) GlobalKey Value WasmGlobalMap := by
  constructor
  exists 7

/-- Ghost map of instantiated runtime modules: `WasmHeapGF` slot 8. -/
@[reducible] def runtimeModuleMap :
    GhostMapG (WasmHeapGF α) Nat Module WasmRuntimeModuleMap := by
  constructor
  exists 8

/-- Ghost map of data segments: `WasmHeapGF` slot 9. -/
@[reducible] def dataSegmentMap :
    GhostMapG (WasmHeapGF α) DataSegmentKey (Option (List UInt8))
      WasmDataSegmentMap := by
  constructor
  exists 9

/-- Ghost map of tables: `WasmHeapGF` slot 10. -/
@[reducible] def tableMap :
    GhostMapG (WasmHeapGF α) TableKey TableInst WasmTableMap := by
  constructor
  exists 10

/-- Ghost map of element segments: `WasmHeapGF` slot 11. -/
@[reducible] def elementSegmentMap :
    GhostMapG (WasmHeapGF α) ElementSegmentKey (Option (List (Option Nat)))
      WasmElementSegmentMap := by
  constructor
  exists 11

/-- Ghost map of host environments: `WasmHeapGF` slot 12. -/
@[reducible] def hostEnvMap :
    GhostMapG (WasmHeapGF α) Nat (HostEnv α) WasmHostEnvMap := by
  constructor
  exists 12

/-- Exclusive-auth element holding the host state: `WasmHeapGF` slot 13. -/
@[reducible] def hostStateElem :
    ElemG (WasmHeapGF α)
      (Auth.AuthRF (OptionOF (Excl.ExclOF (constOF (DiscreteO α))))) := by
  exists 13

/-- Exclusive-auth element holding the current instance id: `WasmHeapGF` slot
14.  Slot 18 carries the same functor, so this number must not be guessed. -/
@[reducible] def instanceElem :
    ElemG (WasmHeapGF α)
      (Auth.AuthRF (OptionOF (Excl.ExclOF (constOF (DiscreteO Nat))))) := by
  exists 14

/-- Agreement element holding the runtime instance table: `WasmHeapGF` slot
15. -/
@[reducible] def runtimeInstancesElem :
    ElemG (WasmHeapGF α)
      (constOF (Agree (DiscreteO (Array (ModuleInstance α))))) := by
  exists 15

/-- Ghost map of in-flight exception payloads: `WasmHeapGF` slot 16. -/
@[reducible] def exceptionMap :
    GhostMapG (WasmHeapGF α) Nat (Nat × List Value) WasmExceptionMap := by
  constructor
  exists 16

/-- Agreement element holding the entry instance's tag table: `WasmHeapGF`
slot 17. -/
@[reducible] def tagTableElem :
    ElemG (WasmHeapGF α) (constOF (Agree (DiscreteO (List Nat)))) := by
  exists 17

end GhostSlot

/-- Assemble the small-step ghost state from the invariant ghost state and the
fourteen Wasm component ghost states, the latter taken from the ambient
instance context (every one of them is a local instance at the point where an
adequacy proof builds its `WasmSmallStepGS`).  Every adequacy entry point
allocates the same components and wires them up the same way; the wiring is
written once here. -/
@[reducible] def smallStepGS (hlc : HasLC)
    (invGS : InvGS_gen hlc (WasmHeapGF α))
    [wasmHeapGS : WasmHeapGS α]
    [heapDomainGS : WasmHeapDomainGS α]
    [memoryPagesGS : WasmMemoryPagesGS α]
    [wasmGlobalGS : WasmGlobalGS α]
    [wasmDataSegmentGS : WasmDataSegmentGS α]
    [wasmTableGS : WasmTableGS α]
    [wasmElementSegmentGS : WasmElementSegmentGS α]
    [wasmExceptionGS : WasmExceptionGS α]
    [tagTableGS : WasmTagTableGS α]
    [runtimeGS : WasmRuntimeModuleGS α]
    [hostEnvGS : WasmHostEnvGS α]
    [hostStateGS : WasmHostStateGS α]
    [instanceGS : WasmInstanceGS α]
    [runtimeInstancesGS : WasmRuntimeInstancesGS α] :
    WasmSmallStepGS hlc α :=
  { toInvGS_gen := invGS
    toWasmHeapGS := wasmHeapGS
    heapDomain := heapDomainGS
    memoryPages := memoryPagesGS
    global := wasmGlobalGS
    dataSegment := wasmDataSegmentGS
    table := wasmTableGS
    elementSegment := wasmElementSegmentGS
    exception := wasmExceptionGS
    tagTable := tagTableGS
    runtime := runtimeGS
    hostEnv := hostEnvGS
    hostState := hostStateGS
    instanceGS := instanceGS
    runtimeInstances := runtimeInstancesGS }

set_option hygiene false in
/-- Allocate the physical memory heap, its domain, and the page authority. -/
macro "wasm_alloc_memory_ghosts " config:term " from " heap:term : tactic =>
  `(tactic|
    (imod genHeap_init (L := MemoryKey) (V := Option UInt8)
         (GF := WasmHeapGF α) (H := WasmHeapMap) ($heap) with
       ⟨%heapGS, Hheap, Hpoints, Hmeta⟩
     imod heapDomain_init (α := α) ($heap) with
       ⟨%heapDomainGS, HheapDomain⟩
     letI _ : WasmHeapDomainGS α := heapDomainGS
     imod memoryPages_init_authority (α := α)
         ($config).store.wasm.mem.pages with
       ⟨%memoryPagesGS, HmemoryPagesAuth⟩
     letI _ : WasmMemoryPagesGS α := memoryPagesGS))

set_option hygiene false in
/-- Allocate empty global, segment, table, and element-segment ghost maps. -/
macro "wasm_alloc_empty_heap_maps" : tactic =>
  `(tactic|
    (letI globalMapG :
        GhostMapG (WasmHeapGF α) GlobalKey Value WasmGlobalMap :=
      GhostSlot.globalMap
     imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := GlobalKey)
         (V := Value) (H := WasmGlobalMap)) with ⟨%globalName, Hglobals⟩
     letI dataSegmentMapG :
         GhostMapG (WasmHeapGF α) DataSegmentKey (Option (List UInt8))
           WasmDataSegmentMap :=
       GhostSlot.dataSegmentMap
     imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := DataSegmentKey)
         (V := Option (List UInt8)) (H := WasmDataSegmentMap)) with
       ⟨%dataSegmentName, Hsegments⟩
     letI tableMapG :
         GhostMapG (WasmHeapGF α) TableKey TableInst WasmTableMap :=
       GhostSlot.tableMap
     imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := TableKey)
         (V := TableInst) (H := WasmTableMap)) with ⟨%tableName, Htables⟩
     letI elementSegmentMapG :
         GhostMapG (WasmHeapGF α) ElementSegmentKey (Option (List (Option Nat)))
           WasmElementSegmentMap :=
       GhostSlot.elementSegmentMap
     imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := ElementSegmentKey)
         (V := Option (List (Option Nat))) (H := WasmElementSegmentMap)) with
       ⟨%elementSegmentName, HelementSegments⟩))

set_option hygiene false in
/-- Allocate a supplied global map and empty segment, table, and element maps. -/
macro "wasm_alloc_globals_and_empty_heap_maps " globals:term : tactic =>
  `(tactic|
    (letI globalMapG :
         GhostMapG (WasmHeapGF α) GlobalKey Value WasmGlobalMap :=
       GhostSlot.globalMap
     imod (ghost_map_alloc (GF := WasmHeapGF α) (K := GlobalKey)
         (V := Value) (H := WasmGlobalMap) ($globals)) with
       ⟨%globalName, Hglobals, HglobalPoints⟩
     letI dataSegmentMapG :
         GhostMapG (WasmHeapGF α) DataSegmentKey (Option (List UInt8))
           WasmDataSegmentMap := GhostSlot.dataSegmentMap
     imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := DataSegmentKey)
         (V := Option (List UInt8)) (H := WasmDataSegmentMap)) with
       ⟨%dataSegmentName, Hsegments⟩
     letI tableMapG :
         GhostMapG (WasmHeapGF α) TableKey TableInst WasmTableMap :=
       GhostSlot.tableMap
     imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := TableKey)
         (V := TableInst) (H := WasmTableMap)) with ⟨%tableName, Htables⟩
     letI elementSegmentMapG :
         GhostMapG (WasmHeapGF α) ElementSegmentKey (Option (List (Option Nat)))
           WasmElementSegmentMap := GhostSlot.elementSegmentMap
     imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := ElementSegmentKey)
         (V := Option (List (Option Nat))) (H := WasmElementSegmentMap)) with
       ⟨%elementSegmentName, HelementSegments⟩))

set_option hygiene false in
/-- Install the five map instances after their authoritative maps are allocated. -/
macro "wasm_install_heap_map_instances" : tactic =>
  `(tactic|
    (letI wasmHeapGS : WasmHeapGS α :=
       { togenHeapGS := heapGS }
     letI wasmGlobalGS : WasmGlobalGS α :=
       { toGhostMapG := globalMapG
         globalName := globalName }
     letI wasmDataSegmentGS : WasmDataSegmentGS α :=
       { toGhostMapG := dataSegmentMapG
         dataSegmentName := dataSegmentName }
     letI wasmTableGS : WasmTableGS α :=
       { toGhostMapG := tableMapG
         tableName := tableName }
     letI wasmElementSegmentGS : WasmElementSegmentGS α :=
       { toGhostMapG := elementSegmentMapG
         elementSegmentName := elementSegmentName }))

set_option hygiene false in
/-- Allocate an empty runtime-module map. -/
macro "wasm_alloc_empty_runtime_modules" : tactic =>
  `(tactic|
    (letI runtimeModuleMapG :
        GhostMapG (WasmHeapGF α) Nat Module WasmRuntimeModuleMap :=
      GhostSlot.runtimeModuleMap
     imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := Nat)
         (V := Module) (H := WasmRuntimeModuleMap)) with
       ⟨%runtimeName, HruntimeModuleAuth⟩
     letI runtimeGS : WasmRuntimeModuleGS α :=
       { toGhostMapG := runtimeModuleMapG
         runtimeName }))

set_option hygiene false in
/-- Allocate a runtime-module map containing the entry instance's module. -/
macro "wasm_alloc_current_runtime_module " config:term : tactic =>
  `(tactic|
    (letI runtimeModuleMapG :
        GhostMapG (WasmHeapGF α) Nat Module WasmRuntimeModuleMap :=
      GhostSlot.runtimeModuleMap
     imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := Nat)
         (V := Module) (H := WasmRuntimeModuleMap)) with
       ⟨%runtimeName, HruntimeModuleAuth⟩
     imod ghost_map_insert_persist (k := ($config).store.runtime.entry.id)
         (v := ($config).store.runtime.currentModule)
         (get?_empty ($config).store.runtime.entry.id) $$ HruntimeModuleAuth with
       ⟨HruntimeModuleAuth', HruntimeWP⟩
     iintuitionistic HruntimeWP
     rw [show insert (∅ : WasmRuntimeModuleMap Module)
         ($config).store.runtime.entry.id ($config).store.runtime.currentModule =
         PartialMap.singleton ($config).store.runtime.entry.id
           ($config).store.runtime.currentModule from rfl]
     letI runtimeGS : WasmRuntimeModuleGS α :=
       { toGhostMapG := runtimeModuleMapG
         runtimeName }))

set_option hygiene false in
/-- Allocate an empty host-environment map. -/
macro "wasm_alloc_empty_host_envs" : tactic =>
  `(tactic|
    (letI hostEnvMapG :
        GhostMapG (WasmHeapGF α) Nat (HostEnv α) WasmHostEnvMap :=
      GhostSlot.hostEnvMap
     imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := Nat)
         (V := HostEnv α) (H := WasmHostEnvMap)) with
       ⟨%hostEnvName, HhostEnvAuth⟩
     letI hostEnvGS : WasmHostEnvGS α :=
       { toGhostMapG := hostEnvMapG
         hostEnvName }))

set_option hygiene false in
/-- Allocate a host-environment map containing the entry instance's host. -/
macro "wasm_alloc_current_host_env " config:term : tactic =>
  `(tactic|
    (letI hostEnvMapG :
        GhostMapG (WasmHeapGF α) Nat (HostEnv α) WasmHostEnvMap :=
      GhostSlot.hostEnvMap
     imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := Nat)
         (V := HostEnv α) (H := WasmHostEnvMap)) with
       ⟨%hostEnvName, HhostEnvAuth⟩
     imod ghost_map_insert_persist (k := ($config).store.runtime.entry.id)
         (v := ($config).store.runtime.currentHost)
         (get?_empty ($config).store.runtime.entry.id) $$ HhostEnvAuth with
       ⟨HhostEnvAuth', HhostEnvWP⟩
     iintuitionistic HhostEnvWP
     rw [show insert (∅ : WasmHostEnvMap (HostEnv α))
         ($config).store.runtime.entry.id ($config).store.runtime.currentHost =
         PartialMap.singleton ($config).store.runtime.entry.id
           ($config).store.runtime.currentHost from rfl]
     letI hostEnvGS : WasmHostEnvGS α :=
       { toGhostMapG := hostEnvMapG
         hostEnvName }))

set_option hygiene false in
/-- Allocate authoritative and fragment ownership of the current host state. -/
macro "wasm_alloc_host_state " config:term : tactic =>
  `(tactic|
    (letI hostStateElem :
        ElemG (WasmHeapGF α)
          (Auth.AuthRF (OptionOF (Excl.ExclOF (constOF (DiscreteO α))))) :=
      GhostSlot.hostStateElem
     imod (iOwn_alloc (E := hostStateElem)
         (ExclAuth.auth (⟨($config).store.wasm.host⟩ : DiscreteO α) •
          ExclAuth.frag (⟨($config).store.wasm.host⟩ : DiscreteO α))
         ExclAuth.valid) with
       ⟨%hostStateName, HhostStateAll⟩
     ihave ⟨HhostState, HhostStateFrag⟩ := iOwn_op.mp $$ HhostStateAll
     letI hostStateGS : WasmHostStateGS α :=
       { hostStateElem
         hostStateName }))

set_option hygiene false in
/-- Allocate authoritative and fragment ownership of the current instance. -/
macro "wasm_alloc_current_instance " config:term : tactic =>
  `(tactic|
    (letI instanceElem :
        ElemG (WasmHeapGF α)
          (Auth.AuthRF (OptionOF (Excl.ExclOF (constOF (DiscreteO Nat))))) :=
      GhostSlot.instanceElem
     imod (iOwn_alloc (E := instanceElem)
         (ExclAuth.auth (⟨($config).store.runtime.entry.id⟩ : DiscreteO Nat) •
          ExclAuth.frag (⟨($config).store.runtime.entry.id⟩ : DiscreteO Nat))
         ExclAuth.valid) with
       ⟨%instanceName, HinstanceAll⟩
     ihave ⟨HinstanceState, HinstanceFrag⟩ := iOwn_op.mp $$ HinstanceAll
     letI instanceGS : WasmInstanceGS α :=
       { instanceElem
         instanceName }))

set_option hygiene false in
/-- Allocate agreement on the runtime instance table. -/
macro "wasm_alloc_runtime_instances " config:term : tactic =>
  `(tactic|
    (letI runtimeInstancesElem :
        ElemG (WasmHeapGF α)
          (constOF (Agree (DiscreteO (Array (ModuleInstance α))))) :=
      GhostSlot.runtimeInstancesElem
     imod (iOwn_alloc (E := runtimeInstancesElem)
         (toAgree ⟨($config).store.runtime.instances⟩) (fun _ => trivial)) with
       ⟨%runtimeInstancesName, HruntimeInstances⟩
     letI runtimeInstancesGS : WasmRuntimeInstancesGS α :=
       { runtimeInstancesElem
         runtimeInstancesName }))

set_option hygiene false in
/-- Allocate the initially empty in-flight exception map. -/
macro "wasm_alloc_exception_map" : tactic =>
  `(tactic|
    (letI exceptionMapG :
        GhostMapG (WasmHeapGF α) Nat (Nat × List Value) WasmExceptionMap :=
      GhostSlot.exceptionMap
     imod (ghost_map_alloc_empty (GF := WasmHeapGF α) (K := Nat)
         (V := Nat × List Value) (H := WasmExceptionMap)) with
       ⟨%exceptionName, Hexceptions⟩
     letI wasmExceptionGS : WasmExceptionGS α :=
       { toGhostMapG := exceptionMapG
         exceptionName := exceptionName }))

set_option hygiene false in
/-- Allocate agreement on the entry instance's tag table. -/
macro "wasm_alloc_tag_table " config:term : tactic =>
  `(tactic|
    (letI tagTableElem : ElemG (WasmHeapGF α)
         (constOF (Agree (DiscreteO (List Nat)))) :=
       GhostSlot.tagTableElem
     imod (iOwn_alloc (E := tagTableElem)
         (toAgree ⟨($config).store.wasm.tagIds⟩) (fun _ => trivial)) with
       ⟨%tagTableName, HtagTable⟩
     letI tagTableGS : WasmTagTableGS α :=
       { tagTableElem
         tagTableName }))

set_option hygiene false in
/-- Allocate the fixed runtime-instance, exception, and tag resources. -/
macro "wasm_alloc_fixed_runtime_resources " config:term : tactic =>
  `(tactic|
    (wasm_alloc_runtime_instances $config
     wasm_alloc_exception_map
     wasm_alloc_tag_table $config))

set_option hygiene false in
/-- Build the auxiliary machine interpretation from freshly allocated state. -/
macro "wasm_build_machine_aux " config:term : tactic =>
  `(tactic|
    (ihave HexceptionInterp :
         exceptionInterp ($config).store.wasm.exns ($config).store.wasm.tagIds $$
         [Hexceptions HtagTable]
     next =>
       unfold exceptionInterp tagTableOwn
       isplitl [Hexceptions]
       next =>
         iexists (∅ : WasmExceptionMap (Nat × List Value))
         isplitl [Hexceptions]
         next => iexact Hexceptions
         next =>
           ipureexact exceptionHeapAgrees_empty _
       next =>
         iexists ($config).store.wasm.tagIds
         isplitl [HtagTable]
         next => iexact HtagTable
         next =>
           ipureexact List.prefix_rfl
     ihave Hexc : machineAuxInterp _ ($config).store.wasm.mem.pages
         ($config).store.wasm.exns ($config).store.wasm.tagIds $$
         [HmemoryPagesAuth HheapDomain HexceptionInterp]
     next =>
       unfold machineAuxInterp
       iframe HmemoryPagesAuth HheapDomain HexceptionInterp))

end Wasm.SmallStep
