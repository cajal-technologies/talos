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

class WasmSmallStepGS (hlc : outParam HasLC) extends
    InvGS_gen hlc WasmHeapGF.{0}, WasmHeapGS.{0} where
  global : WasmGlobalGS.{0}
  dataSegment : WasmDataSegmentGS.{0}
  table : WasmTableGS.{0}
  elementSegment : WasmElementSegmentGS.{0}
  runtime : WasmRuntimeModuleGS

attribute [instance] WasmSmallStepGS.toInvGS_gen
attribute [instance] WasmSmallStepGS.toWasmHeapGS
attribute [reducible, instance] WasmSmallStepGS.global
attribute [reducible, instance] WasmSmallStepGS.dataSegment
attribute [reducible, instance] WasmSmallStepGS.table
attribute [reducible, instance] WasmSmallStepGS.elementSegment
attribute [reducible, instance] WasmSmallStepGS.runtime

instance instStateInterp [WasmSmallStepGS hlc] :
    StateInterp (MachineStore α) StepKind WasmHeapGF where
  stateInterp store _ _ _ := iprop%
    ∃ σ : WasmHeapMap (Option UInt8),
      ∃ globalσ : WasmGlobalMap Value,
      ∃ dataSegmentσ : WasmDataSegmentMap (Option (List UInt8)),
      ∃ tableσ : WasmTableMap TableInst,
      ∃ elementSegmentσ :
        WasmElementSegmentMap (Option (List (Option Nat))),
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
        runtimeModuleOwn store.runtime.module ∗
      ⌜heapAgreesWithMem σ store.wasm.mem ∧
        heapAddressesInBounds σ store.wasm.mem ∧
        globalHeapAgrees globalσ store.wasm.globals ∧
        dataSegmentHeapAgrees dataSegmentσ store.wasm.dataSegments ∧
        tableHeapAgrees tableσ store.wasm.tables ∧
        elementSegmentHeapAgrees elementSegmentσ
          store.wasm.elementSegments⌝

theorem stateInterp_eq [WasmSmallStepGS hlc]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat) :
    stateInterp (GF := WasmHeapGF) store steps observations threads ⊣⊢
      (iprop% ∃ σ : WasmHeapMap (Option UInt8),
        ∃ globalσ : WasmGlobalMap Value,
        ∃ dataSegmentσ : WasmDataSegmentMap (Option (List UInt8)),
        ∃ tableσ : WasmTableMap TableInst,
        ∃ elementSegmentσ :
          WasmElementSegmentMap (Option (List (Option Nat))),
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
          runtimeModuleOwn store.runtime.module ∗
        ⌜heapAgreesWithMem σ store.wasm.mem ∧
          heapAddressesInBounds σ store.wasm.mem ∧
          globalHeapAgrees globalσ store.wasm.globals ∧
          dataSegmentHeapAgrees dataSegmentσ store.wasm.dataSegments ∧
          tableHeapAgrees tableσ store.wasm.tables ∧
          elementSegmentHeapAgrees elementSegmentσ
            store.wasm.elementSegments⌝) :=
  .rfl

theorem stateInterp_pointsTo_read8 [WasmSmallStepGS hlc]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (address : UInt32) (value : UInt8) :
    stateInterp (GF := WasmHeapGF) store steps observations threads ∗
      pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        address (DFrac.own 1) (some value) ==∗
      ⌜store.wasm.mem.read8 address = value⌝ := by
  iintro ⟨Hstate, Hpointsto⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hruntime, %Hfacts⟩
  icases genHeap_valid $$ [$Hheap $Hpointsto] with >%hlookup
  ipureintro
  exact Hfacts.1 address value hlookup

theorem stateInterp_pointsTo_inBounds [WasmSmallStepGS hlc]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (address : UInt32) (value : UInt8) :
    stateInterp (GF := WasmHeapGF) store steps observations threads ∗
      pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        address (DFrac.own 1) (some value) ==∗
      ⌜address.toNat < store.wasm.mem.pages * 65536⌝ := by
  iintro ⟨Hstate, Hpointsto⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hruntime, %Hfacts⟩
  icases genHeap_valid $$ [$Hheap $Hpointsto] with >%hlookup
  ipureintro
  exact Hfacts.2.1 address value hlookup

theorem stateInterp_pointsTo_facts [WasmSmallStepGS hlc]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (address : UInt32) (value : UInt8) :
    stateInterp (GF := WasmHeapGF) store steps observations threads ∗
      pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        address (DFrac.own 1) (some value) ==∗
      ⌜store.wasm.mem.read8 address = value ∧
        address.toNat < store.wasm.mem.pages * 65536⌝ := by
  iintro ⟨Hstate, Hpointsto⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hruntime, %Hfacts⟩
  icases genHeap_valid $$ [$Hheap $Hpointsto] with >%hlookup
  ipureintro
  exact ⟨Hfacts.1 address value hlookup, Hfacts.2.1 address value hlookup⟩

/-- Host-local state is deliberately absent from the Iris physical resources.
Changing only `Store.host` therefore preserves the complete state
interpretation.  This is the frame lemma used by host functions, such as
`stdio.write`, whose effects do not modify Wasm-owned runtime resources. -/
theorem stateInterp_host_set [WasmSmallStepGS hlc]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat) (host : α) :
    stateInterp (GF := WasmHeapGF) store steps observations threads ==∗
      stateInterp (GF := WasmHeapGF)
        { store with wasm := { store.wasm with host } }
        steps observations threads := by
  iintro Hstate
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hruntime, %Hfacts⟩
  imodintro
  iapply (stateInterp_eq
    { store with wasm := { store.wasm with host } }
    steps observations threads).mpr
  iexists σ
  iexists globalσ
  iexists dataSegmentσ
  iexists tableσ
  iexists elementSegmentσ
  iframe Hheap Hglobals Hsegments Htables HelementSegments Hruntime
  ipureintro
  exact Hfacts

/-- Owned global state determines the corresponding physical instantiated
global. -/
theorem stateInterp_global_facts [WasmSmallStepGS hlc]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (index : Nat) (value : Value) :
    stateInterp (GF := WasmHeapGF) store steps observations threads ∗
      globalPointsTo index value ==∗
      ⌜store.wasm.globals.globals[index]? = some value⌝ := by
  iintro ⟨Hstate, Hglobal⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hruntime, %Hfacts⟩
  ihave %hlookup := globalPointsTo_lookup globalσ index value $$ Hglobals Hglobal
  ipureintro
  exact Hfacts.2.2.1 index value hlookup

/-- Updating an owned global updates both the authoritative ghost map and the
physical instantiated global array in lockstep. -/
theorem stateInterp_global_set [WasmSmallStepGS hlc]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (index : Nat) (oldValue newValue : Value) :
    stateInterp (GF := WasmHeapGF) store steps observations threads ∗
      globalPointsTo index oldValue ==∗
      stateInterp (GF := WasmHeapGF)
        { store with wasm :=
            { store.wasm with globals :=
                { globals := store.wasm.globals.globals.set index newValue } } }
        steps observations threads ∗
      globalPointsTo index newValue := by
  iintro ⟨Hstate, Hglobal⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hruntime, %Hfacts⟩
  ihave %hlookup :=
    globalPointsTo_lookup globalσ index oldValue $$ Hglobals Hglobal
  imod globalPointsTo_update globalσ index oldValue newValue $$
      Hglobals Hglobal with
    ⟨Hglobals, Hglobal⟩
  imodintro
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments Hruntime]
  · iapply (stateInterp_eq
      { store with wasm :=
          { store.wasm with globals :=
              { globals := store.wasm.globals.globals.set index newValue } } }
      steps observations threads).mpr
    iexists σ
    iexists insert globalσ index newValue
    iexists dataSegmentσ
    iexists tableσ
    iexists elementSegmentσ
    iframe Hheap Hglobals Hsegments Htables HelementSegments Hruntime
    ipureintro
    exact ⟨Hfacts.1, Hfacts.2.1,
      ⟨global_store_sound globalσ store.wasm.globals
          index oldValue newValue Hfacts.2.2.1 hlookup,
        Hfacts.2.2.2⟩⟩
  · iexact Hglobal

/-- Owned passive-segment state determines the corresponding physical
instantiated segment entry. The framed form keeps both resources available for
a following `memory.init` or `data.drop` transition. -/
theorem stateInterp_dataSegment_facts_frame [WasmSmallStepGS hlc]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (index : Nat) (value : Option (List UInt8)) :
    stateInterp (GF := WasmHeapGF) store steps observations threads ∗
      dataSegmentPointsTo index value ==∗
      stateInterp (GF := WasmHeapGF) store steps observations threads ∗
      dataSegmentPointsTo index value ∗
      ⌜store.wasm.dataSegments[index]? = some value⌝ := by
  iintro ⟨Hstate, Hsegment⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hruntime, %Hfacts⟩
  ihave %hlookup :=
    dataSegmentPointsTo_lookup dataSegmentσ index value $$
      Hsegments Hsegment
  imodintro
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments Hruntime]
  · iapply (stateInterp_eq store steps observations threads).mpr
    iexists σ
    iexists globalσ
    iexists dataSegmentσ
    iexists tableσ
    iexists elementSegmentσ
    iframe
    ipureintro
    exact Hfacts
  · isplitl [Hsegment]
    · iexact Hsegment
    · ipureintro
      exact Hfacts.2.2.2.1 index value hlookup

/-- `data.drop` updates the physical segment status and its authoritative
ghost entry in lockstep. -/
theorem stateInterp_dataSegment_drop [WasmSmallStepGS hlc]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (index : Nat) (oldValue : Option (List UInt8)) :
    stateInterp (GF := WasmHeapGF) store steps observations threads ∗
      dataSegmentPointsTo index oldValue ==∗
      stateInterp (GF := WasmHeapGF)
        { store with wasm :=
            { store.wasm with
              dataSegments := store.wasm.dataSegments.set index none } }
        steps observations threads ∗
      dataSegmentPointsTo index none := by
  iintro ⟨Hstate, Hsegment⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hruntime, %Hfacts⟩
  ihave %hlookup :=
    dataSegmentPointsTo_lookup dataSegmentσ index oldValue $$
      Hsegments Hsegment
  imod dataSegmentPointsTo_update dataSegmentσ index oldValue none $$
      Hsegments Hsegment with
    ⟨Hsegments, Hsegment⟩
  imodintro
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments Hruntime]
  · iapply (stateInterp_eq
      { store with wasm :=
          { store.wasm with
            dataSegments := store.wasm.dataSegments.set index none } }
      steps observations threads).mpr
    iexists σ
    iexists globalσ
    iexists insert dataSegmentσ index none
    iexists tableσ
    iexists elementSegmentσ
    iframe
    ipureintro
    exact ⟨Hfacts.1, Hfacts.2.1, Hfacts.2.2.1,
      dataSegment_store_sound dataSegmentσ store.wasm.dataSegments
        index oldValue none Hfacts.2.2.2.1 hlookup,
      Hfacts.2.2.2.2⟩
  · iexact Hsegment

/-- Element-segment ownership identifies the live or dropped state at the
corresponding stable physical segment index. -/
theorem stateInterp_elementSegment_facts_frame [WasmSmallStepGS hlc]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (index : Nat) (value : Option (List (Option Nat))) :
    stateInterp (GF := WasmHeapGF) store steps observations threads ∗
      elementSegmentPointsTo index value ==∗
      stateInterp (GF := WasmHeapGF) store steps observations threads ∗
      elementSegmentPointsTo index value ∗
      ⌜store.wasm.elementSegments[index]? = some value⌝ := by
  iintro ⟨Hstate, Hsegment⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hruntime, %Hfacts⟩
  ihave %hlookup :=
    elementSegmentPointsTo_lookup elementSegmentσ index value $$
      HelementSegments Hsegment
  imodintro
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments Hruntime]
  · iapply (stateInterp_eq store steps observations threads).mpr
    iexists σ
    iexists globalσ
    iexists dataSegmentσ
    iexists tableσ
    iexists elementSegmentσ
    iframe
    ipureintro
    exact Hfacts
  · isplitl [Hsegment]
    · iexact Hsegment
    · ipureintro
      exact Hfacts.2.2.2.2.2 index value hlookup

/-- `elem.drop` changes the physical segment status and authoritative ghost
entry to `none` without renumbering any segment. -/
theorem stateInterp_elementSegment_drop [WasmSmallStepGS hlc]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (index : Nat) (oldValue : Option (List (Option Nat))) :
    stateInterp (GF := WasmHeapGF) store steps observations threads ∗
      elementSegmentPointsTo index oldValue ==∗
      stateInterp (GF := WasmHeapGF)
        { store with wasm :=
            { store.wasm with
              elementSegments :=
                store.wasm.elementSegments.set index none } }
        steps observations threads ∗
      elementSegmentPointsTo index none := by
  iintro ⟨Hstate, Hsegment⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hruntime, %Hfacts⟩
  ihave %hlookup :=
    elementSegmentPointsTo_lookup elementSegmentσ index oldValue $$
      HelementSegments Hsegment
  imod elementSegmentPointsTo_update
      elementSegmentσ index oldValue none $$
      HelementSegments Hsegment with
    ⟨HelementSegments, Hsegment⟩
  imodintro
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments Hruntime]
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
    iexists insert elementSegmentσ index none
    iframe
    ipureintro
    exact ⟨Hfacts.1, Hfacts.2.1, Hfacts.2.2.1,
      Hfacts.2.2.2.1,
      ⟨Hfacts.2.2.2.2.1,
        elementSegment_store_sound elementSegmentσ
          store.wasm.elementSegments index oldValue none
          Hfacts.2.2.2.2.2 hlookup⟩⟩
  · iexact Hsegment

/-- Owning a table fragment identifies the complete physical instantiated
table at its stable table index. -/
theorem stateInterp_table_facts_frame [WasmSmallStepGS hlc]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (index : Nat) (table : TableInst) :
    stateInterp (GF := WasmHeapGF) store steps observations threads ∗
      tablePointsTo index table ==∗
      stateInterp (GF := WasmHeapGF) store steps observations threads ∗
      tablePointsTo index table ∗
      ⌜store.wasm.tables[index]? = some table⌝ := by
  iintro ⟨Hstate, Htable⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hruntime, %Hfacts⟩
  ihave %hlookup :=
    tablePointsTo_lookup tableσ index table $$ Htables Htable
  imodintro
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments Hruntime]
  · iapply (stateInterp_eq store steps observations threads).mpr
    iexists σ
    iexists globalσ
    iexists dataSegmentσ
    iexists tableσ
    iexists elementSegmentσ
    iframe
    ipureintro
    exact Hfacts
  · isplitl [Htable]
    · iexact Htable
    · ipureintro
      exact Hfacts.2.2.2.2.1 index table hlookup

/-- Replacing an owned table preserves its stable identity and updates the
authoritative ghost map and physical table list in lockstep. -/
theorem stateInterp_table_set [WasmSmallStepGS hlc]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (index : Nat) (oldTable newTable : TableInst) :
    stateInterp (GF := WasmHeapGF) store steps observations threads ∗
      tablePointsTo index oldTable ==∗
      stateInterp (GF := WasmHeapGF)
        { store with wasm :=
            { store.wasm with
              tables := listSetAt store.wasm.tables index newTable } }
        steps observations threads ∗
      tablePointsTo index newTable := by
  iintro ⟨Hstate, Htable⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hruntime, %Hfacts⟩
  ihave %hlookup :=
    tablePointsTo_lookup tableσ index oldTable $$ Htables Htable
  imod tablePointsTo_update tableσ index oldTable newTable $$
      Htables Htable with
    ⟨Htables, Htable⟩
  imodintro
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments Hruntime]
  · iapply (stateInterp_eq
      { store with wasm :=
          { store.wasm with
            tables := listSetAt store.wasm.tables index newTable } }
      steps observations threads).mpr
    iexists σ
    iexists globalσ
    iexists dataSegmentσ
    iexists insert tableσ index newTable
    iexists elementSegmentσ
    iframe
    ipureintro
    exact ⟨Hfacts.1, Hfacts.2.1, Hfacts.2.2.1,
      Hfacts.2.2.2.1,
      ⟨table_store_listSetAt_sound tableσ store.wasm.tables
          index oldTable newTable Hfacts.2.2.2.2.1 hlookup,
        Hfacts.2.2.2.2.2⟩⟩
  · iexact Htable

theorem stateInterp_runtimeModule_agree [WasmSmallStepGS hlc]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat) (m : Module) :
    stateInterp (GF := WasmHeapGF) store steps observations threads ∗
      runtimeModuleOwn m ==∗
      ⌜store.runtime.module = m⌝ := by
  iintro ⟨Hstate, Hexpected⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hactual, %Hfacts⟩
  icombine Hactual Hexpected as Hmodules
  ihave %hagrees :=
    runtimeModuleOwn_agree store.runtime.module m $$ Hmodules
  ipureintro
  exact hagrees

/-- Four-byte ownership determines the physical little-endian word and proves
the complete access is in bounds. The address equalities exclude UInt32
wraparound in the derived byte footprint. -/
theorem stateInterp_pointsTo_u32_facts [WasmSmallStepGS hlc]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (address value : UInt32)
    (h1 : (address + 1).toNat = address.toNat + 1)
    (h2 : (address + 2).toNat = address.toNat + 2)
    (h3 : (address + 3).toNat = address.toNat + 3) :
    stateInterp (GF := WasmHeapGF) store steps observations threads ∗
      pointsTo_u32 address value ==∗
      ⌜store.wasm.mem.read32 address = value ∧
        address.toNat + 4 ≤ store.wasm.mem.pages * 65536⌝ := by
  iintro ⟨Hstate, Hword⟩
  ihave Hword := (pointsTo_u32_eq address value).mp $$ Hword
  icases Hword with ⟨H0, H1, H2, H3⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hruntime, %Hfacts⟩
  ihave %hg0 :
      ⌜get? σ address = some (some (u32Byte value 0))⌝ $$ [Hheap H0]
  · imod genHeap_valid $$ [$Hheap $H0] with %hg0
    ipureintro
    exact hg0
  ihave %hg1 :
      ⌜get? σ (address + 1) = some (some (u32Byte value 1))⌝ $$ [Hheap H1]
  · imod genHeap_valid $$ [$Hheap $H1] with %hg1
    ipureintro
    exact hg1
  ihave %hg2 :
      ⌜get? σ (address + 2) = some (some (u32Byte value 2))⌝ $$ [Hheap H2]
  · imod genHeap_valid $$ [$Hheap $H2] with %hg2
    ipureintro
    exact hg2
  ihave %hg3 :
      ⌜get? σ (address + 3) = some (some (u32Byte value 3))⌝ $$ [Hheap H3]
  · imod genHeap_valid $$ [$Hheap $H3] with %hg3
    ipureintro
    exact hg3
  have hr0 := Hfacts.1 address (u32Byte value 0) hg0
  have hr1 := Hfacts.1 (address + 1) (u32Byte value 1) hg1
  have hr2 := Hfacts.1 (address + 2) (u32Byte value 2) hg2
  have hr3 := Hfacts.1 (address + 3) (u32Byte value 3) hg3
  have hb3 := Hfacts.2.1 (address + 3) (u32Byte value 3) hg3
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
theorem stateInterp_pointsTo_u32_facts_frame [WasmSmallStepGS hlc]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (address value : UInt32)
    (h1 : (address + 1).toNat = address.toNat + 1)
    (h2 : (address + 2).toNat = address.toNat + 2)
    (h3 : (address + 3).toNat = address.toNat + 3) :
    stateInterp (GF := WasmHeapGF) store steps observations threads ∗
      pointsTo_u32 address value ==∗
      stateInterp (GF := WasmHeapGF) store steps observations threads ∗
      pointsTo_u32 address value ∗
      ⌜store.wasm.mem.read32 address = value ∧
        address.toNat + 4 ≤ store.wasm.mem.pages * 65536⌝ := by
  iintro ⟨Hstate, Hword⟩
  ihave Hword := (pointsTo_u32_eq address value).mp $$ Hword
  icases Hword with ⟨H0, H1, H2, H3⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hruntime, %Hfacts⟩
  ihave %hg0 :
      ⌜get? σ address = some (some (u32Byte value 0))⌝ $$ [Hheap H0]
  · imod genHeap_valid $$ [$Hheap $H0] with %hg0
    ipureintro
    exact hg0
  ihave %hg1 :
      ⌜get? σ (address + 1) = some (some (u32Byte value 1))⌝ $$ [Hheap H1]
  · imod genHeap_valid $$ [$Hheap $H1] with %hg1
    ipureintro
    exact hg1
  ihave %hg2 :
      ⌜get? σ (address + 2) = some (some (u32Byte value 2))⌝ $$ [Hheap H2]
  · imod genHeap_valid $$ [$Hheap $H2] with %hg2
    ipureintro
    exact hg2
  ihave %hg3 :
      ⌜get? σ (address + 3) = some (some (u32Byte value 3))⌝ $$ [Hheap H3]
  · imod genHeap_valid $$ [$Hheap $H3] with %hg3
    ipureintro
    exact hg3
  have hr0 := Hfacts.1 address (u32Byte value 0) hg0
  have hr1 := Hfacts.1 (address + 1) (u32Byte value 1) hg1
  have hr2 := Hfacts.1 (address + 2) (u32Byte value 2) hg2
  have hr3 := Hfacts.1 (address + 3) (u32Byte value 3) hg3
  have hb3 := Hfacts.2.1 (address + 3) (u32Byte value 3) hg3
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
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments Hruntime]
  · iapply (stateInterp_eq store steps observations threads).mpr
    iexists σ
    iexists globalσ
    iexists dataSegmentσ
    iexists tableσ
    iexists elementSegmentσ
    iframe
    ipureintro
    exact Hfacts
  · isplitl [H0 H1 H2 H3]
    · iapply (pointsTo_u32_eq address value).mpr
      iframe
    · ipureintro
      exact ⟨hread, hbound⟩

/-- Eight-byte ownership determines the physical little-endian word and proves
the complete access is in bounds. The address equalities exclude UInt32
wraparound in the derived byte footprint. -/
theorem stateInterp_pointsTo_u64_facts [WasmSmallStepGS hlc]
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
    stateInterp (GF := WasmHeapGF) store steps observations threads ∗
      pointsTo_u64 address value ==∗
      ⌜store.wasm.mem.read64 address = value ∧
        address.toNat + 8 ≤ store.wasm.mem.pages * 65536⌝ := by
  iintro ⟨Hstate, Hword⟩
  ihave Hword := (pointsTo_u64_eq address value).mp $$ Hword
  icases Hword with ⟨H0, H1, H2, H3, H4, H5, H6, H7⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hruntime, %Hfacts⟩
  ihave %hg0 :
      ⌜get? σ address = some (some (u64Byte value 0))⌝ $$ [Hheap H0]
  · imod genHeap_valid $$ [$Hheap $H0] with %hg0
    ipureintro; exact hg0
  ihave %hg1 :
      ⌜get? σ (address + 1) = some (some (u64Byte value 1))⌝ $$ [Hheap H1]
  · imod genHeap_valid $$ [$Hheap $H1] with %hg1
    ipureintro; exact hg1
  ihave %hg2 :
      ⌜get? σ (address + 2) = some (some (u64Byte value 2))⌝ $$ [Hheap H2]
  · imod genHeap_valid $$ [$Hheap $H2] with %hg2
    ipureintro; exact hg2
  ihave %hg3 :
      ⌜get? σ (address + 3) = some (some (u64Byte value 3))⌝ $$ [Hheap H3]
  · imod genHeap_valid $$ [$Hheap $H3] with %hg3
    ipureintro; exact hg3
  ihave %hg4 :
      ⌜get? σ (address + 4) = some (some (u64Byte value 4))⌝ $$ [Hheap H4]
  · imod genHeap_valid $$ [$Hheap $H4] with %hg4
    ipureintro; exact hg4
  ihave %hg5 :
      ⌜get? σ (address + 5) = some (some (u64Byte value 5))⌝ $$ [Hheap H5]
  · imod genHeap_valid $$ [$Hheap $H5] with %hg5
    ipureintro; exact hg5
  ihave %hg6 :
      ⌜get? σ (address + 6) = some (some (u64Byte value 6))⌝ $$ [Hheap H6]
  · imod genHeap_valid $$ [$Hheap $H6] with %hg6
    ipureintro; exact hg6
  ihave %hg7 :
      ⌜get? σ (address + 7) = some (some (u64Byte value 7))⌝ $$ [Hheap H7]
  · imod genHeap_valid $$ [$Hheap $H7] with %hg7
    ipureintro; exact hg7
  have hr0 := Hfacts.1 address (u64Byte value 0) hg0
  have hr1 := Hfacts.1 (address + 1) (u64Byte value 1) hg1
  have hr2 := Hfacts.1 (address + 2) (u64Byte value 2) hg2
  have hr3 := Hfacts.1 (address + 3) (u64Byte value 3) hg3
  have hr4 := Hfacts.1 (address + 4) (u64Byte value 4) hg4
  have hr5 := Hfacts.1 (address + 5) (u64Byte value 5) hg5
  have hr6 := Hfacts.1 (address + 6) (u64Byte value 6) hg6
  have hr7 := Hfacts.1 (address + 7) (u64Byte value 7) hg7
  have hb7 := Hfacts.2.1 (address + 7) (u64Byte value 7) hg7
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
theorem stateInterp_pointsTo_u64_facts_frame [WasmSmallStepGS hlc]
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
    stateInterp (GF := WasmHeapGF) store steps observations threads ∗
      pointsTo_u64 address value ==∗
      stateInterp (GF := WasmHeapGF) store steps observations threads ∗
      pointsTo_u64 address value ∗
      ⌜store.wasm.mem.read64 address = value ∧
        address.toNat + 8 ≤ store.wasm.mem.pages * 65536⌝ := by
  iintro ⟨Hstate, Hword⟩
  ihave Hword := (pointsTo_u64_eq address value).mp $$ Hword
  icases Hword with ⟨H0, H1, H2, H3, H4, H5, H6, H7⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hruntime, %Hfacts⟩
  ihave %hg0 :
      ⌜get? σ address = some (some (u64Byte value 0))⌝ $$ [Hheap H0]
  · imod genHeap_valid $$ [$Hheap $H0] with %hg0
    ipureintro; exact hg0
  ihave %hg1 :
      ⌜get? σ (address + 1) = some (some (u64Byte value 1))⌝ $$ [Hheap H1]
  · imod genHeap_valid $$ [$Hheap $H1] with %hg1
    ipureintro; exact hg1
  ihave %hg2 :
      ⌜get? σ (address + 2) = some (some (u64Byte value 2))⌝ $$ [Hheap H2]
  · imod genHeap_valid $$ [$Hheap $H2] with %hg2
    ipureintro; exact hg2
  ihave %hg3 :
      ⌜get? σ (address + 3) = some (some (u64Byte value 3))⌝ $$ [Hheap H3]
  · imod genHeap_valid $$ [$Hheap $H3] with %hg3
    ipureintro; exact hg3
  ihave %hg4 :
      ⌜get? σ (address + 4) = some (some (u64Byte value 4))⌝ $$ [Hheap H4]
  · imod genHeap_valid $$ [$Hheap $H4] with %hg4
    ipureintro; exact hg4
  ihave %hg5 :
      ⌜get? σ (address + 5) = some (some (u64Byte value 5))⌝ $$ [Hheap H5]
  · imod genHeap_valid $$ [$Hheap $H5] with %hg5
    ipureintro; exact hg5
  ihave %hg6 :
      ⌜get? σ (address + 6) = some (some (u64Byte value 6))⌝ $$ [Hheap H6]
  · imod genHeap_valid $$ [$Hheap $H6] with %hg6
    ipureintro; exact hg6
  ihave %hg7 :
      ⌜get? σ (address + 7) = some (some (u64Byte value 7))⌝ $$ [Hheap H7]
  · imod genHeap_valid $$ [$Hheap $H7] with %hg7
    ipureintro; exact hg7
  have hr0 := Hfacts.1 address (u64Byte value 0) hg0
  have hr1 := Hfacts.1 (address + 1) (u64Byte value 1) hg1
  have hr2 := Hfacts.1 (address + 2) (u64Byte value 2) hg2
  have hr3 := Hfacts.1 (address + 3) (u64Byte value 3) hg3
  have hr4 := Hfacts.1 (address + 4) (u64Byte value 4) hg4
  have hr5 := Hfacts.1 (address + 5) (u64Byte value 5) hg5
  have hr6 := Hfacts.1 (address + 6) (u64Byte value 6) hg6
  have hr7 := Hfacts.1 (address + 7) (u64Byte value 7) hg7
  have hb7 := Hfacts.2.1 (address + 7) (u64Byte value 7) hg7
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
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments Hruntime]
  · iapply (stateInterp_eq store steps observations threads).mpr
    iexists σ
    iexists globalσ
    iexists dataSegmentσ
    iexists tableσ
    iexists elementSegmentσ
    iframe
    ipureintro
    exact Hfacts
  · isplitl [H0 H1 H2 H3 H4 H5 H6 H7]
    · iapply (pointsTo_u64_eq address value).mpr
      iframe
    · ipureintro
      exact ⟨hread, hbound⟩

theorem stateInterp_store8 [WasmSmallStepGS hlc]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (address : UInt32) (oldValue newValue : UInt8)
    (hbound : address.toNat < store.wasm.mem.pages * 65536) :
    stateInterp (GF := WasmHeapGF) store steps observations threads ∗
      pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        address (DFrac.own 1) (some oldValue) ==∗
      stateInterp (GF := WasmHeapGF)
        { store with wasm :=
            { store.wasm with mem := store.wasm.mem.write8 address newValue } }
        steps observations threads ∗
      pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        address (DFrac.own 1) (some newValue) := by
  iintro ⟨Hstate, Hpointsto⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hruntime, %Hfacts⟩
  imod genHeap_update (v₂ := some newValue) $$ [$Hheap $Hpointsto] with
    ⟨Hheap, Hpointsto⟩
  imodintro
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments Hruntime]
  · iapply (stateInterp_eq
      { store with wasm :=
          { store.wasm with mem := store.wasm.mem.write8 address newValue } }
      steps observations threads).mpr
    iexists insert σ address (some newValue)
    iexists globalσ
    iexists dataSegmentσ
    iexists tableσ
    iexists elementSegmentσ
    iframe Hheap Hglobals Hsegments Htables HelementSegments Hruntime
    ipureintro
    exact ⟨store_sound σ store.wasm.mem address newValue Hfacts.1,
      store_inBounds σ store.wasm.mem address newValue Hfacts.2.1 hbound,
      Hfacts.2.2⟩
  · iexact Hpointsto

theorem stateInterp_store32 [WasmSmallStepGS hlc]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (address oldValue newValue : UInt32)
    (h1 : (address + 1).toNat = address.toNat + 1)
    (h2 : (address + 2).toNat = address.toNat + 2)
    (h3 : (address + 3).toNat = address.toNat + 3)
    (hbound : address.toNat + 4 ≤ store.wasm.mem.pages * 65536) :
    stateInterp (GF := WasmHeapGF) store steps observations threads ∗
      pointsTo_u32 address oldValue ==∗
      stateInterp (GF := WasmHeapGF)
        { store with wasm :=
            { store.wasm with mem := store.wasm.mem.write32 address newValue } }
        steps observations threads ∗
      pointsTo_u32 address newValue := by
  iintro ⟨Hstate, Hword⟩
  ihave Hword := (pointsTo_u32_eq address oldValue).mp $$ Hword
  icases Hword with ⟨H0, H1, H2, H3⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hruntime, %Hfacts⟩
  imod genHeap_update (v₂ := some (u32Byte newValue 0)) $$
      [$Hheap $H0] with ⟨Hheap, H0⟩
  imod genHeap_update (v₂ := some (u32Byte newValue 1)) $$
      [$Hheap $H1] with ⟨Hheap, H1⟩
  imod genHeap_update (v₂ := some (u32Byte newValue 2)) $$
      [$Hheap $H2] with ⟨Hheap, H2⟩
  imod genHeap_update (v₂ := some (u32Byte newValue 3)) $$
      [$Hheap $H3] with ⟨Hheap, H3⟩
  imodintro
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments Hruntime]
  · iapply (stateInterp_eq
      { store with wasm :=
          { store.wasm with mem := store.wasm.mem.write32 address newValue } }
      steps observations threads).mpr
    iexists
      insert
        (insert
          (insert
            (insert σ address (some (u32Byte newValue 0)))
            (address + 1) (some (u32Byte newValue 1)))
        (address + 2) (some (u32Byte newValue 2)))
        (address + 3) (some (u32Byte newValue 3))
    iexists globalσ
    iexists dataSegmentσ
    iexists tableσ
    iexists elementSegmentσ
    iframe Hheap Hglobals Hsegments Htables HelementSegments Hruntime
    ipureintro
    exact ⟨
        (store32_sound σ store.wasm.mem address newValue h1 h2 h3 Hfacts.1)
        , (store32_inBounds σ store.wasm.mem address newValue h1 h2 h3
          Hfacts.2.1 hbound)
        , Hfacts.2.2⟩
  · iapply (pointsTo_u32_eq address newValue).mpr
    iframe

theorem stateInterp_store64 [WasmSmallStepGS hlc]
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
    stateInterp (GF := WasmHeapGF) store steps observations threads ∗
      pointsTo_u64 address oldValue ==∗
      stateInterp (GF := WasmHeapGF)
        { store with wasm :=
            { store.wasm with mem := store.wasm.mem.write64 address newValue } }
        steps observations threads ∗
      pointsTo_u64 address newValue := by
  iintro ⟨Hstate, Hword⟩
  ihave Hword := (pointsTo_u64_eq address oldValue).mp $$ Hword
  icases Hword with ⟨H0, H1, H2, H3, H4, H5, H6, H7⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hruntime, %Hfacts⟩
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
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments Hruntime]
  · iapply (stateInterp_eq
      { store with wasm :=
          { store.wasm with mem := store.wasm.mem.write64 address newValue } }
      steps observations threads).mpr
    iexists store64Heap σ address newValue
    iexists globalσ
    iexists dataSegmentσ
    iexists tableσ
    iexists elementSegmentσ
    unfold store64Heap
    iframe Hheap Hglobals Hsegments Htables HelementSegments Hruntime
    ipureintro
    exact ⟨
      store64_sound σ store.wasm.mem address newValue
        h1 h2 h3 h4 h5 h6 h7 Hfacts.1,
      store64_inBounds σ store.wasm.mem address newValue
        h1 h2 h3 h4 h5 h6 h7 Hfacts.2.1 hbound,
      Hfacts.2.2⟩
  · iapply (pointsTo_u64_eq address newValue).mpr
    iframe

/-- Successful memory growth preserves the authoritative byte heap unchanged:
physical bytes are identical and every previously owned address remains in
bounds because the page count only increases. -/
theorem stateInterp_memoryGrow [WasmSmallStepGS hlc]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (delta : UInt32) (memory : Mem) (previousPages : Nat)
    (hgrow : store.wasm.mem.grow delta store.runtime.module.memoryCap =
      some (memory, previousPages)) :
    stateInterp (GF := WasmHeapGF) store steps observations threads ⊢
      stateInterp (GF := WasmHeapGF)
        { store with wasm := { store.wasm with mem := memory } }
        steps observations threads := by
  iintro Hstate
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ,
      Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hruntime, %Hfacts⟩
  iapply (stateInterp_eq
    { store with wasm := { store.wasm with mem := memory } }
    steps observations threads).mpr
  iexists σ
  iexists globalσ
  iexists dataSegmentσ
  iexists tableσ
  iexists elementSegmentσ
  iframe Hheap Hglobals Hsegments Htables HelementSegments Hruntime
  ipureintro
  exact ⟨grow_sound σ store.wasm.mem memory delta
      store.runtime.module.memoryCap previousPages hgrow Hfacts.1,
    grow_inBounds σ store.wasm.mem memory delta
      store.runtime.module.memoryCap previousPages hgrow Hfacts.2.1,
    Hfacts.2.2⟩

/-- Four-byte fill update used by the manual memory example. Ownership of the
whole affected range is required and is updated atomically. -/
theorem stateInterp_fill16_four_AB [WasmSmallStepGS hlc]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (oldWord : UInt32)
    (hbound : 20 ≤ store.wasm.mem.pages * 65536) :
    stateInterp (GF := WasmHeapGF) store steps observations threads ∗
      pointsTo_u32 16 oldWord ==∗
      stateInterp (GF := WasmHeapGF)
        { store with wasm :=
            { store.wasm with mem := store.wasm.mem.fill 16 4 0xAB } }
        steps observations threads ∗
      pointsTo_u32 16 0xABABABAB := by
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
theorem stateInterp_init16_four [WasmSmallStepGS hlc]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (oldWord : UInt32)
    (hbound : 20 ≤ store.wasm.mem.pages * 65536) :
    stateInterp (GF := WasmHeapGF) store steps observations threads ∗
      pointsTo_u32 16 oldWord ==∗
      stateInterp (GF := WasmHeapGF)
        { store with wasm :=
            { store.wasm with mem :=
                store.wasm.mem.writeBytesFrom 16 [1, 2, 3, 4] 0 4 } }
        steps observations threads ∗
      pointsTo_u32 16 0x04030201 := by
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
theorem stateInterp_copy8_zero_four [WasmSmallStepGS hlc]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (oldDestination : UInt32) :
    stateInterp (GF := WasmHeapGF) store steps observations threads ∗
      pointsTo_u32 0 0x04030201 ∗ pointsTo_u32 8 oldDestination ==∗
      stateInterp (GF := WasmHeapGF)
        { store with wasm :=
            { store.wasm with mem := store.wasm.mem.copy 8 0 4 } }
        steps observations threads ∗
      pointsTo_u32 0 0x04030201 ∗ pointsTo_u32 8 0x04030201 := by
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
theorem stateInterp_copy2_zero_four [WasmSmallStepGS hlc]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat) :
    stateInterp (GF := WasmHeapGF) store steps observations threads ∗
      pointsTo_u64 0 0x8877665544332211 ==∗
      stateInterp (GF := WasmHeapGF)
        { store with wasm :=
            { store.wasm with mem := store.wasm.mem.copy 2 0 4 } }
        steps observations threads ∗
      pointsTo_u64 0 0x8877443322112211 := by
  iintro ⟨Hstate, Hword⟩
  imod stateInterp_pointsTo_u64_facts_frame
      store steps observations threads
      0 0x8877665544332211 rfl rfl rfl rfl rfl rfl rfl $$
      [$Hstate $Hword] with ⟨Hstate, Hword, %Hfacts⟩
  ihave Hword :=
    (pointsTo_u64_eq 0 0x8877665544332211).mp $$ Hword
  icases Hword with ⟨H0, H1, H2, H3, H4, H5, H6, H7⟩
  ihave H2At :
      pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        2 (DFrac.own 1) (some (u64Byte 0x8877665544332211 2)) $$ [H2]
  · rw [show (0 : UInt32) + 2 = 2 by decide]
    iexact H2
  ihave H3At :
      pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        3 (DFrac.own 1) (some (u64Byte 0x8877665544332211 3)) $$ [H3]
  · rw [show (0 : UInt32) + 3 = 3 by decide]
    iexact H3
  ihave H4At :
      pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        4 (DFrac.own 1) (some (u64Byte 0x8877665544332211 4)) $$ [H4]
  · rw [show (0 : UInt32) + 4 = 4 by decide]
    iexact H4
  ihave H5At :
      pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        5 (DFrac.own 1) (some (u64Byte 0x8877665544332211 5)) $$ [H5]
  · rw [show (0 : UInt32) + 5 = 5 by decide]
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
  · iapply (pointsTo_u64_eq 0 0x8877443322112211).mpr
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

instance instIrisGS [WasmSmallStepGS hlc] :
    IrisGS_gen hlc (Expr α) WasmHeapGF where
  numLatersPerStep _ := 0
  forkPost _ := iprop(True)
  stateInterp_mono _ _ _ _ := by iintro $

end Wasm.SmallStep
