import CodeLib.SepLogic.SmallStepGhostInit
import CodeLib.SepLogic.PrefixResources

/-!
# Whole-state initialization with exact primary-memory pages

These initializers allocate the existing Wasm ghost resources for the supplied
physical store. The state retains half of its page authority and the client
receives the other half, or a persistent frozen token derived from that half.
No physical memory, cap, runtime instance, or host state is replaced.

The ambient invariant instance is retained explicitly in the existential
result so an adequacy frontend can use the returned Wasm instance with its
original invariant machinery. The initializers do not assume a program WP or
an execution trace. The prefix frontend then combines this initialization
with a client total WP to establish exact pages at each reached store.
-/

namespace Wasm.SmallStep

open Iris Iris.ProgramLogic Std
open Wasm.SepLogic

variable {α : Type} {hlc : HasLC}

/-- Client resources for a concrete store with explicit sparse heap, globals,
allocator frontier, and selected physical memory caps. -/
def InitialMachineClientResources [WasmSmallStepGS hlc α]
    (config : Config α) (σ : WasmHeapMap (Option UInt8))
    (globalσ : WasmGlobalMap Value) (capσ : WasmMemoryCapMap Nat)
    (frontier : Nat) : IProp (WasmHeapGF α) := iprop(
  ([∗map] address ↦ value ∈ σ,
    pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
      address (DFrac.own 1) value) ∗
  ([∗map] index ↦ value ∈ globalσ, globalPointsTo index value) ∗
  runtimeModuleOwn config.store.runtime.entry config.store.runtime.currentModule ∗
  hostEnvOwn config.store.runtime.entry.id config.store.runtime.currentHost ∗
  hostStateOwn config.store.wasm.host ∗
  heapFrontierOwn frontier ∗
  memoryPagesOwn config.store.wasm.mem.pages ∗
  ([∗map] index ↦ cap ∈ capσ, memoryCapOwn index cap))

/-- Initialize the actual store and ordinary client footprint, retaining a
state half and a matching linear page token. The pure premises are the same
physical footprint agreements used by the existing cap-aware frontends. -/
theorem smallStep_init_exact_at_caps
    [inv : InvGS_gen hlc (WasmHeapGF α)]
    (config : Config α)
    (σ : WasmHeapMap (Option UInt8))
    (globalσ : WasmGlobalMap Value)
    (capσ : WasmMemoryCapMap Nat)
    (frontier : Nat)
    (hagree : heapAgreesWithMem σ (storeResolve config.store))
    (hinBounds : heapAddressesInBounds σ (storeResolve config.store))
    (hbelow : HeapBelow σ frontier)
    (hcaps : capHeapAgrees capσ config.store.wasm.mem.pages config.store.wasm.memoryCaps)
    (hglobals : globalHeapAgrees globalσ config.store.wasm.globals)
    (hwf : config.store.runtime.entry.id < config.store.runtime.instances.size) :
    ⊢@{IProp (WasmHeapGF α)} |==>
      ∃ gs : WasmSmallStepGS hlc α,
        (letI : WasmSmallStepGS hlc α := gs
         iprop(⌜gs.toInvGS_gen = inv ∧ gs.memoryPages.stateFrac = (1 : Qp).half⌝ ∗
           stateInterp (GF := WasmHeapGF α) config.store 0 [] 0 ∗
           InitialMachineClientResources config σ globalσ capσ frontier ∗
           memoryPagesHalf config.store.wasm.mem.pages)) := by
  imod genHeap_init (L := MemoryKey) (V := Option UInt8)
      (GF := WasmHeapGF α) (H := WasmHeapMap) σ with
    ⟨%heapGS, Hheap, Hpoints, Hmeta⟩
  imod heapDomain_init_at (α := α) σ frontier hbelow with
    ⟨%heapDomainGS, HheapDomain, HheapFrontier⟩
  letI _ : WasmHeapDomainGS α := heapDomainGS
  imod memoryPages_init_exact (α := α) config.store.wasm.mem.pages with
    ⟨%memoryPagesGS, %hMemoryPagesHalf, HmemoryPagesAuth, HmemoryPagesHalf⟩
  letI _ : WasmMemoryPagesGS α := memoryPagesGS
  ihave #HmemoryPagesOwn := memoryPagesOwn_snapshot config.store.wasm.mem.pages $$
    HmemoryPagesAuth
  imod memoryCaps_init_at (α := α) capσ config.store.wasm.mem.pages
      config.store.wasm.memoryCaps hcaps with
    ⟨%memoryCapsGS, HmemoryCapsInterp, HcapPoints⟩
  letI _ : WasmMemoryCapsGS α := memoryCapsGS
  wasm_alloc_globals_and_empty_heap_maps globalσ
  wasm_install_heap_map_instances
  wasm_alloc_current_runtime_module config
  wasm_alloc_current_host_env config
  wasm_alloc_host_state config
  wasm_alloc_current_instance config
  wasm_alloc_fixed_runtime_resources config
  letI gs : WasmSmallStepGS hlc α := smallStepGS hlc inv
  iclear Hmeta
  wasm_build_machine_aux config
  imodintro
  iexists gs
  isplitr
  · ipureexact ⟨rfl, hMemoryPagesHalf⟩
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth'
      HruntimeInstances HinstanceState HhostEnvAuth' HhostState Hexc]
  · iapply (stateInterp_eq config.store 0 [] 0).mpr
    iexists σ, globalσ
    iexists (∅ : WasmDataSegmentMap (Option (List UInt8)))
    iexists (∅ : WasmTableMap TableInst)
    iexists (∅ : WasmElementSegmentMap (Option (List (Option Nat))))
    iexists (PartialMap.singleton config.store.runtime.entry.id
      config.store.runtime.currentModule)
    iexists (PartialMap.singleton config.store.runtime.entry.id
      config.store.runtime.currentHost)
    unfold runtimeModuleElem runtimeInstancesOwn hostStateAuth currentInstanceAuth
      currentInstanceAuthN
    simp only [BI.BigSepM.bigSepM_singleton.to_eq]
    iframe Hheap Hglobals Hsegments Htables HelementSegments HruntimeModuleAuth'
      # HruntimeInstances HinstanceState HhostEnvAuth' HhostState Hexc
    ipureexact ⟨hagree, hinBounds, hglobals,
      dataSegmentHeapAgrees_empty _, tableHeapAgrees_empty _,
      elementSegmentHeapAgrees_empty _,
      runtimeModuleSingletonAgrees config.store.runtime hwf,
      hostEnvSingletonAgrees config.store.runtime hwf⟩
  isplitr [HmemoryPagesHalf]
  · unfold InitialMachineClientResources
    isplitl_exact Hpoints
    isplitl [HglobalPoints]
    · unfold globalPointsTo
      iexact HglobalPoints
    isplitl [HruntimeWP HinstanceFrag]
    · unfold runtimeModuleOwn
      isplitl [HruntimeWP]
      · unfold runtimeModuleElem
        iexact HruntimeWP
      · unfold currentInstanceOwnN
        iexact HinstanceFrag
    isplitl [HhostEnvWP]
    · unfold hostEnvOwn
      iexact HhostEnvWP
    isplitl [HhostStateFrag]
    · unfold hostStateOwn
      iexact HhostStateFrag
    isplitl_exact HheapFrontier
    isplitl_exact HmemoryPagesOwn
    iexact HcapPoints
  · iexact HmemoryPagesHalf

/-- Freeze the client half allocated for the same actual store. All ordinary
client resources and the retained state interpretation are unchanged. -/
theorem smallStep_init_frozen_at_caps
    [inv : InvGS_gen hlc (WasmHeapGF α)]
    (config : Config α)
    (σ : WasmHeapMap (Option UInt8))
    (globalσ : WasmGlobalMap Value)
    (capσ : WasmMemoryCapMap Nat)
    (frontier : Nat)
    (hagree : heapAgreesWithMem σ (storeResolve config.store))
    (hinBounds : heapAddressesInBounds σ (storeResolve config.store))
    (hbelow : HeapBelow σ frontier)
    (hcaps : capHeapAgrees capσ config.store.wasm.mem.pages config.store.wasm.memoryCaps)
    (hglobals : globalHeapAgrees globalσ config.store.wasm.globals)
    (hwf : config.store.runtime.entry.id < config.store.runtime.instances.size) :
    ⊢@{IProp (WasmHeapGF α)} |==>
      ∃ gs : WasmSmallStepGS hlc α,
        (letI : WasmSmallStepGS hlc α := gs
         iprop(⌜gs.toInvGS_gen = inv ∧ gs.memoryPages.stateFrac = (1 : Qp).half⌝ ∗
           stateInterp (GF := WasmHeapGF α) config.store 0 [] 0 ∗
           InitialMachineClientResources config σ globalσ capσ frontier ∗
           memoryPagesFrozen config.store.wasm.mem.pages)) := by
  imod smallStep_init_exact_at_caps config σ globalσ capσ frontier
      hagree hinBounds hbelow hcaps hglobals hwf with
    ⟨%gs, %hmode, Hstate, Hclient, Hhalf⟩
  letI : WasmSmallStepGS hlc α := gs
  imod memoryPagesHalf_freeze config.store.wasm.mem.pages $$ Hhalf with Hfrozen
  imodintro
  iexists gs
  iframe Hstate Hclient Hfrozen
  ipureexact hmode

section Prefix

open Language.Notation

variable {Terminal : Type} [view : TerminalView α Terminal]

local instance (priority := high) exactPagesTerminalLanguage :
    Language (Expr α) (MachineStore α) StepKind Terminal :=
  TerminalView.canonicalLanguage

local instance (priority := high) exactPagesTerminalIrisGS
    [WasmSmallStepGS hlc α] :
    @IrisGS_gen hlc (Expr α) Terminal (MachineStore α) StepKind
      exactPagesTerminalLanguage (WasmHeapGF α) where
  numLatersPerStep _ := 0
  forkPost _ := iprop(True)
  stateInterp_mono _ _ _ _ := by iintro $

/-- A program proved from the actual initial footprint and a frozen page token
preserves that exact physical count at every reached configuration. The page
mode and state interpretation are allocated here, rather than assumed. -/
theorem frozen_pages_at_every_prefix
    [InvGpreS (WasmHeapGF α)]
    (initial : Config α)
    (σ : WasmHeapMap (Option UInt8))
    (globalσ : WasmGlobalMap Value)
    (capσ : WasmMemoryCapMap Nat)
    (frontier : Nat)
    (hagree : heapAgreesWithMem σ (storeResolve initial.store))
    (hinBounds : heapAddressesInBounds σ (storeResolve initial.store))
    (hbelow : HeapBelow σ frontier)
    (hcaps : capHeapAgrees capσ initial.store.wasm.mem.pages initial.store.wasm.memoryCaps)
    (hglobals : globalHeapAgrees globalσ initial.store.wasm.globals)
    (hwf : initial.store.runtime.entry.id < initial.store.runtime.instances.size)
    (hwp : ∀ [WasmSmallStepGS .hasLC α],
      InitialMachineClientResources initial σ globalσ capσ frontier ∗
        memoryPagesFrozen initial.store.wasm.mem.pages ⊢
        WP initial.expr @ Stuckness.NotStuck; ⊤ [{ _value, iprop(True) }])
    {trace : List StepKind} {reached : Config α}
    (execution : Steps initial trace reached) :
    reached.store.wasm.mem.pages = initial.store.wasm.mem.pages := by
  apply twp_prefix_invariance (Terminal := Terminal) initial reached trace
    (reached.store.wasm.mem.pages = initial.store.wasm.mem.pages) ?_ execution
  intro inv observations
  imod smallStep_init_frozen_at_caps initial σ globalσ capσ frontier
      hagree hinBounds hbelow hcaps hglobals hwf with
    ⟨%gs, %hmode, Hstate, Hclient, #Hfrozen⟩
  rcases hmode with ⟨rfl, hhalf⟩
  letI : WasmSmallStepGS .hasLC α := gs
  iexists (fun store observations threads =>
    stateInterp (GF := WasmHeapGF α) store 0 observations threads),
    (fun _value : Terminal => iprop(True))
  imodintro
  isplitl_exact Hstate
  isplitl [Hclient]
  · iapply hwp
    iframe Hclient Hfrozen
  iintro Hreached
  iexists ⊤
  imodintro
  iapply stateInterp_memoryPages_frozen_agree reached.store 0 [] 0
    initial.store.wasm.mem.pages
  iframe Hreached Hfrozen

end Prefix

end Wasm.SmallStep
