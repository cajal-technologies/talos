import Mathlib
import CodeLib

namespace Project.HexEncodeStdio.Grow

open Wasm
open Iris Iris.BI Iris.ProgramLogic Language.Notation Iris.Std
open Wasm.SepLogic Wasm.SmallStep

/-- Insert a consecutive byte string in the authoritative Wasm heap. -/
def insertBytes (σ : WasmHeapMap (Option UInt8)) (addr : UInt32) :
    List UInt8 → WasmHeapMap (Option UInt8)
  | [] => σ
  | b :: bs => insertBytes (insert σ ⟨0, addr⟩ (some b)) (addr + 1) bs

/-- The physical contents of a consecutive range. -/
def bytesAt (memory : Mem) (addr : UInt32) : Nat → List UInt8
  | 0 => []
  | n + 1 => memory.read8 addr :: bytesAt memory (addr + 1) n

@[simp] theorem bytesAt_length (memory : Mem) (addr : UInt32) (n : Nat) :
    (bytesAt memory addr n).length = n := by
  induction n generalizing addr with
  | zero => rfl
  | succ n ih => simp [bytesAt, ih]

private theorem addr_succ_ne (addr : UInt32) (i : Nat)
    (hnowrap : addr.toNat + i + 1 < UInt32.size) :
    addr + UInt32.ofNat (i + 1) ≠ addr := by
  intro h
  have ht := congrArg UInt32.toNat h
  have hi : i + 1 < UInt32.size := by omega
  rw [UInt32.add_ofNat_toNat_noWrap addr (i + 1) hi (by omega)] at ht
  omega

/-- Allocating fresh consecutive entries in `genHeapInterp` exposes exactly
the corresponding `pointsToBytes` resource. -/
theorem genHeap_alloc_bytes {hlc : HasLC} {α : Type}
    [WasmSmallStepGS hlc α]
    (σ : WasmHeapMap (Option UInt8)) (addr : UInt32) (bytes : List UInt8)
    (hnowrap : addr.toNat + bytes.length < UInt32.size)
    (hfresh : ∀ i, i < bytes.length →
      get? σ (⟨0, addr + UInt32.ofNat i⟩ : MemoryKey) = none) :
    genHeapInterp σ ==∗
      genHeapInterp (insertBytes σ addr bytes) ∗ pointsToBytes 0 addr bytes := by
  induction bytes generalizing σ addr with
  | nil =>
      simp only [insertBytes, pointsToBytes]
      iintro Hσ
      imodintro
      iframe
  | cons b bs ih =>
      simp only [List.length_cons] at hnowrap
      have haddr : get? σ (⟨0, addr⟩ : MemoryKey) = none := by
        simpa using hfresh 0 (by simp)
      iintro Hσ
      imod genHeap_alloc haddr $$ Hσ with ⟨Hσ, Haddr, Hmeta⟩
      iclear Hmeta
      have hsucc : (addr + 1).toNat = addr.toNat + 1 :=
        UInt32.add_ofNat_toNat_noWrap addr 1 (by decide) (by
          norm_num [UInt32.size] at hnowrap ⊢
          omega)
      have hnowrap' : (addr + 1).toNat + bs.length < UInt32.size := by
        rw [hsucc]
        omega
      have hfresh' : ∀ i, i < bs.length →
          get? (insert σ (⟨0, addr⟩ : MemoryKey) (some b))
            (⟨0, (addr + 1) + UInt32.ofNat i⟩ : MemoryKey) = none := by
        intro i hi
        have hshift : (addr + 1) + UInt32.ofNat i =
            addr + UInt32.ofNat (i + 1) := by
          rw [UInt32.ofNat_add, show UInt32.ofNat 1 = 1 by rfl]
          simp only [UInt32.add_assoc]
          rw [UInt32.add_comm 1 (UInt32.ofNat i)]
        rw [hshift, get?_insert_ne]
        · exact hfresh (i + 1) (by simp; omega)
        · intro heq
          exact addr_succ_ne addr i (by omega)
            (congrArg MemoryKey.addr heq).symm
      imod ih (insert σ (⟨0, addr⟩ : MemoryKey) (some b)) (addr + 1)
          hnowrap' hfresh' $$ Hσ with ⟨Hσ, Hbs⟩
      imodintro
      isplitl [Hσ]
      · simp only [insertBytes]
        iexact Hσ
      · simp only [pointsToBytes]
        iframe

private theorem insert_read_agrees
    (σ : WasmHeapMap (Option UInt8)) (resolve : Nat → Option Mem)
    (memory : Mem) (addr : UInt32)
    (hresolve : resolve 0 = some memory)
    (hagree : heapAgreesWithMem σ resolve) :
    heapAgreesWithMem (insert σ (⟨0, addr⟩ : MemoryKey)
      (some (memory.read8 addr))) resolve := by
  intro key value hget
  by_cases heq : key = (⟨0, addr⟩ : MemoryKey)
  · subst key
    simp only [get?_insert_eq rfl, Option.some.injEq] at hget
    subst value
    exact ⟨memory, hresolve, rfl⟩
  · rw [get?_insert_ne (Ne.symm heq)] at hget
    exact hagree key value hget

private theorem insert_read_inBounds
    (σ : WasmHeapMap (Option UInt8)) (resolve : Nat → Option Mem)
    (memory : Mem) (addr : UInt32)
    (hresolve : resolve 0 = some memory)
    (hinBounds : heapAddressesInBounds σ resolve)
    (haddr : addr.toNat < memory.pages * 65536) :
    heapAddressesInBounds (insert σ (⟨0, addr⟩ : MemoryKey)
      (some (memory.read8 addr))) resolve := by
  intro key hget
  by_cases heq : key = (⟨0, addr⟩ : MemoryKey)
  · subst key
    exact ⟨memory, hresolve, haddr⟩
  · rw [get?_insert_ne (Ne.symm heq)] at hget
    exact hinBounds key hget

theorem insertBytes_agrees
    (σ : WasmHeapMap (Option UInt8)) (resolve : Nat → Option Mem)
    (memory : Mem) (addr : UInt32) (n : Nat)
    (hresolve : resolve 0 = some memory)
    (hnowrap : addr.toNat + n < UInt32.size)
    (hagree : heapAgreesWithMem σ resolve) :
    heapAgreesWithMem (insertBytes σ addr (bytesAt memory addr n)) resolve := by
  induction n generalizing σ addr with
  | zero => exact hagree
  | succ n ih =>
      simp only [bytesAt, insertBytes]
      have hsucc : (addr + 1).toNat = addr.toNat + 1 :=
        UInt32.add_ofNat_toNat_noWrap addr 1 (by decide) (by
          norm_num [UInt32.size] at hnowrap ⊢
          omega)
      apply ih (insert σ (⟨0, addr⟩ : MemoryKey) (some (memory.read8 addr)))
        (addr + 1)
      · rw [hsucc]
        omega
      · exact insert_read_agrees σ resolve memory addr hresolve hagree

theorem insertBytes_inBounds
    (σ : WasmHeapMap (Option UInt8)) (resolve : Nat → Option Mem)
    (memory : Mem) (addr : UInt32) (n : Nat)
    (hresolve : resolve 0 = some memory)
    (hnowrap : addr.toNat + n < UInt32.size)
    (hrange : addr.toNat + n ≤ memory.pages * 65536)
    (hinBounds : heapAddressesInBounds σ resolve) :
    heapAddressesInBounds (insertBytes σ addr (bytesAt memory addr n)) resolve := by
  induction n generalizing σ addr with
  | zero => exact hinBounds
  | succ n ih =>
      simp only [bytesAt, insertBytes]
      have hsucc : (addr + 1).toNat = addr.toNat + 1 :=
        UInt32.add_ofNat_toNat_noWrap addr 1 (by decide) (by
          norm_num [UInt32.size] at hnowrap ⊢
          omega)
      apply ih (insert σ (⟨0, addr⟩ : MemoryKey) (some (memory.read8 addr)))
        (addr + 1)
      · rw [hsucc]
        omega
      · rw [hsucc]
        omega
      · apply insert_read_inBounds σ resolve memory addr hresolve hinBounds
        omega

private theorem storeResolve_zero {α : Type} (store : MachineStore α) :
    storeResolve store 0 = some store.wasm.mem := by
  simp [storeResolve]

private theorem storeResolve_update_mem0 {α : Type}
    (store : MachineStore α) (newMem : Mem) :
    (fun id => if id = 0 then some newMem else storeResolve store id) =
      storeResolve { store with wasm := { store.wasm with mem := newMem } } := by
  funext id
  simp only [storeResolve]
  by_cases h : id = 0 <;> simp [h]

set_option maxRecDepth 100000 in
/-- Successful growth can soundly expose ownership of every newly addressable
byte.  The byte values are read from the physical memory, so this lemma does
not rely on an extra zero-initialization invariant. -/
theorem stateInterp_memoryGrow_owned {hlc : HasLC} {α : Type}
    [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (delta : UInt32) (cap : Nat) (memory : Mem) (previousPages : Nat)
    (hgrow : store.wasm.mem.grow delta cap = some (memory, previousPages))
    (hlimit : (previousPages + delta.toNat) * 65536 < UInt32.size) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      heapFrontierOwn UInt32.size ==∗
      stateInterp (GF := WasmHeapGF α)
        { store with wasm := { store.wasm with mem := memory } }
        steps observations threads ∗
      pointsToBytes 0 (UInt32.ofNat (previousPages * 65536))
        (bytesAt memory (UInt32.ofNat (previousPages * 65536))
          (delta.toNat * 65536)) ∗
      heapFrontierOwn UInt32.size := by
  have hgrowFacts : previousPages = store.wasm.mem.pages ∧
      memory.pages = store.wasm.mem.pages + delta.toNat ∧
      memory.bytes = store.wasm.mem.bytes := by
    simp only [Mem.grow] at hgrow
    split at hgrow
    · exact ⟨(Prod.mk.inj (Option.some.inj hgrow)).2.symm,
        congrArg Mem.pages (Prod.mk.inj (Option.some.inj hgrow)).1.symm,
        by simpa using
          congrArg Mem.bytes (Prod.mk.inj (Option.some.inj hgrow)).1.symm⟩
    · contradiction
  have htotal : previousPages * 65536 + delta.toNat * 65536 < UInt32.size := by
    simpa only [Nat.add_mul] using hlimit
  have hbase : (UInt32.ofNat (previousPages * 65536)).toNat =
      previousPages * 65536 := by
    apply UInt32.toNat_ofNat_of_lt'
    exact lt_of_le_of_lt (Nat.le_add_right _ _) htotal
  have hnowrap : (UInt32.ofNat (previousPages * 65536)).toNat +
      (bytesAt memory (UInt32.ofNat (previousPages * 65536))
        (delta.toNat * 65536)).length < UInt32.size := by
    rw [hbase]
    simp only [bytesAt_length]
    simpa [Nat.add_mul] using hlimit
  iintro ⟨Hstate, HheapFrontierOwn⟩
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ,
      %runtimeModuleσ, %hostEnvσ, Hheap, Hglobals, Hsegments, Htables,
      HelementSegments, HruntimeModuleAuth, HruntimeModuleBigSep,
      HruntimeInstances, HinstanceAuth, HhostEnvAuth, HstateAuth,
      %Hfacts, Hexc⟩
  have hfresh : ∀ i,
      i < (bytesAt memory (UInt32.ofNat (previousPages * 65536))
        (delta.toNat * 65536)).length →
      get? σ
        (⟨0, UInt32.ofNat (previousPages * 65536) + UInt32.ofNat i⟩ :
          MemoryKey) = none := by
    intro i hi
    simp only [bytesAt_length] at hi
    by_contra hne
    obtain ⟨oldMemory, hresolve, hbound⟩ := Hfacts.2.1 _ hne
    have hold : oldMemory = store.wasm.mem :=
      Option.some.inj (hresolve.symm.trans (storeResolve_zero store))
    subst oldMemory
    have hi32 : i < UInt32.size := by
      exact lt_trans hi (lt_of_le_of_lt (Nat.le_add_left _ _) htotal)
    have hadd :
        (UInt32.ofNat (previousPages * 65536) + UInt32.ofNat i).toNat =
          previousPages * 65536 + i := by
      rw [UInt32.add_ofNat_toNat_noWrap _ i hi32]
      · rw [hbase]
      · rw [hbase]
        exact Nat.add_lt_add_left hi _ |>.trans htotal
    rw [hadd, ← hgrowFacts.1] at hbound
    omega
  imod genHeap_alloc_bytes σ (UInt32.ofNat (previousPages * 65536))
      (bytesAt memory (UInt32.ofNat (previousPages * 65536))
        (delta.toNat * 65536)) hnowrap hfresh $$ Hheap with ⟨Hheap, Hnew⟩
  have hgrownAgree := grow_sound σ (storeResolve store) 0 store.wasm.mem memory
    delta cap previousPages hgrow (storeResolve_zero store) Hfacts.1
  rw [storeResolve_update_mem0] at hgrownAgree
  have hagree := insertBytes_agrees σ
    (storeResolve { store with wasm := { store.wasm with mem := memory } })
    memory (UInt32.ofNat (previousPages * 65536))
    (delta.toNat * 65536) (storeResolve_zero _)
    (by simpa only [bytesAt_length] using hnowrap) hgrownAgree
  have hgrownBounds := grow_inBounds σ (storeResolve store) 0 store.wasm.mem memory
    delta cap previousPages hgrow (storeResolve_zero store) Hfacts.2.1
  rw [storeResolve_update_mem0] at hgrownBounds
  have hrange : (UInt32.ofNat (previousPages * 65536)).toNat +
      delta.toNat * 65536 ≤ memory.pages * 65536 := by
    rw [hbase, hgrowFacts.2.1, ← hgrowFacts.1]
    omega
  have hinBounds := insertBytes_inBounds σ
    (storeResolve { store with wasm := { store.wasm with mem := memory } })
    memory (UInt32.ofNat (previousPages * 65536))
    (delta.toNat * 65536) (storeResolve_zero _)
    (by simpa only [bytesAt_length] using hnowrap) hrange hgrownBounds
  iunfold machineAuxInterp at Hexc
  icases Hexc with ⟨Hpages, Hdomain, HexceptionInterp⟩
  iunfold heapDomainInterp at Hdomain
  icases Hdomain with ⟨%actualFrontier, HfrontierAuth, %Hbelow⟩
  icombine HfrontierAuth HheapFrontierOwn as Hfrontier
  ihave %hfrontierEq := heapFrontierOwn_agree actualFrontier UInt32.size $$ Hfrontier
  subst actualFrontier
  icases Hfrontier with ⟨HfrontierAuth, HheapFrontierOwn⟩
  have hpagesMono : store.wasm.mem.pages ≤ memory.pages := by
    rw [hgrowFacts.2.1]
    exact Nat.le_add_right _ _
  imod memoryPagesAuth_update store.wasm.mem.pages memory.pages hpagesMono $$
      Hpages with ⟨Hpages, -⟩
  ihave Haux : machineAuxInterp
      (insertBytes σ (UInt32.ofNat (previousPages * 65536))
        (bytesAt memory (UInt32.ofNat (previousPages * 65536))
          (delta.toNat * 65536)))
      memory.pages store.wasm.exns store.wasm.tagIds $$
      [Hpages HfrontierAuth HexceptionInterp]
  · unfold machineAuxInterp heapDomainInterp
    isplitl [Hpages]
    · iexact Hpages
    · isplitl [HfrontierAuth]
      · iexists UInt32.size
        iframe HfrontierAuth
        ipureintro
        exact heapBelow_uint32Size _
      · iexact HexceptionInterp
  imodintro
  isplitl [Hheap Hglobals Hsegments Htables HelementSegments
      HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth
      HhostEnvAuth HstateAuth Haux]
  · iapply (stateInterp_eq
      { store with wasm := { store.wasm with mem := memory } }
      steps observations threads).mpr
    iexists insertBytes σ (UInt32.ofNat (previousPages * 65536))
      (bytesAt memory (UInt32.ofNat (previousPages * 65536))
        (delta.toNat * 65536))
    iexists globalσ
    iexists dataSegmentσ
    iexists tableσ
    iexists elementSegmentσ
    iexists runtimeModuleσ
    iexists hostEnvσ
    iframe Hheap Hglobals Hsegments Htables HelementSegments
      HruntimeModuleAuth HruntimeModuleBigSep HruntimeInstances HinstanceAuth
      HhostEnvAuth HstateAuth
    isplitr [Haux]
    · ipureintro
      exact ⟨hagree, hinBounds, Hfacts.2.2⟩
    · iexact Haux
  · isplitl [Hnew]
    · iexact Hnew
    · iexact HheapFrontierOwn

/-- `memory.grow` with ownership of the newly exposed physical range on the
success branch.  The explicit bound is the wasm32 condition used by the
allocator before it executes the instruction. -/
theorem wp_memoryGrow_owned {hlc : HasLC} {α : Type}
    [WasmSmallStepGS hlc α] {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF α)}
    {params localValues values : List Value} {delta : UInt32}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (runtimeModule : Module) (instanceId : ModuleInstanceId)
    (hbound : ∀ (store : MachineStore α) (memory : Mem)
        (previousPages : Nat),
      store.wasm.mem.grow delta
          (store.wasm.memoryCap store.runtime.currentModule 0) =
        some (memory, previousPages) →
      (previousPages + delta.toNat) * 65536 < UInt32.size)
    (Hfail : runtimeModuleOwn instanceId runtimeModule -∗
      heapFrontierOwn UInt32.size -∗
      WP (.running ⟨⟨params, localValues,
          .i32 (0xFFFFFFFF : UInt32) :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E {{ Φ }})
    (Hsuccess : ∀ (memory : Mem) (previousPages : Nat),
      pointsToBytes 0 (UInt32.ofNat (previousPages * 65536))
          (bytesAt memory (UInt32.ofNat (previousPages * 65536))
            (delta.toNat * 65536)) -∗
      runtimeModuleOwn instanceId runtimeModule -∗
      heapFrontierOwn UInt32.size -∗
      WP (.running ⟨⟨params, localValues,
          .i32 previousPages.toUInt32 :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E {{ Φ }}) :
    ▷ runtimeModuleOwn instanceId runtimeModule -∗
    heapFrontierOwn UInt32.size -∗
    WP (.running ⟨⟨params, localValues, .i32 delta :: values⟩,
        .memoryGrow :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E {{ Φ }} := by
  iintro >Hruntime HheapFrontierOwn
  iapply wp_lift_step rfl
  iintro %store %ns %obs %obs' %nt Hσ
  cases hg : store.wasm.mem.grow delta
      (store.wasm.memoryCap store.runtime.currentModule 0) with
  | none =>
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hclose
    isplitr
    · ipureintro
      cases s <;> simp only [Stuckness.MaybeReducible]
      exact ⟨[], _, store, [], ⟨rfl, _, rfl, Step.memoryGrowFailure hg⟩⟩
    iintro !> %e₂ %store₂ %forks %Hstep Hcredit
    rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
    change forks = [] at hforks
    subst forks
    subst obs
    obtain ⟨rfl, hconfig⟩ :=
      step_deterministic (Step.memoryGrowFailure hg) wasmStep
    have parts := Config.mk.inj hconfig
    have hexpr := parts.1
    have hstore := parts.2
    simp only at hexpr hstore
    subst e₂
    subst store₂
    simp only [List.length_nil, Nat.add_zero,
      Iris.Algebra.BigOpL.bigOpL_nil]
    imod Hclose
    imodintro
    isplitl [Hσ]
    · iexact Hσ
    isplitl [Hruntime HheapFrontierOwn]
    · iapply Hfail $$ Hruntime HheapFrontierOwn
    · itrivial
  | some grown =>
    obtain ⟨memory, previousPages⟩ := grown
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hclose
    isplitr
    · ipureintro
      cases s <;> simp only [Stuckness.MaybeReducible]
      exact ⟨[],
        .running ⟨⟨params, localValues,
            .i32 previousPages.toUInt32 :: values⟩,
          code, arity, remainder, controls, calls⟩,
        { store with wasm := { store.wasm with mem := memory } }, [],
        ⟨rfl, _, rfl, by
          simpa only [Wasm.SmallStep.setMemory_eq] using
            Step.memoryGrowSuccess hg⟩⟩
    iintro !> %e₂ %store₂ %forks %Hstep Hcredit
    rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
    change forks = [] at hforks
    subst forks
    subst obs
    have expectedStep : Step
        ⟨.running ⟨⟨params, localValues, .i32 delta :: values⟩,
          .memoryGrow :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .memoryGrow)
        ⟨.running ⟨⟨params, localValues,
            .i32 previousPages.toUInt32 :: values⟩,
          code, arity, remainder, controls, calls⟩,
          { store with wasm := { store.wasm with mem := memory } }⟩ := by
      simpa only [Wasm.SmallStep.setMemory_eq] using Step.memoryGrowSuccess hg
    obtain ⟨rfl, hconfig⟩ := step_deterministic expectedStep wasmStep
    have parts := Config.mk.inj hconfig
    have hexpr := parts.1
    have hstore := parts.2
    simp only at hexpr hstore
    subst e₂
    subst store₂
    simp only [List.length_nil, Nat.add_zero,
      Iris.Algebra.BigOpL.bigOpL_nil]
    imod Hclose
    icombine Hσ HheapFrontierOwn as Hinput
    imod stateInterp_memoryGrow_owned store ns obs' nt delta
      (store.wasm.memoryCap store.runtime.currentModule 0)
      memory previousPages hg (hbound store memory previousPages hg) $$
      Hinput with ⟨Hσ, Hnew, HheapFrontierOwn⟩
    imodintro
    isplitl [Hσ]
    · iexact Hσ
    isplitl [Hruntime Hnew HheapFrontierOwn]
    · iapply Hsuccess memory previousPages $$ Hnew Hruntime HheapFrontierOwn
    · itrivial

end Project.HexEncodeStdio.Grow
