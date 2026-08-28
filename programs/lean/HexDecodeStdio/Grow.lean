import HexDecodeStdio.DecodeSpec
import HexDecodeStdio.TotalLifting

namespace Submission.HexDecodeStdio

open Wasm Project.HexStdio
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep

variable {hlc : outParam HasLC} {α : Type}

/-- Insert byte ownership for a consecutive range into a ghost heap. -/
def insertByteRange (σ : WasmHeapMap (Option UInt8)) (addr : UInt32) :
    List UInt8 → WasmHeapMap (Option UInt8)
  | [] => σ
  | b :: bs => insertByteRange (insert σ ⟨0, addr⟩ (some b)) (addr + 1) bs

private theorem insertByteRange_alloc
    [WasmSmallStepGS hlc α]
    (σ : WasmHeapMap (Option UInt8)) (addr : UInt32) (bytes : List UInt8)
    (hfresh : ∀ i, i < bytes.length →
      get? σ (⟨0, addr + UInt32.ofNat i⟩ : MemoryKey) = none)
    (hnowrap : addr.toNat + bytes.length < UInt32.size) :
    genHeapInterp (GF := WasmHeapGF α) σ ==∗
      genHeapInterp (insertByteRange σ addr bytes) ∗
      pointsToBytes 0 addr bytes := by
  induction bytes generalizing σ addr with
  | nil =>
      simp only [insertByteRange, pointsToBytes]
      iintro Hσ
      imodintro
      iframe
  | cons b bs ih =>
      simp only [insertByteRange, pointsToBytes]
      have hhead : get? σ (⟨0, addr⟩ : MemoryKey) = none := by
        simpa using hfresh 0 (by simp)
      iintro Hσ
      imod genHeap_alloc (v := some b) hhead $$ Hσ with
        ⟨Hσ, Hhead, Hmeta⟩
      have hfresh' : ∀ i, i < bs.length →
          get? (insert σ ⟨0, addr⟩ (some b))
            (⟨0, (addr + 1) + UInt32.ofNat i⟩ : MemoryKey) = none := by
        intro i hi
        have hoff : (addr + 1) + UInt32.ofNat i =
            addr + UInt32.ofNat (i + 1) := by
          rw [byte_offset_succ]
        rw [hoff]
        have hne : (⟨0, addr + UInt32.ofNat (i + 1)⟩ : MemoryKey) ≠
            ⟨0, addr⟩ := by
          intro heq
          have ha := congrArg MemoryKey.addr heq
          have hnowrapN : addr.toNat + (bs.length + 1) < 4294967296 := by
            simpa only [List.length_cons, UInt32.size] using hnowrap
          have hadd : (addr + UInt32.ofNat (i + 1)).toNat =
              addr.toNat + (i + 1) := by
            apply UInt32.add_ofNat_toNat_noWrap addr (i + 1)
            · omega
            · omega
          have hn : (addr + UInt32.ofNat (i + 1)).toNat ≠ addr.toNat := by
            rw [hadd]
            omega
          exact hn (congrArg UInt32.toNat ha)
        rw [get?_insert_ne (Ne.symm hne)]
        exact hfresh (i + 1) (by simp; omega)
      have h1 : (addr + 1).toNat = addr.toNat + 1 := by
        have hnowrapN : addr.toNat + (bs.length + 1) < 4294967296 := by
          simpa only [List.length_cons, UInt32.size] using hnowrap
        apply UInt32.add_ofNat_toNat_noWrap addr 1 (by decide)
        omega
      have hnowrap' : (addr + 1).toNat + bs.length < UInt32.size := by
        rw [h1]
        simp only [List.length_cons] at hnowrap
        omega
      iclear Hmeta
      imod ih (insert σ ⟨0, addr⟩ (some b)) (addr + 1) hfresh' hnowrap' $$ Hσ with
        ⟨Hσ, Htail⟩
      imodintro
      isplitl [Hσ]
      · iexact Hσ
      · iframe

private theorem insertByteRange_agrees
    (σ : WasmHeapMap (Option UInt8)) (resolve : Nat → Option Mem)
    (mem : Mem) (addr : UInt32) (bytes : List UInt8)
    (hresolve : resolve 0 = some mem)
    (hagree : heapAgreesWithMem σ resolve)
    (hbytes : ∀ (i : Nat) (hi : i < bytes.length),
      mem.read8 (addr + UInt32.ofNat i) = bytes[i]'hi) :
    heapAgreesWithMem (insertByteRange σ addr bytes) resolve := by
  induction bytes generalizing σ addr with
  | nil => simpa [insertByteRange] using hagree
  | cons b bs ih =>
      simp only [insertByteRange]
      apply ih (insert σ ⟨0, addr⟩ (some b)) (addr + 1)
      · intro key v hget
        by_cases heq : key = ⟨0, addr⟩
        · subst key
          simp only [get?_insert_eq rfl, Option.some.injEq] at hget
          subst v
          refine ⟨mem, hresolve, ?_⟩
          have hb := hbytes 0 (by simp)
          change mem.read8 (addr + 0) = b at hb
          simpa using hb
        · rw [get?_insert_ne (Ne.symm heq)] at hget
          exact hagree key v hget
      · intro i hi
        have hs : (addr + 1) + UInt32.ofNat i =
            addr + UInt32.ofNat (i + 1) := by
          rw [byte_offset_succ]
        rw [hs]
        have hb := hbytes (i + 1) (by simp; omega)
        change mem.read8 (addr + UInt32.ofNat (i + 1)) = bs[i]'hi at hb
        exact hb

private theorem insertByteRange_inBounds
    (σ : WasmHeapMap (Option UInt8)) (resolve : Nat → Option Mem)
    (mem : Mem) (addr : UInt32) (bytes : List UInt8)
    (hresolve : resolve 0 = some mem)
    (hinBounds : heapAddressesInBounds σ resolve)
    (hbound : addr.toNat + bytes.length ≤ mem.pages * 65536)
    (hnowrap : addr.toNat + bytes.length < UInt32.size) :
    heapAddressesInBounds (insertByteRange σ addr bytes) resolve := by
  induction bytes generalizing σ addr with
  | nil => simpa [insertByteRange] using hinBounds
  | cons b bs ih =>
      simp only [insertByteRange, List.length_cons] at hbound hnowrap ⊢
      have haddr : addr.toNat < mem.pages * 65536 := by omega
      have h1 : (addr + 1).toNat = addr.toNat + 1 := by
        have hnowrapN : addr.toNat + (bs.length + 1) < 4294967296 := by
          simpa only [UInt32.size] using hnowrap
        apply UInt32.add_ofNat_toNat_noWrap addr 1 (by decide)
        omega
      apply ih (insert σ ⟨0, addr⟩ (some b)) (addr + 1)
      · intro key hget
        by_cases heq : key = ⟨0, addr⟩
        · subst key
          exact ⟨mem, hresolve, haddr⟩
        · rw [get?_insert_ne (Ne.symm heq)] at hget
          exact hinBounds key hget
      · rw [h1]
        omega
      · rw [h1]
        omega

/-- Successful growth exposes ownership of every newly addressable byte while
preserving all previously owned resources. -/
theorem stateInterp_memoryGrow_fresh_bytes
    [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (delta : UInt32) (cap : Nat) (memory : Mem) (previousPages : Nat)
    (hgrow : store.wasm.mem.grow delta cap = some (memory, previousPages))
    (hpages : memory.pages < 65536) :
    let addr := UInt32.ofNat (previousPages * 65536)
    let len := delta.toNat * 65536
    stateInterp (GF := WasmHeapGF α) store steps observations threads ==∗
      stateInterp (GF := WasmHeapGF α)
          { store with wasm := { store.wasm with mem := memory } }
          steps observations threads ∗
      pointsToBytes 0 addr
        ((List.range len).map fun i =>
          memory.read8 (addr + UInt32.ofNat i)) := by
  dsimp only
  iintro Hstate
  icases (stateInterp_eq store steps observations threads).mp $$ Hstate with
    ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ,
      %runtimeModuleσ, %hostEnvσ, Hheap, Hglobals, Hsegments, Htables,
      Helements, HruntimeModuleAuth, HruntimeModuleBigSep,
      HruntimeInstances, HinstanceAuth, HhostEnvAuth, HhostAuth,
      %Hfacts, Hexc⟩
  have hgrowFacts : previousPages = store.wasm.mem.pages ∧
      memory.pages = store.wasm.mem.pages + delta.toNat := by
    simp only [Mem.grow] at hgrow
    split at hgrow
    · exact ⟨(Prod.mk.inj (Option.some.inj hgrow)).2.symm,
        congrArg Mem.pages (Prod.mk.inj (Option.some.inj hgrow)).1.symm⟩
    · contradiction
  let addr := UInt32.ofNat (previousPages * 65536)
  let len := delta.toNat * 65536
  let bytes := (List.range len).map fun i =>
    memory.read8 (addr + UInt32.ofNat i)
  have hlen : bytes.length = len := by simp [bytes]
  have hbase : addr.toNat = previousPages * 65536 := by
    apply UInt32.toNat_ofNat_of_lt'
    rw [hgrowFacts.1, show UInt32.size = 4294967296 by decide]
    have hold : store.wasm.mem.pages ≤ memory.pages := by omega
    omega
  have hnowrap : addr.toNat + bytes.length < UInt32.size := by
    rw [hlen, hbase, show UInt32.size = 4294967296 by decide]
    omega
  have hnowrapN : addr.toNat + bytes.length < 4294967296 := by
    simpa only [UInt32.size] using hnowrap
  have hnew : store.wasm.mem.pages * 65536 ≤ addr.toNat := by
    rw [hbase, hgrowFacts.1]
  have hfresh : ∀ i, i < bytes.length →
      get? σ (⟨0, addr + UInt32.ofNat i⟩ : MemoryKey) = none := by
    intro i hi
    by_contra hne
    obtain ⟨mem, hmem, hib⟩ := Hfacts.2.1 _ hne
    have hmem0 : mem = store.wasm.mem := by
      have hz : storeResolve store 0 = some store.wasm.mem := by
        simp [storeResolve]
      exact Option.some.inj (hmem.symm.trans hz)
    subst mem
    have hadd : (addr + UInt32.ofNat i).toNat = addr.toNat + i := by
      apply UInt32.add_ofNat_toNat_noWrap addr i
      · simp only [hlen] at hi
        omega
      · simp only [hlen] at hi
        exact Nat.le_of_lt (by omega)
    rw [hadd] at hib
    omega
  imod insertByteRange_alloc σ addr bytes hfresh hnowrap $$ Hheap with
    ⟨Hheap, Hbytes⟩
  let grownStore : MachineStore α :=
    { store with wasm := { store.wasm with mem := memory } }
  have hresolveEq :
      (fun id => if id = 0 then some memory else storeResolve store id) =
        storeResolve grownStore := by
    funext id
    simp only [grownStore, storeResolve]
    by_cases h : id = 0 <;> simp [h]
  have hagreeGrown : heapAgreesWithMem σ (storeResolve grownStore) := by
    have h := grow_sound σ (storeResolve store) 0 store.wasm.mem memory
      delta cap previousPages hgrow (by simp [storeResolve]) Hfacts.1
    rw [hresolveEq] at h
    exact h
  have hinBoundsGrown : heapAddressesInBounds σ (storeResolve grownStore) := by
    have h := grow_inBounds σ (storeResolve store) 0 store.wasm.mem memory
      delta cap previousPages hgrow (by simp [storeResolve]) Hfacts.2.1
    rw [hresolveEq] at h
    exact h
  have hagree : heapAgreesWithMem (insertByteRange σ addr bytes)
      (storeResolve grownStore) := by
    apply insertByteRange_agrees σ (storeResolve grownStore) memory addr bytes
    · change storeResolve grownStore 0 = some memory
      simp [grownStore, storeResolve]
    · exact hagreeGrown
    · intro i hi
      simp only [bytes, List.length_map, List.length_range] at hi
      simp [bytes]
  have hinBounds : heapAddressesInBounds (insertByteRange σ addr bytes)
      (storeResolve grownStore) := by
    apply insertByteRange_inBounds σ (storeResolve grownStore) memory addr bytes
    · change storeResolve grownStore 0 = some memory
      simp [grownStore, storeResolve]
    · exact hinBoundsGrown
    · rw [hlen, hbase, hgrowFacts.1, hgrowFacts.2]
      simp [len, Nat.add_mul]
    · exact hnowrap
  imodintro
  isplitl [Hheap Hglobals Hsegments Htables Helements HruntimeModuleAuth
      HruntimeModuleBigSep HruntimeInstances HinstanceAuth HhostEnvAuth
      HhostAuth Hexc]
  · iapply (stateInterp_eq grownStore steps observations threads).mpr
    iexists (insertByteRange σ addr bytes), globalσ, dataSegmentσ, tableσ,
      elementSegmentσ, runtimeModuleσ, hostEnvσ
    iframe
    ipureintro
    exact ⟨hagree, hinBounds, Hfacts.2.2⟩
  · dsimp only [bytes, addr, len]
    iassumption

/-- Total `memory.grow` rule which makes the newly addressable byte range
available to the successful continuation.  The page bound is explicit because
the byte-addressed ownership assertion cannot represent the endpoint just past
the final 32-bit address. -/
theorem twp_memoryGrow_fresh
    [WasmSmallStepGS hlc α]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF α)}
    {params localValues values : List Value}
    {delta : UInt32}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (runtimeModule : Module) (instanceId : ModuleInstanceId)
    (R : IProp (WasmHeapGF α))
    (hpages : ∀ (store : MachineStore α) (memory : Mem)
        (previousPages : Nat),
      store.runtime.currentModule = runtimeModule →
      store.wasm.mem.grow delta
          (store.wasm.memoryCap store.runtime.currentModule 0) =
        some (memory, previousPages) →
      memory.pages < 65536)
    (Hfail : runtimeModuleOwn instanceId runtimeModule ∗ R -∗
      WP (.running ⟨⟨params, localValues,
          .i32 (0xffffffff : UInt32) :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }])
    (Hsuccess : ∀ (store : MachineStore α) (memory : Mem)
        (previousPages : Nat)
        (hgrow : store.wasm.mem.grow delta
          (store.wasm.memoryCap store.runtime.currentModule 0) =
            some (memory, previousPages)),
      runtimeModuleOwn instanceId runtimeModule ∗ R ∗
          pointsToBytes 0 (UInt32.ofNat (previousPages * 65536))
            ((List.range (delta.toNat * 65536)).map fun i =>
              memory.read8
                (UInt32.ofNat (previousPages * 65536) + UInt32.ofNat i)) -∗
      WP (.running ⟨⟨params, localValues,
          .i32 previousPages.toUInt32 :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }]) :
    runtimeModuleOwn instanceId runtimeModule ∗ R -∗
    WP (.running ⟨⟨params, localValues, .i32 delta :: values⟩,
        .memoryGrow :: code, arity, remainder, controls, calls⟩ : Expr α) @
      s; E [{ Φ }] := by
  iintro ⟨Hruntime, HR⟩
  iapply twp_lift_step_no_fork rfl
  iintro %store %ns %obs %nt Hσ
  ihave %Hmodule : ⌜store.runtime.currentModule = runtimeModule⌝ $$
      [Hσ Hruntime]
  · imod stateInterp_runtimeModule_agree store ns obs nt
      instanceId runtimeModule $$ [$Hσ $Hruntime] with %Hmodule
    ipureintro
    exact Hmodule
  cases hg : store.wasm.mem.grow delta
      (store.wasm.memoryCap store.runtime.currentModule 0) with
  | none =>
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hclose
    isplitr
    · ipureintro
      cases s <;> simp only [Stuckness.MaybeReducibleNoObs]
      exact ⟨.running ⟨⟨params, localValues,
          .i32 (0xffffffff : UInt32) :: values⟩,
        code, arity, remainder, controls, calls⟩,
        store, [], ⟨rfl, .instruction .memoryGrow, rfl,
          Step.memoryGrowFailure hg⟩⟩
    iintro %κ %e₂ %store₂ %forks %Hstep
    rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
    change forks = [] at hforks
    subst forks
    subst κ
    obtain ⟨rfl, hconfig⟩ :=
      step_deterministic (Step.memoryGrowFailure hg) wasmStep
    have parts := Config.mk.inj hconfig
    have hexpr := parts.1
    have hstore := parts.2
    simp only at hexpr hstore
    subst e₂
    subst store₂
    imod Hclose
    imodintro
    isplit
    · ipureintro; rfl
    isplit
    · ipureintro; rfl
    isplitl [Hσ]
    · iexact Hσ
    · iapply Hfail
      iframe
  | some grown =>
    obtain ⟨memory, previousPages⟩ := grown
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hclose
    isplitr
    · ipureintro
      cases s <;> simp only [Stuckness.MaybeReducibleNoObs]
      exact ⟨.running ⟨⟨params, localValues,
          .i32 previousPages.toUInt32 :: values⟩,
        code, arity, remainder, controls, calls⟩,
        { store with wasm := { store.wasm with mem := memory } }, [],
        ⟨rfl, .instruction .memoryGrow, rfl, by
          simpa only [Wasm.SmallStep.setMemory_eq] using
            Step.memoryGrowSuccess hg⟩⟩
    iintro %κ %e₂ %store₂ %forks %Hstep
    rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
    change forks = [] at hforks
    subst forks
    subst κ
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
    imod stateInterp_memoryGrow_fresh_bytes store ns obs nt delta
      (store.wasm.memoryCap store.runtime.currentModule 0)
      memory previousPages hg (hpages store memory previousPages Hmodule hg) $$
      Hσ with ⟨Hσ, Hfresh⟩
    imod Hclose
    imodintro
    isplit
    · ipureintro; rfl
    isplit
    · ipureintro; rfl
    isplitl [Hσ]
    · iexact Hσ
    · iapply Hsuccess store memory previousPages hg
      iframe

end Submission.HexDecodeStdio
