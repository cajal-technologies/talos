import CodeLib
import HexEncodeStdio.TotalAdequacy
import HexEncodeStdio.Grow
import HexEncodeStdio.Helpers

namespace Project.HexEncodeStdio.FullMemory

open Wasm
open Iris Iris.BI Iris.ProgramLogic Language.Notation Iris.Std FromMathlib
open Wasm.SepLogic Wasm.SmallStep

variable {α : Type}

private theorem addr_succ_ne (addr : UInt32) (i : Nat)
    (hnowrap : addr.toNat + i + 1 < UInt32.size) :
    addr + UInt32.ofNat (i + 1) ≠ addr := by
  intro h
  have ht := congrArg UInt32.toNat h
  have hi : i + 1 < UInt32.size := by omega
  rw [UInt32.add_ofNat_toNat_noWrap addr (i + 1) hi (by omega)] at ht
  omega

def heap (store : MachineStore α) : WasmHeapMap (Option UInt8) :=
  Project.HexEncodeStdio.Grow.insertBytes ∅ 0
    (Project.HexEncodeStdio.Grow.bytesAt store.wasm.mem 0 (store.wasm.mem.pages * 65536))

theorem insertBytes_pointsTo {hlc : HasLC} {α : Type}
    [WasmSmallStepGS hlc α]
    (σ : WasmHeapMap (Option UInt8)) (addr : UInt32) (bytes : List UInt8)
    (hnowrap : addr.toNat + bytes.length < UInt32.size)
    (hfresh : ∀ i, i < bytes.length →
      get? σ (⟨0, addr + UInt32.ofNat i⟩ : MemoryKey) = none) :
    ([∗map] address ↦ value ∈ Project.HexEncodeStdio.Grow.insertBytes σ addr bytes,
      pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        address (DFrac.own 1) value) ⊢
      pointsToBytes 0 addr bytes ∗
      ([∗map] address ↦ value ∈ σ,
        pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
          address (DFrac.own 1) value) := by
  induction bytes generalizing σ addr with
  | nil =>
      simp only [Project.HexEncodeStdio.Grow.insertBytes, pointsToBytes]
      iintro Hheap
      isplitr
      · itrivial
      · iexact Hheap
  | cons b bs ih =>
      simp only [List.length_cons] at hnowrap
      have haddr : get? σ (⟨0, addr⟩ : MemoryKey) = none := by
        simpa using hfresh 0 (by simp)
      have hsucc : (addr + 1).toNat = addr.toNat + 1 := by
        apply UInt32.add_ofNat_toNat_noWrap addr 1 (by decide)
        norm_num [UInt32.size] at hnowrap ⊢
        omega
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
        · exact fun heq => addr_succ_ne addr i (by omega)
            (congrArg MemoryKey.addr heq).symm
      simp only [Project.HexEncodeStdio.Grow.insertBytes, pointsToBytes]
      iintro Hheap
      ihave Hsplit := ih
        (insert σ (⟨0, addr⟩ : MemoryKey) (some b)) (addr + 1)
        hnowrap' hfresh' $$ Hheap
      icases Hsplit with ⟨Hbs, Hstored⟩
      ihave Hhead := (BI.BigSepM.bigSepM_insert haddr).mp $$ Hstored
      icases Hhead with ⟨Hhead, Hrest⟩
      iframe

theorem heap_agrees (store : MachineStore α)
    (hpages : store.wasm.mem.pages < 65536) :
    heapAgreesWithMem (heap store) (storeResolve store) := by
  unfold heap
  apply Project.HexEncodeStdio.Grow.insertBytes_agrees
  · simp [storeResolve]
  · norm_num [UInt32.size]
    omega
  · exact heapAgreesWithMem_empty _

theorem heap_inBounds (store : MachineStore α)
    (hpages : store.wasm.mem.pages < 65536) :
    heapAddressesInBounds (heap store) (storeResolve store) := by
  unfold heap
  apply Project.HexEncodeStdio.Grow.insertBytes_inBounds
  · simp [storeResolve]
  · norm_num [UInt32.size]
    omega
  · simp
  · exact heapAddressesInBounds_empty _

theorem heap_pointsTo {hlc : HasLC} {α : Type}
    [WasmSmallStepGS hlc α]
    (store : MachineStore α) (hpages : store.wasm.mem.pages < 65536) :
    ([∗map] address ↦ value ∈ heap store,
      pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        address (DFrac.own 1) value) ⊢
      pointsToBytes 0 0
        (Project.HexEncodeStdio.Grow.bytesAt store.wasm.mem 0
          (store.wasm.mem.pages * 65536)) := by
  unfold heap
  iintro Hheap
  ihave Hsplit := insertBytes_pointsTo (α := α) ∅ 0
    (Project.HexEncodeStdio.Grow.bytesAt store.wasm.mem 0
      (store.wasm.mem.pages * 65536))
    (by simp [UInt32.size]; omega)
    (by intro i hi; simp [get?_empty]) $$ Hheap
  icases Hsplit with ⟨Hbytes, _⟩
  iexact Hbytes

theorem bytesAt_append (mem : Mem) (addr : UInt32) (m n : Nat)
    (hnowrap : addr.toNat + m + n < UInt32.size) :
    Project.HexEncodeStdio.Grow.bytesAt mem addr (m + n) =
      Project.HexEncodeStdio.Grow.bytesAt mem addr m ++
        Project.HexEncodeStdio.Grow.bytesAt mem (addr + UInt32.ofNat m) n := by
  induction m generalizing addr with
  | zero => simp [Project.HexEncodeStdio.Grow.bytesAt]
  | succ m ih =>
      simp only [Nat.succ_add, Project.HexEncodeStdio.Grow.bytesAt, List.cons.injEq]
      apply congrArg (mem.read8 addr :: ·)
      rw [ih (addr + 1)]
      · congr 2
        rw [UInt32.ofNat_add, show UInt32.ofNat 1 = 1 by rfl]
        simp only [UInt32.add_assoc]
        rw [UInt32.add_comm 1 (UInt32.ofNat m)]
      · have hsucc : (addr + 1).toNat = addr.toNat + 1 := by
          apply UInt32.add_ofNat_toNat_noWrap addr 1 (by decide)
          norm_num [UInt32.size] at hnowrap ⊢
          omega
        rw [hsucc]
        omega

theorem full_bytes_decompose (mem : Mem) (addr : UInt32) (n total : Nat)
    (haddr : addr.toNat + n ≤ total)
    (htotal : total < UInt32.size) :
    Project.HexEncodeStdio.Grow.bytesAt mem 0 total =
      Project.HexEncodeStdio.Grow.bytesAt mem 0 addr.toNat ++
        (Project.HexEncodeStdio.Grow.bytesAt mem addr n ++
         Project.HexEncodeStdio.Grow.bytesAt mem (addr + UInt32.ofNat n)
           (total - (addr.toNat + n))) := by
  have haddrSize : addr.toNat < UInt32.size := UInt32.toNat_lt_size addr
  have hzeroAddr : (0 : UInt32) + UInt32.ofNat addr.toNat = addr := by simp
  have hsum : addr.toNat + (total - addr.toNat) = total := by omega
  rw [← hsum, bytesAt_append mem 0 addr.toNat (total - addr.toNat)]
  · rw [hzeroAddr]
    have hsum' : n + (total - (addr.toNat + n)) = total - addr.toNat := by
      omega
    rw [← hsum', bytesAt_append mem addr n
      (total - (addr.toNat + n))]
    · rw [show addr.toNat +
          (n + (total - (addr.toNat + n))) - (addr.toNat + n) =
          total - (addr.toNat + n) by omega]
    · omega
  · simp
    omega

theorem heap_range {hlc : HasLC} {α : Type}
    [WasmSmallStepGS hlc α]
    (store : MachineStore α) (addr : UInt32) (n : Nat)
    (hpages : store.wasm.mem.pages < 65536)
    (hbound : addr.toNat + n ≤ store.wasm.mem.pages * 65536) :
    ([∗map] address ↦ value ∈ heap store,
      pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        address (DFrac.own 1) value) ⊢
      pointsToBytes 0 addr (Project.HexEncodeStdio.Grow.bytesAt store.wasm.mem addr n) := by
  iintro Hheap
  ihave Hfull : pointsToBytes 0 0
      (Project.HexEncodeStdio.Grow.bytesAt store.wasm.mem 0
        (store.wasm.mem.pages * 65536)) $$ [Hheap]
  · iapply heap_pointsTo store hpages
    iexact Hheap
  have htotal : store.wasm.mem.pages * 65536 < UInt32.size := by
    norm_num [UInt32.size]
    omega
  ihave Hdecomp : pointsToBytes 0 0
      (Project.HexEncodeStdio.Grow.bytesAt store.wasm.mem 0 addr.toNat ++
        (Project.HexEncodeStdio.Grow.bytesAt store.wasm.mem addr n ++
         Project.HexEncodeStdio.Grow.bytesAt store.wasm.mem (addr + UInt32.ofNat n)
           (store.wasm.mem.pages * 65536 - (addr.toNat + n)))) $$ [Hfull]
  · rw [← full_bytes_decompose store.wasm.mem addr n
      (store.wasm.mem.pages * 65536) hbound htotal]
    iexact Hfull
  ihave Hsplit := (pointsToBytes_append 0 0
    (Project.HexEncodeStdio.Grow.bytesAt store.wasm.mem 0 addr.toNat)
    (Project.HexEncodeStdio.Grow.bytesAt store.wasm.mem addr n ++
      Project.HexEncodeStdio.Grow.bytesAt store.wasm.mem (addr + UInt32.ofNat n)
        (store.wasm.mem.pages * 65536 - (addr.toNat + n)))).mp $$ Hdecomp
  icases Hsplit with ⟨_Hprefix, Hrest⟩
  ihave Hrest' : pointsToBytes 0 addr
      (Project.HexEncodeStdio.Grow.bytesAt store.wasm.mem addr n ++
        Project.HexEncodeStdio.Grow.bytesAt store.wasm.mem (addr + UInt32.ofNat n)
          (store.wasm.mem.pages * 65536 - (addr.toNat + n))) $$ [Hrest]
  · simp only [Project.HexEncodeStdio.Grow.bytesAt_length, UInt32.ofNat_toNat,
      UInt32.zero_add]
    iexact Hrest
  ihave Hsplit := (pointsToBytes_append 0 addr
    (Project.HexEncodeStdio.Grow.bytesAt store.wasm.mem addr n)
    (Project.HexEncodeStdio.Grow.bytesAt store.wasm.mem (addr + UInt32.ofNat n)
      (store.wasm.mem.pages * 65536 - (addr.toNat + n)))).mp $$ Hrest'
  icases Hsplit with ⟨Hrange, _Hsuffix⟩
  iexact Hrange

theorem bytesAt_four (mem : Mem) (addr : UInt32)
    (hfit : addr.toNat + 4 < UInt32.size) :
    Project.HexEncodeStdio.Grow.bytesAt mem addr 4 =
      [u32Byte (mem.read32 addr) 0, u32Byte (mem.read32 addr) 1,
       u32Byte (mem.read32 addr) 2, u32Byte (mem.read32 addr) 3] := by
  obtain ⟨_, h1, h2, h3⟩ := Project.HexEncodeStdio.Helpers.wordAccessFacts addr 0 hfit
  have h1' : (addr + 1).toNat = addr.toNat + 1 := by simpa using h1
  have h2' : (addr + 2).toNat = addr.toNat + 2 := by simpa using h2
  have h3' : (addr + 3).toNat = addr.toNat + 3 := by simpa using h3
  simp only [Project.HexEncodeStdio.Grow.bytesAt]
  rw [show addr + 1 + 1 = addr + 2 by bv_decide,
    show addr + 2 + 1 = addr + 3 by bv_decide]
  simp only [Mem.read32, Mem.read8, u32Byte,
    h1', h2', h3']
  congr <;> bv_decide

theorem bytesAt_eq_readBytes (mem : Mem) (addr : UInt32) (n : Nat)
    (hnowrap : addr.toNat + n < UInt32.size) :
    Project.HexEncodeStdio.Grow.bytesAt mem addr n = mem.readBytes addr.toNat n := by
  induction n generalizing addr with
  | zero => simp [Project.HexEncodeStdio.Grow.bytesAt, Mem.readBytes]
  | succ n ih =>
      have hsucc : (addr + 1).toNat = addr.toNat + 1 := by
        apply UInt32.add_ofNat_toNat_noWrap addr 1 (by decide)
        norm_num [UInt32.size] at hnowrap ⊢
        omega
      rw [Project.HexEncodeStdio.Grow.bytesAt]
      rw [ih (addr + 1) (by rw [hsucc]; omega)]
      apply List.ext_getElem
      · simp [Mem.readBytes]
      · intro i hleft hright
        cases i with
        | zero => simp [Mem.readBytes, Mem.read8]
        | succ i =>
            simp only [List.getElem_cons_succ, Mem.readBytes,
              List.getElem_map, List.getElem_range]
            rw [hsucc]
            congr 1
            omega

theorem heap_u32 {hlc : HasLC} {α : Type}
    [WasmSmallStepGS hlc α]
    (store : MachineStore α) (addr : UInt32)
    (hpages : store.wasm.mem.pages < 65536)
    (hbound : addr.toNat + 4 ≤ store.wasm.mem.pages * 65536) :
    ([∗map] address ↦ value ∈ heap store,
      pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        address (DFrac.own 1) value) ⊢
      pointsTo_u32 0 addr (store.wasm.mem.read32 addr) := by
  iintro Hheap
  ihave Hbytes := heap_range store addr 4 hpages hbound $$ Hheap
  iapply (pointsTo_u32_as_bytes 0 addr (store.wasm.mem.read32 addr)).mpr
  rw [← bytesAt_four store.wasm.mem addr (by
    norm_num [UInt32.size]
    omega)]
  iexact Hbytes

theorem terminates
    [WasmSmallStepGpreS α]
    (config : Config α)
    (globalσ : WasmGlobalMap Value)
    (post : List Value → MachineStore α → Prop)
    (hpages : config.store.wasm.mem.pages < 65536)
    (hglobals : globalHeapAgrees globalσ config.store.wasm.globals)
    (hwf : config.store.runtime.entry.id < config.store.runtime.instances.size)
    (htwp : ∀ (hlc : HasLC) [WasmSmallStepGS hlc α],
      (pointsToBytes 0 0
          (Project.HexEncodeStdio.Grow.bytesAt config.store.wasm.mem 0
            (config.store.wasm.mem.pages * 65536)) ∗
        ([∗map] index ↦ value ∈ globalσ, globalPointsTo index value) ∗
        runtimeModuleOwn config.store.runtime.entry
          config.store.runtime.currentModule ∗
        hostEnvOwn config.store.runtime.entry.id
          config.store.runtime.currentHost ∗
        hostStateOwn config.store.wasm.host) ⊢
      WP config.expr @ Stuckness.NotStuck; ⊤
        [{ values,
          ∀ (store : MachineStore α) (_observations : List StepKind),
            stateInterp (GF := WasmHeapGF α) store 0 [] 0 -∗
            ⌜post values store⌝ }]) :
    TerminatesWith config post := by
  apply Wasm.SmallStep.heap_globals_runtime_host_store_terminates
    config (heap config.store) globalσ post
  · exact heap_agrees config.store hpages
  · exact heap_inBounds config.store hpages
  · exact hglobals
  · exact hwf
  · intro hlc _
    iintro ⟨Hheap, Hglobals, Hruntime, Henv, Hhost⟩
    ihave Hbytes := heap_pointsTo config.store hpages $$ Hheap
    iapply htwp hlc
    iframe

end Project.HexEncodeStdio.FullMemory
