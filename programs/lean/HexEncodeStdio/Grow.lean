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

end Project.HexEncodeStdio.Grow
