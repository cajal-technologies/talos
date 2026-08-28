import HexDecodeStdio.DecodeSpec
import HexDecodeStdio.TotalLifting

namespace Submission.HexDecodeStdio

open Wasm Project.HexStdio
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep

variable {hlc : outParam HasLC} {α : Type}

private def writeByteRange (σ : WasmHeapMap (Option UInt8)) (addr : UInt32) :
    List UInt8 → WasmHeapMap (Option UInt8)
  | [] => σ
  | b :: bs => writeByteRange (insert σ ⟨0, addr⟩ (some b)) (addr + 1) bs

private theorem writeByteRange_ghost
    [WasmSmallStepGS hlc α]
    (σ : WasmHeapMap (Option UInt8)) (addr : UInt32)
    (oldBytes newBytes : List UInt8)
    (hlen : oldBytes.length = newBytes.length) :
    genHeapInterp (GF := WasmHeapGF α) σ ∗ pointsToBytes 0 addr oldBytes ==∗
      genHeapInterp (writeByteRange σ addr newBytes) ∗
      pointsToBytes 0 addr newBytes := by
  induction oldBytes generalizing σ addr newBytes with
  | nil =>
      simp only [List.length_nil] at hlen
      have hnew : newBytes = [] := List.eq_nil_of_length_eq_zero hlen.symm
      subst newBytes
      simp only [writeByteRange, pointsToBytes]
      iintro ⟨Hσ, Hemp⟩
      imodintro
      iframe
  | cons old rest ih =>
      cases newBytes with
      | nil => simp at hlen
      | cons new newRest =>
        simp only [List.length_cons, Nat.succ.injEq] at hlen
        simp only [writeByteRange, pointsToBytes]
        iintro ⟨Hσ, Hold, Hrest⟩
        imod genHeap_update (v₂ := some new) $$ [$Hσ $Hold] with
          ⟨Hσ, Hnew⟩
        imod ih (insert σ ⟨0, addr⟩ (some new)) (addr + 1) newRest hlen $$
          [$Hσ $Hrest] with ⟨Hσ, Hrest⟩
        imodintro
        iframe

private theorem Mem.writeBytes_nil_eq (mem : Mem) (offset : Nat) :
    mem.writeBytes offset [] = mem := by
  cases mem with
  | mk pages bytes =>
    simp only [Mem.writeBytes, List.length_nil, Nat.add_zero]
    congr
    funext i
    rw [dif_neg (by omega)]

private theorem Mem.writeBytes_singleton_eq (mem : Mem) (addr : UInt32)
    (b : UInt8) :
    mem.writeBytes addr.toNat [b] = mem.write8 addr b := by
  cases mem with
  | mk pages bytes =>
    simp only [Mem.writeBytes, Mem.write8, List.length_cons, List.length_nil,
      Nat.add_zero]
    congr
    funext i
    by_cases h : i = addr.toNat
    · subst i
      simp
    · rw [dif_neg (by omega), if_neg h]

private theorem Mem.writeBytes_cons_eq (mem : Mem) (addr : UInt32)
    (b : UInt8) (bs : List UInt8)
    (hnext : (addr + 1).toNat = addr.toNat + 1) :
    mem.writeBytes addr.toNat (b :: bs) =
      (mem.write8 addr b).writeBytes (addr + 1).toNat bs := by
  rw [show b :: bs = [b] ++ bs by rfl, Mem.writeBytes_append,
    Mem.writeBytes_singleton_eq, hnext]
  rfl

private theorem writeByteRange_agrees
    (σ : WasmHeapMap (Option UInt8)) (resolve : Nat → Option Mem)
    (mem : Mem) (addr : UInt32) (bytes : List UInt8)
    (hresolve : resolve 0 = some mem)
    (hagree : heapAgreesWithMem σ resolve)
    (hnowrap : addr.toNat + bytes.length < UInt32.size) :
    heapAgreesWithMem (writeByteRange σ addr bytes)
      (fun id => if id = 0 then some (mem.writeBytes addr.toNat bytes)
        else resolve id) := by
  induction bytes generalizing σ addr mem resolve with
  | nil =>
      simp only [writeByteRange, List.length_nil, Mem.writeBytes_nil_eq]
      have hfun : (fun id => if id = 0 then some mem else resolve id) =
          resolve := by
        funext id
        by_cases h : id = 0 <;> simp [h, hresolve]
      rw [hfun]
      exact hagree
  | cons b bs ih =>
      have h1 : (addr + 1).toNat = addr.toNat + 1 := by
        have hnowrapN : addr.toNat + (bs.length + 1) < 4294967296 := by
          simpa only [List.length_cons, UInt32.size] using hnowrap
        apply UInt32.add_ofNat_toNat_noWrap addr 1 (by decide)
        omega
      have hnowrap' : (addr + 1).toNat + bs.length < UInt32.size := by
        rw [h1]
        simp only [List.length_cons] at hnowrap
        omega
      have hi := ih (insert σ ⟨0, addr⟩ (some b))
        (fun id => if id = 0 then some (mem.write8 addr b) else resolve id)
        (mem.write8 addr b) (addr + 1) (by simp)
        (store_sound σ resolve 0 mem addr b hresolve hagree) hnowrap'
      rw [← Mem.writeBytes_cons_eq mem addr b bs h1] at hi
      have hfun :
          (fun id => if id = 0 then
              some (mem.writeBytes addr.toNat (b :: bs))
            else (if id = 0 then some (mem.write8 addr b) else resolve id)) =
          (fun id => if id = 0 then
              some (mem.writeBytes addr.toNat (b :: bs)) else resolve id) := by
        funext id
        by_cases h : id = 0 <;> simp [h]
      rw [hfun] at hi
      simpa only [writeByteRange] using hi

private theorem writeByteRange_inBounds
    (σ : WasmHeapMap (Option UInt8)) (resolve : Nat → Option Mem)
    (mem : Mem) (addr : UInt32) (bytes : List UInt8)
    (hresolve : resolve 0 = some mem)
    (hinBounds : heapAddressesInBounds σ resolve)
    (hbound : addr.toNat + bytes.length ≤ mem.pages * 65536)
    (hnowrap : addr.toNat + bytes.length < UInt32.size) :
    heapAddressesInBounds (writeByteRange σ addr bytes)
      (fun id => if id = 0 then some (mem.writeBytes addr.toNat bytes)
        else resolve id) := by
  induction bytes generalizing σ addr mem resolve with
  | nil =>
      simp only [writeByteRange, List.length_nil, Mem.writeBytes_nil_eq]
      have hfun : (fun id => if id = 0 then some mem else resolve id) =
          resolve := by
        funext id
        by_cases h : id = 0 <;> simp [h, hresolve]
      rw [hfun]
      exact hinBounds
  | cons b bs ih =>
      have h1 : (addr + 1).toNat = addr.toNat + 1 := by
        have hnowrapN : addr.toNat + (bs.length + 1) < 4294967296 := by
          simpa only [List.length_cons, UInt32.size] using hnowrap
        apply UInt32.add_ofNat_toNat_noWrap addr 1 (by decide)
        omega
      have hnowrap' : (addr + 1).toNat + bs.length < UInt32.size := by
        rw [h1]
        simp only [List.length_cons] at hnowrap
        omega
      have hbound' : (addr + 1).toNat + bs.length ≤
          (mem.write8 addr b).pages * 65536 := by
        change (addr + 1).toNat + bs.length ≤ mem.pages * 65536
        rw [h1]
        simp only [List.length_cons] at hbound
        omega
      have hi := ih (insert σ ⟨0, addr⟩ (some b))
        (fun id => if id = 0 then some (mem.write8 addr b) else resolve id)
        (mem.write8 addr b) (addr + 1) (by simp)
        (store_inBounds σ resolve 0 mem addr b hresolve hinBounds
          (by simp only [List.length_cons] at hbound; omega))
        hbound' hnowrap'
      rw [← Mem.writeBytes_cons_eq mem addr b bs h1] at hi
      have hfun :
          (fun id => if id = 0 then
              some (mem.writeBytes addr.toNat (b :: bs))
            else (if id = 0 then some (mem.write8 addr b) else resolve id)) =
          (fun id => if id = 0 then
              some (mem.writeBytes addr.toNat (b :: bs)) else resolve id) := by
        funext id
        by_cases h : id = 0 <;> simp [h]
      rw [hfun] at hi
      simpa only [writeByteRange] using hi

theorem Mem.readBytes_eq_of_read8
    (mem : Mem) (addr : UInt32) (bytes : List UInt8)
    (hread : ∀ i (hi : i < bytes.length),
      mem.read8 (addr + UInt32.ofNat i) = bytes[i]'hi)
    (hnowrap : addr.toNat + bytes.length < UInt32.size) :
    mem.readBytes addr.toNat bytes.length = bytes := by
  apply List.ext_getElem
  · simp [Mem.readBytes]
  · intro i hleft hright
    simp only [Mem.readBytes, List.getElem_map, List.getElem_range]
    have hnowrapN : addr.toNat + bytes.length < 4294967296 := by
      simpa only [UInt32.size] using hnowrap
    have hadd : (addr + UInt32.ofNat i).toNat = addr.toNat + i := by
      apply UInt32.add_ofNat_toNat_noWrap addr i
      · omega
      · omega
    have hr := hread i hright
    simp only [Mem.read8, hadd] at hr
    exact hr

/-- A host-style byte write updates both the authoritative memory and the
caller-owned byte range. -/
theorem stateInterp_writeBytes
    [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (addr : UInt32) (oldBytes newBytes : List UInt8)
    (hlen : oldBytes.length = newBytes.length)
    (hbound : addr.toNat + newBytes.length ≤ store.wasm.mem.pages * 65536)
    (hnowrap : addr.toNat + newBytes.length < UInt32.size) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      pointsToBytes 0 addr oldBytes ==∗
      stateInterp (GF := WasmHeapGF α)
        { store with wasm :=
            { store.wasm with
              mem := store.wasm.mem.writeBytes addr.toNat newBytes } }
        steps observations threads ∗
      pointsToBytes 0 addr newBytes := by
  exact stateInterp_write_bytes store steps observations threads addr
    oldBytes newBytes hlen hbound hnowrap

end Submission.HexDecodeStdio
