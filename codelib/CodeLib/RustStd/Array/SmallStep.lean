import CodeLib.RustStd.Array.IsEmpty
import CodeLib.RustStd.Array.Len
import CodeLib.SepLogic.SmallStepAdequacy

/-! Authoritative small-step ownership for memory-resident Rust slices. -/

namespace Wasm.RustStd.Array

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic

set_option maxHeartbeats 10000000

def fatPtrHeap (p dataPtr len : UInt32) :
    WasmHeapMap (Option UInt8) :=
  store32Heap (store32Heap ∅ 0 p dataPtr) 0 (p + 4) len

theorem fatPtrArithmetic {α} {st : Store α} {p dataPtr len : UInt32}
    (h : FatPtrAt st p dataPtr len) :
    (p + 1).toNat = p.toNat + 1 ∧
    (p + 2).toNat = p.toNat + 2 ∧
    (p + 3).toNat = p.toNat + 3 ∧
    (p + 4).toNat = p.toNat + 4 ∧
    ((p + 4) + 1).toNat = (p + 4).toNat + 1 ∧
    ((p + 4) + 2).toNat = (p + 4).toNat + 2 ∧
    ((p + 4) + 3).toNat = (p + 4).toNat + 3 := by
  have hroom := h.noWrap
  have step (n : Nat) (hn : n < 4294967296)
      (hroom : p.toNat + n < 4294967296) :
      (p + UInt32.ofNat n).toNat = p.toNat + n :=
    UInt32.add_ofNat_toNat_noWrap p n hn hroom
  have hp1 := step 1 (by decide) (by omega)
  have hp2 := step 2 (by decide) (by omega)
  have hp3 := step 3 (by decide) (by omega)
  have hp4 := step 4 (by decide) (by omega)
  have hp5 := step 5 (by decide) (by omega)
  have hp6 := step 6 (by decide) (by omega)
  have hp7 := step 7 (by decide) (by omega)
  have hp4' : (p + 4).toNat = p.toNat + 4 := by simpa using hp4
  have hp5' : (p + 5).toNat = p.toNat + 5 := by simpa using hp5
  have hp6' : (p + 6).toNat = p.toNat + 6 := by simpa using hp6
  have hp7' : (p + 7).toNat = p.toNat + 7 := by simpa using hp7
  refine ⟨hp1, hp2, hp3, hp4, ?_, ?_, ?_⟩
  · rw [UInt32.add_assoc, show (4 + 1 : UInt32) = 5 by decide, hp5', hp4']
  · rw [UInt32.add_assoc, show (4 + 2 : UInt32) = 6 by decide, hp6', hp4']
  · rw [UInt32.add_assoc, show (4 + 3 : UInt32) = 7 by decide, hp7', hp4']

theorem fatPtrHeap_agrees {α} {st : Store α} {p dataPtr len : UInt32}
    (resolve : Nat → Option Mem)
    (h_resolve : resolve 0 = some st.mem)
    (h : FatPtrAt st p dataPtr len) :
    heapAgreesWithMem (fatPtrHeap p dataPtr len) resolve := by
  obtain ⟨hp1, hp2, hp3, _hp4, hp5, hp6, hp7⟩ := fatPtrArithmetic h
  have hempty : heapAgreesWithMem (∅ : WasmHeapMap (Option UInt8)) resolve :=
    heapAgreesWithMem_empty _
  have hfirst := store32_sound (∅ : WasmHeapMap (Option UInt8)) resolve 0 st.mem
    p dataPtr h_resolve hp1 hp2 hp3 hempty
  have hwriteFirst : st.mem.write32 p dataPtr = st.mem :=
    Mem.write32_eq_self (by simpa using h.data) hp1 hp2 hp3
  rw [hwriteFirst] at hfirst
  have hresolveEq : (fun id => if id = 0 then some st.mem else resolve id) = resolve :=
    funext fun id => by by_cases h0 : id = 0 <;> simp [h0, h_resolve]
  have hfirst' : heapAgreesWithMem (store32Heap ∅ 0 p dataPtr) resolve := hresolveEq ▸ hfirst
  have hsecond := store32_sound (store32Heap ∅ 0 p dataPtr) resolve 0 st.mem
    (p + 4) len h_resolve hp5 hp6 hp7 hfirst'
  have hwriteSecond : st.mem.write32 (p + 4) len = st.mem :=
    Mem.write32_eq_self h.count hp5 hp6 hp7
  rw [hwriteSecond] at hsecond
  have hsecond' : heapAgreesWithMem (fatPtrHeap p dataPtr len) resolve := hresolveEq ▸ hsecond
  simpa [fatPtrHeap] using hsecond'

theorem fatPtrHeap_inBounds {α} {st : Store α} {p dataPtr len : UInt32}
    (resolve : Nat → Option Mem)
    (h_resolve : resolve 0 = some st.mem)
    (h : FatPtrAt st p dataPtr len) :
    heapAddressesInBounds (fatPtrHeap p dataPtr len) resolve := by
  obtain ⟨hp1, hp2, hp3, _hp4, hp5, hp6, hp7⟩ := fatPtrArithmetic h
  have hbound := h.bound
  have hempty : heapAddressesInBounds (∅ : WasmHeapMap (Option UInt8)) resolve :=
    heapAddressesInBounds_empty _
  have hfirst := store32_inBounds (∅ : WasmHeapMap (Option UInt8)) resolve 0 st.mem
    p dataPtr h_resolve hp1 hp2 hp3 hempty (by omega)
  have hwriteFirst : st.mem.write32 p dataPtr = st.mem :=
    Mem.write32_eq_self (by simpa using h.data) hp1 hp2 hp3
  rw [hwriteFirst] at hfirst
  have hresolveEq : (fun id => if id = 0 then some st.mem else resolve id) = resolve :=
    funext fun id => by by_cases h0 : id = 0 <;> simp [h0, h_resolve]
  have hfirst' : heapAddressesInBounds (store32Heap ∅ 0 p dataPtr) resolve := hresolveEq ▸ hfirst
  have hsecond := store32_inBounds (store32Heap ∅ 0 p dataPtr) resolve 0 st.mem
    (p + 4) len h_resolve hp5 hp6 hp7 hfirst' (by omega)
  have hwriteSecond : st.mem.write32 (p + 4) len = st.mem :=
    Mem.write32_eq_self h.count hp5 hp6 hp7
  rw [hwriteSecond] at hsecond
  have hsecond' : heapAddressesInBounds (fatPtrHeap p dataPtr len) resolve := hresolveEq ▸ hsecond
  simpa [fatPtrHeap] using hsecond'

theorem fatPtrHeap_pointsTo
    [WasmHeapGS α] (p dataPtr len : UInt32)
    (hroom : p.toNat + 8 ≤ 4294967296) :
    ([∗map] address ↦ byte ∈ fatPtrHeap p dataPtr len,
      pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        address (DFrac.own 1) byte) ⊢
      pointsTo_u32 0 p dataPtr ∗ pointsTo_u32 0 (p + 4) len := by
  have hp (n : Nat) (hn : n < 4294967296)
      (hr : p.toNat + n < 4294967296) :
      (p + UInt32.ofNat n).toNat = p.toNat + n :=
    UInt32.add_ofNat_toNat_noWrap p n hn hr
  have hp1 := hp 1 (by decide) (by omega)
  have hp2 := hp 2 (by decide) (by omega)
  have hp3 := hp 3 (by decide) (by omega)
  have hp4 := hp 4 (by decide) (by omega)
  have hp5 := hp 5 (by decide) (by omega)
  have hp6 := hp 6 (by decide) (by omega)
  have hp7 := hp 7 (by decide) (by omega)
  have hp1' : (p + 1).toNat = p.toNat + 1 := by simpa using hp1
  have hp2' : (p + 2).toNat = p.toNat + 2 := by simpa using hp2
  have hp3' : (p + 3).toNat = p.toNat + 3 := by simpa using hp3
  have hp4' : (p + 4).toNat = p.toNat + 4 := by simpa using hp4
  have hp5' : (p + 5).toNat = p.toNat + 5 := by simpa using hp5
  have hp6' : (p + 6).toNat = p.toNat + 6 := by simpa using hp6
  have hp7' : (p + 7).toNat = p.toNat + 7 := by simpa using hp7
  have h41 : ((p + 4) + 1).toNat = (p + 4).toNat + 1 := by
    rw [UInt32.add_assoc, show (4 + 1 : UInt32) = 5 by decide, hp5', hp4']
  have h42 : ((p + 4) + 2).toNat = (p + 4).toNat + 2 := by
    rw [UInt32.add_assoc, show (4 + 2 : UInt32) = 6 by decide, hp6', hp4']
  have h43 : ((p + 4) + 3).toNat = (p + 4).toNat + 3 := by
    rw [UInt32.add_assoc, show (4 + 3 : UInt32) = 7 by decide, hp7', hp4']
  have fresh (q : MemoryKey) (hq : p.toNat + 4 ≤ q.addr.toNat) :
      get? (store32Heap ∅ 0 p dataPtr) q = none := by
    unfold store32Heap
    have hne0 : q ≠ (⟨0, p⟩ : MemoryKey) := fun heq => by
      have h : q.addr = p := congrArg MemoryKey.addr heq
      have := congrArg UInt32.toNat h; omega
    have hne1 : q ≠ (⟨0, p + 1⟩ : MemoryKey) := fun heq => by
      have h : q.addr = p + 1 := congrArg MemoryKey.addr heq
      have := congrArg UInt32.toNat h; omega
    have hne2 : q ≠ (⟨0, p + 2⟩ : MemoryKey) := fun heq => by
      have h : q.addr = p + 2 := congrArg MemoryKey.addr heq
      have := congrArg UInt32.toNat h; omega
    have hne3 : q ≠ (⟨0, p + 3⟩ : MemoryKey) := fun heq => by
      have h : q.addr = p + 3 := congrArg MemoryKey.addr heq
      have := congrArg UInt32.toNat h; omega
    rw [get?_insert_ne (Ne.symm hne3), get?_insert_ne (Ne.symm hne2),
      get?_insert_ne (Ne.symm hne1), get?_insert_ne (Ne.symm hne0), get?_empty]
  simp only [fatPtrHeap]
  iintro Hbytes
  ihave Hsplit := store32Heap_pointsTo (store32Heap ∅ 0 p dataPtr)
    0 (p + 4) len
    (fresh ⟨0, p + 4⟩ (by simp only [hp4']; omega))
    (fresh ⟨0, (p + 4) + 1⟩ (by simp only [h41, hp4']; omega))
    (fresh ⟨0, (p + 4) + 2⟩ (by simp only [h42, hp4']; omega))
    (fresh ⟨0, (p + 4) + 3⟩ (by simp only [h43, hp4']; omega))
    h41 h42 h43 $$ Hbytes
  icases Hsplit with ⟨Hlen, Hfirst⟩
  ihave HdataSplit := store32Heap_pointsTo
    (∅ : WasmHeapMap (Option UInt8)) 0 p dataPtr
    (get?_empty (⟨0, p⟩ : MemoryKey))
    (get?_empty (⟨0, p + 1⟩ : MemoryKey))
    (get?_empty (⟨0, p + 2⟩ : MemoryKey))
    (get?_empty (⟨0, p + 3⟩ : MemoryKey))
    hp1 hp2 hp3 $$ Hfirst
  icases HdataSplit with ⟨Hdata, _Hempty⟩
  iframe

/-- Iris loader for the canonical `(dataPtr, len)` ABI pair. Both words are
returned unchanged so callers can frame the physical fat pointer across calls. -/
theorem wp_loadFatPtr
    {α : Type}
    [Wasm.SmallStep.WasmSmallStepGS hlc α]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF α)}
    {params localValues values : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List Wasm.SmallStep.ControlFrame}
    {calls : List Wasm.SmallStep.CallFrame}
    (index : Nat) (p dataPtr len : UInt32)
    (hget : (⟨params, localValues, values⟩ : Locals).get index = some (.i32 p))
    (hroom : p.toNat + 8 ≤ 4294967296) :
    ▷ pointsTo_u32 0 p dataPtr -∗
    ▷ pointsTo_u32 0 (p + 4) len -∗
    ▷ WP (Wasm.SmallStep.Expr.running
      ⟨⟨params, localValues, .i32 len :: .i32 dataPtr :: values⟩,
        code, arity, remainder, controls, calls⟩ :
        Wasm.SmallStep.Expr α) @ s; E {{ Φ }} -∗
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨params, localValues, values⟩,
        .localGet index :: .load32 0 :: .localGet index :: .load32 4 :: code,
        arity, remainder, controls, calls⟩ :
        Wasm.SmallStep.Expr α) @ s; E {{ Φ }} := by
  have hp (n : Nat) (hn : n < 4294967296)
      (hr : p.toNat + n < 4294967296) :
      (p + UInt32.ofNat n).toNat = p.toNat + n :=
    UInt32.add_ofNat_toNat_noWrap p n hn hr
  have hp1 : (p + 1).toNat = p.toNat + 1 := by
    simpa using hp 1 (by decide) (by omega)
  have hp2 : (p + 2).toNat = p.toNat + 2 := by
    simpa using hp 2 (by decide) (by omega)
  have hp3 : (p + 3).toNat = p.toNat + 3 := by
    simpa using hp 3 (by decide) (by omega)
  have hp4 : (p + 4).toNat = p.toNat + 4 := by
    simpa using hp 4 (by decide) (by omega)
  have hp5 : ((p + 4) + 1).toNat = (p + 4).toNat + 1 := by
    have h5 : (p + 5).toNat = p.toNat + 5 := by
      simpa using hp 5 (by decide) (by omega)
    rw [UInt32.add_assoc, show (4 + 1 : UInt32) = 5 by decide, h5, hp4]
  have hp6 : ((p + 4) + 2).toNat = (p + 4).toNat + 2 := by
    have h6 : (p + 6).toNat = p.toNat + 6 := by
      simpa using hp 6 (by decide) (by omega)
    rw [UInt32.add_assoc, show (4 + 2 : UInt32) = 6 by decide, h6, hp4]
  have hp7 : ((p + 4) + 3).toNat = (p + 4).toNat + 3 := by
    have h7 : (p + 7).toNat = p.toNat + 7 := by
      simpa using hp 7 (by decide) (by omega)
    rw [UInt32.add_assoc, show (4 + 3 : UInt32) = 7 by decide, h7, hp4]
  iintro >Hdata >Hlen Hwp
  iapply Wasm.SmallStep.wp_localGet hget
  inext
  ihave HdataLater : ▷ pointsTo_u32 0 (p + 0) dataPtr $$ [Hdata]
  · inext
    simp only [UInt32.add_zero]
    iexact Hdata
  iapply Wasm.SmallStep.wp_load32 (address := p) (offset := 0)
    dataPtr (by simp) (by simpa using hp1)
    (by simpa using hp2) (by simpa using hp3) $$ HdataLater
  inext
  iintro Hdata
  have hget' :
      (⟨params, localValues, .i32 dataPtr :: values⟩ : Locals).get index =
        some (.i32 p) := by
    simpa [Locals.get] using hget
  iapply Wasm.SmallStep.wp_localGet hget'
  inext
  ihave HlenLater : ▷ pointsTo_u32 0 (p + 4) len $$ [Hlen]
  · inext
    iexact Hlen
  iapply Wasm.SmallStep.wp_load32 (address := p) (offset := 4)
    len hp4 hp5 hp6 hp7 $$ HlenLater
  inext
  iintro Hlen
  iexact Hwp

end Wasm.RustStd.Array
