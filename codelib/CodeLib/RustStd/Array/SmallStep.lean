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

/-- The seven no-wrap facts about the two words of a fat pointer at `p`. Stated
over the address bound alone so both the `FatPtrAt` and the bare-`hroom` callers
share one proof. -/
theorem fatPtrArithmetic {p : UInt32} (hroom : p.toNat + 8 ≤ 4294967296) :
    (p + 1).toNat = p.toNat + 1 ∧
    (p + 2).toNat = p.toNat + 2 ∧
    (p + 3).toNat = p.toNat + 3 ∧
    (p + 4).toNat = p.toNat + 4 ∧
    ((p + 4) + 1).toNat = (p + 4).toNat + 1 ∧
    ((p + 4) + 2).toNat = (p + 4).toNat + 2 ∧
    ((p + 4) + 3).toNat = (p + 4).toNat + 3 := by
  obtain ⟨hp1, hp2, hp3, hp4, hp5, hp6, hp7⟩ := UInt32.addSteps8 p hroom
  refine ⟨hp1, hp2, hp3, hp4, ?_, ?_, ?_⟩
  · rw [UInt32.add_assoc, show (4 + 1 : UInt32) = 5 by decide, hp5, hp4]
  · rw [UInt32.add_assoc, show (4 + 2 : UInt32) = 6 by decide, hp6, hp4]
  · rw [UInt32.add_assoc, show (4 + 3 : UInt32) = 7 by decide, hp7, hp4]

/-- `fatPtrArithmetic` for a caller that already owns a `FatPtrAt`. -/
theorem fatPtrArithmetic_of {α} {st : Store α} {p dataPtr len : UInt32}
    (h : FatPtrAt st p dataPtr len) :
    (p + 1).toNat = p.toNat + 1 ∧
    (p + 2).toNat = p.toNat + 2 ∧
    (p + 3).toNat = p.toNat + 3 ∧
    (p + 4).toNat = p.toNat + 4 ∧
    ((p + 4) + 1).toNat = (p + 4).toNat + 1 ∧
    ((p + 4) + 2).toNat = (p + 4).toNat + 2 ∧
    ((p + 4) + 3).toNat = (p + 4).toNat + 3 :=
  fatPtrArithmetic h.noWrap

theorem fatPtrHeap_agrees {α} {st : Store α} {p dataPtr len : UInt32}
    (resolve : Nat → Option Mem)
    (h_resolve : resolve 0 = some st.mem)
    (h : FatPtrAt st p dataPtr len) :
    heapAgreesWithMem (fatPtrHeap p dataPtr len) resolve := by
  obtain ⟨hp1, hp2, hp3, _hp4, hp5, hp6, hp7⟩ := fatPtrArithmetic_of h
  unfold fatPtrHeap
  apply insert_physical_word32_sound (store32Heap ∅ 0 p dataPtr) resolve
    0 st.mem (p + 4) len h_resolve hp5 hp6 hp7
  · exact insert_physical_word32_sound (∅ : WasmHeapMap (Option UInt8)) resolve
      0 st.mem p dataPtr h_resolve hp1 hp2 hp3 (heapAgreesWithMem_empty _)
      (by simpa using h.data)
  · exact h.count

theorem fatPtrHeap_inBounds {α} {st : Store α} {p dataPtr len : UInt32}
    (resolve : Nat → Option Mem)
    (h_resolve : resolve 0 = some st.mem)
    (h : FatPtrAt st p dataPtr len) :
    heapAddressesInBounds (fatPtrHeap p dataPtr len) resolve := by
  obtain ⟨hp1, hp2, hp3, hp4, hp5, hp6, hp7⟩ := fatPtrArithmetic_of h
  have hbound := h.bound
  unfold fatPtrHeap
  apply insert_physical_word32_inBounds (store32Heap ∅ 0 p dataPtr) resolve
    0 st.mem (p + 4) len h_resolve hp5 hp6 hp7
  · exact insert_physical_word32_inBounds
      (∅ : WasmHeapMap (Option UInt8)) resolve 0 st.mem p dataPtr
      h_resolve hp1 hp2 hp3 (heapAddressesInBounds_empty _) (by omega)
      (by simpa using h.data)
  · omega
  · exact h.count

theorem fatPtrHeap_pointsTo
    [WasmHeapGS α] (p dataPtr len : UInt32)
    (hroom : p.toNat + 8 ≤ 4294967296) :
    ([∗map] address ↦ byte ∈ fatPtrHeap p dataPtr len,
      pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        address (DFrac.own 1) byte) ⊢
      pointsTo_u32 0 p dataPtr ∗ pointsTo_u32 0 (p + 4) len := by
  obtain ⟨hp1, hp2, hp3, hp4, h41, h42, h43⟩ := fatPtrArithmetic hroom
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
  ihave ⟨Hlen, Hfirst⟩ := store32Heap_pointsTo (store32Heap ∅ 0 p dataPtr)
    0 (p + 4) len
    (fresh ⟨0, p + 4⟩ (by simp only [hp4]; omega))
    (fresh ⟨0, (p + 4) + 1⟩ (by simp only [h41, hp4]; omega))
    (fresh ⟨0, (p + 4) + 2⟩ (by simp only [h42, hp4]; omega))
    (fresh ⟨0, (p + 4) + 3⟩ (by simp only [h43, hp4]; omega))
    h41 h42 h43 $$ Hbytes
  ihave ⟨Hdata, _Hempty⟩ := store32Heap_pointsTo
    (∅ : WasmHeapMap (Option UInt8)) 0 p dataPtr
    (get?_empty (⟨0, p⟩ : MemoryKey))
    (get?_empty (⟨0, p + 1⟩ : MemoryKey))
    (get?_empty (⟨0, p + 2⟩ : MemoryKey))
    (get?_empty (⟨0, p + 3⟩ : MemoryKey))
    hp1 hp2 hp3 $$ Hfirst
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
  obtain ⟨hp1, hp2, hp3, hp4, hp5, hp6, hp7⟩ := fatPtrArithmetic hroom
  iintro >Hdata >Hlen Hwp
  wasm_wp_next Wasm.SmallStep.wp_localGet hget
  ihave HdataLater : ▷ pointsTo_u32 0 (p + 0) dataPtr $$ [Hdata]
  · inext
    simp only [UInt32.add_zero]
    iexact Hdata
  wasm_wp_next_bind Wasm.SmallStep.wp_load32 (address := p) (offset := 0)
    dataPtr (by simp) (by simpa using hp1)
    (by simpa using hp2) (by simpa using hp3) with HdataLater => Hdata
  have hget' :
      (⟨params, localValues, .i32 dataPtr :: values⟩ : Locals).get index =
        some (.i32 p) := by simpa [Locals.get] using hget
  wasm_wp_next Wasm.SmallStep.wp_localGet hget'
  ihave HlenLater : ▷ pointsTo_u32 0 (p + 4) len $$ [Hlen]
  · ilater_exact Hlen
  wasm_wp_next_bind Wasm.SmallStep.wp_load32 (address := p) (offset := 4)
    len hp4 hp5 hp6 hp7 with HlenLater => Hlen
  iexact Hwp

end Wasm.RustStd.Array
