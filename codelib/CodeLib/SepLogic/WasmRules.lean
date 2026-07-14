import CodeLib.SepLogic.WasmHeap
import Interpreter.Wasm
import Std.Tactic.BVDecide

/-! # Bridge: Talos `Mem` ↔ iris-lean GenHeap

The state interpretation (`Adequacy`) maintains agreement between the abstract
GenHeap state `σ` and physical `Mem.bytes`: wherever the ghost heap owns a byte,
the physical memory holds the same byte. These lemmas turn that agreement,
together with `pointsTo_u64` ownership, into facts about `Mem.read64`/`write64`:

* `read64_sound` — owning the 8 little-endian digit-bytes of `v` forces
  `mem.read64 addr = v`.  (load side)
* `write64_agree` — updating exactly those 8 cells to the digits of `v` keeps
  agreement with `mem.write64 addr v`.  Disjointness from *other* owned cells is
  automatic (distinct `UInt32` keys + no wraparound), so there are **no**
  byte-range hypotheses — this is what replaces the manual `read64_write64_ne`
  framing lemmas.  (store side)
-/

namespace Wasm.SepLogic

open Iris Wasm Std

/-! ## Little-endian recomposition (pure `Mem` facts) -/

/-- `Mem.read64` of a memory whose 8 bytes at `a` are the little-endian digits
`byte64 v 0 … byte64 v 7` recomposes to `v`. The digits use the same bit form as
`Mem.write64`, so this is a pure bitvector identity discharged by `bv_decide`. -/
theorem read64_of_digits (mem : Mem) (a : UInt32) (v : UInt64)
    (h : ∀ i : Nat, i < 8 → mem.bytes (a.toNat + i) = byte64 v i) :
    mem.read64 a = v := by
  simp only [Mem.read64]
  have e0 := h 0 (by omega); have e1 := h 1 (by omega)
  have e2 := h 2 (by omega); have e3 := h 3 (by omega)
  have e4 := h 4 (by omega); have e5 := h 5 (by omega)
  have e6 := h 6 (by omega); have e7 := h 7 (by omega)
  simp only [Nat.add_zero] at e0
  rw [e0, e1, e2, e3, e4, e5, e6, e7]
  simp only [byte64, Nat.mul_zero, Nat.mul_one, Nat.reduceMul, UInt64.reduceOfNat]
  bv_decide

/-- The `i`-th byte stored by `Mem.write64 a v` is exactly `byte64 v i`. -/
theorem write64_byte (mem : Mem) (a : UInt32) (v : UInt64) (i : Nat) (hi : i < 8) :
    (mem.write64 a v).bytes (a.toNat + i) = byte64 v i := by
  simp only [Mem.write64, byte64]
  have h8 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases h8 with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp only [Nat.add_zero, Nat.add_eq_left, Nat.reduceEqDiff,
      ↓reduceIte, Nat.reduceMul, Nat.mul_zero, Nat.mul_one, UInt64.reduceOfNat] <;>
    bv_decide

/-- Bytes outside the 8-byte window `[a, a+8)` are untouched by `Mem.write64 a v`. -/
theorem write64_bytes_ne (mem : Mem) (a : UInt32) (v : UInt64) (i : Nat)
    (h : i < a.toNat ∨ a.toNat + 8 ≤ i) : (mem.write64 a v).bytes i = mem.bytes i := by
  simp only [Mem.write64]
  have h0 : i ≠ a.toNat := by omega
  have h1 : i ≠ a.toNat + 1 := by omega
  have h2 : i ≠ a.toNat + 2 := by omega
  have h3 : i ≠ a.toNat + 3 := by omega
  have h4 : i ≠ a.toNat + 4 := by omega
  have h5 : i ≠ a.toNat + 5 := by omega
  have h6 : i ≠ a.toNat + 6 := by omega
  have h7 : i ≠ a.toNat + 7 := by omega
  simp [h0, h1, h2, h3, h4, h5, h6, h7]

/-- Offset addition on a `UInt32` address does not wrap below the 32-bit bound. -/
theorem toNat_add_ofNat (a : UInt32) (k : Nat) (h : a.toNat + k < 2 ^ 32) :
    (a + UInt32.ofNat k).toNat = a.toNat + k := by
  have hsize : UInt32.size = 2 ^ 32 := rfl
  rw [UInt32.toNat_add, UInt32.toNat_ofNat_of_lt' (by omega), Nat.mod_eq_of_lt (by simpa using h)]

/-! ## Ghost-heap ↔ physical-memory agreement -/

variable [inst : WasmHeapGS]

/-- Agreement: wherever the ghost heap `σ` owns a byte, physical `mem` holds it. -/
def heapAgreesWithMem (σ : WasmHeapMap (Option UInt8)) (mem : Mem) : Prop :=
  ∀ (addr : UInt32) (v : UInt8),
    get? σ addr = some (some v) → mem.bytes addr.toNat = v

/-- **Load soundness.** If `σ` agrees with `mem` and owns the 8 little-endian
digit-bytes of `v` at `addr … addr+7`, then `mem.read64 addr = v`. -/
theorem read64_sound (σ : WasmHeapMap (Option UInt8)) (mem : Mem)
    (addr : UInt32) (v : UInt64)
    (hnw : addr.toNat + 8 ≤ 2 ^ 32)
    (hagree : heapAgreesWithMem σ mem)
    (hown : ∀ i : Nat, i < 8 → get? σ (addr + UInt32.ofNat i) = some (some (byte64 v i))) :
    mem.read64 addr = v := by
  apply read64_of_digits
  intro i hi
  have hbyte := hagree (addr + UInt32.ofNat i) (byte64 v i) (hown i hi)
  rwa [toNat_add_ofNat addr i (by omega)] at hbyte

/-- **Store soundness.** If `σ` agrees with `mem`, and `σ'` updates *exactly* the
8 cells at `addr … addr+7` to the digits of `v` (leaving every other owned cell
unchanged), then `σ'` agrees with `mem.write64 addr v`.

Crucially there are no disjointness hypotheses about other owned regions: an
owned cell `k` distinct from all 8 written cells cannot lie in `[addr, addr+8)`
(a `UInt32` in that Nat-range would equal one of the written keys, by
no-wraparound), so `write64` leaves its byte — and thus agreement — intact. -/
theorem write64_agree (σ σ' : WasmHeapMap (Option UInt8)) (mem : Mem)
    (addr : UInt32) (v : UInt64)
    (hnw : addr.toNat + 8 ≤ 2 ^ 32)
    (hagree : heapAgreesWithMem σ mem)
    (hupd : ∀ i : Nat, i < 8 → get? σ' (addr + UInt32.ofNat i) = some (some (byte64 v i)))
    (hframe : ∀ (k : UInt32) (w : UInt8), get? σ' k = some (some w) →
        (∀ i : Nat, i < 8 → k ≠ addr + UInt32.ofNat i) → get? σ k = some (some w)) :
    heapAgreesWithMem σ' (mem.write64 addr v) := by
  intro k w hk
  by_cases hin : ∃ i : Nat, i < 8 ∧ k = addr + UInt32.ofNat i
  · obtain ⟨i, hi, rfl⟩ := hin
    rw [hupd i hi] at hk
    obtain rfl := (Option.some.inj (Option.some.inj hk)).symm
    rw [toNat_add_ofNat addr i (by omega)]
    exact write64_byte mem addr v i hi
  · have hframe' : ∀ i : Nat, i < 8 → k ≠ addr + UInt32.ofNat i :=
      fun i hi hEq => hin ⟨i, hi, hEq⟩
    have hmem := hagree k w (hframe k w hk hframe')
    rcases Nat.lt_or_ge k.toNat addr.toNat with hlt | hge
    · rw [write64_bytes_ne mem addr v k.toNat (Or.inl hlt)]; exact hmem
    · rcases Nat.lt_or_ge k.toNat (addr.toNat + 8) with hlt2 | hge2
      · exact absurd (UInt32.toNat.inj (by
          rw [toNat_add_ofNat addr (k.toNat - addr.toNat) (by omega)]; omega))
          (hframe' (k.toNat - addr.toNat) (by omega))
      · rw [write64_bytes_ne mem addr v k.toNat (Or.inr hge2)]; exact hmem

end Wasm.SepLogic
