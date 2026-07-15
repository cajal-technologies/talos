import CodeLib.SepLogic.WasmHeap
import Interpreter.Wasm

/-! # Bridge: Talos Mem ↔ iris-lean GenHeap

Defines `heapAgreesWithMem` — the agreement predicate between an abstract
GenHeap state σ and physical memory — together with per-byte load/store
soundness lemmas for it, stated against the interpreter's `Mem.read8` /
`Mem.write8` API so they apply directly to interpreter-produced states.

**Status: not yet wired into the WP.** Nothing in `wp_wasm_F`,
`wasm_adequacy`, or `wasm_heap_adequacy` currently asserts this agreement:
the ghost heap threaded through `wp_wasm` is a free-floating resource, so a
`pointsTo` fact does not (yet) imply anything about `st.mem`. These
definitions are the intended ingredient for a future state interpretation
that maintains `heapAgreesWithMem σ st.mem` across steps; until that lands,
memory facts in program proofs must come from pure hypotheses about
`st.mem` (as the load/store rules in `Adequacy.lean` require).
-/

namespace Wasm.SepLogic

open Iris Wasm Std

/-! Agreement: wherever GenHeap has an entry, Mem agrees. -/

def heapAgreesWithMem (σ : WasmHeapMap (Option UInt8)) (mem : Mem) : Prop :=
  ∀ (addr : UInt32) (v : UInt8),
    get? σ addr = some (some v) → mem.read8 addr = v

/-! Soundness of load:
If GenHeap says addr ↦ v and σ agrees with Mem,
then Mem.read8 addr = v. -/

theorem load_sound (σ : WasmHeapMap (Option UInt8)) (mem : Mem)
    (addr : UInt32) (v : UInt8)
    (h_agree : heapAgreesWithMem σ mem)
    (h_own : get? σ addr = some (some v)) :
    mem.read8 addr = v :=
  h_agree addr v h_own

/-! Soundness of store:
After Mem.write8, the updated σ still agrees with the new Mem. -/

theorem store_sound (σ : WasmHeapMap (Option UInt8)) (mem : Mem)
    (addr : UInt32) (new_v : UInt8)
    (h_agree : heapAgreesWithMem σ mem) :
    heapAgreesWithMem (insert σ addr (some new_v)) (mem.write8 addr new_v) := by
  intro addr' v' h_get
  by_cases h : addr' = addr
  · subst h
    simp [get?_insert_eq rfl] at h_get
    simp [Mem.write8, Mem.read8, h_get]
  · simp [get?_insert_ne (Ne.symm h)] at h_get
    have hne : addr'.toNat ≠ addr.toNat :=
      fun h' => h (UInt32.ext h')
    simpa [Mem.write8, Mem.read8, hne] using h_agree addr' v' h_get

/-! ## 32-bit analogues -/

theorem read32_of_digits (mem : Mem) (a : UInt32) (v : UInt32)
    (h : ∀ i : Nat, i < 4 → mem.bytes (a.toNat + i) = byte32 v i) :
    mem.read32 a = v := by
  simp only [Mem.read32]
  have e0 := h 0 (by omega); have e1 := h 1 (by omega)
  have e2 := h 2 (by omega); have e3 := h 3 (by omega)
  simp only [Nat.add_zero] at e0
  rw [e0, e1, e2, e3]
  simp only [byte32, Nat.mul_zero, Nat.mul_one, Nat.reduceMul, UInt32.reduceOfNat]
  bv_decide

theorem write32_byte (mem : Mem) (a : UInt32) (v : UInt32) (i : Nat) (hi : i < 4) :
    (mem.write32 a v).bytes (a.toNat + i) = byte32 v i := by
  simp only [Mem.write32, byte32]
  have h4 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases h4 with rfl|rfl|rfl|rfl <;>
    simp only [Nat.add_zero, Nat.add_eq_left, Nat.reduceEqDiff,
      ↓reduceIte, Nat.reduceMul, Nat.mul_zero, Nat.mul_one, UInt32.reduceOfNat] <;>
    bv_decide

theorem write32_bytes_ne (mem : Mem) (a : UInt32) (v : UInt32) (i : Nat)
    (h : i < a.toNat ∨ a.toNat + 4 ≤ i) : (mem.write32 a v).bytes i = mem.bytes i := by
  simp only [Mem.write32]
  have h0 : i ≠ a.toNat := by omega
  have h1 : i ≠ a.toNat + 1 := by omega
  have h2 : i ≠ a.toNat + 2 := by omega
  have h3 : i ≠ a.toNat + 3 := by omega
  simp [h0, h1, h2, h3]

theorem read32_sound (σ : WasmHeapMap (Option UInt8)) (mem : Mem)
    (addr : UInt32) (v : UInt32)
    (hnw : addr.toNat + 4 ≤ 2 ^ 32)
    (hagree : heapAgreesWithMem σ mem)
    (hown : ∀ i : Nat, i < 4 → get? σ (addr + UInt32.ofNat i) = some (some (byte32 v i))) :
    mem.read32 addr = v := by
  apply read32_of_digits
  intro i hi
  have hbyte := hagree (addr + UInt32.ofNat i) (byte32 v i) (hown i hi)
  rwa [toNat_add_ofNat addr i (by omega)] at hbyte

theorem write32_agree (σ σ' : WasmHeapMap (Option UInt8)) (mem : Mem)
    (addr : UInt32) (v : UInt32)
    (hnw : addr.toNat + 4 ≤ 2 ^ 32)
    (hagree : heapAgreesWithMem σ mem)
    (hupd : ∀ i : Nat, i < 4 → get? σ' (addr + UInt32.ofNat i) = some (some (byte32 v i)))
    (hframe : ∀ (k : UInt32) (w : UInt8), get? σ' k = some (some w) →
        (∀ i : Nat, i < 4 → k ≠ addr + UInt32.ofNat i) → get? σ k = some (some w)) :
    heapAgreesWithMem σ' (mem.write32 addr v) := by
  intro k w hk
  by_cases hin : ∃ i : Nat, i < 4 ∧ k = addr + UInt32.ofNat i
  · obtain ⟨i, hi, rfl⟩ := hin
    rw [hupd i hi] at hk
    obtain rfl := (Option.some.inj (Option.some.inj hk)).symm
    rw [toNat_add_ofNat addr i (by omega)]
    exact write32_byte mem addr v i hi
  · have hframe' : ∀ i : Nat, i < 4 → k ≠ addr + UInt32.ofNat i :=
      fun i hi hEq => hin ⟨i, hi, hEq⟩
    have hmem := hagree k w (hframe k w hk hframe')
    rcases Nat.lt_or_ge k.toNat addr.toNat with hlt | hge
    · rw [write32_bytes_ne mem addr v k.toNat (Or.inl hlt)]; exact hmem
    · rcases Nat.lt_or_ge k.toNat (addr.toNat + 4) with hlt2 | hge2
      · exact absurd (UInt32.toNat.inj (by
          rw [toNat_add_ofNat addr (k.toNat - addr.toNat) (by omega)]; omega))
          (hframe' (k.toNat - addr.toNat) (by omega))
      · rw [write32_bytes_ne mem addr v k.toNat (Or.inr hge2)]; exact hmem

end Wasm.SepLogic
