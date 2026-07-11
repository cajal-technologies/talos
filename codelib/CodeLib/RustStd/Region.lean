import Interpreter.Wasm
import CodeLib.RustStd.Frame

/-!
# `CodeLib.RustStd.Region`

Region-level memory algebra (issue #68, phase 2a), building on the byte-level
framing lemmas in `CodeLib.RustStd.Frame`.

* `MemRegion` — a contiguous byte range of linear memory (`base` + `len`), with
  a decidable `Disjoint` predicate stated over `.toNat` intervals. The interval
  disjunction is the same load-bearing shape the `Frame` lemmas consume, so
  `omega` / `decide` keep discharging side conditions on concrete frame slots
  and symbolic array addresses alike.
* Bridges from `Disjoint` facts to the `Frame` read/write lemmas
  (`Mem.read64_write64_of_region`, …): thin one-liners, so proofs can carry a
  single region fact instead of re-shaping `Or`s at every call site.
* **Disjoint stores commute** (`Mem.write64_write64_comm`, 32/32 and mixed
  widths): requested in #68 and previously missing everywhere. Proved
  byte-pointwise from the function-model `Mem`.
* `slot64` — the `k`-th 8-byte element slot of a `u64` array region, with the
  no-wrap and pairwise-disjointness lemmas array proofs otherwise re-derive
  (first consumer: `Project.SwapElements.Spec`).
-/

namespace Wasm

/-- A contiguous byte region of linear memory: base address and byte length.
The `len` is a `Nat` (not `UInt32`): regions are *specification-level* objects,
and keeping the length unbounded lets `Disjoint` talk about true integer
intervals with no hidden wraparound. -/
structure MemRegion where
  base : UInt32
  len  : Nat
deriving Repr, DecidableEq

namespace MemRegion

/-- Two regions occupy disjoint integer byte ranges. -/
def Disjoint (r₁ r₂ : MemRegion) : Prop :=
  r₁.base.toNat + r₁.len ≤ r₂.base.toNat ∨ r₂.base.toNat + r₂.len ≤ r₁.base.toNat

instance (r₁ r₂ : MemRegion) : Decidable (r₁.Disjoint r₂) := by
  unfold Disjoint; exact inferInstance

theorem Disjoint.symm {r₁ r₂ : MemRegion} (h : r₁.Disjoint r₂) : r₂.Disjoint r₁ :=
  h.elim Or.inr Or.inl

end MemRegion

/-! ## Bridging `Disjoint` to the `Frame` read/write lemmas

The `Frame` lemmas take the raw interval disjunction with the *write* address
on the left; these wrappers take a `Disjoint` fact between the written region
and the read region, in either order. -/

theorem Mem.read64_write64_of_region (m : Mem) (a b : UInt32) (v : UInt64)
    (h : MemRegion.Disjoint ⟨a, 8⟩ ⟨b, 8⟩) :
    (m.write64 a v).read64 b = m.read64 b :=
  Mem.read64_write64_disjoint m a b v (h.elim Or.inr Or.inl)

theorem Mem.read64_write32_of_region (m : Mem) (a b : UInt32) (v : UInt32)
    (h : MemRegion.Disjoint ⟨b, 4⟩ ⟨a, 8⟩) :
    (m.write32 b v).read64 a = m.read64 a :=
  Mem.read64_write32_disjoint m a b v h

theorem Mem.read32_write32_of_region (m : Mem) (a b v : UInt32)
    (h : MemRegion.Disjoint ⟨a, 4⟩ ⟨b, 4⟩) :
    (m.write32 a v).read32 b = m.read32 b :=
  Mem.read32_write32_disjoint m a b v (h.elim Or.inr Or.inl)

theorem Mem.read32_write64_of_region (m : Mem) (a b : UInt32) (v : UInt64)
    (h : MemRegion.Disjoint ⟨a, 4⟩ ⟨b, 8⟩) :
    (m.write64 b v).read32 a = m.read32 a :=
  Mem.read32_write64_disjoint m a b v h

/-! ## Disjoint stores commute -/

/-- Two memories with equal page counts and pointwise-equal bytes are equal. -/
theorem Mem.ext_bytes {m₁ m₂ : Mem} (hp : m₁.pages = m₂.pages)
    (hb : ∀ i, m₁.bytes i = m₂.bytes i) : m₁ = m₂ := by
  cases m₁; cases m₂
  simp only [Mem.mk.injEq]
  exact ⟨hp, funext hb⟩

/-- Inside its 8-byte footprint, the byte written by a `write64` depends only
on the address and value, not on the underlying memory. -/
theorem Mem.write64_bytes_in (m m' : Mem) (a : UInt32) (v : UInt64) (i : Nat)
    (hi : a.toNat ≤ i ∧ i < a.toNat + 8) :
    (m.write64 a v).bytes i = (m'.write64 a v).bytes i := by
  simp only [Mem.write64]
  split_ifs <;> first | rfl | omega

/-- Inside its 4-byte footprint, the byte written by a `write32` depends only
on the address and value, not on the underlying memory. -/
theorem Mem.write32_bytes_in (m m' : Mem) (a v : UInt32) (i : Nat)
    (hi : a.toNat ≤ i ∧ i < a.toNat + 4) :
    (m.write32 a v).bytes i = (m'.write32 a v).bytes i := by
  simp only [Mem.write32]
  split_ifs <;> first | rfl | omega

/-- Two 64-bit stores to disjoint ranges commute. -/
theorem Mem.write64_write64_comm (m : Mem) (a b : UInt32) (v w : UInt64)
    (h : MemRegion.Disjoint ⟨a, 8⟩ ⟨b, 8⟩) :
    (m.write64 a v).write64 b w = (m.write64 b w).write64 a v := by
  have hd : a.toNat + 8 ≤ b.toNat ∨ b.toNat + 8 ≤ a.toNat := h
  refine Mem.ext_bytes (by simp) fun i => ?_
  by_cases hia : a.toNat ≤ i ∧ i < a.toNat + 8
  · rw [Mem.write64_bytes_of_disjoint _ b w i (by omega)]
    exact Mem.write64_bytes_in m (m.write64 b w) a v i hia
  · by_cases hib : b.toNat ≤ i ∧ i < b.toNat + 8
    · rw [Mem.write64_bytes_of_disjoint (m.write64 b w) a v i (by omega)]
      exact Mem.write64_bytes_in (m.write64 a v) m b w i hib
    · rw [Mem.write64_bytes_of_disjoint _ b w i (by omega),
          Mem.write64_bytes_of_disjoint _ a v i (by omega),
          Mem.write64_bytes_of_disjoint _ a v i (by omega),
          Mem.write64_bytes_of_disjoint _ b w i (by omega)]

/-- Two 32-bit stores to disjoint ranges commute. -/
theorem Mem.write32_write32_comm (m : Mem) (a b : UInt32) (v w : UInt32)
    (h : MemRegion.Disjoint ⟨a, 4⟩ ⟨b, 4⟩) :
    (m.write32 a v).write32 b w = (m.write32 b w).write32 a v := by
  have hd : a.toNat + 4 ≤ b.toNat ∨ b.toNat + 4 ≤ a.toNat := h
  refine Mem.ext_bytes (by simp) fun i => ?_
  by_cases hia : a.toNat ≤ i ∧ i < a.toNat + 4
  · rw [Mem.write32_bytes_of_disjoint _ b w i (by omega)]
    exact Mem.write32_bytes_in m (m.write32 b w) a v i hia
  · by_cases hib : b.toNat ≤ i ∧ i < b.toNat + 4
    · rw [Mem.write32_bytes_of_disjoint (m.write32 b w) a v i (by omega)]
      exact Mem.write32_bytes_in (m.write32 a v) m b w i hib
    · rw [Mem.write32_bytes_of_disjoint _ b w i (by omega),
          Mem.write32_bytes_of_disjoint _ a v i (by omega),
          Mem.write32_bytes_of_disjoint _ a v i (by omega),
          Mem.write32_bytes_of_disjoint _ b w i (by omega)]

/-- A 64-bit store and a 32-bit store to disjoint ranges commute. -/
theorem Mem.write64_write32_comm (m : Mem) (a b : UInt32) (v : UInt64) (w : UInt32)
    (h : MemRegion.Disjoint ⟨a, 8⟩ ⟨b, 4⟩) :
    (m.write64 a v).write32 b w = (m.write32 b w).write64 a v := by
  have hd : a.toNat + 8 ≤ b.toNat ∨ b.toNat + 4 ≤ a.toNat := h
  refine Mem.ext_bytes (by simp) fun i => ?_
  by_cases hia : a.toNat ≤ i ∧ i < a.toNat + 8
  · rw [Mem.write32_bytes_of_disjoint _ b w i (by omega)]
    exact Mem.write64_bytes_in m (m.write32 b w) a v i hia
  · by_cases hib : b.toNat ≤ i ∧ i < b.toNat + 4
    · rw [Mem.write64_bytes_of_disjoint (m.write32 b w) a v i (by omega)]
      exact Mem.write32_bytes_in (m.write64 a v) m b w i hib
    · rw [Mem.write32_bytes_of_disjoint _ b w i (by omega),
          Mem.write64_bytes_of_disjoint _ a v i (by omega),
          Mem.write64_bytes_of_disjoint _ a v i (by omega),
          Mem.write32_bytes_of_disjoint _ b w i (by omega)]

/-! ## Array element slots -/

namespace MemRegion

/-- The `k`-th 8-byte slot of a `u64` array based at `base`. Its `base` is the
wasm-level address `base + 8 * k` — definitionally the `elemAddr` shape used by
array specs. -/
def slot64 (base k : UInt32) : MemRegion := ⟨base + 8 * k, 8⟩

/-- `x <<< 3 = 8 * x` on `UInt32`: bridges the `(const 3) shl` address
computation LLVM emits to the `8 * k` slot offset. -/
theorem shl3_eq_mul8 (x : UInt32) : x <<< (3 % 32 : UInt32) = 8 * x := by bv_decide

/-- The codegen's `(k <<< 3) + base` lands on the slot base address. -/
theorem slot64_of_shl (base k : UInt32) :
    k <<< (3 % 32 : UInt32) + base = (slot64 base k).base := by
  simp only [slot64]; bv_decide

/-- No wraparound: if the slot's true byte offset stays below `2^32`, the wasm
address of `slot64 base k` is the integer `base.toNat + 8 * k.toNat`. -/
theorem slot64_base_toNat (base k : UInt32)
    (h : base.toNat + 8 * k.toNat < 4294967296) :
    (slot64 base k).base.toNat = base.toNat + 8 * k.toNat := by
  simp only [slot64, UInt32.toNat_add, UInt32.toNat_mul, UInt32.reduceToNat]
  omega

/-- Distinct in-bounds element slots of a no-wrap array are disjoint regions. -/
theorem slot64_disjoint (base k l : UInt32)
    (hk : base.toNat + 8 * k.toNat < 4294967296)
    (hl : base.toNat + 8 * l.toNat < 4294967296)
    (hkl : k ≠ l) :
    (slot64 base k).Disjoint (slot64 base l) := by
  unfold Disjoint
  rw [slot64_base_toNat base k hk, slot64_base_toNat base l hl]
  have : k.toNat ≠ l.toNat := fun he => hkl (UInt32.toNat.inj he)
  simp only [slot64]
  omega

end MemRegion

end Wasm
