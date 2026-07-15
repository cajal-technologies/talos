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
  single region fact instead of re-shaping `Or`s at every call site. All four
  take the **written region first**; flip with `Disjoint.symm` if a fact
  arrives in the other orientation.
* **Disjoint stores commute** (`Mem.write64_write64_comm`, 32/32 and mixed
  widths): requested in #68 and previously missing everywhere. Each width pair
  is a one-line instance of `Mem.write_write_comm_of_footprints` (Frame), so a
  new width costs only its two byte-level footprint lemmas there.
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

/-- Ordered interval disjointness: one region's byte range ends at or before
the other's begins. For non-empty regions this coincides with set-disjointness
of the byte ranges; a zero-length region strictly *inside* another counts as
overlapping here even though it occupies no bytes. That strictness is
deliberate — it keeps the shape a plain two-case `omega` fact, and every
consumer instantiates a positive `len` (4 or 8). -/
def Disjoint (r₁ r₂ : MemRegion) : Prop :=
  r₁.base.toNat + r₁.len ≤ r₂.base.toNat ∨ r₂.base.toNat + r₂.len ≤ r₁.base.toNat

instance (r₁ r₂ : MemRegion) : Decidable (r₁.Disjoint r₂) := by
  unfold Disjoint; exact inferInstance

theorem Disjoint.symm {r₁ r₂ : MemRegion} (h : r₁.Disjoint r₂) : r₂.Disjoint r₁ :=
  h.elim Or.inr Or.inl

end MemRegion

/-! ## Bridging `Disjoint` to the `Frame` read/write lemmas

The `Frame` lemmas each take a raw interval disjunction whose orientation is
an artifact of their statements; these wrappers hide that behind one uniform
convention: the `Disjoint` fact always names the **written** region first and
the read region second. A fact oriented the other way flips with
`Disjoint.symm`. -/

theorem Mem.read64_write64_of_region (m : Mem) (a b : UInt32) (v : UInt64)
    (h : MemRegion.Disjoint ⟨a, 8⟩ ⟨b, 8⟩) :
    (m.write64 a v).read64 b = m.read64 b :=
  Mem.read64_write64_disjoint m a b v h.symm

theorem Mem.read64_write32_of_region (m : Mem) (a b : UInt32) (v : UInt32)
    (h : MemRegion.Disjoint ⟨b, 4⟩ ⟨a, 8⟩) :
    (m.write32 b v).read64 a = m.read64 a :=
  Mem.read64_write32_disjoint m a b v h

theorem Mem.read32_write32_of_region (m : Mem) (a b v : UInt32)
    (h : MemRegion.Disjoint ⟨a, 4⟩ ⟨b, 4⟩) :
    (m.write32 a v).read32 b = m.read32 b :=
  Mem.read32_write32_disjoint m a b v h.symm

theorem Mem.read32_write64_of_region (m : Mem) (a b : UInt32) (v : UInt64)
    (h : MemRegion.Disjoint ⟨b, 8⟩ ⟨a, 4⟩) :
    (m.write64 b v).read32 a = m.read32 a :=
  Mem.read32_write64_disjoint m a b v h.symm

/-! ## Disjoint stores commute

One-line instances of `Mem.write_write_comm_of_footprints` (Frame): each
width supplies page preservation plus its two byte-level footprint facts. -/

/-- Two 64-bit stores to disjoint ranges commute. -/
theorem Mem.write64_write64_comm (m : Mem) (a b : UInt32) (v w : UInt64)
    (h : MemRegion.Disjoint ⟨a, 8⟩ ⟨b, 8⟩) :
    (m.write64 a v).write64 b w = (m.write64 b w).write64 a v :=
  Mem.write_write_comm_of_footprints (·.write64 a v) (·.write64 b w) a b 8 8 h
    (fun _ => rfl) (fun _ => rfl)
    (fun m i hi => Mem.write64_bytes_of_disjoint m a v i hi)
    (fun m i hi => Mem.write64_bytes_of_disjoint m b w i hi)
    (fun m m' i hi => Mem.write64_bytes_in m m' a v i hi)
    (fun m m' i hi => Mem.write64_bytes_in m m' b w i hi) m

/-- Two 32-bit stores to disjoint ranges commute. -/
theorem Mem.write32_write32_comm (m : Mem) (a b : UInt32) (v w : UInt32)
    (h : MemRegion.Disjoint ⟨a, 4⟩ ⟨b, 4⟩) :
    (m.write32 a v).write32 b w = (m.write32 b w).write32 a v :=
  Mem.write_write_comm_of_footprints (·.write32 a v) (·.write32 b w) a b 4 4 h
    (fun _ => rfl) (fun _ => rfl)
    (fun m i hi => Mem.write32_bytes_of_disjoint m a v i hi)
    (fun m i hi => Mem.write32_bytes_of_disjoint m b w i hi)
    (fun m m' i hi => Mem.write32_bytes_in m m' a v i hi)
    (fun m m' i hi => Mem.write32_bytes_in m m' b w i hi) m

/-- A 64-bit store and a 32-bit store to disjoint ranges commute. -/
theorem Mem.write64_write32_comm (m : Mem) (a b : UInt32) (v : UInt64) (w : UInt32)
    (h : MemRegion.Disjoint ⟨a, 8⟩ ⟨b, 4⟩) :
    (m.write64 a v).write32 b w = (m.write32 b w).write64 a v :=
  Mem.write_write_comm_of_footprints (·.write64 a v) (·.write32 b w) a b 8 4 h
    (fun _ => rfl) (fun _ => rfl)
    (fun m i hi => Mem.write64_bytes_of_disjoint m a v i hi)
    (fun m i hi => Mem.write32_bytes_of_disjoint m b w i hi)
    (fun m m' i hi => Mem.write64_bytes_in m m' a v i hi)
    (fun m m' i hi => Mem.write32_bytes_in m m' b w i hi) m

/-! ## Array element slots -/

namespace MemRegion

/-- The `k`-th 8-byte slot of a `u64` array based at `base`. Its `base` is the
wasm-level address `base + 8 * k` — definitionally the `elemAddr` shape used by
array specs. -/
def slot64 (base k : UInt32) : MemRegion := ⟨base + 8 * k, 8⟩

/-- `x <<< 3 = 8 * x` on `UInt32`: bridges the `(const 3) shl` address
computation LLVM emits to the `8 * k` slot offset. The single `bv_decide`
fact of the slot algebra — `slot64_of_shl` derives from it. -/
theorem shl3_eq_mul8 (x : UInt32) : x <<< (3 % 32 : UInt32) = 8 * x := by bv_decide

/-- The codegen's `(k <<< 3) + base` lands on the slot base address. -/
theorem slot64_of_shl (base k : UInt32) :
    k <<< (3 % 32 : UInt32) + base = (slot64 base k).base := by
  simp only [slot64]
  rw [shl3_eq_mul8, UInt32.add_comm]

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
