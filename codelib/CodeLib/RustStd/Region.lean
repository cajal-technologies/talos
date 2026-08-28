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

/-- The `k`-th 4-byte slot of a `u32` array based at `base` (wasm address
`base + 4 * k`). The 32-bit twin of `slot64`, matching the `Mem.words32`
element stride. -/
def slot32 (base k : UInt32) : MemRegion := ⟨base + 4 * k, 4⟩

/-- `x <<< 2 = 4 * x` on `UInt32`: the `(const 2) shl` address computation LLVM
emits for a `u32` array index. -/
theorem shl2_eq_mul4 (x : UInt32) : x <<< (2 % 32 : UInt32) = 4 * x := by bv_decide

/-- No wraparound: if the slot's true byte offset stays below `2^32`, the wasm
address of `slot32 base k` is the integer `base.toNat + 4 * k.toNat`. -/
theorem slot32_base_toNat (base k : UInt32)
    (h : base.toNat + 4 * k.toNat < 4294967296) :
    (slot32 base k).base.toNat = base.toNat + 4 * k.toNat := by
  simp only [slot32, UInt32.toNat_add, UInt32.toNat_mul, UInt32.reduceToNat]
  omega

end MemRegion

end Wasm
