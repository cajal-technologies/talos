import Interpreter.Wasm
import Std.Tactic.BVDecide

/-!
# `CodeLib.RustStd.Frame`

Foundational reasoning helpers for Rust functions compiled to wasm at
`opt-level = 0` (the corpus convention; see `programs/rust/Cargo.toml`).

At `-O0`, LLVM gives every function a stack frame and **spills results
through linear memory** before returning them. So *every* opt-0 spec proof
pushes a value through a `store`/`load` round-trip and has to show the
frame access stays in bounds. The lemmas here discharge that once, in a
form that does not care about the concrete spill address:

* `Mem.read{32,64}_write{32,64}_same` — read-after-write at the same
  address returns the value (no bound on the address needed).
* `Mem.write{32,64}_pages` — a store leaves the page count unchanged.
* `Mem.read{32,64}_write{32,64}_disjoint` — a read is unaffected by a
  write to a disjoint byte range, in every width combination, built on
  the byte-level `Mem.write{32,64}_bytes_of_disjoint`. Proofs that juggle
  several frame slots (argument spills vs. scratch vs. result) need these
  to carry a value across the unrelated stores in between.

The in-bounds (no-trap) obligation also needs `sp - 16` not to underflow;
that is `UInt32.toNat_sub_of_le`, which Lean core already provides
(`Init.Data.UInt.Lemmas`), so it is used directly rather than re-proved here.

The unconditional `_same`/`_pages` lemmas are intentionally global `@[simp]`
— confluent, terminating rewrites used corpus-wide. The `_disjoint` family
is deliberately **not** `@[simp]`: each rewrite carries a disjointness side
condition, so proofs name these lemmas explicitly (in a `simp only` set or
a `rw`) and discharge the side goal with `decide` / `omega` on the concrete
frame addresses. Op-specific lemmas (e.g. `popcnt` bounds) are added here
only once a real proof first consumes them.
-/

namespace Wasm

/-! ## Store/load round-trips -/

/-- Reading a 32-bit word back from the address it was just written to
returns the stored value. -/
@[simp] theorem Mem.read32_write32_same (m : Mem) (a v : UInt32) :
    (m.write32 a v).read32 a = v := by
  simp only [Mem.read32, Mem.write32]
  have e1 : a.toNat + 1 ≠ a.toNat := by omega
  have e2 : a.toNat + 2 ≠ a.toNat := by omega
  have e3 : a.toNat + 3 ≠ a.toNat := by omega
  have e21 : a.toNat + 2 ≠ a.toNat + 1 := by omega
  have e31 : a.toNat + 3 ≠ a.toNat + 1 := by omega
  have e32 : a.toNat + 3 ≠ a.toNat + 2 := by omega
  simp only [e1, e2, e3, e21, e31, e32, ↓reduceIte]
  bv_decide

/-- Reading a 64-bit word back from the address it was just written to
returns the stored value. -/
@[simp] theorem Mem.read64_write64_same (m : Mem) (a : UInt32) (v : UInt64) :
    (m.write64 a v).read64 a = v := by
  simp only [Mem.read64, Mem.write64]
  simp only [Nat.add_eq_left, OfNat.ofNat_ne_zero, Nat.succ_ne_self, ↓reduceIte,
             Nat.reduceEqDiff]
  bv_decide

/-! ## Byte-level write footprints

A write only touches the bytes inside its footprint. These are the
building blocks for the word-level disjointness lemmas below, and are
occasionally useful on their own when a proof descends to `Mem.bytes`. -/

/-- A byte outside the 8-byte footprint of a `write64` is unchanged. -/
theorem Mem.write64_bytes_of_disjoint (m : Mem) (a : UInt32) (v : UInt64) (i : Nat)
    (h : i < a.toNat ∨ a.toNat + 8 ≤ i) :
    (m.write64 a v).bytes i = m.bytes i := by
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

/-- A byte outside the 4-byte footprint of a `write32` is unchanged. -/
theorem Mem.write32_bytes_of_disjoint (m : Mem) (a v : UInt32) (i : Nat)
    (h : i < a.toNat ∨ a.toNat + 4 ≤ i) :
    (m.write32 a v).bytes i = m.bytes i := by
  simp only [Mem.write32]
  have h0 : i ≠ a.toNat := by omega
  have h1 : i ≠ a.toNat + 1 := by omega
  have h2 : i ≠ a.toNat + 2 := by omega
  have h3 : i ≠ a.toNat + 3 := by omega
  simp [h0, h1, h2, h3]

/-! ## Disjoint read/write framing

A read is unaffected by a write to a disjoint byte range, in all four
width combinations of the opt-0 corpus (`read{32,64}` × `write{32,64}`).
The disjointness hypothesis puts one footprint entirely before the other,
stated on `.toNat` so that `decide` / `omega` closes it when the frame
addresses are concrete. -/

/-- A 64-bit read is unaffected by a 64-bit write to a disjoint 8-byte
range. -/
theorem Mem.read64_write64_disjoint (m : Mem) (a b : UInt32) (v : UInt64)
    (h : b.toNat + 8 ≤ a.toNat ∨ a.toNat + 8 ≤ b.toNat) :
    (m.write64 a v).read64 b = m.read64 b := by
  simp only [Mem.read64]
  rw [Mem.write64_bytes_of_disjoint m a v b.toNat (by omega),
      Mem.write64_bytes_of_disjoint m a v (b.toNat + 1) (by omega),
      Mem.write64_bytes_of_disjoint m a v (b.toNat + 2) (by omega),
      Mem.write64_bytes_of_disjoint m a v (b.toNat + 3) (by omega),
      Mem.write64_bytes_of_disjoint m a v (b.toNat + 4) (by omega),
      Mem.write64_bytes_of_disjoint m a v (b.toNat + 5) (by omega),
      Mem.write64_bytes_of_disjoint m a v (b.toNat + 6) (by omega),
      Mem.write64_bytes_of_disjoint m a v (b.toNat + 7) (by omega)]

/-- A 64-bit read is unaffected by a 32-bit write to a disjoint range. -/
theorem Mem.read64_write32_disjoint (m : Mem) (a b : UInt32) (v : UInt32)
    (h : b.toNat + 4 ≤ a.toNat ∨ a.toNat + 8 ≤ b.toNat) :
    (m.write32 b v).read64 a = m.read64 a := by
  simp only [Mem.read64]
  rw [Mem.write32_bytes_of_disjoint m b v a.toNat (by omega),
      Mem.write32_bytes_of_disjoint m b v (a.toNat + 1) (by omega),
      Mem.write32_bytes_of_disjoint m b v (a.toNat + 2) (by omega),
      Mem.write32_bytes_of_disjoint m b v (a.toNat + 3) (by omega),
      Mem.write32_bytes_of_disjoint m b v (a.toNat + 4) (by omega),
      Mem.write32_bytes_of_disjoint m b v (a.toNat + 5) (by omega),
      Mem.write32_bytes_of_disjoint m b v (a.toNat + 6) (by omega),
      Mem.write32_bytes_of_disjoint m b v (a.toNat + 7) (by omega)]

/-- A 32-bit read is unaffected by a 32-bit write to a disjoint range. -/
theorem Mem.read32_write32_disjoint (m : Mem) (a b v : UInt32)
    (h : b.toNat + 4 ≤ a.toNat ∨ a.toNat + 4 ≤ b.toNat) :
    (m.write32 a v).read32 b = m.read32 b := by
  simp only [Mem.read32]
  rw [Mem.write32_bytes_of_disjoint m a v b.toNat (by omega),
      Mem.write32_bytes_of_disjoint m a v (b.toNat + 1) (by omega),
      Mem.write32_bytes_of_disjoint m a v (b.toNat + 2) (by omega),
      Mem.write32_bytes_of_disjoint m a v (b.toNat + 3) (by omega)]

/-- A 32-bit read is unaffected by a 64-bit write to a disjoint range. -/
theorem Mem.read32_write64_disjoint (m : Mem) (a : UInt32) (b : UInt32) (v : UInt64)
    (h : a.toNat + 4 ≤ b.toNat ∨ b.toNat + 8 ≤ a.toNat) :
    (m.write64 b v).read32 a = m.read32 a := by
  simp only [Mem.read32]
  rw [Mem.write64_bytes_of_disjoint m b v a.toNat (by omega),
      Mem.write64_bytes_of_disjoint m b v (a.toNat + 1) (by omega),
      Mem.write64_bytes_of_disjoint m b v (a.toNat + 2) (by omega),
      Mem.write64_bytes_of_disjoint m b v (a.toNat + 3) (by omega)]

/-! ## Stores preserve the page count -/

@[simp] theorem Mem.write32_pages (m : Mem) (a v : UInt32) :
    (m.write32 a v).pages = m.pages := rfl

@[simp] theorem Mem.write64_pages (m : Mem) (a : UInt32) (v : UInt64) :
    (m.write64 a v).pages = m.pages := rfl

/-! ## Mixed-width read/write round-trips

These lemmas extract the lower or upper 32-bit half from a `write64` or
`read64` — the pattern that arises when func5 copies 8-byte descriptors
through the shadow stack and then reads back the individual 32-bit fields. -/

/-- Reading the lower 32 bits from a `write64` at the same address returns
    the low 32-bit half of the stored value. -/
theorem Mem.read32_write64_low (m : Mem) (a : UInt32) (v : UInt64) :
    (m.write64 a v).read32 a = v.toUInt32 := by
  simp only [Mem.read32, Mem.write64]
  simp only [Nat.add_eq_left, OfNat.ofNat_ne_zero, Nat.succ_ne_self, ↓reduceIte,
             Nat.reduceEqDiff]
  bv_decide

/-- The lower 32 bits of a `read64` equal the `read32` at the same address. -/
theorem Mem.read64_lo_is_read32 (m : Mem) (a : UInt32) :
    (m.read64 a).toUInt32 = m.read32 a := by
  simp only [Mem.read64, Mem.read32]
  bv_decide

/-- Reading the upper 32 bits from a `write64` at the same base address
    (offset +4) returns the high 32-bit half of the stored value.
    Requires that the address does not overflow: `(a + 4).toNat = a.toNat + 4`. -/
theorem Mem.read32_write64_high (m : Mem) (a : UInt32) (v : UInt64)
    (hnat : (a + 4).toNat = a.toNat + 4) :
    (m.write64 a v).read32 (a + 4) = (v >>> 32).toUInt32 := by
  -- After hnat, read positions are a.toNat+4, a.toNat+4+1, a.toNat+4+2, a.toNat+4+3;
  -- normalize the +1/+2/+3 offsets so they match the write64 footprint indices.
  simp only [Mem.read32, Mem.write64, hnat,
             show a.toNat + 4 + 1 = a.toNat + 5 from by omega,
             show a.toNat + 4 + 2 = a.toNat + 6 from by omega,
             show a.toNat + 4 + 3 = a.toNat + 7 from by omega]
  simp only [Nat.add_eq_left, OfNat.ofNat_ne_zero, Nat.succ_ne_self, ↓reduceIte,
             Nat.reduceEqDiff]
  bv_decide

/-- The upper 32 bits of a `read64` equal the `read32` at offset +4.
    Requires that the address does not overflow: `(a + 4).toNat = a.toNat + 4`. -/
theorem Mem.read64_hi_is_read32 (m : Mem) (a : UInt32)
    (hnat : (a + 4).toNat = a.toNat + 4) :
    ((m.read64 a) >>> 32).toUInt32 = m.read32 (a + 4) := by
  simp only [Mem.read64, Mem.read32, hnat,
             show a.toNat + 4 + 1 = a.toNat + 5 from by omega,
             show a.toNat + 4 + 2 = a.toNat + 6 from by omega,
             show a.toNat + 4 + 3 = a.toNat + 7 from by omega]
  bv_decide

end Wasm
