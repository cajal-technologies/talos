import CodeLib.RustStd.Frame

/-!
# `CodeLib.RustStd.Mem` — reusable linear-memory framing

The memory analogue of the `U64/*_chunk` value-op trunk: lemmas that let a
memory-manipulating spec proof reason about *disjoint* accesses without
re-deriving byte-level arithmetic every time.

`Frame.lean` already covers the same-address spill round-trip
(`Mem.read{32,64}_write{32,64}_same`, `Mem.write{32,64}_pages`). This file adds
the other half of a Hoare-style framing discipline — a write to one region
leaves a *disjoint* read untouched:

* `Mem.write64_bytes_outside` — a `write64` mutates only its own 8-byte range.
* `Mem.read64_write64_disjoint` — the derived 64-bit frame rule.

`swap_elements` consumes these (two `u64` elements at distinct indices do not
alias, and neither aliases the shadow-stack scratch slot). The 32-bit and
`Mem.copy` analogues land alongside `encode`/`decode`, which need them.

Disjointness is stated on the underlying byte addresses (`UInt32.toNat`), so the
caller discharges the geometric side conditions with `omega`.
-/

namespace Wasm

/-! ## A store touches only its own range -/

/-- A `write64` leaves every byte outside its 8-byte range `[a, a+8)`
untouched. -/
theorem Mem.write64_bytes_outside (m : Mem) (a : UInt32) (v : UInt64) (i : Nat)
    (h : i < a.toNat ∨ a.toNat + 8 ≤ i) : (m.write64 a v).bytes i = m.bytes i := by
  simp only [Mem.write64]
  have h0 : ¬ (i = a.toNat)     := by omega
  have h1 : ¬ (i = a.toNat + 1) := by omega
  have h2 : ¬ (i = a.toNat + 2) := by omega
  have h3 : ¬ (i = a.toNat + 3) := by omega
  have h4 : ¬ (i = a.toNat + 4) := by omega
  have h5 : ¬ (i = a.toNat + 5) := by omega
  have h6 : ¬ (i = a.toNat + 6) := by omega
  have h7 : ¬ (i = a.toNat + 7) := by omega
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, ↓reduceIte]

/-! ## The 64-bit frame rule -/

/-- Reading a 64-bit word from a range disjoint from a preceding `write64`
returns the original (pre-write) value. The companion to `read64_write64_same`
for frames that store operands at distinct 8-byte slots (`swap_elements`,
`min`/`max`). -/
theorem Mem.read64_write64_disjoint (m : Mem) (a b : UInt32) (v : UInt64)
    (h : a.toNat + 8 ≤ b.toNat ∨ b.toNat + 8 ≤ a.toNat) :
    (m.write64 b v).read64 a = m.read64 a := by
  simp only [Mem.read64]
  rw [Mem.write64_bytes_outside m b v a.toNat (by omega),
      Mem.write64_bytes_outside m b v (a.toNat + 1) (by omega),
      Mem.write64_bytes_outside m b v (a.toNat + 2) (by omega),
      Mem.write64_bytes_outside m b v (a.toNat + 3) (by omega),
      Mem.write64_bytes_outside m b v (a.toNat + 4) (by omega),
      Mem.write64_bytes_outside m b v (a.toNat + 5) (by omega),
      Mem.write64_bytes_outside m b v (a.toNat + 6) (by omega),
      Mem.write64_bytes_outside m b v (a.toNat + 7) (by omega)]

/-! ## 32-bit stores: framing for the opt-0 slice spill

`swap_elements`' entry spills the `(ptr, len)` fat pointer to its stack frame
with two `store32`s, reads them back, then reads the *array* (`read64`) — which
sits in a disjoint region. So we need both the 32-bit frame rule and the mixed
`read64`-past-`write32` rule. -/

/-- A `write32` leaves every byte outside its 4-byte range `[a, a+4)` untouched. -/
theorem Mem.write32_bytes_outside (m : Mem) (a : UInt32) (v : UInt32) (i : Nat)
    (h : i < a.toNat ∨ a.toNat + 4 ≤ i) : (m.write32 a v).bytes i = m.bytes i := by
  simp only [Mem.write32]
  have h0 : ¬ (i = a.toNat)     := by omega
  have h1 : ¬ (i = a.toNat + 1) := by omega
  have h2 : ¬ (i = a.toNat + 2) := by omega
  have h3 : ¬ (i = a.toNat + 3) := by omega
  simp only [h0, h1, h2, h3, ↓reduceIte]

/-- Reading a 32-bit word from a range disjoint from a preceding `write32`
returns the original value. -/
theorem Mem.read32_write32_disjoint (m : Mem) (a b : UInt32) (v : UInt32)
    (h : a.toNat + 4 ≤ b.toNat ∨ b.toNat + 4 ≤ a.toNat) :
    (m.write32 b v).read32 a = m.read32 a := by
  simp only [Mem.read32]
  rw [Mem.write32_bytes_outside m b v a.toNat (by omega),
      Mem.write32_bytes_outside m b v (a.toNat + 1) (by omega),
      Mem.write32_bytes_outside m b v (a.toNat + 2) (by omega),
      Mem.write32_bytes_outside m b v (a.toNat + 3) (by omega)]

/-- Reading a 64-bit word is unaffected by a `write32` to a disjoint 4-byte
slot. The mixed-width frame rule used when the array (`read64`) is read past the
frame's 32-bit spill (`write32`). -/
theorem Mem.read64_write32_disjoint (m : Mem) (a b : UInt32) (v : UInt32)
    (h : a.toNat + 8 ≤ b.toNat ∨ b.toNat + 4 ≤ a.toNat) :
    (m.write32 b v).read64 a = m.read64 a := by
  simp only [Mem.read64]
  rw [Mem.write32_bytes_outside m b v a.toNat (by omega),
      Mem.write32_bytes_outside m b v (a.toNat + 1) (by omega),
      Mem.write32_bytes_outside m b v (a.toNat + 2) (by omega),
      Mem.write32_bytes_outside m b v (a.toNat + 3) (by omega),
      Mem.write32_bytes_outside m b v (a.toNat + 4) (by omega),
      Mem.write32_bytes_outside m b v (a.toNat + 5) (by omega),
      Mem.write32_bytes_outside m b v (a.toNat + 6) (by omega),
      Mem.write32_bytes_outside m b v (a.toNat + 7) (by omega)]

end Wasm
