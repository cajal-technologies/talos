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

The in-bounds (no-trap) obligation also needs `sp - 16` not to underflow;
that is `UInt32.toNat_sub_of_le`, which Lean core already provides
(`Init.Data.UInt.Lemmas`), so it is used directly rather than re-proved here.

The four `Mem.*` lemmas are intentionally global `@[simp]` — confluent,
terminating rewrites used corpus-wide. Op-specific lemmas (e.g. `popcnt`
bounds) are added here only once a real proof first consumes them.
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

/-! ## Stores preserve the page count -/

@[simp] theorem Mem.write32_pages (m : Mem) (a v : UInt32) :
    (m.write32 a v).pages = m.pages := rfl

@[simp] theorem Mem.write64_pages (m : Mem) (a : UInt32) (v : UInt64) :
    (m.write64 a v).pages = m.pages := rfl

/-! ## `memory.copy` framing

`memory.copy dst src len` overwrites exactly `[dst, dst+len)` with the *pre-copy*
bytes of `[src, src+len)` (see `Mem.copy`; this gives `memmove` semantics for
free). These lemmas answer the two questions a proof asks after a bulk copy —
what a byte *inside* the destination now reads (the matching source byte), and
that bytes *outside*, plus the page count, are untouched — mirroring the store
round-trip lemmas above. -/

/-- `memory.copy` leaves the page count unchanged. -/
@[simp] theorem Mem.copy_pages (m : Mem) (dst src len : Nat) :
    (m.copy dst src len).pages = m.pages := rfl

/-- A destination byte after `memory.copy` reads the matching source byte of the
pre-copy memory. -/
theorem Mem.bytes_copy_inside (m : Mem) (dst src len i : Nat)
    (h : dst ≤ i ∧ i < dst + len) :
    (m.copy dst src len).bytes i = m.bytes (src + (i - dst)) := by
  simp only [Mem.copy]
  rw [if_pos h]

/-- A byte outside the copied destination range is unchanged by `memory.copy`. -/
theorem Mem.bytes_copy_outside (m : Mem) (dst src len i : Nat)
    (h : i < dst ∨ dst + len ≤ i) :
    (m.copy dst src len).bytes i = m.bytes i := by
  simp only [Mem.copy]
  rw [if_neg (by omega)]

/-- `read8` of a destination byte after `memory.copy` returns the matching
source byte of the pre-copy memory. -/
theorem Mem.read8_copy_inside (m : Mem) (dst src len : Nat) (a : UInt32)
    (h : dst ≤ a.toNat ∧ a.toNat < dst + len) :
    (m.copy dst src len).read8 a = m.bytes (src + (a.toNat - dst)) := by
  simp only [Mem.read8]
  exact Mem.bytes_copy_inside m dst src len a.toNat h

/-- `read8` outside the copied destination range is unchanged. -/
theorem Mem.read8_copy_outside (m : Mem) (dst src len : Nat) (a : UInt32)
    (h : a.toNat < dst ∨ dst + len ≤ a.toNat) :
    (m.copy dst src len).read8 a = m.read8 a := by
  simp only [Mem.read8]
  exact Mem.bytes_copy_outside m dst src len a.toNat h

/-- `read32` outside the copied destination range is unchanged. -/
theorem Mem.read32_copy_outside (m : Mem) (dst src len : Nat) (a : UInt32)
    (h : a.toNat + 4 ≤ dst ∨ dst + len ≤ a.toNat) :
    (m.copy dst src len).read32 a = m.read32 a := by
  simp only [Mem.read32, Mem.copy]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-! ## Disjoint 32-bit store framing

A store to `[b, b+4)` leaves bytes outside that range — and any 8-bit or 32-bit
read disjoint from it — unchanged. (The same-address round-trip is above; these
are the disjoint counterparts, for proofs that write several nearby fields.) -/

/-- A byte outside a 32-bit store is unchanged. -/
theorem Mem.write32_bytes_of_disjoint (m : Mem) (a v : UInt32) (i : Nat)
    (h : i < a.toNat ∨ a.toNat + 4 ≤ i) :
    (m.write32 a v).bytes i = m.bytes i := by
  simp only [Mem.write32]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- `read8` disjoint from a 32-bit store is unchanged. -/
theorem Mem.read8_write32_disjoint (m : Mem) (a b v : UInt32)
    (h : a.toNat < b.toNat ∨ b.toNat + 4 ≤ a.toNat) :
    (m.write32 b v).read8 a = m.read8 a := by
  simp only [Mem.read8]
  exact Mem.write32_bytes_of_disjoint m b v a.toNat h

/-- `read32` disjoint from a 32-bit store is unchanged. -/
theorem Mem.read32_write32_disjoint (m : Mem) (a b v : UInt32)
    (h : a.toNat + 4 ≤ b.toNat ∨ b.toNat + 4 ≤ a.toNat) :
    (m.write32 b v).read32 a = m.read32 a := by
  simp only [Mem.read32]
  rw [Mem.write32_bytes_of_disjoint m b v a.toNat (by omega),
      Mem.write32_bytes_of_disjoint m b v (a.toNat + 1) (by omega),
      Mem.write32_bytes_of_disjoint m b v (a.toNat + 2) (by omega),
      Mem.write32_bytes_of_disjoint m b v (a.toNat + 3) (by omega)]

end Wasm
