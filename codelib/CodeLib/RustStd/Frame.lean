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

/-- Reading a 64-bit word from a range disjoint from a preceding `write64`
returns the original (pre-write) value. The companion to
`read64_write64_same` for multi-spill frames (`min`/`max`) that store two
operands at adjacent 8-byte slots. -/
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

/-! ## Stores preserve the page count -/

@[simp] theorem Mem.write32_pages (m : Mem) (a v : UInt32) :
    (m.write32 a v).pages = m.pages := rfl

@[simp] theorem Mem.write64_pages (m : Mem) (a : UInt32) (v : UInt64) :
    (m.write64 a v).pages = m.pages := rfl

end Wasm
