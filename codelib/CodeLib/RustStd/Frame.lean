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
* `popcnt64_le` / `popcnt64_lt_2pow32` — `popcnt` fits in 32 bits, so the
  `i32.wrap_i64` after an `i64.popcnt` never truncates.
* `UInt32.toNat_sub_of_le` — frame-pointer arithmetic (`sp - 16`) without
  underflow, needed for the in-bounds (no-trap) obligation.
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

/-! ## `popcnt64` width bound -/

/-- `popcnt64 k a acc` counts at most one extra bit per step. -/
theorem popcnt64_le (k : Nat) (a : UInt64) (acc : Nat) :
    popcnt64 k a acc ≤ k + acc := by
  induction k generalizing a acc with
  | zero => simp [popcnt64]
  | succ k ih =>
    unfold popcnt64
    have h1 : (a &&& 1).toNat ≤ 1 := by
      have : (a &&& 1).toNat = a.toNat % 2 := by
        rw [UInt64.toNat_and]; exact Nat.and_one_is_mod a.toNat
      omega
    have := ih (a >>> 1) (acc + (a &&& 1).toNat)
    omega

theorem popcnt64_lt_2pow32 (a : UInt64) : popcnt64 64 a 0 < 2 ^ 32 := by
  have := popcnt64_le 64 a 0; omega

/-! ## Frame-pointer arithmetic -/

/-- `sp - 16` does not underflow when `16 ≤ sp`. -/
theorem UInt32.toNat_sub_of_le (a b : UInt32) (h : b ≤ a) :
    (a - b).toNat = a.toNat - b.toNat := by
  rw [UInt32.toNat_sub]
  have hle : b.toNat ≤ a.toNat := UInt32.le_iff_toNat_le.mp h
  have hlt : a.toNat < 2 ^ 32 := a.toNat_lt
  have hkey : 2 ^ 32 - b.toNat + a.toNat = 2 ^ 32 + (a.toNat - b.toNat) := by omega
  rw [hkey, Nat.add_mod_left]
  exact Nat.mod_eq_of_lt (by omega)

end Wasm
