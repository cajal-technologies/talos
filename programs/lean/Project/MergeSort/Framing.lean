import Project.MergeSort.Spec

/-!
# Phase A — memory-region framing for `wordsAt`

Foundational, wasm-free lemmas used by every later phase of the `merge_sort`
proof: reading a `u32` word back from a region that a disjoint store did not
touch, and the list-level version for `wordsAt`.

`Mem.read32_write32_same` and the page lemmas already live in
`CodeLib.RustStd.Frame`; what is missing — and added here — is the *disjoint*
case, plus the `wordsAt` wrappers.
-/

namespace Project.MergeSort.Framing

open Wasm Project.MergeSort.Spec

/-- A single byte survives a `write32` whose 4-byte footprint does not cover
it. -/
theorem Mem.read8_write32_of_ne (m : Mem) (a v : UInt32) (j : Nat)
    (h : j < a.toNat ∨ a.toNat + 3 < j) :
    (m.write32 a v).bytes j = m.bytes j := by
  simp only [Mem.write32]
  split_ifs <;> first | rfl | omega

/-- Reading a `u32` word back from an address whose 4-byte footprint is
disjoint from a `write32` returns the original value. -/
theorem Mem.read32_write32_of_disjoint (m : Mem) (a b v : UInt32)
    (h : a.toNat + 4 ≤ b.toNat ∨ b.toNat + 4 ≤ a.toNat) :
    (m.write32 a v).read32 b = m.read32 b := by
  simp only [Mem.read32]
  rw [Mem.read8_write32_of_ne m a v b.toNat (by omega),
      Mem.read8_write32_of_ne m a v (b.toNat + 1) (by omega),
      Mem.read8_write32_of_ne m a v (b.toNat + 2) (by omega),
      Mem.read8_write32_of_ne m a v (b.toNat + 3) (by omega)]

/-- `wordsAt` always has exactly `n` elements. -/
@[simp] theorem wordsAt_length (m : Mem) (base : UInt32) (n : Nat) :
    (wordsAt m base n).length = n := by
  simp [wordsAt]

/-- The `i`-th word of `wordsAt` is the `read32` at `base + 4*i`. -/
theorem wordsAt_getElem (m : Mem) (base : UInt32) (n i : Nat) (hi : i < n) :
    (wordsAt m base n)[i]'(by simp [wordsAt_length]; omega)
      = m.read32 (base + 4 * UInt32.ofNat i) := by
  simp [wordsAt]

/-- The byte address of the `i`-th word, with the `UInt32` wraparound removed
under a no-overflow bound on the whole region. -/
theorem toNat_wordAddr (base : UInt32) (n i : Nat)
    (hi : i < n) (hub : base.toNat + 4 * n ≤ 4294967296) :
    (base + 4 * UInt32.ofNat i).toNat = base.toNat + 4 * i := by
  simp only [UInt32.toNat_add, UInt32.toNat_mul, UInt32.toNat_ofNat,
    UInt32.toNat_ofNat']
  omega

/-- Region-level framing: a `write32` whose footprint is disjoint from the
whole `[base, base + 4*n)` region leaves every word of `wordsAt` untouched. -/
theorem wordsAt_write32_of_disjoint (m : Mem) (base a v : UInt32) (n : Nat)
    (hub : base.toNat + 4 * n ≤ 4294967296)
    (hdis : a.toNat + 4 ≤ base.toNat ∨ base.toNat + 4 * n ≤ a.toNat) :
    wordsAt (m.write32 a v) base n = wordsAt m base n := by
  simp only [wordsAt]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  rw [Mem.read32_write32_of_disjoint m a (base + 4 * UInt32.ofNat i) v
      (by rw [toNat_wordAddr base n i hi hub]; omega)]

/-- `read32` depends only on the four bytes it reads. -/
theorem Mem.read32_congr (m m' : Mem) (a : UInt32)
    (h0 : m'.bytes a.toNat = m.bytes a.toNat)
    (h1 : m'.bytes (a.toNat + 1) = m.bytes (a.toNat + 1))
    (h2 : m'.bytes (a.toNat + 2) = m.bytes (a.toNat + 2))
    (h3 : m'.bytes (a.toNat + 3) = m.bytes (a.toNat + 3)) :
    m'.read32 a = m.read32 a := by
  simp only [Mem.read32, h0, h1, h2, h3]

/-- Byte-agreement bridge: if `m'` matches `m` on every byte of the region
`[base, base + 4*n)`, then `wordsAt` agrees there. This converts the
byte-level effect/frame of a wasm function into the `wordsAt` view. -/
theorem wordsAt_congr_of_bytes (m m' : Mem) (base : UInt32) (n : Nat)
    (hub : base.toNat + 4 * n ≤ 4294967296)
    (h : ∀ i, base.toNat ≤ i → i < base.toNat + 4 * n → m'.bytes i = m.bytes i) :
    wordsAt m' base n = wordsAt m base n := by
  simp only [wordsAt]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  have ha : (base + 4 * UInt32.ofNat i).toNat = base.toNat + 4 * i :=
    toNat_wordAddr base n i hi hub
  apply Mem.read32_congr <;> rw [ha] <;> apply h <;> omega

/-! ## 64-bit ↔ 32-bit store/load bridges

The opt-0 codegen shuffles slice descriptors through 64-bit `load`/`store`
pairs. These bridges turn each 64-bit access into the two adjacent 32-bit
words, so the `read32`/`write32` framing lemmas above carry through. -/

/-- A 64-bit store is two adjacent 32-bit stores (low word first), provided the
8-byte footprint does not wrap the 32-bit address space. -/
theorem Mem.write64_eq_write32 (m : Mem) (a : UInt32) (v : UInt64)
    (h : a.toNat + 8 ≤ 4294967296) :
    m.write64 a v = (m.write32 a v.toUInt32).write32 (a + 4) (v >>> 32).toUInt32 := by
  have ha4 : (a + 4).toNat = a.toNat + 4 := by
    rw [UInt32.toNat_add, show (4 : UInt32).toNat = 4 from rfl]; omega
  simp only [Mem.write64, Mem.write32]
  congr 1
  funext i
  simp only [ha4]
  split_ifs <;> first | omega | bv_decide

/-- The low 32 bits of a 64-bit load are the 32-bit load at the same address. -/
theorem Mem.read64_toUInt32 (m : Mem) (a : UInt32) :
    (m.read64 a).toUInt32 = m.read32 a := by
  simp only [Mem.read64, Mem.read32]
  bv_decide

/-- The high 32 bits of a 64-bit load are the 32-bit load four bytes up. -/
theorem Mem.read64_shiftRight32_toUInt32 (m : Mem) (a : UInt32)
    (h : a.toNat + 8 ≤ 4294967296) :
    (m.read64 a >>> 32).toUInt32 = m.read32 (a + 4) := by
  have ha4 : (a + 4).toNat = a.toNat + 4 := by
    rw [UInt32.toNat_add, show (4 : UInt32).toNat = 4 from rfl]; omega
  simp only [Mem.read64, Mem.read32, ha4,
    show a.toNat + 4 + 1 = a.toNat + 5 from rfl,
    show a.toNat + 4 + 2 = a.toNat + 6 from rfl,
    show a.toNat + 4 + 3 = a.toNat + 7 from rfl]
  bv_decide

end Project.MergeSort.Framing
