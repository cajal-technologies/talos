import CodeLib.RustStd.Region

/-!
# `CodeLib.RustStd.MemArray`

A `List UInt64` *view* of a `u64` array in linear memory (issue #68, spec
readability). `Mem.words64 base n` is the length-`n` list of words at
`base, base+8, …, base+8(n−1)`, so a spec can say `m.words64 base n = vs`
instead of `∀ k < n, m.read64 (base + 8*k) = vs[k]`.

The view is defined via `List.range`/`map`, so its length is a `simp`-lemma
(`length_words64`) and indexing rewrites through `getElem_words64` (kept off
`simp` because of its bounds side-goal). Its interaction with `write64` factors
through the `MemRegion` framing algebra: a write disjoint from the array leaves
the view unchanged (`words64_write64_outside`), and writing `v` to the next slot
past a `v`-filled prefix extends the fill by one (`words64_write64_extend`).
-/

namespace Wasm

/-- The `List UInt64` view of the `u64` array `[base, base + 8*n)`. -/
def Mem.words64 (m : Mem) (base : UInt32) (n : Nat) : List UInt64 :=
  (List.range n).map fun k => m.read64 (base + 8 * (UInt32.ofNat k))

@[simp] theorem Mem.length_words64 (m : Mem) (base : UInt32) (n : Nat) :
    (m.words64 base n).length = n := by
  simp [Mem.words64]

theorem Mem.getElem_words64 (m : Mem) (base : UInt32) (n k : Nat) (h : k < n) :
    (m.words64 base n)[k]'(by simpa using h) = m.read64 (base + 8 * UInt32.ofNat k) := by
  simp [Mem.words64]

/-- Two array views agree iff their words agree pointwise. -/
theorem Mem.words64_ext {m m' : Mem} {base : UInt32} {n : Nat}
    (h : ∀ k < n, m.read64 (base + 8 * UInt32.ofNat k) = m'.read64 (base + 8 * UInt32.ofNat k)) :
    m.words64 base n = m'.words64 base n := by
  apply List.ext_getElem (by simp)
  intro k hk _
  simp only [length_words64] at hk
  rw [getElem_words64 m base n k hk, getElem_words64 m' base n k hk, h k hk]

/-- The wasm address of the `k`-th `u64` slot, `base + 8 * k`, is the integer
`base.toNat + 8 * k` as long as it does not wrap. Shared address bridge for the
framing lemmas below (and their loop consumers). -/
theorem Mem.words64_slotAddr_toNat (base : UInt32) (k : Nat)
    (h : base.toNat + 8 * k < 4294967296) :
    (base + 8 * UInt32.ofNat k).toNat = base.toNat + 8 * k := by
  have hsize : (UInt32.size : Nat) = 4294967296 := rfl
  have hkn : (UInt32.ofNat k).toNat = k :=
    UInt32.toNat_ofNat_of_lt' (by omega : k < UInt32.size)
  have := MemRegion.slot64_base_toNat base (UInt32.ofNat k) (by rw [hkn]; omega)
  rw [hkn] at this; exact this

/-- Under no address wraparound, a `write64` whose target slot `j` is `≥ n`
(i.e. outside the array `[base, base+8n)`) leaves the view unchanged. -/
theorem Mem.words64_write64_outside (m : Mem) (base : UInt32) (n : Nat) (a : UInt32) (v : UInt64)
    (hbnd : base.toNat + 8 * n ≤ 4294967296)
    (hout : a.toNat + 8 ≤ base.toNat ∨ base.toNat + 8 * n ≤ a.toNat) :
    (m.write64 a v).words64 base n = m.words64 base n := by
  apply words64_ext
  intro k hk
  have haddr := Mem.words64_slotAddr_toNat base k (by omega)
  exact Mem.read64_write64_disjoint m a _ v (by rw [haddr]; omega)

/-- One more word: `words64 base (n+1)` is `words64 base n` with the `n`-th
word appended. -/
theorem Mem.words64_succ (m : Mem) (base : UInt32) (n : Nat) :
    m.words64 base (n + 1) = m.words64 base n ++ [m.read64 (base + 8 * UInt32.ofNat n)] := by
  simp [Mem.words64, List.range_succ, List.map_append]

/-- Writing the `n`-th slot with `w` appends `w` to the length-`n` view (the
earlier words are framed away). The store-into-a-fresh-slot step shared by
copy/fill loops over a `u64` array; the 64-bit twin of
`Mem.words32_write32_snoc`. -/
theorem Mem.words64_write64_snoc (m : Mem) (base : UInt32) (n : Nat) (w : UInt64)
    (hbnd : base.toNat + 8 * (n + 1) ≤ 4294967296) :
    (m.write64 (base + 8 * UInt32.ofNat n) w).words64 base (n + 1)
      = m.words64 base n ++ [w] := by
  have haddr := Mem.words64_slotAddr_toNat base n (by omega)
  rw [Mem.words64_succ,
      Mem.words64_write64_outside m base n _ w (by omega) (Or.inr (by rw [haddr])),
      Mem.read64_write64_same]

/-- The fill step, as a view equation: if the first `n` words are already `v`
and slot `n` is written with `v`, the first `n+1` words are `v`. This is the
loop invariant's inductive step; the `replicate`-specialised corollary of
`Mem.words64_write64_snoc`. -/
theorem Mem.words64_write64_extend (m : Mem) (base : UInt32) (n : Nat) (v : UInt64)
    (hbnd : base.toNat + 8 * (n + 1) ≤ 4294967296)
    (hfill : m.words64 base n = List.replicate n v) :
    (m.write64 (base + 8 * UInt32.ofNat n) v).words64 base (n + 1) = List.replicate (n + 1) v := by
  rw [Mem.words64_write64_snoc m base n v hbnd, hfill, List.replicate_succ']

/-! ## 32-bit twin

`Mem.words32` is the `u32` array view, matching the element stride of
`MemRegion.slot32` (and of the `wordsAt` view carried by the merge_sort work
in PR #106, so that file can become an import — `wordsAt` is not in-tree yet). -/

/-- The `List UInt32` view of the `u32` array `[base, base + 4*n)`. -/
def Mem.words32 (m : Mem) (base : UInt32) (n : Nat) : List UInt32 :=
  (List.range n).map fun k => m.read32 (base + 4 * (UInt32.ofNat k))

@[simp] theorem Mem.length_words32 (m : Mem) (base : UInt32) (n : Nat) :
    (m.words32 base n).length = n := by
  simp [Mem.words32]

theorem Mem.getElem_words32 (m : Mem) (base : UInt32) (n k : Nat) (h : k < n) :
    (m.words32 base n)[k]'(by simpa using h) = m.read32 (base + 4 * UInt32.ofNat k) := by
  simp [Mem.words32]

/-- Two `u32` array views agree iff their words agree pointwise. -/
theorem Mem.words32_ext {m m' : Mem} {base : UInt32} {n : Nat}
    (h : ∀ k < n, m.read32 (base + 4 * UInt32.ofNat k) = m'.read32 (base + 4 * UInt32.ofNat k)) :
    m.words32 base n = m'.words32 base n := by
  apply List.ext_getElem (by simp)
  intro k hk _
  simp only [length_words32] at hk
  rw [getElem_words32 m base n k hk, getElem_words32 m' base n k hk, h k hk]

/-- The wasm address of the `k`-th `u32` slot, `base + 4 * k`, is the integer
`base.toNat + 4 * k` as long as it does not wrap. Shared address bridge for the
framing lemmas below (and their loop consumers); the 32-bit twin of
`Mem.words64_slotAddr_toNat`. -/
theorem Mem.words32_slotAddr_toNat (base : UInt32) (k : Nat)
    (h : base.toNat + 4 * k < 4294967296) :
    (base + 4 * UInt32.ofNat k).toNat = base.toNat + 4 * k := by
  have hsize : (UInt32.size : Nat) = 4294967296 := rfl
  have hkn : (UInt32.ofNat k).toNat = k :=
    UInt32.toNat_ofNat_of_lt' (by omega : k < UInt32.size)
  have := MemRegion.slot32_base_toNat base (UInt32.ofNat k) (by rw [hkn]; omega)
  rw [hkn] at this; exact this

/-- A `write32` disjoint from the whole `[base, base+4n)` region leaves the
view unchanged. -/
theorem Mem.words32_write32_outside (m : Mem) (base : UInt32) (n : Nat) (a v : UInt32)
    (hbnd : base.toNat + 4 * n ≤ 4294967296)
    (hout : a.toNat + 4 ≤ base.toNat ∨ base.toNat + 4 * n ≤ a.toNat) :
    (m.write32 a v).words32 base n = m.words32 base n := by
  apply words32_ext
  intro k hk
  have haddr := Mem.words32_slotAddr_toNat base k (by omega)
  exact Mem.read32_write32_disjoint m a _ v (by rw [haddr]; omega)

/-- One more word: `words32 base (n+1)` is `words32 base n` with the `n`-th
word appended. -/
theorem Mem.words32_succ (m : Mem) (base : UInt32) (n : Nat) :
    m.words32 base (n + 1) = m.words32 base n ++ [m.read32 (base + 4 * UInt32.ofNat n)] := by
  simp [Mem.words32, List.range_succ, List.map_append]

/-- Writing the `n`-th slot with `w` appends `w` to the length-`n` view (the
earlier words are framed away). The store-into-a-fresh-slot step shared by
copy/fill loops over a `u32` array. -/
theorem Mem.words32_write32_snoc (m : Mem) (base : UInt32) (n : Nat) (w : UInt32)
    (hbnd : base.toNat + 4 * (n + 1) ≤ 4294967296) :
    (m.write32 (base + 4 * UInt32.ofNat n) w).words32 base (n + 1)
      = m.words32 base n ++ [w] := by
  have haddr := Mem.words32_slotAddr_toNat base n (by omega)
  rw [Mem.words32_succ,
      Mem.words32_write32_outside m base n _ w (by omega) (Or.inr (by rw [haddr])),
      Mem.read32_write32_same]
