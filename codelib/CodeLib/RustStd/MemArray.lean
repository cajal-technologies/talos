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

/-- The fill step, as a view equation: if the first `n` words are already `v`
and slot `n` is written with `v`, the first `n+1` words are `v`. This is the
loop invariant's inductive step, discharged once here. -/
theorem Mem.words64_write64_extend (m : Mem) (base : UInt32) (n : Nat) (v : UInt64)
    (hbnd : base.toNat + 8 * (n + 1) ≤ 4294967296)
    (hfill : m.words64 base n = List.replicate n v) :
    (m.write64 (base + 8 * UInt32.ofNat n) v).words64 base (n + 1) = List.replicate (n + 1) v := by
  have haddr := Mem.words64_slotAddr_toNat base n (by omega)
  rw [Mem.words64_succ,
      Mem.words64_write64_outside m base n _ v (by omega) (Or.inr (by rw [haddr])),
      hfill, Mem.read64_write64_same, List.replicate_succ']
