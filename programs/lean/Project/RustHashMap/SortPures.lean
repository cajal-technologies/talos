import Project.RustHashMap.SortContracts
import CodeLib.RustStd.HashMap.CapacityClz
import CodeLib.RustStd.HashMap.SipHoist

/-!
# The pure lemmas of the compiled pair sort

The five bodies of the sort group read and write the entry buffer with
`i64` moves, and they compute their recursion limit with `i32.clz`.  A
body proof must turn each compiled form into a statement about the pure
model.  This module proves those steps once.  Nothing here mentions Wasm
state, and no proof uses a weakest-precondition rule.

There are four groups.

* The word of one entry.  Absolute `func 15` writes a pair back as one
  `i64.store` of `(value <<< 32) ||| key`, at WAT 2927 to 2934.
  `pairWord_eq_shl_or` says that this word is `Table.pairWord`, and
  `pairWord_key` and `pairWord_value` read the two halves back.
* The recursion limit.  Absolute `func 14` computes
  `((len ||| 1).clz <<< 1) ^^^ 62` at WAT 2836 to 2845.
  `sortLimit_of_wasm` says that this is `SortContracts.sortLimit`.
* The reverse loop.  Absolute `func 14` reverses a descending run in
  place with one exchange per index pair.  `reverse_eq_foldl_swapAt`
  says that the exchanges make `List.reverse`.
* The scan lemmas.  A loop that compares neighbours gives one fact per
  index pair.  `sortedByKey_of_ascending` and `descending_of_scan` turn
  such a fact into `List.Pairwise`, and the `keyAt` lemmas read a key
  off an exchange.

The heap theorems and `bimerge_exhausts` are not here.  They belong to
the body proofs that need them.
-/

namespace Project.RustHashMap.SortPures

open Wasm.RustStd.HashMap
open Wasm (WordCodec clz32)
open Project.RustHashMap.SortModels

/-! ## The word of one entry -/

/-- The four bytes of a key hold the key. -/
private theorem bytesVal_encodeU32 (k : UInt32) :
    Table.bytesVal (WordCodec.encodeU32 k) = k.toNat := by
  rw [← Table.toNat_u64OfBytesLE _ (by simp [WordCodec.encodeU32]),
    SipHash.u64OfBytesLE_encodeU32, UInt32.toNat_toUInt64]

/-- The key bytes and then the value bytes make one eight-byte value. -/
private theorem bytesVal_encode_append (k v : UInt32) :
    Table.bytesVal (WordCodec.encodeU32 k ++ WordCodec.encodeU32 v) =
      Table.bytesVal (WordCodec.encodeU32 k) +
        2 ^ 32 * Table.bytesVal (WordCodec.encodeU32 v) := by
  simp only [WordCodec.encodeU32, List.cons_append, List.nil_append,
    Table.bytesVal]
  ring

/-- The number that the entry word holds.  The key is in the low half
and the value is in the high half. -/
theorem pairWord_toNat (k v : UInt32) :
    (Table.pairWord (k, v)).toNat = k.toNat + 2 ^ 32 * v.toNat := by
  simp only [Table.pairWord, Table.groupWord]
  rw [Table.toNat_u64OfBytesLE _ (by simp [WordCodec.encodeU32]),
    bytesVal_encode_append, bytesVal_encodeU32, bytesVal_encodeU32]

/-- The compiled form of the entry word.  Absolute `func 15` builds it
with `i64.extend_i32_u`, `i64.shl` and `i64.or`. -/
theorem pairWord_eq_shl_or (k v : UInt32) :
    Table.pairWord (k, v) = v.toUInt64 <<< 32 ||| k.toUInt64 := by
  have hk : k.toNat < 2 ^ 32 := UInt32.toNat_lt k
  have hv : v.toNat < 2 ^ 32 := UInt32.toNat_lt v
  have hfit : v.toNat * 2 ^ 32 < 2 ^ 64 := by omega
  apply UInt64.toNat_inj.mp
  rw [pairWord_toNat, UInt64.toNat_or, UInt64.toNat_shiftLeft,
    UInt32.toNat_toUInt64, UInt32.toNat_toUInt64,
    show ((32 : UInt64).toNat % 64) = 32 from rfl, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt hfit, Nat.mul_comm v.toNat (2 ^ 32),
    Nat.add_comm k.toNat (2 ^ 32 * v.toNat)]
  exact Nat.two_pow_add_eq_or_of_lt hk _

/-- The low half of the entry word is the key.  Absolute `func 15` reads
it with `i32.wrap_i64`. -/
theorem pairWord_key (k v : UInt32) :
    (Table.pairWord (k, v)).toUInt32 = k := by
  have hk : k.toNat < 2 ^ 32 := UInt32.toNat_lt k
  apply UInt32.toNat_inj.mp
  rw [UInt64.toNat_toUInt32, pairWord_toNat, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt hk]

/-- The high half of the entry word is the value. -/
theorem pairWord_value (k v : UInt32) :
    (Table.pairWord (k, v) >>> 32).toUInt32 = v := by
  have hk : k.toNat < 2 ^ 32 := UInt32.toNat_lt k
  have hv : v.toNat < 2 ^ 32 := UInt32.toNat_lt v
  apply UInt32.toNat_inj.mp
  rw [UInt64.toNat_toUInt32, UInt64.toNat_shiftRight,
    show ((32 : UInt64).toNat % 64) = 32 from rfl, pairWord_toNat,
    Nat.shiftRight_eq_div_pow,
    Nat.add_mul_div_left _ _ (Nat.two_pow_pos 32),
    Nat.div_eq_of_lt hk, Nat.zero_add, Nat.mod_eq_of_lt hv]

/-! ## The recursion limit of the sort -/

/-- The exclusive-or form of the limit, on the index range that the
`clz` bound allows. -/
private theorem xor_shift_limit :
    ∀ j, j < 28 → ((31 - j) * 2) ^^^ 62 = 2 * j := by
  decide

/-- The compiled recursion limit is `SortContracts.sortLimit`.  Absolute
`func 14` computes `((len ||| 1).clz <<< 1) ^^^ 62`, and the interpreter
gives `clz` the value `UInt32.ofNat (clz32 32 value)`. -/
theorem sortLimit_of_wasm (len : UInt32) (hlen : len.toNat ≤ 2 ^ 27) :
    (UInt32.ofNat (clz32 32 (len ||| 1)) <<< 1) ^^^ 62 =
      UInt32.ofNat (SortContracts.sortLimit len.toNat) := by
  have hor : (len ||| 1).toNat = len.toNat ||| 1 := by
    rw [UInt32.toNat_or, show ((1 : UInt32).toNat) = 1 from rfl]
  have hne : len.toNat ||| 1 ≠ 0 := by
    intro hzero
    have hbit := Nat.testBit_lor len.toNat 1 0
    simp [hzero] at hbit
  have hlt28 : len.toNat ||| 1 < 2 ^ 28 := by
    refine Nat.or_lt_two_pow ?_ ?_ <;> omega
  have hmlt : Nat.log2 (len.toNat ||| 1) < 28 := (Nat.log2_lt hne).2 hlt28
  have hlow : 2 ^ Nat.log2 (len.toNat ||| 1) ≤ (len ||| 1).toNat := by
    rw [hor]
    exact (Nat.le_log2 hne).1 (Nat.le_refl _)
  have hhigh : (len ||| 1).toNat < 2 ^ (Nat.log2 (len.toNat ||| 1) + 1) := by
    rw [hor]
    exact (Nat.log2_lt hne).1 (Nat.lt_succ_self _)
  have hclz : clz32 32 (len ||| 1) = 31 - Nat.log2 (len.toNat ||| 1) :=
    Table.clz32_eq (by omega) hlow hhigh
  have hlimit : SortContracts.sortLimit len.toNat
      = 2 * Nat.log2 (len.toNat ||| 1) := rfl
  rw [hclz, hlimit]
  apply UInt32.toNat_inj.mp
  simp only [UInt32.toNat_xor, UInt32.toNat_shiftLeft, UInt32.toNat_ofNat,
    Nat.shiftLeft_eq]
  norm_num
  revert hmlt
  generalize (len.toNat ||| 1).log2 = j
  intro hj
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  exact xor_shift_limit j hj

/-! ## The reverse loop -/

/-- The list that the first `k` exchanges of the reverse loop make.
Absolute `func 14` exchanges entry `i` with entry `len - 1 - i`. -/
def reverseFold (ps : List (UInt32 × UInt32)) (k : Nat) :
    List (UInt32 × UInt32) :=
  (List.range k).foldl
    (fun acc i => Table.swapAt acc i (ps.length - 1 - i)) ps

theorem reverseFold_zero (ps : List (UInt32 × UInt32)) :
    reverseFold ps 0 = ps := rfl

theorem reverseFold_succ (ps : List (UInt32 × UInt32)) (k : Nat) :
    reverseFold ps (k + 1) =
      Table.swapAt (reverseFold ps k) k (ps.length - 1 - k) := by
  simp [reverseFold, List.range_succ]

@[simp] theorem reverseFold_length (ps : List (UInt32 × UInt32))
    (k : Nat) : (reverseFold ps k).length = ps.length := by
  induction k with
  | zero => rfl
  | succ k ih => rw [reverseFold_succ, Table.swapAt_length, ih]

/-- What the reverse loop holds after `k` exchanges.  The first `k`
entries and the last `k` entries are already turned round, and the
middle keeps the input order. -/
theorem reverseFold_getElem? (ps : List (UInt32 × UInt32)) :
    ∀ k, k ≤ ps.length / 2 → ∀ i, i < ps.length →
      (reverseFold ps k)[i]? =
        if i < k ∨ ps.length - k ≤ i then ps[ps.length - 1 - i]?
        else ps[i]? := by
  intro k
  induction k with
  | zero =>
    intro _ i hi
    rw [reverseFold_zero, if_neg (by omega)]
  | succ k ih =>
    intro hk i hi
    have hlen : (reverseFold ps k).length = ps.length :=
      reverseFold_length ps k
    have hikL : k < (reverseFold ps k).length := by omega
    have hjkL : ps.length - 1 - k < (reverseFold ps k).length := by omega
    rw [reverseFold_succ]
    by_cases hik : i = k
    · subst hik
      rw [Table.swapAt_getElem?_left _ hikL hjkL,
        ih (by omega) _ (by omega), if_neg (by omega), if_pos (by omega)]
    · by_cases hij : i = ps.length - 1 - k
      · subst hij
        rw [Table.swapAt_getElem?_right _ hikL hjkL,
          ih (by omega) _ (by omega), if_neg (by omega), if_pos (by omega)]
        congr 1
        omega
      · rw [Table.swapAt_getElem?_other _ hik hij, ih (by omega) _ hi]
        have hcond : (i < k ∨ ps.length - k ≤ i) ↔
            (i < k + 1 ∨ ps.length - (k + 1) ≤ i) := by
          constructor <;> intro h <;> omega
        simp only [hcond]

/-- The whole reverse loop turns the list round. -/
theorem reverseFold_half (ps : List (UInt32 × UInt32)) :
    reverseFold ps (ps.length / 2) = ps.reverse := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < ps.length
  · rw [reverseFold_getElem? ps _ (Nat.le_refl _) i hi,
      List.getElem?_reverse hi]
    by_cases hcond : i < ps.length / 2 ∨ ps.length - ps.length / 2 ≤ i
    · rw [if_pos hcond]
    · rw [if_neg hcond]
      congr 1
      omega
  · rw [List.getElem?_eq_none (by simp; omega),
      List.getElem?_eq_none (by simp; omega)]

/-- The reverse loop of absolute `func 14`, as the exchanges that the
compiled body makes.  The body unrolls the loop by two, and it makes one
more exchange in the middle when the length is odd; both forms fold to
this one. -/
theorem reverse_eq_foldl_swapAt (ps : List (UInt32 × UInt32)) :
    (List.range (ps.length / 2)).foldl
        (fun acc i => Table.swapAt acc i (ps.length - 1 - i)) ps
      = ps.reverse :=
  reverseFold_half ps

/-- An exchange of an entry with itself changes nothing. -/
theorem swapAt_self (ps : List (UInt32 × UInt32)) {i : Nat}
    (hi : i < ps.length) : Table.swapAt ps i i = ps := by
  rw [Table.swapAt_eq_set_set ps hi hi]
  simp

/-! ## The keys of a list and of an exchange -/

theorem keyAt_eq_getElem (ps : List (UInt32 × UInt32)) {i : Nat}
    (hi : i < ps.length) : keyAt ps i = ps[i].1 := by
  rw [keyAt, List.getD_eq_getElem _ _ hi]

theorem keyAt_eq_getElem? (ps : List (UInt32 × UInt32)) (i : Nat) :
    keyAt ps i = (ps[i]?.getD (0, 0)).1 := by
  rw [keyAt, List.getD_eq_getElem?_getD]

theorem keyAt_swapAt_left (ps : List (UInt32 × UInt32)) {i j : Nat}
    (hi : i < ps.length) (hj : j < ps.length) :
    keyAt (Table.swapAt ps i j) i = keyAt ps j := by
  rw [keyAt_eq_getElem?, keyAt_eq_getElem?,
    Table.swapAt_getElem?_left ps hi hj]

theorem keyAt_swapAt_right (ps : List (UInt32 × UInt32)) {i j : Nat}
    (hi : i < ps.length) (hj : j < ps.length) :
    keyAt (Table.swapAt ps i j) j = keyAt ps i := by
  rw [keyAt_eq_getElem?, keyAt_eq_getElem?,
    Table.swapAt_getElem?_right ps hi hj]

theorem keyAt_swapAt_other (ps : List (UInt32 × UInt32)) {i j k : Nat}
    (hki : k ≠ i) (hkj : k ≠ j) :
    keyAt (Table.swapAt ps i j) k = keyAt ps k := by
  rw [keyAt_eq_getElem?, keyAt_eq_getElem?,
    Table.swapAt_getElem?_other ps hki hkj]

/-! ## The two scans -/

/-- A neighbour fact that holds at every index gives the whole order,
when the relation is transitive. -/
private theorem pairwise_of_adjacent {R : UInt32 → UInt32 → Prop}
    (htrans : ∀ a b c, R a b → R b c → R a c)
    (ps : List (UInt32 × UInt32))
    (h : ∀ i, i + 1 < ps.length → R (keyAt ps i) (keyAt ps (i + 1))) :
    ps.Pairwise (fun a b => R a.1 b.1) := by
  have hstep : ∀ d i, i + (d + 1) < ps.length →
      R (keyAt ps i) (keyAt ps (i + (d + 1))) := by
    intro d
    induction d with
    | zero => intro i hi; simpa using h i (by omega)
    | succ d ih =>
      intro i hi
      have hmid := ih i (by omega)
      have hnext := h (i + (d + 1)) (by omega)
      have heq : i + (d + 1 + 1) = i + (d + 1) + 1 := by omega
      rw [heq]
      exact htrans _ _ _ hmid hnext
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  have hd := hstep (j - i - 1) i (by omega)
  rw [show i + (j - i - 1 + 1) = j from by omega] at hd
  rw [keyAt_eq_getElem ps hi, keyAt_eq_getElem ps hj] at hd
  exact hd

/-- The ascending scan.  The loop of absolute `func 14` walks forward
while each key is at least the key below it. -/
theorem sortedByKey_of_ascending (ps : List (UInt32 × UInt32))
    (h : ∀ i, i + 1 < ps.length → keyAt ps i ≤ keyAt ps (i + 1)) :
    Table.SortedByKey ps :=
  pairwise_of_adjacent (R := fun a b => a ≤ b)
    (fun _ _ _ hab hbc => UInt32.le_trans hab hbc) ps h

/-- The descending scan.  The exit test of the loop is `i32.ge_u`, so
the scan goes on only while the next key is below the key above it. -/
theorem descending_of_scan (ps : List (UInt32 × UInt32))
    (h : ∀ i, i + 1 < ps.length → keyAt ps (i + 1) < keyAt ps i) :
    ps.Pairwise (fun a b => b.1 < a.1) :=
  pairwise_of_adjacent (R := fun a b => b < a)
    (fun _ _ _ hab hbc => UInt32.lt_trans hbc hab) ps h

/-- A descending run is in key order after the reverse loop. -/
theorem sortedByKey_reverse_of_scan (ps : List (UInt32 × UInt32))
    (h : ∀ i, i + 1 < ps.length → keyAt ps (i + 1) < keyAt ps i) :
    Table.SortedByKey ps.reverse :=
  Table.sortedByKey_reverse_of_desc (descending_of_scan ps h)

end Project.RustHashMap.SortPures
