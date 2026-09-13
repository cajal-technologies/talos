import CodeLib.RustStd.HashMap.ProbeWasm
import CodeLib.RustStd.HashMap.ResizeWalk

/-!
# The bit counts, the wrap and the sizing bound that `erase` needs

The compiled remove kernel, which is `Table.erase` in the model, and the
walk over the sorted entries need six pure facts that no module has.
This file proves them.

* `trailingClear_eq_ctz` and `leadingClear_eq_clz` read the two byte
  counts of `BitMask` as the `i64.ctz` and the `i64.clz` of the
  interpreter, divided by eight.  `ProbeWasm.lowestSetByte_eq_ctz`
  covers a non-zero mask only.  These two lemmas also cover the empty
  mask, where both sides are eight.  `clz64_eq` is the specification of
  the interpreter's `clz64`, which no file had.  It mirrors
  `ProbeWasm.ctz64_eq`, and it carries one more hypothesis: the fuel
  must still reach bit 63 from the highest set bit.
* `wrapSub_of_wasm` reads `(i - 8) & bucket_mask` on `i32` as the
  `Table.wrapSub` of the model.  `TableMem.and_mask_toNat` gives the
  mask alone.  This lemma adds the wrap of the subtraction, which the
  backward window of `erase` runs into for every `i` below eight.
* `walk_eq_fullIndices_small` is `ResizeWalk.walk_eq_fullIndices` for a
  table with fewer than eight buckets.  The general lemma asks for a
  bucket count that eight divides, and `Shape` also allows one and four.
  A pad byte of such a table is `EMPTY`, so the one group that the walk
  loads reports exactly the full buckets.
* `length_toList_le` bounds the entry count by the bucket count.
* `capBuckets_le_of_le_max` bounds the bucket count of `withCapacity`
  by `2 ^ 27` for every capacity that the check accepts, and
  `bucketMaskToCapacity_pow27` explains the literal 117440512 of that
  check.

The three list lemmas at the top are the shape of `List.takeWhile` over
`List.range n` and over its reverse.  The two byte counts are lengths of
such a `takeWhile`, and the bit lemmas give the one index where the
predicate turns.

No proof in this file uses `native_decide` or `bv_decide`.

## A rule that the body proofs still need

The total-WP rule for `i64.ctz` is `twp_ctzI64` at
`CodeLib/SepLogic/SmallStepTotalLifting.lean:1627`.  There is no
`twp_clzI64`.  `CodeLib/SepLogic/SmallStepTotalLiftingBits.lean:121`
adds `twp_clz`, which names the 32-bit `clz32`.  A body that runs
`i64.clz` therefore needs one more pure rule beside `twp_ctzI64`.
-/

namespace Wasm.RustStd.HashMap.Table

open Wasm

variable {K V : Type}

/-! ## Two lengths of `List.takeWhile` over a range -/

theorem length_takeWhile_range (p : Nat → Bool) :
    ∀ (n c : Nat), c ≤ n → (∀ j, j < c → p j = true) →
      (n ≤ c ∨ p c = false) → ((List.range n).takeWhile p).length = c
  | 0, c, hcn, _, _ => by
      have hc : c = 0 := by omega
      subst hc
      simp
  | n + 1, 0, _, _, hend => by
      have hp : ¬ p 0 = true := by
        rcases hend with h | h
        · omega
        · simp [h]
      rw [List.range_succ_eq_map, List.takeWhile_cons_of_neg hp]
      simp
  | n + 1, c + 1, hcn, hlt, hend => by
      have hp : p 0 = true := hlt 0 (by omega)
      have ih := length_takeWhile_range (fun j => p (j + 1)) n c (by omega)
        (fun j hj => hlt (j + 1) (by omega))
        (by rcases hend with h | h
            · exact Or.inl (by omega)
            · exact Or.inr h)
      rw [List.range_succ_eq_map, List.takeWhile_cons_of_pos hp,
        List.length_cons, List.takeWhile_map, List.length_map]
      rw [show (p ∘ Nat.succ) = (fun j => p (j + 1)) from rfl, ih]

theorem length_takeWhile_reverse_range (p : Nat → Bool) :
    ∀ (n c : Nat), c < n → (∀ j, c < j → j < n → p j = true) → p c = false →
      ((List.range n).reverse.takeWhile p).length = n - 1 - c
  | 0, _, hcn, _, _ => by omega
  | n + 1, c, hcn, hgt, hpc => by
      rw [List.range_succ, List.reverse_append]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append,
        List.cons_append]
      rcases Nat.lt_or_ge c n with hlt | hge
      · rw [List.takeWhile_cons_of_pos (hgt n hlt (by omega)),
          List.length_cons,
          length_takeWhile_reverse_range p n c hlt
            (fun j hj hjn => hgt j hj (by omega)) hpc]
        omega
      · have hcn' : c = n := by omega
        subst hcn'
        rw [List.takeWhile_cons_of_neg (by simp [hpc])]
        simp

theorem length_takeWhile_reverse_range_all (p : Nat → Bool) :
    ∀ n : Nat, (∀ j, j < n → p j = true) →
      ((List.range n).reverse.takeWhile p).length = n
  | 0, _ => by simp
  | n + 1, h => by
      rw [List.range_succ, List.reverse_append]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append,
        List.cons_append]
      rw [List.takeWhile_cons_of_pos (h n (by omega)), List.length_cons,
        length_takeWhile_reverse_range_all p n (fun j hj => h j (by omega))]

/-! ## The two bit counts of the interpreter on a match mask -/

theorem hasBit_zero (j : Nat) : hasBit 0 j = false := by
  unfold hasBit
  rw [show (0 : UInt64).toNat = 0 from rfl, Nat.zero_testBit]

theorem ctz64_zero : ∀ k : Nat, ctz64 k 0 = 64
  | 0 => rfl
  | k + 1 => by
      rw [ctz64, if_neg (by decide), show (0 : UInt64) >>> 1 = 0 from rfl,
        ctz64_zero k]

theorem clz64_zero : ∀ k : Nat, clz64 k 0 = 64
  | 0 => rfl
  | k + 1 => by
      rw [clz64, if_neg (by decide), show (0 : UInt64) <<< 1 = 0 from rfl,
        clz64_zero k]

theorem lowestByte_of_ne_zero {msk : UInt64} (hmask : msk &&& REP80 = msk)
    (hne : msk ≠ 0) :
    ∃ c, c < 8 ∧ hasBit msk c = true ∧ (∀ j, j < c → hasBit msk j = false) ∧
      ctz64 64 msk = 8 * c + 7 := by
  obtain ⟨i, hi⟩ := exists_testBit_of_ne_zero hne
  obtain ⟨i0, hi0, hmin⟩ := exists_lowest_testBit hi
  have hlt : i0 < 64 := by
    by_contra h
    have hz := Nat.testBit_lt_two_pow
      (Nat.lt_of_lt_of_le (UInt64.toNat_lt msk)
        (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_lt h)))
    rw [hz] at hi0
    simp at hi0
  have hseven : i0 % 8 = 7 := testBit_of_mask hmask hi0
  refine ⟨i0 / 8, by omega, ?_, ?_, ?_⟩
  · unfold hasBit
    rw [show 8 * (i0 / 8) + 7 = i0 by omega]
    exact hi0
  · intro j hj
    unfold hasBit
    exact hmin _ (by omega)
  · have hc := ctz64_eq 64 (Nat.le_refl 64) msk i0 hlt hi0 hmin
    omega

/-- `BitMask::trailing_zeros`, which the compiled code reads as
`i64.ctz` divided by eight.  An empty mask gives eight on both sides. -/
theorem trailingClear_eq_ctz {msk : UInt64} (hmask : msk &&& REP80 = msk) :
    trailingClear msk = ctz64 64 msk / 8 := by
  unfold trailingClear
  by_cases hne : msk = 0
  · subst hne
    rw [ctz64_zero]
    exact length_takeWhile_range _ 8 8 (by omega)
      (fun j _ => by rw [hasBit_zero]; rfl) (Or.inl (by omega))
  · obtain ⟨c, hc8, hcb, hlow, hctz⟩ := lowestByte_of_ne_zero hmask hne
    rw [hctz, show (8 * c + 7) / 8 = c by omega]
    exact length_takeWhile_range _ 8 c (by omega)
      (fun j hj => by rw [hlow j hj]; rfl) (Or.inr (by rw [hcb]; rfl))

theorem top_bit_iff (a : UInt64) :
    (a &&& 0x8000000000000000 ≠ 0) ↔ a.toNat.testBit 63 = true := by
  rw [ne_eq, ← UInt64.toNat_inj, UInt64.toNat_and,
    show (0x8000000000000000 : UInt64).toNat = 2 ^ 63 from by decide,
    show (0 : UInt64).toNat = 0 from rfl, Nat.and_two_pow]
  cases a.toNat.testBit 63 <;> simp

theorem testBit_shiftLeft_one (a : UInt64) (j : Nat) :
    (a <<< 1).toNat.testBit j =
      (decide (j < 64) && (decide (j ≥ 1) && a.toNat.testBit (j - 1))) := by
  rw [UInt64.toNat_shiftLeft, show (1 : UInt64).toNat % 64 = 1 from rfl,
    Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft]

/-- The interpreter's `clz64 k a` counts the clear bits above the highest
set bit, offset by the bits already consumed.  The fuel `k` must still
reach bit 63 from bit `i`, which is what `64 ≤ i + k` says. -/
theorem clz64_eq : ∀ (k : Nat), k ≤ 64 → ∀ (a : UInt64) (i : Nat), i < 64 →
    64 ≤ i + k → a.toNat.testBit i = true →
    (∀ j, i < j → a.toNat.testBit j = false) →
    clz64 k a = 64 - k + (63 - i)
  | 0, _, _, _, _, hik, _, _ => absurd hik (by omega)
  | k + 1, hk, a, i, hi, hik, hbit, hmax => by
    by_cases htop : a &&& 0x8000000000000000 ≠ 0
    · rw [clz64, if_pos htop]
      have h63 : a.toNat.testBit 63 = true := (top_bit_iff a).1 htop
      have hie : i = 63 := by
        by_contra hne
        have hf := hmax 63 (by omega)
        rw [h63] at hf
        exact absurd hf (by simp)
      omega
    · rw [clz64, if_neg htop]
      have h63 : a.toNat.testBit 63 = false := by
        cases h : a.toNat.testBit 63 with
        | false => rfl
        | true => exact absurd ((top_bit_iff a).2 h) htop
      have hi63 : i < 63 := by
        rcases Nat.lt_or_ge i 63 with h | h
        · exact h
        · exfalso
          have hie : i = 63 := by omega
          subst hie
          rw [h63] at hbit
          exact absurd hbit (by simp)
      have ih := clz64_eq k (by omega) (a <<< 1) (i + 1) (by omega) (by omega)
        (by rw [testBit_shiftLeft_one, Nat.add_sub_cancel, hbit, Bool.and_true]
            simp only [Bool.and_eq_true, decide_eq_true_eq]
            omega)
        (fun j hj => by
          rw [testBit_shiftLeft_one]
          by_cases hj64 : j < 64
          · have hf := hmax (j - 1) (by omega)
            simp [hf]
          · simp [hj64])
      rw [ih]
      omega

theorem exists_highest_testBit_aux {n : Nat}
    (hn : ∀ j, 64 ≤ j → n.testBit j = false) :
    ∀ (d i : Nat), 64 ≤ i + d → n.testBit i = true →
      ∃ i1, n.testBit i1 = true ∧ ∀ j, i1 < j → n.testBit j = false
  | 0, i, hd, hi => by
      rw [hn i (by omega)] at hi
      simp at hi
  | d + 1, i, hd, hi => by
      by_cases h : ∃ j, i < j ∧ n.testBit j = true
      · obtain ⟨j, hj, hjb⟩ := h
        exact exists_highest_testBit_aux hn d j (by omega) hjb
      · refine ⟨i, hi, fun j hj => ?_⟩
        cases hb : n.testBit j with
        | false => rfl
        | true => exact absurd ⟨j, hj, hb⟩ h

theorem highestByte_of_ne_zero {msk : UInt64} (hmask : msk &&& REP80 = msk)
    (hne : msk ≠ 0) :
    ∃ c, c < 8 ∧ hasBit msk c = true ∧ (∀ j, c < j → hasBit msk j = false) ∧
      clz64 64 msk = 56 - 8 * c := by
  have hhigh : ∀ j, 64 ≤ j → msk.toNat.testBit j = false := fun j hj =>
    Nat.testBit_lt_two_pow
      (Nat.lt_of_lt_of_le (UInt64.toNat_lt msk)
        (Nat.pow_le_pow_right (by decide) hj))
  obtain ⟨i, hi⟩ := exists_testBit_of_ne_zero hne
  obtain ⟨i1, hi1, hmax⟩ := exists_highest_testBit_aux hhigh 64 i (by omega) hi
  have hlt : i1 < 64 := by
    by_contra h
    rw [hhigh i1 (by omega)] at hi1
    simp at hi1
  have hseven : i1 % 8 = 7 := testBit_of_mask hmask hi1
  refine ⟨i1 / 8, by omega, ?_, ?_, ?_⟩
  · unfold hasBit
    rw [show 8 * (i1 / 8) + 7 = i1 by omega]
    exact hi1
  · intro j hj
    unfold hasBit
    exact hmax _ (by omega)
  · have hc := clz64_eq 64 (Nat.le_refl 64) msk i1 hlt (by omega) hi1 hmax
    omega

/-- `BitMask::leading_zeros`, which the compiled code reads as `i64.clz`
divided by eight.  An empty mask gives eight on both sides. -/
theorem leadingClear_eq_clz {msk : UInt64} (hmask : msk &&& REP80 = msk) :
    leadingClear msk = clz64 64 msk / 8 := by
  unfold leadingClear
  by_cases hne : msk = 0
  · subst hne
    rw [clz64_zero]
    exact length_takeWhile_reverse_range_all _ 8
      (fun j _ => by rw [hasBit_zero]; rfl)
  · obtain ⟨c, hc8, hcb, hhigh, hclz⟩ := highestByte_of_ne_zero hmask hne
    rw [hclz, show (56 - 8 * c) / 8 = 7 - c by omega]
    exact length_takeWhile_reverse_range _ 8 c hc8
      (fun j hj _ => by rw [hhigh j hj]; rfl) (by rw [hcb]; rfl)

/-! ## The backward step of the erase window -/

/-- The address the compiled `erase` computes for the group before the
bucket: `i - 8` wraps in 32 bits, and the mask takes it modulo the bucket
count. -/
theorem wrapSub_of_wasm {b i : Nat} (hs : Shape b) (hi : i < b) :
    ((UInt32.ofNat i - 8) &&& UInt32.ofNat (b - 1)).toNat = wrapSub i 8 b := by
  obtain ⟨m, hm, -, rfl⟩ := hs
  have hle : (2 : Nat) ^ m ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) hm
  have hdvd : (2 : Nat) ^ m ∣ 2 ^ 32 := Nat.pow_dvd_pow 2 hm
  unfold wrapSub
  rw [and_mask_toNat _ hm, UInt32.toNat_sub,
    show (8 : UInt32).toNat = 8 from rfl, UInt32.toNat_ofNat',
    Nat.mod_eq_of_lt (show i < 2 ^ 32 by omega), Nat.mod_mod_of_dvd _ hdvd]
  congr 1
  omega

/-! ## The walk of a table with one group -/

/-- The one-group walk of a table with fewer than eight buckets visits
exactly `Table.fullIndices`.  `ResizeWalk.walk_eq_fullIndices` needs a
bucket count that eight divides, and `Shape` also allows one and four. -/
theorem walk_eq_fullIndices_small {hash : K → UInt64} {t : Table K V}
    (hw : Layout hash t) (hb : t.buckets < 8) :
    setBytes (swarMatchFull (groupWord (groupAt t 0))) = fullIndices t := by
  have hpad : ∀ p, t.buckets ≤ p → p < 8 → isFull (t.ctrlAt p) = false := by
    intro p h1 h2
    have hm := hw.mirror p (by omega)
    rw [if_pos (show IsPad t.buckets p from ⟨hb, h1, h2⟩)] at hm
    rw [hm, isFull_EMPTY]
  rw [setBytes_swarMatchFull]
  unfold fullIndices
  simp only [Nat.zero_add]
  have hnil : ((List.range (8 - t.buckets)).map
      (fun x => t.buckets + x)).filter
      (fun j => isFull (t.ctrlAt j)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro a ha
    simp only [List.mem_map, List.mem_range] at ha
    obtain ⟨j, hj, rfl⟩ := ha
    rw [hpad _ (by omega) (by omega)]
    simp
  rw [show 8 = t.buckets + (8 - t.buckets) by omega, List.range_add,
    List.filter_append, hnil, List.append_nil]

/-- A table holds at most one entry for each bucket. -/
theorem length_toList_le {hash : K → UInt64} {t : Table K V}
    (hw : Layout hash t) : (toList t).length ≤ t.buckets := by
  rw [← length_fullIndices hw]
  unfold fullIndices
  calc ((List.range t.buckets).filter
        (fun i => isFull (t.ctrlAt i))).length
      ≤ (List.range t.buckets).length := List.length_filter_le _ _
    _ = t.buckets := List.length_range

/-! ## The largest capacity the sizing accepts -/

/-- The literal bound of the capacity check: the full capacity of the
largest table the sizing builds. -/
theorem bucketMaskToCapacity_pow27 :
    bucketMaskToCapacity (2 ^ 27 - 1) = 117440512 := by decide

/-- A capacity within that bound gives at most `2 ^ 27` buckets. -/
theorem capBuckets_le_of_le_max {n : Nat} (h : n ≤ 117440512) :
    capBuckets n ≤ 2 ^ 27 := by
  have h27 : (2 : Nat) ^ 27 = 134217728 := by norm_num
  have h32 : (2 : Nat) ^ 32 = 4294967296 := by norm_num
  unfold capBuckets
  by_cases h0 : n = 0
  · rw [if_pos h0]
    omega
  · rw [if_neg h0]
    unfold capacityToBuckets
    by_cases h15 : n < 15
    · rw [if_pos h15]
      show (if max 3 n < 4 then 4 else if max 3 n < 8 then 8 else 16)
        ≤ 2 ^ 27
      split_ifs <;> omega
    · rw [if_neg h15]
      obtain ⟨k, hk32, hp, hnm, hor⟩ :=
        nextPow2_spec (n := n * 8 / 7) (by omega)
      rw [hp]
      rcases hor with rfl | hlt
      · omega
      · have hb : (2 : Nat) ^ (k - 1) < 2 ^ 27 := by omega
        have hk : k - 1 < 27 := (Nat.pow_lt_pow_iff_right (by omega)).1 hb
        exact Nat.pow_le_pow_right (by omega) (by omega)

end Wasm.RustStd.HashMap.Table
