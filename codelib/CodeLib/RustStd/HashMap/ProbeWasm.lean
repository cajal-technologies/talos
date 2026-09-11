import CodeLib.RustStd.HashMap.TableMem
import Interpreter.Wasm.Semantics

/-!
# The probe loop of the compiled code against the model

The probe loop of `find`, `find_or_find_insert_index` and `remove` in the
compiled `rust_hash_map` module is a loop over four registers: the position
`pos`, the stride, the group word loaded at `ctrl + pos`, and the bit mask
of the SWAR match.  `CodeLib.RustStd.HashMap.Swar` relates the match
formulas to the per-byte predicates of the model, and
`CodeLib.RustStd.HashMap.TableMem` relates the loaded word to the control
bytes.  This file closes the two remaining register updates:

* `probeNext_pos_of_wasm`: `(pos + (stride + 8)) & bucket_mask` on `i32`
  is `ProbeSeq.next`.  The sum can wrap in 32 bits, and the mask absorbs
  the wrap because `buckets` divides `2 ^ 32`.
* `lowestSetByte_eq_ctz`: `i64.ctz` of a non-zero match mask, divided by
  eight, is `lowestSetByte` of the mask.  `ctz64_eq` is the specification
  of the interpreter's `ctz64`.
* `setBytes_iterNext` and `hasBit_iterNext`: `mask & (mask + (-1))`, the
  step of `BitMaskIter`, drops the lowest flagged byte and keeps the rest.
* `matchIndex_of_wasm`: the bucket of a match, `((ctz >> 3) + pos) & mask`,
  is `(pos + j) % buckets` for the flagged byte `j`.
* `swarMatchTag_of_wasm` and `repeatByte_h2_of_wasm`: the compiled
  `match_tag` formula, with `+ (-REP01)` and `^ -1`, is `swarMatchTag`.

It also defines `HashMapAt`, the ownership of one `HashMap<u32, u32>`
value: the table and the two SipHash keys of its `RandomState` at offsets
16 and 24.  `MapAt` is the same for the table `ofEntries` builds, which is
the invariant a conditional adequacy statement of the five map contracts
would assume.  `TableU32.wf_ofEntries_u32` proves that this table is
well formed and clean.

What this file does not do: it states nothing about the compiled function
bodies.  The five drivers, the inlined SipHash, the probe loop invariant,
and insert, remove and resize stay open.
-/

namespace Wasm.RustStd.HashMap.Table

open Wasm.SepLogic Wasm.SepLogic.Slices Iris Std

/-! ## The next probe position -/

/-- `ProbeSeq::move_next` as the compiled code computes it: the stride grows
by one group, the sum wraps in 32 bits, and the mask takes it modulo
`buckets`. -/
theorem probeNext_pos_of_wasm {K V : Type} (t : Table K V) {m : Nat} (hm : m ≤ 32)
    (hb : t.buckets = 2 ^ m) (p : ProbeSeq) :
    ((UInt32.ofNat p.pos + (UInt32.ofNat p.stride + 8)) &&&
        UInt32.ofNat (t.buckets - 1)).toNat = (p.next t).pos := by
  simp only [ProbeSeq.next]
  rw [hb, and_mask_toNat _ hm]
  simp only [UInt32.toNat_add, UInt32.toNat_ofNat', show (8 : UInt32).toNat = 8 from rfl]
  have hdvd : 2 ^ m ∣ 2 ^ 32 := Nat.pow_dvd_pow 2 hm
  rw [Nat.mod_add_mod, Nat.mod_add_mod, Nat.add_mod_mod, Nat.mod_mod_of_dvd _ hdvd]

/-! ## Trailing zeros -/

/-- The interpreter's `ctz64 k a` finds the lowest set bit below `k`, offset
by the bits already consumed. -/
theorem ctz64_eq : ∀ (k : Nat), k ≤ 64 → ∀ (a : UInt64) (i : Nat), i < k →
    a.toNat.testBit i = true → (∀ j, j < i → a.toNat.testBit j = false) →
    ctz64 k a = 64 - k + i
  | 0, _, _, _, hi, _, _ => absurd hi (Nat.not_lt_zero _)
  | k + 1, hk, a, i, hi, hbit, hmin => by
    have hlow : (a &&& 1 ≠ 0) ↔ a.toNat.testBit 0 = true := by
      rw [Nat.testBit_zero, decide_eq_true_iff, ne_eq, ← UInt64.toNat_inj, UInt64.toNat_and,
        show (0 : UInt64).toNat = 0 from rfl, show (1 : UInt64).toNat = 1 from rfl,
        Nat.and_one_is_mod]
      omega
    cases i with
    | zero =>
      rw [ctz64, if_pos (hlow.mpr hbit)]
      omega
    | succ i =>
      have hzero : ¬ (a &&& 1 ≠ 0) := fun h => by
        have := hmin 0 (Nat.zero_lt_succ i)
        rw [hlow.mp h] at this
        simp at this
      rw [ctz64, if_neg hzero]
      have hshift : ∀ j, (a >>> 1).toNat.testBit j = a.toNat.testBit (j + 1) := by
        intro j
        rw [UInt64.toNat_shiftRight, show (1 : UInt64).toNat % 64 = 1 from rfl,
          Nat.testBit_shiftRight, Nat.add_comm]
      have ih := ctz64_eq k (by omega) (a >>> 1) i (by omega) (by rw [hshift]; exact hbit)
        (fun j hj => by rw [hshift]; exact hmin (j + 1) (by omega))
      rw [ih]
      omega

/-- Bit `i` of `REP80` is set exactly when `i` is bit 7 of its byte. -/
theorem testBit_REP80 {i : Nat} (hi : i < 64) :
    REP80.toNat.testBit i = decide (i % 8 = 7) := by
  have hj : i / 8 < 8 := by omega
  have h := testBit_byteOf REP80.toNat (i / 8) (i % 8)
  rw [byteOf_REP80 hj, decide_eq_true (Nat.mod_lt i (by decide)), Bool.true_and,
    Nat.div_add_mod i 8] at h
  rw [← h]
  have hlt : i % 8 < 8 := Nat.mod_lt i (by decide)
  generalize i % 8 = r at hlt ⊢
  interval_cases r <;> decide

/-- A bit of a match mask is set only at bit 7 of a byte. -/
theorem testBit_of_mask {msk : UInt64} (hmask : msk &&& REP80 = msk) {i : Nat}
    (hi : msk.toNat.testBit i = true) : i % 8 = 7 := by
  have hlt : i < 64 := by
    by_contra h
    have := Nat.testBit_lt_two_pow
      (Nat.lt_of_lt_of_le (UInt64.toNat_lt msk)
        (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_lt h)))
    rw [this] at hi
    simp at hi
  rw [← hmask, UInt64.toNat_and, Nat.testBit_and, testBit_REP80 hlt] at hi
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hi
  exact hi.2

/-- A set bit has a lowest set bit below or at it. -/
theorem exists_lowest_testBit {n : Nat} {i : Nat} (hi : n.testBit i = true) :
    ∃ i0, n.testBit i0 = true ∧ ∀ j, j < i0 → n.testBit j = false := by
  induction i using Nat.strongRecOn with
  | ind i ih =>
    by_cases h : ∃ j, j < i ∧ n.testBit j = true
    · obtain ⟨j, hj, hbit⟩ := h
      exact ih j hj hbit
    · refine ⟨i, hi, fun j hj => ?_⟩
      cases hb : n.testBit j with
      | false => rfl
      | true => exact absurd ⟨j, hj, hb⟩ h

/-- A non-zero word has a set bit. -/
theorem exists_testBit_of_ne_zero {msk : UInt64} (hne : msk ≠ 0) :
    ∃ i, msk.toNat.testBit i = true := by
  by_contra h
  apply hne
  rw [← UInt64.toNat_inj, show (0 : UInt64).toNat = 0 from rfl]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.zero_testBit]
  cases hb : msk.toNat.testBit i with
  | false => rfl
  | true => exact absurd ⟨i, hb⟩ h

/-- `lowest_set_bit` of a non-zero match mask is `i64.ctz` in bits divided
by eight, as `BitMask::lowest_set_bit` computes it. -/
theorem lowestSetByte_eq_ctz {msk : UInt64} (hmask : msk &&& REP80 = msk) (hne : msk ≠ 0) :
    lowestSetByte msk = some (ctz64 64 msk / 8) := by
  obtain ⟨i, hi⟩ := exists_testBit_of_ne_zero hne
  obtain ⟨i0, hi0, hmin⟩ := exists_lowest_testBit hi
  have hlt : i0 < 64 := by
    by_contra h
    have := Nat.testBit_lt_two_pow
      (Nat.lt_of_lt_of_le (UInt64.toNat_lt msk)
        (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_lt h)))
    rw [this] at hi0
    simp at hi0
  have hctz : ctz64 64 msk = i0 := by
    have := ctz64_eq 64 (Nat.le_refl 64) msk i0 hlt hi0 hmin
    omega
  have hseven : i0 % 8 = 7 := testBit_of_mask hmask hi0
  rw [hctz]
  have hj : i0 / 8 < 8 := by omega
  have hbyte : hasBit msk (i0 / 8) = true := by
    unfold hasBit
    rw [show 8 * (i0 / 8) + 7 = i0 by omega]
    exact hi0
  unfold lowestSetByte
  rw [List.find?_eq_some_iff_getElem]
  refine ⟨hbyte, i0 / 8, by simp [hj], List.getElem_range _, ?_⟩
  intro j hjlt
  rw [List.getElem_range]
  unfold hasBit
  have := hmin (8 * j + 7) (by omega)
  simp [this]

/-! ## Mask iteration

`BitMaskIter::next` returns the lowest flagged byte and clears its bit with
`mask &= mask - 1`.  The compiled code adds `-1` on `i64`.  The lemmas below
follow one step of that loop in the mask predicates of `Swar`. -/

/-- Below the lowest set bit `n - 1` has every bit set, at it none, and above
it the bits of `n`. -/
theorem testBit_sub_one {n i0 : Nat} (hbit : n.testBit i0 = true)
    (hmin : ∀ j, j < i0 → n.testBit j = false) (j : Nat) :
    (n - 1).testBit j = if j < i0 then true else if j = i0 then false else n.testBit j := by
  have hmod : n % 2 ^ (i0 + 1) = 2 ^ i0 := by
    apply Nat.eq_of_testBit_eq
    intro k
    rw [Nat.testBit_mod_two_pow, Nat.testBit_two_pow]
    by_cases hk : k < i0
    · simp [hmin k hk, Nat.ne_of_gt hk]
    · by_cases hk' : k = i0
      · subst hk'
        simp [hbit]
      · have : ¬ k < i0 + 1 := by omega
        simp [this, Ne.symm hk']
  have hdecomp : n = 2 ^ (i0 + 1) * (n / 2 ^ (i0 + 1)) + 2 ^ i0 := by
    have := Nat.div_add_mod n (2 ^ (i0 + 1))
    rw [hmod] at this
    exact this.symm
  have hpos : 0 < 2 ^ i0 := Nat.two_pow_pos i0
  have hsucc : 2 ^ (i0 + 1) = 2 ^ i0 * 2 := Nat.pow_succ 2 i0
  have hsub : n - 1 = 2 ^ (i0 + 1) * (n / 2 ^ (i0 + 1)) + (2 ^ i0 - 1) := by omega
  have hlt : 2 ^ i0 - 1 < 2 ^ (i0 + 1) := by omega
  have hlt' : 2 ^ i0 < 2 ^ (i0 + 1) := by omega
  have hn := Nat.testBit_two_pow_mul_add (n / 2 ^ (i0 + 1)) hlt' j
  rw [← hdecomp, Nat.testBit_two_pow] at hn
  rw [hsub, Nat.testBit_two_pow_mul_add _ hlt, Nat.testBit_two_pow_sub_one, hn]
  by_cases hj : j < i0
  · simp [hj, Nat.lt_succ_of_lt hj]
  · by_cases hj' : j = i0
    · subst hj'
      simp
    · have : ¬ j < i0 + 1 := by omega
      simp [this, hj, hj']

/-- `mask & (mask + (-1))` clears the lowest set bit and keeps every other
bit. -/
theorem testBit_and_add_neg_one {msk : UInt64} {i0 : Nat} (hbit : msk.toNat.testBit i0 = true)
    (hmin : ∀ j, j < i0 → msk.toNat.testBit j = false) (j : Nat) :
    (msk &&& (msk + 18446744073709551615)).toNat.testBit j =
      (msk.toNat.testBit j && decide (j ≠ i0)) := by
  have hne : msk.toNat ≠ 0 := by
    intro h
    rw [h, Nat.zero_testBit] at hbit
    simp at hbit
  have hm : msk.toNat < 2 ^ 64 := UInt64.toNat_lt msk
  have hsub : (msk + 18446744073709551615).toNat = msk.toNat - 1 := by
    rw [UInt64.toNat_add, show (18446744073709551615 : UInt64).toNat = 2 ^ 64 - 1 from rfl,
      show msk.toNat + (2 ^ 64 - 1) = (msk.toNat - 1) + 1 * 2 ^ 64 by omega,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  rw [UInt64.toNat_and, Nat.testBit_and, hsub, testBit_sub_one hbit hmin j]
  by_cases hj : j < i0
  · simp [hj, hmin j hj]
  · by_cases hj' : j = i0
    · subst hj'
      simp
    · simp [hj, hj']

/-- The lowest flagged byte of a match mask, as the lowest set bit. -/
theorem lowest_bit_of_lowestSetByte {msk : UInt64} (hmask : msk &&& REP80 = msk) {j0 : Nat}
    (hlow : lowestSetByte msk = some j0) :
    msk.toNat.testBit (8 * j0 + 7) = true ∧
      ∀ k, k < 8 * j0 + 7 → msk.toNat.testBit k = false := by
  unfold lowestSetByte at hlow
  rw [List.find?_eq_some_iff_getElem] at hlow
  obtain ⟨hj0, i, hi, hij, hbefore⟩ := hlow
  rw [List.getElem_range] at hij
  subst hij
  refine ⟨hj0, fun k hk => ?_⟩
  cases hb : msk.toNat.testBit k with
  | false => rfl
  | true =>
    have h7 := testBit_of_mask hmask hb
    have hki : k / 8 < i := by omega
    have := hbefore (k / 8) hki
    rw [List.getElem_range] at this
    unfold hasBit at this
    rw [show 8 * (k / 8) + 7 = k by omega, hb] at this
    simp at this

/-- One step of `BitMaskIter` in the flag predicate: the lowest flagged byte
is cleared, every other flag stays. -/
theorem hasBit_iterNext {msk : UInt64} (hmask : msk &&& REP80 = msk) {j0 : Nat}
    (hlow : lowestSetByte msk = some j0) (j : Nat) :
    hasBit (msk &&& (msk + 18446744073709551615)) j = (hasBit msk j && decide (j ≠ j0)) := by
  obtain ⟨hbit, hmin⟩ := lowest_bit_of_lowestSetByte hmask hlow
  unfold hasBit
  rw [testBit_and_add_neg_one hbit hmin]
  have heq : (8 * j + 7 ≠ 8 * j0 + 7) ↔ (j ≠ j0) := by omega
  simp only [heq]

/-- One step of `BitMaskIter` in the byte list: the flagged bytes are the
lowest one, then the flagged bytes of the next mask. -/
theorem setBytes_iterNext {msk : UInt64} (hmask : msk &&& REP80 = msk) {j0 : Nat}
    (hlow : lowestSetByte msk = some j0) :
    setBytes msk = j0 :: setBytes (msk &&& (msk + 18446744073709551615)) := by
  have hnext : setBytes (msk &&& (msk + 18446744073709551615)) =
      (setBytes msk).filter (fun j => decide (j ≠ j0)) := by
    unfold setBytes
    rw [List.filter_filter]
    congr 1
    funext j
    rw [hasBit_iterNext hmask hlow j, Bool.and_comm]
  have hhead : setBytes msk = j0 :: ((List.range 8).drop (j0 + 1)).filter (hasBit msk) := by
    unfold lowestSetByte at hlow
    rw [List.find?_eq_some_iff_getElem] at hlow
    obtain ⟨hj0, i, hi, hij, hbefore⟩ := hlow
    rw [List.getElem_range] at hij
    subst hij
    unfold setBytes
    rw [List.filter_eq_cons_iff]
    refine ⟨(List.range 8).take i, (List.range 8).drop (i + 1), ?_, ?_, hj0, rfl⟩
    · have hdrop : List.drop i (List.range 8) = i :: List.drop (i + 1) (List.range 8) := by
        rw [List.drop_eq_getElem_cons hi, List.getElem_range]
      rw [← hdrop, List.take_append_drop]
    · intro x hx
      obtain ⟨j, hj, hxj⟩ := List.mem_iff_getElem.mp hx
      rw [List.length_take, List.length_range] at hj
      rw [List.getElem_take] at hxj
      subst hxj
      have := hbefore j (by omega)
      simpa using this
  have hpw : List.Pairwise (fun a b => a < b) (setBytes msk) :=
    List.Pairwise.filter _ List.pairwise_lt_range
  rw [hhead] at hpw
  have hrest : ∀ a ∈ ((List.range 8).drop (j0 + 1)).filter (hasBit msk), j0 < a :=
    (List.pairwise_cons.mp hpw).1
  rw [hnext, hhead, List.filter_cons, if_neg (by simp)]
  congr 1
  exact (List.filter_eq_self.mpr fun a ha => decide_eq_true (Nat.ne_of_gt (hrest a ha))).symm

/-! ## The compiled match formulas -/

/-- A mask that ends in `& REP80` is fixed by another `& REP80`. -/
theorem and_REP80_and_REP80 (a : UInt64) : a &&& REP80 &&& REP80 = a &&& REP80 := by
  rw [UInt64.and_assoc, UInt64.and_self]

theorem swarMatchTag_and_REP80 (tag : UInt8) (x : UInt64) :
    swarMatchTag tag x &&& REP80 = swarMatchTag tag x :=
  and_REP80_and_REP80 _

theorem swarMatchEmpty_and_REP80 (x : UInt64) :
    swarMatchEmpty x &&& REP80 = swarMatchEmpty x :=
  and_REP80_and_REP80 _

theorem swarMatchEmptyOrDeleted_and_REP80 (x : UInt64) :
    swarMatchEmptyOrDeleted x &&& REP80 = swarMatchEmptyOrDeleted x :=
  and_REP80_and_REP80 _

/-- `!x` is `x ^ -1`, as the compiled code writes it. -/
theorem not_eq_xor_neg_one (a : UInt64) : ~~~a = a ^^^ 18446744073709551615 := by
  rw [← UInt64.toNat_inj, UInt64.toNat_not, UInt64.toNat_xor,
    show (18446744073709551615 : UInt64).toNat = 2 ^ 64 - 1 from rfl]
  have ha := UInt64.toNat_lt a
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one,
    show UInt64.size - 1 - a.toNat = 2 ^ 64 - (a.toNat + 1) by simp only [UInt64.size]; omega,
    Nat.testBit_two_pow_sub_succ ha]
  by_cases hi : i < 64
  · simp [hi]
  · have : a.toNat.testBit i = false :=
      Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_lt hi)))
    simp [hi, this]

/-- `tag * 0x0101010101010101` is the byte `tag` in every lane. -/
theorem repeatByte_eq_mul_REP01 (t : UInt8) : t.toUInt64 * REP01 = repeatByte t := by
  rw [← UInt64.toNat_inj, UInt64.toNat_mul, UInt8.toNat_toUInt64, repeatByte, groupWord,
    toNat_u64OfBytesLE _ (by simp), show REP01.toNat = 72340172838076673 from rfl,
    show List.replicate 8 t = [t, t, t, t, t, t, t, t] from rfl]
  simp only [bytesVal]
  have := UInt8.toNat_lt t
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-- `Group::match_tag` as the compiled code computes it: `cmp + (-REP01)`
for the subtraction and `cmp ^ -1` for the complement. -/
theorem swarMatchTag_of_wasm (tag : UInt8) (x : UInt64) :
    ((x ^^^ tag.toUInt64 * REP01) + 18374403900871474943) &&&
        ((x ^^^ tag.toUInt64 * REP01) ^^^ 18446744073709551615) &&& REP80 =
      swarMatchTag tag x := by
  simp only [swarMatchTag]
  rw [repeatByte_eq_mul_REP01, UInt64.sub_eq_add_neg,
    show (-REP01 : UInt64) = 18374403900871474943 by decide, not_eq_xor_neg_one]

/-- The tag lanes as the compiled code builds them from the hash. -/
theorem repeatByte_h2_of_wasm (hash : UInt64) :
    ((hash >>> 25) &&& 127) * REP01 = repeatByte (h2 hash) := by
  rw [← h2_toUInt64, repeatByte_eq_mul_REP01]

/-- The bucket of a match, as the compiled code computes it: `i64.ctz` of
the mask, wrapped to `i32`, shifted by three, added to the group position,
and masked. -/
theorem matchIndex_of_wasm {K V : Type} (t : Table K V) {m : Nat} (hm : m ≤ 32)
    (hb : t.buckets = 2 ^ m) {msk : UInt64} (hmask : msk &&& REP80 = msk) {j0 : Nat}
    (hlow : lowestSetByte msk = some j0) (pos : Nat) :
    (((UInt64.ofNat (ctz64 64 msk)).toUInt32 >>> 3 + UInt32.ofNat pos) &&&
        UInt32.ofNat (t.buckets - 1)).toNat = (pos + j0) % t.buckets := by
  have hj8 : j0 < 8 := List.mem_range.mp (List.mem_of_find?_eq_some hlow)
  obtain ⟨hbit, hmin⟩ := lowest_bit_of_lowestSetByte hmask hlow
  have hctz : ctz64 64 msk = 8 * j0 + 7 := by
    have := ctz64_eq 64 (Nat.le_refl 64) msk (8 * j0 + 7) (by omega) hbit hmin
    omega
  have hdvd : 2 ^ m ∣ 2 ^ 32 := Nat.pow_dvd_pow 2 hm
  rw [hb, and_mask_toNat _ hm, UInt32.toNat_add, UInt32.toNat_shiftRight, UInt64.toNat_toUInt32,
    UInt64.toNat_ofNat', hctz, UInt32.toNat_ofNat', show (3 : UInt32).toNat % 32 = 3 from rfl,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega : 8 * j0 + 7 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : 8 * j0 + 7 < 2 ^ 32),
    show (8 * j0 + 7) / 2 ^ 3 = j0 by omega, Nat.mod_mod_of_dvd _ hdvd, Nat.add_comm j0,
    Nat.add_mod, Nat.mod_mod_of_dvd pos hdvd, ← Nat.add_mod]

/-! ## The map value -/

section Ownership

variable {α : Type} [WasmHeapGS α]

/-- One `HashMap<u32, u32>` value at `base`: the table, then the two
SipHash keys of its `RandomState` at offsets 16 and 24. -/
def HashMapAt (memId : Nat) (base : UInt32) (k0 k1 : UInt64) (t : Table UInt32 UInt32) :
    IProp (WasmHeapGF α) :=
  iprop(TableAt memId base t ∗ pointsTo_u64 memId (base + 16) k0 ∗
    pointsTo_u64 memId (base + 24) k1)

/-- The map value that `collect_entries` builds from an entry list.  This is
the table invariant a conditional adequacy statement assumes; its pure
side is `TableU32.wf_ofEntries_u32`. -/
def MapAt (memId : Nat) (base : UInt32) (k0 k1 : UInt64) (entries : Map UInt32 UInt32) :
    IProp (WasmHeapGF α) :=
  HashMapAt memId base k0 k1 (ofEntries (SipHash.hashU32 k0 k1) entries)

end Ownership

end Wasm.RustStd.HashMap.Table
