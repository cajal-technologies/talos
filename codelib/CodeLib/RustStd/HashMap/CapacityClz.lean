import CodeLib.RustStd.HashMap.TableRefinement
import Interpreter.Wasm.Semantics

/-!
# `capacity_to_buckets` against the compiled `clz` form

`Table.nextPow2` searches 32 steps for the least power of two that is at
least `n`.  The compiled code does not search.  WAT func 17, lines 3079 to
3100 of `programs/rust/build/rust_hash_map/program.wat`, computes

    (0xFFFFFFFF >>> clz (c - 1)) + 1

for `c = cap * 8 / 7`.  That is `usize::next_power_of_two` as the compiler
emits it.  The guards above the region give `15 <= cap` and
`cap <= 536870911`, so `c` is at least 17 and the form is safe.

This module proves the two forms equal for `2 <= c` and `c <= 2 ^ 32`.  On
the way it proves `clz32_eq`, which reads the interpreter function `clz32`
off a power-of-two bound.  No lemma in the tree did that before.

`clz32_eq` is general.  It belongs in the interpreter beside `clz32`.
-/

namespace Wasm.RustStd.HashMap.Table

/-! ## The top bit of a `u32` -/

private theorem testBit_two_pow_31 {n : Nat} (hn : n < 4294967296) :
    n.testBit 31 = decide (2147483648 ≤ n) := by
  rw [Nat.testBit_eq_decide_div_mod_eq,
    show (2 : Nat) ^ 31 = 2147483648 from by norm_num]
  by_cases h : 2147483648 ≤ n
  · rw [decide_eq_true h,
      decide_eq_true (show n / 2147483648 % 2 = 1 by omega)]
  · rw [decide_eq_false h,
      decide_eq_false (show ¬ (n / 2147483648 % 2 = 1) by omega)]

private theorem and_top_bit_eq_zero {n : Nat} :
    n &&& 2147483648 = 0 ↔ n.testBit 31 = false := by
  constructor
  · intro h
    have hbit : (n &&& 2147483648).testBit 31 = (0 : Nat).testBit 31 := by rw [h]
    rw [Nat.testBit_and, Nat.zero_testBit,
      show (2147483648 : Nat) = 2 ^ 31 from by norm_num,
      Nat.testBit_two_pow] at hbit
    simpa using hbit
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, show (2147483648 : Nat) = 2 ^ 31 from by norm_num,
      Nat.testBit_two_pow, Nat.zero_testBit]
    by_cases hi : (31 : Nat) = i
    · subst hi
      simp [h]
    · simp [hi]

/-- The `i32.and` against `0x80000000` that `clz32` uses is zero exactly
below `2 ^ 31`. -/
private theorem and_top_bit_uint {x : UInt32} :
    x &&& 0x80000000 = 0 ↔ x.toNat < 2 ^ 31 := by
  rw [← UInt32.toNat_inj, UInt32.toNat_and,
    show (0x80000000 : UInt32).toNat = 2147483648 from rfl,
    show (0 : UInt32).toNat = 0 from rfl, and_top_bit_eq_zero,
    testBit_two_pow_31 x.toNat_lt]
  constructor
  · intro h
    have : ¬ (2147483648 ≤ x.toNat) := by simpa using h
    have h31 : (2 : Nat) ^ 31 = 2147483648 := by norm_num
    omega
  · intro h
    have h31 : (2 : Nat) ^ 31 = 2147483648 := by norm_num
    simp only [decide_eq_false_iff_not]
    omega

/-! ## Reading `clz32` off a power-of-two bound -/

private theorem clz32_succ (k : Nat) (x : UInt32) :
    clz32 (k + 1) x =
      if x &&& 0x80000000 ≠ 0 then 32 - (k + 1) else clz32 k (x <<< 1) := rfl

private theorem clz32_go (f : Nat) : ∀ (x : UInt32) (m : Nat), m < 32 →
    2 ^ m ≤ x.toNat → x.toNat < 2 ^ (m + 1) → 31 - m < f → f ≤ 32 →
    clz32 f x = 32 - f + (31 - m) := by
  induction f with
  | zero => intro x m _ _ _ hfuel _; omega
  | succ k ih =>
    intro x m hm hlow hhigh hfuel hf
    rw [clz32_succ]
    by_cases htop : x &&& 0x80000000 ≠ 0
    · rw [if_pos htop]
      have hge : ¬ (x.toNat < 2 ^ 31) := by
        intro hlt
        exact htop (and_top_bit_uint.mpr hlt)
      have hm31 : m = 31 := by
        by_contra hne
        have hle : (2 : Nat) ^ (m + 1) ≤ 2 ^ 31 :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      subst hm31
      omega
    · rw [if_neg htop]
      have hlt31 : x.toNat < 2 ^ 31 :=
        and_top_bit_uint.mp (by simpa using htop)
      have hmlt : m < 31 := by
        by_contra hne
        have hle : (2 : Nat) ^ 31 ≤ 2 ^ m :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      have hshift : (x <<< 1).toNat = x.toNat * 2 := by
        rw [UInt32.toNat_shiftLeft, show (1 : UInt32).toNat % 32 = 1 from rfl,
          Nat.shiftLeft_eq, pow_one, Nat.mod_eq_of_lt]
        have h32 : (2 : Nat) ^ 32 = 2 ^ 31 * 2 := by norm_num
        omega
      have hdouble : (2 : Nat) ^ (m + 1) = 2 ^ m * 2 := by rw [Nat.pow_succ]
      have hdouble2 : (2 : Nat) ^ (m + 1 + 1) = 2 ^ (m + 1) * 2 := by
        rw [Nat.pow_succ]
      have hstep := ih (x <<< 1) (m + 1) (by omega)
        (by rw [hshift]; omega) (by rw [hshift]; omega)
        (by omega) (by omega)
      omega

/-- `clz32` of a word between `2 ^ m` and `2 ^ (m + 1)`. -/
theorem clz32_eq {x : UInt32} {m : Nat} (hm : m < 32)
    (hlow : 2 ^ m ≤ x.toNat) (hhigh : x.toNat < 2 ^ (m + 1)) :
    clz32 32 x = 31 - m := by
  have h := clz32_go 32 x m hm hlow hhigh (by omega) le_rfl
  omega

/-! ## The shift of the all-ones word -/

private theorem shiftRight_allOnes {j : Nat} (hj : j ≤ 32) :
    (4294967295 : Nat) >>> j = 2 ^ (32 - j) - 1 := by
  rw [Nat.shiftRight_eq_div_pow]
  have hpos : 0 < (2 : Nat) ^ j := Nat.two_pow_pos j
  have hprod : (2 : Nat) ^ (32 - j) * 2 ^ j = 2 ^ 32 := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have h32 : (2 : Nat) ^ 32 = 4294967296 := by norm_num
  have hjle : (2 : Nat) ^ j ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) hj
  have hone : 1 ≤ (2 : Nat) ^ (32 - j) := Nat.one_le_two_pow
  have hsplit : (4294967295 : Nat) = (2 ^ j - 1) + (2 ^ (32 - j) - 1) * 2 ^ j := by
    rw [Nat.sub_mul, hprod, Nat.one_mul]
    omega
  rw [hsplit, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt (by omega),
    Nat.zero_add]

/-! ## `nextPow2` from a two-sided bound -/

/-- `nextPow2` is the least power of two that is at least `c`, so a
two-sided bound pins it. -/
theorem nextPow2_eq_of_between {c k : Nat} (hk : k + 1 ≤ 32)
    (hlow : 2 ^ k < c) (hhigh : c ≤ 2 ^ (k + 1)) : nextPow2 c = 2 ^ (k + 1) := by
  have hc32 : c ≤ 2 ^ 32 :=
    le_trans hhigh (Nat.pow_le_pow_right (by norm_num) hk)
  obtain ⟨m, hm32, hnp, hcm, hor⟩ := nextPow2_spec hc32
  rw [hnp]
  congr 1
  rcases hor with rfl | hlt
  · rw [pow_zero] at hcm
    have hone : (1 : Nat) ≤ 2 ^ k := Nat.one_le_two_pow
    omega
  · by_contra hne
    rcases Nat.lt_or_ge m (k + 1) with h | h
    · have hle : (2 : Nat) ^ m ≤ 2 ^ k :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    · have hle : (2 : Nat) ^ (k + 1) ≤ 2 ^ (m - 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      omega

/-! ## The two forms agree -/

/-- The compiled `capacity_to_buckets` computes `nextPow2`. -/
theorem nextPow2_eq_wasm_clz {c : Nat} (h2 : 2 ≤ c) (hub : c ≤ 2 ^ 32) :
    ((0xFFFFFFFF : UInt32) >>>
        UInt32.ofNat (clz32 32 (UInt32.ofNat (c - 1)))).toNat + 1 = nextPow2 c := by
  have h32 : (2 : Nat) ^ 32 = 4294967296 := by norm_num
  have hd0 : c - 1 ≠ 0 := by omega
  have hdlt : c - 1 < 2 ^ 32 := by omega
  set m := Nat.log 2 (c - 1) with hmdef
  have hlow : 2 ^ m ≤ c - 1 := Nat.pow_log_le_self 2 hd0
  have hhigh : c - 1 < 2 ^ (m + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have hm : m < 32 := by
    by_contra hge
    have hle : (2 : Nat) ^ 32 ≤ 2 ^ m :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hofNat : (UInt32.ofNat (c - 1)).toNat = c - 1 := by simp; omega
  have hclz : clz32 32 (UInt32.ofNat (c - 1)) = 31 - m :=
    clz32_eq hm (by rw [hofNat]; exact hlow) (by rw [hofNat]; exact hhigh)
  have hamt : (UInt32.ofNat (31 - m)).toNat % 32 = 31 - m := by
    have : (UInt32.ofNat (31 - m)).toNat = 31 - m := by simp; omega
    rw [this, Nat.mod_eq_of_lt (by omega)]
  rw [hclz, UInt32.toNat_shiftRight,
    show (0xFFFFFFFF : UInt32).toNat = 4294967295 from rfl, hamt,
    shiftRight_allOnes (by omega), show 32 - (31 - m) = m + 1 from by omega,
    Nat.sub_add_cancel Nat.one_le_two_pow]
  refine (nextPow2_eq_of_between (by omega) ?_ ?_).symm
  · omega
  · omega

end Wasm.RustStd.HashMap.Table
