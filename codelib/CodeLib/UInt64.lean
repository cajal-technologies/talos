import Interpreter.Wasm
import Mathlib.Data.Nat.Bitwise

/-!
# `UInt64` arithmetic helpers used by corpus specs

Bridge lemmas between `UInt64` bitwise operations (`>>>`, `<<<`, `|||`,
`-`, the interpreter's `ctz64`) and the `Nat` view that user-facing
specifications prefer.

Used by `Corpus/Crates/NumInteger/Spec.lean` (Stein's binary GCD on
`u64`). Many of the lemmas here are general-purpose and may move to a
more central location once a second consumer appears.

Internal layering:

* `ctz64_lt`, `ctz64_two_pow_dvd`, `ctz64_shr_odd` are the *structural*
  theorems about `ctz64` — every other UInt64 result here reduces to
  them via a `Nat`-level mirror `ntz`.
* `ctz64_or_min` factors the bitwise-`|||` case into the structural
  theorems via `min`, using a `testBit` characterization of `ntz`.
* The recombine identities (`recombine_eq`, `recombine_loop`) and
  loop-step lemmas (`stein_step_x`, `stein_step_y`) plug those into
  `Nat.gcd` algebra (`Nat.gcd_sub_self_left`, `Nat.gcd_mul_left`,
  coprime-with-`2^k` facts) plus `UInt64.toNat_*` arithmetic.
-/

namespace Wasm

/-! ## Small `UInt64 ↔ Nat` helpers (bitwise) -/

private theorem _aux_toNat_and_one (a : UInt64) : (a &&& 1).toNat = a.toNat % 2 := by
  rw [UInt64.toNat_and]
  show a.toNat &&& 1 = a.toNat % 2
  exact Nat.and_one_is_mod a.toNat

private theorem _aux_and_one_ne_zero_iff (a : UInt64) :
    a &&& 1 ≠ 0 ↔ a.toNat % 2 = 1 := by
  have h := _aux_toNat_and_one a
  have hzero : (0 : UInt64).toNat = 0 := rfl
  have hmod : a.toNat % 2 < 2 := Nat.mod_lt _ (by decide)
  constructor
  · intro hne
    have hne' : (a &&& 1).toNat ≠ 0 := by
      intro h0; apply hne; apply UInt64.toNat.inj; rw [hzero]; exact h0
    rw [h] at hne'; omega
  · intro h2 h0
    have : (a &&& 1).toNat = 0 := by rw [h0]; rfl
    rw [h] at this; omega

private theorem _aux_shiftRight_one_toNat (a : UInt64) :
    (a >>> 1).toNat = a.toNat / 2 := by
  rw [UInt64.toNat_shiftRight]
  show a.toNat >>> ((1 : UInt64).toNat % 64) = a.toNat / 2
  show a.toNat >>> 1 = a.toNat / 2
  exact Nat.shiftRight_one _

/-! ## `ctz64` structural facts

We bridge through a `Nat`-level function `ntz` (natural trailing zeros)
which is structurally identical to `ctz64` but operates on `Nat`. -/

/-- `Nat`-level mirror of `ctz64`. Same recursion, on `Nat`. -/
private def ntz : Nat → Nat → Nat
  | 0, _ => 64
  | k + 1, n => if n % 2 = 1 then 64 - (k + 1) else ntz k (n / 2)

private theorem ctz64_eq_ntz (k : Nat) (a : UInt64) :
    ctz64 k a = ntz k a.toNat := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
    show (if a &&& 1 ≠ 0 then 64 - (k + 1) else ctz64 k (a >>> 1))
        = if a.toNat % 2 = 1 then 64 - (k + 1) else ntz k (a.toNat / 2)
    by_cases h : a &&& 1 ≠ 0
    · have h2 : a.toNat % 2 = 1 := (_aux_and_one_ne_zero_iff a).mp h
      simp [h, h2]
    · have h2 : a.toNat % 2 ≠ 1 := fun h2' => h ((_aux_and_one_ne_zero_iff a).mpr h2')
      simp [h, h2]
      rw [ih, _aux_shiftRight_one_toNat]

private theorem ntz_le (k n : Nat) : ntz k n ≤ 64 := by
  induction k generalizing n with
  | zero => exact Nat.le_refl _
  | succ k ih =>
    unfold ntz
    split
    · omega
    · exact ih _

private theorem ntz_lt_or_low_bits_zero (k n : Nat) :
    ntz k n < 64 ∨ (ntz k n = 64 ∧ ∀ i < k, (n / 2^i) % 2 = 0) := by
  induction k generalizing n with
  | zero =>
    right
    refine ⟨rfl, ?_⟩
    intro i hi; omega
  | succ k ih =>
    unfold ntz
    split
    · rename_i h
      left; omega
    · rename_i h
      have hnmod : n % 2 = 0 := by
        have : n % 2 < 2 := Nat.mod_lt _ (by decide)
        omega
      rcases ih (n / 2) with hlt | ⟨heq, hzero⟩
      · left; exact hlt
      · right
        refine ⟨heq, ?_⟩
        intro i hi
        match i with
        | 0 => simpa using hnmod
        | i + 1 =>
          have := hzero i (by omega)
          have hdd : n / 2^(i+1) = (n / 2) / 2^i := by
            rw [pow_succ, Nat.div_div_eq_div_mul, Nat.mul_comm]
          rw [hdd]; exact this

/-- For nonzero `a`, the interpreter's `ctz64 64 a` (number of trailing
zero bits) is strictly less than 64. -/
theorem UInt64.ctz64_lt (a : UInt64) (ha : a ≠ 0) : ctz64 64 a < 64 := by
  rw [ctz64_eq_ntz]
  rcases ntz_lt_or_low_bits_zero 64 a.toNat with hlt | ⟨_, hzero⟩
  · exact hlt
  · exfalso
    apply ha
    apply UInt64.toNat.inj
    show a.toNat = 0
    have h64 : a.toNat < 2 ^ 64 := a.toNat_lt
    -- All 64 low bits zero + a.toNat < 2^64 ⇒ a.toNat = 0.
    have : ∀ i < 64, a.toNat / 2^i % 2 = 0 := hzero
    -- Standard: this implies a.toNat = 0.
    -- Use Nat.eq_zero_of_testBit_eq_false? We have % 2 = 0 = testBit = false.
    apply Nat.zero_of_testBit_eq_false (n := a.toNat)
    intro i
    by_cases hi : i < 64
    · have hmod := this i hi
      rw [Nat.testBit_eq_decide_div_mod_eq]
      simp [hmod]
    · push Not at hi
      have : a.toNat < 2^i := lt_of_lt_of_le h64 (Nat.pow_le_pow_right (by decide) hi)
      exact Nat.testBit_eq_false_of_lt this

/-- `ntz` decomposition: for positive `n < 2^k`, the lowest set bit is at
position `ntz k n - (64 - k)`, the result is in `[64 - k, 63]`, and
`n = 2 ^ (lowest set bit) * (odd)`. -/
private theorem ntz_decompose (k n : Nat) (hk : k ≤ 64) (hpos : 0 < n) (hn : n < 2^k) :
    ∃ m, m % 2 = 1 ∧ n = 2 ^ (ntz k n - (64 - k)) * m ∧
      64 - k ≤ ntz k n ∧ ntz k n < 64 := by
  induction k generalizing n with
  | zero =>
    exfalso
    have : n < 1 := by simpa using hn
    omega
  | succ k ih =>
    unfold ntz
    by_cases h : n % 2 = 1
    · refine ⟨n, h, ?_, ?_, ?_⟩
      · simp [h]
      · simp [h]
      · simp [h]; omega
    · have hmod : n % 2 = 0 := by
        have := Nat.mod_lt n (show 0 < 2 by decide); omega
      have hge2 : 2 ≤ n := by omega
      have hndiv_pos : 0 < n / 2 := by omega
      have hpow : (2:Nat) ^ (k + 1) = 2 * 2^k := by rw [pow_succ]; ring
      have hndiv_bnd : n / 2 < 2 ^ k := by
        have hdm : 2 * (n / 2) + n % 2 = n := Nat.div_add_mod n 2
        have h2 : 2 * (n / 2) < 2 * 2^k := by rw [← hpow]; omega
        exact Nat.lt_of_mul_lt_mul_left h2
      obtain ⟨m, hmod1, heq, hge, hlt⟩ := ih (n / 2) (by omega) hndiv_pos hndiv_bnd
      set c := ntz k (n / 2) with hc
      refine ⟨m, hmod1, ?_, ?_, ?_⟩
      · simp [h]
        have hn_eq : n = 2 * (n / 2) := by
          have hdm : 2 * (n / 2) + n % 2 = n := Nat.div_add_mod n 2
          omega
        have hexp : c - (63 - k) = (c - (64 - k)) + 1 := by omega
        rw [hexp]
        conv_lhs => rw [hn_eq, heq]
        rw [pow_succ]; ring
      · simp [h]; omega
      · simp [h]; exact hlt

private theorem _aux_toNat_UInt64_ofNat (n : Nat) : (UInt64.ofNat n).toNat = n % 2^64 := by
  show (BitVec.ofNat 64 n).toNat = n % 2^64
  exact BitVec.toNat_ofNat _ _

private theorem _aux_toNat_pos (a : UInt64) (ha : a ≠ 0) : 0 < a.toNat := by
  have h0 : (0 : UInt64).toNat = 0 := rfl
  by_contra hzero
  apply ha
  apply UInt64.toNat.inj
  rw [h0]; omega

/-- `2 ^ ctz64 64 a` divides `a.toNat`. (Holds vacuously when `a = 0`
since `ctz64 64 0 = 64` and `2 ^ 64 ∣ 0`.) -/
theorem UInt64.ctz64_two_pow_dvd (a : UInt64) : 2 ^ ctz64 64 a ∣ a.toNat := by
  by_cases ha : a = 0
  · subst ha
    show 2 ^ ctz64 64 (0 : UInt64) ∣ (0 : UInt64).toNat
    simp
  · rw [ctz64_eq_ntz]
    obtain ⟨m, _, heq, _, _⟩ :=
      ntz_decompose 64 a.toNat (by omega) (_aux_toNat_pos a ha) a.toNat_lt
    simp at heq
    exact ⟨m, heq⟩

/-- The "odd part" of a nonzero `UInt64`: dividing out `2 ^ ctz64` leaves
an odd `Nat`. -/
theorem UInt64.ctz64_shr_odd (a : UInt64) (ha : a ≠ 0) :
    (a.toNat / 2 ^ ctz64 64 a) % 2 = 1 := by
  rw [ctz64_eq_ntz]
  obtain ⟨m, hmod1, heq, _, _⟩ :=
    ntz_decompose 64 a.toNat (by omega) (_aux_toNat_pos a ha) a.toNat_lt
  simp at heq
  set c := ntz 64 a.toNat
  have h2pos : 0 < (2 : Nat) ^ c := Nat.two_pow_pos _
  have hkey : a.toNat / 2 ^ c = m := by
    rw [heq]; exact Nat.mul_div_cancel_left _ h2pos
  rw [hkey]; exact hmod1

/-- Bit at `ntz 64 n` is set, and bits below are not. (For n > 0, n < 2^64.) -/
private theorem ntz_64_testBit_spec (n : Nat) (hpos : 0 < n) (hbnd : n < 2^64) :
    n.testBit (ntz 64 n) = true ∧ ∀ i < ntz 64 n, n.testBit i = false := by
  obtain ⟨m, hmod1, heq, _, _⟩ := ntz_decompose 64 n (by omega) hpos hbnd
  simp at heq
  set c := ntz 64 n
  refine ⟨?_, ?_⟩
  · rw [heq, show (2:Nat)^c * m = m <<< c by rw [Nat.shiftLeft_eq]; ring,
        Nat.testBit_shiftLeft]
    simp
    exact hmod1
  · intro i hi
    rw [heq, show (2:Nat)^c * m = m <<< c by rw [Nat.shiftLeft_eq]; ring,
        Nat.testBit_shiftLeft]
    simp; omega

/-- `ntz` is uniquely characterized for nonzero values < 2^64 by the
"lowest set bit" property. -/
private theorem ntz_64_unique (n : Nat) (hpos : 0 < n) (hbnd : n < 2^64)
    (k : Nat) (_hk : k < 64) (hbit : n.testBit k = true)
    (hzero : ∀ i < k, n.testBit i = false) :
    ntz 64 n = k := by
  obtain ⟨hbit', hzero'⟩ := ntz_64_testBit_spec n hpos hbnd
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · -- hlt : ntz 64 n < k
    have := hzero (ntz 64 n) hlt
    rw [hbit'] at this; simp at this
  · -- hlt : k < ntz 64 n
    have := hzero' k hlt
    rw [hbit] at this; simp at this

/-- `ctz64` of a bitwise OR is the smaller of the two `ctz64` values. -/
theorem UInt64.ctz64_or_min (a b : UInt64) (ha : a ≠ 0) (hb : b ≠ 0) :
    ctz64 64 (a ||| b) = min (ctz64 64 a) (ctz64 64 b) := by
  rw [ctz64_eq_ntz, ctz64_eq_ntz, ctz64_eq_ntz]
  have ha' : 0 < a.toNat := _aux_toNat_pos a ha
  have hb' : 0 < b.toNat := _aux_toNat_pos b hb
  have ⟨hbitA, hzeroA⟩ := ntz_64_testBit_spec a.toNat ha' a.toNat_lt
  have ⟨hbitB, hzeroB⟩ := ntz_64_testBit_spec b.toNat hb' b.toNat_lt
  have ha_lt : ntz 64 a.toNat < 64 := by
    obtain ⟨_, _, _, _, h⟩ := ntz_decompose 64 a.toNat (by omega) ha' a.toNat_lt
    exact h
  have hb_lt : ntz 64 b.toNat < 64 := by
    obtain ⟨_, _, _, _, h⟩ := ntz_decompose 64 b.toNat (by omega) hb' b.toNat_lt
    exact h
  have habne : (a ||| b).toNat ≠ 0 := by
    intro h0
    rw [UInt64.toNat_or] at h0
    have : (a.toNat ||| b.toNat).testBit (ntz 64 a.toNat) = true := by
      rw [Nat.testBit_or, hbitA]; simp
    rw [h0] at this
    simp at this
  have habpos : 0 < (a ||| b).toNat := Nat.pos_of_ne_zero habne
  have habbnd : (a ||| b).toNat < 2^64 := (a ||| b).toNat_lt
  set k := min (ntz 64 a.toNat) (ntz 64 b.toNat) with hk_def
  have hk_lt : k < 64 := by omega
  rw [UInt64.toNat_or]
  have habpos' : 0 < a.toNat ||| b.toNat := by rw [← UInt64.toNat_or]; exact habpos
  have habbnd' : a.toNat ||| b.toNat < 2^64 := by rw [← UInt64.toNat_or]; exact habbnd
  apply ntz_64_unique _ habpos' habbnd' k hk_lt
  · rw [Nat.testBit_or]
    by_cases hle : ntz 64 a.toNat ≤ ntz 64 b.toNat
    · have : k = ntz 64 a.toNat := by omega
      rw [this, hbitA]; simp
    · have : k = ntz 64 b.toNat := by omega
      rw [this, hbitB]; simp
  · intro i hi
    rw [Nat.testBit_or]
    have hiA : i < ntz 64 a.toNat := by omega
    have hiB : i < ntz 64 b.toNat := by omega
    rw [hzeroA i hiA, hzeroB i hiB]; rfl

/-! ## `UInt64 → Nat` for the shift / shift-mask compositions used by Stein -/

/-- The `% 64` mask on `UInt64.ofNat (ctz64 64 a)` is inert for nonzero
`a` because `ctz64 < 64`. -/
theorem UInt64.toNat_ofNat_ctz_mod (a : UInt64) (ha : a ≠ 0) :
    (UInt64.ofNat (ctz64 64 a) % 64).toNat = ctz64 64 a := by
  have hlt : ctz64 64 a < 64 := UInt64.ctz64_lt a ha
  rw [UInt64.toNat_mod, _aux_toNat_UInt64_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : ctz64 64 a < 2^64)]
  show ctz64 64 a % (64 : UInt64).toNat = ctz64 64 a
  exact Nat.mod_eq_of_lt hlt

/-- `a >>> (UInt64.ofNat (ctz64 64 a) % 64)` lands at the odd part of `a`
in `Nat`. -/
theorem UInt64.shr_ctz_toNat (a : UInt64) (ha : a ≠ 0) :
    (a >>> (UInt64.ofNat (ctz64 64 a) % 64)).toNat
      = a.toNat / 2 ^ ctz64 64 a := by
  rw [UInt64.toNat_shiftRight]
  rw [UInt64.toNat_ofNat_ctz_mod a ha]
  have hlt : ctz64 64 a < 64 := UInt64.ctz64_lt a ha
  rw [Nat.mod_eq_of_lt hlt, Nat.shiftRight_eq_div_pow]

/-- Shifting a nonzero `UInt64` right by its own `ctz64` keeps it nonzero. -/
theorem UInt64.shr_ctz_ne_zero (a : UInt64) (ha : a ≠ 0) :
    a >>> (UInt64.ofNat (ctz64 64 a) % 64) ≠ 0 := by
  intro h
  have := UInt64.shr_ctz_toNat a ha
  rw [h] at this
  -- this : (0 : UInt64).toNat = a.toNat / 2 ^ ctz64 64 a
  have h0 : (0 : UInt64).toNat = 0 := rfl
  rw [h0] at this
  -- now: 0 = a.toNat / 2 ^ ctz64 64 a, but the odd part is nonzero (mod 2 = 1)
  have hodd : (a.toNat / 2 ^ ctz64 64 a) % 2 = 1 := UInt64.ctz64_shr_odd a ha
  omega

/-- And its `toNat` is odd. -/
theorem UInt64.shr_ctz_toNat_odd (a : UInt64) (ha : a ≠ 0) :
    (a >>> (UInt64.ofNat (ctz64 64 a) % 64)).toNat % 2 = 1 := by
  rw [UInt64.shr_ctz_toNat a ha]
  exact UInt64.ctz64_shr_odd a ha

/-! ## Nat-level Stein identity -/

private theorem _aux_coprime_two_pow_of_odd (k m : Nat) (hm : m % 2 = 1) :
    (2 ^ k).Coprime m := by
  apply Nat.Coprime.pow_left
  show Nat.gcd 2 m = 1
  rw [Nat.gcd_rec, hm]; decide

/-- Stein's identity: `gcd (2^i * m) (2^j * n) = 2^min(i,j) * gcd m n` when
`m, n` are both odd. -/
private theorem _aux_stein_recombine (i j m n : Nat) (hm : m % 2 = 1) (hn : n % 2 = 1) :
    Nat.gcd (2^i * m) (2^j * n) = 2 ^ min i j * Nat.gcd m n := by
  -- WLOG i ≤ j.
  by_cases hij : i ≤ j
  · have hmin : min i j = i := Nat.min_eq_left hij
    have hjsub : 2^j = 2^i * 2^(j-i) := by rw [← pow_add]; congr 1; omega
    rw [hmin, hjsub, Nat.mul_assoc, Nat.gcd_mul_left]
    congr 1
    have hcop : (2 ^ (j - i)).Coprime m := _aux_coprime_two_pow_of_odd _ _ hm
    rw [Nat.gcd_comm m (2 ^ (j - i) * n), Nat.Coprime.gcd_mul_left_cancel _ hcop, Nat.gcd_comm]
  · push Not at hij
    have hji : j ≤ i := by omega
    have hmin : min i j = j := Nat.min_eq_right hji
    have hisub : 2^i = 2^j * 2^(i-j) := by rw [← pow_add]; congr 1; omega
    rw [hmin, hisub, Nat.mul_assoc, Nat.gcd_comm, Nat.gcd_mul_left]
    congr 1
    have hcop : (2 ^ (i - j)).Coprime n := _aux_coprime_two_pow_of_odd _ _ hn
    rw [Nat.gcd_comm n (2 ^ (i - j) * m), Nat.Coprime.gcd_mul_left_cancel _ hcop]

/-! ## Stein recombine identities

These bundle the `ctz64` structural theorems above with `Nat.gcd` algebra
into the exact forms the wasm-level proof needs. -/

/-- `b ||| a ≠ 0` when `b ≠ 0`. -/
private theorem _aux_or_ne_zero (a b : UInt64) (hb : b ≠ 0) : b ||| a ≠ 0 := by
  intro h0
  have h0' : (b ||| a).toNat = 0 := by rw [h0]; rfl
  rw [UInt64.toNat_or] at h0'
  have hbitB : (b.toNat).testBit (ntz 64 b.toNat) = true :=
    (ntz_64_testBit_spec b.toNat (_aux_toNat_pos b hb) b.toNat_lt).1
  have hor_bit : (b.toNat ||| a.toNat).testBit (ntz 64 b.toNat) = true := by
    rw [Nat.testBit_or, hbitB]; simp
  rw [h0'] at hor_bit
  simp at hor_bit

/-- Core recombine: if `o.toNat = gcd(a_odd, b_odd)`, then
`o <<< ctz(b|||a) = gcd a b` at `UInt64`. -/
private theorem _aux_recombine_core (a b o : UInt64) (ha : a ≠ 0) (hb : b ≠ 0)
    (h_o : o.toNat = (a.toNat / 2 ^ ctz64 64 a).gcd (b.toNat / 2 ^ ctz64 64 b)) :
    o <<< (UInt64.ofNat (ctz64 64 (b ||| a)) % 64)
      = UInt64.ofNat (a.toNat.gcd b.toNat) := by
  have ha' : 0 < a.toNat := _aux_toNat_pos a ha
  have hb' : 0 < b.toNat := _aux_toNat_pos b hb
  have hbab : b ||| a ≠ 0 := _aux_or_ne_zero a b hb
  -- ctz of OR, and the mask % 64 is inert.
  have h_or_mask : (UInt64.ofNat (ctz64 64 (b ||| a)) % 64).toNat = ctz64 64 (b ||| a) :=
    UInt64.toNat_ofNat_ctz_mod (b ||| a) hbab
  -- ctz(b|||a) = min(ctz b, ctz a) (note: this is `b ||| a`, not `a ||| b`).
  have h_ctz_or : ctz64 64 (b ||| a) = min (ctz64 64 b) (ctz64 64 a) :=
    UInt64.ctz64_or_min b a hb ha
  -- ctz of OR < 64.
  have h_ctz_or_lt : ctz64 64 (b ||| a) < 64 := UInt64.ctz64_lt _ hbab
  -- ctz_a, ctz_b < 64.
  have h_ctz_a_lt : ctz64 64 a < 64 := UInt64.ctz64_lt a ha
  have h_ctz_b_lt : ctz64 64 b < 64 := UInt64.ctz64_lt b hb
  -- Stein at Nat level: gcd a b = 2^min * gcd(a_odd, b_odd).
  have h_a_decomp : a.toNat = 2 ^ ctz64 64 a * (a.toNat / 2 ^ ctz64 64 a) :=
    (Nat.div_mul_cancel (UInt64.ctz64_two_pow_dvd a)).symm.trans (by ring)
  have h_b_decomp : b.toNat = 2 ^ ctz64 64 b * (b.toNat / 2 ^ ctz64 64 b) :=
    (Nat.div_mul_cancel (UInt64.ctz64_two_pow_dvd b)).symm.trans (by ring)
  have h_a_odd : (a.toNat / 2 ^ ctz64 64 a) % 2 = 1 := UInt64.ctz64_shr_odd a ha
  have h_b_odd : (b.toNat / 2 ^ ctz64 64 b) % 2 = 1 := UInt64.ctz64_shr_odd b hb
  have h_stein : a.toNat.gcd b.toNat =
      2 ^ min (ctz64 64 a) (ctz64 64 b) *
        Nat.gcd (a.toNat / 2 ^ ctz64 64 a) (b.toNat / 2 ^ ctz64 64 b) := by
    conv_lhs => rw [h_a_decomp, h_b_decomp]
    exact _aux_stein_recombine _ _ _ _ h_a_odd h_b_odd
  -- Bound the gcd by a.toNat < 2^64.
  have h_gcd_le_a : a.toNat.gcd b.toNat ≤ a.toNat := Nat.gcd_le_left _ ha'
  have h_gcd_lt_64 : a.toNat.gcd b.toNat < 2^64 := lt_of_le_of_lt h_gcd_le_a a.toNat_lt
  -- Now compute toNat of LHS and RHS, then UInt64.toNat.inj.
  apply UInt64.toNat.inj
  rw [UInt64.toNat_shiftLeft, _aux_toNat_UInt64_ofNat, h_or_mask,
      Nat.mod_eq_of_lt h_ctz_or_lt, Nat.mod_eq_of_lt h_gcd_lt_64,
      Nat.shiftLeft_eq, h_o, h_ctz_or, Nat.min_comm, h_stein, Nat.mul_comm]
  refine Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.le_of_eq ?_) h_gcd_lt_64)
  linarith [h_stein, Nat.mul_comm (2 ^ min (ctz64 64 a) (ctz64 64 b))
    ((a.toNat / 2 ^ ctz64 64 a).gcd (b.toNat / 2 ^ ctz64 64 b))]

/-- Recombine when both operands' odd parts are *equal* (the `INNER.br 1`
exit of Stein's binary GCD). -/
theorem UInt64.recombine_eq (a b : UInt64) (ha : a ≠ 0) (hb : b ≠ 0)
    (hEq : a >>> (UInt64.ofNat (ctz64 64 a) % 64)
         = b >>> (UInt64.ofNat (ctz64 64 b) % 64)) :
    a >>> (UInt64.ofNat (ctz64 64 a) % 64)
        <<< (UInt64.ofNat (ctz64 64 (b ||| a)) % 64)
      = UInt64.ofNat (a.toNat.gcd b.toNat) := by
  set o := a >>> (UInt64.ofNat (ctz64 64 a) % 64) with ho_def
  apply _aux_recombine_core a b o ha hb
  -- Need: o.toNat = (a.toNat / 2^ctz a).gcd (b.toNat / 2^ctz b)
  rw [ho_def, UInt64.shr_ctz_toNat a ha]
  -- Goal: a.toNat / 2^ctz a = (a.toNat / 2^ctz a).gcd (b.toNat / 2^ctz b)
  -- From hEq: a >>> ... = b >>> ..., so a_odd.toNat = b_odd.toNat.
  have h_eq_nat : a.toNat / 2 ^ ctz64 64 a = b.toNat / 2 ^ ctz64 64 b := by
    have h := congrArg UInt64.toNat hEq
    rw [UInt64.shr_ctz_toNat a ha, UInt64.shr_ctz_toNat b hb] at h
    exact h
  rw [← h_eq_nat]
  exact (Nat.gcd_self _).symm

/-- Recombine after the main loop. -/
theorem UInt64.recombine_loop (a b o : UInt64) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : o.toNat.gcd o.toNat
       = (a.toNat >>> (ctz64 64 a % 64)).gcd (b.toNat >>> (ctz64 64 b % 64))) :
    o <<< (UInt64.ofNat (ctz64 64 (b ||| a)) % 64)
      = UInt64.ofNat (a.toNat.gcd b.toNat) := by
  apply _aux_recombine_core a b o ha hb
  have h_ctz_a_lt : ctz64 64 a < 64 := UInt64.ctz64_lt a ha
  have h_ctz_b_lt : ctz64 64 b < 64 := UInt64.ctz64_lt b hb
  rw [Nat.mod_eq_of_lt h_ctz_a_lt, Nat.mod_eq_of_lt h_ctz_b_lt] at h
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow] at h
  rw [Nat.gcd_self] at h
  exact h

/-! ## Loop-step invariants (one iteration of Stein's subtract-and-halve) -/

/-- The Nat-level gcd step: `gcd((x-y)/2^k, y) = gcd(x, y)` when y is odd
and 2^k divides x-y. -/
private theorem _aux_gcd_sub_div_pow2 (x y k : Nat) (hle : y ≤ x) (hy : y % 2 = 1)
    (hdvd : 2^k ∣ x - y) :
    ((x - y) / 2^k).gcd y = x.gcd y := by
  have hdecomp : x - y = 2^k * ((x - y) / 2^k) :=
    (Nat.div_mul_cancel hdvd).symm.trans (by ring)
  have hcop : (2^k).Coprime y := _aux_coprime_two_pow_of_odd k y hy
  have h1 : ((x - y) / 2^k).gcd y = (x - y).gcd y := by
    calc ((x - y) / 2^k).gcd y
        = (2^k * ((x - y) / 2^k)).gcd y := (Nat.Coprime.gcd_mul_left_cancel _ hcop).symm
      _ = (x - y).gcd y := by rw [← hdecomp]
  rw [h1, Nat.gcd_sub_self_left hle]

/-- One iteration in the `y < x` branch. -/
theorem UInt64.stein_step_x (x y : UInt64) (_hxne : x ≠ 0) (hyne : y ≠ 0)
    (hxodd : x.toNat % 2 = 1) (hyodd : y.toNat % 2 = 1) (hlt : y < x) :
    ¬ (x - y) >>> (UInt64.ofNat (ctz64 64 (x - y)) % 64) = 0
    ∧ (x - y).toNat >>> (ctz64 64 (x - y) % 64) % 2 = 1
    ∧ ((x - y).toNat >>> (ctz64 64 (x - y) % 64)).gcd y.toNat
        = x.toNat.gcd y.toNat
    ∧ (x - y).toNat >>> (ctz64 64 (x - y) % 64) < x.toNat := by
  have hxle_nat : y.toNat ≤ x.toNat := Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp hlt)
  have hxle : y ≤ x := UInt64.le_iff_toNat_le.mpr hxle_nat
  have hxlt_nat : y.toNat < x.toNat := UInt64.lt_iff_toNat_lt.mp hlt
  have h_sub_toNat : (x - y).toNat = x.toNat - y.toNat := UInt64.toNat_sub_of_le x y hxle
  have h_sub_pos : 0 < x.toNat - y.toNat := by omega
  have h_sub_ne : x - y ≠ 0 := by
    intro h
    have : (x - y).toNat = 0 := by rw [h]; rfl
    rw [h_sub_toNat] at this; omega
  have h_ctz_lt : ctz64 64 (x - y) < 64 := UInt64.ctz64_lt _ h_sub_ne
  have h_shr_ne : (x - y) >>> (UInt64.ofNat (ctz64 64 (x - y)) % 64) ≠ 0 :=
    UInt64.shr_ctz_ne_zero (x - y) h_sub_ne
  have h_shr_toNat : ((x - y) >>> (UInt64.ofNat (ctz64 64 (x - y)) % 64)).toNat
      = (x - y).toNat / 2 ^ ctz64 64 (x - y) := UInt64.shr_ctz_toNat (x - y) h_sub_ne
  have h_shr_toNat' : (x - y).toNat >>> (ctz64 64 (x - y) % 64)
      = (x - y).toNat / 2 ^ ctz64 64 (x - y) := by
    rw [Nat.mod_eq_of_lt h_ctz_lt, Nat.shiftRight_eq_div_pow]
  -- assemble.
  refine ⟨h_shr_ne, ?_, ?_, ?_⟩
  · rw [h_shr_toNat', ← h_shr_toNat]
    exact UInt64.shr_ctz_toNat_odd (x - y) h_sub_ne
  · rw [h_shr_toNat', h_sub_toNat]
    exact _aux_gcd_sub_div_pow2 x.toNat y.toNat _ hxle_nat hyodd
      (by rw [← h_sub_toNat]; exact UInt64.ctz64_two_pow_dvd (x - y))
  · rw [h_shr_toNat', h_sub_toNat]
    calc (x.toNat - y.toNat) / 2 ^ ctz64 64 (x - y)
        ≤ x.toNat - y.toNat := Nat.div_le_self _ _
      _ < x.toNat := by have : 0 < y.toNat := _aux_toNat_pos y hyne; omega

/-- One iteration in the `x ≤ y, x ≠ y` branch. -/
theorem UInt64.stein_step_y (x y : UInt64) (hxne : x ≠ 0) (_hyne : y ≠ 0)
    (hxodd : x.toNat % 2 = 1) (hyodd : y.toNat % 2 = 1) (hle : ¬ y < x)
    (hne : x ≠ y) :
    ¬ (y - x) >>> (UInt64.ofNat (ctz64 64 (y - x)) % 64) = 0
    ∧ (y - x).toNat >>> (ctz64 64 (y - x) % 64) % 2 = 1
    ∧ x.toNat.gcd ((y - x).toNat >>> (ctz64 64 (y - x) % 64))
        = x.toNat.gcd y.toNat
    ∧ (y - x).toNat >>> (ctz64 64 (y - x) % 64) < y.toNat := by
  have hxlt : x < y := by
    rw [UInt64.lt_iff_toNat_lt]
    have h1 : ¬ y.toNat < x.toNat := fun h => hle (UInt64.lt_iff_toNat_lt.mpr h)
    have h2 : x.toNat ≠ y.toNat := fun h => hne (UInt64.toNat.inj h)
    omega
  have hxle : x ≤ y := UInt64.le_iff_toNat_le.mpr (UInt64.lt_iff_toNat_lt.mp hxlt |> Nat.le_of_lt)
  have hxle_nat : x.toNat ≤ y.toNat := UInt64.le_iff_toNat_le.mp hxle
  have hxlt_nat : x.toNat < y.toNat := UInt64.lt_iff_toNat_lt.mp hxlt
  have h_sub_toNat : (y - x).toNat = y.toNat - x.toNat := UInt64.toNat_sub_of_le y x hxle
  have h_sub_pos : 0 < y.toNat - x.toNat := by omega
  have h_sub_ne : y - x ≠ 0 := by
    intro h
    have : (y - x).toNat = 0 := by rw [h]; rfl
    rw [h_sub_toNat] at this; omega
  have h_ctz_lt : ctz64 64 (y - x) < 64 := UInt64.ctz64_lt _ h_sub_ne
  have h_shr_ne : (y - x) >>> (UInt64.ofNat (ctz64 64 (y - x)) % 64) ≠ 0 :=
    UInt64.shr_ctz_ne_zero (y - x) h_sub_ne
  have h_shr_toNat : ((y - x) >>> (UInt64.ofNat (ctz64 64 (y - x)) % 64)).toNat
      = (y - x).toNat / 2 ^ ctz64 64 (y - x) := UInt64.shr_ctz_toNat (y - x) h_sub_ne
  have h_shr_toNat' : (y - x).toNat >>> (ctz64 64 (y - x) % 64)
      = (y - x).toNat / 2 ^ ctz64 64 (y - x) := by
    rw [Nat.mod_eq_of_lt h_ctz_lt, Nat.shiftRight_eq_div_pow]
  refine ⟨h_shr_ne, ?_, ?_, ?_⟩
  · rw [h_shr_toNat', ← h_shr_toNat]
    exact UInt64.shr_ctz_toNat_odd (y - x) h_sub_ne
  · rw [h_shr_toNat', h_sub_toNat]
    rw [Nat.gcd_comm x.toNat]
    rw [_aux_gcd_sub_div_pow2 y.toNat x.toNat _ hxle_nat hxodd
        (by rw [← h_sub_toNat]; exact UInt64.ctz64_two_pow_dvd (y - x))]
    exact Nat.gcd_comm _ _
  · rw [h_shr_toNat', h_sub_toNat]
    calc (y.toNat - x.toNat) / 2 ^ ctz64 64 (y - x)
        ≤ y.toNat - x.toNat := Nat.div_le_self _ _
      _ < y.toNat := by have : 0 < x.toNat := _aux_toNat_pos x hxne; omega

end Wasm
