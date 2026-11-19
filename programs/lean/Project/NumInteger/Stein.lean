import CodeLib.UInt64

/-!
# Stein's binary GCD on `u64`: step and recombine lemmas

The arithmetic facts shared by the three compiled binary-GCD programs
(`Project.NumInteger`, `Project.NumIntegerOpt3`, `Project.GcdStdio`):

* `UInt64.recombine_loop` — shifting the common odd-part GCD left by
  `ctz64 (b ||| a)` yields `gcd a b`;
* `UInt64.stein_step_x`, `UInt64.stein_step_y` — one subtract-and-halve
  iteration keeps the odd operand nonzero and odd, preserves the GCD, and
  strictly decreases the larger operand.

They combine the general `ctz64` facts of `CodeLib.UInt64` with `Nat.gcd`
algebra (Stein's identity and coprimality with powers of two).
-/

namespace Wasm

private theorem _aux_toNat_pos (a : UInt64) (ha : a ≠ 0) : 0 < a.toNat := by
  rcases Nat.eq_zero_or_pos a.toNat with h | h
  · exact absurd (UInt64.toNat_inj.mp (by simpa using h)) ha
  · exact h

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

These bundle the `ctz64` structural theorems of `CodeLib.UInt64` with
`Nat.gcd` algebra into the exact forms the wasm-level proofs need. -/

/-- `b ||| a ≠ 0` when `b ≠ 0`. -/
private theorem _aux_or_ne_zero (a b : UInt64) (hb : b ≠ 0) : b ||| a ≠ 0 :=
  fun h => hb (UInt64.or_eq_zero_iff.mp h).1

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
  rw [UInt64.toNat_shiftLeft, UInt64.toNat_ofNat', h_or_mask,
      Nat.mod_eq_of_lt h_ctz_or_lt, Nat.mod_eq_of_lt h_gcd_lt_64,
      Nat.shiftLeft_eq, h_o, h_ctz_or, Nat.min_comm, h_stein, Nat.mul_comm]
  refine Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.le_of_eq ?_) h_gcd_lt_64)
  linarith [h_stein, Nat.mul_comm (2 ^ min (ctz64 64 a) (ctz64 64 b))
    ((a.toNat / 2 ^ ctz64 64 a).gcd (b.toNat / 2 ^ ctz64 64 b))]

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
  rw [Nat.gcd_self] at h; exact h

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
    (_hxodd : x.toNat % 2 = 1) (hyodd : y.toNat % 2 = 1) (hlt : y < x) :
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
  · rw [h_shr_toNat', ← h_shr_toNat]; exact UInt64.shr_ctz_toNat_odd (x - y) h_sub_ne
  · rw [h_shr_toNat', h_sub_toNat]; exact _aux_gcd_sub_div_pow2 x.toNat y.toNat _ hxle_nat hyodd
      (by rw [← h_sub_toNat]; exact UInt64.ctz64_two_pow_dvd (x - y))
  · rw [h_shr_toNat', h_sub_toNat]
    calc (x.toNat - y.toNat) / 2 ^ ctz64 64 (x - y)
        ≤ x.toNat - y.toNat := Nat.div_le_self _ _
      _ < x.toNat := by have : 0 < y.toNat := _aux_toNat_pos y hyne; omega

/-- One iteration in the `x ≤ y, x ≠ y` branch. -/
theorem UInt64.stein_step_y (x y : UInt64) (hxne : x ≠ 0) (_hyne : y ≠ 0)
    (hxodd : x.toNat % 2 = 1) (_hyodd : y.toNat % 2 = 1) (hle : ¬ y < x)
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
  · rw [h_shr_toNat', ← h_shr_toNat]; exact UInt64.shr_ctz_toNat_odd (y - x) h_sub_ne
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
