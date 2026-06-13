import Project.Itoa.Proofs.NaiveU64

/-!
# Naive i64 formatter core

The naive i64 side: `func4` negative-path count/write loops, `func4_spec`
(delegating to `func6` for non-negative inputs), and `func3_spec`.
See `Project.Itoa.Proofs` for the overall proof structure.
-/

namespace Project.Itoa.Proofs

open Wasm

/-! ## Naive i64 core (`func4`): negative-path loops, standalone

For negative inputs `func4` runs its own count/write loops over the
magnitude `m = 0 - n` (frame `[fp, fp+80)`, count slot `fp+4`, peel
slot `fp+8`, write-value slot `fp+16`, write-index slot `fp+28`). The
total length `L = numDigits m + 1` includes the leading `'-'` written
separately at `out`; the write loop fills positions `[1, L)`. -/

set_option maxHeartbeats 1600000 in
private theorem func4_count_loop (env : HostEnv Unit) (n m : UInt64) (cap : UInt32)
    (B : Nat → UInt8) {Q : Assertion Unit} {rest : Program}
    (st1 : Store Unit) (fp out : UInt32)
    (hfp_hi : fp.toNat + 80 ≤ 1048576)
    (hcap : cap.toNat ≤ 32)
    (hpg : st1.mem.pages = 17)
    (hslot4 : st1.mem.read32 (fp + 4) = 1)
    (hslot8 : st1.mem.read64 (fp + 8) = UInt64.ofNat (m.toNat / 10))
    (hpres : ∀ i : Nat, i < fp.toNat ∨ fp.toNat + 80 ≤ i → st1.mem.bytes i = B i)
    (hsucc : ∀ st' : Store Unit,
      st'.mem.pages = 17 →
      st'.globals = st1.globals →
      numDigits m.toNat + 1 ≤ cap.toNat →
      (∀ i : Nat, i < fp.toNat ∨ fp.toNat + 80 ≤ i → st'.mem.bytes i = B i) →
      Q (.Break 0 st'
        { params := [Value.i64 n, Value.i32 out, Value.i32 32, Value.i32 cap],
          locals := [Value.i32 fp, Value.i64 m,
            Value.i32 (UInt32.ofNat (numDigits m.toNat + 1)),
            Value.i32 0, Value.i32 0, Value.i32 0],
          values := [] }))
    (hfail : ∀ st' : Store Unit,
      st'.mem.pages = 17 →
      st'.globals = st1.globals →
      cap.toNat < numDigits m.toNat + 1 →
      (∀ i : Nat, i < fp.toNat ∨ fp.toNat + 80 ≤ i → st'.mem.bytes i = B i) →
      Q (.Break 1 st'
        { params := [Value.i64 n, Value.i32 out, Value.i32 32, Value.i32 cap],
          locals := [Value.i32 fp, Value.i64 m,
            Value.i32 (UInt32.ofNat (numDigits m.toNat + 1)),
            Value.i32 0, Value.i32 0, Value.i32 0],
          values := [] })) :
    wp «module»
      (.loop 0 0 [
        .block 0 0 [
          .localGet 4, .load64 (8 : UInt32), .constI64 (0 : UInt64), .gtUI64,
          .const (1 : UInt32), .and, .br_if 0,
          .localGet 4, .load32 (4 : UInt32), .const (1 : UInt32), .add, .localSet 6,
          .localGet 4, .localGet 6, .store32 (68 : UInt32),
          .localGet 6, .localGet 3, .gtS, .const (1 : UInt32), .and, .br_if 3,
          .br 2 ],
        .localGet 4, .localGet 4, .load32 (4 : UInt32), .const (1 : UInt32), .add,
        .store32 (4 : UInt32),
        .localGet 4, .localGet 4, .load64 (8 : UInt32), .constI64 (10 : UInt64),
        .divUI64, .store64 (8 : UInt32),
        .br 0 ] :: rest) Q st1
      { params := [Value.i64 n, Value.i32 out, Value.i32 32, Value.i32 cap],
        locals := [Value.i32 fp, Value.i64 m, Value.i32 0, Value.i32 0,
          Value.i32 0, Value.i32 0],
        values := [] } env := by
  have t4 : (fp + 4).toNat = fp.toNat + 4 := by
    rw [toNat_add_of_lt _ _ (by simp; omega)]; rfl
  have t8 : (fp + 8).toNat = fp.toNat + 8 := by
    rw [toNat_add_of_lt _ _ (by simp; omega)]; rfl
  have t68 : (fp + 68).toNat = fp.toNat + 68 := by
    rw [toNat_add_of_lt _ _ (by simp; omega)]; rfl
  apply wp_loop_cons
    (Inv := fun st' s' =>
      st'.mem.pages = 17 ∧
      st'.globals = st1.globals ∧
      (∃ c : Nat, 1 ≤ c ∧ c ≤ numDigits m.toNat ∧
        st'.mem.read32 (fp + 4) = UInt32.ofNat c ∧
        st'.mem.read64 (fp + 8) = UInt64.ofNat (m.toNat / 10 ^ c)) ∧
      (∀ i : Nat, i < fp.toNat ∨ fp.toNat + 80 ≤ i → st'.mem.bytes i = B i) ∧
      s' = { params := [Value.i64 n, Value.i32 out, Value.i32 32, Value.i32 cap],
             locals := [Value.i32 fp, Value.i64 m, Value.i32 0, Value.i32 0,
               Value.i32 0, Value.i32 0],
             values := [] })
    (μ := fun st' _ => (st'.mem.read64 (fp + 8)).toNat)
  · -- entry invariant: `c = 1`
    refine ⟨hpg, rfl, ⟨1, le_rfl, numDigits_pos m.toNat, by simpa using hslot4, ?_⟩,
      hpres, rfl⟩
    rw [pow_one]
    exact hslot8
  · -- step
    rintro st' s' ⟨hpg', hgl', ⟨c, hc1, hcL, hslot4', hslot8'⟩, hpres', rfl⟩
    have g4 : ¬ (1114112 < fp.toNat + 4 + 4) := by omega
    have g8 : ¬ (1114112 < fp.toNat + 8 + 8) := by omega
    have g68 : ¬ (1114112 < fp.toNat + 68 + 4) := by omega
    have q4 : fp.toNat ≤ 1114104 := by omega
    have q8 : fp.toNat ≤ 1114096 := by omega
    have q68 : fp.toNat ≤ 1114040 := by omega
    apply wp_block_cons
    wp_run
    simp [hpg', hslot4', hslot8', g4, g8, g68]
    have hvsz : m.toNat / 10 ^ c < 18446744073709551616 := by
      have h1 : m.toNat / 10 ^ c ≤ m.toNat := Nat.div_le_self _ _
      have h2 := UInt64.toNat_lt_size m
      simp [UInt64.size] at h2
      omega
    have hofv : (UInt64.ofNat (m.toNat / 10 ^ c)).toNat = m.toNat / 10 ^ c :=
      UInt64.toNat_ofNat_of_lt' hvsz
    by_cases hv : m.toNat / 10 ^ c = 0
    · -- count loop exits: `v = 0`, so `c` is exactly the digit count
      have hvz : UInt64.ofNat (m.toNat / 10 ^ c) = 0 := by
        apply UInt64.toNat.inj; rw [hofv, hv]; rfl
      simp [hvz]
      have hL : c = numDigits m.toNat := by
        have h10 : m.toNat < 10 ^ c := by
          by_contra hge
          have hb : 0 < 10 ^ c := Nat.pow_pos (by norm_num)
          have : 0 < m.toNat / 10 ^ c := Nat.div_pos (by omega) hb
          omega
        rcases Nat.eq_zero_or_pos m.toNat with h0 | h1
        · have : numDigits m.toNat = 1 := by rw [h0]; exact numDigits_lt_ten (by norm_num)
          omega
        · have hlow := ten_pow_numDigits_le m.toNat h1
          have hlt : 10 ^ (numDigits m.toNat - 1) < 10 ^ c := lt_of_le_of_lt hlow h10
          have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 10)).mp hlt
          omega
      have hc20 : c ≤ 20 := hL ▸ numDigits_toNat_le m
      have hadd1 : (1 : UInt32) + UInt32.ofNat c = UInt32.ofNat (c + 1) := by
        apply UInt32.toNat.inj
        rw [UInt32.toNat_add, UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega),
          UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)]
        simp
        omega
      have hofc1 : (UInt32.ofNat (c + 1)).toNat = c + 1 := by
        rw [UInt32.toNat_ofNat_of_lt']
        simp [UInt32.size]; omega
      have hcmpI : (cap.toInt32 < 1 + Int32.ofNat c) ↔ cap.toNat < c + 1 := by
        rw [show (1 : Int32) + Int32.ofNat c = (UInt32.ofNat (c + 1)).toInt32 from by
              rw [← hadd1]; rfl,
            ltS_small cap (UInt32.ofNat (c + 1)) (by omega) (by rw [hofc1]; omega), hofc1]
      by_cases hgt : cap.toNat < c + 1
      · -- total length exceeds `cap`: `br_if 3` fires
        simp [hcmpI, hgt]
        rw [hadd1, hL]
        apply hfail _ (by simp [hpg']) (by simpa using hgl') (by omega)
        intro i hi
        rw [write32_bytes_of_disjoint _ _ _ _ (by omega)]
        exact hpres' i hi
      · -- fits: `br 2`
        simp [hcmpI, hgt]
        rw [hadd1, hL]
        apply hsucc _ (by simp [hpg']) (by simpa using hgl') (by omega)
        intro i hi
        rw [write32_bytes_of_disjoint _ _ _ _ (by omega)]
        exact hpres' i hi
    · -- count loop continues
      have hpos : (0 : UInt64) < UInt64.ofNat (m.toNat / 10 ^ c) := by
        rw [UInt64.lt_iff_toNat_lt, hofv]
        exact Nat.pos_of_ne_zero hv
      simp [hpos]
      have h10c : 10 ^ c ≤ m.toNat := by
        by_contra hlt
        exact hv (Nat.div_eq_of_lt (by omega))
      have hclt : c < numDigits m.toNat := by
        have hup := lt_ten_pow_numDigits m.toNat
        have : 10 ^ c < 10 ^ numDigits m.toNat := by omega
        exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 10)).mp this
      refine ⟨⟨hgl', ⟨c + 1, by omega, by omega, ?_, ?_⟩, ?_⟩, ?_⟩
      · rw [read32_write64_disjoint _ _ _ _ (by omega), read32_write32_same']
        apply UInt32.toNat.inj
        rw [UInt32.toNat_add, UInt32.toNat_ofNat_of_lt', UInt32.toNat_ofNat_of_lt']
        · simp
          have := numDigits_toNat_le m
          omega
        · have := numDigits_toNat_le m
          simp [UInt32.size]; omega
        · have := numDigits_toNat_le m
          simp [UInt32.size]; omega
      · rw [read64_write32_disjoint _ _ _ _ (by omega), hslot8']
        apply UInt64.toNat.inj
        rw [UInt64.toNat_div, hofv, UInt64.toNat_ofNat_of_lt' (by
          have h1 : m.toNat / 10 ^ (c + 1) ≤ m.toNat / 10 ^ c := by
            rw [pow_succ, ← Nat.div_div_eq_div_mul]
            exact Nat.div_le_self _ _
          have hsz : UInt64.size = 18446744073709551616 := rfl
          omega)]
        rw [pow_succ, ← Nat.div_div_eq_div_mul]
        rfl
      · intro i hi
        rw [write64_bytes_of_disjoint _ _ _ _ (by omega),
            write32_bytes_of_disjoint _ _ _ _ (by omega)]
        exact hpres' i hi
      · rw [read64_write32_disjoint _ _ _ _ (by omega), hslot8', hofv,
          Nat.mod_eq_of_lt hvsz]
        exact Nat.div_lt_self (Nat.pos_of_ne_zero hv) (by norm_num)

set_option maxHeartbeats 1600000 in
private theorem func4_write_loop (env : HostEnv Unit) (n m : UInt64) (cap : UInt32)
    (L : Nat) (B : Nat → UInt8) {Q : Assertion Unit} {rest : Program}
    (st2 : Store Unit) (fp out : UInt32)
    (hfp_hi : fp.toNat + 80 ≤ out.toNat)
    (hout_hi : out.toNat + 32 ≤ 1048576)
    (_hcap : cap.toNat ≤ 32) (_hcle : L ≤ cap.toNat) (hL1 : 1 ≤ L) (hL21 : L ≤ 21)
    (hpg2 : st2.mem.pages = 17)
    (hidx : st2.mem.read32 (fp + 28) = UInt32.ofNat L)
    (hval : st2.mem.read64 (fp + 16) = m)
    (hpres : ∀ j : Nat, j < fp.toNat ∨ (fp.toNat + 80 ≤ j ∧ j < out.toNat + 1) ∨
        out.toNat + 32 ≤ j →
      st2.mem.bytes j = B j)
    (hexit : ∀ (st' : Store Unit) (w7 w8 : Value),
      st'.mem.pages = 17 →
      st'.globals = st2.globals →
      st'.mem.read32 fp = UInt32.ofNat L →
      (∀ p : Nat, 1 ≤ p → p < L →
        st'.mem.bytes (out.toNat + p) = UInt8.ofNat (48 + m.toNat / 10 ^ (L - 1 - p) % 10)) →
      (∀ j : Nat, j < fp.toNat ∨ (fp.toNat + 80 ≤ j ∧ j < out.toNat + 1) ∨
          out.toNat + 32 ≤ j →
        st'.mem.bytes j = B j) →
      Q (.Break 0 st'
        { params := [Value.i64 n, Value.i32 out, Value.i32 32, Value.i32 cap],
          locals := [Value.i32 fp, Value.i64 m, Value.i32 (UInt32.ofNat L), w7, w8,
            Value.i32 0],
          values := [] })) :
    wp «module»
      (.loop 0 0 [
        .block 0 0 [
          .localGet 4, .load32 (28 : UInt32), .const (1 : UInt32), .gtU,
          .const (1 : UInt32), .and, .br_if 0,
          .localGet 4, .localGet 6, .store32 (0 : UInt32),
          .br 2 ],
        .localGet 4, .localGet 4, .load32 (28 : UInt32), .const (1 : UInt32), .sub,
        .store32 (28 : UInt32),
        .localGet 4, .load64 (16 : UInt32), .constI64 (10 : UInt64), .remUI64, .wrapI64,
        .localSet 7,
        .localGet 4, .load32 (28 : UInt32), .localSet 8,
        .block 0 0 [
          .localGet 8, .localGet 2, .ltU, .const (1 : UInt32), .and, .eqz, .br_if 0,
          .localGet 1, .localGet 8, .add, .localGet 7, .const (48 : UInt32), .add,
          .store8 (0 : UInt32),
          .localGet 4, .localGet 4, .load64 (16 : UInt32), .constI64 (10 : UInt64),
          .divUI64, .store64 (16 : UInt32),
          .br 1 ]
      ] :: rest) Q st2
      { params := [Value.i64 n, Value.i32 out, Value.i32 32, Value.i32 cap],
        locals := [Value.i32 fp, Value.i64 m, Value.i32 (UInt32.ofNat L), Value.i32 0,
          Value.i32 0, Value.i32 0],
        values := [] } env := by
  have t16 : (fp + 16).toNat = fp.toNat + 16 := by
    rw [toNat_add_of_lt _ _ (by simp; omega)]; rfl
  have t28 : (fp + 28).toNat = fp.toNat + 28 := by
    rw [toNat_add_of_lt _ _ (by simp; omega)]; rfl
  apply wp_loop_cons
    (Inv := fun st' s' =>
      st'.mem.pages = 17 ∧
      st'.globals = st2.globals ∧
      (∃ i : Nat, 1 ≤ i ∧ i ≤ L ∧
        st'.mem.read32 (fp + 28) = UInt32.ofNat i ∧
        st'.mem.read64 (fp + 16) = UInt64.ofNat (m.toNat / 10 ^ (L - i)) ∧
        (∀ p : Nat, i ≤ p → p < L → st'.mem.bytes (out.toNat + p) =
            UInt8.ofNat (48 + m.toNat / 10 ^ (L - 1 - p) % 10)) ∧
        (∀ j : Nat, j < fp.toNat ∨ (fp.toNat + 80 ≤ j ∧ j < out.toNat + 1) ∨
            out.toNat + 32 ≤ j →
            st'.mem.bytes j = B j)) ∧
      (∃ w7 w8 : Value,
        s' = { params := [Value.i64 n, Value.i32 out, Value.i32 32, Value.i32 cap],
               locals := [Value.i32 fp, Value.i64 m, Value.i32 (UInt32.ofNat L), w7, w8,
                 Value.i32 0],
               values := [] }))
    (μ := fun st' _ => (st'.mem.read32 (fp + 28)).toNat)
  · -- entry invariant: `i = L`, value slot holds `m`
    refine ⟨hpg2, rfl, ⟨L, hL1, le_rfl, hidx, ?_, fun p hp1 hp2 => absurd hp1 (by omega),
      hpres⟩, Value.i32 0, Value.i32 0, rfl⟩
    rw [Nat.sub_self, pow_zero, Nat.div_one, UInt64.ofNat_toNat]
    exact hval
  · -- step
    rintro st3 s3 ⟨hpg3, hgl3, ⟨i, hi1, hiL, hidx3, hval3, hdig3, hpres3⟩, w7, w8, rfl⟩
    have g0 : ¬ (1114112 < fp.toNat + 4) := by omega
    have g16 : ¬ (1114112 < fp.toNat + 16 + 8) := by omega
    have g28 : ¬ (1114112 < fp.toNat + 28 + 4) := by omega
    have q0 : fp.toNat ≤ 1114108 := by omega
    have q16 : fp.toNat ≤ 1114088 := by omega
    have q28 : fp.toNat ≤ 1114080 := by omega
    apply wp_block_cons
    wp_run
    simp [hpg3, hidx3, g0, g16, g28]
    have hofi : (UInt32.ofNat i).toNat = i := by
      rw [UInt32.toNat_ofNat_of_lt']
      simp [UInt32.size]; omega
    by_cases hi0 : i = 1
    · -- exit: store the total length into the result slot, `br 2`
      have hz : UInt32.ofNat i = 1 := by rw [hi0]; rfl
      simp [hz]
      apply hexit
      · simp [hpg3]
      · simpa using hgl3
      · rw [read32_write32_same']
      · intro p hp1 hp
        rw [read32_write32_bytes, if_neg (by omega), if_neg (by omega),
          if_neg (by omega), if_neg (by omega)]
        exact hdig3 p (by omega) hp
      · intro j hj
        rw [read32_write32_bytes, if_neg (by omega), if_neg (by omega),
          if_neg (by omega), if_neg (by omega)]
        exact hpres3 j hj
    · -- one more digit to write
      have hpos2 : (1 : UInt32) < UInt32.ofNat i := by
        rw [UInt32.lt_iff_toNat_lt, hofi]
        simp; omega
      simp [hpos2]
      apply wp_block_cons
      wp_run
      have him1 : UInt32.ofNat i - 1 = UInt32.ofNat (i - 1) := by
        apply UInt32.toNat.inj
        rw [UInt32.toNat_sub_of_le _ _ (by
          rw [UInt32.le_iff_toNat_le]
          simpa [hofi] using (by omega : 1 ≤ i)), hofi]
        rw [UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)]
        rfl
      have hofim1 : (UInt32.ofNat (i - 1)).toNat = i - 1 := by
        rw [UInt32.toNat_ofNat_of_lt']
        simp [UInt32.size]; omega
      have hguard : UInt32.ofNat (i - 1) < 32 := by
        rw [UInt32.lt_iff_toNat_lt, hofim1]
        simp; omega
      have haddr : (UInt32.ofNat (i - 1) + out).toNat = out.toNat + (i - 1) := by
        rw [UInt32.toNat_add, hofim1]
        have : (i - 1) + out.toNat < UInt32.size := by simp [UInt32.size]; omega
        rw [Nat.mod_eq_of_lt this]
        omega
      have hnb : ¬ (1114112 ≤ out.toNat + (i - 1)) := by omega
      have hd64 : m.toNat / 10 ^ (L - i) < 18446744073709551616 := by
        have h1 : m.toNat / 10 ^ (L - i) ≤ m.toNat := Nat.div_le_self _ _
        have h2 := UInt64.toNat_lt_size m
        simp [UInt64.size] at h2
        omega
      have hd : m.toNat / 10 ^ (L - i) % 18446744073709551616 % 10 % 4294967296 =
          m.toNat / 10 ^ (L - i) % 10 := by
        rw [Nat.mod_eq_of_lt hd64, Nat.mod_eq_of_lt (by omega)]
      have hrv : (st3.mem.write32 (fp + 28) (UInt32.ofNat (i - 1))).read64 (fp + 16) =
          UInt64.ofNat (m.toNat / 10 ^ (L - i)) := by
        rw [read64_write32_disjoint _ _ _ _ (by omega)]
        exact hval3
      simp [him1, hguard, hrv, hd, haddr, hpg3, hnb, g16]
      -- `hd`'s nested-mod shape makes every later `omega` pathologically
      -- slow (minutes each); drop it now that the simp consumed it.
      clear hd
      refine ⟨⟨hgl3, ⟨i - 1, by omega, by omega, ?_, ?_, ?_, ?_⟩⟩, ?_⟩
      · rw [read32_write64_disjoint _ _ _ _ (by omega),
          read32_write8_disjoint _ _ _ _ (by omega), read32_write32_same']
      · rw [read64_write8_disjoint _ _ _ _ (by omega),
          read64_write32_disjoint _ _ _ _ (by omega), hval3]
        apply UInt64.toNat.inj
        have hsz : UInt64.size = 18446744073709551616 := rfl
        rw [UInt64.toNat_div, UInt64.toNat_ofNat_of_lt' (by omega),
          UInt64.toNat_ofNat_of_lt' (by
            have h1 : m.toNat / 10 ^ (L - (i - 1)) ≤ m.toNat / 10 ^ (L - i) := by
              rw [show L - (i - 1) = (L - i) + 1 from by omega, pow_succ,
                ← Nat.div_div_eq_div_mul]
              exact Nat.div_le_self _ _
            omega)]
        rw [show L - (i - 1) = (L - i) + 1 from by omega, pow_succ,
          ← Nat.div_div_eq_div_mul]
        rfl
      · intro p hp1 hp2
        rw [write64_bytes_of_disjoint _ _ _ _ (by omega)]
        by_cases hpe : p = i - 1
        · subst hpe
          rw [read8_write8_bytes, if_pos (by omega),
            show L - 1 - (i - 1) = L - i from by omega]
        · rw [read8_write8_bytes, if_neg (by omega),
            write32_bytes_of_disjoint _ _ _ _ (by omega),
            hdig3 p (by omega) hp2]
          exact (digit_add8 _ (Nat.mod_lt _ (by norm_num))).symm
      · intro j hj
        rw [write64_bytes_of_disjoint _ _ _ _ (by omega),
          read8_write8_bytes, if_neg (by omega),
          write32_bytes_of_disjoint _ _ _ _ (by omega)]
        exact hpres3 j (by omega)
      · rw [read32_write64_disjoint _ _ _ _ (by omega),
          read32_write8_disjoint _ _ _ _ (by omega), read32_write32_same', hofim1,
          Nat.mod_eq_of_lt (by omega)]
        omega

set_option maxRecDepth 10000 in
/-- `n` (as i64) is non-negative iff its `toNat` is below `2^63` (`≤`-form). -/
private theorem i64_nonneg_bridge (n : UInt64) :
    ((0 : Int64) ≤ n.toInt64) ↔ (n.toNat < 9223372036854775808) := by
  rw [Int64.le_iff_toInt_le, show ((0 : Int64)).toInt = 0 from by decide,
    show n.toInt64.toInt = n.toInt64.toBitVec.toInt from rfl, BitVec.toInt_eq_toNat_bmod,
    show n.toInt64.toBitVec.toNat = n.toNat from rfl, Int.bmod]
  have hb : n.toNat < 18446744073709551616 := by
    have := UInt64.toNat_lt n; simpa [UInt64.size] using this
  norm_num; omega

set_option maxHeartbeats 16000000 in
/-- `func4`: the naive i64 formatter core. For non-negative `n` it delegates
to `func6`; for negative `n` it writes `'-'` and formats the magnitude with
its own loops. -/
theorem func4_spec (env : HostEnv Unit) (st0 : Store Unit) (g out : UInt32)
    (n : UInt64) (cap : UInt32)
    (hpg : st0.mem.pages = 17)
    (hg : st0.globals.globals[0]? = some (.i32 g))
    (hg144 : 144 ≤ g.toNat) (hgout : g.toNat ≤ out.toNat)
    (hout : out.toNat + 32 ≤ 1048576)
    (hcap : cap.toNat ≤ 32) :
    TerminatesWith env «module» 4 st0 [.i32 cap, .i32 32, .i32 out, .i64 n]
      (fun st' rs =>
        st'.mem.pages = 17 ∧
        st'.globals.globals[0]? = some (.i32 g) ∧
        rs = [.i32 (if i64len n ≤ cap.toNat
                    then UInt32.ofNat (i64len n) else 4294967295)] ∧
        (i64len n ≤ cap.toNat → HasDigitsI64 st'.mem out.toNat n) ∧
        (∀ i : Nat, i < g.toNat - 144 ∨ (g.toNat ≤ i ∧ i < out.toNat) ∨
            out.toNat + 32 ≤ i →
          st'.mem.bytes i = st0.mem.bytes i)) := by
  obtain ⟨hglen, -⟩ := List.getElem?_eq_some_iff.mp hg
  have hfp : (g - 80).toNat = g.toNat - 80 := by
    rw [UInt32.toNat_sub_of_le g 80 (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
    rfl
  have t4 : (g - 80 + 4).toNat = g.toNat - 80 + 4 := by
    rw [UInt32.toNat_add, hfp]; simp; omega
  have t8 : (g - 80 + 8).toNat = g.toNat - 80 + 8 := by
    rw [UInt32.toNat_add, hfp]; simp; omega
  have t16 : (g - 80 + 16).toNat = g.toNat - 80 + 16 := by
    rw [UInt32.toNat_add, hfp]; simp; omega
  have t28 : (g - 80 + 28).toNat = g.toNat - 80 + 28 := by
    rw [UInt32.toNat_add, hfp]; simp; omega
  have t32 : (g - 80 + 32).toNat = g.toNat - 80 + 32 := by
    rw [UInt32.toNat_add, hfp]; simp; omega
  have t44 : (g - 80 + 44).toNat = g.toNat - 80 + 44 := by
    rw [UInt32.toNat_add, hfp]; simp; omega
  have t48 : (g - 80 + 48).toNat = g.toNat - 80 + 48 := by
    rw [UInt32.toNat_add, hfp]; simp; omega
  have t52 : (g - 80 + 52).toNat = g.toNat - 80 + 52 := by
    rw [UInt32.toNat_add, hfp]; simp; omega
  have t56 : (g - 80 + 56).toNat = g.toNat - 80 + 56 := by
    rw [UInt32.toNat_add, hfp]; simp; omega
  have t68 : (g - 80 + 68).toNat = g.toNat - 80 + 68 := by
    rw [UInt32.toNat_add, hfp]; simp; omega
  have t72 : (g - 80 + 72).toNat = g.toNat - 80 + 72 := by
    rw [UInt32.toNat_add, hfp]; simp; omega
  have hback : 80 + (g - 80) = g := by
    apply UInt32.toNat.inj
    rw [UInt32.toNat_add, hfp]; simp; omega
  have p0 : ¬ (1114112 < g.toNat - 80 + 4) := by omega
  have p4 : ¬ (1114112 < g.toNat - 80 + 4 + 4) := by omega
  have p8 : ¬ (1114112 < g.toNat - 80 + 8 + 8) := by omega
  have p16 : ¬ (1114112 < g.toNat - 80 + 16 + 8) := by omega
  have p28 : ¬ (1114112 < g.toNat - 80 + 28 + 4) := by omega
  have p32 : ¬ (1114112 < g.toNat - 80 + 32 + 8) := by omega
  have p44 : ¬ (1114112 < g.toNat - 80 + 44 + 4) := by omega
  have p48 : ¬ (1114112 < g.toNat - 80 + 48 + 4) := by omega
  have p52 : ¬ (1114112 < g.toNat - 80 + 52 + 4) := by omega
  have p56 : ¬ (1114112 < g.toNat - 80 + 56 + 8) := by omega
  have p72 : ¬ (1114112 < g.toNat - 80 + 72 + 8) := by omega
  have q0 : g.toNat - 80 ≤ 1114108 := by omega
  have q4 : g.toNat - 80 ≤ 1114104 := by omega
  have q8 : g.toNat - 80 ≤ 1114096 := by omega
  have q16 : g.toNat - 80 ≤ 1114088 := by omega
  have q28 : g.toNat - 80 ≤ 1114080 := by omega
  have q32 : g.toNat - 80 ≤ 1114072 := by omega
  have q44 : g.toNat - 80 ≤ 1114064 := by omega
  have q48 : g.toNat - 80 ≤ 1114060 := by omega
  have q52 : g.toNat - 80 ≤ 1114056 := by omega
  have q56 : g.toNat - 80 ≤ 1114048 := by omega
  have q72 : g.toNat - 80 ≤ 1114032 := by omega
  have hob : ¬ (1114112 ≤ out.toNat) := by omega
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i64, .i32, .i32, .i32], [.i32, .i64, .i32, .i32, .i32, .i32], func4,
      [.i32]⟩) rfl
  unfold func4
  wp_run
  simp [hg, hpg, hfp, p32, p44, p48, p52]
  apply wp_block_cons
  apply wp_block_cons
  apply wp_block_cons
  wp_run
  by_cases hsgn : (0 : Int64) ≤ n.toInt64
  · -- non-negative: delegate to `func6`
    have hneg : n.toNat < 9223372036854775808 := (i64_nonneg_bridge n).mp hsgn
    simp [hsgn]
    have hmag : i64mag n = n.toNat := by
      unfold i64mag; rw [if_neg (by omega)]
    have hlen : i64len n = numDigits n.toNat := by
      unfold i64len; rw [hmag, if_neg (by omega)]; omega
    apply wp_call_of_terminates_frame
      (args := [.i32 cap, .i32 32, .i32 out, .i64 n]) (rem := [.i32 (g - 80)])
      (f := ⟨[.i64, .i32, .i32, .i32], [.i32, .i32, .i32, .i32], func6, [.i32]⟩)
      rfl rfl rfl rfl
      (func6_spec env _ (g - 80) out n cap
        (by simp [hpg]) (by simp [List.getElem?_set_self hglen])
        (by omega) (by omega) hout hcap)
    rintro st' vs ⟨hpg', hg', hrs, hdig, hpres⟩
    obtain ⟨hglen', -⟩ := List.getElem?_eq_some_iff.mp hg'
    subst hrs
    wp_run
    simp [hpg', hg', hback, hfp, p0, q0, List.getElem?_set_self hglen']
    refine ⟨?_, ?_, ?_⟩
    · rw [hlen]
    · rw [hlen]
      intro hfits
      rw [HasDigitsI64, if_neg (by omega), hmag]
      intro j hj
      rw [write32_bytes_of_disjoint _ _ _ _ (by omega)]
      exact hdig hfits j hj
    · intro i hi
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      have hstep := hpres i (by omega)
      rw [hstep]
      rw [write32_bytes_of_disjoint _ _ _ _ (by omega),
          write32_bytes_of_disjoint _ _ _ _ (by omega),
          write32_bytes_of_disjoint _ _ _ _ (by omega),
          write64_bytes_of_disjoint _ _ _ _ (by omega)]
  · -- negative: write `'-'` then format the magnitude
    have hneg : ¬ n.toNat < 9223372036854775808 :=
      fun h => hsgn ((i64_nonneg_bridge n).mpr h)
    simp [hsgn, p4, p8, p56, p72, hpg, hfp]
    have hmag : i64mag n = (0 - n).toNat := by
      unfold i64mag; rw [if_pos (by omega)]
    have hlen : i64len n = numDigits (0 - n).toNat + 1 := by
      unfold i64len; rw [hmag, if_pos (by omega)]
    apply wp_block_cons
    apply wp_block_cons
    apply wp_block_cons
    apply wp_block_cons
    apply wp_block_cons
    apply func4_count_loop env n (0 - n) cap st0.mem.bytes _ (g - 80) out
      (by omega) hcap
    · -- pages after prologue + negative setup
      simp [hpg]
    · -- count slot = 1
      rw [read32_write64_disjoint _ _ _ _ (by omega), read32_write32_same']
    · -- peel slot = m / 10
      rw [read64_write64_same]
      apply UInt64.toNat.inj
      rw [UInt64.toNat_ofNat_of_lt']
      · exact UInt64.toNat_div (0 - n) 10
      · have := UInt64.toNat_lt_size (0 - n)
        have : (0 - n).toNat / 10 ≤ (0 - n).toNat := Nat.div_le_self _ _
        omega
    · -- bytes outside the frame untouched by prologue + setup
      intro i hi
      rw [write64_bytes_of_disjoint _ _ _ _ (by omega),
          write32_bytes_of_disjoint _ _ _ _ (by omega),
          write64_bytes_of_disjoint _ _ _ _ (by omega),
          write64_bytes_of_disjoint _ _ _ _ (by omega),
          write32_bytes_of_disjoint _ _ _ _ (by omega),
          write32_bytes_of_disjoint _ _ _ _ (by omega),
          write32_bytes_of_disjoint _ _ _ _ (by omega),
          write64_bytes_of_disjoint _ _ _ _ (by omega)]
    · -- fits: `'-'`, slots for the write loop, the write loop, epilogue
      intro st' hpg' hgl' hfits hpres'
      simp only []
      wp_run
      simp [hpg', hob, hfp, p16, p28]
      have hmod : (UInt64.size - n.toNat) % UInt64.size = (0 - n).toNat := by simp
      have hsplit : UInt32.ofNat (numDigits (0 - n).toNat) + 1 =
          UInt32.ofNat (numDigits (0 - n).toNat + 1) := by
        apply UInt32.toNat.inj
        rw [UInt32.toNat_add,
          UInt32.toNat_ofNat_of_lt' (by
            have := numDigits_toNat_le (0 - n)
            rw [show UInt32.size = 4294967296 from rfl]; omega),
          UInt32.toNat_ofNat_of_lt' (by
            have := numDigits_toNat_le (0 - n)
            rw [show UInt32.size = 4294967296 from rfl]; omega),
          show (1 : UInt32).toNat = 1 from rfl]
        rw [Nat.mod_eq_of_lt (by
          have := numDigits_toNat_le (0 - n)
          omega)]
      rw [show (-n : UInt64) = 0 - n from by bv_decide, hmod, hsplit]
      apply func4_write_loop env n (0 - n) cap (numDigits (0 - n).toNat + 1)
        (fun j => if j = out.toNat then 45 else st0.mem.bytes j) _ (g - 80) out
        (by omega) hout hcap hfits (by omega)
        (by have := numDigits_toNat_le (0 - n); omega)
      · simp [hpg']
      · -- index slot = L
        rw [read32_write32_same']
      · -- value slot = m
        rw [read64_write32_disjoint _ _ _ _ (by omega), read64_write64_same]
      · -- preservation through `'-'` and the two slot stores
        intro j hj
        rw [write32_bytes_of_disjoint _ _ _ _ (by omega),
            write64_bytes_of_disjoint _ _ _ _ (by omega)]
        by_cases hje : j = out.toNat
        · subst hje
          rw [read8_write8_bytes, if_pos (by omega), if_pos rfl]
        · rw [read8_write8_bytes, if_neg (by omega), if_neg hje]
          exact hpres' j (by omega)
      · -- write-loop exit: epilogue
        intro st2 w7 w8 hpg2 hgl2 hres hdig hpres2
        simp only []
        wp_run
        simp [hpg2, hres, hgl2, hgl', hback, hfp, q0,
          List.getElem?_set_self (by simpa using hglen)]
        refine ⟨?_, ?_, ?_⟩
        · rw [hlen, hmod, hsplit, if_pos (by omega)]
        · rw [hlen]
          intro _
          rw [HasDigitsI64, if_pos (by omega), hmag]
          constructor
          · have h45 := hpres2 out.toNat (by omega)
            rw [if_pos rfl] at h45
            exact h45
          · intro j hjd
            have := hdig (j + 1) (by omega) (by omega)
            rw [show numDigits (0 - n).toNat + 1 - 1 - (j + 1) =
              numDigits (0 - n).toNat - 1 - j from by omega] at this
            rw [show out.toNat + 1 + j = out.toNat + (j + 1) from by omega]
            exact this
        · intro i hi
          have hstep := hpres2 i (by omega)
          rw [hstep, if_neg (by omega)]
    · -- capacity exceeded: store `-1`, epilogue
      intro st' hpg' hgl' hover hpres'
      simp only []
      wp_run
      simp [hpg', hgl', hback, hfp, p0, q0,
        List.getElem?_set_self (by simpa using hglen)]
      refine ⟨fun h => absurd h (by rw [hlen] at h; omega),
        fun h => absurd h (by rw [hlen] at h; omega), ?_⟩
      intro i hi
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      exact hpres' i (by omega)

/-! ## `func3_spec`: the naive i64 wrapper

A 32-byte shadow-stack wrapper: spill `(n, out, outLen, cap)` into a
fresh frame, forward to `func4`, restore the stack pointer. -/

set_option maxHeartbeats 1600000 in
theorem func3_spec (env : HostEnv Unit) (st0 : Store Unit) (g out : UInt32)
    (n : UInt64) (cap : UInt32)
    (hpg : st0.mem.pages = 17)
    (hg : st0.globals.globals[0]? = some (.i32 g))
    (hg176 : 176 ≤ g.toNat) (hgout : g.toNat ≤ out.toNat)
    (hout : out.toNat + 32 ≤ 1048576)
    (hcap : cap.toNat ≤ 32) :
    TerminatesWith env «module» 3 st0 [.i32 cap, .i32 32, .i32 out, .i64 n]
      (fun st' rs =>
        st'.mem.pages = 17 ∧
        st'.globals.globals[0]? = some (.i32 g) ∧
        rs = [.i32 (if i64len n ≤ cap.toNat
                    then UInt32.ofNat (i64len n) else 4294967295)] ∧
        (i64len n ≤ cap.toNat → HasDigitsI64 st'.mem out.toNat n) ∧
        (∀ i : Nat, i < g.toNat - 176 ∨ (g.toNat ≤ i ∧ i < out.toNat) ∨
            out.toNat + 32 ≤ i →
          st'.mem.bytes i = st0.mem.bytes i)) := by
  obtain ⟨hglen, -⟩ := List.getElem?_eq_some_iff.mp hg
  have hsub : (g - 32).toNat = g.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le g 32 (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
    rfl
  have t8 : (g - 32 + 8).toNat = g.toNat - 32 + 8 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t20 : (g - 32 + 20).toNat = g.toNat - 32 + 20 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t24 : (g - 32 + 24).toNat = g.toNat - 32 + 24 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t28 : (g - 32 + 28).toNat = g.toNat - 32 + 28 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have hback : 32 + (g - 32) = g := by
    apply UInt32.toNat.inj
    rw [UInt32.toNat_add, hsub]; simp; omega
  have p8 : ¬ (1114112 < g.toNat - 32 + 8 + 8) := by omega
  have p20 : ¬ (1114112 < g.toNat - 32 + 20 + 4) := by omega
  have p24 : ¬ (1114112 < g.toNat - 32 + 24 + 4) := by omega
  have p28 : ¬ (1114112 < g.toNat - 32 + 28 + 4) := by omega
  have q8 : g.toNat - 32 ≤ 1114096 := by omega
  have q20 : g.toNat - 32 ≤ 1114088 := by omega
  have q24 : g.toNat - 32 ≤ 1114084 := by omega
  have q28 : g.toNat - 32 ≤ 1114080 := by omega
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i64, .i32, .i32, .i32], [.i32, .i32], func3, [.i32]⟩) rfl
  unfold func3
  wp_run
  simp [hg, hpg, hsub, p8, p20, p24, p28]
  apply wp_call_of_terminates (func4_spec env _ (g - 32) out n cap
    (by simp [hpg]) (by simp [List.getElem?_set_self hglen])
    (by omega) (by omega) hout hcap)
  rintro st' vs ⟨hpg', hg', hrs, hdig, hpres⟩
  obtain ⟨hglen', -⟩ := List.getElem?_eq_some_iff.mp hg'
  subst hrs
  wp_run
  simp [hg', hback, hpg', List.getElem?_set_self hglen']
  refine ⟨hdig, ?_⟩
  intro i hi
  have hstep := hpres i (by omega)
  rw [hstep]
  rw [write32_bytes_of_disjoint _ _ _ _ (by omega),
      write32_bytes_of_disjoint _ _ _ _ (by omega),
      write32_bytes_of_disjoint _ _ _ _ (by omega),
      write64_bytes_of_disjoint _ _ _ _ (by omega)]


end Project.Itoa.Proofs
