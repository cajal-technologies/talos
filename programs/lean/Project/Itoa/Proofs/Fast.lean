import Project.Itoa.Proofs.NaiveI64

/-!
# Harness byte-compare loop and fast-formatter helpers

The harness byte-compare loop (`harness_compare_loop`, shared by `func23`
and `func21`) and the fast-formatter helper specs (`func40`'s callee
closure: `func10`/`func25`/`func37`-`func39`/`func41`/`func42`/`func45`-`func49`).
See `Project.Itoa.Proofs` for the overall proof structure.
-/

namespace Project.Itoa.Proofs

open Wasm

/-! ## The harness byte-compare loop, standalone

The tail of `func23`/`func21` (textually identical in both): walk the
index slot `fp+68` over `[0, len)`, comparing the fast buffer at
`[fp, fp+32)` against the naive buffer at `[fp+32, fp+64)` byte by
byte, trapping (`call 17`) on any disagreement. Under the hypothesis
that both buffers hold the same bytes `D` on `[0, len)`, the loop
always exits cleanly via `br_if 1` (`.Break 0` at the loop level),
touching only the index slot. -/

set_option maxHeartbeats 1600000 in
theorem harness_compare_loop (env : HostEnv Unit) (n : UInt64) (cap : UInt32)
    (lenv : UInt32) (D B : Nat → UInt8) {Q : Assertion Unit} {rest : Program}
    (st1 : Store Unit) (fp : UInt32)
    (w3 w4 w5 w7 w8 w9 w10 w11 : Value)
    (hfp_hi : fp.toNat + 96 ≤ 1048576)
    (hL : lenv.toNat ≤ 32)
    (hpg : st1.mem.pages = 17)
    (hidx : st1.mem.read32 (fp + 68) = 0)
    (hpres : ∀ j : Nat, j < fp.toNat + 68 ∨ fp.toNat + 72 ≤ j →
      st1.mem.bytes j = B j)
    (hfast : ∀ j : Nat, j < lenv.toNat → B (fp.toNat + j) = D j)
    (hnaive : ∀ j : Nat, j < lenv.toNat → B (fp.toNat + 32 + j) = D j)
    (hexit : ∀ (st' : Store Unit) (w8' w9' w10' w11' : Value),
      st'.mem.pages = 17 →
      st'.globals = st1.globals →
      (∀ j : Nat, j < fp.toNat + 68 ∨ fp.toNat + 72 ≤ j →
        st'.mem.bytes j = B j) →
      Q (.Break 0 st'
        { params := [Value.i64 n, Value.i32 cap],
          locals := [Value.i32 fp, w3, w4, w5, Value.i32 lenv, w7,
            w8', w9', w10', w11'],
          values := [] })) :
    wp «module»
      (.loop 0 0 [
        .localGet 2, .load32 (68 : UInt32), .localGet 6, .ltU,
        .const (1 : UInt32), .and, .eqz, .br_if 1,
        .localGet 2, .load32 (68 : UInt32), .localSet 8,
        .block 0 0 [
          .block 0 0 [
            .block 0 0 [
              .block 0 0 [
                .block 0 0 [
                  .localGet 8, .const (32 : UInt32), .ltU, .const (1 : UInt32),
                  .and, .eqz, .br_if 0,
                  .localGet 2, .localGet 8, .add, .load8U (0 : UInt32), .localSet 9,
                  .localGet 2, .load32 (68 : UInt32), .localSet 10,
                  .localGet 10, .const (32 : UInt32), .ltU, .const (1 : UInt32),
                  .and, .br_if 1,
                  .br 2 ],
                .localGet 8, .const (32 : UInt32), .const (1049048 : UInt32),
                .call 102, .unreachable ],
              .localGet 2, .const (32 : UInt32), .add, .localGet 10, .add,
              .load8U (0 : UInt32), .localSet 11,
              .localGet 9, .const (255 : UInt32), .and, .localGet 11,
              .const (255 : UInt32), .and, .ne, .const (1 : UInt32), .and,
              .br_if 2, .br 1 ],
            .localGet 10, .const (32 : UInt32), .const (1049064 : UInt32),
            .call 102, .unreachable ],
          .localGet 2, .localGet 2, .load32 (68 : UInt32), .const (1 : UInt32),
          .add, .store32 (68 : UInt32), .br 1 ]
      ] :: rest) Q st1
      { params := [Value.i64 n, Value.i32 cap],
        locals := [Value.i32 fp, w3, w4, w5, Value.i32 lenv, w7, w8, w9, w10, w11],
        values := [] } env := by
  have t68 : (fp + 68).toNat = fp.toNat + 68 := by
    rw [toNat_add_of_lt _ _ (by simp; omega)]; rfl
  apply wp_loop_cons
    (Inv := fun st' s' =>
      st'.mem.pages = 17 ∧
      st'.globals = st1.globals ∧
      (∃ k : Nat, k ≤ lenv.toNat ∧
        st'.mem.read32 (fp + 68) = UInt32.ofNat k ∧
        (∀ j : Nat, j < fp.toNat + 68 ∨ fp.toNat + 72 ≤ j →
          st'.mem.bytes j = B j)) ∧
      (∃ v8 v9 v10 v11 : Value,
        s' = { params := [Value.i64 n, Value.i32 cap],
               locals := [Value.i32 fp, w3, w4, w5, Value.i32 lenv, w7,
                 v8, v9, v10, v11],
               values := [] }))
    (μ := fun st' _ => lenv.toNat - (st'.mem.read32 (fp + 68)).toNat)
  · -- entry invariant: `k = 0`
    exact ⟨hpg, rfl, ⟨0, by omega, by simpa using hidx, hpres⟩,
      w8, w9, w10, w11, rfl⟩
  · -- step
    rintro st3 s3 ⟨hpg3, hgl3, ⟨k, hkL, hidx3, hpres3⟩, v8, v9, v10, v11, rfl⟩
    have g68 : ¬ (1114112 < fp.toNat + 68 + 4) := by omega
    have q68 : fp.toNat ≤ 1114040 := by omega
    have hofk : (UInt32.ofNat k).toNat = k := by
      rw [UInt32.toNat_ofNat_of_lt']
      simp [UInt32.size]; omega
    wp_run
    simp [hpg3, hidx3, g68]
    by_cases hk : k < lenv.toNat
    · -- one more byte to compare
      have hklt : UInt32.ofNat k < lenv := by
        rw [UInt32.lt_iff_toNat_lt, hofk]; exact hk
      have hk32 : UInt32.ofNat k < 32 := by
        rw [UInt32.lt_iff_toNat_lt, hofk]
        simp; omega
      simp [hklt]
      apply wp_block_cons
      apply wp_block_cons
      apply wp_block_cons
      apply wp_block_cons
      apply wp_block_cons
      wp_run
      have haddr1 : (UInt32.ofNat k + fp).toNat = fp.toNat + k := by
        rw [UInt32.toNat_add, hofk]
        have : k + fp.toNat < UInt32.size := by simp [UInt32.size]; omega
        rw [Nat.mod_eq_of_lt this]
        omega
      have haddr2 : (UInt32.ofNat k + (32 + fp)).toNat = fp.toNat + 32 + k := by
        rw [UInt32.toNat_add, hofk, toNat_add_of_lt _ _ (by simp; omega)]
        simp only [show (32 : UInt32).toNat = 32 from rfl]
        have : k + (32 + fp.toNat) < UInt32.size := by simp [UInt32.size]; omega
        rw [Nat.mod_eq_of_lt this]
        omega
      have hnb1 : ¬ (1114112 ≤ fp.toNat + k) := by omega
      have hnb2 : ¬ (1114112 ≤ fp.toNat + 32 + k) := by omega
      have hb1 : st3.mem.read8 (UInt32.ofNat k + fp) = D k := by
        show st3.mem.bytes (UInt32.ofNat k + fp).toNat = D k
        rw [haddr1, hpres3 _ (by omega)]
        exact hfast k hk
      have hb2 : st3.mem.read8 (UInt32.ofNat k + (32 + fp)) = D k := by
        show st3.mem.bytes (UInt32.ofNat k + (32 + fp)).toNat = D k
        rw [haddr2, hpres3 _ (by omega)]
        exact hnaive k hk
      have hadd1 : (1 : UInt32) + UInt32.ofNat k = UInt32.ofNat (k + 1) := by
        apply UInt32.toNat.inj
        rw [UInt32.toNat_add, hofk,
          UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)]
        simp
        omega
      simp [hk32, haddr1, haddr2, hnb1, hnb2, hb1, hb2, hpg3, hidx3, g68]
      refine ⟨⟨hgl3, ⟨k + 1, by omega, hadd1, ?_⟩⟩, ?_⟩
      · intro j hj
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
        exact hpres3 j hj
      · omega
    · -- all bytes agree: `br_if 1` exits the loop
      have hnk : ¬ (UInt32.ofNat k < lenv) := by
        rw [UInt32.lt_iff_toNat_lt, hofk]; omega
      simp [hnk]
      exact hexit st3 v8 v9 v10 v11 hpg3 hgl3 hpres3

/-! ## Fast-formatter helpers (`func40`'s callee closure)

Frame-pointer-parametric specs for every function the `itoa` u64 core
`func40` calls — `func41`/`func42` (checked `Result` wrap/unwrap, per
chunk iteration), `func38` (the `/100` magic-division splitter),
`func39` → `func46` (the `DIGIT_TABLE` address computation), plus the
slice packaging chain `func49` → `func47` → `func37`/`func45` and the
wrapper glue `func10` (identity 2nd-arg) and `func25` (the 40-byte
red-zone copy used by `func22`/`func24`). All are stated over an
abstract shadow-stack pointer `g` (`g.toNat ≤ 1048576`, frame-size
lower bound per function) with byte-level framing postconditions in
`toNat` form, matching the naive-side corpus idiom. Leaves that never
move the stack pointer (`func10`/`func37`/`func38`/`func45`/`func46`/
`func48`/`func25`) spill into the red zone *below* the current `g`, so
their framing windows extend 16/32 bytes beneath it; wrappers compose
callees via `wp_call_of_terminates`.

Signedness/conversion bridges: `extendS_toUInt64_small` (sign-extension
of a known-nonnegative i32 is zero-extension); `func48`/`func41` take
`x.toNat < 2^31` (all of `func40`'s call sites pass constants 999 /
10000), `func42` takes an even discriminant (its call sites pass the
`Ok`-tag 0 written by `func41`). -/

set_option maxHeartbeats 1600000 in
theorem func10_spec (env : HostEnv Unit) (st0 : Store Unit) (g : UInt32)
    (a b : UInt32)
    (hpg : st0.mem.pages = 17)
    (hg : st0.globals.globals[0]? = some (.i32 g))
    (hg16 : 16 ≤ g.toNat) (hghi : g.toNat ≤ 1048576) :
    TerminatesWith env «module» 10 st0 [.i32 b, .i32 a]
      (fun st' rs =>
        st'.mem.pages = 17 ∧
        st'.globals.globals[0]? = some (.i32 g) ∧
        rs = [.i32 b] ∧
        (∀ i : Nat, i < g.toNat - 16 ∨ g.toNat ≤ i →
          st'.mem.bytes i = st0.mem.bytes i)) := by
  have hsub : (g - 16).toNat = g.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le g 16 (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
    rfl
  have t8 : (g - 16 + 8).toNat = g.toNat - 16 + 8 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t12 : (g - 16 + 12).toNat = g.toNat - 16 + 12 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have p8 : ¬ (1114112 < g.toNat - 16 + 8 + 4) := by omega
  have p12 : ¬ (1114112 < g.toNat - 16 + 12 + 4) := by omega
  have q8 : g.toNat - 16 ≤ 1114100 := by omega
  have q12 : g.toNat - 16 ≤ 1114096 := by omega
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i32, .i32], [.i32], func10, [.i32]⟩) rfl
  unfold func10
  wp_run
  simp [hg, hpg, hsub, p8, p12]
  intro i hi
  repeat rw [if_neg (by omega)]

set_option maxHeartbeats 1600000 in
theorem func46_spec (env : HostEnv Unit) (st0 : Store Unit) (g : UInt32)
    (a0 a1 a2 a3 : UInt32)
    (hpg : st0.mem.pages = 17)
    (hg : st0.globals.globals[0]? = some (.i32 g))
    (hg16 : 16 ≤ g.toNat) (hghi : g.toNat ≤ 1048576) :
    TerminatesWith env «module» 46 st0 [.i32 a3, .i32 a2, .i32 a1, .i32 a0]
      (fun st' rs =>
        st'.mem.pages = 17 ∧
        st'.globals.globals[0]? = some (.i32 g) ∧
        rs = [.i32 (a0 + a1)] ∧
        (∀ i : Nat, i < g.toNat - 16 ∨ g.toNat ≤ i →
          st'.mem.bytes i = st0.mem.bytes i)) := by
  have hsub : (g - 16).toNat = g.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le g 16 (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
    rfl
  have t4 : (g - 16 + 4).toNat = g.toNat - 16 + 4 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t8 : (g - 16 + 8).toNat = g.toNat - 16 + 8 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t12 : (g - 16 + 12).toNat = g.toNat - 16 + 12 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have p4 : ¬ (1114112 < g.toNat - 16 + 4 + 4) := by omega
  have p8 : ¬ (1114112 < g.toNat - 16 + 8 + 4) := by omega
  have p12 : ¬ (1114112 < g.toNat - 16 + 12 + 4) := by omega
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i32, .i32, .i32, .i32], [.i32], func46, [.i32]⟩) rfl
  unfold func46
  wp_run
  simp [hg, hpg, hsub, p4, p8, p12]
  intro i hi
  repeat rw [if_neg (by omega)]

set_option maxHeartbeats 1600000 in
theorem func45_spec (env : HostEnv Unit) (st0 : Store Unit) (g : UInt32)
    (ret a b : UInt32)
    (hpg : st0.mem.pages = 17)
    (hg : st0.globals.globals[0]? = some (.i32 g))
    (hg16 : 16 ≤ g.toNat) (hghi : g.toNat ≤ 1048576)
    (hret : ret.toNat + 8 ≤ 1114112) :
    TerminatesWith env «module» 45 st0 [.i32 b, .i32 a, .i32 ret]
      (fun st' rs =>
        st'.mem.pages = 17 ∧
        st'.globals.globals[0]? = some (.i32 g) ∧
        rs = [] ∧
        st'.mem.read32 ret = a ∧
        st'.mem.read32 (ret + 4) = b ∧
        (∀ i : Nat, (i < g.toNat - 16 ∨ g.toNat ≤ i) →
          (i < ret.toNat ∨ ret.toNat + 8 ≤ i) →
          st'.mem.bytes i = st0.mem.bytes i)) := by
  have hsub : (g - 16).toNat = g.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le g 16 (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
    rfl
  have t8 : (g - 16 + 8).toNat = g.toNat - 16 + 8 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t12 : (g - 16 + 12).toNat = g.toNat - 16 + 12 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have tr4 : (ret + 4).toNat = ret.toNat + 4 := by
    rw [UInt32.toNat_add]; simp; omega
  have p8 : ¬ (1114112 < g.toNat - 16 + 8 + 4) := by omega
  have p12 : ¬ (1114112 < g.toNat - 16 + 12 + 4) := by omega
  have pr0 : ¬ (1114112 < ret.toNat + 4) := by omega
  have pr4 : ¬ (1114112 < ret.toNat + 4 + 4) := by omega
  have qr0 : ret.toNat ≤ 1114108 := by omega
  have qr4 : ret.toNat ≤ 1114104 := by omega
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i32, .i32, .i32], [.i32], func45, []⟩) rfl
  unfold func45
  wp_run
  simp [hg, hpg, hsub, p8, p12, pr0, pr4]
  refine ⟨?_, ?_⟩
  · rw [read32_write32_disjoint' _ _ _ _ (by omega), read32_write32_same']
  · intro i hi hir
    repeat rw [if_neg (by omega)]

set_option maxHeartbeats 1600000 in
theorem func37_spec (env : HostEnv Unit) (st0 : Store Unit) (g : UInt32)
    (ret p1 p2 p3 : UInt32)
    (hpg : st0.mem.pages = 17)
    (hg : st0.globals.globals[0]? = some (.i32 g))
    (hg32 : 32 ≤ g.toNat) (hghi : g.toNat ≤ 1048576)
    (hret : ret.toNat + 8 ≤ 1114112) :
    TerminatesWith env «module» 37 st0 [.i32 p3, .i32 p2, .i32 p1, .i32 ret]
      (fun st' rs =>
        st'.mem.pages = 17 ∧
        st'.globals.globals[0]? = some (.i32 g) ∧
        rs = [] ∧
        st'.mem.read32 ret = p1 + p2 ∧
        st'.mem.read32 (ret + 4) = p3 - p1 ∧
        (∀ i : Nat, (i < g.toNat - 32 ∨ g.toNat ≤ i) →
          (i < ret.toNat ∨ ret.toNat + 8 ≤ i) →
          st'.mem.bytes i = st0.mem.bytes i)) := by
  have hsub : (g - 32).toNat = g.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le g 32 (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
    rfl
  have t8 : (g - 32 + 8).toNat = g.toNat - 32 + 8 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t12 : (g - 32 + 12).toNat = g.toNat - 32 + 12 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t16 : (g - 32 + 16).toNat = g.toNat - 32 + 16 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t20 : (g - 32 + 20).toNat = g.toNat - 32 + 20 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t24 : (g - 32 + 24).toNat = g.toNat - 32 + 24 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t28 : (g - 32 + 28).toNat = g.toNat - 32 + 28 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have tr4 : (ret + 4).toNat = ret.toNat + 4 := by
    rw [UInt32.toNat_add]; simp; omega
  have p8 : ¬ (1114112 < g.toNat - 32 + 8 + 4) := by omega
  have p12 : ¬ (1114112 < g.toNat - 32 + 12 + 4) := by omega
  have p16 : ¬ (1114112 < g.toNat - 32 + 16 + 4) := by omega
  have p20 : ¬ (1114112 < g.toNat - 32 + 20 + 4) := by omega
  have p24 : ¬ (1114112 < g.toNat - 32 + 24 + 4) := by omega
  have p28 : ¬ (1114112 < g.toNat - 32 + 28 + 4) := by omega
  have pr0 : ¬ (1114112 < ret.toNat + 4) := by omega
  have pr4 : ¬ (1114112 < ret.toNat + 4 + 4) := by omega
  have qr0 : ret.toNat ≤ 1114108 := by omega
  have qr4 : ret.toNat ≤ 1114104 := by omega
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i32, .i32, .i32, .i32], [.i32, .i32, .i32], func37, []⟩) rfl
  unfold func37
  wp_run
  simp [hg, hpg, hsub, p8, p12, p16, p20, p24, p28, pr0, pr4]
  refine ⟨?_, ?_⟩
  · rw [read32_write32_disjoint' _ _ _ _ (by omega), read32_write32_same']
  · intro i hi hir
    repeat rw [if_neg (by omega)]

set_option maxHeartbeats 1600000 in
theorem func38_spec (env : HostEnv Unit) (st0 : Store Unit) (g : UInt32)
    (ret x : UInt32)
    (hpg : st0.mem.pages = 17)
    (hg : st0.globals.globals[0]? = some (.i32 g))
    (hg16 : 16 ≤ g.toNat) (hghi : g.toNat ≤ 1048576)
    (hret : ret.toNat + 8 ≤ 1114112) :
    TerminatesWith env «module» 38 st0 [.i32 x, .i32 ret]
      (fun st' rs =>
        st'.mem.pages = 17 ∧
        st'.globals.globals[0]? = some (.i32 g) ∧
        rs = [] ∧
        st'.mem.read32 ret = (5243 * x) >>> 19 ∧
        st'.mem.read32 (ret + 4) = x - (100 : UInt32) * ((5243 * x) >>> 19) ∧
        (∀ i : Nat, (i < g.toNat - 16 ∨ g.toNat ≤ i) →
          (i < ret.toNat ∨ ret.toNat + 8 ≤ i) →
          st'.mem.bytes i = st0.mem.bytes i)) := by
  have hsub : (g - 16).toNat = g.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le g 16 (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
    rfl
  have t8 : (g - 16 + 8).toNat = g.toNat - 16 + 8 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t12 : (g - 16 + 12).toNat = g.toNat - 16 + 12 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have tr4 : (ret + 4).toNat = ret.toNat + 4 := by
    rw [UInt32.toNat_add]; simp; omega
  have p8 : ¬ (1114112 < g.toNat - 16 + 8 + 4) := by omega
  have p12 : ¬ (1114112 < g.toNat - 16 + 12 + 4) := by omega
  have pr0 : ¬ (1114112 < ret.toNat + 4) := by omega
  have pr4 : ¬ (1114112 < ret.toNat + 4 + 4) := by omega
  have qr0 : ret.toNat ≤ 1114108 := by omega
  have qr4 : ret.toNat ≤ 1114104 := by omega
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i32, .i32], [.i32, .i32], func38, []⟩) rfl
  unfold func38
  wp_run
  simp [hg, hpg, hsub, p8, p12, pr0, pr4]
  refine ⟨?_, ?_⟩
  · rw [read32_write32_disjoint' _ _ _ _ (by omega), read32_write32_same']
  · intro i hi hir
    repeat rw [if_neg (by omega)]

private theorem extendS_toUInt64_small (x : UInt32) (hx : x.toNat < 2147483648) :
    x.toInt32.toInt64.toUInt64 = x.toUInt64 := by
  have hx' : x < 2147483648 := by rw [UInt32.lt_iff_toNat_lt]; simpa using hx
  bv_decide

set_option maxHeartbeats 1600000 in
theorem func48_spec (env : HostEnv Unit) (st0 : Store Unit) (g : UInt32)
    (ret x : UInt32)
    (hpg : st0.mem.pages = 17)
    (hg : st0.globals.globals[0]? = some (.i32 g))
    (hg16 : 16 ≤ g.toNat) (hghi : g.toNat ≤ 1048576)
    (hret : ret.toNat + 16 ≤ 1114112)
    (hx : x.toNat < 2147483648) :
    TerminatesWith env «module» 48 st0 [.i32 x, .i32 ret]
      (fun st' rs =>
        st'.mem.pages = 17 ∧
        st'.globals.globals[0]? = some (.i32 g) ∧
        rs = [] ∧
        st'.mem.read64 ret = 0 ∧
        st'.mem.read64 (ret + 8) = UInt64.ofNat x.toNat ∧
        (∀ i : Nat, (i < g.toNat - 16 ∨ g.toNat ≤ i) →
          (i < ret.toNat ∨ ret.toNat + 16 ≤ i) →
          st'.mem.bytes i = st0.mem.bytes i)) := by
  have hsub : (g - 16).toNat = g.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le g 16 (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
    rfl
  have t12 : (g - 16 + 12).toNat = g.toNat - 16 + 12 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have tr8 : (ret + 8).toNat = ret.toNat + 8 := by
    rw [UInt32.toNat_add]; simp; omega
  have p12 : ¬ (1114112 < g.toNat - 16 + 12 + 4) := by omega
  have pr0 : ¬ (1114112 < ret.toNat + 8) := by omega
  have pr8 : ¬ (1114112 < ret.toNat + 8 + 8) := by omega
  have qr0 : ret.toNat ≤ 1114104 := by omega
  have qr8 : ret.toNat ≤ 1114096 := by omega
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i32, .i32], [.i32, .i64, .i64], func48, []⟩) rfl
  unfold func48
  wp_run
  simp [hg, hpg, hsub, p12]
  apply wp_block_cons
  apply wp_block_cons
  wp_run
  have hge : (0 : Int32) ≤ x.toInt32 := by
    have h := (leS_small 0 x (by decide) hx).mpr (Nat.zero_le _)
    simpa using h
  simp [hge, hg, hpg, pr0, pr8, extendS_toUInt64_small x hx]
  refine ⟨?_, ?_⟩
  · rw [read64_write64_disjoint _ _ _ _ (by omega), read64_write64_same]
  · intro i hi hir
    rw [write64_bytes_of_disjoint _ _ _ _ (by omega),
        write64_bytes_of_disjoint _ _ _ _ (by omega),
        write32_bytes_of_disjoint _ _ _ _ (by omega)]

set_option maxHeartbeats 1600000 in
theorem func42_spec (env : HostEnv Unit) (st0 : Store Unit) (g : UInt32)
    (v0 v1 : UInt64) (a2 a3 a4 : UInt32)
    (hpg : st0.mem.pages = 17)
    (hg : st0.globals.globals[0]? = some (.i32 g))
    (hg48 : 48 ≤ g.toNat) (hghi : g.toNat ≤ 1048576)
    (hv0 : v0.toNat % 2 = 0) :
    TerminatesWith env «module» 42 st0 [.i32 a4, .i32 a3, .i32 a2, .i64 v1, .i64 v0]
      (fun st' rs =>
        st'.mem.pages = 17 ∧
        st'.globals.globals[0]? = some (.i32 g) ∧
        rs = [.i64 v1] ∧
        (∀ i : Nat, i < g.toNat - 48 ∨ g.toNat ≤ i →
          st'.mem.bytes i = st0.mem.bytes i)) := by
  obtain ⟨hglen, -⟩ := List.getElem?_eq_some_iff.mp hg
  have hsub : (g - 48).toNat = g.toNat - 48 := by
    rw [UInt32.toNat_sub_of_le g 48 (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
    rfl
  have t8 : (g - 48 + 8).toNat = g.toNat - 48 + 8 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t16 : (g - 48 + 16).toNat = g.toNat - 48 + 16 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t32 : (g - 48 + 32).toNat = g.toNat - 48 + 32 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t36 : (g - 48 + 36).toNat = g.toNat - 48 + 36 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t40 : (g - 48 + 40).toNat = g.toNat - 48 + 40 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have hback : 48 + (g - 48) = g := by
    apply UInt32.toNat.inj
    rw [UInt32.toNat_add, hsub]; simp; omega
  have p8 : ¬ (1114112 < g.toNat - 48 + 8 + 8) := by omega
  have p16 : ¬ (1114112 < g.toNat - 48 + 16 + 8) := by omega
  have p32 : ¬ (1114112 < g.toNat - 48 + 32 + 4) := by omega
  have p36 : ¬ (1114112 < g.toNat - 48 + 36 + 4) := by omega
  have p40 : ¬ (1114112 < g.toNat - 48 + 40 + 8) := by omega
  have q8 : g.toNat - 48 ≤ 1114096 := by omega
  have q16 : g.toNat - 48 ≤ 1114088 := by omega
  have q32 : g.toNat - 48 ≤ 1114076 := by omega
  have q36 : g.toNat - 48 ≤ 1114072 := by omega
  have q40 : g.toNat - 48 ≤ 1114064 := by omega
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i64, .i64, .i32, .i32, .i32], [.i32, .i64], func42, [.i64]⟩) rfl
  unfold func42
  wp_run
  simp [hg, hpg, hsub, p8, p16, p32, p36]
  apply wp_block_cons
  wp_run
  have hb8 : ((((st0.mem.write64 (g - 48 + 8) v0).write64 (g - 48 + 16) v1).write32
      (g - 48 + 32) a2).write32 (g - 48 + 36) a3).read64 (g - 48 + 8) = v0 := by
    rw [read64_write32_disjoint _ _ _ _ (by omega),
        read64_write32_disjoint _ _ _ _ (by omega),
        read64_write64_disjoint _ _ _ _ (by omega),
        read64_write64_same]
  have hb16 : ((((st0.mem.write64 (g - 48 + 8) v0).write64 (g - 48 + 16) v1).write32
      (g - 48 + 32) a2).write32 (g - 48 + 36) a3).read64 (g - 48 + 16) = v1 := by
    rw [read64_write32_disjoint _ _ _ _ (by omega),
        read64_write32_disjoint _ _ _ _ (by omega),
        read64_write64_same]
  have hcond : (1 : UInt32) &&& UInt32.ofNat (v0.toNat % 4294967296) = 0 := by
    apply UInt32.toNat.inj
    rw [UInt32.toNat_and,
      UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)]
    show (1 : Nat) &&& v0.toNat % 4294967296 = 0
    rw [Nat.and_comm, Nat.and_one_is_mod]
    omega
  simp [hb8, hb16, hcond, hpg, hsub, hback, p16, p40, q8,
    List.getElem?_set_self (by simpa using hglen)]
  intro i hi
  rw [write64_bytes_of_disjoint _ _ _ _ (by omega),
      write32_bytes_of_disjoint _ _ _ _ (by omega),
      write32_bytes_of_disjoint _ _ _ _ (by omega),
      write64_bytes_of_disjoint _ _ _ _ (by omega),
      write64_bytes_of_disjoint _ _ _ _ (by omega)]

set_option maxHeartbeats 1600000 in
theorem func39_spec (env : HostEnv Unit) (st0 : Store Unit) (g : UInt32)
    (a0 a1 a2 a3 : UInt32)
    (hpg : st0.mem.pages = 17)
    (hg : st0.globals.globals[0]? = some (.i32 g))
    (hg32 : 32 ≤ g.toNat) (hghi : g.toNat ≤ 1048576) :
    TerminatesWith env «module» 39 st0 [.i32 a3, .i32 a2, .i32 a1, .i32 a0]
      (fun st' rs =>
        st'.mem.pages = 17 ∧
        st'.globals.globals[0]? = some (.i32 g) ∧
        rs = [.i32 (a2 + a0)] ∧
        (∀ i : Nat, i < g.toNat - 32 ∨ g.toNat ≤ i →
          st'.mem.bytes i = st0.mem.bytes i)) := by
  obtain ⟨hglen, -⟩ := List.getElem?_eq_some_iff.mp hg
  have hsub : (g - 16).toNat = g.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le g 16 (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
    rfl
  have t4 : (g - 16 + 4).toNat = g.toNat - 16 + 4 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t8 : (g - 16 + 8).toNat = g.toNat - 16 + 8 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t12 : (g - 16 + 12).toNat = g.toNat - 16 + 12 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have hback : 16 + (g - 16) = g := by
    apply UInt32.toNat.inj
    rw [UInt32.toNat_add, hsub]; simp; omega
  have p4 : ¬ (1114112 < g.toNat - 16 + 4 + 4) := by omega
  have p8 : ¬ (1114112 < g.toNat - 16 + 8 + 4) := by omega
  have p12 : ¬ (1114112 < g.toNat - 16 + 12 + 4) := by omega
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i32, .i32, .i32, .i32], [.i32, .i32], func39, [.i32]⟩) rfl
  unfold func39
  wp_run
  simp [hg, hpg, hsub, p4, p8, p12]
  apply wp_call_of_terminates (func46_spec env _ (g - 16) a2 a0 a1 a3
    (by simp [hpg]) (by simp [List.getElem?_set_self hglen])
    (by omega) (by omega))
  rintro st' vs ⟨hpg', hg', hrs, hpres⟩
  obtain ⟨hglen', -⟩ := List.getElem?_eq_some_iff.mp hg'
  subst hrs
  wp_run
  simp [hg', hback, hpg', List.getElem?_set_self hglen']
  intro i hi
  have hstep := hpres i (by omega)
  rw [hstep,
      write32_bytes_of_disjoint _ _ _ _ (by omega),
      write32_bytes_of_disjoint _ _ _ _ (by omega),
      write32_bytes_of_disjoint _ _ _ _ (by omega)]

set_option maxHeartbeats 1600000 in
theorem func41_spec (env : HostEnv Unit) (st0 : Store Unit) (g : UInt32)
    (ret x : UInt32)
    (hpg : st0.mem.pages = 17)
    (hg : st0.globals.globals[0]? = some (.i32 g))
    (hg32 : 32 ≤ g.toNat) (hghi : g.toNat ≤ 1048576)
    (hret : ret.toNat + 16 ≤ 1114112)
    (hx : x.toNat < 2147483648) :
    TerminatesWith env «module» 41 st0 [.i32 x, .i32 ret]
      (fun st' rs =>
        st'.mem.pages = 17 ∧
        st'.globals.globals[0]? = some (.i32 g) ∧
        rs = [] ∧
        st'.mem.read64 ret = 0 ∧
        st'.mem.read64 (ret + 8) = x.toUInt64 ∧
        (∀ i : Nat, (i < g.toNat - 32 ∨ g.toNat ≤ i) →
          (i < ret.toNat ∨ ret.toNat + 16 ≤ i) →
          st'.mem.bytes i = st0.mem.bytes i)) := by
  obtain ⟨hglen, -⟩ := List.getElem?_eq_some_iff.mp hg
  have hsub : (g - 16).toNat = g.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le g 16 (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
    rfl
  have t12 : (g - 16 + 12).toNat = g.toNat - 16 + 12 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have hback : 16 + (g - 16) = g := by
    apply UInt32.toNat.inj
    rw [UInt32.toNat_add, hsub]; simp; omega
  have p12 : ¬ (1114112 < g.toNat - 16 + 12 + 4) := by omega
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i32, .i32], [.i32], func41, []⟩) rfl
  unfold func41
  wp_run
  simp [hg, hpg, hsub, p12]
  apply wp_call_of_terminates (func48_spec env _ (g - 16) ret x
    (by simp [hpg]) (by simp [List.getElem?_set_self hglen])
    (by omega) (by omega) hret hx)
  rintro st' vs ⟨hpg', hg', hrs, hr0, hr8, hpres⟩
  obtain ⟨hglen', -⟩ := List.getElem?_eq_some_iff.mp hg'
  subst hrs
  wp_run
  simp [hg', hback, hpg', hr0, hr8, List.getElem?_set_self hglen']
  intro i hi hir
  have hstep := hpres i (by omega) (by omega)
  rw [hstep, write32_bytes_of_disjoint _ _ _ _ (by omega)]

set_option maxHeartbeats 1600000 in
theorem func47_spec (env : HostEnv Unit) (st0 : Store Unit) (g : UInt32)
    (ret a1 a2 a3 a4 : UInt32)
    (hpg : st0.mem.pages = 17)
    (hg : st0.globals.globals[0]? = some (.i32 g))
    (hg64 : 64 ≤ g.toNat) (hghi : g.toNat ≤ 1048576)
    (hret : ret.toNat + 8 ≤ 1114112) :
    TerminatesWith env «module» 47 st0 [.i32 a4, .i32 a3, .i32 a2, .i32 a1, .i32 ret]
      (fun st' rs =>
        st'.mem.pages = 17 ∧
        st'.globals.globals[0]? = some (.i32 g) ∧
        rs = [] ∧
        st'.mem.read32 ret = a3 + a1 ∧
        st'.mem.read32 (ret + 4) = a2 - a3 ∧
        (∀ i : Nat, (i < g.toNat - 64 ∨ g.toNat ≤ i) →
          (i < ret.toNat ∨ ret.toNat + 8 ≤ i) →
          st'.mem.bytes i = st0.mem.bytes i)) := by
  obtain ⟨hglen, -⟩ := List.getElem?_eq_some_iff.mp hg
  have hsub : (g - 32).toNat = g.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le g 32 (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
    rfl
  have t8 : (g - 32 + 8).toNat = g.toNat - 32 + 8 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t12 : (g - 32 + 12).toNat = g.toNat - 32 + 12 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t20 : (g - 32 + 20).toNat = g.toNat - 32 + 20 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t24 : (g - 32 + 24).toNat = g.toNat - 32 + 24 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t28 : (g - 32 + 28).toNat = g.toNat - 32 + 28 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have tr4 : (ret + 4).toNat = ret.toNat + 4 := by
    rw [UInt32.toNat_add]; simp; omega
  have hback : 32 + (g - 32) = g := by
    apply UInt32.toNat.inj
    rw [UInt32.toNat_add, hsub]; simp; omega
  have p20 : ¬ (1114112 < g.toNat - 32 + 20 + 4) := by omega
  have p24 : ¬ (1114112 < g.toNat - 32 + 24 + 4) := by omega
  have p28 : ¬ (1114112 < g.toNat - 32 + 28 + 4) := by omega
  have p8 : ¬ (1114112 < g.toNat - 32 + 8 + 4) := by omega
  have p12 : ¬ (1114112 < g.toNat - 32 + 12 + 4) := by omega
  have pr0 : ¬ (1114112 < ret.toNat + 4) := by omega
  have pr4 : ¬ (1114112 < ret.toNat + 4 + 4) := by omega
  have qr0 : ret.toNat ≤ 1114108 := by omega
  have qr4 : ret.toNat ≤ 1114104 := by omega
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i32, .i32, .i32, .i32, .i32], [.i32, .i32], func47, []⟩) rfl
  unfold func47
  wp_run
  simp [hg, hpg, hsub, p20, p24, p28]
  have haddr8 : (8 : UInt32) + (g - 32) = g - 32 + 8 := by bv_decide
  have haddr12 : g - 32 + 8 + 4 = g - 32 + 12 := by
    bv_decide
  have t8' : ((8 : UInt32) + (g - 32)).toNat = g.toNat - 32 + 8 := by
    rw [haddr8]; exact t8
  apply wp_call_of_terminates (func37_spec env _ (g - 32) (8 + (g - 32)) a3 a1 a2
    (by simp [hpg]) (by simp [List.getElem?_set_self hglen])
    (by omega) (by omega) (by omega))
  rintro st' vs ⟨hpg', hg', hrs, hr0, hr4, hpres⟩
  obtain ⟨hglen', -⟩ := List.getElem?_eq_some_iff.mp hg'
  subst hrs
  rw [haddr8] at hr0
  rw [haddr8, haddr12] at hr4
  wp_run
  simp [hg', hback, hpg', hsub, hr0, hr4, p8, p12, pr0, pr4,
    List.getElem?_set_self hglen']
  refine ⟨?_, ?_⟩
  · rw [read32_write32_disjoint' _ _ _ _ (by omega), read32_write32_same']
  · intro i hi hir
    repeat rw [if_neg (by omega)]
    have hstep := hpres i (by omega) (by omega)
    rw [hstep,
        write32_bytes_of_disjoint _ _ _ _ (by omega),
        write32_bytes_of_disjoint _ _ _ _ (by omega),
        write32_bytes_of_disjoint _ _ _ _ (by omega)]

set_option maxHeartbeats 8000000 in
theorem func49_spec (env : HostEnv Unit) (st0 : Store Unit) (g : UInt32)
    (ret a1 a2 a3 : UInt32)
    (hpg : st0.mem.pages = 17)
    (hg : st0.globals.globals[0]? = some (.i32 g))
    (hg112 : 112 ≤ g.toNat) (hghi : g.toNat ≤ 1048576)
    (hret : ret.toNat + 8 ≤ 1114112) :
    TerminatesWith env «module» 49 st0 [.i32 a3, .i32 a2, .i32 a1, .i32 ret]
      (fun st' rs =>
        st'.mem.pages = 17 ∧
        st'.globals.globals[0]? = some (.i32 g) ∧
        rs = [] ∧
        st'.mem.read32 ret = a3 + a1 ∧
        st'.mem.read32 (ret + 4) = a2 - a3 ∧
        (∀ i : Nat, (i < g.toNat - 112 ∨ g.toNat ≤ i) →
          (i < ret.toNat ∨ ret.toNat + 8 ≤ i) →
          st'.mem.bytes i = st0.mem.bytes i)) := by
  obtain ⟨hglen, -⟩ := List.getElem?_eq_some_iff.mp hg
  have hsub : (g - 48).toNat = g.toNat - 48 := by
    rw [UInt32.toNat_sub_of_le g 48 (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
    rfl
  have t8 : (g - 48 + 8).toNat = g.toNat - 48 + 8 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t12 : (g - 48 + 12).toNat = g.toNat - 48 + 12 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t16 : (g - 48 + 16).toNat = g.toNat - 48 + 16 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t20 : (g - 48 + 20).toNat = g.toNat - 48 + 20 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t28 : (g - 48 + 28).toNat = g.toNat - 48 + 28 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t32 : (g - 48 + 32).toNat = g.toNat - 48 + 32 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t36 : (g - 48 + 36).toNat = g.toNat - 48 + 36 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t40 : (g - 48 + 40).toNat = g.toNat - 48 + 40 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t44 : (g - 48 + 44).toNat = g.toNat - 48 + 44 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have tr4 : (ret + 4).toNat = ret.toNat + 4 := by
    rw [UInt32.toNat_add]; simp; omega
  have hback : 48 + (g - 48) = g := by
    apply UInt32.toNat.inj
    rw [UInt32.toNat_add, hsub]; simp; omega
  have p28 : ¬ (1114112 < g.toNat - 48 + 28 + 4) := by omega
  have p32 : ¬ (1114112 < g.toNat - 48 + 32 + 4) := by omega
  have p36 : ¬ (1114112 < g.toNat - 48 + 36 + 4) := by omega
  have p16 : ¬ (1114112 < g.toNat - 48 + 16 + 4) := by omega
  have p20 : ¬ (1114112 < g.toNat - 48 + 20 + 4) := by omega
  have p8 : ¬ (1114112 < g.toNat - 48 + 8 + 4) := by omega
  have p12 : ¬ (1114112 < g.toNat - 48 + 12 + 4) := by omega
  have p40 : ¬ (1114112 < g.toNat - 48 + 40 + 4) := by omega
  have p44 : ¬ (1114112 < g.toNat - 48 + 44 + 4) := by omega
  have pr0 : ¬ (1114112 < ret.toNat + 4) := by omega
  have pr4 : ¬ (1114112 < ret.toNat + 4 + 4) := by omega
  have qr0 : ret.toNat ≤ 1114108 := by omega
  have qr4 : ret.toNat ≤ 1114104 := by omega
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i32, .i32, .i32, .i32], [.i32, .i32, .i32, .i32, .i32], func49, []⟩) rfl
  unfold func49
  wp_run
  simp [hg, hpg, hsub, p28, p32, p36]
  have haddr16 : (16 : UInt32) + (g - 48) = g - 48 + 16 := by bv_decide
  have haddr20 : g - 48 + 16 + 4 = g - 48 + 20 := by
    bv_decide
  have haddr8 : (8 : UInt32) + (g - 48) = g - 48 + 8 := by bv_decide
  have haddr12 : g - 48 + 8 + 4 = g - 48 + 12 := by
    bv_decide
  have t16' : ((16 : UInt32) + (g - 48)).toNat = g.toNat - 48 + 16 := by
    rw [haddr16]; exact t16
  have t8' : ((8 : UInt32) + (g - 48)).toNat = g.toNat - 48 + 8 := by
    rw [haddr8]; exact t8
  apply wp_call_of_terminates (func47_spec env _ (g - 48) (16 + (g - 48)) a1 a2 a3 1049608
    (by simp [hpg]) (by simp [List.getElem?_set_self hglen])
    (by omega) (by omega) (by omega))
  rintro st' vs ⟨hpg', hg', hrs, hr16, hr20, hpres⟩
  obtain ⟨hglen', -⟩ := List.getElem?_eq_some_iff.mp hg'
  subst hrs
  rw [haddr16] at hr16
  rw [haddr16, haddr20] at hr20
  wp_run
  simp [hpg', hsub, hr16, hr20, p16, p20, p40, p44]
  apply wp_call_of_terminates (func45_spec env _ (g - 48) (8 + (g - 48)) (a3 + a1) (a2 - a3)
    (by simp [hpg']) (by simpa using hg')
    (by omega) (by omega) (by omega))
  rintro st2 vs2 ⟨hpg2, hg2, hrs2, hra, hrb, hpres2⟩
  obtain ⟨hglen2, -⟩ := List.getElem?_eq_some_iff.mp hg2
  subst hrs2
  rw [haddr8] at hra
  rw [haddr8, haddr12] at hrb
  wp_run
  simp [hg2, hback, hpg2, hsub, hra, hrb, p8, p12, pr0, pr4,
    List.getElem?_set_self hglen2]
  refine ⟨?_, ?_⟩
  · rw [read32_write32_disjoint' _ _ _ _ (by omega), read32_write32_same']
  · intro i hi hir
    repeat rw [if_neg (by omega)]
    have hstep2 := hpres2 i (by omega) (by omega)
    rw [hstep2,
        write32_bytes_of_disjoint _ _ _ _ (by omega),
        write32_bytes_of_disjoint _ _ _ _ (by omega)]
    have hstep := hpres i (by omega) (by omega)
    rw [hstep,
        write32_bytes_of_disjoint _ _ _ _ (by omega),
        write32_bytes_of_disjoint _ _ _ _ (by omega),
        write32_bytes_of_disjoint _ _ _ _ (by omega)]

set_option maxHeartbeats 1600000 in
theorem func25_spec (env : HostEnv Unit) (st0 : Store Unit) (g : UInt32)
    (a0 : UInt32)
    (hpg : st0.mem.pages = 17)
    (hg : st0.globals.globals[0]? = some (.i32 g))
    (hg48 : 48 ≤ g.toNat) (hghi : g.toNat ≤ 1048576)
    (hdst : g.toNat ≤ a0.toNat) (hdhi : a0.toNat + 40 ≤ 1114112) :
    TerminatesWith env «module» 25 st0 [.i32 a0]
      (fun st' rs =>
        st'.mem.pages = 17 ∧
        st'.globals.globals[0]? = some (.i32 g) ∧
        rs = [] ∧
        st'.mem.read64 a0 = st0.mem.read64 (g - 48 + 8) ∧
        st'.mem.read64 (a0 + 8) = st0.mem.read64 (g - 48 + 16) ∧
        st'.mem.read64 (a0 + 16) = st0.mem.read64 (g - 48 + 24) ∧
        st'.mem.read64 (a0 + 24) = st0.mem.read64 (g - 48 + 32) ∧
        st'.mem.read64 (a0 + 32) = st0.mem.read64 (g - 48 + 40) ∧
        (∀ i : Nat, i < a0.toNat ∨ a0.toNat + 40 ≤ i →
          st'.mem.bytes i = st0.mem.bytes i)) := by
  have hsub : (g - 48).toNat = g.toNat - 48 := by
    rw [UInt32.toNat_sub_of_le g 48 (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
    rfl
  have t8 : (g - 48 + 8).toNat = g.toNat - 48 + 8 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t16 : (g - 48 + 16).toNat = g.toNat - 48 + 16 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t24 : (g - 48 + 24).toNat = g.toNat - 48 + 24 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t32 : (g - 48 + 32).toNat = g.toNat - 48 + 32 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have t40 : (g - 48 + 40).toNat = g.toNat - 48 + 40 := by
    rw [UInt32.toNat_add, hsub]; simp; omega
  have ta8 : (a0 + 8).toNat = a0.toNat + 8 := by
    rw [UInt32.toNat_add]; simp; omega
  have ta16 : (a0 + 16).toNat = a0.toNat + 16 := by
    rw [UInt32.toNat_add]; simp; omega
  have ta24 : (a0 + 24).toNat = a0.toNat + 24 := by
    rw [UInt32.toNat_add]; simp; omega
  have ta32 : (a0 + 32).toNat = a0.toNat + 32 := by
    rw [UInt32.toNat_add]; simp; omega
  have ps8 : ¬ (1114112 < g.toNat - 48 + 8 + 8) := by omega
  have ps16 : ¬ (1114112 < g.toNat - 48 + 16 + 8) := by omega
  have ps24 : ¬ (1114112 < g.toNat - 48 + 24 + 8) := by omega
  have ps32 : ¬ (1114112 < g.toNat - 48 + 32 + 8) := by omega
  have ps40 : ¬ (1114112 < g.toNat - 48 + 40 + 8) := by omega
  have pa0 : ¬ (1114112 < a0.toNat + 8) := by omega
  have pa8 : ¬ (1114112 < a0.toNat + 8 + 8) := by omega
  have pa16 : ¬ (1114112 < a0.toNat + 16 + 8) := by omega
  have pa24 : ¬ (1114112 < a0.toNat + 24 + 8) := by omega
  have pa32 : ¬ (1114112 < a0.toNat + 32 + 8) := by omega
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i32], [.i32], func25, []⟩) rfl
  unfold func25
  wp_run
  simp [hg, hpg, hsub, ps8, ps16, ps24, ps32, ps40, pa0, pa8, pa16, pa24, pa32]
  have e32 : (st0.mem.write64 (a0 + 32) (st0.mem.read64 (g - 48 + 40))).read64
      (g - 48 + 32) = st0.mem.read64 (g - 48 + 32) :=
    read64_write64_disjoint _ _ _ _ (by omega)
  simp only [e32]
  have e24 : ((st0.mem.write64 (a0 + 32) (st0.mem.read64 (g - 48 + 40))).write64
      (a0 + 24) (st0.mem.read64 (g - 48 + 32))).read64 (g - 48 + 24)
      = st0.mem.read64 (g - 48 + 24) := by
    rw [read64_write64_disjoint _ _ _ _ (by omega),
        read64_write64_disjoint _ _ _ _ (by omega)]
  simp only [e24]
  have e16 : (((st0.mem.write64 (a0 + 32) (st0.mem.read64 (g - 48 + 40))).write64
      (a0 + 24) (st0.mem.read64 (g - 48 + 32))).write64
      (a0 + 16) (st0.mem.read64 (g - 48 + 24))).read64 (g - 48 + 16)
      = st0.mem.read64 (g - 48 + 16) := by
    rw [read64_write64_disjoint _ _ _ _ (by omega),
        read64_write64_disjoint _ _ _ _ (by omega),
        read64_write64_disjoint _ _ _ _ (by omega)]
  simp only [e16]
  have e8 : ((((st0.mem.write64 (a0 + 32) (st0.mem.read64 (g - 48 + 40))).write64
      (a0 + 24) (st0.mem.read64 (g - 48 + 32))).write64
      (a0 + 16) (st0.mem.read64 (g - 48 + 24))).write64
      (a0 + 8) (st0.mem.read64 (g - 48 + 16))).read64 (g - 48 + 8)
      = st0.mem.read64 (g - 48 + 8) := by
    rw [read64_write64_disjoint _ _ _ _ (by omega),
        read64_write64_disjoint _ _ _ _ (by omega),
        read64_write64_disjoint _ _ _ _ (by omega),
        read64_write64_disjoint _ _ _ _ (by omega)]
  simp only [e8]
  refine ⟨trivial, ?_, ?_, ?_, ?_, ?_⟩
  · rw [read64_write64_disjoint _ _ _ _ (by omega), read64_write64_same]
  · rw [read64_write64_disjoint _ _ _ _ (by omega),
        read64_write64_disjoint _ _ _ _ (by omega), read64_write64_same]
  · rw [read64_write64_disjoint _ _ _ _ (by omega),
        read64_write64_disjoint _ _ _ _ (by omega),
        read64_write64_disjoint _ _ _ _ (by omega), read64_write64_same]
  · rw [read64_write64_disjoint _ _ _ _ (by omega),
        read64_write64_disjoint _ _ _ _ (by omega),
        read64_write64_disjoint _ _ _ _ (by omega),
        read64_write64_disjoint _ _ _ _ (by omega), read64_write64_same]
  · intro i hi
    rw [write64_bytes_of_disjoint _ _ _ _ (by omega),
        write64_bytes_of_disjoint _ _ _ _ (by omega),
        write64_bytes_of_disjoint _ _ _ _ (by omega),
        write64_bytes_of_disjoint _ _ _ _ (by omega),
        write64_bytes_of_disjoint _ _ _ _ (by omega)]


end Project.Itoa.Proofs
