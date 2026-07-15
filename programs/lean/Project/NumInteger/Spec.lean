import Project.NumInteger.Program

/-!
# Specification for `gcd_u64`

The exported `gcd_u64` function implements the binary GCD (Stein's
algorithm) on `u64` operands. By the `num-integer` convention the function
returns `0` on `(0, 0)`.

Unlike the previous optimized build, the unoptimized (`opt-level = 0`)
module keeps the operands in linear memory: the exported wrapper (`func2`)
calls `func0`, which spills the two arguments to a 16-byte stack frame and
hands pointers to `func1`, the actual binary-GCD loop. `func1` copies the
operands into its own 48-byte scratch frame and runs Stein's algorithm
entirely through `i64.load`/`i64.store`. The proof therefore threads the
running values through the memory model with the read-after-write framing
lemmas from `CodeLib.RustStd.Frame`, reusing the `UInt64` Stein lemmas
from `CodeLib` for the arithmetic core.
-/

namespace Project.NumInteger.Spec

open Wasm

set_option maxRecDepth 1048576

/-! ## Shift-amount bridge

The wasm computes each Stein shift count by `i64.ctz`, narrows it to an
`i32` (`i32.wrap_i64`), spills/reloads it through a scratch slot, masks
with `& 63`, and widens back with `i64.extend_i32_u` before the shift.
For a nonzero operand `v` (so `ctz64 64 v < 64`) all of that is the
identity on the value: the resulting `i32` is exactly `UInt32.ofNat
(ctz64 64 v)` and the widened+masked shift count matches the form used
by the `CodeLib` Stein lemmas. -/

/-- The masked, narrowed `ctz` of a nonzero `v` is `ctz64 64 v` (in the exact
`i32`-level `63 &&& _` form the interpreter produces). -/
theorem ctz_wrap_and_toNat (v : UInt64) (hv : v ≠ 0) :
    ((63 : UInt32) &&& UInt32.ofNat ((UInt64.ofNat (ctz64 64 v)).toNat % 2 ^ 32)).toNat
      = ctz64 64 v := by
  have hlt : ctz64 64 v < 64 := UInt64.ctz64_lt v hv
  have hsz64 : UInt64.size = 2 ^ 64 := rfl
  have hsz32 : UInt32.size = 2 ^ 32 := rfl
  rw [UInt32.toNat_and]
  rw [UInt64.toNat_ofNat_of_lt' (show ctz64 64 v < UInt64.size by rw [hsz64]; omega)]
  rw [UInt32.toNat_ofNat_of_lt' (show ctz64 64 v % 2 ^ 32 < UInt32.size by
        rw [hsz32, Nat.mod_eq_of_lt (show ctz64 64 v < 2 ^ 32 by omega)]; omega)]
  rw [Nat.mod_eq_of_lt (show ctz64 64 v < 2 ^ 32 by omega)]
  show (63 : UInt32).toNat &&& ctz64 64 v = ctz64 64 v
  have h63 : (63 : UInt32).toNat = 63 := rfl
  rw [h63, Nat.and_comm, show (63 : Nat) = 2 ^ 6 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod (ctz64 64 v) 6]
  exact Nat.mod_eq_of_lt (by simpa using hlt)

/-- The full narrow→reload→mask→widen pipeline applied to `v ≠ 0` lands on
the `CodeLib` shift count (interpreter `i32`-level `63 &&& _` form). -/
theorem shift_pipeline (v : UInt64) (hv : v ≠ 0) :
    UInt64.ofNat
        ((63 : UInt32) &&& UInt32.ofNat ((UInt64.ofNat (ctz64 64 v)).toNat % 2 ^ 32)).toNat % 64
      = UInt64.ofNat (ctz64 64 v) % 64 := by
  rw [ctz_wrap_and_toNat v hv]

/-! ## `func1`: the binary-GCD loop through memory -/

/-- ctz of `a ||| b` equals ctz of `b ||| a` (OR is commutative). -/
theorem ctz_or_comm (a b : UInt64) : ctz64 64 (a ||| b) = ctz64 64 (b ||| a) := by
  rw [UInt64.or_comm]

/-- The `UInt64` odd-part shift, as a `Nat` shift (the form the `CodeLib`
Stein step lemmas produce). -/
theorem oddPart_toNat (v : UInt64) :
    (v >>> (UInt64.ofNat (ctz64 64 v) % 64)).toNat
      = v.toNat >>> (ctz64 64 v % 64) := by
  rw [UInt64.toNat_shiftRight, UInt64.toNat_mod]
  congr 1
  rw [UInt64.toNat_ofNat', show UInt64.toNat 64 = 64 from rfl,
      Nat.mod_mod_of_dvd _ (by norm_num : (64 : Nat) ∣ 2 ^ 64), Nat.mod_mod]

/-- The OUTER-body program of `func1`: the Stein "meat" (compute the shift
count and both odd parts) followed by the subtract-and-halve `loop`. It is
factored out so its giant continuation never sits under a `simp` driving
the small zero-check blocks. -/
def meatLoopProg : Program :=
  [ .localGet 2, .localGet 2, .load64 8, .localGet 2, .load64 16, .orI64,
    .ctzI64, .wrapI64, .store32 44,
    .localGet 2, .load32 44, .localSet 3,
    .localGet 2, .localGet 2, .load64 8, .ctzI64, .wrapI64, .store32 40,
    .localGet 2, .load32 40, .localSet 4,
    .localGet 2, .localGet 2, .load64 8, .localGet 4, .const 63, .and,
    .extendUI32, .shrUI64, .store64 8,
    .localGet 2, .localGet 2, .load64 16, .ctzI64, .wrapI64, .store32 36,
    .localGet 2, .load32 36, .localSet 5,
    .localGet 2, .localGet 2, .load64 16, .localGet 5, .const 63, .and,
    .extendUI32, .shrUI64, .store64 16,
    .loop 0 0 [
      .block 0 0 [
        .localGet 2, .load64 8, .localGet 2, .load64 16, .neI64, .const 1, .and,
        .br_if 0,
        .localGet 2, .localGet 2, .load64 8, .localGet 3, .const 63, .and,
        .extendUI32, .shlI64, .store64 0,
        .br 2 ],
      .block 0 0 [
        .localGet 2, .load64 8, .localGet 2, .load64 16, .gtUI64, .const 1, .and,
        .br_if 0,
        .localGet 2, .load64 8, .localSet 6,
        .localGet 2, .localGet 2, .load64 16, .localGet 6, .subI64, .store64 16,
        .localGet 2, .localGet 2, .load64 16, .ctzI64, .wrapI64, .store32 32,
        .localGet 2, .load32 32, .localSet 7,
        .localGet 2, .localGet 2, .load64 16, .localGet 7, .const 63, .and,
        .extendUI32, .shrUI64, .store64 16,
        .br 1 ],
      .localGet 2, .load64 16, .localSet 8,
      .localGet 2, .localGet 2, .load64 8, .localGet 8, .subI64, .store64 8,
      .localGet 2, .localGet 2, .load64 8, .ctzI64, .wrapI64, .store32 28,
      .localGet 2, .load32 28, .localSet 9,
      .localGet 2, .localGet 2, .load64 8, .localGet 9, .const 63, .and,
      .extendUI32, .shrUI64, .store64 8,
      .br 0 ] ]

/- Driving the OUTER-body program when both operands are nonzero. The
final result `gcd a b` is left at slot `1048512` (`fp + 0`); the loop
exits via `br 2`, surfacing as a `.Break 0` to the supplied continuation
`Q`. The continuation hypothesis `hQ` only needs the result slot and the
fact that the frame pointer (local 2) is unchanged, which is all the
OUTER continuation reads. -/
set_option maxHeartbeats 4000000 in
theorem meatLoop_wp (env : HostEnv Unit) (stm : Store Unit) (a b : UInt64)
    (p0 p1 l1 l2 l3 l4 l5 l6 l7 : Value) (vals : List Value) (Q : Assertion Unit)
    (hpg : stm.mem.pages = 16)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (ha : stm.mem.read64 1048520 = a)
    (hb : stm.mem.read64 1048528 = b)
    (hQ : ∀ (stf : Store Unit) (sf : Locals),
            stf.mem.read64 1048512 = UInt64.ofNat (a.toNat.gcd b.toNat) →
            stf.mem.pages = 16 →
            stf.globals = stm.globals →
            sf.get 2 = some (.i32 1048512) →
            Q (.Break 0 stf sf)) :
    wp «module» meatLoopProg Q stm
      { params := [p0, p1],
        locals := [.i32 1048512, l1, l2, l3, l4, l5, l6, l7], values := vals } env := by
  show wp «module» meatLoopProg Q stm _ env
  unfold meatLoopProg
  simp only []
  simp (config := { maxSteps := 4000000, decide := true }) only [wp_simp, Locals.get, Locals.set?,
    List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.set_cons_zero, List.set_cons_succ,
    Nat.reduceLT, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, reduceIte,
    Nat.reduceLeDiff,
    UInt32.reduceAdd, UInt32.reduceToNat, gt_iff_lt,
    Mem.read64_write64_disjoint, Mem.read64_write32_disjoint,
    Mem.read32_write32_same,
    hpg, ha, hb,
    Mem.write64_pages, Mem.write32_pages]
  -- Rewrite the two odd-part shift amounts into the `CodeLib` form.
  rw [shift_pipeline a ha0, shift_pipeline b hb0]
  -- Abbreviations for the odd parts and the recombination shift.
  set ao : UInt64 := a >>> (UInt64.ofNat (ctz64 64 a) % 64) with hao
  set bo : UInt64 := b >>> (UInt64.ofNat (ctz64 64 b) % 64) with hbo
  have hab0 : a ||| b ≠ 0 := fun h => ha0 (UInt64.or_eq_zero_iff.mp h).1
  have haone : ao ≠ 0 := UInt64.shr_ctz_ne_zero a ha0
  have hbone : bo ≠ 0 := UInt64.shr_ctz_ne_zero b hb0
  have haodd : ao.toNat % 2 = 1 := UInt64.shr_ctz_toNat_odd a ha0
  have hbodd : bo.toNat % 2 = 1 := UInt64.shr_ctz_toNat_odd b hb0
  -- Generalize the cluttered scratch-only memory into a single store whose
  -- slots `1048520`/`1048528` carry `ao`/`bo`.
  set stL : Store Unit :=
    { globals := stm.globals,
      mem :=
        ((((stm.mem.write32 1048556 (UInt32.ofNat ((UInt64.ofNat (ctz64 64 (a ||| b))).toNat % 2 ^ 32))).write32 1048552
                      (UInt32.ofNat ((UInt64.ofNat (ctz64 64 a)).toNat % 2 ^ 32))).write64
                  1048520 ao).write32
              1048548 (UInt32.ofNat ((UInt64.ofNat (ctz64 64 b)).toNat % 2 ^ 32))).write64
          1048528 bo,
      extraMems := stm.extraMems, dataSegments := stm.dataSegments, tables := stm.tables,
      elementSegments := stm.elementSegments, exns := stm.exns, host := stm.host } with hstL
  have hLpg : stL.mem.pages = 16 := by rw [hstL]; simp [hpg]
  have hLa : stL.mem.read64 1048520 = ao := by
    rw [hstL]
    rw [Mem.read64_write64_disjoint _ _ _ _ (by decide),
        Mem.read64_write32_disjoint _ _ _ _ (by decide),
        Mem.read64_write64_same]
  have hLb : stL.mem.read64 1048528 = bo := by
    rw [hstL]; rw [Mem.read64_write64_same]
  -- The shift amount used by the final `shl` recombine.
  have hsh : UInt64.ofNat ((63 : UInt32) &&&
      UInt32.ofNat ((UInt64.ofNat (ctz64 64 (a ||| b))).toNat % 2 ^ 32)).toNat % 64
      = UInt64.ofNat (ctz64 64 (b ||| a)) % 64 := by
    rw [ctz_wrap_and_toNat (a ||| b) hab0, ctz_or_comm]
  -- The constant shift value sitting in local 3 throughout the loop.
  set sh3 : UInt32 := UInt32.ofNat ((UInt64.ofNat (ctz64 64 (a ||| b))).toNat % 2 ^ 32) with hsh3
  apply wp_loop_cons
    (Inv := fun st' s' =>
      st'.mem.pages = 16 ∧ st'.globals = stm.globals ∧ s'.values = vals ∧
      (∃ c4 c5 c6 c7 c8 c9 : Value,
        s' = { params := [p0, p1],
               locals := [.i32 1048512, .i32 sh3, c4, c5, c6, c7, c8, c9], values := vals }) ∧
      ∃ x y : UInt64,
        st'.mem.read64 1048520 = x ∧ st'.mem.read64 1048528 = y ∧
        x ≠ 0 ∧ y ≠ 0 ∧ x.toNat % 2 = 1 ∧ y.toNat % 2 = 1 ∧
        Nat.gcd x.toNat y.toNat = Nat.gcd ao.toNat bo.toNat)
    (μ := fun st' _ => (st'.mem.read64 1048520).toNat + (st'.mem.read64 1048528).toNat)
  · -- Initial invariant.
    exact ⟨hLpg, rfl, rfl, ⟨_, _, _, _, _, _, rfl⟩, ao, bo, hLa, hLb, haone, hbone, haodd, hbodd, rfl⟩
  · -- One iteration.
    rintro st' s' ⟨hpg', hglob', hvals, ⟨c4, c5, c6, c7, c8, c9, rfl⟩, x, y, hxr, hyr, hxne, hyne, hxodd, hyodd, hgcd⟩
    -- Enter block A.
    apply wp_block_cons
    simp only [wp_simp, Locals.get, List.length_cons, List.length_nil,
      List.getElem?_cons_zero, List.getElem?_cons_succ,
      Nat.reduceLT, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, reduceIte,
      UInt32.reduceAdd, UInt32.reduceToNat, gt_iff_lt, hpg', hxr, hyr]
    by_cases hxy : x = y
    · -- x = y: loop exits with the recombined gcd.
      subst hxy
      simp only [ne_eq, not_true_eq_false, if_false]
      -- The break stores `x <<< shift` at slot 1048512.
      refine hQ _ _ ?_ ?_ hglob' rfl
      · -- result slot holds the gcd.
        rw [Mem.read64_write64_same, hsh]
        have hrec := UInt64.recombine_loop a b x ha0 hb0 ?_
        · simpa [ao, bo, UInt64.toNat_shiftRight] using hrec
        · rw [Nat.gcd_self]
          have hgcd' := hgcd
          rw [hao, hbo] at hgcd'
          simpa [UInt64.toNat_shiftRight] using hgcd'
      · rw [Mem.write64_pages]; exact hpg'
    · -- x ≠ y: fall into block B.
      rw [if_pos hxy]
      simp only [show (1 : UInt32) &&& 1 = 1 from rfl]
      apply wp_block_cons
      simp (config := { maxSteps := 4000000, decide := true }) only [wp_simp,
        Locals.get, Locals.set?, List.length_cons, List.length_nil,
        List.getElem?_cons_zero, List.getElem?_cons_succ, List.set_cons_zero, List.set_cons_succ,
        Nat.reduceLT, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, reduceIte,
        UInt32.reduceAdd, UInt32.reduceToNat, gt_iff_lt, hpg', hxr, hyr,
        Mem.read64_write64_same, Mem.read64_write64_disjoint, Mem.read64_write32_disjoint,
        Mem.read32_write32_same,
        Mem.write64_pages, Mem.write32_pages]
      simp only [List.take_zero, List.drop_zero, List.nil_append]
      by_cases hlt : y < x
      · -- y < x: subtract y from x, halve x.  (x-branch.)
        rw [if_pos hlt]
        obtain ⟨hne', hodd', hgcd', hdec⟩ := UInt64.stein_step_x x y hxne hyne hxodd hyodd hlt
        have hxsub0 : x - y ≠ 0 := by
          intro h
          have hsub := UInt64.toNat_sub_of_le x y
            (UInt64.le_iff_toNat_le.mpr (Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp hlt)))
          have h0 : (x - y).toNat = 0 := by rw [h]; rfl
          rw [hsub] at h0
          have := UInt64.lt_iff_toNat_lt.mp hlt
          omega
        have hshx := ctz_wrap_and_toNat (x - y) hxsub0
        have hx1 := oddPart_toNat (x - y)
        split
        · rename_i h; simp at h
        · rw [hshx]
          refine ⟨⟨trivial, hglob', by simp, ⟨c4, c5, _, _, _, _, rfl⟩,
            (x - y) >>> (UInt64.ofNat (ctz64 64 (x - y)) % 64), y,
            rfl, rfl, hne', hyne, ?_, hyodd, ?_⟩, ?_⟩
          · rw [hx1]; exact hodd'
          · rw [hx1]; exact hgcd'.trans hgcd
          · rw [hx1]; have := hdec; omega
        · rename_i h; exact (h 1 vals rfl).elim
      · -- ¬(y < x): subtract x from y, halve y.  (y-branch.)
        rw [if_neg hlt]
        obtain ⟨hne', hodd', hgcd', hdec⟩ :=
          UInt64.stein_step_y x y hxne hyne hxodd hyodd hlt hxy
        have hysub0 : y - x ≠ 0 := by
          intro h
          have hxlt : x < y := by
            rw [UInt64.lt_iff_toNat_lt]
            have h1 : ¬ y.toNat < x.toNat := fun hh => hlt (UInt64.lt_iff_toNat_lt.mpr hh)
            have h2 : x.toNat ≠ y.toNat := fun hh => hxy (UInt64.toNat.inj hh)
            omega
          have hsub := UInt64.toNat_sub_of_le y x
            (UInt64.le_iff_toNat_le.mpr (Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp hxlt)))
          have h0 : (y - x).toNat = 0 := by rw [h]; rfl
          rw [hsub] at h0
          have := UInt64.lt_iff_toNat_lt.mp hxlt
          omega
        have hshy := ctz_wrap_and_toNat (y - x) hysub0
        have hy1 := oddPart_toNat (y - x)
        split
        · rw [hshy]
          refine ⟨⟨trivial, hglob', trivial, ⟨c4, c5, _, _, c8, c9, rfl⟩,
            x, (y - x) >>> (UInt64.ofNat (ctz64 64 (y - x)) % 64),
            rfl, rfl, hxne, hne', hxodd, ?_, ?_⟩, ?_⟩
          · rw [hy1]; exact hodd'
          · rw [hy1]; exact hgcd'.trans hgcd
          · rw [hy1]; have := hdec; omega
        · rename_i h0 h; simp only [List.cons.injEq, Value.i32.injEq,
            show (1 : UInt32) &&& 0 = 0 from rfl] at h; exact (h0 h.1.symm).elim
        · rename_i h; exact (h 0 vals rfl).elim

set_option maxHeartbeats 4000000 in
theorem func1_terminates (env : HostEnv Unit) (st1 : Store Unit) (a b : UInt64)
    (tail : List Value)
    (hpg : st1.mem.pages = 16)
    (hg0 : st1.globals.globals[0]? = some (.i32 1048560))
    (ha : st1.mem.read64 1048560 = a)
    (hb : st1.mem.read64 1048568 = b) :
    TerminatesWith env «module» 1 st1 ([.i32 1048568, .i32 1048560] ++ tail)
      (fun st' vs => st'.globals = st1.globals ∧
        vs = .i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat)) :: tail) := by
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i32, .i32], [.i32, .i32, .i32, .i32, .i64, .i32, .i64, .i32], func1, [.i64], none⟩) rfl
  unfold func1
  wp_run
  rw [hg0]
  -- After frame setup + the two argument copies the memory is
  -- `(st1.mem.write64 1048520 a).write64 1048528 b`, the frame pointer is
  -- `local2 = 1048512`, and the bound checks are discharged by `hpg`.
  simp [ha, hb, Mem.read64_write64_disjoint, hpg]
  -- Memory now holds `a` at slot 1048520 and `b` at slot 1048528; frame
  -- pointer (local 2) is 1048512. Abbreviate the in-frame store.
  set M0 : Mem := (st1.mem.write64 1048520 a).write64 1048528 b with hM0
  have hM0a : M0.read64 1048520 = a := by
    rw [hM0, Mem.read64_write64_disjoint _ _ _ _ (by decide), Mem.read64_write64_same]
  have hM0b : M0.read64 1048528 = b := by
    rw [hM0, Mem.read64_write64_same]
  have hM0pg : M0.pages = 16 := by rw [hM0]; simp [hpg]
  -- Recognize the OUTER block body as `MIDDLE_block :: meatLoopProg` (defeq),
  -- keeping the giant meat opaque to `simp` during the zero-checks.
  show wp «module»
    (.block 0 0
      (.block 0 0
        (.block 0 0
          [.localGet 2, .load64 8, .constI64 0, .eqI64, .const 1, .and, .br_if 0,
           .localGet 2, .load64 16, .constI64 0, .eqI64, .const 1, .and, .eqz, .br_if 1]
         :: .localGet 2 :: .localGet 2 :: .load64 8 :: .localGet 2 :: .load64 16
            :: .orI64 :: .store64 0 :: .br 1 :: [])
       :: meatLoopProg)
     :: .localGet 2 :: .load64 0 :: .ret :: [])
    _ _ _ env
  apply wp_block_cons
  apply wp_block_cons
  apply wp_block_cons
  -- INNER body: the two zero-checks.
  simp only [wp_simp, Locals.get, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ,
    Nat.reduceLT, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, reduceIte,
    UInt32.reduceAdd, UInt32.reduceToNat, gt_iff_lt, hM0a, hM0b, hM0pg]
  -- The result slot read after the recombine-as-OR store.
  have horRead : (M0.write64 1048512 (a ||| b)).read64 1048512 = a ||| b :=
    Mem.read64_write64_same _ _ _
  have horPg : (M0.write64 1048512 (a ||| b)).pages = 16 := by rw [Mem.write64_pages]; exact hM0pg
  by_cases ha0 : a = 0
  · -- a = 0: result is `0 ||| b = b = gcd 0 b`.
    subst ha0
    simp only [if_true,
      show (1 : UInt32) &&& 1 = 1 from rfl]
    simp only [horRead, horPg, Nat.reduceMul]
    rw [show (0 : UInt64) ||| b = b from by
          apply UInt64.toNat.inj; rw [UInt64.toNat_or]; simp]
    refine ⟨trivial, ?_⟩
    simp [Nat.gcd_zero_left]
  · by_cases hb0 : b = 0
    · -- b = 0: result is `a ||| 0 = a = gcd a 0`.
      subst hb0
      simp only [ha0, if_false, if_true,
        show (1 : UInt32) &&& 0 = 0 from rfl, show (1 : UInt32) &&& 1 = 1 from rfl]
      simp only [horRead, horPg, Nat.reduceMul]
      rw [show a ||| (0 : UInt64) = a from by
            apply UInt64.toNat.inj; rw [UInt64.toNat_or]; simp]
      refine ⟨trivial, ?_⟩
      simp [Nat.gcd_zero_right]
    · -- both nonzero: run the Stein meat+loop.
      simp only [ha0, hb0, if_false, show (1 : UInt32) &&& 0 = 0 from rfl,
        if_true]
      apply meatLoop_wp (a := a) (b := b)
      · exact hM0pg
      · exact ha0
      · exact hb0
      · exact hM0a
      · exact hM0b
      · rintro stf sf hfr hfpg hfglob hfl2
        have hg2 : (if 2 < sf.params.length then sf.params[2]?
            else if 2 < sf.params.length + sf.locals.length then sf.locals[2 - sf.params.length]?
            else none) = some (.i32 1048512) := hfl2
        simp only [hg2, hfpg, List.take, List.nil_append,
          Nat.reduceMul, List.cons_append]
        rw [show (1048512 : UInt32) + 0 = 1048512 from rfl, hfr,
          show UInt32.toNat 1048512 = 1048512 from rfl]
        refine ⟨hfglob, ?_⟩
        norm_num

/-! ## `func0`: the wrapper that spills the operands and calls `func1` -/

/- `func0` allocates a 16-byte frame at `global0 − 16 = 1048560`, spills
`a` to `[1048560]` and `b` to `[1048568]`, calls `func1` with those two
pointers, restores the stack pointer and returns `gcd a b`. -/
set_option maxHeartbeats 1000000 in
theorem func0_terminates (env : HostEnv Unit) (a b : UInt64) :
    TerminatesWith env «module» 0 «module».initialStore [.i64 b, .i64 a]
      (fun _ rs => rs = [.i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))]) := by
  have hg : («module».initialStore : Store Unit).globals.globals[0]? = some (.i32 1048576) := by rfl
  have hp : («module».initialStore : Store Unit).mem.pages = 16 := by rfl
  apply TerminatesWith.of_wp_entry_for
    (f := ⟨[.i64, .i64], [.i32, .i64], func0, [.i64], none⟩) rfl
  unfold func0
  wp_run
  rw [hg]
  simp [hp]
  -- At the call point: memory holds `a` at 1048560, `b` at 1048568, global0
  -- is 1048560.  Discharge `func1` via its `TerminatesWith`.
  apply wp_call_tw
    (func1_terminates env _ a b []
      (by rw [Mem.write64_pages, Mem.write64_pages]; exact hp)
      (by rfl)
      (by rw [Mem.read64_write64_disjoint _ _ _ _ (by decide), Mem.read64_write64_same])
      (by rw [Mem.read64_write64_same]))
  -- The call returns `gcd a b`; restore the stack pointer and `ret`.
  rintro stA vsA ⟨hAglob, rfl⟩
  wp_run
  -- `globalSet 0` is in-bounds because `func1` preserved the globals.
  rw [hAglob]
  rfl

/-! ## Top spec -/

/-- The exported `gcd_u64` returns the greatest common divisor of two
`u64` operands, computed by the binary-GCD (Stein's) algorithm. The
`num-integer` convention `gcd(0, 0) = 0` is preserved.

The `initial = «module».initialStore` hypothesis is load-bearing: `func0`
spills the operands into a stack frame carved out of linear memory and
threads them through the global stack pointer, so the property depends on
the canonical instantiation (`global 0 = 1048576`, `16` pages). -/
@[spec_of "rust-exported" "num_integer::gcd_u64"]
def GcdU64Spec : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (a b : UInt64),
    initial = «module».initialStore →
    TerminatesWith env «module» 2 initial [.i64 b, .i64 a]
      (fun _ rs => rs = [.i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))])

@[proves Project.NumInteger.Spec.GcdU64Spec]
theorem gcd_u64_correct : GcdU64Spec := by
  intro env initial a b hinit
  subst hinit
  -- `func2` is the exported wrapper: pushes both args and calls `func0`.
  apply TerminatesWith.of_wp_entry_for (f := ⟨[.i64, .i64], [], func2, [.i64], none⟩) rfl
  unfold func2
  wp_run
  apply wp_call_tw (func0_terminates env a b)
  rintro st' vs rfl
  wp_run
  rfl

end Project.NumInteger.Spec
