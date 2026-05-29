import Project.NumInteger.Program

/-!
# Specification for `gcd_u64`

The exported `gcd_u64` function implements the binary GCD (Stein's
algorithm) on `u64` operands. By the `num-integer` convention the function
returns `0` on `(0, 0)`.
-/

namespace Project.NumInteger.Spec

open Wasm

/-- Local aliases for the `UInt64` ↔ `Nat` bridge lemmas used in this
proof. The actual content lives in `CodeLib.UInt64`. -/
private alias uint64_shr_ctz_odd    := UInt64.shr_ctz_toNat_odd
private alias uint64_shr_ctz_pos    := UInt64.shr_ctz_ne_zero
private alias uint64_recombine_eq   := UInt64.recombine_eq
private alias uint64_recombine_loop := UInt64.recombine_loop
private alias uint64_loop_step_x    := UInt64.stein_step_x
private alias uint64_loop_step_y    := UInt64.stein_step_y

/-! ## Top spec -/

/-- The exported `gcd_u64` returns the greatest common divisor of two
`u64` operands, computed by the binary-GCD (Stein's) algorithm.

Informal spec:
For any inputs `a b : UInt64`, the wasm export `gcd_u64` terminates and
leaves a single i64 on the value stack equal to `Nat.gcd a.toNat b.toNat`
(coerced back into `UInt64`). The `num-integer` convention `gcd(0, 0) = 0`
is preserved. -/
@[spec_of "rust-exported" "num_integer::gcd_u64"]
def GcdU64Spec : Prop :=
  ∀ (initial : Store) (a b : UInt64),
    -- Args are passed in stack order (top first). The Wasm caller pushes
    -- `a` then `b`, so the operand stack handed to `run` is `[b, a]` —
    -- which `run` reverses on entry to make local 0 = a, local 1 = b.
    TerminatesWith «module» 0 initial [.i64 b, .i64 a]
      (fun _ rs => rs = [.i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))])

@[proves Project.NumInteger.Spec.GcdU64Spec]
theorem gcd_u64_correct : GcdU64Spec := by
  intro initial a b
  refine FuncSpec.to_TerminatesWith (Pre := fun args => args = [.i64 b, .i64 a]) ?spec rfl
  refine FuncSpec.of_wp_body (f := ⟨[.i64, .i64], [.i64, .i64], func0, [.i64]⟩) rfl ?_
  intro args hPre initial'
  subst hPre
  show wp _ func0 _ _ _
  unfold func0
  wp_run
  simp
  -- Enter OUTER block.
  apply wp_block_cons
  -- Zero-check 1: `localGet 0; eqzI64; br_if 0`.
  wp_run
  simp
  by_cases ha0 : a = 0
  · -- a = 0: br_if fires, breaks OUTER; localGet 2 returns b|||a = b.
    subst ha0; simp
  · -- a ≠ 0. First br_if doesn't fire.
    simp [ha0]
    by_cases hb0 : b = 0
    · -- b = 0: second br_if fires.
      subst hb0; simp
    · -- Both nonzero. Enter MIDDLE block.
      simp [hb0]
      apply wp_block_cons
      -- Enter INNER block.
      apply wp_block_cons
      wp_run
      simp
      -- After symbolic execution of INNER body, the goal is a `match` on
      -- `[Value.i32 (if a_odd = b_odd then 0 else 1)]` (the `neI64` result).
      by_cases hEq : a >>> (UInt64.ofNat (ctz64 64 a) % 64)
                   = b >>> (UInt64.ofNat (ctz64 64 b) % 64)
      · -- a_odd = b_odd: fallthrough INNER, the trailing `localSet 0; br 1`
        -- exits MIDDLE; post-MIDDLE recombine then closes.
        simp [hEq]
        have h := uint64_recombine_eq a b ha0 hb0 hEq
        rw [hEq] at h
        exact h
      · -- a_odd ≠ b_odd: br_if 0 fires in INNER → fall into the main LOOP.
        simp [hEq]
        -- Loop invariant: locals[2] = l2 odd & nonzero, params[0] = l0 odd & nonzero,
        -- gcd(l2.toNat, l0.toNat) = gcd(a_odd.toNat, b_odd.toNat).
        apply wp_loop_cons
          (Inv := fun st' s' => st' = initial' ∧
            ∃ (x y : UInt64),
              s' = ⟨[.i64 y, .i64 b],
                    [.i64 x, .i64 (UInt64.ofNat (ctz64 64 (b ||| a)))], []⟩ ∧
              x ≠ 0 ∧ y ≠ 0 ∧ x ≠ y ∧
              x.toNat % 2 = 1 ∧ y.toNat % 2 = 1 ∧
              Nat.gcd x.toNat y.toNat
                = Nat.gcd (a.toNat >>> (ctz64 64 a % 64))
                          (b.toNat >>> (ctz64 64 b % 64)))
          (μ := fun _ s' =>
            match s'.locals.headD (.i64 0), s'.params.headD (.i64 0) with
            | .i64 x, .i64 y => x.toNat + y.toNat
            | _, _ => 0)
        · -- Initial invariant: after INNER's br_if, l2 = a_odd, l0 = b_odd.
          refine ⟨rfl,
            a >>> (UInt64.ofNat (ctz64 64 a) % 64),
            b >>> (UInt64.ofNat (ctz64 64 b) % 64),
            rfl, ?_, ?_, hEq, ?_, ?_, ?_⟩
          · exact uint64_shr_ctz_pos a ha0
          · exact uint64_shr_ctz_pos b hb0
          · exact uint64_shr_ctz_odd a ha0
          · exact uint64_shr_ctz_odd b hb0
          · simp [UInt64.toNat_shiftRight]
        · -- Per-iteration: invariant + measure preservation.
          rintro st' s' ⟨rfl, x, y, rfl, hxne, hyne, hxny, hxodd, hyodd, hgcd⟩
          apply wp_block_cons
          apply wp_block_cons
          wp_run
          simp
          by_cases hlt : y < x
          · -- y < x: subtract y from x, halve. (br_if 0 in B fires.)
            simp [hlt]
            obtain ⟨hxne', hxodd', hgcd', hdec⟩ :=
              uint64_loop_step_x x y hxne hyne hxodd hyodd hlt
            by_cases hEq2 : (x - y) >>> (UInt64.ofNat (ctz64 64 (x - y)) % 64) = y
            · -- Loop exits: l2 = l0 = y. Recombine.
              simp [hEq2]
              have hN : (x - y).toNat >>> (ctz64 64 (x - y) % 64) = y.toNat := by
                have := congrArg UInt64.toNat hEq2
                simpa [UInt64.toNat_shiftRight] using this
              have hgcd'' : y.toNat.gcd y.toNat
                  = (a.toNat >>> (ctz64 64 a % 64)).gcd
                      (b.toNat >>> (ctz64 64 b % 64)) := by
                rw [hN] at hgcd'; rw [hgcd']; exact hgcd
              exact uint64_recombine_loop a b y ha0 hb0 hgcd''
            · -- Loop continues. Build the invariant and bound the measure.
              simp [hEq2]
              exact ⟨⟨hxne', hyne, hxodd', hyodd, hgcd'.trans hgcd⟩, hdec⟩
          · -- y ≥ x: subtract x from y, halve. (br_if 0 in B does NOT fire; falls through.)
            simp [hlt]
            obtain ⟨hyne', hyodd', hgcd', hdec⟩ :=
              uint64_loop_step_y x y hxne hyne hxodd hyodd hlt hxny
            by_cases hEq2 : x = (y - x) >>> (UInt64.ofNat (ctz64 64 (y - x)) % 64)
            · -- Loop exits: l2 = l0 = x. Recombine.
              simp [← hEq2]
              have hN : (y - x).toNat >>> (ctz64 64 (y - x) % 64) = x.toNat := by
                have := congrArg UInt64.toNat hEq2.symm
                simpa [UInt64.toNat_shiftRight] using this
              have hgcd'' : x.toNat.gcd x.toNat
                  = (a.toNat >>> (ctz64 64 a % 64)).gcd
                      (b.toNat >>> (ctz64 64 b % 64)) := by
                rw [hN] at hgcd'; rw [hgcd']; exact hgcd
              exact uint64_recombine_loop a b x ha0 hb0 hgcd''
            · simp [hEq2]
              exact ⟨⟨hxne, hyne', hxodd, hyodd', hgcd'.trans hgcd⟩, hdec⟩

end Project.NumInteger.Spec
