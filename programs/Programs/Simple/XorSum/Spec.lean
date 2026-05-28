import Programs.Simple.XorSum.Program

/-!
# Specification for `xor_sum`

The exported `xor_sum(ptr, len)` function XOR-folds `len` contiguous
little-endian `u32` values from linear memory starting at byte address `ptr`.
Returns `0` when `len = 0`.
-/

namespace Programs.Simple.XorSum.Spec

open Wasm

/-- XOR fold of `n` consecutive u32 values at byte addresses
    `ptr, ptr+4, …, ptr + 4*(n-1)` in memory `m`. -/
def xorFold (m : Mem) (ptr : UInt32) : Nat → UInt32
  | 0     => 0
  | n + 1 => xorFold m ptr n ^^^ m.read32 (ptr + 4 * UInt32.ofNat n)

private lemma xorFold_succ (m : Mem) (ptr : UInt32) (n : Nat) :
    xorFold m ptr (n + 1) = xorFold m ptr n ^^^ m.read32 (ptr + 4 * UInt32.ofNat n) := rfl

private lemma uint32_ofNat_le_of_le {k : Nat} {len : UInt32}
    (hk : k ≤ len.toNat) : UInt32.ofNat k ≤ len := by
  have hk32 : k < UInt32.size := Nat.lt_of_le_of_lt hk (UInt32.toNat_lt len)
  exact (UInt32.ofNat_le_iff hk32).mpr hk

private lemma uint32_sub_toNat_of_nat_le {k : Nat} {len : UInt32}
    (hk : k ≤ len.toNat) : (len - UInt32.ofNat k).toNat = len.toNat - k := by
  have hk32 : k < UInt32.size := Nat.lt_of_le_of_lt hk (UInt32.toNat_lt len)
  have hle := uint32_ofNat_le_of_le hk
  rw [UInt32.toNat_sub_of_le len (UInt32.ofNat k) hle,
      UInt32.toNat_ofNat_of_lt' hk32]

theorem xor_sum_correct (initial : Store) (ptr len : UInt32)
    (hmem : ∀ k < len.toNat, (ptr.toNat + 4 * k) % 4294967296 + 4 ≤ initial.mem.pages * 65536) :
    -- Args in stack order (top first); `run` reverses on entry so
    -- local 0 = ptr, local 1 = len.
    TerminatesWith «module» 0 initial [.i32 len, .i32 ptr]
      (fun st' rs => rs = [.i32 (xorFold st'.mem ptr len.toNat)]) := by
  apply TerminatesWith.of_wp_entry_for (f := ⟨[.i32, .i32], [.i32], func0, [.i32]⟩) rfl
  unfold func0
  wp_run
  simp
  apply wp_block_cons
  wp_run
  simp
  by_cases hlen : len = 0
  · -- len = 0: eqz gives 1, br_if breaks block; acc = 0
    simp [hlen, xorFold]
  · -- len ≠ 0: br_if falls through; enter loop
    simp [hlen]
    apply wp_loop_cons
      (Inv := fun st' s' =>
        st' = initial ∧
        ∃ k : Nat, k < len.toNat ∧
          s' = ⟨[.i32 (ptr + 4 * UInt32.ofNat k),
                  .i32 (len - UInt32.ofNat k)],
                 [.i32 (xorFold initial.mem ptr k)], []⟩)
      (μ := fun _ s' => match s'.params with
        | [_, .i32 rem] => rem.toNat
        | _ => 0)
    · -- Initial invariant: k = 0
      refine ⟨rfl, 0, ?_, ?_⟩
      · exact Nat.pos_of_ne_zero (fun h => hlen (UInt32.toNat.inj (by simpa using h)))
      · simp [xorFold]
    · -- Loop step
      rintro st' s' ⟨rfl, k, hk, rfl⟩
      wp_run
      simp
      -- 4294967295 + (len - k) = len - (k+1) as UInt32 values
      have h_nxt_eq : (4294967295 : UInt32) + (len - UInt32.ofNat k) =
          len - UInt32.ofNat (k + 1) := by
        apply UInt32.toNat.inj
        have hlt := UInt32.toNat_lt len
        rw [uint32_sub_toNat_of_nat_le (by omega : k + 1 ≤ len.toNat)]
        simp [UInt32.toNat_add, uint32_sub_toNat_of_nat_le hk.le]
        omega
      -- Case split on the br_if discriminant directly
      by_cases hexit : (4294967295 : UInt32) + (len - UInt32.ofNat k) = 0
      · -- Loop exits: br_if falls through; accumulate final element
        simp [hexit]
        have hk1 : k + 1 = len.toNat := by
          have h1 := uint32_sub_toNat_of_nat_le (k := k + 1) (len := len) (by omega)
          have h0 : len - UInt32.ofNat (k + 1) = 0 := h_nxt_eq ▸ hexit
          rw [h0] at h1; simp at h1; omega
        refine ⟨hmem k hk, ?_⟩
        simp only [xorFold_succ, ← hk1]
        exact UInt32.xor_comm _ _
      · -- Loop continues: br_if takes branch; re-enter with invariant at k+1
        simp
        have hk1 : k + 1 < len.toNat := by
          have h1 := uint32_sub_toNat_of_nat_le (k := k + 1) (len := len) (by omega)
          have hexit' : len - UInt32.ofNat (k + 1) ≠ 0 :=
            fun h => hexit (h_nxt_eq.symm ▸ h)
          have hne : (len - UInt32.ofNat (k + 1)).toNat ≠ 0 :=
            fun h => hexit' (UInt32.toNat.inj (by simpa using h))
          rw [h1] at hne; omega
        refine ⟨hmem k hk, ⟨k + 1, hk1, ⟨⟨?_, ?_⟩, ?_⟩⟩, ?_⟩
        · apply UInt32.toNat.inj; simp [UInt32.toNat_add]; omega
        · exact h_nxt_eq
        · simp only [xorFold_succ]; exact UInt32.xor_comm _ _
        · have hlt := UInt32.toNat_lt len
          rw [uint32_sub_toNat_of_nat_le hk.le]
          omega

end Programs.Simple.XorSum.Spec
