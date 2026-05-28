import Programs.Simple.Memchr.Program

/-!
# Specification for `memchr`

The exported `memchr(ptr, len, needle)` function returns the (0-based) index
of the first byte equal to `needle` in memory `[ptr, ptr+len)`, or `len` if
no byte matches.
-/

namespace Programs.Simple.Memchr.Spec

open Wasm

/-- Scan `rem` bytes starting at byte index `k`. Returns the absolute index of
    the first match with `needle`, or `k + rem` (= original `len`) if absent. -/
def memchrAux (m : Mem) (ptr needle : UInt32) : Nat → Nat → UInt32
  | 0, k => UInt32.ofNat k
  | rem + 1, k =>
    if (m.read8 (UInt32.ofNat k + ptr)).toUInt32 = needle then UInt32.ofNat k
    else memchrAux m ptr needle rem (k + 1)

private lemma memchrAux_match {m : Mem} {ptr needle : UInt32} {k rem : Nat}
    (h : (m.read8 (UInt32.ofNat k + ptr)).toUInt32 = needle) :
    memchrAux m ptr needle (rem + 1) k = UInt32.ofNat k := by
  simp [memchrAux, h]

private lemma memchrAux_no_match {m : Mem} {ptr needle : UInt32} {k rem : Nat}
    (h : ¬ (m.read8 (UInt32.ofNat k + ptr)).toUInt32 = needle) :
    memchrAux m ptr needle (rem + 1) k = memchrAux m ptr needle rem (k + 1) := by
  simp [memchrAux, h]

theorem memchr_correct (initial : Store) (ptr len needle : UInt32)
    (hmem : ∀ k < len.toNat, (k + ptr.toNat) % 4294967296 < initial.mem.pages * 65536) :
    TerminatesWith «module» 0 initial [.i32 ptr, .i32 len, .i32 needle]
      (fun st' rs => rs = [.i32 (memchrAux st'.mem ptr needle len.toNat 0)]) := by
  apply TerminatesWith.of_wp_entry_for (f := ⟨[.i32, .i32, .i32], [.i32], func0, [.i32]⟩) rfl
  unfold func0
  wp_run
  simp
  apply wp_block_cons
  wp_run
  simp
  by_cases hlen : len = 0
  · -- len = 0: br_if 0 exits block; result = local 3 = 0 = len
    simp [hlen, memchrAux]
  · -- len ≠ 0: falls through; enter loop
    simp [hlen]
    apply wp_loop_cons
      (Inv := fun st' s' =>
        st' = initial ∧
        ∃ k : Nat, k < len.toNat ∧
          memchrAux initial.mem ptr needle (len.toNat - k) k =
            memchrAux initial.mem ptr needle len.toNat 0 ∧
          s' = ⟨[.i32 ptr, .i32 len, .i32 needle], [.i32 (UInt32.ofNat k)], []⟩)
      (μ := fun _ s' => match s'.locals with
        | [.i32 i] => len.toNat - i.toNat
        | _ => 0)
    · -- Initial invariant: k = 0
      refine ⟨rfl, 0, ?_, ?_, ?_⟩
      · exact Nat.pos_of_ne_zero (fun h => hlen (UInt32.toNat.inj (by simpa using h)))
      · simp
      · simp
    · -- Loop step
      rintro st' s' ⟨rfl, k, hk, hinv, rfl⟩
      wp_run
      simp
      -- after simp, goal uses (st'.mem.read8 (UInt32.ofNat k + ptr)).toUInt32
      by_cases hmatch : (st'.mem.read8 (UInt32.ofNat k + ptr)).toUInt32 = needle
      · -- Match: br_if 1 fires → exits block
        simp [hmatch]
        refine ⟨hmem k hk, ?_⟩
        have hrem : len.toNat - k = (len.toNat - k - 1) + 1 := by omega
        rw [← hinv, hrem, memchrAux_match hmatch]
      · -- No match: br_if 1 doesn't fire
        simp [hmatch]
        have hsize : UInt32.size = 4294967296 := rfl
        have hlt := UInt32.toNat_lt len
        have hk_lt : k < UInt32.size := by omega
        have hk1_lt : k + 1 < UInt32.size := by omega
        by_cases hexit : len = 1 + UInt32.ofNat k
        · -- Loop exhausts: br_if 0 doesn't fire → Fallthrough
          simp [hexit]
          refine ⟨hmem k hk, ?_⟩
          -- goal: 1 + UInt32.ofNat k = memchrAux st'.mem ptr needle ((1 + k) % 4294967296) 0
          have hmod : (1 + k) % 4294967296 = k + 1 := by
            rw [← hsize, show 1 + k = k + 1 from by omega]; exact Nat.mod_eq_of_lt hk1_lt
          have hlen_eq : len.toNat = k + 1 := by
            rw [hexit, UInt32.toNat_add, UInt32.toNat_ofNat_of_lt' hk_lt]
            simp only [show (1 : UInt32).toNat = 1 from rfl]
            rw [show 1 + k = k + 1 from by omega, Nat.mod_eq_of_lt hk1_lt]
          rw [hmod, ← hlen_eq]
          -- goal: 1 + UInt32.ofNat k = memchrAux st'.mem ptr needle len.toNat 0
          have hrem : len.toNat - k = 0 + 1 := by omega
          have step : memchrAux st'.mem ptr needle (len.toNat - k) k = UInt32.ofNat (k + 1) := by
            rw [hrem, memchrAux_no_match hmatch]; simp [memchrAux]
          rw [← hinv, step]
          -- goal: 1 + UInt32.ofNat k = UInt32.ofNat (k + 1)
          apply UInt32.toNat.inj
          rw [UInt32.toNat_add, UInt32.toNat_ofNat_of_lt' hk_lt, UInt32.toNat_ofNat_of_lt' hk1_lt]
          simp only [show (1 : UInt32).toNat = 1 from rfl]
          rw [show 1 + k = k + 1 from by omega, Nat.mod_eq_of_lt hk1_lt]
        · -- Loop continues: br_if 0 fires → Break 0
          simp [hexit]
          refine ⟨hmem k hk, ?_⟩
          have hk1 : k + 1 < len.toNat := by
            have hne : len.toNat ≠ k + 1 := by
              intro heq
              apply hexit
              apply UInt32.toNat.inj
              rw [UInt32.toNat_add, UInt32.toNat_ofNat_of_lt' hk_lt]
              simp only [show (1 : UInt32).toNat = 1 from rfl]
              rw [show 1 + k = k + 1 from by omega, Nat.mod_eq_of_lt hk1_lt]
              exact heq
            omega
          have hinv' : memchrAux st'.mem ptr needle (len.toNat - (k + 1)) (k + 1) =
              memchrAux st'.mem ptr needle len.toNat 0 := by
            have hrem : len.toNat - k = (len.toNat - k - 1) + 1 := by omega
            rw [← hinv, hrem, memchrAux_no_match hmatch]
            congr 1
          have hk1_eq : (1 : UInt32) + UInt32.ofNat k = UInt32.ofNat (k + 1) := by
            apply UInt32.toNat.inj
            rw [UInt32.toNat_add, UInt32.toNat_ofNat_of_lt' hk_lt, UInt32.toNat_ofNat_of_lt' hk1_lt]
            simp only [show (1 : UInt32).toNat = 1 from rfl]
            rw [show 1 + k = k + 1 from by omega, Nat.mod_eq_of_lt hk1_lt]
          constructor
          · exact ⟨k + 1, hk1, hinv', hk1_eq⟩
          · have h1 : k % 4294967296 = k := Nat.mod_eq_of_lt (by omega)
            have h2 : (1 + k) % 4294967296 = 1 + k := Nat.mod_eq_of_lt (by omega)
            omega

end Programs.Simple.Memchr.Spec
