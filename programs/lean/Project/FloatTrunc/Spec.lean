import Project.FloatTrunc.Program

/-!
# Specification for `float_trunc`

The exported `check` function asserts that `naive_trunc` (NaN/range checks + cast)
and `sat_trunc` (Rust's saturating `x as i32`) agree on every `f32` bit pattern.
The proof shows `check` always terminates normally with empty result.
-/

namespace Project.FloatTrunc.Spec

open Wasm

set_option maxRecDepth 1048576

/-! ## Efficient `∀ x : UInt32` decidability -/

/-- Countdown from n: true iff p holds for every UInt32 with toNat < n. -/
private def forallUInt32Aux (p : UInt32 → Bool) : Nat → Bool
  | 0     => true
  | n + 1 => if p (UInt32.ofNat n) then forallUInt32Aux p n else false

private theorem forallUInt32Aux_iff (p : UInt32 → Bool) (n : Nat) :
    forallUInt32Aux p n = true ↔ ∀ k : UInt32, k.toNat < n → p k = true := by
  induction n with
  | zero => simp [forallUInt32Aux]
  | succ n ih =>
    simp only [forallUInt32Aux]
    rcases Bool.eq_false_or_eq_true (p (UInt32.ofNat n)) with ht | hf
    · -- ht : p (UInt32.ofNat n) = true
      simp only [ht, ite_true, ih]
      constructor
      · intro hall k hk
        rcases (by omega : k.toNat < n ∨ k.toNat = n) with hlt | hkn
        · exact hall k hlt
        · have hke : k = UInt32.ofNat n := by
            have h0 := UInt32.ofNat_toNat (x := k)
            rw [hkn] at h0; exact h0.symm
          rw [hke]; exact ht
      · intro hall k hlt
        exact hall k (Nat.lt_succ_of_lt hlt)
    · -- hf : p (UInt32.ofNat n) = false
      simp only [hf, ite_false, Bool.false_eq_true, false_iff]
      intro hall
      have hlt : (UInt32.ofNat n).toNat < n + 1 := by
        have h1 : (UInt32.ofNat n).toNat = n % 2 ^ 32 := UInt32.toNat_ofNat'
        have h2 : n % 2 ^ 32 ≤ n := Nat.mod_le n _
        omega
      have hval := hall (UInt32.ofNat n) hlt
      simp [hf] at hval

/-- `native_decide` can decide `∀ x : UInt32, P x` via a 4B-iteration countdown. -/
private instance decidableForallUInt32 {P : UInt32 → Prop} [DecidablePred P] :
    Decidable (∀ x : UInt32, P x) :=
  let p := fun x => decide (P x)
  if h : forallUInt32Aux p UInt32.size then
    isTrue fun x =>
      of_decide_eq_true
        ((forallUInt32Aux_iff p UInt32.size).mp h x (UInt32.toNat_lt_size x))
  else
    isFalse fun hall =>
      h ((forallUInt32Aux_iff p UInt32.size).mpr fun k _ => decide_eq_true (hall k))

/-! ## Float math helpers -/

/-- Expose `private satI32S` body; provable by `rfl` since the kernel reduces it. -/
private theorem i32TruncSatF32S_expand (x : UInt32) :
    i32TruncSatF32S x =
    let f := (Float32.ofBits x).toFloat
    if f.isNaN then 0
    else let t := if f < 0.0 then f.ceil else f.floor
         if t ≤ (-2147483648.0 : Float) then 0x80000000
         else if t ≥ (2147483647.0 : Float) then 0x7FFFFFFF
         else t.toInt64.toUInt64.toUInt32 := rfl

/-- IEEE 754: `f32Ne x x = true` iff `x` encodes a NaN.
`f32Ne x x = !(f == f)` and `Float.isNaN f = !(f == f)` (both opaque externs);
checked for all 2^32 bit patterns by native evaluation. -/
private theorem f32Ne_self_iff_isNaN (x : UInt32) :
    f32Ne x x = (Float32.ofBits x).toFloat.isNaN :=
  IEEE32Exec.f32Ne_self_iff_isNaN x

private theorem i32TruncSatF32S_nan {x : UInt32}
    (h : (Float32.ofBits x).toFloat.isNaN) : i32TruncSatF32S x = 0 := by
  simp [i32TruncSatF32S_expand, h]

/-- `2^31` as a `Float32` bit pattern is `0x4F000000 = 1325400064`. When
`f ≥ 2^31`, `floor f ≥ 2^31 > 2147483647`, so `satI32S` saturates to `MAX`.
Checked for all 2^32 bit patterns by native evaluation. -/
private theorem i32TruncSatF32S_large_pos {x : UInt32}
    (hnan : f32Ne x x = false)
    (hge : f32Ge x 1325400064 = true) :
    i32TruncSatF32S x = 0x7FFFFFFF :=
  IEEE32Exec.i32TruncSatF32S_large_pos hnan hge

/-- `-2^31` as a `Float32` bit pattern is `0xCF000000 = 3472883712`. When
`f < -2^31`, `ceil f ≤ -2^31 ≤ -2147483648`, so `satI32S` saturates to `MIN`.
Checked for all 2^32 bit patterns by native evaluation. -/
private theorem i32TruncSatF32S_large_neg {x : UInt32}
    (hnan : f32Ne x x = false)
    (hlt : f32Lt x 3472883712 = true) :
    i32TruncSatF32S x = 0x80000000 :=
  IEEE32Exec.i32TruncSatF32S_large_neg hnan hlt

/-! ## Per-function termination -/

theorem func1_terminates (env : HostEnv Unit) (st : Store Unit) (x : UInt32)
    (tail : List Value) :
    TerminatesWith env «module» 1 st ([.f32 x] ++ tail)
      (fun _ rs => rs = [.i32 (i32TruncSatF32S x)] ++ tail) := by
  apply TerminatesWith.of_wp_entry_for (f := ⟨[.f32], [], func1, [.i32], none⟩) rfl
  unfold func1
  wp_run
  simp

set_option maxHeartbeats 800000 in
theorem func0_terminates (env : HostEnv Unit) (x : UInt32) :
    TerminatesWith env «module» 0 «module».initialStore [.f32 x]
      (fun _ rs => rs = [.i32 (i32TruncSatF32S x)]) := by
  have hg : («module».initialStore : Store Unit).globals.globals[0]? =
      some (.i32 1048576) := rfl
  have hp : («module».initialStore : Store Unit).mem.pages = 17 := rfl
  apply TerminatesWith.of_wp_entry_for (f := ⟨[.f32], [.i32], func0, [.i32], none⟩) rfl
  unfold func0; wp_run
  simp only [hg]
  apply wp_block_cons; apply wp_block_cons; apply wp_block_cons
  apply wp_block_cons; apply wp_block_cons; apply wp_block_cons
  wp_run
  -- Four-way case split: NaN, large-pos, large-neg, normal
  cases hnan : f32Ne x x
  · -- f32Ne x x = false → not NaN
    cases hge : f32Ge x 1325400064
    · -- not large pos
      cases hlt : f32Lt x 3472883712
      · -- normal case: func0 calls i32TruncSatF32S directly
        simp [hnan, hge, hlt, hp, Mem.write32_pages, Mem.read32_write32_same]
      · -- large neg: stores 0x80000000
        have heq := i32TruncSatF32S_large_neg hnan hlt
        simp [hnan, hge, hlt, hp, Mem.write32_pages, Mem.read32_write32_same, heq]
    · -- large pos: stores 0x7FFFFFFF
      have heq := i32TruncSatF32S_large_pos hnan hge
      simp [hnan, hge, hp, Mem.write32_pages, Mem.read32_write32_same, heq]
  · -- f32Ne x x = true → NaN: stores 0
    have hisNaN : (Float32.ofBits x).toFloat.isNaN = true :=
      (f32Ne_self_iff_isNaN x).symm.trans hnan
    have heq := i32TruncSatF32S_nan hisNaN
    simp [hnan, hp, Mem.write32_pages, Mem.read32_write32_same, heq]

/-! ## Top-level spec -/

@[spec_of "rust-exported" "float_trunc::check"]
def FloatTruncSpec : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (x : UInt32),
    initial = «module».initialStore →
    TerminatesWith env «module» 2 initial [.f32 x] (fun _ rs => rs = [])

@[proves Project.FloatTrunc.Spec.FloatTruncSpec]
theorem check_correct : FloatTruncSpec := by
  intro env initial x hinit
  subst hinit
  apply TerminatesWith.of_wp_entry_for (f := ⟨[.f32], [], func2, [], none⟩) rfl
  unfold func2
  apply wp_block_cons
  wp_run
  apply wp_call_of_terminates (func0_terminates env x)
  rintro st0 vs0 rfl
  wp_run
  apply wp_call_of_terminates (func1_terminates env st0 x [.i32 (i32TruncSatF32S x)])
  rintro st1 vs1 rfl
  wp_run
  simp [ne_eq]

end Project.FloatTrunc.Spec
