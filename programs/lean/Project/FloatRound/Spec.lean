import Project.FloatRound.Program
import CodeLib.IEEE32.Exec

/-!
# Specification for `float_round`

The exported `check_round` function tests whether the naive round
(trunc + compare frac) and optimized round (f32.nearest) agree.
They intentionally disagree on half-integers, so we only prove termination.
-/

namespace Project.FloatRound.Spec

open Wasm

set_option maxRecDepth 1048576
set_option maxHeartbeats 4000000

-- after globalSet 0, the new global[0] holds the stored value
private theorem globals_set0 {st : Store Unit} {sp : UInt32} (sp' : UInt32)
    (hg : st.globals.globals[0]? = some (.i32 sp)) :
    ({st with globals := {globals := st.globals.globals.set 0 (.i32 sp')}} : Store Unit).globals.globals[0]? = some (.i32 sp') := by
  cases h : st.globals.globals with
  | nil => simp [h] at hg
  | cons _ _ => rfl

-- frame at (sp-16)+12 stays in bounds given sp >= 16 and sp <= pages*65536
private theorem frame_oob_false {sp : UInt32} {pages : Nat}
    (h16 : 16 <= sp.toNat) (hb : sp.toNat <= pages * 65536) :
    ¬ ((sp - 16).toNat + 12 + 4 > pages * 65536) := by
  have hle : (16 : UInt32) <= sp := UInt32.le_iff_toNat_le.mpr (by simpa using h16)
  have hsub : (sp - 16).toNat = sp.toNat - 16 := UInt32.toNat_sub_of_le sp 16 hle
  rw [hsub]; omega

-- WP rules produce off.toNat where off : UInt32 = 12; normalize to Nat literal
private theorem off12 : (12 : UInt32).toNat = 12 := rfl

/-! ## func1/2/3/5: single float op via frame -/

private theorem func1_term (env : HostEnv Unit) (st : Store Unit) (sp x : UInt32)
    (tail : List Value)
    (hg : st.globals.globals[0]? = some (.i32 sp))
    (hp : st.mem.pages = 16) (h16 : 16 <= sp.toNat) (hb : sp.toNat <= 16 * 65536) :
    TerminatesWith env «module» 1 st ([.f32 x] ++ tail)
      (fun st' rs => ∃ v : UInt32, rs = [.f32 v] ++ tail ∧
        st'.globals.globals[0]? = some (.i32 sp) ∧ st'.mem.pages = 16) := by
  apply TerminatesWith.of_wp_entry_for (f := ⟨[.f32], [.i32], func1, [.f32], none⟩) rfl
  unfold func1; wp_run
  simp [hg, hp]
  have hle : (16 : UInt32) ≤ sp := UInt32.le_iff_toNat_le.mpr h16
  have hsub : (sp - 16).toNat = sp.toNat - 16 := UInt32.toNat_sub_of_le sp 16 hle
  omega

private theorem func2_term (env : HostEnv Unit) (st : Store Unit) (sp x : UInt32)
    (tail : List Value)
    (hg : st.globals.globals[0]? = some (.i32 sp))
    (hp : st.mem.pages = 16) (h16 : 16 <= sp.toNat) (hb : sp.toNat <= 16 * 65536) :
    TerminatesWith env «module» 2 st ([.f32 x] ++ tail)
      (fun st' rs => ∃ v : UInt32, rs = [.f32 v] ++ tail ∧
        st'.globals.globals[0]? = some (.i32 sp) ∧ st'.mem.pages = 16) := by
  apply TerminatesWith.of_wp_entry_for (f := ⟨[.f32], [.i32], func2, [.f32], none⟩) rfl
  unfold func2; wp_run
  simp [hg, hp]
  have hle : (16 : UInt32) ≤ sp := UInt32.le_iff_toNat_le.mpr h16
  have hsub : (sp - 16).toNat = sp.toNat - 16 := UInt32.toNat_sub_of_le sp 16 hle
  omega

private theorem func3_term (env : HostEnv Unit) (st : Store Unit) (sp x : UInt32)
    (tail : List Value)
    (hg : st.globals.globals[0]? = some (.i32 sp))
    (hp : st.mem.pages = 16) (h16 : 16 <= sp.toNat) (hb : sp.toNat <= 16 * 65536) :
    TerminatesWith env «module» 3 st ([.f32 x] ++ tail)
      (fun st' rs => ∃ v : UInt32, rs = [.f32 v] ++ tail ∧
        st'.globals.globals[0]? = some (.i32 sp) ∧ st'.mem.pages = 16) := by
  apply TerminatesWith.of_wp_entry_for (f := ⟨[.f32], [.i32], func3, [.f32], none⟩) rfl
  unfold func3; wp_run
  simp [hg, hp]
  have hle : (16 : UInt32) ≤ sp := UInt32.le_iff_toNat_le.mpr h16
  have hsub : (sp - 16).toNat = sp.toNat - 16 := UInt32.toNat_sub_of_le sp 16 hle
  omega

private theorem func5_term (env : HostEnv Unit) (st : Store Unit) (sp x : UInt32)
    (tail : List Value)
    (hg : st.globals.globals[0]? = some (.i32 sp))
    (hp : st.mem.pages = 16) (h16 : 16 <= sp.toNat) (hb : sp.toNat <= 16 * 65536) :
    TerminatesWith env «module» 5 st ([.f32 x] ++ tail)
      (fun st' rs => ∃ v : UInt32, rs = [.f32 v] ++ tail ∧
        st'.globals.globals[0]? = some (.i32 sp) ∧ st'.mem.pages = 16) := by
  apply TerminatesWith.of_wp_entry_for (f := ⟨[.f32], [.i32], func5, [.f32], none⟩) rfl
  unfold func5; wp_run
  simp [hg, hp]
  have hle : (16 : UInt32) ≤ sp := UInt32.le_iff_toNat_le.mpr h16
  have hsub : (sp - 16).toNat = sp.toNat - 16 := UInt32.toNat_sub_of_le sp 16 hle
  omega

/-! ## func4: wrapper calling func5 -/

private theorem func4_term (env : HostEnv Unit) (st : Store Unit) (sp x : UInt32)
    (tail : List Value)
    (hg : st.globals.globals[0]? = some (.i32 sp))
    (hp : st.mem.pages = 16) (h16 : 16 <= sp.toNat) (hb : sp.toNat <= 16 * 65536) :
    TerminatesWith env «module» 4 st ([.f32 x] ++ tail)
      (fun st' rs => ∃ v : UInt32, rs = [.f32 v] ++ tail ∧
        st'.globals.globals[0]? = some (.i32 sp) ∧ st'.mem.pages = 16) := by
  apply TerminatesWith.of_wp_entry_for (f := ⟨[.f32], [], func4, [.f32], none⟩) rfl
  unfold func4; wp_run
  apply wp_call_of_terminates (func5_term env st sp x [] hg hp h16 hb)
  rintro st5 vs5 ⟨v5, rfl, hg5, hp5⟩
  wp_run
  exact ⟨v5, rfl, hg5, hp5⟩

/-! ## func0: naive round via trunc + frac comparison -/

private theorem func0_term (env : HostEnv Unit) (st : Store Unit) (sp x : UInt32)
    (hg : st.globals.globals[0]? = some (.i32 sp))
    (hp : st.mem.pages = 16) (h32 : 32 <= sp.toNat) (hb : sp.toNat <= 16 * 65536) :
    TerminatesWith env «module» 0 st [.f32 x]
      (fun st' rs => ∃ v : UInt32, rs = [.f32 v] ∧
        st'.globals.globals[0]? = some (.i32 sp) ∧ st'.mem.pages = 16) := by
  apply TerminatesWith.of_wp_entry_for (f := ⟨[.f32], [.i32, .f32, .f32, .f32], func0, [.f32], none⟩) rfl
  unfold func0; wp_run; simp only [hg]
  -- frame setup: sp -> sp-16, local[1] = sp-16
  have hle32 : (16 : UInt32) <= sp := UInt32.le_iff_toNat_le.mpr (by simpa using (show 16 ≤ sp.toNat from by omega))
  have hsub32 : (sp - 16).toNat = sp.toNat - 16 := UInt32.toNat_sub_of_le sp 16 hle32
  have h16_1 : 16 <= (sp - 16).toNat := by rw [hsub32]; omega
  have hb1 : (sp - 16).toNat <= 16 * 65536 := by rw [hsub32]; omega
  have hg1 : ({st with globals := {globals := st.globals.globals.set 0 (.i32 (sp - 16))}} : Store Unit).globals.globals[0]? = some (.i32 (sp - 16)) :=
    globals_set0 (sp - 16) hg
  -- call func1(x) -> v1 = f32Trunc x (operationally), global and mem unchanged
  apply wp_call_of_terminates (func1_term env _ (sp - 16) x [] hg1 hp h16_1 hb1)
  rintro st1 vs1 ⟨v1, rfl, hg1', hp1'⟩
  -- compute frac = x - v1, enter 4-level block structure
  wp_run
  apply wp_block_cons; apply wp_block_cons; apply wp_block_cons; apply wp_block_cons
  -- inside innermost block D: comparisons and branching
  wp_run
  -- bounds check for func0's own f32Store/f32Load at (sp-16)+12
  have hnt0 : ¬ ((sp - 16).toNat + 12 + 4 > 16 * 65536) :=
    frame_oob_false (by omega) hb
  -- sp frame restore: const 16 is top, localGet 1 is second, add = 16+(sp-16) = sp
  have hrestored : (sp - 16 : UInt32) + 16 = sp := by apply UInt32.ext; simp
  have hrestored' : 16 + (sp - 16 : UInt32) = sp := by apply UInt32.ext; simp [hsub32]; omega
  -- OOB in the normalized form simp produces: (sp-16).toNat ≤ 1048560
  have hnt0' : (sp - 16).toNat ≤ 1048560 := by have := hnt0; omega
  cases hge : f32Ge (f32Sub x v1) 1056964608
  · -- frac < 0.5: not the ceil branch
    simp [hge]
    cases hle' : f32Le (f32Sub x v1) 3204448256
    · -- frac > -0.5: neutral (B cont: store v1 directly)
      simp
      -- B cont: localGet 1, localGet 2, f32Store 12, br 1
      -- rest_after_A: localGet 1, f32Load 12, localSet 4, localGet 1, const 16, add, globalSet 0, localGet 4, ret
      simp [hp1', hnt0', hg1', hrestored']
      exact globals_set0 sp hg1'
    · -- frac <= -0.5: floor branch (A cont: call func3)
      simp
      -- A cont: localGet 1, localGet 2, call 3
      apply wp_call_of_terminates
        (func3_term env st1 (sp - 16) v1 [.i32 (sp - 16)] hg1' hp1' h16_1 hb1)
      rintro st3 vs3 ⟨v3, rfl, hg3, hp3⟩
      have hnt3' : (sp - 16).toNat ≤ 1048560 := by
        have := frame_oob_false (by omega) hb; omega
      -- A cont after call: f32Store 12, fall through to rest_after_A
      wp_run
      simp [hp3, hnt3', hg3, hrestored']
      exact globals_set0 sp hg3
  · -- frac >= 0.5: ceil branch (C cont: call func2, f32Store 12, br 2)
    simp [hge]
    -- C cont: localGet 1, localGet 2, call 2
    apply wp_call_of_terminates
      (func2_term env st1 (sp - 16) v1 [.i32 (sp - 16)] hg1' hp1' h16_1 hb1)
    rintro st2 vs2 ⟨v2, rfl, hg2, hp2⟩
    have hnt2' : (sp - 16).toNat ≤ 1048560 := by
      have := frame_oob_false (by omega) hb; omega
    -- C cont after call: f32Store 12, br 2, rest_after_A
    wp_run
    simp [hp2, hnt2', hg2, hrestored']
    exact globals_set0 sp hg2

/-! ## FloatRoundSpec -/

@[spec_of "rust-exported" "float_round::check_round"]
def FloatRoundSpec : Prop :=
  ∀ (env : HostEnv Unit) (x : UInt32),
    TerminatesWith env «module» 6 «module».initialStore
      [.f32 x]
      (fun _ rs => ∃ b : UInt32, rs = [.i32 b])

@[proves Project.FloatRound.Spec.FloatRoundSpec]
theorem check_round_terminates : FloatRoundSpec := by
  intro env x
  have hg : («module».initialStore : Store Unit).globals.globals[0]? = some (.i32 1048576) := rfl
  have hp : («module».initialStore : Store Unit).mem.pages = 16 := rfl
  apply TerminatesWith.of_wp_entry_for (f := ⟨[.f32], [.i32, .i32], func6, [.i32], none⟩) rfl
  unfold func6; wp_run; simp only [hg]
  -- frame: sp = 1048576 -> 1048560
  have hg6 : ({«module».initialStore with globals := {globals := «module».initialStore.globals.globals.set 0 (.i32 (1048576 - 16))}} : Store Unit).globals.globals[0]? = some (.i32 (1048576 - 16)) :=
    globals_set0 (1048576 - 16) hg
  apply wp_block_cons; apply wp_block_cons
  wp_run
  -- call func0(x)
  apply wp_call_of_terminates
    (func0_term env _ (1048576 - 16) x hg6 (by rfl) (by decide) (by decide))
  rintro st0 vs0 ⟨v0, rfl, hg0, hp0⟩
  wp_run
  -- call func4(x)
  apply wp_call_of_terminates
    (func4_term env st0 (1048576 - 16) x [.f32 v0] hg0 hp0 (by decide) (by decide))
  rintro st4 vs4 ⟨v4, rfl, hg4, hp4⟩
  -- f32Eq, const 1, and, br_if 0: case split on equality
  wp_run
  -- concrete OOB check: 1048560 + 12 + 4 = 1048576 ≤ 16 * 65536
  have hnt6 : ¬ ((1048576 - 16 : UInt32).toNat + 12 + 4 > 16 * 65536) := by decide
  have hrestored6 : (1048576 - 16 : UInt32) + 16 = 1048576 := by decide
  cases heq : f32Eq v0 v4
  · -- not equal: store32 0 at 1048560+12, br 1
    simp [heq]
    simp [hp4, hg4]
  · -- equal: B cont: store32 1 at 1048560+12
    simp [heq]
    simp [hp4, hg4]

end Project.FloatRound.Spec
