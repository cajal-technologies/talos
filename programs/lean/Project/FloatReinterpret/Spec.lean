import Project.FloatReinterpret.Program

/-!
# Specification for `float_reinterpret`
-/

namespace Project.FloatReinterpret.Spec

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

-- frame at (sp-16)+N stays in bounds given sp >= 16 and sp <= pages*65536
private theorem frame_oob_false {sp : UInt32} {pages : Nat}
    (h16 : 16 <= sp.toNat) (hb : sp.toNat <= pages * 65536) :
    ¬ ((sp - 16).toNat + 12 + 4 > pages * 65536) := by
  have hle : (16 : UInt32) <= sp := UInt32.le_iff_toNat_le.mpr (by simpa using h16)
  have hsub : (sp - 16).toNat = sp.toNat - 16 := UInt32.toNat_sub_of_le sp 16 hle
  rw [hsub]; omega

/-! ## func1: f32Abs via frame -/

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

/-! ## func3: f64Abs via frame -/

private theorem func3_term (env : HostEnv Unit) (st : Store Unit) (sp : UInt32) (x : UInt64)
    (tail : List Value)
    (hg : st.globals.globals[0]? = some (.i32 sp))
    (hp : st.mem.pages = 16) (h16 : 16 <= sp.toNat) (hb : sp.toNat <= 16 * 65536) :
    TerminatesWith env «module» 3 st ([.f64 x] ++ tail)
      (fun st' rs => ∃ v : UInt64, rs = [.f64 v] ++ tail ∧
        st'.globals.globals[0]? = some (.i32 sp) ∧ st'.mem.pages = 16) := by
  apply TerminatesWith.of_wp_entry_for (f := ⟨[.f64], [.i32], func3, [.f64], none⟩) rfl
  unfold func3; wp_run
  simp [hg, hp]
  have hle : (16 : UInt32) ≤ sp := UInt32.le_iff_toNat_le.mpr h16
  have hsub : (sp - 16).toNat = sp.toNat - 16 := UInt32.toNat_sub_of_le sp 16 hle
  omega

/-! ## func5: i32ReinterpretF32 (pure) -/

private theorem func5_term (env : HostEnv Unit) (st : Store Unit) (sp x : UInt32)
    (tail : List Value)
    (hg : st.globals.globals[0]? = some (.i32 sp))
    (hp : st.mem.pages = 16) :
    TerminatesWith env «module» 5 st ([.f32 x] ++ tail)
      (fun st' rs => ∃ v : UInt32, rs = [.i32 v] ++ tail ∧
        st'.globals.globals[0]? = some (.i32 sp) ∧ st'.mem.pages = 16) := by
  apply TerminatesWith.of_wp_entry_for (f := ⟨[.f32], [], func5, [.i32], none⟩) rfl
  unfold func5; wp_run
  exact ⟨x, rfl, hg, hp⟩

/-! ## func6: f32ReinterpretI32 (pure) -/

private theorem func6_term (env : HostEnv Unit) (st : Store Unit) (sp x : UInt32)
    (tail : List Value)
    (hg : st.globals.globals[0]? = some (.i32 sp))
    (hp : st.mem.pages = 16) :
    TerminatesWith env «module» 6 st ([.i32 x] ++ tail)
      (fun st' rs => ∃ v : UInt32, rs = [.f32 v] ++ tail ∧
        st'.globals.globals[0]? = some (.i32 sp) ∧ st'.mem.pages = 16) := by
  apply TerminatesWith.of_wp_entry_for (f := ⟨[.i32], [], func6, [.f32], none⟩) rfl
  unfold func6; wp_run
  exact ⟨x, rfl, hg, hp⟩

/-! ## func0: abs wrapper (calls func1) -/

private theorem func0_term (env : HostEnv Unit) (st : Store Unit) (sp x : UInt32)
    (tail : List Value)
    (hg : st.globals.globals[0]? = some (.i32 sp))
    (hp : st.mem.pages = 16) (h16 : 16 <= sp.toNat) (hb : sp.toNat <= 16 * 65536) :
    TerminatesWith env «module» 0 st ([.f32 x] ++ tail)
      (fun st' rs => ∃ v : UInt32, rs = [.f32 v] ++ tail ∧
        st'.globals.globals[0]? = some (.i32 sp) ∧ st'.mem.pages = 16) := by
  apply TerminatesWith.of_wp_entry_for (f := ⟨[.f32], [], func0, [.f32], none⟩) rfl
  unfold func0; wp_run
  apply wp_call_of_terminates (func1_term env st sp x [] hg hp h16 hb)
  rintro st1 vs1 ⟨v1, rfl, hg1, hp1⟩
  wp_run
  exact ⟨v1, rfl, hg1, hp1⟩

/-! ## func2: f64Abs wrapper via promotion (calls func3) -/

private theorem func2_term (env : HostEnv Unit) (st : Store Unit) (sp x : UInt32)
    (tail : List Value)
    (hg : st.globals.globals[0]? = some (.i32 sp))
    (hp : st.mem.pages = 16) (h16 : 16 <= sp.toNat) (hb : sp.toNat <= 16 * 65536) :
    TerminatesWith env «module» 2 st ([.f32 x] ++ tail)
      (fun st' rs => ∃ v : UInt32, rs = [.f32 v] ++ tail ∧
        st'.globals.globals[0]? = some (.i32 sp) ∧ st'.mem.pages = 16) := by
  apply TerminatesWith.of_wp_entry_for (f := ⟨[.f32], [], func2, [.f32], none⟩) rfl
  unfold func2; wp_run
  apply wp_call_of_terminates (func3_term env st sp (f64PromoteF32 x) [] hg hp h16 hb)
  rintro st3 vs3 ⟨v3, rfl, hg3, hp3⟩
  wp_run
  exact ⟨f32DemoteF64 v3, rfl, hg3, hp3⟩

/-! ## func8: f32Copysign via frame (2 f32 params) -/

private theorem func8_term (env : HostEnv Unit) (st : Store Unit) (sp x y : UInt32)
    (tail : List Value)
    (hg : st.globals.globals[0]? = some (.i32 sp))
    (hp : st.mem.pages = 16) (h16 : 16 <= sp.toNat) (hb : sp.toNat <= 16 * 65536) :
    TerminatesWith env «module» 8 st ([.f32 y, .f32 x] ++ tail)
      (fun st' rs => ∃ v : UInt32, rs = [.f32 v] ++ tail ∧
        st'.globals.globals[0]? = some (.i32 sp) ∧ st'.mem.pages = 16) := by
  apply TerminatesWith.of_wp_entry_for (f := ⟨[.f32, .f32], [.i32], func8, [.f32], none⟩) rfl
  unfold func8; wp_run
  simp [hg, hp]
  have hle : (16 : UInt32) ≤ sp := UInt32.le_iff_toNat_le.mpr h16
  have hsub : (sp - 16).toNat = sp.toNat - 16 := UInt32.toNat_sub_of_le sp 16 hle
  omega

/-! ## func7: copysign wrapper (calls func8, 2 f32 params) -/

private theorem func7_term (env : HostEnv Unit) (st : Store Unit) (sp x y : UInt32)
    (tail : List Value)
    (hg : st.globals.globals[0]? = some (.i32 sp))
    (hp : st.mem.pages = 16) (h16 : 16 <= sp.toNat) (hb : sp.toNat <= 16 * 65536) :
    TerminatesWith env «module» 7 st ([.f32 y, .f32 x] ++ tail)
      (fun st' rs => ∃ v : UInt32, rs = [.f32 v] ++ tail ∧
        st'.globals.globals[0]? = some (.i32 sp) ∧ st'.mem.pages = 16) := by
  apply TerminatesWith.of_wp_entry_for (f := ⟨[.f32, .f32], [], func7, [.f32], none⟩) rfl
  unfold func7; wp_run
  apply wp_call_of_terminates (func8_term env st sp x y [] hg hp h16 hb)
  rintro st8 vs8 ⟨v8, rfl, hg8, hp8⟩
  wp_run
  exact ⟨v8, rfl, hg8, hp8⟩

/-! ## func9: abs via bit manipulation (calls func5, func6) -/

private theorem func9_term (env : HostEnv Unit) (st : Store Unit) (sp x : UInt32)
    (tail : List Value)
    (hg : st.globals.globals[0]? = some (.i32 sp))
    (hp : st.mem.pages = 16) :
    TerminatesWith env «module» 9 st ([.f32 x] ++ tail)
      (fun st' rs => ∃ v : UInt32, rs = [.f32 v] ++ tail ∧
        st'.globals.globals[0]? = some (.i32 sp) ∧ st'.mem.pages = 16) := by
  apply TerminatesWith.of_wp_entry_for (f := ⟨[.f32], [], func9, [.f32], none⟩) rfl
  unfold func9; wp_run
  apply wp_call_of_terminates (func5_term env st sp x [] hg hp)
  rintro st5 vs5 ⟨v5, rfl, hg5, hp5⟩
  wp_run
  apply wp_call_of_terminates (func6_term env st5 sp (2147483647 &&& v5) [] hg5 hp5)
  rintro st6 vs6 ⟨v6, rfl, hg6, hp6⟩
  wp_run
  exact ⟨v6, rfl, hg6, hp6⟩

/-! ## func4: copysign via bit manipulation (calls func5 twice, func6; 2 f32 params) -/

private theorem func4_term (env : HostEnv Unit) (st : Store Unit) (sp x y : UInt32)
    (tail : List Value)
    (hg : st.globals.globals[0]? = some (.i32 sp))
    (hp : st.mem.pages = 16) :
    TerminatesWith env «module» 4 st ([.f32 y, .f32 x] ++ tail)
      (fun st' rs => ∃ v : UInt32, rs = [.f32 v] ++ tail ∧
        st'.globals.globals[0]? = some (.i32 sp) ∧ st'.mem.pages = 16) := by
  apply TerminatesWith.of_wp_entry_for (f := ⟨[.f32, .f32], [], func4, [.f32], none⟩) rfl
  unfold func4; wp_run
  apply wp_call_of_terminates (func5_term env st sp y [] hg hp)
  rintro st5 vs5 ⟨v5, rfl, hg5, hp5⟩
  wp_run
  apply wp_call_of_terminates (func5_term env st5 sp x [.i32 (2147483648 &&& v5)] hg5 hp5)
  rintro st5' vs5' ⟨v5', rfl, hg5', hp5'⟩
  wp_run
  apply wp_call_of_terminates
    (func6_term env st5' sp ((2147483648 &&& v5) ||| (2147483647 &&& v5')) [] hg5' hp5')
  rintro st6 vs6 ⟨v6, rfl, hg6, hp6⟩
  wp_run
  exact ⟨v6, rfl, hg6, hp6⟩

/-! ## FloatReinterpretSpec -/

@[spec_of "rust-exported" "float_reinterpret::float_reinterpret"]
def FloatReinterpretSpec : Prop :=
  (∀ (env : HostEnv Unit) (x : UInt32),
    TerminatesWith env «module» 10 «module».initialStore [.f32 x]
      (fun _ rs => ∃ b : UInt32, rs = [.i32 b])) ∧
  (∀ (env : HostEnv Unit) (x y : UInt32),
    TerminatesWith env «module» 11 «module».initialStore [.f32 y, .f32 x]
      (fun _ rs => ∃ b : UInt32, rs = [.i32 b]))

@[proves Project.FloatReinterpret.Spec.FloatReinterpretSpec]
theorem check_terminates : FloatReinterpretSpec := by
  constructor
  · -- check_abs
    intro env x
    have hg : («module».initialStore : Store Unit).globals.globals[0]? = some (.i32 1048576) := rfl
    have hp : («module».initialStore : Store Unit).mem.pages = 16 := rfl
    apply TerminatesWith.of_wp_entry_for (f := ⟨[.f32], [.i32, .i32], func10, [.i32], none⟩) rfl
    unfold func10; wp_run; simp only [hg]
    have hg10 : ({«module».initialStore with globals := {globals := «module».initialStore.globals.globals.set 0 (.i32 (1048576 - 16))}} : Store Unit).globals.globals[0]? = some (.i32 (1048576 - 16)) :=
      globals_set0 (1048576 - 16) hg
    apply wp_block_cons; apply wp_block_cons
    wp_run
    apply wp_call_of_terminates
      (func0_term env _ (1048576 - 16) x [] hg10 (by rfl) (by decide) (by decide))
    rintro st0 vs0 ⟨v0, rfl, hg0, hp0⟩
    wp_run
    apply wp_call_of_terminates (func9_term env st0 (1048576 - 16) x [.f32 v0] hg0 hp0)
    rintro st9 vs9 ⟨v9, rfl, hg9, hp9⟩
    wp_run
    have hnt : ¬ ((1048576 - 16 : UInt32).toNat + 12 + 4 > 16 * 65536) := by decide
    have hrestored : (1048576 - 16 : UInt32) + 16 = 1048576 := by decide
    cases heq09 : f32Eq v0 v9
    · -- v0 ≠ v9: break inner → outer body: store 0
      simp [heq09]
      simp [hp9, hnt, hg9, hrestored]
    · -- v0 = v9: continue; second comparison
      simp [heq09]
      apply wp_call_of_terminates
        (func0_term env st9 (1048576 - 16) x [] hg9 hp9 (by decide) (by decide))
      rintro st0' vs0' ⟨v0', rfl, hg0', hp0'⟩
      wp_run
      apply wp_call_of_terminates
        (func2_term env st0' (1048576 - 16) x [.f32 v0'] hg0' hp0' (by decide) (by decide))
      rintro st2 vs2 ⟨v2, rfl, hg2, hp2⟩
      wp_run
      cases heq02 : f32Eq v0' v2
      · -- v0' ≠ v2: break inner → outer body: store 0
        simp [heq02]
        simp [hp2, hnt, hg2, hrestored]
      · -- v0' = v2: store 1, break outer
        simp [heq02]
        simp [hp2, hnt, hg2, hrestored]
  · -- check_copysign
    intro env x y
    have hg : («module».initialStore : Store Unit).globals.globals[0]? = some (.i32 1048576) := rfl
    have hp : («module».initialStore : Store Unit).mem.pages = 16 := rfl
    apply TerminatesWith.of_wp_entry_for (f := ⟨[.f32, .f32], [.i32, .i32], func11, [.i32], none⟩) rfl
    unfold func11; wp_run; simp only [hg]
    have hg11 : ({«module».initialStore with globals := {globals := «module».initialStore.globals.globals.set 0 (.i32 (1048576 - 16))}} : Store Unit).globals.globals[0]? = some (.i32 (1048576 - 16)) :=
      globals_set0 (1048576 - 16) hg
    apply wp_block_cons; apply wp_block_cons
    wp_run
    apply wp_call_of_terminates
      (func7_term env _ (1048576 - 16) x y [] hg11 (by rfl) (by decide) (by decide))
    rintro st7 vs7 ⟨v7, rfl, hg7, hp7⟩
    wp_run
    apply wp_call_of_terminates (func4_term env st7 (1048576 - 16) x y [.f32 v7] hg7 hp7)
    rintro st4 vs4 ⟨v4, rfl, hg4, hp4⟩
    wp_run
    have hnt : ¬ ((1048576 - 16 : UInt32).toNat + 12 + 4 > 16 * 65536) := by decide
    have hrestored : (1048576 - 16 : UInt32) + 16 = 1048576 := by decide
    cases heq : f32Eq v7 v4
    · -- v7 ≠ v4: store 0, break outer
      simp [heq]
      simp [hrestored]
    · -- v7 = v4: break inner → outer body: store 1
      simp [heq]
      simp [hrestored]

end Project.FloatReinterpret.Spec
