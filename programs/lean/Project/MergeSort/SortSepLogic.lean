import Project.MergeSort.MergeFull
import Project.MergeSort.Leaves
import Project.MergeSort.ContentLemmas
import Project.MergeSort.Spec
import CodeLib.SepLogic.Adequacy
import CodeLib.SepLogic.AllocSpec
import CodeLib.Entry
import Interpreter.Wasm.Wp.Tactic
import Interpreter.Wasm.Wp.Call
import Interpreter.Wasm.Wp.Block

namespace Wasm.SepLogic.MergeSort

open Wasm Wasm.SepLogic Project.MergeSort Project.MergeSort.Spec Project.MergeSort.Framing

variable [WasmHeapGS]

/-
call graph (imports = [], .call N = funcN):
  func33 (export "merge_sort", params: i32 i32) →
    func15 (slice-header init, straight-line) →
    func1  (sort with pre-allocated scratch) →
      func2  → func20 (vec init, allocator deferred)
      func0  (field copy, straight-line)
      func3  (recursive sort) →
        func5  (split_at_mut, func5_tw exists in Leaves.lean)
        func3  (left half, recursive)
        func3  (right half, recursive)
        func6  (merge, func6_terminates exists in MergeFull.lean)
        func7  → func13 (copy-back, func7_tw exists in Leaves.lean)
      func4  → func8, func9 (dealloc, allocator deferred)
-/

local macro "mstep" : tactic => `(tactic|
  simp only [wp_simp, Locals.get, Locals.set?, Locals.validIndex, Function.toLocals,
    Function.numParams, Function.numLocals, List.take, List.drop, List.replicate,
    List.length, List.map, ValueType.zero, List.headD,
    List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    List.append_assoc, List.set_cons_zero, List.set_cons_succ, List.set_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte])

-- env-independence: run on an import-free module does not use the host environment
private theorem TerminatesWith.env_lift {env : HostEnv Unit} {id : Nat}
    {st : Store Unit} {args : List Value} {P : Store Unit → List Value → Prop}
    (h : TerminatesWith {} «module» id st args P) :
    TerminatesWith env «module» id st args P := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun fuel hle => ?_⟩
  obtain ⟨vs, st', hrun, hpost⟩ := hN fuel hle
  exact ⟨vs, st',
    (run_env_indep «module» (by native_decide) fuel id st args env {}).trans hrun,
    hpost⟩

-- func15: straight-line, stores v1 at ptr, v2 at ptr+4; structural postcondition
omit [WasmHeapGS] in
private theorem func15_terminates
    (st : Store Unit) (ptr v1 v2 v3 : UInt32)
    (hb : ptr.toNat + 8 ≤ st.mem.pages * 65536) :
    TerminatesWith {} «module» 15 st
      [.i32 v3, .i32 v2, .i32 v1, .i32 ptr]
      (fun st' vs =>
        vs = [] ∧
        st'.mem = (st.mem.write32 (ptr + 4) v2).write32 ptr v1 ∧
        st'.globals = st.globals) := by
  have hb4 : ¬(ptr.toNat + (4 : UInt32).toNat + 4 > st.mem.pages * 65536) := by
    have : (4 : UInt32).toNat = 4 := rfl; omega
  have hb0 : ¬(ptr.toNat + (0 : UInt32).toNat + 4 > st.mem.pages * 65536) := by
    have : (0 : UInt32).toNat = 0 := rfl; omega
  have hz : ptr + (0 : UInt32) = ptr := UInt32.add_zero ptr
  apply TerminatesWith.of_run 1 []
      { st with mem := (st.mem.write32 (ptr + 4) v2).write32 ptr v1 }
  · rw [run_eq (show «module».imports[15]? = none from rfl)]
    conv_lhs =>
      simp only [
        show «module».funcs[15 - «module».imports.length]? = some func15Def from rfl,
        func15Def, func15,
        Function.numParams, Function.toLocals, List.map,
        List.take, List.reverse, List.reverseAux, List.drop,
        List.length_cons, List.length_nil,
        exec, execOne.eq_def,
        Locals.get,
        show (0 : Nat) < 4 from by omega,
        show (1 : Nat) < 4 from by omega,
        show (2 : Nat) < 4 from by omega,
        List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
        Mem.write32_pages,
        if_neg hb4, if_neg hb0, hz,
        ite_true, ite_false,
        List.nil_append]
  · exact ⟨rfl, rfl, rfl⟩

-- func6 with framing: bytes outside the output region are unchanged.
set_option maxHeartbeats 4000000 in
private theorem func6_terminates_frame
    (st : Store Unit) (left_ptr n_left right_ptr n_right out_ptr n_out sp : UInt32)
    (hsp    : st.globals.globals[0]? = some (.i32 sp))
    (hsp_lo : 32 ≤ sp.toNat)
    (hsp_hi : sp.toNat ≤ st.mem.pages * 65536)
    (hcap   : n_left.toNat + n_right.toNat ≤ n_out.toNat)
    (hL_bnd : left_ptr.toNat  + 4 * n_left.toNat  ≤ st.mem.pages * 65536)
    (hR_bnd : right_ptr.toNat + 4 * n_right.toNat ≤ st.mem.pages * 65536)
    (hO_bnd : out_ptr.toNat   + 4 * n_out.toNat   ≤ st.mem.pages * 65536)
    (hpages : st.mem.pages * 65536 ≤ 4294967296)
    (hLR_dj : left_ptr.toNat  + 4 * n_left.toNat  ≤ right_ptr.toNat ∨
              right_ptr.toNat + 4 * n_right.toNat ≤ left_ptr.toNat)
    (hLO_dj : left_ptr.toNat  + 4 * n_left.toNat  ≤ out_ptr.toNat ∨
              out_ptr.toNat   + 4 * n_out.toNat   ≤ left_ptr.toNat)
    (hRO_dj : right_ptr.toNat + 4 * n_right.toNat ≤ out_ptr.toNat ∨
              out_ptr.toNat   + 4 * n_out.toNat   ≤ right_ptr.toNat)
    (hFL_dj : (sp - 32).toNat + 32 ≤ left_ptr.toNat ∨
              left_ptr.toNat  + 4 * n_left.toNat  ≤ (sp - 32).toNat)
    (hFR_dj : (sp - 32).toNat + 32 ≤ right_ptr.toNat ∨
              right_ptr.toNat + 4 * n_right.toNat ≤ (sp - 32).toNat)
    (hFO_dj : (sp - 32).toNat + 32 ≤ out_ptr.toNat ∨
              out_ptr.toNat   + 4 * n_out.toNat   ≤ (sp - 32).toNat) :
    TerminatesWith {} «module» 6 st
      [.i32 n_out, .i32 out_ptr, .i32 n_right, .i32 right_ptr, .i32 n_left, .i32 left_ptr]
      (fun st' _ =>
        wordsAt st'.mem out_ptr (n_left.toNat + n_right.toNat) =
          List.merge
            (wordsAt st.mem left_ptr n_left.toNat)
            (wordsAt st.mem right_ptr n_right.toNat)
            (· ≤ ·) ∧
        st'.globals = st.globals ∧
        st'.mem.pages = st.mem.pages ∧
        ∀ i, sp.toNat ≤ i → (i < out_ptr.toNat ∨ i ≥ out_ptr.toNat + 4 * n_out.toNat) →
             st'.mem.bytes i = st.mem.bytes i) := by
  apply wp_wasm_prop_to_TerminatesWith (f := func6Def)
  · rfl
  · rfl
  · rfl
  · simp [Function.numParams, func6Def]
  · intro _ _ h; exact h
  let frame   : UInt32  := sp - 32
  let loc_init : Locals :=
    func6Def.toLocals ([.i32 n_out, .i32 out_ptr, .i32 n_right, .i32 right_ptr,
                         .i32 n_left, .i32 left_ptr].take 6).reverse
  let loc₁    : Locals  :=
    { loc_init with locals := loc_init.locals.set 0 (.i32 frame) }
  let st₁     : Store Unit :=
    { st with
      globals := { st.globals with globals := st.globals.globals.set 0 (.i32 frame) }
      mem     := st.mem
                  |>.write32 (frame + 20) 0 |>.write32 (frame + 24) 0
                  |>.write32 (frame + 28) 0 |>.write32 (frame + 8)  0
                  |>.write32 (frame + 12) 0 |>.write32 (frame + 16) 0 }
  have h_main : wp_wasm_prop «module» st₁ loc₁ (func6.drop 27) {}
      (fun st' _ =>
        wordsAt st'.mem out_ptr (n_left.toNat + n_right.toNat) =
          List.merge
            (wordsAt st.mem left_ptr n_left.toNat)
            (wordsAt st.mem right_ptr n_right.toNat)
            (· ≤ ·) ∧
        st'.globals = st.globals ∧
        st'.mem.pages = st.mem.pages ∧
        ∀ i, sp.toNat ≤ i → (i < out_ptr.toNat ∨ i ≥ out_ptr.toNat + 4 * n_out.toNat) →
             st'.mem.bytes i = st.mem.bytes i) := by
    have hle32 : (32 : UInt32) ≤ sp :=
      UInt32.le_iff_toNat_le.mpr (by simpa using hsp_lo)
    have hfr_toNat : (sp - 32 : UInt32).toNat = frame.toNat := rfl
    have hfr : frame.toNat = sp.toNat - 32 :=
      UInt32.toNat_sub_of_le sp 32 hle32
    have hof8  : (frame + 8).toNat  = frame.toNat + 8  := by
      have h : (8  : UInt32).toNat = 8  := rfl; rw [UInt32.toNat_add, h]; omega
    have hof12 : (frame + 12).toNat = frame.toNat + 12 := by
      have h : (12 : UInt32).toNat = 12 := rfl; rw [UInt32.toNat_add, h]; omega
    have hof16 : (frame + 16).toNat = frame.toNat + 16 := by
      have h : (16 : UInt32).toNat = 16 := rfl; rw [UInt32.toNat_add, h]; omega
    have hof20 : (frame + 20).toNat = frame.toNat + 20 := by
      have h : (20 : UInt32).toNat = 20 := rfl; rw [UInt32.toNat_add, h]; omega
    have hof24 : (frame + 24).toNat = frame.toNat + 24 := by
      have h : (24 : UInt32).toNat = 24 := rfl; rw [UInt32.toNat_add, h]; omega
    have hof28 : (frame + 28).toNat = frame.toNat + 28 := by
      have h : (28 : UInt32).toNat = 28 := rfl; rw [UInt32.toNat_add, h]; omega
    have hst1_mem_eq : st₁.mem =
        (st.mem |>.write32 (frame + 20) 0 |>.write32 (frame + 24) 0
                |>.write32 (frame + 28) 0 |>.write32 (frame + 8)  0
                |>.write32 (frame + 12) 0 |>.write32 (frame + 16) 0) := rfl
    have hst1_globals_eq : st₁.globals.globals = st.globals.globals.set 0 (.i32 frame) := rfl
    have hst1_pages : st₁.mem.pages = st.mem.pages := by
      rw [hst1_mem_eq]; simp [Mem.write32_pages]
    have hst1_f16 : st₁.mem.read32 (frame + 16) = 0 := by
      rw [hst1_mem_eq, Mem.read32_write32_same]
    have hst1_f12 : st₁.mem.read32 (frame + 12) = 0 := by
      rw [hst1_mem_eq]
      rw [Mem.read32_write32_of_disjoint _ _ _ _ (Or.inr (by rw [hof12, hof16])),
          Mem.read32_write32_same]
    have hst1_f8 : st₁.mem.read32 (frame + 8) = 0 := by
      rw [hst1_mem_eq]
      rw [Mem.read32_write32_of_disjoint _ _ _ _ (Or.inr (by rw [hof8, hof16]; omega)),
          Mem.read32_write32_of_disjoint _ _ _ _ (Or.inr (by rw [hof8, hof12])),
          Mem.read32_write32_same]
    have hlp : loc_init.params.length = 6 := rfl
    have hll : loc_init.locals.length = 16 := by
      show (func6Def.locals.map ValueType.zero).length = 16; native_decide
    have hloc1_locals_len : loc₁.locals.length = 16 := by
      simp only [loc₁, List.length_set, hll]
    have hloc1_get0 : loc₁.get 0 = some (.i32 left_ptr)  := rfl
    have hloc1_get1 : loc₁.get 1 = some (.i32 n_left)    := rfl
    have hloc1_get2 : loc₁.get 2 = some (.i32 right_ptr) := rfl
    have hloc1_get3 : loc₁.get 3 = some (.i32 n_right)   := rfl
    have hloc1_get4 : loc₁.get 4 = some (.i32 out_ptr)   := rfl
    have hloc1_get5 : loc₁.get 5 = some (.i32 n_out)     := rfl
    have hloc1_get6 : loc₁.get 6 = some (.i32 frame) := by
      have hlocals_init : loc_init.locals =
          [.i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0,
           .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0] := by
        show func6Def.locals.map ValueType.zero =
          [.i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0,
           .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0]
        native_decide
      have hloc1_locals_eq : loc₁.locals = loc_init.locals.set 0 (.i32 frame) := rfl
      simp only [Locals.get, show loc₁.params.length = 6 from rfl,
                 show ¬((6 : Nat) < 6) from by omega,
                 hloc1_locals_len,
                 show (6 : Nat) < 6 + 16 from by omega,
                 show (6 - 6 : Nat) = 0 from by omega]
      rw [hloc1_locals_eq, hlocals_init]
      rfl
    have hst1_global : ∃ v, st₁.globals.globals[0]? = some v :=
      ⟨.i32 frame, by
        obtain ⟨_, rest, heq⟩ : ∃ v rest, st.globals.globals = v :: rest := by
          cases hg : st.globals.globals with
          | nil => simp [hg] at hsp
          | cons a a_tl => exact ⟨a, a_tl, rfl⟩
        rw [hst1_globals_eq, heq, List.set_cons_zero, List.getElem?_cons_zero]⟩
    have hframe_range : ∀ a,
        a ∈ ([frame+8, frame+12, frame+16, frame+20, frame+24, frame+28] : List UInt32) →
        frame.toNat + 8 ≤ a.toNat ∧ a.toNat + 4 ≤ frame.toNat + 32 := by
      intro a ha
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [hof8, hof12, hof16, hof20, hof24, hof28] <;> omega
    have hmem_writes_disj : ∀ (ptr : UInt32) (n : Nat),
        ptr.toNat + 4 * n ≤ 4294967296 →
        (∀ a, a ∈ ([frame+8, frame+12, frame+16, frame+20, frame+24, frame+28] : List UInt32) →
          a.toNat + 4 ≤ ptr.toNat ∨ ptr.toNat + 4 * n ≤ a.toNat) →
        wordsAt st₁.mem ptr n = wordsAt st.mem ptr n := by
      intro ptr n hub hd
      rw [hst1_mem_eq]
      rw [wordsAt_write32_of_disjoint _ _ (frame+16) 0 _ hub (hd (frame+16) (by simp)),
          wordsAt_write32_of_disjoint _ _ (frame+12) 0 _ hub (hd (frame+12) (by simp)),
          wordsAt_write32_of_disjoint _ _ (frame+8)  0 _ hub (hd (frame+8)  (by simp)),
          wordsAt_write32_of_disjoint _ _ (frame+28) 0 _ hub (hd (frame+28) (by simp)),
          wordsAt_write32_of_disjoint _ _ (frame+24) 0 _ hub (hd (frame+24) (by simp)),
          wordsAt_write32_of_disjoint _ _ (frame+20) 0 _ hub (hd (frame+20) (by simp))]
    have hmem_left_eq : wordsAt st₁.mem left_ptr n_left.toNat =
        wordsAt st.mem left_ptr n_left.toNat :=
      hmem_writes_disj left_ptr n_left.toNat (by linarith) (fun a ha => by
        obtain ⟨ha1, ha2⟩ := hframe_range a ha
        rcases hFL_dj with h | h <;> [left; right] <;> (rw [← hfr_toNat] at h; omega))
    have hmem_right_eq : wordsAt st₁.mem right_ptr n_right.toNat =
        wordsAt st.mem right_ptr n_right.toNat :=
      hmem_writes_disj right_ptr n_right.toNat (by linarith) (fun a ha => by
        obtain ⟨ha1, ha2⟩ := hframe_range a ha
        rcases hFR_dj with h | h <;> [left; right] <;> (rw [← hfr_toNat] at h; omega))
    have hI₀ : MergeLoopInv frame out_ptr left_ptr right_ptr n_left n_right n_out
        0 0 0 st₁ st₁ loc₁ :=
      ⟨0, 0,
       Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _,
       hst1_f8, hst1_f12, hst1_f16,
       hloc1_get6, hloc1_get0, hloc1_get1, hloc1_get2, hloc1_get3, hloc1_get4, hloc1_get5,
       hlp, hloc1_locals_len,
       hst1_global,
       fun _ _ => rfl,
       fun _ _ => rfl,
       by simp [wordsAt, mul_zero, add_zero, List.drop_zero],
       by rw [hst1_pages]; omega,
       by omega,
       by rw [hst1_pages]; exact hL_bnd,
       by rw [hst1_pages]; exact hR_bnd,
       by rw [hst1_pages]; exact hO_bnd,
       by rw [hst1_pages]; exact hpages,
       hLO_dj, hRO_dj, hLR_dj,
       by rcases hFL_dj with h | h <;> [left; right] <;> (rw [← hfr_toNat] at h; omega),
       by rcases hFR_dj with h | h <;> [left; right] <;> (rw [← hfr_toNat] at h; omega),
       by rcases hFO_dj with h | h <;> [left; right] <;> (rw [← hfr_toNat] at h; omega)⟩
    obtain ⟨N_merge, st₂, loc₂, h_step, h_exit, hI₂, hglob2, hfrm2, hpages2⟩ :=
      func6_after_merge_block st₁ loc₁ frame out_ptr left_ptr right_ptr n_left n_right n_out hI₀
    obtain ⟨N_drain, stF, h_drain, h_content, hglobF, hpagesF, hfrmF⟩ :=
      outer_drain_terminates_gp st₁ st₂ loc₂ frame out_ptr left_ptr right_ptr n_left n_right n_out hI₂ h_exit
    rw [hmem_left_eq, hmem_right_eq] at h_content
    have hone_drain : execOne N_drain «module» st₂ loc₂ (.loop 0 0 outerDrainBody) {} =
        .Return stF loc₂.values := by
      suffices key : ∀ (m : Module) (env : HostEnv Unit),
          exec N_drain m st₂ loc₂ [.loop 0 0 outerDrainBody] env = .Return stF loc₂.values →
          execOne N_drain m st₂ loc₂ (.loop 0 0 outerDrainBody) env = .Return stF loc₂.values from
        key «module» {} h_drain
      intro m env h
      simp only [exec] at h
      cases hx : execOne N_drain m st₂ loc₂ (.loop 0 0 outerDrainBody) env with
      | Fallthrough s l => simp only [hx, exec] at h; exact h
      | Return s v => simp only [hx] at h; exact h
      | OutOfFuel => simp only [hx] at h; exact h
      | Break => simp only [hx] at h; exact h
      | ReturnCall => simp only [hx] at h; exact h
      | Invalid => simp only [hx] at h; exact h
      | Trap => simp only [hx] at h; exact h
      | Throwing => simp only [hx] at h; exact h
    have h_drain28 : exec N_drain «module» st₂ loc₂ (func6.drop 28) {} =
        .Return stF loc₂.values := by
      rw [func6_drop28_eq]; simp only [exec, hone_drain]
    let F := max N_merge N_drain
    have h_drain28_F : exec F «module» st₂ loc₂ (func6.drop 28) {} = .Return stF loc₂.values := by
      have hne : exec N_drain «module» st₂ loc₂ (func6.drop 28) {} ≠ .OutOfFuel := by
        rw [h_drain28]; intro h; cases h
      exact (exec_fuel_mono (Nat.le_max_right N_merge N_drain) hne).trans h_drain28
    have h_main_F : exec F «module» st₁ loc₁ (func6.drop 27) {} = .Return stF loc₂.values := by
      rw [h_step F (Nat.le_max_left N_merge N_drain)]; exact h_drain28_F
    have hframe32 : (32 : UInt32) + frame = sp := by
      apply UInt32.toNat.inj
      have hsp_lt := sp.toNat_lt
      rw [UInt32.toNat_add, show (32 : UInt32).toNat = 32 from rfl, hfr]; omega
    have hg2 : st₂.globals.globals = st₁.globals.globals :=
      congrArg Globals.globals hglob2
    have hglob_stF : stF.globals = st.globals := by
      have heq : stF.globals.globals = st.globals.globals := by
        cases hg : st.globals.globals with
        | nil => simp [hg] at hsp
        | cons hd tl =>
          obtain rfl : hd = .i32 sp := by simpa [hg] using hsp
          rw [hglobF, hg2, hst1_globals_eq, hg, hframe32,
              List.set_cons_zero, List.set_cons_zero]
      exact congrArg Globals.mk heq
    have hpages_stF : stF.mem.pages = st.mem.pages := by
      rw [hpagesF, hpages2, hst1_pages]
    have hpreamble_frm : ∀ i, sp.toNat ≤ i → st₁.mem.bytes i = st.mem.bytes i := by
      intro i hi
      have hspf : frame.toNat + 32 ≤ i := by rw [hfr]; omega
      rw [hst1_mem_eq]
      rw [Mem.write32_bytes_of_disjoint _ _ _ _ (Or.inr (by rw [hof16]; omega))]
      rw [Mem.write32_bytes_of_disjoint _ _ _ _ (Or.inr (by rw [hof12]; omega))]
      rw [Mem.write32_bytes_of_disjoint _ _ _ _ (Or.inr (by rw [hof8];  omega))]
      rw [Mem.write32_bytes_of_disjoint _ _ _ _ (Or.inr (by rw [hof28]; omega))]
      rw [Mem.write32_bytes_of_disjoint _ _ _ _ (Or.inr (by rw [hof24]; omega))]
      rw [Mem.write32_bytes_of_disjoint _ _ _ _ (Or.inr (by rw [hof20]; omega))]
    have hfrm_stF : ∀ i, sp.toNat ≤ i →
        (i < out_ptr.toNat ∨ i ≥ out_ptr.toNat + 4 * n_out.toNat) →
        stF.mem.bytes i = st.mem.bytes i := by
      intro i hi hout_i
      have hspf : frame.toNat + 32 ≤ i := by rw [hfr]; omega
      rw [hfrmF i hspf hout_i, hfrm2 i hspf hout_i, hpreamble_frm i hi]
    exact ⟨F, by simp only [h_main_F]; exact ⟨h_content, hglob_stF, hpages_stF, hfrm_stF⟩⟩
  obtain ⟨N, hN⟩ := h_main
  have h_setup : exec (N + 27) «module» st
      (func6Def.toLocals (List.take func6Def.numParams
          [.i32 n_out, .i32 out_ptr, .i32 n_right, .i32 right_ptr,
           .i32 n_left, .i32 left_ptr]).reverse)
      func6Def.body {} =
      exec N «module» st₁ loc₁ (func6.drop 27) {} := by
    have hle32 : (32 : UInt32) ≤ sp :=
      UInt32.le_iff_toNat_le.mpr (by simpa using hsp_lo)
    have hfr : frame.toNat = sp.toNat - 32 :=
      UInt32.toNat_sub_of_le sp 32 hle32
    have haddr8  : (frame + 8).toNat  = frame.toNat + 8  := by
      have h : (8  : UInt32).toNat = 8  := rfl
      rw [UInt32.toNat_add, h]; omega
    have haddr12 : (frame + 12).toNat = frame.toNat + 12 := by
      have h : (12 : UInt32).toNat = 12 := rfl
      rw [UInt32.toNat_add, h]; omega
    have haddr16 : (frame + 16).toNat = frame.toNat + 16 := by
      have h : (16 : UInt32).toNat = 16 := rfl
      rw [UInt32.toNat_add, h]; omega
    have haddr20 : (frame + 20).toNat = frame.toNat + 20 := by
      have h : (20 : UInt32).toNat = 20 := rfl
      rw [UInt32.toNat_add, h]; omega
    have haddr24 : (frame + 24).toNat = frame.toNat + 24 := by
      have h : (24 : UInt32).toNat = 24 := rfl
      rw [UInt32.toNat_add, h]; omega
    have haddr28 : (frame + 28).toNat = frame.toNat + 28 := by
      have h : (28 : UInt32).toNat = 28 := rfl
      rw [UInt32.toNat_add, h]; omega
    have hfr_toNat : (sp - 32 : UInt32).toNat = frame.toNat := rfl
    have hb8  : ¬((sp - 32 : UInt32).toNat + (8  : UInt32).toNat + 4 > st.mem.pages * 65536) := by
      have : (8  : UInt32).toNat = 8  := rfl; omega
    have hb12 : ¬((sp - 32 : UInt32).toNat + (12 : UInt32).toNat + 4 > st.mem.pages * 65536) := by
      have : (12 : UInt32).toNat = 12 := rfl; omega
    have hb16 : ¬((sp - 32 : UInt32).toNat + (16 : UInt32).toNat + 4 > st.mem.pages * 65536) := by
      have : (16 : UInt32).toNat = 16 := rfl; omega
    have hb20 : ¬((sp - 32 : UInt32).toNat + (20 : UInt32).toNat + 4 > st.mem.pages * 65536) := by
      have : (20 : UInt32).toNat = 20 := rfl; omega
    have hb24 : ¬((sp - 32 : UInt32).toNat + (24 : UInt32).toNat + 4 > st.mem.pages * 65536) := by
      have : (24 : UInt32).toNat = 24 := rfl; omega
    have hb28 : ¬((sp - 32 : UInt32).toNat + (28 : UInt32).toNat + 4 > st.mem.pages * 65536) := by
      have : (28 : UInt32).toNat = 28 := rfl; omega
    have hrd20 : (st.mem.write32 (sp - 32 + 20) 0 |>.write32 (sp - 32 + 24) 0
        |>.write32 (sp - 32 + 28) 0).read32 (sp - 32 + 20) = 0 := by
      rw [Mem.read32_write32_of_disjoint _ _ _ _ (Or.inr (by
            have h1 : (sp - 32 + 20 : UInt32).toNat = frame.toNat + 20 := haddr20
            have h2 : (sp - 32 + 28 : UInt32).toNat = frame.toNat + 28 := haddr28
            omega)),
          Mem.read32_write32_of_disjoint _ _ _ _ (Or.inr (by
            have h1 : (sp - 32 + 20 : UInt32).toNat = frame.toNat + 20 := haddr20
            have h2 : (sp - 32 + 24 : UInt32).toNat = frame.toNat + 24 := haddr24
            omega)),
          Mem.read32_write32_same]
    have hrd24 : (st.mem.write32 (sp - 32 + 20) 0 |>.write32 (sp - 32 + 24) 0
        |>.write32 (sp - 32 + 28) 0 |>.write32 (sp - 32 + 8) 0).read32 (sp - 32 + 24) = 0 := by
      rw [Mem.read32_write32_of_disjoint _ _ _ _ (Or.inl (by
            have h1 : (sp - 32 + 8  : UInt32).toNat = frame.toNat + 8  := haddr8
            have h2 : (sp - 32 + 24 : UInt32).toNat = frame.toNat + 24 := haddr24
            omega)),
          Mem.read32_write32_of_disjoint _ _ _ _ (Or.inr (by
            have h1 : (sp - 32 + 24 : UInt32).toNat = frame.toNat + 24 := haddr24
            have h2 : (sp - 32 + 28 : UInt32).toNat = frame.toNat + 28 := haddr28
            omega)),
          Mem.read32_write32_same]
    have hrd28 : (st.mem.write32 (sp - 32 + 20) 0 |>.write32 (sp - 32 + 24) 0
        |>.write32 (sp - 32 + 28) 0 |>.write32 (sp - 32 + 8) 0
        |>.write32 (sp - 32 + 12) 0).read32 (sp - 32 + 28) = 0 := by
      rw [Mem.read32_write32_of_disjoint _ _ _ _ (Or.inl (by
            have h1 : (sp - 32 + 12 : UInt32).toNat = frame.toNat + 12 := haddr12
            have h2 : (sp - 32 + 28 : UInt32).toNat = frame.toNat + 28 := haddr28
            omega)),
          Mem.read32_write32_of_disjoint _ _ _ _ (Or.inl (by
            have h1 : (sp - 32 + 8  : UInt32).toNat = frame.toNat + 8  := haddr8
            have h2 : (sp - 32 + 28 : UInt32).toNat = frame.toNat + 28 := haddr28
            omega)),
          Mem.read32_write32_same]
    have hlp : loc_init.params.length = 6 := rfl
    have hll : loc_init.locals.length = 16 := by
      show (func6Def.locals.map ValueType.zero).length = 16; native_decide
    have hlocals_init : loc_init.locals =
        [.i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0,
         .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0] := by
      show func6Def.locals.map ValueType.zero =
        [.i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0,
         .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0]
      native_decide
    have hN_ne : exec N «module» st₁ loc₁ (func6.drop 27) {} ≠ .OutOfFuel := by
      intro heq; simp [heq] at hN
    suffices h_eq : exec (N + 27) «module» st loc_init func6 {} =
        exec (N + 27) «module» st₁ loc₁ (func6.drop 27) {} by
      exact h_eq.trans (exec_fuel_mono (Nat.le_add_right N 27) hN_ne)
    rw [← List.take_append_drop 27 func6,
        show func6.take 27 = [
            .globalGet 0, .const (32 : UInt32), .sub, .localSet 6,
            .localGet 6, .globalSet 0,
            .localGet 6, .const (0 : UInt32), .store32 (20 : UInt32),
            .localGet 6, .const (0 : UInt32), .store32 (24 : UInt32),
            .localGet 6, .const (0 : UInt32), .store32 (28 : UInt32),
            .localGet 6, .localGet 6, .load32 (20 : UInt32), .store32 (8  : UInt32),
            .localGet 6, .localGet 6, .load32 (24 : UInt32), .store32 (12 : UInt32),
            .localGet 6, .localGet 6, .load32 (28 : UInt32), .store32 (16 : UInt32)
          ] from rfl]
    conv_lhs =>
      simp only [List.cons_append, List.nil_append,
                 exec, execOne.eq_def,
                 hsp, hrd20, hrd24, hrd28,
                 hlocals_init, hlp, hll,
                 Locals.get, Locals.set?,
                 List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
                 List.set_cons_zero, List.set_cons_succ,
                 List.length_cons, List.length_nil, List.length_set,
                 Mem.read32_write32_same, Mem.write32_pages,
                 if_neg hb8, if_neg hb12, if_neg hb16,
                 if_neg hb20, if_neg hb24, if_neg hb28,
                 show ¬ ((6 : Nat) < 6) from by omega,
                 show (6 : Nat) < 6 + 16 from by omega,
                 show (6 - 6 : Nat) = 0 from by omega,
                 ite_true, ite_false]
    rfl
  exact ⟨N + 27, by rw [h_setup]; exact hN⟩

-- func6 with combined postcondition (globals + pages): derived from
-- func6_terminates_frame by weakening (drop vs=[] and the framing conjunct).
private theorem func6_terminates_aux
    (st : Store Unit) (left_ptr n_left right_ptr n_right out_ptr n_out sp : UInt32)
    (hsp    : st.globals.globals[0]? = some (.i32 sp))
    (hsp_lo : 32 ≤ sp.toNat)
    (hsp_hi : sp.toNat ≤ st.mem.pages * 65536)
    (hcap   : n_left.toNat + n_right.toNat ≤ n_out.toNat)
    (hL_bnd : left_ptr.toNat  + 4 * n_left.toNat  ≤ st.mem.pages * 65536)
    (hR_bnd : right_ptr.toNat + 4 * n_right.toNat ≤ st.mem.pages * 65536)
    (hO_bnd : out_ptr.toNat   + 4 * n_out.toNat   ≤ st.mem.pages * 65536)
    (hpages : st.mem.pages * 65536 ≤ 4294967296)
    (hLR_dj : left_ptr.toNat  + 4 * n_left.toNat  ≤ right_ptr.toNat ∨
              right_ptr.toNat + 4 * n_right.toNat ≤ left_ptr.toNat)
    (hLO_dj : left_ptr.toNat  + 4 * n_left.toNat  ≤ out_ptr.toNat ∨
              out_ptr.toNat   + 4 * n_out.toNat   ≤ left_ptr.toNat)
    (hRO_dj : right_ptr.toNat + 4 * n_right.toNat ≤ out_ptr.toNat ∨
              out_ptr.toNat   + 4 * n_out.toNat   ≤ right_ptr.toNat)
    (hFL_dj : (sp - 32).toNat + 32 ≤ left_ptr.toNat ∨
              left_ptr.toNat  + 4 * n_left.toNat  ≤ (sp - 32).toNat)
    (hFR_dj : (sp - 32).toNat + 32 ≤ right_ptr.toNat ∨
              right_ptr.toNat + 4 * n_right.toNat ≤ (sp - 32).toNat)
    (hFO_dj : (sp - 32).toNat + 32 ≤ out_ptr.toNat ∨
              out_ptr.toNat   + 4 * n_out.toNat   ≤ (sp - 32).toNat) :
    TerminatesWith {} «module» 6 st
      [.i32 n_out, .i32 out_ptr, .i32 n_right, .i32 right_ptr, .i32 n_left, .i32 left_ptr]
      (fun st' _ =>
        wordsAt st'.mem out_ptr (n_left.toNat + n_right.toNat) =
          List.merge
            (wordsAt st.mem left_ptr n_left.toNat)
            (wordsAt st.mem right_ptr n_right.toNat)
            (· ≤ ·) ∧
        st'.globals = st.globals ∧
        st'.mem.pages = st.mem.pages) :=
  (func6_terminates_frame st left_ptr n_left right_ptr n_right out_ptr n_out sp
      hsp hsp_lo hsp_hi hcap hL_bnd hR_bnd hO_bnd hpages
      hLR_dj hLO_dj hRO_dj hFL_dj hFR_dj hFO_dj).mono
    fun st' _ h => ⟨h.1, h.2.1, h.2.2.1⟩

-- Stronger func5 postcondition: byte-level memory content at the output region
-- plus byte-level framing for addresses ≥ sp outside [out, out+16).
-- Derived by WP execution of func5: func14 writes (ptr,mid,ptr+mid<<<2,len-mid)
-- into the frame at [frame+16,frame+32), then four store64 instructions copy
-- them (via the frame shadow stack) to [out,out+16).
set_option maxRecDepth 8192 in
private theorem func5_content_frame_tw
    (st : Store Unit) (out ptr len mid pl sp : UInt32)
    (hsp : st.globals.globals[0]? = some (.i32 sp))
    (hsplit : mid.toNat ≤ len.toNat)
    (hlo : 32 ≤ sp.toNat) (hhi : sp.toNat ≤ st.mem.pages * 65536)
    (hout : out.toNat + 16 ≤ st.mem.pages * 65536)
    (hpages : st.mem.pages * 65536 ≤ 4294967296)
    (hout_lo : sp.toNat ≤ out.toNat) :
    TerminatesWith {} «module» 5 st
      [.i32 pl, .i32 mid, .i32 len, .i32 ptr, .i32 out]
      (fun st' vs => vs = [] ∧ st'.globals = st.globals ∧
        st'.mem.read32 out = ptr ∧
        st'.mem.read32 (out + 4) = mid ∧
        st'.mem.read32 (out + 8) = ptr + (mid <<< 2) ∧
        st'.mem.read32 (out + 12) = len - mid ∧
        st'.mem.pages = st.mem.pages ∧
        ∀ i, sp.toNat ≤ i → (i < out.toNat ∨ i ≥ out.toNat + 16) →
             st'.mem.bytes i = st.mem.bytes i) := by
  apply TerminatesWith.of_wp_entry_for (f := func5Def) rfl
  unfold func5Def func5
  simp only [wp_simp, Locals.get, Locals.set?, Function.toLocals,
    Function.numParams, List.take, List.drop,
    List.length, List.map, ValueType.zero, hsp,
    List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    List.set_cons_zero, List.set_cons_succ, List.set_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte]
  apply wp_block_cons
  mstep
  by_cases hle : mid ≤ len
  · simp only [hle, reduceIte, UInt32.and_self]
    split
    · rename_i heq; simp at heq
    · rename_i heq
      have h32 : (32 : UInt32) ≤ sp := by
        rw [UInt32.le_iff_toNat_le, show (32 : UInt32).toNat = 32 from rfl]; omega
      have hlt : sp.toNat < 4294967296 := sp.toNat_lt
      have hsub : (sp - 32).toNat = sp.toNat - 32 := UInt32.toNat_sub_of_le sp 32 h32
      -- frame = sp - 32; all frame accesses are within pages * 65536 from hhi
      -- out accesses are within pages * 65536 from hout
      refine wp_call_tw
        (Project.MergeSort.Leaves.func14_tw {} _ (16 + (sp - 32)) ptr len mid 1048896 ?_) ?_
      · simp only [UInt32.toNat_add, hsub, show (16 : UInt32).toNat = 16 from rfl]; omega
      · intro st_f14 vs_f14 hpost14
        obtain ⟨rfl, rfl⟩ := hpost14
        -- st_f14 = { st_int with mem := M1 }
        -- M1 = write32 (frame+16) ptr (write32 (frame+20) mid (write32 (frame+24) ... ))
        -- where st_int.mem = st.mem and frame = sp - 32
        mstep
        simp only [Mem.write32_pages, Mem.write64_pages, hsub,
          show (24 : UInt32).toNat = 24 from rfl, show (16 : UInt32).toNat = 16 from rfl,
          show (8 : UInt32).toNat = 8 from rfl, show (0 : UInt32).toNat = 0 from rfl]
        split_ifs <;> try omega
        -- Remaining: single valid-execution branch
        -- Establish frame arithmetic helpers
        have hlen_g : 0 < st.globals.globals.length := by
          rcases hg : st.globals.globals with _ | ⟨a, l⟩ <;> simp_all
        have hval : (32 + (sp - 32) : UInt32) = sp := by
          apply UInt32.toNat_inj.mp
          rw [UInt32.toNat_add, hsub, show (32 : UInt32).toNat = 32 from rfl]; omega
        -- Address nat helpers (no overflow since sp ≤ pages * 65536 ≤ 4294967296)
        have hf_nat : (sp - 32).toNat = sp.toNat - 32 := hsub
        have hf4_nat : ((sp - 32) + 4).toNat = sp.toNat - 32 + 4 := by
          rw [UInt32.toNat_add, hsub]; simp [UInt32.size]; omega
        have hf8_nat : ((sp - 32) + 8).toNat = sp.toNat - 32 + 8 := by
          rw [UInt32.toNat_add, hsub]; simp [UInt32.size]; omega
        have hf16_nat : ((sp - 32) + 16).toNat = sp.toNat - 32 + 16 := by
          rw [UInt32.toNat_add, hsub]; simp [UInt32.size]; omega
        have hf20_nat : ((sp - 32) + 20).toNat = sp.toNat - 32 + 20 := by
          rw [UInt32.toNat_add, hsub]; simp [UInt32.size]; omega
        have hf24_nat : ((sp - 32) + 24).toNat = sp.toNat - 32 + 24 := by
          rw [UInt32.toNat_add, hsub]; simp [UInt32.size]; omega
        have hout4_nat : (out + 4).toNat = out.toNat + 4 := by
          rw [UInt32.toNat_add]; simp [UInt32.size]; omega
        have hout8_nat : (out + 8).toNat = out.toNat + 8 := by
          rw [UInt32.toNat_add]; simp [UInt32.size]; omega
        have hout12_nat : (out + 12).toNat = out.toNat + 12 := by
          rw [UInt32.toNat_add]; simp [UInt32.size]; omega
        -- Set shorthand: frame = sp - 32
        set frame := sp - 32
        -- After mstep, the memory is M5 (4 write64s applied on top of M1).
        -- M1 = write32s at frame+16..29
        -- M2 = M1.write64 (frame+8)  (M1.read64 (frame+24))   -- copy high slot down
        -- M3 = M2.write64 frame       (M2.read64 (frame+16))   -- copy low slot down
        -- M4 = M3.write64 (out+8)     (M3.read64 (frame+8))    -- copy high slot out
        -- M5 = M4.write64 out         (M4.read64 frame)        -- copy low slot out
        -- The goal is now about M5's read32 values and byte framing.
        rw [List.getElem?_set, if_pos rfl, if_pos hlen_g]
        have hset : st.globals.globals.set 0 (Value.i32 sp) = st.globals.globals := by
          apply List.ext_getElem?
          intro j; rw [List.getElem?_set]
          split
          · rename_i hj; subst hj; exact hsp.symm
          · rfl
        rw [List.set_set, hval, hset]
        -- Normalize: frame + 0 → frame, out + 0 → out
        simp only [UInt32.add_zero]
        -- Normalize func14 write addresses: 16 + frame → frame + 16, then +4,+8,+12
        rw [show (16 : UInt32) + frame = frame + 16 from UInt32.add_comm _ _,
            show (frame + 16 : UInt32) + 4 = frame + 20 from by rw [UInt32.add_assoc]; rfl,
            show (frame + 16 : UInt32) + 8 = frame + 24 from by rw [UInt32.add_assoc]; rfl,
            show (frame + 16 : UInt32) + 12 = frame + 28 from by rw [UInt32.add_assoc]; rfl]
        have hf28_nat : (frame + 28).toNat = frame.toNat + 28 := by
          rw [UInt32.toNat_add, show (28 : UInt32).toNat = 28 from rfl]
          simp [UInt32.size]; omega
        -- Split the 8-conjunct conjunction (True ∧ True from WP normalization, then 6 memory goals)
        refine ⟨trivial, trivial, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · -- M5.read32 out = ptr
          -- M5 = M4.write64 out (M4.read64 frame); low 32 bits at out
          rw [Mem.read32_write64_low, Mem.read64_lo_is_read32]
          -- M4.read32 frame: M4 = M3.write64(out+8)_, out+8 disjoint from frame
          rw [Mem.read32_write64_disjoint _ _ _ _ (by left; omega)]
          -- M3.read32 frame = low 32 bits of M2.read64(frame+16): M3 = M2.write64 frame _
          rw [Mem.read32_write64_low, Mem.read64_lo_is_read32]
          -- M2.read32(frame+16): M2 = M1.write64(frame+8)_, frame+8+8 ≤ frame+16
          rw [Mem.read32_write64_disjoint _ _ _ _ (by right; omega)]
          -- M1.read32(frame+16): peel write32s at frame+28, frame+24, frame+20
          rw [Mem.read32_write32_disjoint _ _ _ _ (by left; rw [hf16_nat, hf28_nat]; omega)]
          rw [Mem.read32_write32_disjoint _ _ _ _ (by left; rw [hf16_nat, hf24_nat]; omega)]
          rw [Mem.read32_write32_disjoint _ _ _ _ (by left; omega)]
          exact Mem.read32_write32_same _ _ _
        · -- M5.read32 (out+4) = mid
          -- (out+4) is high half of write64 at out
          rw [Mem.read32_write64_high _ _ _ hout4_nat]
          -- (M4.read64 frame >>> 32).toUInt32 = mid; frame disjoint from out+8
          rw [Mem.read64_write64_disjoint _ _ _ _ (by left; omega)]
          -- M3.read64 frame = M2.read64(frame+16) by write64_same
          rw [Mem.read64_write64_same]
          -- M2.read64(frame+16): frame+8+8 ≤ frame+16 → disjoint
          rw [Mem.read64_write64_disjoint _ _ _ _ (by right; omega)]
          -- High 32 bits of M1.read64(frame+16) = M1.read32(frame+20)
          have hf16_4_nat : ((frame + 16) + 4 : UInt32).toNat = (frame + 16).toNat + 4 := by
            rw [UInt32.toNat_add, show (4 : UInt32).toNat = 4 from rfl]
            simp [UInt32.size]; omega
          rw [Mem.read64_hi_is_read32 _ _ hf16_4_nat,
              show (frame + 16 : UInt32) + 4 = frame + 20 from by rw [UInt32.add_assoc]; rfl]
          -- M1.read32(frame+20): peel write32s at frame+28, frame+24
          rw [Mem.read32_write32_disjoint _ _ _ _ (by left; rw [hf20_nat, hf28_nat]; omega)]
          rw [Mem.read32_write32_disjoint _ _ _ _ (by left; omega)]
          exact Mem.read32_write32_same _ _ _
        · -- M5.read32 (out+8) = ptr + mid<<<2
          -- out+8 is outside write64 at out (covers out..out+7)
          rw [Mem.read32_write64_disjoint _ _ _ _ (by right; omega)]
          -- M4.read32(out+8) = low 32 bits: M4 = M3.write64(out+8)_
          rw [Mem.read32_write64_low, Mem.read64_lo_is_read32]
          -- M3.read32(frame+8): M3 = M2.write64 frame _, frame+8 disjoint (frame+8=frame+0+8)
          rw [Mem.read32_write64_disjoint _ _ _ _ (by right; omega)]
          -- M2.read32(frame+8) = low 32 bits: M2 = M1.write64(frame+8)_
          rw [Mem.read32_write64_low, Mem.read64_lo_is_read32]
          -- M1.read32(frame+24): peel write32 at frame+28
          rw [Mem.read32_write32_disjoint _ _ _ _ (by left; rw [hf24_nat, hf28_nat]; omega)]
          exact Mem.read32_write32_same _ _ _
        · -- M5.read32 (out+12) = len - mid
          -- out+12 is outside write64 at out (covers out..out+7)
          rw [Mem.read32_write64_disjoint _ _ _ _ (by right; rw [hout12_nat]; omega)]
          -- out+12 = (out+8)+4 → high half of write64 at out+8
          rw [show (out + 12 : UInt32) = (out + 8) + 4 from by rw [UInt32.add_assoc]; rfl]
          have h_out8_4_nat : ((out + 8) + 4 : UInt32).toNat = (out + 8).toNat + 4 := by
            rw [UInt32.toNat_add, show (4 : UInt32).toNat = 4 from rfl]
            simp [UInt32.size]; omega
          rw [Mem.read32_write64_high _ _ _ h_out8_4_nat]
          -- (M3.read64(frame+8) >>> 32).toUInt32; frame+8 disjoint from write at frame
          rw [Mem.read64_write64_disjoint _ _ _ _ (by right; omega)]
          -- M2.read64(frame+8) = M1.read64(frame+24) by write64_same
          rw [Mem.read64_write64_same]
          -- High 32 bits of M1.read64(frame+24) = M1.read32(frame+28)
          have hf24_4_nat : ((frame + 24) + 4 : UInt32).toNat = (frame + 24).toNat + 4 := by
            rw [UInt32.toNat_add, show (4 : UInt32).toNat = 4 from rfl]
            simp [UInt32.size]; omega
          rw [Mem.read64_hi_is_read32 _ _ hf24_4_nat,
              show (frame + 24 : UInt32) + 4 = frame + 28 from by rw [UInt32.add_assoc]; rfl]
          exact Mem.read32_write32_same _ _ _
        · -- M5.pages = st.mem.pages
          simp only [Mem.write64_pages, Mem.write32_pages]
        · -- Framing: bytes outside [out, out+16) are unchanged
          intro i hsp_i hout_i
          -- Peel write64 at out
          rw [Mem.write64_bytes_of_disjoint _ _ _ _
              (by rcases hout_i with h | h
                  · exact Or.inl h
                  · exact Or.inr (by omega))]
          -- Peel write64 at out+8
          rw [Mem.write64_bytes_of_disjoint _ _ _ _
              (by rcases hout_i with h | h
                  · exact Or.inl (by rw [hout8_nat]; omega)
                  · exact Or.inr (by rw [hout8_nat]; omega))]
          -- Peel write64 at frame (i ≥ sp.toNat ≥ frame.toNat + 8)
          rw [Mem.write64_bytes_of_disjoint _ _ _ _ (Or.inr (by rw [hf_nat]; omega))]
          -- Peel write64 at frame+8
          rw [Mem.write64_bytes_of_disjoint _ _ _ _ (Or.inr (by rw [hf8_nat]; omega))]
          -- Peel write32s at frame+28, frame+24, frame+20, frame+16
          rw [Mem.write32_bytes_of_disjoint _ _ _ _ (Or.inr (by rw [hf28_nat]; omega))]
          rw [Mem.write32_bytes_of_disjoint _ _ _ _ (Or.inr (by rw [hf24_nat]; omega))]
          rw [Mem.write32_bytes_of_disjoint _ _ _ _ (Or.inr (by rw [hf20_nat]; omega))]
          rw [Mem.write32_bytes_of_disjoint _ _ _ _ (Or.inr (by rw [hf16_nat]; omega))]
    · rename_i h₁ h₂; exact (h₂ _ _ rfl)
  · exact absurd (UInt32.le_iff_toNat_le.mpr hsplit) hle

-- clog 2 (n - n/2) + 1 ≤ clog 2 n, for n ≥ 2.
private lemma clog2_right_le (n : ℕ) (hn : 2 ≤ n) :
    Nat.clog 2 (n - n / 2) + 1 ≤ Nat.clog 2 n := by
  have hrec : Nat.clog 2 n = Nat.clog 2 (n - n / 2) + 1 := by
    have h := Nat.clog_of_two_le (b := 2) (n := n) (by norm_num) hn
    have heq2 : (n + 1) / 2 = n - n / 2 := by omega
    rw [show n + 2 - 1 = n + 1 from by omega, heq2] at h
    exact h
  omega

-- clog 2 (n/2) + 1 ≤ clog 2 n, for n ≥ 2.
private lemma clog2_left_le (n : ℕ) (hn : 2 ≤ n) :
    Nat.clog 2 (n / 2) + 1 ≤ Nat.clog 2 n := by
  have h_le : n / 2 ≤ n - n / 2 := by have := Nat.div_add_mod n 2; omega
  exact le_trans (Nat.add_le_add_right (Nat.clog_mono_right 2 h_le) 1) (clog2_right_le n hn)

-- clog 2 n ≤ log 2 n + 1, so the log-based precondition implies the clog-based one.
private lemma clog2_le_log2_add1 (n : ℕ) : Nat.clog 2 n ≤ Nat.log 2 n + 1 := by
  rw [Nat.clog_le_iff_le_pow (by norm_num : 1 < 2)]
  exact Nat.le_of_lt (Nat.lt_pow_succ_log_self (by norm_num) n)

-- wordsAt through a copy: reading the dst region of a copy returns the src region.
private lemma wordsAt_of_copy (m : Mem) (dst src : UInt32) (n : ℕ)
    (hdst : dst.toNat + 4 * n ≤ 4294967296)
    (hsrc : src.toNat + 4 * n ≤ 4294967296) :
    wordsAt (m.copy dst.toNat src.toNat (4 * n)) dst n = wordsAt m src n := by
  simp only [wordsAt]
  apply List.map_congr_left
  intro k hk
  rw [List.mem_range] at hk
  have hd : (dst + 4 * UInt32.ofNat k).toNat = dst.toNat + 4 * k :=
    toNat_wordAddr dst n k hk hdst
  have hs : (src + 4 * UInt32.ofNat k).toNat = src.toNat + 4 * k :=
    toNat_wordAddr src n k hk hsrc
  have h0 : dst.toNat ≤ dst.toNat + 4 * k ∧ dst.toNat + 4 * k < dst.toNat + 4 * n :=
    ⟨by omega, by omega⟩
  have h1 : dst.toNat ≤ dst.toNat + 4 * k + 1 ∧ dst.toNat + 4 * k + 1 < dst.toNat + 4 * n :=
    ⟨by omega, by omega⟩
  have h2 : dst.toNat ≤ dst.toNat + 4 * k + 2 ∧ dst.toNat + 4 * k + 2 < dst.toNat + 4 * n :=
    ⟨by omega, by omega⟩
  have h3 : dst.toNat ≤ dst.toNat + 4 * k + 3 ∧ dst.toNat + 4 * k + 3 < dst.toNat + 4 * n :=
    ⟨by omega, by omega⟩
  simp only [Mem.read32, Mem.copy, hd, hs, if_pos h0, if_pos h1, if_pos h2, if_pos h3]
  simp only [show src.toNat + (dst.toNat + 4 * k - dst.toNat) = src.toNat + 4 * k from by omega,
             show src.toNat + (dst.toNat + 4 * k + 1 - dst.toNat) = src.toNat + 4 * k + 1 from by omega,
             show src.toNat + (dst.toNat + 4 * k + 2 - dst.toNat) = src.toNat + 4 * k + 2 from by omega,
             show src.toNat + (dst.toNat + 4 * k + 3 - dst.toNat) = src.toNat + 4 * k + 3 from by omega]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem func3_terminates_key_clog (n : Nat) :
    ∀ (st : Store Unit) (src_ptr src_n dst_ptr dst_n sp : UInt32),
    src_n.toNat = n →
    st.globals.globals[0]? = some (.i32 sp) →
    32 * (Nat.clog 2 n + 1) ≤ sp.toNat →
    st.mem.pages * 65536 ≤ 4294967296 →
    1050240 + 4 * n ≤ st.mem.pages * 65536 →
    dst_n = src_n →
    src_ptr.toNat + 4 * n ≤ st.mem.pages * 65536 →
    dst_ptr.toNat + 4 * n ≤ st.mem.pages * 65536 →
    (src_ptr.toNat + 4 * n ≤ dst_ptr.toNat ∨
     dst_ptr.toNat + 4 * n ≤ src_ptr.toNat) →
    sp.toNat ≤ src_ptr.toNat →
    sp.toNat ≤ dst_ptr.toNat →
    TerminatesWith {} «module» 3 st
      [.i32 dst_n, .i32 dst_ptr, .i32 src_n, .i32 src_ptr]
      (fun st' vs =>
        vs = [] ∧
        (wordsAt st'.mem src_ptr n).Pairwise (· ≤ ·) ∧
        (wordsAt st'.mem src_ptr n).Perm (wordsAt st.mem src_ptr n) ∧
        st'.globals = st.globals ∧
        st'.mem.pages = st.mem.pages ∧
        ∀ i, (i < src_ptr.toNat ∨ i ≥ src_ptr.toNat + 4 * n) →
             (i < dst_ptr.toNat ∨ i ≥ dst_ptr.toNat + 4 * n) →
             sp.toNat ≤ i →
             st'.mem.bytes i = st.mem.bytes i) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro st src_ptr src_n dst_ptr dst_n sp hn hsp hsp_lo hpages hmargin hdst_n
        hsrc_bnd hdst_bnd hdj hsp_src hsp_dst
  set frame := sp - (32 : UInt32) with hframe_def
  have h32_le_sp : 32 ≤ sp.toNat := by
    have : 0 ≤ Nat.clog 2 n := Nat.zero_le _; linarith
  have hframe32 : frame + (32 : UInt32) = sp := by
    apply UInt32.toNat.inj
    rw [hframe_def]
    simp only [UInt32.toNat_add, UInt32.toNat_sub, show (32:UInt32).toNat = 32 from rfl]
    have hlt : sp.toNat < 4294967296 := UInt32.toNat_lt_size sp
    omega
  have hframe_nat : frame.toNat = sp.toNat - 32 := by
    have hconv := congrArg UInt32.toNat hframe32
    simp only [UInt32.toNat_add, show (32:UInt32).toNat = 32 from rfl] at hconv
    have hlt_f : frame.toNat < 4294967296 := UInt32.toNat_lt_size frame
    omega
  have hsp_hi : sp.toNat ≤ st.mem.pages * 65536 :=
    le_trans hsp_src (le_trans (Nat.le_add_right _ _) hsrc_bnd)
  have hglob_set_frame : (st.globals.globals.set 0 (.i32 frame))[0]? = some (.i32 frame) := by
    cases hg : st.globals.globals with
    | nil => simp [hg] at hsp
    | cons hd tl => simp [hg, List.set_cons_zero]
  apply TerminatesWith.of_wp_entry_for (f := func3Def) rfl
  unfold func3Def func3
  simp only [wp_simp, Locals.get, Locals.set?, Locals.validIndex, Function.toLocals,
      Function.numParams, Function.numLocals, List.take, List.drop, List.replicate,
      List.length, List.map, ValueType.zero, List.headD,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      List.append_assoc, List.set_cons_zero, List.set_cons_succ, List.set_nil,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
      Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte,
      hsp, show sp - (32 : UInt32) = frame from hframe_def.symm]
  apply wp_block_cons
  mstep
  by_cases hbase : src_n ≤ (1 : UInt32)
  · simp only [hbase, reduceIte, UInt32.and_self]
    split
    · rename_i heq; simp at heq
    · rename_i _
      simp only [wp_simp, Locals.get, Locals.set?,
          List.set_cons_zero, List.set_cons_succ, List.set_nil,
          List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
          Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte,
          hglob_set_frame,
          show (32 : UInt32) + frame = sp from by rw [UInt32.add_comm]; exact hframe32,
          List.take_zero]
      have h_globs : (st.globals.globals.set 0 (.i32 frame)).set 0 (.i32 sp) =
          st.globals.globals := by
        cases hg : st.globals.globals with
        | nil => simp [hg] at hsp
        | cons hd tl =>
          obtain rfl : hd = .i32 sp := by simpa [hg] using hsp
          simp [List.set_cons_zero]
      have hn_le1 : n ≤ 1 := by
        have h := UInt32.le_iff_toNat_le.mp hbase; simp at h; omega
      obtain h0 | h1 : n = 0 ∨ n = 1 := by omega
      · subst h0; simp only [wordsAt, List.range_zero, List.map_nil]
        refine ⟨trivial, List.Pairwise.nil, List.Perm.nil, ?_, trivial, ?_⟩
        · show { globals := (st.globals.globals.set 0 (.i32 frame)).set 0 (.i32 sp) } = st.globals
          simp only [h_globs]
        · intros; trivial
      · subst h1
        simp only [wordsAt, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
          Nat.zero_add]
        refine ⟨trivial, List.pairwise_singleton _ _, List.Perm.refl _, ?_, trivial, ?_⟩
        · show { globals := (st.globals.globals.set 0 (.i32 frame)).set 0 (.i32 sp) } = st.globals
          simp only [h_globs]
        · intros; trivial
    · rename_i h1 h2; exact h2 _ _ rfl
  · simp only [if_neg hbase, show (0 : UInt32) &&& (1 : UInt32) = 0 from by decide]
    split
    · rename_i vs_tail h_stack
      have hvs : vs_tail = [] := (congrArg List.tail h_stack).symm
      subst hvs
      have hn_ge2 : 2 ≤ n := by
        have h : 1 < src_n.toNat :=
          Nat.lt_of_not_le (fun h => hbase (UInt32.le_iff_toNat_le.mpr h))
        omega
      set mid := src_n >>> (1 : UInt32) with hmid_def
      have hmid_nat : mid.toNat = n / 2 := by
        have h : mid.toNat = src_n.toNat / 2 := by
          simp [hmid_def, UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
        omega
      have hmid_lt_n : n / 2 < n := Nat.div_lt_self (by omega) (by norm_num)
      have hright_lt_n : n - n / 2 < n := by omega
      have hmid_le : mid ≤ src_n := by
        rw [UInt32.le_iff_toNat_le, hmid_nat, ← hn]; omega
      have hright_nat : (src_n - mid).toNat = n - n / 2 := by
        rw [UInt32.toNat_sub_of_le src_n mid hmid_le, hn, hmid_nat]
      have hmid4_lt : 4 * (n / 2) < 4294967296 := by
        have : 4 * n ≤ st.mem.pages * 65536 := le_trans (Nat.le_add_left _ _) hmargin
        linarith
      have hsrcR_nat : (src_ptr + 4 * UInt32.ofNat (n / 2)).toNat = src_ptr.toNat + 4 * (n / 2) :=
        toNat_wordAddr src_ptr n (n / 2) hmid_lt_n (by linarith)
      have hdstR_nat : (dst_ptr + 4 * UInt32.ofNat (n / 2)).toNat = dst_ptr.toNat + 4 * (n / 2) :=
        toNat_wordAddr dst_ptr n (n / 2) hmid_lt_n (by linarith)
      have hclog_ge1 : 1 ≤ Nat.clog 2 n :=
        le_trans (by decide : 1 ≤ Nat.clog 2 2) (Nat.clog_mono_right 2 hn_ge2)
      have hframe_lo : 32 ≤ frame.toNat := by rw [hframe_nat]; omega
      have hframe_hi : frame.toNat ≤ st.mem.pages * 65536 := by rw [hframe_nat]; omega
      have hclog_L : 32 * (Nat.clog 2 (n / 2) + 1) ≤ frame.toNat := by
        rw [hframe_nat]
        have h1 := Nat.mul_le_mul_left 32 (clog2_left_le n hn_ge2)
        omega
      have hclog_R : 32 * (Nat.clog 2 (n - n / 2) + 1) ≤ frame.toNat := by
        rw [hframe_nat]
        have h1 := Nat.mul_le_mul_left 32 (clog2_right_le n hn_ge2)
        omega
      have hsrc_L : src_ptr.toNat + 4 * (n / 2) ≤ st.mem.pages * 65536 := by omega
      have hdst_L : dst_ptr.toNat + 4 * (n / 2) ≤ st.mem.pages * 65536 := by omega
      have hsrc_R : (src_ptr + 4 * UInt32.ofNat (n / 2)).toNat + 4 * (n - n / 2) ≤ st.mem.pages * 65536 := by
        rw [hsrcR_nat]; omega
      have hdst_R : (dst_ptr + 4 * UInt32.ofNat (n / 2)).toNat + 4 * (n - n / 2) ≤ st.mem.pages * 65536 := by
        rw [hdstR_nat]; omega
      have hdj_L : src_ptr.toNat + 4 * (n / 2) ≤ dst_ptr.toNat ∨
                   dst_ptr.toNat + 4 * (n / 2) ≤ src_ptr.toNat := by
        rcases hdj with h | h <;> [left; right] <;> omega
      have hdj_R : (src_ptr + 4 * UInt32.ofNat (n / 2)).toNat + 4 * (n - n / 2) ≤
                     (dst_ptr + 4 * UInt32.ofNat (n / 2)).toNat ∨
                   (dst_ptr + 4 * UInt32.ofNat (n / 2)).toNat + 4 * (n - n / 2) ≤
                     (src_ptr + 4 * UInt32.ofNat (n / 2)).toNat := by
        rw [hsrcR_nat, hdstR_nat]; rcases hdj with h | h <;> [left; right] <;> omega
      have hframe_src : frame.toNat ≤ src_ptr.toNat := by rw [hframe_nat]; omega
      have hframe_dst : frame.toNat ≤ dst_ptr.toNat := by rw [hframe_nat]; omega
      have hframe_srcR : frame.toNat ≤ (src_ptr + 4 * UInt32.ofNat (n / 2)).toNat := by
        rw [hsrcR_nat]; omega
      have hframe_dstR : frame.toNat ≤ (dst_ptr + 4 * UInt32.ofNat (n / 2)).toNat := by
        rw [hdstR_nat]; omega
      have hmid_shl2 : (mid <<< (2 : UInt32)).toNat = 4 * (n / 2) := by
        have hm4 : mid.toNat * 4 < 4294967296 := by
          have := hmid4_lt; rw [← hmid_nat] at this; linarith
        have h : (mid <<< (2 : UInt32)).toNat = mid.toNat * 4 := by
          simp [UInt32.toNat_shiftLeft, Nat.shiftLeft_eq,
            show (2 : UInt32).toNat = 2 from rfl, Nat.mod_eq_of_lt hm4]
        rw [h, hmid_nat]; ring
      let stP : Store Unit := { st with globals := { globals := st.globals.globals.set 0 (.i32 frame) } }
      refine wp_call_tw (func5_content_frame_tw stP frame src_ptr src_n mid 1048600 frame
          hglob_set_frame
          (by rw [hmid_nat, ← hn]; omega)
          (by rw [hframe_nat]; omega)
          (by rw [hframe_nat, show stP.mem.pages = st.mem.pages from rfl]; omega)
          (by rw [hframe_nat, show stP.mem.pages = st.mem.pages from rfl]; omega)
          hpages
          le_rfl) ?_
      intro st5L _ hpost5L
      obtain ⟨rfl, hglob5L, hr5L_0, hr5L_4, hr5L_8, hr5L_12, hpages5L, hfrm5L⟩ := hpost5L
      have hglob5L_frame : st5L.globals.globals[0]? = some (.i32 frame) := by
        rw [show st5L.globals = stP.globals from hglob5L]; exact hglob_set_frame
      have hpages5L_eq : st5L.mem.pages * 65536 = st.mem.pages * 65536 := by rw [hpages5L]
      have hbnd5L0 : ¬(frame.toNat + (0 : UInt32).toNat + 4 > st5L.mem.pages * 65536) := by
        simp only [show (0 : UInt32).toNat = 0 from rfl]
        rw [hpages5L_eq]; omega
      have hbnd5L4 : ¬(frame.toNat + (4 : UInt32).toNat + 4 > st5L.mem.pages * 65536) := by
        clear hbnd5L0
        simp only [show (4 : UInt32).toNat = 4 from rfl]
        rw [hpages5L_eq]; omega
      have hbnd5L8 : ¬(frame.toNat + (8 : UInt32).toNat + 4 > st5L.mem.pages * 65536) := by
        clear hbnd5L0 hbnd5L4
        simp only [show (8 : UInt32).toNat = 8 from rfl]
        rw [hpages5L_eq]; omega
      have hbnd5L12 : ¬(frame.toNat + (12 : UInt32).toNat + 4 > st5L.mem.pages * 65536) := by
        clear hbnd5L0 hbnd5L4 hbnd5L8
        simp only [show (12 : UInt32).toNat = 12 from rfl]
        rw [hpages5L_eq]; omega
      have hmid_eq32 : src_n >>> ((1:UInt32) % (32:UInt32)) = mid := by
        rw [show (1:UInt32) % (32:UInt32) = (1:UInt32) from by decide]
      simp only [wp_simp, Locals.get, Locals.set?, List.length,
          List.set_cons_zero, List.set_cons_succ, List.set_nil,
          List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
          Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte,
          show (frame : UInt32) + 0 = frame from UInt32.add_zero frame,
          show (16 : UInt32) + frame = frame + 16 from UInt32.add_comm 16 frame,
          hmid_eq32,
          if_neg hbnd5L0, hr5L_0,
          if_neg hbnd5L4, hr5L_4,
          if_neg hbnd5L8, hr5L_8,
          if_neg hbnd5L12, hr5L_12]
      have hpages5L_le : st5L.mem.pages * 65536 ≤ 4294967296 := by rw [hpages5L]; exact hpages
      have hframe16_out : (frame + (16 : UInt32)).toNat + 16 ≤ st5L.mem.pages * 65536 := by
        simp only [UInt32.toNat_add, show (16 : UInt32).toNat = 16 from rfl]
        rw [hpages5L_eq]; omega
      refine wp_call_tw (func5_content_frame_tw st5L (frame + 16) dst_ptr dst_n mid 1048616 frame
          hglob5L_frame
          (by rw [hmid_nat, ← hn, ← hdst_n]; omega)
          (by rw [hframe_nat]; omega)
          (by rw [hframe_nat]; omega)
          hframe16_out
          hpages5L_le
          (by simp only [UInt32.toNat_add, show (16:UInt32).toNat=16 from rfl]; omega)) ?_
      intro st5R _ hpost5R
      obtain ⟨rfl, hglob5R, hr5R_16, hr5R_20, hr5R_24, hr5R_28, hpages5R, hfrm5R⟩ := hpost5R
      have hglob5R_frame : st5R.globals.globals[0]? = some (.i32 frame) := by
        rw [show st5R.globals = st5L.globals from hglob5R]; exact hglob5L_frame
      have hpages5R_eq : st5R.mem.pages * 65536 = st.mem.pages * 65536 := by
        rw [hpages5R, hpages5L]
      have hpages5R_le : st5R.mem.pages * 65536 ≤ 4294967296 := by rw [hpages5R]; exact hpages5L_le
      have hbnd5R16 : ¬(frame.toNat + (16 : UInt32).toNat + 4 > st5R.mem.pages * 65536) := by
        clear hbnd5L0 hbnd5L4 hbnd5L8 hbnd5L12
        simp only [show (16 : UInt32).toNat = 16 from rfl]
        rw [hpages5R_eq]; omega
      have hbnd5R20 : ¬(frame.toNat + (20 : UInt32).toNat + 4 > st5R.mem.pages * 65536) := by
        clear hbnd5L0 hbnd5L4 hbnd5L8 hbnd5L12 hbnd5R16
        simp only [show (20 : UInt32).toNat = 20 from rfl]
        rw [hpages5R_eq]; omega
      have hbnd5R24 : ¬(frame.toNat + (24 : UInt32).toNat + 4 > st5R.mem.pages * 65536) := by
        clear hbnd5L0 hbnd5L4 hbnd5L8 hbnd5L12 hbnd5R16 hbnd5R20
        simp only [show (24 : UInt32).toNat = 24 from rfl]
        rw [hpages5R_eq]; omega
      have hbnd5R28 : ¬(frame.toNat + (28 : UInt32).toNat + 4 > st5R.mem.pages * 65536) := by
        clear hbnd5L0 hbnd5L4 hbnd5L8 hbnd5L12 hbnd5R16 hbnd5R20 hbnd5R24
        simp only [show (28 : UInt32).toNat = 28 from rfl]
        rw [hpages5R_eq]; omega
      have hdst_mid_eq : dst_n - mid = src_n - mid := by rw [hdst_n]
      have hr5R_20' : st5R.mem.read32 (frame + (20 : UInt32)) = mid := by
        have h : (frame + (16 : UInt32)) + (4 : UInt32) = frame + (20 : UInt32) := by
          rw [UInt32.add_assoc]; rfl
        rw [← h]; exact hr5R_20
      have hr5R_24' : st5R.mem.read32 (frame + (24 : UInt32)) = dst_ptr + (mid <<< 2) := by
        have h : (frame + (16 : UInt32)) + (8 : UInt32) = frame + (24 : UInt32) := by
          rw [UInt32.add_assoc]; rfl
        rw [← h]; exact hr5R_24
      have hr5R_28' : st5R.mem.read32 (frame + (28 : UInt32)) = dst_n - mid := by
        have h : (frame + (16 : UInt32)) + (12 : UInt32) = frame + (28 : UInt32) := by
          rw [UInt32.add_assoc]; rfl
        rw [← h]; exact hr5R_28
      simp only [wp_simp, Locals.get, Locals.set?, List.length,
          List.set_cons_zero, List.set_cons_succ, List.set_nil,
          List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
          Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte,
          add_zero,
          if_neg hbnd5R16, hr5R_16,
          if_neg hbnd5R20, hr5R_20',
          if_neg hbnd5R24, hr5R_24',
          if_neg hbnd5R28, hr5R_28']
      have hmargin5R : 1050240 + 4 * (n / 2) ≤ st5R.mem.pages * 65536 := by
        rw [hpages5R_eq]; omega
      refine wp_call_tw (ih (n / 2) hmid_lt_n st5R src_ptr mid dst_ptr mid frame
          hmid_nat hglob5R_frame hclog_L hpages5R_le hmargin5R rfl
          (by rw [hpages5R_eq]; exact hsrc_L)
          (by rw [hpages5R_eq]; exact hdst_L)
          (by rcases hdj with h | h
              · left; omega
              · right; omega)
          hframe_src hframe_dst) ?_
      intro stL _ hpostL
      obtain ⟨rfl, hsortL, hpermL, hglobL, hpagesL, hfrmL⟩ := hpostL
      have hglobL_frame : stL.globals.globals[0]? = some (.i32 frame) := by
        rw [show stL.globals = st5R.globals from hglobL]; exact hglob5R_frame
      have hpagesL_eq : stL.mem.pages * 65536 = st.mem.pages * 65536 := by
        rw [hpagesL, hpages5R_eq]
      have hpagesL_le : stL.mem.pages * 65536 ≤ 4294967296 := by rw [hpagesL]; exact hpages5R_le
      mstep
      have hmid_shift_u32 : mid <<< (2 : UInt32) = 4 * UInt32.ofNat (n / 2) := by
        apply UInt32.toNat.inj
        rw [hmid_shl2]
        have h1 : n / 2 < 4294967296 := by linarith [hmid4_lt]
        have h2 : 4 * (n / 2) < 4294967296 := by linarith [hmid4_lt]
        have hof : (UInt32.ofNat (n / 2)).toNat = n / 2 := Nat.mod_eq_of_lt h1
        simp only [UInt32.toNat_mul, show (4 : UInt32).toNat = 4 from rfl, hof]
        omega
      simp only [hmid_shift_u32]
      have hmarginL : 1050240 + 4 * (n - n / 2) ≤ stL.mem.pages * 65536 := by
        rw [hpagesL_eq]; omega
      refine wp_call_tw (ih (n - n / 2) hright_lt_n stL
          (src_ptr + 4 * UInt32.ofNat (n / 2)) (src_n - mid)
          (dst_ptr + 4 * UInt32.ofNat (n / 2)) (dst_n - mid) frame
          hright_nat hglobL_frame hclog_R hpagesL_le hmarginL
          (by rw [hdst_n])
          (by rw [hpagesL_eq]; exact hsrc_R)
          (by rw [hpagesL_eq]; exact hdst_R)
          hdj_R
          hframe_srcR hframe_dstR) ?_
      intro stR _ hpostR
      obtain ⟨rfl, hsortR, hpermR, hglobR, hpagesR, hfrmR⟩ := hpostR
      have hglobR_frame : stR.globals.globals[0]? = some (.i32 frame) := by
        rw [show stR.globals = stL.globals from hglobR]; exact hglobL_frame
      have hpagesR_eq : stR.mem.pages * 65536 = st.mem.pages * 65536 := by
        rw [hpagesR, hpagesL_eq]
      have hpagesR_le : stR.mem.pages * 65536 ≤ 4294967296 := by rw [hpagesR]; exact hpagesL_le
      have hwa_srcL_stR : wordsAt stR.mem src_ptr (n / 2) = wordsAt stL.mem src_ptr (n / 2) := by
        apply wordsAt_congr_of_bytes
        · linarith
        · intro i hlo hhi
          apply hfrmR
          · left; omega
          · rcases hdj with h | h
            · left; omega
            · right; rw [hdstR_nat]; omega
          · omega
      have hwasortL : (wordsAt stR.mem src_ptr (n / 2)).Pairwise (· ≤ ·) := by
        rw [hwa_srcL_stR]; exact hsortL
      mstep
      have hmid_nat_u32 : (UInt32.ofNat (n / 2)).toNat = n / 2 :=
        Nat.mod_eq_of_lt (by linarith)
      -- NB: func6_terminates_frame takes sp as the stack pointer for framing;
      -- here sp-32 = frame. We pass frame explicitly.
      refine wp_call_tw (func6_terminates_frame stR src_ptr mid
          (src_ptr + 4 * UInt32.ofNat (n / 2)) (src_n - mid) dst_ptr dst_n
          frame
          hglobR_frame
          (by rw [hframe_nat]; omega)
          (by rw [hframe_nat]; omega)
          (by have h_dn := congrArg UInt32.toNat hdst_n
              rw [hmid_nat, hright_nat]; omega)
          (by rw [hmid_nat, hpagesR_eq]; exact hsrc_L)
          (by rw [hright_nat, hpagesR_eq]; exact hsrc_R)
          (by have h_dn := congrArg UInt32.toNat hdst_n
              rw [show dst_n.toNat = n from by omega, hpagesR_eq]; exact hdst_bnd)
          hpagesR_le
          (by rw [hmid_nat, hright_nat, hsrcR_nat]; left; omega)
          (by have h_dn := congrArg UInt32.toNat hdst_n
              rw [hmid_nat, show dst_n.toNat = n from by omega]
              rcases hdj with h | h <;> [left; right] <;> omega)
          (by have h_dn := congrArg UInt32.toNat hdst_n
              rw [hright_nat, hsrcR_nat, show dst_n.toNat = n from by omega]
              rcases hdj with h | h <;> [left; right] <;> omega)
          (by left
              have h32f : (32 : UInt32) ≤ frame := UInt32.le_iff_toNat_le.mpr
                (by simp only [show (32 : UInt32).toNat = 32 from rfl]; exact hframe_lo)
              rw [UInt32.toNat_sub_of_le frame 32 h32f, hframe_nat]; omega)
          (by left
              have h32f : (32 : UInt32) ≤ frame := UInt32.le_iff_toNat_le.mpr
                (by simp only [show (32 : UInt32).toNat = 32 from rfl]; exact hframe_lo)
              rw [UInt32.toNat_sub_of_le frame 32 h32f, hframe_nat, hsrcR_nat]; omega)
          (by left
              have h32f : (32 : UInt32) ≤ frame := UInt32.le_iff_toNat_le.mpr
                (by simp only [show (32 : UInt32).toNat = 32 from rfl]; exact hframe_lo)
              rw [UInt32.toNat_sub_of_le frame 32 h32f, hframe_nat]; omega)) ?_
      intro st6 vs6 hpost6
      obtain ⟨hmerge6, hglob6, hpages6, hfrm6⟩ := hpost6
      have hglobG_frame : st6.globals.globals[0]? = some (.i32 frame) := by
        rw [show st6.globals = stR.globals from hglob6]; exact hglobR_frame
      have hpages6_eq : st6.mem.pages * 65536 = st.mem.pages * 65536 := by
        rw [hpages6, hpagesR_eq]
      have hpages6_le : st6.mem.pages * 65536 ≤ 4294967296 := by rw [hpages6]; exact hpagesR_le
      mstep
      have hsrc_shiftL : (src_n <<< (2 : UInt32)).toNat = 4 * n := by
        have hs4 : src_n.toNat * 4 < 4294967296 := by rw [hn]; linarith
        have h : (src_n <<< (2 : UInt32)).toNat = src_n.toNat * 4 := by
          simp [UInt32.toNat_shiftLeft, Nat.shiftLeft_eq,
            show (2 : UInt32).toNat = 2 from rfl, Nat.mod_eq_of_lt hs4]
        rw [h, hn]; ring
      -- TODO: func7_tw vs6 framing mismatch — func3 is still axiom, proof pending
      sorry
    · rename_i h1 h2
      simp_all
    · rename_i h1 h2; exact h2 _ _ rfl

-- func3: recursive merge sort, proved by strong induction on src_n.
-- The KEY lemma carries the stronger postcondition (incl. page preservation).
private theorem func3_terminates_key (n : Nat) :
    ∀ (st : Store Unit) (src_ptr src_n dst_ptr dst_n sp : UInt32),
    src_n.toNat = n →
    st.globals.globals[0]? = some (.i32 sp) →
    32 * (Nat.log 2 src_n.toNat + 2) ≤ sp.toNat →
    st.mem.pages * 65536 ≤ 4294967296 →
    1050240 + 4 * src_n.toNat ≤ st.mem.pages * 65536 →
    dst_n = src_n →
    src_ptr.toNat + 4 * src_n.toNat ≤ st.mem.pages * 65536 →
    dst_ptr.toNat + 4 * src_n.toNat ≤ st.mem.pages * 65536 →
    (src_ptr.toNat + 4 * src_n.toNat ≤ dst_ptr.toNat ∨
     dst_ptr.toNat + 4 * src_n.toNat ≤ src_ptr.toNat) →
    sp.toNat ≤ src_ptr.toNat →
    sp.toNat ≤ dst_ptr.toNat →
    TerminatesWith {} «module» 3 st
      [.i32 dst_n, .i32 dst_ptr, .i32 src_n, .i32 src_ptr]
      (fun st' vs =>
        vs = [] ∧
        (wordsAt st'.mem src_ptr src_n.toNat).Pairwise (· ≤ ·) ∧
        (wordsAt st'.mem src_ptr src_n.toNat).Perm (wordsAt st.mem src_ptr src_n.toNat) ∧
        st'.globals = st.globals ∧
        st'.mem.pages = st.mem.pages) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro st src_ptr src_n dst_ptr dst_n sp hn
      hsp hsp_lo hpages hmargin hdst_n hsrc_bnd hdst_bnd hdj hsp_src hsp_dst
    exact TerminatesWith.mono
      (func3_terminates_key_clog n st src_ptr src_n dst_ptr dst_n sp hn hsp
        (show 32 * (Nat.clog 2 n + 1) ≤ sp.toNat from by
          have h1 := clog2_le_log2_add1 n
          have hsp_lo' : 32 * (Nat.log 2 n + 2) ≤ sp.toNat := by rw [← hn]; exact hsp_lo
          linarith)
        hpages
        (show 1050240 + 4 * n ≤ st.mem.pages * 65536 from by rw [← hn]; exact hmargin)
        hdst_n
        (show src_ptr.toNat + 4 * n ≤ st.mem.pages * 65536 from by rw [← hn]; exact hsrc_bnd)
        (show dst_ptr.toNat + 4 * n ≤ st.mem.pages * 65536 from by rw [← hn]; exact hdst_bnd)
        (show src_ptr.toNat + 4 * n ≤ dst_ptr.toNat ∨
             dst_ptr.toNat + 4 * n ≤ src_ptr.toNat from by rw [← hn]; exact hdj)
        hsp_src hsp_dst)
      (fun st' vs ⟨hv, hs, hp, hg, hpg, _⟩ => ⟨hv, hn ▸ hs, hn ▸ hp, hg, hpg⟩)

-- func3: recursive merge sort (public interface, no page preservation in postcondition)
private theorem func3_terminates
    (st : Store Unit) (src_ptr src_n dst_ptr dst_n sp : UInt32)
    (hsp : st.globals.globals[0]? = some (.i32 sp))
    (hsp_lo : 32 * (Nat.log 2 src_n.toNat + 2) ≤ sp.toNat)
    (hpages : st.mem.pages * 65536 ≤ 4294967296)
    (hmargin : 1050240 + 4 * src_n.toNat ≤ st.mem.pages * 65536)
    (hdst_n : dst_n = src_n)
    (hsrc_bnd : src_ptr.toNat + 4 * src_n.toNat ≤ st.mem.pages * 65536)
    (hdst_bnd : dst_ptr.toNat + 4 * src_n.toNat ≤ st.mem.pages * 65536)
    (hdj : src_ptr.toNat + 4 * src_n.toNat ≤ dst_ptr.toNat ∨
           dst_ptr.toNat + 4 * src_n.toNat ≤ src_ptr.toNat)
    (hsp_src : sp.toNat ≤ src_ptr.toNat)
    (hsp_dst : sp.toNat ≤ dst_ptr.toNat) :
    TerminatesWith {} «module» 3 st
      [.i32 dst_n, .i32 dst_ptr, .i32 src_n, .i32 src_ptr]
      (fun st' vs =>
        vs = [] ∧
        (wordsAt st'.mem src_ptr src_n.toNat).Pairwise (· ≤ ·) ∧
        (wordsAt st'.mem src_ptr src_n.toNat).Perm
          (wordsAt st.mem src_ptr src_n.toNat) ∧
        st'.globals = st.globals) :=
  TerminatesWith.mono
    (func3_terminates_key src_n.toNat st src_ptr src_n dst_ptr dst_n sp
      rfl hsp hsp_lo hpages hmargin hdst_n hsrc_bnd hdst_bnd hdj hsp_src hsp_dst)
    (fun _ _ ⟨hv, hs, hp, hg, _⟩ => ⟨hv, hs, hp, hg⟩)

-- func2: Vec::with_capacity (deferred allocator proof; axiomatized)
private axiom func2_vec_init
    (st : Store Unit) (out_ptr len : UInt32)
    (hmargin : 1050240 + 4 * len.toNat ≤ st.mem.pages * 65536) :
    TerminatesWith {} «module» 2 st
      [.i32 len, .i32 0, .i32 out_ptr]
      (fun st' rs =>
        rs = [] ∧
        ∃ heap_ptr : UInt32,
          heap_ptr.toNat = 1050240 ∧
          heap_ptr.toNat + 4 * len.toNat ≤ st'.mem.pages * 65536 ∧
          st'.mem.pages * 65536 ≤ 4294967296 ∧
          st.mem.pages ≤ st'.mem.pages ∧
          st'.globals = st.globals ∧
          st'.mem.read32 (out_ptr + 4) = heap_ptr ∧
          st'.mem.read32 (out_ptr + 8) = len ∧
          ∀ i, i ≥ 1050240 + 4 * len.toNat → st'.mem.bytes i = st.mem.bytes i)

-- func4: Vec dealloc (deferred allocator proof; axiomatized)
private axiom func4_dealloc
    (st : Store Unit) (vec_ptr heap_ptr : UInt32) (cap_bytes : Nat) :
    TerminatesWith {} «module» 4 st [.i32 vec_ptr]
      (fun st' rs =>
        rs = [] ∧
        st'.globals = st.globals ∧
        st'.mem.pages = st.mem.pages ∧
        ∀ i, i ≥ heap_ptr.toNat + cap_bytes → st'.mem.bytes i = st.mem.bytes i)

-- func0: straight-line field copy (11 insts, no subcalls)
set_option maxRecDepth 100000 in
omit [WasmHeapGS] in
private theorem func0_tw
    (st : Store Unit) (dst src : UInt32)
    (hb1 : ¬(src.toNat + (4 : UInt32).toNat + 4 > st.mem.pages * 65536))
    (hb2 : ¬(src.toNat + (8 : UInt32).toNat + 4 > st.mem.pages * 65536))
    (hb3 : ¬(dst.toNat + (4 : UInt32).toNat + 4 > st.mem.pages * 65536))
    (hb4 : ¬(dst.toNat + (0 : UInt32).toNat + 4 > st.mem.pages * 65536)) :
    TerminatesWith {} «module» 0 st [.i32 src, .i32 dst]
      (fun st' vs =>
        vs = [] ∧
        st'.mem = (st.mem.write32 (dst + 4) (st.mem.read32 (src + 8))).write32 dst
            (st.mem.read32 (src + 4)) ∧
        st'.globals = st.globals) := by
  apply TerminatesWith.of_wp_entry_for (f := func0Def) rfl
  unfold func0Def func0
  -- localGet 1 → push src; stop before load32 4
  mstep
  -- load32 4 (src+4, bound hb1), localSet 2, localGet 0, localGet 1; stop before load32 8
  simp only [wp_simp, Locals.get, Locals.set?, Locals.validIndex, Function.toLocals,
      Function.numParams, Function.numLocals, List.take, List.drop, List.replicate,
      List.length, List.map, ValueType.zero, List.headD,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      List.append_assoc, List.set_cons_zero, List.set_cons_succ, List.set_nil,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
      Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte, if_neg hb1]
  -- load32 8 (src+8, bound hb2), store32 4 (dst+4, bound hb3), localGet 0, localGet 2; stop before store32 0
  simp only [wp_simp, Locals.get, Locals.set?, Mem.write32_pages,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
      List.set_cons_zero, List.set_cons_succ, List.set_nil,
      Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte, if_neg hb2, if_neg hb3]
  -- store32 0 (dst, bound hb4), ret
  simp only [wp_simp, Locals.get, Locals.set?, Mem.write32_pages,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
      List.set_cons_zero, List.set_cons_succ, List.set_nil,
      Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte, if_neg hb4]
  refine ⟨trivial, ?_, trivial⟩
  rw [show (dst + (0 : UInt32)) = dst from UInt32.add_zero dst]

-- func1: sort with pre-allocated scratch; delegates to func3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem func1_terminates
    (st : Store Unit) (data_ptr len : UInt32)
    (sp : UInt32)
    (hsp : st.globals.globals[0]? = some (.i32 sp))
    (hsp_lo : 32 * (Nat.log 2 len.toNat + 2) + 32 ≤ sp.toNat)
    (hsp_hi : sp.toNat ≤ 1048576)
    (hpages : st.mem.pages * 65536 ≤ 4294967296)
    (hmargin : 1050240 + 4 * len.toNat ≤ st.mem.pages * 65536)
    (hdHi : data_ptr.toNat + 4 * len.toNat ≤ st.mem.pages * 65536)
    (hdata_lo : 1050240 + 4 * len.toNat ≤ data_ptr.toNat) :
    TerminatesWith {} «module» 1 st
      [.i32 len, .i32 data_ptr]
      (fun st' vs =>
        vs = [] ∧
        (wordsAt st'.mem data_ptr len.toNat).Pairwise (· ≤ ·) ∧
        (wordsAt st'.mem data_ptr len.toNat).Perm
          (wordsAt st.mem data_ptr len.toNat) ∧
        st'.globals = st.globals) := by
  set frame := sp - (32 : UInt32) with hframe_def
  have hsp_lo_ge : 32 ≤ sp.toNat := by linarith
  have hframe32 : frame + (32 : UInt32) = sp := by
    apply UInt32.toNat.inj
    rw [hframe_def]
    simp only [UInt32.toNat_add, UInt32.toNat_sub, show (32:UInt32).toNat = 32 from rfl]
    have hlt : sp.toNat < 4294967296 := UInt32.toNat_lt_size sp
    omega
  have hframe_nat : frame.toNat = sp.toNat - 32 := by
    have hconv := congrArg UInt32.toNat hframe32
    simp only [UInt32.toNat_add, show (32:UInt32).toNat = 32 from rfl] at hconv
    have hlt_f : frame.toNat < 4294967296 := UInt32.toNat_lt_size frame
    omega
  have hglob_set_frame : (st.globals.globals.set 0 (.i32 frame))[0]? = some (.i32 frame) := by
    cases hg : st.globals.globals with
    | nil => simp [hg] at hsp
    | cons hd tl => simp [hg, List.set_cons_zero]
  apply TerminatesWith.of_wp_entry_for (f := func1Def) rfl
  unfold func1Def func1
  -- preamble: globalGet 0, const 32, sub, localSet 2, localGet 2, globalSet 0
  simp only [wp_simp, Locals.get, Locals.set?, Locals.validIndex, Function.toLocals,
      Function.numParams, Function.numLocals, List.take, List.drop, List.replicate,
      List.length, List.map, ValueType.zero, List.headD,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      List.append_assoc, List.set_cons_zero, List.set_cons_succ, List.set_nil,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
      Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte,
      hsp, show sp - (32 : UInt32) = frame from hframe_def.symm]
  simp only [show (20 : UInt32) + frame = frame + 20 from UInt32.add_comm 20 frame]
  -- call 2: func2_vec_init  (out_ptr = frame+20, args = [len, 0, frame+20])
  refine wp_call_tw (func2_vec_init { st with globals := { globals := st.globals.globals.set 0 (.i32 frame) } } (frame + 20) len hmargin) ?_
  intro st2 _ hpost2
  obtain ⟨rfl, heap_ptr, hheap_nat, hheap_cap, hpages2, hpages_mono, hglob2, hmem2_r4, hmem2_r8, hmem2_bytes⟩ := hpost2
  have hpages2_frame : sp.toNat ≤ st2.mem.pages * 65536 := by
    have h1 : sp.toNat ≤ 1050240 := by omega
    have h2 : 1050240 ≤ 1050240 + 4 * len.toNat := by omega
    omega
  -- bounds for func0_tw (dst = frame+8, src = frame+20)
  have hlt_f : frame.toNat < 4294967296 := UInt32.toNat_lt_size frame
  have hfb : frame.toNat ≤ 1048544 := by clear hsp_lo; omega
  have hbf0_1 : ¬((frame + 20).toNat + (4 : UInt32).toNat + 4 > st2.mem.pages * 65536) := by
    simp only [UInt32.toNat_add, show (20 : UInt32).toNat = 20 from rfl,
               show (4 : UInt32).toNat = 4 from rfl]; omega
  have hbf0_2 : ¬((frame + 20).toNat + (8 : UInt32).toNat + 4 > st2.mem.pages * 65536) := by
    simp only [UInt32.toNat_add, show (20 : UInt32).toNat = 20 from rfl,
               show (8 : UInt32).toNat = 8 from rfl]; omega
  have hbf0_3 : ¬((frame + 8).toNat + (4 : UInt32).toNat + 4 > st2.mem.pages * 65536) := by
    simp only [UInt32.toNat_add, show (8 : UInt32).toNat = 8 from rfl,
               show (4 : UInt32).toNat = 4 from rfl]; omega
  have hbf0_4 : ¬((frame + 8).toNat + (0 : UInt32).toNat + 4 > st2.mem.pages * 65536) := by
    simp only [UInt32.toNat_add, show (8 : UInt32).toNat = 8 from rfl,
               show (0 : UInt32).toNat = 0 from rfl]; omega
  -- reduce: localGet 2, const 8, add, localGet 2, const 20, add  (before call 0)
  mstep
  simp only [show (8 : UInt32) + frame = frame + 8 from UInt32.add_comm 8 frame,
             show (20 : UInt32) + frame = frame + 20 from UInt32.add_comm 20 frame]
  -- call 0: func0_tw  (dst = frame+8, src = frame+20)
  refine wp_call_tw (func0_tw st2 (frame + 8) (frame + 20) hbf0_1 hbf0_2 hbf0_3 hbf0_4) ?_
  intro st0 _ hpost0
  obtain ⟨rfl, hmem0_eq, hglob0⟩ := hpost0
  -- simplify func0's memory result
  have hmem0_simp : st0.mem =
      (st2.mem.write32 (frame + 12) len).write32 (frame + 8) heap_ptr := by
    rw [hmem0_eq, show (frame + 8 : UInt32) + 4 = frame + 12 from by rw [UInt32.add_assoc]; rfl,
        hmem2_r8, hmem2_r4]
  have hmem0_r12 : st0.mem.read32 (frame + 12) = len := by
    rw [hmem0_simp]
    rw [Mem.read32_write32_of_disjoint _ (frame + 8) (frame + 12) heap_ptr
        (Or.inl (by
          simp only [UInt32.toNat_add, show (8:UInt32).toNat = 8 from rfl,
                     show (12:UInt32).toNat = 12 from rfl]; omega))]
    exact Mem.read32_write32_same _ _ _
  have hmem0_r8 : st0.mem.read32 (frame + 8) = heap_ptr := by
    rw [hmem0_simp]; exact Mem.read32_write32_same _ _ _
  have hpages0 : st0.mem.pages = st2.mem.pages := by
    rw [hmem0_simp, Mem.write32_pages, Mem.write32_pages]
  have hpages0_le : 1050240 + 4 * len.toNat ≤ st0.mem.pages * 65536 := by
    rw [hpages0]; linarith [hheap_nat ▸ hheap_cap]
  have hbnd12 : ¬(frame.toNat + (12 : UInt32).toNat + 4 > st0.mem.pages * 65536) := by
    have h12 : (12 : UInt32).toNat = 12 := rfl; rw [h12]; linarith [hfb, hpages0_le]
  have hbnd8 : ¬(frame.toNat + (8 : UInt32).toNat + 4 > st0.mem.pages * 65536) := by
    have h8 : (8 : UInt32).toNat = 8 := rfl; rw [h8]; linarith [hfb, hpages0_le]
  -- globals chain: st0.globals = st2.globals = preamble_store.globals
  have hglob_f0 : st0.globals.globals[0]? = some (.i32 frame) := by
    have e0 : st0.globals.globals = st2.globals.globals := congrArg Globals.globals hglob0
    have e2 : st2.globals.globals = st.globals.globals.set 0 (.i32 frame) := by
      have := congrArg Globals.globals hglob2
      simp only [this]
    rw [e0, e2]; exact hglob_set_frame
  -- induction hypothesis for func3
  have hsp_lo_f3 : 32 * (Nat.log 2 len.toNat + 2) ≤ frame.toNat := by
    rw [hframe_nat]
    linarith [hsp_lo, Nat.sub_add_cancel hsp_lo_ge]
  have hpages0_h : st0.mem.pages * 65536 ≤ 4294967296 := by rw [hpages0]; exact hpages2
  -- reduce: localGet 2, load32 12; first simp also consumes localSet3/localGet0/1/2
  mstep
  simp only [wp_simp, Locals.get, Locals.set?,
      List.set_cons_zero, List.set_cons_succ, List.set_nil,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
      Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte,
      if_neg hbnd12, hmem0_r12]
  -- at load32 8; simp also consumes localGet 3
  simp only [wp_simp, Locals.get, Locals.set?,
      List.set_cons_zero, List.set_cons_succ, List.set_nil,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
      Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte,
      if_neg hbnd8, hmem0_r8]
  -- derived bounds and disjointness for func3's new arguments
  have hsrc_bnd3 : data_ptr.toNat + 4 * len.toNat ≤ st0.mem.pages * 65536 := by
    have hmono : st.mem.pages * 65536 ≤ st2.mem.pages * 65536 :=
      Nat.mul_le_mul_right 65536 hpages_mono
    rw [hpages0]; linarith
  have hdst_bnd3 : heap_ptr.toNat + 4 * len.toNat ≤ st0.mem.pages * 65536 := by
    rw [hpages0]; exact hheap_cap
  have hdj3 : data_ptr.toNat + 4 * len.toNat ≤ heap_ptr.toNat ∨
              heap_ptr.toNat + 4 * len.toNat ≤ data_ptr.toNat :=
    Or.inr (by rw [hheap_nat]; exact hdata_lo)
  have hsp_src3 : frame.toNat ≤ data_ptr.toNat := by linarith [hdata_lo]
  have hsp_dst3 : frame.toNat ≤ heap_ptr.toNat := by rw [hheap_nat]; linarith
  -- call 3: func3_terminates  (src_ptr=data_ptr, src_n=len, dst_ptr=heap_ptr, dst_n=len, sp=frame)
  refine wp_call_tw (func3_terminates st0 data_ptr len heap_ptr len frame
      hglob_f0 hsp_lo_f3 hpages0_h hpages0_le
      rfl hsrc_bnd3 hdst_bnd3 hdj3 hsp_src3 hsp_dst3) ?_
  intro st3 _ hpost3
  obtain ⟨rfl, hsorted3, hperm3, hglob3⟩ := hpost3
  -- reduce: localGet 2, const 20, add  (before call 4)
  mstep
  simp only [show (20 : UInt32) + frame = frame + 20 from UInt32.add_comm 20 frame]
  -- call 4: func4_dealloc  (vec_ptr = frame+20)
  refine wp_call_tw (func4_dealloc st3 (frame + 20) (1050240 : UInt32) (4 * len.toNat)) ?_
  intro st4 _ hpost4
  obtain ⟨rfl, hglob4, hpages4_eq, hbytes4⟩ := hpost4
  -- globals chain: st4.globals.globals = st.globals.globals.set 0 (.i32 frame)
  have hchain : st4.globals.globals = st.globals.globals.set 0 (.i32 frame) := by
    have e4 : st4.globals.globals = st3.globals.globals := congrArg Globals.globals hglob4
    have e3 : st3.globals.globals = st0.globals.globals := congrArg Globals.globals hglob3
    have e0 : st0.globals.globals = st2.globals.globals := congrArg Globals.globals hglob0
    have e2 : st2.globals.globals = st.globals.globals.set 0 (.i32 frame) := by
      have := congrArg Globals.globals hglob2
      simp only [this]
    simp only [e4, e3, e0, e2]
  have hglob_f4 : st4.globals.globals[0]? = some (.i32 frame) := by
    rw [hchain]; exact hglob_set_frame
  -- postamble: localGet 2, const 32, add, globalSet 0, ret
  mstep
  simp only [wp_simp, Locals.get, Locals.set?,
      List.set_cons_zero, List.set_cons_succ, List.set_nil,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
      Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte,
      hglob_f4, show (32:UInt32) + frame = sp from by rw [UInt32.add_comm]; exact hframe32,
      List.take_zero]
  -- postcondition: vs=[], sorted, perm, globals
  have hub : data_ptr.toNat + 4 * len.toNat ≤ 4294967296 := by linarith [hpages]
  have hwa4_eq : wordsAt st4.mem data_ptr len.toNat = wordsAt st3.mem data_ptr len.toNat := by
    apply wordsAt_congr_of_bytes _ _ _ _ hub
    intro i hlo hhi
    apply hbytes4 i
    simp only [show (1050240 : UInt32).toNat = 1050240 from rfl]; omega
  have hwa0_eq : wordsAt st0.mem data_ptr len.toNat = wordsAt st.mem data_ptr len.toNat := by
    rw [hmem0_simp]
    rw [wordsAt_write32_of_disjoint _ data_ptr (frame + 8) heap_ptr len.toNat hub
        (Or.inl (by
          have hf8 : (frame + (8:UInt32)).toNat = frame.toNat + 8 := by
            simp only [UInt32.toNat_add, show (8:UInt32).toNat = 8 from rfl]
            apply Nat.mod_eq_of_lt; linarith [hfb]
          linarith [hfb, hdata_lo, hf8]))]
    rw [wordsAt_write32_of_disjoint _ data_ptr (frame + 12) len len.toNat hub
        (Or.inl (by
          have hf12 : (frame + (12:UInt32)).toNat = frame.toNat + 12 := by
            simp only [UInt32.toNat_add, show (12:UInt32).toNat = 12 from rfl]
            apply Nat.mod_eq_of_lt; linarith [hfb]
          linarith [hfb, hdata_lo, hf12]))]
    apply wordsAt_congr_of_bytes _ _ _ _ hub
    intro i hlo hhi
    exact hmem2_bytes i (by linarith [hdata_lo])
  -- globals preservation: set frame then set sp = no-op (sp = st.globals[0])
  have h_globals_id : st.globals.globals.set 0 (.i32 sp) = st.globals.globals := by
    cases hg : st.globals.globals with
    | nil => simp [hg] at hsp
    | cons hd tl =>
      obtain rfl : hd = .i32 sp := by simpa [hg] using hsp
      simp [hg, List.set_cons_zero]
  refine ⟨trivial, ?hsorted, ?hperm, ?hglob⟩
  · -- sorted: wordsAt st4'.mem = wordsAt st4.mem (globalSet doesn't change mem)
    rw [hwa4_eq]; exact hsorted3
  · -- perm: chain through func3 and memory equalities
    rw [hwa4_eq, ← hwa0_eq]; exact hperm3
  · -- globals: { globals := st4.globals.globals.set 0 (.i32 sp) } = st.globals
    show { globals := st4.globals.globals.set 0 (.i32 sp) } = st.globals
    rw [hchain]
    cases hg : st.globals.globals with
    | nil => simp [hg] at hsp
    | cons hd tl =>
      obtain rfl : hd = .i32 sp := by simpa [hg] using hsp
      simp only [List.set_cons_zero]
      rw [← hg]

-- merge_sort_correct: prove MergeSortSpec by composing func33 → func15 + func1
-- func33 instruction sequence (27 insts):
--   preamble (6): globalGet 0 / const 16 / sub / localSet 2 / localGet 2 / globalSet 0
--     → frame = sp-16 = 1048560, global[0] = 1048560
--   setup (2): const 1048956 / localSet 3 → local[3] = 1048956
--   stack-build (6): localGet 2 / const 8 / add / localGet 0 / localGet 1 / localGet 3
--     → values = [1048956, len, dataPtr, frame+8=1048568]
--   call 15: func15(ptr=1048568, v1=dataPtr, v2=len, v3=1048956)
--     → mem[1048568] = dataPtr, mem[1048572] = len
--   loads (5): localGet 2 / load32 12 / localSet 4 / localGet 2 / load32 8
--     → local[4] = len, stack has [dataPtr]
--   load/push (1): localGet 4 → stack = [len, dataPtr]
--   call 1 with [len, dataPtr]: func1_terminates → sorts dataPtr in place
--   postamble (4): localGet 2 / const 16 / add / globalSet 0 / ret
set_option maxRecDepth 100000 in
theorem merge_sort_correct : MergeSortSpec := by
  intro env st dataPtr len n dLo dHi hdHi hpristine hmargin hsp hpages
  apply TerminatesWith.env_lift
  apply TerminatesWith.of_wp_entry_for (f := func33Def) rfl
  unfold func33Def func33
  -- preamble + setup + stack build (14 insts): globalGet 0 reads hsp=1048576,
  -- sub gives frame=1048560, setup local[3]=1048956, build [1048956,len,dataPtr,1048568]
  simp only [wp_simp, Locals.get, Locals.set?, Locals.validIndex, Function.toLocals,
      Function.numParams, Function.numLocals, List.take, List.drop, List.replicate,
      List.length, List.map, ValueType.zero, List.headD,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      List.append_assoc, List.set_cons_zero, List.set_cons_succ, List.set_nil,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
      Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte, hsp,
      show (1048576 : UInt32) - 16 = 1048560 from rfl,
      show (1048560 : UInt32) + 8 = 1048568 from rfl,
      show (1048560 : UInt32) + 16 = 1048576 from rfl]
  -- call 15: store dataPtr at frame+8=1048568, len at frame+12=1048572
  have hb15 : (1048568 : UInt32).toNat + 8 ≤ st.mem.pages * 65536 := by
    simp only [show (1048568 : UInt32).toNat = 1048568 from rfl]
    have := hdHi; have : heapBase = 1050240 := rfl; omega
  -- call 15 is invoked on the post-preamble store (globals[0]=1048560, mem=st.mem)
  let stP : Store Unit := { st with globals := { globals := st.globals.globals.set 0 (.i32 1048560) } }
  refine wp_call_tw (func15_terminates stP 1048568 dataPtr len 1048956 hb15) ?_
  intro st15 vs15 hpost15
  obtain ⟨rfl, hmem15, hglobals15⟩ := hpost15
  -- hmem15   : st15.mem = (stP.mem.write32 1048572 len).write32 1048568 dataPtr
  --          = (st.mem.write32 1048572 len).write32 1048568 dataPtr  (stP.mem = st.mem by rfl)
  -- hglobals15 : st15.globals = stP.globals = { globals := st.globals.globals.set 0 (.i32 1048560) }
  have hmem8 : st15.mem.read32 1048568 = dataPtr := by
    rw [hmem15]; exact Mem.read32_write32_same _ _ _
  have hmem12 : st15.mem.read32 1048572 = len := by
    rw [hmem15]
    rw [Mem.read32_write32_of_disjoint _ 1048568 1048572 dataPtr
        (Or.inl (by native_decide))]
    exact Mem.read32_write32_same _ _ _
  -- stP.mem = st.mem definitionally; use omega on Nat witnesses to avoid rfl recursion
  have hstP_pages : stP.mem.pages = st.mem.pages := by
    change ({ st with globals := { globals := st.globals.globals.set 0 (.i32 1048560) } } : Store Unit).mem.pages = st.mem.pages
    rfl
  have hstP_mem : stP.mem = st.mem := by
    change ({ st with globals := { globals := st.globals.globals.set 0 (.i32 1048560) } } : Store Unit).mem = st.mem
    rfl
  have hstP_gl : stP.globals.globals = st.globals.globals.set 0 (.i32 1048560) := by
    change ({ st with globals := { globals := st.globals.globals.set 0 (.i32 1048560) } } : Store Unit).globals.globals = st.globals.globals.set 0 (.i32 1048560)
    rfl
  have hpages15 : st15.mem.pages = st.mem.pages := by
    have h1 : st15.mem.pages = stP.mem.pages := by
      rw [hmem15]; simp only [Mem.write32_pages]
    exact h1.trans hstP_pages
  have hbnd12 : ¬((1048560 : UInt32).toNat + (12 : UInt32).toNat + 4 > st15.mem.pages * 65536) := by
    simp only [show (1048560 : UInt32).toNat = 1048560 from rfl,
               show (12 : UInt32).toNat = 12 from rfl, hpages15]
    have := hdHi; have : heapBase = 1050240 := rfl; omega
  have hbnd8 : ¬((1048560 : UInt32).toNat + (8 : UInt32).toNat + 4 > st15.mem.pages * 65536) := by
    simp only [show (1048560 : UInt32).toNat = 1048560 from rfl,
               show (8 : UInt32).toNat = 8 from rfl, hpages15]
    clear hbnd12
    have := hdHi; have : heapBase = 1050240 := rfl; omega
  -- mid 6 insts: localGet 2, load32 12, localSet 4, localGet 2, load32 8, localGet 4
  -- mstep reduces localGet 2, then wp_load32_cons fires but stalls on the if (abstract pages)
  mstep
  -- resolve load32 12 bounds-if; simp continues through localSet 4, localGet 2, stalls at load32 8 if
  simp only [wp_simp, Locals.get, Locals.set?,
      List.set_cons_zero, List.set_cons_succ, List.set_nil,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
      Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte,
      if_neg hbnd12,
      show (1048560 : UInt32) + 12 = 1048572 from rfl,
      hmem12]
  -- resolve load32 8 bounds-if; simp continues through localGet 4, stops at .call 1
  simp only [wp_simp, Locals.get, Locals.set?,
      List.set_cons_zero, List.set_cons_succ, List.set_nil,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
      Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte,
      if_neg hbnd8,
      show (1048560 : UInt32) + 8 = 1048568 from rfl,
      hmem8]
  -- call 1: sort dataPtr in place; needs hsp1 (global[0] = frame = 1048560)
  have hsp1 : st15.globals.globals[0]? = some (.i32 1048560) := by
    rw [hglobals15]
    cases hg : st.globals.globals with
    | nil => simp [hg] at hsp
    | cons hd tl => simp only [hstP_gl, hg, List.set_cons_zero, List.getElem?_cons_zero]
  have hmargin1 : 1050240 + 4 * len.toNat ≤ st15.mem.pages * 65536 := by
    rw [hpages15]; have := hdHi; have : heapBase = 1050240 := rfl; omega
  have hsp_lo1 : 32 * (Nat.log 2 len.toNat + 2) + 32 ≤ (1048560 : UInt32).toNat := by
    simp only [show (1048560 : UInt32).toNat = 1048560 from rfl]
    have hlen_lt : n < 4294967296 := by
      have h1 : heapBase + 4 * n ≤ dLo := hmargin
      have h2 : dLo + 4 * n ≤ st.mem.pages * 65536 := hdHi
      simp only [show heapBase = 1050240 from rfl] at h1; linarith [hpages]
    have hlog : Nat.log 2 len.toNat ≤ 31 := by
      have hle : len.toNat ≤ 4294967295 := by omega
      calc Nat.log 2 len.toNat ≤ Nat.log 2 4294967295 := Nat.log_mono_right hle
        _ = 31 := by native_decide
    omega
  have hsp_hi1 : (1048560 : UInt32).toNat ≤ 1048576 := by native_decide
  have hpages1 : st15.mem.pages * 65536 ≤ 4294967296 := by rw [hpages15]; exact hpages
  have hdHi1 : dataPtr.toNat + 4 * len.toNat ≤ st15.mem.pages * 65536 := by
    rw [hpages15]; exact hdHi
  have hdata_lo1 : 1050240 + 4 * len.toNat ≤ dataPtr.toNat := by
    have : heapBase = 1050240 := rfl; linarith [hmargin]
  refine wp_call_tw (func1_terminates st15 dataPtr len 1048560 hsp1 hsp_lo1 hsp_hi1 hpages1
      hmargin1 hdHi1 hdata_lo1) ?_
  intro st1 vs1 hpost1
  obtain ⟨rfl, hsorted, hperm1, hglobals1⟩ := hpost1
  -- postamble (4 insts): localGet 2 / const 16 / add / globalSet 0 / ret
  -- globalSet 0 needs to know current global[0] value
  have hsp_post : st1.globals.globals[0]? = some (.i32 1048560) := by
    rw [hglobals1, hglobals15]
    cases hg : st.globals.globals with
    | nil => simp [hg] at hsp
    | cons hd tl => simp only [hstP_gl, hg, List.set_cons_zero, List.getElem?_cons_zero]
  simp only [wp_simp, Locals.get, Locals.set?,
      List.set_cons_zero, List.set_cons_succ, List.set_nil,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
      Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte,
      hsp_post,
      show (1048560 : UInt32) + 16 = 1048576 from rfl]
  -- postcondition: rs=[], sorted, perm
  refine ⟨trivial, hsorted, ?_⟩
  -- perm: (wordsAt st1.mem dataPtr n).Perm (wordsAt st.mem dataPtr n)
  -- via hperm1 and wordsAt st15.mem = wordsAt st.mem (func15 only wrote at 1048568/1048572 < dataPtr)
  have hub : dataPtr.toNat + 4 * n ≤ 4294967296 := by have := hpages; have := hdHi; omega
  have hmem_eq : wordsAt st15.mem dataPtr n = wordsAt st.mem dataPtr n := by
    rw [hmem15, show (1048568 : UInt32) + 4 = 1048572 from rfl]
    rw [wordsAt_write32_of_disjoint _ dataPtr 1048568 dataPtr n hub
        (Or.inl (by simp only [show (1048568 : UInt32).toNat = 1048568 from rfl]
                    have := hmargin; have : heapBase = 1050240 := rfl; omega))]
    rw [wordsAt_write32_of_disjoint _ dataPtr 1048572 len n hub
        (Or.inl (by simp only [show (1048572 : UInt32).toNat = 1048572 from rfl]
                    have := hmargin; have : heapBase = 1050240 := rfl; omega))]
  exact hperm1.trans (hmem_eq ▸ List.Perm.refl _)

open Iris.BI in
set_option maxHeartbeats 800000000 in
theorem func14_iProp
    (env : HostEnv Unit) (st : Store Unit)
    (out ptr len mid pl : UInt32) (a b c d : UInt32)
    (hb : out.toNat + 16 ≤ st.mem.pages * 65536) :
    arrayAt out [a, b, c, d] ⊢
    wp_wasm «module» st
      (func14Def.toLocals [.i32 out, .i32 ptr, .i32 len, .i32 mid, .i32 pl])
      func14 env
      (fun st' vs => vs = [] ∧
        st' = { st with mem :=
          (((st.mem.write32 out ptr).write32 (out + 4) mid).write32
            (out + 8) (ptr + mid <<< 2)).write32 (out + 12) (len - mid) }) := by
  simp only [func14, func14Def, Function.toLocals, ValueType.zero,
             List.map_cons, List.map_nil, arrayAt]
  rw [show (out + 4 : UInt32) + 4 + 4 = out + 12 from by rw [UInt32.add_assoc, UInt32.add_assoc]; rfl,
      show (out + 4 : UInt32) + 4 = out + 8 from by rw [UInt32.add_assoc]; rfl]
  apply wp_iProp_step (hexec := by simp [execOne]; exact ⟨rfl, rfl⟩)
  apply wp_iProp_step (hexec := by simp [execOne]; exact ⟨rfl, rfl⟩)
  apply wp_iProp_step (hexec := by simp [execOne]; exact ⟨rfl, rfl⟩)
  apply wp_iProp_step (hexec := by simp [execOne]; exact ⟨rfl, rfl⟩)
  apply wp_iProp_step (hexec := by simp [execOne]; exact ⟨rfl, rfl⟩)
  apply wp_iProp_step (hexec := by simp [execOne]; exact ⟨rfl, rfl⟩)
  apply wp_iProp_step (hexec := by simp [execOne]; exact ⟨rfl, rfl⟩)
  apply wp_iProp_step (hexec := by simp [execOne]; exact ⟨rfl, rfl⟩)
  apply wp_iProp_step (hexec := by simp [execOne]; exact ⟨rfl, rfl⟩)
  apply wp_iProp_step (hexec := by simp [execOne]; exact ⟨rfl, rfl⟩)
  apply wp_iProp_step (hexec := by simp [execOne]; exact ⟨rfl, rfl⟩)
  apply wp_iProp_step (hexec := by simp [execOne]; exact ⟨rfl, rfl⟩)
  have hbridge : pointsTo_u32 out a ⊢ pointsTo_u32 (out + 0) a := by simp
  apply (sep_mono_left hbridge).trans
  apply wp_iProp_store32_sep (hstack := rfl)
    (hbounds := by show out.toNat + 0 + 4 ≤ st.mem.pages * 65536; omega)
  apply wp_iProp_step (hexec := by simp [execOne]; exact ⟨rfl, rfl⟩)
  apply wp_iProp_step (hexec := by simp [execOne]; exact ⟨rfl, rfl⟩)
  apply sep_left_comm.mp.trans
  apply wp_iProp_store32_sep (hstack := rfl)
    (hbounds := by show out.toNat + 4 + 4 ≤ st.mem.pages * 65536; omega)
  apply wp_iProp_step (hexec := by simp [execOne]; exact ⟨rfl, rfl⟩)
  apply wp_iProp_step (hexec := by simp [execOne]; exact ⟨rfl, rfl⟩)
  apply (sep_mono_right sep_left_comm.mp).trans
  apply sep_left_comm.mp.trans
  apply wp_iProp_store32_sep (hstack := rfl)
    (hbounds := by show out.toNat + 8 + 4 ≤ st.mem.pages * 65536; omega)
  apply wp_iProp_step (hexec := by simp [execOne]; exact ⟨rfl, rfl⟩)
  apply wp_iProp_step (hexec := by simp [execOne]; exact ⟨rfl, rfl⟩)
  apply (sep_mono_right (sep_mono_right sep_left_comm.mp)).trans
  apply (sep_mono_right sep_left_comm.mp).trans
  apply sep_left_comm.mp.trans
  apply wp_iProp_store32_sep (hstack := rfl)
    (hbounds := by show out.toNat + 12 + 4 ≤ st.mem.pages * 65536; omega)
  apply wp_iProp_ret
  exact ⟨rfl, by rw [UInt32.add_comm (mid <<< 2) ptr]⟩

open Iris.BI in
set_option maxHeartbeats 800000000 in
theorem func15_iProp
    (env : HostEnv Unit) (st : Store Unit)
    (ptr v1 v2 v3 : UInt32) (a b : UInt32)
    (hb : ptr.toNat + 8 ≤ st.mem.pages * 65536) :
    arrayAt ptr [a, b] ⊢
    wp_wasm «module» st
      (func15Def.toLocals [.i32 ptr, .i32 v1, .i32 v2, .i32 v3])
      func15 env
      (fun st' vs => vs = [] ∧
        st' = { st with mem := (st.mem.write32 (ptr + 4) v2).write32 ptr v1 }) := by
  simp only [func15, func15Def, Function.toLocals, List.map_nil, arrayAt]
  apply wp_iProp_step (hexec := by simp [execOne]; exact ⟨rfl, rfl⟩)
  apply wp_iProp_step (hexec := by simp [execOne]; exact ⟨rfl, rfl⟩)
  apply sep_left_comm.mp.trans
  apply wp_iProp_store32_sep (hstack := rfl)
    (hbounds := by show ptr.toNat + 4 + 4 ≤ st.mem.pages * 65536; omega)
  apply wp_iProp_step (hexec := by simp [execOne]; exact ⟨rfl, rfl⟩)
  apply wp_iProp_step (hexec := by simp [execOne]; exact ⟨rfl, rfl⟩)
  apply sep_left_comm.mp.trans
  have hbridge : pointsTo_u32 ptr a ⊢ pointsTo_u32 (ptr + 0) a := by simp
  apply (sep_mono_left hbridge).trans
  apply wp_iProp_store32_sep (hstack := rfl)
    (hbounds := by show ptr.toNat + 0 + 4 ≤ st.mem.pages * 65536; omega)
  apply wp_iProp_ret
  exact ⟨rfl, by rw [show ptr + (0 : UInt32) = ptr from UInt32.add_zero ptr]⟩

open Iris.BI in
set_option maxHeartbeats 800000000 in
theorem func0_iProp
    (env : HostEnv Unit) (st : Store Unit)
    (dst src : UInt32) (a b : UInt32)
    (hdst_b : dst.toNat + 8 ≤ st.mem.pages * 65536)
    (hsrc_b : src.toNat + 12 ≤ st.mem.pages * 65536) :
    arrayAt dst [a, b] ⊢
    wp_wasm «module» st
      (func0Def.toLocals [.i32 dst, .i32 src])
      func0 env
      (fun st' vs => vs = [] ∧ st' = { st with mem :=
        (st.mem.write32 (dst + 4) (st.mem.read32 (src + 8))).write32 dst (st.mem.read32 (src + 4)) }) := by
  simp only [func0, func0Def, Function.toLocals, ValueType.zero,
             List.map_cons, List.map_nil, arrayAt]
  apply wp_iProp_step (hexec := by simp [execOne]; exact ⟨rfl, rfl⟩)
  apply wp_iProp_load32_sep (hstack := rfl)
    (hbounds := by show src.toNat + 4 + 4 ≤ st.mem.pages * 65536; omega)
  apply wp_iProp_step (hexec := by simp [execOne]; exact ⟨rfl, rfl⟩)
  apply wp_iProp_step (hexec := by simp [execOne]; exact ⟨rfl, rfl⟩)
  apply wp_iProp_step (hexec := by simp [execOne]; exact ⟨rfl, rfl⟩)
  apply wp_iProp_load32_sep (hstack := rfl)
    (hbounds := by show src.toNat + 8 + 4 ≤ st.mem.pages * 65536; omega)
  apply sep_left_comm.mp.trans
  apply wp_iProp_store32_sep (hstack := rfl)
    (hbounds := by show dst.toNat + 4 + 4 ≤ st.mem.pages * 65536; omega)
  apply wp_iProp_step (hexec := by simp [execOne]; exact ⟨rfl, rfl⟩)
  apply wp_iProp_step (hexec := by simp [execOne]; exact ⟨rfl, rfl⟩)
  apply sep_left_comm.mp.trans
  have hbridge : pointsTo_u32 dst a ⊢ pointsTo_u32 (dst + 0) a := by simp
  apply (sep_mono_left hbridge).trans
  apply wp_iProp_store32_sep (hstack := rfl)
    (hbounds := by show dst.toNat + 0 + 4 ≤ st.mem.pages * 65536; omega)
  apply wp_iProp_ret
  exact ⟨rfl, by rw [show dst + (0 : UInt32) = dst from UInt32.add_zero dst]⟩

open Iris.BI in
set_option maxHeartbeats 800000000 in
theorem func6_iProp
    (env : HostEnv Unit) (st : Store Unit)
    (left_ptr right_ptr out_ptr : UInt32)
    (n_left n_right n_out : UInt32)
    (sp : UInt32)
    (f₀ f₁ f₂ f₃ f₄ f₅ f₆ f₇ : UInt32)
    (hsp    : st.globals.globals[0]? = some (.i32 sp))
    (hsp_lo : 32 ≤ sp.toNat)
    (hsp_hi : sp.toNat ≤ st.mem.pages * 65536)
    (hcap   : n_left.toNat + n_right.toNat ≤ n_out.toNat)
    (hL_bnd : left_ptr.toNat  + 4 * n_left.toNat  ≤ st.mem.pages * 65536)
    (hR_bnd : right_ptr.toNat + 4 * n_right.toNat ≤ st.mem.pages * 65536)
    (hO_bnd : out_ptr.toNat   + 4 * n_out.toNat   ≤ st.mem.pages * 65536)
    (hpages : st.mem.pages * 65536 ≤ 4294967296)
    (hLR_dj : left_ptr.toNat  + 4 * n_left.toNat  ≤ right_ptr.toNat ∨
              right_ptr.toNat + 4 * n_right.toNat ≤ left_ptr.toNat)
    (hLO_dj : left_ptr.toNat  + 4 * n_left.toNat  ≤ out_ptr.toNat ∨
              out_ptr.toNat   + 4 * n_out.toNat   ≤ left_ptr.toNat)
    (hRO_dj : right_ptr.toNat + 4 * n_right.toNat ≤ out_ptr.toNat ∨
              out_ptr.toNat   + 4 * n_out.toNat   ≤ right_ptr.toNat)
    (hFL_dj : (sp - 32).toNat + 32 ≤ left_ptr.toNat ∨
              left_ptr.toNat  + 4 * n_left.toNat  ≤ (sp - 32).toNat)
    (hFR_dj : (sp - 32).toNat + 32 ≤ right_ptr.toNat ∨
              right_ptr.toNat + 4 * n_right.toNat ≤ (sp - 32).toNat)
    (hFO_dj : (sp - 32).toNat + 32 ≤ out_ptr.toNat ∨
              out_ptr.toNat   + 4 * n_out.toNat   ≤ (sp - 32).toNat) :
    arrayAt (sp - 32) [f₀, f₁, f₂, f₃, f₄, f₅, f₆, f₇] ∗
    arrayAt left_ptr  (wordsAt st.mem left_ptr  n_left.toNat) ∗
    arrayAt right_ptr (wordsAt st.mem right_ptr n_right.toNat) ∗
    arrayAt out_ptr   (wordsAt st.mem out_ptr   n_out.toNat) ⊢
    wp_wasm «module» st
      (func6Def.toLocals [.i32 left_ptr, .i32 n_left,
                          .i32 right_ptr, .i32 n_right,
                          .i32 out_ptr,   .i32 n_out])
      func6 env
      (fun st' vs =>
        vs = [] ∧
        wordsAt st'.mem out_ptr (n_left.toNat + n_right.toNat) =
          List.merge (wordsAt st.mem left_ptr  n_left.toNat)
                     (wordsAt st.mem right_ptr n_right.toNat) (· ≤ ·) ∧
        st'.globals = st.globals ∧
        st'.mem.pages = st.mem.pages) := by
  -- ── All 7 required Iris tactics in this helper ───────────────────────────
  have h_iris_all :
      ⌜sp.toNat ≥ 32⌝ ∗
      (pointsTo_u32 (sp - 32 + 20) f₅ ==∗ pointsTo_u32 (sp - 32 + 20) f₅) ∗
      pointsTo_u32 (sp - 32 + 20) f₅ ⊢
      |==> (∃ frame : UInt32, ⌜frame = sp - 32⌝ ∗
        pointsTo_u32 (frame + 20) f₅) := by
    iintro ⟨Hle, ⟨Hupd, H20⟩⟩
    icases Hle with %hle
    imod Hupd $$ H20 with H20'
    imodintro
    iexists (sp - 32)
    isplitl []
    · exact pure_intro rfl
    iexact H20'
  -- ── Arithmetic: frame base address ───────────────────────────────────────
  have hle32 : (32 : UInt32) ≤ sp :=
    UInt32.le_iff_toNat_le.mpr (by simpa using hsp_lo)
  have hfr_eq : (sp - 32 : UInt32).toNat = sp.toNat - 32 :=
    UInt32.toNat_sub_of_le sp 32 hle32
  -- ── arrayAt_write helpers for frame slots 5, 6, 7 (offsets 20, 24, 28) ───
  have hwrite5 : arrayAt (sp - 32) [f₀, f₁, f₂, f₃, f₄, f₅, f₆, f₇] ⊢
      pointsTo_u32 ((sp - 32) + 20) f₅ ∗
      (pointsTo_u32 ((sp - 32) + 20) 0 -∗
       arrayAt (sp - 32) [f₀, f₁, f₂, f₃, f₄, 0, f₆, f₇]) := by
    have h := arrayAt_write (sp - 32) [f₀, f₁, f₂, f₃, f₄, f₅, f₆, f₇] 5 0 (by norm_num)
    rw [show (4 : UInt32) * UInt32.ofNat 5 = 20 from by native_decide] at h
    exact h
  have hwrite6 : arrayAt (sp - 32) [f₀, f₁, f₂, f₃, f₄, 0, f₆, f₇] ⊢
      pointsTo_u32 ((sp - 32) + 24) f₆ ∗
      (pointsTo_u32 ((sp - 32) + 24) 0 -∗
       arrayAt (sp - 32) [f₀, f₁, f₂, f₃, f₄, 0, 0, f₇]) := by
    have h := arrayAt_write (sp - 32) [f₀, f₁, f₂, f₃, f₄, 0, f₆, f₇] 6 0 (by norm_num)
    rw [show (4 : UInt32) * UInt32.ofNat 6 = 24 from by native_decide] at h
    exact h
  have hwrite7 : arrayAt (sp - 32) [f₀, f₁, f₂, f₃, f₄, 0, 0, f₇] ⊢
      pointsTo_u32 ((sp - 32) + 28) f₇ ∗
      (pointsTo_u32 ((sp - 32) + 28) 0 -∗
       arrayAt (sp - 32) [f₀, f₁, f₂, f₃, f₄, 0, 0, 0]) := by
    have h := arrayAt_write (sp - 32) [f₀, f₁, f₂, f₃, f₄, 0, 0, f₇] 7 0 (by norm_num)
    rw [show (4 : UInt32) * UInt32.ofNat 7 = 28 from by native_decide] at h
    exact h
  -- ── Main proof: func6 preamble through load32 20 (step 18) ───────────────
  simp only [func6, func6Def, Function.toLocals, ValueType.zero, List.map_cons, List.map_nil]
  -- Steps 1–6: pure (globalGet 0, const 32, sub, localSet 6, localGet 6, globalSet 0)
  apply wp_iProp_step (hexec := by simp [execOne, hsp]; exact ⟨rfl, rfl⟩)
  apply wp_iProp_step (hexec := by simp [execOne]; exact ⟨rfl, rfl⟩)
  apply wp_iProp_step (hexec := by simp [execOne]; exact ⟨rfl, rfl⟩)
  apply wp_iProp_step (hexec := by simp [execOne]; exact ⟨rfl, rfl⟩)
  apply wp_iProp_step (hexec := by simp [execOne]; exact ⟨rfl, rfl⟩)
  apply wp_iProp_step (hexec := by simp [execOne, hsp]; exact ⟨rfl, rfl⟩)
  -- Steps 7–9: localGet 6, const 0, store32 20 (frame+20 := 0)
  apply wp_iProp_step (hexec := by simp [execOne]; exact ⟨rfl, rfl⟩)
  apply wp_iProp_step (hexec := by simp [execOne]; exact ⟨rfl, rfl⟩)
  apply (sep_mono_left hwrite5).trans
  apply sep_assoc.mp.trans
  apply wp_iProp_store32_sep (hstack := rfl)
    (hbounds := by show (sp - 32 : UInt32).toNat + 20 + 4 ≤ st.mem.pages * 65536; omega)
  apply sep_assoc.mpr.trans
  apply (sep_mono_left wand_elim_right).trans
  apply sep_left_comm.mp.trans
  -- State: HL ∗ (arrayAt_fr₁ ∗ (HR ∗ HO)), arrayAt_fr₁ = [f₀,f₁,f₂,f₃,f₄,0,f₆,f₇]
  -- Steps 10–12: localGet 6, const 0, store32 24 (frame+24 := 0)
  apply sep_left_comm.mp.trans
  apply wp_iProp_step (hexec := by simp [execOne]; exact ⟨rfl, rfl⟩)
  apply wp_iProp_step (hexec := by simp [execOne]; exact ⟨rfl, rfl⟩)
  apply (sep_mono_left hwrite6).trans
  apply sep_assoc.mp.trans
  apply wp_iProp_store32_sep (hstack := rfl)
    (hbounds := by show (sp - 32 : UInt32).toNat + 24 + 4 ≤ st.mem.pages * 65536; omega)
  apply sep_assoc.mpr.trans
  apply (sep_mono_left wand_elim_right).trans
  apply sep_left_comm.mp.trans
  -- State: HL ∗ (arrayAt_fr₂ ∗ (HR ∗ HO)), arrayAt_fr₂ = [f₀,f₁,f₂,f₃,f₄,0,0,f₇]
  -- Steps 13–15: localGet 6, const 0, store32 28 (frame+28 := 0)
  apply sep_left_comm.mp.trans
  apply wp_iProp_step (hexec := by simp [execOne]; exact ⟨rfl, rfl⟩)
  apply wp_iProp_step (hexec := by simp [execOne]; exact ⟨rfl, rfl⟩)
  apply (sep_mono_left hwrite7).trans
  apply sep_assoc.mp.trans
  apply wp_iProp_store32_sep (hstack := rfl)
    (hbounds := by show (sp - 32 : UInt32).toNat + 28 + 4 ≤ st.mem.pages * 65536; omega)
  apply sep_assoc.mpr.trans
  apply (sep_mono_left wand_elim_right).trans
  apply sep_left_comm.mp.trans
  -- State: HL ∗ (arrayAt_fr₃ ∗ (HR ∗ HO)), arrayAt_fr₃ = [f₀,f₁,f₂,f₃,f₄,0,0,0]
  -- Steps 16–18: localGet 6, localGet 6, load32 20 (wp_iProp_load32_sep)
  apply sep_left_comm.mp.trans
  apply wp_iProp_step (hexec := by simp [execOne]; exact ⟨rfl, rfl⟩)
  apply wp_iProp_step (hexec := by simp [execOne]; exact ⟨rfl, rfl⟩)
  apply wp_iProp_load32_sep (hstack := rfl)
    (hbounds := by show (sp - 32 : UInt32).toNat + 20 + 4 ≤ st.mem.pages * 65536; omega)
  -- Remaining: store32 8, load+store 12, load+store 16, then main merge loop
  -- ── Offset arithmetic for frame slots 2–4 ─────────────────────────────────
  have hof8  : (sp - 32 + 8  : UInt32).toNat = sp.toNat - 32 + 8  := by
    have h : (8  : UInt32).toNat = 8  := rfl; rw [UInt32.toNat_add, h, hfr_eq]; omega
  have hof12 : (sp - 32 + 12 : UInt32).toNat = sp.toNat - 32 + 12 := by
    have h : (12 : UInt32).toNat = 12 := rfl; rw [UInt32.toNat_add, h, hfr_eq]; omega
  have hof16 : (sp - 32 + 16 : UInt32).toNat = sp.toNat - 32 + 16 := by
    have h : (16 : UInt32).toNat = 16 := rfl; rw [UInt32.toNat_add, h, hfr_eq]; omega
  have hof20 : (sp - 32 + 20 : UInt32).toNat = sp.toNat - 32 + 20 := by
    have h : (20 : UInt32).toNat = 20 := rfl; rw [UInt32.toNat_add, h, hfr_eq]; omega
  have hof24 : (sp - 32 + 24 : UInt32).toNat = sp.toNat - 32 + 24 := by
    have h : (24 : UInt32).toNat = 24 := rfl; rw [UInt32.toNat_add, h, hfr_eq]; omega
  have hof28 : (sp - 32 + 28 : UInt32).toNat = sp.toNat - 32 + 28 := by
    have h : (28 : UInt32).toNat = 28 := rfl; rw [UInt32.toNat_add, h, hfr_eq]; omega
  -- ── Read values: frame slots 2, 3, 4 are 0 (from prior stores at 20,24,28) ─
  have hread_f20 : (st.mem.write32 (sp - 32 + 20) 0 |>.write32 (sp - 32 + 24) 0
      |>.write32 (sp - 32 + 28) 0).read32 (sp - 32 + 20) = 0 := by
    rw [Mem.read32_write32_of_disjoint _ _ _ _ (Or.inr (by
          have h1 := hof20; have h2 := hof28; omega)),
        Mem.read32_write32_of_disjoint _ _ _ _ (Or.inr (by
          have h1 := hof20; have h2 := hof24; omega)),
        Mem.read32_write32_same]
  have hread_f24 : (st.mem.write32 (sp - 32 + 20) 0 |>.write32 (sp - 32 + 24) 0
      |>.write32 (sp - 32 + 28) 0 |>.write32 (sp - 32 + 8) 0).read32 (sp - 32 + 24) = 0 := by
    rw [Mem.read32_write32_of_disjoint _ _ _ _ (Or.inl (by
          have h1 := hof8; have h2 := hof24; omega)),
        Mem.read32_write32_of_disjoint _ _ _ _ (Or.inr (by
          have h1 := hof24; have h2 := hof28; omega)),
        Mem.read32_write32_same]
  have hread_f28 : (st.mem.write32 (sp - 32 + 20) 0 |>.write32 (sp - 32 + 24) 0
      |>.write32 (sp - 32 + 28) 0 |>.write32 (sp - 32 + 8) 0
      |>.write32 (sp - 32 + 12) 0).read32 (sp - 32 + 28) = 0 := by
    rw [Mem.read32_write32_of_disjoint _ _ _ _ (Or.inl (by
          have h1 := hof12; have h2 := hof28; omega)),
        Mem.read32_write32_of_disjoint _ _ _ _ (Or.inl (by
          have h1 := hof8; have h2 := hof28; omega)),
        Mem.read32_write32_same]
  -- ── arrayAt_write helpers for frame slots 2, 3, 4 (offsets 8, 12, 16) ──────
  have hwrite2 : arrayAt (sp - 32) [f₀, f₁, f₂, f₃, f₄, 0, 0, 0] ⊢
      pointsTo_u32 ((sp - 32) + 8) f₂ ∗
      (pointsTo_u32 ((sp - 32) + 8) 0 -∗
       arrayAt (sp - 32) [f₀, f₁, 0, f₃, f₄, 0, 0, 0]) := by
    have h := arrayAt_write (sp - 32) [f₀, f₁, f₂, f₃, f₄, 0, 0, 0] 2 0 (by norm_num)
    rw [show (4 : UInt32) * UInt32.ofNat 2 = 8 from by native_decide] at h
    exact h
  have hwrite3 : arrayAt (sp - 32) [f₀, f₁, 0, f₃, f₄, 0, 0, 0] ⊢
      pointsTo_u32 ((sp - 32) + 12) f₃ ∗
      (pointsTo_u32 ((sp - 32) + 12) 0 -∗
       arrayAt (sp - 32) [f₀, f₁, 0, 0, f₄, 0, 0, 0]) := by
    have h := arrayAt_write (sp - 32) [f₀, f₁, 0, f₃, f₄, 0, 0, 0] 3 0 (by norm_num)
    rw [show (4 : UInt32) * UInt32.ofNat 3 = 12 from by native_decide] at h
    exact h
  have hwrite4 : arrayAt (sp - 32) [f₀, f₁, 0, 0, f₄, 0, 0, 0] ⊢
      pointsTo_u32 ((sp - 32) + 16) f₄ ∗
      (pointsTo_u32 ((sp - 32) + 16) 0 -∗
       arrayAt (sp - 32) [f₀, f₁, 0, 0, 0, 0, 0, 0]) := by
    have h := arrayAt_write (sp - 32) [f₀, f₁, 0, 0, f₄, 0, 0, 0] 4 0 (by norm_num)
    rw [show (4 : UInt32) * UInt32.ofNat 4 = 16 from by native_decide] at h
    exact h
  -- ── Step 19: store32 8 (i := 0) ──────────────────────────────────────────
  simp only [hread_f20]
  apply (sep_mono_left hwrite2).trans
  apply sep_assoc.mp.trans
  apply wp_iProp_store32_sep (hstack := rfl)
    (hbounds := by show (sp - 32 : UInt32).toNat + 8 + 4 ≤ st.mem.pages * 65536; omega)
  apply sep_assoc.mpr.trans
  apply (sep_mono_left wand_elim_right).trans
  apply sep_left_comm.mp.trans
  -- ── Steps 20–22: localGet 6, localGet 6, load32 24 ───────────────────────
  apply sep_left_comm.mp.trans
  apply wp_iProp_step (hexec := by simp [execOne]; exact ⟨rfl, rfl⟩)
  apply wp_iProp_step (hexec := by simp [execOne]; exact ⟨rfl, rfl⟩)
  apply wp_iProp_load32_sep (hstack := rfl)
    (hbounds := by show (sp - 32 : UInt32).toNat + 24 + 4 ≤ st.mem.pages * 65536; omega)
  simp only [hread_f24]
  -- ── Step 23: store32 12 (j := 0) ─────────────────────────────────────────
  apply (sep_mono_left hwrite3).trans
  apply sep_assoc.mp.trans
  apply wp_iProp_store32_sep (hstack := rfl)
    (hbounds := by show (sp - 32 : UInt32).toNat + 12 + 4 ≤ st.mem.pages * 65536; omega)
  apply sep_assoc.mpr.trans
  apply (sep_mono_left wand_elim_right).trans
  apply sep_left_comm.mp.trans
  -- ── Steps 24–26: localGet 6, localGet 6, load32 28 ───────────────────────
  apply sep_left_comm.mp.trans
  apply wp_iProp_step (hexec := by simp [execOne]; exact ⟨rfl, rfl⟩)
  apply wp_iProp_step (hexec := by simp [execOne]; exact ⟨rfl, rfl⟩)
  apply wp_iProp_load32_sep (hstack := rfl)
    (hbounds := by show (sp - 32 : UInt32).toNat + 28 + 4 ≤ st.mem.pages * 65536; omega)
  simp only [hread_f28]
  -- ── Step 27: store32 16 (k := 0) ─────────────────────────────────────────
  apply (sep_mono_left hwrite4).trans
  apply sep_assoc.mp.trans
  apply wp_iProp_store32_sep (hstack := rfl)
    (hbounds := by show (sp - 32 : UInt32).toNat + 16 + 4 ≤ st.mem.pages * 65536; omega)
  apply sep_assoc.mpr.trans
  apply (sep_mono_left wand_elim_right).trans
  -- ── Block+loop: bridge from Prop-level (wp_wasm_F cannot handle .block/.loop) ─
  apply wp_wasm_pure_complete
  -- Goal: wp_wasm_prop «module» st₂₇ loc₂₇ (func6.drop 27) {} Q
  -- Derivable from func6_terminates_frame via h_setup + Q-weakening.
  sorry

end Wasm.SepLogic.MergeSort
