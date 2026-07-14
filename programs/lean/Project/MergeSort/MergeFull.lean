import Project.MergeSort.ContentLemmas
import Project.MergeSort.MergeSepLogic
import Project.MergeSort.DrainSepLogic
import Project.MergeSort.OuterDrainSpec
import Project.MergeSort.Program
import CodeLib.SepLogic.Adequacy

namespace Wasm.SepLogic.MergeSort

open Wasm Project.MergeSort Project.MergeSort.Spec Project.MergeSort.Framing

variable [WasmHeapGS]

set_option maxHeartbeats 2000000 in
theorem func6_terminates
    (st : Store Unit)
    (left_ptr n_left right_ptr n_right out_ptr n_out sp : UInt32)
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
            (· ≤ ·)) := by
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
  -- BLOCKER: MergeLoopInv / DrainInv are `private` in MergeSepLogic / DrainSepLogic.
  -- Constructing the invariant or applying main_merge_loop_spec / right_drain_spec
  -- from outside those files requires making those types public first.
  -- NOTE: postcondition uses n_out.toNat, but func6 only writes n_left+n_right elements.
  -- wordsAt has length n_out.toNat while List.merge has length n_left+n_right; for equality
  -- to hold we need n_out.toNat = n_left.toNat + n_right.toNat (hcap gives only ≤).
  -- Recommend changing the postcondition to (n_left.toNat + n_right.toNat) or hcap to =.
  --
  -- BLOCKERS preventing this sorry from being filled:
  --
  -- (1) main_merge_loop_spec (MergeSepLogic.lean:223) returns only the WEAK exit condition
  --     (read32(frame+8)=n_left ∨ read32(frame+12)=n_right). It does NOT return
  --     MergeLoopInv at exit, so the content written to out[0..k-1] is unknown.
  --     Fix: add a theorem main_merge_loop_spec_with_inv to MergeSepLogic.lean that also
  --     returns MergeLoopInv in the postcondition. The exit cases (lines 1869–1944) already
  --     have `hI : MergeLoopInv stA locA` available; just add ∧ hI to those two conclusions.
  --     The iteration cases thread through automatically since IH gives the stronger result.
  --
  -- (2) rightDrainBody (DrainSepLogic.lean:31) and leftDrainBody (line 798) are private,
  --     so right_drain_spec and left_drain_spec cannot be invoked from this file: their
  --     conclusions reference private terms that cannot be constructed or matched externally.
  --     Fix A: make rightDrainBody and leftDrainBody non-private.
  --     Fix B (cleaner): add outer_drain_spec to DrainSepLogic.lean that takes
  --       MergeLoopInv at exit + exit condition and proves the outer drain loop
  --       (.loop 0 0 outerDrainBody, lines 480–632 of Program.lean) fills
  --       wordsAt out_ptr (n_left+n_right) = merge left right using right_drain_spec /
  --       left_drain_spec internally.
  --
  -- (3) DrainInv (DrainSepLogic.lean:78) and LeftDrainInv (line 830) are private,
  --     so they cannot be constructed from this file to discharge the hypotheses of
  --     right_drain_spec / left_drain_spec even if (2) is resolved.
  --     Fix: remove private from both defs in DrainSepLogic.lean.
  --
  -- PROOF SKETCH once blockers are resolved:
  --   1. Apply main_merge_loop_spec_with_inv to get MergeLoopInv at exit + exit_cond.
  --   2. Apply wp_wasm_prop_block to split func6.drop 27 at the main merge block.
  --   3. Apply outer_drain_spec (or wp_wasm_prop_loop with inline OuterDrainInv) for
  --      the outer drain loop (.loop 0 0 [...], Program.lean line 480).
  --   4. In Return case (j=n_right, i=n_left): content invariant gives
  --        wordsAt out_ptr (n_left+n_right) ++ [] = merge left right → done.
  --   5. In Break-0 case (left drain step, i<n_left, j=n_right):
  --        write left[i] to out[i+n_right], i++, k++; content maintained.
  have h_main : wp_wasm_prop «module» st₁ loc₁ (func6.drop 27) {}
      (fun st' _ =>
        wordsAt st'.mem out_ptr (n_left.toNat + n_right.toNat) =
          List.merge
            (wordsAt st.mem left_ptr n_left.toNat)
            (wordsAt st.mem right_ptr n_right.toNat)
            (· ≤ ·)) := by
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
    -- all preamble writes land in [frame+8, frame+32), disjoint from left/right/out by hFL/FR/FO_dj
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
    -- MergeLoopInv at (0,0,0) for (st₁, st₁, loc₁)
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
    -- execute the main merge block
    obtain ⟨N_merge, st₂, loc₂, h_step, h_exit, hI₂⟩ :=
      func6_after_merge_block st₁ loc₁ frame out_ptr left_ptr right_ptr n_left n_right n_out hI₀
    -- execute the outer drain loop
    obtain ⟨N_drain, stF, h_drain, h_content⟩ :=
      outer_drain_terminates st₁ st₂ loc₂ frame out_ptr left_ptr right_ptr n_left n_right n_out hI₂ h_exit
    -- bridge: st₁.mem left/right = st.mem left/right
    rw [hmem_left_eq, hmem_right_eq] at h_content
    -- extract execOne from exec [.loop ...]
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
    -- exec at func6.drop 28 = Return
    have h_drain28 : exec N_drain «module» st₂ loc₂ (func6.drop 28) {} =
        .Return stF loc₂.values := by
      rw [func6_drop28_eq]; simp only [exec, hone_drain]
    -- lift to max fuel
    let F := max N_merge N_drain
    have h_drain28_F : exec F «module» st₂ loc₂ (func6.drop 28) {} = .Return stF loc₂.values := by
      have hne : exec N_drain «module» st₂ loc₂ (func6.drop 28) {} ≠ .OutOfFuel := by
        rw [h_drain28]; intro h; cases h
      exact (exec_fuel_mono (Nat.le_max_right N_merge N_drain) hne).trans h_drain28
    have h_main_F : exec F «module» st₁ loc₁ (func6.drop 27) {} = .Return stF loc₂.values := by
      rw [h_step F (Nat.le_max_left N_merge N_drain)]; exact h_drain28_F
    exact ⟨F, by simp only [h_main_F]; exact h_content⟩
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
    -- hrd: the address used in the preamble loads is sp-32 (= frame); use haddr lemmas to connect
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

