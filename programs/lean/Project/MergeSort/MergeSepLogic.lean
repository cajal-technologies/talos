import CodeLib.SepLogic.Adequacy
import Project.MergeSort.ContentLemmas
import Project.MergeSort.Framing
import Project.MergeSort.Program

/-! # Main merge loop spec for func6

Proves `main_merge_loop_spec`: the inner merge `.loop 0 0 mainMergeBody` (wrapped
in its outer `.block 0 0 [.loop ...]`) from `func6` (Program.lean lines 274–479)
terminates with either `i = n_left` or `j = n_right`.

The loop body exits via `br_if 1` (Break 1 from the body), which the loop
converts to Break 0, which the outer block converts to Fallthrough.  The spec
is therefore stated for `[.block 0 0 [.loop 0 0 mainMergeBody]]`.

First-pass: the counter invariant is proven; the content invariant (output is
the correct merge of the two prefixes) is left for a follow-up.
-/

namespace Wasm.SepLogic.MergeSort

open Wasm Project.MergeSort.Spec Project.MergeSort.Framing

variable [WasmHeapGS]

/-- Body of func6's main merge loop (Program.lean lines 276–477).

    Structure:
      - two exit checks (i ≥ n_left or j ≥ n_right → br_if 1 exits the loop+block)
      - load i into local7
      - 14-block comparison/copy structure:
          path A (left[i] ≤ right[j]): copies left[i] to out[k], i++
          path B (left[i] > right[j]): copies right[j] to out[k], j++
          all bounds-check panics (.call 87) are unreachable under the invariant
      - k++ (common to both paths, after the 14-block structure)
      - br 0 (loop restart) -/
private def mainMergeBody : Program := [
  -- exit: i ≥ n_left
  .localGet 6, .load32 (8 : UInt32), .localGet 1, .ltU,
  .const (1 : UInt32), .and, .eqz, .br_if 1,
  -- exit: j ≥ n_right
  .localGet 6, .load32 (12 : UInt32), .localGet 3, .ltU,
  .const (1 : UInt32), .and, .eqz, .br_if 1,
  -- i → local7
  .localGet 6, .load32 (8 : UInt32), .localSet 7,
  -- 14-block comparison + copy
  .block 0 0 [
    .block 0 0 [
      .block 0 0 [
        .block 0 0 [
          .block 0 0 [
            .block 0 0 [
              .block 0 0 [
                .block 0 0 [
                  .block 0 0 [
                    .block 0 0 [
                      .block 0 0 [
                        .block 0 0 [
                          .block 0 0 [
                            .block 0 0 [
                              -- check i < n_left (br_if 0 = panic)
                              .localGet 7, .localGet 1, .ltU,
                              .const (1 : UInt32), .and, .eqz, .br_if 0,
                              -- left[i] → local8; j → local9
                              .localGet 0, .localGet 7, .const (2 : UInt32), .shl,
                              .add, .load32 (0 : UInt32), .localSet 8,
                              .localGet 6, .load32 (12 : UInt32), .localSet 9,
                              -- check j < n_right: ok → br_if 1; fail → br 2
                              .localGet 9, .localGet 3, .ltU,
                              .const (1 : UInt32), .and, .br_if 1, .br 2
                            ],
                            -- bounds-check panic path — impossible under invariant
                            .localGet 7, .localGet 1,
                            .const (1048712 : UInt32), .call 87, .unreachable
                          ],
                          -- compare left[i] vs right[j]:
                          -- left[i] ≤ right[j] → br_if 2 (left path)
                          -- left[i] > right[j] → br 1 (right path)
                          .localGet 8, .localGet 2, .localGet 9,
                          .const (2 : UInt32), .shl, .add, .load32 (0 : UInt32),
                          .leU, .const (1 : UInt32), .and, .br_if 2, .br 1
                        ],
                        -- bounds-check panic path — impossible under invariant
                        .localGet 9, .localGet 3,
                        .const (1048728 : UInt32), .call 87, .unreachable
                      ],
                      -- right path: j → local10; check j < n_right
                      .localGet 6, .load32 (12 : UInt32), .localSet 10,
                      .localGet 10, .localGet 3, .ltU,
                      .const (1 : UInt32), .and, .br_if 1, .br 2
                    ],
                    -- left path: i → local11; check i < n_left: ok → br_if 4; fail → br 5
                    .localGet 6, .load32 (8 : UInt32), .localSet 11,
                    .localGet 11, .localGet 1, .ltU,
                    .const (1 : UInt32), .and, .br_if 4, .br 5
                  ],
                  -- right path cont: right[j] → local12; k → local13
                  .localGet 2, .localGet 10, .const (2 : UInt32), .shl,
                  .add, .load32 (0 : UInt32), .localSet 12,
                  .localGet 6, .load32 (16 : UInt32), .localSet 13,
                  -- check k < n_out: ok → br_if 1; fail → br 2
                  .localGet 13, .localGet 5, .ltU,
                  .const (1 : UInt32), .and, .br_if 1, .br 2
                ],
                -- bounds-check panic path — impossible under invariant
                .localGet 10, .localGet 3,
                .const (1048744 : UInt32), .call 87, .unreachable
              ],
              -- right path store: out[k] = right[j]; j++; exit all 6 inner blocks
              .localGet 4, .localGet 13, .const (2 : UInt32), .shl,
              .add, .localGet 12, .store32 (0 : UInt32),
              .localGet 6, .localGet 6, .load32 (12 : UInt32),
              .const (1 : UInt32), .add, .store32 (12 : UInt32),
              .br 5
            ],
            -- bounds-check panic path — impossible under invariant
            .localGet 13, .localGet 5,
            .const (1048760 : UInt32), .call 87, .unreachable
          ],
          -- left path cont: left[i] → local14; k → local15
          .localGet 0, .localGet 11, .const (2 : UInt32), .shl,
          .add, .load32 (0 : UInt32), .localSet 14,
          .localGet 6, .load32 (16 : UInt32), .localSet 15,
          -- check k < n_out: ok → br_if 1; fail → br 2
          .localGet 15, .localGet 5, .ltU,
          .const (1 : UInt32), .and, .br_if 1, .br 2
        ],
        -- bounds-check panic path — impossible under invariant
        .localGet 11, .localGet 1,
        .const (1048776 : UInt32), .call 87, .unreachable
      ],
      -- left path store: out[k] = left[i]; i++; exit 2 outer blocks
      .localGet 4, .localGet 15, .const (2 : UInt32), .shl,
      .add, .localGet 14, .store32 (0 : UInt32),
      .localGet 6, .localGet 6, .load32 (8 : UInt32),
      .const (1 : UInt32), .add, .store32 (8 : UInt32),
      .br 1
    ],
    -- bounds-check panic path — impossible under invariant
    .localGet 15, .localGet 5,
    .const (1048792 : UInt32), .call 87, .unreachable
  ],
  -- k++ (after either path exits the 14-block structure)
  .localGet 6, .localGet 6, .load32 (16 : UInt32),
  .const (1 : UInt32), .add, .store32 (16 : UInt32),
  .br 0
]

/-- Loop invariant (counter-tracking only; content invariant is a follow-up).

    Tracks current i, j and k = k₀ + (i - i₀) + (j - j₀), with local-structure
    constraints and disjointness conditions.  `st_init` is fixed so future
    content-invariant fields can refer to original source values. -/
def MergeLoopInv
    (frame out_ptr left_ptr right_ptr n_left n_right n_out : UInt32)
    (i₀ j₀ k₀ : Nat) (st_init : Store Unit)
    (stA : Store Unit) (locA : Locals) : Prop :=
  ∃ i j : Nat,
    i₀ ≤ i ∧ i ≤ n_left.toNat ∧
    j₀ ≤ j ∧ j ≤ n_right.toNat ∧
    -- i, j, k stored in frame slots
    stA.mem.read32 (frame + 8)  = UInt32.ofNat i ∧
    stA.mem.read32 (frame + 12) = UInt32.ofNat j ∧
    stA.mem.read32 (frame + 16) = UInt32.ofNat (k₀ + (i - i₀) + (j - j₀)) ∧
    -- six params unchanged
    locA.get 6 = some (.i32 frame) ∧
    locA.get 0 = some (.i32 left_ptr) ∧
    locA.get 1 = some (.i32 n_left) ∧
    locA.get 2 = some (.i32 right_ptr) ∧
    locA.get 3 = some (.i32 n_right) ∧
    locA.get 4 = some (.i32 out_ptr) ∧
    locA.get 5 = some (.i32 n_out) ∧
    locA.params.length = 6 ∧ locA.locals.length = 16 ∧
    -- global 0 writable (exit path uses globalSet 0 in drain loops)
    (∃ v, stA.globals.globals[0]? = some v) ∧
    -- source arrays unchanged (placeholder; content invariant fields go here)
    (∀ q, q < n_left.toNat →
      stA.mem.read32 (left_ptr + 4 * UInt32.ofNat q) =
      st_init.mem.read32 (left_ptr + 4 * UInt32.ofNat q)) ∧
    (∀ q, q < n_right.toNat →
      stA.mem.read32 (right_ptr + 4 * UInt32.ofNat q) =
      st_init.mem.read32 (right_ptr + 4 * UInt32.ofNat q)) ∧
    -- content: output region is the merge prefix so far; remaining merge completes it
    wordsAt stA.mem (out_ptr + 4 * UInt32.ofNat k₀) ((i - i₀) + (j - j₀)) ++
      List.merge
        ((wordsAt st_init.mem left_ptr n_left.toNat).drop i)
        ((wordsAt st_init.mem right_ptr n_right.toNat).drop j)
        (· ≤ ·) =
    List.merge
      ((wordsAt st_init.mem left_ptr n_left.toNat).drop i₀)
      ((wordsAt st_init.mem right_ptr n_right.toNat).drop j₀)
      (· ≤ ·) ∧
    -- memory bounds
    frame.toNat + 20 ≤ stA.mem.pages * 65536 ∧
    k₀ + (n_left.toNat - i₀) + (n_right.toNat - j₀) ≤ n_out.toNat ∧
    left_ptr.toNat  + 4 * n_left.toNat  ≤ stA.mem.pages * 65536 ∧
    right_ptr.toNat + 4 * n_right.toNat ≤ stA.mem.pages * 65536 ∧
    out_ptr.toNat   + 4 * n_out.toNat   ≤ stA.mem.pages * 65536 ∧
    stA.mem.pages * 65536 ≤ 4294967296 ∧
    -- disjointness
    (left_ptr.toNat + 4 * n_left.toNat ≤ out_ptr.toNat ∨
     out_ptr.toNat + 4 * n_out.toNat ≤ left_ptr.toNat) ∧
    (right_ptr.toNat + 4 * n_right.toNat ≤ out_ptr.toNat ∨
     out_ptr.toNat + 4 * n_out.toNat ≤ right_ptr.toNat) ∧
    (left_ptr.toNat + 4 * n_left.toNat ≤ right_ptr.toNat ∨
     right_ptr.toNat + 4 * n_right.toNat ≤ left_ptr.toNat) ∧
    (frame.toNat + 20 ≤ left_ptr.toNat ∨
     left_ptr.toNat + 4 * n_left.toNat ≤ frame.toNat) ∧
    (frame.toNat + 20 ≤ right_ptr.toNat ∨
     right_ptr.toNat + 4 * n_right.toNat ≤ frame.toNat) ∧
    (frame.toNat + 20 ≤ out_ptr.toNat ∨
     out_ptr.toNat + 4 * n_out.toNat ≤ frame.toNat)

set_option maxHeartbeats 800000 in
/-- The main merge loop of `func6` terminates with either `i = n_left` or
    `j = n_right` (the loop exhausted at least one source array).

    The spec covers `[.block 0 0 [.loop 0 0 mainMergeBody]]` because the loop
    exits via `br_if 1` (Break 1 from body → Break 0 from loop) and the outer
    block converts that Break 0 to Fallthrough.

    Measure: μ = (n_left.toNat - i) + (n_right.toNat - j).
    Each iteration increments exactly one of i, j, so μ strictly decreases. -/
theorem main_merge_loop_spec
    {m : Module} {env : HostEnv Unit}
    (st : Store Unit) (locals : Locals)
    (frame out_ptr left_ptr right_ptr n_left n_right n_out : UInt32)
    (i₀ j₀ k₀ : Nat)
    (hI₀ : MergeLoopInv frame out_ptr left_ptr right_ptr n_left n_right n_out
             i₀ j₀ k₀ st st locals) :
    wp_wasm_prop m st locals [.block 0 0 [.loop 0 0 mainMergeBody]] env
      (fun st' _ =>
        st'.mem.read32 (frame + 8)  = n_left ∨
        st'.mem.read32 (frame + 12) = n_right) := by
  -- strong induction on μ = (n_left - i) + (n_right - j)
  suffices key : ∀ n stA locA,
      MergeLoopInv frame out_ptr left_ptr right_ptr n_left n_right n_out
        i₀ j₀ k₀ st stA locA →
      (n_left.toNat - (stA.mem.read32 (frame + 8)).toNat) +
        (n_right.toNat - (stA.mem.read32 (frame + 12)).toNat) = n →
      wp_wasm_prop m stA locA [.block 0 0 [.loop 0 0 mainMergeBody]] env
        (fun st' _ =>
          st'.mem.read32 (frame + 8) = n_left ∨
          st'.mem.read32 (frame + 12) = n_right) from
    key _ st locals hI₀ rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro stA locA hI hμ
    obtain ⟨i, j, hi_lo, hi_hi, hj_lo, hj_hi,
             hi_m, hj_m, hk_m,
             hf6, h0, h1, h2, h3, h4, h5,
             hlparams, hllocals, hglobal,
             hleft, hright, hcontent,
             hpages, hk_global,
             hleft_global, hright_global, hout_global,
             hpages_u32,
             hleft_out_disj, hright_out_disj, hleft_right_disj,
             hframe_left_disj, hframe_right_disj, hframe_out_disj⟩ := hI
    by_cases hlt_i : i < n_left.toNat
    · by_cases hlt_j : j < n_right.toNat
      · -- iteration: i < n_left, j < n_right
        -- Case-split on comparison left[i] ≤ right[j].
        -- Each path: exec trace through 14 nested blocks sorry'd;
        -- invariant restoration and measure decrease proven; IH applied.
        obtain ⟨v₀, hg⟩ := hglobal
        have hμ_pos : 0 < n := by
          rw [← hμ, hi_m, hj_m, UInt32.toNat_ofNat', UInt32.toNat_ofNat']
          have := n_left.toNat_lt; have := n_right.toNat_lt; omega
        let k := k₀ + (i - i₀) + (j - j₀)
        have hk_val : k < n_out.toNat := by have := hk_global; omega
        have hft8  : (frame + 8).toNat  = frame.toNat + 8  := by
          rw [UInt32.toNat_add, show (8 : UInt32).toNat = 8 from rfl]
          exact Nat.mod_eq_of_lt (by omega)
        have hft12 : (frame + 12).toNat = frame.toNat + 12 := by
          rw [UInt32.toNat_add, show (12 : UInt32).toNat = 12 from rfl]
          exact Nat.mod_eq_of_lt (by omega)
        have hft16 : (frame + 16).toNat = frame.toNat + 16 := by
          rw [UInt32.toNat_add, show (16 : UInt32).toNat = 16 from rfl]
          exact Nat.mod_eq_of_lt (by omega)
        have hout_k_toNat : (out_ptr + 4 * UInt32.ofNat k).toNat = out_ptr.toNat + 4 * k :=
          toNat_wordAddr out_ptr n_out.toNat k hk_val (by linarith)
        let left_i  := stA.mem.read32 (left_ptr + 4 * UInt32.ofNat i)
        let right_j := stA.mem.read32 (right_ptr + 4 * UInt32.ofNat j)
        have hi_add1 : UInt32.ofNat i + 1 = UInt32.ofNat (i + 1) := by
          apply UInt32.toNat_inj.mp
          simp only [UInt32.toNat_add, UInt32.toNat_ofNat', show (1 : UInt32).toNat = 1 from rfl,
                     Nat.mod_eq_of_lt (show i + 1 < 4294967296 from by
                       have := n_left.toNat_lt; omega)]
          omega
        have hj_add1 : UInt32.ofNat j + 1 = UInt32.ofNat (j + 1) := by
          apply UInt32.toNat_inj.mp
          simp only [UInt32.toNat_add, UInt32.toNat_ofNat', show (1 : UInt32).toNat = 1 from rfl,
                     Nat.mod_eq_of_lt (show j + 1 < 4294967296 from by
                       have := n_right.toNat_lt; omega)]
          omega
        have hk_add1 : UInt32.ofNat k + 1 = UInt32.ofNat (k + 1) := by
          apply UInt32.toNat_inj.mp
          simp only [UInt32.toNat_add, UInt32.toNat_ofNat', show (1 : UInt32).toNat = 1 from rfl,
                     Nat.mod_eq_of_lt (show k + 1 < 4294967296 from by
                       have := n_out.toNat_lt; omega)]
          omega
        by_cases hle : left_i ≤ right_j
        · -- ── path A: left[i] ≤ right[j]: copy left[i] to out[k], i++, k++ ──
          let mem1_A := stA.mem.write32 (out_ptr + 4 * UInt32.ofNat k) left_i
          let mem2_A := mem1_A.write32 (frame + 8) (UInt32.ofNat i + 1)
          let mem3_A := mem2_A.write32 (frame + 16) (UInt32.ofNat k + 1)
          let stC_A : Store Unit := { stA with mem := mem3_A }
          -- Result locals: localSet 7(→local[1]) 8(→local[2]) 9(→local[3])
          --                       11(→local[5]) 14(→local[8]) 15(→local[9])
          let locA_out_locs :=
            locA.locals.set 1 (.i32 (UInt32.ofNat i)) |>.set 2 (.i32 left_i)
              |>.set 3 (.i32 (UInt32.ofNat j)) |>.set 5 (.i32 (UInt32.ofNat i))
              |>.set 8 (.i32 left_i) |>.set 9 (.i32 (UInt32.ofNat k))
          let locA_out_A : Locals := { locA with locals := locA_out_locs }
          -- exec trace (staged through 14 nested blocks)
          have h_body_A : ∃ f_A,
              exec f_A m stA locA mainMergeBody env = .Break 0 stC_A locA_out_A := by
            refine ⟨15, ?_⟩
            -- ── body let-bindings (definitionally transparent to mainMergeBody internals) ──
            let body14 : Program := [
              .localGet 7, .localGet 1, .ltU, .const (1:UInt32), .and, .eqz, .br_if 0,
              .localGet 0, .localGet 7, .const (2:UInt32), .shl, .add,
              .load32 (0:UInt32), .localSet 8,
              .localGet 6, .load32 (12:UInt32), .localSet 9,
              .localGet 9, .localGet 3, .ltU, .const (1:UInt32), .and, .br_if 1, .br 2]
            let body13 : Program := [.block 0 0 body14,
              .localGet 7, .localGet 1, .const (1048712:UInt32), .call 87, .unreachable]
            let body12 : Program := [.block 0 0 body13,
              .localGet 8, .localGet 2, .localGet 9, .const (2:UInt32), .shl, .add,
              .load32 (0:UInt32), .leU, .const (1:UInt32), .and, .br_if 2, .br 1]
            let body11 : Program := [.block 0 0 body12,
              .localGet 9, .localGet 3, .const (1048728:UInt32), .call 87, .unreachable]
            let body10 : Program := [.block 0 0 body11,
              .localGet 6, .load32 (12:UInt32), .localSet 10,
              .localGet 10, .localGet 3, .ltU, .const (1:UInt32), .and, .br_if 1, .br 2]
            let body9 : Program := [.block 0 0 body10,
              .localGet 6, .load32 (8:UInt32), .localSet 11,
              .localGet 11, .localGet 1, .ltU, .const (1:UInt32), .and, .br_if 4, .br 5]
            let body8 : Program := [.block 0 0 body9,
              .localGet 2, .localGet 10, .const (2:UInt32), .shl, .add,
              .load32 (0:UInt32), .localSet 12,
              .localGet 6, .load32 (16:UInt32), .localSet 13,
              .localGet 13, .localGet 5, .ltU, .const (1:UInt32), .and, .br_if 1, .br 2]
            let body7 : Program := [.block 0 0 body8,
              .localGet 10, .localGet 3, .const (1048744:UInt32), .call 87, .unreachable]
            let body6 : Program := [.block 0 0 body7,
              .localGet 4, .localGet 13, .const (2:UInt32), .shl, .add,
              .localGet 12, .store32 (0:UInt32),
              .localGet 6, .localGet 6, .load32 (12:UInt32),
              .const (1:UInt32), .add, .store32 (12:UInt32), .br 5]
            let body5 : Program := [.block 0 0 body6,
              .localGet 13, .localGet 5, .const (1048760:UInt32), .call 87, .unreachable]
            let body4 : Program := [.block 0 0 body5,
              .localGet 0, .localGet 11, .const (2:UInt32), .shl, .add,
              .load32 (0:UInt32), .localSet 14,
              .localGet 6, .load32 (16:UInt32), .localSet 15,
              .localGet 15, .localGet 5, .ltU, .const (1:UInt32), .and, .br_if 1, .br 2]
            let body3 : Program := [.block 0 0 body4,
              .localGet 11, .localGet 1, .const (1048776:UInt32), .call 87, .unreachable]
            let body2 : Program := [.block 0 0 body3,
              .localGet 4, .localGet 15, .const (2:UInt32), .shl, .add,
              .localGet 14, .store32 (0:UInt32),
              .localGet 6, .localGet 6, .load32 (8:UInt32),
              .const (1:UInt32), .add, .store32 (8:UInt32), .br 1]
            let body1 : Program := [.block 0 0 body2,
              .localGet 15, .localGet 5, .const (1048792:UInt32), .call 87, .unreachable]
            -- ── intermediate Locals states ──
            -- after prefix localSet 7: local[1] = UInt32.ofNat i
            let locA_7 : Locals :=
              { locA with locals := locA.locals.set 1 (.i32 (UInt32.ofNat i)) }
            -- after body14 localSet 8,9: local[2]=left_i, local[3]=UInt32.ofNat j
            let locA_89_locs :=
              locA.locals.set 1 (.i32 (UInt32.ofNat i)) |>.set 2 (.i32 left_i)
                |>.set 3 (.i32 (UInt32.ofNat j))
            let locA_89 : Locals := { locA with locals := locA_89_locs }
            -- after B9_left_cont localSet 11: local[5]=UInt32.ofNat i
            let locA_11_locs :=
              locA.locals.set 1 (.i32 (UInt32.ofNat i)) |>.set 2 (.i32 left_i)
                |>.set 3 (.i32 (UInt32.ofNat j)) |>.set 5 (.i32 (UInt32.ofNat i))
            let locA_11 : Locals := { locA with locals := locA_11_locs }
            -- store after B2: out[k]=left_i written, frame+8=i+1 written
            let stA_m2 : Store Unit := { stA with mem := mem2_A }
            -- ── auxiliary lemmas ──
            have hi_lt_u32 : UInt32.ofNat i < n_left := by
              rw [UInt32.lt_iff_toNat_lt_toNat, UInt32.toNat_ofNat']
              have := n_left.toNat_lt; omega
            have hj_lt_u32 : UInt32.ofNat j < n_right := by
              rw [UInt32.lt_iff_toNat_lt_toNat, UInt32.toNat_ofNat']
              have := n_right.toNat_lt; omega
            have hk_lt_u32 : UInt32.ofNat k < n_out := by
              rw [UInt32.lt_iff_toNat_lt_toNat, UInt32.toNat_ofNat']
              have := n_out.toNat_lt; omega
            have hmem1_fr8 : mem1_A.read32 (frame + 8) = UInt32.ofNat i := by
              simp only [mem1_A,
                Mem.read32_write32_of_disjoint _ (out_ptr + 4 * UInt32.ofNat k) (frame + 8) _
                  (by rw [hout_k_toNat, hft8]; rcases hframe_out_disj with h | h <;> omega)]
              exact hi_m
            have hmem2_fr16 : mem2_A.read32 (frame + 16) = UInt32.ofNat k := by
              simp only [mem2_A,
                Mem.read32_write32_of_disjoint _ (frame + 8) (frame + 16) _
                  (by left; rw [hft8, hft16]; omega)]
              simp only [mem1_A,
                Mem.read32_write32_of_disjoint _ (out_ptr + 4 * UInt32.ofNat k) (frame + 16) _
                  (by rw [hout_k_toNat, hft16]; rcases hframe_out_disj with h | h <;> omega)]
              exact hk_m
            have hbnd_out_k : ¬((out_ptr + 4 * UInt32.ofNat k).toNat + 4 > stA.mem.pages * 65536) := by
              rw [hout_k_toNat]; omega
            have hbnd_fr8 : ¬((frame + 8).toNat + 4 > stA.mem.pages * 65536) := by
              rw [hft8]; omega
            have hbnd_fr12 : ¬((frame + 12).toNat + 4 > stA.mem.pages * 65536) := by
              rw [hft12]; omega
            have hbnd_fr16 : ¬((frame + 16).toNat + 4 > stA.mem.pages * 65536) := by
              rw [hft16]; omega
            have hbnd_left_i : ¬((left_ptr + 4 * UInt32.ofNat i).toNat + 4 > stA.mem.pages * 65536) := by
              rw [toNat_wordAddr left_ptr n_left.toNat i hlt_i (by linarith)]; omega
            have hbnd_right_j : ¬((right_ptr + 4 * UInt32.ofNat j).toNat + 4 > stA.mem.pages * 65536) := by
              rw [toNat_wordAddr right_ptr n_right.toNat j hlt_j (by linarith)]; omega
            -- ── exec chain through 14 blocks ──
            -- body14: 23 flat instructions → Break 1 (br_if 1 fires: j < n_right)
            have h_B14 : exec 1 m stA locA_7 body14 env = .Break 1 stA locA_89 := by
              -- GV helpers: {locA_7 with values := vs}.get N = locA_7.get N
              have hgv7_7 : ∀ vs, ({locA_7 with values := vs} : Locals).get 7 = locA_7.get 7 := fun _ => rfl
              have hgv1_7 : ∀ vs, ({locA_7 with values := vs} : Locals).get 1 = locA_7.get 1 := fun _ => rfl
              have hgv0_7 : ∀ vs, ({locA_7 with values := vs} : Locals).get 0 = locA_7.get 0 := fun _ => rfl
              have hgv6_7 : ∀ vs, ({locA_7 with values := vs} : Locals).get 6 = locA_7.get 6 := fun _ => rfl
              have hgv3_7 : ∀ vs, ({locA_7 with values := vs} : Locals).get 3 = locA_7.get 3 := fun _ => rfl
              -- locA_7 length facts
              have hlp_7 : locA_7.params.length = 6  := hlparams
              have hll_7 : locA_7.locals.length = 16 := by simp [locA_7, List.length_set, hllocals]
              -- locA_7 specific gets
              have hg7_7 : locA_7.get 7 = some (.i32 (UInt32.ofNat i)) := by
                simp only [Locals.get, hlp_7, hll_7, List.length_set,
                           show ¬(7 < 6) from by omega, show (7 : Nat) < 6 + 16 from by omega,
                           show (7 : Nat) - 6 = 1 from by omega]
                -- goal: locA_7.locals[1]? = some _; locA_7.locals = locA.locals.set 1 _
                change (locA.locals.set 1 (.i32 (UInt32.ofNat i)))[1]? = _
                exact List.getElem?_set_self (by rw [hllocals]; norm_num)
              have hg1_7 : locA_7.get 1 = some (.i32 n_left) := by
                simp only [Locals.get, locA_7, hlparams, show (1 : Nat) < 6 from by omega] at h1 ⊢
                exact h1
              have hg0_7 : locA_7.get 0 = some (.i32 left_ptr) := by
                simp only [Locals.get, locA_7, hlparams, show (0 : Nat) < 6 from by omega] at h0 ⊢
                exact h0
              have hg6_7 : locA_7.get 6 = some (.i32 frame) := by
                have h : locA_7.get 6 = locA.get 6 := by
                  simp [locA_7, Locals.get, hlparams, hllocals, List.length_set, List.getElem?_set]
                rw [h]; exact hf6
              have hg3_7 : locA_7.get 3 = some (.i32 n_right) := by
                simp only [Locals.get, locA_7, hlparams, show (3 : Nat) < 6 from by omega] at h3 ⊢
                exact h3
              -- raw-form get 6 after localSet 8 (sets local[2] = left_i)
              have hg6_8_raw : ∀ vs,
                  (Locals.mk locA_7.params (locA_7.locals.set 2 (.i32 left_i)) vs).get 6
                  = some (.i32 frame) := by
                intro vs
                have h : (Locals.mk locA_7.params (locA_7.locals.set 2 (.i32 left_i)) vs).get 6
                    = locA.get 6 := by
                  simp [locA_7, Locals.get, hlparams, hllocals, List.length_set, List.getElem?_set]
                rw [h]; exact hf6
              -- raw-form gets after localSet 9 (sets local[3] = j)
              have hg9_89_raw : ∀ vs,
                  (Locals.mk locA_7.params
                    ((locA_7.locals.set 2 (.i32 left_i)).set 3 (.i32 (UInt32.ofNat j))) vs).get 9
                  = some (.i32 (UInt32.ofNat j)) := by
                intro vs
                simp only [Locals.get, hlp_7, hll_7, List.length_set,
                           show ¬(9 < 6) from by omega, show (9 : Nat) < 6 + 16 from by omega,
                           show (9 : Nat) - 6 = 3 from by omega]
                -- goal: ((locA_7.locals.set 2 _).set 3 _)[3]? = some _
                exact List.getElem?_set_self (by simp [List.length_set, hll_7])
              have hg3_89_raw : ∀ vs,
                  (Locals.mk locA_7.params
                    ((locA_7.locals.set 2 (.i32 left_i)).set 3 (.i32 (UInt32.ofNat j))) vs).get 3
                  = some (.i32 n_right) := by
                intro vs
                have h3_raw : locA.params[3]? = some (.i32 n_right) := by
                  have h := h3
                  simp only [Locals.get, hlparams, show (3 : Nat) < 6 from by omega] at h
                  exact h
                simp only [Locals.get, hlp_7, show (3 : Nat) < 6 from by omega]
                exact h3_raw
              -- shl-by-2 = multiply-by-4
              have hshl_i : UInt32.ofNat i <<< ((2 : UInt32) % 32) = 4 * UInt32.ofNat i := by
                rw [show (2 : UInt32) % 32 = 2 from by decide]
                apply UInt32.toNat_inj.mp
                have hi_bnd : i < 2 ^ 30 := by have := n_left.toNat_lt; omega
                simp only [UInt32.toNat_mul, UInt32.toNat_ofNat',
                           show (4 : UInt32).toNat = 4 from rfl,
                           Nat.mod_eq_of_lt (show i < 4294967296 from by omega),
                           Nat.mod_eq_of_lt (show i * 4 < 4294967296 from by omega)]
                simp [UInt32.shiftLeft, Fin.shiftLeft, Nat.shiftLeft_eq]; omega
              have hshl_j : UInt32.ofNat j <<< ((2 : UInt32) % 32) = 4 * UInt32.ofNat j := by
                rw [show (2 : UInt32) % 32 = 2 from by decide]
                apply UInt32.toNat_inj.mp
                have hj_bnd : j < 2 ^ 30 := by have := n_right.toNat_lt; omega
                simp only [UInt32.toNat_mul, UInt32.toNat_ofNat',
                           show (4 : UInt32).toNat = 4 from rfl,
                           Nat.mod_eq_of_lt (show j < 4294967296 from by omega),
                           Nat.mod_eq_of_lt (show j * 4 < 4294967296 from by omega)]
                simp [UInt32.shiftLeft, Fin.shiftLeft, Nat.shiftLeft_eq]; omega
              -- big simp: reduce body14's 23 flat instructions
              simp only [exec, execOne.eq_def, body14, Locals.set?,
                         hgv7_7, hgv1_7, hgv0_7, hgv6_7, hgv3_7,
                         hg7_7, hg1_7, hg0_7, hg6_7, hg3_7,
                         if_pos hi_lt_u32,
                         show (1 : UInt32) &&& 1 = 1 from by decide,
                         show (if (1 : UInt32) = 0 then (1 : UInt32) else 0) = 0 from by decide,
                         hshl_i,
                         if_neg (show ¬((4 * UInt32.ofNat i + left_ptr).toNat +
                                         UInt32.toNat (0 : UInt32) + 4 > stA.mem.pages * 65536) from by
                                   rw [show 4 * UInt32.ofNat i + left_ptr =
                                           left_ptr + 4 * UInt32.ofNat i from UInt32.add_comm _ _,
                                       show UInt32.toNat (0 : UInt32) = 0 from rfl]; omega),
                         show stA.mem.read32 (4 * UInt32.ofNat i + left_ptr + (0 : UInt32)) = left_i from by
                           rw [show 4 * UInt32.ofNat i + left_ptr + (0 : UInt32) =
                                   left_ptr + 4 * UInt32.ofNat i from by
                               rw [UInt32.add_comm (4 * UInt32.ofNat i) left_ptr, UInt32.add_zero]],
                         hlp_7, hll_7, List.length_set,
                         if_neg (show ¬(8 < 6) from by omega),
                         if_pos (show (8 : Nat) < 6 + 16 from by omega),
                         show (8 : Nat) - 6 = 2 from by omega,
                         hg6_8_raw,
                         if_neg (show ¬(frame.toNat + (12 : UInt32).toNat + 4 > stA.mem.pages * 65536)
                                   from by simp only [show (12 : UInt32).toNat = 12 from by decide]; omega),
                         show stA.mem.read32 (frame + (12 : UInt32)) = UInt32.ofNat j from hj_m,
                         if_neg (show ¬(9 < 6) from by omega),
                         if_pos (show (9 : Nat) < 6 + 16 from by omega),
                         show (9 : Nat) - 6 = 3 from by omega,
                         hg9_89_raw, hg3_89_raw,
                         if_pos hj_lt_u32,
                         show (1 : UInt32) &&& 1 = 1 from by decide,
                         show Locals.mk locA_7.params
                               ((locA_7.locals.set 2 (.i32 left_i)).set 3 (.i32 (UInt32.ofNat j)))
                               locA.values = locA_89 from rfl]
              rfl
            -- body13: Break(0+1) from body14 → Break 0
            have h_B13 : exec 2 m stA locA_7 body13 env = .Break 0 stA locA_89 := by
              rw [show (2:Nat) = 1+1 from rfl, exec_block_cons, h_B14]
            -- body12: Break 0 → B12_compare runs, leU fires (left_i ≤ right_j), br_if 2 → Break 2
            have h_B12_A : exec 3 m stA locA_7 body12 env = .Break 2 stA locA_89 := by
              rw [show (3:Nat) = 2+1 from rfl, exec_block_cons, h_B13]
              simp only [List.take_zero, List.drop_zero, List.nil_append]
              have hll_89 : locA_89.locals.length = 16 := by
                simp [locA_89, locA_89_locs, List.length_set, hllocals]
              have hgv8_89 : ∀ vs, ({locA_89 with values := vs} : Locals).get 8 = locA_89.get 8 := fun _ => rfl
              have hgv2_89 : ∀ vs, ({locA_89 with values := vs} : Locals).get 2 = locA_89.get 2 := fun _ => rfl
              have hgv9_89 : ∀ vs, ({locA_89 with values := vs} : Locals).get 9 = locA_89.get 9 := fun _ => rfl
              have hg8_89 : locA_89.get 8 = some (.i32 left_i) := by
                simp only [Locals.get, locA_89, locA_89_locs, hlparams, hllocals, List.length_set,
                           show ¬(8 < 6) from by omega, show (8:Nat) < 6+16 from by omega,
                           show (8:Nat) - 6 = 2 from by omega]
                rw [List.getElem?_set_ne (show (3:Nat) ≠ 2 from by omega)]
                exact List.getElem?_set_self (by rw [List.length_set, hllocals]; norm_num)
              have hg2_89 : locA_89.get 2 = some (.i32 right_ptr) := by
                simp only [Locals.get, locA_89, hlparams, show (2:Nat) < 6 from by omega] at h2 ⊢
                exact h2
              have hg9_89 : locA_89.get 9 = some (.i32 (UInt32.ofNat j)) := by
                simp only [Locals.get, locA_89, locA_89_locs, hlparams, hllocals, List.length_set,
                           show ¬(9 < 6) from by omega, show (9:Nat) < 6+16 from by omega,
                           show (9:Nat) - 6 = 3 from by omega]
                exact List.getElem?_set_self (by rw [List.length_set, List.length_set, hllocals]; norm_num)
              have hshl_j : UInt32.ofNat j <<< ((2:UInt32) % 32) = 4 * UInt32.ofNat j := by
                rw [show (2:UInt32) % 32 = 2 from by decide]
                apply UInt32.toNat_inj.mp
                have hj_bnd : j < 2^30 := by have := n_right.toNat_lt; omega
                simp only [UInt32.toNat_mul, UInt32.toNat_ofNat',
                           show (4:UInt32).toNat = 4 from rfl,
                           Nat.mod_eq_of_lt (show j < 4294967296 from by omega),
                           Nat.mod_eq_of_lt (show j*4 < 4294967296 from by omega)]
                simp [UInt32.shiftLeft, Fin.shiftLeft, Nat.shiftLeft_eq]; omega
              simp only [exec, execOne.eq_def,
                         show ({locA_89 with values := locA_7.values} : Locals) = locA_89 from rfl,
                         hgv8_89, hgv2_89, hgv9_89,
                         hg8_89, hg2_89, hg9_89,
                         hshl_j,
                         if_neg (show ¬((4 * UInt32.ofNat j + right_ptr).toNat +
                                         UInt32.toNat (0:UInt32) + 4 > stA.mem.pages * 65536) from by
                                   rw [show 4 * UInt32.ofNat j + right_ptr =
                                               right_ptr + 4 * UInt32.ofNat j from UInt32.add_comm _ _,
                                           show UInt32.toNat (0:UInt32) = 0 from rfl]
                                   omega),
                         show stA.mem.read32 (4 * UInt32.ofNat j + right_ptr + (0:UInt32)) = right_j from by
                             rw [show 4 * UInt32.ofNat j + right_ptr + (0:UInt32) =
                                         right_ptr + 4 * UInt32.ofNat j from by
                                     rw [UInt32.add_comm (4 * UInt32.ofNat j) right_ptr, UInt32.add_zero]],
                         if_pos hle,
                         show (1:UInt32) &&& 1 = 1 from by decide,
                         show ({locA_89 with values := locA.values} : Locals) = locA_89 from rfl]
              rfl
            -- body11: Break(1+1) → Break 1
            have h_B11 : exec 4 m stA locA_7 body11 env = .Break 1 stA locA_89 := by
              rw [show (4:Nat) = 3+1 from rfl, exec_block_cons, h_B12_A]
            -- body10: Break(0+1) → Break 0 (B10_right_cont NOT reached in path A)
            have h_B10 : exec 5 m stA locA_7 body10 env = .Break 0 stA locA_89 := by
              rw [show (5:Nat) = 4+1 from rfl, exec_block_cons, h_B11]
            -- body9: Break 0 → B9_left_cont runs, br_if 4 fires (i < n_left) → Break 4
            have h_B9 : exec 6 m stA locA_7 body9 env = .Break 4 stA locA_11 := by
              rw [show (6:Nat) = 5+1 from rfl, exec_block_cons, h_B10]
              simp only [List.take_zero, List.drop_zero, List.nil_append]
              -- B9_left_cont: localGet 6, load32 8, localSet 11, localGet 11, localGet 1, ltU, const 1, and, br_if 4
              have hlp_89 : locA_89.params.length = 6 := hlparams
              have hll_89 : locA_89.locals.length = 16 := by
                simp [locA_89, locA_89_locs, List.length_set, hllocals]
              have hgv11_11 : ∀ vs, ({locA_11 with values := vs} : Locals).get 11 = locA_11.get 11 := fun _ => rfl
              have hgv1_11  : ∀ vs, ({locA_11 with values := vs} : Locals).get 1  = locA_11.get 1  := fun _ => rfl
              have hg6_89 : locA_89.get 6 = some (.i32 frame) := by
                simp only [Locals.get, locA_89, locA_89_locs, hlparams, hllocals, List.length_set,
                           show ¬(6 < 6) from by omega, show (6:Nat) < 6+16 from by omega,
                           show (6:Nat) - 6 = 0 from by omega]
                rw [List.getElem?_set_ne (show (3:Nat) ≠ 0 from by omega)]
                rw [List.getElem?_set_ne (show (2:Nat) ≠ 0 from by omega)]
                rw [List.getElem?_set_ne (show (1:Nat) ≠ 0 from by omega)]
                simpa [Locals.get, hlparams, hllocals, List.length_set,
                       show ¬(6 < 6) from by omega, show (6:Nat) < 6+16 from by omega,
                       show (6:Nat) - 6 = 0 from by omega] using hf6
              have hg11_11 : locA_11.get 11 = some (.i32 (UInt32.ofNat i)) := by
                simp only [Locals.get, locA_11, locA_11_locs, hlparams, hllocals, List.length_set,
                           show ¬(11 < 6) from by omega, show (11:Nat) < 6+16 from by omega,
                           show (11:Nat) - 6 = 5 from by omega]
                exact List.getElem?_set_self
                  (by rw [List.length_set, List.length_set, List.length_set, hllocals]; norm_num)
              have hg1_11 : locA_11.get 1 = some (.i32 n_left) := by
                simp only [Locals.get, locA_11, hlparams, show (1:Nat) < 6 from by omega] at h1 ⊢
                exact h1
              simp only [exec, execOne.eq_def,
                         show ({locA_89 with values := locA_7.values} : Locals) = locA_89 from rfl,
                         hg6_89,
                         if_neg (show ¬(frame.toNat + (8:UInt32).toNat + 4 > stA.mem.pages * 65536) from by
                                   simp only [show (8:UInt32).toNat = 8 from by decide]; omega),
                         show stA.mem.read32 (frame + (8:UInt32)) = UInt32.ofNat i from hi_m,
                         Locals.set?,
                         hlp_89, hll_89, List.length_set,
                         if_neg (show ¬(11 < 6) from by omega),
                         if_pos (show (11:Nat) < 6 + 16 from by omega),
                         show (11:Nat) - 6 = 5 from by omega,
                         show Locals.mk locA_89.params (locA_89.locals.set 5 (.i32 (UInt32.ofNat i))) locA_89.values = locA_11 from rfl,
                         hgv11_11, hg11_11, hgv1_11, hg1_11,
                         if_pos hi_lt_u32,
                         show (1:UInt32) &&& 1 = 1 from by decide,
                         show ({locA_11 with values := locA_11.values} : Locals) = locA_11 from rfl]
              rfl
            -- body8: Break(3+1) → Break 3
            have h_B8 : exec 7 m stA locA_7 body8 env = .Break 3 stA locA_11 := by
              rw [show (7:Nat) = 6+1 from rfl, exec_block_cons, h_B9]
            -- body7: Break(2+1) → Break 2
            have h_B7 : exec 8 m stA locA_7 body7 env = .Break 2 stA locA_11 := by
              rw [show (8:Nat) = 7+1 from rfl, exec_block_cons, h_B8]
            -- body6: Break(1+1) → Break 1
            have h_B6 : exec 9 m stA locA_7 body6 env = .Break 1 stA locA_11 := by
              rw [show (9:Nat) = 8+1 from rfl, exec_block_cons, h_B7]
            -- body5: Break(0+1) → Break 0 (B5_panic NOT reached)
            have h_B5 : exec 10 m stA locA_7 body5 env = .Break 0 stA locA_11 := by
              rw [show (10:Nat) = 9+1 from rfl, exec_block_cons, h_B6]
            -- body4: Break 0 → B4_left_cont runs, localSet 14,15, br_if 1 fires → Break 1
            have h_B4 : exec 11 m stA locA_7 body4 env = .Break 1 stA locA_out_A := by
              rw [show (11:Nat) = 10+1 from rfl, exec_block_cons, h_B5]
              simp only [List.take_zero, List.drop_zero, List.nil_append]
              -- B4_left_cont: localGet 0, localGet 11, const 2, shl, add, load32 0, localSet 14,
              --                localGet 6, load32 16, localSet 15, localGet 15, localGet 5, ltU, const 1, and, br_if 1
              have hlp_11 : locA_11.params.length = 6 := hlparams
              have hll_11 : locA_11.locals.length = 16 := by
                simp [locA_11, locA_11_locs, List.length_set, hllocals]
              have hgv0_11  : ∀ vs, ({locA_11 with values := vs} : Locals).get 0  = locA_11.get 0  := fun _ => rfl
              have hgv11_11 : ∀ vs, ({locA_11 with values := vs} : Locals).get 11 = locA_11.get 11 := fun _ => rfl
              have hg0_11 : locA_11.get 0 = some (.i32 left_ptr) := by
                simp only [Locals.get, locA_11, hlparams, show (0:Nat) < 6 from by omega] at h0 ⊢; exact h0
              have hg11_11 : locA_11.get 11 = some (.i32 (UInt32.ofNat i)) := by
                simp only [Locals.get, locA_11, locA_11_locs, hlparams, hllocals, List.length_set,
                           show ¬(11 < 6) from by omega, show (11:Nat) < 6+16 from by omega,
                           show (11:Nat) - 6 = 5 from by omega]
                exact List.getElem?_set_self
                  (by rw [List.length_set, List.length_set, List.length_set, hllocals]; norm_num)
              -- ∀-vs helpers for gets from intermediate/post-localSet states
              have hg6_14_raw : ∀ vs,
                  (Locals.mk locA_11.params (locA_11.locals.set 8 (.i32 left_i)) vs).get 6
                  = some (.i32 frame) := by
                intro vs
                have h : (Locals.mk locA_11.params (locA_11.locals.set 8 (.i32 left_i)) vs).get 6
                    = locA.get 6 := by
                  simp [locA_11, locA_11_locs, Locals.get, hlparams, hllocals,
                        List.length_set, List.getElem?_set]
                rw [h]; exact hf6
              have hg15_out_raw : ∀ vs,
                  (Locals.mk locA_11.params
                    ((locA_11.locals.set 8 (.i32 left_i)).set 9 (.i32 (UInt32.ofNat k))) vs).get 15
                  = some (.i32 (UInt32.ofNat k)) := by
                intro vs
                simp only [Locals.get, hlp_11, hll_11, List.length_set,
                           show ¬(15 < 6) from by omega, show (15:Nat) < 6+16 from by omega,
                           show (15:Nat) - 6 = 9 from by omega]
                exact List.getElem?_set_self (by simp [List.length_set, hll_11])
              have hg5_out_raw : ∀ vs,
                  (Locals.mk locA_11.params
                    ((locA_11.locals.set 8 (.i32 left_i)).set 9 (.i32 (UInt32.ofNat k))) vs).get 5
                  = some (.i32 n_out) := by
                intro vs
                have h5_raw : locA.params[5]? = some (.i32 n_out) := by
                  have h := h5
                  simp only [Locals.get, hlparams, show (5:Nat) < 6 from by omega] at h
                  exact h
                simp only [Locals.get, hlp_11, show (5:Nat) < 6 from by omega]
                exact h5_raw
              have hshl_i : UInt32.ofNat i <<< ((2:UInt32) % 32) = 4 * UInt32.ofNat i := by
                rw [show (2:UInt32) % 32 = 2 from by decide]
                apply UInt32.toNat_inj.mp
                have hi_bnd : i < 2^30 := by have := n_left.toNat_lt; omega
                simp only [UInt32.toNat_mul, UInt32.toNat_ofNat',
                           show (4:UInt32).toNat = 4 from rfl,
                           Nat.mod_eq_of_lt (show i < 4294967296 from by omega),
                           Nat.mod_eq_of_lt (show i * 4 < 4294967296 from by omega)]
                simp [UInt32.shiftLeft, Fin.shiftLeft, Nat.shiftLeft_eq]; omega
              simp only [exec, execOne.eq_def,
                         show ({locA_11 with values := locA_7.values} : Locals) = locA_11 from rfl,
                         hgv0_11, hg0_11, hgv11_11, hg11_11,
                         hshl_i,
                         if_neg (show ¬((4 * UInt32.ofNat i + left_ptr).toNat +
                                         UInt32.toNat (0:UInt32) + 4 > stA.mem.pages * 65536) from by
                                   rw [show 4 * UInt32.ofNat i + left_ptr =
                                               left_ptr + 4 * UInt32.ofNat i from UInt32.add_comm _ _,
                                       show UInt32.toNat (0:UInt32) = 0 from rfl]; omega),
                         show stA.mem.read32 (4 * UInt32.ofNat i + left_ptr + (0:UInt32)) = left_i from by
                             rw [show 4 * UInt32.ofNat i + left_ptr + (0:UInt32) =
                                         left_ptr + 4 * UInt32.ofNat i from by
                                     rw [UInt32.add_comm (4 * UInt32.ofNat i) left_ptr, UInt32.add_zero]],
                         Locals.set?,
                         hlp_11, hll_11, List.length_set,
                         if_neg (show ¬(14 < 6) from by omega),
                         if_pos (show (14:Nat) < 6 + 16 from by omega),
                         show (14:Nat) - 6 = 8 from by omega,
                         hg6_14_raw,
                         if_neg (show ¬(frame.toNat + (16:UInt32).toNat + 4 > stA.mem.pages * 65536) from by
                                   simp only [show (16:UInt32).toNat = 16 from by decide]; omega),
                         show stA.mem.read32 (frame + (16:UInt32)) = UInt32.ofNat k from hk_m,
                         if_neg (show ¬(15 < 6) from by omega),
                         if_pos (show (15:Nat) < 6 + 16 from by omega),
                         show (15:Nat) - 6 = 9 from by omega,
                         hg15_out_raw, hg5_out_raw,
                         if_pos hk_lt_u32,
                         show (1:UInt32) &&& 1 = 1 from by decide,
                         show Locals.mk locA_11.params
                               ((locA_11.locals.set 8 (.i32 left_i)).set 9 (.i32 (UInt32.ofNat k)))
                               locA.values = locA_out_A from rfl]
              rfl
            -- body3: Break(0+1) → Break 0 (B3_panic NOT reached)
            have h_B3 : exec 12 m stA locA_7 body3 env = .Break 0 stA locA_out_A := by
              rw [show (12:Nat) = 11+1 from rfl, exec_block_cons, h_B4]
            -- body2: Break 0 → B2_store_left runs, writes out[k]=left_i, frame+8=i+1, br 1 → Break 1
            have h_B2 : exec 13 m stA locA_7 body2 env = .Break 1 stA_m2 locA_out_A := by
              rw [show (13:Nat) = 12+1 from rfl, exec_block_cons, h_B3]
              simp only [List.take_zero, List.drop_zero, List.nil_append]
              -- B2_store_left: localGet 4, localGet 15, const 2, shl, add, localGet 14,
              --   store32 0 (→mem1_A), localGet 6, localGet 6, load32 8 (→i), const 1, add,
              --   store32 8 (→mem2_A), br 1
              have hgv4_out  : ∀ vs, ({locA_out_A with values := vs} : Locals).get 4  = locA_out_A.get 4  := fun _ => rfl
              have hgv15_out : ∀ vs, ({locA_out_A with values := vs} : Locals).get 15 = locA_out_A.get 15 := fun _ => rfl
              have hgv14_out : ∀ vs, ({locA_out_A with values := vs} : Locals).get 14 = locA_out_A.get 14 := fun _ => rfl
              have hgv6_out  : ∀ vs, ({locA_out_A with values := vs} : Locals).get 6  = locA_out_A.get 6  := fun _ => rfl
              have hg4_out : locA_out_A.get 4 = some (.i32 out_ptr) := by
                simp only [Locals.get, locA_out_A, hlparams, show (4:Nat) < 6 from by omega] at h4 ⊢; exact h4
              have hg15_out : locA_out_A.get 15 = some (.i32 (UInt32.ofNat k)) := by
                simp only [Locals.get, locA_out_A, locA_out_locs, hlparams, hllocals, List.length_set,
                           show ¬(15 < 6) from by omega, show (15:Nat) < 6+16 from by omega,
                           show (15:Nat) - 6 = 9 from by omega]
                exact List.getElem?_set_self
                  (by rw [List.length_set, List.length_set, List.length_set,
                           List.length_set, List.length_set, hllocals]; norm_num)
              have hg14_out : locA_out_A.get 14 = some (.i32 left_i) := by
                simp only [Locals.get, locA_out_A, locA_out_locs, hlparams, hllocals, List.length_set,
                           show ¬(14 < 6) from by omega, show (14:Nat) < 6+16 from by omega,
                           show (14:Nat) - 6 = 8 from by omega]
                rw [List.getElem?_set_ne (show (9:Nat) ≠ 8 from by omega)]
                exact List.getElem?_set_self
                  (by rw [List.length_set, List.length_set, List.length_set,
                           List.length_set, hllocals]; norm_num)
              have hg6_out : locA_out_A.get 6 = some (.i32 frame) := by
                simp only [Locals.get, locA_out_A, locA_out_locs, hlparams, hllocals, List.length_set,
                           show ¬(6 < 6) from by omega, show (6:Nat) < 6+16 from by omega,
                           show (6:Nat) - 6 = 0 from by omega,
                           List.getElem?_set, show (9:Nat) ≠ 0 from by omega,
                           show (8:Nat) ≠ 0 from by omega, show (5:Nat) ≠ 0 from by omega,
                           show (3:Nat) ≠ 0 from by omega, show (2:Nat) ≠ 0 from by omega,
                           show (1:Nat) ≠ 0 from by omega, if_false]
                simpa [Locals.get, hlparams, hllocals, show ¬(6 < 6) from by omega] using hf6
              have hshl_k : UInt32.ofNat k <<< ((2:UInt32) % 32) = 4 * UInt32.ofNat k := by
                rw [show (2:UInt32) % 32 = 2 from by decide]
                apply UInt32.toNat_inj.mp
                have hk_bnd : k < 2^30 := by have := n_out.toNat_lt; omega
                simp only [UInt32.toNat_mul, UInt32.toNat_ofNat',
                           show (4:UInt32).toNat = 4 from rfl,
                           Nat.mod_eq_of_lt (show k < 4294967296 from by omega),
                           Nat.mod_eq_of_lt (show k * 4 < 4294967296 from by omega)]
                simp [UInt32.shiftLeft, Fin.shiftLeft, Nat.shiftLeft_eq]; omega
              simp only [exec, execOne.eq_def,
                         show ({locA_out_A with values := locA_7.values} : Locals) = locA_out_A from rfl,
                         hgv4_out, hg4_out, hgv15_out, hg15_out,
                         hshl_k,
                         if_neg (show ¬((4 * UInt32.ofNat k + out_ptr).toNat +
                                         UInt32.toNat (0:UInt32) + 4 > stA.mem.pages * 65536) from by
                                   rw [show 4 * UInt32.ofNat k + out_ptr =
                                               out_ptr + 4 * UInt32.ofNat k from UInt32.add_comm _ _,
                                       show UInt32.toNat (0:UInt32) = 0 from rfl]; omega),
                         show stA.mem.write32 (4 * UInt32.ofNat k + out_ptr + (0:UInt32)) left_i = mem1_A from by
                             rw [show 4 * UInt32.ofNat k + out_ptr + (0:UInt32) =
                                         out_ptr + 4 * UInt32.ofNat k from by
                                     rw [UInt32.add_comm (4 * UInt32.ofNat k) out_ptr, UInt32.add_zero]],
                         hgv14_out, hg14_out,
                         hgv6_out, hg6_out,
                         if_neg (show ¬(frame.toNat + UInt32.toNat (8:UInt32) + 4 >
                                         {stA with mem := mem1_A}.mem.pages * 65536) from by
                                   rw [show ({stA with mem := mem1_A} : Store Unit).mem.pages =
                                         stA.mem.pages from rfl,
                                       show UInt32.toNat (8:UInt32) = 8 from by decide, hft8.symm]
                                   exact hbnd_fr8),
                         show ({stA with mem := mem1_A} : Store Unit).mem.read32 (frame + (8:UInt32)) =
                               UInt32.ofNat i from hmem1_fr8,
                         show (1:UInt32) + UInt32.ofNat i = UInt32.ofNat i + 1 from UInt32.add_comm _ _,
                         if_neg (show ¬(frame.toNat + UInt32.toNat (8:UInt32) + 4 >
                                         {stA with mem := mem1_A}.mem.pages * 65536) from by
                                   rw [show ({stA with mem := mem1_A} : Store Unit).mem.pages =
                                         stA.mem.pages from rfl,
                                       show UInt32.toNat (8:UInt32) = 8 from by decide, hft8.symm]
                                   exact hbnd_fr8),
                         show ({stA with mem := mem1_A} : Store Unit).mem.write32
                               (frame + (8:UInt32)) (UInt32.ofNat i + 1) = mem2_A from rfl,
                         show ({stA with mem := mem2_A} : Store Unit) = stA_m2 from rfl,
                         show ({locA_out_A with values := locA_out_A.values} : Locals) = locA_out_A from rfl]
            -- body1: Break(0+1) → Break 0 (B1_panic NOT reached)
            have h_B1 : exec 14 m stA locA_7 body1 env = .Break 0 stA_m2 locA_out_A := by
              rw [show (14:Nat) = 13+1 from rfl, exec_block_cons, h_B2]
            -- ── assemble: prefix → outer block (h_B1) → suffix ──
            have h_pre : exec 15 m stA locA mainMergeBody env =
                exec 15 m stA locA_7
                  (.block 0 0 body1 :: [.localGet 6, .localGet 6, .load32 (16:UInt32),
                    .const (1:UInt32), .add, .store32 (16:UInt32), .br 0]) env := by
              -- Abstract the continuation to make body1 truly opaque to simp
              have h_prefix_aux : ∀ cont : Program,
                  exec 15 m stA locA
                    ([.localGet 6, .load32 (8:UInt32), .localGet 1, .ltU,
                      .const (1:UInt32), .and, .eqz, .br_if 1,
                      .localGet 6, .load32 (12:UInt32), .localGet 3, .ltU,
                      .const (1:UInt32), .and, .eqz, .br_if 1,
                      .localGet 6, .load32 (8:UInt32), .localSet 7] ++ cont) env
                    = exec 15 m stA locA_7 cont env := by
                intro cont
                have hgv6_pre : ∀ vs, ({locA with values := vs} : Locals).get 6 = locA.get 6 := fun _ => rfl
                have hgv1_pre : ∀ vs, ({locA with values := vs} : Locals).get 1 = locA.get 1 := fun _ => rfl
                have hgv3_pre : ∀ vs, ({locA with values := vs} : Locals).get 3 = locA.get 3 := fun _ => rfl
                -- Convert ++ cont to pure cons form (by rfl, since ++ is definitional for finite lists)
                rw [show [.localGet 6, .load32 (8:UInt32), .localGet 1, .ltU,
                          .const (1:UInt32), .and, .eqz, .br_if 1,
                          .localGet 6, .load32 (12:UInt32), .localGet 3, .ltU,
                          .const (1:UInt32), .and, .eqz, .br_if 1,
                          .localGet 6, .load32 (8:UInt32), .localSet 7] ++ cont =
                         .localGet 6 :: .load32 (8:UInt32) :: .localGet 1 :: .ltU ::
                         .const (1:UInt32) :: .and :: .eqz :: .br_if 1 ::
                         .localGet 6 :: .load32 (12:UInt32) :: .localGet 3 :: .ltU ::
                         .const (1:UInt32) :: .and :: .eqz :: .br_if 1 ::
                         .localGet 6 :: .load32 (8:UInt32) :: .localSet 7 :: cont from rfl]
                -- Now simp on pure cons form: no List.cons_append needed
                simp only
                  [exec, execOne.eq_def, Locals.set?,
                   hgv6_pre, hgv1_pre, hgv3_pre,
                   hf6, h1, h3,
                   hi_m, hj_m,
                   if_neg (show ¬(frame.toNat + UInt32.toNat (8 : UInt32) + 4 > stA.mem.pages * 65536) from by
                     rw [show UInt32.toNat (8 : UInt32) = 8 from by decide, ← hft8]; exact hbnd_fr8),
                   if_pos hi_lt_u32,
                   show (1 : UInt32) &&& 1 = 1 from by decide,
                   show (if (1 : UInt32) = 0 then (1 : UInt32) else 0) = 0 from by decide,
                   if_neg (show ¬(frame.toNat + UInt32.toNat (12 : UInt32) + 4 > stA.mem.pages * 65536) from by
                     rw [show UInt32.toNat (12 : UInt32) = 12 from by decide, ← hft12]; exact hbnd_fr12),
                   if_pos hj_lt_u32,
                   hlparams, hllocals,
                   if_neg (show ¬(7 < 6) from by omega),
                   if_pos (show (7 : Nat) < 6 + 16 from by omega),
                   show (7 : Nat) - 6 = 1 from by omega]
                rfl
              exact h_prefix_aux _
            rw [h_pre, show (15:Nat) = 14+1 from rfl, exec_block_cons, h_B1]
            simp only [List.take_zero, List.drop_zero, List.nil_append]
            -- suffix: localGet 6 ×2, load32 16 (=k), const 1, add (=k+1), store32 16 (→mem3_A), br 0
            have hgv6_suf : ∀ vs, ({locA_out_A with values := vs} : Locals).get 6 = locA_out_A.get 6 := fun _ => rfl
            have hg6_suf : locA_out_A.get 6 = some (.i32 frame) := by
              simp only [Locals.get, locA_out_A, locA_out_locs, hlparams, hllocals, List.length_set,
                         show ¬(6 < 6) from by omega, show (6:Nat) < 6+16 from by omega,
                         show (6:Nat) - 6 = 0 from by omega,
                         List.getElem?_set, show (9:Nat) ≠ 0 from by omega,
                         show (8:Nat) ≠ 0 from by omega, show (5:Nat) ≠ 0 from by omega,
                         show (3:Nat) ≠ 0 from by omega, show (2:Nat) ≠ 0 from by omega,
                         show (1:Nat) ≠ 0 from by omega, if_false]
              simpa [Locals.get, hlparams, hllocals, show ¬(6 < 6) from by omega] using hf6
            simp only [exec, execOne.eq_def,
                       show ({locA_out_A with values := locA_7.values} : Locals) = locA_out_A from rfl,
                       hgv6_suf, hg6_suf,
                       if_neg (show ¬(frame.toNat + UInt32.toNat (16 : UInt32) + 4 > stA_m2.mem.pages * 65536) from by
                         rw [show stA_m2.mem.pages = stA.mem.pages from rfl,
                             show UInt32.toNat (16 : UInt32) = 16 from by decide, ← hft16]
                         exact hbnd_fr16),
                       show stA_m2.mem.read32 (frame + (16 : UInt32)) = UInt32.ofNat k from hmem2_fr16,
                       show (1 : UInt32) + UInt32.ofNat k = UInt32.ofNat (k + 1) from by
                         rw [UInt32.add_comm]; exact hk_add1,
                       show stA_m2.mem.write32 (frame + (16 : UInt32)) (UInt32.ofNat (k + 1)) = mem3_A from by
                         simp only [stA_m2, mem3_A]; rw [← hk_add1],
                       show ({stA_m2 with mem := mem3_A} : Store Unit) = stC_A from rfl,
                       show ({locA_out_A with values := locA_out_A.values} : Locals) = locA_out_A from rfl]
          obtain ⟨f_A, h_body_A⟩ := h_body_A
          -- memory reads after path A writes
          have hread8_A : stC_A.mem.read32 (frame + 8) = UInt32.ofNat (i + 1) := by
            simp only [stC_A, mem3_A, mem2_A, mem1_A]
            rw [Mem.read32_write32_of_disjoint _ (frame + 16) (frame + 8) _
                  (by right; rw [hft16, hft8]; omega),
                Mem.read32_write32_same, hi_add1]
          have hread12_A : stC_A.mem.read32 (frame + 12) = UInt32.ofNat j := by
            simp only [stC_A, mem3_A, mem2_A, mem1_A]
            rw [Mem.read32_write32_of_disjoint _ (frame + 16) (frame + 12) _
                  (by right; rw [hft16, hft12]),
                Mem.read32_write32_of_disjoint _ (frame + 8) (frame + 12) _
                  (by left; rw [hft8, hft12]),
                Mem.read32_write32_of_disjoint _ (out_ptr + 4 * UInt32.ofNat k) (frame + 12) _
                  (by rw [hout_k_toNat, hft12];
                      rcases hframe_out_disj with h | h <;> omega),
                hj_m]
          have hread16_A : stC_A.mem.read32 (frame + 16) = UInt32.ofNat (k + 1) := by
            simp only [stC_A, mem3_A]
            rw [Mem.read32_write32_same, hk_add1]
          -- locA_out_A.get 6: local[0] unchanged (set indices 1,2,3,5,8,9 ≠ 0)
          have hf6_out_A : locA_out_A.get 6 = some (.i32 frame) := by
            simp only [locA_out_A, locA_out_locs, Locals.get, hlparams, hllocals, List.length_set,
                       show ¬ (6 < 6) from by omega,
                       show 6 < 6 + 16 from by omega,
                       show 6 - 6 = 0 from by omega,
                       List.getElem?_set,
                       show (9 : Nat) ≠ 0 from by omega,
                       show (8 : Nat) ≠ 0 from by omega,
                       show (5 : Nat) ≠ 0 from by omega,
                       show (3 : Nat) ≠ 0 from by omega,
                       show (2 : Nat) ≠ 0 from by omega,
                       show (1 : Nat) ≠ 0 from by omega,
                       if_false]
            simpa [Locals.get, hlparams, hllocals,
                   show ¬ (6 < 6) from by omega] using hf6
          have hllocals_out_A : locA_out_A.locals.length = 16 := by
            simp [locA_out_A, locA_out_locs, List.length_set, hllocals]
          -- locA_out_A.get 0..5 = locA.get 0..5: params unchanged, needs hlparams for if-branch
          have hg_eq_A : ∀ n, n < 6 → locA_out_A.get n = locA.get n := fun n hn => by
            simp only [locA_out_A, Locals.get, hlparams, if_pos hn]
          have hlparams_out_A : locA_out_A.params.length = 6 := by exact hlparams
          -- invariant restoration: (i+1, j)
          have hI_A : MergeLoopInv frame out_ptr left_ptr right_ptr n_left n_right n_out
                        i₀ j₀ k₀ st stC_A locA_out_A :=
            ⟨i + 1, j, by omega, by omega, hj_lo, hj_hi,
             hread8_A, hread12_A,
             by rw [hread16_A]; congr 1; omega,
             hf6_out_A,
             (hg_eq_A 0 (by omega)).trans h0, (hg_eq_A 1 (by omega)).trans h1,
             (hg_eq_A 2 (by omega)).trans h2, (hg_eq_A 3 (by omega)).trans h3,
             (hg_eq_A 4 (by omega)).trans h4, (hg_eq_A 5 (by omega)).trans h5,
             hlparams_out_A, hllocals_out_A, ⟨v₀, hg⟩,
             fun q hq => by
               simp only [stC_A, mem3_A, mem2_A, mem1_A]
               have hliq : (left_ptr + 4 * UInt32.ofNat q).toNat = left_ptr.toNat + 4 * q :=
                 toNat_wordAddr left_ptr n_left.toNat q hq (by linarith)
               rw [Mem.read32_write32_of_disjoint _ (frame + 16) _ _
                     (by rw [hft16, hliq]; rcases hframe_left_disj with h | h <;> omega),
                   Mem.read32_write32_of_disjoint _ (frame + 8) _ _
                     (by rw [hft8, hliq]; rcases hframe_left_disj with h | h <;> omega),
                   Mem.read32_write32_of_disjoint _ (out_ptr + 4 * UInt32.ofNat k) _ _
                     (by rw [hout_k_toNat, hliq]; rcases hleft_out_disj with h | h <;> omega)]
               exact hleft q hq,
             fun q hq => by
               simp only [stC_A, mem3_A, mem2_A, mem1_A]
               have hriq : (right_ptr + 4 * UInt32.ofNat q).toNat = right_ptr.toNat + 4 * q :=
                 toNat_wordAddr right_ptr n_right.toNat q hq (by linarith)
               rw [Mem.read32_write32_of_disjoint _ (frame + 16) _ _
                     (by rw [hft16, hriq]; rcases hframe_right_disj with h | h <;> omega),
                   Mem.read32_write32_of_disjoint _ (frame + 8) _ _
                     (by rw [hft8, hriq]; rcases hframe_right_disj with h | h <;> omega),
                   Mem.read32_write32_of_disjoint _ (out_ptr + 4 * UInt32.ofNat k) _ _
                     (by rw [hout_k_toNat, hriq]; rcases hright_out_disj with h | h <;> omega)]
               exact hright q hq,
             (by
               -- content invariant: wordsAt stC_A (out+4k₀) (W+1) ++ merge(L.drop(i+1), R.drop j)
               --                  = merge(L.drop i₀, R.drop j₀)
               -- where W = (i-i₀)+(j-j₀) and the write is at out+4k (= out+4k₀+4W)
               have hW : (i + 1 - i₀) + (j - j₀) = (i - i₀) + (j - j₀) + 1 := by omega
               rw [hW]
               -- (out_ptr + 4*k₀).toNat = out_ptr.toNat + 4*k₀
               have h_k₀_addr : (out_ptr + 4 * UInt32.ofNat k₀).toNat = out_ptr.toNat + 4 * k₀ :=
                 toNat_wordAddr out_ptr n_out.toNat k₀ (by have := hk_val; omega) (by linarith)
               -- bound for the output region
               have hout_bnd : (out_ptr + 4 * UInt32.ofNat k₀).toNat + 4 * ((i - i₀) + (j - j₀) + 1) ≤ 4294967296 := by
                 rw [h_k₀_addr]; have := hk_val; omega
               -- wordsAt stC_A (out+4k₀) (W+1) = wordsAt stA (out+4k₀) W ++ [left_i]
               have hwords : wordsAt stC_A.mem (out_ptr + 4 * UInt32.ofNat k₀) ((i - i₀) + (j - j₀) + 1) =
                   wordsAt stA.mem (out_ptr + 4 * UInt32.ofNat k₀) ((i - i₀) + (j - j₀)) ++ [left_i] := by
                 simp only [stC_A, mem3_A, mem2_A, mem1_A]
                 -- remove frame+16 and frame+8 writes (disjoint from out region)
                 rw [wordsAt_write32_of_disjoint _ _ (frame + 16) _ _ hout_bnd
                       (by rw [hft16, h_k₀_addr]; rcases hframe_out_disj with h | h <;> [left; right] <;> omega),
                     wordsAt_write32_of_disjoint _ _ (frame + 8) _ _ hout_bnd
                       (by rw [hft8, h_k₀_addr]; rcases hframe_out_disj with h | h <;> [left; right] <;> omega),
                     wordsAt_split _ _ _ ((i - i₀) + (j - j₀)) (by omega)]
                 simp only [show (i - i₀) + (j - j₀) + 1 - ((i - i₀) + (j - j₀)) = 1 from by omega]
                 congr 1
                 · -- write at out+4k disjoint from [out+4k₀, out+4k₀+4W)
                   rw [wordsAt_write32_of_disjoint _ _ (out_ptr + 4 * UInt32.ofNat k) _ _
                         (by omega)
                         (by right; rw [h_k₀_addr, hout_k_toNat]; omega)]
                 · -- write at out+4k (= out+4k₀+4W); read gives left_i
                   have hbase_W : out_ptr + 4 * UInt32.ofNat k₀ + 4 * UInt32.ofNat ((i - i₀) + (j - j₀)) =
                       out_ptr + 4 * UInt32.ofNat k := by
                     have hkeq : k₀ + ((i - i₀) + (j - j₀)) = k := by omega
                     rw [UInt32.add_assoc, ← UInt32.mul_add, ← UInt32.ofNat_add, hkeq]
                   rw [hbase_W]; simp [wordsAt, Mem.read32_write32_same]
               -- assemble: [left_i] ++ merge(L.drop(i+1), R.drop j) = left_i :: merge(...)
               rw [hwords, List.append_assoc, List.singleton_append]
               -- rewrite RHS using hcontent (reversed): merge(L.drop i₀, R.drop j₀)
               --   = wordsAt stA W ++ merge(L.drop i, R.drop j)
               conv_rhs => rw [← hcontent]
               congr 1
               -- left_i :: merge(L.drop(i+1), R.drop j) = merge(L.drop i, R.drop j)
               -- prove via merge_cons_le + List.drop_eq_getElem_cons
               have hL_drop_i : (wordsAt st.mem left_ptr n_left.toNat).drop i =
                   st.mem.read32 (left_ptr + 4 * UInt32.ofNat i) ::
                   (wordsAt st.mem left_ptr n_left.toNat).drop (i + 1) := by
                 have h1 : i < (wordsAt st.mem left_ptr n_left.toNat).length := by
                   simp [wordsAt_length]; exact hlt_i
                 rw [List.drop_eq_getElem_cons h1, wordsAt_getElem _ _ _ _ hlt_i]
               have hR_drop_j : (wordsAt st.mem right_ptr n_right.toNat).drop j =
                   st.mem.read32 (right_ptr + 4 * UInt32.ofNat j) ::
                   (wordsAt st.mem right_ptr n_right.toNat).drop (j + 1) := by
                 have h2 : j < (wordsAt st.mem right_ptr n_right.toNat).length := by
                   simp [wordsAt_length]; exact hlt_j
                 rw [List.drop_eq_getElem_cons h2, wordsAt_getElem _ _ _ _ hlt_j]
               have hleft_i_eq : left_i = st.mem.read32 (left_ptr + 4 * UInt32.ofNat i) :=
                 hleft i hlt_i
               have hle_st : st.mem.read32 (left_ptr + 4 * UInt32.ofNat i) ≤
                   st.mem.read32 (right_ptr + 4 * UInt32.ofNat j) := by
                 rw [← hleft i hlt_i, ← hright j hlt_j]; exact hle
               rw [hleft_i_eq, hL_drop_i, hR_drop_j, merge_cons_le hle_st]),
             by simp [stC_A, mem3_A, mem2_A, mem1_A, Mem.write32_pages, hpages],
             hk_global,
             by simp [stC_A, mem3_A, mem2_A, mem1_A, Mem.write32_pages, hleft_global],
             by simp [stC_A, mem3_A, mem2_A, mem1_A, Mem.write32_pages, hright_global],
             by simp [stC_A, mem3_A, mem2_A, mem1_A, Mem.write32_pages, hout_global],
             hpages_u32, hleft_out_disj, hright_out_disj, hleft_right_disj,
             hframe_left_disj, hframe_right_disj, hframe_out_disj⟩
          -- measure decrease
          have hμ_A : (n_left.toNat - (stC_A.mem.read32 (frame + 8)).toNat) +
                      (n_right.toNat - (stC_A.mem.read32 (frame + 12)).toNat) < n := by
            rw [hread8_A, hread12_A, UInt32.toNat_ofNat', UInt32.toNat_ofNat',
                Nat.mod_eq_of_lt (by have := n_left.toNat_lt; omega),
                Nat.mod_eq_of_lt (by have := n_right.toNat_lt; omega),
                ← hμ, hi_m, hj_m, UInt32.toNat_ofNat', UInt32.toNat_ofNat',
                Nat.mod_eq_of_lt (by have := n_left.toNat_lt; omega),
                Nat.mod_eq_of_lt (by have := n_right.toNat_lt; omega)]
            omega
          -- IH at reduced measure: input is (stC_A, locA_out_A)
          obtain ⟨f_rest, hf_rest⟩ := IH _ hμ_A stC_A locA_out_A hI_A rfl
          -- Fuel composition: one body iteration at stA then IH fuel at stC_A
          have hbody_ne : exec f_A m stA locA mainMergeBody env ≠ .OutOfFuel := by
            simp [h_body_A]
          have hfuel_ne : exec f_rest m stC_A locA_out_A [.block 0 0 [.loop 0 0 mainMergeBody]] env ≠ .OutOfFuel :=
            fun h => by rw [h] at hf_rest; exact hf_rest
          have hbody_mono : exec (max f_A f_rest) m stA locA mainMergeBody env = .Break 0 stC_A locA_out_A :=
            (exec_fuel_mono (Nat.le_max_left f_A f_rest) hbody_ne).trans h_body_A
          have hblock_mono : exec (max f_A f_rest + 1) m stC_A locA_out_A [.block 0 0 [.loop 0 0 mainMergeBody]] env =
              exec f_rest m stC_A locA_out_A [.block 0 0 [.loop 0 0 mainMergeBody]] env :=
            exec_fuel_mono (by omega) hfuel_ne
          have hloop_single : ∀ F stT locT,
              exec F m stT locT [.loop 0 0 mainMergeBody] env =
              execOne F m stT locT (.loop 0 0 mainMergeBody) env := fun F stT locT => by
            cases F with
            | zero => simp [exec, execOne]
            | succ f =>
              simp only [exec]
              rcases execOne (f + 1) m stT locT (.loop 0 0 mainMergeBody) env with
                ⟨_, _⟩ | ⟨_, _, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_⟩ | _
              · rfl
              all_goals rfl
          have hloop_eq : exec (max f_A f_rest + 1) m stA locA [.loop 0 0 mainMergeBody] env =
              exec (max f_A f_rest) m stC_A locA_out_A [.loop 0 0 mainMergeBody] env := by
            rw [hloop_single, hloop_single]
            conv_lhs => rw [execOne_loop_succ]
            simp only [hbody_mono, List.take_zero, List.nil_append, List.drop_zero]
            -- {locA_out_A with values := locA.values} = locA_out_A by rfl:
            -- locA_out_A = {locA with locals := ...}, so .values = locA.values definitionally
            rfl
          have heq : exec (max f_A f_rest + 2) m stA locA [.block 0 0 [.loop 0 0 mainMergeBody]] env =
              exec (max f_A f_rest + 1) m stC_A locA_out_A [.block 0 0 [.loop 0 0 mainMergeBody]] env := by
            rw [show max f_A f_rest + 2 = max f_A f_rest + 1 + 1 from rfl]
            conv_lhs => rw [exec_block_cons, hloop_eq]
            conv_rhs => rw [exec_block_cons]
            set discr := exec (max f_A f_rest) m stC_A locA_out_A [.loop 0 0 mainMergeBody] env
            rcases discr with ⟨r', s'⟩ | ⟨n, r', s'⟩ | ⟨r', vs⟩ | ⟨r', msg⟩ | ⟨msg⟩ | _
            · simp [exec, locA_out_A, locA_out_locs]
            · cases n with | zero => simp [exec, locA_out_A, locA_out_locs] | succ k => rfl
            all_goals rfl
          exact ⟨max f_A f_rest + 2, by rw [heq, hblock_mono]; exact hf_rest⟩
        · -- ── path B: left[i] > right[j]: copy right[j] to out[k], j++, k++ ──
          let mem1_B := stA.mem.write32 (out_ptr + 4 * UInt32.ofNat k) right_j
          let mem2_B := mem1_B.write32 (frame + 12) (UInt32.ofNat j + 1)
          let mem3_B := mem2_B.write32 (frame + 16) (UInt32.ofNat k + 1)
          let stC_B : Store Unit := { stA with mem := mem3_B }
          -- Result locals: localSet 7(→local[1]) 8(→local[2]) 9(→local[3])
          --                       10(→local[4]) 12(→local[6]) 13(→local[7])
          let locB_out_locs :=
            locA.locals.set 1 (.i32 (UInt32.ofNat i)) |>.set 2 (.i32 left_i)
              |>.set 3 (.i32 (UInt32.ofNat j)) |>.set 4 (.i32 (UInt32.ofNat j))
              |>.set 6 (.i32 right_j) |>.set 7 (.i32 (UInt32.ofNat k))
          let locB_out_B : Locals := { locA with locals := locB_out_locs }
          -- exec trace (staged through 14 nested blocks)
          have h_body_B : ∃ f_B,
              exec f_B m stA locA mainMergeBody env = .Break 0 stC_B locB_out_B := by
            refine ⟨15, ?_⟩
            -- ── body let-bindings (same definitions as Path A) ──
            let body14 : Program := [
              .localGet 7, .localGet 1, .ltU, .const (1:UInt32), .and, .eqz, .br_if 0,
              .localGet 0, .localGet 7, .const (2:UInt32), .shl, .add,
              .load32 (0:UInt32), .localSet 8,
              .localGet 6, .load32 (12:UInt32), .localSet 9,
              .localGet 9, .localGet 3, .ltU, .const (1:UInt32), .and, .br_if 1, .br 2]
            let body13 : Program := [.block 0 0 body14,
              .localGet 7, .localGet 1, .const (1048712:UInt32), .call 87, .unreachable]
            let body12 : Program := [.block 0 0 body13,
              .localGet 8, .localGet 2, .localGet 9, .const (2:UInt32), .shl, .add,
              .load32 (0:UInt32), .leU, .const (1:UInt32), .and, .br_if 2, .br 1]
            let body11 : Program := [.block 0 0 body12,
              .localGet 9, .localGet 3, .const (1048728:UInt32), .call 87, .unreachable]
            let body10 : Program := [.block 0 0 body11,
              .localGet 6, .load32 (12:UInt32), .localSet 10,
              .localGet 10, .localGet 3, .ltU, .const (1:UInt32), .and, .br_if 1, .br 2]
            let body9 : Program := [.block 0 0 body10,
              .localGet 6, .load32 (8:UInt32), .localSet 11,
              .localGet 11, .localGet 1, .ltU, .const (1:UInt32), .and, .br_if 4, .br 5]
            let body8 : Program := [.block 0 0 body9,
              .localGet 2, .localGet 10, .const (2:UInt32), .shl, .add,
              .load32 (0:UInt32), .localSet 12,
              .localGet 6, .load32 (16:UInt32), .localSet 13,
              .localGet 13, .localGet 5, .ltU, .const (1:UInt32), .and, .br_if 1, .br 2]
            let body7 : Program := [.block 0 0 body8,
              .localGet 10, .localGet 3, .const (1048744:UInt32), .call 87, .unreachable]
            let body6 : Program := [.block 0 0 body7,
              .localGet 4, .localGet 13, .const (2:UInt32), .shl, .add,
              .localGet 12, .store32 (0:UInt32),
              .localGet 6, .localGet 6, .load32 (12:UInt32),
              .const (1:UInt32), .add, .store32 (12:UInt32), .br 5]
            let body5 : Program := [.block 0 0 body6,
              .localGet 13, .localGet 5, .const (1048760:UInt32), .call 87, .unreachable]
            let body4 : Program := [.block 0 0 body5,
              .localGet 0, .localGet 11, .const (2:UInt32), .shl, .add,
              .load32 (0:UInt32), .localSet 14,
              .localGet 6, .load32 (16:UInt32), .localSet 15,
              .localGet 15, .localGet 5, .ltU, .const (1:UInt32), .and, .br_if 1, .br 2]
            let body3 : Program := [.block 0 0 body4,
              .localGet 11, .localGet 1, .const (1048776:UInt32), .call 87, .unreachable]
            let body2 : Program := [.block 0 0 body3,
              .localGet 4, .localGet 15, .const (2:UInt32), .shl, .add,
              .localGet 14, .store32 (0:UInt32),
              .localGet 6, .localGet 6, .load32 (8:UInt32),
              .const (1:UInt32), .add, .store32 (8:UInt32), .br 1]
            let body1 : Program := [.block 0 0 body2,
              .localGet 15, .localGet 5, .const (1048792:UInt32), .call 87, .unreachable]
            -- ── intermediate Locals states ──
            let locA_7 : Locals :=
              { locA with locals := locA.locals.set 1 (.i32 (UInt32.ofNat i)) }
            let locA_89_locs :=
              locA.locals.set 1 (.i32 (UInt32.ofNat i)) |>.set 2 (.i32 left_i)
                |>.set 3 (.i32 (UInt32.ofNat j))
            let locA_89 : Locals := { locA with locals := locA_89_locs }
            -- Path B: after body10 localSet 10: local[4] = j
            let locA_10_B : Locals :=
              { locA with locals := locA_89_locs.set 4 (.i32 (UInt32.ofNat j)) }
            -- Path B: after body8 localSet 12,13: local[6]=right_j, local[7]=k
            let locA_1213_B_locs :=
              locA_89_locs.set 4 (.i32 (UInt32.ofNat j))
                |>.set 6 (.i32 right_j) |>.set 7 (.i32 (UInt32.ofNat k))
            let locA_1213_B : Locals := { locA with locals := locA_1213_B_locs }
            -- store after B6: out[k]=right_j written, frame+12=j+1 written
            let stA_m2_B : Store Unit := { stA with mem := mem2_B }
            -- ── auxiliary lemmas ──
            have hi_lt_u32 : UInt32.ofNat i < n_left := by
              rw [UInt32.lt_iff_toNat_lt_toNat, UInt32.toNat_ofNat']
              have := n_left.toNat_lt; omega
            have hj_lt_u32 : UInt32.ofNat j < n_right := by
              rw [UInt32.lt_iff_toNat_lt_toNat, UInt32.toNat_ofNat']
              have := n_right.toNat_lt; omega
            have hk_lt_u32 : UInt32.ofNat k < n_out := by
              rw [UInt32.lt_iff_toNat_lt_toNat, UInt32.toNat_ofNat']
              have := n_out.toNat_lt; omega
            have hbnd_out_k : ¬((out_ptr + 4 * UInt32.ofNat k).toNat + 4 > stA.mem.pages * 65536) := by
              rw [hout_k_toNat]; omega
            have hbnd_fr8 : ¬((frame + 8).toNat + 4 > stA.mem.pages * 65536) := by
              rw [hft8]; omega
            have hbnd_fr12 : ¬((frame + 12).toNat + 4 > stA.mem.pages * 65536) := by
              rw [hft12]; omega
            have hbnd_fr16 : ¬((frame + 16).toNat + 4 > stA.mem.pages * 65536) := by
              rw [hft16]; omega
            have hbnd_left_i : ¬((left_ptr + 4 * UInt32.ofNat i).toNat + 4 > stA.mem.pages * 65536) := by
              rw [toNat_wordAddr left_ptr n_left.toNat i hlt_i (by linarith)]; omega
            have hbnd_right_j : ¬((right_ptr + 4 * UInt32.ofNat j).toNat + 4 > stA.mem.pages * 65536) := by
              rw [toNat_wordAddr right_ptr n_right.toNat j hlt_j (by linarith)]; omega
            have hmem1_B_fr12 : mem1_B.read32 (frame + 12) = UInt32.ofNat j := by
              simp only [mem1_B,
                Mem.read32_write32_of_disjoint _ (out_ptr + 4 * UInt32.ofNat k) (frame + 12) _
                  (by rw [hout_k_toNat, hft12]; rcases hframe_out_disj with h | h <;> omega)]
              exact hj_m
            have hmem2_B_fr16 : mem2_B.read32 (frame + 16) = UInt32.ofNat k := by
              simp only [mem2_B,
                Mem.read32_write32_of_disjoint _ (frame + 12) (frame + 16) _
                  (by left; rw [hft12, hft16])]
              simp only [mem1_B,
                Mem.read32_write32_of_disjoint _ (out_ptr + 4 * UInt32.ofNat k) (frame + 16) _
                  (by rw [hout_k_toNat, hft16]; rcases hframe_out_disj with h | h <;> omega)]
              exact hk_m
            -- ── exec chain through 14 blocks ──
            -- body14: same as Path A (loads left_i→local8, j→local9; br_if 1 fires) → Break 1
            have h_B14_B : exec 1 m stA locA_7 body14 env = .Break 1 stA locA_89 := by
              have hgv7_7 : ∀ vs, ({locA_7 with values := vs} : Locals).get 7 = locA_7.get 7 := fun _ => rfl
              have hgv1_7 : ∀ vs, ({locA_7 with values := vs} : Locals).get 1 = locA_7.get 1 := fun _ => rfl
              have hgv0_7 : ∀ vs, ({locA_7 with values := vs} : Locals).get 0 = locA_7.get 0 := fun _ => rfl
              have hgv6_7 : ∀ vs, ({locA_7 with values := vs} : Locals).get 6 = locA_7.get 6 := fun _ => rfl
              have hgv3_7 : ∀ vs, ({locA_7 with values := vs} : Locals).get 3 = locA_7.get 3 := fun _ => rfl
              have hlp_7 : locA_7.params.length = 6  := hlparams
              have hll_7 : locA_7.locals.length = 16 := by simp [locA_7, List.length_set, hllocals]
              have hg7_7 : locA_7.get 7 = some (.i32 (UInt32.ofNat i)) := by
                simp only [Locals.get, hlp_7, hll_7, List.length_set,
                           show ¬(7 < 6) from by omega, show (7 : Nat) < 6 + 16 from by omega,
                           show (7 : Nat) - 6 = 1 from by omega]
                change (locA.locals.set 1 (.i32 (UInt32.ofNat i)))[1]? = _
                exact List.getElem?_set_self (by rw [hllocals]; norm_num)
              have hg1_7 : locA_7.get 1 = some (.i32 n_left) := by
                simp only [Locals.get, locA_7, hlparams, show (1 : Nat) < 6 from by omega] at h1 ⊢
                exact h1
              have hg0_7 : locA_7.get 0 = some (.i32 left_ptr) := by
                simp only [Locals.get, locA_7, hlparams, show (0 : Nat) < 6 from by omega] at h0 ⊢
                exact h0
              have hg6_7 : locA_7.get 6 = some (.i32 frame) := by
                have h : locA_7.get 6 = locA.get 6 := by
                  simp [locA_7, Locals.get, hlparams, hllocals, List.length_set, List.getElem?_set]
                rw [h]; exact hf6
              have hg3_7 : locA_7.get 3 = some (.i32 n_right) := by
                simp only [Locals.get, locA_7, hlparams, show (3 : Nat) < 6 from by omega] at h3 ⊢
                exact h3
              have hg6_8_raw : ∀ vs,
                  (Locals.mk locA_7.params (locA_7.locals.set 2 (.i32 left_i)) vs).get 6
                  = some (.i32 frame) := by
                intro vs
                have h : (Locals.mk locA_7.params (locA_7.locals.set 2 (.i32 left_i)) vs).get 6
                    = locA.get 6 := by
                  simp [locA_7, Locals.get, hlparams, hllocals, List.length_set, List.getElem?_set]
                rw [h]; exact hf6
              have hg9_89_raw : ∀ vs,
                  (Locals.mk locA_7.params
                    ((locA_7.locals.set 2 (.i32 left_i)).set 3 (.i32 (UInt32.ofNat j))) vs).get 9
                  = some (.i32 (UInt32.ofNat j)) := by
                intro vs
                simp only [Locals.get, hlp_7, hll_7, List.length_set,
                           show ¬(9 < 6) from by omega, show (9 : Nat) < 6 + 16 from by omega,
                           show (9 : Nat) - 6 = 3 from by omega]
                exact List.getElem?_set_self (by simp [List.length_set, hll_7])
              have hg3_89_raw : ∀ vs,
                  (Locals.mk locA_7.params
                    ((locA_7.locals.set 2 (.i32 left_i)).set 3 (.i32 (UInt32.ofNat j))) vs).get 3
                  = some (.i32 n_right) := by
                intro vs
                have h3_raw : locA.params[3]? = some (.i32 n_right) := by
                  have h := h3
                  simp only [Locals.get, hlparams, show (3 : Nat) < 6 from by omega] at h
                  exact h
                simp only [Locals.get, hlp_7, show (3 : Nat) < 6 from by omega]
                exact h3_raw
              have hshl_i : UInt32.ofNat i <<< ((2 : UInt32) % 32) = 4 * UInt32.ofNat i := by
                rw [show (2 : UInt32) % 32 = 2 from by decide]
                apply UInt32.toNat_inj.mp
                have hi_bnd : i < 2 ^ 30 := by have := n_left.toNat_lt; omega
                simp only [UInt32.toNat_mul, UInt32.toNat_ofNat',
                           show (4 : UInt32).toNat = 4 from rfl,
                           Nat.mod_eq_of_lt (show i < 4294967296 from by omega),
                           Nat.mod_eq_of_lt (show i * 4 < 4294967296 from by omega)]
                simp [UInt32.shiftLeft, Fin.shiftLeft, Nat.shiftLeft_eq]; omega
              have hshl_j_14 : UInt32.ofNat j <<< ((2 : UInt32) % 32) = 4 * UInt32.ofNat j := by
                rw [show (2 : UInt32) % 32 = 2 from by decide]
                apply UInt32.toNat_inj.mp
                have hj_bnd : j < 2 ^ 30 := by have := n_right.toNat_lt; omega
                simp only [UInt32.toNat_mul, UInt32.toNat_ofNat',
                           show (4 : UInt32).toNat = 4 from rfl,
                           Nat.mod_eq_of_lt (show j < 4294967296 from by omega),
                           Nat.mod_eq_of_lt (show j * 4 < 4294967296 from by omega)]
                simp [UInt32.shiftLeft, Fin.shiftLeft, Nat.shiftLeft_eq]; omega
              simp only [exec, execOne.eq_def, body14, Locals.set?,
                         hgv7_7, hgv1_7, hgv0_7, hgv6_7, hgv3_7,
                         hg7_7, hg1_7, hg0_7, hg6_7, hg3_7,
                         if_pos hi_lt_u32,
                         show (1 : UInt32) &&& 1 = 1 from by decide,
                         show (if (1 : UInt32) = 0 then (1 : UInt32) else 0) = 0 from by decide,
                         hshl_i,
                         if_neg (show ¬((4 * UInt32.ofNat i + left_ptr).toNat +
                                         UInt32.toNat (0 : UInt32) + 4 > stA.mem.pages * 65536) from by
                                   rw [show 4 * UInt32.ofNat i + left_ptr =
                                           left_ptr + 4 * UInt32.ofNat i from UInt32.add_comm _ _,
                                       show UInt32.toNat (0 : UInt32) = 0 from rfl]; omega),
                         show stA.mem.read32 (4 * UInt32.ofNat i + left_ptr + (0 : UInt32)) = left_i from by
                           rw [show 4 * UInt32.ofNat i + left_ptr + (0 : UInt32) =
                                   left_ptr + 4 * UInt32.ofNat i from by
                               rw [UInt32.add_comm (4 * UInt32.ofNat i) left_ptr, UInt32.add_zero]],
                         hlp_7, hll_7, List.length_set,
                         if_neg (show ¬(8 < 6) from by omega),
                         if_pos (show (8 : Nat) < 6 + 16 from by omega),
                         show (8 : Nat) - 6 = 2 from by omega,
                         hg6_8_raw,
                         if_neg (show ¬(frame.toNat + (12 : UInt32).toNat + 4 > stA.mem.pages * 65536)
                                   from by simp only [show (12 : UInt32).toNat = 12 from by decide]; omega),
                         show stA.mem.read32 (frame + (12 : UInt32)) = UInt32.ofNat j from hj_m,
                         if_neg (show ¬(9 < 6) from by omega),
                         if_pos (show (9 : Nat) < 6 + 16 from by omega),
                         show (9 : Nat) - 6 = 3 from by omega,
                         hg9_89_raw, hg3_89_raw,
                         if_pos hj_lt_u32,
                         show (1 : UInt32) &&& 1 = 1 from by decide,
                         show Locals.mk locA_7.params
                               ((locA_7.locals.set 2 (.i32 left_i)).set 3 (.i32 (UInt32.ofNat j)))
                               locA.values = locA_89 from rfl]
              rfl
            -- body13: Break(0+1) from body14 → Break 0
            have h_B13_B : exec 2 m stA locA_7 body13 env = .Break 0 stA locA_89 := by
              rw [show (2:Nat) = 1+1 from rfl, exec_block_cons, h_B14_B]
            -- body12: ¬hle (left_i > right_j): br_if 2 NOT taken, br 1 → Break 1
            have h_B12_B : exec 3 m stA locA_7 body12 env = .Break 1 stA locA_89 := by
              rw [show (3:Nat) = 2+1 from rfl, exec_block_cons, h_B13_B]
              simp only [List.take_zero, List.drop_zero, List.nil_append]
              have hll_89 : locA_89.locals.length = 16 := by
                simp [locA_89, locA_89_locs, List.length_set, hllocals]
              have hgv8_89 : ∀ vs, ({locA_89 with values := vs} : Locals).get 8 = locA_89.get 8 := fun _ => rfl
              have hgv2_89 : ∀ vs, ({locA_89 with values := vs} : Locals).get 2 = locA_89.get 2 := fun _ => rfl
              have hgv9_89 : ∀ vs, ({locA_89 with values := vs} : Locals).get 9 = locA_89.get 9 := fun _ => rfl
              have hg8_89 : locA_89.get 8 = some (.i32 left_i) := by
                simp only [Locals.get, locA_89, locA_89_locs, hlparams, hllocals, List.length_set,
                           show ¬(8 < 6) from by omega, show (8:Nat) < 6+16 from by omega,
                           show (8:Nat) - 6 = 2 from by omega]
                rw [List.getElem?_set_ne (show (3:Nat) ≠ 2 from by omega)]
                exact List.getElem?_set_self (by rw [List.length_set, hllocals]; norm_num)
              have hg2_89 : locA_89.get 2 = some (.i32 right_ptr) := by
                simp only [Locals.get, locA_89, hlparams, show (2:Nat) < 6 from by omega] at h2 ⊢
                exact h2
              have hg9_89 : locA_89.get 9 = some (.i32 (UInt32.ofNat j)) := by
                simp only [Locals.get, locA_89, locA_89_locs, hlparams, hllocals, List.length_set,
                           show ¬(9 < 6) from by omega, show (9:Nat) < 6+16 from by omega,
                           show (9:Nat) - 6 = 3 from by omega]
                exact List.getElem?_set_self (by rw [List.length_set, List.length_set, hllocals]; norm_num)
              have hshl_j : UInt32.ofNat j <<< ((2:UInt32) % 32) = 4 * UInt32.ofNat j := by
                rw [show (2:UInt32) % 32 = 2 from by decide]
                apply UInt32.toNat_inj.mp
                have hj_bnd : j < 2^30 := by have := n_right.toNat_lt; omega
                simp only [UInt32.toNat_mul, UInt32.toNat_ofNat',
                           show (4:UInt32).toNat = 4 from rfl,
                           Nat.mod_eq_of_lt (show j < 4294967296 from by omega),
                           Nat.mod_eq_of_lt (show j*4 < 4294967296 from by omega)]
                simp [UInt32.shiftLeft, Fin.shiftLeft, Nat.shiftLeft_eq]; omega
              simp only [exec, execOne.eq_def,
                         show ({locA_89 with values := locA_7.values} : Locals) = locA_89 from rfl,
                         hgv8_89, hgv2_89, hgv9_89,
                         hg8_89, hg2_89, hg9_89,
                         hshl_j,
                         if_neg (show ¬((4 * UInt32.ofNat j + right_ptr).toNat +
                                         UInt32.toNat (0:UInt32) + 4 > stA.mem.pages * 65536) from by
                                   rw [show 4 * UInt32.ofNat j + right_ptr =
                                               right_ptr + 4 * UInt32.ofNat j from UInt32.add_comm _ _,
                                       show UInt32.toNat (0:UInt32) = 0 from rfl]
                                   exact hbnd_right_j),
                         show stA.mem.read32 (4 * UInt32.ofNat j + right_ptr + (0:UInt32)) = right_j from by
                             rw [show 4 * UInt32.ofNat j + right_ptr + (0:UInt32) =
                                         right_ptr + 4 * UInt32.ofNat j from by
                                     rw [UInt32.add_comm (4 * UInt32.ofNat j) right_ptr, UInt32.add_zero]],
                         if_neg hle,
                         show (1:UInt32) &&& 0 = 0 from by decide,
                         show ({locA_89 with values := locA.values} : Locals) = locA_89 from rfl]
            -- body11: Break(0+1) from body12 → Break 0
            have h_B11_B : exec 4 m stA locA_7 body11 env = .Break 0 stA locA_89 := by
              rw [show (4:Nat) = 3+1 from rfl, exec_block_cons, h_B12_B]
            -- body10: Break 0 → B10_right_cont: localGet6, load32_12(j)→localSet10, j<n_right br_if1 → Break 1
            have h_B10_B : exec 5 m stA locA_7 body10 env = .Break 1 stA locA_10_B := by
              rw [show (5:Nat) = 4+1 from rfl, exec_block_cons, h_B11_B]
              simp only [List.take_zero, List.drop_zero, List.nil_append]
              have hlp_89 : locA_89.params.length = 6 := hlparams
              have hll_89 : locA_89.locals.length = 16 := by
                simp [locA_89, locA_89_locs, List.length_set, hllocals]
              have hgv6_89 : ∀ vs, ({locA_89 with values := vs} : Locals).get 6 = locA_89.get 6 := fun _ => rfl
              have hg6_89 : locA_89.get 6 = some (.i32 frame) := by
                simp only [Locals.get, locA_89, locA_89_locs, hlparams, hllocals, List.length_set,
                           show ¬(6 < 6) from by omega, show (6:Nat) < 6+16 from by omega,
                           show (6:Nat) - 6 = 0 from by omega]
                rw [List.getElem?_set_ne (show (3:Nat) ≠ 0 from by omega)]
                rw [List.getElem?_set_ne (show (2:Nat) ≠ 0 from by omega)]
                rw [List.getElem?_set_ne (show (1:Nat) ≠ 0 from by omega)]
                simpa [Locals.get, hlparams, hllocals, show ¬(6 < 6) from by omega] using hf6
              have hgv10_10B : ∀ vs, ({locA_10_B with values := vs} : Locals).get 10 = locA_10_B.get 10 := fun _ => rfl
              have hgv3_10B  : ∀ vs, ({locA_10_B with values := vs} : Locals).get 3  = locA_10_B.get 3  := fun _ => rfl
              have hg10_10B : locA_10_B.get 10 = some (.i32 (UInt32.ofNat j)) := by
                simp only [Locals.get, locA_10_B, locA_89_locs, hlparams, hllocals, List.length_set,
                           show ¬(10 < 6) from by omega, show (10:Nat) < 6+16 from by omega,
                           show (10:Nat) - 6 = 4 from by omega]
                exact List.getElem?_set_self
                  (by rw [List.length_set, List.length_set, List.length_set, hllocals]; norm_num)
              have hg3_10B : locA_10_B.get 3 = some (.i32 n_right) := by
                simp only [Locals.get, locA_10_B, hlparams, show (3:Nat) < 6 from by omega] at h3 ⊢
                exact h3
              simp only [exec, execOne.eq_def,
                         show ({locA_89 with values := locA_7.values} : Locals) = locA_89 from rfl,
                         hgv6_89, hg6_89,
                         if_neg (show ¬(frame.toNat + UInt32.toNat (12:UInt32) + 4 > stA.mem.pages * 65536) from by
                                   simp only [show (12:UInt32).toNat = 12 from by decide]; omega),
                         show stA.mem.read32 (frame + (12:UInt32)) = UInt32.ofNat j from hj_m,
                         Locals.set?,
                         hlp_89, hll_89, List.length_set,
                         if_neg (show ¬(10 < 6) from by omega),
                         if_pos (show (10:Nat) < 6+16 from by omega),
                         show (10:Nat) - 6 = 4 from by omega,
                         show Locals.mk locA_89.params (locA_89.locals.set 4 (.i32 (UInt32.ofNat j)))
                               locA_89.values = locA_10_B from rfl,
                         hgv10_10B, hg10_10B, hgv3_10B, hg3_10B,
                         if_pos hj_lt_u32,
                         show (1:UInt32) &&& 1 = 1 from by decide,
                         show ({locA_10_B with values := locA_10_B.values} : Locals) = locA_10_B from rfl]
              rfl
            -- body9: Break(0+1) from body10 → Break 0
            have h_B9_B : exec 6 m stA locA_7 body9 env = .Break 0 stA locA_10_B := by
              rw [show (6:Nat) = 5+1 from rfl, exec_block_cons, h_B10_B]
            -- body8: Break 0 → B8_right_load: load right[j]→local12, k→local13, k<n_out br_if1 → Break 1
            have h_B8_B : exec 7 m stA locA_7 body8 env = .Break 1 stA locA_1213_B := by
              rw [show (7:Nat) = 6+1 from rfl, exec_block_cons, h_B9_B]
              simp only [List.take_zero, List.drop_zero, List.nil_append]
              have hlp_10B : locA_10_B.params.length = 6 := hlparams
              have hll_10B : locA_10_B.locals.length = 16 := by
                simp [locA_10_B, locA_89_locs, List.length_set, hllocals]
              have hgv2_10B  : ∀ vs, ({locA_10_B with values := vs} : Locals).get 2  = locA_10_B.get 2  := fun _ => rfl
              have hgv10_10B : ∀ vs, ({locA_10_B with values := vs} : Locals).get 10 = locA_10_B.get 10 := fun _ => rfl
              have hg2_10B : locA_10_B.get 2 = some (.i32 right_ptr) := by
                simp only [Locals.get, locA_10_B, hlparams, show (2:Nat) < 6 from by omega] at h2 ⊢
                exact h2
              have hg10_10B : locA_10_B.get 10 = some (.i32 (UInt32.ofNat j)) := by
                simp only [Locals.get, locA_10_B, locA_89_locs, hlparams, hllocals, List.length_set,
                           show ¬(10 < 6) from by omega, show (10:Nat) < 6+16 from by omega,
                           show (10:Nat) - 6 = 4 from by omega]
                exact List.getElem?_set_self
                  (by rw [List.length_set, List.length_set, List.length_set, hllocals]; norm_num)
              have hshl_j : UInt32.ofNat j <<< ((2:UInt32) % 32) = 4 * UInt32.ofNat j := by
                rw [show (2:UInt32) % 32 = 2 from by decide]
                apply UInt32.toNat_inj.mp
                have hj_bnd : j < 2^30 := by have := n_right.toNat_lt; omega
                simp only [UInt32.toNat_mul, UInt32.toNat_ofNat',
                           show (4:UInt32).toNat = 4 from rfl,
                           Nat.mod_eq_of_lt (show j < 4294967296 from by omega),
                           Nat.mod_eq_of_lt (show j*4 < 4294967296 from by omega)]
                simp [UInt32.shiftLeft, Fin.shiftLeft, Nat.shiftLeft_eq]; omega
              have hg6_12B_raw : ∀ vs,
                  (Locals.mk locA_10_B.params (locA_10_B.locals.set 6 (.i32 right_j)) vs).get 6
                  = some (.i32 frame) := by
                intro vs
                have h : (Locals.mk locA_10_B.params (locA_10_B.locals.set 6 (.i32 right_j)) vs).get 6
                    = locA.get 6 := by
                  simp [locA_10_B, locA_89_locs, Locals.get, hlparams, hllocals,
                        List.length_set, List.getElem?_set]
                rw [h]; exact hf6
              have hg13_1213_raw : ∀ vs,
                  (Locals.mk locA_10_B.params
                    ((locA_10_B.locals.set 6 (.i32 right_j)).set 7 (.i32 (UInt32.ofNat k))) vs).get 13
                  = some (.i32 (UInt32.ofNat k)) := by
                intro vs
                simp only [Locals.get, hlp_10B, hll_10B, List.length_set,
                           show ¬(13 < 6) from by omega, show (13:Nat) < 6+16 from by omega,
                           show (13:Nat) - 6 = 7 from by omega]
                exact List.getElem?_set_self (by simp [List.length_set, hll_10B])
              have hg5_1213_raw : ∀ vs,
                  (Locals.mk locA_10_B.params
                    ((locA_10_B.locals.set 6 (.i32 right_j)).set 7 (.i32 (UInt32.ofNat k))) vs).get 5
                  = some (.i32 n_out) := by
                intro vs
                have h5_raw : locA.params[5]? = some (.i32 n_out) := by
                  have h := h5
                  simp only [Locals.get, hlparams, show (5:Nat) < 6 from by omega] at h
                  exact h
                simp only [Locals.get, hlp_10B, show (5:Nat) < 6 from by omega]
                exact h5_raw
              simp only [exec, execOne.eq_def,
                         show ({locA_10_B with values := locA_7.values} : Locals) = locA_10_B from rfl,
                         hgv2_10B, hg2_10B, hgv10_10B, hg10_10B,
                         hshl_j,
                         if_neg (show ¬((4 * UInt32.ofNat j + right_ptr).toNat +
                                         UInt32.toNat (0:UInt32) + 4 > stA.mem.pages * 65536) from by
                                   rw [show 4 * UInt32.ofNat j + right_ptr =
                                               right_ptr + 4 * UInt32.ofNat j from UInt32.add_comm _ _,
                                       show UInt32.toNat (0:UInt32) = 0 from rfl]
                                   exact hbnd_right_j),
                         show stA.mem.read32 (4 * UInt32.ofNat j + right_ptr + (0:UInt32)) = right_j from by
                             rw [show 4 * UInt32.ofNat j + right_ptr + (0:UInt32) =
                                         right_ptr + 4 * UInt32.ofNat j from by
                                     rw [UInt32.add_comm (4 * UInt32.ofNat j) right_ptr, UInt32.add_zero]],
                         Locals.set?,
                         hlp_10B, hll_10B, List.length_set,
                         if_neg (show ¬(12 < 6) from by omega),
                         if_pos (show (12:Nat) < 6+16 from by omega),
                         show (12:Nat) - 6 = 6 from by omega,
                         hg6_12B_raw,
                         if_neg (show ¬(frame.toNat + UInt32.toNat (16:UInt32) + 4 > stA.mem.pages * 65536) from by
                                   simp only [show (16:UInt32).toNat = 16 from by decide]; omega),
                         show stA.mem.read32 (frame + (16:UInt32)) = UInt32.ofNat k from hk_m,
                         if_neg (show ¬(13 < 6) from by omega),
                         if_pos (show (13:Nat) < 6+16 from by omega),
                         show (13:Nat) - 6 = 7 from by omega,
                         hg13_1213_raw, hg5_1213_raw,
                         if_pos hk_lt_u32,
                         show (1:UInt32) &&& 1 = 1 from by decide,
                         show Locals.mk locA_10_B.params
                               ((locA_10_B.locals.set 6 (.i32 right_j)).set 7 (.i32 (UInt32.ofNat k)))
                               locA.values = locA_1213_B from rfl]
              rfl
            -- body7: Break(0+1) from body8 → Break 0
            have h_B7_B : exec 8 m stA locA_7 body7 env = .Break 0 stA locA_1213_B := by
              rw [show (8:Nat) = 7+1 from rfl, exec_block_cons, h_B8_B]
            -- body6: Break 0 → B6_right_store: write out[k]=right_j, frame+12=j+1, br 5 → Break 5
            have h_B6_B : exec 9 m stA locA_7 body6 env = .Break 5 stA_m2_B locA_1213_B := by
              rw [show (9:Nat) = 8+1 from rfl, exec_block_cons, h_B7_B]
              simp only [List.take_zero, List.drop_zero, List.nil_append]
              have hgv4_1213  : ∀ vs, ({locA_1213_B with values := vs} : Locals).get 4  = locA_1213_B.get 4  := fun _ => rfl
              have hgv13_1213 : ∀ vs, ({locA_1213_B with values := vs} : Locals).get 13 = locA_1213_B.get 13 := fun _ => rfl
              have hgv12_1213 : ∀ vs, ({locA_1213_B with values := vs} : Locals).get 12 = locA_1213_B.get 12 := fun _ => rfl
              have hgv6_1213  : ∀ vs, ({locA_1213_B with values := vs} : Locals).get 6  = locA_1213_B.get 6  := fun _ => rfl
              have hg4_1213 : locA_1213_B.get 4 = some (.i32 out_ptr) := by
                simp only [Locals.get, locA_1213_B, hlparams, show (4:Nat) < 6 from by omega] at h4 ⊢
                exact h4
              have hg13_1213 : locA_1213_B.get 13 = some (.i32 (UInt32.ofNat k)) := by
                simp only [Locals.get, locA_1213_B, locA_1213_B_locs, locA_89_locs,
                           hlparams, hllocals, List.length_set,
                           show ¬(13 < 6) from by omega, show (13:Nat) < 6+16 from by omega,
                           show (13:Nat) - 6 = 7 from by omega]
                exact List.getElem?_set_self
                  (by rw [List.length_set, List.length_set, List.length_set,
                           List.length_set, List.length_set, hllocals]; norm_num)
              have hg12_1213 : locA_1213_B.get 12 = some (.i32 right_j) := by
                simp only [Locals.get, locA_1213_B, locA_1213_B_locs, locA_89_locs,
                           hlparams, hllocals, List.length_set,
                           show ¬(12 < 6) from by omega, show (12:Nat) < 6+16 from by omega,
                           show (12:Nat) - 6 = 6 from by omega]
                rw [List.getElem?_set_ne (show (7:Nat) ≠ 6 from by omega)]
                exact List.getElem?_set_self
                  (by rw [List.length_set, List.length_set, List.length_set, List.length_set, hllocals]; norm_num)
              have hg6_1213 : locA_1213_B.get 6 = some (.i32 frame) := by
                simp only [Locals.get, locA_1213_B, locA_1213_B_locs, locA_89_locs,
                           hlparams, hllocals, List.length_set,
                           show ¬(6 < 6) from by omega, show (6:Nat) < 6+16 from by omega,
                           show (6:Nat) - 6 = 0 from by omega,
                           List.getElem?_set, show (7:Nat) ≠ 0 from by omega,
                           show (6:Nat) ≠ 0 from by omega, show (4:Nat) ≠ 0 from by omega,
                           show (3:Nat) ≠ 0 from by omega, show (2:Nat) ≠ 0 from by omega,
                           show (1:Nat) ≠ 0 from by omega, if_false]
                simpa [Locals.get, hlparams, hllocals, show ¬(6 < 6) from by omega] using hf6
              have hshl_k : UInt32.ofNat k <<< ((2:UInt32) % 32) = 4 * UInt32.ofNat k := by
                rw [show (2:UInt32) % 32 = 2 from by decide]
                apply UInt32.toNat_inj.mp
                have hk_bnd : k < 2^30 := by have := n_out.toNat_lt; omega
                simp only [UInt32.toNat_mul, UInt32.toNat_ofNat',
                           show (4:UInt32).toNat = 4 from rfl,
                           Nat.mod_eq_of_lt (show k < 4294967296 from by omega),
                           Nat.mod_eq_of_lt (show k * 4 < 4294967296 from by omega)]
                simp [UInt32.shiftLeft, Fin.shiftLeft, Nat.shiftLeft_eq]; omega
              simp only [exec, execOne.eq_def,
                         show ({locA_1213_B with values := locA_7.values} : Locals) = locA_1213_B from rfl,
                         hgv4_1213, hg4_1213, hgv13_1213, hg13_1213,
                         hshl_k,
                         if_neg (show ¬((4 * UInt32.ofNat k + out_ptr).toNat +
                                         UInt32.toNat (0:UInt32) + 4 > stA.mem.pages * 65536) from by
                                   rw [show 4 * UInt32.ofNat k + out_ptr =
                                               out_ptr + 4 * UInt32.ofNat k from UInt32.add_comm _ _,
                                       show UInt32.toNat (0:UInt32) = 0 from rfl]; omega),
                         show stA.mem.write32 (4 * UInt32.ofNat k + out_ptr + (0:UInt32)) right_j = mem1_B from by
                             rw [show 4 * UInt32.ofNat k + out_ptr + (0:UInt32) =
                                         out_ptr + 4 * UInt32.ofNat k from by
                                     rw [UInt32.add_comm (4 * UInt32.ofNat k) out_ptr, UInt32.add_zero]],
                         hgv12_1213, hg12_1213,
                         hgv6_1213, hg6_1213,
                         if_neg (show ¬(frame.toNat + UInt32.toNat (12:UInt32) + 4 >
                                         {stA with mem := mem1_B}.mem.pages * 65536) from by
                                   rw [show ({stA with mem := mem1_B} : Store Unit).mem.pages =
                                         stA.mem.pages from rfl,
                                       show UInt32.toNat (12:UInt32) = 12 from by decide, hft12.symm]
                                   exact hbnd_fr12),
                         show ({stA with mem := mem1_B} : Store Unit).mem.read32 (frame + (12:UInt32)) =
                               UInt32.ofNat j from hmem1_B_fr12,
                         show (1:UInt32) + UInt32.ofNat j = UInt32.ofNat j + 1 from UInt32.add_comm _ _,
                         if_neg (show ¬(frame.toNat + UInt32.toNat (12:UInt32) + 4 >
                                         {stA with mem := mem1_B}.mem.pages * 65536) from by
                                   rw [show ({stA with mem := mem1_B} : Store Unit).mem.pages =
                                         stA.mem.pages from rfl,
                                       show UInt32.toNat (12:UInt32) = 12 from by decide, hft12.symm]
                                   exact hbnd_fr12),
                         show ({stA with mem := mem1_B} : Store Unit).mem.write32
                               (frame + (12:UInt32)) (UInt32.ofNat j + 1) = mem2_B from rfl,
                         show ({stA with mem := mem2_B} : Store Unit) = stA_m2_B from rfl,
                         show ({locA_1213_B with values := locA_1213_B.values} : Locals) = locA_1213_B from rfl]
            -- body5: Break(4+1) → Break 4
            have h_B5_B : exec 10 m stA locA_7 body5 env = .Break 4 stA_m2_B locA_1213_B := by
              rw [show (10:Nat) = 9+1 from rfl, exec_block_cons, h_B6_B]
            -- body4: Break(3+1) → Break 3
            have h_B4_B : exec 11 m stA locA_7 body4 env = .Break 3 stA_m2_B locA_1213_B := by
              rw [show (11:Nat) = 10+1 from rfl, exec_block_cons, h_B5_B]
            -- body3: Break(2+1) → Break 2
            have h_B3_B : exec 12 m stA locA_7 body3 env = .Break 2 stA_m2_B locA_1213_B := by
              rw [show (12:Nat) = 11+1 from rfl, exec_block_cons, h_B4_B]
            -- body2: Break(1+1) → Break 1
            have h_B2_B : exec 13 m stA locA_7 body2 env = .Break 1 stA_m2_B locA_1213_B := by
              rw [show (13:Nat) = 12+1 from rfl, exec_block_cons, h_B3_B]
            -- body1: Break(0+1) → Break 0
            have h_B1_B : exec 14 m stA locA_7 body1 env = .Break 0 stA_m2_B locA_1213_B := by
              rw [show (14:Nat) = 13+1 from rfl, exec_block_cons, h_B2_B]
            -- ── assemble: prefix → outer block (h_B1_B) → suffix ──
            have h_pre_B : exec 15 m stA locA mainMergeBody env =
                exec 15 m stA locA_7
                  (.block 0 0 body1 :: [.localGet 6, .localGet 6, .load32 (16:UInt32),
                    .const (1:UInt32), .add, .store32 (16:UInt32), .br 0]) env := by
              have h_prefix_aux : ∀ cont : Program,
                  exec 15 m stA locA
                    ([.localGet 6, .load32 (8:UInt32), .localGet 1, .ltU,
                      .const (1:UInt32), .and, .eqz, .br_if 1,
                      .localGet 6, .load32 (12:UInt32), .localGet 3, .ltU,
                      .const (1:UInt32), .and, .eqz, .br_if 1,
                      .localGet 6, .load32 (8:UInt32), .localSet 7] ++ cont) env
                    = exec 15 m stA locA_7 cont env := by
                intro cont
                have hgv6_pre : ∀ vs, ({locA with values := vs} : Locals).get 6 = locA.get 6 := fun _ => rfl
                have hgv1_pre : ∀ vs, ({locA with values := vs} : Locals).get 1 = locA.get 1 := fun _ => rfl
                have hgv3_pre : ∀ vs, ({locA with values := vs} : Locals).get 3 = locA.get 3 := fun _ => rfl
                rw [show [.localGet 6, .load32 (8:UInt32), .localGet 1, .ltU,
                          .const (1:UInt32), .and, .eqz, .br_if 1,
                          .localGet 6, .load32 (12:UInt32), .localGet 3, .ltU,
                          .const (1:UInt32), .and, .eqz, .br_if 1,
                          .localGet 6, .load32 (8:UInt32), .localSet 7] ++ cont =
                         .localGet 6 :: .load32 (8:UInt32) :: .localGet 1 :: .ltU ::
                         .const (1:UInt32) :: .and :: .eqz :: .br_if 1 ::
                         .localGet 6 :: .load32 (12:UInt32) :: .localGet 3 :: .ltU ::
                         .const (1:UInt32) :: .and :: .eqz :: .br_if 1 ::
                         .localGet 6 :: .load32 (8:UInt32) :: .localSet 7 :: cont from rfl]
                simp only
                  [exec, execOne.eq_def, Locals.set?,
                   hgv6_pre, hgv1_pre, hgv3_pre,
                   hf6, h1, h3,
                   hi_m, hj_m,
                   if_neg (show ¬(frame.toNat + UInt32.toNat (8 : UInt32) + 4 > stA.mem.pages * 65536) from by
                     rw [show UInt32.toNat (8 : UInt32) = 8 from by decide, ← hft8]; exact hbnd_fr8),
                   if_pos hi_lt_u32,
                   show (1 : UInt32) &&& 1 = 1 from by decide,
                   show (if (1 : UInt32) = 0 then (1 : UInt32) else 0) = 0 from by decide,
                   if_neg (show ¬(frame.toNat + UInt32.toNat (12 : UInt32) + 4 > stA.mem.pages * 65536) from by
                     rw [show UInt32.toNat (12 : UInt32) = 12 from by decide, ← hft12]; exact hbnd_fr12),
                   if_pos hj_lt_u32,
                   hlparams, hllocals,
                   if_neg (show ¬(7 < 6) from by omega),
                   if_pos (show (7 : Nat) < 6 + 16 from by omega),
                   show (7 : Nat) - 6 = 1 from by omega]
                rfl
              exact h_prefix_aux _
            rw [h_pre_B, show (15:Nat) = 14+1 from rfl, exec_block_cons, h_B1_B]
            simp only [List.take_zero, List.drop_zero, List.nil_append]
            -- suffix: localGet 6 ×2, load32 16 (=k), const 1, add (=k+1), store32 16 (→mem3_B), br 0
            have hgv6_suf_B : ∀ vs, ({locA_1213_B with values := vs} : Locals).get 6 = locA_1213_B.get 6 := fun _ => rfl
            have hg6_suf_B : locA_1213_B.get 6 = some (.i32 frame) := by
              simp only [Locals.get, locA_1213_B, locA_1213_B_locs, locA_89_locs,
                         hlparams, hllocals, List.length_set,
                         show ¬(6 < 6) from by omega, show (6:Nat) < 6+16 from by omega,
                         show (6:Nat) - 6 = 0 from by omega,
                         List.getElem?_set, show (7:Nat) ≠ 0 from by omega,
                         show (6:Nat) ≠ 0 from by omega, show (4:Nat) ≠ 0 from by omega,
                         show (3:Nat) ≠ 0 from by omega, show (2:Nat) ≠ 0 from by omega,
                         show (1:Nat) ≠ 0 from by omega, if_false]
              simpa [Locals.get, hlparams, hllocals, show ¬(6 < 6) from by omega] using hf6
            simp only [exec, execOne.eq_def,
                       hgv6_suf_B, hg6_suf_B,
                       if_neg (show ¬(frame.toNat + UInt32.toNat (16 : UInt32) + 4 > stA_m2_B.mem.pages * 65536) from by
                         rw [show stA_m2_B.mem.pages = stA.mem.pages from rfl,
                             show UInt32.toNat (16 : UInt32) = 16 from by decide, ← hft16]
                         exact hbnd_fr16),
                       show stA_m2_B.mem.read32 (frame + (16 : UInt32)) = UInt32.ofNat k from hmem2_B_fr16,
                       show (1 : UInt32) + UInt32.ofNat k = UInt32.ofNat (k + 1) from by
                         rw [UInt32.add_comm]; exact hk_add1,
                       show stA_m2_B.mem.write32 (frame + (16 : UInt32)) (UInt32.ofNat (k + 1)) = mem3_B from by
                         simp only [stA_m2_B, mem3_B]; rw [← hk_add1]]
            rfl
          obtain ⟨f_B, h_body_B⟩ := h_body_B
          -- memory reads after path B writes
          have hread8_B : stC_B.mem.read32 (frame + 8) = UInt32.ofNat i := by
            simp only [stC_B, mem3_B, mem2_B, mem1_B]
            rw [Mem.read32_write32_of_disjoint _ (frame + 16) (frame + 8) _
                  (by right; rw [hft16, hft8]; omega),
                Mem.read32_write32_of_disjoint _ (frame + 12) (frame + 8) _
                  (by right; rw [hft12, hft8]),
                Mem.read32_write32_of_disjoint _ (out_ptr + 4 * UInt32.ofNat k) (frame + 8) _
                  (by rw [hout_k_toNat, hft8];
                      rcases hframe_out_disj with h | h <;> omega),
                hi_m]
          have hread12_B : stC_B.mem.read32 (frame + 12) = UInt32.ofNat (j + 1) := by
            simp only [stC_B, mem3_B, mem2_B, mem1_B]
            rw [Mem.read32_write32_of_disjoint _ (frame + 16) (frame + 12) _
                  (by right; rw [hft16, hft12]),
                Mem.read32_write32_same, hj_add1]
          have hread16_B : stC_B.mem.read32 (frame + 16) = UInt32.ofNat (k + 1) := by
            simp only [stC_B, mem3_B]
            rw [Mem.read32_write32_same, hk_add1]
          -- locB_out_B.get 6: local[0] unchanged (set indices 1,2,3,4,6,7 ≠ 0)
          have hf6_out_B : locB_out_B.get 6 = some (.i32 frame) := by
            simp only [locB_out_B, locB_out_locs, Locals.get, hlparams, hllocals, List.length_set,
                       show ¬ (6 < 6) from by omega,
                       show 6 < 6 + 16 from by omega,
                       show 6 - 6 = 0 from by omega,
                       List.getElem?_set,
                       show (7 : Nat) ≠ 0 from by omega,
                       show (6 : Nat) ≠ 0 from by omega,
                       show (4 : Nat) ≠ 0 from by omega,
                       show (3 : Nat) ≠ 0 from by omega,
                       show (2 : Nat) ≠ 0 from by omega,
                       show (1 : Nat) ≠ 0 from by omega,
                       if_false]
            simpa [Locals.get, hlparams, hllocals,
                   show ¬ (6 < 6) from by omega] using hf6
          have hllocals_out_B : locB_out_B.locals.length = 16 := by
            simp [locB_out_B, locB_out_locs, List.length_set, hllocals]
          -- locB_out_B.get 0..5 = locA.get 0..5: params unchanged, needs hlparams for if-branch
          have hg_eq_B : ∀ n, n < 6 → locB_out_B.get n = locA.get n := fun n hn => by
            simp only [locB_out_B, Locals.get, hlparams, if_pos hn]
          have hlparams_out_B : locB_out_B.params.length = 6 := by exact hlparams
          -- invariant restoration: (i, j+1)
          have hI_B : MergeLoopInv frame out_ptr left_ptr right_ptr n_left n_right n_out
                        i₀ j₀ k₀ st stC_B locB_out_B :=
            ⟨i, j + 1, hi_lo, hi_hi, by omega, by omega,
             hread8_B, hread12_B,
             by rw [hread16_B]; congr 1; omega,
             hf6_out_B,
             (hg_eq_B 0 (by omega)).trans h0, (hg_eq_B 1 (by omega)).trans h1,
             (hg_eq_B 2 (by omega)).trans h2, (hg_eq_B 3 (by omega)).trans h3,
             (hg_eq_B 4 (by omega)).trans h4, (hg_eq_B 5 (by omega)).trans h5,
             hlparams_out_B, hllocals_out_B, ⟨v₀, hg⟩,
             fun q hq => by
               simp only [stC_B, mem3_B, mem2_B, mem1_B]
               have hliq : (left_ptr + 4 * UInt32.ofNat q).toNat = left_ptr.toNat + 4 * q :=
                 toNat_wordAddr left_ptr n_left.toNat q hq (by linarith)
               rw [Mem.read32_write32_of_disjoint _ (frame + 16) _ _
                     (by rw [hft16, hliq]; rcases hframe_left_disj with h | h <;> omega),
                   Mem.read32_write32_of_disjoint _ (frame + 12) _ _
                     (by rw [hft12, hliq]; rcases hframe_left_disj with h | h <;> omega),
                   Mem.read32_write32_of_disjoint _ (out_ptr + 4 * UInt32.ofNat k) _ _
                     (by rw [hout_k_toNat, hliq]; rcases hleft_out_disj with h | h <;> omega)]
               exact hleft q hq,
             fun q hq => by
               simp only [stC_B, mem3_B, mem2_B, mem1_B]
               have hriq : (right_ptr + 4 * UInt32.ofNat q).toNat = right_ptr.toNat + 4 * q :=
                 toNat_wordAddr right_ptr n_right.toNat q hq (by linarith)
               rw [Mem.read32_write32_of_disjoint _ (frame + 16) _ _
                     (by rw [hft16, hriq]; rcases hframe_right_disj with h | h <;> omega),
                   Mem.read32_write32_of_disjoint _ (frame + 12) _ _
                     (by rw [hft12, hriq]; rcases hframe_right_disj with h | h <;> omega),
                   Mem.read32_write32_of_disjoint _ (out_ptr + 4 * UInt32.ofNat k) _ _
                     (by rw [hout_k_toNat, hriq]; rcases hright_out_disj with h | h <;> omega)]
               exact hright q hq,
             (by
               -- content invariant: wordsAt stC_B (out+4k₀) (W+1) ++ merge(L.drop i, R.drop(j+1))
               --                  = merge(L.drop i₀, R.drop j₀)  (path B: ¬(left_i ≤ right_j))
               have hW : (i - i₀) + (j + 1 - j₀) = (i - i₀) + (j - j₀) + 1 := by omega
               rw [hW]
               have h_k₀_addr : (out_ptr + 4 * UInt32.ofNat k₀).toNat = out_ptr.toNat + 4 * k₀ :=
                 toNat_wordAddr out_ptr n_out.toNat k₀ (by have := hk_val; omega) (by linarith)
               have hout_bnd : (out_ptr + 4 * UInt32.ofNat k₀).toNat + 4 * ((i - i₀) + (j - j₀) + 1) ≤ 4294967296 := by
                 rw [h_k₀_addr]; have := hk_val; omega
               have hwords : wordsAt stC_B.mem (out_ptr + 4 * UInt32.ofNat k₀) ((i - i₀) + (j - j₀) + 1) =
                   wordsAt stA.mem (out_ptr + 4 * UInt32.ofNat k₀) ((i - i₀) + (j - j₀)) ++ [right_j] := by
                 simp only [stC_B, mem3_B, mem2_B, mem1_B]
                 rw [wordsAt_write32_of_disjoint _ _ (frame + 16) _ _ hout_bnd
                       (by rw [hft16, h_k₀_addr]; rcases hframe_out_disj with h | h <;> [left; right] <;> omega),
                     wordsAt_write32_of_disjoint _ _ (frame + 12) _ _ hout_bnd
                       (by rw [hft12, h_k₀_addr]; rcases hframe_out_disj with h | h <;> [left; right] <;> omega),
                     wordsAt_split _ _ _ ((i - i₀) + (j - j₀)) (by omega)]
                 simp only [show (i - i₀) + (j - j₀) + 1 - ((i - i₀) + (j - j₀)) = 1 from by omega]
                 congr 1
                 · rw [wordsAt_write32_of_disjoint _ _ (out_ptr + 4 * UInt32.ofNat k) _ _
                         (by omega)
                         (by right; rw [h_k₀_addr, hout_k_toNat]; omega)]
                 · have hbase_W : out_ptr + 4 * UInt32.ofNat k₀ + 4 * UInt32.ofNat ((i - i₀) + (j - j₀)) =
                       out_ptr + 4 * UInt32.ofNat k := by
                     have hkeq : k₀ + ((i - i₀) + (j - j₀)) = k := by omega
                     rw [UInt32.add_assoc, ← UInt32.mul_add, ← UInt32.ofNat_add, hkeq]
                   rw [hbase_W]; simp [wordsAt, Mem.read32_write32_same]
               rw [hwords, List.append_assoc, List.singleton_append]
               conv_rhs => rw [← hcontent]
               congr 1
               -- right_j :: merge(L.drop i, R.drop(j+1)) = merge(L.drop i, R.drop j)
               have hL_drop_i : (wordsAt st.mem left_ptr n_left.toNat).drop i =
                   st.mem.read32 (left_ptr + 4 * UInt32.ofNat i) ::
                   (wordsAt st.mem left_ptr n_left.toNat).drop (i + 1) := by
                 have h1 : i < (wordsAt st.mem left_ptr n_left.toNat).length := by
                   simp [wordsAt_length]; exact hlt_i
                 rw [List.drop_eq_getElem_cons h1, wordsAt_getElem _ _ _ _ hlt_i]
               have hR_drop_j : (wordsAt st.mem right_ptr n_right.toNat).drop j =
                   st.mem.read32 (right_ptr + 4 * UInt32.ofNat j) ::
                   (wordsAt st.mem right_ptr n_right.toNat).drop (j + 1) := by
                 have h2 : j < (wordsAt st.mem right_ptr n_right.toNat).length := by
                   simp [wordsAt_length]; exact hlt_j
                 rw [List.drop_eq_getElem_cons h2, wordsAt_getElem _ _ _ _ hlt_j]
               have hright_j_eq : right_j = st.mem.read32 (right_ptr + 4 * UInt32.ofNat j) :=
                 hright j hlt_j
               have hnle_st : ¬(st.mem.read32 (left_ptr + 4 * UInt32.ofNat i) ≤
                   st.mem.read32 (right_ptr + 4 * UInt32.ofNat j)) := by
                 rw [← hleft i hlt_i, ← hright j hlt_j]; exact hle
               rw [hright_j_eq, hL_drop_i, hR_drop_j, merge_cons_gt hnle_st]),
             by simp [stC_B, mem3_B, mem2_B, mem1_B, Mem.write32_pages, hpages],
             hk_global,
             by simp [stC_B, mem3_B, mem2_B, mem1_B, Mem.write32_pages, hleft_global],
             by simp [stC_B, mem3_B, mem2_B, mem1_B, Mem.write32_pages, hright_global],
             by simp [stC_B, mem3_B, mem2_B, mem1_B, Mem.write32_pages, hout_global],
             hpages_u32, hleft_out_disj, hright_out_disj, hleft_right_disj,
             hframe_left_disj, hframe_right_disj, hframe_out_disj⟩
          -- measure decrease
          have hμ_B : (n_left.toNat - (stC_B.mem.read32 (frame + 8)).toNat) +
                      (n_right.toNat - (stC_B.mem.read32 (frame + 12)).toNat) < n := by
            rw [hread8_B, hread12_B, UInt32.toNat_ofNat', UInt32.toNat_ofNat',
                Nat.mod_eq_of_lt (by have := n_left.toNat_lt; omega),
                Nat.mod_eq_of_lt (by have := n_right.toNat_lt; omega),
                ← hμ, hi_m, hj_m, UInt32.toNat_ofNat', UInt32.toNat_ofNat',
                Nat.mod_eq_of_lt (by have := n_left.toNat_lt; omega),
                Nat.mod_eq_of_lt (by have := n_right.toNat_lt; omega)]
            omega
          -- IH at reduced measure: input is (stC_B, locB_out_B)
          obtain ⟨f_rest, hf_rest⟩ := IH _ hμ_B stC_B locB_out_B hI_B rfl
          -- Fuel composition: one body iteration at stA then IH fuel at stC_B
          have hbody_ne : exec f_B m stA locA mainMergeBody env ≠ .OutOfFuel := by
            simp [h_body_B]
          have hfuel_ne : exec f_rest m stC_B locB_out_B [.block 0 0 [.loop 0 0 mainMergeBody]] env ≠ .OutOfFuel :=
            fun h => by rw [h] at hf_rest; exact hf_rest
          have hbody_mono : exec (max f_B f_rest) m stA locA mainMergeBody env = .Break 0 stC_B locB_out_B :=
            (exec_fuel_mono (Nat.le_max_left f_B f_rest) hbody_ne).trans h_body_B
          have hblock_mono : exec (max f_B f_rest + 1) m stC_B locB_out_B [.block 0 0 [.loop 0 0 mainMergeBody]] env =
              exec f_rest m stC_B locB_out_B [.block 0 0 [.loop 0 0 mainMergeBody]] env :=
            exec_fuel_mono (by omega) hfuel_ne
          have hloop_single : ∀ F stT locT,
              exec F m stT locT [.loop 0 0 mainMergeBody] env =
              execOne F m stT locT (.loop 0 0 mainMergeBody) env := fun F stT locT => by
            cases F with
            | zero => simp [exec, execOne]
            | succ f =>
              simp only [exec]
              rcases execOne (f + 1) m stT locT (.loop 0 0 mainMergeBody) env with
                ⟨_, _⟩ | ⟨_, _, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_⟩ | _
              · rfl
              all_goals rfl
          have hloop_eq : exec (max f_B f_rest + 1) m stA locA [.loop 0 0 mainMergeBody] env =
              exec (max f_B f_rest) m stC_B locB_out_B [.loop 0 0 mainMergeBody] env := by
            rw [hloop_single, hloop_single]
            conv_lhs => rw [execOne_loop_succ]
            simp only [hbody_mono, List.take_zero, List.nil_append, List.drop_zero]
            rfl
          have heq : exec (max f_B f_rest + 2) m stA locA [.block 0 0 [.loop 0 0 mainMergeBody]] env =
              exec (max f_B f_rest + 1) m stC_B locB_out_B [.block 0 0 [.loop 0 0 mainMergeBody]] env := by
            rw [show max f_B f_rest + 2 = max f_B f_rest + 1 + 1 from rfl]
            conv_lhs => rw [exec_block_cons, hloop_eq]
            conv_rhs => rw [exec_block_cons]
            set discr := exec (max f_B f_rest) m stC_B locB_out_B [.loop 0 0 mainMergeBody] env
            rcases discr with ⟨r', s'⟩ | ⟨n, r', s'⟩ | ⟨r', vs⟩ | ⟨r', msg⟩ | ⟨msg⟩ | _
            · simp [exec, locB_out_B, locB_out_locs]
            · cases n with | zero => simp [exec, locB_out_B, locB_out_locs] | succ k => rfl
            all_goals rfl
          exact ⟨max f_B f_rest + 2, by rw [heq, hblock_mono]; exact hf_rest⟩
      · -- exit: j = n_right
        -- body's second br_if 1 fires: exec 1 body = Break 1 → exec 2 loop = Break 0
        -- → exec 3 block = Fallthrough.  Q: stA.mem.read32(frame+12) = n_right.
        have hj_eq : j = n_right.toNat := Nat.le_antisymm hj_hi (Nat.not_lt.mp hlt_j)
        have hi_lt32  : UInt32.ofNat i < n_left := by
          rw [UInt32.lt_iff_toNat_lt_toNat, UInt32.toNat_ofNat']
          have := n_left.toNat_lt; omega
        have hj_nlt32 : ¬(UInt32.ofNat j < n_right) := by
          rw [UInt32.lt_iff_toNat_lt_toNat, UInt32.toNat_ofNat']
          have := n_right.toNat_lt; omega
        have hb8  : ¬(frame.toNat + (8 : UInt32).toNat + 4 > stA.mem.pages * 65536) :=
          by simp; omega
        have hb12 : ¬(frame.toNat + (12 : UInt32).toNat + 4 > stA.mem.pages * 65536) :=
          by simp; omega
        have hgv6j : ∀ xs, ({ locA with values := xs } : Locals).get 6 = locA.get 6 := fun _ => rfl
        have hgv1j : ∀ xs, ({ locA with values := xs } : Locals).get 1 = locA.get 1 := fun _ => rfl
        have hgv3j : ∀ xs, ({ locA with values := xs } : Locals).get 3 = locA.get 3 := fun _ => rfl
        -- exec 1 body = Break 1 (second br_if 1 fires since j = n_right)
        have h_body_exit_j : exec 1 m stA locA mainMergeBody env = .Break 1 stA locA := by
          simp only [mainMergeBody, exec, execOne.eq_def,
                     hgv6j, hgv1j, hgv3j, hf6, h1, h3,
                     hi_m, hj_m,
                     if_neg hb8, if_neg hb12,
                     if_pos hi_lt32,
                     show (1 : UInt32) &&& 1 = 1 from by decide,
                     show (if (1 : UInt32) = 0 then (1 : UInt32) else 0) = 0 from by decide,
                     if_neg hj_nlt32,
                     show (1 : UInt32) &&& 0 = 0 from by decide]
          rfl
        -- exec 2 [.loop ...] = Break 0  (Break 1 from body → loop converts to Break 0)
        have h_loop_exit_j : exec 2 m stA locA [.loop 0 0 mainMergeBody] env = .Break 0 stA locA := by
          simp only [show (2 : Nat) = 1 + 1 from rfl, exec, execOne_loop_succ]
          rw [h_body_exit_j]
        -- exec 3 [.block ...] = Fallthrough  (Break 0 from loop → block gives Fallthrough)
        have h_block_exit_j : exec 3 m stA locA [.block 0 0 [.loop 0 0 mainMergeBody]] env =
            .Fallthrough stA locA := by
          rw [show (3 : Nat) = 2 + 1 from rfl, exec_block_cons, h_loop_exit_j]
          simp only [List.take_zero, List.nil_append, List.drop_zero, exec]
        have hQ_j : stA.mem.read32 (frame + 12) = n_right := by
          rw [hj_m, hj_eq]
          apply UInt32.toNat_inj.mp
          simp
        exact ⟨3, by simp only [h_block_exit_j]; exact Or.inr hQ_j⟩
    · -- exit: i = n_left
      -- body's first br_if 1 fires immediately: exec 1 body = Break 1 → exec 2 loop = Break 0
      -- → exec 3 block = Fallthrough.  Q: stA.mem.read32(frame+8) = n_left.
      have hi_eq : i = n_left.toNat := Nat.le_antisymm hi_hi (Nat.not_lt.mp hlt_i)
      have hi_nlt32 : ¬(UInt32.ofNat i < n_left) := by
        rw [UInt32.lt_iff_toNat_lt_toNat, UInt32.toNat_ofNat']
        have := n_left.toNat_lt; omega
      have hb8i : ¬(frame.toNat + (8 : UInt32).toNat + 4 > stA.mem.pages * 65536) :=
        by simp; omega
      have hgv6i : ∀ xs, ({ locA with values := xs } : Locals).get 6 = locA.get 6 := fun _ => rfl
      have hgv1i : ∀ xs, ({ locA with values := xs } : Locals).get 1 = locA.get 1 := fun _ => rfl
      -- exec 1 body = Break 1 (first br_if 1 fires since i = n_left)
      have h_body_exit_i : exec 1 m stA locA mainMergeBody env = .Break 1 stA locA := by
        simp only [mainMergeBody, exec, execOne.eq_def,
                   hgv1i, hf6, h1, hi_m,
                   if_neg hb8i,
                   if_neg hi_nlt32,
                   show (1 : UInt32) &&& 0 = 0 from by decide]
        rfl
      -- exec 2 [.loop ...] = Break 0
      have h_loop_exit_i : exec 2 m stA locA [.loop 0 0 mainMergeBody] env = .Break 0 stA locA := by
        simp only [show (2 : Nat) = 1 + 1 from rfl, exec, execOne_loop_succ]
        rw [h_body_exit_i]
      -- exec 3 [.block 0 0 [.loop ...]] = Fallthrough
      have h_block_exit_i : exec 3 m stA locA [.block 0 0 [.loop 0 0 mainMergeBody]] env =
          .Fallthrough stA locA := by
        rw [show (3 : Nat) = 2 + 1 from rfl, exec_block_cons, h_loop_exit_i]
        simp only [List.take_zero, List.nil_append, List.drop_zero, exec]
      have hQ_i : stA.mem.read32 (frame + 8) = n_left := by
        rw [hi_m, hi_eq]
        apply UInt32.toNat_inj.mp
        simp
      exact ⟨3, by simp only [h_block_exit_i]; exact Or.inl hQ_i⟩


set_option maxHeartbeats 800000 in
theorem main_merge_loop_spec_with_inv
    {m : Module} {env : HostEnv Unit}
    (st : Store Unit) (locals : Locals)
    (frame out_ptr left_ptr right_ptr n_left n_right n_out : UInt32)
    (i₀ j₀ k₀ : Nat)
    (hI₀ : MergeLoopInv frame out_ptr left_ptr right_ptr n_left n_right n_out
             i₀ j₀ k₀ st st locals) :
    wp_wasm_prop m st locals [.block 0 0 [.loop 0 0 mainMergeBody]] env
      (fun st' _ =>
        (st'.mem.read32 (frame + 8)  = n_left ∨
         st'.mem.read32 (frame + 12) = n_right) ∧
        ∃ i j : Nat,
          i₀ ≤ i ∧ i ≤ n_left.toNat ∧ j₀ ≤ j ∧ j ≤ n_right.toNat ∧
          st'.mem.read32 (frame + 8)  = UInt32.ofNat i ∧
          st'.mem.read32 (frame + 12) = UInt32.ofNat j ∧
          st'.mem.read32 (frame + 16) = UInt32.ofNat (k₀ + (i - i₀) + (j - j₀)) ∧
          (∀ q, q < n_left.toNat →
            st'.mem.read32 (left_ptr + 4 * UInt32.ofNat q) =
            st.mem.read32  (left_ptr + 4 * UInt32.ofNat q)) ∧
          (∀ q, q < n_right.toNat →
            st'.mem.read32 (right_ptr + 4 * UInt32.ofNat q) =
            st.mem.read32  (right_ptr + 4 * UInt32.ofNat q)) ∧
          wordsAt st'.mem (out_ptr + 4 * UInt32.ofNat k₀) ((i - i₀) + (j - j₀)) ++
            List.merge
              ((wordsAt st.mem left_ptr n_left.toNat).drop i)
              ((wordsAt st.mem right_ptr n_right.toNat).drop j)
              (· ≤ ·) =
          List.merge
            ((wordsAt st.mem left_ptr n_left.toNat).drop i₀)
            ((wordsAt st.mem right_ptr n_right.toNat).drop j₀)
            (· ≤ ·)) := by
  -- strong induction on μ = (n_left - i) + (n_right - j)
  suffices key : ∀ n stA locA,
      MergeLoopInv frame out_ptr left_ptr right_ptr n_left n_right n_out
        i₀ j₀ k₀ st stA locA →
      (n_left.toNat - (stA.mem.read32 (frame + 8)).toNat) +
        (n_right.toNat - (stA.mem.read32 (frame + 12)).toNat) = n →
      wp_wasm_prop m stA locA [.block 0 0 [.loop 0 0 mainMergeBody]] env
        (fun st' _ =>
          (st'.mem.read32 (frame + 8)  = n_left ∨
           st'.mem.read32 (frame + 12) = n_right) ∧
          ∃ i j : Nat,
            i₀ ≤ i ∧ i ≤ n_left.toNat ∧ j₀ ≤ j ∧ j ≤ n_right.toNat ∧
            st'.mem.read32 (frame + 8)  = UInt32.ofNat i ∧
            st'.mem.read32 (frame + 12) = UInt32.ofNat j ∧
            st'.mem.read32 (frame + 16) = UInt32.ofNat (k₀ + (i - i₀) + (j - j₀)) ∧
            (∀ q, q < n_left.toNat →
              st'.mem.read32 (left_ptr + 4 * UInt32.ofNat q) =
              st.mem.read32  (left_ptr + 4 * UInt32.ofNat q)) ∧
            (∀ q, q < n_right.toNat →
              st'.mem.read32 (right_ptr + 4 * UInt32.ofNat q) =
              st.mem.read32  (right_ptr + 4 * UInt32.ofNat q)) ∧
            wordsAt st'.mem (out_ptr + 4 * UInt32.ofNat k₀) ((i - i₀) + (j - j₀)) ++
              List.merge
                ((wordsAt st.mem left_ptr n_left.toNat).drop i)
                ((wordsAt st.mem right_ptr n_right.toNat).drop j)
                (· ≤ ·) =
            List.merge
              ((wordsAt st.mem left_ptr n_left.toNat).drop i₀)
              ((wordsAt st.mem right_ptr n_right.toNat).drop j₀)
              (· ≤ ·)) from
    key _ st locals hI₀ rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro stA locA hI hμ
    obtain ⟨i, j, hi_lo, hi_hi, hj_lo, hj_hi,
             hi_m, hj_m, hk_m,
             hf6, h0, h1, h2, h3, h4, h5,
             hlparams, hllocals, hglobal,
             hleft, hright, hcontent,
             hpages, hk_global,
             hleft_global, hright_global, hout_global,
             hpages_u32,
             hleft_out_disj, hright_out_disj, hleft_right_disj,
             hframe_left_disj, hframe_right_disj, hframe_out_disj⟩ := hI
    by_cases hlt_i : i < n_left.toNat
    · by_cases hlt_j : j < n_right.toNat
      · -- iteration: i < n_left, j < n_right
        -- Case-split on comparison left[i] ≤ right[j].
        -- Each path: exec trace through 14 nested blocks sorry'd;
        -- invariant restoration and measure decrease proven; IH applied.
        obtain ⟨v₀, hg⟩ := hglobal
        have hμ_pos : 0 < n := by
          rw [← hμ, hi_m, hj_m, UInt32.toNat_ofNat', UInt32.toNat_ofNat']
          have := n_left.toNat_lt; have := n_right.toNat_lt; omega
        let k := k₀ + (i - i₀) + (j - j₀)
        have hk_val : k < n_out.toNat := by have := hk_global; omega
        have hft8  : (frame + 8).toNat  = frame.toNat + 8  := by
          rw [UInt32.toNat_add, show (8 : UInt32).toNat = 8 from rfl]
          exact Nat.mod_eq_of_lt (by omega)
        have hft12 : (frame + 12).toNat = frame.toNat + 12 := by
          rw [UInt32.toNat_add, show (12 : UInt32).toNat = 12 from rfl]
          exact Nat.mod_eq_of_lt (by omega)
        have hft16 : (frame + 16).toNat = frame.toNat + 16 := by
          rw [UInt32.toNat_add, show (16 : UInt32).toNat = 16 from rfl]
          exact Nat.mod_eq_of_lt (by omega)
        have hout_k_toNat : (out_ptr + 4 * UInt32.ofNat k).toNat = out_ptr.toNat + 4 * k :=
          toNat_wordAddr out_ptr n_out.toNat k hk_val (by linarith)
        let left_i  := stA.mem.read32 (left_ptr + 4 * UInt32.ofNat i)
        let right_j := stA.mem.read32 (right_ptr + 4 * UInt32.ofNat j)
        have hi_add1 : UInt32.ofNat i + 1 = UInt32.ofNat (i + 1) := by
          apply UInt32.toNat_inj.mp
          simp only [UInt32.toNat_add, UInt32.toNat_ofNat', show (1 : UInt32).toNat = 1 from rfl,
                     Nat.mod_eq_of_lt (show i + 1 < 4294967296 from by
                       have := n_left.toNat_lt; omega)]
          omega
        have hj_add1 : UInt32.ofNat j + 1 = UInt32.ofNat (j + 1) := by
          apply UInt32.toNat_inj.mp
          simp only [UInt32.toNat_add, UInt32.toNat_ofNat', show (1 : UInt32).toNat = 1 from rfl,
                     Nat.mod_eq_of_lt (show j + 1 < 4294967296 from by
                       have := n_right.toNat_lt; omega)]
          omega
        have hk_add1 : UInt32.ofNat k + 1 = UInt32.ofNat (k + 1) := by
          apply UInt32.toNat_inj.mp
          simp only [UInt32.toNat_add, UInt32.toNat_ofNat', show (1 : UInt32).toNat = 1 from rfl,
                     Nat.mod_eq_of_lt (show k + 1 < 4294967296 from by
                       have := n_out.toNat_lt; omega)]
          omega
        by_cases hle : left_i ≤ right_j
        · -- ── path A: left[i] ≤ right[j]: copy left[i] to out[k], i++, k++ ──
          let mem1_A := stA.mem.write32 (out_ptr + 4 * UInt32.ofNat k) left_i
          let mem2_A := mem1_A.write32 (frame + 8) (UInt32.ofNat i + 1)
          let mem3_A := mem2_A.write32 (frame + 16) (UInt32.ofNat k + 1)
          let stC_A : Store Unit := { stA with mem := mem3_A }
          -- Result locals: localSet 7(→local[1]) 8(→local[2]) 9(→local[3])
          --                       11(→local[5]) 14(→local[8]) 15(→local[9])
          let locA_out_locs :=
            locA.locals.set 1 (.i32 (UInt32.ofNat i)) |>.set 2 (.i32 left_i)
              |>.set 3 (.i32 (UInt32.ofNat j)) |>.set 5 (.i32 (UInt32.ofNat i))
              |>.set 8 (.i32 left_i) |>.set 9 (.i32 (UInt32.ofNat k))
          let locA_out_A : Locals := { locA with locals := locA_out_locs }
          -- exec trace (staged through 14 nested blocks)
          have h_body_A : ∃ f_A,
              exec f_A m stA locA mainMergeBody env = .Break 0 stC_A locA_out_A := by
            refine ⟨15, ?_⟩
            -- ── body let-bindings (definitionally transparent to mainMergeBody internals) ──
            let body14 : Program := [
              .localGet 7, .localGet 1, .ltU, .const (1:UInt32), .and, .eqz, .br_if 0,
              .localGet 0, .localGet 7, .const (2:UInt32), .shl, .add,
              .load32 (0:UInt32), .localSet 8,
              .localGet 6, .load32 (12:UInt32), .localSet 9,
              .localGet 9, .localGet 3, .ltU, .const (1:UInt32), .and, .br_if 1, .br 2]
            let body13 : Program := [.block 0 0 body14,
              .localGet 7, .localGet 1, .const (1048712:UInt32), .call 87, .unreachable]
            let body12 : Program := [.block 0 0 body13,
              .localGet 8, .localGet 2, .localGet 9, .const (2:UInt32), .shl, .add,
              .load32 (0:UInt32), .leU, .const (1:UInt32), .and, .br_if 2, .br 1]
            let body11 : Program := [.block 0 0 body12,
              .localGet 9, .localGet 3, .const (1048728:UInt32), .call 87, .unreachable]
            let body10 : Program := [.block 0 0 body11,
              .localGet 6, .load32 (12:UInt32), .localSet 10,
              .localGet 10, .localGet 3, .ltU, .const (1:UInt32), .and, .br_if 1, .br 2]
            let body9 : Program := [.block 0 0 body10,
              .localGet 6, .load32 (8:UInt32), .localSet 11,
              .localGet 11, .localGet 1, .ltU, .const (1:UInt32), .and, .br_if 4, .br 5]
            let body8 : Program := [.block 0 0 body9,
              .localGet 2, .localGet 10, .const (2:UInt32), .shl, .add,
              .load32 (0:UInt32), .localSet 12,
              .localGet 6, .load32 (16:UInt32), .localSet 13,
              .localGet 13, .localGet 5, .ltU, .const (1:UInt32), .and, .br_if 1, .br 2]
            let body7 : Program := [.block 0 0 body8,
              .localGet 10, .localGet 3, .const (1048744:UInt32), .call 87, .unreachable]
            let body6 : Program := [.block 0 0 body7,
              .localGet 4, .localGet 13, .const (2:UInt32), .shl, .add,
              .localGet 12, .store32 (0:UInt32),
              .localGet 6, .localGet 6, .load32 (12:UInt32),
              .const (1:UInt32), .add, .store32 (12:UInt32), .br 5]
            let body5 : Program := [.block 0 0 body6,
              .localGet 13, .localGet 5, .const (1048760:UInt32), .call 87, .unreachable]
            let body4 : Program := [.block 0 0 body5,
              .localGet 0, .localGet 11, .const (2:UInt32), .shl, .add,
              .load32 (0:UInt32), .localSet 14,
              .localGet 6, .load32 (16:UInt32), .localSet 15,
              .localGet 15, .localGet 5, .ltU, .const (1:UInt32), .and, .br_if 1, .br 2]
            let body3 : Program := [.block 0 0 body4,
              .localGet 11, .localGet 1, .const (1048776:UInt32), .call 87, .unreachable]
            let body2 : Program := [.block 0 0 body3,
              .localGet 4, .localGet 15, .const (2:UInt32), .shl, .add,
              .localGet 14, .store32 (0:UInt32),
              .localGet 6, .localGet 6, .load32 (8:UInt32),
              .const (1:UInt32), .add, .store32 (8:UInt32), .br 1]
            let body1 : Program := [.block 0 0 body2,
              .localGet 15, .localGet 5, .const (1048792:UInt32), .call 87, .unreachable]
            -- ── intermediate Locals states ──
            -- after prefix localSet 7: local[1] = UInt32.ofNat i
            let locA_7 : Locals :=
              { locA with locals := locA.locals.set 1 (.i32 (UInt32.ofNat i)) }
            -- after body14 localSet 8,9: local[2]=left_i, local[3]=UInt32.ofNat j
            let locA_89_locs :=
              locA.locals.set 1 (.i32 (UInt32.ofNat i)) |>.set 2 (.i32 left_i)
                |>.set 3 (.i32 (UInt32.ofNat j))
            let locA_89 : Locals := { locA with locals := locA_89_locs }
            -- after B9_left_cont localSet 11: local[5]=UInt32.ofNat i
            let locA_11_locs :=
              locA.locals.set 1 (.i32 (UInt32.ofNat i)) |>.set 2 (.i32 left_i)
                |>.set 3 (.i32 (UInt32.ofNat j)) |>.set 5 (.i32 (UInt32.ofNat i))
            let locA_11 : Locals := { locA with locals := locA_11_locs }
            -- store after B2: out[k]=left_i written, frame+8=i+1 written
            let stA_m2 : Store Unit := { stA with mem := mem2_A }
            -- ── auxiliary lemmas ──
            have hi_lt_u32 : UInt32.ofNat i < n_left := by
              rw [UInt32.lt_iff_toNat_lt_toNat, UInt32.toNat_ofNat']
              have := n_left.toNat_lt; omega
            have hj_lt_u32 : UInt32.ofNat j < n_right := by
              rw [UInt32.lt_iff_toNat_lt_toNat, UInt32.toNat_ofNat']
              have := n_right.toNat_lt; omega
            have hk_lt_u32 : UInt32.ofNat k < n_out := by
              rw [UInt32.lt_iff_toNat_lt_toNat, UInt32.toNat_ofNat']
              have := n_out.toNat_lt; omega
            have hmem1_fr8 : mem1_A.read32 (frame + 8) = UInt32.ofNat i := by
              simp only [mem1_A,
                Mem.read32_write32_of_disjoint _ (out_ptr + 4 * UInt32.ofNat k) (frame + 8) _
                  (by rw [hout_k_toNat, hft8]; rcases hframe_out_disj with h | h <;> omega)]
              exact hi_m
            have hmem2_fr16 : mem2_A.read32 (frame + 16) = UInt32.ofNat k := by
              simp only [mem2_A,
                Mem.read32_write32_of_disjoint _ (frame + 8) (frame + 16) _
                  (by left; rw [hft8, hft16]; omega)]
              simp only [mem1_A,
                Mem.read32_write32_of_disjoint _ (out_ptr + 4 * UInt32.ofNat k) (frame + 16) _
                  (by rw [hout_k_toNat, hft16]; rcases hframe_out_disj with h | h <;> omega)]
              exact hk_m
            have hbnd_out_k : ¬((out_ptr + 4 * UInt32.ofNat k).toNat + 4 > stA.mem.pages * 65536) := by
              rw [hout_k_toNat]; omega
            have hbnd_fr8 : ¬((frame + 8).toNat + 4 > stA.mem.pages * 65536) := by
              rw [hft8]; omega
            have hbnd_fr12 : ¬((frame + 12).toNat + 4 > stA.mem.pages * 65536) := by
              rw [hft12]; omega
            have hbnd_fr16 : ¬((frame + 16).toNat + 4 > stA.mem.pages * 65536) := by
              rw [hft16]; omega
            have hbnd_left_i : ¬((left_ptr + 4 * UInt32.ofNat i).toNat + 4 > stA.mem.pages * 65536) := by
              rw [toNat_wordAddr left_ptr n_left.toNat i hlt_i (by linarith)]; omega
            have hbnd_right_j : ¬((right_ptr + 4 * UInt32.ofNat j).toNat + 4 > stA.mem.pages * 65536) := by
              rw [toNat_wordAddr right_ptr n_right.toNat j hlt_j (by linarith)]; omega
            -- ── exec chain through 14 blocks ──
            -- body14: 23 flat instructions → Break 1 (br_if 1 fires: j < n_right)
            have h_B14 : exec 1 m stA locA_7 body14 env = .Break 1 stA locA_89 := by
              -- GV helpers: {locA_7 with values := vs}.get N = locA_7.get N
              have hgv7_7 : ∀ vs, ({locA_7 with values := vs} : Locals).get 7 = locA_7.get 7 := fun _ => rfl
              have hgv1_7 : ∀ vs, ({locA_7 with values := vs} : Locals).get 1 = locA_7.get 1 := fun _ => rfl
              have hgv0_7 : ∀ vs, ({locA_7 with values := vs} : Locals).get 0 = locA_7.get 0 := fun _ => rfl
              have hgv6_7 : ∀ vs, ({locA_7 with values := vs} : Locals).get 6 = locA_7.get 6 := fun _ => rfl
              have hgv3_7 : ∀ vs, ({locA_7 with values := vs} : Locals).get 3 = locA_7.get 3 := fun _ => rfl
              -- locA_7 length facts
              have hlp_7 : locA_7.params.length = 6  := hlparams
              have hll_7 : locA_7.locals.length = 16 := by simp [locA_7, List.length_set, hllocals]
              -- locA_7 specific gets
              have hg7_7 : locA_7.get 7 = some (.i32 (UInt32.ofNat i)) := by
                simp only [Locals.get, hlp_7, hll_7, List.length_set,
                           show ¬(7 < 6) from by omega, show (7 : Nat) < 6 + 16 from by omega,
                           show (7 : Nat) - 6 = 1 from by omega]
                -- goal: locA_7.locals[1]? = some _; locA_7.locals = locA.locals.set 1 _
                change (locA.locals.set 1 (.i32 (UInt32.ofNat i)))[1]? = _
                exact List.getElem?_set_self (by rw [hllocals]; norm_num)
              have hg1_7 : locA_7.get 1 = some (.i32 n_left) := by
                simp only [Locals.get, locA_7, hlparams, show (1 : Nat) < 6 from by omega] at h1 ⊢
                exact h1
              have hg0_7 : locA_7.get 0 = some (.i32 left_ptr) := by
                simp only [Locals.get, locA_7, hlparams, show (0 : Nat) < 6 from by omega] at h0 ⊢
                exact h0
              have hg6_7 : locA_7.get 6 = some (.i32 frame) := by
                have h : locA_7.get 6 = locA.get 6 := by
                  simp [locA_7, Locals.get, hlparams, hllocals, List.length_set, List.getElem?_set]
                rw [h]; exact hf6
              have hg3_7 : locA_7.get 3 = some (.i32 n_right) := by
                simp only [Locals.get, locA_7, hlparams, show (3 : Nat) < 6 from by omega] at h3 ⊢
                exact h3
              -- raw-form get 6 after localSet 8 (sets local[2] = left_i)
              have hg6_8_raw : ∀ vs,
                  (Locals.mk locA_7.params (locA_7.locals.set 2 (.i32 left_i)) vs).get 6
                  = some (.i32 frame) := by
                intro vs
                have h : (Locals.mk locA_7.params (locA_7.locals.set 2 (.i32 left_i)) vs).get 6
                    = locA.get 6 := by
                  simp [locA_7, Locals.get, hlparams, hllocals, List.length_set, List.getElem?_set]
                rw [h]; exact hf6
              -- raw-form gets after localSet 9 (sets local[3] = j)
              have hg9_89_raw : ∀ vs,
                  (Locals.mk locA_7.params
                    ((locA_7.locals.set 2 (.i32 left_i)).set 3 (.i32 (UInt32.ofNat j))) vs).get 9
                  = some (.i32 (UInt32.ofNat j)) := by
                intro vs
                simp only [Locals.get, hlp_7, hll_7, List.length_set,
                           show ¬(9 < 6) from by omega, show (9 : Nat) < 6 + 16 from by omega,
                           show (9 : Nat) - 6 = 3 from by omega]
                -- goal: ((locA_7.locals.set 2 _).set 3 _)[3]? = some _
                exact List.getElem?_set_self (by simp [List.length_set, hll_7])
              have hg3_89_raw : ∀ vs,
                  (Locals.mk locA_7.params
                    ((locA_7.locals.set 2 (.i32 left_i)).set 3 (.i32 (UInt32.ofNat j))) vs).get 3
                  = some (.i32 n_right) := by
                intro vs
                have h3_raw : locA.params[3]? = some (.i32 n_right) := by
                  have h := h3
                  simp only [Locals.get, hlparams, show (3 : Nat) < 6 from by omega] at h
                  exact h
                simp only [Locals.get, hlp_7, show (3 : Nat) < 6 from by omega]
                exact h3_raw
              -- shl-by-2 = multiply-by-4
              have hshl_i : UInt32.ofNat i <<< ((2 : UInt32) % 32) = 4 * UInt32.ofNat i := by
                rw [show (2 : UInt32) % 32 = 2 from by decide]
                apply UInt32.toNat_inj.mp
                have hi_bnd : i < 2 ^ 30 := by have := n_left.toNat_lt; omega
                simp only [UInt32.toNat_mul, UInt32.toNat_ofNat',
                           show (4 : UInt32).toNat = 4 from rfl,
                           Nat.mod_eq_of_lt (show i < 4294967296 from by omega),
                           Nat.mod_eq_of_lt (show i * 4 < 4294967296 from by omega)]
                simp [UInt32.shiftLeft, Fin.shiftLeft, Nat.shiftLeft_eq]; omega
              have hshl_j : UInt32.ofNat j <<< ((2 : UInt32) % 32) = 4 * UInt32.ofNat j := by
                rw [show (2 : UInt32) % 32 = 2 from by decide]
                apply UInt32.toNat_inj.mp
                have hj_bnd : j < 2 ^ 30 := by have := n_right.toNat_lt; omega
                simp only [UInt32.toNat_mul, UInt32.toNat_ofNat',
                           show (4 : UInt32).toNat = 4 from rfl,
                           Nat.mod_eq_of_lt (show j < 4294967296 from by omega),
                           Nat.mod_eq_of_lt (show j * 4 < 4294967296 from by omega)]
                simp [UInt32.shiftLeft, Fin.shiftLeft, Nat.shiftLeft_eq]; omega
              -- big simp: reduce body14's 23 flat instructions
              simp only [exec, execOne.eq_def, body14, Locals.set?,
                         hgv7_7, hgv1_7, hgv0_7, hgv6_7, hgv3_7,
                         hg7_7, hg1_7, hg0_7, hg6_7, hg3_7,
                         if_pos hi_lt_u32,
                         show (1 : UInt32) &&& 1 = 1 from by decide,
                         show (if (1 : UInt32) = 0 then (1 : UInt32) else 0) = 0 from by decide,
                         hshl_i,
                         if_neg (show ¬((4 * UInt32.ofNat i + left_ptr).toNat +
                                         UInt32.toNat (0 : UInt32) + 4 > stA.mem.pages * 65536) from by
                                   rw [show 4 * UInt32.ofNat i + left_ptr =
                                           left_ptr + 4 * UInt32.ofNat i from UInt32.add_comm _ _,
                                       show UInt32.toNat (0 : UInt32) = 0 from rfl]; omega),
                         show stA.mem.read32 (4 * UInt32.ofNat i + left_ptr + (0 : UInt32)) = left_i from by
                           rw [show 4 * UInt32.ofNat i + left_ptr + (0 : UInt32) =
                                   left_ptr + 4 * UInt32.ofNat i from by
                               rw [UInt32.add_comm (4 * UInt32.ofNat i) left_ptr, UInt32.add_zero]],
                         hlp_7, hll_7, List.length_set,
                         if_neg (show ¬(8 < 6) from by omega),
                         if_pos (show (8 : Nat) < 6 + 16 from by omega),
                         show (8 : Nat) - 6 = 2 from by omega,
                         hg6_8_raw,
                         if_neg (show ¬(frame.toNat + (12 : UInt32).toNat + 4 > stA.mem.pages * 65536)
                                   from by simp only [show (12 : UInt32).toNat = 12 from by decide]; omega),
                         show stA.mem.read32 (frame + (12 : UInt32)) = UInt32.ofNat j from hj_m,
                         if_neg (show ¬(9 < 6) from by omega),
                         if_pos (show (9 : Nat) < 6 + 16 from by omega),
                         show (9 : Nat) - 6 = 3 from by omega,
                         hg9_89_raw, hg3_89_raw,
                         if_pos hj_lt_u32,
                         show (1 : UInt32) &&& 1 = 1 from by decide,
                         show Locals.mk locA_7.params
                               ((locA_7.locals.set 2 (.i32 left_i)).set 3 (.i32 (UInt32.ofNat j)))
                               locA.values = locA_89 from rfl]
              rfl
            -- body13: Break(0+1) from body14 → Break 0
            have h_B13 : exec 2 m stA locA_7 body13 env = .Break 0 stA locA_89 := by
              rw [show (2:Nat) = 1+1 from rfl, exec_block_cons, h_B14]
            -- body12: Break 0 → B12_compare runs, leU fires (left_i ≤ right_j), br_if 2 → Break 2
            have h_B12_A : exec 3 m stA locA_7 body12 env = .Break 2 stA locA_89 := by
              rw [show (3:Nat) = 2+1 from rfl, exec_block_cons, h_B13]
              simp only [List.take_zero, List.drop_zero, List.nil_append]
              have hll_89 : locA_89.locals.length = 16 := by
                simp [locA_89, locA_89_locs, List.length_set, hllocals]
              have hgv8_89 : ∀ vs, ({locA_89 with values := vs} : Locals).get 8 = locA_89.get 8 := fun _ => rfl
              have hgv2_89 : ∀ vs, ({locA_89 with values := vs} : Locals).get 2 = locA_89.get 2 := fun _ => rfl
              have hgv9_89 : ∀ vs, ({locA_89 with values := vs} : Locals).get 9 = locA_89.get 9 := fun _ => rfl
              have hg8_89 : locA_89.get 8 = some (.i32 left_i) := by
                simp only [Locals.get, locA_89, locA_89_locs, hlparams, hllocals, List.length_set,
                           show ¬(8 < 6) from by omega, show (8:Nat) < 6+16 from by omega,
                           show (8:Nat) - 6 = 2 from by omega]
                rw [List.getElem?_set_ne (show (3:Nat) ≠ 2 from by omega)]
                exact List.getElem?_set_self (by rw [List.length_set, hllocals]; norm_num)
              have hg2_89 : locA_89.get 2 = some (.i32 right_ptr) := by
                simp only [Locals.get, locA_89, hlparams, show (2:Nat) < 6 from by omega] at h2 ⊢
                exact h2
              have hg9_89 : locA_89.get 9 = some (.i32 (UInt32.ofNat j)) := by
                simp only [Locals.get, locA_89, locA_89_locs, hlparams, hllocals, List.length_set,
                           show ¬(9 < 6) from by omega, show (9:Nat) < 6+16 from by omega,
                           show (9:Nat) - 6 = 3 from by omega]
                exact List.getElem?_set_self (by rw [List.length_set, List.length_set, hllocals]; norm_num)
              have hshl_j : UInt32.ofNat j <<< ((2:UInt32) % 32) = 4 * UInt32.ofNat j := by
                rw [show (2:UInt32) % 32 = 2 from by decide]
                apply UInt32.toNat_inj.mp
                have hj_bnd : j < 2^30 := by have := n_right.toNat_lt; omega
                simp only [UInt32.toNat_mul, UInt32.toNat_ofNat',
                           show (4:UInt32).toNat = 4 from rfl,
                           Nat.mod_eq_of_lt (show j < 4294967296 from by omega),
                           Nat.mod_eq_of_lt (show j*4 < 4294967296 from by omega)]
                simp [UInt32.shiftLeft, Fin.shiftLeft, Nat.shiftLeft_eq]; omega
              simp only [exec, execOne.eq_def,
                         show ({locA_89 with values := locA_7.values} : Locals) = locA_89 from rfl,
                         hgv8_89, hgv2_89, hgv9_89,
                         hg8_89, hg2_89, hg9_89,
                         hshl_j,
                         if_neg (show ¬((4 * UInt32.ofNat j + right_ptr).toNat +
                                         UInt32.toNat (0:UInt32) + 4 > stA.mem.pages * 65536) from by
                                   rw [show 4 * UInt32.ofNat j + right_ptr =
                                               right_ptr + 4 * UInt32.ofNat j from UInt32.add_comm _ _,
                                           show UInt32.toNat (0:UInt32) = 0 from rfl]
                                   omega),
                         show stA.mem.read32 (4 * UInt32.ofNat j + right_ptr + (0:UInt32)) = right_j from by
                             rw [show 4 * UInt32.ofNat j + right_ptr + (0:UInt32) =
                                         right_ptr + 4 * UInt32.ofNat j from by
                                     rw [UInt32.add_comm (4 * UInt32.ofNat j) right_ptr, UInt32.add_zero]],
                         if_pos hle,
                         show (1:UInt32) &&& 1 = 1 from by decide,
                         show ({locA_89 with values := locA.values} : Locals) = locA_89 from rfl]
              rfl
            -- body11: Break(1+1) → Break 1
            have h_B11 : exec 4 m stA locA_7 body11 env = .Break 1 stA locA_89 := by
              rw [show (4:Nat) = 3+1 from rfl, exec_block_cons, h_B12_A]
            -- body10: Break(0+1) → Break 0 (B10_right_cont NOT reached in path A)
            have h_B10 : exec 5 m stA locA_7 body10 env = .Break 0 stA locA_89 := by
              rw [show (5:Nat) = 4+1 from rfl, exec_block_cons, h_B11]
            -- body9: Break 0 → B9_left_cont runs, br_if 4 fires (i < n_left) → Break 4
            have h_B9 : exec 6 m stA locA_7 body9 env = .Break 4 stA locA_11 := by
              rw [show (6:Nat) = 5+1 from rfl, exec_block_cons, h_B10]
              simp only [List.take_zero, List.drop_zero, List.nil_append]
              -- B9_left_cont: localGet 6, load32 8, localSet 11, localGet 11, localGet 1, ltU, const 1, and, br_if 4
              have hlp_89 : locA_89.params.length = 6 := hlparams
              have hll_89 : locA_89.locals.length = 16 := by
                simp [locA_89, locA_89_locs, List.length_set, hllocals]
              have hgv11_11 : ∀ vs, ({locA_11 with values := vs} : Locals).get 11 = locA_11.get 11 := fun _ => rfl
              have hgv1_11  : ∀ vs, ({locA_11 with values := vs} : Locals).get 1  = locA_11.get 1  := fun _ => rfl
              have hg6_89 : locA_89.get 6 = some (.i32 frame) := by
                simp only [Locals.get, locA_89, locA_89_locs, hlparams, hllocals, List.length_set,
                           show ¬(6 < 6) from by omega, show (6:Nat) < 6+16 from by omega,
                           show (6:Nat) - 6 = 0 from by omega]
                rw [List.getElem?_set_ne (show (3:Nat) ≠ 0 from by omega)]
                rw [List.getElem?_set_ne (show (2:Nat) ≠ 0 from by omega)]
                rw [List.getElem?_set_ne (show (1:Nat) ≠ 0 from by omega)]
                simpa [Locals.get, hlparams, hllocals, List.length_set,
                       show ¬(6 < 6) from by omega, show (6:Nat) < 6+16 from by omega,
                       show (6:Nat) - 6 = 0 from by omega] using hf6
              have hg11_11 : locA_11.get 11 = some (.i32 (UInt32.ofNat i)) := by
                simp only [Locals.get, locA_11, locA_11_locs, hlparams, hllocals, List.length_set,
                           show ¬(11 < 6) from by omega, show (11:Nat) < 6+16 from by omega,
                           show (11:Nat) - 6 = 5 from by omega]
                exact List.getElem?_set_self
                  (by rw [List.length_set, List.length_set, List.length_set, hllocals]; norm_num)
              have hg1_11 : locA_11.get 1 = some (.i32 n_left) := by
                simp only [Locals.get, locA_11, hlparams, show (1:Nat) < 6 from by omega] at h1 ⊢
                exact h1
              simp only [exec, execOne.eq_def,
                         show ({locA_89 with values := locA_7.values} : Locals) = locA_89 from rfl,
                         hg6_89,
                         if_neg (show ¬(frame.toNat + (8:UInt32).toNat + 4 > stA.mem.pages * 65536) from by
                                   simp only [show (8:UInt32).toNat = 8 from by decide]; omega),
                         show stA.mem.read32 (frame + (8:UInt32)) = UInt32.ofNat i from hi_m,
                         Locals.set?,
                         hlp_89, hll_89, List.length_set,
                         if_neg (show ¬(11 < 6) from by omega),
                         if_pos (show (11:Nat) < 6 + 16 from by omega),
                         show (11:Nat) - 6 = 5 from by omega,
                         show Locals.mk locA_89.params (locA_89.locals.set 5 (.i32 (UInt32.ofNat i))) locA_89.values = locA_11 from rfl,
                         hgv11_11, hg11_11, hgv1_11, hg1_11,
                         if_pos hi_lt_u32,
                         show (1:UInt32) &&& 1 = 1 from by decide,
                         show ({locA_11 with values := locA_11.values} : Locals) = locA_11 from rfl]
              rfl
            -- body8: Break(3+1) → Break 3
            have h_B8 : exec 7 m stA locA_7 body8 env = .Break 3 stA locA_11 := by
              rw [show (7:Nat) = 6+1 from rfl, exec_block_cons, h_B9]
            -- body7: Break(2+1) → Break 2
            have h_B7 : exec 8 m stA locA_7 body7 env = .Break 2 stA locA_11 := by
              rw [show (8:Nat) = 7+1 from rfl, exec_block_cons, h_B8]
            -- body6: Break(1+1) → Break 1
            have h_B6 : exec 9 m stA locA_7 body6 env = .Break 1 stA locA_11 := by
              rw [show (9:Nat) = 8+1 from rfl, exec_block_cons, h_B7]
            -- body5: Break(0+1) → Break 0 (B5_panic NOT reached)
            have h_B5 : exec 10 m stA locA_7 body5 env = .Break 0 stA locA_11 := by
              rw [show (10:Nat) = 9+1 from rfl, exec_block_cons, h_B6]
            -- body4: Break 0 → B4_left_cont runs, localSet 14,15, br_if 1 fires → Break 1
            have h_B4 : exec 11 m stA locA_7 body4 env = .Break 1 stA locA_out_A := by
              rw [show (11:Nat) = 10+1 from rfl, exec_block_cons, h_B5]
              simp only [List.take_zero, List.drop_zero, List.nil_append]
              -- B4_left_cont: localGet 0, localGet 11, const 2, shl, add, load32 0, localSet 14,
              --                localGet 6, load32 16, localSet 15, localGet 15, localGet 5, ltU, const 1, and, br_if 1
              have hlp_11 : locA_11.params.length = 6 := hlparams
              have hll_11 : locA_11.locals.length = 16 := by
                simp [locA_11, locA_11_locs, List.length_set, hllocals]
              have hgv0_11  : ∀ vs, ({locA_11 with values := vs} : Locals).get 0  = locA_11.get 0  := fun _ => rfl
              have hgv11_11 : ∀ vs, ({locA_11 with values := vs} : Locals).get 11 = locA_11.get 11 := fun _ => rfl
              have hg0_11 : locA_11.get 0 = some (.i32 left_ptr) := by
                simp only [Locals.get, locA_11, hlparams, show (0:Nat) < 6 from by omega] at h0 ⊢; exact h0
              have hg11_11 : locA_11.get 11 = some (.i32 (UInt32.ofNat i)) := by
                simp only [Locals.get, locA_11, locA_11_locs, hlparams, hllocals, List.length_set,
                           show ¬(11 < 6) from by omega, show (11:Nat) < 6+16 from by omega,
                           show (11:Nat) - 6 = 5 from by omega]
                exact List.getElem?_set_self
                  (by rw [List.length_set, List.length_set, List.length_set, hllocals]; norm_num)
              -- ∀-vs helpers for gets from intermediate/post-localSet states
              have hg6_14_raw : ∀ vs,
                  (Locals.mk locA_11.params (locA_11.locals.set 8 (.i32 left_i)) vs).get 6
                  = some (.i32 frame) := by
                intro vs
                have h : (Locals.mk locA_11.params (locA_11.locals.set 8 (.i32 left_i)) vs).get 6
                    = locA.get 6 := by
                  simp [locA_11, locA_11_locs, Locals.get, hlparams, hllocals,
                        List.length_set, List.getElem?_set]
                rw [h]; exact hf6
              have hg15_out_raw : ∀ vs,
                  (Locals.mk locA_11.params
                    ((locA_11.locals.set 8 (.i32 left_i)).set 9 (.i32 (UInt32.ofNat k))) vs).get 15
                  = some (.i32 (UInt32.ofNat k)) := by
                intro vs
                simp only [Locals.get, hlp_11, hll_11, List.length_set,
                           show ¬(15 < 6) from by omega, show (15:Nat) < 6+16 from by omega,
                           show (15:Nat) - 6 = 9 from by omega]
                exact List.getElem?_set_self (by simp [List.length_set, hll_11])
              have hg5_out_raw : ∀ vs,
                  (Locals.mk locA_11.params
                    ((locA_11.locals.set 8 (.i32 left_i)).set 9 (.i32 (UInt32.ofNat k))) vs).get 5
                  = some (.i32 n_out) := by
                intro vs
                have h5_raw : locA.params[5]? = some (.i32 n_out) := by
                  have h := h5
                  simp only [Locals.get, hlparams, show (5:Nat) < 6 from by omega] at h
                  exact h
                simp only [Locals.get, hlp_11, show (5:Nat) < 6 from by omega]
                exact h5_raw
              have hshl_i : UInt32.ofNat i <<< ((2:UInt32) % 32) = 4 * UInt32.ofNat i := by
                rw [show (2:UInt32) % 32 = 2 from by decide]
                apply UInt32.toNat_inj.mp
                have hi_bnd : i < 2^30 := by have := n_left.toNat_lt; omega
                simp only [UInt32.toNat_mul, UInt32.toNat_ofNat',
                           show (4:UInt32).toNat = 4 from rfl,
                           Nat.mod_eq_of_lt (show i < 4294967296 from by omega),
                           Nat.mod_eq_of_lt (show i * 4 < 4294967296 from by omega)]
                simp [UInt32.shiftLeft, Fin.shiftLeft, Nat.shiftLeft_eq]; omega
              simp only [exec, execOne.eq_def,
                         show ({locA_11 with values := locA_7.values} : Locals) = locA_11 from rfl,
                         hgv0_11, hg0_11, hgv11_11, hg11_11,
                         hshl_i,
                         if_neg (show ¬((4 * UInt32.ofNat i + left_ptr).toNat +
                                         UInt32.toNat (0:UInt32) + 4 > stA.mem.pages * 65536) from by
                                   rw [show 4 * UInt32.ofNat i + left_ptr =
                                               left_ptr + 4 * UInt32.ofNat i from UInt32.add_comm _ _,
                                       show UInt32.toNat (0:UInt32) = 0 from rfl]; omega),
                         show stA.mem.read32 (4 * UInt32.ofNat i + left_ptr + (0:UInt32)) = left_i from by
                             rw [show 4 * UInt32.ofNat i + left_ptr + (0:UInt32) =
                                         left_ptr + 4 * UInt32.ofNat i from by
                                     rw [UInt32.add_comm (4 * UInt32.ofNat i) left_ptr, UInt32.add_zero]],
                         Locals.set?,
                         hlp_11, hll_11, List.length_set,
                         if_neg (show ¬(14 < 6) from by omega),
                         if_pos (show (14:Nat) < 6 + 16 from by omega),
                         show (14:Nat) - 6 = 8 from by omega,
                         hg6_14_raw,
                         if_neg (show ¬(frame.toNat + (16:UInt32).toNat + 4 > stA.mem.pages * 65536) from by
                                   simp only [show (16:UInt32).toNat = 16 from by decide]; omega),
                         show stA.mem.read32 (frame + (16:UInt32)) = UInt32.ofNat k from hk_m,
                         if_neg (show ¬(15 < 6) from by omega),
                         if_pos (show (15:Nat) < 6 + 16 from by omega),
                         show (15:Nat) - 6 = 9 from by omega,
                         hg15_out_raw, hg5_out_raw,
                         if_pos hk_lt_u32,
                         show (1:UInt32) &&& 1 = 1 from by decide,
                         show Locals.mk locA_11.params
                               ((locA_11.locals.set 8 (.i32 left_i)).set 9 (.i32 (UInt32.ofNat k)))
                               locA.values = locA_out_A from rfl]
              rfl
            -- body3: Break(0+1) → Break 0 (B3_panic NOT reached)
            have h_B3 : exec 12 m stA locA_7 body3 env = .Break 0 stA locA_out_A := by
              rw [show (12:Nat) = 11+1 from rfl, exec_block_cons, h_B4]
            -- body2: Break 0 → B2_store_left runs, writes out[k]=left_i, frame+8=i+1, br 1 → Break 1
            have h_B2 : exec 13 m stA locA_7 body2 env = .Break 1 stA_m2 locA_out_A := by
              rw [show (13:Nat) = 12+1 from rfl, exec_block_cons, h_B3]
              simp only [List.take_zero, List.drop_zero, List.nil_append]
              -- B2_store_left: localGet 4, localGet 15, const 2, shl, add, localGet 14,
              --   store32 0 (→mem1_A), localGet 6, localGet 6, load32 8 (→i), const 1, add,
              --   store32 8 (→mem2_A), br 1
              have hgv4_out  : ∀ vs, ({locA_out_A with values := vs} : Locals).get 4  = locA_out_A.get 4  := fun _ => rfl
              have hgv15_out : ∀ vs, ({locA_out_A with values := vs} : Locals).get 15 = locA_out_A.get 15 := fun _ => rfl
              have hgv14_out : ∀ vs, ({locA_out_A with values := vs} : Locals).get 14 = locA_out_A.get 14 := fun _ => rfl
              have hgv6_out  : ∀ vs, ({locA_out_A with values := vs} : Locals).get 6  = locA_out_A.get 6  := fun _ => rfl
              have hg4_out : locA_out_A.get 4 = some (.i32 out_ptr) := by
                simp only [Locals.get, locA_out_A, hlparams, show (4:Nat) < 6 from by omega] at h4 ⊢; exact h4
              have hg15_out : locA_out_A.get 15 = some (.i32 (UInt32.ofNat k)) := by
                simp only [Locals.get, locA_out_A, locA_out_locs, hlparams, hllocals, List.length_set,
                           show ¬(15 < 6) from by omega, show (15:Nat) < 6+16 from by omega,
                           show (15:Nat) - 6 = 9 from by omega]
                exact List.getElem?_set_self
                  (by rw [List.length_set, List.length_set, List.length_set,
                           List.length_set, List.length_set, hllocals]; norm_num)
              have hg14_out : locA_out_A.get 14 = some (.i32 left_i) := by
                simp only [Locals.get, locA_out_A, locA_out_locs, hlparams, hllocals, List.length_set,
                           show ¬(14 < 6) from by omega, show (14:Nat) < 6+16 from by omega,
                           show (14:Nat) - 6 = 8 from by omega]
                rw [List.getElem?_set_ne (show (9:Nat) ≠ 8 from by omega)]
                exact List.getElem?_set_self
                  (by rw [List.length_set, List.length_set, List.length_set,
                           List.length_set, hllocals]; norm_num)
              have hg6_out : locA_out_A.get 6 = some (.i32 frame) := by
                simp only [Locals.get, locA_out_A, locA_out_locs, hlparams, hllocals, List.length_set,
                           show ¬(6 < 6) from by omega, show (6:Nat) < 6+16 from by omega,
                           show (6:Nat) - 6 = 0 from by omega,
                           List.getElem?_set, show (9:Nat) ≠ 0 from by omega,
                           show (8:Nat) ≠ 0 from by omega, show (5:Nat) ≠ 0 from by omega,
                           show (3:Nat) ≠ 0 from by omega, show (2:Nat) ≠ 0 from by omega,
                           show (1:Nat) ≠ 0 from by omega, if_false]
                simpa [Locals.get, hlparams, hllocals, show ¬(6 < 6) from by omega] using hf6
              have hshl_k : UInt32.ofNat k <<< ((2:UInt32) % 32) = 4 * UInt32.ofNat k := by
                rw [show (2:UInt32) % 32 = 2 from by decide]
                apply UInt32.toNat_inj.mp
                have hk_bnd : k < 2^30 := by have := n_out.toNat_lt; omega
                simp only [UInt32.toNat_mul, UInt32.toNat_ofNat',
                           show (4:UInt32).toNat = 4 from rfl,
                           Nat.mod_eq_of_lt (show k < 4294967296 from by omega),
                           Nat.mod_eq_of_lt (show k * 4 < 4294967296 from by omega)]
                simp [UInt32.shiftLeft, Fin.shiftLeft, Nat.shiftLeft_eq]; omega
              simp only [exec, execOne.eq_def,
                         show ({locA_out_A with values := locA_7.values} : Locals) = locA_out_A from rfl,
                         hgv4_out, hg4_out, hgv15_out, hg15_out,
                         hshl_k,
                         if_neg (show ¬((4 * UInt32.ofNat k + out_ptr).toNat +
                                         UInt32.toNat (0:UInt32) + 4 > stA.mem.pages * 65536) from by
                                   rw [show 4 * UInt32.ofNat k + out_ptr =
                                               out_ptr + 4 * UInt32.ofNat k from UInt32.add_comm _ _,
                                       show UInt32.toNat (0:UInt32) = 0 from rfl]; omega),
                         show stA.mem.write32 (4 * UInt32.ofNat k + out_ptr + (0:UInt32)) left_i = mem1_A from by
                             rw [show 4 * UInt32.ofNat k + out_ptr + (0:UInt32) =
                                         out_ptr + 4 * UInt32.ofNat k from by
                                     rw [UInt32.add_comm (4 * UInt32.ofNat k) out_ptr, UInt32.add_zero]],
                         hgv14_out, hg14_out,
                         hgv6_out, hg6_out,
                         if_neg (show ¬(frame.toNat + UInt32.toNat (8:UInt32) + 4 >
                                         {stA with mem := mem1_A}.mem.pages * 65536) from by
                                   rw [show ({stA with mem := mem1_A} : Store Unit).mem.pages =
                                         stA.mem.pages from rfl,
                                       show UInt32.toNat (8:UInt32) = 8 from by decide, hft8.symm]
                                   exact hbnd_fr8),
                         show ({stA with mem := mem1_A} : Store Unit).mem.read32 (frame + (8:UInt32)) =
                               UInt32.ofNat i from hmem1_fr8,
                         show (1:UInt32) + UInt32.ofNat i = UInt32.ofNat i + 1 from UInt32.add_comm _ _,
                         if_neg (show ¬(frame.toNat + UInt32.toNat (8:UInt32) + 4 >
                                         {stA with mem := mem1_A}.mem.pages * 65536) from by
                                   rw [show ({stA with mem := mem1_A} : Store Unit).mem.pages =
                                         stA.mem.pages from rfl,
                                       show UInt32.toNat (8:UInt32) = 8 from by decide, hft8.symm]
                                   exact hbnd_fr8),
                         show ({stA with mem := mem1_A} : Store Unit).mem.write32
                               (frame + (8:UInt32)) (UInt32.ofNat i + 1) = mem2_A from rfl,
                         show ({stA with mem := mem2_A} : Store Unit) = stA_m2 from rfl,
                         show ({locA_out_A with values := locA_out_A.values} : Locals) = locA_out_A from rfl]
            -- body1: Break(0+1) → Break 0 (B1_panic NOT reached)
            have h_B1 : exec 14 m stA locA_7 body1 env = .Break 0 stA_m2 locA_out_A := by
              rw [show (14:Nat) = 13+1 from rfl, exec_block_cons, h_B2]
            -- ── assemble: prefix → outer block (h_B1) → suffix ──
            have h_pre : exec 15 m stA locA mainMergeBody env =
                exec 15 m stA locA_7
                  (.block 0 0 body1 :: [.localGet 6, .localGet 6, .load32 (16:UInt32),
                    .const (1:UInt32), .add, .store32 (16:UInt32), .br 0]) env := by
              -- Abstract the continuation to make body1 truly opaque to simp
              have h_prefix_aux : ∀ cont : Program,
                  exec 15 m stA locA
                    ([.localGet 6, .load32 (8:UInt32), .localGet 1, .ltU,
                      .const (1:UInt32), .and, .eqz, .br_if 1,
                      .localGet 6, .load32 (12:UInt32), .localGet 3, .ltU,
                      .const (1:UInt32), .and, .eqz, .br_if 1,
                      .localGet 6, .load32 (8:UInt32), .localSet 7] ++ cont) env
                    = exec 15 m stA locA_7 cont env := by
                intro cont
                have hgv6_pre : ∀ vs, ({locA with values := vs} : Locals).get 6 = locA.get 6 := fun _ => rfl
                have hgv1_pre : ∀ vs, ({locA with values := vs} : Locals).get 1 = locA.get 1 := fun _ => rfl
                have hgv3_pre : ∀ vs, ({locA with values := vs} : Locals).get 3 = locA.get 3 := fun _ => rfl
                -- Convert ++ cont to pure cons form (by rfl, since ++ is definitional for finite lists)
                rw [show [.localGet 6, .load32 (8:UInt32), .localGet 1, .ltU,
                          .const (1:UInt32), .and, .eqz, .br_if 1,
                          .localGet 6, .load32 (12:UInt32), .localGet 3, .ltU,
                          .const (1:UInt32), .and, .eqz, .br_if 1,
                          .localGet 6, .load32 (8:UInt32), .localSet 7] ++ cont =
                         .localGet 6 :: .load32 (8:UInt32) :: .localGet 1 :: .ltU ::
                         .const (1:UInt32) :: .and :: .eqz :: .br_if 1 ::
                         .localGet 6 :: .load32 (12:UInt32) :: .localGet 3 :: .ltU ::
                         .const (1:UInt32) :: .and :: .eqz :: .br_if 1 ::
                         .localGet 6 :: .load32 (8:UInt32) :: .localSet 7 :: cont from rfl]
                -- Now simp on pure cons form: no List.cons_append needed
                simp only
                  [exec, execOne.eq_def, Locals.set?,
                   hgv6_pre, hgv1_pre, hgv3_pre,
                   hf6, h1, h3,
                   hi_m, hj_m,
                   if_neg (show ¬(frame.toNat + UInt32.toNat (8 : UInt32) + 4 > stA.mem.pages * 65536) from by
                     rw [show UInt32.toNat (8 : UInt32) = 8 from by decide, ← hft8]; exact hbnd_fr8),
                   if_pos hi_lt_u32,
                   show (1 : UInt32) &&& 1 = 1 from by decide,
                   show (if (1 : UInt32) = 0 then (1 : UInt32) else 0) = 0 from by decide,
                   if_neg (show ¬(frame.toNat + UInt32.toNat (12 : UInt32) + 4 > stA.mem.pages * 65536) from by
                     rw [show UInt32.toNat (12 : UInt32) = 12 from by decide, ← hft12]; exact hbnd_fr12),
                   if_pos hj_lt_u32,
                   hlparams, hllocals,
                   if_neg (show ¬(7 < 6) from by omega),
                   if_pos (show (7 : Nat) < 6 + 16 from by omega),
                   show (7 : Nat) - 6 = 1 from by omega]
                rfl
              exact h_prefix_aux _
            rw [h_pre, show (15:Nat) = 14+1 from rfl, exec_block_cons, h_B1]
            simp only [List.take_zero, List.drop_zero, List.nil_append]
            -- suffix: localGet 6 ×2, load32 16 (=k), const 1, add (=k+1), store32 16 (→mem3_A), br 0
            have hgv6_suf : ∀ vs, ({locA_out_A with values := vs} : Locals).get 6 = locA_out_A.get 6 := fun _ => rfl
            have hg6_suf : locA_out_A.get 6 = some (.i32 frame) := by
              simp only [Locals.get, locA_out_A, locA_out_locs, hlparams, hllocals, List.length_set,
                         show ¬(6 < 6) from by omega, show (6:Nat) < 6+16 from by omega,
                         show (6:Nat) - 6 = 0 from by omega,
                         List.getElem?_set, show (9:Nat) ≠ 0 from by omega,
                         show (8:Nat) ≠ 0 from by omega, show (5:Nat) ≠ 0 from by omega,
                         show (3:Nat) ≠ 0 from by omega, show (2:Nat) ≠ 0 from by omega,
                         show (1:Nat) ≠ 0 from by omega, if_false]
              simpa [Locals.get, hlparams, hllocals, show ¬(6 < 6) from by omega] using hf6
            simp only [exec, execOne.eq_def,
                       show ({locA_out_A with values := locA_7.values} : Locals) = locA_out_A from rfl,
                       hgv6_suf, hg6_suf,
                       if_neg (show ¬(frame.toNat + UInt32.toNat (16 : UInt32) + 4 > stA_m2.mem.pages * 65536) from by
                         rw [show stA_m2.mem.pages = stA.mem.pages from rfl,
                             show UInt32.toNat (16 : UInt32) = 16 from by decide, ← hft16]
                         exact hbnd_fr16),
                       show stA_m2.mem.read32 (frame + (16 : UInt32)) = UInt32.ofNat k from hmem2_fr16,
                       show (1 : UInt32) + UInt32.ofNat k = UInt32.ofNat (k + 1) from by
                         rw [UInt32.add_comm]; exact hk_add1,
                       show stA_m2.mem.write32 (frame + (16 : UInt32)) (UInt32.ofNat (k + 1)) = mem3_A from by
                         simp only [stA_m2, mem3_A]; rw [← hk_add1],
                       show ({stA_m2 with mem := mem3_A} : Store Unit) = stC_A from rfl,
                       show ({locA_out_A with values := locA_out_A.values} : Locals) = locA_out_A from rfl]
          obtain ⟨f_A, h_body_A⟩ := h_body_A
          -- memory reads after path A writes
          have hread8_A : stC_A.mem.read32 (frame + 8) = UInt32.ofNat (i + 1) := by
            simp only [stC_A, mem3_A, mem2_A, mem1_A]
            rw [Mem.read32_write32_of_disjoint _ (frame + 16) (frame + 8) _
                  (by right; rw [hft16, hft8]; omega),
                Mem.read32_write32_same, hi_add1]
          have hread12_A : stC_A.mem.read32 (frame + 12) = UInt32.ofNat j := by
            simp only [stC_A, mem3_A, mem2_A, mem1_A]
            rw [Mem.read32_write32_of_disjoint _ (frame + 16) (frame + 12) _
                  (by right; rw [hft16, hft12]),
                Mem.read32_write32_of_disjoint _ (frame + 8) (frame + 12) _
                  (by left; rw [hft8, hft12]),
                Mem.read32_write32_of_disjoint _ (out_ptr + 4 * UInt32.ofNat k) (frame + 12) _
                  (by rw [hout_k_toNat, hft12];
                      rcases hframe_out_disj with h | h <;> omega),
                hj_m]
          have hread16_A : stC_A.mem.read32 (frame + 16) = UInt32.ofNat (k + 1) := by
            simp only [stC_A, mem3_A]
            rw [Mem.read32_write32_same, hk_add1]
          -- locA_out_A.get 6: local[0] unchanged (set indices 1,2,3,5,8,9 ≠ 0)
          have hf6_out_A : locA_out_A.get 6 = some (.i32 frame) := by
            simp only [locA_out_A, locA_out_locs, Locals.get, hlparams, hllocals, List.length_set,
                       show ¬ (6 < 6) from by omega,
                       show 6 < 6 + 16 from by omega,
                       show 6 - 6 = 0 from by omega,
                       List.getElem?_set,
                       show (9 : Nat) ≠ 0 from by omega,
                       show (8 : Nat) ≠ 0 from by omega,
                       show (5 : Nat) ≠ 0 from by omega,
                       show (3 : Nat) ≠ 0 from by omega,
                       show (2 : Nat) ≠ 0 from by omega,
                       show (1 : Nat) ≠ 0 from by omega,
                       if_false]
            simpa [Locals.get, hlparams, hllocals,
                   show ¬ (6 < 6) from by omega] using hf6
          have hllocals_out_A : locA_out_A.locals.length = 16 := by
            simp [locA_out_A, locA_out_locs, List.length_set, hllocals]
          -- locA_out_A.get 0..5 = locA.get 0..5: params unchanged, needs hlparams for if-branch
          have hg_eq_A : ∀ n, n < 6 → locA_out_A.get n = locA.get n := fun n hn => by
            simp only [locA_out_A, Locals.get, hlparams, if_pos hn]
          have hlparams_out_A : locA_out_A.params.length = 6 := by exact hlparams
          -- invariant restoration: (i+1, j)
          have hI_A : MergeLoopInv frame out_ptr left_ptr right_ptr n_left n_right n_out
                        i₀ j₀ k₀ st stC_A locA_out_A :=
            ⟨i + 1, j, by omega, by omega, hj_lo, hj_hi,
             hread8_A, hread12_A,
             by rw [hread16_A]; congr 1; omega,
             hf6_out_A,
             (hg_eq_A 0 (by omega)).trans h0, (hg_eq_A 1 (by omega)).trans h1,
             (hg_eq_A 2 (by omega)).trans h2, (hg_eq_A 3 (by omega)).trans h3,
             (hg_eq_A 4 (by omega)).trans h4, (hg_eq_A 5 (by omega)).trans h5,
             hlparams_out_A, hllocals_out_A, ⟨v₀, hg⟩,
             fun q hq => by
               simp only [stC_A, mem3_A, mem2_A, mem1_A]
               have hliq : (left_ptr + 4 * UInt32.ofNat q).toNat = left_ptr.toNat + 4 * q :=
                 toNat_wordAddr left_ptr n_left.toNat q hq (by linarith)
               rw [Mem.read32_write32_of_disjoint _ (frame + 16) _ _
                     (by rw [hft16, hliq]; rcases hframe_left_disj with h | h <;> omega),
                   Mem.read32_write32_of_disjoint _ (frame + 8) _ _
                     (by rw [hft8, hliq]; rcases hframe_left_disj with h | h <;> omega),
                   Mem.read32_write32_of_disjoint _ (out_ptr + 4 * UInt32.ofNat k) _ _
                     (by rw [hout_k_toNat, hliq]; rcases hleft_out_disj with h | h <;> omega)]
               exact hleft q hq,
             fun q hq => by
               simp only [stC_A, mem3_A, mem2_A, mem1_A]
               have hriq : (right_ptr + 4 * UInt32.ofNat q).toNat = right_ptr.toNat + 4 * q :=
                 toNat_wordAddr right_ptr n_right.toNat q hq (by linarith)
               rw [Mem.read32_write32_of_disjoint _ (frame + 16) _ _
                     (by rw [hft16, hriq]; rcases hframe_right_disj with h | h <;> omega),
                   Mem.read32_write32_of_disjoint _ (frame + 8) _ _
                     (by rw [hft8, hriq]; rcases hframe_right_disj with h | h <;> omega),
                   Mem.read32_write32_of_disjoint _ (out_ptr + 4 * UInt32.ofNat k) _ _
                     (by rw [hout_k_toNat, hriq]; rcases hright_out_disj with h | h <;> omega)]
               exact hright q hq,
             (by
               -- content invariant: wordsAt stC_A (out+4k₀) (W+1) ++ merge(L.drop(i+1), R.drop j)
               --                  = merge(L.drop i₀, R.drop j₀)
               -- where W = (i-i₀)+(j-j₀) and the write is at out+4k (= out+4k₀+4W)
               have hW : (i + 1 - i₀) + (j - j₀) = (i - i₀) + (j - j₀) + 1 := by omega
               rw [hW]
               -- (out_ptr + 4*k₀).toNat = out_ptr.toNat + 4*k₀
               have h_k₀_addr : (out_ptr + 4 * UInt32.ofNat k₀).toNat = out_ptr.toNat + 4 * k₀ :=
                 toNat_wordAddr out_ptr n_out.toNat k₀ (by have := hk_val; omega) (by linarith)
               -- bound for the output region
               have hout_bnd : (out_ptr + 4 * UInt32.ofNat k₀).toNat + 4 * ((i - i₀) + (j - j₀) + 1) ≤ 4294967296 := by
                 rw [h_k₀_addr]; have := hk_val; omega
               -- wordsAt stC_A (out+4k₀) (W+1) = wordsAt stA (out+4k₀) W ++ [left_i]
               have hwords : wordsAt stC_A.mem (out_ptr + 4 * UInt32.ofNat k₀) ((i - i₀) + (j - j₀) + 1) =
                   wordsAt stA.mem (out_ptr + 4 * UInt32.ofNat k₀) ((i - i₀) + (j - j₀)) ++ [left_i] := by
                 simp only [stC_A, mem3_A, mem2_A, mem1_A]
                 -- remove frame+16 and frame+8 writes (disjoint from out region)
                 rw [wordsAt_write32_of_disjoint _ _ (frame + 16) _ _ hout_bnd
                       (by rw [hft16, h_k₀_addr]; rcases hframe_out_disj with h | h <;> [left; right] <;> omega),
                     wordsAt_write32_of_disjoint _ _ (frame + 8) _ _ hout_bnd
                       (by rw [hft8, h_k₀_addr]; rcases hframe_out_disj with h | h <;> [left; right] <;> omega),
                     wordsAt_split _ _ _ ((i - i₀) + (j - j₀)) (by omega)]
                 simp only [show (i - i₀) + (j - j₀) + 1 - ((i - i₀) + (j - j₀)) = 1 from by omega]
                 congr 1
                 · -- write at out+4k disjoint from [out+4k₀, out+4k₀+4W)
                   rw [wordsAt_write32_of_disjoint _ _ (out_ptr + 4 * UInt32.ofNat k) _ _
                         (by omega)
                         (by right; rw [h_k₀_addr, hout_k_toNat]; omega)]
                 · -- write at out+4k (= out+4k₀+4W); read gives left_i
                   have hbase_W : out_ptr + 4 * UInt32.ofNat k₀ + 4 * UInt32.ofNat ((i - i₀) + (j - j₀)) =
                       out_ptr + 4 * UInt32.ofNat k := by
                     have hkeq : k₀ + ((i - i₀) + (j - j₀)) = k := by omega
                     rw [UInt32.add_assoc, ← UInt32.mul_add, ← UInt32.ofNat_add, hkeq]
                   rw [hbase_W]; simp [wordsAt, Mem.read32_write32_same]
               -- assemble: [left_i] ++ merge(L.drop(i+1), R.drop j) = left_i :: merge(...)
               rw [hwords, List.append_assoc, List.singleton_append]
               -- rewrite RHS using hcontent (reversed): merge(L.drop i₀, R.drop j₀)
               --   = wordsAt stA W ++ merge(L.drop i, R.drop j)
               conv_rhs => rw [← hcontent]
               congr 1
               -- left_i :: merge(L.drop(i+1), R.drop j) = merge(L.drop i, R.drop j)
               -- prove via merge_cons_le + List.drop_eq_getElem_cons
               have hL_drop_i : (wordsAt st.mem left_ptr n_left.toNat).drop i =
                   st.mem.read32 (left_ptr + 4 * UInt32.ofNat i) ::
                   (wordsAt st.mem left_ptr n_left.toNat).drop (i + 1) := by
                 have h1 : i < (wordsAt st.mem left_ptr n_left.toNat).length := by
                   simp [wordsAt_length]; exact hlt_i
                 rw [List.drop_eq_getElem_cons h1, wordsAt_getElem _ _ _ _ hlt_i]
               have hR_drop_j : (wordsAt st.mem right_ptr n_right.toNat).drop j =
                   st.mem.read32 (right_ptr + 4 * UInt32.ofNat j) ::
                   (wordsAt st.mem right_ptr n_right.toNat).drop (j + 1) := by
                 have h2 : j < (wordsAt st.mem right_ptr n_right.toNat).length := by
                   simp [wordsAt_length]; exact hlt_j
                 rw [List.drop_eq_getElem_cons h2, wordsAt_getElem _ _ _ _ hlt_j]
               have hleft_i_eq : left_i = st.mem.read32 (left_ptr + 4 * UInt32.ofNat i) :=
                 hleft i hlt_i
               have hle_st : st.mem.read32 (left_ptr + 4 * UInt32.ofNat i) ≤
                   st.mem.read32 (right_ptr + 4 * UInt32.ofNat j) := by
                 rw [← hleft i hlt_i, ← hright j hlt_j]; exact hle
               rw [hleft_i_eq, hL_drop_i, hR_drop_j, merge_cons_le hle_st]),
             by simp [stC_A, mem3_A, mem2_A, mem1_A, Mem.write32_pages, hpages],
             hk_global,
             by simp [stC_A, mem3_A, mem2_A, mem1_A, Mem.write32_pages, hleft_global],
             by simp [stC_A, mem3_A, mem2_A, mem1_A, Mem.write32_pages, hright_global],
             by simp [stC_A, mem3_A, mem2_A, mem1_A, Mem.write32_pages, hout_global],
             hpages_u32, hleft_out_disj, hright_out_disj, hleft_right_disj,
             hframe_left_disj, hframe_right_disj, hframe_out_disj⟩
          -- measure decrease
          have hμ_A : (n_left.toNat - (stC_A.mem.read32 (frame + 8)).toNat) +
                      (n_right.toNat - (stC_A.mem.read32 (frame + 12)).toNat) < n := by
            rw [hread8_A, hread12_A, UInt32.toNat_ofNat', UInt32.toNat_ofNat',
                Nat.mod_eq_of_lt (by have := n_left.toNat_lt; omega),
                Nat.mod_eq_of_lt (by have := n_right.toNat_lt; omega),
                ← hμ, hi_m, hj_m, UInt32.toNat_ofNat', UInt32.toNat_ofNat',
                Nat.mod_eq_of_lt (by have := n_left.toNat_lt; omega),
                Nat.mod_eq_of_lt (by have := n_right.toNat_lt; omega)]
            omega
          -- IH at reduced measure: input is (stC_A, locA_out_A)
          obtain ⟨f_rest, hf_rest⟩ := IH _ hμ_A stC_A locA_out_A hI_A rfl
          -- Fuel composition: one body iteration at stA then IH fuel at stC_A
          have hbody_ne : exec f_A m stA locA mainMergeBody env ≠ .OutOfFuel := by
            simp [h_body_A]
          have hfuel_ne : exec f_rest m stC_A locA_out_A [.block 0 0 [.loop 0 0 mainMergeBody]] env ≠ .OutOfFuel :=
            fun h => by rw [h] at hf_rest; exact hf_rest
          have hbody_mono : exec (max f_A f_rest) m stA locA mainMergeBody env = .Break 0 stC_A locA_out_A :=
            (exec_fuel_mono (Nat.le_max_left f_A f_rest) hbody_ne).trans h_body_A
          have hblock_mono : exec (max f_A f_rest + 1) m stC_A locA_out_A [.block 0 0 [.loop 0 0 mainMergeBody]] env =
              exec f_rest m stC_A locA_out_A [.block 0 0 [.loop 0 0 mainMergeBody]] env :=
            exec_fuel_mono (by omega) hfuel_ne
          have hloop_single : ∀ F stT locT,
              exec F m stT locT [.loop 0 0 mainMergeBody] env =
              execOne F m stT locT (.loop 0 0 mainMergeBody) env := fun F stT locT => by
            cases F with
            | zero => simp [exec, execOne]
            | succ f =>
              simp only [exec]
              rcases execOne (f + 1) m stT locT (.loop 0 0 mainMergeBody) env with
                ⟨_, _⟩ | ⟨_, _, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_⟩ | _
              · rfl
              all_goals rfl
          have hloop_eq : exec (max f_A f_rest + 1) m stA locA [.loop 0 0 mainMergeBody] env =
              exec (max f_A f_rest) m stC_A locA_out_A [.loop 0 0 mainMergeBody] env := by
            rw [hloop_single, hloop_single]
            conv_lhs => rw [execOne_loop_succ]
            simp only [hbody_mono, List.take_zero, List.nil_append, List.drop_zero]
            -- {locA_out_A with values := locA.values} = locA_out_A by rfl:
            -- locA_out_A = {locA with locals := ...}, so .values = locA.values definitionally
            rfl
          have heq : exec (max f_A f_rest + 2) m stA locA [.block 0 0 [.loop 0 0 mainMergeBody]] env =
              exec (max f_A f_rest + 1) m stC_A locA_out_A [.block 0 0 [.loop 0 0 mainMergeBody]] env := by
            rw [show max f_A f_rest + 2 = max f_A f_rest + 1 + 1 from rfl]
            conv_lhs => rw [exec_block_cons, hloop_eq]
            conv_rhs => rw [exec_block_cons]
            set discr := exec (max f_A f_rest) m stC_A locA_out_A [.loop 0 0 mainMergeBody] env
            rcases discr with ⟨r', s'⟩ | ⟨n, r', s'⟩ | ⟨r', vs⟩ | ⟨r', msg⟩ | ⟨msg⟩ | _
            · simp [exec, locA_out_A, locA_out_locs]
            · cases n with | zero => simp [exec, locA_out_A, locA_out_locs] | succ k => rfl
            all_goals rfl
          exact ⟨max f_A f_rest + 2, by rw [heq, hblock_mono]; exact hf_rest⟩
        · -- ── path B: left[i] > right[j]: copy right[j] to out[k], j++, k++ ──
          let mem1_B := stA.mem.write32 (out_ptr + 4 * UInt32.ofNat k) right_j
          let mem2_B := mem1_B.write32 (frame + 12) (UInt32.ofNat j + 1)
          let mem3_B := mem2_B.write32 (frame + 16) (UInt32.ofNat k + 1)
          let stC_B : Store Unit := { stA with mem := mem3_B }
          -- Result locals: localSet 7(→local[1]) 8(→local[2]) 9(→local[3])
          --                       10(→local[4]) 12(→local[6]) 13(→local[7])
          let locB_out_locs :=
            locA.locals.set 1 (.i32 (UInt32.ofNat i)) |>.set 2 (.i32 left_i)
              |>.set 3 (.i32 (UInt32.ofNat j)) |>.set 4 (.i32 (UInt32.ofNat j))
              |>.set 6 (.i32 right_j) |>.set 7 (.i32 (UInt32.ofNat k))
          let locB_out_B : Locals := { locA with locals := locB_out_locs }
          -- exec trace (staged through 14 nested blocks)
          have h_body_B : ∃ f_B,
              exec f_B m stA locA mainMergeBody env = .Break 0 stC_B locB_out_B := by
            refine ⟨15, ?_⟩
            -- ── body let-bindings (same definitions as Path A) ──
            let body14 : Program := [
              .localGet 7, .localGet 1, .ltU, .const (1:UInt32), .and, .eqz, .br_if 0,
              .localGet 0, .localGet 7, .const (2:UInt32), .shl, .add,
              .load32 (0:UInt32), .localSet 8,
              .localGet 6, .load32 (12:UInt32), .localSet 9,
              .localGet 9, .localGet 3, .ltU, .const (1:UInt32), .and, .br_if 1, .br 2]
            let body13 : Program := [.block 0 0 body14,
              .localGet 7, .localGet 1, .const (1048712:UInt32), .call 87, .unreachable]
            let body12 : Program := [.block 0 0 body13,
              .localGet 8, .localGet 2, .localGet 9, .const (2:UInt32), .shl, .add,
              .load32 (0:UInt32), .leU, .const (1:UInt32), .and, .br_if 2, .br 1]
            let body11 : Program := [.block 0 0 body12,
              .localGet 9, .localGet 3, .const (1048728:UInt32), .call 87, .unreachable]
            let body10 : Program := [.block 0 0 body11,
              .localGet 6, .load32 (12:UInt32), .localSet 10,
              .localGet 10, .localGet 3, .ltU, .const (1:UInt32), .and, .br_if 1, .br 2]
            let body9 : Program := [.block 0 0 body10,
              .localGet 6, .load32 (8:UInt32), .localSet 11,
              .localGet 11, .localGet 1, .ltU, .const (1:UInt32), .and, .br_if 4, .br 5]
            let body8 : Program := [.block 0 0 body9,
              .localGet 2, .localGet 10, .const (2:UInt32), .shl, .add,
              .load32 (0:UInt32), .localSet 12,
              .localGet 6, .load32 (16:UInt32), .localSet 13,
              .localGet 13, .localGet 5, .ltU, .const (1:UInt32), .and, .br_if 1, .br 2]
            let body7 : Program := [.block 0 0 body8,
              .localGet 10, .localGet 3, .const (1048744:UInt32), .call 87, .unreachable]
            let body6 : Program := [.block 0 0 body7,
              .localGet 4, .localGet 13, .const (2:UInt32), .shl, .add,
              .localGet 12, .store32 (0:UInt32),
              .localGet 6, .localGet 6, .load32 (12:UInt32),
              .const (1:UInt32), .add, .store32 (12:UInt32), .br 5]
            let body5 : Program := [.block 0 0 body6,
              .localGet 13, .localGet 5, .const (1048760:UInt32), .call 87, .unreachable]
            let body4 : Program := [.block 0 0 body5,
              .localGet 0, .localGet 11, .const (2:UInt32), .shl, .add,
              .load32 (0:UInt32), .localSet 14,
              .localGet 6, .load32 (16:UInt32), .localSet 15,
              .localGet 15, .localGet 5, .ltU, .const (1:UInt32), .and, .br_if 1, .br 2]
            let body3 : Program := [.block 0 0 body4,
              .localGet 11, .localGet 1, .const (1048776:UInt32), .call 87, .unreachable]
            let body2 : Program := [.block 0 0 body3,
              .localGet 4, .localGet 15, .const (2:UInt32), .shl, .add,
              .localGet 14, .store32 (0:UInt32),
              .localGet 6, .localGet 6, .load32 (8:UInt32),
              .const (1:UInt32), .add, .store32 (8:UInt32), .br 1]
            let body1 : Program := [.block 0 0 body2,
              .localGet 15, .localGet 5, .const (1048792:UInt32), .call 87, .unreachable]
            -- ── intermediate Locals states ──
            let locA_7 : Locals :=
              { locA with locals := locA.locals.set 1 (.i32 (UInt32.ofNat i)) }
            let locA_89_locs :=
              locA.locals.set 1 (.i32 (UInt32.ofNat i)) |>.set 2 (.i32 left_i)
                |>.set 3 (.i32 (UInt32.ofNat j))
            let locA_89 : Locals := { locA with locals := locA_89_locs }
            -- Path B: after body10 localSet 10: local[4] = j
            let locA_10_B : Locals :=
              { locA with locals := locA_89_locs.set 4 (.i32 (UInt32.ofNat j)) }
            -- Path B: after body8 localSet 12,13: local[6]=right_j, local[7]=k
            let locA_1213_B_locs :=
              locA_89_locs.set 4 (.i32 (UInt32.ofNat j))
                |>.set 6 (.i32 right_j) |>.set 7 (.i32 (UInt32.ofNat k))
            let locA_1213_B : Locals := { locA with locals := locA_1213_B_locs }
            -- store after B6: out[k]=right_j written, frame+12=j+1 written
            let stA_m2_B : Store Unit := { stA with mem := mem2_B }
            -- ── auxiliary lemmas ──
            have hi_lt_u32 : UInt32.ofNat i < n_left := by
              rw [UInt32.lt_iff_toNat_lt_toNat, UInt32.toNat_ofNat']
              have := n_left.toNat_lt; omega
            have hj_lt_u32 : UInt32.ofNat j < n_right := by
              rw [UInt32.lt_iff_toNat_lt_toNat, UInt32.toNat_ofNat']
              have := n_right.toNat_lt; omega
            have hk_lt_u32 : UInt32.ofNat k < n_out := by
              rw [UInt32.lt_iff_toNat_lt_toNat, UInt32.toNat_ofNat']
              have := n_out.toNat_lt; omega
            have hbnd_out_k : ¬((out_ptr + 4 * UInt32.ofNat k).toNat + 4 > stA.mem.pages * 65536) := by
              rw [hout_k_toNat]; omega
            have hbnd_fr8 : ¬((frame + 8).toNat + 4 > stA.mem.pages * 65536) := by
              rw [hft8]; omega
            have hbnd_fr12 : ¬((frame + 12).toNat + 4 > stA.mem.pages * 65536) := by
              rw [hft12]; omega
            have hbnd_fr16 : ¬((frame + 16).toNat + 4 > stA.mem.pages * 65536) := by
              rw [hft16]; omega
            have hbnd_left_i : ¬((left_ptr + 4 * UInt32.ofNat i).toNat + 4 > stA.mem.pages * 65536) := by
              rw [toNat_wordAddr left_ptr n_left.toNat i hlt_i (by linarith)]; omega
            have hbnd_right_j : ¬((right_ptr + 4 * UInt32.ofNat j).toNat + 4 > stA.mem.pages * 65536) := by
              rw [toNat_wordAddr right_ptr n_right.toNat j hlt_j (by linarith)]; omega
            have hmem1_B_fr12 : mem1_B.read32 (frame + 12) = UInt32.ofNat j := by
              simp only [mem1_B,
                Mem.read32_write32_of_disjoint _ (out_ptr + 4 * UInt32.ofNat k) (frame + 12) _
                  (by rw [hout_k_toNat, hft12]; rcases hframe_out_disj with h | h <;> omega)]
              exact hj_m
            have hmem2_B_fr16 : mem2_B.read32 (frame + 16) = UInt32.ofNat k := by
              simp only [mem2_B,
                Mem.read32_write32_of_disjoint _ (frame + 12) (frame + 16) _
                  (by left; rw [hft12, hft16])]
              simp only [mem1_B,
                Mem.read32_write32_of_disjoint _ (out_ptr + 4 * UInt32.ofNat k) (frame + 16) _
                  (by rw [hout_k_toNat, hft16]; rcases hframe_out_disj with h | h <;> omega)]
              exact hk_m
            -- ── exec chain through 14 blocks ──
            -- body14: same as Path A (loads left_i→local8, j→local9; br_if 1 fires) → Break 1
            have h_B14_B : exec 1 m stA locA_7 body14 env = .Break 1 stA locA_89 := by
              have hgv7_7 : ∀ vs, ({locA_7 with values := vs} : Locals).get 7 = locA_7.get 7 := fun _ => rfl
              have hgv1_7 : ∀ vs, ({locA_7 with values := vs} : Locals).get 1 = locA_7.get 1 := fun _ => rfl
              have hgv0_7 : ∀ vs, ({locA_7 with values := vs} : Locals).get 0 = locA_7.get 0 := fun _ => rfl
              have hgv6_7 : ∀ vs, ({locA_7 with values := vs} : Locals).get 6 = locA_7.get 6 := fun _ => rfl
              have hgv3_7 : ∀ vs, ({locA_7 with values := vs} : Locals).get 3 = locA_7.get 3 := fun _ => rfl
              have hlp_7 : locA_7.params.length = 6  := hlparams
              have hll_7 : locA_7.locals.length = 16 := by simp [locA_7, List.length_set, hllocals]
              have hg7_7 : locA_7.get 7 = some (.i32 (UInt32.ofNat i)) := by
                simp only [Locals.get, hlp_7, hll_7, List.length_set,
                           show ¬(7 < 6) from by omega, show (7 : Nat) < 6 + 16 from by omega,
                           show (7 : Nat) - 6 = 1 from by omega]
                change (locA.locals.set 1 (.i32 (UInt32.ofNat i)))[1]? = _
                exact List.getElem?_set_self (by rw [hllocals]; norm_num)
              have hg1_7 : locA_7.get 1 = some (.i32 n_left) := by
                simp only [Locals.get, locA_7, hlparams, show (1 : Nat) < 6 from by omega] at h1 ⊢
                exact h1
              have hg0_7 : locA_7.get 0 = some (.i32 left_ptr) := by
                simp only [Locals.get, locA_7, hlparams, show (0 : Nat) < 6 from by omega] at h0 ⊢
                exact h0
              have hg6_7 : locA_7.get 6 = some (.i32 frame) := by
                have h : locA_7.get 6 = locA.get 6 := by
                  simp [locA_7, Locals.get, hlparams, hllocals, List.length_set, List.getElem?_set]
                rw [h]; exact hf6
              have hg3_7 : locA_7.get 3 = some (.i32 n_right) := by
                simp only [Locals.get, locA_7, hlparams, show (3 : Nat) < 6 from by omega] at h3 ⊢
                exact h3
              have hg6_8_raw : ∀ vs,
                  (Locals.mk locA_7.params (locA_7.locals.set 2 (.i32 left_i)) vs).get 6
                  = some (.i32 frame) := by
                intro vs
                have h : (Locals.mk locA_7.params (locA_7.locals.set 2 (.i32 left_i)) vs).get 6
                    = locA.get 6 := by
                  simp [locA_7, Locals.get, hlparams, hllocals, List.length_set, List.getElem?_set]
                rw [h]; exact hf6
              have hg9_89_raw : ∀ vs,
                  (Locals.mk locA_7.params
                    ((locA_7.locals.set 2 (.i32 left_i)).set 3 (.i32 (UInt32.ofNat j))) vs).get 9
                  = some (.i32 (UInt32.ofNat j)) := by
                intro vs
                simp only [Locals.get, hlp_7, hll_7, List.length_set,
                           show ¬(9 < 6) from by omega, show (9 : Nat) < 6 + 16 from by omega,
                           show (9 : Nat) - 6 = 3 from by omega]
                exact List.getElem?_set_self (by simp [List.length_set, hll_7])
              have hg3_89_raw : ∀ vs,
                  (Locals.mk locA_7.params
                    ((locA_7.locals.set 2 (.i32 left_i)).set 3 (.i32 (UInt32.ofNat j))) vs).get 3
                  = some (.i32 n_right) := by
                intro vs
                have h3_raw : locA.params[3]? = some (.i32 n_right) := by
                  have h := h3
                  simp only [Locals.get, hlparams, show (3 : Nat) < 6 from by omega] at h
                  exact h
                simp only [Locals.get, hlp_7, show (3 : Nat) < 6 from by omega]
                exact h3_raw
              have hshl_i : UInt32.ofNat i <<< ((2 : UInt32) % 32) = 4 * UInt32.ofNat i := by
                rw [show (2 : UInt32) % 32 = 2 from by decide]
                apply UInt32.toNat_inj.mp
                have hi_bnd : i < 2 ^ 30 := by have := n_left.toNat_lt; omega
                simp only [UInt32.toNat_mul, UInt32.toNat_ofNat',
                           show (4 : UInt32).toNat = 4 from rfl,
                           Nat.mod_eq_of_lt (show i < 4294967296 from by omega),
                           Nat.mod_eq_of_lt (show i * 4 < 4294967296 from by omega)]
                simp [UInt32.shiftLeft, Fin.shiftLeft, Nat.shiftLeft_eq]; omega
              have hshl_j_14 : UInt32.ofNat j <<< ((2 : UInt32) % 32) = 4 * UInt32.ofNat j := by
                rw [show (2 : UInt32) % 32 = 2 from by decide]
                apply UInt32.toNat_inj.mp
                have hj_bnd : j < 2 ^ 30 := by have := n_right.toNat_lt; omega
                simp only [UInt32.toNat_mul, UInt32.toNat_ofNat',
                           show (4 : UInt32).toNat = 4 from rfl,
                           Nat.mod_eq_of_lt (show j < 4294967296 from by omega),
                           Nat.mod_eq_of_lt (show j * 4 < 4294967296 from by omega)]
                simp [UInt32.shiftLeft, Fin.shiftLeft, Nat.shiftLeft_eq]; omega
              simp only [exec, execOne.eq_def, body14, Locals.set?,
                         hgv7_7, hgv1_7, hgv0_7, hgv6_7, hgv3_7,
                         hg7_7, hg1_7, hg0_7, hg6_7, hg3_7,
                         if_pos hi_lt_u32,
                         show (1 : UInt32) &&& 1 = 1 from by decide,
                         show (if (1 : UInt32) = 0 then (1 : UInt32) else 0) = 0 from by decide,
                         hshl_i,
                         if_neg (show ¬((4 * UInt32.ofNat i + left_ptr).toNat +
                                         UInt32.toNat (0 : UInt32) + 4 > stA.mem.pages * 65536) from by
                                   rw [show 4 * UInt32.ofNat i + left_ptr =
                                           left_ptr + 4 * UInt32.ofNat i from UInt32.add_comm _ _,
                                       show UInt32.toNat (0 : UInt32) = 0 from rfl]; omega),
                         show stA.mem.read32 (4 * UInt32.ofNat i + left_ptr + (0 : UInt32)) = left_i from by
                           rw [show 4 * UInt32.ofNat i + left_ptr + (0 : UInt32) =
                                   left_ptr + 4 * UInt32.ofNat i from by
                               rw [UInt32.add_comm (4 * UInt32.ofNat i) left_ptr, UInt32.add_zero]],
                         hlp_7, hll_7, List.length_set,
                         if_neg (show ¬(8 < 6) from by omega),
                         if_pos (show (8 : Nat) < 6 + 16 from by omega),
                         show (8 : Nat) - 6 = 2 from by omega,
                         hg6_8_raw,
                         if_neg (show ¬(frame.toNat + (12 : UInt32).toNat + 4 > stA.mem.pages * 65536)
                                   from by simp only [show (12 : UInt32).toNat = 12 from by decide]; omega),
                         show stA.mem.read32 (frame + (12 : UInt32)) = UInt32.ofNat j from hj_m,
                         if_neg (show ¬(9 < 6) from by omega),
                         if_pos (show (9 : Nat) < 6 + 16 from by omega),
                         show (9 : Nat) - 6 = 3 from by omega,
                         hg9_89_raw, hg3_89_raw,
                         if_pos hj_lt_u32,
                         show (1 : UInt32) &&& 1 = 1 from by decide,
                         show Locals.mk locA_7.params
                               ((locA_7.locals.set 2 (.i32 left_i)).set 3 (.i32 (UInt32.ofNat j)))
                               locA.values = locA_89 from rfl]
              rfl
            -- body13: Break(0+1) from body14 → Break 0
            have h_B13_B : exec 2 m stA locA_7 body13 env = .Break 0 stA locA_89 := by
              rw [show (2:Nat) = 1+1 from rfl, exec_block_cons, h_B14_B]
            -- body12: ¬hle (left_i > right_j): br_if 2 NOT taken, br 1 → Break 1
            have h_B12_B : exec 3 m stA locA_7 body12 env = .Break 1 stA locA_89 := by
              rw [show (3:Nat) = 2+1 from rfl, exec_block_cons, h_B13_B]
              simp only [List.take_zero, List.drop_zero, List.nil_append]
              have hll_89 : locA_89.locals.length = 16 := by
                simp [locA_89, locA_89_locs, List.length_set, hllocals]
              have hgv8_89 : ∀ vs, ({locA_89 with values := vs} : Locals).get 8 = locA_89.get 8 := fun _ => rfl
              have hgv2_89 : ∀ vs, ({locA_89 with values := vs} : Locals).get 2 = locA_89.get 2 := fun _ => rfl
              have hgv9_89 : ∀ vs, ({locA_89 with values := vs} : Locals).get 9 = locA_89.get 9 := fun _ => rfl
              have hg8_89 : locA_89.get 8 = some (.i32 left_i) := by
                simp only [Locals.get, locA_89, locA_89_locs, hlparams, hllocals, List.length_set,
                           show ¬(8 < 6) from by omega, show (8:Nat) < 6+16 from by omega,
                           show (8:Nat) - 6 = 2 from by omega]
                rw [List.getElem?_set_ne (show (3:Nat) ≠ 2 from by omega)]
                exact List.getElem?_set_self (by rw [List.length_set, hllocals]; norm_num)
              have hg2_89 : locA_89.get 2 = some (.i32 right_ptr) := by
                simp only [Locals.get, locA_89, hlparams, show (2:Nat) < 6 from by omega] at h2 ⊢
                exact h2
              have hg9_89 : locA_89.get 9 = some (.i32 (UInt32.ofNat j)) := by
                simp only [Locals.get, locA_89, locA_89_locs, hlparams, hllocals, List.length_set,
                           show ¬(9 < 6) from by omega, show (9:Nat) < 6+16 from by omega,
                           show (9:Nat) - 6 = 3 from by omega]
                exact List.getElem?_set_self (by rw [List.length_set, List.length_set, hllocals]; norm_num)
              have hshl_j : UInt32.ofNat j <<< ((2:UInt32) % 32) = 4 * UInt32.ofNat j := by
                rw [show (2:UInt32) % 32 = 2 from by decide]
                apply UInt32.toNat_inj.mp
                have hj_bnd : j < 2^30 := by have := n_right.toNat_lt; omega
                simp only [UInt32.toNat_mul, UInt32.toNat_ofNat',
                           show (4:UInt32).toNat = 4 from rfl,
                           Nat.mod_eq_of_lt (show j < 4294967296 from by omega),
                           Nat.mod_eq_of_lt (show j*4 < 4294967296 from by omega)]
                simp [UInt32.shiftLeft, Fin.shiftLeft, Nat.shiftLeft_eq]; omega
              simp only [exec, execOne.eq_def,
                         show ({locA_89 with values := locA_7.values} : Locals) = locA_89 from rfl,
                         hgv8_89, hgv2_89, hgv9_89,
                         hg8_89, hg2_89, hg9_89,
                         hshl_j,
                         if_neg (show ¬((4 * UInt32.ofNat j + right_ptr).toNat +
                                         UInt32.toNat (0:UInt32) + 4 > stA.mem.pages * 65536) from by
                                   rw [show 4 * UInt32.ofNat j + right_ptr =
                                               right_ptr + 4 * UInt32.ofNat j from UInt32.add_comm _ _,
                                       show UInt32.toNat (0:UInt32) = 0 from rfl]
                                   exact hbnd_right_j),
                         show stA.mem.read32 (4 * UInt32.ofNat j + right_ptr + (0:UInt32)) = right_j from by
                             rw [show 4 * UInt32.ofNat j + right_ptr + (0:UInt32) =
                                         right_ptr + 4 * UInt32.ofNat j from by
                                     rw [UInt32.add_comm (4 * UInt32.ofNat j) right_ptr, UInt32.add_zero]],
                         if_neg hle,
                         show (1:UInt32) &&& 0 = 0 from by decide,
                         show ({locA_89 with values := locA.values} : Locals) = locA_89 from rfl]
            -- body11: Break(0+1) from body12 → Break 0
            have h_B11_B : exec 4 m stA locA_7 body11 env = .Break 0 stA locA_89 := by
              rw [show (4:Nat) = 3+1 from rfl, exec_block_cons, h_B12_B]
            -- body10: Break 0 → B10_right_cont: localGet6, load32_12(j)→localSet10, j<n_right br_if1 → Break 1
            have h_B10_B : exec 5 m stA locA_7 body10 env = .Break 1 stA locA_10_B := by
              rw [show (5:Nat) = 4+1 from rfl, exec_block_cons, h_B11_B]
              simp only [List.take_zero, List.drop_zero, List.nil_append]
              have hlp_89 : locA_89.params.length = 6 := hlparams
              have hll_89 : locA_89.locals.length = 16 := by
                simp [locA_89, locA_89_locs, List.length_set, hllocals]
              have hgv6_89 : ∀ vs, ({locA_89 with values := vs} : Locals).get 6 = locA_89.get 6 := fun _ => rfl
              have hg6_89 : locA_89.get 6 = some (.i32 frame) := by
                simp only [Locals.get, locA_89, locA_89_locs, hlparams, hllocals, List.length_set,
                           show ¬(6 < 6) from by omega, show (6:Nat) < 6+16 from by omega,
                           show (6:Nat) - 6 = 0 from by omega]
                rw [List.getElem?_set_ne (show (3:Nat) ≠ 0 from by omega)]
                rw [List.getElem?_set_ne (show (2:Nat) ≠ 0 from by omega)]
                rw [List.getElem?_set_ne (show (1:Nat) ≠ 0 from by omega)]
                simpa [Locals.get, hlparams, hllocals, show ¬(6 < 6) from by omega] using hf6
              have hgv10_10B : ∀ vs, ({locA_10_B with values := vs} : Locals).get 10 = locA_10_B.get 10 := fun _ => rfl
              have hgv3_10B  : ∀ vs, ({locA_10_B with values := vs} : Locals).get 3  = locA_10_B.get 3  := fun _ => rfl
              have hg10_10B : locA_10_B.get 10 = some (.i32 (UInt32.ofNat j)) := by
                simp only [Locals.get, locA_10_B, locA_89_locs, hlparams, hllocals, List.length_set,
                           show ¬(10 < 6) from by omega, show (10:Nat) < 6+16 from by omega,
                           show (10:Nat) - 6 = 4 from by omega]
                exact List.getElem?_set_self
                  (by rw [List.length_set, List.length_set, List.length_set, hllocals]; norm_num)
              have hg3_10B : locA_10_B.get 3 = some (.i32 n_right) := by
                simp only [Locals.get, locA_10_B, hlparams, show (3:Nat) < 6 from by omega] at h3 ⊢
                exact h3
              simp only [exec, execOne.eq_def,
                         show ({locA_89 with values := locA_7.values} : Locals) = locA_89 from rfl,
                         hgv6_89, hg6_89,
                         if_neg (show ¬(frame.toNat + UInt32.toNat (12:UInt32) + 4 > stA.mem.pages * 65536) from by
                                   simp only [show (12:UInt32).toNat = 12 from by decide]; omega),
                         show stA.mem.read32 (frame + (12:UInt32)) = UInt32.ofNat j from hj_m,
                         Locals.set?,
                         hlp_89, hll_89, List.length_set,
                         if_neg (show ¬(10 < 6) from by omega),
                         if_pos (show (10:Nat) < 6+16 from by omega),
                         show (10:Nat) - 6 = 4 from by omega,
                         show Locals.mk locA_89.params (locA_89.locals.set 4 (.i32 (UInt32.ofNat j)))
                               locA_89.values = locA_10_B from rfl,
                         hgv10_10B, hg10_10B, hgv3_10B, hg3_10B,
                         if_pos hj_lt_u32,
                         show (1:UInt32) &&& 1 = 1 from by decide,
                         show ({locA_10_B with values := locA_10_B.values} : Locals) = locA_10_B from rfl]
              rfl
            -- body9: Break(0+1) from body10 → Break 0
            have h_B9_B : exec 6 m stA locA_7 body9 env = .Break 0 stA locA_10_B := by
              rw [show (6:Nat) = 5+1 from rfl, exec_block_cons, h_B10_B]
            -- body8: Break 0 → B8_right_load: load right[j]→local12, k→local13, k<n_out br_if1 → Break 1
            have h_B8_B : exec 7 m stA locA_7 body8 env = .Break 1 stA locA_1213_B := by
              rw [show (7:Nat) = 6+1 from rfl, exec_block_cons, h_B9_B]
              simp only [List.take_zero, List.drop_zero, List.nil_append]
              have hlp_10B : locA_10_B.params.length = 6 := hlparams
              have hll_10B : locA_10_B.locals.length = 16 := by
                simp [locA_10_B, locA_89_locs, List.length_set, hllocals]
              have hgv2_10B  : ∀ vs, ({locA_10_B with values := vs} : Locals).get 2  = locA_10_B.get 2  := fun _ => rfl
              have hgv10_10B : ∀ vs, ({locA_10_B with values := vs} : Locals).get 10 = locA_10_B.get 10 := fun _ => rfl
              have hg2_10B : locA_10_B.get 2 = some (.i32 right_ptr) := by
                simp only [Locals.get, locA_10_B, hlparams, show (2:Nat) < 6 from by omega] at h2 ⊢
                exact h2
              have hg10_10B : locA_10_B.get 10 = some (.i32 (UInt32.ofNat j)) := by
                simp only [Locals.get, locA_10_B, locA_89_locs, hlparams, hllocals, List.length_set,
                           show ¬(10 < 6) from by omega, show (10:Nat) < 6+16 from by omega,
                           show (10:Nat) - 6 = 4 from by omega]
                exact List.getElem?_set_self
                  (by rw [List.length_set, List.length_set, List.length_set, hllocals]; norm_num)
              have hshl_j : UInt32.ofNat j <<< ((2:UInt32) % 32) = 4 * UInt32.ofNat j := by
                rw [show (2:UInt32) % 32 = 2 from by decide]
                apply UInt32.toNat_inj.mp
                have hj_bnd : j < 2^30 := by have := n_right.toNat_lt; omega
                simp only [UInt32.toNat_mul, UInt32.toNat_ofNat',
                           show (4:UInt32).toNat = 4 from rfl,
                           Nat.mod_eq_of_lt (show j < 4294967296 from by omega),
                           Nat.mod_eq_of_lt (show j*4 < 4294967296 from by omega)]
                simp [UInt32.shiftLeft, Fin.shiftLeft, Nat.shiftLeft_eq]; omega
              have hg6_12B_raw : ∀ vs,
                  (Locals.mk locA_10_B.params (locA_10_B.locals.set 6 (.i32 right_j)) vs).get 6
                  = some (.i32 frame) := by
                intro vs
                have h : (Locals.mk locA_10_B.params (locA_10_B.locals.set 6 (.i32 right_j)) vs).get 6
                    = locA.get 6 := by
                  simp [locA_10_B, locA_89_locs, Locals.get, hlparams, hllocals,
                        List.length_set, List.getElem?_set]
                rw [h]; exact hf6
              have hg13_1213_raw : ∀ vs,
                  (Locals.mk locA_10_B.params
                    ((locA_10_B.locals.set 6 (.i32 right_j)).set 7 (.i32 (UInt32.ofNat k))) vs).get 13
                  = some (.i32 (UInt32.ofNat k)) := by
                intro vs
                simp only [Locals.get, hlp_10B, hll_10B, List.length_set,
                           show ¬(13 < 6) from by omega, show (13:Nat) < 6+16 from by omega,
                           show (13:Nat) - 6 = 7 from by omega]
                exact List.getElem?_set_self (by simp [List.length_set, hll_10B])
              have hg5_1213_raw : ∀ vs,
                  (Locals.mk locA_10_B.params
                    ((locA_10_B.locals.set 6 (.i32 right_j)).set 7 (.i32 (UInt32.ofNat k))) vs).get 5
                  = some (.i32 n_out) := by
                intro vs
                have h5_raw : locA.params[5]? = some (.i32 n_out) := by
                  have h := h5
                  simp only [Locals.get, hlparams, show (5:Nat) < 6 from by omega] at h
                  exact h
                simp only [Locals.get, hlp_10B, show (5:Nat) < 6 from by omega]
                exact h5_raw
              simp only [exec, execOne.eq_def,
                         show ({locA_10_B with values := locA_7.values} : Locals) = locA_10_B from rfl,
                         hgv2_10B, hg2_10B, hgv10_10B, hg10_10B,
                         hshl_j,
                         if_neg (show ¬((4 * UInt32.ofNat j + right_ptr).toNat +
                                         UInt32.toNat (0:UInt32) + 4 > stA.mem.pages * 65536) from by
                                   rw [show 4 * UInt32.ofNat j + right_ptr =
                                               right_ptr + 4 * UInt32.ofNat j from UInt32.add_comm _ _,
                                       show UInt32.toNat (0:UInt32) = 0 from rfl]
                                   exact hbnd_right_j),
                         show stA.mem.read32 (4 * UInt32.ofNat j + right_ptr + (0:UInt32)) = right_j from by
                             rw [show 4 * UInt32.ofNat j + right_ptr + (0:UInt32) =
                                         right_ptr + 4 * UInt32.ofNat j from by
                                     rw [UInt32.add_comm (4 * UInt32.ofNat j) right_ptr, UInt32.add_zero]],
                         Locals.set?,
                         hlp_10B, hll_10B, List.length_set,
                         if_neg (show ¬(12 < 6) from by omega),
                         if_pos (show (12:Nat) < 6+16 from by omega),
                         show (12:Nat) - 6 = 6 from by omega,
                         hg6_12B_raw,
                         if_neg (show ¬(frame.toNat + UInt32.toNat (16:UInt32) + 4 > stA.mem.pages * 65536) from by
                                   simp only [show (16:UInt32).toNat = 16 from by decide]; omega),
                         show stA.mem.read32 (frame + (16:UInt32)) = UInt32.ofNat k from hk_m,
                         if_neg (show ¬(13 < 6) from by omega),
                         if_pos (show (13:Nat) < 6+16 from by omega),
                         show (13:Nat) - 6 = 7 from by omega,
                         hg13_1213_raw, hg5_1213_raw,
                         if_pos hk_lt_u32,
                         show (1:UInt32) &&& 1 = 1 from by decide,
                         show Locals.mk locA_10_B.params
                               ((locA_10_B.locals.set 6 (.i32 right_j)).set 7 (.i32 (UInt32.ofNat k)))
                               locA.values = locA_1213_B from rfl]
              rfl
            -- body7: Break(0+1) from body8 → Break 0
            have h_B7_B : exec 8 m stA locA_7 body7 env = .Break 0 stA locA_1213_B := by
              rw [show (8:Nat) = 7+1 from rfl, exec_block_cons, h_B8_B]
            -- body6: Break 0 → B6_right_store: write out[k]=right_j, frame+12=j+1, br 5 → Break 5
            have h_B6_B : exec 9 m stA locA_7 body6 env = .Break 5 stA_m2_B locA_1213_B := by
              rw [show (9:Nat) = 8+1 from rfl, exec_block_cons, h_B7_B]
              simp only [List.take_zero, List.drop_zero, List.nil_append]
              have hgv4_1213  : ∀ vs, ({locA_1213_B with values := vs} : Locals).get 4  = locA_1213_B.get 4  := fun _ => rfl
              have hgv13_1213 : ∀ vs, ({locA_1213_B with values := vs} : Locals).get 13 = locA_1213_B.get 13 := fun _ => rfl
              have hgv12_1213 : ∀ vs, ({locA_1213_B with values := vs} : Locals).get 12 = locA_1213_B.get 12 := fun _ => rfl
              have hgv6_1213  : ∀ vs, ({locA_1213_B with values := vs} : Locals).get 6  = locA_1213_B.get 6  := fun _ => rfl
              have hg4_1213 : locA_1213_B.get 4 = some (.i32 out_ptr) := by
                simp only [Locals.get, locA_1213_B, hlparams, show (4:Nat) < 6 from by omega] at h4 ⊢
                exact h4
              have hg13_1213 : locA_1213_B.get 13 = some (.i32 (UInt32.ofNat k)) := by
                simp only [Locals.get, locA_1213_B, locA_1213_B_locs, locA_89_locs,
                           hlparams, hllocals, List.length_set,
                           show ¬(13 < 6) from by omega, show (13:Nat) < 6+16 from by omega,
                           show (13:Nat) - 6 = 7 from by omega]
                exact List.getElem?_set_self
                  (by rw [List.length_set, List.length_set, List.length_set,
                           List.length_set, List.length_set, hllocals]; norm_num)
              have hg12_1213 : locA_1213_B.get 12 = some (.i32 right_j) := by
                simp only [Locals.get, locA_1213_B, locA_1213_B_locs, locA_89_locs,
                           hlparams, hllocals, List.length_set,
                           show ¬(12 < 6) from by omega, show (12:Nat) < 6+16 from by omega,
                           show (12:Nat) - 6 = 6 from by omega]
                rw [List.getElem?_set_ne (show (7:Nat) ≠ 6 from by omega)]
                exact List.getElem?_set_self
                  (by rw [List.length_set, List.length_set, List.length_set, List.length_set, hllocals]; norm_num)
              have hg6_1213 : locA_1213_B.get 6 = some (.i32 frame) := by
                simp only [Locals.get, locA_1213_B, locA_1213_B_locs, locA_89_locs,
                           hlparams, hllocals, List.length_set,
                           show ¬(6 < 6) from by omega, show (6:Nat) < 6+16 from by omega,
                           show (6:Nat) - 6 = 0 from by omega,
                           List.getElem?_set, show (7:Nat) ≠ 0 from by omega,
                           show (6:Nat) ≠ 0 from by omega, show (4:Nat) ≠ 0 from by omega,
                           show (3:Nat) ≠ 0 from by omega, show (2:Nat) ≠ 0 from by omega,
                           show (1:Nat) ≠ 0 from by omega, if_false]
                simpa [Locals.get, hlparams, hllocals, show ¬(6 < 6) from by omega] using hf6
              have hshl_k : UInt32.ofNat k <<< ((2:UInt32) % 32) = 4 * UInt32.ofNat k := by
                rw [show (2:UInt32) % 32 = 2 from by decide]
                apply UInt32.toNat_inj.mp
                have hk_bnd : k < 2^30 := by have := n_out.toNat_lt; omega
                simp only [UInt32.toNat_mul, UInt32.toNat_ofNat',
                           show (4:UInt32).toNat = 4 from rfl,
                           Nat.mod_eq_of_lt (show k < 4294967296 from by omega),
                           Nat.mod_eq_of_lt (show k * 4 < 4294967296 from by omega)]
                simp [UInt32.shiftLeft, Fin.shiftLeft, Nat.shiftLeft_eq]; omega
              simp only [exec, execOne.eq_def,
                         show ({locA_1213_B with values := locA_7.values} : Locals) = locA_1213_B from rfl,
                         hgv4_1213, hg4_1213, hgv13_1213, hg13_1213,
                         hshl_k,
                         if_neg (show ¬((4 * UInt32.ofNat k + out_ptr).toNat +
                                         UInt32.toNat (0:UInt32) + 4 > stA.mem.pages * 65536) from by
                                   rw [show 4 * UInt32.ofNat k + out_ptr =
                                               out_ptr + 4 * UInt32.ofNat k from UInt32.add_comm _ _,
                                       show UInt32.toNat (0:UInt32) = 0 from rfl]; omega),
                         show stA.mem.write32 (4 * UInt32.ofNat k + out_ptr + (0:UInt32)) right_j = mem1_B from by
                             rw [show 4 * UInt32.ofNat k + out_ptr + (0:UInt32) =
                                         out_ptr + 4 * UInt32.ofNat k from by
                                     rw [UInt32.add_comm (4 * UInt32.ofNat k) out_ptr, UInt32.add_zero]],
                         hgv12_1213, hg12_1213,
                         hgv6_1213, hg6_1213,
                         if_neg (show ¬(frame.toNat + UInt32.toNat (12:UInt32) + 4 >
                                         {stA with mem := mem1_B}.mem.pages * 65536) from by
                                   rw [show ({stA with mem := mem1_B} : Store Unit).mem.pages =
                                         stA.mem.pages from rfl,
                                       show UInt32.toNat (12:UInt32) = 12 from by decide, hft12.symm]
                                   exact hbnd_fr12),
                         show ({stA with mem := mem1_B} : Store Unit).mem.read32 (frame + (12:UInt32)) =
                               UInt32.ofNat j from hmem1_B_fr12,
                         show (1:UInt32) + UInt32.ofNat j = UInt32.ofNat j + 1 from UInt32.add_comm _ _,
                         if_neg (show ¬(frame.toNat + UInt32.toNat (12:UInt32) + 4 >
                                         {stA with mem := mem1_B}.mem.pages * 65536) from by
                                   rw [show ({stA with mem := mem1_B} : Store Unit).mem.pages =
                                         stA.mem.pages from rfl,
                                       show UInt32.toNat (12:UInt32) = 12 from by decide, hft12.symm]
                                   exact hbnd_fr12),
                         show ({stA with mem := mem1_B} : Store Unit).mem.write32
                               (frame + (12:UInt32)) (UInt32.ofNat j + 1) = mem2_B from rfl,
                         show ({stA with mem := mem2_B} : Store Unit) = stA_m2_B from rfl,
                         show ({locA_1213_B with values := locA_1213_B.values} : Locals) = locA_1213_B from rfl]
            -- body5: Break(4+1) → Break 4
            have h_B5_B : exec 10 m stA locA_7 body5 env = .Break 4 stA_m2_B locA_1213_B := by
              rw [show (10:Nat) = 9+1 from rfl, exec_block_cons, h_B6_B]
            -- body4: Break(3+1) → Break 3
            have h_B4_B : exec 11 m stA locA_7 body4 env = .Break 3 stA_m2_B locA_1213_B := by
              rw [show (11:Nat) = 10+1 from rfl, exec_block_cons, h_B5_B]
            -- body3: Break(2+1) → Break 2
            have h_B3_B : exec 12 m stA locA_7 body3 env = .Break 2 stA_m2_B locA_1213_B := by
              rw [show (12:Nat) = 11+1 from rfl, exec_block_cons, h_B4_B]
            -- body2: Break(1+1) → Break 1
            have h_B2_B : exec 13 m stA locA_7 body2 env = .Break 1 stA_m2_B locA_1213_B := by
              rw [show (13:Nat) = 12+1 from rfl, exec_block_cons, h_B3_B]
            -- body1: Break(0+1) → Break 0
            have h_B1_B : exec 14 m stA locA_7 body1 env = .Break 0 stA_m2_B locA_1213_B := by
              rw [show (14:Nat) = 13+1 from rfl, exec_block_cons, h_B2_B]
            -- ── assemble: prefix → outer block (h_B1_B) → suffix ──
            have h_pre_B : exec 15 m stA locA mainMergeBody env =
                exec 15 m stA locA_7
                  (.block 0 0 body1 :: [.localGet 6, .localGet 6, .load32 (16:UInt32),
                    .const (1:UInt32), .add, .store32 (16:UInt32), .br 0]) env := by
              have h_prefix_aux : ∀ cont : Program,
                  exec 15 m stA locA
                    ([.localGet 6, .load32 (8:UInt32), .localGet 1, .ltU,
                      .const (1:UInt32), .and, .eqz, .br_if 1,
                      .localGet 6, .load32 (12:UInt32), .localGet 3, .ltU,
                      .const (1:UInt32), .and, .eqz, .br_if 1,
                      .localGet 6, .load32 (8:UInt32), .localSet 7] ++ cont) env
                    = exec 15 m stA locA_7 cont env := by
                intro cont
                have hgv6_pre : ∀ vs, ({locA with values := vs} : Locals).get 6 = locA.get 6 := fun _ => rfl
                have hgv1_pre : ∀ vs, ({locA with values := vs} : Locals).get 1 = locA.get 1 := fun _ => rfl
                have hgv3_pre : ∀ vs, ({locA with values := vs} : Locals).get 3 = locA.get 3 := fun _ => rfl
                rw [show [.localGet 6, .load32 (8:UInt32), .localGet 1, .ltU,
                          .const (1:UInt32), .and, .eqz, .br_if 1,
                          .localGet 6, .load32 (12:UInt32), .localGet 3, .ltU,
                          .const (1:UInt32), .and, .eqz, .br_if 1,
                          .localGet 6, .load32 (8:UInt32), .localSet 7] ++ cont =
                         .localGet 6 :: .load32 (8:UInt32) :: .localGet 1 :: .ltU ::
                         .const (1:UInt32) :: .and :: .eqz :: .br_if 1 ::
                         .localGet 6 :: .load32 (12:UInt32) :: .localGet 3 :: .ltU ::
                         .const (1:UInt32) :: .and :: .eqz :: .br_if 1 ::
                         .localGet 6 :: .load32 (8:UInt32) :: .localSet 7 :: cont from rfl]
                simp only
                  [exec, execOne.eq_def, Locals.set?,
                   hgv6_pre, hgv1_pre, hgv3_pre,
                   hf6, h1, h3,
                   hi_m, hj_m,
                   if_neg (show ¬(frame.toNat + UInt32.toNat (8 : UInt32) + 4 > stA.mem.pages * 65536) from by
                     rw [show UInt32.toNat (8 : UInt32) = 8 from by decide, ← hft8]; exact hbnd_fr8),
                   if_pos hi_lt_u32,
                   show (1 : UInt32) &&& 1 = 1 from by decide,
                   show (if (1 : UInt32) = 0 then (1 : UInt32) else 0) = 0 from by decide,
                   if_neg (show ¬(frame.toNat + UInt32.toNat (12 : UInt32) + 4 > stA.mem.pages * 65536) from by
                     rw [show UInt32.toNat (12 : UInt32) = 12 from by decide, ← hft12]; exact hbnd_fr12),
                   if_pos hj_lt_u32,
                   hlparams, hllocals,
                   if_neg (show ¬(7 < 6) from by omega),
                   if_pos (show (7 : Nat) < 6 + 16 from by omega),
                   show (7 : Nat) - 6 = 1 from by omega]
                rfl
              exact h_prefix_aux _
            rw [h_pre_B, show (15:Nat) = 14+1 from rfl, exec_block_cons, h_B1_B]
            simp only [List.take_zero, List.drop_zero, List.nil_append]
            -- suffix: localGet 6 ×2, load32 16 (=k), const 1, add (=k+1), store32 16 (→mem3_B), br 0
            have hgv6_suf_B : ∀ vs, ({locA_1213_B with values := vs} : Locals).get 6 = locA_1213_B.get 6 := fun _ => rfl
            have hg6_suf_B : locA_1213_B.get 6 = some (.i32 frame) := by
              simp only [Locals.get, locA_1213_B, locA_1213_B_locs, locA_89_locs,
                         hlparams, hllocals, List.length_set,
                         show ¬(6 < 6) from by omega, show (6:Nat) < 6+16 from by omega,
                         show (6:Nat) - 6 = 0 from by omega,
                         List.getElem?_set, show (7:Nat) ≠ 0 from by omega,
                         show (6:Nat) ≠ 0 from by omega, show (4:Nat) ≠ 0 from by omega,
                         show (3:Nat) ≠ 0 from by omega, show (2:Nat) ≠ 0 from by omega,
                         show (1:Nat) ≠ 0 from by omega, if_false]
              simpa [Locals.get, hlparams, hllocals, show ¬(6 < 6) from by omega] using hf6
            simp only [exec, execOne.eq_def,
                       hgv6_suf_B, hg6_suf_B,
                       if_neg (show ¬(frame.toNat + UInt32.toNat (16 : UInt32) + 4 > stA_m2_B.mem.pages * 65536) from by
                         rw [show stA_m2_B.mem.pages = stA.mem.pages from rfl,
                             show UInt32.toNat (16 : UInt32) = 16 from by decide, ← hft16]
                         exact hbnd_fr16),
                       show stA_m2_B.mem.read32 (frame + (16 : UInt32)) = UInt32.ofNat k from hmem2_B_fr16,
                       show (1 : UInt32) + UInt32.ofNat k = UInt32.ofNat (k + 1) from by
                         rw [UInt32.add_comm]; exact hk_add1,
                       show stA_m2_B.mem.write32 (frame + (16 : UInt32)) (UInt32.ofNat (k + 1)) = mem3_B from by
                         simp only [stA_m2_B, mem3_B]; rw [← hk_add1]]
            rfl
          obtain ⟨f_B, h_body_B⟩ := h_body_B
          -- memory reads after path B writes
          have hread8_B : stC_B.mem.read32 (frame + 8) = UInt32.ofNat i := by
            simp only [stC_B, mem3_B, mem2_B, mem1_B]
            rw [Mem.read32_write32_of_disjoint _ (frame + 16) (frame + 8) _
                  (by right; rw [hft16, hft8]; omega),
                Mem.read32_write32_of_disjoint _ (frame + 12) (frame + 8) _
                  (by right; rw [hft12, hft8]),
                Mem.read32_write32_of_disjoint _ (out_ptr + 4 * UInt32.ofNat k) (frame + 8) _
                  (by rw [hout_k_toNat, hft8];
                      rcases hframe_out_disj with h | h <;> omega),
                hi_m]
          have hread12_B : stC_B.mem.read32 (frame + 12) = UInt32.ofNat (j + 1) := by
            simp only [stC_B, mem3_B, mem2_B, mem1_B]
            rw [Mem.read32_write32_of_disjoint _ (frame + 16) (frame + 12) _
                  (by right; rw [hft16, hft12]),
                Mem.read32_write32_same, hj_add1]
          have hread16_B : stC_B.mem.read32 (frame + 16) = UInt32.ofNat (k + 1) := by
            simp only [stC_B, mem3_B]
            rw [Mem.read32_write32_same, hk_add1]
          -- locB_out_B.get 6: local[0] unchanged (set indices 1,2,3,4,6,7 ≠ 0)
          have hf6_out_B : locB_out_B.get 6 = some (.i32 frame) := by
            simp only [locB_out_B, locB_out_locs, Locals.get, hlparams, hllocals, List.length_set,
                       show ¬ (6 < 6) from by omega,
                       show 6 < 6 + 16 from by omega,
                       show 6 - 6 = 0 from by omega,
                       List.getElem?_set,
                       show (7 : Nat) ≠ 0 from by omega,
                       show (6 : Nat) ≠ 0 from by omega,
                       show (4 : Nat) ≠ 0 from by omega,
                       show (3 : Nat) ≠ 0 from by omega,
                       show (2 : Nat) ≠ 0 from by omega,
                       show (1 : Nat) ≠ 0 from by omega,
                       if_false]
            simpa [Locals.get, hlparams, hllocals,
                   show ¬ (6 < 6) from by omega] using hf6
          have hllocals_out_B : locB_out_B.locals.length = 16 := by
            simp [locB_out_B, locB_out_locs, List.length_set, hllocals]
          -- locB_out_B.get 0..5 = locA.get 0..5: params unchanged, needs hlparams for if-branch
          have hg_eq_B : ∀ n, n < 6 → locB_out_B.get n = locA.get n := fun n hn => by
            simp only [locB_out_B, Locals.get, hlparams, if_pos hn]
          have hlparams_out_B : locB_out_B.params.length = 6 := by exact hlparams
          -- invariant restoration: (i, j+1)
          have hI_B : MergeLoopInv frame out_ptr left_ptr right_ptr n_left n_right n_out
                        i₀ j₀ k₀ st stC_B locB_out_B :=
            ⟨i, j + 1, hi_lo, hi_hi, by omega, by omega,
             hread8_B, hread12_B,
             by rw [hread16_B]; congr 1; omega,
             hf6_out_B,
             (hg_eq_B 0 (by omega)).trans h0, (hg_eq_B 1 (by omega)).trans h1,
             (hg_eq_B 2 (by omega)).trans h2, (hg_eq_B 3 (by omega)).trans h3,
             (hg_eq_B 4 (by omega)).trans h4, (hg_eq_B 5 (by omega)).trans h5,
             hlparams_out_B, hllocals_out_B, ⟨v₀, hg⟩,
             fun q hq => by
               simp only [stC_B, mem3_B, mem2_B, mem1_B]
               have hliq : (left_ptr + 4 * UInt32.ofNat q).toNat = left_ptr.toNat + 4 * q :=
                 toNat_wordAddr left_ptr n_left.toNat q hq (by linarith)
               rw [Mem.read32_write32_of_disjoint _ (frame + 16) _ _
                     (by rw [hft16, hliq]; rcases hframe_left_disj with h | h <;> omega),
                   Mem.read32_write32_of_disjoint _ (frame + 12) _ _
                     (by rw [hft12, hliq]; rcases hframe_left_disj with h | h <;> omega),
                   Mem.read32_write32_of_disjoint _ (out_ptr + 4 * UInt32.ofNat k) _ _
                     (by rw [hout_k_toNat, hliq]; rcases hleft_out_disj with h | h <;> omega)]
               exact hleft q hq,
             fun q hq => by
               simp only [stC_B, mem3_B, mem2_B, mem1_B]
               have hriq : (right_ptr + 4 * UInt32.ofNat q).toNat = right_ptr.toNat + 4 * q :=
                 toNat_wordAddr right_ptr n_right.toNat q hq (by linarith)
               rw [Mem.read32_write32_of_disjoint _ (frame + 16) _ _
                     (by rw [hft16, hriq]; rcases hframe_right_disj with h | h <;> omega),
                   Mem.read32_write32_of_disjoint _ (frame + 12) _ _
                     (by rw [hft12, hriq]; rcases hframe_right_disj with h | h <;> omega),
                   Mem.read32_write32_of_disjoint _ (out_ptr + 4 * UInt32.ofNat k) _ _
                     (by rw [hout_k_toNat, hriq]; rcases hright_out_disj with h | h <;> omega)]
               exact hright q hq,
             (by
               -- content invariant: wordsAt stC_B (out+4k₀) (W+1) ++ merge(L.drop i, R.drop(j+1))
               --                  = merge(L.drop i₀, R.drop j₀)  (path B: ¬(left_i ≤ right_j))
               have hW : (i - i₀) + (j + 1 - j₀) = (i - i₀) + (j - j₀) + 1 := by omega
               rw [hW]
               have h_k₀_addr : (out_ptr + 4 * UInt32.ofNat k₀).toNat = out_ptr.toNat + 4 * k₀ :=
                 toNat_wordAddr out_ptr n_out.toNat k₀ (by have := hk_val; omega) (by linarith)
               have hout_bnd : (out_ptr + 4 * UInt32.ofNat k₀).toNat + 4 * ((i - i₀) + (j - j₀) + 1) ≤ 4294967296 := by
                 rw [h_k₀_addr]; have := hk_val; omega
               have hwords : wordsAt stC_B.mem (out_ptr + 4 * UInt32.ofNat k₀) ((i - i₀) + (j - j₀) + 1) =
                   wordsAt stA.mem (out_ptr + 4 * UInt32.ofNat k₀) ((i - i₀) + (j - j₀)) ++ [right_j] := by
                 simp only [stC_B, mem3_B, mem2_B, mem1_B]
                 rw [wordsAt_write32_of_disjoint _ _ (frame + 16) _ _ hout_bnd
                       (by rw [hft16, h_k₀_addr]; rcases hframe_out_disj with h | h <;> [left; right] <;> omega),
                     wordsAt_write32_of_disjoint _ _ (frame + 12) _ _ hout_bnd
                       (by rw [hft12, h_k₀_addr]; rcases hframe_out_disj with h | h <;> [left; right] <;> omega),
                     wordsAt_split _ _ _ ((i - i₀) + (j - j₀)) (by omega)]
                 simp only [show (i - i₀) + (j - j₀) + 1 - ((i - i₀) + (j - j₀)) = 1 from by omega]
                 congr 1
                 · rw [wordsAt_write32_of_disjoint _ _ (out_ptr + 4 * UInt32.ofNat k) _ _
                         (by omega)
                         (by right; rw [h_k₀_addr, hout_k_toNat]; omega)]
                 · have hbase_W : out_ptr + 4 * UInt32.ofNat k₀ + 4 * UInt32.ofNat ((i - i₀) + (j - j₀)) =
                       out_ptr + 4 * UInt32.ofNat k := by
                     have hkeq : k₀ + ((i - i₀) + (j - j₀)) = k := by omega
                     rw [UInt32.add_assoc, ← UInt32.mul_add, ← UInt32.ofNat_add, hkeq]
                   rw [hbase_W]; simp [wordsAt, Mem.read32_write32_same]
               rw [hwords, List.append_assoc, List.singleton_append]
               conv_rhs => rw [← hcontent]
               congr 1
               -- right_j :: merge(L.drop i, R.drop(j+1)) = merge(L.drop i, R.drop j)
               have hL_drop_i : (wordsAt st.mem left_ptr n_left.toNat).drop i =
                   st.mem.read32 (left_ptr + 4 * UInt32.ofNat i) ::
                   (wordsAt st.mem left_ptr n_left.toNat).drop (i + 1) := by
                 have h1 : i < (wordsAt st.mem left_ptr n_left.toNat).length := by
                   simp [wordsAt_length]; exact hlt_i
                 rw [List.drop_eq_getElem_cons h1, wordsAt_getElem _ _ _ _ hlt_i]
               have hR_drop_j : (wordsAt st.mem right_ptr n_right.toNat).drop j =
                   st.mem.read32 (right_ptr + 4 * UInt32.ofNat j) ::
                   (wordsAt st.mem right_ptr n_right.toNat).drop (j + 1) := by
                 have h2 : j < (wordsAt st.mem right_ptr n_right.toNat).length := by
                   simp [wordsAt_length]; exact hlt_j
                 rw [List.drop_eq_getElem_cons h2, wordsAt_getElem _ _ _ _ hlt_j]
               have hright_j_eq : right_j = st.mem.read32 (right_ptr + 4 * UInt32.ofNat j) :=
                 hright j hlt_j
               have hnle_st : ¬(st.mem.read32 (left_ptr + 4 * UInt32.ofNat i) ≤
                   st.mem.read32 (right_ptr + 4 * UInt32.ofNat j)) := by
                 rw [← hleft i hlt_i, ← hright j hlt_j]; exact hle
               rw [hright_j_eq, hL_drop_i, hR_drop_j, merge_cons_gt hnle_st]),
             by simp [stC_B, mem3_B, mem2_B, mem1_B, Mem.write32_pages, hpages],
             hk_global,
             by simp [stC_B, mem3_B, mem2_B, mem1_B, Mem.write32_pages, hleft_global],
             by simp [stC_B, mem3_B, mem2_B, mem1_B, Mem.write32_pages, hright_global],
             by simp [stC_B, mem3_B, mem2_B, mem1_B, Mem.write32_pages, hout_global],
             hpages_u32, hleft_out_disj, hright_out_disj, hleft_right_disj,
             hframe_left_disj, hframe_right_disj, hframe_out_disj⟩
          -- measure decrease
          have hμ_B : (n_left.toNat - (stC_B.mem.read32 (frame + 8)).toNat) +
                      (n_right.toNat - (stC_B.mem.read32 (frame + 12)).toNat) < n := by
            rw [hread8_B, hread12_B, UInt32.toNat_ofNat', UInt32.toNat_ofNat',
                Nat.mod_eq_of_lt (by have := n_left.toNat_lt; omega),
                Nat.mod_eq_of_lt (by have := n_right.toNat_lt; omega),
                ← hμ, hi_m, hj_m, UInt32.toNat_ofNat', UInt32.toNat_ofNat',
                Nat.mod_eq_of_lt (by have := n_left.toNat_lt; omega),
                Nat.mod_eq_of_lt (by have := n_right.toNat_lt; omega)]
            omega
          -- IH at reduced measure: input is (stC_B, locB_out_B)
          obtain ⟨f_rest, hf_rest⟩ := IH _ hμ_B stC_B locB_out_B hI_B rfl
          -- Fuel composition: one body iteration at stA then IH fuel at stC_B
          have hbody_ne : exec f_B m stA locA mainMergeBody env ≠ .OutOfFuel := by
            simp [h_body_B]
          have hfuel_ne : exec f_rest m stC_B locB_out_B [.block 0 0 [.loop 0 0 mainMergeBody]] env ≠ .OutOfFuel :=
            fun h => by rw [h] at hf_rest; exact hf_rest
          have hbody_mono : exec (max f_B f_rest) m stA locA mainMergeBody env = .Break 0 stC_B locB_out_B :=
            (exec_fuel_mono (Nat.le_max_left f_B f_rest) hbody_ne).trans h_body_B
          have hblock_mono : exec (max f_B f_rest + 1) m stC_B locB_out_B [.block 0 0 [.loop 0 0 mainMergeBody]] env =
              exec f_rest m stC_B locB_out_B [.block 0 0 [.loop 0 0 mainMergeBody]] env :=
            exec_fuel_mono (by omega) hfuel_ne
          have hloop_single : ∀ F stT locT,
              exec F m stT locT [.loop 0 0 mainMergeBody] env =
              execOne F m stT locT (.loop 0 0 mainMergeBody) env := fun F stT locT => by
            cases F with
            | zero => simp [exec, execOne]
            | succ f =>
              simp only [exec]
              rcases execOne (f + 1) m stT locT (.loop 0 0 mainMergeBody) env with
                ⟨_, _⟩ | ⟨_, _, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_⟩ | _
              · rfl
              all_goals rfl
          have hloop_eq : exec (max f_B f_rest + 1) m stA locA [.loop 0 0 mainMergeBody] env =
              exec (max f_B f_rest) m stC_B locB_out_B [.loop 0 0 mainMergeBody] env := by
            rw [hloop_single, hloop_single]
            conv_lhs => rw [execOne_loop_succ]
            simp only [hbody_mono, List.take_zero, List.nil_append, List.drop_zero]
            rfl
          have heq : exec (max f_B f_rest + 2) m stA locA [.block 0 0 [.loop 0 0 mainMergeBody]] env =
              exec (max f_B f_rest + 1) m stC_B locB_out_B [.block 0 0 [.loop 0 0 mainMergeBody]] env := by
            rw [show max f_B f_rest + 2 = max f_B f_rest + 1 + 1 from rfl]
            conv_lhs => rw [exec_block_cons, hloop_eq]
            conv_rhs => rw [exec_block_cons]
            set discr := exec (max f_B f_rest) m stC_B locB_out_B [.loop 0 0 mainMergeBody] env
            rcases discr with ⟨r', s'⟩ | ⟨n, r', s'⟩ | ⟨r', vs⟩ | ⟨r', msg⟩ | ⟨msg⟩ | _
            · simp [exec, locB_out_B, locB_out_locs]
            · cases n with | zero => simp [exec, locB_out_B, locB_out_locs] | succ k => rfl
            all_goals rfl
          exact ⟨max f_B f_rest + 2, by rw [heq, hblock_mono]; exact hf_rest⟩
      · -- exit: j = n_right
        -- body's second br_if 1 fires: exec 1 body = Break 1 → exec 2 loop = Break 0
        -- → exec 3 block = Fallthrough.  Q: stA.mem.read32(frame+12) = n_right.
        have hj_eq : j = n_right.toNat := Nat.le_antisymm hj_hi (Nat.not_lt.mp hlt_j)
        have hi_lt32  : UInt32.ofNat i < n_left := by
          rw [UInt32.lt_iff_toNat_lt_toNat, UInt32.toNat_ofNat']
          have := n_left.toNat_lt; omega
        have hj_nlt32 : ¬(UInt32.ofNat j < n_right) := by
          rw [UInt32.lt_iff_toNat_lt_toNat, UInt32.toNat_ofNat']
          have := n_right.toNat_lt; omega
        have hb8  : ¬(frame.toNat + (8 : UInt32).toNat + 4 > stA.mem.pages * 65536) :=
          by simp; omega
        have hb12 : ¬(frame.toNat + (12 : UInt32).toNat + 4 > stA.mem.pages * 65536) :=
          by simp; omega
        have hgv6j : ∀ xs, ({ locA with values := xs } : Locals).get 6 = locA.get 6 := fun _ => rfl
        have hgv1j : ∀ xs, ({ locA with values := xs } : Locals).get 1 = locA.get 1 := fun _ => rfl
        have hgv3j : ∀ xs, ({ locA with values := xs } : Locals).get 3 = locA.get 3 := fun _ => rfl
        -- exec 1 body = Break 1 (second br_if 1 fires since j = n_right)
        have h_body_exit_j : exec 1 m stA locA mainMergeBody env = .Break 1 stA locA := by
          simp only [mainMergeBody, exec, execOne.eq_def,
                     hgv6j, hgv1j, hgv3j, hf6, h1, h3,
                     hi_m, hj_m,
                     if_neg hb8, if_neg hb12,
                     if_pos hi_lt32,
                     show (1 : UInt32) &&& 1 = 1 from by decide,
                     show (if (1 : UInt32) = 0 then (1 : UInt32) else 0) = 0 from by decide,
                     if_neg hj_nlt32,
                     show (1 : UInt32) &&& 0 = 0 from by decide]
          rfl
        -- exec 2 [.loop ...] = Break 0  (Break 1 from body → loop converts to Break 0)
        have h_loop_exit_j : exec 2 m stA locA [.loop 0 0 mainMergeBody] env = .Break 0 stA locA := by
          simp only [show (2 : Nat) = 1 + 1 from rfl, exec, execOne_loop_succ]
          rw [h_body_exit_j]
        -- exec 3 [.block ...] = Fallthrough  (Break 0 from loop → block gives Fallthrough)
        have h_block_exit_j : exec 3 m stA locA [.block 0 0 [.loop 0 0 mainMergeBody]] env =
            .Fallthrough stA locA := by
          rw [show (3 : Nat) = 2 + 1 from rfl, exec_block_cons, h_loop_exit_j]
          simp only [List.take_zero, List.nil_append, List.drop_zero, exec]
        have hQ_j : stA.mem.read32 (frame + 12) = n_right := by
          rw [hj_m, hj_eq]
          apply UInt32.toNat_inj.mp
          simp
        refine ⟨3, ?_⟩
        simp only [h_block_exit_j]
        exact ⟨Or.inr hQ_j, i, j, hi_lo, hi_hi, hj_lo, hj_hi,
               hi_m, hj_m, hk_m, hleft, hright, hcontent⟩
    · -- exit: i = n_left
      -- body's first br_if 1 fires immediately: exec 1 body = Break 1 → exec 2 loop = Break 0
      -- → exec 3 block = Fallthrough.  Q: stA.mem.read32(frame+8) = n_left.
      have hi_eq : i = n_left.toNat := Nat.le_antisymm hi_hi (Nat.not_lt.mp hlt_i)
      have hi_nlt32 : ¬(UInt32.ofNat i < n_left) := by
        rw [UInt32.lt_iff_toNat_lt_toNat, UInt32.toNat_ofNat']
        have := n_left.toNat_lt; omega
      have hb8i : ¬(frame.toNat + (8 : UInt32).toNat + 4 > stA.mem.pages * 65536) :=
        by simp; omega
      have hgv6i : ∀ xs, ({ locA with values := xs } : Locals).get 6 = locA.get 6 := fun _ => rfl
      have hgv1i : ∀ xs, ({ locA with values := xs } : Locals).get 1 = locA.get 1 := fun _ => rfl
      -- exec 1 body = Break 1 (first br_if 1 fires since i = n_left)
      have h_body_exit_i : exec 1 m stA locA mainMergeBody env = .Break 1 stA locA := by
        simp only [mainMergeBody, exec, execOne.eq_def,
                   hgv1i, hf6, h1, hi_m,
                   if_neg hb8i,
                   if_neg hi_nlt32,
                   show (1 : UInt32) &&& 0 = 0 from by decide]
        rfl
      -- exec 2 [.loop ...] = Break 0
      have h_loop_exit_i : exec 2 m stA locA [.loop 0 0 mainMergeBody] env = .Break 0 stA locA := by
        simp only [show (2 : Nat) = 1 + 1 from rfl, exec, execOne_loop_succ]
        rw [h_body_exit_i]
      -- exec 3 [.block 0 0 [.loop ...]] = Fallthrough
      have h_block_exit_i : exec 3 m stA locA [.block 0 0 [.loop 0 0 mainMergeBody]] env =
          .Fallthrough stA locA := by
        rw [show (3 : Nat) = 2 + 1 from rfl, exec_block_cons, h_loop_exit_i]
        simp only [List.take_zero, List.nil_append, List.drop_zero, exec]
      have hQ_i : stA.mem.read32 (frame + 8) = n_left := by
        rw [hi_m, hi_eq]
        apply UInt32.toNat_inj.mp
        simp
      refine ⟨3, ?_⟩
      simp only [h_block_exit_i]
      exact ⟨Or.inl hQ_i, i, j, hi_lo, hi_hi, hj_lo, hj_hi,
             hi_m, hj_m, hk_m, hleft, hright, hcontent⟩

set_option maxHeartbeats 800000 in
theorem main_merge_loop_spec_exec
    {m : Module} {env : HostEnv Unit}
    (st : Store Unit) (locals : Locals)
    (frame out_ptr left_ptr right_ptr n_left n_right n_out : UInt32)
    (i₀ j₀ k₀ : Nat)
    (hI₀ : MergeLoopInv frame out_ptr left_ptr right_ptr n_left n_right n_out
             i₀ j₀ k₀ st st locals) :
    ∃ N : Nat, ∃ st₂ : Store Unit, ∃ loc₂ : Locals,
      exec N m st locals [.block 0 0 [.loop 0 0 mainMergeBody]] env = .Fallthrough st₂ loc₂ ∧
      ((st₂.mem.read32 (frame + 8)  = n_left ∨
        st₂.mem.read32 (frame + 12) = n_right) ∧
       ∃ i j : Nat,
         i₀ ≤ i ∧ i ≤ n_left.toNat ∧ j₀ ≤ j ∧ j ≤ n_right.toNat ∧
         st₂.mem.read32 (frame + 8)  = UInt32.ofNat i ∧
         st₂.mem.read32 (frame + 12) = UInt32.ofNat j ∧
         st₂.mem.read32 (frame + 16) = UInt32.ofNat (k₀ + (i - i₀) + (j - j₀)) ∧
         (∀ q, q < n_left.toNat →
           st₂.mem.read32 (left_ptr + 4 * UInt32.ofNat q) =
           st.mem.read32  (left_ptr + 4 * UInt32.ofNat q)) ∧
         (∀ q, q < n_right.toNat →
           st₂.mem.read32 (right_ptr + 4 * UInt32.ofNat q) =
           st.mem.read32  (right_ptr + 4 * UInt32.ofNat q)) ∧
         wordsAt st₂.mem (out_ptr + 4 * UInt32.ofNat k₀) ((i - i₀) + (j - j₀)) ++
           List.merge
             ((wordsAt st.mem left_ptr n_left.toNat).drop i)
             ((wordsAt st.mem right_ptr n_right.toNat).drop j)
             (· ≤ ·) =
         List.merge
           ((wordsAt st.mem left_ptr n_left.toNat).drop i₀)
           ((wordsAt st.mem right_ptr n_right.toNat).drop j₀)
           (· ≤ ·)) ∧
      MergeLoopInv frame out_ptr left_ptr right_ptr n_left n_right n_out
        i₀ j₀ k₀ st st₂ loc₂ ∧
      st₂.globals = st.globals ∧
      (∀ ix, frame.toNat + 32 ≤ ix →
             (ix < out_ptr.toNat ∨ ix ≥ out_ptr.toNat + 4 * n_out.toNat) →
             st₂.mem.bytes ix = st.mem.bytes ix) ∧
      st₂.mem.pages = st.mem.pages := by
  -- strong induction on μ = (n_left - i) + (n_right - j)
  suffices key : ∀ n stA locA,
      MergeLoopInv frame out_ptr left_ptr right_ptr n_left n_right n_out
        i₀ j₀ k₀ st stA locA →
      (n_left.toNat - (stA.mem.read32 (frame + 8)).toNat) +
        (n_right.toNat - (stA.mem.read32 (frame + 12)).toNat) = n →
      ∃ N : Nat, ∃ st₂ : Store Unit, ∃ loc₂ : Locals,
        exec N m stA locA [.block 0 0 [.loop 0 0 mainMergeBody]] env = .Fallthrough st₂ loc₂ ∧
        ((st₂.mem.read32 (frame + 8)  = n_left ∨
          st₂.mem.read32 (frame + 12) = n_right) ∧
         ∃ i j : Nat,
           i₀ ≤ i ∧ i ≤ n_left.toNat ∧ j₀ ≤ j ∧ j ≤ n_right.toNat ∧
           st₂.mem.read32 (frame + 8)  = UInt32.ofNat i ∧
           st₂.mem.read32 (frame + 12) = UInt32.ofNat j ∧
           st₂.mem.read32 (frame + 16) = UInt32.ofNat (k₀ + (i - i₀) + (j - j₀)) ∧
           (∀ q, q < n_left.toNat →
             st₂.mem.read32 (left_ptr + 4 * UInt32.ofNat q) =
             st.mem.read32  (left_ptr + 4 * UInt32.ofNat q)) ∧
           (∀ q, q < n_right.toNat →
             st₂.mem.read32 (right_ptr + 4 * UInt32.ofNat q) =
             st.mem.read32  (right_ptr + 4 * UInt32.ofNat q)) ∧
           wordsAt st₂.mem (out_ptr + 4 * UInt32.ofNat k₀) ((i - i₀) + (j - j₀)) ++
             List.merge
               ((wordsAt st.mem left_ptr n_left.toNat).drop i)
               ((wordsAt st.mem right_ptr n_right.toNat).drop j)
               (· ≤ ·) =
           List.merge
             ((wordsAt st.mem left_ptr n_left.toNat).drop i₀)
             ((wordsAt st.mem right_ptr n_right.toNat).drop j₀)
             (· ≤ ·)) ∧
        MergeLoopInv frame out_ptr left_ptr right_ptr n_left n_right n_out
          i₀ j₀ k₀ st st₂ loc₂ ∧
        st₂.globals = stA.globals ∧
        (∀ ix, frame.toNat + 32 ≤ ix →
               (ix < out_ptr.toNat ∨ ix ≥ out_ptr.toNat + 4 * n_out.toNat) →
               st₂.mem.bytes ix = stA.mem.bytes ix) ∧
        st₂.mem.pages = stA.mem.pages from
    key _ st locals hI₀ rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro stA locA hI hμ
    have hI_save := hI
    obtain ⟨i, j, hi_lo, hi_hi, hj_lo, hj_hi,
             hi_m, hj_m, hk_m,
             hf6, h0, h1, h2, h3, h4, h5,
             hlparams, hllocals, hglobal,
             hleft, hright, hcontent,
             hpages, hk_global,
             hleft_global, hright_global, hout_global,
             hpages_u32,
             hleft_out_disj, hright_out_disj, hleft_right_disj,
             hframe_left_disj, hframe_right_disj, hframe_out_disj⟩ := hI
    by_cases hlt_i : i < n_left.toNat
    · by_cases hlt_j : j < n_right.toNat
      · -- iteration: i < n_left, j < n_right
        -- Case-split on comparison left[i] ≤ right[j].
        -- Each path: exec trace through 14 nested blocks sorry'd;
        -- invariant restoration and measure decrease proven; IH applied.
        obtain ⟨v₀, hg⟩ := hglobal
        have hμ_pos : 0 < n := by
          rw [← hμ, hi_m, hj_m, UInt32.toNat_ofNat', UInt32.toNat_ofNat']
          have := n_left.toNat_lt; have := n_right.toNat_lt; omega
        let k := k₀ + (i - i₀) + (j - j₀)
        have hk_val : k < n_out.toNat := by have := hk_global; omega
        have hft8  : (frame + 8).toNat  = frame.toNat + 8  := by
          rw [UInt32.toNat_add, show (8 : UInt32).toNat = 8 from rfl]
          exact Nat.mod_eq_of_lt (by omega)
        have hft12 : (frame + 12).toNat = frame.toNat + 12 := by
          rw [UInt32.toNat_add, show (12 : UInt32).toNat = 12 from rfl]
          exact Nat.mod_eq_of_lt (by omega)
        have hft16 : (frame + 16).toNat = frame.toNat + 16 := by
          rw [UInt32.toNat_add, show (16 : UInt32).toNat = 16 from rfl]
          exact Nat.mod_eq_of_lt (by omega)
        have hout_k_toNat : (out_ptr + 4 * UInt32.ofNat k).toNat = out_ptr.toNat + 4 * k :=
          toNat_wordAddr out_ptr n_out.toNat k hk_val (by linarith)
        let left_i  := stA.mem.read32 (left_ptr + 4 * UInt32.ofNat i)
        let right_j := stA.mem.read32 (right_ptr + 4 * UInt32.ofNat j)
        have hi_add1 : UInt32.ofNat i + 1 = UInt32.ofNat (i + 1) := by
          apply UInt32.toNat_inj.mp
          simp only [UInt32.toNat_add, UInt32.toNat_ofNat', show (1 : UInt32).toNat = 1 from rfl,
                     Nat.mod_eq_of_lt (show i + 1 < 4294967296 from by
                       have := n_left.toNat_lt; omega)]
          omega
        have hj_add1 : UInt32.ofNat j + 1 = UInt32.ofNat (j + 1) := by
          apply UInt32.toNat_inj.mp
          simp only [UInt32.toNat_add, UInt32.toNat_ofNat', show (1 : UInt32).toNat = 1 from rfl,
                     Nat.mod_eq_of_lt (show j + 1 < 4294967296 from by
                       have := n_right.toNat_lt; omega)]
          omega
        have hk_add1 : UInt32.ofNat k + 1 = UInt32.ofNat (k + 1) := by
          apply UInt32.toNat_inj.mp
          simp only [UInt32.toNat_add, UInt32.toNat_ofNat', show (1 : UInt32).toNat = 1 from rfl,
                     Nat.mod_eq_of_lt (show k + 1 < 4294967296 from by
                       have := n_out.toNat_lt; omega)]
          omega
        by_cases hle : left_i ≤ right_j
        · -- ── path A: left[i] ≤ right[j]: copy left[i] to out[k], i++, k++ ──
          let mem1_A := stA.mem.write32 (out_ptr + 4 * UInt32.ofNat k) left_i
          let mem2_A := mem1_A.write32 (frame + 8) (UInt32.ofNat i + 1)
          let mem3_A := mem2_A.write32 (frame + 16) (UInt32.ofNat k + 1)
          let stC_A : Store Unit := { stA with mem := mem3_A }
          -- Result locals: localSet 7(→local[1]) 8(→local[2]) 9(→local[3])
          --                       11(→local[5]) 14(→local[8]) 15(→local[9])
          let locA_out_locs :=
            locA.locals.set 1 (.i32 (UInt32.ofNat i)) |>.set 2 (.i32 left_i)
              |>.set 3 (.i32 (UInt32.ofNat j)) |>.set 5 (.i32 (UInt32.ofNat i))
              |>.set 8 (.i32 left_i) |>.set 9 (.i32 (UInt32.ofNat k))
          let locA_out_A : Locals := { locA with locals := locA_out_locs }
          -- exec trace (staged through 14 nested blocks)
          have h_body_A : ∃ f_A,
              exec f_A m stA locA mainMergeBody env = .Break 0 stC_A locA_out_A := by
            refine ⟨15, ?_⟩
            -- ── body let-bindings (definitionally transparent to mainMergeBody internals) ──
            let body14 : Program := [
              .localGet 7, .localGet 1, .ltU, .const (1:UInt32), .and, .eqz, .br_if 0,
              .localGet 0, .localGet 7, .const (2:UInt32), .shl, .add,
              .load32 (0:UInt32), .localSet 8,
              .localGet 6, .load32 (12:UInt32), .localSet 9,
              .localGet 9, .localGet 3, .ltU, .const (1:UInt32), .and, .br_if 1, .br 2]
            let body13 : Program := [.block 0 0 body14,
              .localGet 7, .localGet 1, .const (1048712:UInt32), .call 87, .unreachable]
            let body12 : Program := [.block 0 0 body13,
              .localGet 8, .localGet 2, .localGet 9, .const (2:UInt32), .shl, .add,
              .load32 (0:UInt32), .leU, .const (1:UInt32), .and, .br_if 2, .br 1]
            let body11 : Program := [.block 0 0 body12,
              .localGet 9, .localGet 3, .const (1048728:UInt32), .call 87, .unreachable]
            let body10 : Program := [.block 0 0 body11,
              .localGet 6, .load32 (12:UInt32), .localSet 10,
              .localGet 10, .localGet 3, .ltU, .const (1:UInt32), .and, .br_if 1, .br 2]
            let body9 : Program := [.block 0 0 body10,
              .localGet 6, .load32 (8:UInt32), .localSet 11,
              .localGet 11, .localGet 1, .ltU, .const (1:UInt32), .and, .br_if 4, .br 5]
            let body8 : Program := [.block 0 0 body9,
              .localGet 2, .localGet 10, .const (2:UInt32), .shl, .add,
              .load32 (0:UInt32), .localSet 12,
              .localGet 6, .load32 (16:UInt32), .localSet 13,
              .localGet 13, .localGet 5, .ltU, .const (1:UInt32), .and, .br_if 1, .br 2]
            let body7 : Program := [.block 0 0 body8,
              .localGet 10, .localGet 3, .const (1048744:UInt32), .call 87, .unreachable]
            let body6 : Program := [.block 0 0 body7,
              .localGet 4, .localGet 13, .const (2:UInt32), .shl, .add,
              .localGet 12, .store32 (0:UInt32),
              .localGet 6, .localGet 6, .load32 (12:UInt32),
              .const (1:UInt32), .add, .store32 (12:UInt32), .br 5]
            let body5 : Program := [.block 0 0 body6,
              .localGet 13, .localGet 5, .const (1048760:UInt32), .call 87, .unreachable]
            let body4 : Program := [.block 0 0 body5,
              .localGet 0, .localGet 11, .const (2:UInt32), .shl, .add,
              .load32 (0:UInt32), .localSet 14,
              .localGet 6, .load32 (16:UInt32), .localSet 15,
              .localGet 15, .localGet 5, .ltU, .const (1:UInt32), .and, .br_if 1, .br 2]
            let body3 : Program := [.block 0 0 body4,
              .localGet 11, .localGet 1, .const (1048776:UInt32), .call 87, .unreachable]
            let body2 : Program := [.block 0 0 body3,
              .localGet 4, .localGet 15, .const (2:UInt32), .shl, .add,
              .localGet 14, .store32 (0:UInt32),
              .localGet 6, .localGet 6, .load32 (8:UInt32),
              .const (1:UInt32), .add, .store32 (8:UInt32), .br 1]
            let body1 : Program := [.block 0 0 body2,
              .localGet 15, .localGet 5, .const (1048792:UInt32), .call 87, .unreachable]
            -- ── intermediate Locals states ──
            -- after prefix localSet 7: local[1] = UInt32.ofNat i
            let locA_7 : Locals :=
              { locA with locals := locA.locals.set 1 (.i32 (UInt32.ofNat i)) }
            -- after body14 localSet 8,9: local[2]=left_i, local[3]=UInt32.ofNat j
            let locA_89_locs :=
              locA.locals.set 1 (.i32 (UInt32.ofNat i)) |>.set 2 (.i32 left_i)
                |>.set 3 (.i32 (UInt32.ofNat j))
            let locA_89 : Locals := { locA with locals := locA_89_locs }
            -- after B9_left_cont localSet 11: local[5]=UInt32.ofNat i
            let locA_11_locs :=
              locA.locals.set 1 (.i32 (UInt32.ofNat i)) |>.set 2 (.i32 left_i)
                |>.set 3 (.i32 (UInt32.ofNat j)) |>.set 5 (.i32 (UInt32.ofNat i))
            let locA_11 : Locals := { locA with locals := locA_11_locs }
            -- store after B2: out[k]=left_i written, frame+8=i+1 written
            let stA_m2 : Store Unit := { stA with mem := mem2_A }
            -- ── auxiliary lemmas ──
            have hi_lt_u32 : UInt32.ofNat i < n_left := by
              rw [UInt32.lt_iff_toNat_lt_toNat, UInt32.toNat_ofNat']
              have := n_left.toNat_lt; omega
            have hj_lt_u32 : UInt32.ofNat j < n_right := by
              rw [UInt32.lt_iff_toNat_lt_toNat, UInt32.toNat_ofNat']
              have := n_right.toNat_lt; omega
            have hk_lt_u32 : UInt32.ofNat k < n_out := by
              rw [UInt32.lt_iff_toNat_lt_toNat, UInt32.toNat_ofNat']
              have := n_out.toNat_lt; omega
            have hmem1_fr8 : mem1_A.read32 (frame + 8) = UInt32.ofNat i := by
              simp only [mem1_A,
                Mem.read32_write32_of_disjoint _ (out_ptr + 4 * UInt32.ofNat k) (frame + 8) _
                  (by rw [hout_k_toNat, hft8]; rcases hframe_out_disj with h | h <;> omega)]
              exact hi_m
            have hmem2_fr16 : mem2_A.read32 (frame + 16) = UInt32.ofNat k := by
              simp only [mem2_A,
                Mem.read32_write32_of_disjoint _ (frame + 8) (frame + 16) _
                  (by left; rw [hft8, hft16]; omega)]
              simp only [mem1_A,
                Mem.read32_write32_of_disjoint _ (out_ptr + 4 * UInt32.ofNat k) (frame + 16) _
                  (by rw [hout_k_toNat, hft16]; rcases hframe_out_disj with h | h <;> omega)]
              exact hk_m
            have hbnd_out_k : ¬((out_ptr + 4 * UInt32.ofNat k).toNat + 4 > stA.mem.pages * 65536) := by
              rw [hout_k_toNat]; omega
            have hbnd_fr8 : ¬((frame + 8).toNat + 4 > stA.mem.pages * 65536) := by
              rw [hft8]; omega
            have hbnd_fr12 : ¬((frame + 12).toNat + 4 > stA.mem.pages * 65536) := by
              rw [hft12]; omega
            have hbnd_fr16 : ¬((frame + 16).toNat + 4 > stA.mem.pages * 65536) := by
              rw [hft16]; omega
            have hbnd_left_i : ¬((left_ptr + 4 * UInt32.ofNat i).toNat + 4 > stA.mem.pages * 65536) := by
              rw [toNat_wordAddr left_ptr n_left.toNat i hlt_i (by linarith)]; omega
            have hbnd_right_j : ¬((right_ptr + 4 * UInt32.ofNat j).toNat + 4 > stA.mem.pages * 65536) := by
              rw [toNat_wordAddr right_ptr n_right.toNat j hlt_j (by linarith)]; omega
            -- ── exec chain through 14 blocks ──
            -- body14: 23 flat instructions → Break 1 (br_if 1 fires: j < n_right)
            have h_B14 : exec 1 m stA locA_7 body14 env = .Break 1 stA locA_89 := by
              -- GV helpers: {locA_7 with values := vs}.get N = locA_7.get N
              have hgv7_7 : ∀ vs, ({locA_7 with values := vs} : Locals).get 7 = locA_7.get 7 := fun _ => rfl
              have hgv1_7 : ∀ vs, ({locA_7 with values := vs} : Locals).get 1 = locA_7.get 1 := fun _ => rfl
              have hgv0_7 : ∀ vs, ({locA_7 with values := vs} : Locals).get 0 = locA_7.get 0 := fun _ => rfl
              have hgv6_7 : ∀ vs, ({locA_7 with values := vs} : Locals).get 6 = locA_7.get 6 := fun _ => rfl
              have hgv3_7 : ∀ vs, ({locA_7 with values := vs} : Locals).get 3 = locA_7.get 3 := fun _ => rfl
              -- locA_7 length facts
              have hlp_7 : locA_7.params.length = 6  := hlparams
              have hll_7 : locA_7.locals.length = 16 := by simp [locA_7, List.length_set, hllocals]
              -- locA_7 specific gets
              have hg7_7 : locA_7.get 7 = some (.i32 (UInt32.ofNat i)) := by
                simp only [Locals.get, hlp_7, hll_7, List.length_set,
                           show ¬(7 < 6) from by omega, show (7 : Nat) < 6 + 16 from by omega,
                           show (7 : Nat) - 6 = 1 from by omega]
                -- goal: locA_7.locals[1]? = some _; locA_7.locals = locA.locals.set 1 _
                change (locA.locals.set 1 (.i32 (UInt32.ofNat i)))[1]? = _
                exact List.getElem?_set_self (by rw [hllocals]; norm_num)
              have hg1_7 : locA_7.get 1 = some (.i32 n_left) := by
                simp only [Locals.get, locA_7, hlparams, show (1 : Nat) < 6 from by omega] at h1 ⊢
                exact h1
              have hg0_7 : locA_7.get 0 = some (.i32 left_ptr) := by
                simp only [Locals.get, locA_7, hlparams, show (0 : Nat) < 6 from by omega] at h0 ⊢
                exact h0
              have hg6_7 : locA_7.get 6 = some (.i32 frame) := by
                have h : locA_7.get 6 = locA.get 6 := by
                  simp [locA_7, Locals.get, hlparams, hllocals, List.length_set, List.getElem?_set]
                rw [h]; exact hf6
              have hg3_7 : locA_7.get 3 = some (.i32 n_right) := by
                simp only [Locals.get, locA_7, hlparams, show (3 : Nat) < 6 from by omega] at h3 ⊢
                exact h3
              -- raw-form get 6 after localSet 8 (sets local[2] = left_i)
              have hg6_8_raw : ∀ vs,
                  (Locals.mk locA_7.params (locA_7.locals.set 2 (.i32 left_i)) vs).get 6
                  = some (.i32 frame) := by
                intro vs
                have h : (Locals.mk locA_7.params (locA_7.locals.set 2 (.i32 left_i)) vs).get 6
                    = locA.get 6 := by
                  simp [locA_7, Locals.get, hlparams, hllocals, List.length_set, List.getElem?_set]
                rw [h]; exact hf6
              -- raw-form gets after localSet 9 (sets local[3] = j)
              have hg9_89_raw : ∀ vs,
                  (Locals.mk locA_7.params
                    ((locA_7.locals.set 2 (.i32 left_i)).set 3 (.i32 (UInt32.ofNat j))) vs).get 9
                  = some (.i32 (UInt32.ofNat j)) := by
                intro vs
                simp only [Locals.get, hlp_7, hll_7, List.length_set,
                           show ¬(9 < 6) from by omega, show (9 : Nat) < 6 + 16 from by omega,
                           show (9 : Nat) - 6 = 3 from by omega]
                -- goal: ((locA_7.locals.set 2 _).set 3 _)[3]? = some _
                exact List.getElem?_set_self (by simp [List.length_set, hll_7])
              have hg3_89_raw : ∀ vs,
                  (Locals.mk locA_7.params
                    ((locA_7.locals.set 2 (.i32 left_i)).set 3 (.i32 (UInt32.ofNat j))) vs).get 3
                  = some (.i32 n_right) := by
                intro vs
                have h3_raw : locA.params[3]? = some (.i32 n_right) := by
                  have h := h3
                  simp only [Locals.get, hlparams, show (3 : Nat) < 6 from by omega] at h
                  exact h
                simp only [Locals.get, hlp_7, show (3 : Nat) < 6 from by omega]
                exact h3_raw
              -- shl-by-2 = multiply-by-4
              have hshl_i : UInt32.ofNat i <<< ((2 : UInt32) % 32) = 4 * UInt32.ofNat i := by
                rw [show (2 : UInt32) % 32 = 2 from by decide]
                apply UInt32.toNat_inj.mp
                have hi_bnd : i < 2 ^ 30 := by have := n_left.toNat_lt; omega
                simp only [UInt32.toNat_mul, UInt32.toNat_ofNat',
                           show (4 : UInt32).toNat = 4 from rfl,
                           Nat.mod_eq_of_lt (show i < 4294967296 from by omega),
                           Nat.mod_eq_of_lt (show i * 4 < 4294967296 from by omega)]
                simp [UInt32.shiftLeft, Fin.shiftLeft, Nat.shiftLeft_eq]; omega
              have hshl_j : UInt32.ofNat j <<< ((2 : UInt32) % 32) = 4 * UInt32.ofNat j := by
                rw [show (2 : UInt32) % 32 = 2 from by decide]
                apply UInt32.toNat_inj.mp
                have hj_bnd : j < 2 ^ 30 := by have := n_right.toNat_lt; omega
                simp only [UInt32.toNat_mul, UInt32.toNat_ofNat',
                           show (4 : UInt32).toNat = 4 from rfl,
                           Nat.mod_eq_of_lt (show j < 4294967296 from by omega),
                           Nat.mod_eq_of_lt (show j * 4 < 4294967296 from by omega)]
                simp [UInt32.shiftLeft, Fin.shiftLeft, Nat.shiftLeft_eq]; omega
              -- big simp: reduce body14's 23 flat instructions
              simp only [exec, execOne.eq_def, body14, Locals.set?,
                         hgv7_7, hgv1_7, hgv0_7, hgv6_7, hgv3_7,
                         hg7_7, hg1_7, hg0_7, hg6_7, hg3_7,
                         if_pos hi_lt_u32,
                         show (1 : UInt32) &&& 1 = 1 from by decide,
                         show (if (1 : UInt32) = 0 then (1 : UInt32) else 0) = 0 from by decide,
                         hshl_i,
                         if_neg (show ¬((4 * UInt32.ofNat i + left_ptr).toNat +
                                         UInt32.toNat (0 : UInt32) + 4 > stA.mem.pages * 65536) from by
                                   rw [show 4 * UInt32.ofNat i + left_ptr =
                                           left_ptr + 4 * UInt32.ofNat i from UInt32.add_comm _ _,
                                       show UInt32.toNat (0 : UInt32) = 0 from rfl]; omega),
                         show stA.mem.read32 (4 * UInt32.ofNat i + left_ptr + (0 : UInt32)) = left_i from by
                           rw [show 4 * UInt32.ofNat i + left_ptr + (0 : UInt32) =
                                   left_ptr + 4 * UInt32.ofNat i from by
                               rw [UInt32.add_comm (4 * UInt32.ofNat i) left_ptr, UInt32.add_zero]],
                         hlp_7, hll_7, List.length_set,
                         if_neg (show ¬(8 < 6) from by omega),
                         if_pos (show (8 : Nat) < 6 + 16 from by omega),
                         show (8 : Nat) - 6 = 2 from by omega,
                         hg6_8_raw,
                         if_neg (show ¬(frame.toNat + (12 : UInt32).toNat + 4 > stA.mem.pages * 65536)
                                   from by simp only [show (12 : UInt32).toNat = 12 from by decide]; omega),
                         show stA.mem.read32 (frame + (12 : UInt32)) = UInt32.ofNat j from hj_m,
                         if_neg (show ¬(9 < 6) from by omega),
                         if_pos (show (9 : Nat) < 6 + 16 from by omega),
                         show (9 : Nat) - 6 = 3 from by omega,
                         hg9_89_raw, hg3_89_raw,
                         if_pos hj_lt_u32,
                         show (1 : UInt32) &&& 1 = 1 from by decide,
                         show Locals.mk locA_7.params
                               ((locA_7.locals.set 2 (.i32 left_i)).set 3 (.i32 (UInt32.ofNat j)))
                               locA.values = locA_89 from rfl]
              rfl
            -- body13: Break(0+1) from body14 → Break 0
            have h_B13 : exec 2 m stA locA_7 body13 env = .Break 0 stA locA_89 := by
              rw [show (2:Nat) = 1+1 from rfl, exec_block_cons, h_B14]
            -- body12: Break 0 → B12_compare runs, leU fires (left_i ≤ right_j), br_if 2 → Break 2
            have h_B12_A : exec 3 m stA locA_7 body12 env = .Break 2 stA locA_89 := by
              rw [show (3:Nat) = 2+1 from rfl, exec_block_cons, h_B13]
              simp only [List.take_zero, List.drop_zero, List.nil_append]
              have hll_89 : locA_89.locals.length = 16 := by
                simp [locA_89, locA_89_locs, List.length_set, hllocals]
              have hgv8_89 : ∀ vs, ({locA_89 with values := vs} : Locals).get 8 = locA_89.get 8 := fun _ => rfl
              have hgv2_89 : ∀ vs, ({locA_89 with values := vs} : Locals).get 2 = locA_89.get 2 := fun _ => rfl
              have hgv9_89 : ∀ vs, ({locA_89 with values := vs} : Locals).get 9 = locA_89.get 9 := fun _ => rfl
              have hg8_89 : locA_89.get 8 = some (.i32 left_i) := by
                simp only [Locals.get, locA_89, locA_89_locs, hlparams, hllocals, List.length_set,
                           show ¬(8 < 6) from by omega, show (8:Nat) < 6+16 from by omega,
                           show (8:Nat) - 6 = 2 from by omega]
                rw [List.getElem?_set_ne (show (3:Nat) ≠ 2 from by omega)]
                exact List.getElem?_set_self (by rw [List.length_set, hllocals]; norm_num)
              have hg2_89 : locA_89.get 2 = some (.i32 right_ptr) := by
                simp only [Locals.get, locA_89, hlparams, show (2:Nat) < 6 from by omega] at h2 ⊢
                exact h2
              have hg9_89 : locA_89.get 9 = some (.i32 (UInt32.ofNat j)) := by
                simp only [Locals.get, locA_89, locA_89_locs, hlparams, hllocals, List.length_set,
                           show ¬(9 < 6) from by omega, show (9:Nat) < 6+16 from by omega,
                           show (9:Nat) - 6 = 3 from by omega]
                exact List.getElem?_set_self (by rw [List.length_set, List.length_set, hllocals]; norm_num)
              have hshl_j : UInt32.ofNat j <<< ((2:UInt32) % 32) = 4 * UInt32.ofNat j := by
                rw [show (2:UInt32) % 32 = 2 from by decide]
                apply UInt32.toNat_inj.mp
                have hj_bnd : j < 2^30 := by have := n_right.toNat_lt; omega
                simp only [UInt32.toNat_mul, UInt32.toNat_ofNat',
                           show (4:UInt32).toNat = 4 from rfl,
                           Nat.mod_eq_of_lt (show j < 4294967296 from by omega),
                           Nat.mod_eq_of_lt (show j*4 < 4294967296 from by omega)]
                simp [UInt32.shiftLeft, Fin.shiftLeft, Nat.shiftLeft_eq]; omega
              simp only [exec, execOne.eq_def,
                         show ({locA_89 with values := locA_7.values} : Locals) = locA_89 from rfl,
                         hgv8_89, hgv2_89, hgv9_89,
                         hg8_89, hg2_89, hg9_89,
                         hshl_j,
                         if_neg (show ¬((4 * UInt32.ofNat j + right_ptr).toNat +
                                         UInt32.toNat (0:UInt32) + 4 > stA.mem.pages * 65536) from by
                                   rw [show 4 * UInt32.ofNat j + right_ptr =
                                               right_ptr + 4 * UInt32.ofNat j from UInt32.add_comm _ _,
                                           show UInt32.toNat (0:UInt32) = 0 from rfl]
                                   omega),
                         show stA.mem.read32 (4 * UInt32.ofNat j + right_ptr + (0:UInt32)) = right_j from by
                             rw [show 4 * UInt32.ofNat j + right_ptr + (0:UInt32) =
                                         right_ptr + 4 * UInt32.ofNat j from by
                                     rw [UInt32.add_comm (4 * UInt32.ofNat j) right_ptr, UInt32.add_zero]],
                         if_pos hle,
                         show (1:UInt32) &&& 1 = 1 from by decide,
                         show ({locA_89 with values := locA.values} : Locals) = locA_89 from rfl]
              rfl
            -- body11: Break(1+1) → Break 1
            have h_B11 : exec 4 m stA locA_7 body11 env = .Break 1 stA locA_89 := by
              rw [show (4:Nat) = 3+1 from rfl, exec_block_cons, h_B12_A]
            -- body10: Break(0+1) → Break 0 (B10_right_cont NOT reached in path A)
            have h_B10 : exec 5 m stA locA_7 body10 env = .Break 0 stA locA_89 := by
              rw [show (5:Nat) = 4+1 from rfl, exec_block_cons, h_B11]
            -- body9: Break 0 → B9_left_cont runs, br_if 4 fires (i < n_left) → Break 4
            have h_B9 : exec 6 m stA locA_7 body9 env = .Break 4 stA locA_11 := by
              rw [show (6:Nat) = 5+1 from rfl, exec_block_cons, h_B10]
              simp only [List.take_zero, List.drop_zero, List.nil_append]
              -- B9_left_cont: localGet 6, load32 8, localSet 11, localGet 11, localGet 1, ltU, const 1, and, br_if 4
              have hlp_89 : locA_89.params.length = 6 := hlparams
              have hll_89 : locA_89.locals.length = 16 := by
                simp [locA_89, locA_89_locs, List.length_set, hllocals]
              have hgv11_11 : ∀ vs, ({locA_11 with values := vs} : Locals).get 11 = locA_11.get 11 := fun _ => rfl
              have hgv1_11  : ∀ vs, ({locA_11 with values := vs} : Locals).get 1  = locA_11.get 1  := fun _ => rfl
              have hg6_89 : locA_89.get 6 = some (.i32 frame) := by
                simp only [Locals.get, locA_89, locA_89_locs, hlparams, hllocals, List.length_set,
                           show ¬(6 < 6) from by omega, show (6:Nat) < 6+16 from by omega,
                           show (6:Nat) - 6 = 0 from by omega]
                rw [List.getElem?_set_ne (show (3:Nat) ≠ 0 from by omega)]
                rw [List.getElem?_set_ne (show (2:Nat) ≠ 0 from by omega)]
                rw [List.getElem?_set_ne (show (1:Nat) ≠ 0 from by omega)]
                simpa [Locals.get, hlparams, hllocals, List.length_set,
                       show ¬(6 < 6) from by omega, show (6:Nat) < 6+16 from by omega,
                       show (6:Nat) - 6 = 0 from by omega] using hf6
              have hg11_11 : locA_11.get 11 = some (.i32 (UInt32.ofNat i)) := by
                simp only [Locals.get, locA_11, locA_11_locs, hlparams, hllocals, List.length_set,
                           show ¬(11 < 6) from by omega, show (11:Nat) < 6+16 from by omega,
                           show (11:Nat) - 6 = 5 from by omega]
                exact List.getElem?_set_self
                  (by rw [List.length_set, List.length_set, List.length_set, hllocals]; norm_num)
              have hg1_11 : locA_11.get 1 = some (.i32 n_left) := by
                simp only [Locals.get, locA_11, hlparams, show (1:Nat) < 6 from by omega] at h1 ⊢
                exact h1
              simp only [exec, execOne.eq_def,
                         show ({locA_89 with values := locA_7.values} : Locals) = locA_89 from rfl,
                         hg6_89,
                         if_neg (show ¬(frame.toNat + (8:UInt32).toNat + 4 > stA.mem.pages * 65536) from by
                                   simp only [show (8:UInt32).toNat = 8 from by decide]; omega),
                         show stA.mem.read32 (frame + (8:UInt32)) = UInt32.ofNat i from hi_m,
                         Locals.set?,
                         hlp_89, hll_89, List.length_set,
                         if_neg (show ¬(11 < 6) from by omega),
                         if_pos (show (11:Nat) < 6 + 16 from by omega),
                         show (11:Nat) - 6 = 5 from by omega,
                         show Locals.mk locA_89.params (locA_89.locals.set 5 (.i32 (UInt32.ofNat i))) locA_89.values = locA_11 from rfl,
                         hgv11_11, hg11_11, hgv1_11, hg1_11,
                         if_pos hi_lt_u32,
                         show (1:UInt32) &&& 1 = 1 from by decide,
                         show ({locA_11 with values := locA_11.values} : Locals) = locA_11 from rfl]
              rfl
            -- body8: Break(3+1) → Break 3
            have h_B8 : exec 7 m stA locA_7 body8 env = .Break 3 stA locA_11 := by
              rw [show (7:Nat) = 6+1 from rfl, exec_block_cons, h_B9]
            -- body7: Break(2+1) → Break 2
            have h_B7 : exec 8 m stA locA_7 body7 env = .Break 2 stA locA_11 := by
              rw [show (8:Nat) = 7+1 from rfl, exec_block_cons, h_B8]
            -- body6: Break(1+1) → Break 1
            have h_B6 : exec 9 m stA locA_7 body6 env = .Break 1 stA locA_11 := by
              rw [show (9:Nat) = 8+1 from rfl, exec_block_cons, h_B7]
            -- body5: Break(0+1) → Break 0 (B5_panic NOT reached)
            have h_B5 : exec 10 m stA locA_7 body5 env = .Break 0 stA locA_11 := by
              rw [show (10:Nat) = 9+1 from rfl, exec_block_cons, h_B6]
            -- body4: Break 0 → B4_left_cont runs, localSet 14,15, br_if 1 fires → Break 1
            have h_B4 : exec 11 m stA locA_7 body4 env = .Break 1 stA locA_out_A := by
              rw [show (11:Nat) = 10+1 from rfl, exec_block_cons, h_B5]
              simp only [List.take_zero, List.drop_zero, List.nil_append]
              -- B4_left_cont: localGet 0, localGet 11, const 2, shl, add, load32 0, localSet 14,
              --                localGet 6, load32 16, localSet 15, localGet 15, localGet 5, ltU, const 1, and, br_if 1
              have hlp_11 : locA_11.params.length = 6 := hlparams
              have hll_11 : locA_11.locals.length = 16 := by
                simp [locA_11, locA_11_locs, List.length_set, hllocals]
              have hgv0_11  : ∀ vs, ({locA_11 with values := vs} : Locals).get 0  = locA_11.get 0  := fun _ => rfl
              have hgv11_11 : ∀ vs, ({locA_11 with values := vs} : Locals).get 11 = locA_11.get 11 := fun _ => rfl
              have hg0_11 : locA_11.get 0 = some (.i32 left_ptr) := by
                simp only [Locals.get, locA_11, hlparams, show (0:Nat) < 6 from by omega] at h0 ⊢; exact h0
              have hg11_11 : locA_11.get 11 = some (.i32 (UInt32.ofNat i)) := by
                simp only [Locals.get, locA_11, locA_11_locs, hlparams, hllocals, List.length_set,
                           show ¬(11 < 6) from by omega, show (11:Nat) < 6+16 from by omega,
                           show (11:Nat) - 6 = 5 from by omega]
                exact List.getElem?_set_self
                  (by rw [List.length_set, List.length_set, List.length_set, hllocals]; norm_num)
              -- ∀-vs helpers for gets from intermediate/post-localSet states
              have hg6_14_raw : ∀ vs,
                  (Locals.mk locA_11.params (locA_11.locals.set 8 (.i32 left_i)) vs).get 6
                  = some (.i32 frame) := by
                intro vs
                have h : (Locals.mk locA_11.params (locA_11.locals.set 8 (.i32 left_i)) vs).get 6
                    = locA.get 6 := by
                  simp [locA_11, locA_11_locs, Locals.get, hlparams, hllocals,
                        List.length_set, List.getElem?_set]
                rw [h]; exact hf6
              have hg15_out_raw : ∀ vs,
                  (Locals.mk locA_11.params
                    ((locA_11.locals.set 8 (.i32 left_i)).set 9 (.i32 (UInt32.ofNat k))) vs).get 15
                  = some (.i32 (UInt32.ofNat k)) := by
                intro vs
                simp only [Locals.get, hlp_11, hll_11, List.length_set,
                           show ¬(15 < 6) from by omega, show (15:Nat) < 6+16 from by omega,
                           show (15:Nat) - 6 = 9 from by omega]
                exact List.getElem?_set_self (by simp [List.length_set, hll_11])
              have hg5_out_raw : ∀ vs,
                  (Locals.mk locA_11.params
                    ((locA_11.locals.set 8 (.i32 left_i)).set 9 (.i32 (UInt32.ofNat k))) vs).get 5
                  = some (.i32 n_out) := by
                intro vs
                have h5_raw : locA.params[5]? = some (.i32 n_out) := by
                  have h := h5
                  simp only [Locals.get, hlparams, show (5:Nat) < 6 from by omega] at h
                  exact h
                simp only [Locals.get, hlp_11, show (5:Nat) < 6 from by omega]
                exact h5_raw
              have hshl_i : UInt32.ofNat i <<< ((2:UInt32) % 32) = 4 * UInt32.ofNat i := by
                rw [show (2:UInt32) % 32 = 2 from by decide]
                apply UInt32.toNat_inj.mp
                have hi_bnd : i < 2^30 := by have := n_left.toNat_lt; omega
                simp only [UInt32.toNat_mul, UInt32.toNat_ofNat',
                           show (4:UInt32).toNat = 4 from rfl,
                           Nat.mod_eq_of_lt (show i < 4294967296 from by omega),
                           Nat.mod_eq_of_lt (show i * 4 < 4294967296 from by omega)]
                simp [UInt32.shiftLeft, Fin.shiftLeft, Nat.shiftLeft_eq]; omega
              simp only [exec, execOne.eq_def,
                         show ({locA_11 with values := locA_7.values} : Locals) = locA_11 from rfl,
                         hgv0_11, hg0_11, hgv11_11, hg11_11,
                         hshl_i,
                         if_neg (show ¬((4 * UInt32.ofNat i + left_ptr).toNat +
                                         UInt32.toNat (0:UInt32) + 4 > stA.mem.pages * 65536) from by
                                   rw [show 4 * UInt32.ofNat i + left_ptr =
                                               left_ptr + 4 * UInt32.ofNat i from UInt32.add_comm _ _,
                                       show UInt32.toNat (0:UInt32) = 0 from rfl]; omega),
                         show stA.mem.read32 (4 * UInt32.ofNat i + left_ptr + (0:UInt32)) = left_i from by
                             rw [show 4 * UInt32.ofNat i + left_ptr + (0:UInt32) =
                                         left_ptr + 4 * UInt32.ofNat i from by
                                     rw [UInt32.add_comm (4 * UInt32.ofNat i) left_ptr, UInt32.add_zero]],
                         Locals.set?,
                         hlp_11, hll_11, List.length_set,
                         if_neg (show ¬(14 < 6) from by omega),
                         if_pos (show (14:Nat) < 6 + 16 from by omega),
                         show (14:Nat) - 6 = 8 from by omega,
                         hg6_14_raw,
                         if_neg (show ¬(frame.toNat + (16:UInt32).toNat + 4 > stA.mem.pages * 65536) from by
                                   simp only [show (16:UInt32).toNat = 16 from by decide]; omega),
                         show stA.mem.read32 (frame + (16:UInt32)) = UInt32.ofNat k from hk_m,
                         if_neg (show ¬(15 < 6) from by omega),
                         if_pos (show (15:Nat) < 6 + 16 from by omega),
                         show (15:Nat) - 6 = 9 from by omega,
                         hg15_out_raw, hg5_out_raw,
                         if_pos hk_lt_u32,
                         show (1:UInt32) &&& 1 = 1 from by decide,
                         show Locals.mk locA_11.params
                               ((locA_11.locals.set 8 (.i32 left_i)).set 9 (.i32 (UInt32.ofNat k)))
                               locA.values = locA_out_A from rfl]
              rfl
            -- body3: Break(0+1) → Break 0 (B3_panic NOT reached)
            have h_B3 : exec 12 m stA locA_7 body3 env = .Break 0 stA locA_out_A := by
              rw [show (12:Nat) = 11+1 from rfl, exec_block_cons, h_B4]
            -- body2: Break 0 → B2_store_left runs, writes out[k]=left_i, frame+8=i+1, br 1 → Break 1
            have h_B2 : exec 13 m stA locA_7 body2 env = .Break 1 stA_m2 locA_out_A := by
              rw [show (13:Nat) = 12+1 from rfl, exec_block_cons, h_B3]
              simp only [List.take_zero, List.drop_zero, List.nil_append]
              -- B2_store_left: localGet 4, localGet 15, const 2, shl, add, localGet 14,
              --   store32 0 (→mem1_A), localGet 6, localGet 6, load32 8 (→i), const 1, add,
              --   store32 8 (→mem2_A), br 1
              have hgv4_out  : ∀ vs, ({locA_out_A with values := vs} : Locals).get 4  = locA_out_A.get 4  := fun _ => rfl
              have hgv15_out : ∀ vs, ({locA_out_A with values := vs} : Locals).get 15 = locA_out_A.get 15 := fun _ => rfl
              have hgv14_out : ∀ vs, ({locA_out_A with values := vs} : Locals).get 14 = locA_out_A.get 14 := fun _ => rfl
              have hgv6_out  : ∀ vs, ({locA_out_A with values := vs} : Locals).get 6  = locA_out_A.get 6  := fun _ => rfl
              have hg4_out : locA_out_A.get 4 = some (.i32 out_ptr) := by
                simp only [Locals.get, locA_out_A, hlparams, show (4:Nat) < 6 from by omega] at h4 ⊢; exact h4
              have hg15_out : locA_out_A.get 15 = some (.i32 (UInt32.ofNat k)) := by
                simp only [Locals.get, locA_out_A, locA_out_locs, hlparams, hllocals, List.length_set,
                           show ¬(15 < 6) from by omega, show (15:Nat) < 6+16 from by omega,
                           show (15:Nat) - 6 = 9 from by omega]
                exact List.getElem?_set_self
                  (by rw [List.length_set, List.length_set, List.length_set,
                           List.length_set, List.length_set, hllocals]; norm_num)
              have hg14_out : locA_out_A.get 14 = some (.i32 left_i) := by
                simp only [Locals.get, locA_out_A, locA_out_locs, hlparams, hllocals, List.length_set,
                           show ¬(14 < 6) from by omega, show (14:Nat) < 6+16 from by omega,
                           show (14:Nat) - 6 = 8 from by omega]
                rw [List.getElem?_set_ne (show (9:Nat) ≠ 8 from by omega)]
                exact List.getElem?_set_self
                  (by rw [List.length_set, List.length_set, List.length_set,
                           List.length_set, hllocals]; norm_num)
              have hg6_out : locA_out_A.get 6 = some (.i32 frame) := by
                simp only [Locals.get, locA_out_A, locA_out_locs, hlparams, hllocals, List.length_set,
                           show ¬(6 < 6) from by omega, show (6:Nat) < 6+16 from by omega,
                           show (6:Nat) - 6 = 0 from by omega,
                           List.getElem?_set, show (9:Nat) ≠ 0 from by omega,
                           show (8:Nat) ≠ 0 from by omega, show (5:Nat) ≠ 0 from by omega,
                           show (3:Nat) ≠ 0 from by omega, show (2:Nat) ≠ 0 from by omega,
                           show (1:Nat) ≠ 0 from by omega, if_false]
                simpa [Locals.get, hlparams, hllocals, show ¬(6 < 6) from by omega] using hf6
              have hshl_k : UInt32.ofNat k <<< ((2:UInt32) % 32) = 4 * UInt32.ofNat k := by
                rw [show (2:UInt32) % 32 = 2 from by decide]
                apply UInt32.toNat_inj.mp
                have hk_bnd : k < 2^30 := by have := n_out.toNat_lt; omega
                simp only [UInt32.toNat_mul, UInt32.toNat_ofNat',
                           show (4:UInt32).toNat = 4 from rfl,
                           Nat.mod_eq_of_lt (show k < 4294967296 from by omega),
                           Nat.mod_eq_of_lt (show k * 4 < 4294967296 from by omega)]
                simp [UInt32.shiftLeft, Fin.shiftLeft, Nat.shiftLeft_eq]; omega
              simp only [exec, execOne.eq_def,
                         show ({locA_out_A with values := locA_7.values} : Locals) = locA_out_A from rfl,
                         hgv4_out, hg4_out, hgv15_out, hg15_out,
                         hshl_k,
                         if_neg (show ¬((4 * UInt32.ofNat k + out_ptr).toNat +
                                         UInt32.toNat (0:UInt32) + 4 > stA.mem.pages * 65536) from by
                                   rw [show 4 * UInt32.ofNat k + out_ptr =
                                               out_ptr + 4 * UInt32.ofNat k from UInt32.add_comm _ _,
                                       show UInt32.toNat (0:UInt32) = 0 from rfl]; omega),
                         show stA.mem.write32 (4 * UInt32.ofNat k + out_ptr + (0:UInt32)) left_i = mem1_A from by
                             rw [show 4 * UInt32.ofNat k + out_ptr + (0:UInt32) =
                                         out_ptr + 4 * UInt32.ofNat k from by
                                     rw [UInt32.add_comm (4 * UInt32.ofNat k) out_ptr, UInt32.add_zero]],
                         hgv14_out, hg14_out,
                         hgv6_out, hg6_out,
                         if_neg (show ¬(frame.toNat + UInt32.toNat (8:UInt32) + 4 >
                                         {stA with mem := mem1_A}.mem.pages * 65536) from by
                                   rw [show ({stA with mem := mem1_A} : Store Unit).mem.pages =
                                         stA.mem.pages from rfl,
                                       show UInt32.toNat (8:UInt32) = 8 from by decide, hft8.symm]
                                   exact hbnd_fr8),
                         show ({stA with mem := mem1_A} : Store Unit).mem.read32 (frame + (8:UInt32)) =
                               UInt32.ofNat i from hmem1_fr8,
                         show (1:UInt32) + UInt32.ofNat i = UInt32.ofNat i + 1 from UInt32.add_comm _ _,
                         if_neg (show ¬(frame.toNat + UInt32.toNat (8:UInt32) + 4 >
                                         {stA with mem := mem1_A}.mem.pages * 65536) from by
                                   rw [show ({stA with mem := mem1_A} : Store Unit).mem.pages =
                                         stA.mem.pages from rfl,
                                       show UInt32.toNat (8:UInt32) = 8 from by decide, hft8.symm]
                                   exact hbnd_fr8),
                         show ({stA with mem := mem1_A} : Store Unit).mem.write32
                               (frame + (8:UInt32)) (UInt32.ofNat i + 1) = mem2_A from rfl,
                         show ({stA with mem := mem2_A} : Store Unit) = stA_m2 from rfl,
                         show ({locA_out_A with values := locA_out_A.values} : Locals) = locA_out_A from rfl]
            -- body1: Break(0+1) → Break 0 (B1_panic NOT reached)
            have h_B1 : exec 14 m stA locA_7 body1 env = .Break 0 stA_m2 locA_out_A := by
              rw [show (14:Nat) = 13+1 from rfl, exec_block_cons, h_B2]
            -- ── assemble: prefix → outer block (h_B1) → suffix ──
            have h_pre : exec 15 m stA locA mainMergeBody env =
                exec 15 m stA locA_7
                  (.block 0 0 body1 :: [.localGet 6, .localGet 6, .load32 (16:UInt32),
                    .const (1:UInt32), .add, .store32 (16:UInt32), .br 0]) env := by
              -- Abstract the continuation to make body1 truly opaque to simp
              have h_prefix_aux : ∀ cont : Program,
                  exec 15 m stA locA
                    ([.localGet 6, .load32 (8:UInt32), .localGet 1, .ltU,
                      .const (1:UInt32), .and, .eqz, .br_if 1,
                      .localGet 6, .load32 (12:UInt32), .localGet 3, .ltU,
                      .const (1:UInt32), .and, .eqz, .br_if 1,
                      .localGet 6, .load32 (8:UInt32), .localSet 7] ++ cont) env
                    = exec 15 m stA locA_7 cont env := by
                intro cont
                have hgv6_pre : ∀ vs, ({locA with values := vs} : Locals).get 6 = locA.get 6 := fun _ => rfl
                have hgv1_pre : ∀ vs, ({locA with values := vs} : Locals).get 1 = locA.get 1 := fun _ => rfl
                have hgv3_pre : ∀ vs, ({locA with values := vs} : Locals).get 3 = locA.get 3 := fun _ => rfl
                -- Convert ++ cont to pure cons form (by rfl, since ++ is definitional for finite lists)
                rw [show [.localGet 6, .load32 (8:UInt32), .localGet 1, .ltU,
                          .const (1:UInt32), .and, .eqz, .br_if 1,
                          .localGet 6, .load32 (12:UInt32), .localGet 3, .ltU,
                          .const (1:UInt32), .and, .eqz, .br_if 1,
                          .localGet 6, .load32 (8:UInt32), .localSet 7] ++ cont =
                         .localGet 6 :: .load32 (8:UInt32) :: .localGet 1 :: .ltU ::
                         .const (1:UInt32) :: .and :: .eqz :: .br_if 1 ::
                         .localGet 6 :: .load32 (12:UInt32) :: .localGet 3 :: .ltU ::
                         .const (1:UInt32) :: .and :: .eqz :: .br_if 1 ::
                         .localGet 6 :: .load32 (8:UInt32) :: .localSet 7 :: cont from rfl]
                -- Now simp on pure cons form: no List.cons_append needed
                simp only
                  [exec, execOne.eq_def, Locals.set?,
                   hgv6_pre, hgv1_pre, hgv3_pre,
                   hf6, h1, h3,
                   hi_m, hj_m,
                   if_neg (show ¬(frame.toNat + UInt32.toNat (8 : UInt32) + 4 > stA.mem.pages * 65536) from by
                     rw [show UInt32.toNat (8 : UInt32) = 8 from by decide, ← hft8]; exact hbnd_fr8),
                   if_pos hi_lt_u32,
                   show (1 : UInt32) &&& 1 = 1 from by decide,
                   show (if (1 : UInt32) = 0 then (1 : UInt32) else 0) = 0 from by decide,
                   if_neg (show ¬(frame.toNat + UInt32.toNat (12 : UInt32) + 4 > stA.mem.pages * 65536) from by
                     rw [show UInt32.toNat (12 : UInt32) = 12 from by decide, ← hft12]; exact hbnd_fr12),
                   if_pos hj_lt_u32,
                   hlparams, hllocals,
                   if_neg (show ¬(7 < 6) from by omega),
                   if_pos (show (7 : Nat) < 6 + 16 from by omega),
                   show (7 : Nat) - 6 = 1 from by omega]
                rfl
              exact h_prefix_aux _
            rw [h_pre, show (15:Nat) = 14+1 from rfl, exec_block_cons, h_B1]
            simp only [List.take_zero, List.drop_zero, List.nil_append]
            -- suffix: localGet 6 ×2, load32 16 (=k), const 1, add (=k+1), store32 16 (→mem3_A), br 0
            have hgv6_suf : ∀ vs, ({locA_out_A with values := vs} : Locals).get 6 = locA_out_A.get 6 := fun _ => rfl
            have hg6_suf : locA_out_A.get 6 = some (.i32 frame) := by
              simp only [Locals.get, locA_out_A, locA_out_locs, hlparams, hllocals, List.length_set,
                         show ¬(6 < 6) from by omega, show (6:Nat) < 6+16 from by omega,
                         show (6:Nat) - 6 = 0 from by omega,
                         List.getElem?_set, show (9:Nat) ≠ 0 from by omega,
                         show (8:Nat) ≠ 0 from by omega, show (5:Nat) ≠ 0 from by omega,
                         show (3:Nat) ≠ 0 from by omega, show (2:Nat) ≠ 0 from by omega,
                         show (1:Nat) ≠ 0 from by omega, if_false]
              simpa [Locals.get, hlparams, hllocals, show ¬(6 < 6) from by omega] using hf6
            simp only [exec, execOne.eq_def,
                       show ({locA_out_A with values := locA_7.values} : Locals) = locA_out_A from rfl,
                       hgv6_suf, hg6_suf,
                       if_neg (show ¬(frame.toNat + UInt32.toNat (16 : UInt32) + 4 > stA_m2.mem.pages * 65536) from by
                         rw [show stA_m2.mem.pages = stA.mem.pages from rfl,
                             show UInt32.toNat (16 : UInt32) = 16 from by decide, ← hft16]
                         exact hbnd_fr16),
                       show stA_m2.mem.read32 (frame + (16 : UInt32)) = UInt32.ofNat k from hmem2_fr16,
                       show (1 : UInt32) + UInt32.ofNat k = UInt32.ofNat (k + 1) from by
                         rw [UInt32.add_comm]; exact hk_add1,
                       show stA_m2.mem.write32 (frame + (16 : UInt32)) (UInt32.ofNat (k + 1)) = mem3_A from by
                         simp only [stA_m2, mem3_A]; rw [← hk_add1],
                       show ({stA_m2 with mem := mem3_A} : Store Unit) = stC_A from rfl,
                       show ({locA_out_A with values := locA_out_A.values} : Locals) = locA_out_A from rfl]
          obtain ⟨f_A, h_body_A⟩ := h_body_A
          -- memory reads after path A writes
          have hread8_A : stC_A.mem.read32 (frame + 8) = UInt32.ofNat (i + 1) := by
            simp only [stC_A, mem3_A, mem2_A, mem1_A]
            rw [Mem.read32_write32_of_disjoint _ (frame + 16) (frame + 8) _
                  (by right; rw [hft16, hft8]; omega),
                Mem.read32_write32_same, hi_add1]
          have hread12_A : stC_A.mem.read32 (frame + 12) = UInt32.ofNat j := by
            simp only [stC_A, mem3_A, mem2_A, mem1_A]
            rw [Mem.read32_write32_of_disjoint _ (frame + 16) (frame + 12) _
                  (by right; rw [hft16, hft12]),
                Mem.read32_write32_of_disjoint _ (frame + 8) (frame + 12) _
                  (by left; rw [hft8, hft12]),
                Mem.read32_write32_of_disjoint _ (out_ptr + 4 * UInt32.ofNat k) (frame + 12) _
                  (by rw [hout_k_toNat, hft12];
                      rcases hframe_out_disj with h | h <;> omega),
                hj_m]
          have hread16_A : stC_A.mem.read32 (frame + 16) = UInt32.ofNat (k + 1) := by
            simp only [stC_A, mem3_A]
            rw [Mem.read32_write32_same, hk_add1]
          -- locA_out_A.get 6: local[0] unchanged (set indices 1,2,3,5,8,9 ≠ 0)
          have hf6_out_A : locA_out_A.get 6 = some (.i32 frame) := by
            simp only [locA_out_A, locA_out_locs, Locals.get, hlparams, hllocals, List.length_set,
                       show ¬ (6 < 6) from by omega,
                       show 6 < 6 + 16 from by omega,
                       show 6 - 6 = 0 from by omega,
                       List.getElem?_set,
                       show (9 : Nat) ≠ 0 from by omega,
                       show (8 : Nat) ≠ 0 from by omega,
                       show (5 : Nat) ≠ 0 from by omega,
                       show (3 : Nat) ≠ 0 from by omega,
                       show (2 : Nat) ≠ 0 from by omega,
                       show (1 : Nat) ≠ 0 from by omega,
                       if_false]
            simpa [Locals.get, hlparams, hllocals,
                   show ¬ (6 < 6) from by omega] using hf6
          have hllocals_out_A : locA_out_A.locals.length = 16 := by
            simp [locA_out_A, locA_out_locs, List.length_set, hllocals]
          -- locA_out_A.get 0..5 = locA.get 0..5: params unchanged, needs hlparams for if-branch
          have hg_eq_A : ∀ n, n < 6 → locA_out_A.get n = locA.get n := fun n hn => by
            simp only [locA_out_A, Locals.get, hlparams, if_pos hn]
          have hlparams_out_A : locA_out_A.params.length = 6 := by exact hlparams
          -- invariant restoration: (i+1, j)
          have hI_A : MergeLoopInv frame out_ptr left_ptr right_ptr n_left n_right n_out
                        i₀ j₀ k₀ st stC_A locA_out_A :=
            ⟨i + 1, j, by omega, by omega, hj_lo, hj_hi,
             hread8_A, hread12_A,
             by rw [hread16_A]; congr 1; omega,
             hf6_out_A,
             (hg_eq_A 0 (by omega)).trans h0, (hg_eq_A 1 (by omega)).trans h1,
             (hg_eq_A 2 (by omega)).trans h2, (hg_eq_A 3 (by omega)).trans h3,
             (hg_eq_A 4 (by omega)).trans h4, (hg_eq_A 5 (by omega)).trans h5,
             hlparams_out_A, hllocals_out_A, ⟨v₀, hg⟩,
             fun q hq => by
               simp only [stC_A, mem3_A, mem2_A, mem1_A]
               have hliq : (left_ptr + 4 * UInt32.ofNat q).toNat = left_ptr.toNat + 4 * q :=
                 toNat_wordAddr left_ptr n_left.toNat q hq (by linarith)
               rw [Mem.read32_write32_of_disjoint _ (frame + 16) _ _
                     (by rw [hft16, hliq]; rcases hframe_left_disj with h | h <;> omega),
                   Mem.read32_write32_of_disjoint _ (frame + 8) _ _
                     (by rw [hft8, hliq]; rcases hframe_left_disj with h | h <;> omega),
                   Mem.read32_write32_of_disjoint _ (out_ptr + 4 * UInt32.ofNat k) _ _
                     (by rw [hout_k_toNat, hliq]; rcases hleft_out_disj with h | h <;> omega)]
               exact hleft q hq,
             fun q hq => by
               simp only [stC_A, mem3_A, mem2_A, mem1_A]
               have hriq : (right_ptr + 4 * UInt32.ofNat q).toNat = right_ptr.toNat + 4 * q :=
                 toNat_wordAddr right_ptr n_right.toNat q hq (by linarith)
               rw [Mem.read32_write32_of_disjoint _ (frame + 16) _ _
                     (by rw [hft16, hriq]; rcases hframe_right_disj with h | h <;> omega),
                   Mem.read32_write32_of_disjoint _ (frame + 8) _ _
                     (by rw [hft8, hriq]; rcases hframe_right_disj with h | h <;> omega),
                   Mem.read32_write32_of_disjoint _ (out_ptr + 4 * UInt32.ofNat k) _ _
                     (by rw [hout_k_toNat, hriq]; rcases hright_out_disj with h | h <;> omega)]
               exact hright q hq,
             (by
               -- content invariant: wordsAt stC_A (out+4k₀) (W+1) ++ merge(L.drop(i+1), R.drop j)
               --                  = merge(L.drop i₀, R.drop j₀)
               -- where W = (i-i₀)+(j-j₀) and the write is at out+4k (= out+4k₀+4W)
               have hW : (i + 1 - i₀) + (j - j₀) = (i - i₀) + (j - j₀) + 1 := by omega
               rw [hW]
               -- (out_ptr + 4*k₀).toNat = out_ptr.toNat + 4*k₀
               have h_k₀_addr : (out_ptr + 4 * UInt32.ofNat k₀).toNat = out_ptr.toNat + 4 * k₀ :=
                 toNat_wordAddr out_ptr n_out.toNat k₀ (by have := hk_val; omega) (by linarith)
               -- bound for the output region
               have hout_bnd : (out_ptr + 4 * UInt32.ofNat k₀).toNat + 4 * ((i - i₀) + (j - j₀) + 1) ≤ 4294967296 := by
                 rw [h_k₀_addr]; have := hk_val; omega
               -- wordsAt stC_A (out+4k₀) (W+1) = wordsAt stA (out+4k₀) W ++ [left_i]
               have hwords : wordsAt stC_A.mem (out_ptr + 4 * UInt32.ofNat k₀) ((i - i₀) + (j - j₀) + 1) =
                   wordsAt stA.mem (out_ptr + 4 * UInt32.ofNat k₀) ((i - i₀) + (j - j₀)) ++ [left_i] := by
                 simp only [stC_A, mem3_A, mem2_A, mem1_A]
                 -- remove frame+16 and frame+8 writes (disjoint from out region)
                 rw [wordsAt_write32_of_disjoint _ _ (frame + 16) _ _ hout_bnd
                       (by rw [hft16, h_k₀_addr]; rcases hframe_out_disj with h | h <;> [left; right] <;> omega),
                     wordsAt_write32_of_disjoint _ _ (frame + 8) _ _ hout_bnd
                       (by rw [hft8, h_k₀_addr]; rcases hframe_out_disj with h | h <;> [left; right] <;> omega),
                     wordsAt_split _ _ _ ((i - i₀) + (j - j₀)) (by omega)]
                 simp only [show (i - i₀) + (j - j₀) + 1 - ((i - i₀) + (j - j₀)) = 1 from by omega]
                 congr 1
                 · -- write at out+4k disjoint from [out+4k₀, out+4k₀+4W)
                   rw [wordsAt_write32_of_disjoint _ _ (out_ptr + 4 * UInt32.ofNat k) _ _
                         (by omega)
                         (by right; rw [h_k₀_addr, hout_k_toNat]; omega)]
                 · -- write at out+4k (= out+4k₀+4W); read gives left_i
                   have hbase_W : out_ptr + 4 * UInt32.ofNat k₀ + 4 * UInt32.ofNat ((i - i₀) + (j - j₀)) =
                       out_ptr + 4 * UInt32.ofNat k := by
                     have hkeq : k₀ + ((i - i₀) + (j - j₀)) = k := by omega
                     rw [UInt32.add_assoc, ← UInt32.mul_add, ← UInt32.ofNat_add, hkeq]
                   rw [hbase_W]; simp [wordsAt, Mem.read32_write32_same]
               -- assemble: [left_i] ++ merge(L.drop(i+1), R.drop j) = left_i :: merge(...)
               rw [hwords, List.append_assoc, List.singleton_append]
               -- rewrite RHS using hcontent (reversed): merge(L.drop i₀, R.drop j₀)
               --   = wordsAt stA W ++ merge(L.drop i, R.drop j)
               conv_rhs => rw [← hcontent]
               congr 1
               -- left_i :: merge(L.drop(i+1), R.drop j) = merge(L.drop i, R.drop j)
               -- prove via merge_cons_le + List.drop_eq_getElem_cons
               have hL_drop_i : (wordsAt st.mem left_ptr n_left.toNat).drop i =
                   st.mem.read32 (left_ptr + 4 * UInt32.ofNat i) ::
                   (wordsAt st.mem left_ptr n_left.toNat).drop (i + 1) := by
                 have h1 : i < (wordsAt st.mem left_ptr n_left.toNat).length := by
                   simp [wordsAt_length]; exact hlt_i
                 rw [List.drop_eq_getElem_cons h1, wordsAt_getElem _ _ _ _ hlt_i]
               have hR_drop_j : (wordsAt st.mem right_ptr n_right.toNat).drop j =
                   st.mem.read32 (right_ptr + 4 * UInt32.ofNat j) ::
                   (wordsAt st.mem right_ptr n_right.toNat).drop (j + 1) := by
                 have h2 : j < (wordsAt st.mem right_ptr n_right.toNat).length := by
                   simp [wordsAt_length]; exact hlt_j
                 rw [List.drop_eq_getElem_cons h2, wordsAt_getElem _ _ _ _ hlt_j]
               have hleft_i_eq : left_i = st.mem.read32 (left_ptr + 4 * UInt32.ofNat i) :=
                 hleft i hlt_i
               have hle_st : st.mem.read32 (left_ptr + 4 * UInt32.ofNat i) ≤
                   st.mem.read32 (right_ptr + 4 * UInt32.ofNat j) := by
                 rw [← hleft i hlt_i, ← hright j hlt_j]; exact hle
               rw [hleft_i_eq, hL_drop_i, hR_drop_j, merge_cons_le hle_st]),
             by simp [stC_A, mem3_A, mem2_A, mem1_A, Mem.write32_pages, hpages],
             hk_global,
             by simp [stC_A, mem3_A, mem2_A, mem1_A, Mem.write32_pages, hleft_global],
             by simp [stC_A, mem3_A, mem2_A, mem1_A, Mem.write32_pages, hright_global],
             by simp [stC_A, mem3_A, mem2_A, mem1_A, Mem.write32_pages, hout_global],
             hpages_u32, hleft_out_disj, hright_out_disj, hleft_right_disj,
             hframe_left_disj, hframe_right_disj, hframe_out_disj⟩
          -- measure decrease
          have hμ_A : (n_left.toNat - (stC_A.mem.read32 (frame + 8)).toNat) +
                      (n_right.toNat - (stC_A.mem.read32 (frame + 12)).toNat) < n := by
            rw [hread8_A, hread12_A, UInt32.toNat_ofNat', UInt32.toNat_ofNat',
                Nat.mod_eq_of_lt (by have := n_left.toNat_lt; omega),
                Nat.mod_eq_of_lt (by have := n_right.toNat_lt; omega),
                ← hμ, hi_m, hj_m, UInt32.toNat_ofNat', UInt32.toNat_ofNat',
                Nat.mod_eq_of_lt (by have := n_left.toNat_lt; omega),
                Nat.mod_eq_of_lt (by have := n_right.toNat_lt; omega)]
            omega
          -- IH at reduced measure: input is (stC_A, locA_out_A)
          obtain ⟨f_rest, st₂, loc₂, hf_exec, hQ_rest, hMI_rest, hG_A, hFrm_A, hPages_A⟩ := IH _ hμ_A stC_A locA_out_A hI_A rfl
          -- Fuel composition: one body iteration at stA then IH fuel at stC_A
          have hbody_ne : exec f_A m stA locA mainMergeBody env ≠ .OutOfFuel := by
            simp [h_body_A]
          have hfuel_ne : exec f_rest m stC_A locA_out_A [.block 0 0 [.loop 0 0 mainMergeBody]] env ≠ .OutOfFuel :=
            fun h => by simp [h] at hf_exec
          have hbody_mono : exec (max f_A f_rest) m stA locA mainMergeBody env = .Break 0 stC_A locA_out_A :=
            (exec_fuel_mono (Nat.le_max_left f_A f_rest) hbody_ne).trans h_body_A
          have hblock_mono : exec (max f_A f_rest + 1) m stC_A locA_out_A [.block 0 0 [.loop 0 0 mainMergeBody]] env =
              exec f_rest m stC_A locA_out_A [.block 0 0 [.loop 0 0 mainMergeBody]] env :=
            exec_fuel_mono (by omega) hfuel_ne
          have hloop_single : ∀ F stT locT,
              exec F m stT locT [.loop 0 0 mainMergeBody] env =
              execOne F m stT locT (.loop 0 0 mainMergeBody) env := fun F stT locT => by
            cases F with
            | zero => simp [exec, execOne]
            | succ f =>
              simp only [exec]
              rcases execOne (f + 1) m stT locT (.loop 0 0 mainMergeBody) env with
                ⟨_, _⟩ | ⟨_, _, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_⟩ | _
              · rfl
              all_goals rfl
          have hloop_eq : exec (max f_A f_rest + 1) m stA locA [.loop 0 0 mainMergeBody] env =
              exec (max f_A f_rest) m stC_A locA_out_A [.loop 0 0 mainMergeBody] env := by
            rw [hloop_single, hloop_single]
            conv_lhs => rw [execOne_loop_succ]
            simp only [hbody_mono, List.take_zero, List.nil_append, List.drop_zero]
            -- {locA_out_A with values := locA.values} = locA_out_A by rfl:
            -- locA_out_A = {locA with locals := ...}, so .values = locA.values definitionally
            rfl
          have heq : exec (max f_A f_rest + 2) m stA locA [.block 0 0 [.loop 0 0 mainMergeBody]] env =
              exec (max f_A f_rest + 1) m stC_A locA_out_A [.block 0 0 [.loop 0 0 mainMergeBody]] env := by
            rw [show max f_A f_rest + 2 = max f_A f_rest + 1 + 1 from rfl]
            conv_lhs => rw [exec_block_cons, hloop_eq]
            conv_rhs => rw [exec_block_cons]
            set discr := exec (max f_A f_rest) m stC_A locA_out_A [.loop 0 0 mainMergeBody] env
            rcases discr with ⟨r', s'⟩ | ⟨n, r', s'⟩ | ⟨r', vs⟩ | ⟨r', msg⟩ | ⟨msg⟩ | _
            · simp [exec, locA_out_A, locA_out_locs]
            · cases n with | zero => simp [exec, locA_out_A, locA_out_locs] | succ k => rfl
            all_goals rfl
          have hFrm_stC_A : ∀ ix, frame.toNat + 32 ≤ ix →
              (ix < out_ptr.toNat ∨ ix ≥ out_ptr.toNat + 4 * n_out.toNat) →
              stC_A.mem.bytes ix = stA.mem.bytes ix := fun ix hix hout => by
            simp only [stC_A, mem3_A, mem2_A, mem1_A]
            rw [Mem.write32_bytes_of_disjoint _ (frame + 16) _ ix
                  (by right; rw [hft16]; omega),
                Mem.write32_bytes_of_disjoint _ (frame + 8) _ ix
                  (by right; rw [hft8]; omega),
                Mem.write32_bytes_of_disjoint _ (out_ptr + 4 * UInt32.ofNat k) _ ix
                  (by rcases hout with h | h
                      · left; rw [hout_k_toNat]; omega
                      · right; rw [hout_k_toNat]; omega)]
          have hPages_stC_A : stC_A.mem.pages = stA.mem.pages := by
            simp only [stC_A, mem3_A, mem2_A, mem1_A, Mem.write32_pages]
          exact ⟨max f_A f_rest + 2, st₂, loc₂, by rw [heq, hblock_mono]; exact hf_exec, hQ_rest, hMI_rest, hG_A, fun ix hix hout => (hFrm_A ix hix hout).trans (hFrm_stC_A ix hix hout), hPages_A.trans hPages_stC_A⟩
        · -- ── path B: left[i] > right[j]: copy right[j] to out[k], j++, k++ ──
          let mem1_B := stA.mem.write32 (out_ptr + 4 * UInt32.ofNat k) right_j
          let mem2_B := mem1_B.write32 (frame + 12) (UInt32.ofNat j + 1)
          let mem3_B := mem2_B.write32 (frame + 16) (UInt32.ofNat k + 1)
          let stC_B : Store Unit := { stA with mem := mem3_B }
          -- Result locals: localSet 7(→local[1]) 8(→local[2]) 9(→local[3])
          --                       10(→local[4]) 12(→local[6]) 13(→local[7])
          let locB_out_locs :=
            locA.locals.set 1 (.i32 (UInt32.ofNat i)) |>.set 2 (.i32 left_i)
              |>.set 3 (.i32 (UInt32.ofNat j)) |>.set 4 (.i32 (UInt32.ofNat j))
              |>.set 6 (.i32 right_j) |>.set 7 (.i32 (UInt32.ofNat k))
          let locB_out_B : Locals := { locA with locals := locB_out_locs }
          -- exec trace (staged through 14 nested blocks)
          have h_body_B : ∃ f_B,
              exec f_B m stA locA mainMergeBody env = .Break 0 stC_B locB_out_B := by
            refine ⟨15, ?_⟩
            -- ── body let-bindings (same definitions as Path A) ──
            let body14 : Program := [
              .localGet 7, .localGet 1, .ltU, .const (1:UInt32), .and, .eqz, .br_if 0,
              .localGet 0, .localGet 7, .const (2:UInt32), .shl, .add,
              .load32 (0:UInt32), .localSet 8,
              .localGet 6, .load32 (12:UInt32), .localSet 9,
              .localGet 9, .localGet 3, .ltU, .const (1:UInt32), .and, .br_if 1, .br 2]
            let body13 : Program := [.block 0 0 body14,
              .localGet 7, .localGet 1, .const (1048712:UInt32), .call 87, .unreachable]
            let body12 : Program := [.block 0 0 body13,
              .localGet 8, .localGet 2, .localGet 9, .const (2:UInt32), .shl, .add,
              .load32 (0:UInt32), .leU, .const (1:UInt32), .and, .br_if 2, .br 1]
            let body11 : Program := [.block 0 0 body12,
              .localGet 9, .localGet 3, .const (1048728:UInt32), .call 87, .unreachable]
            let body10 : Program := [.block 0 0 body11,
              .localGet 6, .load32 (12:UInt32), .localSet 10,
              .localGet 10, .localGet 3, .ltU, .const (1:UInt32), .and, .br_if 1, .br 2]
            let body9 : Program := [.block 0 0 body10,
              .localGet 6, .load32 (8:UInt32), .localSet 11,
              .localGet 11, .localGet 1, .ltU, .const (1:UInt32), .and, .br_if 4, .br 5]
            let body8 : Program := [.block 0 0 body9,
              .localGet 2, .localGet 10, .const (2:UInt32), .shl, .add,
              .load32 (0:UInt32), .localSet 12,
              .localGet 6, .load32 (16:UInt32), .localSet 13,
              .localGet 13, .localGet 5, .ltU, .const (1:UInt32), .and, .br_if 1, .br 2]
            let body7 : Program := [.block 0 0 body8,
              .localGet 10, .localGet 3, .const (1048744:UInt32), .call 87, .unreachable]
            let body6 : Program := [.block 0 0 body7,
              .localGet 4, .localGet 13, .const (2:UInt32), .shl, .add,
              .localGet 12, .store32 (0:UInt32),
              .localGet 6, .localGet 6, .load32 (12:UInt32),
              .const (1:UInt32), .add, .store32 (12:UInt32), .br 5]
            let body5 : Program := [.block 0 0 body6,
              .localGet 13, .localGet 5, .const (1048760:UInt32), .call 87, .unreachable]
            let body4 : Program := [.block 0 0 body5,
              .localGet 0, .localGet 11, .const (2:UInt32), .shl, .add,
              .load32 (0:UInt32), .localSet 14,
              .localGet 6, .load32 (16:UInt32), .localSet 15,
              .localGet 15, .localGet 5, .ltU, .const (1:UInt32), .and, .br_if 1, .br 2]
            let body3 : Program := [.block 0 0 body4,
              .localGet 11, .localGet 1, .const (1048776:UInt32), .call 87, .unreachable]
            let body2 : Program := [.block 0 0 body3,
              .localGet 4, .localGet 15, .const (2:UInt32), .shl, .add,
              .localGet 14, .store32 (0:UInt32),
              .localGet 6, .localGet 6, .load32 (8:UInt32),
              .const (1:UInt32), .add, .store32 (8:UInt32), .br 1]
            let body1 : Program := [.block 0 0 body2,
              .localGet 15, .localGet 5, .const (1048792:UInt32), .call 87, .unreachable]
            -- ── intermediate Locals states ──
            let locA_7 : Locals :=
              { locA with locals := locA.locals.set 1 (.i32 (UInt32.ofNat i)) }
            let locA_89_locs :=
              locA.locals.set 1 (.i32 (UInt32.ofNat i)) |>.set 2 (.i32 left_i)
                |>.set 3 (.i32 (UInt32.ofNat j))
            let locA_89 : Locals := { locA with locals := locA_89_locs }
            -- Path B: after body10 localSet 10: local[4] = j
            let locA_10_B : Locals :=
              { locA with locals := locA_89_locs.set 4 (.i32 (UInt32.ofNat j)) }
            -- Path B: after body8 localSet 12,13: local[6]=right_j, local[7]=k
            let locA_1213_B_locs :=
              locA_89_locs.set 4 (.i32 (UInt32.ofNat j))
                |>.set 6 (.i32 right_j) |>.set 7 (.i32 (UInt32.ofNat k))
            let locA_1213_B : Locals := { locA with locals := locA_1213_B_locs }
            -- store after B6: out[k]=right_j written, frame+12=j+1 written
            let stA_m2_B : Store Unit := { stA with mem := mem2_B }
            -- ── auxiliary lemmas ──
            have hi_lt_u32 : UInt32.ofNat i < n_left := by
              rw [UInt32.lt_iff_toNat_lt_toNat, UInt32.toNat_ofNat']
              have := n_left.toNat_lt; omega
            have hj_lt_u32 : UInt32.ofNat j < n_right := by
              rw [UInt32.lt_iff_toNat_lt_toNat, UInt32.toNat_ofNat']
              have := n_right.toNat_lt; omega
            have hk_lt_u32 : UInt32.ofNat k < n_out := by
              rw [UInt32.lt_iff_toNat_lt_toNat, UInt32.toNat_ofNat']
              have := n_out.toNat_lt; omega
            have hbnd_out_k : ¬((out_ptr + 4 * UInt32.ofNat k).toNat + 4 > stA.mem.pages * 65536) := by
              rw [hout_k_toNat]; omega
            have hbnd_fr8 : ¬((frame + 8).toNat + 4 > stA.mem.pages * 65536) := by
              rw [hft8]; omega
            have hbnd_fr12 : ¬((frame + 12).toNat + 4 > stA.mem.pages * 65536) := by
              rw [hft12]; omega
            have hbnd_fr16 : ¬((frame + 16).toNat + 4 > stA.mem.pages * 65536) := by
              rw [hft16]; omega
            have hbnd_left_i : ¬((left_ptr + 4 * UInt32.ofNat i).toNat + 4 > stA.mem.pages * 65536) := by
              rw [toNat_wordAddr left_ptr n_left.toNat i hlt_i (by linarith)]; omega
            have hbnd_right_j : ¬((right_ptr + 4 * UInt32.ofNat j).toNat + 4 > stA.mem.pages * 65536) := by
              rw [toNat_wordAddr right_ptr n_right.toNat j hlt_j (by linarith)]; omega
            have hmem1_B_fr12 : mem1_B.read32 (frame + 12) = UInt32.ofNat j := by
              simp only [mem1_B,
                Mem.read32_write32_of_disjoint _ (out_ptr + 4 * UInt32.ofNat k) (frame + 12) _
                  (by rw [hout_k_toNat, hft12]; rcases hframe_out_disj with h | h <;> omega)]
              exact hj_m
            have hmem2_B_fr16 : mem2_B.read32 (frame + 16) = UInt32.ofNat k := by
              simp only [mem2_B,
                Mem.read32_write32_of_disjoint _ (frame + 12) (frame + 16) _
                  (by left; rw [hft12, hft16])]
              simp only [mem1_B,
                Mem.read32_write32_of_disjoint _ (out_ptr + 4 * UInt32.ofNat k) (frame + 16) _
                  (by rw [hout_k_toNat, hft16]; rcases hframe_out_disj with h | h <;> omega)]
              exact hk_m
            -- ── exec chain through 14 blocks ──
            -- body14: same as Path A (loads left_i→local8, j→local9; br_if 1 fires) → Break 1
            have h_B14_B : exec 1 m stA locA_7 body14 env = .Break 1 stA locA_89 := by
              have hgv7_7 : ∀ vs, ({locA_7 with values := vs} : Locals).get 7 = locA_7.get 7 := fun _ => rfl
              have hgv1_7 : ∀ vs, ({locA_7 with values := vs} : Locals).get 1 = locA_7.get 1 := fun _ => rfl
              have hgv0_7 : ∀ vs, ({locA_7 with values := vs} : Locals).get 0 = locA_7.get 0 := fun _ => rfl
              have hgv6_7 : ∀ vs, ({locA_7 with values := vs} : Locals).get 6 = locA_7.get 6 := fun _ => rfl
              have hgv3_7 : ∀ vs, ({locA_7 with values := vs} : Locals).get 3 = locA_7.get 3 := fun _ => rfl
              have hlp_7 : locA_7.params.length = 6  := hlparams
              have hll_7 : locA_7.locals.length = 16 := by simp [locA_7, List.length_set, hllocals]
              have hg7_7 : locA_7.get 7 = some (.i32 (UInt32.ofNat i)) := by
                simp only [Locals.get, hlp_7, hll_7, List.length_set,
                           show ¬(7 < 6) from by omega, show (7 : Nat) < 6 + 16 from by omega,
                           show (7 : Nat) - 6 = 1 from by omega]
                change (locA.locals.set 1 (.i32 (UInt32.ofNat i)))[1]? = _
                exact List.getElem?_set_self (by rw [hllocals]; norm_num)
              have hg1_7 : locA_7.get 1 = some (.i32 n_left) := by
                simp only [Locals.get, locA_7, hlparams, show (1 : Nat) < 6 from by omega] at h1 ⊢
                exact h1
              have hg0_7 : locA_7.get 0 = some (.i32 left_ptr) := by
                simp only [Locals.get, locA_7, hlparams, show (0 : Nat) < 6 from by omega] at h0 ⊢
                exact h0
              have hg6_7 : locA_7.get 6 = some (.i32 frame) := by
                have h : locA_7.get 6 = locA.get 6 := by
                  simp [locA_7, Locals.get, hlparams, hllocals, List.length_set, List.getElem?_set]
                rw [h]; exact hf6
              have hg3_7 : locA_7.get 3 = some (.i32 n_right) := by
                simp only [Locals.get, locA_7, hlparams, show (3 : Nat) < 6 from by omega] at h3 ⊢
                exact h3
              have hg6_8_raw : ∀ vs,
                  (Locals.mk locA_7.params (locA_7.locals.set 2 (.i32 left_i)) vs).get 6
                  = some (.i32 frame) := by
                intro vs
                have h : (Locals.mk locA_7.params (locA_7.locals.set 2 (.i32 left_i)) vs).get 6
                    = locA.get 6 := by
                  simp [locA_7, Locals.get, hlparams, hllocals, List.length_set, List.getElem?_set]
                rw [h]; exact hf6
              have hg9_89_raw : ∀ vs,
                  (Locals.mk locA_7.params
                    ((locA_7.locals.set 2 (.i32 left_i)).set 3 (.i32 (UInt32.ofNat j))) vs).get 9
                  = some (.i32 (UInt32.ofNat j)) := by
                intro vs
                simp only [Locals.get, hlp_7, hll_7, List.length_set,
                           show ¬(9 < 6) from by omega, show (9 : Nat) < 6 + 16 from by omega,
                           show (9 : Nat) - 6 = 3 from by omega]
                exact List.getElem?_set_self (by simp [List.length_set, hll_7])
              have hg3_89_raw : ∀ vs,
                  (Locals.mk locA_7.params
                    ((locA_7.locals.set 2 (.i32 left_i)).set 3 (.i32 (UInt32.ofNat j))) vs).get 3
                  = some (.i32 n_right) := by
                intro vs
                have h3_raw : locA.params[3]? = some (.i32 n_right) := by
                  have h := h3
                  simp only [Locals.get, hlparams, show (3 : Nat) < 6 from by omega] at h
                  exact h
                simp only [Locals.get, hlp_7, show (3 : Nat) < 6 from by omega]
                exact h3_raw
              have hshl_i : UInt32.ofNat i <<< ((2 : UInt32) % 32) = 4 * UInt32.ofNat i := by
                rw [show (2 : UInt32) % 32 = 2 from by decide]
                apply UInt32.toNat_inj.mp
                have hi_bnd : i < 2 ^ 30 := by have := n_left.toNat_lt; omega
                simp only [UInt32.toNat_mul, UInt32.toNat_ofNat',
                           show (4 : UInt32).toNat = 4 from rfl,
                           Nat.mod_eq_of_lt (show i < 4294967296 from by omega),
                           Nat.mod_eq_of_lt (show i * 4 < 4294967296 from by omega)]
                simp [UInt32.shiftLeft, Fin.shiftLeft, Nat.shiftLeft_eq]; omega
              have hshl_j_14 : UInt32.ofNat j <<< ((2 : UInt32) % 32) = 4 * UInt32.ofNat j := by
                rw [show (2 : UInt32) % 32 = 2 from by decide]
                apply UInt32.toNat_inj.mp
                have hj_bnd : j < 2 ^ 30 := by have := n_right.toNat_lt; omega
                simp only [UInt32.toNat_mul, UInt32.toNat_ofNat',
                           show (4 : UInt32).toNat = 4 from rfl,
                           Nat.mod_eq_of_lt (show j < 4294967296 from by omega),
                           Nat.mod_eq_of_lt (show j * 4 < 4294967296 from by omega)]
                simp [UInt32.shiftLeft, Fin.shiftLeft, Nat.shiftLeft_eq]; omega
              simp only [exec, execOne.eq_def, body14, Locals.set?,
                         hgv7_7, hgv1_7, hgv0_7, hgv6_7, hgv3_7,
                         hg7_7, hg1_7, hg0_7, hg6_7, hg3_7,
                         if_pos hi_lt_u32,
                         show (1 : UInt32) &&& 1 = 1 from by decide,
                         show (if (1 : UInt32) = 0 then (1 : UInt32) else 0) = 0 from by decide,
                         hshl_i,
                         if_neg (show ¬((4 * UInt32.ofNat i + left_ptr).toNat +
                                         UInt32.toNat (0 : UInt32) + 4 > stA.mem.pages * 65536) from by
                                   rw [show 4 * UInt32.ofNat i + left_ptr =
                                           left_ptr + 4 * UInt32.ofNat i from UInt32.add_comm _ _,
                                       show UInt32.toNat (0 : UInt32) = 0 from rfl]; omega),
                         show stA.mem.read32 (4 * UInt32.ofNat i + left_ptr + (0 : UInt32)) = left_i from by
                           rw [show 4 * UInt32.ofNat i + left_ptr + (0 : UInt32) =
                                   left_ptr + 4 * UInt32.ofNat i from by
                               rw [UInt32.add_comm (4 * UInt32.ofNat i) left_ptr, UInt32.add_zero]],
                         hlp_7, hll_7, List.length_set,
                         if_neg (show ¬(8 < 6) from by omega),
                         if_pos (show (8 : Nat) < 6 + 16 from by omega),
                         show (8 : Nat) - 6 = 2 from by omega,
                         hg6_8_raw,
                         if_neg (show ¬(frame.toNat + (12 : UInt32).toNat + 4 > stA.mem.pages * 65536)
                                   from by simp only [show (12 : UInt32).toNat = 12 from by decide]; omega),
                         show stA.mem.read32 (frame + (12 : UInt32)) = UInt32.ofNat j from hj_m,
                         if_neg (show ¬(9 < 6) from by omega),
                         if_pos (show (9 : Nat) < 6 + 16 from by omega),
                         show (9 : Nat) - 6 = 3 from by omega,
                         hg9_89_raw, hg3_89_raw,
                         if_pos hj_lt_u32,
                         show (1 : UInt32) &&& 1 = 1 from by decide,
                         show Locals.mk locA_7.params
                               ((locA_7.locals.set 2 (.i32 left_i)).set 3 (.i32 (UInt32.ofNat j)))
                               locA.values = locA_89 from rfl]
              rfl
            -- body13: Break(0+1) from body14 → Break 0
            have h_B13_B : exec 2 m stA locA_7 body13 env = .Break 0 stA locA_89 := by
              rw [show (2:Nat) = 1+1 from rfl, exec_block_cons, h_B14_B]
            -- body12: ¬hle (left_i > right_j): br_if 2 NOT taken, br 1 → Break 1
            have h_B12_B : exec 3 m stA locA_7 body12 env = .Break 1 stA locA_89 := by
              rw [show (3:Nat) = 2+1 from rfl, exec_block_cons, h_B13_B]
              simp only [List.take_zero, List.drop_zero, List.nil_append]
              have hll_89 : locA_89.locals.length = 16 := by
                simp [locA_89, locA_89_locs, List.length_set, hllocals]
              have hgv8_89 : ∀ vs, ({locA_89 with values := vs} : Locals).get 8 = locA_89.get 8 := fun _ => rfl
              have hgv2_89 : ∀ vs, ({locA_89 with values := vs} : Locals).get 2 = locA_89.get 2 := fun _ => rfl
              have hgv9_89 : ∀ vs, ({locA_89 with values := vs} : Locals).get 9 = locA_89.get 9 := fun _ => rfl
              have hg8_89 : locA_89.get 8 = some (.i32 left_i) := by
                simp only [Locals.get, locA_89, locA_89_locs, hlparams, hllocals, List.length_set,
                           show ¬(8 < 6) from by omega, show (8:Nat) < 6+16 from by omega,
                           show (8:Nat) - 6 = 2 from by omega]
                rw [List.getElem?_set_ne (show (3:Nat) ≠ 2 from by omega)]
                exact List.getElem?_set_self (by rw [List.length_set, hllocals]; norm_num)
              have hg2_89 : locA_89.get 2 = some (.i32 right_ptr) := by
                simp only [Locals.get, locA_89, hlparams, show (2:Nat) < 6 from by omega] at h2 ⊢
                exact h2
              have hg9_89 : locA_89.get 9 = some (.i32 (UInt32.ofNat j)) := by
                simp only [Locals.get, locA_89, locA_89_locs, hlparams, hllocals, List.length_set,
                           show ¬(9 < 6) from by omega, show (9:Nat) < 6+16 from by omega,
                           show (9:Nat) - 6 = 3 from by omega]
                exact List.getElem?_set_self (by rw [List.length_set, List.length_set, hllocals]; norm_num)
              have hshl_j : UInt32.ofNat j <<< ((2:UInt32) % 32) = 4 * UInt32.ofNat j := by
                rw [show (2:UInt32) % 32 = 2 from by decide]
                apply UInt32.toNat_inj.mp
                have hj_bnd : j < 2^30 := by have := n_right.toNat_lt; omega
                simp only [UInt32.toNat_mul, UInt32.toNat_ofNat',
                           show (4:UInt32).toNat = 4 from rfl,
                           Nat.mod_eq_of_lt (show j < 4294967296 from by omega),
                           Nat.mod_eq_of_lt (show j*4 < 4294967296 from by omega)]
                simp [UInt32.shiftLeft, Fin.shiftLeft, Nat.shiftLeft_eq]; omega
              simp only [exec, execOne.eq_def,
                         show ({locA_89 with values := locA_7.values} : Locals) = locA_89 from rfl,
                         hgv8_89, hgv2_89, hgv9_89,
                         hg8_89, hg2_89, hg9_89,
                         hshl_j,
                         if_neg (show ¬((4 * UInt32.ofNat j + right_ptr).toNat +
                                         UInt32.toNat (0:UInt32) + 4 > stA.mem.pages * 65536) from by
                                   rw [show 4 * UInt32.ofNat j + right_ptr =
                                               right_ptr + 4 * UInt32.ofNat j from UInt32.add_comm _ _,
                                       show UInt32.toNat (0:UInt32) = 0 from rfl]
                                   exact hbnd_right_j),
                         show stA.mem.read32 (4 * UInt32.ofNat j + right_ptr + (0:UInt32)) = right_j from by
                             rw [show 4 * UInt32.ofNat j + right_ptr + (0:UInt32) =
                                         right_ptr + 4 * UInt32.ofNat j from by
                                     rw [UInt32.add_comm (4 * UInt32.ofNat j) right_ptr, UInt32.add_zero]],
                         if_neg hle,
                         show (1:UInt32) &&& 0 = 0 from by decide,
                         show ({locA_89 with values := locA.values} : Locals) = locA_89 from rfl]
            -- body11: Break(0+1) from body12 → Break 0
            have h_B11_B : exec 4 m stA locA_7 body11 env = .Break 0 stA locA_89 := by
              rw [show (4:Nat) = 3+1 from rfl, exec_block_cons, h_B12_B]
            -- body10: Break 0 → B10_right_cont: localGet6, load32_12(j)→localSet10, j<n_right br_if1 → Break 1
            have h_B10_B : exec 5 m stA locA_7 body10 env = .Break 1 stA locA_10_B := by
              rw [show (5:Nat) = 4+1 from rfl, exec_block_cons, h_B11_B]
              simp only [List.take_zero, List.drop_zero, List.nil_append]
              have hlp_89 : locA_89.params.length = 6 := hlparams
              have hll_89 : locA_89.locals.length = 16 := by
                simp [locA_89, locA_89_locs, List.length_set, hllocals]
              have hgv6_89 : ∀ vs, ({locA_89 with values := vs} : Locals).get 6 = locA_89.get 6 := fun _ => rfl
              have hg6_89 : locA_89.get 6 = some (.i32 frame) := by
                simp only [Locals.get, locA_89, locA_89_locs, hlparams, hllocals, List.length_set,
                           show ¬(6 < 6) from by omega, show (6:Nat) < 6+16 from by omega,
                           show (6:Nat) - 6 = 0 from by omega]
                rw [List.getElem?_set_ne (show (3:Nat) ≠ 0 from by omega)]
                rw [List.getElem?_set_ne (show (2:Nat) ≠ 0 from by omega)]
                rw [List.getElem?_set_ne (show (1:Nat) ≠ 0 from by omega)]
                simpa [Locals.get, hlparams, hllocals, show ¬(6 < 6) from by omega] using hf6
              have hgv10_10B : ∀ vs, ({locA_10_B with values := vs} : Locals).get 10 = locA_10_B.get 10 := fun _ => rfl
              have hgv3_10B  : ∀ vs, ({locA_10_B with values := vs} : Locals).get 3  = locA_10_B.get 3  := fun _ => rfl
              have hg10_10B : locA_10_B.get 10 = some (.i32 (UInt32.ofNat j)) := by
                simp only [Locals.get, locA_10_B, locA_89_locs, hlparams, hllocals, List.length_set,
                           show ¬(10 < 6) from by omega, show (10:Nat) < 6+16 from by omega,
                           show (10:Nat) - 6 = 4 from by omega]
                exact List.getElem?_set_self
                  (by rw [List.length_set, List.length_set, List.length_set, hllocals]; norm_num)
              have hg3_10B : locA_10_B.get 3 = some (.i32 n_right) := by
                simp only [Locals.get, locA_10_B, hlparams, show (3:Nat) < 6 from by omega] at h3 ⊢
                exact h3
              simp only [exec, execOne.eq_def,
                         show ({locA_89 with values := locA_7.values} : Locals) = locA_89 from rfl,
                         hgv6_89, hg6_89,
                         if_neg (show ¬(frame.toNat + UInt32.toNat (12:UInt32) + 4 > stA.mem.pages * 65536) from by
                                   simp only [show (12:UInt32).toNat = 12 from by decide]; omega),
                         show stA.mem.read32 (frame + (12:UInt32)) = UInt32.ofNat j from hj_m,
                         Locals.set?,
                         hlp_89, hll_89, List.length_set,
                         if_neg (show ¬(10 < 6) from by omega),
                         if_pos (show (10:Nat) < 6+16 from by omega),
                         show (10:Nat) - 6 = 4 from by omega,
                         show Locals.mk locA_89.params (locA_89.locals.set 4 (.i32 (UInt32.ofNat j)))
                               locA_89.values = locA_10_B from rfl,
                         hgv10_10B, hg10_10B, hgv3_10B, hg3_10B,
                         if_pos hj_lt_u32,
                         show (1:UInt32) &&& 1 = 1 from by decide,
                         show ({locA_10_B with values := locA_10_B.values} : Locals) = locA_10_B from rfl]
              rfl
            -- body9: Break(0+1) from body10 → Break 0
            have h_B9_B : exec 6 m stA locA_7 body9 env = .Break 0 stA locA_10_B := by
              rw [show (6:Nat) = 5+1 from rfl, exec_block_cons, h_B10_B]
            -- body8: Break 0 → B8_right_load: load right[j]→local12, k→local13, k<n_out br_if1 → Break 1
            have h_B8_B : exec 7 m stA locA_7 body8 env = .Break 1 stA locA_1213_B := by
              rw [show (7:Nat) = 6+1 from rfl, exec_block_cons, h_B9_B]
              simp only [List.take_zero, List.drop_zero, List.nil_append]
              have hlp_10B : locA_10_B.params.length = 6 := hlparams
              have hll_10B : locA_10_B.locals.length = 16 := by
                simp [locA_10_B, locA_89_locs, List.length_set, hllocals]
              have hgv2_10B  : ∀ vs, ({locA_10_B with values := vs} : Locals).get 2  = locA_10_B.get 2  := fun _ => rfl
              have hgv10_10B : ∀ vs, ({locA_10_B with values := vs} : Locals).get 10 = locA_10_B.get 10 := fun _ => rfl
              have hg2_10B : locA_10_B.get 2 = some (.i32 right_ptr) := by
                simp only [Locals.get, locA_10_B, hlparams, show (2:Nat) < 6 from by omega] at h2 ⊢
                exact h2
              have hg10_10B : locA_10_B.get 10 = some (.i32 (UInt32.ofNat j)) := by
                simp only [Locals.get, locA_10_B, locA_89_locs, hlparams, hllocals, List.length_set,
                           show ¬(10 < 6) from by omega, show (10:Nat) < 6+16 from by omega,
                           show (10:Nat) - 6 = 4 from by omega]
                exact List.getElem?_set_self
                  (by rw [List.length_set, List.length_set, List.length_set, hllocals]; norm_num)
              have hshl_j : UInt32.ofNat j <<< ((2:UInt32) % 32) = 4 * UInt32.ofNat j := by
                rw [show (2:UInt32) % 32 = 2 from by decide]
                apply UInt32.toNat_inj.mp
                have hj_bnd : j < 2^30 := by have := n_right.toNat_lt; omega
                simp only [UInt32.toNat_mul, UInt32.toNat_ofNat',
                           show (4:UInt32).toNat = 4 from rfl,
                           Nat.mod_eq_of_lt (show j < 4294967296 from by omega),
                           Nat.mod_eq_of_lt (show j*4 < 4294967296 from by omega)]
                simp [UInt32.shiftLeft, Fin.shiftLeft, Nat.shiftLeft_eq]; omega
              have hg6_12B_raw : ∀ vs,
                  (Locals.mk locA_10_B.params (locA_10_B.locals.set 6 (.i32 right_j)) vs).get 6
                  = some (.i32 frame) := by
                intro vs
                have h : (Locals.mk locA_10_B.params (locA_10_B.locals.set 6 (.i32 right_j)) vs).get 6
                    = locA.get 6 := by
                  simp [locA_10_B, locA_89_locs, Locals.get, hlparams, hllocals,
                        List.length_set, List.getElem?_set]
                rw [h]; exact hf6
              have hg13_1213_raw : ∀ vs,
                  (Locals.mk locA_10_B.params
                    ((locA_10_B.locals.set 6 (.i32 right_j)).set 7 (.i32 (UInt32.ofNat k))) vs).get 13
                  = some (.i32 (UInt32.ofNat k)) := by
                intro vs
                simp only [Locals.get, hlp_10B, hll_10B, List.length_set,
                           show ¬(13 < 6) from by omega, show (13:Nat) < 6+16 from by omega,
                           show (13:Nat) - 6 = 7 from by omega]
                exact List.getElem?_set_self (by simp [List.length_set, hll_10B])
              have hg5_1213_raw : ∀ vs,
                  (Locals.mk locA_10_B.params
                    ((locA_10_B.locals.set 6 (.i32 right_j)).set 7 (.i32 (UInt32.ofNat k))) vs).get 5
                  = some (.i32 n_out) := by
                intro vs
                have h5_raw : locA.params[5]? = some (.i32 n_out) := by
                  have h := h5
                  simp only [Locals.get, hlparams, show (5:Nat) < 6 from by omega] at h
                  exact h
                simp only [Locals.get, hlp_10B, show (5:Nat) < 6 from by omega]
                exact h5_raw
              simp only [exec, execOne.eq_def,
                         show ({locA_10_B with values := locA_7.values} : Locals) = locA_10_B from rfl,
                         hgv2_10B, hg2_10B, hgv10_10B, hg10_10B,
                         hshl_j,
                         if_neg (show ¬((4 * UInt32.ofNat j + right_ptr).toNat +
                                         UInt32.toNat (0:UInt32) + 4 > stA.mem.pages * 65536) from by
                                   rw [show 4 * UInt32.ofNat j + right_ptr =
                                               right_ptr + 4 * UInt32.ofNat j from UInt32.add_comm _ _,
                                       show UInt32.toNat (0:UInt32) = 0 from rfl]
                                   exact hbnd_right_j),
                         show stA.mem.read32 (4 * UInt32.ofNat j + right_ptr + (0:UInt32)) = right_j from by
                             rw [show 4 * UInt32.ofNat j + right_ptr + (0:UInt32) =
                                         right_ptr + 4 * UInt32.ofNat j from by
                                     rw [UInt32.add_comm (4 * UInt32.ofNat j) right_ptr, UInt32.add_zero]],
                         Locals.set?,
                         hlp_10B, hll_10B, List.length_set,
                         if_neg (show ¬(12 < 6) from by omega),
                         if_pos (show (12:Nat) < 6+16 from by omega),
                         show (12:Nat) - 6 = 6 from by omega,
                         hg6_12B_raw,
                         if_neg (show ¬(frame.toNat + UInt32.toNat (16:UInt32) + 4 > stA.mem.pages * 65536) from by
                                   simp only [show (16:UInt32).toNat = 16 from by decide]; omega),
                         show stA.mem.read32 (frame + (16:UInt32)) = UInt32.ofNat k from hk_m,
                         if_neg (show ¬(13 < 6) from by omega),
                         if_pos (show (13:Nat) < 6+16 from by omega),
                         show (13:Nat) - 6 = 7 from by omega,
                         hg13_1213_raw, hg5_1213_raw,
                         if_pos hk_lt_u32,
                         show (1:UInt32) &&& 1 = 1 from by decide,
                         show Locals.mk locA_10_B.params
                               ((locA_10_B.locals.set 6 (.i32 right_j)).set 7 (.i32 (UInt32.ofNat k)))
                               locA.values = locA_1213_B from rfl]
              rfl
            -- body7: Break(0+1) from body8 → Break 0
            have h_B7_B : exec 8 m stA locA_7 body7 env = .Break 0 stA locA_1213_B := by
              rw [show (8:Nat) = 7+1 from rfl, exec_block_cons, h_B8_B]
            -- body6: Break 0 → B6_right_store: write out[k]=right_j, frame+12=j+1, br 5 → Break 5
            have h_B6_B : exec 9 m stA locA_7 body6 env = .Break 5 stA_m2_B locA_1213_B := by
              rw [show (9:Nat) = 8+1 from rfl, exec_block_cons, h_B7_B]
              simp only [List.take_zero, List.drop_zero, List.nil_append]
              have hgv4_1213  : ∀ vs, ({locA_1213_B with values := vs} : Locals).get 4  = locA_1213_B.get 4  := fun _ => rfl
              have hgv13_1213 : ∀ vs, ({locA_1213_B with values := vs} : Locals).get 13 = locA_1213_B.get 13 := fun _ => rfl
              have hgv12_1213 : ∀ vs, ({locA_1213_B with values := vs} : Locals).get 12 = locA_1213_B.get 12 := fun _ => rfl
              have hgv6_1213  : ∀ vs, ({locA_1213_B with values := vs} : Locals).get 6  = locA_1213_B.get 6  := fun _ => rfl
              have hg4_1213 : locA_1213_B.get 4 = some (.i32 out_ptr) := by
                simp only [Locals.get, locA_1213_B, hlparams, show (4:Nat) < 6 from by omega] at h4 ⊢
                exact h4
              have hg13_1213 : locA_1213_B.get 13 = some (.i32 (UInt32.ofNat k)) := by
                simp only [Locals.get, locA_1213_B, locA_1213_B_locs, locA_89_locs,
                           hlparams, hllocals, List.length_set,
                           show ¬(13 < 6) from by omega, show (13:Nat) < 6+16 from by omega,
                           show (13:Nat) - 6 = 7 from by omega]
                exact List.getElem?_set_self
                  (by rw [List.length_set, List.length_set, List.length_set,
                           List.length_set, List.length_set, hllocals]; norm_num)
              have hg12_1213 : locA_1213_B.get 12 = some (.i32 right_j) := by
                simp only [Locals.get, locA_1213_B, locA_1213_B_locs, locA_89_locs,
                           hlparams, hllocals, List.length_set,
                           show ¬(12 < 6) from by omega, show (12:Nat) < 6+16 from by omega,
                           show (12:Nat) - 6 = 6 from by omega]
                rw [List.getElem?_set_ne (show (7:Nat) ≠ 6 from by omega)]
                exact List.getElem?_set_self
                  (by rw [List.length_set, List.length_set, List.length_set, List.length_set, hllocals]; norm_num)
              have hg6_1213 : locA_1213_B.get 6 = some (.i32 frame) := by
                simp only [Locals.get, locA_1213_B, locA_1213_B_locs, locA_89_locs,
                           hlparams, hllocals, List.length_set,
                           show ¬(6 < 6) from by omega, show (6:Nat) < 6+16 from by omega,
                           show (6:Nat) - 6 = 0 from by omega,
                           List.getElem?_set, show (7:Nat) ≠ 0 from by omega,
                           show (6:Nat) ≠ 0 from by omega, show (4:Nat) ≠ 0 from by omega,
                           show (3:Nat) ≠ 0 from by omega, show (2:Nat) ≠ 0 from by omega,
                           show (1:Nat) ≠ 0 from by omega, if_false]
                simpa [Locals.get, hlparams, hllocals, show ¬(6 < 6) from by omega] using hf6
              have hshl_k : UInt32.ofNat k <<< ((2:UInt32) % 32) = 4 * UInt32.ofNat k := by
                rw [show (2:UInt32) % 32 = 2 from by decide]
                apply UInt32.toNat_inj.mp
                have hk_bnd : k < 2^30 := by have := n_out.toNat_lt; omega
                simp only [UInt32.toNat_mul, UInt32.toNat_ofNat',
                           show (4:UInt32).toNat = 4 from rfl,
                           Nat.mod_eq_of_lt (show k < 4294967296 from by omega),
                           Nat.mod_eq_of_lt (show k * 4 < 4294967296 from by omega)]
                simp [UInt32.shiftLeft, Fin.shiftLeft, Nat.shiftLeft_eq]; omega
              simp only [exec, execOne.eq_def,
                         show ({locA_1213_B with values := locA_7.values} : Locals) = locA_1213_B from rfl,
                         hgv4_1213, hg4_1213, hgv13_1213, hg13_1213,
                         hshl_k,
                         if_neg (show ¬((4 * UInt32.ofNat k + out_ptr).toNat +
                                         UInt32.toNat (0:UInt32) + 4 > stA.mem.pages * 65536) from by
                                   rw [show 4 * UInt32.ofNat k + out_ptr =
                                               out_ptr + 4 * UInt32.ofNat k from UInt32.add_comm _ _,
                                       show UInt32.toNat (0:UInt32) = 0 from rfl]; omega),
                         show stA.mem.write32 (4 * UInt32.ofNat k + out_ptr + (0:UInt32)) right_j = mem1_B from by
                             rw [show 4 * UInt32.ofNat k + out_ptr + (0:UInt32) =
                                         out_ptr + 4 * UInt32.ofNat k from by
                                     rw [UInt32.add_comm (4 * UInt32.ofNat k) out_ptr, UInt32.add_zero]],
                         hgv12_1213, hg12_1213,
                         hgv6_1213, hg6_1213,
                         if_neg (show ¬(frame.toNat + UInt32.toNat (12:UInt32) + 4 >
                                         {stA with mem := mem1_B}.mem.pages * 65536) from by
                                   rw [show ({stA with mem := mem1_B} : Store Unit).mem.pages =
                                         stA.mem.pages from rfl,
                                       show UInt32.toNat (12:UInt32) = 12 from by decide, hft12.symm]
                                   exact hbnd_fr12),
                         show ({stA with mem := mem1_B} : Store Unit).mem.read32 (frame + (12:UInt32)) =
                               UInt32.ofNat j from hmem1_B_fr12,
                         show (1:UInt32) + UInt32.ofNat j = UInt32.ofNat j + 1 from UInt32.add_comm _ _,
                         if_neg (show ¬(frame.toNat + UInt32.toNat (12:UInt32) + 4 >
                                         {stA with mem := mem1_B}.mem.pages * 65536) from by
                                   rw [show ({stA with mem := mem1_B} : Store Unit).mem.pages =
                                         stA.mem.pages from rfl,
                                       show UInt32.toNat (12:UInt32) = 12 from by decide, hft12.symm]
                                   exact hbnd_fr12),
                         show ({stA with mem := mem1_B} : Store Unit).mem.write32
                               (frame + (12:UInt32)) (UInt32.ofNat j + 1) = mem2_B from rfl,
                         show ({stA with mem := mem2_B} : Store Unit) = stA_m2_B from rfl,
                         show ({locA_1213_B with values := locA_1213_B.values} : Locals) = locA_1213_B from rfl]
            -- body5: Break(4+1) → Break 4
            have h_B5_B : exec 10 m stA locA_7 body5 env = .Break 4 stA_m2_B locA_1213_B := by
              rw [show (10:Nat) = 9+1 from rfl, exec_block_cons, h_B6_B]
            -- body4: Break(3+1) → Break 3
            have h_B4_B : exec 11 m stA locA_7 body4 env = .Break 3 stA_m2_B locA_1213_B := by
              rw [show (11:Nat) = 10+1 from rfl, exec_block_cons, h_B5_B]
            -- body3: Break(2+1) → Break 2
            have h_B3_B : exec 12 m stA locA_7 body3 env = .Break 2 stA_m2_B locA_1213_B := by
              rw [show (12:Nat) = 11+1 from rfl, exec_block_cons, h_B4_B]
            -- body2: Break(1+1) → Break 1
            have h_B2_B : exec 13 m stA locA_7 body2 env = .Break 1 stA_m2_B locA_1213_B := by
              rw [show (13:Nat) = 12+1 from rfl, exec_block_cons, h_B3_B]
            -- body1: Break(0+1) → Break 0
            have h_B1_B : exec 14 m stA locA_7 body1 env = .Break 0 stA_m2_B locA_1213_B := by
              rw [show (14:Nat) = 13+1 from rfl, exec_block_cons, h_B2_B]
            -- ── assemble: prefix → outer block (h_B1_B) → suffix ──
            have h_pre_B : exec 15 m stA locA mainMergeBody env =
                exec 15 m stA locA_7
                  (.block 0 0 body1 :: [.localGet 6, .localGet 6, .load32 (16:UInt32),
                    .const (1:UInt32), .add, .store32 (16:UInt32), .br 0]) env := by
              have h_prefix_aux : ∀ cont : Program,
                  exec 15 m stA locA
                    ([.localGet 6, .load32 (8:UInt32), .localGet 1, .ltU,
                      .const (1:UInt32), .and, .eqz, .br_if 1,
                      .localGet 6, .load32 (12:UInt32), .localGet 3, .ltU,
                      .const (1:UInt32), .and, .eqz, .br_if 1,
                      .localGet 6, .load32 (8:UInt32), .localSet 7] ++ cont) env
                    = exec 15 m stA locA_7 cont env := by
                intro cont
                have hgv6_pre : ∀ vs, ({locA with values := vs} : Locals).get 6 = locA.get 6 := fun _ => rfl
                have hgv1_pre : ∀ vs, ({locA with values := vs} : Locals).get 1 = locA.get 1 := fun _ => rfl
                have hgv3_pre : ∀ vs, ({locA with values := vs} : Locals).get 3 = locA.get 3 := fun _ => rfl
                rw [show [.localGet 6, .load32 (8:UInt32), .localGet 1, .ltU,
                          .const (1:UInt32), .and, .eqz, .br_if 1,
                          .localGet 6, .load32 (12:UInt32), .localGet 3, .ltU,
                          .const (1:UInt32), .and, .eqz, .br_if 1,
                          .localGet 6, .load32 (8:UInt32), .localSet 7] ++ cont =
                         .localGet 6 :: .load32 (8:UInt32) :: .localGet 1 :: .ltU ::
                         .const (1:UInt32) :: .and :: .eqz :: .br_if 1 ::
                         .localGet 6 :: .load32 (12:UInt32) :: .localGet 3 :: .ltU ::
                         .const (1:UInt32) :: .and :: .eqz :: .br_if 1 ::
                         .localGet 6 :: .load32 (8:UInt32) :: .localSet 7 :: cont from rfl]
                simp only
                  [exec, execOne.eq_def, Locals.set?,
                   hgv6_pre, hgv1_pre, hgv3_pre,
                   hf6, h1, h3,
                   hi_m, hj_m,
                   if_neg (show ¬(frame.toNat + UInt32.toNat (8 : UInt32) + 4 > stA.mem.pages * 65536) from by
                     rw [show UInt32.toNat (8 : UInt32) = 8 from by decide, ← hft8]; exact hbnd_fr8),
                   if_pos hi_lt_u32,
                   show (1 : UInt32) &&& 1 = 1 from by decide,
                   show (if (1 : UInt32) = 0 then (1 : UInt32) else 0) = 0 from by decide,
                   if_neg (show ¬(frame.toNat + UInt32.toNat (12 : UInt32) + 4 > stA.mem.pages * 65536) from by
                     rw [show UInt32.toNat (12 : UInt32) = 12 from by decide, ← hft12]; exact hbnd_fr12),
                   if_pos hj_lt_u32,
                   hlparams, hllocals,
                   if_neg (show ¬(7 < 6) from by omega),
                   if_pos (show (7 : Nat) < 6 + 16 from by omega),
                   show (7 : Nat) - 6 = 1 from by omega]
                rfl
              exact h_prefix_aux _
            rw [h_pre_B, show (15:Nat) = 14+1 from rfl, exec_block_cons, h_B1_B]
            simp only [List.take_zero, List.drop_zero, List.nil_append]
            -- suffix: localGet 6 ×2, load32 16 (=k), const 1, add (=k+1), store32 16 (→mem3_B), br 0
            have hgv6_suf_B : ∀ vs, ({locA_1213_B with values := vs} : Locals).get 6 = locA_1213_B.get 6 := fun _ => rfl
            have hg6_suf_B : locA_1213_B.get 6 = some (.i32 frame) := by
              simp only [Locals.get, locA_1213_B, locA_1213_B_locs, locA_89_locs,
                         hlparams, hllocals, List.length_set,
                         show ¬(6 < 6) from by omega, show (6:Nat) < 6+16 from by omega,
                         show (6:Nat) - 6 = 0 from by omega,
                         List.getElem?_set, show (7:Nat) ≠ 0 from by omega,
                         show (6:Nat) ≠ 0 from by omega, show (4:Nat) ≠ 0 from by omega,
                         show (3:Nat) ≠ 0 from by omega, show (2:Nat) ≠ 0 from by omega,
                         show (1:Nat) ≠ 0 from by omega, if_false]
              simpa [Locals.get, hlparams, hllocals, show ¬(6 < 6) from by omega] using hf6
            simp only [exec, execOne.eq_def,
                       hgv6_suf_B, hg6_suf_B,
                       if_neg (show ¬(frame.toNat + UInt32.toNat (16 : UInt32) + 4 > stA_m2_B.mem.pages * 65536) from by
                         rw [show stA_m2_B.mem.pages = stA.mem.pages from rfl,
                             show UInt32.toNat (16 : UInt32) = 16 from by decide, ← hft16]
                         exact hbnd_fr16),
                       show stA_m2_B.mem.read32 (frame + (16 : UInt32)) = UInt32.ofNat k from hmem2_B_fr16,
                       show (1 : UInt32) + UInt32.ofNat k = UInt32.ofNat (k + 1) from by
                         rw [UInt32.add_comm]; exact hk_add1,
                       show stA_m2_B.mem.write32 (frame + (16 : UInt32)) (UInt32.ofNat (k + 1)) = mem3_B from by
                         simp only [stA_m2_B, mem3_B]; rw [← hk_add1]]
            rfl
          obtain ⟨f_B, h_body_B⟩ := h_body_B
          -- memory reads after path B writes
          have hread8_B : stC_B.mem.read32 (frame + 8) = UInt32.ofNat i := by
            simp only [stC_B, mem3_B, mem2_B, mem1_B]
            rw [Mem.read32_write32_of_disjoint _ (frame + 16) (frame + 8) _
                  (by right; rw [hft16, hft8]; omega),
                Mem.read32_write32_of_disjoint _ (frame + 12) (frame + 8) _
                  (by right; rw [hft12, hft8]),
                Mem.read32_write32_of_disjoint _ (out_ptr + 4 * UInt32.ofNat k) (frame + 8) _
                  (by rw [hout_k_toNat, hft8];
                      rcases hframe_out_disj with h | h <;> omega),
                hi_m]
          have hread12_B : stC_B.mem.read32 (frame + 12) = UInt32.ofNat (j + 1) := by
            simp only [stC_B, mem3_B, mem2_B, mem1_B]
            rw [Mem.read32_write32_of_disjoint _ (frame + 16) (frame + 12) _
                  (by right; rw [hft16, hft12]),
                Mem.read32_write32_same, hj_add1]
          have hread16_B : stC_B.mem.read32 (frame + 16) = UInt32.ofNat (k + 1) := by
            simp only [stC_B, mem3_B]
            rw [Mem.read32_write32_same, hk_add1]
          -- locB_out_B.get 6: local[0] unchanged (set indices 1,2,3,4,6,7 ≠ 0)
          have hf6_out_B : locB_out_B.get 6 = some (.i32 frame) := by
            simp only [locB_out_B, locB_out_locs, Locals.get, hlparams, hllocals, List.length_set,
                       show ¬ (6 < 6) from by omega,
                       show 6 < 6 + 16 from by omega,
                       show 6 - 6 = 0 from by omega,
                       List.getElem?_set,
                       show (7 : Nat) ≠ 0 from by omega,
                       show (6 : Nat) ≠ 0 from by omega,
                       show (4 : Nat) ≠ 0 from by omega,
                       show (3 : Nat) ≠ 0 from by omega,
                       show (2 : Nat) ≠ 0 from by omega,
                       show (1 : Nat) ≠ 0 from by omega,
                       if_false]
            simpa [Locals.get, hlparams, hllocals,
                   show ¬ (6 < 6) from by omega] using hf6
          have hllocals_out_B : locB_out_B.locals.length = 16 := by
            simp [locB_out_B, locB_out_locs, List.length_set, hllocals]
          -- locB_out_B.get 0..5 = locA.get 0..5: params unchanged, needs hlparams for if-branch
          have hg_eq_B : ∀ n, n < 6 → locB_out_B.get n = locA.get n := fun n hn => by
            simp only [locB_out_B, Locals.get, hlparams, if_pos hn]
          have hlparams_out_B : locB_out_B.params.length = 6 := by exact hlparams
          -- invariant restoration: (i, j+1)
          have hI_B : MergeLoopInv frame out_ptr left_ptr right_ptr n_left n_right n_out
                        i₀ j₀ k₀ st stC_B locB_out_B :=
            ⟨i, j + 1, hi_lo, hi_hi, by omega, by omega,
             hread8_B, hread12_B,
             by rw [hread16_B]; congr 1; omega,
             hf6_out_B,
             (hg_eq_B 0 (by omega)).trans h0, (hg_eq_B 1 (by omega)).trans h1,
             (hg_eq_B 2 (by omega)).trans h2, (hg_eq_B 3 (by omega)).trans h3,
             (hg_eq_B 4 (by omega)).trans h4, (hg_eq_B 5 (by omega)).trans h5,
             hlparams_out_B, hllocals_out_B, ⟨v₀, hg⟩,
             fun q hq => by
               simp only [stC_B, mem3_B, mem2_B, mem1_B]
               have hliq : (left_ptr + 4 * UInt32.ofNat q).toNat = left_ptr.toNat + 4 * q :=
                 toNat_wordAddr left_ptr n_left.toNat q hq (by linarith)
               rw [Mem.read32_write32_of_disjoint _ (frame + 16) _ _
                     (by rw [hft16, hliq]; rcases hframe_left_disj with h | h <;> omega),
                   Mem.read32_write32_of_disjoint _ (frame + 12) _ _
                     (by rw [hft12, hliq]; rcases hframe_left_disj with h | h <;> omega),
                   Mem.read32_write32_of_disjoint _ (out_ptr + 4 * UInt32.ofNat k) _ _
                     (by rw [hout_k_toNat, hliq]; rcases hleft_out_disj with h | h <;> omega)]
               exact hleft q hq,
             fun q hq => by
               simp only [stC_B, mem3_B, mem2_B, mem1_B]
               have hriq : (right_ptr + 4 * UInt32.ofNat q).toNat = right_ptr.toNat + 4 * q :=
                 toNat_wordAddr right_ptr n_right.toNat q hq (by linarith)
               rw [Mem.read32_write32_of_disjoint _ (frame + 16) _ _
                     (by rw [hft16, hriq]; rcases hframe_right_disj with h | h <;> omega),
                   Mem.read32_write32_of_disjoint _ (frame + 12) _ _
                     (by rw [hft12, hriq]; rcases hframe_right_disj with h | h <;> omega),
                   Mem.read32_write32_of_disjoint _ (out_ptr + 4 * UInt32.ofNat k) _ _
                     (by rw [hout_k_toNat, hriq]; rcases hright_out_disj with h | h <;> omega)]
               exact hright q hq,
             (by
               -- content invariant: wordsAt stC_B (out+4k₀) (W+1) ++ merge(L.drop i, R.drop(j+1))
               --                  = merge(L.drop i₀, R.drop j₀)  (path B: ¬(left_i ≤ right_j))
               have hW : (i - i₀) + (j + 1 - j₀) = (i - i₀) + (j - j₀) + 1 := by omega
               rw [hW]
               have h_k₀_addr : (out_ptr + 4 * UInt32.ofNat k₀).toNat = out_ptr.toNat + 4 * k₀ :=
                 toNat_wordAddr out_ptr n_out.toNat k₀ (by have := hk_val; omega) (by linarith)
               have hout_bnd : (out_ptr + 4 * UInt32.ofNat k₀).toNat + 4 * ((i - i₀) + (j - j₀) + 1) ≤ 4294967296 := by
                 rw [h_k₀_addr]; have := hk_val; omega
               have hwords : wordsAt stC_B.mem (out_ptr + 4 * UInt32.ofNat k₀) ((i - i₀) + (j - j₀) + 1) =
                   wordsAt stA.mem (out_ptr + 4 * UInt32.ofNat k₀) ((i - i₀) + (j - j₀)) ++ [right_j] := by
                 simp only [stC_B, mem3_B, mem2_B, mem1_B]
                 rw [wordsAt_write32_of_disjoint _ _ (frame + 16) _ _ hout_bnd
                       (by rw [hft16, h_k₀_addr]; rcases hframe_out_disj with h | h <;> [left; right] <;> omega),
                     wordsAt_write32_of_disjoint _ _ (frame + 12) _ _ hout_bnd
                       (by rw [hft12, h_k₀_addr]; rcases hframe_out_disj with h | h <;> [left; right] <;> omega),
                     wordsAt_split _ _ _ ((i - i₀) + (j - j₀)) (by omega)]
                 simp only [show (i - i₀) + (j - j₀) + 1 - ((i - i₀) + (j - j₀)) = 1 from by omega]
                 congr 1
                 · rw [wordsAt_write32_of_disjoint _ _ (out_ptr + 4 * UInt32.ofNat k) _ _
                         (by omega)
                         (by right; rw [h_k₀_addr, hout_k_toNat]; omega)]
                 · have hbase_W : out_ptr + 4 * UInt32.ofNat k₀ + 4 * UInt32.ofNat ((i - i₀) + (j - j₀)) =
                       out_ptr + 4 * UInt32.ofNat k := by
                     have hkeq : k₀ + ((i - i₀) + (j - j₀)) = k := by omega
                     rw [UInt32.add_assoc, ← UInt32.mul_add, ← UInt32.ofNat_add, hkeq]
                   rw [hbase_W]; simp [wordsAt, Mem.read32_write32_same]
               rw [hwords, List.append_assoc, List.singleton_append]
               conv_rhs => rw [← hcontent]
               congr 1
               -- right_j :: merge(L.drop i, R.drop(j+1)) = merge(L.drop i, R.drop j)
               have hL_drop_i : (wordsAt st.mem left_ptr n_left.toNat).drop i =
                   st.mem.read32 (left_ptr + 4 * UInt32.ofNat i) ::
                   (wordsAt st.mem left_ptr n_left.toNat).drop (i + 1) := by
                 have h1 : i < (wordsAt st.mem left_ptr n_left.toNat).length := by
                   simp [wordsAt_length]; exact hlt_i
                 rw [List.drop_eq_getElem_cons h1, wordsAt_getElem _ _ _ _ hlt_i]
               have hR_drop_j : (wordsAt st.mem right_ptr n_right.toNat).drop j =
                   st.mem.read32 (right_ptr + 4 * UInt32.ofNat j) ::
                   (wordsAt st.mem right_ptr n_right.toNat).drop (j + 1) := by
                 have h2 : j < (wordsAt st.mem right_ptr n_right.toNat).length := by
                   simp [wordsAt_length]; exact hlt_j
                 rw [List.drop_eq_getElem_cons h2, wordsAt_getElem _ _ _ _ hlt_j]
               have hright_j_eq : right_j = st.mem.read32 (right_ptr + 4 * UInt32.ofNat j) :=
                 hright j hlt_j
               have hnle_st : ¬(st.mem.read32 (left_ptr + 4 * UInt32.ofNat i) ≤
                   st.mem.read32 (right_ptr + 4 * UInt32.ofNat j)) := by
                 rw [← hleft i hlt_i, ← hright j hlt_j]; exact hle
               rw [hright_j_eq, hL_drop_i, hR_drop_j, merge_cons_gt hnle_st]),
             by simp [stC_B, mem3_B, mem2_B, mem1_B, Mem.write32_pages, hpages],
             hk_global,
             by simp [stC_B, mem3_B, mem2_B, mem1_B, Mem.write32_pages, hleft_global],
             by simp [stC_B, mem3_B, mem2_B, mem1_B, Mem.write32_pages, hright_global],
             by simp [stC_B, mem3_B, mem2_B, mem1_B, Mem.write32_pages, hout_global],
             hpages_u32, hleft_out_disj, hright_out_disj, hleft_right_disj,
             hframe_left_disj, hframe_right_disj, hframe_out_disj⟩
          -- measure decrease
          have hμ_B : (n_left.toNat - (stC_B.mem.read32 (frame + 8)).toNat) +
                      (n_right.toNat - (stC_B.mem.read32 (frame + 12)).toNat) < n := by
            rw [hread8_B, hread12_B, UInt32.toNat_ofNat', UInt32.toNat_ofNat',
                Nat.mod_eq_of_lt (by have := n_left.toNat_lt; omega),
                Nat.mod_eq_of_lt (by have := n_right.toNat_lt; omega),
                ← hμ, hi_m, hj_m, UInt32.toNat_ofNat', UInt32.toNat_ofNat',
                Nat.mod_eq_of_lt (by have := n_left.toNat_lt; omega),
                Nat.mod_eq_of_lt (by have := n_right.toNat_lt; omega)]
            omega
          -- IH at reduced measure: input is (stC_B, locB_out_B)
          obtain ⟨f_rest, st₂, loc₂, hf_exec, hQ_rest, hMI_rest, hG_B, hFrm_B, hPages_B⟩ := IH _ hμ_B stC_B locB_out_B hI_B rfl
          -- Fuel composition: one body iteration at stA then IH fuel at stC_B
          have hbody_ne : exec f_B m stA locA mainMergeBody env ≠ .OutOfFuel := by
            simp [h_body_B]
          have hfuel_ne : exec f_rest m stC_B locB_out_B [.block 0 0 [.loop 0 0 mainMergeBody]] env ≠ .OutOfFuel :=
            fun h => by simp [h] at hf_exec
          have hbody_mono : exec (max f_B f_rest) m stA locA mainMergeBody env = .Break 0 stC_B locB_out_B :=
            (exec_fuel_mono (Nat.le_max_left f_B f_rest) hbody_ne).trans h_body_B
          have hblock_mono : exec (max f_B f_rest + 1) m stC_B locB_out_B [.block 0 0 [.loop 0 0 mainMergeBody]] env =
              exec f_rest m stC_B locB_out_B [.block 0 0 [.loop 0 0 mainMergeBody]] env :=
            exec_fuel_mono (by omega) hfuel_ne
          have hloop_single : ∀ F stT locT,
              exec F m stT locT [.loop 0 0 mainMergeBody] env =
              execOne F m stT locT (.loop 0 0 mainMergeBody) env := fun F stT locT => by
            cases F with
            | zero => simp [exec, execOne]
            | succ f =>
              simp only [exec]
              rcases execOne (f + 1) m stT locT (.loop 0 0 mainMergeBody) env with
                ⟨_, _⟩ | ⟨_, _, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_⟩ | _
              · rfl
              all_goals rfl
          have hloop_eq : exec (max f_B f_rest + 1) m stA locA [.loop 0 0 mainMergeBody] env =
              exec (max f_B f_rest) m stC_B locB_out_B [.loop 0 0 mainMergeBody] env := by
            rw [hloop_single, hloop_single]
            conv_lhs => rw [execOne_loop_succ]
            simp only [hbody_mono, List.take_zero, List.nil_append, List.drop_zero]
            rfl
          have heq : exec (max f_B f_rest + 2) m stA locA [.block 0 0 [.loop 0 0 mainMergeBody]] env =
              exec (max f_B f_rest + 1) m stC_B locB_out_B [.block 0 0 [.loop 0 0 mainMergeBody]] env := by
            rw [show max f_B f_rest + 2 = max f_B f_rest + 1 + 1 from rfl]
            conv_lhs => rw [exec_block_cons, hloop_eq]
            conv_rhs => rw [exec_block_cons]
            set discr := exec (max f_B f_rest) m stC_B locB_out_B [.loop 0 0 mainMergeBody] env
            rcases discr with ⟨r', s'⟩ | ⟨n, r', s'⟩ | ⟨r', vs⟩ | ⟨r', msg⟩ | ⟨msg⟩ | _
            · simp [exec, locB_out_B, locB_out_locs]
            · cases n with | zero => simp [exec, locB_out_B, locB_out_locs] | succ k => rfl
            all_goals rfl
          have hFrm_stC_B : ∀ ix, frame.toNat + 32 ≤ ix →
              (ix < out_ptr.toNat ∨ ix ≥ out_ptr.toNat + 4 * n_out.toNat) →
              stC_B.mem.bytes ix = stA.mem.bytes ix := fun ix hix hout => by
            simp only [stC_B, mem3_B, mem2_B, mem1_B]
            rw [Mem.write32_bytes_of_disjoint _ (frame + 16) _ ix
                  (by right; rw [hft16]; omega),
                Mem.write32_bytes_of_disjoint _ (frame + 12) _ ix
                  (by right; rw [hft12]; omega),
                Mem.write32_bytes_of_disjoint _ (out_ptr + 4 * UInt32.ofNat k) _ ix
                  (by rcases hout with h | h
                      · left; rw [hout_k_toNat]; omega
                      · right; rw [hout_k_toNat]; omega)]
          have hPages_stC_B : stC_B.mem.pages = stA.mem.pages := by
            simp only [stC_B, mem3_B, mem2_B, mem1_B, Mem.write32_pages]
          exact ⟨max f_B f_rest + 2, st₂, loc₂, by rw [heq, hblock_mono]; exact hf_exec, hQ_rest, hMI_rest, hG_B, fun ix hix hout => (hFrm_B ix hix hout).trans (hFrm_stC_B ix hix hout), hPages_B.trans hPages_stC_B⟩
      · -- exit: j = n_right
        -- body's second br_if 1 fires: exec 1 body = Break 1 → exec 2 loop = Break 0
        -- → exec 3 block = Fallthrough.  Q: stA.mem.read32(frame+12) = n_right.
        have hj_eq : j = n_right.toNat := Nat.le_antisymm hj_hi (Nat.not_lt.mp hlt_j)
        have hi_lt32  : UInt32.ofNat i < n_left := by
          rw [UInt32.lt_iff_toNat_lt_toNat, UInt32.toNat_ofNat']
          have := n_left.toNat_lt; omega
        have hj_nlt32 : ¬(UInt32.ofNat j < n_right) := by
          rw [UInt32.lt_iff_toNat_lt_toNat, UInt32.toNat_ofNat']
          have := n_right.toNat_lt; omega
        have hb8  : ¬(frame.toNat + (8 : UInt32).toNat + 4 > stA.mem.pages * 65536) :=
          by simp; omega
        have hb12 : ¬(frame.toNat + (12 : UInt32).toNat + 4 > stA.mem.pages * 65536) :=
          by simp; omega
        have hgv6j : ∀ xs, ({ locA with values := xs } : Locals).get 6 = locA.get 6 := fun _ => rfl
        have hgv1j : ∀ xs, ({ locA with values := xs } : Locals).get 1 = locA.get 1 := fun _ => rfl
        have hgv3j : ∀ xs, ({ locA with values := xs } : Locals).get 3 = locA.get 3 := fun _ => rfl
        -- exec 1 body = Break 1 (second br_if 1 fires since j = n_right)
        have h_body_exit_j : exec 1 m stA locA mainMergeBody env = .Break 1 stA locA := by
          simp only [mainMergeBody, exec, execOne.eq_def,
                     hgv6j, hgv1j, hgv3j, hf6, h1, h3,
                     hi_m, hj_m,
                     if_neg hb8, if_neg hb12,
                     if_pos hi_lt32,
                     show (1 : UInt32) &&& 1 = 1 from by decide,
                     show (if (1 : UInt32) = 0 then (1 : UInt32) else 0) = 0 from by decide,
                     if_neg hj_nlt32,
                     show (1 : UInt32) &&& 0 = 0 from by decide]
          rfl
        -- exec 2 [.loop ...] = Break 0  (Break 1 from body → loop converts to Break 0)
        have h_loop_exit_j : exec 2 m stA locA [.loop 0 0 mainMergeBody] env = .Break 0 stA locA := by
          simp only [show (2 : Nat) = 1 + 1 from rfl, exec, execOne_loop_succ]
          rw [h_body_exit_j]
        -- exec 3 [.block ...] = Fallthrough  (Break 0 from loop → block gives Fallthrough)
        have h_block_exit_j : exec 3 m stA locA [.block 0 0 [.loop 0 0 mainMergeBody]] env =
            .Fallthrough stA locA := by
          rw [show (3 : Nat) = 2 + 1 from rfl, exec_block_cons, h_loop_exit_j]
          simp only [List.take_zero, List.nil_append, List.drop_zero, exec]
        have hQ_j : stA.mem.read32 (frame + 12) = n_right := by
          rw [hj_m, hj_eq]
          apply UInt32.toNat_inj.mp
          simp
        exact ⟨3, stA, locA, h_block_exit_j, ⟨Or.inr hQ_j, i, j, hi_lo, hi_hi, hj_lo, hj_hi,
               hi_m, hj_m, hk_m, hleft, hright, hcontent⟩, hI_save, rfl, fun _ _ _ => rfl, rfl⟩
    · -- exit: i = n_left
      -- body's first br_if 1 fires immediately: exec 1 body = Break 1 → exec 2 loop = Break 0
      -- → exec 3 block = Fallthrough.  Q: stA.mem.read32(frame+8) = n_left.
      have hi_eq : i = n_left.toNat := Nat.le_antisymm hi_hi (Nat.not_lt.mp hlt_i)
      have hi_nlt32 : ¬(UInt32.ofNat i < n_left) := by
        rw [UInt32.lt_iff_toNat_lt_toNat, UInt32.toNat_ofNat']
        have := n_left.toNat_lt; omega
      have hb8i : ¬(frame.toNat + (8 : UInt32).toNat + 4 > stA.mem.pages * 65536) :=
        by simp; omega
      have hgv6i : ∀ xs, ({ locA with values := xs } : Locals).get 6 = locA.get 6 := fun _ => rfl
      have hgv1i : ∀ xs, ({ locA with values := xs } : Locals).get 1 = locA.get 1 := fun _ => rfl
      -- exec 1 body = Break 1 (first br_if 1 fires since i = n_left)
      have h_body_exit_i : exec 1 m stA locA mainMergeBody env = .Break 1 stA locA := by
        simp only [mainMergeBody, exec, execOne.eq_def,
                   hgv1i, hf6, h1, hi_m,
                   if_neg hb8i,
                   if_neg hi_nlt32,
                   show (1 : UInt32) &&& 0 = 0 from by decide]
        rfl
      -- exec 2 [.loop ...] = Break 0
      have h_loop_exit_i : exec 2 m stA locA [.loop 0 0 mainMergeBody] env = .Break 0 stA locA := by
        simp only [show (2 : Nat) = 1 + 1 from rfl, exec, execOne_loop_succ]
        rw [h_body_exit_i]
      -- exec 3 [.block 0 0 [.loop ...]] = Fallthrough
      have h_block_exit_i : exec 3 m stA locA [.block 0 0 [.loop 0 0 mainMergeBody]] env =
          .Fallthrough stA locA := by
        rw [show (3 : Nat) = 2 + 1 from rfl, exec_block_cons, h_loop_exit_i]
        simp only [List.take_zero, List.nil_append, List.drop_zero, exec]
      have hQ_i : stA.mem.read32 (frame + 8) = n_left := by
        rw [hi_m, hi_eq]
        apply UInt32.toNat_inj.mp
        simp
      exact ⟨3, stA, locA, h_block_exit_i, ⟨Or.inl hQ_i, i, j, hi_lo, hi_hi, hj_lo, hj_hi,
             hi_m, hj_m, hk_m, hleft, hright, hcontent⟩, hI_save, rfl, fun _ _ _ => rfl, rfl⟩
private theorem exec_step_FT
    {f : Nat} {m : Module} {st : Store Unit} {loc : Locals}
    {inst : Instruction} {rest : Program} {env : HostEnv Unit}
    {st' : Store Unit} {loc' : Locals}
    (h : exec f m st loc [inst] env = .Fallthrough st' loc') :
    exec f m st loc (inst :: rest) env = exec f m st' loc' rest env := by
  have hone : execOne f m st loc inst env = .Fallthrough st' loc' := by
    simp only [exec] at h
    cases hfuel : execOne f m st loc inst env with
    | Fallthrough s l => simp only [hfuel, exec] at h; exact h
    | OutOfFuel      => simp only [hfuel] at h; exact h
    | Break k s l    => simp only [hfuel] at h; exact h
    | Return s v     => simp only [hfuel] at h; exact h
    | ReturnCall s r => simp only [hfuel] at h; exact h
    | Invalid        => simp only [hfuel] at h; exact h
    | Trap           => simp only [hfuel] at h; exact h
    | Throwing       => simp only [hfuel] at h; exact h
  simp only [exec, hone]

theorem func6_after_merge_block
    {m : Module} {env : HostEnv Unit}
    (st₁ : Store Unit) (loc₁ : Locals)
    (frame out_ptr left_ptr right_ptr n_left n_right n_out : UInt32)
    (hI₀ : MergeLoopInv frame out_ptr left_ptr right_ptr n_left n_right n_out
             0 0 0 st₁ st₁ loc₁) :
    ∃ (N : Nat) (st₂ : Store Unit) (loc₂ : Locals),
      (∀ fuel : Nat, N ≤ fuel →
        exec fuel m st₁ loc₁ (Project.MergeSort.func6.drop 27) env =
        exec fuel m st₂ loc₂ (Project.MergeSort.func6.drop 28) env) ∧
      (st₂.mem.read32 (frame + 8) = n_left ∨
       st₂.mem.read32 (frame + 12) = n_right) ∧
      MergeLoopInv frame out_ptr left_ptr right_ptr n_left n_right n_out
        0 0 0 st₁ st₂ loc₂ ∧
      st₂.globals = st₁.globals ∧
      (∀ ix, frame.toNat + 32 ≤ ix →
             (ix < out_ptr.toNat ∨ ix ≥ out_ptr.toNat + 4 * n_out.toNat) →
             st₂.mem.bytes ix = st₁.mem.bytes ix) ∧
      st₂.mem.pages = st₁.mem.pages := by
  obtain ⟨N, st₂, loc₂, h_exec, ⟨h_exit, hI₂⟩, h_gp, h_frm, h_pages⟩ :=
    main_merge_loop_spec_exec st₁ loc₁ frame out_ptr left_ptr right_ptr
      n_left n_right n_out 0 0 0 hI₀
  have h_split : (Project.MergeSort.func6.drop 27 : Program) =
      .block 0 0 [.loop 0 0 mainMergeBody] :: Project.MergeSort.func6.drop 28 := rfl
  refine ⟨N, st₂, loc₂, ?_, h_exit, h_gp, h_frm, h_pages⟩
  intro fuel hfuel
  rw [h_split]
  apply exec_step_FT
  have hne : exec N m st₁ loc₁ [.block 0 0 [.loop 0 0 mainMergeBody]] env ≠ .OutOfFuel := by
    rw [h_exec]; intro h; cases h
  exact (exec_fuel_mono hfuel hne).trans h_exec

end Wasm.SepLogic.MergeSort
