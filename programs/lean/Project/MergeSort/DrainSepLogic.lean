import CodeLib.SepLogic.Adequacy
import Project.MergeSort.Framing

/-! # Right-drain inner loop of func6

Proves `right_drain_spec`: the inner right-drain `.loop 0 0 rightDrainBody` from
`func6` (Program.lean lines 489-562) drains `right[j₀..n_right-1]` into
`out[k₀..k₀+(n_right-j₀)-1]`, using `wp_wasm_prop_loop` with the Return-exit arm.

Loop exits via `.ret` (Return arm) when `j = n_right`; iterates via `.br 1`
inside BCO (Break-0 arm) when `j < n_right`.  No fuel appears in the statement.
-/

namespace Wasm.SepLogic.MergeSort

open Wasm Project.MergeSort.Framing

variable [WasmHeapGS]

/-- The body of func6's inner right-drain loop (Program.lean lines 490–561).

    Structure:
      - condition block: if j ≥ n_right → restore frame → .ret (Return exit)
      - localGet 6, load32 12, localSet 16  (load j into local16)
      - BCO block (CORRECT: copy + .br 1 INSIDE; error_k at top level):
          BCM block:
            BCI block: bounds check; br_if 1 (k < n_out) or br 2 (k ≥ n_out)
            error_j path (unreachable under invariant)
          copy: out[k] = right[j]; j++; k++; .br 1 (Break 1 → BCO Break 0)
      - error_k path (unreachable under invariant)  -/
private def rightDrainBody : Program := [
  -- condition block: j ≥ n_right → exit via .ret
  .block 0 0 [
    .localGet 6, .load32 (12 : UInt32),
    .localGet 3, .ltU,
    .const (1 : UInt32), .and,
    .br_if 0,
    .localGet 6, .const (32 : UInt32), .add,
    .globalSet 0, .ret
  ],
  -- load j = mem[frame+12] into local16
  .localGet 6, .load32 (12 : UInt32), .localSet 16,
  -- BCO: bounds check then copy (copy + .br 1 INSIDE, error_k OUTSIDE)
  .block 0 0 [
    -- BCM
    .block 0 0 [
      -- BCI
      .block 0 0 [
        .localGet 16, .localGet 3, .ltU, .const (1 : UInt32), .and, .eqz, .br_if 0,
        .localGet 2, .localGet 16, .const (2 : UInt32), .shl, .add, .load32 (0 : UInt32),
        .localSet 17,
        .localGet 6, .load32 (16 : UInt32), .localSet 18,
        .localGet 18, .localGet 5, .ltU, .const (1 : UInt32), .and, .br_if 1, .br 2
      ],
      -- error_j (unreachable when j < n_right under invariant)
      .localGet 16, .localGet 3, .const (1048648 : UInt32), .call 87, .unreachable
    ],
    -- copy: out[k] = right[j]; j++; k++  (INSIDE BCO)
    .localGet 4, .localGet 18, .const (2 : UInt32), .shl, .add, .localGet 17,
    .store32 (0 : UInt32),
    .localGet 6, .localGet 6, .load32 (12 : UInt32), .const (1 : UInt32), .add,
    .store32 (12 : UInt32),
    .localGet 6, .localGet 6, .load32 (16 : UInt32), .const (1 : UInt32), .add,
    .store32 (16 : UInt32),
    -- Break 1 → BCO maps to Break 0 → loop restarts  (INSIDE BCO)
    .br 1
  ],
  -- error_k (unreachable when k < n_out under invariant, OUTSIDE BCO)
  .localGet 18, .localGet 5, .const (1048664 : UInt32), .call 87, .unreachable
]

/-- Loop invariant.

    Tracks current right-index `j` and output-index `k = k₀ + (j - j₀)`, with
    the partial copy result, local-structure constraints, and disjointness
    conditions needed for framing during the copy step.  `st_init` is fixed at
    the initial store so `hcopy` and `hright` can refer to the original source. -/
private def DrainInv
    (frame out_ptr right_ptr n_right n_out : UInt32)
    (j₀ k₀ : Nat)
    (st_init : Store Unit)
    (stA : Store Unit) (locA : Locals) : Prop :=
  ∃ j : Nat,
    j₀ ≤ j ∧ j ≤ n_right.toNat ∧
    -- five loop-parameter locals unchanged by the body
    locA.get 6 = some (.i32 frame) ∧
    locA.get 3 = some (.i32 n_right) ∧
    locA.get 2 = some (.i32 right_ptr) ∧
    locA.get 4 = some (.i32 out_ptr) ∧
    locA.get 5 = some (.i32 n_out) ∧
    -- local-frame shape required to evaluate localSet 16/17/18
    locA.params.length = 6 ∧
    locA.locals.length = 16 ∧
    -- global 0 must be writable (globalSet 0 in the exit path)
    (∃ v, stA.globals.globals[0]? = some v) ∧
    -- frame slots: j and k stored in memory
    stA.mem.read32 (frame + 12) = UInt32.ofNat j ∧
    stA.mem.read32 (frame + 16) = UInt32.ofNat (k₀ + (j - j₀)) ∧
    -- partial copy: out[k₀..k₀+(j-j₀)-1] = right_init[j₀..j₀+(j-j₀)-1]
    (∀ i, i < j - j₀ →
      stA.mem.read32 (out_ptr + 4 * UInt32.ofNat (k₀ + i)) =
      st_init.mem.read32 (right_ptr + 4 * UInt32.ofNat (j₀ + i))) ∧
    -- source unchanged during drain
    (∀ i, i < n_right.toNat →
      stA.mem.read32 (right_ptr + 4 * UInt32.ofNat i) =
      st_init.mem.read32 (right_ptr + 4 * UInt32.ofNat i)) ∧
    -- frame in-bounds for load/store 12 and 16
    frame.toNat + 20 ≤ stA.mem.pages * 65536 ∧
    -- global output-range bound: enough room for all remaining copies
    k₀ + (n_right.toNat - j₀) ≤ n_out.toNat ∧
    -- array region bounds (no UInt32 overflow, in-bounds for r/w)
    right_ptr.toNat + 4 * n_right.toNat ≤ stA.mem.pages * 65536 ∧
    out_ptr.toNat + 4 * n_out.toNat ≤ stA.mem.pages * 65536 ∧
    -- pages fit in 32-bit address space (required for toNat_wordAddr)
    stA.mem.pages * 65536 ≤ 4294967296 ∧
    -- disjointness: right and out arrays don't overlap
    (right_ptr.toNat + 4 * n_right.toNat ≤ out_ptr.toNat ∨
     out_ptr.toNat + 4 * n_out.toNat ≤ right_ptr.toNat) ∧
    -- disjointness: frame region [frame, frame+20) vs right array
    (frame.toNat + 20 ≤ right_ptr.toNat ∨
     right_ptr.toNat + 4 * n_right.toNat ≤ frame.toNat) ∧
    -- disjointness: frame region [frame, frame+20) vs out array
    (frame.toNat + 20 ≤ out_ptr.toNat ∨
     out_ptr.toNat + 4 * n_out.toNat ≤ frame.toNat)

/-- The right-drain inner loop of `func6` correctly drains `right[j₀..n_right-1]`
    into `out[k₀..]`.

    **Exit**: when `j = n_right`, `.ret` fires (Return arm).
    **Iteration**: when `j < n_right`, `.br 1` inside BCO fires (Break-0 arm). -/
theorem right_drain_spec
    {m : Module} {env : HostEnv Unit}
    (st : Store Unit) (locals : Locals)
    (frame out_ptr right_ptr n_right n_out : UInt32)
    (j₀ k₀ : Nat)
    (hI₀ : DrainInv frame out_ptr right_ptr n_right n_out j₀ k₀ st st locals) :
    wp_wasm_prop m st locals [.loop 0 0 rightDrainBody] env
      (fun st' _ =>
        ∀ i, i < n_right.toNat - j₀ →
          st'.mem.read32 (out_ptr + 4 * UInt32.ofNat (k₀ + i)) =
          st.mem.read32 (right_ptr + 4 * UInt32.ofNat (j₀ + i))) := by
  apply wp_wasm_prop_loop
      (I := DrainInv frame out_ptr right_ptr n_right n_out j₀ k₀ st)
      (μ := fun stA _ => n_right.toNat - (stA.mem.read32 (frame + 12)).toNat)
  · exact hI₀
  · intro stA locA ⟨j, hj_lo, hj_hi, hf6, h3, h2, h4, h5,
                   hlparams, hllocals, hglobal,
                   hj_m, hk_m, hcopy, hright,
                   hpages, hk_global, hright_global, hout_global, hpages_u32,
                   hright_out_disj, hframe_right_disj, hframe_out_disj⟩
    by_cases hlt : j < n_right.toNat
    · -- break-0: copy step, loop restart
      -- Abbreviations
      let k := k₀ + (j - j₀)
      have hk_lt : k < n_out.toNat := by
        omega
      -- UInt32 comparison fact for ltU (j < n_right)
      have hj_lt32 : UInt32.ofNat j < n_right := by
        rw [UInt32.lt_iff_toNat_lt_toNat, UInt32.toNat_ofNat']
        have := n_right.toNat_lt; omega
      -- UInt32 comparison fact for ltU (k < n_out)
      have hk_lt32 : UInt32.ofNat (k₀ + (j - j₀)) < n_out := by
        rw [UInt32.lt_iff_toNat_lt_toNat, UInt32.toNat_ofNat']
        have := n_out.toNat_lt; omega
      -- Bounds facts for load32/store32 (all via omega once toNat is resolved)
      have hframe_toNat12 : (frame + 12).toNat = frame.toNat + 12 := by
        rw [UInt32.toNat_add]; simp [UInt32.toNat_ofNat']; omega
      have hframe_toNat16 : (frame + 16).toNat = frame.toNat + 16 := by
        rw [UInt32.toNat_add]; simp [UInt32.toNat_ofNat']; omega
      have hright_j_toNat : (right_ptr + 4 * UInt32.ofNat j).toNat
          = right_ptr.toNat + 4 * j :=
        toNat_wordAddr right_ptr n_right.toNat j hlt (by linarith)
      have hout_k_toNat : (out_ptr + 4 * UInt32.ofNat k).toNat
          = out_ptr.toNat + 4 * k :=
        toNat_wordAddr out_ptr n_out.toNat k (by omega) (by linarith)
      -- Actual right[j] value
      let right_j := stA.mem.read32 (right_ptr + 4 * UInt32.ofNat j)
      -- Memory snapshots after each write in the copy step
      let mem1 := stA.mem.write32 (out_ptr + 4 * UInt32.ofNat k) right_j
      let mem2 := mem1.write32 (frame + 12) (UInt32.ofNat j + 1)
      let mem3 := mem2.write32 (frame + 16) (UInt32.ofNat k + 1)
      let stC : Store Unit := { stA with mem := mem3 }
      -- The locals state after localSet 16 (local16 := j)
      let locA16 : Locals :=
        { locA with locals := locA.locals.set 10 (.i32 (UInt32.ofNat j)) }
      -- After BCI sets local17 := right[j] and local18 := k
      let locA17 : Locals :=
        { locA16 with locals := locA16.locals.set 11 (.i32 right_j) }
      let locA18 : Locals :=
        { locA17 with locals := locA17.locals.set 12 (.i32 (UInt32.ofNat k)) }
      -- sB: locals at Break 0 (copy unchanged the params/locals structure)
      let sB : Locals := { locA18 with values := locA.values }
      -- exec trace
      -- condBody at fuel 3: br_if 0 fires (value = 1) → Break 0 stA locA
      have h_cond : exec 3 m stA locA [
          .localGet 6, .load32 (12 : UInt32),
          .localGet 3, .ltU, .const (1 : UInt32), .and, .br_if 0,
          .localGet 6, .const (32 : UInt32), .add, .globalSet 0, .ret
        ] env = .Break 0 stA locA := by
        have hgv3 : ∀ xs, ({ locA with values := xs } : Locals).get 3 = locA.get 3 :=
          fun _ => rfl
        simp only [exec, execOne.eq_def, hgv3, hf6, h3, hj_m,
                   if_neg (show ¬(frame.toNat + (12 : UInt32).toNat + 4
                                  > stA.mem.pages * 65536) from by simp; omega),
                   if_pos hj_lt32,
                   show (1 : UInt32) &&& 1 = 1 from by decide]
        rfl
      -- cond_block: exec_block_cons at fuel 4; Break 0 → Fallthrough locA
      -- (take 0 ++ drop 0 = locA.values)
      have h_condblock : exec 4 m stA locA
          (.block 0 0 [
            .localGet 6, .load32 (12 : UInt32),
            .localGet 3, .ltU, .const (1 : UInt32), .and, .br_if 0,
            .localGet 6, .const (32 : UInt32), .add, .globalSet 0, .ret
          ] :: [
            .localGet 6, .load32 (12 : UInt32), .localSet 16,
            .block 0 0 [
              .block 0 0 [
                .block 0 0 [
                  .localGet 16, .localGet 3, .ltU, .const (1 : UInt32), .and, .eqz, .br_if 0,
                  .localGet 2, .localGet 16, .const (2 : UInt32), .shl, .add,
                  .load32 (0 : UInt32), .localSet 17,
                  .localGet 6, .load32 (16 : UInt32), .localSet 18,
                  .localGet 18, .localGet 5, .ltU, .const (1 : UInt32), .and, .br_if 1, .br 2
                ],
                .localGet 16, .localGet 3, .const (1048648 : UInt32), .call 87, .unreachable
              ],
              .localGet 4, .localGet 18, .const (2 : UInt32), .shl, .add, .localGet 17,
              .store32 (0 : UInt32),
              .localGet 6, .localGet 6, .load32 (12 : UInt32), .const (1 : UInt32), .add,
              .store32 (12 : UInt32),
              .localGet 6, .localGet 6, .load32 (16 : UInt32), .const (1 : UInt32), .add,
              .store32 (16 : UInt32), .br 1
            ],
            .localGet 18, .localGet 5, .const (1048664 : UInt32), .call 87, .unreachable
          ]) env =
          exec 4 m stA locA16 [
            .block 0 0 [
              .block 0 0 [
                .block 0 0 [
                  .localGet 16, .localGet 3, .ltU, .const (1 : UInt32), .and, .eqz, .br_if 0,
                  .localGet 2, .localGet 16, .const (2 : UInt32), .shl, .add,
                  .load32 (0 : UInt32), .localSet 17,
                  .localGet 6, .load32 (16 : UInt32), .localSet 18,
                  .localGet 18, .localGet 5, .ltU, .const (1 : UInt32), .and, .br_if 1, .br 2
                ],
                .localGet 16, .localGet 3, .const (1048648 : UInt32), .call 87, .unreachable
              ],
              .localGet 4, .localGet 18, .const (2 : UInt32), .shl, .add, .localGet 17,
              .store32 (0 : UInt32),
              .localGet 6, .localGet 6, .load32 (12 : UInt32), .const (1 : UInt32), .add,
              .store32 (12 : UInt32),
              .localGet 6, .localGet 6, .load32 (16 : UInt32), .const (1 : UInt32), .add,
              .store32 (16 : UInt32), .br 1
            ],
            .localGet 18, .localGet 5, .const (1048664 : UInt32), .call 87, .unreachable
          ] env := by
        rw [show (4 : Nat) = 3 + 1 from rfl, exec_block_cons, h_cond]
        simp only [List.take_zero, List.drop_zero, List.nil_append]
        simp only [exec, execOne.eq_def, hf6, hj_m,
                   if_neg (show ¬(frame.toNat + (12 : UInt32).toNat + 4
                                   > stA.mem.pages * 65536) from by simp; omega),
                   Locals.set?, hlparams, hllocals, List.length_set,
                   if_neg (show ¬((16 : Nat) < 6) from by omega),
                   if_pos (show (16 : Nat) < 6 + 16 from by omega),
                   show (16 : Nat) - 6 = 10 from by omega,
                   show Locals.mk locA.params (locA.locals.set 10 (Value.i32 (UInt32.ofNat j)))
                         locA.values = locA16 from rfl]
      -- localGet 6; load32 12; localSet 16  at fuel 4 → Fallthrough stA locA16
      have hset16 : locA.set? 16 (.i32 (UInt32.ofNat j)) = some locA16 := by
        simp only [Locals.set?, locA16, hlparams, hllocals,
                   show ¬((16 : Nat) < 6) from by omega,
                   show (16 : Nat) < 6 + 16 from by omega,
                   show (16 : Nat) - 6 = 10 from by omega,
                   List.length_set]
        rfl
      have hlocA16_get6 : locA16.get 6 = some (.i32 frame) := by
        simp only [Locals.get, locA16, hlparams, hllocals, List.length_set,
                   show ¬((6 : Nat) < 6) from by omega,
                   show (6 : Nat) < 6 + 16 from by omega,
                   show (6 : Nat) - 6 = 0 from by omega,
                   List.getElem?_set,
                   show ¬(10 = 0 ∧ 0 < 16) from by omega]
        simpa [Locals.get, hlparams, hllocals, show ¬((6:Nat) < 6) from by omega] using hf6
      have hlocA16_get3 : locA16.get 3 = some (.i32 n_right) := by
        simp only [Locals.get, locA16, hlparams, show (3 : Nat) < 6 from by omega] at h3 ⊢
        exact h3
      have hlocA16_get2 : locA16.get 2 = some (.i32 right_ptr) := by
        simp only [Locals.get, locA16, hlparams, show (2 : Nat) < 6 from by omega] at h2 ⊢
        exact h2
      have hlocA16_get5 : locA16.get 5 = some (.i32 n_out) := by
        simp only [Locals.get, locA16, hlparams, show (5 : Nat) < 6 from by omega] at h5 ⊢
        exact h5
      have hlocA16_get4 : locA16.get 4 = some (.i32 out_ptr) := by
        simp only [Locals.get, locA16, hlparams, show (4 : Nat) < 6 from by omega] at h4 ⊢
        exact h4
      have hlocA16_get16 : locA16.get 16 = some (.i32 (UInt32.ofNat j)) := by
        simp only [Locals.get, locA16, hlparams, hllocals, List.length_set,
                   show ¬((16 : Nat) < 6) from by omega,
                   show (16 : Nat) < 6 + 16 from by omega,
                   show (16 : Nat) - 6 = 10 from by omega,
                   List.getElem?_set, show (10 : Nat) < 16 from by omega,
                   if_true, if_false]
      have hlocA16_params : locA16.params.length = 6 := by simp [locA16, hlparams]
      have hlocA16_locals : locA16.locals.length = 16 := by
        simp [locA16, List.length_set, hllocals]
      -- BCI body at fuel 0: br_if 1 fires (k < n_out) → Break 1
      -- After localSet 17 (right_j) and localSet 18 (k), the locals are locA18
      -- (we prove BCI body directly)
      have hset17 : locA16.set? 17 (.i32 right_j) = some locA17 := by
        simp only [Locals.set?, locA17, hlocA16_params, hlocA16_locals, List.length_set,
                   show ¬((17 : Nat) < 6) from by omega,
                   show (17 : Nat) < 6 + 16 from by omega,
                   show (17 : Nat) - 6 = 11 from by omega]
        rfl
      have hset18 : locA17.set? 18 (.i32 (UInt32.ofNat k)) = some locA18 := by
        have hlen17p : locA17.params.length = 6 := by simp [locA17, hlocA16_params]
        have hlen17l : locA17.locals.length = 16 := by
          simp [locA17, List.length_set, hlocA16_locals]
        simp only [Locals.set?, locA18, hlen17p, hlen17l, List.length_set,
                   show ¬((18 : Nat) < 6) from by omega,
                   show (18 : Nat) < 6 + 16 from by omega,
                   show (18 : Nat) - 6 = 12 from by omega]
        rfl
      have hlocA18_get18 : locA18.get 18 = some (.i32 (UInt32.ofNat k)) := by
        have hlen17p : locA17.params.length = 6 := by simp [locA17, hlocA16_params]
        have hlen17l : locA17.locals.length = 16 := by
          simp [locA17, List.length_set, hlocA16_locals]
        simp only [Locals.get, locA18, hlen17p, hlen17l, List.length_set,
                   show ¬((18 : Nat) < 6) from by omega,
                   show (18 : Nat) < 6 + 16 from by omega,
                   show (18 : Nat) - 6 = 12 from by omega,
                   List.getElem?_set, show (12 : Nat) < 16 from by omega,
                   if_true, if_false]
      have hlocA18_get5 : locA18.get 5 = some (.i32 n_out) := by
        have hlen17p : locA17.params.length = 6 := by simp [locA17, hlocA16_params]
        simp only [Locals.get, locA18, locA17, locA16,
                   hlen17p, hlocA16_params, hlparams,
                   show (5 : Nat) < 6 from by omega] at h5 ⊢
        exact h5
      have hlocA18_get4 : locA18.get 4 = some (.i32 out_ptr) := by
        have hlen17p : locA17.params.length = 6 := by simp [locA17, hlocA16_params]
        simp only [Locals.get, locA18, locA17, locA16,
                   hlen17p, hlocA16_params, hlparams,
                   show (4 : Nat) < 6 from by omega] at h4 ⊢
        exact h4
      have hlocA18_get6 : locA18.get 6 = some (.i32 frame) := by
        have hlen17p : locA17.params.length = 6 := by simp [locA17, hlocA16_params]
        have hlen17l : locA17.locals.length = 16 := by
          simp [locA17, List.length_set, hlocA16_locals]
        simp only [Locals.get, locA18, locA17, locA16,
                   hlen17p, hlen17l, hlocA16_params, hlocA16_locals, hlparams, hllocals,
                   List.length_set,
                   show ¬((6 : Nat) < 6) from by omega,
                   show (6 : Nat) < 6 + 16 from by omega,
                   show (6 : Nat) - 6 = 0 from by omega,
                   List.getElem?_set,
                   show ¬(12 = 0 ∧ (0 : Nat) < 16) from by omega,
                   show ¬(11 = 0 ∧ (0 : Nat) < 16) from by omega,
                   show ¬(10 = 0 ∧ (0 : Nat) < 16) from by omega] at hf6 ⊢
        exact hf6
      have hlocA18_get17 : locA18.get 17 = some (.i32 right_j) := by
        have hlen17p : locA17.params.length = 6 := by simp [locA17, hlocA16_params]
        have hlen17l : locA17.locals.length = 16 := by
          simp [locA17, List.length_set, hlocA16_locals]
        simp only [Locals.get, locA18, locA17, hlen17p, hlen17l, hlocA16_locals,
                   List.length_set,
                   show ¬((17 : Nat) < 6) from by omega,
                   show (17 : Nat) < 6 + 16 from by omega,
                   show (17 : Nat) - 6 = 11 from by omega,
                   List.getElem?_set,
                   show (12 : Nat) ≠ 11 from by omega, if_false,
                   if_true, show (11 : Nat) < 16 from by omega]
      -- BCI body exec at fuel 1: break 1 via br_if 1
      have h_bci_body : exec 1 m stA locA16 [
          .localGet 16, .localGet 3, .ltU, .const (1 : UInt32), .and, .eqz, .br_if 0,
          .localGet 2, .localGet 16, .const (2 : UInt32), .shl, .add,
          .load32 (0 : UInt32), .localSet 17,
          .localGet 6, .load32 (16 : UInt32), .localSet 18,
          .localGet 18, .localGet 5, .ltU, .const (1 : UInt32), .and, .br_if 1, .br 2
        ] env = .Break 1 stA { locA18 with values := locA.values } := by
        -- values-update lemmas: { locA_N with values := xs }.get I = locA_N.get I
        have hgv16 : ∀ xs, ({ locA16 with values := xs } : Locals).get 16 = locA16.get 16 :=
          fun _ => rfl
        have hgv3' : ∀ xs, ({ locA16 with values := xs } : Locals).get 3 = locA16.get 3 :=
          fun _ => rfl
        have hgv2 : ∀ xs, ({ locA16 with values := xs } : Locals).get 2 = locA16.get 2 :=
          fun _ => rfl
        have hgv6 : ∀ xs, ({ locA16 with values := xs } : Locals).get 6 = locA16.get 6 :=
          fun _ => rfl
        have hgv17_6 : ∀ xs, ({ locA17 with values := xs } : Locals).get 6 = locA17.get 6 :=
          fun _ => rfl
        have hgv18_18 : ∀ xs, ({ locA18 with values := xs } : Locals).get 18 = locA18.get 18 :=
          fun _ => rfl
        have hgv18_5 : ∀ xs, ({ locA18 with values := xs } : Locals).get 5 = locA18.get 5 :=
          fun _ => rfl
        -- locA17.get 6 = frame (set slot 11 doesn't touch slot 0)
        have hlocA17_get6 : locA17.get 6 = some (.i32 frame) := by
          show ({ locA16 with locals := locA16.locals.set 11 (.i32 right_j) } : Locals).get 6 = _
          simp only [Locals.get, hlocA16_params, hlocA16_locals, List.length_set,
                     show ¬((6 : Nat) < 6) from by omega,
                     show (6 : Nat) < 6 + 16 from by omega,
                     show (6 : Nat) - 6 = 0 from by omega,
                     List.getElem?_set,
                     show (11 : Nat) ≠ 0 from by omega, if_false]
          simpa [Locals.get, hlocA16_params, hlocA16_locals,
                 show ¬((6 : Nat) < 6) from by omega] using hlocA16_get6
        -- Raw-form get lemmas matching the actual Locals.mk form produced by exec/Locals.set?
        have hget17_6_raw : ∀ xs,
            (Locals.mk locA16.params (locA16.locals.set 11 (.i32 right_j)) xs).get 6
            = some (.i32 frame) := fun xs => (hgv17_6 xs).trans hlocA17_get6
        have hget18_18_raw : ∀ xs,
            (Locals.mk locA16.params
              ((locA16.locals.set 11 (.i32 right_j)).set 12 (.i32 (UInt32.ofNat (k₀ + (j - j₀))))) xs).get 18
            = some (.i32 (UInt32.ofNat (k₀ + (j - j₀)))) := fun xs => (hgv18_18 xs).trans hlocA18_get18
        have hget18_5_raw : ∀ xs,
            (Locals.mk locA16.params
              ((locA16.locals.set 11 (.i32 right_j)).set 12 (.i32 (UInt32.ofNat (k₀ + (j - j₀))))) xs).get 5
            = some (.i32 n_out) := fun xs => (hgv18_5 xs).trans hlocA18_get5
        -- shl by 2 = multiply by 4 for UInt32
        have hshl_j : UInt32.ofNat j <<< ((2 : UInt32) % 32) = 4 * UInt32.ofNat j := by
          rw [show (2 : UInt32) % 32 = 2 from by decide]
          apply UInt32.toNat_inj.mp
          have hj_bnd : j < 2 ^ 30 := by have := n_right.toNat_lt; omega
          simp only [UInt32.toNat_mul, UInt32.toNat_ofNat',
                     show (4 : UInt32).toNat = 4 from rfl,
                     Nat.mod_eq_of_lt (show j < 4294967296 from by omega),
                     Nat.mod_eq_of_lt (show j * 4 < 4294967296 from by omega)]
          simp [UInt32.shiftLeft, Fin.shiftLeft, Nat.shiftLeft_eq]
          omega
        simp only [exec, execOne.eq_def, Locals.set?,
                   hgv16, hgv3', hgv2, hgv6,
                   hlocA16_get16, hlocA16_get3,
                   if_pos hj_lt32,
                   show (1 : UInt32) &&& 1 = 1 from by decide,
                   show (if (1 : UInt32) = 0 then (1 : UInt32) else 0) = 0 from by decide,
                   hlocA16_get2, hlocA16_get6, hk_m,
                   if_neg (show ¬(frame.toNat + (16 : UInt32).toNat + 4
                                  > stA.mem.pages * 65536) from by simp; omega),
                   hlocA16_params, hlocA16_locals, List.length_set,
                   if_false, if_true,
                   show ¬((17 : Nat) < 6) from by omega,
                   show (17 : Nat) < 6 + 16 from by omega,
                   show (17 : Nat) - 6 = 11 from by omega,
                   show (11 : Nat) < 16 from by omega,
                   hget17_6_raw,
                   show ¬((18 : Nat) < 6) from by omega,
                   show (18 : Nat) < 6 + 16 from by omega,
                   show (18 : Nat) - 6 = 12 from by omega,
                   show (12 : Nat) < 16 from by omega,
                   hget18_18_raw, hget18_5_raw,
                   if_neg (show ¬((4 * UInt32.ofNat j + right_ptr).toNat +
                                   UInt32.toNat 0 + 4 > stA.mem.pages * 65536) from by
                             rw [show 4 * UInt32.ofNat j + right_ptr =
                                   right_ptr + 4 * UInt32.ofNat j from UInt32.add_comm _ _,
                                 hright_j_toNat, show UInt32.toNat 0 = 0 from rfl]
                             omega),
                   show stA.mem.read32 (4 * UInt32.ofNat j + right_ptr + (0 : UInt32))
                       = right_j from by
                     rw [show 4 * UInt32.ofNat j + right_ptr + (0 : UInt32)
                             = right_ptr + 4 * UInt32.ofNat j from by
                               rw [UInt32.add_comm (4 * UInt32.ofNat j) right_ptr,
                                   UInt32.add_zero]],
                   if_pos hk_lt32,
                   show (1 : UInt32) &&& 1 = 1 from by decide,
                   hshl_j]
        simp only [locA16, locA17, locA18]
        rfl
      -- BCI_block at fuel 2: body runs at fuel 1 (Break 1 → Break 0, rest skipped)
      have h_bci_block : exec 2 m stA locA16 [
          .block 0 0 [
            .localGet 16, .localGet 3, .ltU, .const (1 : UInt32), .and, .eqz, .br_if 0,
            .localGet 2, .localGet 16, .const (2 : UInt32), .shl, .add,
            .load32 (0 : UInt32), .localSet 17,
            .localGet 6, .load32 (16 : UInt32), .localSet 18,
            .localGet 18, .localGet 5, .ltU, .const (1 : UInt32), .and, .br_if 1, .br 2
          ],
          .localGet 16, .localGet 3, .const (1048648 : UInt32), .call 87, .unreachable
        ] env = .Break 0 stA { locA18 with values := locA.values } := by
        rw [show (2 : Nat) = 1 + 1 from rfl, exec_block_cons, h_bci_body]
      -- BCM body exec: Break 0 propagates
      -- BCM_block: Break 0 → Fallthrough (take 0 ++ drop 0 = locA.values)
      -- After BCM_block Fallthrough, copy code runs
      -- Memory after copy:
      have hmem1_frame12 : mem1.read32 (frame + 12) = stA.mem.read32 (frame + 12) :=
        Mem.read32_write32_of_disjoint stA.mem (out_ptr + 4 * UInt32.ofNat k) (frame + 12) right_j
          (by rw [hframe_toNat12, hout_k_toNat]; rcases hframe_out_disj with h | h <;> [right; left] <;> omega)
      have hmem1_frame16 : mem1.read32 (frame + 16) = stA.mem.read32 (frame + 16) :=
        Mem.read32_write32_of_disjoint stA.mem (out_ptr + 4 * UInt32.ofNat k) (frame + 16) right_j
          (by rw [hframe_toNat16, hout_k_toNat]; rcases hframe_out_disj with h | h <;> [right; left] <;> omega)
      have hmem2_frame16 : mem2.read32 (frame + 16) = stA.mem.read32 (frame + 16) :=
        (Mem.read32_write32_of_disjoint mem1 (frame + 12) (frame + 16) _
          (by left; rw [hframe_toNat12, hframe_toNat16])).trans hmem1_frame16
      -- shl semantics: UInt32.ofNat k <<< 2 = 4 * UInt32.ofNat k (verified by simp)
      have hshl_k : UInt32.ofNat k <<< ((2 : UInt32) % 32) = 4 * UInt32.ofNat k := by
        rw [show (2 : UInt32) % 32 = 2 from by decide]
        apply UInt32.toNat_inj.mp
        have hk_bnd : k < 2 ^ 30 := by have := n_out.toNat_lt; omega
        simp only [UInt32.toNat_mul, UInt32.toNat_ofNat',
                   show (4 : UInt32).toNat = 4 from rfl,
                   Nat.mod_eq_of_lt (show k < 4294967296 from by omega),
                   Nat.mod_eq_of_lt (show k * 4 < 4294967296 from by omega)]
        simp [UInt32.shiftLeft, Fin.shiftLeft, Nat.shiftLeft_eq]
        omega
      -- BCO body exec at fuel 3: BCM Fallthrough then copy then .br 1 → Break 1
      have h_bco_body : exec 3 m stA locA16 [
          .block 0 0 [
            .block 0 0 [
              .localGet 16, .localGet 3, .ltU, .const (1 : UInt32), .and, .eqz, .br_if 0,
              .localGet 2, .localGet 16, .const (2 : UInt32), .shl, .add,
              .load32 (0 : UInt32), .localSet 17,
              .localGet 6, .load32 (16 : UInt32), .localSet 18,
              .localGet 18, .localGet 5, .ltU, .const (1 : UInt32), .and, .br_if 1, .br 2
            ],
            .localGet 16, .localGet 3, .const (1048648 : UInt32), .call 87, .unreachable
          ],
          .localGet 4, .localGet 18, .const (2 : UInt32), .shl, .add, .localGet 17,
          .store32 (0 : UInt32),
          .localGet 6, .localGet 6, .load32 (12 : UInt32), .const (1 : UInt32), .add,
          .store32 (12 : UInt32),
          .localGet 6, .localGet 6, .load32 (16 : UInt32), .const (1 : UInt32), .add,
          .store32 (16 : UInt32), .br 1
        ] env = .Break 1 stC sB := by
        rw [show (3 : Nat) = 2 + 1 from rfl, exec_block_cons, h_bci_block]
        simp only [List.take_zero, List.drop_zero, List.nil_append]
        -- values-update lemmas for the copy-out instructions
        have hgv18_4 : ∀ xs, ({ locA18 with values := xs } : Locals).get 4 = locA18.get 4 :=
          fun _ => rfl
        have hgv18_18 : ∀ xs, ({ locA18 with values := xs } : Locals).get 18 = locA18.get 18 :=
          fun _ => rfl
        have hgv18_17 : ∀ xs, ({ locA18 with values := xs } : Locals).get 17 = locA18.get 17 :=
          fun _ => rfl
        have hgv18_6 : ∀ xs, ({ locA18 with values := xs } : Locals).get 6 = locA18.get 6 :=
          fun _ => rfl
        simp only [exec, execOne.eq_def,
                   hgv18_4, hgv18_18, hgv18_17, hgv18_6,
                   hlocA18_get4, hlocA18_get18, hlocA18_get17, hlocA18_get6,
                   hj_m, hk_m,
                   show ∀ v, (stA.mem.write32 (out_ptr + 4 * UInt32.ofNat k) v).read32 (frame + 12)
                         = stA.mem.read32 (frame + 12) from fun v =>
                     Mem.read32_write32_of_disjoint stA.mem (out_ptr + 4 * UInt32.ofNat k) (frame + 12) v
                       (by rw [hframe_toNat12, hout_k_toNat];
                           rcases hframe_out_disj with h | h <;> [right; left] <;> omega),
                   show ∀ v1 v2, ((stA.mem.write32 (out_ptr + 4 * UInt32.ofNat k) v1).write32
                                 (frame + 12) v2).read32 (frame + 16)
                         = stA.mem.read32 (frame + 16) from fun v1 v2 =>
                     (Mem.read32_write32_of_disjoint _ (frame + 12) (frame + 16) v2
                       (by left; rw [hframe_toNat12, hframe_toNat16])).trans
                     (Mem.read32_write32_of_disjoint stA.mem (out_ptr + 4 * UInt32.ofNat k) (frame + 16) v1
                       (by rw [hframe_toNat16, hout_k_toNat];
                           rcases hframe_out_disj with h | h <;> [right; left] <;> omega)),
                   show ∀ n, (1 : UInt32) + UInt32.ofNat n = UInt32.ofNat n + 1 from fun n => UInt32.add_comm _ _,
                   hshl_k,
                   Mem.write32_pages,
                   if_neg (show ¬(frame.toNat + (12 : UInt32).toNat + 4
                                  > stA.mem.pages * 65536) from by simp; omega),
                   if_neg (show ¬(frame.toNat + (16 : UInt32).toNat + 4
                                  > stA.mem.pages * 65536) from by simp; omega),
                   show 4 * UInt32.ofNat k + out_ptr = out_ptr + 4 * UInt32.ofNat k from UInt32.add_comm _ _,
                   UInt32.add_zero,
                   if_neg (show ¬((out_ptr + 4 * UInt32.ofNat k).toNat +
                                   (0 : UInt32).toNat + 4 > stA.mem.pages * 65536) from by
                             simp [hout_k_toNat]; omega),
                   if_neg (show ¬(frame.toNat + (12 : UInt32).toNat + 4
                                  > mem1.pages * 65536) from by
                             simp [mem1, Mem.write32_pages]; omega),
                   if_neg (show ¬(frame.toNat + (16 : UInt32).toNat + 4
                                  > mem2.pages * 65536) from by
                             simp [mem2, mem1, Mem.write32_pages]; omega)]
        simp only [stC, sB, mem1, mem2, mem3, locA18, right_j]
        rfl
      -- BCO_block at fuel 4: Break 1 → Break 0
      -- Then exec sees Break 0 → other → Break 0 stC sB
      have h_body : exec 4 m stA locA rightDrainBody env = .Break 0 stC sB := by
        show exec 4 m stA locA
          (.block 0 0 [
            .localGet 6, .load32 (12 : UInt32),
            .localGet 3, .ltU, .const (1 : UInt32), .and, .br_if 0,
            .localGet 6, .const (32 : UInt32), .add, .globalSet 0, .ret
          ] :: _) env = _
        rw [h_condblock, show (4 : Nat) = 3 + 1 from rfl, exec_block_cons, h_bco_body]
      --  break-0 witness
      refine ⟨4, fun fuel hfuel => Or.inr (Or.inl ⟨stC, sB, ?_, ?_, ?_⟩)⟩
      · -- exec result
        have hne : exec 4 m stA locA rightDrainBody env ≠ .OutOfFuel := by
          rw [h_body]; intro h; cases h
        exact (exec_fuel_mono (by omega) hne).trans h_body
      · -- DrainInv stC sB  (= DrainInv stC {sB with values = sB.values.take 0 ++ locA.values.drop 0})
        -- since sB.values = locA.values, take 0 ++ drop 0 = locA.values = sB.values, so {sB with values = locA.values} = sB
        simp only [List.take_zero, List.nil_append, List.drop_zero]
        -- Provide j+1 as the new index
        refine ⟨j + 1, by omega, by omega,
                ?_hf6, ?_h3, ?_h2, ?_h4, ?_h5,
                ?_hlparams, ?_hllocals, ?_hglobal,
                ?_hj_m, ?_hk_m, ?_hcopy, ?_hright,
                ?_hpages, ?_hk_global, ?_hright_global, ?_hout_global, ?_hpages_u32,
                ?_hright_out_disj, ?_hframe_right_disj, ?_hframe_out_disj⟩
        -- sB.get i = locA.get i for all param indices (params unchanged)
        · exact hlocA18_get6
        · have hlen17p : locA17.params.length = 6 := by simp [locA17, hlocA16_params]
          simp only [Locals.get, sB, locA18, hlen17p, show (3 : Nat) < 6 from by omega]
          simp only [Locals.get, locA17, hlocA16_params, show (3 : Nat) < 6 from by omega]
          simp only [Locals.get, hlparams, show (3 : Nat) < 6 from by omega] at h3
          exact h3
        · have hlen17p : locA17.params.length = 6 := by simp [locA17, hlocA16_params]
          simp only [Locals.get, sB, locA18, hlen17p, show (2 : Nat) < 6 from by omega]
          simp only [Locals.get, locA17, hlocA16_params, show (2 : Nat) < 6 from by omega]
          simp only [Locals.get, hlparams, show (2 : Nat) < 6 from by omega] at h2
          exact h2
        · have hlen17p : locA17.params.length = 6 := by simp [locA17, hlocA16_params]
          simp only [Locals.get, sB, locA18, hlen17p, show (4 : Nat) < 6 from by omega]
          simp only [Locals.get, locA17, hlocA16_params, show (4 : Nat) < 6 from by omega]
          simp only [Locals.get, hlparams, show (4 : Nat) < 6 from by omega] at h4
          exact h4
        · have hlen17p : locA17.params.length = 6 := by simp [locA17, hlocA16_params]
          simp only [Locals.get, sB, locA18, hlen17p, show (5 : Nat) < 6 from by omega]
          simp only [Locals.get, locA17, hlocA16_params, show (5 : Nat) < 6 from by omega]
          simp only [Locals.get, hlparams, show (5 : Nat) < 6 from by omega] at h5
          exact h5
        -- params/locals lengths unchanged
        · have hlen17p : locA17.params.length = 6 := by simp [locA17, hlocA16_params]
          simp [sB, locA18, hlen17p]
        · have hlen17p : locA17.params.length = 6 := by simp [locA17, hlocA16_params]
          have hlen17l : locA17.locals.length = 16 := by
            simp [locA17, List.length_set, hlocA16_locals]
          simp [sB, locA18, hlen17p, hlen17l, List.length_set]
        -- global 0 still exists (write32 doesn't touch globals)
        · exact ⟨_, hglobal.choose_spec⟩
        -- frame+12 after writes = j+1
        · have hj_add_one : UInt32.ofNat j + 1 = UInt32.ofNat (j + 1) := by
            apply UInt32.toNat_inj.mp
            simp only [UInt32.toNat_add, UInt32.toNat_ofNat',
                       show (1 : UInt32).toNat = 1 from rfl,
                       Nat.mod_eq_of_lt (show j + 1 < 4294967296 from by
                         have := n_right.toNat_lt; omega)]
            omega
          simp only [stC, mem3, mem2, mem1]
          rw [Mem.read32_write32_of_disjoint _ (frame + 16) (frame + 12) _
                (by right; rw [hframe_toNat12, hframe_toNat16]),
              Mem.read32_write32_same, hj_add_one]
        -- frame+16 after writes = k+1
        · have hk_add_one : UInt32.ofNat k + 1 = UInt32.ofNat (k + 1) := by
            apply UInt32.toNat_inj.mp
            simp only [UInt32.toNat_add, UInt32.toNat_ofNat',
                       show (1 : UInt32).toNat = 1 from rfl,
                       Nat.mod_eq_of_lt (show k + 1 < 4294967296 from by
                         have := n_out.toNat_lt; omega)]
            omega
          simp only [stC, mem3]
          rw [Mem.read32_write32_same, hk_add_one]
          congr 1
          omega
        -- partial copy for i < (j+1) - j₀
        · intro i hi
          by_cases hidk : i < j - j₀
          · -- i < j - j₀: previous element, preserved by write to out[k]
            have hdisj : (out_ptr + 4 * UInt32.ofNat k).toNat + 4 ≤
                (out_ptr + 4 * UInt32.ofNat (k₀ + i)).toNat ∨
                (out_ptr + 4 * UInt32.ofNat (k₀ + i)).toNat + 4 ≤
                (out_ptr + 4 * UInt32.ofNat k).toNat := by
              have hia : (out_ptr + 4 * UInt32.ofNat (k₀ + i)).toNat
                  = out_ptr.toNat + 4 * (k₀ + i) :=
                toNat_wordAddr out_ptr n_out.toNat (k₀ + i)
                  (by omega)
                  (by linarith)
              rw [hia, hout_k_toNat]
              omega
            have hread_out_i : (stC.mem.read32 (out_ptr + 4 * UInt32.ofNat (k₀ + i)))
                = stA.mem.read32 (out_ptr + 4 * UInt32.ofNat (k₀ + i)) := by
              simp only [stC, mem3, mem2, mem1]
              rw [Mem.read32_write32_of_disjoint _ (frame + 16) _ _
                    (by have hia : (out_ptr + 4 * UInt32.ofNat (k₀ + i)).toNat
                            = out_ptr.toNat + 4 * (k₀ + i) :=
                          toNat_wordAddr out_ptr n_out.toNat (k₀ + i)
                            (by omega) (by linarith)
                        rcases hframe_out_disj with h | h
                        · left; rw [hframe_toNat16, hia]; omega
                        · right; rw [hframe_toNat16, hia]; omega),
                  Mem.read32_write32_of_disjoint _ (frame + 12) _ _
                    (by have hia : (out_ptr + 4 * UInt32.ofNat (k₀ + i)).toNat
                            = out_ptr.toNat + 4 * (k₀ + i) :=
                          toNat_wordAddr out_ptr n_out.toNat (k₀ + i)
                            (by omega) (by linarith)
                        rcases hframe_out_disj with h | h
                        · left; rw [hframe_toNat12, hia]; omega
                        · right; rw [hframe_toNat12, hia]; omega),
                  Mem.read32_write32_of_disjoint _ (out_ptr + 4 * UInt32.ofNat k) _ _ hdisj]
            rw [hread_out_i]
            exact hcopy i hidk
          · -- i = j - j₀: the new element written this step
            have hieq : i = j - j₀ := by omega
            subst hieq
            have hk_eq : k₀ + (j - j₀) = k := rfl
            rw [hk_eq]
            simp only [stC, mem3, mem2, mem1]
            rw [Mem.read32_write32_of_disjoint _ (frame + 16) _ _
                  (by rcases hframe_out_disj with h | h
                      · left; rw [hframe_toNat16, hout_k_toNat]; omega
                      · right; rw [hframe_toNat16, hout_k_toNat]; omega),
                Mem.read32_write32_of_disjoint _ (frame + 12) _ _
                  (by rcases hframe_out_disj with h | h
                      · left; rw [hframe_toNat12, hout_k_toNat]; omega
                      · right; rw [hframe_toNat12, hout_k_toNat]; omega),
                Mem.read32_write32_same]
            -- right_j = stA.mem.read32(right_ptr + 4*j) = st.mem.read32(right_ptr + 4*(j₀+(j-j₀)))
            show stA.mem.read32 (right_ptr + 4 * UInt32.ofNat j) =
                st.mem.read32 (right_ptr + 4 * UInt32.ofNat (j₀ + (j - j₀)))
            rw [show j₀ + (j - j₀) = j from by omega]
            exact hright j hlt
        -- right array unchanged: all three writes are disjoint from right[i]
        · intro i hi
          simp only [stC, mem3, mem2, mem1]
          have hri_toNat : (right_ptr + 4 * UInt32.ofNat i).toNat
              = right_ptr.toNat + 4 * i :=
            toNat_wordAddr right_ptr n_right.toNat i hi (by linarith)
          rw [Mem.read32_write32_of_disjoint _ (frame + 16) _ _
                (by rw [hframe_toNat16, hri_toNat]
                    rcases hframe_right_disj with h | h <;> omega),
              Mem.read32_write32_of_disjoint _ (frame + 12) _ _
                (by rw [hframe_toNat12, hri_toNat]
                    rcases hframe_right_disj with h | h <;> omega),
              Mem.read32_write32_of_disjoint _ (out_ptr + 4 * UInt32.ofNat k) _ _
                (by rw [hout_k_toNat, hri_toNat]
                    rcases hright_out_disj with h | h
                    · right; omega
                    · left; omega)]
          exact hright i hi
        -- hpages: pages unchanged by write32
        · simp [stC, mem3, mem2, mem1, Mem.write32_pages, hpages]
        -- hk_global: unchanged
        · omega
        -- hright_global, hout_global, hpages_u32: unchanged (pages same)
        · simp [stC, mem3, mem2, mem1, Mem.write32_pages, hright_global]
        · simp [stC, mem3, mem2, mem1, Mem.write32_pages, hout_global]
        · simp [stC, mem3, mem2, mem1, Mem.write32_pages, hpages_u32]
        -- disjointness conditions: independent of memory contents
        · exact hright_out_disj
        · exact hframe_right_disj
        · exact hframe_out_disj
      · -- μ decreases: n_right.toNat - (stC.mem.read32(frame+12)).toNat < n_right.toNat - j
        simp only [stC, mem3, mem2, mem1]
        rw [Mem.read32_write32_of_disjoint _ (frame + 16) (frame + 12) _
              (by right; rw [hframe_toNat12, hframe_toNat16]),
            Mem.read32_write32_same,
            UInt32.toNat_add, UInt32.toNat_ofNat',
            show (1 : UInt32).toNat = 1 from rfl,
            hj_m, UInt32.toNat_ofNat']
        have := n_right.toNat_lt
        omega

    · -- return: j = n_right, exit
      have hj_eq : j = n_right.toNat := Nat.le_antisymm hj_hi (Nat.not_lt.mp hlt)
      have hj_nlt : ¬(UInt32.ofNat j < n_right) := by
        rw [UInt32.lt_iff_toNat_lt_toNat, UInt32.toNat_ofNat']
        have := n_right.toNat_lt; omega
      have hb12 : ¬(frame.toNat + (12 : UInt32).toNat + 4 > stA.mem.pages * 65536) := by
        simp; omega
      obtain ⟨v₀, hg⟩ := hglobal
      -- stB: store after globalSet 0 (mem unchanged)
      let stB : Store Unit :=
        { stA with globals := { globals := stA.globals.globals.set 0 (.i32 (32 + frame)) } }
      -- condBody exec at fuel 1: all simple instructions, no blocks
      -- br_if 0 sees .i32 0 → Fallthrough; then globalSet 0; ret → Return
      have h_cond0 : exec 1 m stA locA [
          .localGet 6, .load32 (12 : UInt32),
          .localGet 3, .ltU,
          .const (1 : UInt32), .and,
          .br_if 0,
          .localGet 6, .const (32 : UInt32), .add,
          .globalSet 0, .ret
        ] env = .Return stB locA.values := by
        have hgv6_c : ∀ xs, ({ locA with values := xs } : Locals).get 6 = locA.get 6 :=
          fun _ => rfl
        have hgv3_c : ∀ xs, ({ locA with values := xs } : Locals).get 3 = locA.get 3 :=
          fun _ => rfl
        simp only [exec, execOne.eq_def, hgv6_c, hgv3_c, hf6, h3, hj_m, hg,
                   if_neg hb12,
                   if_neg hj_nlt,
                   show (1 : UInt32) &&& 0 = 0 from by decide,
                   stB]
      -- exec of rightDrainBody at fuel 2: exec_block_cons peels cond_block;
      -- condBody at fuel 1 → Return propagates via the `other` arm
      have h_body1 : exec 2 m stA locA rightDrainBody env = .Return stB locA.values := by
        simp only [rightDrainBody]
        rw [show (2 : Nat) = 1 + 1 from rfl, exec_block_cons]
        simp only [h_cond0]
      -- For any fuel ≥ 2
      refine ⟨2, fun fuel hfuel => Or.inr (Or.inr ⟨stB, locA.values, ?_, ?_⟩)⟩
      · have hne : exec 2 m stA locA rightDrainBody env ≠ .OutOfFuel := by
          rw [h_body1]; intro h; cases h
        exact (exec_fuel_mono (by omega) hne).trans h_body1
      · -- Q: postcondition from hcopy (with j = n_right, j - j₀ = n_right.toNat - j₀)
        intro i hi
        have hi' : i < j - j₀ := by omega
        -- stB.mem = stA.mem (globalSet only changes globals)
        exact hcopy i hi'

private def leftDrainBody : Program := [
  .block 0 0 [
    .localGet 6, .load32 (8 : UInt32),
    .localGet 1, .ltU,
    .const (1 : UInt32), .and,
    .br_if 0,
    .localGet 6, .const (32 : UInt32), .add,
    .globalSet 0, .ret
  ],
  .localGet 6, .load32 (8 : UInt32), .localSet 19,
  .block 0 0 [
    .block 0 0 [
      .block 0 0 [
        .localGet 19, .localGet 1, .ltU, .const (1 : UInt32), .and, .eqz, .br_if 0,
        .localGet 0, .localGet 19, .const (2 : UInt32), .shl, .add, .load32 (0 : UInt32),
        .localSet 20,
        .localGet 6, .load32 (16 : UInt32), .localSet 21,
        .localGet 21, .localGet 5, .ltU, .const (1 : UInt32), .and, .br_if 1, .br 2
      ],
      .localGet 19, .localGet 1, .const (1048680 : UInt32), .call 87, .unreachable
    ],
    .localGet 4, .localGet 21, .const (2 : UInt32), .shl, .add, .localGet 20,
    .store32 (0 : UInt32),
    .localGet 6, .localGet 6, .load32 (8 : UInt32), .const (1 : UInt32), .add,
    .store32 (8 : UInt32),
    .localGet 6, .localGet 6, .load32 (16 : UInt32), .const (1 : UInt32), .add,
    .store32 (16 : UInt32),
    .br 1
  ],
  .localGet 21, .localGet 5, .const (1048696 : UInt32), .call 87, .unreachable
]

private def LeftDrainInv
    (frame out_ptr left_ptr n_left n_out : UInt32)
    (i₀ k₀ : Nat)
    (st_init : Store Unit)
    (stA : Store Unit) (locA : Locals) : Prop :=
  ∃ i : Nat,
    i₀ ≤ i ∧ i ≤ n_left.toNat ∧
    locA.get 6 = some (.i32 frame) ∧
    locA.get 1 = some (.i32 n_left) ∧
    locA.get 0 = some (.i32 left_ptr) ∧
    locA.get 4 = some (.i32 out_ptr) ∧
    locA.get 5 = some (.i32 n_out) ∧
    locA.params.length = 6 ∧
    locA.locals.length = 16 ∧
    (∃ v, stA.globals.globals[0]? = some v) ∧
    stA.mem.read32 (frame + 8) = UInt32.ofNat i ∧
    stA.mem.read32 (frame + 16) = UInt32.ofNat (k₀ + (i - i₀)) ∧
    (∀ q, q < i - i₀ →
      stA.mem.read32 (out_ptr + 4 * UInt32.ofNat (k₀ + q)) =
      st_init.mem.read32 (left_ptr + 4 * UInt32.ofNat (i₀ + q))) ∧
    (∀ q, q < n_left.toNat →
      stA.mem.read32 (left_ptr + 4 * UInt32.ofNat q) =
      st_init.mem.read32 (left_ptr + 4 * UInt32.ofNat q)) ∧
    frame.toNat + 20 ≤ stA.mem.pages * 65536 ∧
    k₀ + (n_left.toNat - i₀) ≤ n_out.toNat ∧
    left_ptr.toNat + 4 * n_left.toNat ≤ stA.mem.pages * 65536 ∧
    out_ptr.toNat + 4 * n_out.toNat ≤ stA.mem.pages * 65536 ∧
    stA.mem.pages * 65536 ≤ 4294967296 ∧
    (left_ptr.toNat + 4 * n_left.toNat ≤ out_ptr.toNat ∨
     out_ptr.toNat + 4 * n_out.toNat ≤ left_ptr.toNat) ∧
    (frame.toNat + 20 ≤ left_ptr.toNat ∨
     left_ptr.toNat + 4 * n_left.toNat ≤ frame.toNat) ∧
    (frame.toNat + 20 ≤ out_ptr.toNat ∨
     out_ptr.toNat + 4 * n_out.toNat ≤ frame.toNat)

theorem left_drain_spec
    {m : Module} {env : HostEnv Unit}
    (st : Store Unit) (locals : Locals)
    (frame out_ptr left_ptr n_left n_out : UInt32)
    (i₀ k₀ : Nat)
    (hI₀ : LeftDrainInv frame out_ptr left_ptr n_left n_out i₀ k₀ st st locals) :
    wp_wasm_prop m st locals [.loop 0 0 leftDrainBody] env
      (fun st' _ =>
        ∀ q, q < n_left.toNat - i₀ →
          st'.mem.read32 (out_ptr + 4 * UInt32.ofNat (k₀ + q)) =
          st.mem.read32 (left_ptr + 4 * UInt32.ofNat (i₀ + q))) := by
  apply wp_wasm_prop_loop
      (I := LeftDrainInv frame out_ptr left_ptr n_left n_out i₀ k₀ st)
      (μ := fun stA _ => n_left.toNat - (stA.mem.read32 (frame + 8)).toNat)
  · exact hI₀
  · intro stA locA ⟨i, hi_lo, hi_hi, hf6, h1, h0, h4, h5,
                   hlparams, hllocals, hglobal,
                   hi_m, hk_m, hcopy, hleft,
                   hpages, hk_global, hleft_global, hout_global, hpages_u32,
                   hleft_out_disj, hframe_left_disj, hframe_out_disj⟩
    by_cases hlt : i < n_left.toNat
    · -- Break-0 case (i < n_left): one copy step then loop restart
      let k := k₀ + (i - i₀)
      have hk_lt : k < n_out.toNat := by omega
      have hi_lt32 : UInt32.ofNat i < n_left := by
        rw [UInt32.lt_iff_toNat_lt_toNat, UInt32.toNat_ofNat']
        have := n_left.toNat_lt; omega
      have hk_lt32 : UInt32.ofNat (k₀ + (i - i₀)) < n_out := by
        rw [UInt32.lt_iff_toNat_lt_toNat, UInt32.toNat_ofNat']
        have := n_out.toNat_lt; omega
      have hframe_toNat8 : (frame + 8).toNat = frame.toNat + 8 := by
        rw [UInt32.toNat_add]; simp [UInt32.toNat_ofNat']; omega
      have hframe_toNat16 : (frame + 16).toNat = frame.toNat + 16 := by
        rw [UInt32.toNat_add]; simp [UInt32.toNat_ofNat']; omega
      have hleft_i_toNat : (left_ptr + 4 * UInt32.ofNat i).toNat
          = left_ptr.toNat + 4 * i :=
        toNat_wordAddr left_ptr n_left.toNat i hlt (by linarith)
      have hout_k_toNat : (out_ptr + 4 * UInt32.ofNat k).toNat
          = out_ptr.toNat + 4 * k :=
        toNat_wordAddr out_ptr n_out.toNat k (by omega) (by linarith)
      let left_i := stA.mem.read32 (left_ptr + 4 * UInt32.ofNat i)
      let mem1 := stA.mem.write32 (out_ptr + 4 * UInt32.ofNat k) left_i
      let mem2 := mem1.write32 (frame + 8) (UInt32.ofNat i + 1)
      let mem3 := mem2.write32 (frame + 16) (UInt32.ofNat k + 1)
      let stC : Store Unit := { stA with mem := mem3 }
      let locA19 : Locals :=
        { locA with locals := locA.locals.set 13 (.i32 (UInt32.ofNat i)) }
      let locA20 : Locals :=
        { locA19 with locals := locA19.locals.set 14 (.i32 left_i) }
      let locA21 : Locals :=
        { locA20 with locals := locA20.locals.set 15 (.i32 (UInt32.ofNat k)) }
      let sB : Locals := { locA21 with values := locA.values }
      have h_cond : exec 3 m stA locA [
          .localGet 6, .load32 (8 : UInt32),
          .localGet 1, .ltU, .const (1 : UInt32), .and, .br_if 0,
          .localGet 6, .const (32 : UInt32), .add, .globalSet 0, .ret
        ] env = .Break 0 stA locA := by
          have hgv1' : ∀ xs, ({ locA with values := xs } : Locals).get 1 = locA.get 1 :=
            fun _ => rfl
          simp only [exec, execOne.eq_def, hgv1', hf6, h1, hi_m,
                     if_neg (show ¬(frame.toNat + (8 : UInt32).toNat + 4
                                    > stA.mem.pages * 65536) from by simp; omega),
                     if_pos hi_lt32,
                     show (1 : UInt32) &&& 1 = 1 from by decide]
          rfl
      have h_condblock : exec 4 m stA locA
          (.block 0 0 [
            .localGet 6, .load32 (8 : UInt32),
            .localGet 1, .ltU,
            .const (1 : UInt32), .and,
            .br_if 0,
            .localGet 6, .const (32 : UInt32), .add,
            .globalSet 0, .ret
          ] :: [
            .localGet 6, .load32 (8 : UInt32), .localSet 19,
            .block 0 0 [
              .block 0 0 [
                .block 0 0 [
                  .localGet 19, .localGet 1, .ltU, .const (1 : UInt32), .and, .eqz, .br_if 0,
                  .localGet 0, .localGet 19, .const (2 : UInt32), .shl, .add,
                  .load32 (0 : UInt32), .localSet 20,
                  .localGet 6, .load32 (16 : UInt32), .localSet 21,
                  .localGet 21, .localGet 5, .ltU, .const (1 : UInt32), .and, .br_if 1, .br 2
                ],
                .localGet 19, .localGet 1, .const (1048680 : UInt32), .call 87, .unreachable
              ],
              .localGet 4, .localGet 21, .const (2 : UInt32), .shl, .add, .localGet 20,
              .store32 (0 : UInt32),
              .localGet 6, .localGet 6, .load32 (8 : UInt32), .const (1 : UInt32), .add,
              .store32 (8 : UInt32),
              .localGet 6, .localGet 6, .load32 (16 : UInt32), .const (1 : UInt32), .add,
              .store32 (16 : UInt32), .br 1
            ],
            .localGet 21, .localGet 5, .const (1048696 : UInt32), .call 87, .unreachable
          ]) env =
          exec 4 m stA locA19 [
            .block 0 0 [
              .block 0 0 [
                .block 0 0 [
                  .localGet 19, .localGet 1, .ltU, .const (1 : UInt32), .and, .eqz, .br_if 0,
                  .localGet 0, .localGet 19, .const (2 : UInt32), .shl, .add,
                  .load32 (0 : UInt32), .localSet 20,
                  .localGet 6, .load32 (16 : UInt32), .localSet 21,
                  .localGet 21, .localGet 5, .ltU, .const (1 : UInt32), .and, .br_if 1, .br 2
                ],
                .localGet 19, .localGet 1, .const (1048680 : UInt32), .call 87, .unreachable
              ],
              .localGet 4, .localGet 21, .const (2 : UInt32), .shl, .add, .localGet 20,
              .store32 (0 : UInt32),
              .localGet 6, .localGet 6, .load32 (8 : UInt32), .const (1 : UInt32), .add,
              .store32 (8 : UInt32),
              .localGet 6, .localGet 6, .load32 (16 : UInt32), .const (1 : UInt32), .add,
              .store32 (16 : UInt32), .br 1
            ],
            .localGet 21, .localGet 5, .const (1048696 : UInt32), .call 87, .unreachable
          ] env := by
        rw [show (4 : Nat) = 3 + 1 from rfl, exec_block_cons, h_cond]
        simp only [List.take_zero, List.drop_zero, List.nil_append]
        simp only [exec, execOne.eq_def, hf6, hi_m,
                   if_neg (show ¬(frame.toNat + (8 : UInt32).toNat + 4
                                   > stA.mem.pages * 65536) from by simp; omega),
                   Locals.set?, hlparams, hllocals, List.length_set,
                   if_neg (show ¬((19 : Nat) < 6) from by omega),
                   if_pos (show (19 : Nat) < 6 + 16 from by omega),
                   show (19 : Nat) - 6 = 13 from by omega,
                   show Locals.mk locA.params (locA.locals.set 13 (Value.i32 (UInt32.ofNat i)))
                         locA.values = locA19 from rfl]
      have hset19 : locA.set? 19 (.i32 (UInt32.ofNat i)) = some locA19 := by
        simp only [Locals.set?, locA19, hlparams, hllocals,
                   show ¬((19 : Nat) < 6) from by omega,
                   show (19 : Nat) < 6 + 16 from by omega,
                   show (19 : Nat) - 6 = 13 from by omega,
                   List.length_set]
        rfl
      have hlocA19_get6 : locA19.get 6 = some (.i32 frame) := by
        simp only [Locals.get, locA19, hlparams, hllocals, List.length_set,
                   show ¬((6 : Nat) < 6) from by omega,
                   show (6 : Nat) < 6 + 16 from by omega,
                   show (6 : Nat) - 6 = 0 from by omega,
                   List.getElem?_set,
                   show ¬(13 = 0 ∧ 0 < 16) from by omega]
        simpa [Locals.get, hlparams, hllocals, show ¬((6:Nat) < 6) from by omega] using hf6
      have hlocA19_get1 : locA19.get 1 = some (.i32 n_left) := by
        simp only [Locals.get, locA19, hlparams, show (1 : Nat) < 6 from by omega] at h1 ⊢
        exact h1
      have hlocA19_get0 : locA19.get 0 = some (.i32 left_ptr) := by
        simp only [Locals.get, locA19, hlparams, show (0 : Nat) < 6 from by omega] at h0 ⊢
        exact h0
      have hlocA19_get5 : locA19.get 5 = some (.i32 n_out) := by
        simp only [Locals.get, locA19, hlparams, show (5 : Nat) < 6 from by omega] at h5 ⊢
        exact h5
      have hlocA19_get4 : locA19.get 4 = some (.i32 out_ptr) := by
        simp only [Locals.get, locA19, hlparams, show (4 : Nat) < 6 from by omega] at h4 ⊢
        exact h4
      have hlocA19_get19 : locA19.get 19 = some (.i32 (UInt32.ofNat i)) := by
        simp only [Locals.get, locA19, hlparams, hllocals, List.length_set,
                   show ¬((19 : Nat) < 6) from by omega,
                   show (19 : Nat) < 6 + 16 from by omega,
                   show (19 : Nat) - 6 = 13 from by omega,
                   List.getElem?_set, show (13 : Nat) < 16 from by omega,
                   if_true, if_false]
      have hlocA19_params : locA19.params.length = 6 := by simp [locA19, hlparams]
      have hlocA19_locals : locA19.locals.length = 16 := by
        simp [locA19, List.length_set, hllocals]
      have hset20 : locA19.set? 20 (.i32 left_i) = some locA20 := by
        simp only [Locals.set?, locA20, hlocA19_params, hlocA19_locals, List.length_set,
                   show ¬((20 : Nat) < 6) from by omega,
                   show (20 : Nat) < 6 + 16 from by omega,
                   show (20 : Nat) - 6 = 14 from by omega]
        rfl
      have hset21 : locA20.set? 21 (.i32 (UInt32.ofNat k)) = some locA21 := by
        have hlen20p : locA20.params.length = 6 := by simp [locA20, hlocA19_params]
        have hlen20l : locA20.locals.length = 16 := by
          simp [locA20, List.length_set, hlocA19_locals]
        simp only [Locals.set?, locA21, hlen20p, hlen20l, List.length_set,
                   show ¬((21 : Nat) < 6) from by omega,
                   show (21 : Nat) < 6 + 16 from by omega,
                   show (21 : Nat) - 6 = 15 from by omega]
        rfl
      have hlocA21_get21 : locA21.get 21 = some (.i32 (UInt32.ofNat k)) := by
        have hlen20p : locA20.params.length = 6 := by simp [locA20, hlocA19_params]
        have hlen20l : locA20.locals.length = 16 := by
          simp [locA20, List.length_set, hlocA19_locals]
        simp only [Locals.get, locA21, hlen20p, hlen20l, List.length_set,
                   show ¬((21 : Nat) < 6) from by omega,
                   show (21 : Nat) < 6 + 16 from by omega,
                   show (21 : Nat) - 6 = 15 from by omega,
                   List.getElem?_set, show (15 : Nat) < 16 from by omega,
                   if_true, if_false]
      have hlocA21_get5 : locA21.get 5 = some (.i32 n_out) := by
        have hlen20p : locA20.params.length = 6 := by simp [locA20, hlocA19_params]
        simp only [Locals.get, locA21, locA20, locA19,
                   hlen20p, hlocA19_params, hlparams,
                   show (5 : Nat) < 6 from by omega] at h5 ⊢
        exact h5
      have hlocA21_get4 : locA21.get 4 = some (.i32 out_ptr) := by
        have hlen20p : locA20.params.length = 6 := by simp [locA20, hlocA19_params]
        simp only [Locals.get, locA21, locA20, locA19,
                   hlen20p, hlocA19_params, hlparams,
                   show (4 : Nat) < 6 from by omega] at h4 ⊢
        exact h4
      have hlocA21_get6 : locA21.get 6 = some (.i32 frame) := by
        have hlen20p : locA20.params.length = 6 := by simp [locA20, hlocA19_params]
        have hlen20l : locA20.locals.length = 16 := by
          simp [locA20, List.length_set, hlocA19_locals]
        simp only [Locals.get, locA21, locA20, locA19,
                   hlen20p, hlen20l, hlocA19_params, hlocA19_locals, hlparams, hllocals,
                   List.length_set,
                   show ¬((6 : Nat) < 6) from by omega,
                   show (6 : Nat) < 6 + 16 from by omega,
                   show (6 : Nat) - 6 = 0 from by omega,
                   List.getElem?_set,
                   show ¬(15 = 0 ∧ (0 : Nat) < 16) from by omega,
                   show ¬(14 = 0 ∧ (0 : Nat) < 16) from by omega,
                   show ¬(13 = 0 ∧ (0 : Nat) < 16) from by omega] at hf6 ⊢
        exact hf6
      have hlocA21_get20 : locA21.get 20 = some (.i32 left_i) := by
        have hlen20p : locA20.params.length = 6 := by simp [locA20, hlocA19_params]
        have hlen20l : locA20.locals.length = 16 := by
          simp [locA20, List.length_set, hlocA19_locals]
        simp only [Locals.get, locA21, locA20, hlen20p, hlen20l, hlocA19_locals,
                   List.length_set,
                   show ¬((20 : Nat) < 6) from by omega,
                   show (20 : Nat) < 6 + 16 from by omega,
                   show (20 : Nat) - 6 = 14 from by omega,
                   List.getElem?_set,
                   show (15 : Nat) ≠ 14 from by omega, if_false,
                   if_true, show (14 : Nat) < 16 from by omega]
      have hshl_i : UInt32.ofNat i <<< ((2 : UInt32) % 32) = 4 * UInt32.ofNat i := by
        rw [show (2 : UInt32) % 32 = 2 from by decide]
        apply UInt32.toNat_inj.mp
        have hi_bnd : i < 2 ^ 30 := by have := n_left.toNat_lt; omega
        simp only [UInt32.toNat_mul, UInt32.toNat_ofNat',
                   show (4 : UInt32).toNat = 4 from rfl,
                   Nat.mod_eq_of_lt (show i < 4294967296 from by omega),
                   Nat.mod_eq_of_lt (show i * 4 < 4294967296 from by omega)]
        simp [UInt32.shiftLeft, Fin.shiftLeft, Nat.shiftLeft_eq]
        omega
      have hlocA20_get6 : locA20.get 6 = some (.i32 frame) := by
        show ({ locA19 with locals := locA19.locals.set 14 (.i32 left_i) } : Locals).get 6 = _
        simp only [Locals.get, hlocA19_params, hlocA19_locals, List.length_set,
                   show ¬((6 : Nat) < 6) from by omega,
                   show (6 : Nat) < 6 + 16 from by omega,
                   show (6 : Nat) - 6 = 0 from by omega,
                   List.getElem?_set,
                   show (14 : Nat) ≠ 0 from by omega, if_false]
        simpa [Locals.get, hlocA19_params, hlocA19_locals,
               show ¬((6 : Nat) < 6) from by omega] using hlocA19_get6
      have h_bci_body : exec 1 m stA locA19 [
          .localGet 19, .localGet 1, .ltU, .const (1 : UInt32), .and, .eqz, .br_if 0,
          .localGet 0, .localGet 19, .const (2 : UInt32), .shl, .add,
          .load32 (0 : UInt32), .localSet 20,
          .localGet 6, .load32 (16 : UInt32), .localSet 21,
          .localGet 21, .localGet 5, .ltU, .const (1 : UInt32), .and, .br_if 1, .br 2
        ] env = .Break 1 stA { locA21 with values := locA.values } := by
          have hgv19 : ∀ xs, ({ locA19 with values := xs } : Locals).get 19 = locA19.get 19 :=
            fun _ => rfl
          have hgv1' : ∀ xs, ({ locA19 with values := xs } : Locals).get 1 = locA19.get 1 :=
            fun _ => rfl
          have hgv0 : ∀ xs, ({ locA19 with values := xs } : Locals).get 0 = locA19.get 0 :=
            fun _ => rfl
          have hgv6 : ∀ xs, ({ locA19 with values := xs } : Locals).get 6 = locA19.get 6 :=
            fun _ => rfl
          have hgv20_6 : ∀ xs, ({ locA20 with values := xs } : Locals).get 6 = locA20.get 6 :=
            fun _ => rfl
          have hgv21_21 : ∀ xs, ({ locA21 with values := xs } : Locals).get 21 = locA21.get 21 :=
            fun _ => rfl
          have hgv21_5 : ∀ xs, ({ locA21 with values := xs } : Locals).get 5 = locA21.get 5 :=
            fun _ => rfl
          have hget20_6_raw : ∀ xs,
              (Locals.mk locA19.params (locA19.locals.set 14 (.i32 left_i)) xs).get 6
              = some (.i32 frame) := fun xs => (hgv20_6 xs).trans hlocA20_get6
          have hget21_21_raw : ∀ xs,
              (Locals.mk locA19.params
                ((locA19.locals.set 14 (.i32 left_i)).set 15
                  (.i32 (UInt32.ofNat (k₀ + (i - i₀))))) xs).get 21
              = some (.i32 (UInt32.ofNat (k₀ + (i - i₀)))) :=
            fun xs => (hgv21_21 xs).trans hlocA21_get21
          have hget21_5_raw : ∀ xs,
              (Locals.mk locA19.params
                ((locA19.locals.set 14 (.i32 left_i)).set 15
                  (.i32 (UInt32.ofNat (k₀ + (i - i₀))))) xs).get 5
              = some (.i32 n_out) :=
            fun xs => (hgv21_5 xs).trans hlocA21_get5
          simp only [exec, execOne.eq_def, Locals.set?,
                     hgv19, hgv1', hgv0, hgv6,
                     hlocA19_get19, hlocA19_get1,
                     if_pos hi_lt32,
                     show (1 : UInt32) &&& 1 = 1 from by decide,
                     show (if (1 : UInt32) = 0 then (1 : UInt32) else 0) = 0 from by decide,
                     hlocA19_get0, hlocA19_get6, hk_m,
                     if_neg (show ¬(frame.toNat + (16 : UInt32).toNat + 4
                                    > stA.mem.pages * 65536) from by simp; omega),
                     hlocA19_params, hlocA19_locals, List.length_set,
                     if_false, if_true,
                     show ¬((20 : Nat) < 6) from by omega,
                     show (20 : Nat) < 6 + 16 from by omega,
                     show (20 : Nat) - 6 = 14 from by omega,
                     show (14 : Nat) < 16 from by omega,
                     hget20_6_raw,
                     show ¬((21 : Nat) < 6) from by omega,
                     show (21 : Nat) < 6 + 16 from by omega,
                     show (21 : Nat) - 6 = 15 from by omega,
                     show (15 : Nat) < 16 from by omega,
                     hget21_21_raw, hget21_5_raw,
                     if_neg (show ¬((4 * UInt32.ofNat i + left_ptr).toNat +
                                     UInt32.toNat 0 + 4 > stA.mem.pages * 65536) from by
                               rw [show 4 * UInt32.ofNat i + left_ptr =
                                     left_ptr + 4 * UInt32.ofNat i from UInt32.add_comm _ _,
                                   hleft_i_toNat, show UInt32.toNat 0 = 0 from rfl]
                               omega),
                     show stA.mem.read32 (4 * UInt32.ofNat i + left_ptr + (0 : UInt32))
                         = left_i from by
                       rw [show 4 * UInt32.ofNat i + left_ptr + (0 : UInt32)
                               = left_ptr + 4 * UInt32.ofNat i from by
                                 rw [UInt32.add_comm (4 * UInt32.ofNat i) left_ptr,
                                     UInt32.add_zero]],
                     if_pos hk_lt32,
                     show (1 : UInt32) &&& 1 = 1 from by decide,
                     hshl_i]
          simp only [locA19, locA20, locA21]
          rfl
      have h_bci_block : exec 2 m stA locA19 [
          .block 0 0 [
            .localGet 19, .localGet 1, .ltU, .const (1 : UInt32), .and, .eqz, .br_if 0,
            .localGet 0, .localGet 19, .const (2 : UInt32), .shl, .add,
            .load32 (0 : UInt32), .localSet 20,
            .localGet 6, .load32 (16 : UInt32), .localSet 21,
            .localGet 21, .localGet 5, .ltU, .const (1 : UInt32), .and, .br_if 1, .br 2
          ],
          .localGet 19, .localGet 1, .const (1048680 : UInt32), .call 87, .unreachable
        ] env = .Break 0 stA { locA21 with values := locA.values } := by
        rw [show (2 : Nat) = 1 + 1 from rfl, exec_block_cons, h_bci_body]
      have hmem1_frame8 : mem1.read32 (frame + 8) = stA.mem.read32 (frame + 8) :=
        Mem.read32_write32_of_disjoint stA.mem (out_ptr + 4 * UInt32.ofNat k) (frame + 8) left_i
          (by rw [hframe_toNat8, hout_k_toNat]; rcases hframe_out_disj with h | h <;> [right; left] <;> omega)
      have hmem1_frame16 : mem1.read32 (frame + 16) = stA.mem.read32 (frame + 16) :=
        Mem.read32_write32_of_disjoint stA.mem (out_ptr + 4 * UInt32.ofNat k) (frame + 16) left_i
          (by rw [hframe_toNat16, hout_k_toNat]; rcases hframe_out_disj with h | h <;> [right; left] <;> omega)
      have hmem2_frame16 : mem2.read32 (frame + 16) = stA.mem.read32 (frame + 16) :=
        (Mem.read32_write32_of_disjoint mem1 (frame + 8) (frame + 16) _
          (by left; rw [hframe_toNat8, hframe_toNat16]; omega)).trans hmem1_frame16
      have hshl_k : UInt32.ofNat k <<< ((2 : UInt32) % 32) = 4 * UInt32.ofNat k := by
        rw [show (2 : UInt32) % 32 = 2 from by decide]
        apply UInt32.toNat_inj.mp
        have hk_bnd : k < 2 ^ 30 := by have := n_out.toNat_lt; omega
        simp only [UInt32.toNat_mul, UInt32.toNat_ofNat',
                   show (4 : UInt32).toNat = 4 from rfl,
                   Nat.mod_eq_of_lt (show k < 4294967296 from by omega),
                   Nat.mod_eq_of_lt (show k * 4 < 4294967296 from by omega)]
        simp [UInt32.shiftLeft, Fin.shiftLeft, Nat.shiftLeft_eq]
        omega
      have h_bco_body : exec 3 m stA locA19 [
          .block 0 0 [
            .block 0 0 [
              .localGet 19, .localGet 1, .ltU, .const (1 : UInt32), .and, .eqz, .br_if 0,
              .localGet 0, .localGet 19, .const (2 : UInt32), .shl, .add,
              .load32 (0 : UInt32), .localSet 20,
              .localGet 6, .load32 (16 : UInt32), .localSet 21,
              .localGet 21, .localGet 5, .ltU, .const (1 : UInt32), .and, .br_if 1, .br 2
            ],
            .localGet 19, .localGet 1, .const (1048680 : UInt32), .call 87, .unreachable
          ],
          .localGet 4, .localGet 21, .const (2 : UInt32), .shl, .add, .localGet 20,
          .store32 (0 : UInt32),
          .localGet 6, .localGet 6, .load32 (8 : UInt32), .const (1 : UInt32), .add,
          .store32 (8 : UInt32),
          .localGet 6, .localGet 6, .load32 (16 : UInt32), .const (1 : UInt32), .add,
          .store32 (16 : UInt32), .br 1
        ] env = .Break 1 stC sB := by
        rw [show (3 : Nat) = 2 + 1 from rfl, exec_block_cons, h_bci_block]
        simp only [List.take_zero, List.drop_zero, List.nil_append]
        have hgv21_4 : ∀ xs, ({ locA21 with values := xs } : Locals).get 4 = locA21.get 4 :=
          fun _ => rfl
        have hgv21_21 : ∀ xs, ({ locA21 with values := xs } : Locals).get 21 = locA21.get 21 :=
          fun _ => rfl
        have hgv21_20 : ∀ xs, ({ locA21 with values := xs } : Locals).get 20 = locA21.get 20 :=
          fun _ => rfl
        have hgv21_6 : ∀ xs, ({ locA21 with values := xs } : Locals).get 6 = locA21.get 6 :=
          fun _ => rfl
        simp only [exec, execOne.eq_def,
                   hgv21_4, hgv21_21, hgv21_20, hgv21_6,
                   hlocA21_get4, hlocA21_get21, hlocA21_get20, hlocA21_get6,
                   hi_m, hk_m,
                   show ∀ v, (stA.mem.write32 (out_ptr + 4 * UInt32.ofNat k) v).read32 (frame + 8)
                         = stA.mem.read32 (frame + 8) from fun v =>
                     Mem.read32_write32_of_disjoint stA.mem
                       (out_ptr + 4 * UInt32.ofNat k) (frame + 8) v
                       (by rw [hframe_toNat8, hout_k_toNat];
                           rcases hframe_out_disj with h | h <;> [right; left] <;> omega),
                   show ∀ v1 v2,
                       ((stA.mem.write32 (out_ptr + 4 * UInt32.ofNat k) v1).write32
                         (frame + 8) v2).read32 (frame + 16)
                       = stA.mem.read32 (frame + 16) from fun v1 v2 =>
                     (Mem.read32_write32_of_disjoint _ (frame + 8) (frame + 16) v2
                       (by left; rw [hframe_toNat8, hframe_toNat16]; omega)).trans
                     (Mem.read32_write32_of_disjoint stA.mem
                       (out_ptr + 4 * UInt32.ofNat k) (frame + 16) v1
                       (by rw [hframe_toNat16, hout_k_toNat];
                           rcases hframe_out_disj with h | h <;> [right; left] <;> omega)),
                   show ∀ n, (1 : UInt32) + UInt32.ofNat n = UInt32.ofNat n + 1 from
                     fun n => UInt32.add_comm _ _,
                   hshl_k,
                   Mem.write32_pages,
                   if_neg (show ¬(frame.toNat + (8 : UInt32).toNat + 4
                                  > stA.mem.pages * 65536) from by simp; omega),
                   if_neg (show ¬(frame.toNat + (16 : UInt32).toNat + 4
                                  > stA.mem.pages * 65536) from by simp; omega),
                   show 4 * UInt32.ofNat k + out_ptr = out_ptr + 4 * UInt32.ofNat k from
                     UInt32.add_comm _ _,
                   UInt32.add_zero,
                   if_neg (show ¬((out_ptr + 4 * UInt32.ofNat k).toNat +
                                   (0 : UInt32).toNat + 4 > stA.mem.pages * 65536) from by
                             simp [hout_k_toNat]; omega),
                   if_neg (show ¬(frame.toNat + (8 : UInt32).toNat + 4
                                  > mem1.pages * 65536) from by
                             simp [mem1, Mem.write32_pages]; omega),
                   if_neg (show ¬(frame.toNat + (16 : UInt32).toNat + 4
                                  > mem2.pages * 65536) from by
                             simp [mem2, mem1, Mem.write32_pages]; omega)]
        simp only [stC, sB, mem1, mem2, mem3, locA21, left_i]
        rfl
      have h_body : exec 4 m stA locA leftDrainBody env = .Break 0 stC sB := by
        show exec 4 m stA locA
          (.block 0 0 [
            .localGet 6, .load32 (8 : UInt32),
            .localGet 1, .ltU,
            .const (1 : UInt32), .and,
            .br_if 0,
            .localGet 6, .const (32 : UInt32), .add,
            .globalSet 0, .ret
          ] :: _) env = _
        rw [h_condblock, show (4 : Nat) = 3 + 1 from rfl, exec_block_cons, h_bco_body]
      refine ⟨4, fun fuel hfuel => Or.inr (Or.inl ⟨stC, sB, ?_, ?_, ?_⟩)⟩
      · have hne : exec 4 m stA locA leftDrainBody env ≠ .OutOfFuel := by
          rw [h_body]; intro h; cases h
        exact (exec_fuel_mono (by omega) hne).trans h_body
      · simp only [List.take_zero, List.nil_append, List.drop_zero]
        refine ⟨i + 1, by omega, by omega,
                ?_hf6, ?_h1, ?_h0, ?_h4, ?_h5,
                ?_hlparams, ?_hllocals, ?_hglobal,
                ?_hi_m, ?_hk_m, ?_hcopy, ?_hleft,
                ?_hpages, ?_hk_global, ?_hleft_global, ?_hout_global, ?_hpages_u32,
                ?_hleft_out_disj, ?_hframe_left_disj, ?_hframe_out_disj⟩
        · exact hlocA21_get6
        · have hlen20p : locA20.params.length = 6 := by simp [locA20, hlocA19_params]
          simp only [Locals.get, sB, locA21, hlen20p, show (1 : Nat) < 6 from by omega]
          simp only [Locals.get, locA20, hlocA19_params, show (1 : Nat) < 6 from by omega]
          simp only [Locals.get, hlparams, show (1 : Nat) < 6 from by omega] at h1
          exact h1
        · have hlen20p : locA20.params.length = 6 := by simp [locA20, hlocA19_params]
          simp only [Locals.get, sB, locA21, hlen20p, show (0 : Nat) < 6 from by omega]
          simp only [Locals.get, locA20, hlocA19_params, show (0 : Nat) < 6 from by omega]
          simp only [Locals.get, hlparams, show (0 : Nat) < 6 from by omega] at h0
          exact h0
        · have hlen20p : locA20.params.length = 6 := by simp [locA20, hlocA19_params]
          simp only [Locals.get, sB, locA21, hlen20p, show (4 : Nat) < 6 from by omega]
          simp only [Locals.get, locA20, hlocA19_params, show (4 : Nat) < 6 from by omega]
          simp only [Locals.get, hlparams, show (4 : Nat) < 6 from by omega] at h4
          exact h4
        · have hlen20p : locA20.params.length = 6 := by simp [locA20, hlocA19_params]
          simp only [Locals.get, sB, locA21, hlen20p, show (5 : Nat) < 6 from by omega]
          simp only [Locals.get, locA20, hlocA19_params, show (5 : Nat) < 6 from by omega]
          simp only [Locals.get, hlparams, show (5 : Nat) < 6 from by omega] at h5
          exact h5
        · have hlen20p : locA20.params.length = 6 := by simp [locA20, hlocA19_params]
          simp [sB, locA21, hlen20p]
        · have hlen20p : locA20.params.length = 6 := by simp [locA20, hlocA19_params]
          have hlen20l : locA20.locals.length = 16 := by
            simp [locA20, List.length_set, hlocA19_locals]
          simp [sB, locA21, hlen20p, hlen20l, List.length_set]
        · exact ⟨_, hglobal.choose_spec⟩
        · have hi_add_one : UInt32.ofNat i + 1 = UInt32.ofNat (i + 1) := by
            apply UInt32.toNat_inj.mp
            simp only [UInt32.toNat_add, UInt32.toNat_ofNat',
                       show (1 : UInt32).toNat = 1 from rfl,
                       Nat.mod_eq_of_lt (show i + 1 < 4294967296 from by
                         have := n_left.toNat_lt; omega)]
            omega
          simp only [stC, mem3, mem2, mem1]
          rw [Mem.read32_write32_of_disjoint _ (frame + 16) (frame + 8) _
                (by right; rw [hframe_toNat8, hframe_toNat16]; omega),
              Mem.read32_write32_same, hi_add_one]
        · have hk_add_one : UInt32.ofNat k + 1 = UInt32.ofNat (k + 1) := by
            apply UInt32.toNat_inj.mp
            simp only [UInt32.toNat_add, UInt32.toNat_ofNat',
                       show (1 : UInt32).toNat = 1 from rfl,
                       Nat.mod_eq_of_lt (show k + 1 < 4294967296 from by
                         have := n_out.toNat_lt; omega)]
            omega
          simp only [stC, mem3]
          rw [Mem.read32_write32_same, hk_add_one]
          congr 1
          omega
        · intro q hq
          by_cases hqdk : q < i - i₀
          · have hdisj : (out_ptr + 4 * UInt32.ofNat k).toNat + 4 ≤
                (out_ptr + 4 * UInt32.ofNat (k₀ + q)).toNat ∨
                (out_ptr + 4 * UInt32.ofNat (k₀ + q)).toNat + 4 ≤
                (out_ptr + 4 * UInt32.ofNat k).toNat := by
              have hia : (out_ptr + 4 * UInt32.ofNat (k₀ + q)).toNat
                  = out_ptr.toNat + 4 * (k₀ + q) :=
                toNat_wordAddr out_ptr n_out.toNat (k₀ + q) (by omega) (by linarith)
              rw [hia, hout_k_toNat]; omega
            have hread_out_q : stC.mem.read32 (out_ptr + 4 * UInt32.ofNat (k₀ + q))
                = stA.mem.read32 (out_ptr + 4 * UInt32.ofNat (k₀ + q)) := by
              simp only [stC, mem3, mem2, mem1]
              rw [Mem.read32_write32_of_disjoint _ (frame + 16) _ _
                    (by have hia : (out_ptr + 4 * UInt32.ofNat (k₀ + q)).toNat
                            = out_ptr.toNat + 4 * (k₀ + q) :=
                          toNat_wordAddr out_ptr n_out.toNat (k₀ + q) (by omega) (by linarith)
                        rcases hframe_out_disj with h | h
                        · left; rw [hframe_toNat16, hia]; omega
                        · right; rw [hframe_toNat16, hia]; omega),
                  Mem.read32_write32_of_disjoint _ (frame + 8) _ _
                    (by have hia : (out_ptr + 4 * UInt32.ofNat (k₀ + q)).toNat
                            = out_ptr.toNat + 4 * (k₀ + q) :=
                          toNat_wordAddr out_ptr n_out.toNat (k₀ + q) (by omega) (by linarith)
                        rcases hframe_out_disj with h | h
                        · left; rw [hframe_toNat8, hia]; omega
                        · right; rw [hframe_toNat8, hia]; omega),
                  Mem.read32_write32_of_disjoint _ (out_ptr + 4 * UInt32.ofNat k) _ _ hdisj]
            rw [hread_out_q]; exact hcopy q hqdk
          · have hqeq : q = i - i₀ := by omega
            subst hqeq
            have hk_eq : k₀ + (i - i₀) = k := rfl
            rw [hk_eq]
            simp only [stC, mem3, mem2, mem1]
            rw [Mem.read32_write32_of_disjoint _ (frame + 16) _ _
                  (by rcases hframe_out_disj with h | h
                      · left; rw [hframe_toNat16, hout_k_toNat]; omega
                      · right; rw [hframe_toNat16, hout_k_toNat]; omega),
                Mem.read32_write32_of_disjoint _ (frame + 8) _ _
                  (by rcases hframe_out_disj with h | h
                      · left; rw [hframe_toNat8, hout_k_toNat]; omega
                      · right; rw [hframe_toNat8, hout_k_toNat]; omega),
                Mem.read32_write32_same]
            show stA.mem.read32 (left_ptr + 4 * UInt32.ofNat i) =
                st.mem.read32 (left_ptr + 4 * UInt32.ofNat (i₀ + (i - i₀)))
            rw [show i₀ + (i - i₀) = i from by omega]
            exact hleft i hlt
        · intro q hq
          simp only [stC, mem3, mem2, mem1]
          have hlq_toNat : (left_ptr + 4 * UInt32.ofNat q).toNat
              = left_ptr.toNat + 4 * q :=
            toNat_wordAddr left_ptr n_left.toNat q hq (by linarith)
          rw [Mem.read32_write32_of_disjoint _ (frame + 16) _ _
                (by rw [hframe_toNat16, hlq_toNat]
                    rcases hframe_left_disj with h | h <;> omega),
              Mem.read32_write32_of_disjoint _ (frame + 8) _ _
                (by rw [hframe_toNat8, hlq_toNat]
                    rcases hframe_left_disj with h | h <;> omega),
              Mem.read32_write32_of_disjoint _ (out_ptr + 4 * UInt32.ofNat k) _ _
                (by rw [hout_k_toNat, hlq_toNat]
                    rcases hleft_out_disj with h | h
                    · right; omega
                    · left; omega)]
          exact hleft q hq
        · simp [stC, mem3, mem2, mem1, Mem.write32_pages, hpages]
        · omega
        · simp [stC, mem3, mem2, mem1, Mem.write32_pages, hleft_global]
        · simp [stC, mem3, mem2, mem1, Mem.write32_pages, hout_global]
        · simp [stC, mem3, mem2, mem1, Mem.write32_pages, hpages_u32]
        · exact hleft_out_disj
        · exact hframe_left_disj
        · exact hframe_out_disj
      · simp only [stC, mem3, mem2, mem1]
        rw [Mem.read32_write32_of_disjoint _ (frame + 16) (frame + 8) _
              (by right; rw [hframe_toNat8, hframe_toNat16]; omega),
            Mem.read32_write32_same,
            UInt32.toNat_add, UInt32.toNat_ofNat',
            show (1 : UInt32).toNat = 1 from rfl,
            hi_m, UInt32.toNat_ofNat']
        have := n_left.toNat_lt
        omega

    · -- Return case (i = n_left): exit via .ret
      have hi_eq : i = n_left.toNat := Nat.le_antisymm hi_hi (Nat.not_lt.mp hlt)
      have hi_nlt : ¬(UInt32.ofNat i < n_left) := by
        rw [UInt32.lt_iff_toNat_lt_toNat, UInt32.toNat_ofNat']
        have := n_left.toNat_lt; omega
      have hb8 : ¬(frame.toNat + (8 : UInt32).toNat + 4 > stA.mem.pages * 65536) := by
        simp; omega
      obtain ⟨v₀, hg⟩ := hglobal
      let stB : Store Unit :=
        { stA with globals := { globals := stA.globals.globals.set 0 (.i32 (32 + frame)) } }
      have h_cond0 : exec 1 m stA locA [
          .localGet 6, .load32 (8 : UInt32),
          .localGet 1, .ltU,
          .const (1 : UInt32), .and,
          .br_if 0,
          .localGet 6, .const (32 : UInt32), .add,
          .globalSet 0, .ret
        ] env = .Return stB locA.values := by
        have hgv6_c : ∀ xs, ({ locA with values := xs } : Locals).get 6 = locA.get 6 :=
          fun _ => rfl
        have hgv1_c : ∀ xs, ({ locA with values := xs } : Locals).get 1 = locA.get 1 :=
          fun _ => rfl
        simp only [exec, execOne.eq_def, hgv6_c, hgv1_c, hf6, h1, hi_m, hg,
                   if_neg hb8,
                   if_neg hi_nlt,
                   show (1 : UInt32) &&& 0 = 0 from by decide,
                   stB]
      have h_body1 : exec 2 m stA locA leftDrainBody env = .Return stB locA.values := by
        simp only [leftDrainBody]
        rw [show (2 : Nat) = 1 + 1 from rfl, exec_block_cons]
        simp only [h_cond0]
      refine ⟨2, fun fuel hfuel => Or.inr (Or.inr ⟨stB, locA.values, ?_, ?_⟩)⟩
      · have hne : exec 2 m stA locA leftDrainBody env ≠ .OutOfFuel := by
          rw [h_body1]; intro h; cases h
        exact (exec_fuel_mono (by omega) hne).trans h_body1
      · intro q hq
        have hq' : q < i - i₀ := by omega
        exact hcopy q hq'

end Wasm.SepLogic.MergeSort
