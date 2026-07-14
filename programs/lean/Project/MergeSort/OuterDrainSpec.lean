import CodeLib.SepLogic.Adequacy
import Project.MergeSort.ContentLemmas
import Project.MergeSort.MergeSepLogic

namespace Wasm.SepLogic.MergeSort

open Wasm Project.MergeSort Project.MergeSort.Spec Project.MergeSort.Framing

variable [WasmHeapGS]

private def innerRightDrainBody : Program := [
  .block 0 0 [
    .localGet 6, .load32 (12 : UInt32),
    .localGet 3, .ltU, .const (1 : UInt32), .and, .br_if 0,
    .localGet 6, .const (32 : UInt32), .add, .globalSet 0, .ret
  ],
  .localGet 6, .load32 (12 : UInt32), .localSet 16,
  .block 0 0 [
    .block 0 0 [
      .block 0 0 [
        .localGet 16, .localGet 3, .ltU, .const (1 : UInt32), .and, .eqz, .br_if 0,
        .localGet 2, .localGet 16, .const (2 : UInt32), .shl, .add, .load32 (0 : UInt32),
        .localSet 17,
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
    .store32 (16 : UInt32),
    .br 1
  ]
]

def outerDrainBody : Program := [
  .block 0 0 [
    .localGet 6, .load32 (8 : UInt32),
    .localGet 1, .ltU, .const (1 : UInt32), .and, .br_if 0,
    .loop 0 0 innerRightDrainBody,
    .localGet 18, .localGet 5, .const (1048664 : UInt32), .call 87, .unreachable
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
  ]
]

theorem func6_drop28_eq :
    func6.drop 28 = [.loop 0 0 outerDrainBody,
                     .localGet 21, .localGet 5, .const (1048696 : UInt32), .call 87, .unreachable] := by
  rfl

-- helper: extract execOne from exec [inst]
private theorem execOne_of_exec_singleton
    {f : Nat} {m : Module} {st : Store Unit} {loc : Locals} {inst : Instruction} {env : HostEnv Unit}
    {st' : Store Unit} {vs : List Value}
    (h : exec f m st loc [inst] env = .Return st' vs) :
    execOne f m st loc inst env = .Return st' vs := by
  simp only [exec] at h
  cases hx : execOne f m st loc inst env with
  | Fallthrough s l => simp only [hx, exec] at h; exact h
  | Return s v => simp only [hx] at h; exact h
  | OutOfFuel => simp only [hx] at h; exact h
  | Break => simp only [hx] at h; exact h
  | ReturnCall => simp only [hx] at h; exact h
  | Invalid => simp only [hx] at h; exact h
  | Trap => simp only [hx] at h; exact h
  | Throwing => simp only [hx] at h; exact h

private theorem exec_append {α : Type} (fuel : Nat) (m : Module) (st : Store α) (s : Locals)
    (p1 p2 : Program) (env : HostEnv α) :
    exec fuel m st s (p1 ++ p2) env =
    (match exec fuel m st s p1 env with
     | .Fallthrough st' s' => exec fuel m st' s' p2 env
     | other => other) := by
  induction p1 generalizing st s with
  | nil => simp [exec]
  | cons i p1' ih =>
    simp only [List.cons_append, exec]
    cases execOne fuel m st s i env with
    | Fallthrough st' s' => exact ih st' s'
    | _ => rfl

set_option maxHeartbeats 2000000 in
private theorem inner_right_drain_terminates
    {m : Module} {env : HostEnv Unit}
    (st_init stA : Store Unit) (locA : Locals)
    (frame out_ptr right_ptr n_right n_out : UInt32)
    (j₀ k₀ : Nat)
    (hj₀_hi : j₀ ≤ n_right.toNat)
    (hf6 : locA.get 6 = some (.i32 frame))
    (h3  : locA.get 3 = some (.i32 n_right))
    (h2  : locA.get 2 = some (.i32 right_ptr))
    (h4  : locA.get 4 = some (.i32 out_ptr))
    (h5  : locA.get 5 = some (.i32 n_out))
    (hlparams : locA.params.length = 6)
    (hllocals : locA.locals.length = 16)
    (hglobal : ∃ v, stA.globals.globals[0]? = some v)
    (hj₀_m  : stA.mem.read32 (frame + 12) = UInt32.ofNat j₀)
    (hk₀_m  : stA.mem.read32 (frame + 16) = UInt32.ofNat k₀)
    (hright : ∀ i, i < n_right.toNat →
        stA.mem.read32 (right_ptr + 4 * UInt32.ofNat i) =
        st_init.mem.read32 (right_ptr + 4 * UInt32.ofNat i))
    (hpages      : frame.toNat + 20 ≤ stA.mem.pages * 65536)
    (hk_bound    : k₀ + (n_right.toNat - j₀) ≤ n_out.toNat)
    (hright_bnd  : right_ptr.toNat + 4 * n_right.toNat ≤ stA.mem.pages * 65536)
    (hout_bnd    : out_ptr.toNat   + 4 * n_out.toNat   ≤ stA.mem.pages * 65536)
    (hpages_u32  : stA.mem.pages * 65536 ≤ 4294967296)
    (hright_out_disj   : right_ptr.toNat + 4 * n_right.toNat ≤ out_ptr.toNat ∨
                          out_ptr.toNat   + 4 * n_out.toNat   ≤ right_ptr.toNat)
    (hframe_right_disj : frame.toNat + 20 ≤ right_ptr.toNat ∨
                          right_ptr.toNat + 4 * n_right.toNat ≤ frame.toNat)
    (hframe_out_disj   : frame.toNat + 20 ≤ out_ptr.toNat ∨
                          out_ptr.toNat + 4 * n_out.toNat ≤ frame.toNat) :
    ∃ N stF,
      exec N m stA locA [.loop 0 0 innerRightDrainBody] env = .Return stF locA.values ∧
      (∀ i, i < n_right.toNat - j₀ →
        stF.mem.read32 (out_ptr + 4 * UInt32.ofNat (k₀ + i)) =
        st_init.mem.read32 (right_ptr + 4 * UInt32.ofNat (j₀ + i))) ∧
      (∀ q, q < k₀ →
        stF.mem.read32 (out_ptr + 4 * UInt32.ofNat q) =
        stA.mem.read32 (out_ptr + 4 * UInt32.ofNat q)) := by
  -- strong induction on n_right.toNat - j
  suffices key : ∀ n stB locB j k,
      n_right.toNat - j = n →
      j₀ ≤ j → j ≤ n_right.toNat →
      locB.get 6 = some (.i32 frame) →
      locB.get 3 = some (.i32 n_right) →
      locB.get 2 = some (.i32 right_ptr) →
      locB.get 4 = some (.i32 out_ptr) →
      locB.get 5 = some (.i32 n_out) →
      locB.params.length = 6 → locB.locals.length = 16 →
      (∃ v, stB.globals.globals[0]? = some v) →
      stB.mem.read32 (frame + 12) = UInt32.ofNat j →
      stB.mem.read32 (frame + 16) = UInt32.ofNat k →
      k = k₀ + (j - j₀) →
      (∀ i, i < j - j₀ →
        stB.mem.read32 (out_ptr + 4 * UInt32.ofNat (k₀ + i)) =
        st_init.mem.read32 (right_ptr + 4 * UInt32.ofNat (j₀ + i))) →
      (∀ i, i < n_right.toNat →
        stB.mem.read32 (right_ptr + 4 * UInt32.ofNat i) =
        st_init.mem.read32 (right_ptr + 4 * UInt32.ofNat i)) →
      frame.toNat + 20 ≤ stB.mem.pages * 65536 →
      right_ptr.toNat + 4 * n_right.toNat ≤ stB.mem.pages * 65536 →
      out_ptr.toNat   + 4 * n_out.toNat   ≤ stB.mem.pages * 65536 →
      stB.mem.pages * 65536 ≤ 4294967296 →
      (right_ptr.toNat + 4 * n_right.toNat ≤ out_ptr.toNat ∨
       out_ptr.toNat   + 4 * n_out.toNat   ≤ right_ptr.toNat) →
      (frame.toNat + 20 ≤ right_ptr.toNat ∨
       right_ptr.toNat + 4 * n_right.toNat ≤ frame.toNat) →
      (frame.toNat + 20 ≤ out_ptr.toNat ∨
       out_ptr.toNat + 4 * n_out.toNat ≤ frame.toNat) →
      ∃ N stF,
        exec N m stB locB [.loop 0 0 innerRightDrainBody] env = .Return stF locB.values ∧
        (∀ i, i < n_right.toNat - j →
          stF.mem.read32 (out_ptr + 4 * UInt32.ofNat (k₀ + (j - j₀) + i)) =
          st_init.mem.read32 (right_ptr + 4 * UInt32.ofNat (j + i))) ∧
        (∀ q, q < k →
          stF.mem.read32 (out_ptr + 4 * UInt32.ofNat q) =
          stB.mem.read32 (out_ptr + 4 * UInt32.ofNat q)) from by
    obtain ⟨N, stF, hret, hcont, hpres⟩ :=
      key (n_right.toNat - j₀) stA locA j₀ k₀
        rfl (le_refl _) hj₀_hi hf6 h3 h2 h4 h5 hlparams hllocals
        hglobal hj₀_m hk₀_m (by omega)
        (by intro _ hi; omega)
        hright hpages hright_bnd hout_bnd hpages_u32
        hright_out_disj hframe_right_disj hframe_out_disj
    refine ⟨N, stF, hret, ?_, ?_⟩
    · intro i hi; have := hcont i (by simpa using hi)
      simpa using this
    · intro q hq; exact hpres q (by simpa using hq)
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro stB locB j k hn hj_lo hj_hi hf6' h3' h2' h4' h5' hlparams' hllocals'
          hglobal' hj_m hk_m hkeq hcopy hright' hpages' hright_bnd' hout_bnd'
          hpages_u32' hright_out_disj' hframe_right_disj' hframe_out_disj'
    by_cases hlt : j < n_right.toNat
    · -- Break-0 arm: copy right[j] to out[k]
      let k_val := k₀ + (j - j₀)
      have hk_lt : k_val < n_out.toNat := by omega
      have hj_lt32 : UInt32.ofNat j < n_right := by
        rw [UInt32.lt_iff_toNat_lt_toNat, UInt32.toNat_ofNat']
        have := n_right.toNat_lt; omega
      have hk_lt32 : UInt32.ofNat k_val < n_out := by
        rw [UInt32.lt_iff_toNat_lt_toNat, UInt32.toNat_ofNat']
        have := n_out.toNat_lt; omega
      have hframe_toNat12 : (frame + 12).toNat = frame.toNat + 12 := by
        rw [UInt32.toNat_add]; simp [UInt32.toNat_ofNat']; omega
      have hframe_toNat16 : (frame + 16).toNat = frame.toNat + 16 := by
        rw [UInt32.toNat_add]; simp [UInt32.toNat_ofNat']; omega
      have hright_j_toNat : (right_ptr + 4 * UInt32.ofNat j).toNat = right_ptr.toNat + 4 * j :=
        toNat_wordAddr right_ptr n_right.toNat j hlt (by linarith)
      have hout_k_toNat : (out_ptr + 4 * UInt32.ofNat k_val).toNat = out_ptr.toNat + 4 * k_val :=
        toNat_wordAddr out_ptr n_out.toNat k_val (by omega) (by linarith)
      let right_j := stB.mem.read32 (right_ptr + 4 * UInt32.ofNat j)
      let mem1 := stB.mem.write32 (out_ptr + 4 * UInt32.ofNat k_val) right_j
      let mem2 := mem1.write32 (frame + 12) (UInt32.ofNat j + 1)
      let mem3 := mem2.write32 (frame + 16) (UInt32.ofNat k_val + 1)
      let stC : Store Unit := { stB with mem := mem3 }
      let locB16 : Locals :=
        { locB with locals := locB.locals.set 10 (.i32 (UInt32.ofNat j)) }
      let locB17 : Locals :=
        { locB16 with locals := locB16.locals.set 11 (.i32 right_j) }
      let locB18 : Locals :=
        { locB17 with locals := locB17.locals.set 12 (.i32 (UInt32.ofNat k_val)) }
      let sB : Locals := { locB18 with values := locB.values }
      -- h_cond: exec 3 condBody = Break 0 when j < n_right
      have h_cond : exec 3 m stB locB [
          .localGet 6, .load32 (12 : UInt32),
          .localGet 3, .ltU, .const (1 : UInt32), .and, .br_if 0,
          .localGet 6, .const (32 : UInt32), .add, .globalSet 0, .ret
        ] env = .Break 0 stB locB := by
        have hgv3 : ∀ xs, ({ locB with values := xs } : Locals).get 3 = locB.get 3 := fun _ => rfl
        simp only [exec, execOne.eq_def, hgv3, hf6', h3', hj_m,
                   if_neg (show ¬(frame.toNat + (12 : UInt32).toNat + 4
                                   > stB.mem.pages * 65536) from by simp; omega),
                   if_pos hj_lt32,
                   show (1 : UInt32) &&& 1 = 1 from by decide]
        rfl
      -- h_condblock: exec 4 (COND_BLOCK :: [load12, localSet16, BCO]) = exec 4 locB16 [BCO]
      have h_condblock : exec 4 m stB locB
          (.block 0 0 [.localGet 6, .load32 (12 : UInt32), .localGet 3, .ltU,
                       .const (1 : UInt32), .and, .br_if 0,
                       .localGet 6, .const (32 : UInt32), .add, .globalSet 0, .ret] ::
           [.localGet 6, .load32 (12 : UInt32), .localSet 16,
            .block 0 0 [
              .block 0 0 [
                .block 0 0 [
                  .localGet 16, .localGet 3, .ltU, .const (1 : UInt32), .and, .eqz, .br_if 0,
                  .localGet 2, .localGet 16, .const (2 : UInt32), .shl, .add, .load32 (0 : UInt32),
                  .localSet 17,
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
            ]]) env =
          exec 4 m stB locB16
            [.block 0 0 [
              .block 0 0 [
                .block 0 0 [
                  .localGet 16, .localGet 3, .ltU, .const (1 : UInt32), .and, .eqz, .br_if 0,
                  .localGet 2, .localGet 16, .const (2 : UInt32), .shl, .add, .load32 (0 : UInt32),
                  .localSet 17,
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
            ]] env := by
        rw [show (4 : Nat) = 3 + 1 from rfl, exec_block_cons, h_cond]
        simp only [List.take_zero, List.drop_zero, List.nil_append]
        simp only [exec, execOne.eq_def, hf6', hj_m,
                   if_neg (show ¬(frame.toNat + (12 : UInt32).toNat + 4
                                   > stB.mem.pages * 65536) from by simp; omega),
                   Locals.set?, hlparams', hllocals', List.length_set,
                   if_neg (show ¬((16 : Nat) < 6) from by omega),
                   if_pos (show (16 : Nat) < 6 + 16 from by omega),
                   show (16 : Nat) - 6 = 10 from by omega,
                   show Locals.mk locB.params (locB.locals.set 10 (Value.i32 (UInt32.ofNat j)))
                         locB.values = locB16 from rfl]
      -- local access helpers for locB16
      have hlocB16_get6 : locB16.get 6 = some (.i32 frame) := by
        simp only [Locals.get, locB16, hlparams', hllocals', List.length_set,
                   show ¬((6 : Nat) < 6) from by omega,
                   show (6 : Nat) < 6 + 16 from by omega,
                   show (6 : Nat) - 6 = 0 from by omega,
                   List.getElem?_set,
                   show ¬(10 = 0 ∧ 0 < 16) from by omega]
        simpa [Locals.get, hlparams', hllocals', show ¬((6 : Nat) < 6) from by omega] using hf6'
      have hlocB16_get3 : locB16.get 3 = some (.i32 n_right) := by
        simp only [Locals.get, locB16, hlparams', show (3 : Nat) < 6 from by omega] at h3' ⊢; exact h3'
      have hlocB16_get2 : locB16.get 2 = some (.i32 right_ptr) := by
        simp only [Locals.get, locB16, hlparams', show (2 : Nat) < 6 from by omega] at h2' ⊢; exact h2'
      have hlocB16_get5 : locB16.get 5 = some (.i32 n_out) := by
        simp only [Locals.get, locB16, hlparams', show (5 : Nat) < 6 from by omega] at h5' ⊢; exact h5'
      have hlocB16_get4 : locB16.get 4 = some (.i32 out_ptr) := by
        simp only [Locals.get, locB16, hlparams', show (4 : Nat) < 6 from by omega] at h4' ⊢; exact h4'
      have hlocB16_get16 : locB16.get 16 = some (.i32 (UInt32.ofNat j)) := by
        simp only [Locals.get, locB16, hlparams', hllocals', List.length_set,
                   show ¬((16 : Nat) < 6) from by omega,
                   show (16 : Nat) < 6 + 16 from by omega,
                   show (16 : Nat) - 6 = 10 from by omega,
                   List.getElem?_set, show (10 : Nat) < 16 from by omega,
                   if_true, if_false]
      have hlocB16_params : locB16.params.length = 6 := by simp [locB16, hlparams']
      have hlocB16_locals : locB16.locals.length = 16 := by simp [locB16, List.length_set, hllocals']
      -- set? helpers
      have hset17 : locB16.set? 17 (.i32 right_j) = some locB17 := by
        simp only [Locals.set?, locB17, hlocB16_params, hlocB16_locals, List.length_set,
                   show ¬((17 : Nat) < 6) from by omega,
                   show (17 : Nat) < 6 + 16 from by omega,
                   show (17 : Nat) - 6 = 11 from by omega]; rfl
      have hset18 : locB17.set? 18 (.i32 (UInt32.ofNat k_val)) = some locB18 := by
        have hlen17p : locB17.params.length = 6 := by simp [locB17, hlocB16_params]
        have hlen17l : locB17.locals.length = 16 := by simp [locB17, List.length_set, hlocB16_locals]
        simp only [Locals.set?, locB18, hlen17p, hlen17l, List.length_set,
                   show ¬((18 : Nat) < 6) from by omega,
                   show (18 : Nat) < 6 + 16 from by omega,
                   show (18 : Nat) - 6 = 12 from by omega]; rfl
      have hlocB18_get18 : locB18.get 18 = some (.i32 (UInt32.ofNat k_val)) := by
        have hlen17p : locB17.params.length = 6 := by simp [locB17, hlocB16_params]
        have hlen17l : locB17.locals.length = 16 := by simp [locB17, List.length_set, hlocB16_locals]
        simp only [Locals.get, locB18, hlen17p, hlen17l, List.length_set,
                   show ¬((18 : Nat) < 6) from by omega,
                   show (18 : Nat) < 6 + 16 from by omega,
                   show (18 : Nat) - 6 = 12 from by omega,
                   List.getElem?_set, show (12 : Nat) < 16 from by omega,
                   if_true, if_false]
      have hlocB18_get5 : locB18.get 5 = some (.i32 n_out) := by
        have hlen17p : locB17.params.length = 6 := by simp [locB17, hlocB16_params]
        simp only [Locals.get, locB18, locB17, locB16,
                   hlen17p, hlocB16_params, hlparams', show (5 : Nat) < 6 from by omega] at h5' ⊢
        exact h5'
      have hlocB18_get4 : locB18.get 4 = some (.i32 out_ptr) := by
        have hlen17p : locB17.params.length = 6 := by simp [locB17, hlocB16_params]
        simp only [Locals.get, locB18, locB17, locB16,
                   hlen17p, hlocB16_params, hlparams', show (4 : Nat) < 6 from by omega] at h4' ⊢
        exact h4'
      have hlocB18_get6 : locB18.get 6 = some (.i32 frame) := by
        have hlen17p : locB17.params.length = 6 := by simp [locB17, hlocB16_params]
        have hlen17l : locB17.locals.length = 16 := by simp [locB17, List.length_set, hlocB16_locals]
        simp only [Locals.get, locB18, locB17, locB16,
                   hlen17p, hlen17l, hlocB16_params, hlocB16_locals, hlparams', hllocals',
                   List.length_set,
                   show ¬((6 : Nat) < 6) from by omega,
                   show (6 : Nat) < 6 + 16 from by omega,
                   show (6 : Nat) - 6 = 0 from by omega,
                   List.getElem?_set,
                   show ¬(12 = 0 ∧ (0 : Nat) < 16) from by omega,
                   show ¬(11 = 0 ∧ (0 : Nat) < 16) from by omega,
                   show ¬(10 = 0 ∧ (0 : Nat) < 16) from by omega] at hf6' ⊢
        exact hf6'
      have hlocB18_get17 : locB18.get 17 = some (.i32 right_j) := by
        have hlen17p : locB17.params.length = 6 := by simp [locB17, hlocB16_params]
        have hlen17l : locB17.locals.length = 16 := by simp [locB17, List.length_set, hlocB16_locals]
        simp only [Locals.get, locB18, locB17, hlen17p, hlen17l, hlocB16_locals,
                   List.length_set,
                   show ¬((17 : Nat) < 6) from by omega,
                   show (17 : Nat) < 6 + 16 from by omega,
                   show (17 : Nat) - 6 = 11 from by omega,
                   List.getElem?_set,
                   show (12 : Nat) ≠ 11 from by omega, if_false,
                   if_true, show (11 : Nat) < 16 from by omega]
      -- shl: j <<< 2 = 4 * j
      have hshl_j : UInt32.ofNat j <<< ((2 : UInt32) % 32) = 4 * UInt32.ofNat j := by
        rw [show (2 : UInt32) % 32 = 2 from by decide]
        apply UInt32.toNat_inj.mp
        have hj_bnd : j < 2 ^ 30 := by have := n_right.toNat_lt; omega
        simp only [UInt32.toNat_mul, UInt32.toNat_ofNat',
                   show (4 : UInt32).toNat = 4 from rfl,
                   Nat.mod_eq_of_lt (show j < 4294967296 from by omega),
                   Nat.mod_eq_of_lt (show j * 4 < 4294967296 from by omega)]
        simp [UInt32.shiftLeft, Fin.shiftLeft, Nat.shiftLeft_eq]; omega
      have hk_m' : stB.mem.read32 (frame + 16) = UInt32.ofNat k_val := by
        rw [hk_m]; congr 1
      -- h_bci_body: BCI block body at fuel 1 → Break 1
      have h_bci_body : exec 1 m stB locB16 [
          .localGet 16, .localGet 3, .ltU, .const (1 : UInt32), .and, .eqz, .br_if 0,
          .localGet 2, .localGet 16, .const (2 : UInt32), .shl, .add,
          .load32 (0 : UInt32), .localSet 17,
          .localGet 6, .load32 (16 : UInt32), .localSet 18,
          .localGet 18, .localGet 5, .ltU, .const (1 : UInt32), .and, .br_if 1, .br 2
        ] env = .Break 1 stB { locB18 with values := locB.values } := by
        have hgv16 : ∀ xs, ({ locB16 with values := xs } : Locals).get 16 = locB16.get 16 := fun _ => rfl
        have hgv3' : ∀ xs, ({ locB16 with values := xs } : Locals).get 3 = locB16.get 3 := fun _ => rfl
        have hgv2 : ∀ xs, ({ locB16 with values := xs } : Locals).get 2 = locB16.get 2 := fun _ => rfl
        have hgv6 : ∀ xs, ({ locB16 with values := xs } : Locals).get 6 = locB16.get 6 := fun _ => rfl
        have hgv17_6 : ∀ xs, ({ locB17 with values := xs } : Locals).get 6 = locB17.get 6 := fun _ => rfl
        have hgv18_18 : ∀ xs, ({ locB18 with values := xs } : Locals).get 18 = locB18.get 18 := fun _ => rfl
        have hgv18_5 : ∀ xs, ({ locB18 with values := xs } : Locals).get 5 = locB18.get 5 := fun _ => rfl
        have hlocB17_get6 : locB17.get 6 = some (.i32 frame) := by
          show ({ locB16 with locals := locB16.locals.set 11 (.i32 right_j) } : Locals).get 6 = _
          simp only [Locals.get, hlocB16_params, hlocB16_locals, List.length_set,
                     show ¬((6 : Nat) < 6) from by omega,
                     show (6 : Nat) < 6 + 16 from by omega,
                     show (6 : Nat) - 6 = 0 from by omega,
                     List.getElem?_set, show (11 : Nat) ≠ 0 from by omega, if_false]
          simpa [Locals.get, hlocB16_params, hlocB16_locals, show ¬((6 : Nat) < 6) from by omega] using hlocB16_get6
        have hget17_6_raw : ∀ xs,
            (Locals.mk locB16.params (locB16.locals.set 11 (.i32 right_j)) xs).get 6
            = some (.i32 frame) := fun xs => (hgv17_6 xs).trans hlocB17_get6
        have hget18_18_raw : ∀ xs,
            (Locals.mk locB16.params
              ((locB16.locals.set 11 (.i32 right_j)).set 12 (.i32 (UInt32.ofNat k_val))) xs).get 18
            = some (.i32 (UInt32.ofNat k_val)) := fun xs => (hgv18_18 xs).trans hlocB18_get18
        have hget18_5_raw : ∀ xs,
            (Locals.mk locB16.params
              ((locB16.locals.set 11 (.i32 right_j)).set 12 (.i32 (UInt32.ofNat k_val))) xs).get 5
            = some (.i32 n_out) := fun xs => (hgv18_5 xs).trans hlocB18_get5
        simp only [exec, execOne.eq_def, Locals.set?,
                   hgv16, hgv3', hgv2, hgv6,
                   hlocB16_get16, hlocB16_get3,
                   if_pos hj_lt32,
                   show (1 : UInt32) &&& 1 = 1 from by decide,
                   show (if (1 : UInt32) = 0 then (1 : UInt32) else 0) = 0 from by decide,
                   hlocB16_get2, hlocB16_get6, hk_m',
                   if_neg (show ¬(frame.toNat + (16 : UInt32).toNat + 4
                                   > stB.mem.pages * 65536) from by simp; omega),
                   hlocB16_params, hlocB16_locals, List.length_set,
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
                                   UInt32.toNat 0 + 4 > stB.mem.pages * 65536) from by
                             rw [show 4 * UInt32.ofNat j + right_ptr =
                                   right_ptr + 4 * UInt32.ofNat j from UInt32.add_comm _ _,
                                 hright_j_toNat, show UInt32.toNat 0 = 0 from rfl]; omega),
                   show stB.mem.read32 (4 * UInt32.ofNat j + right_ptr + (0 : UInt32))
                       = right_j from by
                     rw [show 4 * UInt32.ofNat j + right_ptr + (0 : UInt32)
                             = right_ptr + 4 * UInt32.ofNat j from by
                               rw [UInt32.add_comm (4 * UInt32.ofNat j) right_ptr, UInt32.add_zero]],
                   if_pos hk_lt32,
                   show (1 : UInt32) &&& 1 = 1 from by decide,
                   hshl_j]
        simp only [locB16, locB17, locB18]
        rfl
      -- h_bci_block
      have h_bci_block : exec 2 m stB locB16 [
          .block 0 0 [
            .localGet 16, .localGet 3, .ltU, .const (1 : UInt32), .and, .eqz, .br_if 0,
            .localGet 2, .localGet 16, .const (2 : UInt32), .shl, .add,
            .load32 (0 : UInt32), .localSet 17,
            .localGet 6, .load32 (16 : UInt32), .localSet 18,
            .localGet 18, .localGet 5, .ltU, .const (1 : UInt32), .and, .br_if 1, .br 2
          ],
          .localGet 16, .localGet 3, .const (1048648 : UInt32), .call 87, .unreachable
        ] env = .Break 0 stB { locB18 with values := locB.values } := by
        rw [show (2 : Nat) = 1 + 1 from rfl, exec_block_cons, h_bci_body]
      -- shl for k_val
      have hshl_k : UInt32.ofNat k_val <<< ((2 : UInt32) % 32) = 4 * UInt32.ofNat k_val := by
        rw [show (2 : UInt32) % 32 = 2 from by decide]
        apply UInt32.toNat_inj.mp
        have hk_bnd : k_val < 2 ^ 30 := by have := n_out.toNat_lt; omega
        simp only [UInt32.toNat_mul, UInt32.toNat_ofNat',
                   show (4 : UInt32).toNat = 4 from rfl,
                   Nat.mod_eq_of_lt (show k_val < 4294967296 from by omega),
                   Nat.mod_eq_of_lt (show k_val * 4 < 4294967296 from by omega)]
        simp [UInt32.shiftLeft, Fin.shiftLeft, Nat.shiftLeft_eq]; omega
      -- h_bco_body
      have h_bco_body : exec 3 m stB locB16 [
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
        have hgv18_4 : ∀ xs, ({ locB18 with values := xs } : Locals).get 4 = locB18.get 4 := fun _ => rfl
        have hgv18_18 : ∀ xs, ({ locB18 with values := xs } : Locals).get 18 = locB18.get 18 := fun _ => rfl
        have hgv18_17 : ∀ xs, ({ locB18 with values := xs } : Locals).get 17 = locB18.get 17 := fun _ => rfl
        have hgv18_6 : ∀ xs, ({ locB18 with values := xs } : Locals).get 6 = locB18.get 6 := fun _ => rfl
        simp only [exec, execOne.eq_def,
                   hgv18_4, hgv18_18, hgv18_17, hgv18_6,
                   hlocB18_get4, hlocB18_get18, hlocB18_get17, hlocB18_get6,
                   hj_m, hk_m',
                   show ∀ v, (stB.mem.write32 (out_ptr + 4 * UInt32.ofNat k_val) v).read32 (frame + 12)
                         = stB.mem.read32 (frame + 12) from fun v =>
                     Mem.read32_write32_of_disjoint stB.mem (out_ptr + 4 * UInt32.ofNat k_val) (frame + 12) v
                       (by rw [hframe_toNat12, hout_k_toNat];
                           rcases hframe_out_disj' with h | h <;> [right; left] <;> omega),
                   show ∀ v1 v2, ((stB.mem.write32 (out_ptr + 4 * UInt32.ofNat k_val) v1).write32
                                 (frame + 12) v2).read32 (frame + 16)
                         = stB.mem.read32 (frame + 16) from fun v1 v2 =>
                     (Mem.read32_write32_of_disjoint _ (frame + 12) (frame + 16) v2
                       (by left; rw [hframe_toNat12, hframe_toNat16])).trans
                     (Mem.read32_write32_of_disjoint stB.mem (out_ptr + 4 * UInt32.ofNat k_val) (frame + 16) v1
                       (by rw [hframe_toNat16, hout_k_toNat];
                           rcases hframe_out_disj' with h | h <;> [right; left] <;> omega)),
                   show ∀ n, (1 : UInt32) + UInt32.ofNat n = UInt32.ofNat n + 1 from fun n => UInt32.add_comm _ _,
                   hshl_k,
                   Mem.write32_pages,
                   if_neg (show ¬(frame.toNat + (12 : UInt32).toNat + 4
                                   > stB.mem.pages * 65536) from by simp; omega),
                   if_neg (show ¬(frame.toNat + (16 : UInt32).toNat + 4
                                   > stB.mem.pages * 65536) from by simp; omega),
                   show 4 * UInt32.ofNat k_val + out_ptr = out_ptr + 4 * UInt32.ofNat k_val from UInt32.add_comm _ _,
                   UInt32.add_zero,
                   if_neg (show ¬((out_ptr + 4 * UInt32.ofNat k_val).toNat +
                                   (0 : UInt32).toNat + 4 > stB.mem.pages * 65536) from by
                             simp [hout_k_toNat]; omega),
                   if_neg (show ¬(frame.toNat + (12 : UInt32).toNat + 4
                                   > mem1.pages * 65536) from by
                             simp [mem1, Mem.write32_pages]; omega),
                   if_neg (show ¬(frame.toNat + (16 : UInt32).toNat + 4
                                   > mem2.pages * 65536) from by
                             simp [mem2, mem1, Mem.write32_pages]; omega)]
        simp only [stC, sB, mem1, mem2, mem3, locB18, right_j]
        rfl
      -- h_body: exec 4 innerRightDrainBody = Break 0 stC sB
      have h_body : exec 4 m stB locB innerRightDrainBody env = .Break 0 stC sB := by
        show exec 4 m stB locB (.block 0 0 _ :: _) env = _
        rw [h_condblock, show (4 : Nat) = 3 + 1 from rfl, exec_block_cons, h_bco_body]
      -- invariant maintenance for stC / sB
      have hmem1_frame12 : mem1.read32 (frame + 12) = stB.mem.read32 (frame + 12) :=
        Mem.read32_write32_of_disjoint stB.mem (out_ptr + 4 * UInt32.ofNat k_val) (frame + 12) right_j
          (by rw [hframe_toNat12, hout_k_toNat]; rcases hframe_out_disj' with h | h <;> [right; left] <;> omega)
      have hmem1_frame16 : mem1.read32 (frame + 16) = stB.mem.read32 (frame + 16) :=
        Mem.read32_write32_of_disjoint stB.mem (out_ptr + 4 * UInt32.ofNat k_val) (frame + 16) right_j
          (by rw [hframe_toNat16, hout_k_toNat]; rcases hframe_out_disj' with h | h <;> [right; left] <;> omega)
      -- stC.mem.read32 (frame+12) = j+1
      have hj_next : UInt32.ofNat j + 1 = UInt32.ofNat (j + 1) := by
        apply UInt32.toNat_inj.mp
        simp only [UInt32.toNat_add, UInt32.toNat_ofNat',
                   show (1 : UInt32).toNat = 1 from rfl,
                   Nat.mod_eq_of_lt (show j + 1 < 4294967296 from by have := n_right.toNat_lt; omega)]
        omega
      have hj_m_next : stC.mem.read32 (frame + 12) = UInt32.ofNat (j + 1) := by
        simp only [stC, mem3, mem2, mem1]
        rw [Mem.read32_write32_of_disjoint _ (frame + 16) (frame + 12) _
              (by right; rw [hframe_toNat12, hframe_toNat16]),
            Mem.read32_write32_same, hj_next]
      have hk_next : UInt32.ofNat k_val + 1 = UInt32.ofNat (k_val + 1) := by
        apply UInt32.toNat_inj.mp
        simp only [UInt32.toNat_add, UInt32.toNat_ofNat',
                   show (1 : UInt32).toNat = 1 from rfl,
                   Nat.mod_eq_of_lt (show k_val + 1 < 4294967296 from by have := n_out.toNat_lt; omega)]
        omega
      have hk_m_next : stC.mem.read32 (frame + 16) = UInt32.ofNat (k_val + 1) := by
        simp only [stC, mem3]; rw [Mem.read32_write32_same, hk_next]
      -- k_val + 1 = k₀ + (j+1 - j₀)
      have hkeq_next : k_val + 1 = k₀ + (j + 1 - j₀) := by omega
      -- right source unchanged in stC
      have hright_stC : ∀ i, i < n_right.toNat →
          stC.mem.read32 (right_ptr + 4 * UInt32.ofNat i) =
          st_init.mem.read32 (right_ptr + 4 * UInt32.ofNat i) := by
        intro i hi
        simp only [stC, mem3, mem2, mem1]
        have hri : (right_ptr + 4 * UInt32.ofNat i).toNat = right_ptr.toNat + 4 * i :=
          toNat_wordAddr right_ptr n_right.toNat i hi (by linarith)
        rw [Mem.read32_write32_of_disjoint _ (frame + 16) _ _
              (by rw [hframe_toNat16, hri]; rcases hframe_right_disj' with h | h <;> omega),
            Mem.read32_write32_of_disjoint _ (frame + 12) _ _
              (by rw [hframe_toNat12, hri]; rcases hframe_right_disj' with h | h <;> omega),
            Mem.read32_write32_of_disjoint _ (out_ptr + 4 * UInt32.ofNat k_val) _ _
              (by rw [hout_k_toNat, hri]; rcases hright_out_disj' with h | h <;> [right; left] <;> omega)]
        exact hright' i hi
      -- copy invariant for stC (∀ i < (j+1)-j₀, stC.mem.read32(out+4*(k₀+i)) = st_init.mem.read32(right+4*(j₀+i)))
      have hcopy_next : ∀ i, i < j + 1 - j₀ →
          stC.mem.read32 (out_ptr + 4 * UInt32.ofNat (k₀ + i)) =
          st_init.mem.read32 (right_ptr + 4 * UInt32.ofNat (j₀ + i)) := by
        intro i hi
        by_cases hidk : i < j - j₀
        · have hdisj : (out_ptr + 4 * UInt32.ofNat k_val).toNat + 4 ≤
              (out_ptr + 4 * UInt32.ofNat (k₀ + i)).toNat ∨
              (out_ptr + 4 * UInt32.ofNat (k₀ + i)).toNat + 4 ≤
              (out_ptr + 4 * UInt32.ofNat k_val).toNat := by
            have hia : (out_ptr + 4 * UInt32.ofNat (k₀ + i)).toNat = out_ptr.toNat + 4 * (k₀ + i) :=
              toNat_wordAddr out_ptr n_out.toNat (k₀ + i) (by omega) (by linarith)
            rw [hia, hout_k_toNat]; omega
          simp only [stC, mem3, mem2, mem1]
          rw [Mem.read32_write32_of_disjoint _ (frame + 16) _ _
                (by have hia := toNat_wordAddr out_ptr n_out.toNat (k₀ + i) (by omega) (by linarith)
                    rcases hframe_out_disj' with h | h
                    · left; rw [hframe_toNat16, hia]; omega
                    · right; rw [hframe_toNat16, hia]; omega),
              Mem.read32_write32_of_disjoint _ (frame + 12) _ _
                (by have hia := toNat_wordAddr out_ptr n_out.toNat (k₀ + i) (by omega) (by linarith)
                    rcases hframe_out_disj' with h | h
                    · left; rw [hframe_toNat12, hia]; omega
                    · right; rw [hframe_toNat12, hia]; omega),
              Mem.read32_write32_of_disjoint _ (out_ptr + 4 * UInt32.ofNat k_val) _ _ hdisj]
          exact hcopy i hidk
        · have hieq : i = j - j₀ := by omega
          subst hieq
          simp only [stC, mem3, mem2, mem1]
          rw [Mem.read32_write32_of_disjoint _ (frame + 16) _ _
                (by rcases hframe_out_disj' with h | h
                    · left; rw [hframe_toNat16, hout_k_toNat]; omega
                    · right; rw [hframe_toNat16, hout_k_toNat]; omega),
              Mem.read32_write32_of_disjoint _ (frame + 12) _ _
                (by rcases hframe_out_disj' with h | h
                    · left; rw [hframe_toNat12, hout_k_toNat]; omega
                    · right; rw [hframe_toNat12, hout_k_toNat]; omega),
              Mem.read32_write32_same]
          show stB.mem.read32 (right_ptr + 4 * UInt32.ofNat j) =
              st_init.mem.read32 (right_ptr + 4 * UInt32.ofNat (j₀ + (j - j₀)))
          rw [show j₀ + (j - j₀) = j from by omega]; exact hright' j hlt
      -- Apply IH at (stC, sB, j+1)
      have hk_eq_sB : sB.values = locB.values := rfl
      have hsB_params : sB.params.length = 6 := by
        simp [sB, locB18, locB17, locB16, hlparams']
      have hsB_locals : sB.locals.length = 16 := by
        simp [sB, locB18, locB17, locB16, List.length_set, hllocals']
      have hsB_get6 : sB.get 6 = some (.i32 frame) := by exact hlocB18_get6
      have hsB_get3 : sB.get 3 = some (.i32 n_right) := by
        have hlen17p : locB17.params.length = 6 := by simp [locB17, hlocB16_params]
        simp only [Locals.get, sB, locB18, hlen17p, show (3 : Nat) < 6 from by omega]
        simp only [Locals.get, locB17, hlocB16_params, show (3 : Nat) < 6 from by omega]
        simp only [Locals.get, hlparams', show (3 : Nat) < 6 from by omega] at h3'; exact h3'
      have hsB_get2 : sB.get 2 = some (.i32 right_ptr) := by
        have hlen17p : locB17.params.length = 6 := by simp [locB17, hlocB16_params]
        simp only [Locals.get, sB, locB18, hlen17p, show (2 : Nat) < 6 from by omega]
        simp only [Locals.get, locB17, hlocB16_params, show (2 : Nat) < 6 from by omega]
        simp only [Locals.get, hlparams', show (2 : Nat) < 6 from by omega] at h2'; exact h2'
      have hsB_get4 : sB.get 4 = some (.i32 out_ptr) := by
        have hlen17p : locB17.params.length = 6 := by simp [locB17, hlocB16_params]
        simp only [Locals.get, sB, locB18, hlen17p, show (4 : Nat) < 6 from by omega]
        simp only [Locals.get, locB17, hlocB16_params, show (4 : Nat) < 6 from by omega]
        simp only [Locals.get, hlparams', show (4 : Nat) < 6 from by omega] at h4'; exact h4'
      have hsB_get5 : sB.get 5 = some (.i32 n_out) := by exact hlocB18_get5
      obtain ⟨N_ih, stF, h_ih, h_ih_cont, h_ih_pres⟩ :=
        IH (n - 1) (by omega) stC sB (j + 1) (k_val + 1)
          (by omega) (by omega) (by omega)
          hsB_get6 hsB_get3 hsB_get2 hsB_get4 hsB_get5
          hsB_params hsB_locals
          ⟨_, hglobal'.choose_spec⟩
          (by simpa using hj_m_next)
          hk_m_next
          (by omega)
          hcopy_next
          hright_stC
          (by simp [stC, mem3, mem2, mem1, Mem.write32_pages]; omega)
          (by simp [stC, mem3, mem2, mem1, Mem.write32_pages]; omega)
          (by simp [stC, mem3, mem2, mem1, Mem.write32_pages]; omega)
          (by simp [stC, mem3, mem2, mem1, Mem.write32_pages]; exact hpages_u32')
          hright_out_disj' hframe_right_disj' hframe_out_disj'
      -- combine
      have h_body_ne : exec 4 m stB locB innerRightDrainBody env ≠ .OutOfFuel := by
        rw [h_body]; intro h; cases h
      have h_body' : exec (max N_ih 4) m stB locB innerRightDrainBody env = .Break 0 stC sB :=
        (exec_fuel_mono (Nat.le_max_right N_ih 4) h_body_ne).trans h_body
      have h_ih_ne : exec N_ih m stC sB [.loop 0 0 innerRightDrainBody] env ≠ .OutOfFuel := by
        rw [h_ih]; intro h; cases h
      have h_ih' : exec (max N_ih 4) m stC sB [.loop 0 0 innerRightDrainBody] env = .Return stF sB.values :=
        (exec_fuel_mono (Nat.le_max_left N_ih 4) h_ih_ne).trans h_ih
      have hone_cs : execOne (max N_ih 4) m stC sB (.loop 0 0 innerRightDrainBody) env = .Return stF sB.values :=
        execOne_of_exec_singleton h_ih'
      have hone_stB : execOne (max N_ih 4 + 1) m stB locB (.loop 0 0 innerRightDrainBody) env =
          .Return stF locB.values := by
        rw [execOne_loop_succ]
        simp only [h_body', List.take_zero, List.nil_append, List.drop_zero]
        have hsB_vals : ({ sB with values := locB.values } : Locals) = sB := by simp [sB]
        rw [hsB_vals, hone_cs]
      refine ⟨max N_ih 4 + 1, stF, ?_, ?_, ?_⟩
      · simp only [exec, hone_stB]
      · intro i hi
        cases i with
        | zero =>
          show stF.mem.read32 (out_ptr + 4 * UInt32.ofNat k_val) =
               st_init.mem.read32 (right_ptr + 4 * UInt32.ofNat j)
          have hpres_k := h_ih_pres k_val (by omega)
          rw [hpres_k]
          simp only [stC, mem3, mem2, mem1]
          rw [Mem.read32_write32_of_disjoint _ (frame + 16) _ _
                (by rcases hframe_out_disj' with h | h <;> [left; right] <;>
                    (rw [hframe_toNat16, hout_k_toNat]; omega)),
              Mem.read32_write32_of_disjoint _ (frame + 12) _ _
                (by rcases hframe_out_disj' with h | h <;> [left; right] <;>
                    (rw [hframe_toNat12, hout_k_toNat]; omega)),
              Mem.read32_write32_same]
          exact hright' j hlt
        | succ i' =>
          have hi' : i' < n_right.toNat - (j + 1) := by omega
          have key2 := h_ih_cont i' hi'
          simp only [show k₀ + (j - j₀) + (i' + 1) = k₀ + ((j + 1) - j₀) + i' from by omega,
                     show j + (i' + 1) = j + 1 + i' from by omega]
          exact key2
      · intro q hq
        by_cases hqlt : q < k_val
        · have := h_ih_pres q (by omega)
          rw [this]
          -- stC.mem.read32(out+4*q) = stB.mem.read32(out+4*q) for q < k_val
          have hqtoNat : (out_ptr + 4 * UInt32.ofNat q).toNat = out_ptr.toNat + 4 * q :=
            toNat_wordAddr out_ptr n_out.toNat q (by omega) (by linarith)
          simp only [stC, mem3, mem2, mem1]
          rw [Mem.read32_write32_of_disjoint _ (frame + 16) _ _
                (by rcases hframe_out_disj' with h | h
                    · left; rw [hframe_toNat16, hqtoNat]; omega
                    · right; rw [hframe_toNat16, hqtoNat]; omega),
              Mem.read32_write32_of_disjoint _ (frame + 12) _ _
                (by rcases hframe_out_disj' with h | h
                    · left; rw [hframe_toNat12, hqtoNat]; omega
                    · right; rw [hframe_toNat12, hqtoNat]; omega),
              Mem.read32_write32_of_disjoint _ (out_ptr + 4 * UInt32.ofNat k_val) _ _
                (by rw [hout_k_toNat, hqtoNat]; omega)]
        · exfalso; omega
    · -- Return arm: j = n_right, exit via .ret
      have hj_eq : j = n_right.toNat := Nat.le_antisymm hj_hi (Nat.not_lt.mp hlt)
      have hj_nlt : ¬(UInt32.ofNat j < n_right) := by
        rw [UInt32.lt_iff_toNat_lt_toNat, UInt32.toNat_ofNat']
        have := n_right.toNat_lt; omega
      have hb12 : ¬(frame.toNat + (12 : UInt32).toNat + 4 > stB.mem.pages * 65536) := by simp; omega
      obtain ⟨v₀, hg⟩ := hglobal'
      let stRet : Store Unit :=
        { stB with globals := { globals := stB.globals.globals.set 0 (.i32 (32 + frame)) } }
      have h_cond0 : exec 1 m stB locB [
          .localGet 6, .load32 (12 : UInt32),
          .localGet 3, .ltU, .const (1 : UInt32), .and, .br_if 0,
          .localGet 6, .const (32 : UInt32), .add, .globalSet 0, .ret
        ] env = .Return stRet locB.values := by
        have hgv6_c : ∀ xs, ({ locB with values := xs } : Locals).get 6 = locB.get 6 := fun _ => rfl
        have hgv3_c : ∀ xs, ({ locB with values := xs } : Locals).get 3 = locB.get 3 := fun _ => rfl
        simp only [exec, execOne.eq_def, hgv6_c, hgv3_c, hf6', h3', hj_m, hg,
                   if_neg hb12, if_neg hj_nlt,
                   show (1 : UInt32) &&& 0 = 0 from by decide, stRet]
      have h_body1 : exec 2 m stB locB innerRightDrainBody env = .Return stRet locB.values := by
        simp only [innerRightDrainBody]
        rw [show (2 : Nat) = 1 + 1 from rfl, exec_block_cons]
        simp only [h_cond0]
      have hone_ret : execOne 3 m stB locB (.loop 0 0 innerRightDrainBody) env = .Return stRet locB.values := by
        rw [show (3 : Nat) = 2 + 1 from rfl, execOne_loop_succ]
        simp only [h_body1]
      refine ⟨3, stRet, ?_, ?_, ?_⟩
      · simp only [exec, hone_ret]
      · intro i hi; omega
      · intro q hq
        -- stRet.mem = stB.mem (globalSet only touches globals)
        show stB.mem.read32 (out_ptr + 4 * UInt32.ofNat q) =
             stB.mem.read32 (out_ptr + 4 * UInt32.ofNat q)
        rfl

set_option maxHeartbeats 4000000 in
theorem outer_drain_terminates
    {m : Module} {env : HostEnv Unit}
    (st_init stA : Store Unit) (locA : Locals)
    (frame out_ptr left_ptr right_ptr n_left n_right n_out : UInt32)
    (hI : MergeLoopInv frame out_ptr left_ptr right_ptr n_left n_right n_out
            0 0 0 st_init stA locA)
    (h_exit : stA.mem.read32 (frame + 8) = n_left ∨
               stA.mem.read32 (frame + 12) = n_right) :
    ∃ N stF,
      exec N m stA locA [.loop 0 0 outerDrainBody] env = .Return stF locA.values ∧
      wordsAt stF.mem out_ptr (n_left.toNat + n_right.toNat) =
        List.merge
          (wordsAt st_init.mem left_ptr n_left.toNat)
          (wordsAt st_init.mem right_ptr n_right.toNat)
          (· ≤ ·) := by
  obtain ⟨i, j, _, hi_hi, _, hj_hi,
           hi_m, hj_m, hk_m,
           hf6, h0, h1, h2, h3, h4, h5,
           hlparams, hllocals, hglobal,
           hleft, hright,
           hcontent,
           hpages, hk_bound, hleft_bnd, hright_bnd, hout_bnd, hpages_u32,
           hleft_out_disj, hright_out_disj, hleft_right_disj,
           hframe_left_disj, hframe_right_disj, hframe_out_disj⟩ := hI
  -- derive i = n_left or j = n_right from h_exit
  have hi_exit : i = n_left.toNat ∨ j = n_right.toNat := by
    rcases h_exit with h | h
    · left
      have := congr_arg UInt32.toNat (hi_m.symm.trans h)
      simp [UInt32.toNat_ofNat'] at this
      have := n_left.toNat_lt; omega
    · right
      have := congr_arg UInt32.toNat (hj_m.symm.trans h)
      simp [UInt32.toNat_ofNat'] at this
      have := n_right.toNat_lt; omega
  -- k at exit = i + j (since k₀=i₀=j₀=0)
  have hk_ij : stA.mem.read32 (frame + 16) = UInt32.ofNat (i + j) := by
    rwa [show (0 : Nat) + (i - 0) + (j - 0) = i + j from by omega] at hk_m
  -- strong induction on n_left - i
  suffices key : ∀ n stB locB i2 j2,
      n_left.toNat - i2 = n →
      i2 ≤ n_left.toNat → j2 ≤ n_right.toNat →
      (i2 = n_left.toNat ∨ j2 = n_right.toNat) →
      locB.get 6 = some (.i32 frame) →
      locB.get 0 = some (.i32 left_ptr) →
      locB.get 1 = some (.i32 n_left) →
      locB.get 2 = some (.i32 right_ptr) →
      locB.get 3 = some (.i32 n_right) →
      locB.get 4 = some (.i32 out_ptr) →
      locB.get 5 = some (.i32 n_out) →
      locB.params.length = 6 → locB.locals.length = 16 →
      (∃ v, stB.globals.globals[0]? = some v) →
      stB.mem.read32 (frame + 8)  = UInt32.ofNat i2 →
      stB.mem.read32 (frame + 12) = UInt32.ofNat j2 →
      stB.mem.read32 (frame + 16) = UInt32.ofNat (i2 + j2) →
      (∀ q, q < n_left.toNat  → stB.mem.read32 (left_ptr  + 4 * UInt32.ofNat q) = st_init.mem.read32 (left_ptr  + 4 * UInt32.ofNat q)) →
      (∀ q, q < n_right.toNat → stB.mem.read32 (right_ptr + 4 * UInt32.ofNat q) = st_init.mem.read32 (right_ptr + 4 * UInt32.ofNat q)) →
      wordsAt stB.mem (out_ptr + 4 * UInt32.ofNat 0) (i2 + j2) ++
        List.merge ((wordsAt st_init.mem left_ptr n_left.toNat).drop i2)
                   ((wordsAt st_init.mem right_ptr n_right.toNat).drop j2) (· ≤ ·) =
      List.merge (wordsAt st_init.mem left_ptr n_left.toNat)
                 (wordsAt st_init.mem right_ptr n_right.toNat) (· ≤ ·) →
      frame.toNat + 20 ≤ stB.mem.pages * 65536 →
      i2 + j2 + ((n_left.toNat - i2) + (n_right.toNat - j2)) ≤ n_out.toNat →
      left_ptr.toNat  + 4 * n_left.toNat  ≤ stB.mem.pages * 65536 →
      right_ptr.toNat + 4 * n_right.toNat ≤ stB.mem.pages * 65536 →
      out_ptr.toNat   + 4 * n_out.toNat   ≤ stB.mem.pages * 65536 →
      stB.mem.pages * 65536 ≤ 4294967296 →
      (left_ptr.toNat  + 4 * n_left.toNat  ≤ out_ptr.toNat ∨ out_ptr.toNat + 4 * n_out.toNat ≤ left_ptr.toNat) →
      (right_ptr.toNat + 4 * n_right.toNat ≤ out_ptr.toNat ∨ out_ptr.toNat + 4 * n_out.toNat ≤ right_ptr.toNat) →
      (left_ptr.toNat  + 4 * n_left.toNat  ≤ right_ptr.toNat ∨ right_ptr.toNat + 4 * n_right.toNat ≤ left_ptr.toNat) →
      (frame.toNat + 20 ≤ left_ptr.toNat  ∨ left_ptr.toNat  + 4 * n_left.toNat  ≤ frame.toNat) →
      (frame.toNat + 20 ≤ right_ptr.toNat ∨ right_ptr.toNat + 4 * n_right.toNat ≤ frame.toNat) →
      (frame.toNat + 20 ≤ out_ptr.toNat   ∨ out_ptr.toNat   + 4 * n_out.toNat   ≤ frame.toNat) →
      ∃ N stF,
        exec N m stB locB [.loop 0 0 outerDrainBody] env = .Return stF locB.values ∧
        wordsAt stF.mem out_ptr (n_left.toNat + n_right.toNat) =
          List.merge (wordsAt st_init.mem left_ptr n_left.toNat)
                     (wordsAt st_init.mem right_ptr n_right.toNat) (· ≤ ·) from by
    apply key (n_left.toNat - i) stA locA i j rfl hi_hi hj_hi hi_exit
      hf6 h0 h1 h2 h3 h4 h5 hlparams hllocals hglobal
      hi_m hj_m hk_ij hleft hright
    · simpa using hcontent
    · exact hpages
    · omega
    · exact hleft_bnd
    · exact hright_bnd
    · exact hout_bnd
    · exact hpages_u32
    · exact hleft_out_disj
    · exact hright_out_disj
    · exact hleft_right_disj
    · exact hframe_left_disj
    · exact hframe_right_disj
    · exact hframe_out_disj
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro stB locB i2 j2 hn hi2_hi hj2_hi hexit
      hf6' h0' h1' h2' h3' h4' h5'
      hlparams' hllocals' hglobal'
      hi2_m hj2_m hk2_m
      hleft' hright' hcontent'
      hpages' hk_bound' hleft_bnd' hright_bnd' hout_bnd' hpages_u32'
      hleft_out_disj' hright_out_disj' hleft_right_disj'
      hframe_left_disj' hframe_right_disj' hframe_out_disj'
    rcases hexit with hi_eq | hj_eq
    · -- Case: i2 = n_left (right drain via inner loop)
      subst hi_eq
      -- COND_BLOCK does not fire (i2 = n_left)
      have hi2_nlt : ¬(UInt32.ofNat n_left.toNat < n_left) := by
        rw [UInt32.lt_iff_toNat_lt_toNat, UInt32.toNat_ofNat']
        simp [UInt32.toNat_ofNat', n_left.toNat_lt]
      have hb8 : ¬(frame.toNat + (8 : UInt32).toNat + 4 > stB.mem.pages * 65536) := by simp; omega
      -- Run inner right drain
      have hk_for_inner : n_left.toNat + j2 = n_left.toNat + j2 := rfl
      have hk_bound_inner : (n_left.toNat + j2) + (n_right.toNat - j2) ≤ n_out.toNat := by omega
      obtain ⟨N_inner, stF, h_inner, h_inner_cont, h_inner_pres⟩ :=
        inner_right_drain_terminates st_init stB locB
          frame out_ptr right_ptr n_right n_out j2 (n_left.toNat + j2)
          hj2_hi hf6' h3' h2' h4' h5' hlparams' hllocals' hglobal'
          hj2_m hk2_m
          hright'
          hpages' hk_bound_inner hright_bnd' hout_bnd' hpages_u32'
          hright_out_disj' hframe_right_disj' hframe_out_disj'
      -- exec N_inner condBodyOuter = Return stF locB.values
      have hone_inner : execOne N_inner m stB locB (.loop 0 0 innerRightDrainBody) env =
          .Return stF locB.values :=
        execOne_of_exec_singleton h_inner
      -- exec (N_inner+1) [check_i_flat, .loop inner, error_k] = Return stF locB.values
      -- (condBodyOuter execution: br_if 0 doesn't fire, falls through to .loop inner)
      have hgv6_c : ∀ xs, ({ locB with values := xs } : Locals).get 6 = locB.get 6 := fun _ => rfl
      have hgv1_c : ∀ xs, ({ locB with values := xs } : Locals).get 1 = locB.get 1 := fun _ => rfl
      have hcond_body_exit : exec N_inner m stB locB [
          .localGet 6, .load32 (8 : UInt32),
          .localGet 1, .ltU, .const (1 : UInt32), .and, .br_if 0,
          .loop 0 0 innerRightDrainBody,
          .localGet 18, .localGet 5, .const (1048664 : UInt32), .call 87, .unreachable
        ] env = .Return stF locB.values := by
        cases N_inner with
        | zero => simp [exec, execOne.eq_def] at h_inner
        | succ k =>
          have h7 : exec 1 m stB locB [
              .localGet 6, .load32 (8 : UInt32),
              .localGet 1, .ltU, .const (1 : UInt32), .and, .br_if 0
            ] env = .Fallthrough stB locB := by
            simp only [exec, execOne.eq_def, hgv6_c, hgv1_c, hf6', h1', hi2_m,
                       if_neg hb8, if_neg hi2_nlt,
                       show (1 : UInt32) &&& 0 = 0 from by decide,
                       show (if (0 : UInt32) ≠ 0 then True else False) = False from by decide]
          have h7k : exec (k + 1) m stB locB [
              .localGet 6, .load32 (8 : UInt32),
              .localGet 1, .ltU, .const (1 : UInt32), .and, .br_if 0
            ] env = .Fallthrough stB locB :=
            (exec_fuel_mono (by omega : 1 ≤ k + 1) (by rw [h7]; intro h; cases h)).trans h7
          have hlist : ([.localGet 6, .load32 (8 : UInt32), .localGet 1, .ltU,
                        .const (1 : UInt32), .and, .br_if 0,
                        .loop 0 0 innerRightDrainBody,
                        .localGet 18, .localGet 5, .const (1048664 : UInt32), .call 87, .unreachable] : Program)
              = [.localGet 6, .load32 (8 : UInt32), .localGet 1, .ltU,
                 .const (1 : UInt32), .and, .br_if 0]
                ++ [.loop 0 0 innerRightDrainBody,
                    .localGet 18, .localGet 5, .const (1048664 : UInt32), .call 87, .unreachable] := rfl
          rw [hlist, exec_append, h7k]
          simp only [exec, hone_inner]
      have h_block_exit : execOne (N_inner + 2) m stB locB (.block 0 0 [
          .localGet 6, .load32 (8 : UInt32),
          .localGet 1, .ltU, .const (1 : UInt32), .and, .br_if 0,
          .loop 0 0 innerRightDrainBody,
          .localGet 18, .localGet 5, .const (1048664 : UInt32), .call 87, .unreachable
        ]) env = .Return stF locB.values := by
        have hne : exec N_inner m stB locB [
            .localGet 6, .load32 (8 : UInt32),
            .localGet 1, .ltU, .const (1 : UInt32), .and, .br_if 0,
            .loop 0 0 innerRightDrainBody,
            .localGet 18, .localGet 5, .const (1048664 : UInt32), .call 87, .unreachable
          ] env ≠ .OutOfFuel := by rw [hcond_body_exit]; intro h; cases h
        have hN1 : exec (N_inner + 1) m stB locB [
            .localGet 6, .load32 (8 : UInt32),
            .localGet 1, .ltU, .const (1 : UInt32), .and, .br_if 0,
            .loop 0 0 innerRightDrainBody,
            .localGet 18, .localGet 5, .const (1048664 : UInt32), .call 87, .unreachable
          ] env = .Return stF locB.values :=
          (exec_fuel_mono (by omega) hne).trans hcond_body_exit
        simp only [execOne.eq_def, hN1]
      have h_outer_body_exit : exec (N_inner + 2) m stB locB outerDrainBody env = .Return stF locB.values := by
        show exec (N_inner + 2) m stB locB (.block 0 0 _ :: _) env = _
        simp only [exec]
        simp only [h_block_exit]
      have hone_outer : execOne (N_inner + 3) m stB locB (.loop 0 0 outerDrainBody) env =
          .Return stF locB.values := by
        rw [show (N_inner + 3) = (N_inner + 2) + 1 from by omega, execOne_loop_succ]
        simp only [h_outer_body_exit]
      refine ⟨N_inner + 3, stF, ?_, ?_⟩
      · simp only [exec, hone_outer]
      · -- content proof: i2 = n_left
        -- From hcontent': wordsAt stB out_ptr (n_left+j2) ++ merge(left₁.drop n_left, right₁.drop j2) = merge(left₁, right₁)
        -- merge(left₁.drop n_left, right₁.drop j2) = merge([], right₁.drop j2) = right₁.drop j2
        -- (merge_nil_left)
        -- stF has: ∀ q < n_right.toNat - j2, stF.mem.read32(out+4*(n_left+j2+q)) = st_init.mem.read32(right+4*(j2+q))
        --          ∀ q < n_left+j2, stF.mem.read32(out+4*q) = stB.mem.read32(out+4*q)
        simp only [show UInt32.ofNat 0 = 0 from rfl, UInt32.mul_zero, UInt32.add_zero] at hcontent'
        have hleft_drop : (wordsAt st_init.mem left_ptr n_left.toNat).drop n_left.toNat = [] := by
          simp [List.drop_length]
        rw [hleft_drop, merge_nil_left] at hcontent'
        -- wordsAt stF out_ptr (n_left+n_right) = wordsAt stB out_ptr (n_left+j2) ++ right₁.drop j2
        have hsplit : wordsAt stF.mem out_ptr (n_left.toNat + n_right.toNat) =
            wordsAt stF.mem out_ptr (n_left.toNat + j2) ++
            wordsAt stF.mem (out_ptr + 4 * UInt32.ofNat (n_left.toNat + j2)) (n_right.toNat - j2) := by
          rw [wordsAt_split stF.mem out_ptr (n_left.toNat + n_right.toNat) (n_left.toNat + j2) (by omega)]
          congr 1; congr 1; omega
        rw [hsplit]
        -- left part: wordsAt stF out (n_left+j2) = wordsAt stB out (n_left+j2)
        have hleft_part : wordsAt stF.mem out_ptr (n_left.toNat + j2) =
            wordsAt stB.mem out_ptr (n_left.toNat + j2) := by
          apply List.ext_getElem
          · simp [wordsAt_length]
          · intro idx hidx1 _
            simp only [wordsAt, List.getElem_map, List.getElem_range]
            have hidx : idx < n_left.toNat + j2 := by simp [wordsAt_length] at hidx1; exact hidx1
            rw [h_inner_pres idx (by omega)]
        -- right part: wordsAt stF out@(n_left+j2) (n_right-j2) = (wordsAt st_init right n_right).drop j2
        have hright_part : wordsAt stF.mem (out_ptr + 4 * UInt32.ofNat (n_left.toNat + j2))
            (n_right.toNat - j2) =
            (wordsAt st_init.mem right_ptr n_right.toNat).drop j2 := by
          apply List.ext_getElem
          · simp [wordsAt_length, wordsAt_drop_eq, List.length_drop]
          · intro idx hidx1 hidx2
            simp only [wordsAt, List.getElem_map, List.getElem_range]
            have hidx_lt : idx < n_right.toNat - j2 := by
              simp only [wordsAt_length] at hidx1; exact hidx1
            have haddr : out_ptr + 4 * UInt32.ofNat (n_left.toNat + j2) + 4 * UInt32.ofNat idx =
                out_ptr + 4 * UInt32.ofNat (n_left.toNat + j2 + idx) := by
              simp [UInt32.mul_add, UInt32.add_assoc]
            rw [haddr]
            rw [h_inner_cont idx (by omega)]
            simp only [List.getElem_drop, List.getElem_map, List.getElem_range]
        rw [hleft_part, hright_part]
        -- now: wordsAt stB out (n_left+j2) ++ right₁.drop j2 = merge(left₁, right₁) = hcontent'
        rw [← hcontent']
    · -- Case: j2 = n_right, copy left[i2] step (BCO_left)
      subst hj_eq
      -- If also i2 = n_left, fallback to inner right drain with j2 = n_right
      by_cases hi2_eq : i2 = n_left.toNat
      · -- i2 = n_left AND j2 = n_right: inner drain with 0 elements
        subst hi2_eq
        have hk_for_inner : n_left.toNat + n_right.toNat = n_left.toNat + n_right.toNat := rfl
        obtain ⟨N_inner, stF, h_inner, h_inner_cont, h_inner_pres⟩ :=
          inner_right_drain_terminates st_init stB locB
            frame out_ptr right_ptr n_right n_out n_right.toNat (n_left.toNat + n_right.toNat)
            (le_refl _) hf6' h3' h2' h4' h5' hlparams' hllocals' hglobal'
            hj2_m hk2_m
            hright'
            hpages' (by omega) hright_bnd' hout_bnd' hpages_u32'
            hright_out_disj' hframe_right_disj' hframe_out_disj'
        have hone_inner : execOne N_inner m stB locB (.loop 0 0 innerRightDrainBody) env =
            .Return stF locB.values := execOne_of_exec_singleton h_inner
        have hi2_nlt : ¬(UInt32.ofNat n_left.toNat < n_left) := by
          rw [UInt32.lt_iff_toNat_lt_toNat, UInt32.toNat_ofNat']
          simp [n_left.toNat_lt]
        have hb8 : ¬(frame.toNat + (8 : UInt32).toNat + 4 > stB.mem.pages * 65536) := by simp; omega
        have hgv6_c : ∀ xs, ({ locB with values := xs } : Locals).get 6 = locB.get 6 := fun _ => rfl
        have hgv1_c : ∀ xs, ({ locB with values := xs } : Locals).get 1 = locB.get 1 := fun _ => rfl
        have hcond_body_exit : exec N_inner m stB locB [
            .localGet 6, .load32 (8 : UInt32),
            .localGet 1, .ltU, .const (1 : UInt32), .and, .br_if 0,
            .loop 0 0 innerRightDrainBody,
            .localGet 18, .localGet 5, .const (1048664 : UInt32), .call 87, .unreachable
          ] env = .Return stF locB.values := by
          cases N_inner with
          | zero => simp [exec, execOne.eq_def] at h_inner
          | succ k =>
            have h7 : exec 1 m stB locB [
                .localGet 6, .load32 (8 : UInt32),
                .localGet 1, .ltU, .const (1 : UInt32), .and, .br_if 0
              ] env = .Fallthrough stB locB := by
              simp only [exec, execOne.eq_def, hgv6_c, hgv1_c, hf6', h1', hi2_m,
                         if_neg hb8, if_neg hi2_nlt,
                         show (1 : UInt32) &&& 0 = 0 from by decide,
                         show (if (0 : UInt32) ≠ 0 then True else False) = False from by decide]
            have h7k : exec (k + 1) m stB locB [
                .localGet 6, .load32 (8 : UInt32),
                .localGet 1, .ltU, .const (1 : UInt32), .and, .br_if 0
              ] env = .Fallthrough stB locB :=
              (exec_fuel_mono (by omega : 1 ≤ k + 1) (by rw [h7]; intro h; cases h)).trans h7
            have hlist : ([.localGet 6, .load32 (8 : UInt32), .localGet 1, .ltU,
                          .const (1 : UInt32), .and, .br_if 0,
                          .loop 0 0 innerRightDrainBody,
                          .localGet 18, .localGet 5, .const (1048664 : UInt32), .call 87, .unreachable] : Program)
                = [.localGet 6, .load32 (8 : UInt32), .localGet 1, .ltU,
                   .const (1 : UInt32), .and, .br_if 0]
                  ++ [.loop 0 0 innerRightDrainBody,
                      .localGet 18, .localGet 5, .const (1048664 : UInt32), .call 87, .unreachable] := rfl
            rw [hlist, exec_append, h7k]
            simp only [exec, hone_inner]
        have h_block_exit : execOne (N_inner + 2) m stB locB (.block 0 0 [
            .localGet 6, .load32 (8 : UInt32),
            .localGet 1, .ltU, .const (1 : UInt32), .and, .br_if 0,
            .loop 0 0 innerRightDrainBody,
            .localGet 18, .localGet 5, .const (1048664 : UInt32), .call 87, .unreachable
          ]) env = .Return stF locB.values := by
          have hne : exec N_inner m stB locB [
              .localGet 6, .load32 (8 : UInt32),
              .localGet 1, .ltU, .const (1 : UInt32), .and, .br_if 0,
              .loop 0 0 innerRightDrainBody,
              .localGet 18, .localGet 5, .const (1048664 : UInt32), .call 87, .unreachable
            ] env ≠ .OutOfFuel := by rw [hcond_body_exit]; intro h; cases h
          have hN1 : exec (N_inner + 1) m stB locB [
              .localGet 6, .load32 (8 : UInt32),
              .localGet 1, .ltU, .const (1 : UInt32), .and, .br_if 0,
              .loop 0 0 innerRightDrainBody,
              .localGet 18, .localGet 5, .const (1048664 : UInt32), .call 87, .unreachable
            ] env = .Return stF locB.values :=
            (exec_fuel_mono (by omega) hne).trans hcond_body_exit
          simp only [execOne.eq_def, hN1]
        have h_outer_body_exit : exec (N_inner + 2) m stB locB outerDrainBody env = .Return stF locB.values := by
          show exec (N_inner + 2) m stB locB (.block 0 0 _ :: _) env = _
          simp only [exec]
          simp only [h_block_exit]
        have hone_outer : execOne (N_inner + 3) m stB locB (.loop 0 0 outerDrainBody) env =
            .Return stF locB.values := by
          rw [show (N_inner + 3) = (N_inner + 2) + 1 from by omega, execOne_loop_succ]
          simp only [h_outer_body_exit]
        refine ⟨N_inner + 3, stF, ?_, ?_⟩
        · simp only [exec, hone_outer]
        · simp only [show UInt32.ofNat 0 = 0 from rfl, UInt32.mul_zero, UInt32.add_zero] at hcontent'
          have hleft_drop : (wordsAt st_init.mem left_ptr n_left.toNat).drop n_left.toNat = [] := by
            simp [List.drop_length]
          have hright_drop : (wordsAt st_init.mem right_ptr n_right.toNat).drop n_right.toNat = [] := by
            simp [List.drop_length]
          rw [hleft_drop, hright_drop, merge_nil_left] at hcontent'
          simp only [List.append_nil] at hcontent'
          -- stF has: inner_cont vacuous, inner_pres ∀ q < n_left+n_right
          -- wordsAt stF out (n_left+n_right) = wordsAt stB out (n_left+n_right)
          have hfull_pres : wordsAt stF.mem out_ptr (n_left.toNat + n_right.toNat) =
              wordsAt stB.mem out_ptr (n_left.toNat + n_right.toNat) := by
            apply List.ext_getElem
            · simp [wordsAt_length]
            · intro idx hidx1 _
              simp only [wordsAt, List.getElem_map, List.getElem_range]
              rw [h_inner_pres idx (by simp [wordsAt_length] at hidx1; omega)]
          rw [hfull_pres, ← hcontent']
      · -- i2 < n_left, j2 = n_right: BCO_left copy step
        have hi2_lt : i2 < n_left.toNat := Nat.lt_of_le_of_ne hi2_hi hi2_eq
        -- copy left[i2] to out[i2+n_right]
        let k_val := i2 + n_right.toNat
        have hk_lt : k_val < n_out.toNat := by omega
        have hi2_lt32 : UInt32.ofNat i2 < n_left := by
          rw [UInt32.lt_iff_toNat_lt_toNat, UInt32.toNat_ofNat']
          have := n_left.toNat_lt; omega
        have hk_lt32 : UInt32.ofNat k_val < n_out := by
          rw [UInt32.lt_iff_toNat_lt_toNat, UInt32.toNat_ofNat']
          have := n_out.toNat_lt; omega
        have hframe_toNat8 : (frame + 8).toNat = frame.toNat + 8 := by
          rw [UInt32.toNat_add]; simp [UInt32.toNat_ofNat']; omega
        have hframe_toNat16 : (frame + 16).toNat = frame.toNat + 16 := by
          rw [UInt32.toNat_add]; simp [UInt32.toNat_ofNat']; omega
        have hleft_i_toNat : (left_ptr + 4 * UInt32.ofNat i2).toNat = left_ptr.toNat + 4 * i2 :=
          toNat_wordAddr left_ptr n_left.toNat i2 hi2_lt (by linarith)
        have hout_k_toNat : (out_ptr + 4 * UInt32.ofNat k_val).toNat = out_ptr.toNat + 4 * k_val :=
          toNat_wordAddr out_ptr n_out.toNat k_val (by omega) (by linarith)
        let left_i := stB.mem.read32 (left_ptr + 4 * UInt32.ofNat i2)
        let mem1 := stB.mem.write32 (out_ptr + 4 * UInt32.ofNat k_val) left_i
        let mem2 := mem1.write32 (frame + 8) (UInt32.ofNat i2 + 1)
        let mem3 := mem2.write32 (frame + 16) (UInt32.ofNat k_val + 1)
        let stC : Store Unit := { stB with mem := mem3 }
        let locB19 : Locals :=
          { locB with locals := locB.locals.set 13 (.i32 (UInt32.ofNat i2)) }
        let locB20 : Locals :=
          { locB19 with locals := locB19.locals.set 14 (.i32 left_i) }
        let locB21 : Locals :=
          { locB20 with locals := locB20.locals.set 15 (.i32 (UInt32.ofNat k_val)) }
        let sB : Locals := { locB21 with values := locB.values }
        -- h_cond for outer (i2 < n_left)
        have h_cond : exec 3 m stB locB [
            .localGet 6, .load32 (8 : UInt32),
            .localGet 1, .ltU, .const (1 : UInt32), .and, .br_if 0,
            .loop 0 0 innerRightDrainBody,
            .localGet 18, .localGet 5, .const (1048664 : UInt32), .call 87, .unreachable
          ] env = .Break 0 stB locB := by
          have hgv1' : ∀ xs, ({ locB with values := xs } : Locals).get 1 = locB.get 1 := fun _ => rfl
          simp only [exec, execOne.eq_def, hgv1', hf6', h1', hi2_m,
                     if_neg (show ¬(frame.toNat + (8 : UInt32).toNat + 4
                                     > stB.mem.pages * 65536) from by simp; omega),
                     if_pos hi2_lt32,
                     show (1 : UInt32) &&& 1 = 1 from by decide]
          rfl
        -- h_condblock_outer
        have h_condblock : exec 4 m stB locB
            (.block 0 0 [.localGet 6, .load32 (8 : UInt32), .localGet 1, .ltU,
                         .const (1 : UInt32), .and, .br_if 0,
                         .loop 0 0 innerRightDrainBody,
                         .localGet 18, .localGet 5, .const (1048664 : UInt32), .call 87, .unreachable] ::
             [.localGet 6, .load32 (8 : UInt32), .localSet 19,
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
                .store32 (16 : UInt32), .br 1
              ]]) env =
            exec 4 m stB locB19
              [.block 0 0 [
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
                .store32 (16 : UInt32), .br 1
              ]] env := by
          rw [show (4 : Nat) = 3 + 1 from rfl, exec_block_cons, h_cond]
          simp only [List.take_zero, List.drop_zero, List.nil_append]
          simp only [exec, execOne.eq_def, hf6', hi2_m,
                     if_neg (show ¬(frame.toNat + (8 : UInt32).toNat + 4
                                     > stB.mem.pages * 65536) from by simp; omega),
                     Locals.set?, hlparams', hllocals', List.length_set,
                     if_neg (show ¬((19 : Nat) < 6) from by omega),
                     if_pos (show (19 : Nat) < 6 + 16 from by omega),
                     show (19 : Nat) - 6 = 13 from by omega,
                     show Locals.mk locB.params (locB.locals.set 13 (Value.i32 (UInt32.ofNat i2)))
                           locB.values = locB19 from rfl]
        -- local access helpers for locB19
        have hlocB19_params : locB19.params.length = 6 := by simp [locB19, hlparams']
        have hlocB19_locals : locB19.locals.length = 16 := by simp [locB19, List.length_set, hllocals']
        have hlocB19_get6 : locB19.get 6 = some (.i32 frame) := by
          simp only [Locals.get, locB19, hlparams', hllocals', List.length_set,
                     show ¬((6 : Nat) < 6) from by omega,
                     show (6 : Nat) < 6 + 16 from by omega,
                     show (6 : Nat) - 6 = 0 from by omega,
                     List.getElem?_set, show ¬(13 = 0 ∧ 0 < 16) from by omega]
          simpa [Locals.get, hlparams', hllocals', show ¬((6 : Nat) < 6) from by omega] using hf6'
        have hlocB19_get1 : locB19.get 1 = some (.i32 n_left) := by
          simp only [Locals.get, locB19, hlparams', show (1 : Nat) < 6 from by omega] at h1' ⊢; exact h1'
        have hlocB19_get0 : locB19.get 0 = some (.i32 left_ptr) := by
          simp only [Locals.get, locB19, hlparams', show (0 : Nat) < 6 from by omega] at h0' ⊢; exact h0'
        have hlocB19_get5 : locB19.get 5 = some (.i32 n_out) := by
          simp only [Locals.get, locB19, hlparams', show (5 : Nat) < 6 from by omega] at h5' ⊢; exact h5'
        have hlocB19_get4 : locB19.get 4 = some (.i32 out_ptr) := by
          simp only [Locals.get, locB19, hlparams', show (4 : Nat) < 6 from by omega] at h4' ⊢; exact h4'
        have hlocB19_get19 : locB19.get 19 = some (.i32 (UInt32.ofNat i2)) := by
          simp only [Locals.get, locB19, hlparams', hllocals', List.length_set,
                     show ¬((19 : Nat) < 6) from by omega,
                     show (19 : Nat) < 6 + 16 from by omega,
                     show (19 : Nat) - 6 = 13 from by omega,
                     List.getElem?_set, show (13 : Nat) < 16 from by omega, if_true, if_false]
        have hset20 : locB19.set? 20 (.i32 left_i) = some locB20 := by
          simp only [Locals.set?, locB20, hlocB19_params, hlocB19_locals, List.length_set,
                     show ¬((20 : Nat) < 6) from by omega,
                     show (20 : Nat) < 6 + 16 from by omega,
                     show (20 : Nat) - 6 = 14 from by omega]; rfl
        have hset21 : locB20.set? 21 (.i32 (UInt32.ofNat k_val)) = some locB21 := by
          have hlen20p : locB20.params.length = 6 := by simp [locB20, hlocB19_params]
          have hlen20l : locB20.locals.length = 16 := by simp [locB20, List.length_set, hlocB19_locals]
          simp only [Locals.set?, locB21, hlen20p, hlen20l, List.length_set,
                     show ¬((21 : Nat) < 6) from by omega,
                     show (21 : Nat) < 6 + 16 from by omega,
                     show (21 : Nat) - 6 = 15 from by omega]; rfl
        have hlocB21_get21 : locB21.get 21 = some (.i32 (UInt32.ofNat k_val)) := by
          have hlen20p : locB20.params.length = 6 := by simp [locB20, hlocB19_params]
          have hlen20l : locB20.locals.length = 16 := by simp [locB20, List.length_set, hlocB19_locals]
          simp only [Locals.get, locB21, hlen20p, hlen20l, List.length_set,
                     show ¬((21 : Nat) < 6) from by omega,
                     show (21 : Nat) < 6 + 16 from by omega,
                     show (21 : Nat) - 6 = 15 from by omega,
                     List.getElem?_set, show (15 : Nat) < 16 from by omega, if_true, if_false]
        have hlocB21_get5 : locB21.get 5 = some (.i32 n_out) := by
          have hlen20p : locB20.params.length = 6 := by simp [locB20, hlocB19_params]
          simp only [Locals.get, locB21, locB20, locB19,
                     hlen20p, hlocB19_params, hlparams', show (5 : Nat) < 6 from by omega] at h5' ⊢
          exact h5'
        have hlocB21_get4 : locB21.get 4 = some (.i32 out_ptr) := by
          have hlen20p : locB20.params.length = 6 := by simp [locB20, hlocB19_params]
          simp only [Locals.get, locB21, locB20, locB19,
                     hlen20p, hlocB19_params, hlparams', show (4 : Nat) < 6 from by omega] at h4' ⊢
          exact h4'
        have hlocB21_get6 : locB21.get 6 = some (.i32 frame) := by
          have hlen20p : locB20.params.length = 6 := by simp [locB20, hlocB19_params]
          have hlen20l : locB20.locals.length = 16 := by simp [locB20, List.length_set, hlocB19_locals]
          simp only [Locals.get, locB21, locB20, locB19,
                     hlen20p, hlen20l, hlocB19_params, hlocB19_locals, hlparams', hllocals',
                     List.length_set,
                     show ¬((6 : Nat) < 6) from by omega,
                     show (6 : Nat) < 6 + 16 from by omega,
                     show (6 : Nat) - 6 = 0 from by omega,
                     List.getElem?_set,
                     show ¬(15 = 0 ∧ (0 : Nat) < 16) from by omega,
                     show ¬(14 = 0 ∧ (0 : Nat) < 16) from by omega,
                     show ¬(13 = 0 ∧ (0 : Nat) < 16) from by omega] at hf6' ⊢
          exact hf6'
        have hlocB21_get20 : locB21.get 20 = some (.i32 left_i) := by
          have hlen20p : locB20.params.length = 6 := by simp [locB20, hlocB19_params]
          have hlen20l : locB20.locals.length = 16 := by simp [locB20, List.length_set, hlocB19_locals]
          simp only [Locals.get, locB21, locB20, hlen20p, hlen20l, hlocB19_locals,
                     List.length_set,
                     show ¬((20 : Nat) < 6) from by omega,
                     show (20 : Nat) < 6 + 16 from by omega,
                     show (20 : Nat) - 6 = 14 from by omega,
                     List.getElem?_set,
                     show (15 : Nat) ≠ 14 from by omega, if_false,
                     if_true, show (14 : Nat) < 16 from by omega]
        -- shl
        have hshl_i2 : UInt32.ofNat i2 <<< ((2 : UInt32) % 32) = 4 * UInt32.ofNat i2 := by
          rw [show (2 : UInt32) % 32 = 2 from by decide]
          apply UInt32.toNat_inj.mp
          have hi_bnd : i2 < 2 ^ 30 := by have := n_left.toNat_lt; omega
          simp only [UInt32.toNat_mul, UInt32.toNat_ofNat',
                     show (4 : UInt32).toNat = 4 from rfl,
                     Nat.mod_eq_of_lt (show i2 < 4294967296 from by omega),
                     Nat.mod_eq_of_lt (show i2 * 4 < 4294967296 from by omega)]
          simp [UInt32.shiftLeft, Fin.shiftLeft, Nat.shiftLeft_eq]; omega
        have hshl_k : UInt32.ofNat k_val <<< ((2 : UInt32) % 32) = 4 * UInt32.ofNat k_val := by
          rw [show (2 : UInt32) % 32 = 2 from by decide]
          apply UInt32.toNat_inj.mp
          have hk_bnd : k_val < 2 ^ 30 := by have := n_out.toNat_lt; omega
          simp only [UInt32.toNat_mul, UInt32.toNat_ofNat',
                     show (4 : UInt32).toNat = 4 from rfl,
                     Nat.mod_eq_of_lt (show k_val < 4294967296 from by omega),
                     Nat.mod_eq_of_lt (show k_val * 4 < 4294967296 from by omega)]
          simp [UInt32.shiftLeft, Fin.shiftLeft, Nat.shiftLeft_eq]; omega
        -- h_bci_body for outer
        have h_bci_body : exec 1 m stB locB19 [
            .localGet 19, .localGet 1, .ltU, .const (1 : UInt32), .and, .eqz, .br_if 0,
            .localGet 0, .localGet 19, .const (2 : UInt32), .shl, .add, .load32 (0 : UInt32),
            .localSet 20,
            .localGet 6, .load32 (16 : UInt32), .localSet 21,
            .localGet 21, .localGet 5, .ltU, .const (1 : UInt32), .and, .br_if 1, .br 2
          ] env = .Break 1 stB { locB21 with values := locB.values } := by
          have hgv19 : ∀ xs, ({ locB19 with values := xs } : Locals).get 19 = locB19.get 19 := fun _ => rfl
          have hgv1' : ∀ xs, ({ locB19 with values := xs } : Locals).get 1 = locB19.get 1 := fun _ => rfl
          have hgv0 : ∀ xs, ({ locB19 with values := xs } : Locals).get 0 = locB19.get 0 := fun _ => rfl
          have hgv6' : ∀ xs, ({ locB19 with values := xs } : Locals).get 6 = locB19.get 6 := fun _ => rfl
          have hgv20_6 : ∀ xs, ({ locB20 with values := xs } : Locals).get 6 = locB20.get 6 := fun _ => rfl
          have hgv21_21 : ∀ xs, ({ locB21 with values := xs } : Locals).get 21 = locB21.get 21 := fun _ => rfl
          have hgv21_5 : ∀ xs, ({ locB21 with values := xs } : Locals).get 5 = locB21.get 5 := fun _ => rfl
          have hlocB20_get6 : locB20.get 6 = some (.i32 frame) := by
            show ({ locB19 with locals := locB19.locals.set 14 (.i32 left_i) } : Locals).get 6 = _
            simp only [Locals.get, hlocB19_params, hlocB19_locals, List.length_set,
                       show ¬((6 : Nat) < 6) from by omega,
                       show (6 : Nat) < 6 + 16 from by omega,
                       show (6 : Nat) - 6 = 0 from by omega,
                       List.getElem?_set, show (14 : Nat) ≠ 0 from by omega, if_false]
            simpa [Locals.get, hlocB19_params, hlocB19_locals, show ¬((6 : Nat) < 6) from by omega] using hlocB19_get6
          have hget20_6_raw : ∀ xs,
              (Locals.mk locB19.params (locB19.locals.set 14 (.i32 left_i)) xs).get 6
              = some (.i32 frame) := fun xs => (hgv20_6 xs).trans hlocB20_get6
          have hget21_21_raw : ∀ xs,
              (Locals.mk locB19.params
                ((locB19.locals.set 14 (.i32 left_i)).set 15 (.i32 (UInt32.ofNat k_val))) xs).get 21
              = some (.i32 (UInt32.ofNat k_val)) := fun xs => (hgv21_21 xs).trans hlocB21_get21
          have hget21_5_raw : ∀ xs,
              (Locals.mk locB19.params
                ((locB19.locals.set 14 (.i32 left_i)).set 15 (.i32 (UInt32.ofNat k_val))) xs).get 5
              = some (.i32 n_out) := fun xs => (hgv21_5 xs).trans hlocB21_get5
          have hk2_m' : stB.mem.read32 (frame + 16) = UInt32.ofNat k_val := hk2_m
          simp only [exec, execOne.eq_def, Locals.set?,
                     hgv19, hgv1', hgv0, hgv6',
                     hlocB19_get19, hlocB19_get1,
                     if_pos hi2_lt32,
                     show (1 : UInt32) &&& 1 = 1 from by decide,
                     show (if (1 : UInt32) = 0 then (1 : UInt32) else 0) = 0 from by decide,
                     hlocB19_get0, hlocB19_get6, hk2_m',
                     if_neg (show ¬(frame.toNat + (16 : UInt32).toNat + 4
                                     > stB.mem.pages * 65536) from by simp; omega),
                     hlocB19_params, hlocB19_locals, List.length_set,
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
                     if_neg (show ¬((4 * UInt32.ofNat i2 + left_ptr).toNat +
                                     UInt32.toNat 0 + 4 > stB.mem.pages * 65536) from by
                               rw [show 4 * UInt32.ofNat i2 + left_ptr =
                                     left_ptr + 4 * UInt32.ofNat i2 from UInt32.add_comm _ _,
                                   hleft_i_toNat, show UInt32.toNat 0 = 0 from rfl]; omega),
                     show stB.mem.read32 (4 * UInt32.ofNat i2 + left_ptr + (0 : UInt32)) = left_i from by
                       rw [show 4 * UInt32.ofNat i2 + left_ptr + (0 : UInt32) =
                               left_ptr + 4 * UInt32.ofNat i2 from by
                             rw [UInt32.add_comm (4 * UInt32.ofNat i2) left_ptr, UInt32.add_zero]],
                     if_pos hk_lt32,
                     show (1 : UInt32) &&& 1 = 1 from by decide,
                     hshl_i2]
          simp only [locB19, locB20, locB21]
          rfl
        -- h_bci_block
        have h_bci_block : exec 2 m stB locB19 [
            .block 0 0 [
              .localGet 19, .localGet 1, .ltU, .const (1 : UInt32), .and, .eqz, .br_if 0,
              .localGet 0, .localGet 19, .const (2 : UInt32), .shl, .add, .load32 (0 : UInt32),
              .localSet 20,
              .localGet 6, .load32 (16 : UInt32), .localSet 21,
              .localGet 21, .localGet 5, .ltU, .const (1 : UInt32), .and, .br_if 1, .br 2
            ],
            .localGet 19, .localGet 1, .const (1048680 : UInt32), .call 87, .unreachable
          ] env = .Break 0 stB { locB21 with values := locB.values } := by
          rw [show (2 : Nat) = 1 + 1 from rfl, exec_block_cons, h_bci_body]
        -- h_bco_body for outer
        have h_bco_body : exec 3 m stB locB19 [
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
            .store32 (16 : UInt32), .br 1
          ] env = .Break 1 stC sB := by
          rw [show (3 : Nat) = 2 + 1 from rfl, exec_block_cons, h_bci_block]
          simp only [List.take_zero, List.drop_zero, List.nil_append]
          have hgv21_4 : ∀ xs, ({ locB21 with values := xs } : Locals).get 4 = locB21.get 4 := fun _ => rfl
          have hgv21_21 : ∀ xs, ({ locB21 with values := xs } : Locals).get 21 = locB21.get 21 := fun _ => rfl
          have hgv21_20 : ∀ xs, ({ locB21 with values := xs } : Locals).get 20 = locB21.get 20 := fun _ => rfl
          have hgv21_6 : ∀ xs, ({ locB21 with values := xs } : Locals).get 6 = locB21.get 6 := fun _ => rfl
          simp only [exec, execOne.eq_def,
                     hgv21_4, hgv21_21, hgv21_20, hgv21_6,
                     hlocB21_get4, hlocB21_get21, hlocB21_get20, hlocB21_get6,
                     hi2_m, hk2_m,
                     show ∀ v, (stB.mem.write32 (out_ptr + 4 * UInt32.ofNat k_val) v).read32 (frame + 8)
                           = stB.mem.read32 (frame + 8) from fun v =>
                       Mem.read32_write32_of_disjoint stB.mem (out_ptr + 4 * UInt32.ofNat k_val) (frame + 8) v
                         (by rw [hframe_toNat8, hout_k_toNat];
                             rcases hframe_out_disj' with h | h <;> [right; left] <;> omega),
                     show ∀ v1 v2, ((stB.mem.write32 (out_ptr + 4 * UInt32.ofNat k_val) v1).write32
                                   (frame + 8) v2).read32 (frame + 16)
                           = stB.mem.read32 (frame + 16) from fun v1 v2 =>
                       (Mem.read32_write32_of_disjoint _ (frame + 8) (frame + 16) v2
                         (by left; rw [hframe_toNat8, hframe_toNat16]; omega)).trans
                       (Mem.read32_write32_of_disjoint stB.mem (out_ptr + 4 * UInt32.ofNat k_val) (frame + 16) v1
                         (by rw [hframe_toNat16, hout_k_toNat];
                             rcases hframe_out_disj' with h | h <;> [right; left] <;> omega)),
                     show ∀ nn, (1 : UInt32) + UInt32.ofNat nn = UInt32.ofNat nn + 1 from fun nn => UInt32.add_comm _ _,
                     hshl_k,
                     Mem.write32_pages,
                     if_neg (show ¬(frame.toNat + (8 : UInt32).toNat + 4
                                     > stB.mem.pages * 65536) from by simp; omega),
                     if_neg (show ¬(frame.toNat + (16 : UInt32).toNat + 4
                                     > stB.mem.pages * 65536) from by simp; omega),
                     show 4 * UInt32.ofNat k_val + out_ptr = out_ptr + 4 * UInt32.ofNat k_val from UInt32.add_comm _ _,
                     UInt32.add_zero,
                     if_neg (show ¬((out_ptr + 4 * UInt32.ofNat k_val).toNat +
                                     (0 : UInt32).toNat + 4 > stB.mem.pages * 65536) from by
                               simp [hout_k_toNat]; omega),
                     if_neg (show ¬(frame.toNat + (8 : UInt32).toNat + 4
                                     > mem1.pages * 65536) from by
                               simp [mem1, Mem.write32_pages]; omega),
                     if_neg (show ¬(frame.toNat + (16 : UInt32).toNat + 4
                                     > mem2.pages * 65536) from by
                               simp [mem2, mem1, Mem.write32_pages]; omega)]
          simp only [stC, sB, mem1, mem2, mem3, locB21, left_i]
          rfl
        -- h_body: exec 4 outerDrainBody = Break 0 stC sB
        have h_body : exec 4 m stB locB outerDrainBody env = .Break 0 stC sB := by
          show exec 4 m stB locB (.block 0 0 _ :: _) env = _
          rw [h_condblock, show (4 : Nat) = 3 + 1 from rfl, exec_block_cons, h_bco_body]
        -- invariant maintenance
        have hframe_toNat8' : (frame + 8).toNat = frame.toNat + 8 := hframe_toNat8
        have hframe_toNat16' : (frame + 16).toNat = frame.toNat + 16 := hframe_toNat16
        have hhi_next : UInt32.ofNat i2 + 1 = UInt32.ofNat (i2 + 1) := by
          apply UInt32.toNat_inj.mp
          simp only [UInt32.toNat_add, UInt32.toNat_ofNat', show (1 : UInt32).toNat = 1 from rfl,
                     Nat.mod_eq_of_lt (show i2 + 1 < 4294967296 from by have := n_left.toNat_lt; omega)]
          omega
        have hk_next : UInt32.ofNat k_val + 1 = UInt32.ofNat (k_val + 1) := by
          apply UInt32.toNat_inj.mp
          simp only [UInt32.toNat_add, UInt32.toNat_ofNat', show (1 : UInt32).toNat = 1 from rfl,
                     Nat.mod_eq_of_lt (show k_val + 1 < 4294967296 from by have := n_out.toNat_lt; omega)]
          omega
        have hi2_m_next : stC.mem.read32 (frame + 8) = UInt32.ofNat (i2 + 1) := by
          simp only [stC, mem3, mem2, mem1]
          rw [Mem.read32_write32_of_disjoint _ (frame + 16) (frame + 8) _
                (by right; rw [hframe_toNat8', hframe_toNat16']; omega),
              Mem.read32_write32_same, hhi_next]
        have hk_m_next : stC.mem.read32 (frame + 16) = UInt32.ofNat (k_val + 1) := by
          simp only [stC, mem3]; rw [Mem.read32_write32_same, hk_next]
        have hj2_m_stC : stC.mem.read32 (frame + 12) = UInt32.ofNat n_right.toNat := by
          -- j2 = n_right.toNat by assumption, and stC doesn't touch frame+12
          have hframe_toNat12 : (frame + 12).toNat = frame.toNat + 12 := by
            rw [UInt32.toNat_add]; simp [UInt32.toNat_ofNat']; omega
          simp only [stC, mem3, mem2, mem1]
          rw [Mem.read32_write32_of_disjoint _ (frame + 16) (frame + 12) _
                (by right; rw [hframe_toNat16, hframe_toNat12]),
              Mem.read32_write32_of_disjoint _ (frame + 8) (frame + 12) _
                (by left; rw [hframe_toNat8, hframe_toNat12]),
              Mem.read32_write32_of_disjoint _ (out_ptr + 4 * UInt32.ofNat k_val) (frame + 12) _
                (by rcases hframe_out_disj' with h | h
                    · right; rw [hframe_toNat12, hout_k_toNat]; omega
                    · left; rw [hframe_toNat12, hout_k_toNat]; omega),
              hj2_m]
        have hleft_stC : ∀ q, q < n_left.toNat →
            stC.mem.read32 (left_ptr + 4 * UInt32.ofNat q) =
            st_init.mem.read32 (left_ptr + 4 * UInt32.ofNat q) := by
          intro q hq
          have hqtoNat : (left_ptr + 4 * UInt32.ofNat q).toNat = left_ptr.toNat + 4 * q :=
            toNat_wordAddr left_ptr n_left.toNat q hq (by linarith)
          simp only [stC, mem3, mem2, mem1]
          rw [Mem.read32_write32_of_disjoint _ (frame + 16) _ _
                (by rcases hframe_left_disj' with h | h
                    · left; rw [hframe_toNat16, hqtoNat]; omega
                    · right; rw [hframe_toNat16, hqtoNat]; omega),
              Mem.read32_write32_of_disjoint _ (frame + 8) _ _
                (by rcases hframe_left_disj' with h | h
                    · left; rw [hframe_toNat8, hqtoNat]; omega
                    · right; rw [hframe_toNat8, hqtoNat]; omega),
              Mem.read32_write32_of_disjoint _ (out_ptr + 4 * UInt32.ofNat k_val) _ _
                (by rw [hout_k_toNat, hqtoNat]; rcases hleft_out_disj' with h | h <;> [right; left] <;> omega)]
          exact hleft' q hq
        have hright_stC : ∀ q, q < n_right.toNat →
            stC.mem.read32 (right_ptr + 4 * UInt32.ofNat q) =
            st_init.mem.read32 (right_ptr + 4 * UInt32.ofNat q) := by
          intro q hq
          have hqtoNat : (right_ptr + 4 * UInt32.ofNat q).toNat = right_ptr.toNat + 4 * q :=
            toNat_wordAddr right_ptr n_right.toNat q hq (by linarith)
          simp only [stC, mem3, mem2, mem1]
          rw [Mem.read32_write32_of_disjoint _ (frame + 16) _ _
                (by rcases hframe_right_disj' with h | h
                    · left; rw [hframe_toNat16, hqtoNat]; omega
                    · right; rw [hframe_toNat16, hqtoNat]; omega),
              Mem.read32_write32_of_disjoint _ (frame + 8) _ _
                (by rcases hframe_right_disj' with h | h
                    · left; rw [hframe_toNat8, hqtoNat]; omega
                    · right; rw [hframe_toNat8, hqtoNat]; omega),
              Mem.read32_write32_of_disjoint _ (out_ptr + 4 * UInt32.ofNat k_val) _ _
                (by rw [hout_k_toNat, hqtoNat]; rcases hright_out_disj' with h | h <;> [right; left] <;> omega)]
          exact hright' q hq
        -- content invariant for stC
        -- hcontent' at (i2, n_right): wordsAt stB out (i2+n_right) ++ merge(left₁.drop i2, []) = merge(...)
        -- merge(left₁.drop i2, []) = left₁.drop i2 (merge_nil_right)
        -- After writing left[i2] at out[k_val = i2+n_right]:
        -- wordsAt stC out ((i2+1)+n_right) = wordsAt stB out (i2+n_right) ++ [left[i2]]
        -- merge(left₁.drop (i2+1), []) = left₁.drop (i2+1)
        -- left₁.drop i2 = [left[i2]] ++ left₁.drop (i2+1)
        -- So content holds for (i2+1, n_right)
        have hright_drop : (wordsAt st_init.mem right_ptr n_right.toNat).drop n_right.toNat = [] := by
          simp [List.drop_length]
        simp only [show UInt32.ofNat 0 = 0 from rfl, UInt32.mul_zero, UInt32.add_zero] at hcontent'
        rw [hright_drop, merge_nil_right] at hcontent'
        have hcontent_next : wordsAt stC.mem (out_ptr + 4 * UInt32.ofNat 0) ((i2 + 1) + n_right.toNat) ++
            List.merge ((wordsAt st_init.mem left_ptr n_left.toNat).drop (i2 + 1))
                       ((wordsAt st_init.mem right_ptr n_right.toNat).drop n_right.toNat) (· ≤ ·) =
            List.merge (wordsAt st_init.mem left_ptr n_left.toNat)
                       (wordsAt st_init.mem right_ptr n_right.toNat) (· ≤ ·) := by
          rw [hright_drop, merge_nil_right]
          -- need: wordsAt stC out ((i2+1)+n_right) = wordsAt stB out (i2+n_right) ++ [left[i2]]
          -- and: left₁.drop (i2+1) = ... left₁.drop i2 minus first element
          -- left₁.drop i2 = [left₁[i2]] ++ left₁.drop (i2+1)
          -- From hcontent': wordsAt stB out (i2+n_right) ++ left₁.drop i2 = merge(left₁, right₁)
          -- wordsAt stC out ((i2+1)+n_right) ++ left₁.drop (i2+1)
          -- = wordsAt stC out (i2+n_right) ++ [left[i2]] ++ left₁.drop (i2+1)
          -- = wordsAt stB out (i2+n_right) ++ [left₁[i2]] ++ left₁.drop (i2+1)  (preservation)
          -- = wordsAt stB out (i2+n_right) ++ left₁.drop i2  (since drop i2 = [i2] :: drop (i2+1))
          -- = merge(left₁, right₁) from hcontent'
          simp only [show (i2 + 1) + n_right.toNat = (i2 + n_right.toNat) + 1 from by omega]
          -- wordsAt stC out (i2+n_right+1) = wordsAt stC out (i2+n_right) ++ [stC.mem.read32(out+4*(i2+n_right))]
          rw [show (i2 + n_right.toNat + 1 : Nat) = (i2 + n_right.toNat) + 1 from rfl]
          simp only [show UInt32.ofNat 0 = 0 from rfl, UInt32.mul_zero, UInt32.add_zero]
          rw [wordsAt_split stC.mem out_ptr ((i2 + n_right.toNat) + 1) (i2 + n_right.toNat) (by omega)]
          simp only [show (i2 + n_right.toNat + 1 - (i2 + n_right.toNat) : Nat) = 1 from by omega]
          -- wordsAt stC out (i2+n_right) = wordsAt stB out (i2+n_right) by preservation
          have hpres_prefix : wordsAt stC.mem out_ptr (i2 + n_right.toNat) =
              wordsAt stB.mem out_ptr (i2 + n_right.toNat) := by
            apply List.ext_getElem
            · simp [wordsAt_length]
            · intro idx hidx1 _
              simp only [wordsAt, List.getElem_map, List.getElem_range]
              have hidx_lt : idx < i2 + n_right.toNat := by simp [wordsAt_length] at hidx1; exact hidx1
              have hidxtoNat : (out_ptr + 4 * UInt32.ofNat idx).toNat = out_ptr.toNat + 4 * idx :=
                toNat_wordAddr out_ptr n_out.toNat idx (by omega) (by linarith)
              simp only [stC, mem3, mem2, mem1]
              rw [Mem.read32_write32_of_disjoint _ (frame + 16) _ _
                    (by rcases hframe_out_disj' with h | h
                        · left; rw [hframe_toNat16, hidxtoNat]; omega
                        · right; rw [hframe_toNat16, hidxtoNat]; omega),
                  Mem.read32_write32_of_disjoint _ (frame + 8) _ _
                    (by rcases hframe_out_disj' with h | h
                        · left; rw [hframe_toNat8, hidxtoNat]; omega
                        · right; rw [hframe_toNat8, hidxtoNat]; omega),
                  Mem.read32_write32_of_disjoint _ (out_ptr + 4 * UInt32.ofNat k_val) _ _
                    (by rw [hout_k_toNat, hidxtoNat]; omega)]
          -- stC.mem.read32 at k_val = left_i = left₁[i2]
          have hread_kval : stC.mem.read32 (out_ptr + 4 * UInt32.ofNat k_val) = left_i := by
            simp only [stC, mem3, mem2, mem1]
            rw [Mem.read32_write32_of_disjoint _ (frame + 16) _ _
                  (by rcases hframe_out_disj' with h | h
                      · left; rw [hframe_toNat16, hout_k_toNat]; omega
                      · right; rw [hframe_toNat16, hout_k_toNat]; omega),
                Mem.read32_write32_of_disjoint _ (frame + 8) _ _
                  (by rcases hframe_out_disj' with h | h
                      · left; rw [hframe_toNat8, hout_k_toNat]; omega
                      · right; rw [hframe_toNat8, hout_k_toNat]; omega),
                Mem.read32_write32_same]
          -- wordsAt stC out@k_val 1 = [left_i]
          have hwat1 : wordsAt stC.mem (out_ptr + 4 * UInt32.ofNat k_val) 1 = [left_i] := by
            simp [wordsAt, hread_kval]
          -- k_val = i2 + n_right
          have hkval_eq : k_val = i2 + n_right.toNat := rfl
          rw [hpres_prefix, ← hkval_eq, hwat1]
          -- Now: wordsAt stB out (i2+n_right) ++ [left_i] ++ left₁.drop (i2+1) = merge(left₁, right₁)
          -- left₁.drop i2 = [left_i] ++ left₁.drop (i2+1) (using left_i = st_init.mem.read32(left+4*i2))
          rw [List.append_assoc, ← hcontent']
          congr 1
          -- left₁.drop i2 = [left_i] ++ left₁.drop (i2+1)
          have hleft_drop_eq : (wordsAt st_init.mem left_ptr n_left.toNat).drop i2 =
              [st_init.mem.read32 (left_ptr + 4 * UInt32.ofNat i2)] ++
              (wordsAt st_init.mem left_ptr n_left.toNat).drop (i2 + 1) := by
            rw [wordsAt_drop_eq, wordsAt_drop_eq,
                show n_left.toNat - i2 = 1 + (n_left.toNat - (i2 + 1)) from by omega,
                wordsAt_split _ _ _ 1 (by omega),
                show 1 + (n_left.toNat - (i2 + 1)) - 1 = n_left.toNat - (i2 + 1) from by omega]
            simp only [wordsAt, List.range_succ, List.range_zero, List.nil_append,
                       List.map_cons, List.map_nil,
                       show UInt32.ofNat 0 = 0 from rfl, UInt32.mul_zero, UInt32.add_zero]
            congr 1
            apply List.map_congr_left
            intro i _
            congr 1
            rw [UInt32.ofNat_add, UInt32.mul_add, ← UInt32.add_assoc]
          rw [hleft_drop_eq]
          -- left_i = st_init.mem.read32(left+4*i2) (from hleft': source unchanged)
          have hleft_i_eq : left_i = st_init.mem.read32 (left_ptr + 4 * UInt32.ofNat i2) := by
            rw [← hleft' i2 hi2_lt]
          rw [← hleft_i_eq]
        -- sB locals helpers
        have hsB_params : sB.params.length = 6 := by simp [sB, locB21, locB20, locB19, hlparams']
        have hsB_locals : sB.locals.length = 16 := by simp [sB, locB21, locB20, locB19, List.length_set, hllocals']
        have hsB_get6 : sB.get 6 = some (.i32 frame) := hlocB21_get6
        have hsB_get0 : sB.get 0 = some (.i32 left_ptr) := by
          have hlen20p : locB20.params.length = 6 := by simp [locB20, hlocB19_params]
          simp only [Locals.get, sB, locB21, hlen20p, show (0 : Nat) < 6 from by omega]
          simp only [Locals.get, locB20, hlocB19_params, show (0 : Nat) < 6 from by omega]
          simp only [Locals.get, hlparams', show (0 : Nat) < 6 from by omega] at h0'; exact h0'
        have hsB_get1 : sB.get 1 = some (.i32 n_left) := by
          have hlen20p : locB20.params.length = 6 := by simp [locB20, hlocB19_params]
          simp only [Locals.get, sB, locB21, hlen20p, show (1 : Nat) < 6 from by omega]
          simp only [Locals.get, locB20, hlocB19_params, show (1 : Nat) < 6 from by omega]
          simp only [Locals.get, hlparams', show (1 : Nat) < 6 from by omega] at h1'; exact h1'
        have hsB_get2 : sB.get 2 = some (.i32 right_ptr) := by
          have hlen20p : locB20.params.length = 6 := by simp [locB20, hlocB19_params]
          simp only [Locals.get, sB, locB21, hlen20p, show (2 : Nat) < 6 from by omega]
          simp only [Locals.get, locB20, hlocB19_params, show (2 : Nat) < 6 from by omega]
          simp only [Locals.get, hlparams', show (2 : Nat) < 6 from by omega] at h2'; exact h2'
        have hsB_get3 : sB.get 3 = some (.i32 n_right) := by
          have hlen20p : locB20.params.length = 6 := by simp [locB20, hlocB19_params]
          simp only [Locals.get, sB, locB21, hlen20p, show (3 : Nat) < 6 from by omega]
          simp only [Locals.get, locB20, hlocB19_params, show (3 : Nat) < 6 from by omega]
          simp only [Locals.get, hlparams', show (3 : Nat) < 6 from by omega] at h3'; exact h3'
        have hsB_get4 : sB.get 4 = some (.i32 out_ptr) := hlocB21_get4
        have hsB_get5 : sB.get 5 = some (.i32 n_out) := hlocB21_get5
        -- Apply IH at (stC, sB, i2+1, n_right)
        obtain ⟨N_ih, stF, h_ih, h_ih_content⟩ :=
          IH (n - 1) (by omega) stC sB (i2 + 1) n_right.toNat (by omega)
            (by omega) (le_refl _) (Or.inr rfl)
            hsB_get6 hsB_get0 hsB_get1 hsB_get2 hsB_get3 hsB_get4 hsB_get5
            hsB_params hsB_locals
            ⟨_, hglobal'.choose_spec⟩
            (by simpa using hi2_m_next)
            (by simpa using hj2_m_stC)
            (by rw [hk_m_next]; congr 1; omega)
            hleft_stC hright_stC
            (by simpa using hcontent_next)
            (by simp [stC, mem3, mem2, mem1, Mem.write32_pages]; omega)
            (by omega)
            (by simp [stC, mem3, mem2, mem1, Mem.write32_pages]; omega)
            (by simp [stC, mem3, mem2, mem1, Mem.write32_pages]; omega)
            (by simp [stC, mem3, mem2, mem1, Mem.write32_pages]; omega)
            (by simp [stC, mem3, mem2, mem1, Mem.write32_pages]; exact hpages_u32')
            hleft_out_disj' hright_out_disj' hleft_right_disj'
            hframe_left_disj' hframe_right_disj' hframe_out_disj'
        -- combine
        have h_body_ne : exec 4 m stB locB outerDrainBody env ≠ .OutOfFuel := by
          rw [h_body]; intro h; cases h
        have h_body' : exec (max N_ih 4) m stB locB outerDrainBody env = .Break 0 stC sB :=
          (exec_fuel_mono (Nat.le_max_right N_ih 4) h_body_ne).trans h_body
        have h_ih_ne : exec N_ih m stC sB [.loop 0 0 outerDrainBody] env ≠ .OutOfFuel := by
          rw [h_ih]; intro h; cases h
        have h_ih' : exec (max N_ih 4) m stC sB [.loop 0 0 outerDrainBody] env = .Return stF sB.values :=
          (exec_fuel_mono (Nat.le_max_left N_ih 4) h_ih_ne).trans h_ih
        have hone_cs : execOne (max N_ih 4) m stC sB (.loop 0 0 outerDrainBody) env = .Return stF sB.values :=
          execOne_of_exec_singleton h_ih'
        have hone_stB : execOne (max N_ih 4 + 1) m stB locB (.loop 0 0 outerDrainBody) env =
            .Return stF locB.values := by
          rw [execOne_loop_succ]
          simp only [h_body', List.take_zero, List.nil_append, List.drop_zero]
          have : ({ sB with values := locB.values } : Locals) = sB := by simp [sB]
          rw [this, hone_cs]
        exact ⟨max N_ih 4 + 1, stF, by simp [exec, hone_stB], h_ih_content⟩

end Wasm.SepLogic.MergeSort
