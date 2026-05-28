import Interpreter.Wasm.Wp.Tactic
import Interpreter.Wasm.Wp.Block
import Interpreter.Wasm.Wp.Call

/-! ## Example: IsEvenRec / IsOddRec

    Mutually recursive parity check. Spec proven by strong induction on the
    input `n`, using each function's spec as the IH for the other's call.
    Termination measure: the input value, strictly smaller per recursive call. -/

namespace Wasm

def IsEvenRec : Program := [
    .block 0 0 [.localGet 0, .eqz, .br_if 0, .localGet 0, .const 1, .sub, .call 1, .eqz, .localSet 0],
    .localGet 0, .eqz
]

def IsOddRec : Program := [
  .block 0 0 [.localGet 0, .eqz, .br_if 0, .localGet 0, .const 1, .sub, .call 0, .localSet 0],
  .localGet 0
]

def evenOddModule : Module :=
  { funcs := [{ params := [.i32], body := IsEvenRec, results := [.i32] },
              { params := [.i32], body := IsOddRec,  results := [.i32] }] }

/-- Joint spec for both functions, proven simultaneously by strong induction
    on `n.toNat` (the unsigned measure). -/
theorem evenOddSpec : ∀ n : UInt32,
    FuncSpec evenOddModule 0 (· = [.i32 n])
      (fun _ vs => vs = [.i32 (if n.toNat % 2 = 0 then 1 else 0)]) ∧
    FuncSpec evenOddModule 1 (· = [.i32 n])
      (fun _ vs => vs = [.i32 (if n.toNat % 2 = 1 then 1 else 0)]) := by
  intro n
  induction hk : n.toNat using Nat.strong_induction_on generalizing n with
  | _ k ih =>
  subst hk
  have ih' : ∀ (k : UInt32), k.toNat < n.toNat →
      FuncSpec evenOddModule 0 (· = [.i32 k])
        (fun _ vs => vs = [.i32 (if k.toNat % 2 = 0 then 1 else 0)]) ∧
      FuncSpec evenOddModule 1 (· = [.i32 k])
        (fun _ vs => vs = [.i32 (if k.toNat % 2 = 1 then 1 else 0)]) := by
    intro k hk; exact ih k.toNat hk k rfl
  clear ih
  refine ⟨?_, ?_⟩
  · -- IsEvenRec
    apply FuncSpec.of_wp_body (f := { params := [.i32], body := IsEvenRec, results := [.i32] })
    · rfl
    · rintro args rfl initial
      simp [Function.toLocals, Function.numParams]
      unfold IsEvenRec
      apply wp_block_cons
      wp_run
      simp
      by_cases hn : n = 0
      · subst hn; simp
      · have hn1 : (n - 1).toNat < n.toNat := by
          have hnn : n.toNat ≠ 0 := fun h => hn (UInt32.toNat.inj h)
          rw [UInt32.toNat_sub]
          simp only [show (1 : UInt32).toNat = 1 from rfl]
          have := n.toNat_lt
          omega
        have ihOdd := (ih' (n - 1) hn1).2
        simp [hn]
        apply wp_call_cons
          (Pre := (· = [.i32 (n - 1)]))
          (Post := fun _ vs => vs = [.i32 (if (n-1).toNat % 2 = 1 then 1 else 0)])
          ihOdd
        · rfl
        · rintro st' vs rfl
          wp_run
          simp
          have hnn : n.toNat ≠ 0 := fun h => hn (UInt32.toNat.inj h)
          have hnsub : (n - 1).toNat = n.toNat - 1 := by
            rw [UInt32.toNat_sub]
            simp only [show (1 : UInt32).toNat = 1 from rfl]
            have := n.toNat_lt
            omega
          rw [hnsub]
          split_ifs <;> simp_all <;> omega
  · -- IsOddRec
    apply FuncSpec.of_wp_body (f := { params := [.i32], body := IsOddRec, results := [.i32] })
    · rfl
    · rintro args rfl initial
      simp [Function.toLocals, Function.numParams]
      unfold IsOddRec
      apply wp_block_cons
      wp_run
      simp
      by_cases hn : n = 0
      · subst hn; simp
      · have hn1 : (n - 1).toNat < n.toNat := by
          have hnn : n.toNat ≠ 0 := fun h => hn (UInt32.toNat.inj h)
          rw [UInt32.toNat_sub]
          simp only [show (1 : UInt32).toNat = 1 from rfl]
          have := n.toNat_lt
          omega
        have ihEven := (ih' (n - 1) hn1).1
        simp [hn]
        apply wp_call_cons
          (Pre := (· = [.i32 (n - 1)]))
          (Post := fun _ vs => vs = [.i32 (if (n-1).toNat % 2 = 0 then 1 else 0)])
          ihEven
        · rfl
        · rintro st' vs rfl
          wp_run
          simp
          have hnn : n.toNat ≠ 0 := fun h => hn (UInt32.toNat.inj h)
          have hnsub : (n - 1).toNat = n.toNat - 1 := by
            rw [UInt32.toNat_sub]
            simp only [show (1 : UInt32).toNat = 1 from rfl]
            have := n.toNat_lt
            omega
          rw [hnsub]
          split_ifs <;> simp_all <;> omega

end Wasm
