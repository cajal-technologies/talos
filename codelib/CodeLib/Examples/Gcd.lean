import CodeLib.SepLogic.SmallStepAdequacy

/-!
# Euclidean GCD

A handwritten Wasm implementation of Euclid's algorithm and its Iris
weakest-precondition proof.  The loop invariant is indexed by the current
pair of locals and records that their mathematical gcd is unchanged.
-/

namespace Wasm.Examples.Gcd

open Wasm
open Iris Iris.ProgramLogic Language.Notation
open Wasm.SepLogic
open Wasm.SmallStep

def gcdLoopBlock : Program := [
  .localGet 1,
  .eqz,
  .br_if 0,
  .localGet 0,
  .localGet 1,
  .remU,
  .localSet 2,
  .localGet 1,
  .localSet 0,
  .localGet 2,
  .localSet 1,
  .br 1
]

def gcdLoopBody : Program := [.block 0 0 gcdLoopBlock]

/-- Handwritten Wasm body for unsigned Euclidean GCD. -/
def gcdBody : Program := [
  .loop 0 0 gcdLoopBody,
  .localGet 0,
  .ret
]

def gcdFunction : Function :=
  { params := [.i32, .i32]
    results := [.i32]
    locals := [.i32]
    body := gcdBody }

def gcdModule : Module := { funcs := [gcdFunction] }

private def gcdLocals (a b temporary : UInt32) : Locals :=
  ⟨[.i32 a, .i32 b], [.i32 temporary], []⟩

private def gcdInvariant (a₀ b₀ : UInt32)
    (state : UInt32 × UInt32 × UInt32) : IProp WasmHeapGF :=
  iprop% ⌜Nat.gcd state.1.toNat state.2.1.toNat =
    Nat.gcd a₀.toNat b₀.toNat⌝

set_option maxHeartbeats 2000000 in
/-- Iris WP for the handwritten function body.  The theorem is contextual in
the call stack, so it can be used after the ordinary `wp_call` rule. -/
theorem wp_gcdBody
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (a b : UInt32) (calls : List CallFrame)
    (hreturn : ∀ (currentA currentB temporary : UInt32),
      currentB = 0 →
      Nat.gcd currentA.toNat currentB.toNat =
        Nat.gcd a.toNat b.toNat →
      ⊢@{IProp WasmHeapGF}
        WP (.running
          ⟨{ gcdLocals currentA currentB temporary with
              values := [.i32 currentA] },
            [.ret], 1, [], [], calls⟩ :
            Expr Unit) @ s; E {{ Φ }}) :
    ⊢@{IProp WasmHeapGF}
      WP (.running
        ⟨gcdLocals a b 0, gcdBody, 1, [], [], calls⟩ :
          Expr Unit) @ s; E {{ Φ }} := by
  simp only [gcdBody]
  iapply wp_loop_löb_family
    (ι := UInt32 × UInt32 × UInt32)
    (locals := fun state =>
      gcdLocals state.1 state.2.1 state.2.2)
    (I := gcdInvariant a b)
    (initial := (a, b, 0))
    (belowStack := [])
    rfl
  intro state
  simp only [gcdInvariant, Wasm.SmallStep.loopBodyExpr]
  iintro Hrec HI
  icases HI with %Hgcd
  simp only [gcdLoopBody, gcdLoopBlock]
  iapply wp_block
  inext
  iapply wp_localGet rfl
  inext
  by_cases hb : state.2.1 = 0
  · iapply wp_eqz (result := 1) (by simp [hb])
    inext
    iapply wp_brIf (by decide) rfl
    inext
    iapply wp_exitControl rfl
    inext
    iapply wp_localGet rfl
    inext
    iclear Hrec
    simp only [gcdLocals, List.take_nil, List.drop_nil, List.nil_append]
    exact hreturn state.1 state.2.1 state.2.2 hb Hgcd
  · iapply wp_eqz (result := 0) (by simp [hb])
    inext
    iapply wp_brIfZero
    inext
    iapply wp_localGet rfl
    inext
    iapply wp_localGet rfl
    inext
    iapply Wasm.SmallStep.wp_remU hb
    inext
    iapply wp_localSet rfl
    inext
    iapply wp_localGet rfl
    inext
    iapply wp_localSet rfl
    inext
    iapply wp_localGet rfl
    inext
    iapply wp_localSet rfl
    inext
    iapply wp_br rfl
    inext
    simp [gcdLocals, List.set]
    ispecialize Hrec $$
      %(state.2.1, state.1 % state.2.1, state.1 % state.2.1)
    iapply Hrec
    ipureintro
    have hstep :
        Nat.gcd state.2.1.toNat
            (state.1.toNat % state.2.1.toNat) =
          Nat.gcd state.1.toNat state.2.1.toNat := by
      rw [Nat.gcd_comm state.2.1.toNat
          (state.1.toNat % state.2.1.toNat),
        Nat.gcd_comm state.1.toNat state.2.1.toNat,
        Nat.gcd_rec state.2.1.toNat state.1.toNat]
    exact (by simpa using hstep.trans Hgcd)
  · simp only [gcdInvariant]
    itrivial

/-- Closed WP: the function returns the mathematical gcd of its two inputs. -/
theorem wp_gcd
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    (a b : UInt32) :
    ⊢@{IProp WasmHeapGF}
      WP (.running
        ⟨gcdLocals a b 0, gcdBody, 1, [], [], []⟩ :
          Expr Unit) @ s; E
        {{ values,
          ⌜values =
            [.i32 (UInt32.ofNat (Nat.gcd a.toNat b.toNat))]⌝ }} := by
  iapply wp_gcdBody a b []
  intro currentA currentB temporary hzero Hgcd
  subst currentB
  iapply wp_returnFromFunction
  inext
  iapply wp_value'
  ipureintro
  simp
  have hcurrent :
      currentA.toNat = Nat.gcd a.toNat b.toNat := by
    simpa [Nat.gcd_zero_right] using Hgcd
  congr 2
  calc
    currentA = UInt32.ofNat currentA.toNat :=
      (UInt32.ofNat_toNat : UInt32.ofNat currentA.toNat = currentA).symm
    _ = UInt32.ofNat (Nat.gcd a.toNat b.toNat) :=
      congrArg UInt32.ofNat hcurrent

end Wasm.Examples.Gcd
