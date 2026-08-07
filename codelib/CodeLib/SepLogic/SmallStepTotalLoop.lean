import CodeLib.SepLogic.SmallStepLifting
import CodeLib.SepLogic.SmallStepTotalLifting

/-!
# Well-founded loop family rule for total Wasm weakest preconditions

`wp_loop_löb_family` closes a partial loop proof with guarded Löb induction.
Total weakest preconditions have no later to guard the recursive occurrence,
so the corresponding total rule takes a `Nat` measure on the family index and
offers the recursive hypothesis only at strictly smaller measures. That is the
variant supplying the termination argument Iris partial correctness omits.
-/

namespace Wasm.SmallStep

open Iris Iris.ProgramLogic Language.Notation
open Wasm.SepLogic

variable [WasmSmallStepGS hlc]
local instance instWasmTotalLoopIrisGS :
    IrisGS_gen hlc (Expr α) WasmHeapGF :=
  instIrisGS
variable {s : Stuckness} {E : CoPset}
variable {Φ : List Value → IProp WasmHeapGF}

/-- Total counterpart of `wp_loop_löb_family`. The body proof may branch back
to any family index whose measure is strictly smaller, which is exactly the
well-founded variant a terminating loop provides. -/
theorem twp_loop_wf_family
    {ι : Type} (measure : ι → Nat)
    (locals : ι → Locals) (I : ι → IProp WasmHeapGF)
    (initial : ι) (initialLocals : Locals)
    {paramArity resultArity arity : Nat}
    {body code : Program} {remainder belowStack : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (hinitial : locals initial = initialLocals)
    (hbelow : belowStack = (locals initial).values.drop paramArity)
    (body_closes : ∀ i,
      ⊢@{IProp WasmHeapGF} (iprop%
        (∀ (j : ι), ⌜measure j < measure i⌝ -∗ I j -∗
          WP (loopBodyExpr (α := α) (locals j)
            paramArity resultArity arity body code remainder belowStack
            controls calls) @ s; E [{ Φ }]) -∗
        I i -∗
          WP (loopBodyExpr (α := α) (locals i)
            paramArity resultArity arity body code remainder belowStack
            controls calls) @ s; E [{ Φ }])) :
    I initial ⊢
      WP (.running
        ⟨initialLocals, .loop paramArity resultArity body :: code,
          arity, remainder, controls, calls⟩ : Expr α) @ s; E
        [{ Φ }] := by
  have closes : ∀ i,
      I i ⊢
        WP (loopBodyExpr (α := α) (locals i)
          paramArity resultArity arity body code remainder belowStack
          controls calls) @ s; E [{ Φ }] := by
    intro current
    induction hmeasure : measure current using Nat.strongRecOn
        generalizing current with
    | ind n ih =>
      subst n
      iintro HI
      iapply body_closes current
      · iintro %j %hji Hj
        ihave Hih := ih (measure j) hji j rfl $$ Hj
        iexact Hih
      · iexact HI
  simp only [loopBodyExpr] at closes
  subst initialLocals
  iintro HI
  iapply twp_loop
  rw [← hbelow]
  ihave Hbody := closes initial $$ HI
  iexact Hbody

end Wasm.SmallStep
