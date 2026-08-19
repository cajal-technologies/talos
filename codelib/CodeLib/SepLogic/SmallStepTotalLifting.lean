import CodeLib.SepLogic.SmallStepState
import Iris.ProgramLogic.TotalLifting

/-!
# Total Iris lifting rules for Wasm small steps

The ordinary lifting layer is guarded by `▷`, as required by partial `WP`.
Total weakest preconditions are inductive and therefore deliberately expose
their recursive continuation without a later. This file starts a separate
total lifting layer over the same authoritative `Wasm.SmallStep.Step`
relation.
-/

namespace Iris.ProgramLogic

open Iris Language Language.Notation BI

section
variable {hlc : outParam HasLC} {Expr State Obs Val}
variable [Λ : Language Expr State Obs Val]
variable {GF : BundledGFunctors} [ι : IrisGS_gen hlc Expr GF]
variable {s : Stuckness} {E : CoPset}
variable {e₁ : Expr} {Φ : Val → IProp GF}

/-- Total lifting for steps that fork no threads. Lived in iris-lean's
`TotalLifting` until iris-lean#554 was merged without it; ported verbatim
(modulo the upstream rename `twp_lift_step` → `twp.lift_step`). -/
theorem twp_lift_step_no_fork (h : toVal e₁ = none) :
    (∀ σ₁ ns obs nt, stateInterp σ₁ ns obs nt ={E,∅}=∗
      ⌜s.MaybeReducibleNoObs (e₁, σ₁)⌝ ∗
      ∀ κ e₂ σ₂ eₜ, ⌜(e₁, σ₁) -<κ>-> (e₂, σ₂, eₜ)⌝ ={∅,E}=∗
        ⌜κ = []⌝ ∗ ⌜eₜ = []⌝ ∗
        stateInterp σ₂ (ns + 1) obs nt ∗
        WP e₂ @ s; E [{ Φ }])
    ⊢ WP e₁ @ s; E [{ Φ }] := by
  iintro H
  iapply twp.lift_step h
  iintro %σ₁ %ns %obs %nt Hσ
  imod H $$ Hσ with ⟨%Hred, H⟩
  imodintro
  iframe %Hred
  iintro %κ %e₂ %σ₂ %eₜ %Hstep
  imod H $$ %κ %e₂ %σ₂ %eₜ %Hstep with ⟨%hκ, %heₜ, Hσ, Hwp⟩
  subst heₜ
  imodintro
  simp only [List.length_nil, Nat.add_zero, Algebra.BigOpL.bigOpL_nil]
  iframe %hκ Hσ Hwp

end

end Iris.ProgramLogic

namespace Wasm.SmallStep

open Iris Iris.ProgramLogic Language.Notation
open Wasm.SepLogic

variable [WasmSmallStepGS hlc α]
local instance instWasmTotalIrisGS :
    IrisGS_gen hlc (Expr α) (WasmHeapGF α) :=
  instIrisGS
variable {s : Stuckness} {E : CoPset}
variable {Φ : List Value → IProp (WasmHeapGF α)}

/-- Generic total lifting rule for a store-preserving deterministic Wasm
step. Unlike `wp_pureStep`, its continuation is not guarded by a later. -/
theorem twp_pureStep
    (kind : StepKind) (current next : ThreadState α)
    (hstep : ∀ store : MachineStore α,
      Step ⟨.running current, store⟩ kind ⟨.running next, store⟩) :
    WP (Expr.running next : Expr α) @ s; E [{ Φ }] ⊢
      WP (Expr.running current : Expr α) @ s; E [{ Φ }] := by
  iintro Htwp
  iapply twp_lift_step_no_fork rfl
  iintro %store %ns %obs %nt Hσ
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducibleNoObs]
    exact ⟨.running next, store, [],
      ⟨rfl, kind, rfl, hstep store⟩⟩
  iintro %κ %e₂ %store₂ %forks %Hprim
  rcases Hprim with ⟨hforks, actualKind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst κ
  obtain ⟨rfl, hconfig⟩ :=
    step_deterministic (hstep store) wasmStep
  have parts := Config.mk.inj hconfig
  have hexpr := parts.1
  have hstore := parts.2
  simp only at hexpr hstore
  subst e₂
  subst store₂
  imod Hclose
  imodintro
  isplit
  · ipureintro
    rfl
  isplit
  · ipureintro
    rfl
  iframe

/-- A normally finishing body is a total step to its result value. -/
theorem twp_finish
    {locals : Locals} {values : List Value} {arity : Nat}
    {remainder : List Value} :
    WP (.done (values.take arity ++ remainder) : Expr α) @ s; E
        [{ Φ }] ⊢
      WP (.running
        ⟨{ locals with values }, [], arity, remainder, [], []⟩ :
          Expr α) @ s; E [{ Φ }] := by
  iintro Htwp
  iapply twp_lift_step_no_fork rfl
  iintro %store %ns %obs %nt Hσ
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducibleNoObs]
    exact ⟨.done (values.take arity ++ remainder), store, [],
      ⟨rfl, .administrative .finish, rfl, Step.finish⟩⟩
  iintro %κ %e₂ %store₂ %forks %Hprim
  rcases Hprim with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst κ
  obtain ⟨rfl, hconfig⟩ := step_deterministic Step.finish wasmStep
  have parts := Config.mk.inj hconfig
  have hexpr := parts.1
  have hstore := parts.2
  simp only at hexpr hstore
  subst e₂
  subst store₂
  imod Hclose
  imodintro
  isplit
  · ipureintro
    rfl
  isplit
  · ipureintro
    rfl
  iframe

/-- Explicit total return from a top-level invocation. -/
theorem twp_returnFromFunction
    {locals : Locals} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame} :
    WP (.done (locals.values.take arity ++ remainder) : Expr α) @ s; E
        [{ Φ }] ⊢
      WP (.running
        ⟨locals, .ret :: code, arity, remainder, controls, []⟩ : Expr α) @
        s; E [{ Φ }] := by
  iintro Htwp
  iapply twp_lift_step_no_fork rfl
  iintro %store %ns %obs %nt Hσ
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducibleNoObs]
    exact ⟨.done (locals.values.take arity ++ remainder), store, [],
      ⟨rfl, .administrative .returnFromFunction, rfl,
        Step.returnFromFunction⟩⟩
  iintro %κ %e₂ %store₂ %forks %Hprim
  rcases Hprim with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst κ
  obtain ⟨rfl, hconfig⟩ :=
    step_deterministic Step.returnFromFunction wasmStep
  have parts := Config.mk.inj hconfig
  have hexpr := parts.1
  have hstore := parts.2
  simp only at hexpr hstore
  subst e₂
  subst store₂
  imod Hclose
  imodintro
  isplit
  · ipureintro
    rfl
  isplit
  · ipureintro
    rfl
  iframe

theorem twp_remU
    {params localValues values : List Value}
    {dividend divisor : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    (hdivisor : divisor ≠ 0) :
    WP (.running
      ⟨⟨params, localValues, .i32 (dividend % divisor) :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
        [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, .i32 divisor :: .i32 dividend :: values⟩,
        .remU :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.remU hdivisor)

theorem twp_eqz
    {params localValues values : List Value}
    {value result : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    (hresult : result = if value = 0 then 1 else 0) :
    WP (.running
      ⟨⟨params, localValues, .i32 result :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
        [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, .i32 value :: values⟩,
        .eqz :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.eqz hresult)

theorem twp_const
    {params localValues values : List Value}
    {value : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    let current : ThreadState α :=
      ⟨⟨params, localValues, values⟩, .const value :: code,
        arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨⟨params, localValues, .i32 value :: values⟩, code,
        arity, remainder, controls, calls⟩
    WP (Expr.running next : Expr α) @ s; E [{ Φ }] ⊢
      WP (Expr.running current : Expr α) @ s; E [{ Φ }] := by
  dsimp only
  exact twp_pureStep _ _ _ (fun _ => Step.const)

theorem twp_add
    {params localValues values : List Value}
    {lhs rhs : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    WP (.running
      ⟨⟨params, localValues, .i32 (rhs + lhs) :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
        [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, .i32 rhs :: .i32 lhs :: values⟩,
        .add :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.add)

theorem twp_sub
    {params localValues values : List Value}
    {lhs rhs : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    WP (.running
      ⟨⟨params, localValues, .i32 (lhs - rhs) :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
        [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, .i32 rhs :: .i32 lhs :: values⟩,
        .sub :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.sub)

theorem twp_mul
    {params localValues values : List Value}
    {lhs rhs : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    WP (.running
      ⟨⟨params, localValues, .i32 (rhs * lhs) :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
        [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, .i32 rhs :: .i32 lhs :: values⟩,
        .mul :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.mul)

theorem twp_shl
    {params localValues values : List Value}
    {lhs rhs : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    WP (.running
      ⟨⟨params, localValues, .i32 (lhs <<< (rhs % 32)) :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
        [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, .i32 rhs :: .i32 lhs :: values⟩,
        .shl :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.shl)

theorem twp_ltU
    {params localValues values : List Value}
    {lhs rhs result : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    (hresult : result = if lhs < rhs then 1 else 0) :
    WP (.running
      ⟨⟨params, localValues, .i32 result :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
        [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, .i32 rhs :: .i32 lhs :: values⟩,
        .ltU :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.ltU hresult)

theorem twp_iff
    {params localValues values : List Value}
    {condition : UInt32}
    {paramArity resultArity arity : Nat}
    {thenBody elseBody selectedBody code : Program}
    {paramTypes resultTypes : List ValueType}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    (hselected :
      selectedBody = if condition ≠ 0 then thenBody else elseBody) :
    WP (.running
      ⟨⟨params, localValues, values⟩, selectedBody, arity, remainder,
        { kind := .block, paramArity, resultArity,
          body := selectedBody, continuation := code,
          belowStack := values.drop paramArity } :: controls,
        calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, .i32 condition :: values⟩,
        .iff paramArity resultArity thenBody elseBody
          paramTypes resultTypes :: code,
        arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.iff hselected)

theorem twp_block
    {locals : Locals} {paramArity resultArity arity : Nat}
    {body code : Program} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    let frame : ControlFrame :=
      { kind := .block
        paramArity
        resultArity
        body
        continuation := code
        belowStack := locals.values.drop paramArity }
    WP (.running
      ⟨locals, body, arity, remainder, frame :: controls, calls⟩ :
        Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨locals, .block paramArity resultArity body :: code,
        arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] := by
  dsimp only
  exact twp_pureStep _ _ _ (fun _ => Step.block)

theorem twp_loop
    {locals : Locals} {paramArity resultArity arity : Nat}
    {body code : Program} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    let frame : ControlFrame :=
      { kind := .loop
        paramArity
        resultArity
        body
        continuation := code
        belowStack := locals.values.drop paramArity }
    WP (.running
      ⟨locals, body, arity, remainder, frame :: controls, calls⟩ :
        Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨locals, .loop paramArity resultArity body :: code,
        arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] := by
  dsimp only
  exact twp_pureStep _ _ _ (fun _ => Step.loop)

theorem twp_exitControl
    {locals : Locals} {frame : ControlFrame}
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (hkind : frame.kind.isThrowing = false) :
    WP (.running
      ⟨{ locals with
          values := locals.values.take frame.resultArity ++ frame.belowStack },
        frame.continuation, arity, remainder, controls, calls⟩ :
        Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨locals, [], arity, remainder, frame :: controls, calls⟩ :
        Expr α) @ s; E [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.exitControl hkind)

theorem twp_brIfZero
    {params localValues values : List Value}
    {depth arity : Nat} {code : Program} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    WP (.running
      ⟨⟨params, localValues, values⟩, code,
        arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, .i32 0 :: values⟩, .br_if depth :: code,
        arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.brIfZero)

theorem twp_brIf
    {params localValues values targetValues : List Value}
    {condition : UInt32} {depth arity : Nat}
    {code targetCode : Program} {remainder : List Value}
    {controls targetControl : List ControlFrame} {calls : List CallFrame}
    (hcondition : condition ≠ 0)
    (htarget : branchTarget? arity depth controls values =
      some (targetCode, targetControl, targetValues)) :
    WP (.running
      ⟨⟨params, localValues, targetValues⟩, targetCode,
        arity, remainder, targetControl, calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, .i32 condition :: values⟩,
        .br_if depth :: code, arity, remainder, controls, calls⟩ :
        Expr α) @ s; E [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.brIf hcondition htarget)

theorem twp_br
    {params localValues values targetValues : List Value}
    {depth arity : Nat} {code targetCode : Program}
    {remainder : List Value}
    {controls targetControl : List ControlFrame} {calls : List CallFrame}
    (htarget : branchTarget? arity depth controls values =
      some (targetCode, targetControl, targetValues)) :
    WP (.running
      ⟨⟨params, localValues, targetValues⟩, targetCode,
        arity, remainder, targetControl, calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, values⟩, .br depth :: code,
        arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.br htarget)

theorem twp_localGet
    {params localValues values : List Value}
    {index : Nat} {value : Value} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    (hget : (⟨params, localValues, values⟩ : Locals).get index =
      some value) :
    let current : ThreadState α :=
      ⟨⟨params, localValues, values⟩, .localGet index :: code,
        arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨⟨params, localValues, value :: values⟩, code,
        arity, remainder, controls, calls⟩
    WP (Expr.running next : Expr α) @ s; E [{ Φ }] ⊢
      WP (Expr.running current : Expr α) @ s; E [{ Φ }] := by
  dsimp only
  exact twp_pureStep _ _ _ (fun _ => Step.localGet hget)

theorem twp_localSet
    {params localValues values : List Value}
    {index : Nat} {value : Value} {locals' : Locals}
    {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    (hset : (⟨params, localValues, value :: values⟩ : Locals).set? index value =
      some locals') :
    let current : ThreadState α :=
      ⟨⟨params, localValues, value :: values⟩, .localSet index :: code,
        arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨{ locals' with values }, code, arity, remainder, controls, calls⟩
    WP (Expr.running next : Expr α) @ s; E [{ Φ }] ⊢
      WP (Expr.running current : Expr α) @ s; E [{ Φ }] := by
  dsimp only
  exact twp_pureStep _ _ _ (fun _ => Step.localSet hset)

/-- Total entry rule for a defined Wasm function. -/
theorem twp_call
    (runtimeModule : Module) (functionIndex : Nat) (fn : Function)
    (himports : ¬functionIndex < runtimeModule.imports.length)
    (hfn : runtimeModule.funcs[
      functionIndex - runtimeModule.imports.length]? = some fn)
    {params localValues values : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    let caller : CallFrame :=
      { locals := ⟨params, localValues, values.drop fn.numParams⟩
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls }
    let current : ThreadState α :=
      ⟨⟨params, localValues, values⟩, .call functionIndex :: code,
        arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨fn.toLocals (values.take fn.numParams).reverse,
        fn.body, fn.results.length, [], [], caller :: calls⟩
    runtimeModuleOwn runtimeModule -∗
    (runtimeModuleOwn runtimeModule -∗
      WP (Expr.running next : Expr α) @ s; E [{ Φ }]) -∗
      WP (Expr.running current : Expr α) @ s; E [{ Φ }] := by
  dsimp only
  iintro Hruntime Htwp
  iapply twp_lift_step_no_fork rfl
  iintro %store %ns %obs %nt Hσ
  ihave %Hmodule : ⌜store.runtime.module = runtimeModule⌝ $$
      [Hσ Hruntime]
  · imod stateInterp_runtimeModule_agree store ns obs nt
      runtimeModule $$ [$Hσ $Hruntime] with %Hmodule
    ipureintro
    exact Hmodule
  have himports' :
      ¬functionIndex < store.runtime.module.imports.length := by
    simpa only [Hmodule] using himports
  have hfn' : store.runtime.module.funcs[
      functionIndex - store.runtime.module.imports.length]? = some fn := by
    simpa only [Hmodule] using hfn
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducibleNoObs]
    exact ⟨.running
        ⟨fn.toLocals (values.take fn.numParams).reverse,
          fn.body, fn.results.length, [], [],
          { locals := ⟨params, localValues, values.drop fn.numParams⟩
            continuation := code
            resultArity := arity
            callerRemainder := remainder
            control := controls } :: calls⟩,
      store, [], ⟨rfl, .instruction (.call functionIndex), rfl,
        Step.call himports' hfn'⟩⟩
  iintro %κ %e₂ %store₂ %forks %Hstep
  rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst κ
  obtain ⟨rfl, hconfig⟩ :=
    step_deterministic (Step.call (α := α) himports' hfn') wasmStep
  have parts := Config.mk.inj hconfig
  have hexpr := parts.1
  have hstore := parts.2
  simp only at hexpr hstore
  subst e₂
  subst store₂
  imod Hclose
  imodintro
  isplit
  · ipureintro
    rfl
  isplit
  · ipureintro
    rfl
  isplitl [Hσ]
  · iexact Hσ
  · iapply Htwp
    iexact Hruntime

theorem twp_returnFromCallExplicit
    {calleeLocals callerLocals : Locals}
    {calleeCode callerCode : Program}
    {calleeArity callerArity : Nat}
    {calleeRemainder callerRemainder : List Value}
    {calleeControls callerControls : List ControlFrame}
    {calls : List CallFrame} :
    let caller : CallFrame :=
      { locals := callerLocals
        continuation := callerCode
        resultArity := callerArity
        callerRemainder := callerRemainder
        control := callerControls }
    let current : ThreadState α :=
      ⟨calleeLocals, .ret :: calleeCode, calleeArity, calleeRemainder,
        calleeControls, caller :: calls⟩
    let next : ThreadState α :=
      ⟨{ callerLocals with
          values :=
            calleeLocals.values.take calleeArity ++ callerLocals.values },
        callerCode, callerArity, callerRemainder, callerControls, calls⟩
    WP (Expr.running next : Expr α) @ s; E [{ Φ }] ⊢
      WP (Expr.running current : Expr α) @ s; E [{ Φ }] := by
  dsimp only
  exact twp_pureStep _ _ _ (fun _ => Step.returnFromCallExplicit)

theorem twp_load32
    {params localValues values : List Value}
    {address offset : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} (word : UInt32)
    (hnowrap : (address + offset).toNat =
      address.toNat + offset.toNat)
    (h1 : ((address + offset) + 1).toNat =
      (address + offset).toNat + 1)
    (h2 : ((address + offset) + 2).toNat =
      (address + offset).toNat + 2)
    (h3 : ((address + offset) + 3).toNat =
      (address + offset).toNat + 3) :
    let current : ThreadState α :=
      ⟨⟨params, localValues, .i32 address :: values⟩,
        .load32 offset :: code, arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨⟨params, localValues, .i32 word :: values⟩,
        code, arity, remainder, controls, calls⟩
    pointsTo_u32 (address + offset) word -∗
    (pointsTo_u32 (address + offset) word -∗
      WP (Expr.running next : Expr α) @ s; E [{ Φ }]) -∗
      WP (Expr.running current : Expr α) @ s; E [{ Φ }] := by
  dsimp only
  iintro Hword Htwp
  iapply twp_lift_step_no_fork rfl
  iintro %store %ns %obs %nt Hσ
  ihave %Hfacts :
      ⌜store.wasm.mem.read32 (address + offset) = word ∧
        (address + offset).toNat + 4 ≤
          store.wasm.mem.pages * 65536⌝ $$ [Hσ Hword]
  · imod stateInterp_pointsTo_u32_facts store ns obs nt
      (address + offset) word h1 h2 h3 $$ [$Hσ $Hword] with %Hfacts
    ipureintro
    exact Hfacts
  obtain ⟨Hread, HinBounds⟩ := Hfacts
  have hbound : address.toNat + offset.toNat + 4 ≤
      store.wasm.mem.pages * 65536 := by
    simpa only [hnowrap] using HinBounds
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducibleNoObs]
    exact ⟨.running
        ⟨⟨params, localValues, .i32 word :: values⟩,
          code, arity, remainder, controls, calls⟩,
      store, [], ⟨rfl, .instruction (.load32 offset), rfl,
        by simpa [Hread] using Step.load32 hbound⟩⟩
  iintro %κ %e₂ %store₂ %forks %Hstep
  rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst κ
  have expectedStep : Step
      ⟨.running
        ⟨⟨params, localValues, .i32 address :: values⟩,
          .load32 offset :: code, arity, remainder, controls, calls⟩,
        store⟩
      (.instruction (.load32 offset))
      ⟨.running
        ⟨⟨params, localValues, .i32 word :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩ := by
    simpa [Hread] using (Step.load32 (α := α) hbound)
  obtain ⟨rfl, hconfig⟩ :=
    step_deterministic expectedStep wasmStep
  have parts := Config.mk.inj hconfig
  have hexpr := parts.1
  have hstore := parts.2
  simp only at hexpr hstore
  subst e₂
  subst store₂
  imod Hclose
  imodintro
  isplit
  · ipureintro
    rfl
  isplit
  · ipureintro
    rfl
  isplitl [Hσ]
  · iexact Hσ
  · iapply Htwp
    iexact Hword

theorem twp_store32
    {params localValues values : List Value}
    {address offset value : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} (oldWord : UInt32)
    (hnowrap : (address + offset).toNat =
      address.toNat + offset.toNat)
    (h1 : ((address + offset) + 1).toNat =
      (address + offset).toNat + 1)
    (h2 : ((address + offset) + 2).toNat =
      (address + offset).toNat + 2)
    (h3 : ((address + offset) + 3).toNat =
      (address + offset).toNat + 3) :
    let current : ThreadState α :=
      ⟨⟨params, localValues, .i32 value :: .i32 address :: values⟩,
        .store32 offset :: code, arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨⟨params, localValues, values⟩,
        code, arity, remainder, controls, calls⟩
    pointsTo_u32 (address + offset) oldWord -∗
    (pointsTo_u32 (address + offset) value -∗
      WP (Expr.running next : Expr α) @ s; E [{ Φ }]) -∗
      WP (Expr.running current : Expr α) @ s; E [{ Φ }] := by
  dsimp only
  iintro Hword Htwp
  iapply twp_lift_step_no_fork rfl
  iintro %store %ns %obs %nt Hσ
  ihave %Hfacts :
      ⌜store.wasm.mem.read32 (address + offset) = oldWord ∧
        (address + offset).toNat + 4 ≤
          store.wasm.mem.pages * 65536⌝ $$ [Hσ Hword]
  · imod stateInterp_pointsTo_u32_facts store ns obs nt
      (address + offset) oldWord h1 h2 h3 $$ [$Hσ $Hword] with %Hfacts
    ipureintro
    exact Hfacts
  have hbound : address.toNat + offset.toNat + 4 ≤
      store.wasm.mem.pages * 65536 := by
    simpa only [hnowrap] using Hfacts.2
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducibleNoObs]
    exact ⟨.running
        ⟨⟨params, localValues, values⟩,
          code, arity, remainder, controls, calls⟩,
      { store with wasm :=
          { store.wasm with
            mem := store.wasm.mem.write32 (address + offset) value } },
      [], ⟨rfl, .instruction (.store32 offset), rfl,
        Step.store32 hbound⟩⟩
  iintro %κ %e₂ %store₂ %forks %Hstep
  rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst κ
  have expectedStep : Step
      ⟨.running
        ⟨⟨params, localValues, .i32 value :: .i32 address :: values⟩,
          .store32 offset :: code, arity, remainder, controls, calls⟩,
        store⟩
      (.instruction (.store32 offset))
      ⟨.running
        ⟨⟨params, localValues, values⟩,
          code, arity, remainder, controls, calls⟩,
        { store with wasm :=
            { store.wasm with
              mem := store.wasm.mem.write32 (address + offset) value } }⟩ :=
    Step.store32 hbound
  obtain ⟨rfl, hconfig⟩ :=
    step_deterministic expectedStep wasmStep
  have parts := Config.mk.inj hconfig
  have hexpr := parts.1
  have hstore := parts.2
  simp only at hexpr hstore
  subst e₂
  subst store₂
  imod stateInterp_store32 store ns obs nt
      (address + offset) oldWord value h1 h2 h3 Hfacts.2 $$
      [$Hσ $Hword] with ⟨Hσ, Hword⟩
  imod Hclose
  imodintro
  isplit
  · ipureintro
    rfl
  isplit
  · ipureintro
    rfl
  isplitl [Hσ]
  · iexact Hσ
  · iapply Htwp
    iexact Hword

end Wasm.SmallStep
