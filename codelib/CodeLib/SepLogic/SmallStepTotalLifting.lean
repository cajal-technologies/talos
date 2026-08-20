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
    {controls : List ControlFrame} {calls : List CallFrame}
    (callerId : ModuleInstanceId) :
    let caller : CallFrame :=
      { locals := ⟨params, localValues, values.drop fn.numParams⟩
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls
        returningInstance := callerId }
    let current : ThreadState α :=
      ⟨⟨params, localValues, values⟩, .call functionIndex :: code,
        arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨fn.toLocals (values.take fn.numParams).reverse,
        fn.body, fn.results.length, [], [], caller :: calls⟩
    runtimeModuleOwn callerId runtimeModule -∗
    (runtimeModuleOwn callerId runtimeModule -∗
      WP (Expr.running next : Expr α) @ s; E [{ Φ }]) -∗
      WP (Expr.running current : Expr α) @ s; E [{ Φ }] := by
  dsimp only
  iintro Hruntime Htwp
  iapply twp_lift_step_no_fork rfl
  iintro %store %ns %obs %nt Hσ
  ihave %Hmodule : ⌜store.runtime.currentModule = runtimeModule⌝ $$
      [Hσ Hruntime]
  · imod stateInterp_runtimeModule_agree store ns obs nt
      callerId runtimeModule $$ [$Hσ $Hruntime] with %Hmodule
    ipureintro
    exact Hmodule
  have himports' :
      ¬functionIndex < store.runtime.currentModule.imports.length := by
    simpa only [Hmodule] using himports
  have hfn' : store.runtime.currentModule.funcs[
      functionIndex - store.runtime.currentModule.imports.length]? = some fn := by
    simpa only [Hmodule] using hfn
  simp only [runtimeModuleOwn]
  icases Hruntime with ⟨HruntimeElem, HinstanceOwn⟩
  ihave %Hentry : ⌜store.runtime.entry = callerId⌝ $$ [Hσ HinstanceOwn]
  · imod stateInterp_currentInstance_agree store ns obs nt callerId $$
        [$Hσ $HinstanceOwn] with %Hentry
    ipureintro
    exact Hentry
  have hsame : callerId = store.runtime.entry := Hentry.symm
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
            control := controls
            returningInstance := store.runtime.entry } :: calls⟩,
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
  · rw [← hsame]
    iapply Htwp
    isplitl [HruntimeElem]
    · iexact HruntimeElem
    · iexact HinstanceOwn

theorem twp_returnFromCallExplicit
    {calleeLocals callerLocals : Locals}
    {calleeCode callerCode : Program}
    {calleeArity callerArity : Nat}
    {calleeRemainder callerRemainder : List Value}
    {calleeControls callerControls : List ControlFrame}
    {returningInstance : ModuleInstanceId}
    {module : Module}
    {calls : List CallFrame} :
    let caller : CallFrame :=
      { locals := callerLocals
        continuation := callerCode
        resultArity := callerArity
        callerRemainder := callerRemainder
        control := callerControls
        returningInstance := returningInstance }
    let current : ThreadState α :=
      ⟨calleeLocals, .ret :: calleeCode, calleeArity, calleeRemainder,
        calleeControls, caller :: calls⟩
    let next : ThreadState α :=
      ⟨{ callerLocals with
          values :=
            calleeLocals.values.take calleeArity ++ callerLocals.values },
        callerCode, callerArity, callerRemainder, callerControls, calls⟩
    runtimeModuleOwn returningInstance module -∗
    (runtimeModuleOwn returningInstance module -∗
      WP (Expr.running next : Expr α) @ s; E [{ Φ }]) -∗
      WP (Expr.running current : Expr α) @ s; E [{ Φ }] := by
  dsimp only
  iintro Hruntime Hwp
  iapply twp_lift_step_no_fork rfl
  iintro %store %ns %obs %nt Hσ
  simp only [runtimeModuleOwn]
  icases Hruntime with ⟨HruntimeElem, HinstanceOwn⟩
  ihave %Hentry : ⌜store.runtime.entry = returningInstance⌝ $$ [Hσ HinstanceOwn]
  · imod stateInterp_currentInstance_agree store ns obs nt returningInstance $$
        [$Hσ $HinstanceOwn] with %Hentry
    ipureintro
    exact Hentry
  have hsame : returningInstance = store.runtime.entry := Hentry.symm
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducibleNoObs]
    exact ⟨_, store, [],
      ⟨rfl, _, rfl, Step.returnFromCallExplicit hsame⟩⟩
  iintro %κ %e₂ %store₂ %forks %Hstep
  rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst κ
  obtain ⟨rfl, hconfig⟩ :=
    step_deterministic (Step.returnFromCallExplicit (α := α) hsame) wasmStep
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
  · simp only [resumeCaller]
    iapply Hwp
    isplitl [HruntimeElem]
    · iexact HruntimeElem
    · iexact HinstanceOwn

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
    pointsTo_u32 0 (address + offset) word -∗
    (pointsTo_u32 0 (address + offset) word -∗
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
    pointsTo_u32 0 (address + offset) oldWord -∗
    (pointsTo_u32 0 (address + offset) value -∗
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

<<<<<<< HEAD
theorem twp_geS
=======
theorem twp_and
    {params localValues values : List Value}
    {lhs rhs : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    WP (.running
      ⟨⟨params, localValues, .i32 (lhs &&& rhs) :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
        [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, .i32 rhs :: .i32 lhs :: values⟩,
        .and :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.and)

theorem twp_ne
>>>>>>> origin/main
    {params localValues values : List Value}
    {lhs rhs result : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
<<<<<<< HEAD
    (hresult : result = if lhs.toInt32 ≥ rhs.toInt32 then 1 else 0) :
=======
    (hresult : result = if lhs ≠ rhs then 1 else 0) :
>>>>>>> origin/main
    WP (.running
      ⟨⟨params, localValues, .i32 result :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
        [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, .i32 rhs :: .i32 lhs :: values⟩,
<<<<<<< HEAD
        .geS :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.geS hresult)

theorem twp_memoryFill32
    {params localValues values : List Value}
    {destination len value : UInt32}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (oldBytes : List UInt8)
    (hlen : oldBytes.length = len.toNat)
    (hpos : 0 < len.toNat)
    (hnowrap : destination.toNat + len.toNat < 4294967296) :
    pointsToBytes destination oldBytes -∗
    (pointsToBytes destination (List.replicate oldBytes.length value.toUInt8) -∗
      WP (Expr.running ⟨⟨params, localValues, values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }]) -∗
    WP (Expr.running ⟨⟨params, localValues,
        .i32 len :: .i32 value :: .i32 destination :: values⟩,
        .memoryFill :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro Hbytes Htwp
  iapply twp_lift_step_no_fork rfl
  iintro %store %ns %obs %nt Hσ
  ihave %Hpb : ⌜∀ i b, oldBytes[i]? = some b →
      store.wasm.mem.read8 (destination + UInt32.ofNat i) = b ∧
      (destination + UInt32.ofNat i).toNat < store.wasm.mem.pages * 65536⌝ $$
      [Hσ Hbytes]
  · imod stateInterp_pointsToBytes_agree store ns obs nt
        destination oldBytes $$ [$Hσ $Hbytes] with %Hpb
    ipureintro
    exact Hpb
  have hbound : destination.toNat + len.toNat ≤ store.wasm.mem.pages * 65536 := by
    have := pointsToBytes_facts_bound Hpb (by omega) (by omega)
    omega
=======
        .ne :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.ne hresult)

theorem twp_globalGet
    {params localValues values : List Value}
    {value : Value} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    let current : ThreadState α :=
      ⟨⟨params, localValues, values⟩, .globalGet 0 :: code,
        arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨⟨params, localValues, value :: values⟩, code,
        arity, remainder, controls, calls⟩
    globalPointsToAt 0 0 value -∗
    (globalPointsToAt 0 0 value -∗
      WP (Expr.running next : Expr α) @ s; E [{ Φ }]) -∗
      WP (Expr.running current : Expr α) @ s; E [{ Φ }] := by
  dsimp only
  iintro Hglobal Htwp
  iapply twp_lift_step_no_fork rfl
  iintro %store %ns %obs %nt Hσ
  have hcanonical : ∀ s : MachineStore α,
      canonicalGlobalIndex s 0 = 0 := fun _ => rfl
  ihave %Hget :
      ⌜store.wasm.globals.globals[0]? = some value⌝ $$ [Hσ Hglobal]
  · imod stateInterp_global_facts store ns obs nt 0 value $$
        [$Hσ $Hglobal] with %Hget
    ipureintro
    exact Hget
>>>>>>> origin/main
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducibleNoObs]
<<<<<<< HEAD
    exact ⟨.running ⟨⟨params, localValues, values⟩,
        code, arity, remainder, controls, calls⟩,
      { store with wasm :=
          { store.wasm with mem :=
              store.wasm.mem.fill destination.toNat len.toNat value.toUInt8 } },
      [], ⟨rfl, .instruction .memoryFill, rfl,
        by simpa only [setMemory_eq] using Step.memoryFill32 hbound⟩⟩
=======
    exact ⟨.running ⟨⟨params, localValues, value :: values⟩,
        code, arity, remainder, controls, calls⟩,
      store, [], ⟨rfl, _, rfl, Step.globalGet (by
        simpa [globalAt?, hcanonical] using Hget)⟩⟩
>>>>>>> origin/main
  iintro %κ %e₂ %store₂ %forks %Hstep
  rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst κ
<<<<<<< HEAD
  have expectedStep : Step
      ⟨.running ⟨⟨params, localValues,
          .i32 len :: .i32 value :: .i32 destination :: values⟩,
          .memoryFill :: code, arity, remainder, controls, calls⟩, store⟩
      (.instruction .memoryFill)
      ⟨.running ⟨⟨params, localValues, values⟩,
          code, arity, remainder, controls, calls⟩,
        { store with wasm :=
            { store.wasm with mem :=
                store.wasm.mem.fill destination.toNat oldBytes.length value.toUInt8 } }⟩ := by
    rw [hlen]
    simpa only [setMemory_eq] using Step.memoryFill32 hbound
  obtain ⟨rfl, hconfig⟩ := step_deterministic expectedStep wasmStep
=======
  obtain ⟨rfl, hconfig⟩ :=
    step_deterministic (Step.globalGet (α := α) (by
      simpa [globalAt?, hcanonical] using Hget)) wasmStep
>>>>>>> origin/main
  have parts := Config.mk.inj hconfig
  have hexpr := parts.1
  have hstore := parts.2
  simp only at hexpr hstore
  subst e₂
  subst store₂
<<<<<<< HEAD
  imod stateInterp_fill_bytes store ns obs nt destination oldBytes value.toUInt8
      (by rw [hlen]; exact hbound) (by rw [hlen]; exact hnowrap)
      $$ [$Hσ $Hbytes] with ⟨Hσ, Hbytes⟩
=======
>>>>>>> origin/main
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
<<<<<<< HEAD
    iexact Hbytes

/-- `throw` instruction (total form).  Tag identity is supplied by the
persistent `tagTableOwn` fragment handed out at adequacy setup, not by an
invariant of the state interpretation: the rule only needs `tagIndex` to be
canonical in the entry instance's tag table, which stays true when the machine
tag table carries further entries from other registered modules. -/
theorem twp_throwI
    (runtimeModule : Module) (tagIndex : Nat) {tagType : FuncType}
    {tagIds : List Nat}
    {params localValues values : List Value}
    (htag : runtimeModule.tags[tagIndex]? = some tagType)
    (hcanonical : TagIndexCanonical tagIds tagIndex)
    (hargs : tagType.params.length ≤ values.length)
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn runtimeModule -∗
    tagTableOwn tagIds -∗
    (runtimeModuleOwn runtimeModule -∗
        WP (.running
          ⟨⟨params, localValues, values.drop tagType.params.length⟩,
            [], arity, remainder,
            { kind := .throwing tagIndex (values.take tagType.params.length)
              paramArity := 0
              resultArity := 0
              body := []
              continuation := []
              belowStack := [] } :: controls,
            calls⟩ : Expr α) @ s; E [{ Φ }]) -∗
    WP (.running
      ⟨⟨params, localValues, values⟩,
        .throwI tagIndex :: code, arity, remainder, controls, calls⟩ :
        Expr α) @ s; E [{ Φ }] := by
  iintro Hruntime Htags Hwp
  iapply twp_lift_step_no_fork rfl
  iintro %store %ns %obs %nt Hσ
  ihave %Hmodule : ⌜store.runtime.module = runtimeModule⌝ $$ [Hσ Hruntime]
  · imod stateInterp_runtimeModule_agree store ns obs nt
        runtimeModule $$ [$Hσ $Hruntime] with %Hmodule
    ipureintro
    exact Hmodule
  have htag' : store.runtime.module.tags[tagIndex]? = some tagType := by
    simpa only [Hmodule] using htag
  ihave %Hprefix : ⌜tagIds.IsPrefix store.wasm.tagIds⌝ $$ [Hσ Htags]
  · imod stateInterp_tagTable_prefix store ns obs nt tagIds $$ [$Hσ $Htags]
      with %Hprefix
    ipureintro
    exact Hprefix
=======
    iexact Hglobal

theorem twp_scalarFloat0
    {params localValues values : List Value}
    {instruction : Instruction} {value : Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (heval : evalScalarFloat0? instruction = some value) :
    WP (.running
      ⟨⟨params, localValues, value :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
        [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, values⟩,
        instruction :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.scalarFloat0 heval)

theorem twp_scalarFloat1
    {params localValues values : List Value}
    {instruction : Instruction} {operand value : Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (hzero : evalScalarFloat0? instruction = none)
    (heval : evalScalarFloat1? instruction operand = some value) :
    WP (.running
      ⟨⟨params, localValues, value :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
        [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, operand :: values⟩,
        instruction :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.scalarFloat1 hzero heval)

theorem twp_scalarFloat2
    {params localValues values : List Value}
    {instruction : Instruction} {lhs rhs value : Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (hzero : evalScalarFloat0? instruction = none)
    (hunary : evalScalarFloat1? instruction rhs = none)
    (heval : evalScalarFloat2? instruction lhs rhs = some value) :
    WP (.running
      ⟨⟨params, localValues, value :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
        [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, rhs :: lhs :: values⟩,
        instruction :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.scalarFloat2 hzero hunary heval)

theorem twp_f32Load
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
        .f32Load offset :: code, arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨⟨params, localValues, .f32 word :: values⟩,
        code, arity, remainder, controls, calls⟩
    pointsTo_u32 0 (address + offset) word -∗
    (pointsTo_u32 0 (address + offset) word -∗
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
>>>>>>> origin/main
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducibleNoObs]
<<<<<<< HEAD
    exact ⟨_, store, [], ⟨rfl, .instruction (.throwI tagIndex), rfl,
        Step.throwI htag' hargs⟩⟩
=======
    exact ⟨.running
        ⟨⟨params, localValues, .f32 word :: values⟩,
          code, arity, remainder, controls, calls⟩,
      store, [], ⟨rfl, .instruction (.f32Load offset), rfl,
        by simpa [Hread] using
          Step.f32Load (α := α) (address := .i32 address) rfl hbound⟩⟩
>>>>>>> origin/main
  iintro %κ %e₂ %store₂ %forks %Hstep
  rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst κ
<<<<<<< HEAD
  obtain ⟨rfl, hconfig⟩ :=
    step_deterministic (Step.throwI (α := α) htag' hargs) wasmStep
=======
  have expectedStep : Step
      ⟨.running
        ⟨⟨params, localValues, .i32 address :: values⟩,
          .f32Load offset :: code, arity, remainder, controls, calls⟩,
        store⟩
      (.instruction (.f32Load offset))
      ⟨.running
        ⟨⟨params, localValues, .f32 word :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩ := by
    simpa [Hread] using
      (Step.f32Load (α := α) (address := .i32 address) rfl hbound)
  obtain ⟨rfl, hconfig⟩ :=
    step_deterministic expectedStep wasmStep
>>>>>>> origin/main
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
<<<<<<< HEAD
  · have hcanonicalStore :=
      (canonicalTagIndex_eq store tagIndex).trans
        (canonicalTagIndex_of_prefix store tagIds tagIndex Hprefix hcanonical)
    rw [hcanonicalStore]
    iapply Hwp
    iexact Hruntime

theorem twp_catchException
    {locals : Locals} {tag : Nat} {arguments : List Value}
    {throwingFrame : ControlFrame}
    {catches : List CatchClause}
    {handlerParamArity handlerResultArity : Nat}
    {handlerBody handlerContinuation : Program}
    {belowStack : List Value}
    {outer : List ControlFrame} {arity : Nat} {remainder : List Value}
    {calls : List CallFrame}
    {clause : CatchClause}
    {targetCode : Program} {targetControl : List ControlFrame}
    {targetValues : List Value}
    (htarget : ∀ store : MachineStore α,
        branchTarget? arity
          (match clause with
            | .catch _ l | .catchRef _ l | .catchAll l | .catchAllRef l => l)
          outer
          ((prepareCatch tag arguments clause store).1 ++ belowStack) =
          some (targetCode, targetControl, targetValues))
    (hthrow : throwingFrame.kind = .throwing tag arguments)
    (hmatch : matchingCatch? tag catches = some clause) :
    WP (.running ⟨{ locals with values := targetValues }, targetCode,
            arity, remainder, targetControl, calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running ⟨locals, [], arity, remainder,
            throwingFrame ::
              { kind := .tryTable catches, paramArity := handlerParamArity,
                resultArity := handlerResultArity, body := handlerBody,
                continuation := handlerContinuation, belowStack } :: outer,
            calls⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro Hwp
  iapply twp_lift_step_no_fork rfl
  iintro %store %ns %obs %nt Hσ
=======
  · iapply Htwp
    iexact Hword

theorem twp_f32Store
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
      ⟨⟨params, localValues, .f32 value :: .i32 address :: values⟩,
        .f32Store offset :: code, arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨⟨params, localValues, values⟩,
        code, arity, remainder, controls, calls⟩
    pointsTo_u32 0 (address + offset) oldWord -∗
    (pointsTo_u32 0 (address + offset) value -∗
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
>>>>>>> origin/main
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducibleNoObs]
<<<<<<< HEAD
    exact ⟨.running ⟨{ locals with values := targetValues }, targetCode,
        arity, remainder, targetControl, calls⟩,
      (prepareCatch tag arguments clause store).2, [],
      ⟨rfl, .administrative .catchException, rfl,
        Step.catchException hthrow hmatch (htarget store)⟩⟩
=======
    exact ⟨.running
        ⟨⟨params, localValues, values⟩,
          code, arity, remainder, controls, calls⟩,
      { store with wasm :=
          { store.wasm with
            mem := store.wasm.mem.write32 (address + offset) value } },
      [], ⟨rfl, .instruction (.f32Store offset), rfl,
        by simpa only [Wasm.SmallStep.setMemory_eq] using
          Step.f32Store (address := .i32 address) rfl hbound⟩⟩
>>>>>>> origin/main
  iintro %κ %e₂ %store₂ %forks %Hstep
  rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst κ
  have expectedStep : Step
<<<<<<< HEAD
      ⟨.running ⟨locals, [], arity, remainder,
          throwingFrame ::
            { kind := .tryTable catches, paramArity := handlerParamArity,
              resultArity := handlerResultArity, body := handlerBody,
              continuation := handlerContinuation, belowStack } :: outer,
          calls⟩, store⟩
      (.administrative .catchException)
      ⟨.running ⟨{ locals with values := targetValues }, targetCode,
          arity, remainder, targetControl, calls⟩,
        (prepareCatch tag arguments clause store).2⟩ :=
    Step.catchException hthrow hmatch (htarget store)
  obtain ⟨rfl, hconfig⟩ := step_deterministic expectedStep wasmStep
=======
      ⟨.running
        ⟨⟨params, localValues, .f32 value :: .i32 address :: values⟩,
          .f32Store offset :: code, arity, remainder, controls, calls⟩,
        store⟩
      (.instruction (.f32Store offset))
      ⟨.running
        ⟨⟨params, localValues, values⟩,
          code, arity, remainder, controls, calls⟩,
        { store with wasm :=
            { store.wasm with
              mem := store.wasm.mem.write32 (address + offset) value } }⟩ := by
    simpa only [Wasm.SmallStep.setMemory_eq] using
      Step.f32Store (address := .i32 address) rfl hbound
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

theorem twp_globalSet
    {params localValues values : List Value}
    {oldValue newValue : Value} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    let current : ThreadState α :=
      ⟨⟨params, localValues, newValue :: values⟩,
        .globalSet 0 :: code, arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨⟨params, localValues, values⟩,
        code, arity, remainder, controls, calls⟩
    globalPointsToAt 0 0 oldValue -∗
    (globalPointsToAt 0 0 newValue -∗
      WP (Expr.running next : Expr α) @ s; E [{ Φ }]) -∗
      WP (Expr.running current : Expr α) @ s; E [{ Φ }] := by
  dsimp only
  iintro Hglobal Htwp
  iapply twp_lift_step_no_fork rfl
  iintro %store %ns %obs %nt Hσ
  have hcanonical : ∀ s : MachineStore α,
      canonicalGlobalIndex s 0 = 0 := fun _ => rfl
  ihave %Hget :
      ⌜store.wasm.globals.globals[0]? = some oldValue⌝ $$ [Hσ Hglobal]
  · imod stateInterp_global_facts store ns obs nt 0 oldValue $$
        [$Hσ $Hglobal] with %Hget
    ipureintro
    exact Hget
  have hsome :
      (globalAt? store 0).isSome = true := by
    simp [globalAt?, hcanonical, Hget]
  let updatedStore : MachineStore α :=
    { store with wasm :=
        { store.wasm with globals :=
            { globals := store.wasm.globals.globals.set 0 newValue } } }
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducibleNoObs]
    exact ⟨.running
        ⟨⟨params, localValues, values⟩,
          code, arity, remainder, controls, calls⟩,
      updatedStore, [], ⟨rfl, _, rfl, by
        dsimp [updatedStore]
        rw [← setGlobal_eq_of_canonical store 0 newValue (hcanonical store)]
        exact Step.globalSet hsome⟩⟩
  iintro %κ %e₂ %store₂ %forks %Hstep
  rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst κ
  have expectedStep : Step
      ⟨.running
        ⟨⟨params, localValues, newValue :: values⟩,
          .globalSet 0 :: code, arity, remainder, controls, calls⟩,
        store⟩
      (.instruction (.globalSet 0))
      ⟨.running
        ⟨⟨params, localValues, values⟩,
          code, arity, remainder, controls, calls⟩,
        updatedStore⟩ := by
    dsimp [updatedStore]
    rw [← setGlobal_eq_of_canonical store 0 newValue (hcanonical store)]
    exact Step.globalSet hsome
  obtain ⟨rfl, hconfig⟩ :=
    step_deterministic expectedStep wasmStep
  have parts := Config.mk.inj hconfig
  have hexpr := parts.1
  have hstore := parts.2
  simp only at hexpr hstore
  subst e₂
  subst store₂
  imod stateInterp_global_set store ns obs nt
      0 oldValue newValue $$ [$Hσ $Hglobal] with ⟨Hσ, Hglobal⟩
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
    iexact Hglobal

theorem twp_or
    {params localValues values : List Value}
    {lhs rhs : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    WP (.running
      ⟨⟨params, localValues, .i32 (lhs ||| rhs) :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
        [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, .i32 rhs :: .i32 lhs :: values⟩,
        .or :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.or)

theorem twp_f64Load
    {params localValues values : List Value}
    {address offset : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} (word : UInt64)
    (hnowrap : (address + offset).toNat =
      address.toNat + offset.toNat)
    (h1 : ((address + offset) + 1).toNat =
      (address + offset).toNat + 1)
    (h2 : ((address + offset) + 2).toNat =
      (address + offset).toNat + 2)
    (h3 : ((address + offset) + 3).toNat =
      (address + offset).toNat + 3)
    (h4 : ((address + offset) + 4).toNat =
      (address + offset).toNat + 4)
    (h5 : ((address + offset) + 5).toNat =
      (address + offset).toNat + 5)
    (h6 : ((address + offset) + 6).toNat =
      (address + offset).toNat + 6)
    (h7 : ((address + offset) + 7).toNat =
      (address + offset).toNat + 7) :
    let current : ThreadState α :=
      ⟨⟨params, localValues, .i32 address :: values⟩,
        .f64Load offset :: code, arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨⟨params, localValues, .f64 word :: values⟩,
        code, arity, remainder, controls, calls⟩
    pointsTo_u64 0 (address + offset) word -∗
    (pointsTo_u64 0 (address + offset) word -∗
      WP (Expr.running next : Expr α) @ s; E [{ Φ }]) -∗
      WP (Expr.running current : Expr α) @ s; E [{ Φ }] := by
  dsimp only
  iintro Hword Htwp
  iapply twp_lift_step_no_fork rfl
  iintro %store %ns %obs %nt Hσ
  ihave %Hfacts :
      ⌜store.wasm.mem.read64 (address + offset) = word ∧
        (address + offset).toNat + 8 ≤
          store.wasm.mem.pages * 65536⌝ $$ [Hσ Hword]
  · imod stateInterp_pointsTo_u64_facts store ns obs nt
      (address + offset) word h1 h2 h3 h4 h5 h6 h7 $$ [$Hσ $Hword] with %Hfacts
    ipureintro
    exact Hfacts
  obtain ⟨Hread, HinBounds⟩ := Hfacts
  have hbound : address.toNat + offset.toNat + 8 ≤
      store.wasm.mem.pages * 65536 := by
    simpa only [hnowrap] using HinBounds
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducibleNoObs]
    exact ⟨.running
        ⟨⟨params, localValues, .f64 word :: values⟩,
          code, arity, remainder, controls, calls⟩,
      store, [], ⟨rfl, .instruction (.f64Load offset), rfl,
        by simpa [Hread] using
          Step.f64Load (α := α) (address := .i32 address) rfl hbound⟩⟩
  iintro %κ %e₂ %store₂ %forks %Hprim
  rcases Hprim with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst κ
  have expectedStep : Step
      ⟨.running
        ⟨⟨params, localValues, .i32 address :: values⟩,
          .f64Load offset :: code, arity, remainder, controls, calls⟩,
        store⟩
      (.instruction (.f64Load offset))
      ⟨.running
        ⟨⟨params, localValues, .f64 word :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩ := by
    simpa [Hread] using
      (Step.f64Load (α := α) (address := .i32 address) rfl hbound)
  obtain ⟨rfl, hconfig⟩ :=
    step_deterministic expectedStep wasmStep
>>>>>>> origin/main
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
<<<<<<< HEAD
  · icases (stateInterp_eq store ns obs nt).mp $$ Hσ with
        ⟨%σ, %globalσ, %dataSegmentσ, %tableσ, %elementSegmentσ, %exceptionσ,
          Hheap, Hglobals, Hsegments, Htables, HelementSegments, Hexceptions, Hruntime,
          HhostState, %Hfacts⟩
    have hpreserve :
        (prepareCatch tag arguments clause store).2.wasm.mem = store.wasm.mem ∧
        (prepareCatch tag arguments clause store).2.wasm.globals = store.wasm.globals ∧
        (prepareCatch tag arguments clause store).2.wasm.dataSegments =
          store.wasm.dataSegments ∧
        (prepareCatch tag arguments clause store).2.wasm.tables = store.wasm.tables ∧
        (prepareCatch tag arguments clause store).2.wasm.elementSegments =
          store.wasm.elementSegments := by
      rcases clause with _ | _ | _ | _ <;> simp [prepareCatch_eq]
    have hruntime :
        (prepareCatch tag arguments clause store).2.runtime.module =
          store.runtime.module := by
      rcases clause with _ | _ | _ | _ <;> simp [prepareCatch_eq]
    have hhost :
        (prepareCatch tag arguments clause store).2.wasm.host = store.wasm.host := by
      rcases clause with _ | _ | _ | _ <;> simp [prepareCatch_eq]
    have htagIds :
        (prepareCatch tag arguments clause store).2.wasm.tagIds =
          store.wasm.tagIds := by
      rcases clause with _ | _ | _ | _ <;> simp [prepareCatch_eq]
    iapply (stateInterp_eq (prepareCatch tag arguments clause store).2 ns obs nt).mpr
    iexists σ; iexists globalσ; iexists dataSegmentσ; iexists tableσ; iexists elementSegmentσ
    iexists exceptionσ
    simp only [hpreserve.1, hpreserve.2.1, hpreserve.2.2.1, hpreserve.2.2.2.1,
      hpreserve.2.2.2.2, hruntime, hhost, htagIds]
    iframe Hheap Hglobals Hsegments Htables HelementSegments Hexceptions Hruntime HhostState
    ipureintro
    refine ⟨Hfacts.1, Hfacts.2.1, Hfacts.2.2.1, Hfacts.2.2.2.1, Hfacts.2.2.2.2.1,
      Hfacts.2.2.2.2.2.1, ?_⟩
    rcases clause with _ | _ | _ | _ <;> simp [prepareCatch_eq]
    · exact Hfacts.2.2.2.2.2.2
    · exact exceptionHeapAgrees_append Hfacts.2.2.2.2.2.2
    · exact Hfacts.2.2.2.2.2.2
    · exact exceptionHeapAgrees_append Hfacts.2.2.2.2.2.2
  · iexact Hwp

theorem twp_tryTable
    {locals : Locals} {paramArity resultArity arity : Nat}
    {catches : List CatchClause} {body code : Program}
    {paramTypes resultTypes : List ValueType}
    {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    let frame : ControlFrame :=
      { kind := .tryTable catches
        paramArity
        resultArity
        body
        continuation := code
        belowStack := locals.values.drop paramArity }
    WP (.running
      ⟨locals, body, arity, remainder, frame :: controls, calls⟩ :
        Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨locals, .tryTable paramArity resultArity catches body paramTypes resultTypes :: code,
        arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] := by
  dsimp only
  exact twp_pureStep _ _ _ (fun _ => Step.tryTable)


=======
  · iexact Hσ
  · iapply Htwp
    iexact Hword

theorem twp_f64Store
    {params localValues values : List Value}
    {address offset : UInt32} {value : UInt64}
    {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} (oldWord : UInt64)
    (hnowrap : (address + offset).toNat =
      address.toNat + offset.toNat)
    (h1 : ((address + offset) + 1).toNat =
      (address + offset).toNat + 1)
    (h2 : ((address + offset) + 2).toNat =
      (address + offset).toNat + 2)
    (h3 : ((address + offset) + 3).toNat =
      (address + offset).toNat + 3)
    (h4 : ((address + offset) + 4).toNat =
      (address + offset).toNat + 4)
    (h5 : ((address + offset) + 5).toNat =
      (address + offset).toNat + 5)
    (h6 : ((address + offset) + 6).toNat =
      (address + offset).toNat + 6)
    (h7 : ((address + offset) + 7).toNat =
      (address + offset).toNat + 7) :
    let current : ThreadState α :=
      ⟨⟨params, localValues, .f64 value :: .i32 address :: values⟩,
        .f64Store offset :: code, arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨⟨params, localValues, values⟩,
        code, arity, remainder, controls, calls⟩
    pointsTo_u64 0 (address + offset) oldWord -∗
    (pointsTo_u64 0 (address + offset) value -∗
      WP (Expr.running next : Expr α) @ s; E [{ Φ }]) -∗
      WP (Expr.running current : Expr α) @ s; E [{ Φ }] := by
  dsimp only
  iintro Hword Htwp
  iapply twp_lift_step_no_fork rfl
  iintro %store %ns %obs %nt Hσ
  ihave %Hfacts :
      ⌜store.wasm.mem.read64 (address + offset) = oldWord ∧
        (address + offset).toNat + 8 ≤
          store.wasm.mem.pages * 65536⌝ $$ [Hσ Hword]
  · imod stateInterp_pointsTo_u64_facts store ns obs nt
      (address + offset) oldWord h1 h2 h3 h4 h5 h6 h7 $$ [$Hσ $Hword] with %Hfacts
    ipureintro
    exact Hfacts
  have hbound : address.toNat + offset.toNat + 8 ≤
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
            mem := store.wasm.mem.write64 (address + offset) value } },
      [], ⟨rfl, .instruction (.f64Store offset), rfl,
        by simpa only [Wasm.SmallStep.setMemory_eq] using
          Step.f64Store (address := .i32 address) rfl hbound⟩⟩
  iintro %κ %e₂ %store₂ %forks %Hstep
  rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst κ
  have expectedStep : Step
      ⟨.running
        ⟨⟨params, localValues, .f64 value :: .i32 address :: values⟩,
          .f64Store offset :: code, arity, remainder, controls, calls⟩,
        store⟩
      (.instruction (.f64Store offset))
      ⟨.running
        ⟨⟨params, localValues, values⟩,
          code, arity, remainder, controls, calls⟩,
        { store with wasm :=
            { store.wasm with
              mem := store.wasm.mem.write64 (address + offset) value } }⟩ := by
    simpa only [Wasm.SmallStep.setMemory_eq] using
      Step.f64Store (address := .i32 address) rfl hbound
  obtain ⟨rfl, hconfig⟩ :=
    step_deterministic expectedStep wasmStep
  have parts := Config.mk.inj hconfig
  have hexpr := parts.1
  have hstore := parts.2
  simp only at hexpr hstore
  subst e₂
  subst store₂
  imod stateInterp_store64 store ns obs nt
      (address + offset) oldWord value h1 h2 h3 h4 h5 h6 h7 Hfacts.2 $$
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

theorem twp_load64
    {params localValues values : List Value}
    {address offset : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} (word : UInt64)
    (hnowrap : (address + offset).toNat =
      address.toNat + offset.toNat)
    (h1 : ((address + offset) + 1).toNat =
      (address + offset).toNat + 1)
    (h2 : ((address + offset) + 2).toNat =
      (address + offset).toNat + 2)
    (h3 : ((address + offset) + 3).toNat =
      (address + offset).toNat + 3)
    (h4 : ((address + offset) + 4).toNat =
      (address + offset).toNat + 4)
    (h5 : ((address + offset) + 5).toNat =
      (address + offset).toNat + 5)
    (h6 : ((address + offset) + 6).toNat =
      (address + offset).toNat + 6)
    (h7 : ((address + offset) + 7).toNat =
      (address + offset).toNat + 7) :
    let current : ThreadState α :=
      ⟨⟨params, localValues, .i32 address :: values⟩,
        .load64 offset :: code, arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨⟨params, localValues, .i64 word :: values⟩,
        code, arity, remainder, controls, calls⟩
    pointsTo_u64 0 (address + offset) word -∗
    (pointsTo_u64 0 (address + offset) word -∗
      WP (Expr.running next : Expr α) @ s; E [{ Φ }]) -∗
      WP (Expr.running current : Expr α) @ s; E [{ Φ }] := by
  dsimp only
  iintro Hword Htwp
  iapply twp_lift_step_no_fork rfl
  iintro %store %ns %obs %nt Hσ
  ihave %Hfacts :
      ⌜store.wasm.mem.read64 (address + offset) = word ∧
        (address + offset).toNat + 8 ≤
          store.wasm.mem.pages * 65536⌝ $$ [Hσ Hword]
  · imod stateInterp_pointsTo_u64_facts store ns obs nt
      (address + offset) word h1 h2 h3 h4 h5 h6 h7 $$ [$Hσ $Hword] with %Hfacts
    ipureintro
    exact Hfacts
  obtain ⟨Hread, HinBounds⟩ := Hfacts
  have hbound : address.toNat + offset.toNat + 8 ≤
      store.wasm.mem.pages * 65536 := by
    simpa only [hnowrap] using HinBounds
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducibleNoObs]
    exact ⟨.running
        ⟨⟨params, localValues, .i64 word :: values⟩,
          code, arity, remainder, controls, calls⟩,
      store, [], ⟨rfl, .instruction (.load64 offset), rfl,
        by simpa [Hread] using
          Step.load64 (α := α) (address := .i32 address) rfl hbound⟩⟩
  iintro %κ %e₂ %store₂ %forks %Hprim
  rcases Hprim with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst κ
  have expectedStep : Step
      ⟨.running
        ⟨⟨params, localValues, .i32 address :: values⟩,
          .load64 offset :: code, arity, remainder, controls, calls⟩,
        store⟩
      (.instruction (.load64 offset))
      ⟨.running
        ⟨⟨params, localValues, .i64 word :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩ := by
    simpa [Hread] using
      (Step.load64 (α := α) (address := .i32 address) rfl hbound)
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

theorem twp_store64
    {params localValues values : List Value}
    {address offset : UInt32} {value : UInt64}
    {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} (oldWord : UInt64)
    (hnowrap : (address + offset).toNat =
      address.toNat + offset.toNat)
    (h1 : ((address + offset) + 1).toNat =
      (address + offset).toNat + 1)
    (h2 : ((address + offset) + 2).toNat =
      (address + offset).toNat + 2)
    (h3 : ((address + offset) + 3).toNat =
      (address + offset).toNat + 3)
    (h4 : ((address + offset) + 4).toNat =
      (address + offset).toNat + 4)
    (h5 : ((address + offset) + 5).toNat =
      (address + offset).toNat + 5)
    (h6 : ((address + offset) + 6).toNat =
      (address + offset).toNat + 6)
    (h7 : ((address + offset) + 7).toNat =
      (address + offset).toNat + 7) :
    let current : ThreadState α :=
      ⟨⟨params, localValues, .i64 value :: .i32 address :: values⟩,
        .store64 offset :: code, arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨⟨params, localValues, values⟩,
        code, arity, remainder, controls, calls⟩
    pointsTo_u64 0 (address + offset) oldWord -∗
    (pointsTo_u64 0 (address + offset) value -∗
      WP (Expr.running next : Expr α) @ s; E [{ Φ }]) -∗
      WP (Expr.running current : Expr α) @ s; E [{ Φ }] := by
  dsimp only
  iintro Hword Htwp
  iapply twp_lift_step_no_fork rfl
  iintro %store %ns %obs %nt Hσ
  ihave %Hfacts :
      ⌜store.wasm.mem.read64 (address + offset) = oldWord ∧
        (address + offset).toNat + 8 ≤
          store.wasm.mem.pages * 65536⌝ $$ [Hσ Hword]
  · imod stateInterp_pointsTo_u64_facts store ns obs nt
      (address + offset) oldWord h1 h2 h3 h4 h5 h6 h7 $$ [$Hσ $Hword] with %Hfacts
    ipureintro
    exact Hfacts
  have hbound : address.toNat + offset.toNat + 8 ≤
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
            mem := store.wasm.mem.write64 (address + offset) value } },
      [], ⟨rfl, .instruction (.store64 offset), rfl,
        by simpa only [Wasm.SmallStep.setMemory_eq] using
          Step.store64 (α := α) (address := .i32 address) rfl hbound⟩⟩
  iintro %κ %e₂ %store₂ %forks %Hstep
  rcases Hstep with ⟨hforks, kind, hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst κ
  have expectedStep : Step
      ⟨.running
        ⟨⟨params, localValues, .i64 value :: .i32 address :: values⟩,
          .store64 offset :: code, arity, remainder, controls, calls⟩,
        store⟩
      (.instruction (.store64 offset))
      ⟨.running
        ⟨⟨params, localValues, values⟩,
          code, arity, remainder, controls, calls⟩,
        { store with wasm :=
            { store.wasm with
              mem := store.wasm.mem.write64 (address + offset) value } }⟩ := by
    simpa only [Wasm.SmallStep.setMemory_eq] using
      Step.store64 (α := α) (address := .i32 address) rfl hbound
  obtain ⟨rfl, hconfig⟩ :=
    step_deterministic expectedStep wasmStep
  have parts := Config.mk.inj hconfig
  have hexpr := parts.1
  have hstore := parts.2
  simp only at hexpr hstore
  subst e₂
  subst store₂
  imod stateInterp_store64 store ns obs nt
      (address + offset) oldWord value h1 h2 h3 h4 h5 h6 h7 Hfacts.2 $$
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

theorem twp_swapElementsFunc2Prefix
    (ptrA ptrB : UInt32) (oldScratch oldA oldB : UInt64)
    (hroomA : ptrA.toNat + 8 ≤ 4294967296)
    (hroomB : ptrB.toNat + 8 ≤ 4294967296)
    {calls : List CallFrame} :
    (globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u64 0 1048552 oldScratch ∗
      pointsTo_u64 0 ptrA oldA ∗ pointsTo_u64 0 ptrB oldB) ∗
    ((globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u64 0 1048552 oldA ∗
      pointsTo_u64 0 ptrA oldB ∗ pointsTo_u64 0 ptrB oldA) -∗
      WP (.running
        ⟨⟨[.i32 ptrA, .i32 ptrB], [.i32 1048544], []⟩,
          [.ret], 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 ptrA, .i32 ptrB], [.i32 0], []⟩,
        [ .globalGet 0, .const 16, .sub, .localSet 2,
          .localGet 2, .localGet 0, .load64 0, .store64 8,
          .localGet 0, .localGet 1, .load64 0, .store64 0,
          .localGet 1, .localGet 2, .load64 8, .store64 0, .ret ],
        0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  have ha1 : (ptrA + 1).toNat = ptrA.toNat + 1 := by
    simpa using UInt32.add_ofNat_toNat_noWrap ptrA 1 (by omega) (by omega)
  have ha2 : (ptrA + 2).toNat = ptrA.toNat + 2 := by
    simpa using UInt32.add_ofNat_toNat_noWrap ptrA 2 (by omega) (by omega)
  have ha3 : (ptrA + 3).toNat = ptrA.toNat + 3 := by
    simpa using UInt32.add_ofNat_toNat_noWrap ptrA 3 (by omega) (by omega)
  have ha4 : (ptrA + 4).toNat = ptrA.toNat + 4 := by
    simpa using UInt32.add_ofNat_toNat_noWrap ptrA 4 (by omega) (by omega)
  have ha5 : (ptrA + 5).toNat = ptrA.toNat + 5 := by
    simpa using UInt32.add_ofNat_toNat_noWrap ptrA 5 (by omega) (by omega)
  have ha6 : (ptrA + 6).toNat = ptrA.toNat + 6 := by
    simpa using UInt32.add_ofNat_toNat_noWrap ptrA 6 (by omega) (by omega)
  have ha7 : (ptrA + 7).toNat = ptrA.toNat + 7 := by
    simpa using UInt32.add_ofNat_toNat_noWrap ptrA 7 (by omega) (by omega)
  have hb1 : (ptrB + 1).toNat = ptrB.toNat + 1 := by
    simpa using UInt32.add_ofNat_toNat_noWrap ptrB 1 (by omega) (by omega)
  have hb2 : (ptrB + 2).toNat = ptrB.toNat + 2 := by
    simpa using UInt32.add_ofNat_toNat_noWrap ptrB 2 (by omega) (by omega)
  have hb3 : (ptrB + 3).toNat = ptrB.toNat + 3 := by
    simpa using UInt32.add_ofNat_toNat_noWrap ptrB 3 (by omega) (by omega)
  have hb4 : (ptrB + 4).toNat = ptrB.toNat + 4 := by
    simpa using UInt32.add_ofNat_toNat_noWrap ptrB 4 (by omega) (by omega)
  have hb5 : (ptrB + 5).toNat = ptrB.toNat + 5 := by
    simpa using UInt32.add_ofNat_toNat_noWrap ptrB 5 (by omega) (by omega)
  have hb6 : (ptrB + 6).toNat = ptrB.toNat + 6 := by
    simpa using UInt32.add_ofNat_toNat_noWrap ptrB 6 (by omega) (by omega)
  have hb7 : (ptrB + 7).toNat = ptrB.toNat + 7 := by
    simpa using UInt32.add_ofNat_toNat_noWrap ptrB 7 (by omega) (by omega)
  iintro ⟨⟨Hglobal, Hscratch, HA, HB⟩, Hdone⟩
  iapply twp_globalGet $$ Hglobal
  iintro Hglobal
  iapply twp_const
  iapply twp_sub
  iapply twp_localSet rfl
  simp only [UInt32.reduceSub, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub, List.set]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  ihave HA' : pointsTo_u64 0 (ptrA + 0) oldA $$ [HA]
  · rw [UInt32.add_zero]
    iexact HA
  iapply twp_load64 oldA (by simp)
    (by simpa using ha1) (by simpa using ha2) (by simpa using ha3)
    (by simpa using ha4) (by simpa using ha5) (by simpa using ha6)
    (by simpa using ha7) $$ HA'
  iintro HA
  ihave Hscratch' :
      pointsTo_u64 0 ((1048544 : UInt32) + 8) oldScratch $$ [Hscratch]
  · rw [show (1048544 : UInt32) + 8 = 1048552 from rfl]
    iexact Hscratch
  iapply twp_store64 oldScratch rfl rfl rfl rfl rfl rfl rfl rfl $$
    Hscratch'
  iintro Hscratch
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  ihave HB' : pointsTo_u64 0 (ptrB + 0) oldB $$ [HB]
  · rw [UInt32.add_zero]
    iexact HB
  iapply twp_load64 oldB (by simp)
    (by simpa using hb1) (by simpa using hb2) (by simpa using hb3)
    (by simpa using hb4) (by simpa using hb5) (by simpa using hb6)
    (by simpa using hb7) $$ HB'
  iintro HB
  ihave HA' : pointsTo_u64 0 (ptrA + 0) oldA $$ [HA]
  · rw [UInt32.add_zero]
    iexact HA
  iapply twp_store64 oldA (by simp)
    (by simpa using ha1) (by simpa using ha2) (by simpa using ha3)
    (by simpa using ha4) (by simpa using ha5) (by simpa using ha6)
    (by simpa using ha7) $$ HA'
  iintro HA
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  ihave Hscratch' :
      pointsTo_u64 0 ((1048544 : UInt32) + 8) oldA $$ [Hscratch]
  · rw [show (1048544 : UInt32) + 8 = 1048552 from rfl]
    iexact Hscratch
  iapply twp_load64 oldA rfl rfl rfl rfl rfl rfl rfl rfl $$
    Hscratch'
  iintro Hscratch
  ihave HB' : pointsTo_u64 0 (ptrB + 0) oldB $$ [HB]
  · rw [UInt32.add_zero]
    iexact HB
  iapply twp_store64 oldB (by simp)
    (by simpa using hb1) (by simpa using hb2) (by simpa using hb3)
    (by simpa using hb4) (by simpa using hb5) (by simpa using hb6)
    (by simpa using hb7) $$ HB'
  iintro HB
  iapply Hdone
  simp only [UInt32.add_zero, UInt32.reduceAdd]
  iframe

theorem twp_swapElementsFunc2AliasPrefix
    (ptr : UInt32) (oldScratch oldValue : UInt64)
    (hroom : ptr.toNat + 8 ≤ 4294967296)
    {calls : List CallFrame} :
    (globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u64 0 1048552 oldScratch ∗ pointsTo_u64 0 ptr oldValue) ∗
    ((globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u64 0 1048552 oldValue ∗ pointsTo_u64 0 ptr oldValue) -∗
      WP (.running
        ⟨⟨[.i32 ptr, .i32 ptr], [.i32 1048544], []⟩,
          [.ret], 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 ptr, .i32 ptr], [.i32 0], []⟩,
        [ .globalGet 0, .const 16, .sub, .localSet 2,
          .localGet 2, .localGet 0, .load64 0, .store64 8,
          .localGet 0, .localGet 1, .load64 0, .store64 0,
          .localGet 1, .localGet 2, .load64 8, .store64 0, .ret ],
        0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  have h1 : (ptr + 1).toNat = ptr.toNat + 1 := by
    simpa using UInt32.add_ofNat_toNat_noWrap ptr 1 (by omega) (by omega)
  have h2 : (ptr + 2).toNat = ptr.toNat + 2 := by
    simpa using UInt32.add_ofNat_toNat_noWrap ptr 2 (by omega) (by omega)
  have h3 : (ptr + 3).toNat = ptr.toNat + 3 := by
    simpa using UInt32.add_ofNat_toNat_noWrap ptr 3 (by omega) (by omega)
  have h4 : (ptr + 4).toNat = ptr.toNat + 4 := by
    simpa using UInt32.add_ofNat_toNat_noWrap ptr 4 (by omega) (by omega)
  have h5 : (ptr + 5).toNat = ptr.toNat + 5 := by
    simpa using UInt32.add_ofNat_toNat_noWrap ptr 5 (by omega) (by omega)
  have h6 : (ptr + 6).toNat = ptr.toNat + 6 := by
    simpa using UInt32.add_ofNat_toNat_noWrap ptr 6 (by omega) (by omega)
  have h7 : (ptr + 7).toNat = ptr.toNat + 7 := by
    simpa using UInt32.add_ofNat_toNat_noWrap ptr 7 (by omega) (by omega)
  iintro ⟨⟨Hglobal, Hscratch, Hcell⟩, Hdone⟩
  iapply twp_globalGet $$ Hglobal
  iintro Hglobal
  iapply twp_const
  iapply twp_sub
  iapply twp_localSet rfl
  simp only [UInt32.reduceSub, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub, List.set]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  ihave Hcell' : pointsTo_u64 0 (ptr + 0) oldValue $$ [Hcell]
  · rw [UInt32.add_zero]
    iexact Hcell
  iapply twp_load64 oldValue (by simp)
    (by simpa using h1) (by simpa using h2) (by simpa using h3)
    (by simpa using h4) (by simpa using h5) (by simpa using h6)
    (by simpa using h7) $$ Hcell'
  iintro Hcell
  ihave Hscratch' :
      pointsTo_u64 0 ((1048544 : UInt32) + 8) oldScratch $$ [Hscratch]
  · rw [show (1048544 : UInt32) + 8 = 1048552 from rfl]
    iexact Hscratch
  iapply twp_store64 oldScratch rfl rfl rfl rfl rfl rfl rfl rfl $$
    Hscratch'
  iintro Hscratch
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  ihave Hcell' : pointsTo_u64 0 (ptr + 0) oldValue $$ [Hcell]
  · rw [UInt32.add_zero]
    iexact Hcell
  iapply twp_load64 oldValue (by simp)
    (by simpa using h1) (by simpa using h2) (by simpa using h3)
    (by simpa using h4) (by simpa using h5) (by simpa using h6)
    (by simpa using h7) $$ Hcell'
  iintro Hcell
  ihave Hcell' : pointsTo_u64 0 (ptr + 0) oldValue $$ [Hcell]
  · rw [UInt32.add_zero]
    iexact Hcell
  iapply twp_store64 oldValue (by simp)
    (by simpa using h1) (by simpa using h2) (by simpa using h3)
    (by simpa using h4) (by simpa using h5) (by simpa using h6)
    (by simpa using h7) $$ Hcell'
  iintro Hcell
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  ihave Hscratch' :
      pointsTo_u64 0 ((1048544 : UInt32) + 8) oldValue $$ [Hscratch]
  · rw [show (1048544 : UInt32) + 8 = 1048552 from rfl]
    iexact Hscratch
  iapply twp_load64 oldValue rfl rfl rfl rfl rfl rfl rfl rfl $$
    Hscratch'
  iintro Hscratch
  ihave Hcell' : pointsTo_u64 0 (ptr + 0) oldValue $$ [Hcell]
  · rw [UInt32.add_zero]
    iexact Hcell
  iapply twp_store64 oldValue (by simp)
    (by simpa using h1) (by simpa using h2) (by simpa using h3)
    (by simpa using h4) (by simpa using h5) (by simpa using h6)
    (by simpa using h7) $$ Hcell'
  iintro Hcell
  iapply Hdone
  simp only [UInt32.add_zero, UInt32.reduceAdd]
  iframe

theorem twp_swapElementsFunc2
    (ptrA ptrB : UInt32) (oldScratch oldA oldB : UInt64)
    (hroomA : ptrA.toNat + 8 ≤ 4294967296)
    (hroomB : ptrB.toNat + 8 ≤ 4294967296) :
    globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u64 0 1048552 oldScratch ∗
      pointsTo_u64 0 ptrA oldA ∗ pointsTo_u64 0 ptrB oldB ⊢
    WP (.running
      ⟨⟨[.i32 ptrA, .i32 ptrB], [.i32 0], []⟩,
        [ .globalGet 0, .const 16, .sub, .localSet 2,
          .localGet 2, .localGet 0, .load64 0, .store64 8,
          .localGet 0, .localGet 1, .load64 0, .store64 0,
          .localGet 1, .localGet 2, .load64 8, .store64 0, .ret ],
        0, [], [], []⟩ : Expr α) @ s; E
      [{ result, ⌜result = []⌝ ∗
        globalPointsToAt 0 0 (.i32 1048560) ∗
        pointsTo_u64 0 1048552 oldA ∗
        pointsTo_u64 0 ptrA oldB ∗ pointsTo_u64 0 ptrB oldA }] := by
  iintro Hresources
  iapply twp_swapElementsFunc2Prefix ptrA ptrB oldScratch oldA oldB
    hroomA hroomB (calls := [])
  isplitl [Hresources]
  · iexact Hresources
  · iintro Hresources
    iapply twp_returnFromFunction
    simp only [List.take, List.nil_append]
    iapply twp.value rfl
    isplitr
    · ipureintro
      rfl
    · iexact Hresources

theorem twp_swapElementsFunc2Alias
    (ptr : UInt32) (oldScratch oldValue : UInt64)
    (hroom : ptr.toNat + 8 ≤ 4294967296) :
    globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u64 0 1048552 oldScratch ∗ pointsTo_u64 0 ptr oldValue ⊢
    WP (.running
      ⟨⟨[.i32 ptr, .i32 ptr], [.i32 0], []⟩,
        [ .globalGet 0, .const 16, .sub, .localSet 2,
          .localGet 2, .localGet 0, .load64 0, .store64 8,
          .localGet 0, .localGet 1, .load64 0, .store64 0,
          .localGet 1, .localGet 2, .load64 8, .store64 0, .ret ],
        0, [], [], []⟩ : Expr α) @ s; E
      [{ result, ⌜result = []⌝ ∗
        globalPointsToAt 0 0 (.i32 1048560) ∗
        pointsTo_u64 0 1048552 oldValue ∗
        pointsTo_u64 0 ptr oldValue }] := by
  iintro Hresources
  iapply twp_swapElementsFunc2AliasPrefix ptr oldScratch oldValue hroom
    (calls := [])
  isplitl [Hresources]
  · iexact Hresources
  · iintro Hresources
    iapply twp_returnFromFunction
    simp only [List.take, List.nil_append]
    iapply twp.value rfl
    isplitr
    · ipureintro
      rfl
    · iexact Hresources

theorem twp_swapElementsFunc3
    (oldPtr oldLen ptr len : UInt32) :
    pointsTo_u32 0 1048568 oldPtr ∗ pointsTo_u32 0 1048572 oldLen ⊢
    WP (.running
      ⟨⟨[.i32 1048568, .i32 ptr, .i32 len, .i32 1048652], [], []⟩,
        [ .localGet 0, .localGet 2, .store32 4,
          .localGet 0, .localGet 1, .store32 0, .ret ],
        0, [], [], []⟩ : Expr α) @ s; E
      [{ result, ⌜result = []⌝ ∗
        pointsTo_u32 0 1048568 ptr ∗ pointsTo_u32 0 1048572 len }] := by
  iintro ⟨Hptr, Hlen⟩
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  ihave Hlen' :
      pointsTo_u32 0 ((1048568 : UInt32) + 4) oldLen $$ [Hlen]
  · rw [show (1048568 : UInt32) + 4 = 1048572 from rfl]
    iexact Hlen
  iapply twp_store32 oldLen rfl rfl rfl rfl $$ Hlen'
  iintro Hlen
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  ihave Hptr' :
      pointsTo_u32 0 ((1048568 : UInt32) + 0) oldPtr $$ [Hptr]
  · rw [UInt32.add_zero]
    iexact Hptr
  iapply twp_store32 oldPtr rfl rfl rfl rfl $$ Hptr'
  iintro Hptr
  iapply twp_returnFromFunction
  simp only [List.take, List.nil_append]
  iapply twp.value rfl
  isplitr
  · ipureintro
    rfl
  · isplitl [Hptr]
    · rw [UInt32.add_zero]
      iexact Hptr
    · rw [← show (1048568 : UInt32) + 4 = 1048572 from rfl]
      iexact Hlen

theorem twp_subI64
    {params localValues values : List Value}
    {lhs rhs : UInt64} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    WP (.running
      ⟨⟨params, localValues, .i64 (lhs - rhs) :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
        [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, .i64 rhs :: .i64 lhs :: values⟩,
        .subI64 :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.subI64)

theorem twp_constI64
    {params localValues values : List Value}
    {value : UInt64} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    WP (.running
      ⟨⟨params, localValues, .i64 value :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
        [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, values⟩,
        .constI64 value :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.constI64)

theorem twp_orI64
    {params localValues values : List Value}
    {lhs rhs : UInt64} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    WP (.running
      ⟨⟨params, localValues, .i64 (lhs ||| rhs) :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
        [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, .i64 rhs :: .i64 lhs :: values⟩,
        .orI64 :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.orI64)

theorem twp_shlI64
    {params localValues values : List Value}
    {lhs rhs : UInt64} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    WP (.running
      ⟨⟨params, localValues, .i64 (lhs <<< (rhs % 64)) :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
        [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, .i64 rhs :: .i64 lhs :: values⟩,
        .shlI64 :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.shlI64)

theorem twp_shrUI64
    {params localValues values : List Value}
    {lhs rhs : UInt64} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    WP (.running
      ⟨⟨params, localValues, .i64 (lhs >>> (rhs % 64)) :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
        [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, .i64 rhs :: .i64 lhs :: values⟩,
        .shrUI64 :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.shrUI64)

theorem twp_ctzI64
    {params localValues values : List Value}
    {value : UInt64} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    WP (.running
      ⟨⟨params, localValues,
          .i64 (UInt64.ofNat (ctz64 64 value)) :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
        [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, .i64 value :: values⟩,
        .ctzI64 :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.ctzI64)

theorem twp_wrapI64
    {params localValues values : List Value}
    {value : UInt64} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    WP (.running
      ⟨⟨params, localValues,
          .i32 (UInt32.ofNat (value.toNat % 2 ^ 32)) :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
        [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, .i64 value :: values⟩,
        .wrapI64 :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.wrapI64)

theorem twp_extendUI32
    {params localValues values : List Value}
    {value : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    WP (.running
      ⟨⟨params, localValues, .i64 (UInt64.ofNat value.toNat) :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
        [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, .i32 value :: values⟩,
        .extendUI32 :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.extendUI32)

theorem twp_eqI64
    {params localValues values : List Value}
    {lhs rhs : UInt64} {result : UInt32}
    {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    (hresult : result = if lhs = rhs then 1 else 0) :
    WP (.running
      ⟨⟨params, localValues, .i32 result :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
        [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, .i64 rhs :: .i64 lhs :: values⟩,
        .eqI64 :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.eqI64 hresult)

theorem twp_neI64
    {params localValues values : List Value}
    {lhs rhs : UInt64} {result : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    (hresult : result = if lhs ≠ rhs then 1 else 0) :
    WP (.running
      ⟨⟨params, localValues, .i32 result :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
        [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, .i64 rhs :: .i64 lhs :: values⟩,
        .neI64 :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.neI64 hresult)

theorem twp_gtUI64
    {params localValues values : List Value}
    {lhs rhs : UInt64} {result : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    (hresult : result = if lhs > rhs then 1 else 0) :
    WP (.running
      ⟨⟨params, localValues, .i32 result :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
        [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, .i64 rhs :: .i64 lhs :: values⟩,
        .gtUI64 :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
      [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.gtUI64 hresult)
>>>>>>> origin/main

end Wasm.SmallStep
