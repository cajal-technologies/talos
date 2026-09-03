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
variable {GF : BundledGFunctors}
variable [ι : @IrisGS_gen hlc Expr Val State Obs Λ GF]
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

set_option hygiene false in
/-- Enter the total Iris lifting rule and name its physical-step context. -/
macro "wasm_twp_begin" : tactic =>
  `(tactic|
    (iapply twp_lift_step_no_fork
        (@TerminalView.running_not_val α Terminal view _)
     iintro %store %ns %obs %nt Hσ))

section terminalGeneric

variable [WasmSmallStepGS hlc α]
variable {Terminal : Type}
variable [view : TerminalView α Terminal]
local instance (priority := high) activeTerminalLanguage :
    Language (Expr α) (MachineStore α) StepKind Terminal :=
  TerminalView.canonicalLanguage
local instance (priority := high) activeTerminalIrisGS :
    @IrisGS_gen hlc (Expr α) Terminal (MachineStore α) StepKind
      activeTerminalLanguage (WasmHeapGF α) :=
  { numLatersPerStep _ := 0
    forkPost _ := iprop(True)
    stateInterp_mono _ _ _ _ := by iintro $ }
variable {s : Stuckness} {E : CoPset}
variable {Φ : Terminal → IProp (WasmHeapGF α)}

/-- Generic total lifting rule for a store-preserving deterministic Wasm
step. Unlike `wp_pureStep`, its continuation is not guarded by a later. -/
theorem twp_pureStep
    (kind : StepKind) (current next : ThreadState α)
    (hstep : ∀ store : MachineStore α,
      Step ⟨.running current, store⟩ kind ⟨.running next, store⟩) :
    WP (Expr.running next : Expr α) @ s; E [{ Φ }] ⊢
      WP (Expr.running current : Expr α) @ s; E [{ Φ }] := by
  iintro Htwp
  wasm_twp_begin
  wasm_twp_step hstep store =>
    wasm_twp_frame
      iexact Htwp

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
  wasm_twp_begin
  wasm_twp_step Step.finish =>
    wasm_twp_frame
      iexact Htwp

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
  wasm_twp_begin
  wasm_twp_step Step.returnFromFunction =>
    wasm_twp_frame
      iexact Htwp

/-- Take a terminal machine step and expose its result as a total Iris value. -/
macro "wasm_twp_terminal_value " step:pmTerm : tactic =>
  `(tactic|
    (iapply $step
     iapply twp.value rfl))

/-! ## Generating total pure rules

`wasm_twp_pure_rule` is the total-WP counterpart of `wasm_wp_pure_rule`.
It preserves the public binder names while factoring the common
instruction/operand-stack transition shape.
-/
set_option hygiene false in
macro "wasm_twp_pure_rule " name:ident binders:bracketedBinder* " : "
    instruction:term ", " before:term " => " after:term " := "
    step:term : command => do
  let isValueBinder (b : Lean.TSyntax ``Lean.Parser.Term.bracketedBinder) : Bool :=
    b.raw.getKind == ``Lean.Parser.Term.implicitBinder
  let isSideCondition (b : Lean.TSyntax ``Lean.Parser.Term.bracketedBinder) : Bool :=
    b.raw.getKind == ``Lean.Parser.Term.explicitBinder
  for b in binders do
    unless isValueBinder b || isSideCondition b do
      Lean.Macro.throwErrorAt b
        "wasm_twp_pure_rule takes implicit value binders and explicit side conditions"
  let valueBinders := binders.filter isValueBinder
  let sideConditions := binders.filter isSideCondition
  `(command|
    theorem $name:ident
        {params localValues values : List Value}
        $valueBinders:bracketedBinder*
        {code : Program} {arity : Nat}
        {remainder : List Value} {controls : List ControlFrame}
        {calls : List CallFrame}
        $sideConditions:bracketedBinder* :
        WP (.running
          ⟨⟨params, localValues, $after⟩,
            code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
        WP (.running
          ⟨⟨params, localValues, $before⟩,
            $instruction :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E
          [{ Φ }] :=
      twp_pureStep _ _ _ (fun _ => $step))

wasm_twp_pure_rule twp_remU {dividend divisor : UInt32}
    (hdivisor : divisor ≠ 0) :
  .remU, .i32 divisor :: .i32 dividend :: values =>
    .i32 (dividend % divisor) :: values := Step.remU hdivisor

wasm_twp_pure_rule twp_eqz {value result : UInt32}
    (hresult : result = if value = 0 then 1 else 0) :
  .eqz, .i32 value :: values => .i32 result :: values := Step.eqz hresult

wasm_twp_pure_rule twp_const {value : UInt32} :
  .const value, values => .i32 value :: values := Step.const

wasm_twp_pure_rule twp_add {lhs rhs : UInt32} :
  .add, .i32 rhs :: .i32 lhs :: values => .i32 (rhs + lhs) :: values := Step.add

wasm_twp_pure_rule twp_sub {lhs rhs : UInt32} :
  .sub, .i32 rhs :: .i32 lhs :: values => .i32 (lhs - rhs) :: values := Step.sub

wasm_twp_pure_rule twp_mul {lhs rhs : UInt32} :
  .mul, .i32 rhs :: .i32 lhs :: values => .i32 (rhs * lhs) :: values := Step.mul

wasm_twp_pure_rule twp_shl {lhs rhs : UInt32} :
  .shl, .i32 rhs :: .i32 lhs :: values =>
    .i32 (lhs <<< (rhs % 32)) :: values := Step.shl

wasm_twp_pure_rule twp_shrU {lhs rhs : UInt32} :
  .shrU, .i32 rhs :: .i32 lhs :: values =>
    .i32 (lhs >>> (rhs % 32)) :: values := Step.shrU

wasm_twp_pure_rule twp_ltU {lhs rhs result : UInt32}
    (hresult : result = if lhs < rhs then 1 else 0) :
  .ltU, .i32 rhs :: .i32 lhs :: values => .i32 result :: values := Step.ltU hresult

wasm_twp_pure_rule twp_eq {lhs rhs result : UInt32}
    (hresult : result = if lhs = rhs then 1 else 0) :
  .eq, .i32 rhs :: .i32 lhs :: values => .i32 result :: values := Step.eq hresult

wasm_twp_pure_rule twp_geU {lhs rhs result : UInt32}
    (hresult : result = if lhs ≥ rhs then 1 else 0) :
  .geU, .i32 rhs :: .i32 lhs :: values => .i32 result :: values := Step.geU hresult

wasm_twp_pure_rule twp_leU {lhs rhs result : UInt32}
    (hresult : result = if lhs ≤ rhs then 1 else 0) :
  .leU, .i32 rhs :: .i32 lhs :: values => .i32 result :: values := Step.leU hresult

wasm_twp_pure_rule twp_gtU {lhs rhs result : UInt32}
    (hresult : result = if lhs > rhs then 1 else 0) :
  .gtU, .i32 rhs :: .i32 lhs :: values => .i32 result :: values := Step.gtU hresult

wasm_twp_pure_rule twp_select
    {first second selected : Value} {condition : UInt32}
    (h : selected = if condition ≠ 0 then first else second) :
  .select, .i32 condition :: second :: first :: values => selected :: values := Step.select h

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

theorem twp_localTee
    {params localValues values : List Value}
    {index : Nat} {value : Value} {locals' : Locals}
    {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    (hset : (⟨params, localValues, value :: values⟩ : Locals).set? index value =
      some locals') :
    let current : ThreadState α :=
      ⟨⟨params, localValues, value :: values⟩, .localTee index :: code,
        arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨locals', code, arity, remainder, controls, calls⟩
    WP (Expr.running next : Expr α) @ s; E [{ Φ }] ⊢
      WP (Expr.running current : Expr α) @ s; E [{ Φ }] := by
  dsimp only
  exact twp_pureStep _ _ _ (fun _ => Step.localTee hset)

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
  wasm_twp_begin
  wasm_runtime_module_agree obs, callerId, runtimeModule $$ [$Hσ $Hruntime]
  have himports' :
      ¬functionIndex < store.runtime.currentModule.imports.length := by
    simpa only [Hmodule] using himports
  have hfn' : store.runtime.currentModule.funcs[
      functionIndex - store.runtime.currentModule.imports.length]? = some fn := by
    simpa only [Hmodule] using hfn
  simp only [runtimeModuleOwn]
  icases Hruntime with ⟨HruntimeElem, HinstanceOwn⟩
  wasm_current_instance_agree obs, callerId $$ [$Hσ $HinstanceOwn]
  have hsame : callerId = store.runtime.entry := Hentry.symm
  wasm_twp_step (Step.call (α := α) himports' hfn') =>
    wasm_twp_frame
      rw [← hsame]
      iapply Htwp
      isplitl_exact HruntimeElem
      · iexact HinstanceOwn

/-- Total execution of an imported host function.  The resource-transfer
premises are shared with `wp_callHost`; only the recursive continuations lose
their later guards. -/
theorem twp_callHost
    (runtimeModule : Module) (functionIndex : Nat) (imp : ImportDecl)
    (hostFn : HostFn α)
    (himports : functionIndex < runtimeModule.imports.length)
    (himp : runtimeModule.imports[functionIndex] = imp)
    (hostEnv : HostEnv α)
    (hfuncs : hostEnv.funcs[functionIndex]? = some hostFn)
    {params localValues values : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (P : IProp (WasmHeapGF α))
    (QRet : List Value → IProp (WasmHeapGF α))
    (QTrap : IProp (WasmHeapGF α))
    (QThrow : IProp (WasmHeapGF α))
    (callerId : ModuleInstanceId)
    (hRetTransfer : ∀ (store : MachineStore α) (ns : Nat)
        (obs : List StepKind) (nt : Nat),
        store.runtime.currentModule = runtimeModule →
        ∀ results postWasm,
        hostFn.invoke store.wasm (values.take imp.params.length).reverse =
          .Return results postWasm →
        P ∗ stateInterp (GF := WasmHeapGF α) store ns obs nt ==∗
        QRet results ∗
        stateInterp (GF := WasmHeapGF α)
          { store with wasm := postWasm } ns obs nt)
    (hTrapTransfer : ∀ (store : MachineStore α) (ns : Nat)
        (obs : List StepKind) (nt : Nat),
        store.runtime.currentModule = runtimeModule →
        ∀ postWasm msg,
        hostFn.invoke store.wasm (values.take imp.params.length).reverse =
          .Trap postWasm msg →
        P ∗ stateInterp (GF := WasmHeapGF α) store ns obs nt ==∗
        QTrap ∗
        stateInterp (GF := WasmHeapGF α)
          { store with wasm := postWasm } ns obs nt)
    (hThrowTransfer : ∀ (store : MachineStore α) (ns : Nat)
        (obs : List StepKind) (nt : Nat),
        store.runtime.currentModule = runtimeModule →
        ∀ postWasm tag xs,
        hostFn.invoke store.wasm (values.take imp.params.length).reverse =
          .Throw postWasm tag xs →
        P ∗ stateInterp (GF := WasmHeapGF α) store ns obs nt ==∗
        QThrow ∗
        stateInterp (GF := WasmHeapGF α)
          { store with wasm := postWasm } ns obs nt) :
    let current : ThreadState α :=
      ⟨⟨params, localValues, values⟩, .call functionIndex :: code,
        arity, remainder, controls, calls⟩
    P -∗
    runtimeModuleOwn callerId runtimeModule -∗
    hostEnvOwn callerId.id hostEnv -∗
    (∀ preWasm results postWasm
          (_h : hostFn.invoke preWasm
            (values.take imp.params.length).reverse =
            .Return results postWasm),
        QRet results ∗ runtimeModuleOwn callerId runtimeModule -∗
        WP (Expr.running
            ⟨⟨params, localValues,
                results.take imp.results.length ++
                  values.drop imp.params.length⟩,
              code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) -∗
    (∀ preWasm postWasm msg
          (_h : hostFn.invoke preWasm
            (values.take imp.params.length).reverse =
            .Trap postWasm msg),
        QTrap -∗
        WP (Expr.trapped (.host msg) : Expr α) @ s; E [{ Φ }]) -∗
    (∀ preWasm postWasm tag xs
          (_h : hostFn.invoke preWasm
            (values.take imp.params.length).reverse =
            .Throw postWasm tag xs),
        QThrow -∗
        WP (Expr.running
            ⟨⟨params, localValues, values.drop imp.params.length⟩,
              [], arity, remainder,
              [{ kind := .throwing tag xs
                 paramArity := 0
                 resultArity := 0
                 body := []
                 continuation := []
                 belowStack := [] }] ++ controls,
              calls⟩ : Expr α)
          @ s; E [{ Φ }]) -∗
    WP (Expr.running current : Expr α) @ s; E [{ Φ }] := by
  dsimp only
  iintro HP Hruntime Henv HwpRet HwpTrap HwpThrow
  wasm_twp_begin
  wasm_runtime_module_agree obs, callerId, runtimeModule $$ [$Hσ $Hruntime]
  simp only [runtimeModuleOwn]
  icases Hruntime with ⟨HruntimeElem, HinstanceOwn⟩
  have himports' : functionIndex <
      store.runtime.currentModule.imports.length := by
    simpa only [Hmodule] using himports
  have himp' : store.runtime.currentModule.imports[functionIndex] = imp := by
    simpa only [Hmodule] using himp
  ihave_pure Hhost : ⌜store.runtime.currentHost = hostEnv⌝ using
    stateInterp_hostEnv store ns obs nt callerId.id hostEnv $$
      [Hσ HinstanceOwn Henv]
  have hhost' : store.runtime.currentHost.funcs[functionIndex]? =
      some hostFn := by
    rw [Hhost]
    exact hfuncs
  match h : hostFn.invoke store.wasm
      (values.take imp.params.length).reverse with
  | .Return results newWasm =>
    wasm_twp_step
        (Step.callHostReturn (α := α) himports' himp' hhost' h) =>
      imod hRetTransfer store ns obs nt Hmodule results newWasm h $$
        [$HP $Hσ] with ⟨HQ, Hσ⟩
      wasm_twp_frame
        ispecialize HwpRet $$ %(store.wasm) %results %newWasm %h
        iapply HwpRet
        isplitl_exact HQ
        · isplitl [HruntimeElem]
          · iexact HruntimeElem
          · iexact HinstanceOwn
  | .Trap newWasm msg =>
    iclear HinstanceOwn HruntimeElem
    wasm_twp_step (Step.callHostTrap (α := α) himports' himp' hhost' h) =>
      imod hTrapTransfer store ns obs nt Hmodule newWasm msg h $$
        [$HP $Hσ] with ⟨HQ, Hσ⟩
      wasm_twp_frame
        ispecialize HwpTrap $$ %(store.wasm) %newWasm %msg %h
        iapply HwpTrap
        iexact HQ
  | .Throw newWasm tag xs =>
    iclear HinstanceOwn HruntimeElem
    wasm_twp_step (Step.callHostThrow (α := α) himports' himp' hhost' h) =>
      imod hThrowTransfer store ns obs nt Hmodule newWasm tag xs h $$
        [$HP $Hσ] with ⟨HQ, Hσ⟩
      wasm_twp_frame
        ispecialize HwpThrow $$ %(store.wasm) %newWasm %tag %xs %h
        iapply HwpThrow
        iexact HQ

theorem twp_returnFromCallFallthrough
    {calleeLocals callerLocals : Locals}
    {callerCode : Program}
    {calleeArity callerArity : Nat}
    {calleeRemainder callerRemainder : List Value}
    {callerControls : List ControlFrame}
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
      ⟨calleeLocals, [], calleeArity, calleeRemainder, [], caller :: calls⟩
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
  wasm_twp_begin
  simp only [runtimeModuleOwn]
  icases Hruntime with ⟨HruntimeElem, HinstanceOwn⟩
  wasm_current_instance_agree obs, returningInstance $$ [$Hσ $HinstanceOwn]
  have hsame : returningInstance = store.runtime.entry := Hentry.symm
  wasm_twp_step (Step.returnFromCallFallthrough (α := α) hsame) =>
    wasm_twp_frame
      simp only [resumeCaller]
      iapply Hwp
      isplitl_exact HruntimeElem
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
  wasm_twp_begin
  simp only [runtimeModuleOwn]
  icases Hruntime with ⟨HruntimeElem, HinstanceOwn⟩
  wasm_current_instance_agree obs, returningInstance $$ [$Hσ $HinstanceOwn]
  have hsame : returningInstance = store.runtime.entry := Hentry.symm
  wasm_twp_step (Step.returnFromCallExplicit (α := α) hsame) =>
    wasm_twp_frame
      simp only [resumeCaller]
      iapply Hwp
      isplitl_exact HruntimeElem
      · iexact HinstanceOwn

/-- Return totally from a callee and bind the restored runtime ownership. -/
macro "wasm_twp_return_from_call " runtime:ident : tactic => do
  let spec ← `(specPat| $runtime:ident)
  let intro ← `(introPat| $runtime:ident)
  `(tactic|
    (iapply twp_returnFromCallExplicit $$ $spec
     iintro $intro))

theorem twp_memorySize
    {params localValues values : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (runtimeModule : Module) (instanceId : ModuleInstanceId)
    (Hwp : ∀ pages : Nat,
        runtimeModuleOwn instanceId runtimeModule -∗
        WP (.running ⟨⟨params, localValues,
            sizeValue runtimeModule.memIs64 pages :: values⟩,
          code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) :
    runtimeModuleOwn instanceId runtimeModule -∗
    WP (.running ⟨⟨params, localValues, values⟩,
        .memorySize :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro Hruntime
  wasm_twp_begin
  wasm_runtime_module_agree obs, instanceId, runtimeModule $$ [$Hσ $Hruntime]
  wasm_twp_step Step.memorySize =>
    wasm_twp_frame
      simp only [Hmodule]
      iapply Hwp store.wasm.mem.pages
      iexact Hruntime

/-- Total `memory.size` rule that returns an exact persistent snapshot of the
observed physical page count while preserving an arbitrary caller frame. -/
theorem twp_memorySize_tracked
    {params localValues values : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {P : IProp (WasmHeapGF α)}
    (runtimeModule : Module) (instanceId : ModuleInstanceId)
    (Hwp : ∀ pages : Nat,
        P -∗
        runtimeModuleOwn instanceId runtimeModule -∗
        memoryPagesOwn pages -∗
        WP (.running ⟨⟨params, localValues,
            sizeValue runtimeModule.memIs64 pages :: values⟩,
          code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) :
    P -∗
    runtimeModuleOwn instanceId runtimeModule -∗
    WP (.running ⟨⟨params, localValues, values⟩,
        .memorySize :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro HP Hruntime
  wasm_twp_begin
  wasm_runtime_module_agree obs, instanceId, runtimeModule $$ [$Hσ $Hruntime]
  icombine HP Hruntime as Hclient
  icombine Hσ Hclient as Hinput
  imod (stateInterp_memoryPages_snapshot_frame store ns obs nt
      (P := iprop(P ∗ runtimeModuleOwn instanceId runtimeModule))) $$
      Hinput with Hout
  icases Hout with ⟨⟨Hσ, #Hpages⟩, HP, Hruntime'⟩
  ihave Hcont := Hwp store.wasm.mem.pages
  ispecialize Hcont $$ HP Hruntime' Hpages
  wasm_twp_step Step.memorySize =>
    wasm_twp_frame
      simp only [Hmodule]
      iexact Hcont

/-- Total `memory.grow` rule. The continuation handles both the physical
success result (the previous page count) and the standard failure sentinel. -/
theorem twp_memoryGrow
    {params localValues values : List Value}
    {delta : UInt32}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (runtimeModule : Module) (instanceId : ModuleInstanceId)
    (Hwp : ∀ result : UInt32,
        runtimeModuleOwn instanceId runtimeModule -∗
        WP (.running ⟨⟨params, localValues, .i32 result :: values⟩,
          code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) :
    runtimeModuleOwn instanceId runtimeModule -∗
    WP (.running ⟨⟨params, localValues, .i32 delta :: values⟩,
        .memoryGrow :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro Hruntime
  wasm_twp_begin
  cases hg : store.wasm.mem.grow delta
      (store.wasm.memoryCap store.runtime.currentModule 0) with
  | none =>
    wasm_twp_step Step.memoryGrowFailure hg =>
      wasm_twp_frame
        iapply Hwp (0xFFFFFFFF : UInt32)
        iexact Hruntime
  | some grown =>
    obtain ⟨memory, previousPages⟩ := grown
    wasm_twp_step (by
        simpa only [Wasm.SmallStep.setMemory_eq] using Step.memoryGrowSuccess hg)
        =>
      imod (stateInterp_memoryGrow store ns obs nt delta
          (store.wasm.memoryCap store.runtime.currentModule 0)
          memory previousPages hg) $$ Hσ with Hσ
      wasm_twp_frame
        iapply Hwp previousPages.toUInt32
        iexact Hruntime

/-- Tracked total `memory.grow` rule.  A snapshot previously issued by
`memory.size` is threaded through an arbitrary caller frame.  Both outcomes
relate that measurement to the actual pre-grow count; success additionally
returns an exact new-page snapshot and the equations established by
`Mem.grow`. -/
theorem twp_memoryGrow_tracked
    {params localValues values : List Value}
    {delta : UInt32}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {P : IProp (WasmHeapGF α)}
    (runtimeModule : Module) (instanceId : ModuleInstanceId)
    (measuredPages : Nat)
    (Hfailure : ∀ pages : Nat, measuredPages ≤ pages →
        P -∗
        runtimeModuleOwn instanceId runtimeModule -∗
        memoryPagesOwn measuredPages -∗
        WP (.running ⟨⟨params, localValues,
            .i32 (0xFFFFFFFF : UInt32) :: values⟩,
          code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }])
    (Hsuccess : ∀ oldPages previousPages newPages : Nat,
        previousPages = oldPages ∧
          newPages = previousPages + delta.toNat →
        measuredPages ≤ oldPages →
        P -∗
        runtimeModuleOwn instanceId runtimeModule -∗
        memoryPagesOwn measuredPages -∗
        memoryPagesOwn newPages -∗
        WP (.running ⟨⟨params, localValues,
            .i32 previousPages.toUInt32 :: values⟩,
          code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) :
    P -∗
    runtimeModuleOwn instanceId runtimeModule -∗
    memoryPagesOwn measuredPages -∗
    WP (.running ⟨⟨params, localValues, .i32 delta :: values⟩,
        .memoryGrow :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro HP Hruntime HmeasuredPages
  wasm_twp_begin
  ihave %hmeasuredPages : ⌜measuredPages ≤ store.wasm.mem.pages⌝ $$
      [Hσ HmeasuredPages]
  · imod (stateInterp_memoryPages_agree store ns obs nt measuredPages) $$
        [$Hσ $HmeasuredPages] with ⟨_, _, %hle⟩
    ipureexact hle
  cases hg : store.wasm.mem.grow delta
      (store.wasm.memoryCap store.runtime.currentModule 0) with
  | none =>
    ihave Hcont := Hfailure store.wasm.mem.pages hmeasuredPages
    ispecialize Hcont $$ HP Hruntime HmeasuredPages
    wasm_twp_step Step.memoryGrowFailure hg =>
      wasm_twp_frame
        iexact Hcont
  | some grown =>
    obtain ⟨memory, previousPages⟩ := grown
    have hfacts : previousPages = store.wasm.mem.pages ∧
        memory.pages = previousPages + delta.toNat := by
      simp only [Mem.grow] at hg
      split at hg
      · have hinj := Prod.mk.inj (Option.some.inj hg)
        exact ⟨hinj.2.symm,
          (congrArg (fun result : Mem => result.pages) hinj.1).symm.trans
            (by rw [hinj.2])⟩
      · contradiction
    ihave HcontNew := Hsuccess store.wasm.mem.pages previousPages memory.pages
      hfacts hmeasuredPages
    ispecialize HcontNew $$ HP Hruntime HmeasuredPages
    wasm_twp_step (by
        simpa only [Wasm.SmallStep.setMemory_eq] using Step.memoryGrowSuccess hg)
        =>
      icombine Hσ HcontNew as Hinput
      imod (stateInterp_memoryGrow_tracked_frame store ns obs nt delta
          (store.wasm.memoryCap store.runtime.currentModule 0)
          memory previousPages hg) $$ Hinput with Hout
      icases Hout with ⟨⟨Hσ, HnewPages, %_⟩, HcontNew⟩
      ispecialize HcontNew $$ HnewPages
      wasm_twp_frame
        iexact HcontNew

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
  wasm_twp_begin
  ihave_pure Hfacts :
      ⌜store.wasm.mem.read32 (address + offset) = word ∧
        (address + offset).toNat + 4 ≤
          store.wasm.mem.pages * 65536⌝ using
    stateInterp_pointsTo_u32_facts store ns obs nt
      (address + offset) word h1 h2 h3 $$ [Hσ Hword]
  obtain ⟨Hread, HinBounds⟩ := Hfacts
  have hbound : address.toNat + offset.toNat + 4 ≤
      store.wasm.mem.pages * 65536 := by
    simpa only [hnowrap] using HinBounds
  wasm_twp_step (by
    simpa [Hread] using
      (Step.load32 (α := α) (address := Value.i32 address) rfl hbound)) =>
    wasm_twp_frame
      iapply Htwp
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
  wasm_twp_begin
  ihave_pure Hfacts :
      ⌜store.wasm.mem.read32 (address + offset) = oldWord ∧
        (address + offset).toNat + 4 ≤
          store.wasm.mem.pages * 65536⌝ using
    stateInterp_pointsTo_u32_facts store ns obs nt
      (address + offset) oldWord h1 h2 h3 $$ [Hσ Hword]
  have hbound : address.toNat + offset.toNat + 4 ≤
      store.wasm.mem.pages * 65536 := by
    simpa only [hnowrap] using Hfacts.2
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
    Step.store32 (α := α) (address := Value.i32 address) rfl hbound
  wasm_twp_step expectedStep =>
    imod stateInterp_store32 store ns obs nt
        (address + offset) oldWord value h1 h2 h3 Hfacts.2 $$
        [$Hσ $Hword] with ⟨Hσ, Hword⟩
    wasm_twp_frame
      iapply Htwp
      iexact Hword


wasm_twp_pure_rule twp_geS {lhs rhs result : UInt32}
    (hresult : result = if lhs.toInt32 ≥ rhs.toInt32 then 1 else 0) :
  .geS, .i32 rhs :: .i32 lhs :: values =>
    .i32 result :: values := Step.geS hresult

theorem twp_memoryFill32
    {params localValues values : List Value}
    {destination len value : UInt32}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (oldBytes : List UInt8)
    (hlen : oldBytes.length = len.toNat)
    (hpos : 0 < len.toNat)
    (hnowrap : destination.toNat + len.toNat < 4294967296) :
    pointsToBytes 0 destination oldBytes -∗
    (pointsToBytes 0 destination (List.replicate oldBytes.length value.toUInt8) -∗
      WP (Expr.running ⟨⟨params, localValues, values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }]) -∗
    WP (Expr.running ⟨⟨params, localValues,
        .i32 len :: .i32 value :: .i32 destination :: values⟩,
        .memoryFill :: code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro Hbytes Htwp
  wasm_twp_begin
  wasm_points_to_bytes_agree Hpb, destination, oldBytes, obs $$ [Hσ Hbytes]
  have hbound : destination.toNat + len.toNat ≤ store.wasm.mem.pages * 65536 := by
    have := pointsToBytes_facts_bound Hpb (by omega) (by omega)
    omega
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
  wasm_twp_step expectedStep =>
    imod stateInterp_fill_bytes store ns obs nt destination oldBytes value.toUInt8
        (by rw [hlen]; exact hbound) (by rw [hlen]; exact hnowrap)
        $$ [$Hσ $Hbytes] with ⟨Hσ, Hbytes⟩
    wasm_twp_frame
      iapply Htwp
      iexact Hbytes

theorem twp_memoryCopy32
    {params localValues values : List Value}
    {destination source len : UInt32}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (oldDstBytes srcBytes : List UInt8)
    (hlen_dst : oldDstBytes.length = len.toNat)
    (hlen_src : srcBytes.length = len.toNat)
    (hpos : 0 < len.toNat)
    (hnowrap_dst : destination.toNat + len.toNat < 4294967296)
    (hnowrap_src : source.toNat + len.toNat < 4294967296) :
    pointsToBytes 0 source srcBytes -∗
    pointsToBytes 0 destination oldDstBytes -∗
    (pointsToBytes 0 source srcBytes -∗
      pointsToBytes 0 destination srcBytes -∗
      WP (Expr.running ⟨⟨params, localValues, values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }]) -∗
    WP (Expr.running ⟨⟨params, localValues,
        .i32 len :: .i32 source :: .i32 destination :: values⟩,
        .memoryCopy :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro Hsrc Hdst Htwp
  wasm_twp_begin
  wasm_points_to_bytes_agree Hpbsrc, source, srcBytes, obs $$ [Hσ Hsrc]
  wasm_points_to_bytes_agree Hpbdst, destination, oldDstBytes, obs $$ [Hσ Hdst]
  have hbound_src :
      source.toNat + len.toNat ≤ store.wasm.mem.pages * 65536 := by
    have := pointsToBytes_facts_bound Hpbsrc (by omega) (by omega)
    omega
  have hbound_dst :
      destination.toNat + len.toNat ≤ store.wasm.mem.pages * 65536 := by
    have := pointsToBytes_facts_bound Hpbdst (by omega) (by omega)
    omega
  have expectedStep : Step
      ⟨.running ⟨⟨params, localValues,
          .i32 len :: .i32 source :: .i32 destination :: values⟩,
          .memoryCopy :: code, arity, remainder, controls, calls⟩, store⟩
      (.instruction .memoryCopy)
      ⟨.running ⟨⟨params, localValues, values⟩,
          code, arity, remainder, controls, calls⟩,
        { store with wasm :=
            { store.wasm with mem :=
                store.wasm.mem.copy destination.toNat source.toNat oldDstBytes.length } }⟩ := by
    rw [hlen_dst]
    simpa only [setMemory_eq] using Step.memoryCopy32 hbound_dst hbound_src
  wasm_twp_step expectedStep =>
    imod stateInterp_copy_bytes store ns obs nt
        destination source oldDstBytes srcBytes
        (hlen_src.trans hlen_dst.symm)
        (by rw [hlen_dst]; exact hbound_dst)
        (by rw [hlen_dst]; exact hnowrap_dst)
        (by rw [hlen_src]; exact hbound_src)
        (by rw [hlen_src]; exact hnowrap_src)
        $$ [$Hσ $Hsrc $Hdst] with ⟨Hσ, Hsrc, Hdst⟩
    wasm_twp_frame
      iapply Htwp $$ Hsrc Hdst

/-- `throw` instruction (total form).  Tag identity is supplied by the
persistent `tagTableOwn` fragment handed out at adequacy setup, not by an
invariant of the state interpretation: the rule only needs `tagIndex` to be
canonical in the entry instance's tag table, which stays true when the machine
tag table carries further entries from other registered modules. -/
theorem twp_throwI
    (runtimeModule : Module) (instanceId : ModuleInstanceId) (tagIndex : Nat) {tagType : FuncType}
    {tagIds : List Nat}
    {params localValues values : List Value}
    (htag : runtimeModule.tags[tagIndex]? = some tagType)
    (hcanonical : TagIndexCanonical tagIds tagIndex)
    (hargs : tagType.params.length ≤ values.length)
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn instanceId runtimeModule -∗
    tagTableOwn tagIds -∗
    (runtimeModuleOwn instanceId runtimeModule -∗
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
  wasm_twp_begin
  wasm_runtime_module_agree obs, instanceId, runtimeModule $$ [$Hσ $Hruntime]
  have htag' : store.runtime.currentModule.tags[tagIndex]? = some tagType := by
    simpa only [Hmodule] using htag
  ihave_pure Hprefix : ⌜tagIds.IsPrefix store.wasm.tagIds⌝ using
    stateInterp_tagTable_prefix store ns obs nt tagIds $$ [Hσ Htags]
  wasm_twp_step (Step.throwI (α := α) htag' hargs) =>
    wasm_twp_frame
      have hcanonicalStore :=
        (canonicalTagIndex_eq store tagIndex).trans
          (canonicalTagIndex_of_prefix store tagIds tagIndex Hprefix hcanonical)
      rw [hcanonicalStore]
      iapply Hwp
      iexact Hruntime

/-- Total-correctness counterpart of `wp_catchException`, and restricted the
same way: `hclause` limits it to the ref-less `.catch` / `.catchAll` clauses,
because for `.catchRef` / `.catchAllRef` the store-universal `htarget` premise
is unsatisfiable (`prepareCatch` puts `store.wasm.exns.length` into the pushed
`exnref`). -/
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
    (hclause : (∃ t l, clause = .catch t l) ∨ (∃ l, clause = .catchAll l))
    (htarget : ∀ store : MachineStore α,
        branchTarget? arity (catchLabel clause) outer
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
  wasm_twp_begin
  have expectedStep : Step
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
  wasm_twp_step expectedStep =>
    have hstore_eq : (prepareCatch tag arguments clause store).2 = store := by
      rcases hclause with ⟨t, l, rfl⟩ | ⟨l, rfl⟩ <;> rfl
    rw [hstore_eq]
    wasm_twp_frame
      iexact Hwp

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


wasm_twp_pure_rule twp_and {lhs rhs : UInt32} :
  .and, .i32 rhs :: .i32 lhs :: values => .i32 (lhs &&& rhs) :: values := Step.and

wasm_twp_pure_rule twp_ne {lhs rhs result : UInt32}
    (hresult : result = if lhs ≠ rhs then 1 else 0) :
  .ne, .i32 rhs :: .i32 lhs :: values => .i32 result :: values := Step.ne hresult

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
  wasm_twp_begin
  have hcanonical : ∀ s : MachineStore α,
      canonicalGlobalIndex s 0 = 0 := fun _ => rfl
  ihave_pure Hget :
      ⌜store.wasm.globals.globals[0]? = some value⌝ using
    stateInterp_global_facts store ns obs nt 0 value $$ [Hσ Hglobal]
  wasm_twp_step (Step.globalGet (α := α) (by
    simpa [globalAt?, hcanonical] using Hget)) =>
    wasm_twp_frame
      iapply Htwp
      iexact Hglobal

wasm_twp_pure_rule twp_scalarFloat0
    {instruction : Instruction} {value : Value}
    (heval : evalScalarFloat0? instruction = some value) :
  instruction, values => value :: values := Step.scalarFloat0 heval

wasm_twp_pure_rule twp_scalarFloat1
    {instruction : Instruction} {operand value : Value}
    (hzero : evalScalarFloat0? instruction = none)
    (heval : evalScalarFloat1? instruction operand = some value) :
  instruction, operand :: values => value :: values :=
    Step.scalarFloat1 hzero heval

wasm_twp_pure_rule twp_scalarFloat2
    {instruction : Instruction} {lhs rhs value : Value}
    (hzero : evalScalarFloat0? instruction = none)
    (hunary : evalScalarFloat1? instruction rhs = none)
    (heval : evalScalarFloat2? instruction lhs rhs = some value) :
  instruction, rhs :: lhs :: values => value :: values :=
    Step.scalarFloat2 hzero hunary heval

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
  wasm_twp_begin
  ihave_pure Hfacts :
      ⌜store.wasm.mem.read32 (address + offset) = word ∧
        (address + offset).toNat + 4 ≤
          store.wasm.mem.pages * 65536⌝ using
    stateInterp_pointsTo_u32_facts store ns obs nt
      (address + offset) word h1 h2 h3 $$ [Hσ Hword]
  obtain ⟨Hread, HinBounds⟩ := Hfacts
  have hbound : address.toNat + offset.toNat + 4 ≤
      store.wasm.mem.pages * 65536 := by
    simpa only [hnowrap] using HinBounds
  wasm_twp_step (by
    simpa [Hread] using
      (Step.f32Load (α := α) (address := .i32 address) rfl hbound)) =>
    wasm_twp_frame
      iapply Htwp
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
  wasm_twp_begin
  ihave_pure Hfacts :
      ⌜store.wasm.mem.read32 (address + offset) = oldWord ∧
        (address + offset).toNat + 4 ≤
          store.wasm.mem.pages * 65536⌝ using
    stateInterp_pointsTo_u32_facts store ns obs nt
      (address + offset) oldWord h1 h2 h3 $$ [Hσ Hword]
  have hbound : address.toNat + offset.toNat + 4 ≤
      store.wasm.mem.pages * 65536 := by
    simpa only [hnowrap] using Hfacts.2
  have expectedStep : Step
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
  wasm_twp_step expectedStep =>
    imod stateInterp_store32 store ns obs nt
        (address + offset) oldWord value h1 h2 h3 Hfacts.2 $$
        [$Hσ $Hword] with ⟨Hσ, Hword⟩
    wasm_twp_frame
      iapply Htwp
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
  wasm_twp_begin
  have hcanonical : ∀ s : MachineStore α,
      canonicalGlobalIndex s 0 = 0 := fun _ => rfl
  ihave_pure Hget :
      ⌜store.wasm.globals.globals[0]? = some oldValue⌝ using
    stateInterp_global_facts store ns obs nt 0 oldValue $$ [Hσ Hglobal]
  have hsome :
      (globalAt? store 0).isSome = true := by
    simp [globalAt?, hcanonical, Hget]
  let updatedStore : MachineStore α :=
    { store with wasm :=
        { store.wasm with globals :=
            { globals := store.wasm.globals.globals.set 0 newValue } } }
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
  wasm_twp_step expectedStep =>
    imod stateInterp_global_set store ns obs nt
        0 oldValue newValue $$ [$Hσ $Hglobal] with ⟨Hσ, Hglobal⟩
    wasm_twp_frame
      iapply Htwp
      iexact Hglobal

wasm_twp_pure_rule twp_or {lhs rhs : UInt32} :
  .or, .i32 rhs :: .i32 lhs :: values => .i32 (lhs ||| rhs) :: values := Step.or

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
  wasm_twp_begin
  ihave_pure Hfacts :
      ⌜store.wasm.mem.read64 (address + offset) = word ∧
        (address + offset).toNat + 8 ≤
          store.wasm.mem.pages * 65536⌝ using
    stateInterp_pointsTo_u64_facts store ns obs nt
      (address + offset) word h1 h2 h3 h4 h5 h6 h7 $$ [Hσ Hword]
  obtain ⟨Hread, HinBounds⟩ := Hfacts
  have hbound : address.toNat + offset.toNat + 8 ≤
      store.wasm.mem.pages * 65536 := by
    simpa only [hnowrap] using HinBounds
  wasm_twp_step (by
    simpa [Hread] using
      (Step.f64Load (α := α) (address := .i32 address) rfl hbound)) =>
    wasm_twp_frame
      iapply Htwp
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
  wasm_twp_begin
  ihave_pure Hfacts :
      ⌜store.wasm.mem.read64 (address + offset) = oldWord ∧
        (address + offset).toNat + 8 ≤
          store.wasm.mem.pages * 65536⌝ using
    stateInterp_pointsTo_u64_facts store ns obs nt
      (address + offset) oldWord h1 h2 h3 h4 h5 h6 h7 $$ [Hσ Hword]
  have hbound : address.toNat + offset.toNat + 8 ≤
      store.wasm.mem.pages * 65536 := by
    simpa only [hnowrap] using Hfacts.2
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
  wasm_twp_step expectedStep =>
    imod stateInterp_store64 store ns obs nt
        (address + offset) oldWord value h1 h2 h3 h4 h5 h6 h7 Hfacts.2 $$
        [$Hσ $Hword] with ⟨Hσ, Hword⟩
    wasm_twp_frame
      iapply Htwp
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
  wasm_twp_begin
  ihave_pure Hfacts :
      ⌜store.wasm.mem.read64 (address + offset) = word ∧
        (address + offset).toNat + 8 ≤
          store.wasm.mem.pages * 65536⌝ using
    stateInterp_pointsTo_u64_facts store ns obs nt
      (address + offset) word h1 h2 h3 h4 h5 h6 h7 $$ [Hσ Hword]
  obtain ⟨Hread, HinBounds⟩ := Hfacts
  have hbound : address.toNat + offset.toNat + 8 ≤
      store.wasm.mem.pages * 65536 := by
    simpa only [hnowrap] using HinBounds
  wasm_twp_step (by
    simpa [Hread] using
      (Step.load64 (α := α) (address := .i32 address) rfl hbound)) =>
    wasm_twp_frame
      iapply Htwp
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
  wasm_twp_begin
  ihave_pure Hfacts :
      ⌜store.wasm.mem.read64 (address + offset) = oldWord ∧
        (address + offset).toNat + 8 ≤
          store.wasm.mem.pages * 65536⌝ using
    stateInterp_pointsTo_u64_facts store ns obs nt
      (address + offset) oldWord h1 h2 h3 h4 h5 h6 h7 $$ [Hσ Hword]
  have hbound : address.toNat + offset.toNat + 8 ≤
      store.wasm.mem.pages * 65536 := by
    simpa only [hnowrap] using Hfacts.2
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
  wasm_twp_step expectedStep =>
    imod stateInterp_store64 store ns obs nt
        (address + offset) oldWord value h1 h2 h3 h4 h5 h6 h7 Hfacts.2 $$
        [$Hσ $Hword] with ⟨Hσ, Hword⟩
    wasm_twp_frame
      iapply Htwp
      iexact Hword

end terminalGeneric

section terminalGenericHelpers

variable [WasmSmallStepGS hlc α]
variable {Terminal : Type}
variable [view : TerminalView α Terminal]
local instance (priority := high) activeTerminalLanguageHelpers :
    Language (Expr α) (MachineStore α) StepKind Terminal :=
  TerminalView.canonicalLanguage
local instance (priority := high) activeTerminalIrisGSHelpers :
    @IrisGS_gen hlc (Expr α) Terminal (MachineStore α) StepKind
      activeTerminalLanguageHelpers (WasmHeapGF α) :=
  { numLatersPerStep _ := 0
    forkPost _ := iprop(True)
    stateInterp_mono _ _ _ _ := by iintro $ }
variable {s : Stuckness} {E : CoPset}
variable {Φ : Terminal → IProp (WasmHeapGF α)}

wasm_twp_pure_rule twp_subI64 {lhs rhs : UInt64} :
  .subI64, .i64 rhs :: .i64 lhs :: values =>
    .i64 (lhs - rhs) :: values := Step.subI64

wasm_twp_pure_rule twp_mulI64 {lhs rhs : UInt64} :
  .mulI64, .i64 rhs :: .i64 lhs :: values =>
    .i64 (lhs * rhs) :: values := Step.mulI64

wasm_twp_pure_rule twp_constI64 {value : UInt64} :
  .constI64 value, values => .i64 value :: values := Step.constI64

wasm_twp_pure_rule twp_orI64 {lhs rhs : UInt64} :
  .orI64, .i64 rhs :: .i64 lhs :: values =>
    .i64 (lhs ||| rhs) :: values := Step.orI64

wasm_twp_pure_rule twp_shlI64 {lhs rhs : UInt64} :
  .shlI64, .i64 rhs :: .i64 lhs :: values =>
    .i64 (lhs <<< (rhs % 64)) :: values := Step.shlI64

wasm_twp_pure_rule twp_shrUI64 {lhs rhs : UInt64} :
  .shrUI64, .i64 rhs :: .i64 lhs :: values =>
    .i64 (lhs >>> (rhs % 64)) :: values := Step.shrUI64

wasm_twp_pure_rule twp_ctzI64 {value : UInt64} :
  .ctzI64, .i64 value :: values =>
    .i64 (UInt64.ofNat (ctz64 64 value)) :: values := Step.ctzI64

wasm_twp_pure_rule twp_wrapI64 {value : UInt64} :
  .wrapI64, .i64 value :: values =>
    .i32 (UInt32.ofNat (value.toNat % 2 ^ 32)) :: values := Step.wrapI64

wasm_twp_pure_rule twp_extendUI32 {value : UInt32} :
  .extendUI32, .i32 value :: values =>
    .i64 (UInt64.ofNat value.toNat) :: values := Step.extendUI32

wasm_twp_pure_rule twp_eqI64 {lhs rhs : UInt64} {result : UInt32}
    (hresult : result = if lhs = rhs then 1 else 0) :
  .eqI64, .i64 rhs :: .i64 lhs :: values =>
    .i32 result :: values := Step.eqI64 hresult

wasm_twp_pure_rule twp_neI64 {lhs rhs : UInt64} {result : UInt32}
    (hresult : result = if lhs ≠ rhs then 1 else 0) :
  .neI64, .i64 rhs :: .i64 lhs :: values =>
    .i32 result :: values := Step.neI64 hresult

wasm_twp_pure_rule twp_ltUI64 {lhs rhs : UInt64} {result : UInt32}
    (hresult : result = if lhs < rhs then 1 else 0) :
  .ltUI64, .i64 rhs :: .i64 lhs :: values =>
    .i32 result :: values := Step.ltUI64 hresult

wasm_twp_pure_rule twp_gtUI64 {lhs rhs : UInt64} {result : UInt32}
    (hresult : result = if lhs > rhs then 1 else 0) :
  .gtUI64, .i64 rhs :: .i64 lhs :: values =>
    .i32 result :: values := Step.gtUI64 hresult

/-- Apply an explicit sequence of side-condition-free pure Wasm steps.
Stops before any rule that needs a semantic choice, client resource, or
non-definitional proof. -/
syntax "wasm_twp_pures" "[" ident* "]" : tactic

macro_rules
  | `(tactic| wasm_twp_pures []) => `(tactic| skip)
  | `(tactic| wasm_twp_pures [twp_localGet $rest:ident*]) =>
      `(tactic| iapply twp_localGet rfl; wasm_twp_pures [$rest:ident*])
  | `(tactic| wasm_twp_pures [twp_localSet $rest:ident*]) =>
      `(tactic| iapply twp_localSet rfl; wasm_twp_pures [$rest:ident*])
  | `(tactic| wasm_twp_pures [twp_localTee $rest:ident*]) =>
      `(tactic| iapply twp_localTee rfl; wasm_twp_pures [$rest:ident*])
  | `(tactic| wasm_twp_pures [twp_const $rest:ident*]) =>
      `(tactic| iapply twp_const; wasm_twp_pures [$rest:ident*])
  | `(tactic| wasm_twp_pures [twp_add $rest:ident*]) =>
      `(tactic| iapply twp_add; wasm_twp_pures [$rest:ident*])
  | `(tactic| wasm_twp_pures [twp_sub $rest:ident*]) =>
      `(tactic| iapply twp_sub; wasm_twp_pures [$rest:ident*])
  | `(tactic| wasm_twp_pures [twp_mul $rest:ident*]) =>
      `(tactic| iapply twp_mul; wasm_twp_pures [$rest:ident*])
  | `(tactic| wasm_twp_pures [twp_and $rest:ident*]) =>
      `(tactic| iapply twp_and; wasm_twp_pures [$rest:ident*])
  | `(tactic| wasm_twp_pures [twp_or $rest:ident*]) =>
      `(tactic| iapply twp_or; wasm_twp_pures [$rest:ident*])
  | `(tactic| wasm_twp_pures [twp_shl $rest:ident*]) =>
      `(tactic| iapply twp_shl; wasm_twp_pures [$rest:ident*])
  | `(tactic| wasm_twp_pures [twp_shrU $rest:ident*]) =>
      `(tactic| iapply twp_shrU; wasm_twp_pures [$rest:ident*])
  | `(tactic| wasm_twp_pures [twp_constI64 $rest:ident*]) =>
      `(tactic| iapply twp_constI64; wasm_twp_pures [$rest:ident*])
  | `(tactic| wasm_twp_pures [twp_subI64 $rest:ident*]) =>
      `(tactic| iapply twp_subI64; wasm_twp_pures [$rest:ident*])
  | `(tactic| wasm_twp_pures [twp_mulI64 $rest:ident*]) =>
      `(tactic| iapply twp_mulI64; wasm_twp_pures [$rest:ident*])
  | `(tactic| wasm_twp_pures [twp_orI64 $rest:ident*]) =>
      `(tactic| iapply twp_orI64; wasm_twp_pures [$rest:ident*])
  | `(tactic| wasm_twp_pures [twp_shlI64 $rest:ident*]) =>
      `(tactic| iapply twp_shlI64; wasm_twp_pures [$rest:ident*])
  | `(tactic| wasm_twp_pures [twp_shrUI64 $rest:ident*]) =>
      `(tactic| iapply twp_shrUI64; wasm_twp_pures [$rest:ident*])
  | `(tactic| wasm_twp_pures [twp_ctzI64 $rest:ident*]) =>
      `(tactic| iapply twp_ctzI64; wasm_twp_pures [$rest:ident*])
  | `(tactic| wasm_twp_pures [twp_wrapI64 $rest:ident*]) =>
      `(tactic| iapply twp_wrapI64; wasm_twp_pures [$rest:ident*])
  | `(tactic| wasm_twp_pures [twp_extendUI32 $rest:ident*]) =>
      `(tactic| iapply twp_extendUI32; wasm_twp_pures [$rest:ident*])
  | `(tactic| wasm_twp_pures [twp_block $rest:ident*]) =>
      `(tactic| iapply twp_block; wasm_twp_pures [$rest:ident*])
  | `(tactic| wasm_twp_pures [twp_brIfZero $rest:ident*]) =>
      `(tactic| iapply twp_brIfZero; wasm_twp_pures [$rest:ident*])
  | `(tactic| wasm_twp_pures [twp_br $rest:ident*]) =>
      `(tactic| iapply twp_br rfl; wasm_twp_pures [$rest:ident*])
  | `(tactic| wasm_twp_pures [twp_exitControl $rest:ident*]) =>
      `(tactic| iapply twp_exitControl rfl; wasm_twp_pures [$rest:ident*])
  | `(tactic| wasm_twp_pures [twp_eqz $rest:ident*]) =>
      `(tactic| iapply twp_eqz rfl; wasm_twp_pures [$rest:ident*])
  | `(tactic| wasm_twp_pures [twp_eq $rest:ident*]) =>
      `(tactic| iapply twp_eq rfl; wasm_twp_pures [$rest:ident*])
  | `(tactic| wasm_twp_pures [twp_ltU $rest:ident*]) =>
      `(tactic| iapply twp_ltU rfl; wasm_twp_pures [$rest:ident*])
  | `(tactic| wasm_twp_pures [twp_gtU $rest:ident*]) =>
      `(tactic| iapply twp_gtU rfl; wasm_twp_pures [$rest:ident*])
  | `(tactic| wasm_twp_pures [twp_ltUI64 $rest:ident*]) =>
      `(tactic| iapply twp_ltUI64 rfl; wasm_twp_pures [$rest:ident*])
  | `(tactic| wasm_twp_pures [twp_iff $rest:ident*]) =>
      `(tactic| iapply twp_iff rfl; wasm_twp_pures [$rest:ident*])
  | `(tactic| wasm_twp_pures [twp_scalarFloat0 $rest:ident*]) =>
      `(tactic| iapply twp_scalarFloat0 rfl; wasm_twp_pures [$rest:ident*])

/-- `i32.load` at offset 0, phrased directly on `addr` rather than
`addr + 0`, which keeps Iris's unifier from having to see through the
offset addition.  Relocated here from `SmallStepAdequacy`, where it sat
among the adequacy proofs despite being an ordinary lifting rule. -/
theorem twp_load32_addr
    {params localValues values : List Value}
    {addr : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    (word : UInt32)
    (h1 : (addr + 1 : UInt32).toNat = addr.toNat + 1)
    (h2 : (addr + 2 : UInt32).toNat = addr.toNat + 2)
    (h3 : (addr + 3 : UInt32).toNat = addr.toNat + 3) :
    let current : ThreadState α :=
      ⟨⟨params, localValues, .i32 addr :: values⟩,
        .load32 0 :: code, arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨⟨params, localValues, .i32 word :: values⟩,
        code, arity, remainder, controls, calls⟩
    pointsTo_u32 0 addr word -∗
    (pointsTo_u32 0 addr word -∗
      WP (Expr.running next : Expr α) @ s; E [{ Φ }]) -∗
      WP (Expr.running current : Expr α) @ s; E [{ Φ }] := by
  dsimp only
  iintro Hword Htwp
  wasm_twp_begin
  ihave_pure Hfacts :
      ⌜store.wasm.mem.read32 addr = word ∧
        addr.toNat + 4 ≤ store.wasm.mem.pages * 65536⌝ using
    stateInterp_pointsTo_u32_facts store ns obs nt
      addr word h1 h2 h3 $$ [Hσ Hword]
  obtain ⟨Hread, HinBounds⟩ := Hfacts
  have hbound : addr.toNat + (0 : UInt32).toNat + 4 ≤
      store.wasm.mem.pages * 65536 := by
    have h0 : (0 : UInt32).toNat = 0 := rfl
    omega
  wasm_twp_step (by
    simpa only [show (addr + 0 : UInt32) = addr from by simp, Hread]
      using Step.load32 (α := α) (address := Value.i32 addr) rfl hbound) =>
    wasm_twp_frame
      iapply Htwp
      iexact Hword

end terminalGenericHelpers

end Wasm.SmallStep
