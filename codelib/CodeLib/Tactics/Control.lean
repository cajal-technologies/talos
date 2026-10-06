import Lean
import Qq
import Iris.ProofMode
import CodeLib.Tactics.Pure
import CodeLib.SepLogic.SmallStepTotalLoop
import CodeLib.SepLogic.SmallStepTotalLifting

open Lean Meta Elab Tactic Qq
open Iris.BI Iris.ProofMode

namespace CodeLib.Tactics

-- ─── wasm_loop ────────────────────────────────────────────────────────────────

/-- Find the bound-variable identifier in the binder of a `fun` expression.
Only inspects paren wrappers and the binder subtree of a `fun` node — never
the body — so identifiers in the body (e.g. from list notation) are skipped. -/
private partial def findFunBinder : Syntax → Option Name
  | .ident _ _ n _ => if n != `_ && n != .anonymous then some n else none
  | .node _ k args =>
    if k == `Lean.Parser.Term.paren then
      -- Strip parentheses: look at all children (one of them is the fun node).
      args.findSome? findFunBinder
    else if k == `Lean.Parser.Term.fun then
      -- `fun binders => body` — only inspect binders (index 1), not body.
      if h : 1 < args.size then findFunBinder args[1] else none
    else
      -- Binder container nodes: recurse freely.
      args.findSome? findFunBinder
  | _ => none

/-- Extract the bound-variable identifier from the `locals` lambda.
Falls back to `___wasm_loop_state` when the pattern doesn't match. -/
private def lambdaVarIdent (locals : TSyntax `term) : TSyntax `ident :=
  match findFunBinder locals.raw with
  | some n => Lean.mkIdent n
  | none   => Lean.mkIdent `___wasm_loop_state

private def extractWpInitialLocals (goal : MVarId) : MetaM Expr := do
  let goalTy ← goal.getType >>= instantiateMVars
  let (wpExpr, _) ← unwrapIrisGoal goalTy
  let wpArgs := wpExpr.getAppArgs
  let e  ← whnf wpArgs[wpArgs.size - 2]!
  let eArgs := e.getAppArgs
  let thread ← whnf (eArgs[eArgs.size - 1]!)
  let tArgs := thread.getAppArgs
  -- ThreadState.mk α locals code arity ...  (tArgs[0]=α, tArgs[1]=locals)
  if tArgs.size < 2 then
    throwError "wasm_loop: cannot extract locals from thread state \
      (got {tArgs.size} constructor args)"
  return tArgs[1]!

/-- `wasm_loop inv using measure initial locals` — total WP loop rule.

Applies `Wasm.SmallStep.twp_loop_wf_family` with the supplied invariant `inv`,
well-founded `measure`, `initial` family index, and `locals` function.
Closes `hinitial` and `hbelow` automatically with `first | rfl | decide | (simp; rfl)`.
Leaves two goals in this order:
1. The body-closure goal, with the family index intro'd under the bound variable
   name from the `locals` lambda (e.g. `state`) and `loopBodyExpr` simplified away.
2. The initial-invariant Iris goal `Γ ⊢ I initial`. -/
elab "wasm_loop" inv:term "using" measure:term "," initial:term "," locals:term : tactic => do
  let goal ← getMainGoal
  let (ctorKey, modality) ← instrHeadKey goal
  if modality != "twp" then
    throwError "wasm_loop: only total-WP goals are supported (got modality {modality})"
  if ctorKey != Name.mkSimple "loop" then
    throwError "wasm_loop: head instruction is not .loop (got {ctorKey})"
  let initialLocalsExpr  ← extractWpInitialLocals goal
  let initialLocalsTerm  ← PrettyPrinter.delab initialLocalsExpr
  evalTactic (← `(tactic|
    (iapply Wasm.SmallStep.twp_loop_wf_family
      (I := $inv) (measure := $measure) (initial := $initial) (locals := $locals)
      (initialLocals := $initialLocalsTerm)
      (by first | rfl | decide | (simp; rfl))
      (by first | rfl | decide | (simp; rfl)))))
  -- Goals: [body_closes, I_initial_iris]
  -- On body_closes: intro the index variable, then simp away loopBodyExpr.
  let allGoals ← getGoals
  if allGoals.isEmpty then return
  let restGoals := allGoals.tail
  setGoals [allGoals.head!]
  let stateVar := lambdaVarIdent locals
  evalTactic (← `(tactic| intro $stateVar:ident))
  evalTactic (← `(tactic| simp only [Wasm.SmallStep.loopBodyExpr]))
  let bodyGoals ← getGoals
  setGoals (bodyGoals ++ restGoals)

-- ─── wasm_call ────────────────────────────────────────────────────────────────

section
open Iris

/-- Scan an Iris `Hyps` tree for the first spatial hypothesis whose type is
`runtimeModuleOwn callerId runtimeModule`.  Returns `(hypName, callerId, runtimeModule)`. -/
private partial def findRuntimeModuleOwn
    {u : Level} {prop : Q(Type u)} {bi : Q(BI $prop)}
    : ∀ {e : Q($prop)}, Hyps bi e → MetaM (Option (Name × Expr × Expr))
  | _, .emp _ => return none
  | _, .hyp _ name _ivar bp ty _ => do
    if isTrue bp then return none  -- skip persistent hyps
    let fn := (ty : Expr).consumeMData.getAppFn
    if fn.isConst && fn.constName!.getString! == "runtimeModuleOwn" then
      let args := (ty : Expr).consumeMData.getAppArgs
      if args.size >= 2 then
        return some (name, args[args.size - 2]!, args[args.size - 1]!)
    return none
  | _, .sep _ _ _ _ lhs rhs => do
    match ← findRuntimeModuleOwn lhs with
    | some r => return some r
    | none   => findRuntimeModuleOwn rhs

end

/-- Close non-Iris Prop-valued side goals (the `himports` and `hfn` holes left by
`iapply (twp_call _ _ _ _ _ _)`) with `first | assumption | decide | rfl`.
Loops until no more progress, so resolving `hfn` can clean up the data metavar
goal for `fn` as a side effect. -/
private partial def closeSideGoals : TacticM Unit := do
  let closeTac ← `(tactic| first | assumption | decide | rfl)
  let goals ← getGoals
  -- Drop any metavars that were resolved as side effects of a previous close.
  let liveGoals ← goals.filterM fun g => return !(← g.isAssigned)
  if liveGoals.length != goals.length then
    setGoals liveGoals
    return ← closeSideGoals
  -- Try to close the first Prop goal that isn't an Iris proof-mode goal.
  for g in liveGoals do
    let gty ← g.getType >>= instantiateMVars
    if (parseIrisGoal? gty).isSome then continue   -- leave Iris goals alone
    if !(← isProp gty) then continue               -- skip data metavars (e.g. fn : Function)
    let ok ← withoutModifyingState do
      try
        setGoals [g]
        evalTactic closeTac
        return (← getGoals).isEmpty
      catch _ => return false
    if ok then
      let otherGoals := liveGoals.filter (· != g)
      setGoals [g]
      evalTactic closeTac
      let leftoverGoals ← getGoals  -- [] when fully closed
      setGoals (leftoverGoals ++ otherGoals)
      return ← closeSideGoals  -- recurse to handle the remaining goals
  -- No closable Prop goal found — done.

/-- Scan the caller's thread-state `values` field (before `iapply` fires) for a
named values-preparation function (e.g. `mergeArguments`).  Returns `none` for
plain cons-list stacks (`List.cons` head) which simp handles without extra help. -/
private def resolveValuesHelperFn (goal : MVarId) : MetaM (Option Name) := do
  try
    let goalTy ← goal.getType >>= instantiateMVars
    let (wpExpr, _) ← unwrapIrisGoal goalTy
    let wpArgs := wpExpr.getAppArgs
    let e ← whnf wpArgs[wpArgs.size - 2]!
    let eArgs := e.getAppArgs
    if eArgs.isEmpty then return none
    let thread ← whnf (eArgs[eArgs.size - 1]!)
    let tArgs := thread.getAppArgs
    if tArgs.size < 2 then return none
    -- tArgs[1] = Locals.mk params locals values
    let localsStruct ← whnf tArgs[1]!
    let localsArgs := localsStruct.getAppArgs
    if localsArgs.size < 3 then return none
    let values ← instantiateMVars localsArgs[localsArgs.size - 1]!
    let fn := values.getAppFn
    if fn.isConst then
      let nm := fn.constName!
      match nm with
      | `List.cons | `List.nil | `List.append => return none
      | _ => return some nm
    return none
  catch _ => return none

/-- After `twp_call` side goals are resolved and `?fn` is instantiated, extract
the callee function's definition name from `Function.toLocals fn …` in the
thread-state locals field, so it can be added to the `simp` set. -/
private def resolveFnSimpName (mainGoal : MVarId) : MetaM (Option Name) := do
  try
    let goalTy ← mainGoal.getType >>= instantiateMVars
    let (wpExpr, _) ← unwrapIrisGoal goalTy
    let wpArgs := wpExpr.getAppArgs
    let e ← whnf wpArgs[wpArgs.size - 2]!
    let eArgs := e.getAppArgs
    if eArgs.isEmpty then return none
    let thread ← whnf (eArgs[eArgs.size - 1]!)
    let tArgs := thread.getAppArgs
    if tArgs.size < 2 then return none
    -- tArgs[1] = Function.toLocals fn args
    let localsExpr ← instantiateMVars tArgs[1]!
    let laFn := localsExpr.getAppFn
    -- Confirm the head is Function.toLocals (last Name component = "toLocals")
    unless laFn.isConst && laFn.constName!.getString! == "toLocals" do return none
    let laArgs := localsExpr.getAppArgs
    if laArgs.isEmpty then return none
    -- laArgs[0] is the resolved fn
    let fn ← instantiateMVars laArgs[0]!
    match fn.getAppFn with
    | .const n _ => return some n
    | _          => return none
  catch _ => return none

/-- `wasm_call thm` — total WP call rule.

Finds the `runtimeModuleOwn` hypothesis in the Iris context, applies
`Wasm.SmallStep.twp_call` with all remaining arguments as holes, discharges
the `himports` and `hfn` side goals via `first | assumption | decide | rfl`,
normalises the callee's initial locals with
`simp only [<fn_def>, Function.toLocals, Function.numParams, ValueType.zero]`,
and finally applies `thm` (the callee-body theorem, including all its arguments)
to the resulting goal, leaving the continuation.

`thm` is a plain Lean term — pass the theorem with all arguments that would
normally follow `iapply`, e.g.:
  `wasm_call twp_mergeBody_from (α := α) initialLocals src tmp ... rfl`

Fails with a named error if the head instruction is not `.call`. -/
elab "wasm_call" thm:term : tactic => do
  let goal ← getMainGoal
  let (ctorKey, _) ← instrHeadKey goal
  if ctorKey != Name.mkSimple "call" then
    throwError "wasm_call: head instruction is not .call (got {ctorKey})"
  -- Locate runtimeModuleOwn in the Iris spatial context.
  let goalTy ← goal.getType >>= instantiateMVars
  let some irisGoal := parseIrisGoal? goalTy
    | throwError "wasm_call: goal is not in Iris proof mode"
  let some (runtimeHypName, _, _) ← findRuntimeModuleOwn irisGoal.hyps
    | throwError "wasm_call: no runtimeModuleOwn hypothesis found in Iris context"
  let runtimeHypId := mkIdent runtimeHypName
  -- Capture the values-preparation helper from the caller's stack BEFORE iapply
  -- changes the goal (e.g. `mergeArguments` needs to be in the simp set so that
  -- `(mergeArguments ...).take n` reduces; plain cons-lists don't need this).
  let valuesHelperOpt ← resolveValuesHelperFn goal
  -- Apply twp_call with all args as holes; Iris unifies runtimeModule and
  -- callerId from $$ runtimeHypId; functionIndex from the WP goal conclusion.
  let spec  ← `(specPat| $runtimeHypId:ident)
  let intro ← `(introPat| $runtimeHypId:ident)
  let applied ← `(pmTerm| (Wasm.SmallStep.twp_call _ _ _ _ _ _) $$ $spec)
  evalTactic (← `(tactic| iapply $applied))
  -- Close himports/hfn (and resolve ?fn) BEFORE iintro, because iapply puts
  -- Lean-level side goals first and iintro must target the Iris wand goal.
  closeSideGoals
  evalTactic (← `(tactic| iintro $intro))
  -- Build a simp set: fn's own definition + values helper (if any) + base
  -- helpers.  Use full `simp` (not `simp only`) so that @[simp] list lemmas
  -- (List.take_cons, List.reverse_cons, etc.) reduce the concrete params field.
  let mainGoal ← getMainGoal
  let fnNameOpt ← resolveFnSimpName mainGoal
  let baseNames : Array Name :=
    #[`Wasm.Function.toLocals, `Wasm.Function.numParams, `Wasm.ValueType.zero]
  let withFn  := match fnNameOpt      with | some n => #[n] | none => #[]
  let withVH  := match valuesHelperOpt with | some n => #[n] | none => #[]
  let allNames := withFn ++ withVH ++ baseNames
  let simpLemmas ← allNames.mapM fun n => do
    let id := Lean.mkIdent n
    `(Lean.Parser.Tactic.simpLemma| $id:ident)
  evalTactic (← `(tactic| simp [$simpLemmas,*]))
  -- Apply the callee-body theorem (with all its arguments).
  let pmt : TSyntax `pmTerm ← `(pmTerm| $thm:term)
  evalTactic (← `(tactic| iapply $pmt))

end CodeLib.Tactics
