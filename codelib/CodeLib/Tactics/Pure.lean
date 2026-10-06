import Lean
import CodeLib.Tactics.Registry

open Lean Meta Elab Tactic

namespace CodeLib.Tactics

/-- Return the last string component of `n` as a fresh simple `Name`.
Used to turn a fully-qualified constructor name such as
`Wasm.Instruction.const` into the registry key `Name.mkSimple "const"`. -/
def nameLastSimple : Name → Name
  | .str _ s => .str .anonymous s
  | n        => n

/-- Given a Lean expression that is either a WP IProp directly or the iris
proof-mode wrapper `envs_entails Γ (WP ...)`, return the WP IProp and its
modality key string:
- `"twp"` for `TotalWp.totalWp`  (notation `WP e @ s; E [{ Φ }]`)
- `"wp"`  for `Wp.wp`            (notation `WP e @ s; E {{ Φ }}`)
Throws if neither matches. -/
def unwrapIrisGoal (goalTy : Expr) : MetaM (Expr × String) := do
  let goalTy := goalTy.consumeMData
  let fn := goalTy.getAppFn
  -- Direct case: TotalWp.totalWp or Wp.wp is the head
  if fn.isConst then
    let n := fn.constName!.getString!
    if n == "totalWp" then return (goalTy, "twp")
    if n == "wp"       then return (goalTy, "wp")
  -- Iris proof-mode case: envs_entails Γ (WP ...)
  -- The iris goal is the last explicit argument.
  let args := goalTy.getAppArgs
  if h : args.size > 0 then
    let inner := (args[args.size - 1]).consumeMData
    let fn' := inner.getAppFn
    if fn'.isConst then
      let n' := fn'.constName!.getString!
      if n' == "totalWp" then return (inner, "twp")
      if n' == "wp"       then return (inner, "wp")
  throwError "wasm_pure: goal is not a TWP/WP goal \
    (expected TotalWp.totalWp or Wp.wp head or iris envs_entails wrapper; \
    got {goalTy})"

/-- Resolve the instruction-head key and modality from the WP goal in `goal`.

The goal type must be (or wrap) a WP proposition of the form
  `TotalWp.totalWp s E (Expr.running thread) Φ`  or
  `Wp.wp          s E (Expr.running thread) Φ`
where `thread.code` reduces (under default-transparency `whnf`) to a concrete
`List Instruction`.  Returns `(ctorKey, modality)` where `ctorKey` is the
unqualified constructor name (e.g. `Name.mkSimple "const"`) and `modality`
is `"twp"` or `"wp"`. -/
def instrHeadKey (goal : MVarId) : MetaM (Name × String) := do
  let goalTy ← goal.getType >>= instantiateMVars
  let (wpExpr, modality) ← unwrapIrisGoal goalTy
  let args := wpExpr.getAppArgs
  if args.size < 4 then
    throwError "wasm_pure: WP applied to fewer than 4 args"
  -- args[size-4] = s, args[size-3] = E, args[size-2] = e, args[size-1] = Φ
  let e  := args[args.size - 2]!
  let e' ← whnf e
  let eFn   := e'.getAppFn
  let eArgs := e'.getAppArgs
  unless eFn.isConst && eFn.constName!.getString! == "running" do
    throwError "wasm_pure: Wasm expression is not .running (got {eFn})"
  if eArgs.size < 1 then
    throwError "wasm_pure: Expr.running has no thread argument"
  let thread  := eArgs[eArgs.size - 1]!
  let thread' ← whnf thread
  let tArgs := thread'.getAppArgs
  if tArgs.size < 3 then
    throwError "wasm_pure: could not extract code field from thread state \
      (got {tArgs.size} args for ThreadState constructor)"
  let code  := tArgs[2]!
  let code' ← whnf code
  let codeFn := code'.getAppFn
  if codeFn.isConst && codeFn.constName!.getString! == "nil" then
    return (Name.mkSimple "nil", modality)
  let cArgs := code'.getAppArgs
  if cArgs.size < 2 then
    throwError "wasm_pure: code list is not fully reduced (got {cArgs.size} \
      args for cons, need ≥ 2)"
  let instr  := cArgs[1]!
  let instr' ← whnf instr
  let instrFn := instr'.getAppFn
  unless instrFn.isConst do
    throwError "wasm_pure: instruction head did not reduce to a constructor"
  return (nameLastSimple instrFn.constName!, modality)

/-- Try each pure-step entry in registration order; return `true` on first
success, `false` if every entry fails to unify or close its side conditions.
Infrastructure errors (e.g., `iapply` throwing for reasons other than unification
failure) propagate normally. -/
private def tryApplyPureRules (pureEntries : Array WasmRuleEntry) : TacticM Bool := do
  for entry in pureEntries do
    let .pure needsRfl := entry.kind | continue
    let st ← saveState
    let thmTerm : TSyntax `term := ⟨(mkIdent entry.thmName).raw⟩
    let pmt : TSyntax `pmTerm ←
      if needsRfl then do
        let rflTerm : TSyntax `term := ⟨(mkIdent `rfl).raw⟩
        let appExpr ← `($thmTerm $rflTerm)
        `(pmTerm| $appExpr:term)
      else
        `(pmTerm| $thmTerm:term)
    let succeeded ← try
      evalTactic (← `(tactic| iapply $pmt))
      let newGoals ← getGoals
      if newGoals.isEmpty then pure true
      else
        let mut continuation : List MVarId := []
        let mut ok := true
        for sg in newGoals do
          let ty ← sg.getType >>= instantiateMVars
          let headStr := ty.consumeMData.getAppFn.constName?
                          |>.map Name.getString! |>.getD ""
          -- Iris proof-mode goals in iris-lean are `Iris.ProofMode.Entails' A B`.
          if headStr == "Entails'" then
            continuation := continuation ++ [sg]
          else if ← Meta.isProp ty then
            -- Prop-type side condition: close with rfl or decide.
            -- May assign non-Prop value metavars that appear in it as a side effect.
            setGoals [sg]
            try evalTactic (← `(tactic| first | rfl | decide))
            catch _ => ok := false; break
            unless (← getGoals).isEmpty do ok := false; break
          -- Non-Prop value-type metavars are skipped; assigned by rfl on Prop goals.
        if ok then
          setGoals continuation
          try evalTactic (← `(tactic| simp (config := { decide := true }) only [List.take_succ_cons, List.take_zero, List.take_nil, List.nil_append, List.drop_zero, List.drop_nil, List.append_nil, ite_true, ite_false, ite_eq_left, ite_eq_right, List.length_cons, List.length_nil, List.set_cons_zero, List.set_cons_succ, Nat.sub_zero, Nat.sub_self]))
          catch _ => pure ()
        if !ok then restoreState st
        pure ok
    catch _ =>
      restoreState st
      pure false
    if succeeded then return true
  return false

/-- Apply one pure-step rule (TWP or WP) determined by the head of `thread.code`.

Looks up the instruction constructor in the `@[wasm_rule]` registry under
the modality derived from the goal (`twp` for `[{ Φ }]`, `wp` for `{{ Φ }}`).
Tries each registered entry in order; the first entry whose `iapply` unifies
and whose Prop side conditions close with `rfl`/`decide` wins.
After each successful step the tactic simplifies `List.take`/`List.drop`
leftovers from branch rules and evaluates closed `if` conditions.

**Errors** (with the instruction name) if:
- the goal is not a TWP/WP goal (bare or iris-mode-wrapped);
- `thread.code` cannot be reduced to a concrete instruction;
- no rule is registered for the head constructor;
- all registered entries fail to apply. -/
elab "wasm_pure" : tactic => do
  let goal ← getMainGoal
  let (ctorKey, modality) ← instrHeadKey goal
  let env ← getEnv
  let entries ← match getWasmRule env (Name.mkSimple modality) ctorKey with
    | none => throwError "wasm_pure: no rule registered for {ctorKey}"
    | some arr => pure arr
  let hasMem := entries.any fun e => match e.kind with | .mem _ => true | _ => false
  let pureEntries := entries.filter fun e => match e.kind with | .pure _ => true | _ => false
  if pureEntries.isEmpty then
    if hasMem then throwError "wasm_pure: rule for {ctorKey} is a mem rule; use wasm_mem"
    else        throwError "wasm_pure: no rule registered for {ctorKey}"
  let succeeded ← tryApplyPureRules pureEntries
  if succeeded then return
  let triedStr := String.intercalate ", "
    (pureEntries.toList.map fun e => e.thmName.getString!)
  throwError m!"wasm_pure: no registered rule applied to {ctorKey} (tried: {triedStr})"

/-- Repeat `wasm_pure` and `wasm_mem` until the head instruction has no registered
rule or the goal is no longer a WP goal.

Dispatches to `tryApplyPureRules` for pure-step rules and to `wasm_mem` for
memory and global rules, looping until no rule is found for the current head.
After each successful pure step the tactic simplifies `List.take`/`List.drop`
leftovers from branch rules and evaluates closed `if` conditions.

With `wasm_pures using [l₁, …, lₙ]`, runs `simp only [l₁, …, lₙ]` on the goal
at the start of each iteration.  This normalises the code list, locals, and
arithmetic expressions so that `instrHeadKey` can read the next instruction
after block/branch/opaque-definition steps.  The same lemma list is forwarded
to each `wasm_mem using [l₁, …, lₙ]` call for address normalisation.

The pre-check (`instrHeadKey` + `getWasmRule`) is wrapped in `try … catch`
so that all expected termination signals (wrong goal type, un-reducible code,
unregistered head) stop the loop silently.  For `.pure` dispatch,
`tryApplyPureRules` returns `false` when all registered entries fail
(e.g. `br_if` with a symbolic condition), stopping the loop silently.
For `.mem` dispatch, errors from `wasm_mem` propagate to the caller —
a missing or ambiguous ownership hypothesis is a real proof obligation,
not a loop termination signal. -/
private partial def wasmPuresLoop (usingTerms : Array (TSyntax `term)) : TacticM Unit := do
  let goals ← getGoals
  if goals.isEmpty then return
  if !usingTerms.isEmpty then
    let simpLemmas ← usingTerms.mapM fun t => `(Lean.Parser.Tactic.simpLemma| $t:term)
    try evalTactic (← `(tactic| simp only [$simpLemmas,*]))
    catch _ => pure ()
  let goalsNow ← getGoals
  if goalsNow.isEmpty then return
  let goal ← getMainGoal
  let maybeEntries : Option (Array WasmRuleEntry) ← do
    try
      let (ctorKey, modality) ← instrHeadKey goal
      let env ← getEnv
      pure (getWasmRule env (Name.mkSimple modality) ctorKey)
    catch _ => pure none
  match maybeEntries with
  | none => return
  | some entries =>
    if entries.isEmpty then return
    match entries[0]!.kind with
    | .mem _ =>
      if usingTerms.isEmpty then
        evalTactic (← `(tactic| wasm_mem))
      else
        evalTactic (← `(tactic| wasm_mem using [$usingTerms,*]))
      wasmPuresLoop usingTerms
    | .pure _ =>
      let pureEntries := entries.filter fun e => match e.kind with | .pure _ => true | _ => false
      let succeeded ← tryApplyPureRules pureEntries
      if !succeeded then return
      wasmPuresLoop usingTerms

syntax (name := wasm_pures) "wasm_pures" ("using" "[" term,* "]")? : tactic

@[tactic wasm_pures]
def elabWasmPures : Lean.Elab.Tactic.Tactic := fun stx => do
  let usingTerms : Array (TSyntax `term) ←
    if stx[1].isNone then pure #[]
    else do
      let inner := stx[1][0]
      let termsSep := inner[2]
      pure (termsSep.getSepArgs.map (⟨·⟩))
  wasmPuresLoop usingTerms

end CodeLib.Tactics
