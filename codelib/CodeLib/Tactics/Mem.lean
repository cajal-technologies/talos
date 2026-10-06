import Lean
import Qq
import Iris.ProofMode
import CodeLib.Tactics.Pure

open Lean Meta Elab Tactic Qq
open Iris.BI Iris.ProofMode

namespace CodeLib.Tactics

-- ─── Address normalization with user-supplied simp lemmas ─────────────────────

/-- Normalize `e` with `simp only [lemmaNames]`; identity if `lemmaNames` is empty. -/
private def normWithLemmas (e : Expr) (lemmaNames : Array Name) : MetaM Expr := do
  if lemmaNames.isEmpty then return e
  let mut st : SimpTheorems := {}
  for n in lemmaNames do
    st ← st.addConst n
  let ctx ← Simp.mkContext {} (simpTheorems := #[st])
  let (result, _) ← Simp.main e ctx
  return result.expr

-- ─── Iris hypothesis scanning ─────────────────────────────────────────────────

/-- Extract the address from a WasmHeap predicate type.

Returns `some addr` when `ty` is headed by the matching predicate:
- `"u32"` → `Wasm.SepLogic.pointsTo_u32 _ addr _`;  addr = args[args.size-2]
- `"u64"` → `Wasm.SepLogic.pointsTo_u64 _ addr _`;  addr = args[args.size-2]
- `"global"` → `Wasm.SepLogic.globalPointsToAt _ idx _`; idx = args[args.size-2]
- `"byte"` → `Iris.BI.Lib.GenHeap.pointsTo _ loc _ _`;  loc = args[args.size-3]

Returns `none` when the head doesn't match. -/
private def matchPredAddr (predWidth : String) (ty : Expr) : Option Expr := do
  let fn := ty.consumeMData.getAppFn
  guard fn.isConst
  let fnStr := fn.constName!.getString!
  let args := ty.consumeMData.getAppArgs
  match predWidth with
  | "u32"    => guard (fnStr == "pointsTo_u32");    if args.size >= 2 then some args[args.size - 2]! else none
  | "u64"    => guard (fnStr == "pointsTo_u64");    if args.size >= 2 then some args[args.size - 2]! else none
  | "global" => guard (fnStr == "globalPointsToAt"); if args.size >= 2 then some args[args.size - 2]! else none
  | "byte"   => guard (fnStr == "pointsTo"); if args.size >= 3 then (let loc := args[args.size - 3]!; let locArgs := loc.getAppArgs; if locArgs.size >= 2 then some locArgs[locArgs.size - 1]! else some loc) else none
  | _        => none

/-- An `arrayAt` / `array64At` region hypothesis found during scanning. -/
private structure ArrayCandidate where
  hypName : Name
  ptr     : Expr        -- base pointer extracted from the hypothesis type
  isU64   : Bool        -- true for `array64At` (stride 8); false for `arrayAt` (stride 4)
  index   : Option Nat  -- cell index resolved during candidate selection, if known
  deriving Inhabited

section
open Iris

/-- Traverse an Iris `Hyps` tree, collecting:
  - direct spatial hypotheses whose predicate address matches `normEffAddr`, and
  - `arrayAt` / `array64At` region hypotheses whose element width matches `predWidth`
    (for cell focusing when the address lies inside the region). -/
private partial def scanIrisHyps
    {u : Level} {prop : Q(Type u)} {bi : Q(BI $prop)}
    (predWidth : String) (normEffAddr : Expr) (usingLemmas : Array Name)
    : ∀ {e : Q($prop)}, Hyps bi e → MetaM (List Name × List ArrayCandidate)
  | _, .emp _ => return ([], [])
  | _, .hyp _ name _ivar bp ty _ => do
    if isTrue bp then return ([], [])
    let ty' : Expr := ty
    -- Check for arrayAt / array64At region hypothesis
    let fnStr := ty'.consumeMData.getAppFn.constName?.map (·.getString!) |>.getD ""
    if fnStr == "arrayAt" || fnStr == "array64At" then
      let isU64 := fnStr == "array64At"
      let eltWidth := if isU64 then "u64" else "u32"
      if eltWidth == predWidth then
        let args := ty'.consumeMData.getAppArgs
        if args.size >= 3 then
          let ptr := args[args.size - 2]!
          return ([], [{ hypName := name, ptr, isU64, index := none }])
      return ([], [])
    -- Check for direct pointsTo match
    match matchPredAddr predWidth ty' with
    | none      => return ([], [])
    | some addr =>
      let normHypAddr ← normWithLemmas addr usingLemmas
      if ← withoutModifyingState (isDefEq normEffAddr normHypAddr) then
        return ([name], [])
      else return ([], [])
  | _, .sep _ _ _ _ lhs rhs => do
    let lr ← scanIrisHyps predWidth normEffAddr usingLemmas lhs
    let rr ← scanIrisHyps predWidth normEffAddr usingLemmas rhs
    return (lr.1 ++ rr.1, lr.2 ++ rr.2)

/-- Count list-constructor nodes in a `List α` `Expr`, using `whnfD` at each step
to reduce through definitions. Works for lists with symbolic elements (e.g.
`[a, b]` where `a b : UInt32`) where `reduce (List.length xs)` returns
`Nat.succ` chains rather than `.lit (.natVal n)`. -/
private partial def countListLen (e : Expr) : MetaM (Option Nat) := do
  let e' ← whnfD e
  let fn := e'.consumeMData.getAppFn
  if !fn.isConst then return none
  match fn.constName!.getString! with
  | "nil"  => return some 0
  | "cons" =>
    let args := e'.consumeMData.getAppArgs
    if args.size >= 3 then
      match ← countListLen args[2]! with
      | some n => return some (n + 1)
      | none   => return none
    else return none
  | _ => return none

/-- Find the length of the `xs` list in an `arrayAt`/`array64At` hypothesis
    identified by `hypName` in an Iris `Hyps` tree.  Returns `none` if not found
    or if the list length cannot be determined. -/
private partial def findArrayListLen
    {u : Level} {prop : Q(Type u)} {bi : Q(BI $prop)}
    (hypName : Name)
    : ∀ {e : Q($prop)}, Hyps bi e → MetaM (Option Nat)
  | _, .emp _ => return none
  | _, .hyp _ name _ivar _bp ty _ => do
    if name != hypName then return none
    let args := ty.consumeMData.getAppArgs
    if args.size < 3 then return none
    let xs := args[args.size - 1]!
    countListLen xs
  | _, .sep _ _ _ _ lhs rhs => do
    let l ← findArrayListLen hypName lhs
    if l.isSome then return l
    findArrayListLen hypName rhs

end  -- open Iris

-- ─── Effective-address extraction from the WP goal ────────────────────────────

private structure MemGoalInfo where
  instr      : Expr        -- the head instruction expression (after whnf)
  stackAddr  : Expr        -- UInt32 address (load: stack[0], store: stack[1])
  instrOffset: Expr        -- UInt32 offset field of the instruction
  isGlobal   : Bool
  isStore    : Bool        -- true when the instruction is a store (stack top = value, next = addr)
  storeValue : Option Expr -- for stores: the UInt32/UInt64 value being written (stack top)

/-- Extract the instruction, stack address, and instruction offset from the WP goal.

For a load: address is the top stack element.
For a store: address is the second stack element (top is the value being stored).
For globalGet/globalSet: no stack-based address; uses the instruction's index. -/
private def extractMemGoalInfo (goal : MVarId) (predWidth : String) : MetaM MemGoalInfo := do
  let goalTy ← goal.getType >>= instantiateMVars
  let (wpExpr, _) ← unwrapIrisGoal goalTy
  let wpArgs := wpExpr.getAppArgs
  -- wpArgs: [..., s, E, e, Φ]; e is the Wasm expression
  let e ← whnf wpArgs[wpArgs.size - 2]!
  let eArgs := e.getAppArgs
  -- e = Expr.running thread; thread is the last arg
  let thread ← whnf eArgs[eArgs.size - 1]!
  let tArgs := thread.getAppArgs
  -- thread = ThreadState.mk α locals code arity ...
  -- tArgs[2] = code (List Instruction)
  let code ← whnf tArgs[2]!
  let cArgs := code.getAppArgs
  -- code = List.cons α instr rest; cArgs[1] = head instruction
  let instr ← whnf cArgs[1]!
  let instrArgs := instr.getAppArgs
  -- instrOffset = first explicit arg of instruction (UInt32 or Nat for globals)
  let instrOffset := if instrArgs.isEmpty then mkNatLit 0 else instrArgs[0]!
  if predWidth == "global" then
    return { instr, stackAddr := mkNatLit 0, instrOffset, isGlobal := true, isStore := false,
             storeValue := none }
  -- tArgs[1] = Locals; locals.values is the operand stack
  let locals ← whnf tArgs[1]!
  let lArgs := locals.getAppArgs
  let values ← whnf lArgs[2]!   -- operand stack = List Value
  let vArgs := values.getAppArgs
  -- vArgs = [α, head, tail]  (List.cons α head tail)
  let instrName := instr.getAppFn.constName!.getString!
  -- `store8`/`store32`/`store64`/… and `f32Store`/`f64Store`.
  let isStore := instrName.startsWith "store" || instrName.endsWith "Store"
  let stackAddr ←
    if isStore then do
      -- store: top = value being stored, second = address
      let tail ← whnf vArgs[2]!
      let tArgs2 := tail.getAppArgs
      -- tArgs2 = [α, Value.i32 addr, rest]
      let headVal ← whnf tArgs2[1]!
      let headArgs := headVal.getAppArgs
      -- Value.i32 addr → headArgs[0] = addr
      pure (if headArgs.isEmpty then headVal else headArgs[0]!)
    else do
      -- load: top = address
      let headVal ← whnf vArgs[1]!
      let headArgs := headVal.getAppArgs
      pure (if headArgs.isEmpty then headVal else headArgs[0]!)
  -- For store rules, extract the value being written (top of stack) so we can pass it
  -- explicitly as {value := …} to the step theorem, preventing an unresolved implicit
  -- from blocking IntoWand synthesis in iApplyCore.
  let storeValue : Option Expr ←
    if isStore then do
      let headVal ← whnf vArgs[1]!   -- first stack element = Value.i32/i64 <sv>
      let headArgs := headVal.getAppArgs
      pure (if headArgs.size == 1 then some headArgs[0]! else none)
    else pure none
  return { instr, stackAddr, instrOffset, isGlobal := false, isStore, storeValue }

/-- Compute the effective address expression from `MemGoalInfo`.

For non-global memory: `stackAddr + instrOffset`.
For globals: the raw global index from the instruction. -/
private def effectiveAddr (info : MemGoalInfo) : MetaM Expr :=
  if info.isGlobal then
    return info.instrOffset
  else
    mkAppM ``HAdd.hAdd #[info.stackAddr, info.instrOffset]

-- ─── Counting explicit args before the wand ───────────────────────────────────

/-- Count the number of explicit `∀` binders before the first non-`∀` expression
    in a theorem type.  Stops at `let`-bindings (`.letE`) and applications,
    which mark the start of the wand / conclusion. -/
private def countExplicitForalls (ty : Expr) : Nat :=
  match ty with
  | .forallE _ _ body bi =>
    (if bi == .default then 1 else 0) + countExplicitForalls body
  | _ => 0

/-- Number of explicit args the theorem takes before its first `-∗` premise. -/
private def numExplicitArgsBeforeWand (thmName : Name) : MetaM Nat := do
  let some ci := (← getEnv).find? thmName
    | return 0
  return countExplicitForalls ci.type

-- ─── Zero-offset check ────────────────────────────────────────────────────────

/-- True iff `e` is definitionally equal to the additive zero of its type. -/
private def isZeroOffset (e : Expr) : MetaM Bool :=
  withoutModifyingState do
    let ty ← inferType e
    try
      let zero ← mkNumeral ty 0
      isDefEq e zero
    catch _ => return false

-- ─── Array cell focusing ──────────────────────────────────────────────────────

/-- Find index `k` such that `normEffAddr = ptr + stride * UInt32.ofNat k`.
    Tries the fast path (concrete numerals) first; falls back to `isDefEq` iteration.
    Returns `none` if not found within `maxK` iterations. -/
private def findArrayIndex
    (normEffAddr ptr : Expr) (stride : Nat) (maxK : Nat := 1024)
    : MetaM (Option Nat) := do
  -- Fast path: extract concrete nat values and compute k directly
  let tryNat (e : Expr) : MetaM (Option Nat) := do
    try
      let app ← mkAppM ``UInt32.toNat #[e]
      let n   ← reduce app
      if let .lit (.natVal v) := n then return some v else return none
    catch _ => return none
  if let (some ea, some p) := (← tryNat normEffAddr, ← tryNat ptr) then
    if ea >= p && (ea - p) % stride == 0 then return some ((ea - p) / stride)
    else return none
  -- Slow path: iterate k and check structural equality
  let u32Ty    := mkConst ``UInt32
  let strideEx ← mkNumeral u32Ty stride
  for k in List.range maxK do
    let kEx  ← mkAppM ``UInt32.ofNat #[mkNatLit k]
    let cand ← mkAppM ``HAdd.hAdd #[ptr, ← mkAppM ``HMul.hMul #[strideEx, kEx]]
    if ← withoutModifyingState (isDefEq normEffAddr cand) then return some k
  return none

-- ─── `wasm_mem` elaborator ────────────────────────────────────────────────────

/-- Apply one memory or global step rule (TWP or WP modality) using the
ownership hypothesis found in the spatial Iris context.

    wasm_mem [using [lemma₁, …, lemmaₙ]]

1. Identifies the instruction head and looks up its `mem` rule.
2. Extracts the effective address from the WP goal.
3. Optionally normalises both sides of the address comparison with the
   user-supplied `simp only [using …]` lemmas.
4. Scans the spatial Iris context for a matching `pointsTo_u32` /
   `pointsTo_u64` / `pointsTo` / `globalPointsToAt` hypothesis.
5. Selects the `_addr` (zero-offset) variant when the instruction offset is 0.
6. Applies the rule as `iapply (thmName _ sc sc …) $$ HypName` and then
   `iintro HypName` to re-bind the output hypothesis.

Errors (with named messages) on zero or multiple matches, or on `arrayAt` region
predicates that need cell focusing first. -/
@[tactic wasm_mem]
def elabWasmMem : Lean.Elab.Tactic.Tactic := fun stx => do
  -- ── Parse optional `using [lemmas]` ───────────────────────────────────────
  let usingLemmas : Array Name ←
    if stx[1].isNone then pure #[]
    else do
      -- stx[1] is the optional group node for `("using" "[" term,* "]")?`
      -- layout inside the group: [0]="using", [1]="[", [2]=SepBy(term,","), [3]="]"
      let inner := stx[1][0]  -- unwrap the anonymous optional wrapper
      let termsSep := inner[2]  -- the `term,*` SepBy node
      let termArgs := termsSep.getSepArgs
      termArgs.filterMapM fun t => do
        if t.isIdent then return some t.getId
        else
          logWarning m!"wasm_mem using: ignoring non-identifier argument {t}"
          return none
  -- ── Look up the registered mem rule ───────────────────────────────────────
  let goal ← getMainGoal
  let (ctorKey, modality) ← instrHeadKey goal
  let env ← getEnv
  let some entries := getWasmRule env (Name.mkSimple modality) ctorKey
    | throwError "wasm_mem: no rule registered for {ctorKey} \
        (is this instruction registered with `@[wasm_mem_rule …]`?)"
  let some entry := entries.find? fun e => match e.kind with | .mem _ => true | _ => false
    | throwError "wasm_mem: rule for {ctorKey} is a pure rule; use wasm_pure"
  let .mem info := entry.kind | unreachable!
  -- ── Extract effective address and normalise ────────────────────────────────
  -- For non-global rules that have an addr variant, check whether the
  -- instruction offset is zero.  If so we use the _addr theorem (which has
  -- `addr` in its precondition, not `addr + 0`), and the effective address for
  -- hypothesis matching is just `stackAddr`, NOT `stackAddr + 0`.  This avoids
  -- requiring `using [UInt32.add_zero]` on every load/store with offset 0.
  let goalInfo ← extractMemGoalInfo goal info.predWidth
  let useAddrVariant := !goalInfo.isGlobal && info.addrVariantThm != .anonymous
  let isZeroOff ← if useAddrVariant then isZeroOffset goalInfo.instrOffset else pure false
  let rawEffAddr ←
    if useAddrVariant && isZeroOff then
      pure goalInfo.stackAddr   -- addr variant: match against stackAddr, not stackAddr + 0
    else
      effectiveAddr goalInfo
  let normEffAddr ← normWithLemmas rawEffAddr usingLemmas
  -- ── Scan the Iris context for a matching hypothesis ────────────────────────
  let goalTy ← goal.getType >>= instantiateMVars
  let some irisGoal := parseIrisGoal? goalTy
    | throwError "wasm_mem: goal is not in Iris proof mode \
        (run `istart` first, or check that the goal is a TWP/WP entailment)"
  let scanRes     ← scanIrisHyps info.predWidth normEffAddr usingLemmas irisGoal.hyps
  let directCands := scanRes.1
  let arrayCands  := scanRes.2
  -- ── Candidate dispatch ────────────────────────────────────────────────────
  -- Priority: direct matches first, then resolved array candidates.
  let (resolvedArrayCands, oobCands) :
      Array ArrayCandidate × Array (Name × Nat × Nat × Expr) ←
    if directCands.isEmpty then do
      let mut resolved : Array ArrayCandidate := #[]
      let mut oobCands : Array (Name × Nat × Nat × Expr) := #[]
      for arrayCand in arrayCands do
        let stride   := if arrayCand.isU64 then 8 else 4
        let normPtr  ← normWithLemmas arrayCand.ptr usingLemmas
        match ← findArrayIndex normEffAddr normPtr stride with
        | none   => pure ()  -- unresolved
        | some k =>
          let lenOpt ← findArrayListLen arrayCand.hypName irisGoal.hyps
          match lenOpt with
          | some len =>
            if k < len then
              resolved := resolved.push { arrayCand with index := some k }
            else
              oobCands := oobCands.push (arrayCand.hypName, k, len, normPtr)
          | none => resolved := resolved.push { arrayCand with index := some k }
      pure (resolved, oobCands)
    else pure (#[], #[])
  match directCands with
  | [_] => pure ()
  | _ :: _ :: _ =>
    throwError "wasm_mem: ambiguous — multiple {info.predWidth} \
        hypotheses match address {normEffAddr}: {directCands}"
  | [] =>
    match resolvedArrayCands.toList with
    | [_] => pure ()
    | _ :: _ :: _ =>
      let names := resolvedArrayCands.toList.map (·.hypName)
      throwError "wasm_mem: ambiguous — multiple {info.predWidth} \
          hypotheses match address {normEffAddr}: {names}"
    | [] =>
      if arrayCands.isEmpty then
        throwError "wasm_mem: no {info.predWidth} hypothesis found \
            for effective address {normEffAddr}; check the Iris context"
      else if !oobCands.isEmpty then
        let (hName, _, len, normPtr) := oobCands[0]!
        throwError "wasm_mem: address {normEffAddr} is past the end of \
            array region {hName} (base {normPtr}, {len} cells)"
      else
        let first    := arrayCands[0]!
        let stride   : Nat := if first.isU64 then 8 else 4
        let normPtr  ← normWithLemmas first.ptr usingLemmas
        throwError "wasm_mem: address {normEffAddr} lies in array region \
            {first.hypName} (base {normPtr}) but no cell index was found \
            for stride {stride}"
  -- For store rules, precompute the concrete value syntax so we can pass it both to
  -- the array-focus lemma (preventing a syntheticOpaque metavar in _wasm_mem_close) and
  -- to the step theorem's implicit {value} arg (allowing IntoWand synthesis to unify
  -- WP current against the concrete WP goal without leaving ?value unresolved).
  let svSyntaxOpt : Option (TSyntax `term) ←
    if goalInfo.isStore then
      match goalInfo.storeValue with
      | some sv => pure (some (← PrettyPrinter.delab sv))
      | none    => pure none
    else pure none
  -- Exactly one candidate: either a direct pointsTo hyp or an arrayAt/array64At region
  let (hypName, arrayCloseOpt) : Name × Option Name ←
    match directCands with
    | [n] => pure (n, none)
    | _ =>
      -- Single resolved array candidate: focus cell and emit ihave preamble
      let arrayCand := resolvedArrayCands[0]!
      let k         := arrayCand.index.get!
      let arrayHypId := mkIdent arrayCand.hypName
      let cellId     := mkIdent `_wasm_mem_cell
      let closeId    := mkIdent `_wasm_mem_close
      let kTerm      : TSyntax `term := ⟨(Lean.Syntax.mkNumLit (toString k)).raw⟩
      let byDec      : TSyntax `term ←
        `((by first | decide | omega | (simp only [List.length_cons, List.length_nil]; omega)))
      let focusLemma : Name :=
        match arrayCand.isU64, goalInfo.isStore with
        | false, false => ``Wasm.SepLogic.arrayAt_get
        | false, true  => ``Wasm.SepLogic.arrayAt_set
        | true,  false => ``Wasm.SepLogic.array64At_get
        | true,  true  => ``Wasm.SepLogic.array64At_set
      let focusTm  : TSyntax `term := ⟨(mkIdent focusLemma).raw⟩
      -- Pass sv concretely so _wasm_mem_close gets a ground type (no syntheticOpaque mvar).
      let focusApp : TSyntax `term ←
        match goalInfo.isStore, svSyntaxOpt with
        | true, some sv => `($focusTm _ _ _ $kTerm $sv $byDec)
        | true, none    => `($focusTm _ _ _ $kTerm _ $byDec)
        | false, _      => `($focusTm _ _ _ $kTerm $byDec)
      let cellPat  : TSyntax `icasesPat ← `(icasesPat| ⟨$cellId:ident, $closeId:ident⟩)
      let focusPmt : TSyntax `pmTerm    ← `(pmTerm| $focusApp:term $$ $arrayHypId:ident)
      evalTactic (← `(tactic| ihave $cellPat := $focusPmt))
      pure (`_wasm_mem_cell, some `_wasm_mem_close)
  -- ── Choose _addr variant (offset 0) vs general ────────────────────────────
  let thmName : Name :=
    if useAddrVariant && isZeroOff then info.addrVariantThm
    else entry.thmName
  -- ── Count explicit args before the wand ─────────────────────────────────
  let numArgs ← numExplicitArgsBeforeWand thmName
  -- ── Build and evaluate `iapply (thmName _ sc … sc) $$ HypName` ────────────
  let thmIdent : TSyntax `term := ⟨(mkIdent thmName).raw⟩
  let hypIdent  := mkIdent hypName
  let sideCondTac : TSyntax `term ← `((by first | decide | omega))
  let holeTerm  : TSyntax `term ← `(_)
  -- Supply implicit {value} explicitly so IntoWand synthesis can unify WP current
  -- against the concrete WP goal without leaving ?value unresolved.
  let mut appTerm : TSyntax `term := thmIdent
  if let some sv := svSyntaxOpt then
    appTerm ← `($appTerm (value := $sv))
  if numArgs > 0 then
    appTerm ← `($appTerm $holeTerm)          -- arg 0: oldWord (inferred from hypothesis)
    for _ in List.range (numArgs - 1) do
      appTerm ← `($appTerm $sideCondTac)     -- remaining: side conditions
  -- pmTerm:  appTerm $$ HypName
  let pmt : TSyntax `pmTerm ←
    `(pmTerm| $appTerm:term $$ $hypIdent:ident)
  evalTactic (← `(tactic| iapply $pmt))
  -- Partial-WP (`wp`) memory rules guard the continuation with a `▷`
  -- (`▷ P -∗ ▷ (P' -∗ WP …) -∗ WP …`); strip it before re-introducing.
  if modality == "wp" then
    evalTactic (← `(tactic| inext))
  -- ── Re-introduce the output hypothesis ────────────────────────────────────
  -- Build IntroPat programmatically to avoid going through IntroPat.parse,
  -- which rejects a raw ident spliced into introPat position at runtime.
  let biNode  ← `(binderIdent| $hypIdent:ident)
  let icp     : iCasesPat := { ref := hypIdent.raw, case := .one biNode }
  let ip      : IntroPat  := .intro icp
  ProofModeM.runTactic `wasm_mem_iintro fun mvar ig => do
    let pf ← iIntroCore ig.hyps ig.goal [(hypIdent.raw, ip)]
    mvar.assign pf
  -- ── Reassemble array if cell focusing was used ────────────────────────────
  if let some closeName := arrayCloseOpt then
    let arrayCand  := resolvedArrayCands[0]!
    let closeId    := mkIdent closeName
    let cellId     := mkIdent hypName          -- `_wasm_mem_cell after re-intro
    let arrayHypId := mkIdent arrayCand.hypName
    let closePmt   : TSyntax `pmTerm    ← `(pmTerm| $closeId:term $$ $cellId:ident)
    let arrayPat   : TSyntax `icasesPat ← `(icasesPat| $arrayHypId:ident)
    evalTactic (← `(tactic| ihave $arrayPat := $closePmt))
    -- Normalize any List.getElem expressions left in the WP goal by the array focusing.
    evalTactic (← `(tactic| simp (config := { failIfUnchanged := false }) only [List.getElem_cons_succ, List.getElem_cons_zero]))

end CodeLib.Tactics
