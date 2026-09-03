import Interpreter.Wasm.SmallStep

/-!
# Entering a module through its host

`HostEnv` says what a host *does*; this file says how a module is *started*
under one, and what it means for that run to finish.  Both definitions are
parametric in the host state `α`, exactly as `HostFn`, `HostEnv`, `HostSpec`
and `HostContract` already are, so a host introduced later reuses them
unchanged.

`RunsWith` is the zero-argument shape used by the existing byte-stream
specifications. `RunsExportWith` is its general exported-call counterpart: a
specification packages the initial Wasm store and arguments as an `ExportCall`,
then observes returned Wasm values and the final store through `ExportReturn`.
Fuel and the machine's administrative bookkeeping stay inside both relations.

These definitions cannot live in `Interpreter/Wasm/Host.lean` beside `HostEnv`
itself: that file is imported by `Semantics`, which `SmallStep` is built on, so
naming `SmallStep.Config` there would close an import cycle.
-/

namespace Wasm

/-! ## Semantic exported calls -/

/-- Everything supplied by an embedder when invoking a Wasm export. Retaining
the initial Wasm store is necessary for semantic inputs represented in linear
memory, tables or globals. A client-facing specification normally hides this
representation behind its own `args : Input → ExportCall α` function. -/
structure ExportCall (α : Type) where
  initial : Store α
  /-- Entry operands in the interpreter's stack order (top first). A semantic
  `args` adapter hides this ABI detail from the public proposition. -/
  arguments : List Value

/-- Construct the common case from parameters in source-function order: the
module's canonical initial Wasm store, a chosen host state, and explicit Wasm
parameters. This constructor reverses them into the interpreter operand-stack
order carried by `ExportCall.arguments`. -/
def ExportCall.ofHost [Inhabited α] (m : Module) (host : α)
    (parameters : List Value := []) : ExportCall α :=
  { initial := { (m.initialStore : Store α) with host := host }
    arguments := parameters.reverse }

/-- The observable normal result of an exported call. A client-facing
specification normally hides this representation behind a semantic
`result : Output → ExportReturn α → Prop` predicate. -/
structure ExportReturn (α : Type) where
  /-- Returned values in interpreter operand-stack order (top first). -/
  values : List Value
  final : Store α

/-- A normal return or structural trap together with the final Wasm store.
This keeps exceptional specifications honest: an allocator OOM, for example,
is not encoded as a successful `ExportReturn`. -/
structure ExportOutcome (α : Type) where
  outcome : SmallStep.ObservableOutcome
  final : Store α

/-- Runtime values supplied at an exported-call boundary must match the
function's declared parameter types. Precise GC reference types consult the
initial store, just as the operational `ref.test`/`ref.cast` machinery does. -/
private def exportValueMatches (m : Module) (st : Store α) :
    Value → ValueType → Bool
  | .i32 _, .i32 => true
  | .i64 _, .i64 => true
  | .f32 _, .f32 => true
  | .f64 _, .f64 => true
  | .funcref _, .funcref => true
  | .externref _, .externref => true
  | .v128 _, .v128 => true
  | .exnref _, .exnref => true
  | .anyref _, .anyref => true
  | value, .ref nullable heap => gcRefMatches m st nullable heap value
  | _, _ => false

private def exportArgumentsMatch (m : Module) (call : ExportCall α)
    (signature : FuncType) : Bool :=
  (call.arguments.reverse.zip signature.params).all fun pair =>
    exportValueMatches m call.initial pair.1 pair.2

/-- Evidence that a named export exists and declares no Wasm parameters.
Concrete generated modules normally discharge this with `native_decide`. -/
def ZeroArgumentExport (m : Module) (op : String) : Prop :=
  (match m.findExport op with
   | none => false
   | some entry =>
       match m.funcSig? entry with
       | none => false
       | some signature => signature.params.isEmpty) = true

instance (m : Module) (op : String) : Decidable (ZeroArgumentExport m op) := by
  unfold ZeroArgumentExport
  infer_instance

/-- Initialize `m` at its export named `op` with explicit Wasm arguments,
running under `env` from the call's initial Wasm store. `none` when the export
cannot be entered.

Unlike the lower-level initializer, this embedder-facing boundary rejects the
wrong number or types of arguments rather than treating extras as a caller
operand-stack remainder. -/
def startExportConfig? [Inhabited α] (env : HostEnv α) (m : Module)
    (op : String) (call : ExportCall α) : Option (SmallStep.Config α) := do
  let entry ← m.findExport op
  let signature ← m.funcSig? entry
  guard (call.arguments.length == signature.params.length)
  guard (exportArgumentsMatch m call signature)
  (SmallStep.initConfig
    { module := m, host := env }
    entry call.initial
    call.arguments).toOption

/-- Total correctness for a parameterized exported call, observing both its
returned Wasm values and final store. A module-local abbreviation can hide
`env` and `m`, giving public specifications the uniform surface
`Runs "op" (args input) (result output)`. -/
def RunsExportWith [Inhabited α] (env : HostEnv α) (m : Module) (op : String)
    (call : ExportCall α) (post : ExportReturn α → Prop) : Prop :=
  ∃ config,
    startExportConfig? env m op call = some config ∧
    SmallStep.TerminatesWith config (fun values final =>
      post { values := values, final := final.wasm })

/-- Two successful specifications of the same exported call observe one common
return. Clients combine this with functionality of their semantic `result`
adapter to identify semantic outputs without exposing machine configurations. -/
theorem RunsExportWith.deterministic
    {α : Type} [Inhabited α] {env : HostEnv α} {m : Module} {op : String}
    {call : ExportCall α}
    {firstPost secondPost : ExportReturn α → Prop}
    (first : RunsExportWith env m op call firstPost)
    (second : RunsExportWith env m op call secondPost) :
    ∃ returned, firstPost returned ∧ secondPost returned := by
  rcases first with
    ⟨firstConfig, firstStart, firstTrace, firstValues, firstStore,
      firstSteps, hfirst⟩
  rcases second with
    ⟨secondConfig, secondStart, secondTrace, secondValues, secondStore,
      secondSteps, hsecond⟩
  rw [firstStart] at secondStart
  injection secondStart with configEq
  subst secondConfig
  obtain ⟨rfl, rfl⟩ :=
    SmallStep.steps_done_deterministic firstSteps secondSteps
  exact ⟨{ values := firstValues, final := firstStore.wasm }, hfirst, hsecond⟩

/-- Specialized determinism when both postconditions name an exact raw
return. -/
theorem RunsExportWith.return_unique
    {α : Type} [Inhabited α] {env : HostEnv α} {m : Module} {op : String}
    {call : ExportCall α} {firstReturn secondReturn : ExportReturn α}
    (first : RunsExportWith env m op call (· = firstReturn))
    (second : RunsExportWith env m op call (· = secondReturn)) :
    firstReturn = secondReturn := by
  obtain ⟨returned, hfirst, hsecond⟩ := first.deterministic second
  exact hfirst.symm.trans hsecond

/-- Outcome-valued total correctness for a parameterized exported call. This
is the counterpart of `RunsExportWith` for specifications whose legitimate
terminal behavior includes a structural trap such as the distinguished OOM
host signal. -/
def RunsExportWithOutcome [Inhabited α]
    (env : HostEnv α) (m : Module) (op : String)
    (call : ExportCall α) (post : ExportOutcome α → Prop) : Prop :=
  ∃ config,
    startExportConfig? env m op call = some config ∧
    SmallStep.TerminatesWithOutcome config (fun outcome final =>
      post { outcome := outcome, final := final.wasm })

private theorem observableOutcome_toExpr_injective :
    Function.Injective
      (SmallStep.ObservableOutcome.toExpr :
        SmallStep.ObservableOutcome → SmallStep.Expr α) := by
  intro first second heq
  cases first <;> cases second <;>
    simp_all [SmallStep.ObservableOutcome.toExpr]

/-- Two total outcome specifications of the same exported call observe one
common terminal outcome and final store. -/
theorem RunsExportWithOutcome.deterministic
    {α : Type} [Inhabited α] {env : HostEnv α} {m : Module} {op : String}
    {call : ExportCall α}
    {firstPost secondPost : ExportOutcome α → Prop}
    (first : RunsExportWithOutcome env m op call firstPost)
    (second : RunsExportWithOutcome env m op call secondPost) :
    ∃ observed, firstPost observed ∧ secondPost observed := by
  rcases first with
    ⟨firstConfig, firstStart, firstTrace, firstOutcome, firstStore,
      firstSteps, hfirst⟩
  rcases second with
    ⟨secondConfig, secondStart, secondTrace, secondOutcome, secondStore,
      secondSteps, hsecond⟩
  rw [firstStart] at secondStart
  injection secondStart with configEq
  subst secondConfig
  have firstTerminal (kind : SmallStep.StepKind)
      (next : SmallStep.Config α) :
      ¬ SmallStep.Step
        ⟨firstOutcome.toExpr, firstStore⟩ kind next := by
    cases firstOutcome with
    | done => exact SmallStep.done_terminal
    | trapped => exact SmallStep.trapped_terminal
  have secondTerminal (kind : SmallStep.StepKind)
      (next : SmallStep.Config α) :
      ¬ SmallStep.Step
        ⟨secondOutcome.toExpr, secondStore⟩ kind next := by
    cases secondOutcome with
    | done => exact SmallStep.done_terminal
    | trapped => exact SmallStep.trapped_terminal
  have finalEq := SmallStep.steps_irreducible_deterministic
    firstSteps secondSteps firstTerminal secondTerminal
  obtain ⟨exprEq, storeEq⟩ := SmallStep.Config.mk.inj finalEq
  have outcomeEq := observableOutcome_toExpr_injective exprEq
  subst secondOutcome
  have storesEqual : firstStore = secondStore := storeEq
  subst secondStore
  exact
    ⟨{ outcome := firstOutcome, final := firstStore.wasm }, hfirst, hsecond⟩

/-- Partial correctness for a parameterized exported call's normal returns.
It constrains every finite successful execution and deliberately makes no
termination claim; structural traps are outside this predicate. -/
def PartiallyRunsExportWith [Inhabited α]
    (env : HostEnv α) (m : Module) (op : String)
    (call : ExportCall α) (post : ExportReturn α → Prop) : Prop :=
  ∃ config,
    startExportConfig? env m op call = some config ∧
    SmallStep.PartiallyMeets config (fun values final =>
      post { values := values, final := final.wasm })

/-- Outcome-complete partial correctness for a parameterized exported call.
Every finite normal return or structural trap must satisfy `post`, while
divergence remains permitted. -/
def PartiallyRunsExportWithOutcome [Inhabited α]
    (env : HostEnv α) (m : Module) (op : String)
    (call : ExportCall α) (post : ExportOutcome α → Prop) : Prop :=
  ∃ config,
    startExportConfig? env m op call = some config ∧
    SmallStep.PartiallyMeetsOutcome config (fun outcome final =>
      post { outcome := outcome, final := final.wasm })

/-- Initialize `m` at its export named `op`, running under `env` from host
state `initial` over the module's own initial memory, globals and tables.
`none` when `m` exports no such name, or when the entry point that name
resolves to cannot be entered. -/
def startConfig? [Inhabited α] (env : HostEnv α) (m : Module) (op : String)
    (initial : α) : Option (SmallStep.Config α) := do
  let entry ← m.findExport op
  (SmallStep.initConfig
    { module := m, host := env }
    entry { (m.initialStore : Store α) with host := initial } []).toOption

/-- On an actual zero-argument export, the general exported-call initializer
specialized through `ExportCall.ofHost` is exactly the established initializer.
This is the compatibility seam used to reuse existing stream proofs. -/
theorem startExportConfig?_ofHost_zero
    {α : Type} [Inhabited α] {env : HostEnv α} {m : Module} {op : String}
    {initial : α}
    (hzero : ZeroArgumentExport m op) :
    startExportConfig? env m op (ExportCall.ofHost m initial) =
      startConfig? env m op initial := by
  unfold ZeroArgumentExport at hzero
  cases hexport : m.findExport op with
  | none => simp [hexport] at hzero
  | some entry =>
      cases hsignature : m.funcSig? entry with
      | none => simp [hexport, hsignature] at hzero
      | some signature =>
          have hparams : signature.params = [] := by
            cases hparams : signature.params with
            | nil => rfl
            | cons head tail =>
                simp [hexport, hsignature, hparams] at hzero
          simp [startExportConfig?, startConfig?, ExportCall.ofHost, hexport,
            hsignature, hparams, exportArgumentsMatch]
          rfl

/-- Initialize a zero-argument export as an actual Wasm `call` instruction.
Unlike `startConfig?`, which enters a local function body directly, this shape
is suitable for applying a call-site contract to the exported function.  The
callee's result arity is recovered from the ordinary initializer so this
remains faithful to the selected export. -/
def startCallConfig? [Inhabited α] (env : HostEnv α) (m : Module)
    (op : String) (initial : α) : Option (SmallStep.Config α) := do
  let entry ← m.findExport op
  let direct ← (SmallStep.initConfig
    { module := m, host := env }
    entry { (m.initialStore : Store α) with host := initial } []).toOption
  let resultArity ← match direct.expr with
    | .running thread => some thread.resultArity
    | _ => none
  some
    { expr := .running
        { locals := {}
          code := [.call entry]
          resultArity
          callerRemainder := [] }
      store := direct.store }

/-- Export `op` of `m`, started under `env` in host state `initial`, terminates
having returned no values and left a host state satisfying `post`. -/
def RunsWith [Inhabited α] (env : HostEnv α) (m : Module) (op : String)
    (initial : α) (post : α → Prop) : Prop :=
  ∃ config,
    startConfig? env m op initial = some config ∧
    SmallStep.TerminatesWith config (fun values final =>
      values = [] ∧ post final.wasm.host)

/-- Two successful zero-argument runs from the same host state observe one
common final host state. -/
theorem RunsWith.deterministic
    {α : Type} [Inhabited α] {env : HostEnv α} {m : Module} {op : String}
    {initial : α} {firstPost secondPost : α → Prop}
    (first : RunsWith env m op initial firstPost)
    (second : RunsWith env m op initial secondPost) :
    ∃ final, firstPost final ∧ secondPost final := by
  rcases first with
    ⟨firstConfig, firstStart, firstTrace, firstValues, firstStore,
      firstSteps, _, hfirst⟩
  rcases second with
    ⟨secondConfig, secondStart, secondTrace, secondValues, secondStore,
      secondSteps, _, hsecond⟩
  rw [firstStart] at secondStart
  injection secondStart with configEq
  subst secondConfig
  obtain ⟨rfl, rfl⟩ :=
    SmallStep.steps_done_deterministic firstSteps secondSteps
  exact ⟨firstStore.wasm.host, hfirst, hsecond⟩

/-- Re-express an established zero-argument normal execution through the
general exported-call interface without changing or replaying its trace. -/
theorem RunsWith.toRunsExportWith
    {α : Type} [Inhabited α] {env : HostEnv α} {m : Module} {op : String}
    {initial : α} {post : α → Prop}
    (hzero : ZeroArgumentExport m op)
    (run : RunsWith env m op initial post) :
    RunsExportWith env m op (ExportCall.ofHost m initial)
      (fun returned => returned.values = [] ∧ post returned.final.host) := by
  rcases run with ⟨config, hstart, execution⟩
  refine ⟨config, ?_, execution⟩
  rw [startExportConfig?_ofHost_zero hzero]
  exact hstart

/-- Lift an established zero-argument normal execution into the total
outcome-valued interface. -/
theorem RunsWith.toRunsExportWithOutcome
    {α : Type} [Inhabited α] {env : HostEnv α} {m : Module} {op : String}
    {initial : α} {post : α → Prop}
    (hzero : ZeroArgumentExport m op)
    (run : RunsWith env m op initial post) :
    RunsExportWithOutcome env m op (ExportCall.ofHost m initial)
      (fun observed =>
        observed.outcome = .done [] ∧ post observed.final.host) := by
  rcases run with
    ⟨config, hstart, trace, values, final, steps, hvalues, hpost⟩
  subst values
  refine ⟨config, ?_, trace, .done [], final, steps, rfl, hpost⟩
  rw [startExportConfig?_ofHost_zero hzero]
  exact hstart

/-- Export `op` of `m`, started under `env` in host state `initial`, reaches
the structural trap `reason` with a host state satisfying `post`.

This is the exceptional-outcome analogue of `RunsWith`: both predicates hide
linear memory and administrative machine state while retaining a finite-trace
termination claim. -/
def TrapsWithHost [Inhabited α] (env : HostEnv α) (m : Module) (op : String)
    (initial : α) (reason : SmallStep.TrapReason) (post : α → Prop) : Prop :=
  ∃ config,
    startConfig? env m op initial = some config ∧
    SmallStep.TrapsWith config reason (fun final => post final.wasm.host)

/-- Lift an established zero-argument structural trap into the total
outcome-valued exported-call interface. -/
theorem TrapsWithHost.toRunsExportWithOutcome
    {α : Type} [Inhabited α] {env : HostEnv α} {m : Module} {op : String}
    {initial : α} {reason : SmallStep.TrapReason} {post : α → Prop}
    (hzero : ZeroArgumentExport m op)
    (run : TrapsWithHost env m op initial reason post) :
    RunsExportWithOutcome env m op (ExportCall.ofHost m initial)
      (fun observed =>
        observed.outcome = .trapped reason ∧ post observed.final.host) := by
  rcases run with ⟨config, hstart, trace, final, steps, hpost⟩
  refine ⟨config, ?_, trace, .trapped reason, final, steps, rfl, hpost⟩
  rw [startExportConfig?_ofHost_zero hzero]
  exact hstart

/-- Partial correctness of a zero-argument exported call, observing both
normal completion and structural traps while hiding the final machine store.
This predicate intentionally makes no termination claim. -/
def PartiallyRunsWithOutcome [Inhabited α]
    (env : HostEnv α) (m : Module) (op : String)
    (initial : α) (post : SmallStep.ObservableOutcome → α → Prop) : Prop :=
  ∃ config,
    startCallConfig? env m op initial = some config ∧
    SmallStep.PartiallyMeetsOutcome config
      (fun outcome final => post outcome final.wasm.host)

end Wasm
