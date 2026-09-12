import CodeLib.SepLogic.SmallStepLanguage

/-!
# State-sensitive costs on authoritative Wasm traces

`CostedSteps` annotates `SmallStep.Step`; it neither executes instructions nor
changes the semantics. Erasure gives the existing `Steps`, including its Iris
`NSteps` bridge. A total-WP adequacy result can therefore be annotated after
adequacy, preserving its exact terminal store and functional postcondition.

That annotation alone gives no quantitative upper bound. `with_cost_bound`
requires a separately proved potential invariant for every reachable step.
Existing total WPs discard this information, so this file does not claim that
their existing proofs automatically establish a budget or a complexity bound.

`byteWork` is a concrete single-memory Wasm work model: each semantic step costs
one, bulk byte instructions additionally cost their requested length, successful
primary-memory growth costs the added byte capacity, and host steps use an
explicit state-sensitive byte-transfer charge. Charging a trapping bulk request
its requested length is intentionally conservative. This is not wall-clock time
or a complete cost model for GC/table operations. Host clients must supply and
justify their actual transfer charge before using it for a whole-program bound.
-/

namespace Wasm.SmallStep

/-- A charge may inspect operands, the executed instruction, and the state
change, including host transfers and successful memory growth. -/
abbrev StepCost (α : Type) := Config α → StepKind → Config α → Nat

/-- Derived cost annotation of the existing authoritative transition relation. -/
inductive CostedSteps (charge : StepCost α) :
    Config α → List StepKind → Config α → Nat → Prop where
  | refl (config) : CostedSteps charge config [] config 0
  | cons (head : Step config kind next)
      (tail : CostedSteps charge next trace final amount) :
      CostedSteps charge config (kind :: trace) final
        (charge config kind next + amount)

variable {α : Type} {charge : StepCost α}
  {config next middle final final₁ final₂ : Config α}
  {kind : StepKind} {trace trace₁ trace₂ : List StepKind}
  {amount amount₁ amount₂ : Nat}
  {post : ObservableOutcome → MachineStore α → Prop}

namespace CostedSteps

theorem erase (execution : CostedSteps charge config trace final amount) :
    Steps config trace final := by
  induction execution with
  | refl => exact .refl _
  | cons head _ ih => exact .cons head ih

theorem single (head : Step config kind next) :
    CostedSteps charge config [kind] next (charge config kind next) := by
  simpa using CostedSteps.cons (charge := charge) head (.refl next)

theorem trans
    (first : CostedSteps charge config trace₁ middle amount₁)
    (second : CostedSteps charge middle trace₂ final amount₂) :
    CostedSteps charge config (trace₁ ++ trace₂) final (amount₁ + amount₂) := by
  induction first with
  | refl => simpa using second
  | cons head _ ih =>
      simpa [Nat.add_assoc] using CostedSteps.cons head (ih second)

/-- Positive charges bound instruction and administrative progress alike. -/
theorem length_le
    (execution : CostedSteps charge config trace final amount)
    (positive : ∀ before kind after, Step before kind after →
      1 ≤ charge before kind after) :
    trace.length ≤ amount := by
  induction execution with
  | refl => simp
  | cons head _ ih =>
      have := positive _ _ _ head
      simp only [List.length_cons]
      omega

/-- The annotation cannot assign different costs to the same authoritative
trace: successor configurations are fixed by Wasm step determinism. -/
theorem amount_unique
    (first : CostedSteps charge config trace final₁ amount₁)
    (second : CostedSteps charge config trace final₂ amount₂) :
    amount₁ = amount₂ := by
  induction first generalizing final₂ amount₂ with
  | refl => cases second; rfl
  | cons head tail ih =>
      cases second with
      | cons otherHead otherTail =>
          obtain ⟨_, rfl⟩ := step_deterministic head otherHead
          rw [ih otherTail]

/-- A compositional potential invariant bounds an already justified execution.
The invariant need only cover reachable states, not every machine configuration.
The residual potential is retained so callers can compose local budgets. -/
theorem potential_bound
    (execution : CostedSteps charge config trace final amount)
    (invariant : Config α → Prop) (potential : Config α → Nat)
    (initial : invariant config)
    (advance : ∀ before kind after, invariant before → Step before kind after →
      invariant after ∧ charge before kind after + potential after ≤ potential before) :
    invariant final ∧ amount + potential final ≤ potential config := by
  induction execution with
  | refl => exact ⟨initial, by omega⟩
  | cons head _ ih =>
      obtain ⟨nextInvariant, localBound⟩ := advance _ _ _ initial head
      obtain ⟨finalInvariant, tailBound⟩ := ih nextInvariant
      exact ⟨finalInvariant, by omega⟩

/-- Reuse the existing Iris language correspondence, with the same semantic
step count. Costs do not become Iris observations. -/
theorem to_languageNSteps [TerminalView α Terminal]
    (execution : CostedSteps charge config trace final amount) :
    @Iris.ProgramLogic.Language.NSteps
      (Expr α) Terminal (MachineStore α) StepKind
      TerminalView.canonicalLanguage trace.length
      ([config.expr], config.store) [] ([final.expr], final.store) :=
  execution.erase.to_languageNSteps

end CostedSteps

/-- Every existing finite trace has an annotation; no symbolic execution is
replayed. Existence of a cost is weaker than an upper bound on that cost. -/
theorem Steps.with_cost (execution : Steps config trace final)
    (charge : StepCost α) :
    ∃ amount, CostedSteps charge config trace final amount := by
  induction execution with
  | refl => exact ⟨0, .refl _⟩
  | cons head _ ih =>
      obtain ⟨amount, tail⟩ := ih
      exact ⟨_, .cons head tail⟩

/-- Attach costs to the exact terminal execution delivered by total adequacy. -/
theorem TerminatesWithOutcome.with_cost
    (execution : TerminatesWithOutcome config post) (charge : StepCost α) :
    ∃ trace outcome store amount,
      CostedSteps charge config trace ⟨outcome.toExpr, store⟩ amount ∧
      post outcome store := by
  obtain ⟨trace, outcome, store, steps, result⟩ := execution
  obtain ⟨amount, annotated⟩ := steps.with_cost charge
  exact ⟨trace, outcome, store, amount, annotated, result⟩

/-- A total adequacy proof and an independently established potential invariant
give functional correctness and a cost bound on one and the same execution. -/
theorem TerminatesWithOutcome.with_cost_bound
    (execution : TerminatesWithOutcome config post) (charge : StepCost α)
    (invariant : Config α → Prop) (potential : Config α → Nat)
    (initial : invariant config)
    (advance : ∀ before kind after, invariant before → Step before kind after →
      invariant after ∧ charge before kind after + potential after ≤ potential before) :
    ∃ trace outcome store amount,
      CostedSteps charge config trace ⟨outcome.toExpr, store⟩ amount ∧
      post outcome store ∧ amount ≤ potential config := by
  obtain ⟨trace, outcome, store, amount, annotated, result⟩ :=
    execution.with_cost charge
  have bound := (annotated.potential_bound invariant potential initial advance).2
  exact ⟨trace, outcome, store, amount, annotated, result, by omega⟩

/-- Bulk instructions keep their length on top of the operand stack. -/
def operandLength (config : Config α) : Nat :=
  match config.expr with
  | .running thread =>
      match thread.locals.values with
      | .i32 len :: _ => len.toNat
      | .i64 len :: _ => len.toNat
      | _ => 0
  | _ => 0

/-- Concrete byte-work charge. The host callback must describe the concrete
host's transferred bytes; it receives both states and the host function index. -/
def byteWork (hostBytes : Config α → Nat → Config α → Nat) : StepCost α :=
  fun before kind after => 1 +
    match kind with
    | .instruction .memoryCopy | .instruction .memoryFill
    | .instruction (.memoryCopyBetween _ _)
    | .instruction (.memoryInit _) => operandLength before
    | .instruction .memoryGrow =>
        65536 * (after.store.wasm.mem.pages - before.store.wasm.mem.pages)
    | .host index => hostBytes before index after
    | _ => 0

theorem byteWork_positive (hostBytes) (before : Config α) kind after :
    1 ≤ byteWork hostBytes before kind after := by
  simp only [byteWork]
  omega

/-- Symbolic successful memory.copy consumer. The bulk copy costs its entire
byte length even though the authoritative semantics executes it atomically. -/
theorem memoryCopy32_costed
    (store : MachineStore α) (params localValues values : List Value)
    (code : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (destination source len : UInt32)
    (hdestination : destination.toNat + len.toNat ≤ store.wasm.mem.pages * 65536)
    (hsource : source.toNat + len.toNat ≤ store.wasm.mem.pages * 65536)
    (hostBytes : Config α → Nat → Config α → Nat) :
    CostedSteps (byteWork hostBytes)
      ⟨.running ⟨⟨params, localValues,
        .i32 len :: .i32 source :: .i32 destination :: values⟩,
        .memoryCopy :: code, arity, remainder, controls, calls⟩, store⟩
      [.instruction .memoryCopy]
      ⟨.running ⟨⟨params, localValues, values⟩,
        code, arity, remainder, controls, calls⟩,
        { store with wasm := { store.wasm with
          mem := store.wasm.mem.copy destination.toNat source.toNat len.toNat } }⟩
      (1 + len.toNat) := by
  exact CostedSteps.single (Step.memoryCopy32 hdestination hsource)

/-- A symbolic successful growth costs its added byte capacity, not one unit
per memory.grow regardless of size. The physical cap is the store's own cap. -/
theorem memoryGrow32_costed
    (store : MachineStore α) (params localValues values : List Value)
    (code : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (delta : UInt32)
    (hcap : store.wasm.mem.pages + delta.toNat ≤
      store.wasm.memoryCap store.runtime.currentModule 0)
    (hostBytes : Config α → Nat → Config α → Nat) :
    CostedSteps (byteWork hostBytes)
      ⟨.running ⟨⟨params, localValues, .i32 delta :: values⟩,
        .memoryGrow :: code, arity, remainder, controls, calls⟩, store⟩
      [.instruction .memoryGrow]
      ⟨.running ⟨⟨params, localValues, .i32 store.wasm.mem.pages.toUInt32 :: values⟩,
        code, arity, remainder, controls, calls⟩,
        { store with wasm := { store.wasm with mem :=
          { store.wasm.mem with pages := store.wasm.mem.pages + delta.toNat } } }⟩
      (1 + 65536 * delta.toNat) := by
  have grow := Step.memoryGrowSuccess (α := α)
    (params := params) (localValues := localValues) (values := values)
    (code := code) (arity := arity) (remainder := remainder)
    (controls := controls) (calls := calls)
    (show store.wasm.mem.grow delta
      (store.wasm.memoryCap store.runtime.currentModule 0) =
      some ({ store.wasm.mem with pages := store.wasm.mem.pages + delta.toNat },
        store.wasm.mem.pages) by simp [Mem.grow, hcap])
  simpa [byteWork, setMemory_eq] using
    CostedSteps.single (charge := byteWork hostBytes) grow

end Wasm.SmallStep
