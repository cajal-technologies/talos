/- Authors: Abraxas1010 (IAOM / Apoth3osis). -/

import Interpreter.Wasm.Semantics

/-!
# Observation-labelled small-step semantics

This module starts the relational small-step migration with a deliberately
small, complete vertical slice.  `Step` is the authoritative semantics;
`step?` is a separate executable presentation, with soundness and completeness
proved below.  The slice covers constants, locals, i32 addition/subtraction/
multiplication, and unsigned division (including its trapping case).

The transition result already has the shape required by iris-lean: a list of
observations and a list of spawned expressions.  Both are empty for this
single-threaded, host-free fragment.
-/

namespace Wasm.SmallStep

/-- Whether a transition executes a Wasm instruction or only rearranges the
abstract machine. -/
inductive StepKind where
  | instruction
  | administrative
deriving Repr, Inhabited, DecidableEq, BEq

/-- External events emitted by Wasm execution.

The pure-core slice has no event constructors.  Making the type empty is
intentional: an observation can only be introduced together with the semantic
transition that emits it. -/
inductive WasmObservation
deriving Repr, DecidableEq, BEq

/-- A transition label.  Lists are used because iris-lean concatenates the
observations emitted by primitive steps. -/
structure StepLabel where
  kind : StepKind
  observations : List WasmObservation
deriving Repr, DecidableEq

/-- Structured traps supported by the initial small-step fragment. -/
inductive TrapReason where
  | integerDivideByZero
deriving Repr, Inhabited, DecidableEq, BEq

/-- Per-execution state.  The existing `Locals.values` field remains the
operand stack, while `code` is the not-yet-executed instruction stream. -/
structure ThreadState where
  frame : Locals
  code : Program
deriving Repr, Inhabited

/-- Immutable instantiated metadata.  The pure-core fragment performs no
module lookup, so the initial carrier has no fields.  Future instruction
families extend this structure rather than reintroducing `Module` as a
parameter to `Step`. -/
structure RuntimeEnv where
deriving Repr, Inhabited

/-- Iris-facing state split: immutable runtime metadata and the existing
physical Wasm store. -/
structure MachineStore (α : Type) where
  runtime : RuntimeEnv
  physical : Store α
deriving Repr

/-- Small-step expressions.  Validation/internal errors are deliberately not
semantic expressions: malformed running states are stuck and are rejected by
the checked iterator. -/
inductive Expr where
  | running (thread : ThreadState)
  | done (values : List Value)
  | trapped (reason : TrapReason)
deriving Repr

structure Config (α : Type) where
  expr : Expr
  store : MachineStore α
deriving Repr

structure StepResult (α : Type) where
  label : StepLabel
  next : Config α
  spawned : List Expr
deriving Repr

def instructionLabel : StepLabel :=
  { kind := .instruction, observations := [] }

def administrativeLabel : StepLabel :=
  { kind := .administrative, observations := [] }

def nextConfig (store : MachineStore α) (frame : Locals)
    (code : Program) : Config α :=
  { expr := .running { frame, code }, store }

def instructionResult (store : MachineStore α) (frame : Locals)
    (code : Program) : StepResult α :=
  { label := instructionLabel
    next := nextConfig store frame code
    spawned := [] }

def trapResult (store : MachineStore α) (reason : TrapReason) :
    StepResult α :=
  { label := instructionLabel
    next := { expr := .trapped reason, store }
    spawned := [] }

/-- The instruction family owned by this vertical slice. -/
inductive PureCoreInstruction : Instruction → Prop where
  | localGet (i) : PureCoreInstruction (.localGet i)
  | localSet (i) : PureCoreInstruction (.localSet i)
  | const (v) : PureCoreInstruction (.const v)
  | constI64 (v) : PureCoreInstruction (.constI64 v)
  | add : PureCoreInstruction .add
  | sub : PureCoreInstruction .sub
  | mul : PureCoreInstruction .mul
  | divU : PureCoreInstruction .divU

/-- Authoritative relational semantics for the pure-core slice. -/
inductive Step : Config α → StepResult α → Prop where
  | finish (store frame) :
      Step
        { expr := .running { frame, code := [] }, store }
        { label := administrativeLabel
          next := { expr := .done frame.values, store }
          spawned := [] }
  | localGet (store frame rest i v)
      (hget : frame.get i = some v) :
      Step
        { expr := .running { frame, code := .localGet i :: rest }, store }
        (instructionResult store { frame with values := v :: frame.values } rest)
  | localSet (store frame rest i v vs frame')
      (hvalues : frame.values = v :: vs)
      (hset : frame.set? i v = some frame') :
      Step
        { expr := .running { frame, code := .localSet i :: rest }, store }
        (instructionResult store { frame' with values := vs } rest)
  | const (store frame rest v) :
      Step
        { expr := .running { frame, code := .const v :: rest }, store }
        (instructionResult store
          { frame with values := .i32 v :: frame.values } rest)
  | constI64 (store frame rest v) :
      Step
        { expr := .running { frame, code := .constI64 v :: rest }, store }
        (instructionResult store
          { frame with values := .i64 v :: frame.values } rest)
  | add (store frame rest a b vs)
      (hvalues : frame.values = .i32 a :: .i32 b :: vs) :
      Step
        { expr := .running { frame, code := .add :: rest }, store }
        (instructionResult store
          { frame with values := .i32 (a + b) :: vs } rest)
  | sub (store frame rest a b vs)
      (hvalues : frame.values = .i32 a :: .i32 b :: vs) :
      Step
        { expr := .running { frame, code := .sub :: rest }, store }
        (instructionResult store
          { frame with values := .i32 (b - a) :: vs } rest)
  | mul (store frame rest a b vs)
      (hvalues : frame.values = .i32 a :: .i32 b :: vs) :
      Step
        { expr := .running { frame, code := .mul :: rest }, store }
        (instructionResult store
          { frame with values := .i32 (a * b) :: vs } rest)
  | divU (store frame rest a b vs)
      (hvalues : frame.values = .i32 b :: .i32 a :: vs)
      (hnz : b ≠ 0) :
      Step
        { expr := .running { frame, code := .divU :: rest }, store }
        (instructionResult store
          { frame with values := .i32 (a / b) :: vs } rest)
  | divUTrap (store frame rest a vs)
      (hvalues : frame.values = .i32 0 :: .i32 a :: vs) :
      Step
        { expr := .running { frame, code := .divU :: rest }, store }
        (trapResult store .integerDivideByZero)

/-- Deterministic executable presentation of `Step`.

Unsupported and malformed configurations return `none`; they are not silently
turned into semantic traps. -/
def step? (config : Config α) : Option (StepResult α) :=
  match config.expr with
  | .done _ | .trapped _ => none
  | .running thread =>
    match thread.code with
    | [] =>
        some
          { label := administrativeLabel
            next := { expr := .done thread.frame.values, store := config.store }
            spawned := [] }
    | inst :: rest =>
      match inst with
      | .localGet i =>
          (thread.frame.get i).map fun v =>
            instructionResult config.store
              { thread.frame with values := v :: thread.frame.values } rest
      | .localSet i =>
          match thread.frame.values with
          | v :: vs =>
              (thread.frame.set? i v).map fun frame =>
                instructionResult config.store { frame with values := vs } rest
          | [] => none
      | .const v =>
          some <| instructionResult config.store
            { thread.frame with values := .i32 v :: thread.frame.values } rest
      | .constI64 v =>
          some <| instructionResult config.store
            { thread.frame with values := .i64 v :: thread.frame.values } rest
      | .add =>
          match thread.frame.values with
          | .i32 a :: .i32 b :: vs =>
              some <| instructionResult config.store
                { thread.frame with values := .i32 (a + b) :: vs } rest
          | _ => none
      | .sub =>
          match thread.frame.values with
          | .i32 a :: .i32 b :: vs =>
              some <| instructionResult config.store
                { thread.frame with values := .i32 (b - a) :: vs } rest
          | _ => none
      | .mul =>
          match thread.frame.values with
          | .i32 a :: .i32 b :: vs =>
              some <| instructionResult config.store
                { thread.frame with values := .i32 (a * b) :: vs } rest
          | _ => none
      | .divU =>
          match thread.frame.values with
          | .i32 b :: .i32 a :: vs =>
              if b = 0 then
                some <| trapResult config.store .integerDivideByZero
              else
                some <| instructionResult config.store
                  { thread.frame with values := .i32 (a / b) :: vs } rest
          | _ => none
      | _ => none

theorem step?_sound {config : Config α} {out : StepResult α} :
    step? config = some out → Step config out := by
  intro h
  rcases config with ⟨expr, store⟩
  cases expr with
  | done values => simp [step?] at h
  | trapped reason => simp [step?] at h
  | running thread =>
    rcases thread with ⟨frame, code⟩
    cases code with
    | nil =>
      simp [step?] at h
      subst out
      exact .finish store frame
    | cons inst rest =>
      cases inst with
      | localGet i =>
        simp only [step?, Option.map_eq_some_iff] at h
        obtain ⟨v, hget, rfl⟩ := h
        exact .localGet store frame rest i v hget
      | localSet i =>
        cases hvalues : frame.values with
        | nil => simp [step?, hvalues] at h
        | cons v vs =>
          simp only [step?, hvalues, Option.map_eq_some_iff] at h
          obtain ⟨frame', hset, rfl⟩ := h
          exact .localSet store frame rest i v vs frame' hvalues hset
      | const v =>
        simp [step?] at h
        subst out
        exact .const store frame rest v
      | constI64 v =>
        simp [step?] at h
        subst out
        exact .constI64 store frame rest v
      | add =>
        simp only [step?] at h
        split at h <;> simp_all
        subst out
        apply Step.add
        assumption
      | sub =>
        simp only [step?] at h
        split at h <;> simp_all
        subst out
        apply Step.sub
        assumption
      | mul =>
        simp only [step?] at h
        split at h <;> simp_all
        subst out
        apply Step.mul
        assumption
      | divU =>
        simp only [step?] at h
        split at h <;> try simp_all
        all_goals split at h <;> try simp_all
        all_goals subst out
        all_goals
          first
          | apply Step.divUTrap <;> assumption
          | apply Step.divU <;> assumption
      | _ => simp [step?] at h

theorem step?_complete {config : Config α} {out : StepResult α} :
    Step config out → step? config = some out := by
  intro h
  cases h <;> simp_all [step?, instructionResult, trapResult]

theorem step_iff {config : Config α} {out : StepResult α} :
    step? config = some out ↔ Step config out :=
  ⟨step?_sound, step?_complete⟩

theorem step_deterministic {config : Config α} {out₁ out₂ : StepResult α} :
    Step config out₁ → Step config out₂ → out₁ = out₂ := by
  intro h₁ h₂
  have hs₁ := step?_complete h₁
  have hs₂ := step?_complete h₂
  rw [hs₁] at hs₂
  exact Option.some.inj hs₂

def Terminal (config : Config α) : Prop :=
  match config.expr with
  | .done _ | .trapped _ => True
  | .running _ => False

theorem terminal_no_step {config : Config α} :
    Terminal config → ¬ ∃ out, Step config out := by
  intro hterminal ⟨out, hstep⟩
  have := step?_complete hstep
  cases config with
  | mk expr store =>
    cases expr <;> simp_all [Terminal, step?]

theorem step_observations_empty {config : Config α} {out : StepResult α}
    (h : Step config out) :
    out.label.observations = [] := by
  cases h <;> rfl

theorem administrative_step_observations_empty
    {config : Config α} {out : StepResult α}
    (h : Step config out) (_hkind : out.label.kind = .administrative) :
    out.label.observations = [] :=
  step_observations_empty h

theorem no_spawn_current_fragment {config : Config α} {out : StepResult α}
    (h : Step config out) :
    out.spawned = [] := by
  cases h <;> rfl

theorem runtimeEnv_preserved {config : Config α} {out : StepResult α}
    (h : Step config out) :
    out.next.store.runtime = config.store.runtime := by
  cases h <;> rfl

theorem physicalStore_preserved {config : Config α} {out : StepResult α}
    (h : Step config out) :
    out.next.store.physical = config.store.physical := by
  cases h <;> rfl

theorem instruction_head_step_kind
    {store : MachineStore α} {frame : Locals} {inst : Instruction}
    {rest : Program} {out : StepResult α}
    (h : Step
      { expr := .running { frame, code := inst :: rest }, store } out) :
    out.label.kind = .instruction := by
  cases h <;> rfl

end Wasm.SmallStep
