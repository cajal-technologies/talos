/- Authors: Abraxas1010 (IAOM / Apoth3osis). -/

import Interpreter.Wasm.SmallStep

/-!
# Pure-core well-formedness and progress

`FrameProgramWellFormed` is a constructive typing/safety witness for the
initial small-step fragment.  Each constructor records the operand/local shape
needed by the next instruction and recursively checks its concrete successor.
It therefore cannot be inhabited by merely asserting that some transition
exists.
-/

namespace Wasm.SmallStep

/-- A complete, well-shaped pure-core instruction stream from a concrete
frame.  The `divUTrap` case is terminal, so its remaining code is unreachable
and needs no recursive witness. -/
inductive FrameProgramWellFormed : Locals → Program → Prop where
  | finish (frame) :
      FrameProgramWellFormed frame []
  | localGet (frame rest i v)
      (hget : frame.get i = some v)
      (hnext : FrameProgramWellFormed
        { frame with values := v :: frame.values } rest) :
      FrameProgramWellFormed frame (.localGet i :: rest)
  | localSet (frame rest i v vs frame')
      (hvalues : frame.values = v :: vs)
      (hset : frame.set? i v = some frame')
      (hnext : FrameProgramWellFormed { frame' with values := vs } rest) :
      FrameProgramWellFormed frame (.localSet i :: rest)
  | const (frame rest v)
      (hnext : FrameProgramWellFormed
        { frame with values := .i32 v :: frame.values } rest) :
      FrameProgramWellFormed frame (.const v :: rest)
  | constI64 (frame rest v)
      (hnext : FrameProgramWellFormed
        { frame with values := .i64 v :: frame.values } rest) :
      FrameProgramWellFormed frame (.constI64 v :: rest)
  | add (frame rest a b vs)
      (hvalues : frame.values = .i32 a :: .i32 b :: vs)
      (hnext : FrameProgramWellFormed
        { frame with values := .i32 (a + b) :: vs } rest) :
      FrameProgramWellFormed frame (.add :: rest)
  | sub (frame rest a b vs)
      (hvalues : frame.values = .i32 a :: .i32 b :: vs)
      (hnext : FrameProgramWellFormed
        { frame with values := .i32 (b - a) :: vs } rest) :
      FrameProgramWellFormed frame (.sub :: rest)
  | mul (frame rest a b vs)
      (hvalues : frame.values = .i32 a :: .i32 b :: vs)
      (hnext : FrameProgramWellFormed
        { frame with values := .i32 (a * b) :: vs } rest) :
      FrameProgramWellFormed frame (.mul :: rest)
  | divU (frame rest a b vs)
      (hvalues : frame.values = .i32 b :: .i32 a :: vs)
      (hnz : b ≠ 0)
      (hnext : FrameProgramWellFormed
        { frame with values := .i32 (a / b) :: vs } rest) :
      FrameProgramWellFormed frame (.divU :: rest)
  | divUTrap (frame rest a vs)
      (hvalues : frame.values = .i32 0 :: .i32 a :: vs) :
      FrameProgramWellFormed frame (.divU :: rest)

/-- Well-formed terminal expressions are unconditional; running expressions
must carry a structurally valid pure-core program. -/
def WellFormed (config : Config α) : Prop :=
  match config.expr with
  | .done _ | .trapped _ => True
  | .running thread => FrameProgramWellFormed thread.frame thread.code

/-- A nonterminal well-formed configuration has a concrete relational
successor, and that successor remains well formed. -/
private theorem wellFormed_running_step
    (store : MachineStore α) (frame : Locals) (code : Program)
    (hwf : FrameProgramWellFormed frame code) :
    ∃ out,
      Step { expr := .running { frame, code }, store } out ∧
      WellFormed out.next := by
  cases hwf with
  | finish =>
      refine ⟨_, .finish store frame, ?_⟩
      trivial
  | localGet frame rest i v hget hnext =>
      refine ⟨_, .localGet store frame rest i v hget, ?_⟩
      exact hnext
  | localSet frame rest i v vs frame' hvalues hset hnext =>
      refine ⟨_, .localSet store frame rest i v vs frame' hvalues hset, ?_⟩
      exact hnext
  | const frame rest v hnext =>
      refine ⟨_, .const store frame rest v, ?_⟩
      exact hnext
  | constI64 frame rest v hnext =>
      refine ⟨_, .constI64 store frame rest v, ?_⟩
      exact hnext
  | add frame rest a b vs hvalues hnext =>
      refine ⟨_, .add store frame rest a b vs hvalues, ?_⟩
      exact hnext
  | sub frame rest a b vs hvalues hnext =>
      refine ⟨_, .sub store frame rest a b vs hvalues, ?_⟩
      exact hnext
  | mul frame rest a b vs hvalues hnext =>
      refine ⟨_, .mul store frame rest a b vs hvalues, ?_⟩
      exact hnext
  | divU frame rest a b vs hvalues hnz hnext =>
      refine ⟨_, .divU store frame rest a b vs hvalues hnz, ?_⟩
      exact hnext
  | divUTrap frame rest a vs hvalues =>
      refine ⟨_, .divUTrap store frame rest a vs hvalues, ?_⟩
      trivial

theorem wellFormed_progress {config : Config α} :
    WellFormed config → ¬ Terminal config → ∃ out, Step config out := by
  intro hwf hterminal
  rcases config with ⟨expr, store⟩
  cases expr with
  | done values => exact False.elim (hterminal trivial)
  | trapped reason => exact False.elim (hterminal trivial)
  | running thread =>
      rcases thread with ⟨frame, code⟩
      exact (wellFormed_running_step store frame code hwf).imp fun _ h => h.1

theorem step_preserves_wellFormed {config : Config α} {out : StepResult α} :
    WellFormed config → Step config out → WellFormed out.next := by
  intro hwf hstep
  rcases config with ⟨expr, store⟩
  cases expr with
  | done values =>
      exact False.elim
        (terminal_no_step
          (config := { expr := .done values, store }) trivial ⟨out, hstep⟩)
  | trapped reason =>
      exact False.elim
        (terminal_no_step
          (config := { expr := .trapped reason, store }) trivial ⟨out, hstep⟩)
  | running thread =>
      rcases thread with ⟨frame, code⟩
      obtain ⟨expected, hexpected, hwfExpected⟩ :=
        wellFormed_running_step store frame code hwf
      have : out = expected := step_deterministic hstep hexpected
      simpa [this] using hwfExpected

end Wasm.SmallStep
