import Interpreter.Wasm.SpecTest.Run

/-!
# Specification shapes and the verdict table

The verdict for one input depends only on how the run ended, the shape of the
specification (which terminal behaviours it permits), and the executable
postcondition `post`. The table is the same for every problem.
-/

namespace Wasm.SpecTest

open SmallStep

/-- What a specification promises about terminal behaviour. -/
inductive Shape where
  /-- Terminates with a normal return that satisfies `post` (e.g. `gcd_stdio`). -/
  | totalStream
  /-- Terminates, with a normal return satisfying `post` or the designated OOM trap. -/
  | totalDisjunctiveStream
  /-- Every finite run returns normally satisfying `post` or raises the designated
  OOM trap; divergence is permitted (e.g. OOM-aware merge sort). -/
  | partialStream
  /-- Terminates returning values that satisfy `post` (no stream observation). -/
  | valueLevel
deriving BEq, Inhabited

def Shape.ofString? : String → Option Shape
  | "total-stream" => some .totalStream
  | "total-disjunctive-stream" => some .totalDisjunctiveStream
  | "partial-stream" => some .partialStream
  | "value-level" => some .valueLevel
  | _ => none

def Shape.name : Shape → String
  | .totalStream => "total-stream"
  | .totalDisjunctiveStream => "total-disjunctive-stream"
  | .partialStream => "partial-stream"
  | .valueLevel => "value-level"

/-- The verdict for one input. -/
inductive Verdict where
  | pass
  /-- A counterexample; `clause` names what failed. -/
  | fail (clause : String)
  /-- The designated OOM trap, accepted by a disjunctive or partial shape. -/
  | vacuousOom
  /-- Out of fuel under a partial shape, which permits divergence. -/
  | vacuousDivergent
  /-- The unmodified module ran out of its fixed fuel cap under a shape that
  claims termination; reported separately rather than as a counterexample. -/
  | outOfFuelOriginal
  /-- The interpreter itself failed: never a verdict about the program. -/
  | error (message : String)

def Verdict.isFail : Verdict → Bool
  | .fail _ => true
  | _ => false

/-- The run ended with the allocator's distinguished OOM signal: the host trap
carrying `talos.oom` together with the OOM host's typed marker. -/
def Observation.isOom (obs : Observation) : Bool :=
  match obs.termination with
  | .trapped (.host message) => message == OOM.trapMessage && obs.oomRaised
  | _ => false

/-- The uniform verdict table. Stream shapes judge the output bytes of a
normal return with no values; `value-level` hands the returned values to `post`.
`original` marks runs of the unmodified module under its fixed fuel cap. -/
def classify (shape : Shape) (original : Bool) (post : Observation → Bool)
    (obs : Observation) : Verdict :=
  match obs.termination with
  | .internalError message => .error message
  | .outOfFuel =>
    match shape with
    | .partialStream => .vacuousDivergent
    | _ => if original then .outOfFuelOriginal
      else .fail "out of fuel under a shape that claims termination"
  | .done values =>
    match shape with
    | .valueLevel => if post obs then .pass else .fail "post"
    | _ =>
      if !values.isEmpty then .fail "returned values ≠ []"
      else if post obs then .pass
      else .fail "post: the output does not satisfy the postcondition"
  | .trapped reason =>
    if obs.isOom then
      match shape with
      | .totalStream | .valueLevel => .fail "OOM trap under a shape that claims a normal return"
      | .totalDisjunctiveStream | .partialStream => .vacuousOom
    else .fail s!"trap: {reason.message}"

end Wasm.SpecTest
