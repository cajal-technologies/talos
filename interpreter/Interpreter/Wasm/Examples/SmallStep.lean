/- Authors: Abraxas1010 (IAOM / Apoth3osis). -/

import Interpreter.Wasm.SmallStep.Refinement

/-!
# Observation-labelled small-step discriminator

The main program distinguishes operand order, stack update, local mutation,
and terminal readback.  Its division-by-zero twin distinguishes a semantic
trap from successful completion, while the malformed case remains an internal
error rather than being mislabeled as a trap.
-/

namespace Wasm.Examples.SmallStep

open Wasm.SmallStep

def testModule : Module := default

def testStore : Store Unit :=
  testModule.initialStore

def testRuntime : RuntimeEnv := {}

def discriminator : Program := [
  .const 7,
  .const 3,
  .sub,
  .localSet 0,
  .localGet 0
]

def discriminatorFrame : Locals :=
  { locals := [.i32 0] }

def discriminatorConfig : Config Unit :=
  ofOld testRuntime testStore discriminatorFrame discriminator

example :
    (runSteps 6 discriminatorConfig).values? = some [.i32 4] := by
  native_decide

/-- The old and new executable paths agree on the discriminator's observable
terminal values. -/
example :
    (runSteps 6 discriminatorConfig).values? =
      match exec 1 testModule testStore discriminatorFrame discriminator with
      | .Fallthrough _ frame => some frame.values
      | _ => none := by
  native_decide

/-- Covers the remaining migrated arithmetic constructors while making the
mixed i32/i64 stack shape observable. -/
def arithmeticCoverage : Program := [
  .constI64 9,
  .const 6,
  .const 7,
  .mul,
  .const 2,
  .add
]

def arithmeticCoverageConfig : Config Unit :=
  ofOld testRuntime testStore {} arithmeticCoverage

example :
    (runSteps 7 arithmeticCoverageConfig).values? =
      some [.i32 44, .i64 9] := by
  native_decide

example :
    (runSteps 7 arithmeticCoverageConfig).values? =
      match exec 1 testModule testStore {} arithmeticCoverage with
      | .Fallthrough _ frame => some frame.values
      | _ => none := by
  native_decide

def divideByZero : Program := [
  .const 7,
  .const 0,
  .divU
]

def divideByZeroConfig : Config Unit :=
  ofOld testRuntime testStore {} divideByZero

example :
    (runSteps 3 divideByZeroConfig).trap? =
      some .integerDivideByZero := by
  native_decide

example :
    (runSteps 3 divideByZeroConfig).classification =
      .trapped := by
  native_decide

/-- A malformed local write is diagnostic stuckness, not a semantic trap. -/
def malformedConfig : Config Unit :=
  ofOld testRuntime testStore {} [.localSet 0]

example :
    (runSteps 1 malformedConfig).classification =
      .internalError := by
  native_decide

example :
    (runSteps 1 malformedConfig).trap? = none := by
  native_decide

/-- The structural invariant is inhabited by the discriminator using only
concrete local/stack witnesses. -/
theorem discriminator_wellFormed :
    WellFormed discriminatorConfig := by
  apply FrameProgramWellFormed.const
  apply FrameProgramWellFormed.const
  apply FrameProgramWellFormed.sub (a := 3) (b := 7) (vs := [])
  · rfl
  apply FrameProgramWellFormed.localSet
      (v := .i32 4) (vs := [])
      (frame' := { locals := [.i32 4], values := [.i32 4] })
  · rfl
  · simp [Locals.set?, discriminatorFrame]
  apply FrameProgramWellFormed.localGet (v := .i32 4)
  · rfl
  exact .finish _

end Wasm.Examples.SmallStep
