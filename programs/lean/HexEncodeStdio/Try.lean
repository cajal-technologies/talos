import HexEncodeStdio.Outcome
import HexEncodeStdio.Blueprint

open Wasm

set_option pp.universes false
set_option pp.all false
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
example (b : UInt8) (bs : List UInt8) :
    let config := (startConfig? (Universal.envFor Project.HexStdio.«module»)
      Project.HexStdio.«module» "encode" (Universal.State.ofInput (b :: bs))).get rfl
    True := by
  dsimp

/-- Symbolic inputs are checked through the total proof; their trace length
need not be fixed to an incidental compiler instruction count. -/
example (b : UInt8) (bs : List UInt8) : ∃ config fuel,
    startConfig? (Universal.envFor Project.HexStdio.«module»)
      Project.HexStdio.«module» "encode" (Universal.State.ofInput (b :: bs)) = some config ∧
    Project.HexEncodeStdio.Outcome.EncodesOrOOM (b :: bs)
      (SmallStep.runSteps fuel config).result := by
  exact Project.HexEncodeStdio.Blueprint.func10_export_run (b :: bs)
