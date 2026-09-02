import HexEncodeStdio.Outcome

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

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 1048576 in
example (b : UInt8) (bs : List UInt8) : ∃ config,
    startConfig? (Universal.envFor Project.HexStdio.«module»)
      Project.HexStdio.«module» "encode" (Universal.State.ofInput (b :: bs)) = some config ∧
    (SmallStep.runSteps 740 config).trace.length = 740 := by
  refine ⟨_, rfl, ?_⟩
  rfl
