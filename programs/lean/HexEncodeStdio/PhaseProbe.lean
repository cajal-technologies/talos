import Project.HexStdio.Spec

open Wasm

def phaseProbe (input : List UInt8) (fuel : Nat) : String :=
  match startConfig? (Universal.envFor Project.HexStdio.«module»)
      Project.HexStdio.«module» "encode" (Universal.State.ofInput input) with
  | none => "none"
  | some config =>
    match (SmallStep.runSteps fuel config).result with
    | .outOfFuel c => match c.expr with
      | .running t => s!"n={input.length} f={fuel}: calls={t.calls.length} code={t.code.length} head={repr t.code.head?} input={c.store.wasm.host.stdio.input.length} output={c.store.wasm.host.stdio.output.length}"
      | _ => s!"n={input.length} f={fuel}: terminal"
    | .success _ _ => s!"n={input.length} f={fuel}: success"
    | .trapped r _ => s!"n={input.length} f={fuel}: trap {repr r}"
    | .internalError e _ => s!"n={input.length} f={fuel}: error {e.message}"

#eval for n in [1,2,3,4,5,6,7,8,9,16,32,33] do
  IO.println (phaseProbe (List.replicate n 0xab) 740)
