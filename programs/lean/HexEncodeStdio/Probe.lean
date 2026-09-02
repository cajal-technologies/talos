import Project.HexStdio.Spec

open Wasm

def probe (input : List UInt8) (fuel : Nat) : String :=
  match startConfig? (Universal.envFor Project.HexStdio.«module»)
      Project.HexStdio.«module» "encode" (Universal.State.ofInput input) with
  | none => "none"
  | some config =>
    match (SmallStep.runSteps fuel config).result with
    | .outOfFuel c => match c.expr with
      | .running t => s!"{fuel}: calls={t.calls.length} code={t.code.length} head={repr t.code.head?} input={c.store.wasm.host.stdio.input.length} output={c.store.wasm.host.stdio.output.length}"
      | _ => s!"{fuel}: terminal"
    | .success _ _ => s!"{fuel}: success"
    | .trapped r _ => s!"{fuel}: trap {repr r}"
    | .internalError e _ => s!"{fuel}: error {e.message}"

#eval for n in [0:350] do
  if n % 10 = 0 then IO.println (probe [0xab] n)

def stepsUsed (input : List UInt8) : Nat :=
  match startConfig? (Universal.envFor Project.HexStdio.«module»)
      Project.HexStdio.«module» "encode" (Universal.State.ofInput input) with
  | none => 0
  | some config => (SmallStep.runSteps 100000 config).trace.length

#eval IO.println s!"counts: {(List.range 20).map fun n => stepsUsed (List.replicate n 0xab)}"
