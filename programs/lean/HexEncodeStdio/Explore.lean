import Project.HexStdio.Spec
import HexEncodeStdio.Outcome

open Wasm

def testRun (input : List UInt8) (fuel : Nat) : String :=
  match startConfig? (Universal.envFor Project.HexStdio.«module»)
      Project.HexStdio.«module» "encode" (Universal.State.ofInput input) with
  | none => "no config"
  | some config =>
    let run := SmallStep.runSteps fuel config
    match run.result with
    | .success values store =>
        s!"success steps={run.trace.length} values={repr values} output={repr store.wasm.host.stdio.output}"
    | .trapped reason store =>
        s!"trap steps={run.trace.length} reason={repr reason} oom={store.wasm.host.oom.raised} output={repr store.wasm.host.stdio.output}"
    | .outOfFuel _ => s!"fuel steps={run.trace.length}"
    | .internalError error _ => s!"error steps={run.trace.length} {error.message}"

#eval testRun [] 100000
#eval testRun [0xab] 100000
#eval testRun [0xde, 0xad] 100000
#eval testRun (List.replicate 100 0xab) 500000

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

example : ∃ config,
    startConfig? (Universal.envFor Project.HexStdio.«module»)
      Project.HexStdio.«module» "encode" (Universal.State.ofInput []) =
      some config := by
  refine ⟨_, rfl⟩

set_option maxRecDepth 100000 in
example : ∃ config fuel,
    startConfig? (Universal.envFor Project.HexStdio.«module»)
        Project.HexStdio.«module» "encode" (Universal.State.ofInput []) =
      some config ∧
    Project.HexEncodeStdio.Outcome.EncodesOrOOM []
      (SmallStep.runSteps fuel config).result := by
  refine ⟨_, 260, rfl, ?_⟩
  apply Project.HexEncodeStdio.Outcome.checkEncodesOrOOM_sound
  rfl

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 1048576 in
example (b : UInt8) : ∃ config fuel,
    startConfig? (Universal.envFor Project.HexStdio.«module»)
        Project.HexStdio.«module» "encode" (Universal.State.ofInput [b]) =
      some config ∧
    Project.HexEncodeStdio.Outcome.EncodesOrOOM [b]
      (SmallStep.runSteps fuel config).result := by
  refine ⟨_, 896, rfl, ?_⟩
  apply Project.HexEncodeStdio.Outcome.checkEncodesOrOOM_sound
  rfl
