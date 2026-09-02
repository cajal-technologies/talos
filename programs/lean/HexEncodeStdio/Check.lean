import Project.HexStdio.Program
import HexEncodeStdio.Helpers
import HexEncodeStdio.Outcome
#check Project.HexEncodeStdio.Helpers.pointsToBytes_focus

example : ¬ 21 < Project.HexStdio.«module».imports.length := by decide
example : Project.HexStdio.«module».funcs[21 - Project.HexStdio.«module».imports.length]? =
    some Project.HexStdio.func18Def := by rfl

#eval IO.println (repr (Project.HexStdio.«module».imports[2]?))
#eval IO.println (repr Project.HexStdio.func6)

def testOuter : Wasm.Program :=
  match Project.HexStdio.func6[28]? with
  | some (Wasm.Instruction.block _ _ body _ _) => body
  | _ => []

def testLoop : Wasm.Program :=
  match testOuter[11]? with
  | some (Wasm.Instruction.loop _ _ body _ _) => body
  | _ => []

#eval IO.println s!"outer={testOuter.length} loop={testLoop.length}"

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 1048576 in
example (a b : UInt8) : ∃ config fuel,
    Wasm.startConfig? (Wasm.Universal.envFor Project.HexStdio.«module»)
        Project.HexStdio.«module» "encode" (Wasm.Universal.State.ofInput [a,b]) =
      some config ∧
    Project.HexEncodeStdio.Outcome.EncodesOrOOM [a,b]
      (Wasm.SmallStep.runSteps fuel config).result := by
  refine ⟨_, 1100, rfl, ?_⟩
  apply Project.HexEncodeStdio.Outcome.checkEncodesOrOOM_sound
  rfl

#check UInt32.toNat_lt_size
#check UInt32.size
#check UInt32.toNat_ofNat_of_lt'

open Wasm

def universalInstance : SmallStep.ModuleInstance Universal.State :=
  { module := Project.HexStdio.«module»
    host := Universal.envFor Project.HexStdio.«module»
    resolvedImports := (Universal.envFor Project.HexStdio.«module»).funcs.toArray.map .host }

set_option maxRecDepth 100000 in
example (st : Store Universal.State) : ∃ config,
    SmallStep.initConfig universalInstance 16 st [] = .ok config ∧
    ∃ final,
      (SmallStep.runSteps 5 config).result =
        .trapped (.host OOM.trapMessage) final ∧
      final.wasm.host.oom.raised = true := by
  refine ⟨_, rfl, ?_⟩
  exact ⟨_, rfl, rfl⟩

def allocTerminal : SmallStep.RunnerResult Universal.State → Prop
  | .success _ _ => True
  | .trapped (.host msg) final =>
      msg = OOM.trapMessage ∧ final.wasm.host.oom.raised = true
  | _ => False

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
example (st : Store Universal.State) (size : UInt32) : ∃ config,
    SmallStep.initConfig universalInstance 15 st [.i32 1, .i32 size] =
      .ok config ∧
    allocTerminal (SmallStep.runSteps 100 config).result := by
  refine ⟨_, rfl, ?_⟩
  simp [allocTerminal, SmallStep.runSteps]
