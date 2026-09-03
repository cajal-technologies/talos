import Interpreter.Wasm.SmallStep
import Lean.Data.Json

/-!
# Execution tracing for the small-step Wasm interpreter

This module deliberately observes `SmallStep.stepChecked?` instead of adding
instrumentation fields to the semantic configuration.  The relational `Step`
semantics, its executable presentation, and all existing proofs therefore stay
unchanged.  An instruction is counted from the head of the *pre-step* program;
this also counts instructions whose public `StepKind` is administrative or
host-facing (notably `return` and cross-instance/host calls).
-/

namespace Wasm

namespace Instruction

/-- First whitespace-delimited token of a `Repr` rendering. -/
private def reprConstructor (value : String) : String :=
  (value.takeWhile (fun c => !c.isWhitespace)).toString

/-- Stable constructor-level key used for aggregation. Immediates are omitted,
so `local.get 0` and `local.get 1` contribute to the same counter. Bundled GC
and SIMD constructors include the bundled operation constructor. -/
def opcode : Instruction → String
  | .memOp _ instr => instr.opcode
  | .gc op => "gc." ++ (reprConstructor (reprStr op)).replace "Wasm.GcOp." ""
  | .vUnOp op => "vUnOp." ++ (reprConstructor (reprStr op)).replace "Wasm.Simd.UnOp." ""
  | .vBinOp op => "vBinOp." ++ (reprConstructor (reprStr op)).replace "Wasm.Simd.BinOp." ""
  | .vTestOp op => "vTestOp." ++ (reprConstructor (reprStr op)).replace "Wasm.Simd.TestOp." ""
  | .vShiftOp op => "vShiftOp." ++ (reprConstructor (reprStr op)).replace "Wasm.Simd.ShiftOp." ""
  | instr => (reprConstructor (reprStr instr)).replace "Wasm.Instruction." ""

end Instruction

namespace SmallStep

inductive TraceExit where
  | returned
  | tailCall
  | trapped (reason : TrapReason)
  | internalError (message : String)
deriving Repr

inductive TraceEnd where
  | success
  | trapped (reason : TrapReason)
  | outOfFuel
  | internalError (message : String)
deriving Repr

inductive MemoryAccessKind where
  | load
  | store
  | fill
  | copy
  | init
deriving Repr, DecidableEq, BEq

structure FunctionRef where
  instanceId : Nat
  functionIndex : Nat
  stableId : Option Nat
  name : String
deriving Repr, DecidableEq, BEq

structure Invocation where
  id : Nat
  function : FunctionRef
deriving Repr, DecidableEq, BEq

inductive TraceEvent where
  | instruction
      (sequence invocation : Nat) (opcode : String) (instruction : Instruction)
      (trapped : Bool)
  | functionEnter
      (sequence : Nat) (invocation : Invocation) (parent : Option Nat)
      (arguments : List Value) (host : Bool := false)
  | functionExit
      (sequence : Nat) (invocation : Invocation) (outcome : TraceExit)
      (results : List Value := [])
  | localRead
      (sequence invocation index : Nat) (value : Option Value)
  | localWrite
      (sequence invocation index : Nat) (oldValue newValue : Option Value)
      (tee : Bool := false)
  | globalRead
      (sequence invocation index : Nat) (stableId : Option Nat)
      (value : Option Value)
  | globalWrite
      (sequence invocation index : Nat) (stableId : Option Nat)
      (oldValue newValue : Option Value)
  | memory
      (sequence invocation : Nat) (kind : MemoryAccessKind)
      (memoryIndex : Nat) (memoryId : Option Nat) (address : Option Nat)
      (sourceMemoryIndex : Option Nat) (sourceAddress : Option Nat)
      (byteCount : Option Nat) (value : Option Value) (trapped : Bool)
  | runEnd (sequence : Nat) (outcome : TraceEnd)
deriving Repr

structure TraceSummary where
  transitions : Nat := 0
  instructions : Nat := 0
  instructionCounts : List (String × Nat) := []
  functionEntryCounts : List (String × Nat) := []
  functionExits : Nat := 0
  localReads : Nat := 0
  localWrites : Nat := 0
  globalReads : Nat := 0
  globalWrites : Nat := 0
  memoryLoads : Nat := 0
  memoryStores : Nat := 0
  memoryBulkOperations : Nat := 0
deriving Repr, Inhabited

private def increment (key : String) : List (String × Nat) → List (String × Nat)
  | [] => [(key, 1)]
  | (other, n) :: rest =>
      if key = other then (other, n + 1) :: rest
      else (other, n) :: increment key rest

def TraceSummary.instructionCount (summary : TraceSummary) (opcode : String) : Nat :=
  (summary.instructionCounts.find? (·.1 = opcode)).map (·.2) |>.getD 0

def TraceSummary.functionEntryCount (summary : TraceSummary) (key : String) : Nat :=
  (summary.functionEntryCounts.find? (·.1 = key)).map (·.2) |>.getD 0

def FunctionRef.key (ref : FunctionRef) : String :=
  s!"{ref.instanceId}:{ref.functionIndex}"

private def exportedName? : List Export → Nat → Option String
  | [], _ => none
  | item :: rest, index =>
      if item.funcIdx = index then some item.name else exportedName? rest index

def functionRef (config : Config α) (index : Nat) : FunctionRef :=
  let module := config.store.runtime.currentModule
  let importedName := module.imports[index]?.map (fun imp => s!"{imp.module}.{imp.name}")
  let name := (exportedName? module.exports index).orElse (fun _ => importedName)
    |>.getD s!"func[{index}]"
  { instanceId := config.store.runtime.entry.id
    functionIndex := index
    stableId := config.store.wasm.functionIds[index]?
    name }

private def currentInstruction? (config : Config α) : Option Instruction :=
  match config.expr with
  | .running thread => thread.code.head?
  | _ => none

private def currentInvocationId (stack : List Invocation) : Nat :=
  stack.head?.map (·.id) |>.getD 0

private def isTrapped (config : Config α) : Bool :=
  match config.expr with
  | .trapped _ => true
  | _ => false

private def stackValues (config : Config α) : List Value :=
  match config.expr with
  | .running thread => thread.locals.values
  | _ => []

private def callDepth (config : Config α) : Nat :=
  match config.expr with
  | .running thread => thread.calls.length
  | _ => 0

private def callArguments (before after : Config α) : List Value :=
  match after.expr with
  | .running thread => thread.locals.params
  | _ => stackValues before

private def directOrDynamicTarget? (config : Config α) : Instruction → Option Nat
  | .call index | .returnCall index => some index
  | .callIndirect _ tableIndex | .returnCallIndirect _ tableIndex => do
      let selector ← (stackValues config).head?
      let elementIndex ← selector.addrNat?
      let table ← config.store.wasm.tables[tableIndex]?
      match table[elementIndex]? with
      | some (.funcref (some index)) => some index
      | _ => none
  | .callRef _ | .returnCallRef _ =>
      match (stackValues config).head? with
      | some (.funcref (some index)) => some index
      | _ => none
  | _ => none

/-- Resolve a successful call's target in the callee's own unified function
index space. Cross-instance imports store a callee-local (defined-function)
index, so the callee's import count must be restored before assigning its
trace identity. -/
private def enteredFunctionRef?
    (before after : Config α) (instr : Instruction) : Option FunctionRef := do
  let target ← directOrDynamicTarget? before instr
  if before.store.runtime.entry = after.store.runtime.entry then
    pure (functionRef after target)
  else
    match before.store.runtime.currentInstance.resolvedImports[target]? with
    | some (.wasm _ localIndex) =>
        pure (functionRef after (after.store.runtime.currentModule.imports.length + localIndex))
    | _ => pure (functionRef after target)

private def isTailCall : Instruction → Bool
  | .returnCall _ | .returnCallIndirect _ _ | .returnCallRef _ => true
  | _ => false

private structure MemoryShape where
  kind : MemoryAccessKind
  memoryIndex : Nat
  sourceMemoryIndex : Option Nat := none
  offset : Nat := 0
  byteCount : Option Nat := none
  addressPosition : Nat := 0
  sourceAddressPosition : Option Nat := none

private def scalarMemoryShape? (memoryIndex : Nat) : Instruction → Option MemoryShape
  | .load8U off | .load8S off | .load8UI64 off | .load8SI64 off =>
      some { kind := .load, memoryIndex, offset := off.toNat, byteCount := some 1 }
  | .load16U off | .load16S off | .load16UI64 off | .load16SI64 off =>
      some { kind := .load, memoryIndex, offset := off.toNat, byteCount := some 2 }
  | .load32 off | .load32UI64 off | .load32SI64 off | .f32Load off =>
      some { kind := .load, memoryIndex, offset := off.toNat, byteCount := some 4 }
  | .load64 off | .f64Load off =>
      some { kind := .load, memoryIndex, offset := off.toNat, byteCount := some 8 }
  | .store8 off | .store8I64 off =>
      some { kind := .store, memoryIndex, offset := off.toNat, byteCount := some 1, addressPosition := 1 }
  | .store16 off | .store16I64 off =>
      some { kind := .store, memoryIndex, offset := off.toNat, byteCount := some 2, addressPosition := 1 }
  | .store32 off | .store32I64 off | .f32Store off =>
      some { kind := .store, memoryIndex, offset := off.toNat, byteCount := some 4, addressPosition := 1 }
  | .store64 off | .f64Store off =>
      some { kind := .store, memoryIndex, offset := off.toNat, byteCount := some 8, addressPosition := 1 }
  | .v128Load off =>
      some { kind := .load, memoryIndex, offset := off.toNat, byteCount := some 16 }
  | .v128Store off =>
      some { kind := .store, memoryIndex, offset := off.toNat, byteCount := some 16, addressPosition := 1 }
  | .v128LoadExt _ _ off =>
      some { kind := .load, memoryIndex, offset := off.toNat, byteCount := some 8 }
  | .v128LoadSplat bits off | .v128LoadZero bits off =>
      some { kind := .load, memoryIndex, offset := off.toNat, byteCount := some (bits / 8) }
  | .v128LoadLane bits _ off =>
      some { kind := .load, memoryIndex, offset := off.toNat, byteCount := some (bits / 8), addressPosition := 1 }
  | .v128StoreLane bits _ off =>
      some { kind := .store, memoryIndex, offset := off.toNat, byteCount := some (bits / 8), addressPosition := 1 }
  | .memoryFill =>
      some { kind := .fill, memoryIndex, addressPosition := 2 }
  | .memoryCopy =>
      some { kind := .copy, memoryIndex, sourceMemoryIndex := some memoryIndex, addressPosition := 2, sourceAddressPosition := some 1 }
  | .memoryInit _ =>
      some { kind := .init, memoryIndex, addressPosition := 2, sourceAddressPosition := some 1 }
  | .memOp nestedIndex nested => scalarMemoryShape? nestedIndex nested
  | .memoryCopyBetween destinationMemory sourceMemory =>
      some { kind := .copy, memoryIndex := destinationMemory, sourceMemoryIndex := some sourceMemory, addressPosition := 2, sourceAddressPosition := some 1 }
  | _ => none

private def valueAt? (values : List Value) (position : Nat) : Option Value :=
  values[position]?

private def addressAt? (values : List Value) (position : Nat) (offset : Nat) : Option Nat := do
  let value ← valueAt? values position
  let address ← value.addrNat?
  pure (address + offset)

private def dynamicByteCount? (shape : MemoryShape) (values : List Value) : Option Nat :=
  match shape.byteCount with
  | some n => some n
  | none => values.head?.bind Value.addrNat?

private def memoryId? (config : Config α) (index : Nat) : Option Nat :=
  config.store.wasm.memoryIds[index]?

private structure TraceState where
  nextSequence : Nat := 0
  nextInvocation : Nat := 0
  invocations : List Invocation := []
  eventsRev : List TraceEvent := []
  summary : TraceSummary := {}

private def TraceState.emit (state : TraceState) (make : Nat → TraceEvent) : TraceState :=
  { state with
    nextSequence := state.nextSequence + 1
    eventsRev := make state.nextSequence :: state.eventsRev }

private def TraceState.emitEnter
    (state : TraceState) (ref : FunctionRef) (arguments : List Value)
    (host : Bool := false) (push : Bool := true) : TraceState :=
  let invocation := { id := state.nextInvocation, function := ref }
  let parent := state.invocations.head?.map (·.id)
  let state := state.emit (fun sequence =>
    .functionEnter sequence invocation parent arguments host)
  { state with
    nextInvocation := state.nextInvocation + 1
    invocations := if push then invocation :: state.invocations else state.invocations
    summary := { state.summary with
      functionEntryCounts := increment ref.key state.summary.functionEntryCounts } }

private def TraceState.emitExit
    (state : TraceState) (invocation : Invocation) (outcome : TraceExit)
    (results : List Value := []) (pop : Bool := true) : TraceState :=
  let state := state.emit (fun sequence =>
    .functionExit sequence invocation outcome results)
  { state with
    invocations := if pop then state.invocations.drop 1 else state.invocations
    summary := { state.summary with functionExits := state.summary.functionExits + 1 } }

private def TraceState.closeAll
    (state : TraceState) (outcome : TraceExit) (results : List Value := []) : TraceState :=
  let rec go : List Invocation → TraceState → TraceState
    | [], state => { state with invocations := [] }
    | invocation :: rest, state =>
        let invocationResults := if rest.isEmpty then results else []
        go rest (state.emitExit invocation outcome invocationResults false)
  go state.invocations state

private def observeDataAccess
    (state : TraceState) (before after : Config α) (instr : Instruction) : TraceState :=
  let invocation := currentInvocationId state.invocations
  let trapped := isTrapped after
  let values := stackValues before
  match instr with
  | .localGet index =>
      let value := match before.expr with
        | .running thread => thread.locals.get index
        | _ => none
      let state := state.emit (fun sequence => .localRead sequence invocation index value)
      { state with summary := { state.summary with localReads := state.summary.localReads + 1 } }
  | .localSet index | .localTee index =>
      let oldValue := match before.expr with
        | .running thread => thread.locals.get index
        | _ => none
      let newValue := values.head?
      let tee := match instr with | .localTee _ => true | _ => false
      let state := state.emit (fun sequence =>
        .localWrite sequence invocation index oldValue newValue tee)
      { state with summary := { state.summary with localWrites := state.summary.localWrites + 1 } }
  | .globalGet index =>
      let state := state.emit (fun sequence =>
        .globalRead sequence invocation index before.store.wasm.globalIds[index]?
          (globalAt? before.store index))
      { state with summary := { state.summary with globalReads := state.summary.globalReads + 1 } }
  | .globalSet index =>
      let state := state.emit (fun sequence =>
        .globalWrite sequence invocation index before.store.wasm.globalIds[index]?
          (globalAt? before.store index) values.head?)
      { state with summary := { state.summary with globalWrites := state.summary.globalWrites + 1 } }
  | instr =>
      match scalarMemoryShape? 0 instr with
      | none => state
      | some shape =>
          let address := addressAt? values shape.addressPosition shape.offset
          let sourceAddress := shape.sourceAddressPosition.bind
            (fun position => addressAt? values position 0)
          let value :=
            match shape.kind with
            | .load => if trapped then none else (stackValues after).head?
            | .store => values.head?
            | _ => none
          let state := state.emit (fun sequence =>
            .memory sequence invocation shape.kind shape.memoryIndex
              (memoryId? before shape.memoryIndex) address shape.sourceMemoryIndex
              sourceAddress (dynamicByteCount? shape values) value trapped)
          let summary := match shape.kind with
            | .load => { state.summary with memoryLoads := state.summary.memoryLoads + 1 }
            | .store => { state.summary with memoryStores := state.summary.memoryStores + 1 }
            | _ => { state.summary with
                memoryBulkOperations := state.summary.memoryBulkOperations + 1 }
          { state with summary }

private def observeLifecycle
    (state : TraceState) (before after : Config α) (kind : StepKind)
    (instr? : Option Instruction) : TraceState :=
  let beforeDepth := callDepth before
  let afterDepth := callDepth after
  let hostIndex? := match kind with | .host index => some index | _ => none
  let state := match hostIndex? with
    | some index =>
        let state := state.emitEnter (functionRef before index) (stackValues before) true false
        let invocation := { id := state.nextInvocation - 1, function := functionRef before index }
        let outcome := match after.expr with
          | .trapped reason => .trapped reason
          | _ => .returned
        state.emitExit invocation outcome (stackValues after) false
    | none => state
  let state := match instr? with
    | some instr =>
        if isTailCall instr && !isTrapped after && hostIndex?.isNone then
          match state.invocations, enteredFunctionRef? before after instr with
          | current :: _, some target =>
              let state := state.emitExit current .tailCall
              state.emitEnter target (callArguments before after)
          | _, _ => state
        else if afterDepth > beforeDepth then
          match enteredFunctionRef? before after instr with
          | some target => state.emitEnter target (callArguments before after)
          | none => state
        else state
    | none => state
  let state :=
    if afterDepth < beforeDepth then
      match state.invocations with
      | invocation :: _ => state.emitExit invocation .returned
      | [] => state
    else state
  match after.expr with
  | .done values => state.closeAll .returned values
  | .trapped reason => state.closeAll (.trapped reason)
  | .running _ => state

private def observeTransition
    (state : TraceState) (before : Config α) (kind : StepKind)
    (after : Config α) : TraceState :=
  let state := { state with
    summary := { state.summary with transitions := state.summary.transitions + 1 } }
  let instr? := currentInstruction? before
  let state := match instr? with
    | some instr =>
        let opcode := instr.opcode
        let invocation := currentInvocationId state.invocations
        let state := state.emit (fun sequence =>
          .instruction sequence invocation opcode instr (isTrapped after))
        { state with summary := { state.summary with
            instructions := state.summary.instructions + 1
            instructionCounts := increment opcode state.summary.instructionCounts } }
    | none => state
  let state := match instr? with
    | some instr => observeDataAccess state before after instr
    | none => state
  observeLifecycle state before after kind instr?

structure TracedRun (α : Type) where
  events : List TraceEvent
  summary : TraceSummary
  result : RunnerResult α

private def finishTrace
    (state : TraceState) (outcome : TraceEnd) (result : RunnerResult α) : TracedRun α :=
  let state := state.emit (fun sequence => .runEnd sequence outcome)
  { events := state.eventsRev.reverse, summary := state.summary, result }

/-- Execute the authoritative small-step interpreter while collecting derived
metadata. `entry` is explicit because `Config` intentionally stores execution
state rather than the source-level identity of its root function. -/
def runTraced (fuel : Nat) (entry : Nat) (config : Config α) : TracedRun α :=
  let initialRef := functionRef config entry
  let initialArgs := match config.expr with
    | .running thread => thread.locals.params
    | _ => []
  let initial := ({} : TraceState).emitEnter initialRef initialArgs
  let rec go (fuel : Nat) (config : Config α) (state : TraceState) : TracedRun α :=
    match config.expr with
    | .done values =>
        let state := state.closeAll .returned values
        finishTrace state .success (.success values config.store)
    | .trapped reason =>
        let state := state.closeAll (.trapped reason)
        finishTrace state (.trapped reason) (.trapped reason config.store)
    | .running _ =>
      match fuel with
      | 0 => finishTrace state .outOfFuel (.outOfFuel config)
      | fuel + 1 =>
        match stepChecked? config with
        | .error error =>
            let state := state.closeAll (.internalError error.message)
            finishTrace state (.internalError error.message) (.internalError error config)
        | .ok none =>
            let error : InternalError := ⟨"running configuration has no successor"⟩
            let state := state.closeAll (.internalError error.message)
            finishTrace state (.internalError error.message) (.internalError error config)
        | .ok (some (kind, next)) =>
            go fuel next (observeTransition state config kind next)
  go fuel config initial

namespace TraceJson

open Lean

private def value (v : Value) : Json := toJson (reprStr v)
private def valueOpt : Option Value → Json
  | some v => value v
  | none => Json.null
private def natOpt : Option Nat → Json
  | some n => toJson n
  | none => Json.null
private def stringOpt : Option String → Json
  | some s => toJson s
  | none => Json.null

private def function (ref : FunctionRef) : Json := Json.mkObj
  [("instance", toJson ref.instanceId), ("index", toJson ref.functionIndex),
   ("stable_id", natOpt ref.stableId), ("name", toJson ref.name)]

private def exitName : TraceExit → String
  | .returned => "returned"
  | .tailCall => "tail_call"
  | .trapped _ => "trapped"
  | .internalError _ => "internal_error"

private def endName : TraceEnd → String
  | .success => "success"
  | .trapped _ => "trapped"
  | .outOfFuel => "out_of_fuel"
  | .internalError _ => "internal_error"

private def memoryKind : MemoryAccessKind → String
  | .load => "load"
  | .store => "store"
  | .fill => "fill"
  | .copy => "copy"
  | .init => "init"

def event : TraceEvent → Json
  | .instruction sequence invocation opcode instruction trapped => Json.mkObj
      [("sequence", toJson sequence), ("event", "instruction"),
       ("invocation", toJson invocation), ("opcode", toJson opcode),
       ("instruction", toJson (reprStr instruction)), ("trapped", toJson trapped)]
  | .functionEnter sequence invocation parent arguments host => Json.mkObj
      [("sequence", toJson sequence), ("event", "function_enter"),
       ("invocation", toJson invocation.id), ("parent", natOpt parent),
       ("function", function invocation.function),
       ("arguments", Json.arr (arguments.map value).toArray), ("host", toJson host)]
  | .functionExit sequence invocation outcome results => Json.mkObj
      [("sequence", toJson sequence), ("event", "function_exit"),
       ("invocation", toJson invocation.id), ("function", function invocation.function),
       ("outcome", toJson (exitName outcome)),
       ("detail", match outcome with
          | .trapped reason => toJson reason.message
          | .internalError message => toJson message
          | _ => Json.null),
       ("results", Json.arr (results.map value).toArray)]
  | .localRead sequence invocation index v => Json.mkObj
      [("sequence", toJson sequence), ("event", "local_read"),
       ("invocation", toJson invocation), ("index", toJson index), ("value", valueOpt v)]
  | .localWrite sequence invocation index oldValue newValue tee => Json.mkObj
      [("sequence", toJson sequence), ("event", "local_write"),
       ("invocation", toJson invocation), ("index", toJson index),
       ("old_value", valueOpt oldValue), ("new_value", valueOpt newValue),
       ("tee", toJson tee)]
  | .globalRead sequence invocation index stableId v => Json.mkObj
      [("sequence", toJson sequence), ("event", "global_read"),
       ("invocation", toJson invocation), ("index", toJson index),
       ("stable_id", natOpt stableId), ("value", valueOpt v)]
  | .globalWrite sequence invocation index stableId oldValue newValue => Json.mkObj
      [("sequence", toJson sequence), ("event", "global_write"),
       ("invocation", toJson invocation), ("index", toJson index),
       ("stable_id", natOpt stableId), ("old_value", valueOpt oldValue),
       ("new_value", valueOpt newValue)]
  | .memory sequence invocation kind memoryIndex memoryId address sourceMemoryIndex
      sourceAddress byteCount v trapped => Json.mkObj
      [("sequence", toJson sequence), ("event", "memory"),
       ("invocation", toJson invocation), ("kind", toJson (memoryKind kind)),
       ("memory_index", toJson memoryIndex), ("memory_id", natOpt memoryId),
       ("address", natOpt address), ("source_memory_index", natOpt sourceMemoryIndex),
       ("source_address", natOpt sourceAddress), ("bytes", natOpt byteCount),
       ("value", valueOpt v), ("trapped", toJson trapped)]
  | .runEnd sequence outcome => Json.mkObj
      [("sequence", toJson sequence), ("event", "run_end"),
       ("outcome", toJson (endName outcome)),
       ("detail", match outcome with
          | .trapped reason => toJson reason.message
          | .internalError message => toJson message
          | _ => Json.null)]

private def counts (entries : List (String × Nat)) : Json :=
  Json.mkObj (entries.map fun (key, count) => (key, toJson count))

def summary (s : TraceSummary) : Json := Json.mkObj
  [("transitions", toJson s.transitions), ("instructions", toJson s.instructions),
   ("instruction_counts", counts s.instructionCounts),
   ("function_entry_counts", counts s.functionEntryCounts),
   ("function_exits", toJson s.functionExits), ("local_reads", toJson s.localReads),
   ("local_writes", toJson s.localWrites), ("global_reads", toJson s.globalReads),
   ("global_writes", toJson s.globalWrites), ("memory_loads", toJson s.memoryLoads),
   ("memory_stores", toJson s.memoryStores),
   ("memory_bulk_operations", toJson s.memoryBulkOperations)]

def jsonLines (events : List TraceEvent) : String :=
  String.intercalate "\n" (events.map (fun item => (event item).compress)) ++ "\n"

end TraceJson

end SmallStep
end Wasm
