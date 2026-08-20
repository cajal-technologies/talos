import Interpreter.Wasm.Semantics

set_option maxHeartbeats 2000000

/-!
# Small-step WebAssembly machine

This file is the first vertical slice of the Iris migration.  The existing
fuel-bounded interpreter remains available as a regression oracle, but none of
the definitions below call `execOne`, `exec`, or `run`.

The relational `Step` relation is the semantic interface.  `stepChecked?` is
its deterministic executable presentation for the instruction families ported
so far.  An `InternalError` denotes a configuration which validation should
have ruled out, or an instruction family which has not yet been migrated; it is
not a Wasm trap.
-/

namespace Wasm
namespace SmallStep

inductive TrapReason where
  | unreachable
  | integerDivideByZero
  | integerOverflow
  | invalidConversionToInteger
  | outOfBoundsMemory
  | outOfBoundsTable
  | undefinedElement
  | uninitializedElement (index : Nat)
  | indirectCallTypeMismatch
  | nullReference
  | nullFunctionReference
  | nullExceptionReference
  | nullI31Reference
  | nullStructureReference
  | nullArrayReference
  | castFailure
  | outOfBoundsArray
  | uncaughtException (tag : Nat) (arguments : List Value)
  | host (message : String)
  /-- Forward-compatible category for a GC proposal trap that has not yet
  received a dedicated structural constructor. -/
  | gc (message : String)
deriving Repr, Inhabited, DecidableEq, BEq

/-- Stable driver-facing rendering of structural traps. The semantic machine
retains the constructor; CLI and testsuite surfaces use this text only at their
boundary. -/
def TrapReason.message : TrapReason → String
  | .unreachable => "unreachable"
  | .integerDivideByZero => "integer divide by zero"
  | .integerOverflow => "integer overflow"
  | .invalidConversionToInteger => "invalid conversion to integer"
  | .outOfBoundsMemory => "out of bounds memory access"
  | .outOfBoundsTable => "out of bounds table access"
  | .undefinedElement => "undefined element"
  | .uninitializedElement index => s!"uninitialized element {index}"
  | .indirectCallTypeMismatch => "indirect call type mismatch"
  | .nullReference => "null reference"
  | .nullFunctionReference => "null function reference"
  | .nullExceptionReference => "null exception reference"
  | .nullI31Reference => "null i31 reference"
  | .nullStructureReference => "null structure reference"
  | .nullArrayReference => "null array reference"
  | .castFailure => "cast failure"
  | .outOfBoundsArray => "out of bounds array access"
  | .uncaughtException tag _ => s!"uncaught exception with tag {tag}"
  | .host message | .gc message => message

inductive AdministrativeStep where
  | finish
  | exitControl
  | returnFromFunction
  | returnFromCall
  | returnFromCallCrossInstance
  | callCrossInstance
  | unwindException
  | catchException
deriving Repr, Inhabited, DecidableEq, BEq

inductive StepKind where
  | instruction (instr : Instruction)
  | administrative (kind : AdministrativeStep)
  | host (functionIndex : Nat)
deriving Repr

structure ModuleInstanceId where
  id : Nat
deriving DecidableEq, Ord, Repr, BEq

-- import resolved to either a host function or a wasm function in another instance
inductive ResolvedImport (α : Type) where
  | host : HostFn α → ResolvedImport α
  | wasm : ModuleInstanceId → Nat → ResolvedImport α

/-- Per-module execution metadata: the module's syntax, its host imports, and
the cross-instance resolution of its function imports.

**Modeling caveat (shared store).** Instances carry only *metadata*; all
runtime state — linear memories, globals, tables, exception instances — lives
in the single `MachineStore.wasm` pool shared by every instance. A
cross-instance call switches `RuntimeEnv.entry` and nothing else, so the
callee reads and writes the *same* physical store as the caller. Real Wasm
instantiation gives each instance its own address space (imports alias
selected resources explicitly). Consequently, cross-module results proved
against this semantics do **not** transfer to a spec-conforming engine
whenever the participating modules rely on disjoint address spaces; they are
faithful only for module systems that deliberately share one store (e.g. a
module split into components over one memory). -/
structure ModuleInstance (α : Type) where
  module : Module
  host : HostEnv α
  resolvedImports : Array (ResolvedImport α) := #[]
deriving Inhabited

/-- Immutable execution metadata.  Keeping the host parameter on the runtime
environment makes the eventual Iris language instance available uniformly for
each fixed host-state type `α`.

**Modeling caveat (shared store).** `instances` holds per-module metadata
only; see `ModuleInstance` — every instance executes against the single
shared `MachineStore.wasm` state, unlike real Wasm instance isolation. -/
structure RuntimeEnv (α : Type) where
  instances : Array (ModuleInstance α)
  entry : ModuleInstanceId

/-- The instance currently executing.

Precondition: `re.entry.id < re.instances.size`. The panicking index
(`[·]!`) silently yields the default (`Inhabited`) instance when `entry` is
out of range, so callers must only construct runtimes whose entry points at
an existing instance. `initConfig` and `addInstanceConfig` maintain this
invariant, and every `Step` preserves `instances` while only switching
`entry` to an id validated by `hcallee`/`returningInstance` hypotheses. -/
@[reducible] def RuntimeEnv.currentInstance (re : RuntimeEnv α) : ModuleInstance α :=
  re.instances[re.entry.id]!

@[reducible] def RuntimeEnv.currentModule (re : RuntimeEnv α) : Module :=
  re.currentInstance.module

@[reducible] def RuntimeEnv.currentHost (re : RuntimeEnv α) : HostEnv α :=
  re.currentInstance.host

@[simp] theorem RuntimeEnv.currentModule_mk1 (inst : ModuleInstance α) :
    ({ instances := #[inst], entry := ⟨0⟩ } : RuntimeEnv α).currentModule = inst.module := by
  simp [RuntimeEnv.currentModule, RuntimeEnv.currentInstance]

@[simp] theorem RuntimeEnv.currentHost_mk1 (inst : ModuleInstance α) :
    ({ instances := #[inst], entry := ⟨0⟩ } : RuntimeEnv α).currentHost = inst.host := by
  simp [RuntimeEnv.currentHost, RuntimeEnv.currentInstance]

/-- Reserved funcref address range for function instances owned by another
module. Local Wasm function indices are far below this boundary. A funcref
`foreignFunctionBase + id` names the script-wide callable
`HostEnv.foreignFuncs[id]`, letting a funcref exported by one module travel
through a shared table and be `call_indirect`-ed from another module. -/
def foreignFunctionBase : Nat := 1 <<< 62

def isForeignFunctionIndex (importCount index : Nat) : Bool :=
  importCount ≤ index && foreignFunctionBase ≤ index

/-- Shared state visible to Wasm and host calls. -/
structure MachineStore (α : Type) where
  runtime : RuntimeEnv α
  wasm : Store α

inductive ControlKind where
  | block
  | loop
  | tryTable (catches : List CatchClause)
  | throwing (tag : Nat) (arguments : List Value)
deriving Repr, Inhabited, DecidableEq

/-- Whether a control frame is the administrative exception-propagation
marker. Exposed for primitive Iris rules that discharge ordinary block exits. -/
def ControlKind.isThrowing : ControlKind → Bool
  | .throwing _ _ => true
  | _ => false

/-- A structured-control label. Frames are thread-local and explicitly retain
the operand stack below the construct, the enclosing continuation, and the
loop body needed by a back-edge. -/
structure ControlFrame where
  kind : ControlKind
  paramArity : Nat
  resultArity : Nat
  body : Program
  continuation : Program
  belowStack : List Value
deriving Repr

/-- Suspended caller state. A direct call installs fresh callee locals and
control frames while retaining the caller continuation here. -/
structure CallFrame where
  locals : Locals
  continuation : Program
  resultArity : Nat
  callerRemainder : List Value
  control : List ControlFrame
  returningInstance : ModuleInstanceId
deriving Repr

/-- Per-invocation state. Control and call frames belong to the thread rather
than the shared machine store. -/
structure ThreadState (α : Type) where
  locals : Locals
  code : Program
  resultArity : Nat
  callerRemainder : List Value
  control : List ControlFrame := []
  calls : List CallFrame := []

inductive Expr (α : Type) where
  | running (thread : ThreadState α)
  | done (values : List Value)
  | trapped (reason : TrapReason)

structure Config (α : Type) where
  expr : Expr α
  store : MachineStore α

structure InternalError where
  message : String
deriving Repr, Inhabited, DecidableEq

private def gcTrapReasonOfMessage : String → TrapReason
  | "null i31 reference" => .nullI31Reference
  | "null structure reference" => .nullStructureReference
  | "null array reference" => .nullArrayReference
  | "cast failure" => .castFailure
  | "out of bounds array access" => .outOfBoundsArray
  | "out of bounds memory access" => .outOfBoundsMemory
  | "out of bounds table access" => .outOfBoundsTable
  | message => .gc message

private def returnedValues (thread : ThreadState α) : List Value :=
  thread.locals.values.take thread.resultArity ++ thread.callerRemainder

/-- Restore a suspended caller and prepend the callee's declared results to
the caller operand stack. Exposed so Iris lifting rules can state the exact
administrative successor without duplicating an opaque transition helper. -/
def resumeCaller (callee : ThreadState α) (caller : CallFrame)
    (calls : List CallFrame) : ThreadState α :=
  { locals :=
      { caller.locals with
        values :=
          callee.locals.values.take callee.resultArity ++ caller.locals.values }
    code := caller.continuation
    resultArity := caller.resultArity
    callerRemainder := caller.callerRemainder
    control := caller.control
    calls }

private def resumeExceptionCaller
    (throwingFrame : ControlFrame) (caller : CallFrame)
    (calls : List CallFrame) : ThreadState α :=
  { locals := caller.locals
    code := []
    resultArity := caller.resultArity
    callerRemainder := caller.callerRemainder
    control := throwingFrame :: caller.control
    calls }

theorem resumeExceptionCaller_eq {α : Type} (throwingFrame : ControlFrame) (caller : CallFrame)
    (calls : List CallFrame) :
    (resumeExceptionCaller throwingFrame caller calls : ThreadState α) =
    { locals := caller.locals
      code := []
      resultArity := caller.resultArity
      callerRemainder := caller.callerRemainder
      control := throwingFrame :: caller.control
      calls } := rfl

def canonicalGlobalIndex (store : MachineStore α) : Nat → Nat
  | 0 => 0
  | index + 1 =>
    match store.wasm.globalIds[index + 1]? with
    | some id => (store.wasm.globalIds.findIdx? (· = id)).getD (index + 1)
    | none => index + 1

def globalAt? (store : MachineStore α) (index : Nat) : Option Value :=
  store.wasm.globals.globals[canonicalGlobalIndex store index]?

@[simp] theorem canonicalGlobalIndex_zero (store : MachineStore α) :
    canonicalGlobalIndex store 0 = 0 := rfl

private def canonicalTagIndex (store : MachineStore α) (index : Nat) : Nat :=
  match store.wasm.tagIds[index]? with
  | some id => (store.wasm.tagIds.findIdx? (· = id)).getD index
  | none => index

theorem canonicalTagIndex_eq (store : MachineStore α) (index : Nat) :
    canonicalTagIndex store index =
    match store.wasm.tagIds[index]? with
    | some id => (store.wasm.tagIds.findIdx? (· = id)).getD index
    | none => index := rfl

private def setGlobal (store : MachineStore α) (index : Nat) (value : Value) :
    MachineStore α :=
  let index := canonicalGlobalIndex store index
  { store with wasm :=
      { store.wasm with globals :=
          { globals := store.wasm.globals.globals.set index value } } }

@[simp] theorem setGlobal_zero_eq (store : MachineStore α) (value : Value) :
    setGlobal store 0 value =
      { store with wasm :=
          { store.wasm with globals :=
              { globals := store.wasm.globals.globals.set 0 value } } } := by
  simp [setGlobal]

theorem setGlobal_eq_of_canonical
    (store : MachineStore α) (index : Nat) (value : Value)
    (h : canonicalGlobalIndex store index = index) :
    setGlobal store index value =
      { store with wasm :=
          { store.wasm with globals :=
              { globals := store.wasm.globals.globals.set index value } } } := by
  simp [setGlobal, h]

private def setMemory (store : MachineStore α) (memory : Mem) : MachineStore α :=
  { store with wasm := { store.wasm with mem := memory } }

/-- Public unfolding equation for proof layers that frame the primary memory.
The implementation helper remains private so clients cannot accidentally build
a second state-transition API around it. -/
theorem setMemory_eq (store : MachineStore α) (memory : Mem) :
    setMemory store memory =
      { store with wasm := { store.wasm with mem := memory } } :=
  rfl

private def rawMemoryAt? (store : MachineStore α) (index : Nat) : Option Mem :=
  if index = 0 then some store.wasm.mem
  else store.wasm.extraMems[index - 1]?

private def canonicalMemoryIndex (store : MachineStore α) (index : Nat) : Nat :=
  match store.wasm.memoryIds[index]? with
  | some id => (store.wasm.memoryIds.findIdx? (· = id)).getD index
  | none => index

def memoryAt? (store : MachineStore α) (index : Nat) : Option Mem :=
  rawMemoryAt? store (canonicalMemoryIndex store index)

def setMemoryAt
    (store : MachineStore α) (index : Nat) (memory : Mem) : MachineStore α :=
  let index := canonicalMemoryIndex store index
  if index = 0 then setMemory store memory
  else
    { store with wasm :=
        { store.wasm with
          extraMems := store.wasm.extraMems.set (index - 1) memory } }

private def enterIndexedMemory?
    (store : MachineStore α) (index : Nat) : Option (MachineStore α) :=
  match memoryAt? store index,
      store.runtime.currentModule.extraMemories[index - 1]? with
  | some memory, some declaration =>
      let selectedCap := store.wasm.memoryCap store.runtime.currentModule index
      let selectedId := store.wasm.memoryIds[index]?
      some
        { runtime :=
            { store.runtime with
              instances := store.runtime.instances.modify
                store.runtime.entry.id
                (fun inst => { inst with module := { inst.module with memory := some declaration } }) }
          wasm :=
            { store.wasm with
              mem := memory
              memoryCaps := [selectedCap]
              memoryIds := selectedId.toList } }
  | _, _ => none

private def leaveIndexedMemory
    (original stepped : MachineStore α) (index : Nat) : MachineStore α :=
  let restored : MachineStore α :=
    { runtime := original.runtime
      wasm :=
        { stepped.wasm with
          mem := original.wasm.mem
          memoryCaps := original.wasm.memoryCaps
          memoryIds := original.wasm.memoryIds
          extraMems := original.wasm.extraMems } }
  setMemoryAt restored index stepped.wasm.mem

private def resumeAfterIndexedMemory
    (rest : Program) (original : MachineStore α) (index : Nat)
    (config : Config α) : Config α :=
  let expr :=
    match config.expr with
    | .running thread => .running { thread with code := thread.code ++ rest }
    | .done values => .done values
    | .trapped reason => .trapped reason
  { expr, store := leaveIndexedMemory original config.store index }

private def isMemOp : Instruction → Bool
  | .memOp _ _ => true
  | _ => false

private def firstMemOpDepth : Config α → Nat
  | ⟨.running thread, _⟩ =>
      match thread.code with
      | instruction :: _ => if isMemOp instruction then 1 else 0
      | [] => 0
  | _ => 0

private def setDataSegments (store : MachineStore α)
    (segments : List (Option (List UInt8))) : MachineStore α :=
  { store with wasm := { store.wasm with dataSegments := segments } }

private def setTables (store : MachineStore α) (tables : List TableInst) :
    MachineStore α :=
  { store with wasm := { store.wasm with tables := tables } }

private def setElementSegments (store : MachineStore α)
    (segments : List (Option (List (Option Nat)))) : MachineStore α :=
  { store with wasm := { store.wasm with elementSegments := segments } }

def elementSegmentValues (store : MachineStore α) (elementIndex : Nat)
    (segmentState : Option (List (Option Nat))) : List Value :=
  match segmentState with
  | none => []
  | some _ =>
    (store.runtime.currentModule.elements[elementIndex]?.map
      ElementSegment.values).getD []

private def rotateLeft32 (value count : UInt32) : UInt32 :=
  let count := count % 32
  if count = 0 then value
  else (value <<< count) ||| (value >>> (32 - count))

theorem rotateLeft32_eq (value count : UInt32) : rotateLeft32 value count =
    let count := count % 32
    if count = 0 then value
    else (value <<< count) ||| (value >>> (32 - count)) := rfl

private def rotateRight32 (value count : UInt32) : UInt32 :=
  let count := count % 32
  if count = 0 then value
  else (value >>> count) ||| (value <<< (32 - count))

theorem rotateRight32_eq (value count : UInt32) : rotateRight32 value count =
    let count := count % 32
    if count = 0 then value
    else (value >>> count) ||| (value <<< (32 - count)) := rfl

private def rotateLeft64 (value count : UInt64) : UInt64 :=
  let count := count % 64
  if count = 0 then value
  else (value <<< count) ||| (value >>> (64 - count))

theorem rotateLeft64_eq (value count : UInt64) : rotateLeft64 value count =
    let count := count % 64
    if count = 0 then value
    else (value <<< count) ||| (value >>> (64 - count)) := rfl

private def rotateRight64 (value count : UInt64) : UInt64 :=
  let count := count % 64
  if count = 0 then value
  else (value >>> count) ||| (value <<< (64 - count))

theorem rotateRight64_eq (value count : UInt64) : rotateRight64 value count =
    let count := count % 64
    if count = 0 then value
    else (value >>> count) ||| (value <<< (64 - count)) := rfl

private def signedDiv32 (dividend divisor : UInt32) : UInt32 :=
  (Int32.ofInt
    (Int.tdiv dividend.toInt32.toInt divisor.toInt32.toInt)).toUInt32

theorem signedDiv32_eq (dividend divisor : UInt32) : signedDiv32 dividend divisor =
    (Int32.ofInt (Int.tdiv dividend.toInt32.toInt divisor.toInt32.toInt)).toUInt32 := rfl

private def signedRem32 (dividend divisor : UInt32) : UInt32 :=
  (Int32.ofInt
    (Int.tmod dividend.toInt32.toInt divisor.toInt32.toInt)).toUInt32

theorem signedRem32_eq (dividend divisor : UInt32) : signedRem32 dividend divisor =
    (Int32.ofInt (Int.tmod dividend.toInt32.toInt divisor.toInt32.toInt)).toUInt32 := rfl

private def signedDiv64 (dividend divisor : UInt64) : UInt64 :=
  (Int64.ofInt
    (Int.tdiv dividend.toInt64.toInt divisor.toInt64.toInt)).toUInt64

theorem signedDiv64_eq (dividend divisor : UInt64) : signedDiv64 dividend divisor =
    (Int64.ofInt (Int.tdiv dividend.toInt64.toInt divisor.toInt64.toInt)).toUInt64 := rfl

private def signedRem64 (dividend divisor : UInt64) : UInt64 :=
  (Int64.ofInt
    (Int.tmod dividend.toInt64.toInt divisor.toInt64.toInt)).toUInt64

theorem signedRem64_eq (dividend divisor : UInt64) : signedRem64 dividend divisor =
    (Int64.ofInt (Int.tmod dividend.toInt64.toInt divisor.toInt64.toInt)).toUInt64 := rfl

private def wrap64To32 (value : UInt64) : UInt32 :=
  UInt32.ofNat (value.toNat % 2 ^ 32)

theorem wrap64To32_eq (value : UInt64) : wrap64To32 value =
    UInt32.ofNat (value.toNat % 2 ^ 32) := rfl

private def extendSigned32To64 (value : UInt32) : UInt64 :=
  (Int64.ofInt value.toInt32.toInt).toUInt64

theorem extendSigned32To64_eq (value : UInt32) : extendSigned32To64 value =
    (Int64.ofInt value.toInt32.toInt).toUInt64 := rfl

private def extendUnsigned32To64 (value : UInt32) : UInt64 :=
  UInt64.ofNat value.toNat

theorem extendUnsigned32To64_eq (value : UInt32) : extendUnsigned32To64 value =
    UInt64.ofNat value.toNat := rfl

private def extend8To32 (value : UInt32) : UInt32 :=
  (Int32.ofInt (signExtend (value.toNat % 256) 8)).toUInt32

theorem extend8To32_eq (value : UInt32) :
    extend8To32 value = (Int32.ofInt (signExtend (value.toNat % 256) 8)).toUInt32 := rfl

private def extend16To32 (value : UInt32) : UInt32 :=
  (Int32.ofInt (signExtend (value.toNat % 65536) 16)).toUInt32

theorem extend16To32_eq (value : UInt32) :
    extend16To32 value = (Int32.ofInt (signExtend (value.toNat % 65536) 16)).toUInt32 := rfl

private def extend8To64 (value : UInt64) : UInt64 :=
  (Int64.ofInt (signExtend (value.toNat % 256) 8)).toUInt64

theorem extend8To64_eq (value : UInt64) : extend8To64 value =
    (Int64.ofInt (signExtend (value.toNat % 256) 8)).toUInt64 := rfl

private def extend16To64 (value : UInt64) : UInt64 :=
  (Int64.ofInt (signExtend (value.toNat % 65536) 16)).toUInt64

theorem extend16To64_eq (value : UInt64) : extend16To64 value =
    (Int64.ofInt (signExtend (value.toNat % 65536) 16)).toUInt64 := rfl

private def extend32To64 (value : UInt64) : UInt64 :=
  (Int64.ofInt (signExtend (value.toNat % 2 ^ 32) 32)).toUInt64

theorem extend32To64_eq (value : UInt64) : extend32To64 value =
    (Int64.ofInt (signExtend (value.toNat % 2 ^ 32) 32)).toUInt64 := rfl

/-- The mathematical address used for bounds checks and the current reference
memory's physical UInt32 index. Memory64 addresses above the implementation
limit fail the bounds check before the truncated physical index is observed. -/
private def memoryAddress? : Value → Option (Nat × UInt32)
  | .i32 address => some (address.toNat, address)
  | .i64 address => some (address.toNat, address.toUInt32)
  | _ => none

theorem memoryAddress?_i32_eq (a : UInt32) : memoryAddress? (.i32 a) = some (a.toNat, a) := rfl

theorem memoryAddress?_i64_eq (a : UInt64) : memoryAddress? (.i64 a) = some (a.toNat, a.toUInt32) := rfl

def evalScalarFloat0? : Instruction → Option Value
  | .f32Const value => some (.f32 value)
  | .f64Const value => some (.f64 value)
  | _ => none

def evalScalarFloat1? : Instruction → Value → Option Value
  | .f32Abs, .f32 value => some (.f32 (f32Abs value))
  | .f32Neg, .f32 value => some (.f32 (f32Neg value))
  | .f32Sqrt, .f32 value => some (.f32 (f32Sqrt value))
  | .f32Ceil, .f32 value => some (.f32 (f32Ceil value))
  | .f32Floor, .f32 value => some (.f32 (f32Floor value))
  | .f32Trunc, .f32 value => some (.f32 (f32Trunc value))
  | .f32Nearest, .f32 value => some (.f32 (f32Nearest value))
  | .f64Abs, .f64 value => some (.f64 (f64Abs value))
  | .f64Neg, .f64 value => some (.f64 (f64Neg value))
  | .f64Sqrt, .f64 value => some (.f64 (f64Sqrt value))
  | .f64Ceil, .f64 value => some (.f64 (f64Ceil value))
  | .f64Floor, .f64 value => some (.f64 (f64Floor value))
  | .f64Trunc, .f64 value => some (.f64 (f64Trunc value))
  | .f64Nearest, .f64 value => some (.f64 (f64Nearest value))
  | .f32ConvertI32S, .i32 value => some (.f32 (f32ConvertI32S value))
  | .f32ConvertI32U, .i32 value => some (.f32 (f32ConvertI32U value))
  | .f32ConvertI64S, .i64 value => some (.f32 (f32ConvertI64S value))
  | .f32ConvertI64U, .i64 value => some (.f32 (f32ConvertI64U value))
  | .f64ConvertI32S, .i32 value => some (.f64 (f64ConvertI32S value))
  | .f64ConvertI32U, .i32 value => some (.f64 (f64ConvertI32U value))
  | .f64ConvertI64S, .i64 value => some (.f64 (f64ConvertI64S value))
  | .f64ConvertI64U, .i64 value => some (.f64 (f64ConvertI64U value))
  | .i32TruncSatF32S, .f32 value => some (.i32 (i32TruncSatF32S value))
  | .i32TruncSatF32U, .f32 value => some (.i32 (i32TruncSatF32U value))
  | .i32TruncSatF64S, .f64 value => some (.i32 (i32TruncSatF64S value))
  | .i32TruncSatF64U, .f64 value => some (.i32 (i32TruncSatF64U value))
  | .i64TruncSatF32S, .f32 value => some (.i64 (i64TruncSatF32S value))
  | .i64TruncSatF32U, .f32 value => some (.i64 (i64TruncSatF32U value))
  | .i64TruncSatF64S, .f64 value => some (.i64 (i64TruncSatF64S value))
  | .i64TruncSatF64U, .f64 value => some (.i64 (i64TruncSatF64U value))
  | .f32DemoteF64, .f64 value => some (.f32 (f32DemoteF64 value))
  | .f64PromoteF32, .f32 value => some (.f64 (f64PromoteF32 value))
  | .i32ReinterpretF32, .f32 value => some (.i32 value)
  | .i64ReinterpretF64, .f64 value => some (.i64 value)
  | .f32ReinterpretI32, .i32 value => some (.f32 value)
  | .f64ReinterpretI64, .i64 value => some (.f64 value)
  | _, _ => none

def evalScalarTrunc? :
    Instruction → Value → Option (Except TrapReason Value)
  | .i32TruncF32S, .f32 value =>
      some <| match i32TruncF32S value with
        | some result => .ok (.i32 result)
        | none => .error (if (Float32.ofBits value).isNaN then
            .invalidConversionToInteger else .integerOverflow)
  | .i32TruncF32U, .f32 value =>
      some <| match i32TruncF32U value with
        | some result => .ok (.i32 result)
        | none => .error (if (Float32.ofBits value).isNaN then
            .invalidConversionToInteger else .integerOverflow)
  | .i32TruncF64S, .f64 value =>
      some <| match i32TruncF64S value with
        | some result => .ok (.i32 result)
        | none => .error (if (Float.ofBits value).isNaN then
            .invalidConversionToInteger else .integerOverflow)
  | .i32TruncF64U, .f64 value =>
      some <| match i32TruncF64U value with
        | some result => .ok (.i32 result)
        | none => .error (if (Float.ofBits value).isNaN then
            .invalidConversionToInteger else .integerOverflow)
  | .i64TruncF32S, .f32 value =>
      some <| match i64TruncF32S value with
        | some result => .ok (.i64 result)
        | none => .error (if (Float32.ofBits value).isNaN then
            .invalidConversionToInteger else .integerOverflow)
  | .i64TruncF32U, .f32 value =>
      some <| match i64TruncF32U value with
        | some result => .ok (.i64 result)
        | none => .error (if (Float32.ofBits value).isNaN then
            .invalidConversionToInteger else .integerOverflow)
  | .i64TruncF64S, .f64 value =>
      some <| match i64TruncF64S value with
        | some result => .ok (.i64 result)
        | none => .error (if (Float.ofBits value).isNaN then
            .invalidConversionToInteger else .integerOverflow)
  | .i64TruncF64U, .f64 value =>
      some <| match i64TruncF64U value with
        | some result => .ok (.i64 result)
        | none => .error (if (Float.ofBits value).isNaN then
            .invalidConversionToInteger else .integerOverflow)
  | _, _ => none

private def simdExtractLane
    (shape : Simd.Shape) (signed : Bool) (lane : Nat)
    (value : BitVec 128) : Value :=
  let laneValue := Simd.getLane shape.laneBits lane value
  match shape with
  | .i8x16 => .i32 (if signed then
      UInt32.ofNat (Simd.toU 32 (Simd.sx 8 laneValue))
    else UInt32.ofNat laneValue)
  | .i16x8 => .i32 (if signed then
      UInt32.ofNat (Simd.toU 32 (Simd.sx 16 laneValue))
    else UInt32.ofNat laneValue)
  | .i32x4 => .i32 (UInt32.ofNat laneValue)
  | .i64x2 => .i64 (UInt64.ofNat laneValue)
  | .f32x4 => .f32 (UInt32.ofNat laneValue)
  | .f64x2 => .f64 (UInt64.ofNat laneValue)

theorem simdExtractLane_eq (shape : Simd.Shape) (signed : Bool) (lane : Nat)
    (value : BitVec 128) : simdExtractLane shape signed lane value =
    let laneValue := Simd.getLane shape.laneBits lane value
    match shape with
    | .i8x16 => .i32 (if signed then
        UInt32.ofNat (Simd.toU 32 (Simd.sx 8 laneValue))
      else UInt32.ofNat laneValue)
    | .i16x8 => .i32 (if signed then
        UInt32.ofNat (Simd.toU 32 (Simd.sx 16 laneValue))
      else UInt32.ofNat laneValue)
    | .i32x4 => .i32 (UInt32.ofNat laneValue)
    | .i64x2 => .i64 (UInt64.ofNat laneValue)
    | .f32x4 => .f32 (UInt32.ofNat laneValue)
    | .f64x2 => .f64 (UInt64.ofNat laneValue) := rfl

private def readV128 (memory : Mem) (address : UInt32) : BitVec 128 :=
  let lo := memory.read64 address
  let hi := memory.read64 (address + 8)
  BitVec.ofNat 128 (lo.toNat + hi.toNat * 2 ^ 64)

theorem readV128_eq (memory : Mem) (address : UInt32) : readV128 memory address =
    let lo := memory.read64 address
    let hi := memory.read64 (address + 8)
    BitVec.ofNat 128 (lo.toNat + hi.toNat * 2 ^ 64) := rfl

private def writeV128
    (memory : Mem) (address : UInt32) (value : BitVec 128) : Mem :=
  let lo := UInt64.ofNat (value.toNat % 2 ^ 64)
  let hi := UInt64.ofNat (value.toNat / 2 ^ 64)
  (memory.write64 address lo).write64 (address + 8) hi

theorem writeV128_eq (memory : Mem) (address : UInt32) (value : BitVec 128) :
    writeV128 memory address value =
    let lo := UInt64.ofNat (value.toNat % 2 ^ 64)
    let hi := UInt64.ofNat (value.toNat / 2 ^ 64)
    (memory.write64 address lo).write64 (address + 8) hi := rfl

private def readLaneNat (memory : Mem) (address : UInt32) (bits : Nat) : Nat :=
  match bits with
  | 8 => (memory.read8 address).toNat
  | 16 => (memory.read16 address).toNat
  | 32 => (memory.read32 address).toNat
  | _ => (memory.read64 address).toNat

theorem readLaneNat_eq (memory : Mem) (address : UInt32) (bits : Nat) :
    readLaneNat memory address bits =
    match bits with
    | 8 => (memory.read8 address).toNat
    | 16 => (memory.read16 address).toNat
    | 32 => (memory.read32 address).toNat
    | _ => (memory.read64 address).toNat := rfl

private def writeLaneNat
    (memory : Mem) (address : UInt32) (bits value : Nat) : Mem :=
  match bits with
  | 8 => memory.write8 address (UInt8.ofNat value)
  | 16 => memory.write16 address (UInt32.ofNat value)
  | 32 => memory.write32 address (UInt32.ofNat value)
  | _ => memory.write64 address (UInt64.ofNat value)

theorem writeLaneNat_eq_8 (memory : Mem) (address : UInt32) (value : Nat) :
    writeLaneNat memory address 8 value = memory.write8 address (UInt8.ofNat value) := rfl

theorem writeLaneNat_eq_16 (memory : Mem) (address : UInt32) (value : Nat) :
    writeLaneNat memory address 16 value = memory.write16 address (UInt32.ofNat value) := rfl

theorem writeLaneNat_eq_32 (memory : Mem) (address : UInt32) (value : Nat) :
    writeLaneNat memory address 32 value = memory.write32 address (UInt32.ofNat value) := rfl

theorem writeLaneNat_eq_64 (memory : Mem) (address : UInt32) (value : Nat) :
    writeLaneNat memory address 64 value = memory.write64 address (UInt64.ofNat value) := rfl

private def loadV128Ext
    (memory : Mem) (address : UInt32) (srcBits : Nat) (signed : Bool) :
    BitVec 128 :=
  let word := memory.read64 address
  let dstBits := srcBits * 2
  let count := 64 / srcBits
  let lanes := (List.range count).map fun i =>
    let value := (word.toNat >>> (i * srcBits)) % 2 ^ srcBits
    if signed then Simd.toU dstBits (Simd.sx srcBits value) else value
  Simd.ofLanes dstBits lanes

theorem loadV128Ext_eq (memory : Mem) (address : UInt32) (srcBits : Nat) (signed : Bool) :
    loadV128Ext memory address srcBits signed =
    let word := memory.read64 address
    let dstBits := srcBits * 2
    let count := 64 / srcBits
    let lanes := (List.range count).map fun i =>
      let value := (word.toNat >>> (i * srcBits)) % 2 ^ srcBits
      if signed then Simd.toU dstBits (Simd.sx srcBits value) else value
    Simd.ofLanes dstBits lanes := rfl

def evalScalarFloat2? : Instruction → Value → Value → Option Value
  | .f32Add, .f32 lhs, .f32 rhs => some (.f32 (f32Add lhs rhs))
  | .f32Sub, .f32 lhs, .f32 rhs => some (.f32 (f32Sub lhs rhs))
  | .f32Mul, .f32 lhs, .f32 rhs => some (.f32 (f32Mul lhs rhs))
  | .f32Div, .f32 lhs, .f32 rhs => some (.f32 (f32Div lhs rhs))
  | .f32Min, .f32 lhs, .f32 rhs => some (.f32 (f32Min lhs rhs))
  | .f32Max, .f32 lhs, .f32 rhs => some (.f32 (f32Max lhs rhs))
  | .f32Copysign, .f32 lhs, .f32 rhs =>
      some (.f32 (f32Copysign lhs rhs))
  | .f64Add, .f64 lhs, .f64 rhs => some (.f64 (f64Add lhs rhs))
  | .f64Sub, .f64 lhs, .f64 rhs => some (.f64 (f64Sub lhs rhs))
  | .f64Mul, .f64 lhs, .f64 rhs => some (.f64 (f64Mul lhs rhs))
  | .f64Div, .f64 lhs, .f64 rhs => some (.f64 (f64Div lhs rhs))
  | .f64Min, .f64 lhs, .f64 rhs => some (.f64 (f64Min lhs rhs))
  | .f64Max, .f64 lhs, .f64 rhs => some (.f64 (f64Max lhs rhs))
  | .f64Copysign, .f64 lhs, .f64 rhs =>
      some (.f64 (f64Copysign lhs rhs))
  | .f32Eq, .f32 lhs, .f32 rhs =>
      some (.i32 (if f32Eq lhs rhs then 1 else 0))
  | .f32Ne, .f32 lhs, .f32 rhs =>
      some (.i32 (if f32Ne lhs rhs then 1 else 0))
  | .f32Lt, .f32 lhs, .f32 rhs =>
      some (.i32 (if f32Lt lhs rhs then 1 else 0))
  | .f32Gt, .f32 lhs, .f32 rhs =>
      some (.i32 (if f32Gt lhs rhs then 1 else 0))
  | .f32Le, .f32 lhs, .f32 rhs =>
      some (.i32 (if f32Le lhs rhs then 1 else 0))
  | .f32Ge, .f32 lhs, .f32 rhs =>
      some (.i32 (if f32Ge lhs rhs then 1 else 0))
  | .f64Eq, .f64 lhs, .f64 rhs =>
      some (.i32 (if f64Eq lhs rhs then 1 else 0))
  | .f64Ne, .f64 lhs, .f64 rhs =>
      some (.i32 (if f64Ne lhs rhs then 1 else 0))
  | .f64Lt, .f64 lhs, .f64 rhs =>
      some (.i32 (if f64Lt lhs rhs then 1 else 0))
  | .f64Gt, .f64 lhs, .f64 rhs =>
      some (.i32 (if f64Gt lhs rhs then 1 else 0))
  | .f64Le, .f64 lhs, .f64 rhs =>
      some (.i32 (if f64Le lhs rhs then 1 else 0))
  | .f64Ge, .f64 lhs, .f64 rhs =>
      some (.i32 (if f64Ge lhs rhs then 1 else 0))
  | _, _, _ => none

def branchTarget? (functionArity : Nat) : Nat → List ControlFrame → List Value →
    Option (Program × List ControlFrame × List Value)
  | 0, [], values => some ([], [], values.take functionArity)
  | _ + 1, [], _ => none
  | 0, frame :: outer, values =>
      let arity :=
        match frame.kind with
        | .block | .tryTable _ => frame.resultArity
        | .loop => frame.paramArity
        | .throwing _ _ => 0
      let values := values.take arity ++ frame.belowStack
      match frame.kind with
      | .block | .tryTable _ => some (frame.continuation, outer, values)
      | .loop => some (frame.body, frame :: outer, values)
      | .throwing _ _ => none
  | depth + 1, _ :: outer, values =>
      branchTarget? functionArity depth outer values

def matchingCatch? (tag : Nat) :
    List CatchClause → Option CatchClause
  | [] => none
  | clause :: clauses =>
      let doesMatch : Bool :=
        match clause with
        | .catch expected _ | .catchRef expected _ => expected == tag
        | .catchAll _ | .catchAllRef _ => true
      if doesMatch then some clause else matchingCatch? tag clauses

theorem matchingCatch?_nil (tag : Nat) : matchingCatch? tag [] = none := rfl

theorem matchingCatch?_cons (tag : Nat) (clause : CatchClause) (clauses : List CatchClause) :
    matchingCatch? tag (clause :: clauses) =
    let doesMatch : Bool :=
      match clause with
      | .catch expected _ | .catchRef expected _ => expected == tag
      | .catchAll _ | .catchAllRef _ => true
    if doesMatch then some clause else matchingCatch? tag clauses := rfl

def catchLabel : CatchClause → Nat
  | .catch _ label | .catchRef _ label
  | .catchAll label | .catchAllRef label => label

theorem catchLabel_eq (clause : CatchClause) : catchLabel clause =
    match clause with
    | .catch _ label | .catchRef _ label
    | .catchAll label | .catchAllRef label => label := rfl

def prepareCatch
    (tag : Nat) (arguments : List Value) (clause : CatchClause)
    (store : MachineStore α) : List Value × MachineStore α :=
  match clause with
  | .catch _ _ => (arguments, store)
  | .catchAll _ => ([], store)
  | .catchRef _ _ =>
      let index := store.wasm.exns.length
      (.exnref (some index) :: arguments,
        { store with
          wasm :=
            { store.wasm with
              exns := store.wasm.exns ++ [(tag, arguments)] } })
  | .catchAllRef _ =>
      let index := store.wasm.exns.length
      ([.exnref (some index)],
        { store with
          wasm :=
            { store.wasm with
              exns := store.wasm.exns ++ [(tag, arguments)] } })

theorem prepareCatch_eq (tag : Nat) (arguments : List Value) (clause : CatchClause)
    (store : MachineStore α) : prepareCatch tag arguments clause store =
    match clause with
    | .catch _ _ => (arguments, store)
    | .catchAll _ => ([], store)
    | .catchRef _ _ =>
        let index := store.wasm.exns.length
        (.exnref (some index) :: arguments,
          { store with wasm := { store.wasm with exns := store.wasm.exns ++ [(tag, arguments)] } })
    | .catchAllRef _ =>
        let index := store.wasm.exns.length
        ([.exnref (some index)],
          { store with wasm := { store.wasm with exns := store.wasm.exns ++ [(tag, arguments)] } }) := rfl

/-- Checked executable presentation. Unsupported and malformed configurations
remain diagnostic errors until validation and the corresponding `Step`
constructors are added. -/
private def stepPlainChecked?
    (config : Config α) : Except InternalError (Option (StepKind × Config α)) :=
  match config with
  | ⟨.done _, _⟩ | ⟨.trapped _, _⟩ => .ok none
  | ⟨.running thread, store⟩ =>
    match thread.code with
    | [] =>
      match thread.control with
      | throwingFrame :: handler :: outer =>
        match throwingFrame.kind with
        | .throwing tag arguments =>
          match handler.kind with
          | .tryTable catches =>
            match matchingCatch? tag catches with
            | some clause =>
              let (caughtValues, store') :=
                prepareCatch tag arguments clause store
              match branchTarget? thread.resultArity (catchLabel clause) outer
                  (caughtValues ++ handler.belowStack) with
              | some (code, control, values) =>
                .ok (some (.administrative .catchException,
                  ⟨.running
                    { thread with
                      locals := { thread.locals with values }
                      code
                      control },
                    store'⟩))
              | none =>
                .error ⟨s!"exception catch label {catchLabel clause} is invalid"⟩
            | none =>
              .ok (some (.administrative .unwindException,
                ⟨.running
                  { thread with control := throwingFrame :: outer }, store⟩))
          | .block | .loop =>
            .ok (some (.administrative .unwindException,
              ⟨.running
                { thread with control := throwingFrame :: outer }, store⟩))
          | .throwing _ _ =>
            .ok (some (.administrative .unwindException,
              ⟨.running
                { thread with control := throwingFrame :: outer }, store⟩))
        | _ =>
          .ok (some (.administrative .exitControl,
            ⟨.running
              { thread with
                locals :=
                  { thread.locals with
                    values :=
                      thread.locals.values.take throwingFrame.resultArity ++
                        throwingFrame.belowStack }
                code := throwingFrame.continuation
                control := handler :: outer },
              store⟩))
      | [throwingFrame] =>
        match throwingFrame.kind with
        | .throwing tag arguments =>
          match thread.calls with
          | caller :: calls =>
            .ok (some (.administrative .unwindException,
              ⟨.running
                (resumeExceptionCaller throwingFrame caller calls), store⟩))
          | [] =>
            .ok (some (.administrative .unwindException,
              ⟨.trapped (.uncaughtException tag arguments), store⟩))
        | _ =>
          .ok (some (.administrative .exitControl,
            ⟨.running
              { thread with
                locals :=
                  { thread.locals with
                    values :=
                      thread.locals.values.take throwingFrame.resultArity ++
                        throwingFrame.belowStack }
                code := throwingFrame.continuation
                control := [] },
              store⟩))
      | [] =>
        match thread.calls with
        | [] => .ok (some (.administrative .finish,
            ⟨.done (returnedValues thread), store⟩))
        | caller :: calls =>
          if caller.returningInstance = store.runtime.entry then
            .ok (some (.administrative .returnFromCall,
              ⟨.running (resumeCaller thread caller calls), store⟩))
          else
            .ok (some (.administrative .returnFromCallCrossInstance,
              ⟨.running (resumeCaller thread caller calls),
                { store with runtime :=
                    { store.runtime with entry := caller.returningInstance } }⟩))
    | instr :: rest =>
      let next (locals : Locals) (store' := store) :=
        .ok (some (.instruction instr,
          ⟨.running { thread with locals := locals, code := rest }, store'⟩))
      match instr with
      | .ret =>
        match thread.calls with
        | [] => .ok (some (.administrative .returnFromFunction,
            ⟨.done (returnedValues thread), store⟩))
        | caller :: calls =>
          if caller.returningInstance = store.runtime.entry then
            .ok (some (.administrative .returnFromCall,
              ⟨.running (resumeCaller thread caller calls), store⟩))
          else
            .ok (some (.administrative .returnFromCallCrossInstance,
              ⟨.running (resumeCaller thread caller calls),
                { store with runtime :=
                    { store.runtime with entry := caller.returningInstance } }⟩))
      | .block paramArity resultArity body _ _ =>
        let frame : ControlFrame :=
          { kind := .block, paramArity, resultArity, body,
            continuation := rest,
            belowStack := thread.locals.values.drop paramArity }
        .ok (some (.instruction instr,
          ⟨.running
            { thread with code := body, control := frame :: thread.control },
            store⟩))
      | .loop paramArity resultArity body _ _ =>
        let frame : ControlFrame :=
          { kind := .loop, paramArity, resultArity, body,
            continuation := rest,
            belowStack := thread.locals.values.drop paramArity }
        .ok (some (.instruction instr,
          ⟨.running
            { thread with code := body, control := frame :: thread.control },
            store⟩))
      | .tryTable paramArity resultArity catches body _ _ =>
        let frame : ControlFrame :=
          { kind := .tryTable catches, paramArity, resultArity, body,
            continuation := rest,
            belowStack := thread.locals.values.drop paramArity }
        .ok (some (.instruction instr,
          ⟨.running
            { thread with code := body, control := frame :: thread.control },
            store⟩))
      | .throwI tagIndex =>
        match store.runtime.currentModule.tags[tagIndex]? with
        | some tagType =>
          let count := tagType.params.length
          if thread.locals.values.length < count then
            .error ⟨"throw requires its tag arguments"⟩
          else
            let throwingFrame : ControlFrame :=
              { kind :=
                  .throwing (canonicalTagIndex store tagIndex)
                    (thread.locals.values.take count)
                paramArity := 0
                resultArity := 0
                body := []
                continuation := []
                belowStack := [] }
            .ok (some (.instruction instr,
              ⟨.running
                { thread with
                  locals :=
                    { thread.locals with
                      values := thread.locals.values.drop count }
                  code := []
                  control := throwingFrame :: thread.control },
                store⟩))
        | none => .error ⟨s!"tag index {tagIndex} is invalid"⟩
      | .throwRef =>
        match thread.locals.values with
        | .exnref none :: _ =>
          .ok (some (.instruction instr,
            ⟨.trapped .nullExceptionReference, store⟩))
        | .exnref (some exceptionIndex) :: values =>
          match store.wasm.exns[exceptionIndex]? with
          | some (tag, arguments) =>
            let throwingFrame : ControlFrame :=
              { kind := .throwing tag arguments
                paramArity := 0
                resultArity := 0
                body := []
                continuation := []
                belowStack := [] }
            .ok (some (.instruction instr,
              ⟨.running
                { thread with
                  locals := { thread.locals with values }
                  code := []
                  control := throwingFrame :: thread.control },
                store⟩))
          | none =>
            .error ⟨s!"exception index {exceptionIndex} is invalid"⟩
        | _ => .error ⟨"throw_ref requires an exception reference"⟩
      | .iff paramArity resultArity thenBody elseBody _ _ =>
        match thread.locals.values with
        | .i32 condition :: values =>
          let body := if condition ≠ 0 then thenBody else elseBody
          let frame : ControlFrame :=
            { kind := .block, paramArity, resultArity, body,
              continuation := rest,
              belowStack := values.drop paramArity }
          .ok (some (.instruction instr,
            ⟨.running
              { thread with locals := { thread.locals with values }, code := body, control := frame :: thread.control },
              store⟩))
        | _ => .error ⟨"if requires one i32 condition operand"⟩
      | .br depth =>
        match branchTarget? thread.resultArity depth thread.control
            thread.locals.values with
        | some (code, control, values) =>
          .ok (some (.instruction instr,
            ⟨.running
              { thread with locals := { thread.locals with values }, code, control },
              store⟩))
        | none => .error ⟨s!"branch depth {depth} is invalid"⟩
      | .br_if depth =>
        match thread.locals.values with
        | .i32 0 :: values =>
          next { thread.locals with values }
        | .i32 _ :: values =>
          match branchTarget? thread.resultArity depth thread.control values with
          | some (code, control, values) =>
            .ok (some (.instruction instr,
              ⟨.running
                { thread with locals := { thread.locals with values }, code, control },
                store⟩))
          | none => .error ⟨s!"branch depth {depth} is invalid"⟩
        | _ => .error ⟨"br_if requires one i32 condition operand"⟩
      | .brTable targets defaultTarget =>
        match thread.locals.values with
        | .i32 index :: values =>
          let depth := targets[index.toNat]?.getD defaultTarget
          match branchTarget? thread.resultArity depth thread.control values with
          | some (code, control, values) =>
            .ok (some (.instruction instr,
              ⟨.running
                { thread with
                  locals := { thread.locals with values }, code, control },
                store⟩))
          | none => .error ⟨s!"branch depth {depth} is invalid"⟩
        | _ => .error ⟨"br_table requires one i32 selector operand"⟩
      | .call functionIndex =>
        if functionIndex < store.runtime.currentModule.imports.length then
          match store.runtime.currentModule.imports[functionIndex]?,
              store.runtime.currentHost.funcs[functionIndex]? with
          | some imp, some hostFunction =>
            let hostArgs :=
              (thread.locals.values.take imp.params.length).reverse
            let remaining := thread.locals.values.drop imp.params.length
            match hostFunction.invoke store.wasm hostArgs with
            | .Return results wasm =>
              .ok (some (.host functionIndex,
                ⟨.running
                  { thread with
                    locals :=
                      { thread.locals with
                        values := results.take imp.results.length ++ remaining }
                    code := rest },
                  { store with wasm }⟩))
            | .Trap wasm message =>
              .ok (some (.host functionIndex,
                ⟨.trapped (.host message), { store with wasm }⟩))
            | .Throw wasm tag arguments =>
              let throwingFrame : ControlFrame :=
                { kind := .throwing tag arguments
                  paramArity := 0
                  resultArity := 0
                  body := []
                  continuation := []
                  belowStack := [] }
              .ok (some (.host functionIndex,
                ⟨.running
                  { thread with
                    locals := { thread.locals with values := remaining }
                    code := []
                    control := throwingFrame :: thread.control },
                  { store with wasm }⟩))
          -- no host function: try cross-instance wasm dispatch
          | some imp, none =>
            match store.runtime.currentInstance.resolvedImports[functionIndex]? with
            | some (.wasm calleeId localIdx) =>
              match store.runtime.instances[calleeId.id]? with
              | none => .error ⟨s!"callCrossInstance: instance {calleeId.id} not found"⟩
              | some calleeInstance =>
                match calleeInstance.module.funcs[localIdx]? with
                | none => .error ⟨s!"callCrossInstance: function {localIdx} not found"⟩
                | some fn =>
                  let args := (thread.locals.values.take imp.params.length).reverse
                  let remaining := thread.locals.values.drop imp.params.length
                  let caller : CallFrame :=
                    { locals := { thread.locals with values := remaining }
                      continuation := rest
                      resultArity := thread.resultArity
                      callerRemainder := thread.callerRemainder
                      control := thread.control
                      returningInstance := store.runtime.entry }
                  .ok (some (.administrative .callCrossInstance,
                    ⟨.running
                      { locals := fn.toLocals args
                        code := fn.body
                        resultArity := fn.results.length
                        callerRemainder := []
                        control := []
                        calls := caller :: thread.calls },
                      { store with runtime :=
                          { store.runtime with entry := calleeId } }⟩))
            | _ => .error ⟨s!"unresolved import: index {functionIndex}"⟩
          | _, _ => .error ⟨s!"unresolved host function: index {functionIndex}"⟩
        else
          match store.runtime.currentModule.funcs[
              functionIndex - store.runtime.currentModule.imports.length]? with
          | none => .error ⟨s!"function index {functionIndex} is invalid"⟩
          | some fn =>
            let caller : CallFrame :=
              { locals :=
                  { thread.locals with
                    values := thread.locals.values.drop fn.numParams }
                continuation := rest
                resultArity := thread.resultArity
                callerRemainder := thread.callerRemainder
                control := thread.control
                returningInstance := store.runtime.entry }
            let calleeLocals :=
              fn.toLocals
                (thread.locals.values.take fn.numParams).reverse
            .ok (some (.instruction instr,
              ⟨.running
                { locals := calleeLocals
                  code := fn.body
                  resultArity := fn.results.length
                  callerRemainder := []
                  control := []
                  calls := caller :: thread.calls },
                store⟩))
      -- Cross-instance dispatch asymmetry: only `.call` and `.callIndirect`
      -- consult `resolvedImports` and dispatch to another instance's wasm
      -- function. `returnCall`, `returnCallIndirect`, `callRef`, and
      -- `returnCallRef` on an import resolved as `.wasm _ _` fall through to
      -- `.error "unresolved host function"` below.
      -- TODO(module-linking): extend tail calls and typed function
      -- references with cross-instance dispatch (needs a tail-call variant
      -- of the `returningInstance` bookkeeping).
      | .returnCall functionIndex =>
        if functionIndex < store.runtime.currentModule.imports.length then
          match store.runtime.currentModule.imports[functionIndex]?,
              store.runtime.currentHost.funcs[functionIndex]? with
          | some imp, some hostFunction =>
            let hostArgs :=
              (thread.locals.values.take imp.params.length).reverse
            match hostFunction.invoke store.wasm hostArgs with
            | .Return results wasm =>
              .ok (some (.host functionIndex,
                ⟨.running
                  { thread with
                    locals :=
                      { thread.locals with
                        values := results.take imp.results.length }
                    code := []
                    control := [] },
                  { store with wasm }⟩))
            | .Trap wasm message =>
              .ok (some (.host functionIndex,
                ⟨.trapped (.host message), { store with wasm }⟩))
            | .Throw wasm tag arguments =>
              let throwingFrame : ControlFrame :=
                { kind := .throwing tag arguments
                  paramArity := 0
                  resultArity := 0
                  body := []
                  continuation := []
                  belowStack := [] }
              .ok (some (.host functionIndex,
                ⟨.running
                  { thread with
                    locals := { thread.locals with values := [] }
                    code := []
                    control := [throwingFrame] },
                  { store with wasm }⟩))
          | _, _ => .error ⟨s!"unresolved host function: index {functionIndex}"⟩
        else
          match store.runtime.currentModule.funcs[
              functionIndex - store.runtime.currentModule.imports.length]? with
          | none => .error ⟨s!"function index {functionIndex} is invalid"⟩
          | some fn =>
            let calleeLocals :=
              fn.toLocals
                (thread.locals.values.take fn.numParams).reverse
            .ok (some (.instruction instr,
              ⟨.running
                { locals := calleeLocals
                  code := fn.body
                  resultArity := thread.resultArity
                  callerRemainder := thread.callerRemainder
                  control := []
                  calls := thread.calls },
                store⟩))
      | .callIndirect typeIndex tableIndex =>
        match thread.locals.values with
        | selector :: values =>
          match selector.addrNat?, store.wasm.tables[tableIndex]? with
          | some elementIndex, some table =>
            match table[elementIndex]? with
            | none =>
              .ok (some (.instruction instr,
                ⟨.trapped .undefinedElement, store⟩))
            | some (.funcref none) =>
              .ok (some (.instruction instr,
                ⟨.trapped (.uninitializedElement elementIndex), store⟩))
            | some (.funcref (some functionIndex)) =>
              if isForeignFunctionIndex
                  store.runtime.currentModule.imports.length functionIndex then
                let address := functionIndex - foreignFunctionBase
                match store.runtime.currentHost.foreignFuncs[address]?,
                    store.runtime.currentModule.types[typeIndex]? with
                | some hostFunction, some expected =>
                  if hostFunction.params == expected.params &&
                      hostFunction.results == expected.results then
                    let hostArgs :=
                      (values.take hostFunction.params.length).reverse
                    let remaining := values.drop hostFunction.params.length
                    match hostFunction.invoke store.wasm hostArgs with
                    | .Return results wasm =>
                      .ok (some (.host functionIndex,
                        ⟨.running
                          { thread with
                            locals :=
                              { thread.locals with
                                values :=
                                  results.take hostFunction.results.length ++
                                    remaining }
                            code := rest },
                          { store with wasm }⟩))
                    | .Trap wasm message =>
                      .ok (some (.host functionIndex,
                        ⟨.trapped (.host message), { store with wasm }⟩))
                    | .Throw wasm tag arguments =>
                      let throwingFrame : ControlFrame :=
                        { kind := .throwing tag arguments
                          paramArity := 0
                          resultArity := 0
                          body := []
                          continuation := []
                          belowStack := [] }
                      .ok (some (.host functionIndex,
                        ⟨.running
                          { thread with
                            locals := { thread.locals with values := remaining }
                            code := []
                            control := throwingFrame :: thread.control },
                          { store with wasm }⟩))
                  else
                    .ok (some (.instruction instr,
                      ⟨.trapped .indirectCallTypeMismatch, store⟩))
                | _, _ =>
                  .error ⟨"foreign indirect call has an invalid function or type index"⟩
              else if functionIndex < store.runtime.currentModule.imports.length then
                match store.runtime.currentModule.imports[functionIndex]?,
                    store.runtime.currentHost.funcs[functionIndex]?,
                    store.runtime.currentModule.funcSig? functionIndex,
                    store.runtime.currentModule.types[typeIndex]? with
                | some imp, some hostFunction, some signature, some expected =>
                  if store.runtime.currentModule.indirectCallTypeOk
                      functionIndex typeIndex signature expected = true then
                    let hostArgs := (values.take imp.params.length).reverse
                    let remaining := values.drop imp.params.length
                    match hostFunction.invoke store.wasm hostArgs with
                    | .Return results wasm =>
                      .ok (some (.host functionIndex,
                        ⟨.running
                          { thread with
                            locals :=
                              { thread.locals with
                                values :=
                                  results.take imp.results.length ++ remaining }
                            code := rest },
                          { store with wasm }⟩))
                    | .Trap wasm message =>
                      .ok (some (.host functionIndex,
                        ⟨.trapped (.host message), { store with wasm }⟩))
                    | .Throw wasm tag arguments =>
                      let throwingFrame : ControlFrame :=
                        { kind := .throwing tag arguments
                          paramArity := 0
                          resultArity := 0
                          body := []
                          continuation := []
                          belowStack := [] }
                      .ok (some (.host functionIndex,
                        ⟨.running
                          { thread with
                            locals := { thread.locals with values := remaining }
                            code := []
                            control := throwingFrame :: thread.control },
                          { store with wasm }⟩))
                  else
                    .ok (some (.instruction instr,
                      ⟨.trapped .indirectCallTypeMismatch, store⟩))
                | some imp, none, some signature, some expected =>
                  match store.runtime.currentInstance.resolvedImports[functionIndex]? with
                  | some (.wasm calleeId localIdx) =>
                    if store.runtime.currentModule.indirectCallTypeOk
                        functionIndex typeIndex signature expected = true then
                      match store.runtime.instances[calleeId.id]? with
                      | some calleeInstance =>
                        match calleeInstance.module.funcs[localIdx]? with
                        | some fn =>
                          let args := (values.take imp.params.length).reverse
                          let remaining := values.drop imp.params.length
                          let caller : CallFrame :=
                            { locals := { thread.locals with values := remaining }
                              continuation := rest
                              resultArity := thread.resultArity
                              callerRemainder := thread.callerRemainder
                              control := thread.control
                              returningInstance := store.runtime.entry }
                          .ok (some (.administrative .callCrossInstance,
                            ⟨.running
                              { locals := fn.toLocals args
                                code := fn.body
                                resultArity := fn.results.length
                                callerRemainder := []
                                control := []
                                calls := caller :: thread.calls },
                              { store with runtime :=
                                  { store.runtime with entry := calleeId } }⟩))
                        | none =>
                          .error ⟨s!"callIndirect cross-instance: function {localIdx} not found"⟩
                      | none =>
                        .error ⟨s!"callIndirect cross-instance: instance {calleeId.id} not found"⟩
                    else
                      .ok (some (.instruction instr,
                        ⟨.trapped .indirectCallTypeMismatch, store⟩))
                  | _ => .error ⟨s!"callIndirect: unresolved import {functionIndex}"⟩
                | _, _, _, _ =>
                  .error ⟨"indirect host call has an invalid function or type index"⟩
              else
                match store.runtime.currentModule.funcs[
                    functionIndex - store.runtime.currentModule.imports.length]?,
                    store.runtime.currentModule.funcSig? functionIndex,
                    store.runtime.currentModule.types[typeIndex]? with
                | some fn, some signature, some expected =>
                  if store.runtime.currentModule.indirectCallTypeOk
                      functionIndex typeIndex signature expected = true then
                    let caller : CallFrame :=
                      { locals :=
                          { thread.locals with
                            values := values.drop fn.numParams }
                        continuation := rest
                        resultArity := thread.resultArity
                        callerRemainder := thread.callerRemainder
                        control := thread.control
                        returningInstance := store.runtime.entry }
                    .ok (some (.instruction instr,
                      ⟨.running
                        { locals :=
                            fn.toLocals
                              (values.take fn.numParams).reverse
                          code := fn.body
                          resultArity := fn.results.length
                          callerRemainder := []
                          control := []
                          calls := caller :: thread.calls },
                        store⟩))
                  else
                    .ok (some (.instruction instr,
                      ⟨.trapped .indirectCallTypeMismatch, store⟩))
                | _, _, _ =>
                  .error ⟨"indirect call has an invalid function or type index"⟩
            | some _ => .error ⟨"indirect call requires a funcref table entry"⟩
          | none, _ => .error ⟨"call_indirect requires an integer selector"⟩
          | _, none => .error ⟨s!"table index {tableIndex} is invalid"⟩
        | [] => .error ⟨"call_indirect requires an integer selector"⟩
      | .returnCallIndirect typeIndex tableIndex =>
        match thread.locals.values with
        | selector :: values =>
          match selector.addrNat?, store.wasm.tables[tableIndex]? with
          | some elementIndex, some table =>
            match table[elementIndex]? with
            | none =>
              .ok (some (.instruction instr,
                ⟨.trapped .undefinedElement, store⟩))
            | some (.funcref none) =>
              .ok (some (.instruction instr,
                ⟨.trapped (.uninitializedElement elementIndex), store⟩))
            | some (.funcref (some functionIndex)) =>
              if functionIndex < store.runtime.currentModule.imports.length then
                match store.runtime.currentModule.imports[functionIndex]?,
                    store.runtime.currentHost.funcs[functionIndex]?,
                    store.runtime.currentModule.funcSig? functionIndex,
                    store.runtime.currentModule.types[typeIndex]? with
                | some imp, some hostFunction, some signature, some expected =>
                  if store.runtime.currentModule.indirectCallTypeOk
                      functionIndex typeIndex signature expected = true then
                    let hostArgs := (values.take imp.params.length).reverse
                    match hostFunction.invoke store.wasm hostArgs with
                    | .Return results wasm =>
                      .ok (some (.host functionIndex,
                        ⟨.running
                          { thread with
                            locals :=
                              { thread.locals with
                                values := results.take imp.results.length }
                            code := []
                            control := [] },
                          { store with wasm }⟩))
                    | .Trap wasm message =>
                      .ok (some (.host functionIndex,
                        ⟨.trapped (.host message), { store with wasm }⟩))
                    | .Throw wasm tag arguments =>
                      let throwingFrame : ControlFrame :=
                        { kind := .throwing tag arguments
                          paramArity := 0
                          resultArity := 0
                          body := []
                          continuation := []
                          belowStack := [] }
                      .ok (some (.host functionIndex,
                        ⟨.running
                          { thread with
                            locals := { thread.locals with values := [] }
                            code := []
                            control := [throwingFrame] },
                          { store with wasm }⟩))
                  else
                    .ok (some (.instruction instr,
                      ⟨.trapped .indirectCallTypeMismatch, store⟩))
                | _, _, _, _ =>
                  .error ⟨"indirect host tail call has an invalid function or type index"⟩
              else
                match store.runtime.currentModule.funcs[
                    functionIndex - store.runtime.currentModule.imports.length]?,
                    store.runtime.currentModule.funcSig? functionIndex,
                    store.runtime.currentModule.types[typeIndex]? with
                | some fn, some signature, some expected =>
                  if store.runtime.currentModule.indirectCallTypeOk
                      functionIndex typeIndex signature expected = true then
                    .ok (some (.instruction instr,
                      ⟨.running
                        { locals :=
                            fn.toLocals
                              (values.take fn.numParams).reverse
                          code := fn.body
                          resultArity := thread.resultArity
                          callerRemainder := thread.callerRemainder
                          control := []
                          calls := thread.calls },
                        store⟩))
                  else
                    .ok (some (.instruction instr,
                      ⟨.trapped .indirectCallTypeMismatch, store⟩))
                | _, _, _ =>
                  .error ⟨"indirect tail call has an invalid function or type index"⟩
            | some _ => .error ⟨"indirect tail call requires a funcref table entry"⟩
          | none, _ => .error ⟨"return_call_indirect requires an integer selector"⟩
          | _, none => .error ⟨s!"table index {tableIndex} is invalid"⟩
        | [] => .error ⟨"return_call_indirect requires an integer selector"⟩
      | .refNull _ =>
        next { thread.locals with
          values := .funcref none :: thread.locals.values }
      | .refNullExtern _ =>
        next { thread.locals with
          values := .externref none :: thread.locals.values }
      | .refNullExn _ =>
        next { thread.locals with
          values := .exnref none :: thread.locals.values }
      | .refFunc functionIndex =>
        next { thread.locals with
          values := .funcref (some functionIndex) :: thread.locals.values }
      | .callRef _ =>
        match thread.locals.values with
        | .funcref none :: _ =>
          .ok (some (.instruction instr,
            ⟨.trapped .nullFunctionReference, store⟩))
        | .funcref (some functionIndex) :: values =>
          if functionIndex < store.runtime.currentModule.imports.length then
            match store.runtime.currentModule.imports[functionIndex]?,
                store.runtime.currentHost.funcs[functionIndex]? with
            | some imp, some hostFunction =>
              let hostArgs := (values.take imp.params.length).reverse
              let remaining := values.drop imp.params.length
              match hostFunction.invoke store.wasm hostArgs with
              | .Return results wasm =>
                .ok (some (.host functionIndex,
                  ⟨.running
                    { thread with
                      locals :=
                        { thread.locals with
                          values := results.take imp.results.length ++ remaining }
                      code := rest },
                    { store with wasm }⟩))
              | .Trap wasm message =>
                .ok (some (.host functionIndex,
                  ⟨.trapped (.host message), { store with wasm }⟩))
              | .Throw wasm tag arguments =>
                let throwingFrame : ControlFrame :=
                  { kind := .throwing tag arguments
                    paramArity := 0
                    resultArity := 0
                    body := []
                    continuation := []
                    belowStack := [] }
                .ok (some (.host functionIndex,
                  ⟨.running
                    { thread with
                      locals := { thread.locals with values := remaining }
                      code := []
                      control := throwingFrame :: thread.control },
                    { store with wasm }⟩))
            | _, _ =>
              .error ⟨s!"unresolved host function: index {functionIndex}"⟩
          else
            match store.runtime.currentModule.funcs[
                functionIndex - store.runtime.currentModule.imports.length]? with
            | some fn =>
              let caller : CallFrame :=
                { locals :=
                    { thread.locals with
                      values := values.drop fn.numParams }
                  continuation := rest
                  resultArity := thread.resultArity
                  callerRemainder := thread.callerRemainder
                  control := thread.control
                  returningInstance := store.runtime.entry }
              .ok (some (.instruction instr,
                ⟨.running
                  { locals :=
                      fn.toLocals (values.take fn.numParams).reverse
                    code := fn.body
                    resultArity := fn.results.length
                    callerRemainder := []
                    control := []
                    calls := caller :: thread.calls },
                  store⟩))
            | none => .error ⟨s!"function index {functionIndex} is invalid"⟩
        | _ => .error ⟨"call_ref requires a funcref operand"⟩
      | .returnCallRef _ =>
        match thread.locals.values with
        | .funcref none :: _ =>
          .ok (some (.instruction instr,
            ⟨.trapped .nullFunctionReference, store⟩))
        | .funcref (some functionIndex) :: values =>
          if functionIndex < store.runtime.currentModule.imports.length then
            match store.runtime.currentModule.imports[functionIndex]?,
                store.runtime.currentHost.funcs[functionIndex]? with
            | some imp, some hostFunction =>
              let hostArgs := (values.take imp.params.length).reverse
              match hostFunction.invoke store.wasm hostArgs with
              | .Return results wasm =>
                .ok (some (.host functionIndex,
                  ⟨.running
                    { thread with
                      locals :=
                        { thread.locals with
                          values := results.take imp.results.length }
                      code := []
                      control := [] },
                    { store with wasm }⟩))
              | .Trap wasm message =>
                .ok (some (.host functionIndex,
                  ⟨.trapped (.host message), { store with wasm }⟩))
              | .Throw wasm tag arguments =>
                let throwingFrame : ControlFrame :=
                  { kind := .throwing tag arguments
                    paramArity := 0
                    resultArity := 0
                    body := []
                    continuation := []
                    belowStack := [] }
                .ok (some (.host functionIndex,
                  ⟨.running
                    { thread with
                      locals := { thread.locals with values := [] }
                      code := []
                      control := [throwingFrame] },
                    { store with wasm }⟩))
            | _, _ =>
              .error ⟨s!"unresolved host function: index {functionIndex}"⟩
          else
            match store.runtime.currentModule.funcs[
                functionIndex - store.runtime.currentModule.imports.length]? with
            | some fn =>
              .ok (some (.instruction instr,
                ⟨.running
                  { locals :=
                      fn.toLocals (values.take fn.numParams).reverse
                    code := fn.body
                    resultArity := thread.resultArity
                    callerRemainder := thread.callerRemainder
                    control := []
                    calls := thread.calls },
                  store⟩))
            | none => .error ⟨s!"function index {functionIndex} is invalid"⟩
        | _ => .error ⟨"return_call_ref requires a funcref operand"⟩
      | .refIsNull =>
        match thread.locals.values with
        | value :: values =>
          match value.isNullRef? with
          | some isNull =>
            next { thread.locals with
              values := .i32 (if isNull then 1 else 0) :: values }
          | none => .error ⟨"ref.is_null requires a reference operand"⟩
        | [] => .error ⟨"ref.is_null requires a reference operand"⟩
      | .refAsNonNull =>
        match thread.locals.values with
        | value :: _ =>
          match value.isNullRef? with
          | some true =>
            .ok (some (.instruction instr, ⟨.trapped .nullReference, store⟩))
          | some false => next thread.locals
          | none => .error ⟨"ref.as_non_null requires a reference operand"⟩
        | [] => .error ⟨"ref.as_non_null requires a reference operand"⟩
      | .brOnNull depth =>
        match thread.locals.values with
        | value :: values =>
          match value.isNullRef? with
          | some true =>
            match branchTarget? thread.resultArity depth thread.control values with
            | some (targetCode, targetControl, targetValues) =>
              .ok (some (.instruction instr,
                ⟨.running
                  { thread with
                    locals := { thread.locals with values := targetValues }
                    code := targetCode
                    control := targetControl },
                  store⟩))
            | none => .error ⟨s!"branch depth {depth} is invalid"⟩
          | some false => next thread.locals
          | none => .error ⟨"br_on_null requires a reference operand"⟩
        | [] => .error ⟨"br_on_null requires a reference operand"⟩
      | .brOnNonNull depth =>
        match thread.locals.values with
        | value :: values =>
          match value.isNullRef? with
          | some true => next { thread.locals with values }
          | some false =>
            match branchTarget? thread.resultArity depth thread.control
                (value :: values) with
            | some (targetCode, targetControl, targetValues) =>
              .ok (some (.instruction instr,
                ⟨.running
                  { thread with
                    locals := { thread.locals with values := targetValues }
                    code := targetCode
                    control := targetControl },
                  store⟩))
            | none => .error ⟨s!"branch depth {depth} is invalid"⟩
          | none => .error ⟨"br_on_non_null requires a reference operand"⟩
        | [] => .error ⟨"br_on_non_null requires a reference operand"⟩
      | .tableGet tableIndex =>
        match thread.locals.values with
        | index :: values =>
          match index.addrNat?, store.wasm.tables[tableIndex]? with
          | some elementIndex, some table =>
            match table[elementIndex]? with
            | some value =>
              next { thread.locals with values := value :: values }
            | none =>
              .ok (some (.instruction instr,
                ⟨.trapped .outOfBoundsTable, store⟩))
          | none, _ => .error ⟨"table.get requires an integer index operand"⟩
          | _, none => .error ⟨s!"table index {tableIndex} is invalid"⟩
        | [] => .error ⟨"table.get requires an integer index operand"⟩
      | .tableSize tableIndex =>
        match store.wasm.tables[tableIndex]? with
        | some table =>
          next { thread.locals with
            values :=
              sizeValue (store.runtime.currentModule.tableIs64 tableIndex)
                table.length :: thread.locals.values }
        | none => .error ⟨s!"table index {tableIndex} is invalid"⟩
      | .tableSet tableIndex =>
        match thread.locals.values with
        | value :: index :: values =>
          match index.addrNat?, store.wasm.tables[tableIndex]? with
          | some elementIndex, some table =>
            if elementIndex < table.length then
              next { thread.locals with values }
                (setTables store
                  (listSetAt store.wasm.tables tableIndex
                    (listSetAt table elementIndex value)))
            else
              .ok (some (.instruction instr,
                ⟨.trapped .outOfBoundsTable, store⟩))
          | none, _ => .error ⟨"table.set requires an integer index operand"⟩
          | _, none => .error ⟨s!"table index {tableIndex} is invalid"⟩
        | _ => .error ⟨"table.set requires a value and integer index operands"⟩
      | .tableGrow tableIndex =>
        match thread.locals.values with
        | .i32 delta :: initial :: values =>
          match store.wasm.tables[tableIndex]? with
          | some table =>
            if table.length + delta.toNat ≤
                store.runtime.currentModule.tableCap tableIndex then
              next { thread.locals with
                values := .i32 table.length.toUInt32 :: values }
                (setTables store
                  (listSetAt store.wasm.tables tableIndex
                    (table ++ List.replicate delta.toNat initial)))
            else
              next { thread.locals with
                values := .i32 (0xFFFFFFFF : UInt32) :: values }
          | none => .error ⟨s!"table index {tableIndex} is invalid"⟩
        | .i64 delta :: initial :: values =>
          match store.wasm.tables[tableIndex]? with
          | some table =>
            if table.length + delta.toNat ≤
                store.runtime.currentModule.tableCap tableIndex then
              next { thread.locals with
                values := .i64 table.length.toUInt64 :: values }
                (setTables store
                  (listSetAt store.wasm.tables tableIndex
                    (table ++ List.replicate delta.toNat initial)))
            else
              next { thread.locals with
                values := .i64 (0xFFFFFFFFFFFFFFFF : UInt64) :: values }
          | none => .error ⟨s!"table index {tableIndex} is invalid"⟩
        | _ => .error ⟨"table.grow requires a reference and integer delta operands"⟩
      | .tableFill tableIndex =>
        match thread.locals.values with
        | length :: value :: destination :: values =>
          match length.addrNat?, destination.addrNat?,
              store.wasm.tables[tableIndex]? with
          | some length, some destination, some table =>
            if destination + length > table.length then
              .ok (some (.instruction instr,
                ⟨.trapped .outOfBoundsTable, store⟩))
            else
              next { thread.locals with values }
                (setTables store
                  (listSetAt store.wasm.tables tableIndex
                    (listWriteAt table destination
                      (List.replicate length value))))
          | none, _, _ | _, none, _ =>
            .error ⟨"table.fill requires integer destination and length operands"⟩
          | _, _, none => .error ⟨s!"table index {tableIndex} is invalid"⟩
        | _ => .error ⟨"table.fill requires destination, value, and length operands"⟩
      | .tableCopy destinationTableIndex sourceTableIndex =>
        match thread.locals.values with
        | length :: source :: destination :: values =>
          match length.addrNat?, source.addrNat?, destination.addrNat?,
              store.wasm.tables[destinationTableIndex]?,
              store.wasm.tables[sourceTableIndex]? with
          | some length, some source, some destination,
              some destinationTable, some sourceTable =>
            if destination + length > destinationTable.length ∨
                source + length > sourceTable.length then
              .ok (some (.instruction instr,
                ⟨.trapped .outOfBoundsTable, store⟩))
            else
              let slice := (sourceTable.drop source).take length
              next { thread.locals with values }
                (setTables store
                  (listSetAt store.wasm.tables destinationTableIndex
                    (listWriteAt destinationTable destination slice)))
          | none, _, _, _, _ | _, none, _, _, _ | _, _, none, _, _ =>
            .error ⟨"table.copy requires integer destination, source, and length operands"⟩
          | _, _, _, none, _ | _, _, _, _, none =>
            .error ⟨"table.copy table index is invalid"⟩
        | _ => .error ⟨"table.copy requires destination, source, and length operands"⟩
      | .tableInit tableIndex elementIndex =>
        match thread.locals.values with
        | .i32 length :: .i32 source :: destination :: values =>
          match destination.addrNat?, store.wasm.tables[tableIndex]?,
              store.wasm.elementSegments[elementIndex]? with
          | some destination, some table, some segmentState =>
            let segmentValues :=
              elementSegmentValues store elementIndex segmentState
            if source.toNat + length.toNat > segmentValues.length ∨
                destination + length.toNat > table.length then
              .ok (some (.instruction instr,
                ⟨.trapped .outOfBoundsTable, store⟩))
            else
              let slice :=
                (segmentValues.drop source.toNat).take length.toNat
              next { thread.locals with values }
                (setTables store
                  (listSetAt store.wasm.tables tableIndex
                    (listWriteAt table destination slice)))
          | none, _, _ =>
            .error ⟨"table.init requires an integer destination operand"⟩
          | _, none, _ => .error ⟨s!"table index {tableIndex} is invalid"⟩
          | _, _, none => .error ⟨s!"element segment index {elementIndex} is invalid"⟩
        | _ =>
          .error ⟨"table.init requires destination, i32 source, and i32 length operands"⟩
      | .elemDrop elementIndex =>
        match store.wasm.elementSegments[elementIndex]? with
        | some _ =>
          next thread.locals
            (setElementSegments store
              (store.wasm.elementSegments.set elementIndex none))
        | none => .error ⟨s!"element segment index {elementIndex} is invalid"⟩
      | .unreachable => .ok (some (.instruction instr, ⟨.trapped .unreachable, store⟩))
      | .nop => next thread.locals
      | .drop =>
        match thread.locals.values with
        | _ :: values => next { thread.locals with values }
        | _ => .error ⟨"drop requires one operand"⟩
      | .select =>
        match thread.locals.values with
        | .i32 condition :: second :: first :: values =>
          next { thread.locals with
            values := (if condition ≠ 0 then first else second) :: values }
        | _ => .error ⟨"select requires two values and an i32 condition"⟩
      | .const value =>
          next { thread.locals with values := .i32 value :: thread.locals.values }
      | .constI64 value =>
          next { thread.locals with values := .i64 value :: thread.locals.values }
      | .localGet index =>
        match thread.locals.get index with
        | some value => next { thread.locals with values := value :: thread.locals.values }
        | none => .error ⟨s!"local.get index {index} is invalid"⟩
      | .localSet index =>
        match thread.locals.values with
        | value :: values =>
          match thread.locals.set? index value with
          | some locals => next { locals with values := values }
          | none => .error ⟨s!"local.set index {index} is invalid"⟩
        | _ => .error ⟨"local.set requires one operand"⟩
      | .globalGet index =>
        match globalAt? store index with
        | some value => next { thread.locals with values := value :: thread.locals.values }
        | none => .error ⟨s!"global.get index {index} is invalid"⟩
      | .globalSet index =>
        match thread.locals.values, globalAt? store index with
        | value :: values, some _ =>
          next { thread.locals with values := values }
            (setGlobal store index value)
        | [], _ => .error ⟨"global.set requires one operand"⟩
        | _, none => .error ⟨s!"global.set index {index} is invalid"⟩
      | .add =>
        match thread.locals.values with
        | .i32 a :: .i32 b :: values =>
            next { thread.locals with values := .i32 (a + b) :: values }
        | _ => .error ⟨"i32.add requires two i32 operands"⟩
      | .sub =>
        match thread.locals.values with
        | .i32 a :: .i32 b :: values =>
            next { thread.locals with values := .i32 (b - a) :: values }
        | _ => .error ⟨"i32.sub requires two i32 operands"⟩
      | .mul =>
        match thread.locals.values with
        | .i32 a :: .i32 b :: values =>
            next { thread.locals with values := .i32 (a * b) :: values }
        | _ => .error ⟨"i32.mul requires two i32 operands"⟩
      | .and =>
        match thread.locals.values with
        | .i32 rhs :: .i32 lhs :: values =>
          next { thread.locals with values := .i32 (lhs &&& rhs) :: values }
        | _ => .error ⟨"i32.and requires two i32 operands"⟩
      | .or =>
        match thread.locals.values with
        | .i32 rhs :: .i32 lhs :: values =>
          next { thread.locals with values := .i32 (lhs ||| rhs) :: values }
        | _ => .error ⟨"i32.or requires two i32 operands"⟩
      | .xor =>
        match thread.locals.values with
        | .i32 rhs :: .i32 lhs :: values =>
          next { thread.locals with values := .i32 (lhs ^^^ rhs) :: values }
        | _ => .error ⟨"i32.xor requires two i32 operands"⟩
      | .shl =>
        match thread.locals.values with
        | .i32 rhs :: .i32 lhs :: values =>
          next { thread.locals with values := .i32 (lhs <<< (rhs % 32)) :: values }
        | _ => .error ⟨"i32.shl requires two i32 operands"⟩
      | .shrU =>
        match thread.locals.values with
        | .i32 rhs :: .i32 lhs :: values =>
          next { thread.locals with values := .i32 (lhs >>> (rhs % 32)) :: values }
        | _ => .error ⟨"i32.shr_u requires two i32 operands"⟩
      | .shrS =>
        match thread.locals.values with
        | .i32 rhs :: .i32 lhs :: values =>
          let shifted := UInt32.ofNat
            (BitVec.sshiftRight lhs.toBitVec (rhs % 32).toNat).toNat
          next { thread.locals with values := .i32 shifted :: values }
        | _ => .error ⟨"i32.shr_s requires two i32 operands"⟩
      | .rotl =>
        match thread.locals.values with
        | .i32 rhs :: .i32 lhs :: values =>
          next { thread.locals with
            values := .i32 (rotateLeft32 lhs rhs) :: values }
        | _ => .error ⟨"i32.rotl requires two i32 operands"⟩
      | .rotr =>
        match thread.locals.values with
        | .i32 rhs :: .i32 lhs :: values =>
          next { thread.locals with
            values := .i32 (rotateRight32 lhs rhs) :: values }
        | _ => .error ⟨"i32.rotr requires two i32 operands"⟩
      | .clz =>
        match thread.locals.values with
        | .i32 value :: values =>
          next { thread.locals with
            values := .i32 (UInt32.ofNat (clz32 32 value)) :: values }
        | _ => .error ⟨"i32.clz requires one i32 operand"⟩
      | .ctz =>
        match thread.locals.values with
        | .i32 value :: values =>
          next { thread.locals with
            values := .i32 (UInt32.ofNat (ctz32 32 value)) :: values }
        | _ => .error ⟨"i32.ctz requires one i32 operand"⟩
      | .popcnt =>
        match thread.locals.values with
        | .i32 value :: values =>
          next { thread.locals with
            values := .i32 (UInt32.ofNat (popcnt32 32 value 0)) :: values }
        | _ => .error ⟨"i32.popcnt requires one i32 operand"⟩
      | .addI64 =>
        match thread.locals.values with
        | .i64 rhs :: .i64 lhs :: values =>
            next { thread.locals with values := .i64 (lhs + rhs) :: values }
        | _ => .error ⟨"i64.add requires two i64 operands"⟩
      | .subI64 =>
        match thread.locals.values with
        | .i64 rhs :: .i64 lhs :: values =>
            next { thread.locals with values := .i64 (lhs - rhs) :: values }
        | _ => .error ⟨"i64.sub requires two i64 operands"⟩
      | .mulI64 =>
        match thread.locals.values with
        | .i64 rhs :: .i64 lhs :: values =>
            next { thread.locals with values := .i64 (lhs * rhs) :: values }
        | _ => .error ⟨"i64.mul requires two i64 operands"⟩
      | .andI64 =>
        match thread.locals.values with
        | .i64 rhs :: .i64 lhs :: values =>
          next { thread.locals with values := .i64 (lhs &&& rhs) :: values }
        | _ => .error ⟨"i64.and requires two i64 operands"⟩
      | .orI64 =>
        match thread.locals.values with
        | .i64 rhs :: .i64 lhs :: values =>
          next { thread.locals with values := .i64 (lhs ||| rhs) :: values }
        | _ => .error ⟨"i64.or requires two i64 operands"⟩
      | .xorI64 =>
        match thread.locals.values with
        | .i64 rhs :: .i64 lhs :: values =>
          next { thread.locals with values := .i64 (lhs ^^^ rhs) :: values }
        | _ => .error ⟨"i64.xor requires two i64 operands"⟩
      | .shlI64 =>
        match thread.locals.values with
        | .i64 rhs :: .i64 lhs :: values =>
          next { thread.locals with values := .i64 (lhs <<< (rhs % 64)) :: values }
        | _ => .error ⟨"i64.shl requires two i64 operands"⟩
      | .shrUI64 =>
        match thread.locals.values with
        | .i64 rhs :: .i64 lhs :: values =>
          next { thread.locals with values := .i64 (lhs >>> (rhs % 64)) :: values }
        | _ => .error ⟨"i64.shr_u requires two i64 operands"⟩
      | .shrSI64 =>
        match thread.locals.values with
        | .i64 rhs :: .i64 lhs :: values =>
          let shifted := UInt64.ofNat
            (BitVec.sshiftRight lhs.toBitVec (rhs % 64).toNat).toNat
          next { thread.locals with values := .i64 shifted :: values }
        | _ => .error ⟨"i64.shr_s requires two i64 operands"⟩
      | .rotlI64 =>
        match thread.locals.values with
        | .i64 rhs :: .i64 lhs :: values =>
          next { thread.locals with
            values := .i64 (rotateLeft64 lhs rhs) :: values }
        | _ => .error ⟨"i64.rotl requires two i64 operands"⟩
      | .rotrI64 =>
        match thread.locals.values with
        | .i64 rhs :: .i64 lhs :: values =>
          next { thread.locals with
            values := .i64 (rotateRight64 lhs rhs) :: values }
        | _ => .error ⟨"i64.rotr requires two i64 operands"⟩
      | .clzI64 =>
        match thread.locals.values with
        | .i64 value :: values =>
          next { thread.locals with
            values := .i64 (UInt64.ofNat (clz64 64 value)) :: values }
        | _ => .error ⟨"i64.clz requires one i64 operand"⟩
      | .ctzI64 =>
        match thread.locals.values with
        | .i64 value :: values =>
          next { thread.locals with
            values := .i64 (UInt64.ofNat (ctz64 64 value)) :: values }
        | _ => .error ⟨"i64.ctz requires one i64 operand"⟩
      | .popcntI64 =>
        match thread.locals.values with
        | .i64 value :: values =>
          next { thread.locals with
            values := .i64 (UInt64.ofNat (popcnt64 64 value 0)) :: values }
        | _ => .error ⟨"i64.popcnt requires one i64 operand"⟩
      | .divU =>
        match thread.locals.values with
        | .i32 0 :: .i32 _ :: _ =>
            .ok (some (.instruction instr, ⟨.trapped .integerDivideByZero, store⟩))
        | .i32 divisor :: .i32 dividend :: values =>
            next { thread.locals with values := .i32 (dividend / divisor) :: values }
        | _ => .error ⟨"i32.div_u requires two i32 operands"⟩
      | .divS =>
        match thread.locals.values with
        | .i32 0 :: .i32 _ :: _ =>
            .ok (some (.instruction instr, ⟨.trapped .integerDivideByZero, store⟩))
        | .i32 0xFFFFFFFF :: .i32 0x80000000 :: _ =>
            .ok (some (.instruction instr, ⟨.trapped .integerOverflow, store⟩))
        | .i32 divisor :: .i32 dividend :: values =>
            next { thread.locals with
              values := .i32 (signedDiv32 dividend divisor) :: values }
        | _ => .error ⟨"i32.div_s requires two i32 operands"⟩
      | .remU =>
        match thread.locals.values with
        | .i32 0 :: .i32 _ :: _ =>
            .ok (some (.instruction instr, ⟨.trapped .integerDivideByZero, store⟩))
        | .i32 divisor :: .i32 dividend :: values =>
            next { thread.locals with values := .i32 (dividend % divisor) :: values }
        | _ => .error ⟨"i32.rem_u requires two i32 operands"⟩
      | .remS =>
        match thread.locals.values with
        | .i32 0 :: .i32 _ :: _ =>
            .ok (some (.instruction instr, ⟨.trapped .integerDivideByZero, store⟩))
        | .i32 divisor :: .i32 dividend :: values =>
            next { thread.locals with
              values := .i32 (signedRem32 dividend divisor) :: values }
        | _ => .error ⟨"i32.rem_s requires two i32 operands"⟩
      | .divUI64 =>
        match thread.locals.values with
        | .i64 0 :: .i64 _ :: _ =>
            .ok (some (.instruction instr, ⟨.trapped .integerDivideByZero, store⟩))
        | .i64 divisor :: .i64 dividend :: values =>
            next { thread.locals with values := .i64 (dividend / divisor) :: values }
        | _ => .error ⟨"i64.div_u requires two i64 operands"⟩
      | .divSI64 =>
        match thread.locals.values with
        | .i64 0 :: .i64 _ :: _ =>
            .ok (some (.instruction instr, ⟨.trapped .integerDivideByZero, store⟩))
        | .i64 0xFFFFFFFFFFFFFFFF :: .i64 0x8000000000000000 :: _ =>
            .ok (some (.instruction instr, ⟨.trapped .integerOverflow, store⟩))
        | .i64 divisor :: .i64 dividend :: values =>
            next { thread.locals with
              values := .i64 (signedDiv64 dividend divisor) :: values }
        | _ => .error ⟨"i64.div_s requires two i64 operands"⟩
      | .remUI64 =>
        match thread.locals.values with
        | .i64 0 :: .i64 _ :: _ =>
            .ok (some (.instruction instr, ⟨.trapped .integerDivideByZero, store⟩))
        | .i64 divisor :: .i64 dividend :: values =>
            next { thread.locals with values := .i64 (dividend % divisor) :: values }
        | _ => .error ⟨"i64.rem_u requires two i64 operands"⟩
      | .remSI64 =>
        match thread.locals.values with
        | .i64 0 :: .i64 _ :: _ =>
            .ok (some (.instruction instr, ⟨.trapped .integerDivideByZero, store⟩))
        | .i64 divisor :: .i64 dividend :: values =>
            next { thread.locals with
              values := .i64 (signedRem64 dividend divisor) :: values }
        | _ => .error ⟨"i64.rem_s requires two i64 operands"⟩
      | .i32TruncF32S | .i32TruncF32U =>
        match thread.locals.values with
        | operand@(.f32 _) :: values =>
          match evalScalarTrunc? instr operand with
          | some (.ok value) =>
            next { thread.locals with values := value :: values }
          | some (.error reason) =>
            .ok (some (.instruction instr, ⟨.trapped reason, store⟩))
          | none => .error ⟨"invalid i32 truncation operation"⟩
        | _ => .error ⟨"i32 truncation requires one f32 operand"⟩
      | .i32TruncF64S | .i32TruncF64U =>
        match thread.locals.values with
        | operand@(.f64 _) :: values =>
          match evalScalarTrunc? instr operand with
          | some (.ok value) =>
            next { thread.locals with values := value :: values }
          | some (.error reason) =>
            .ok (some (.instruction instr, ⟨.trapped reason, store⟩))
          | none => .error ⟨"invalid i32 truncation operation"⟩
        | _ => .error ⟨"i32 truncation requires one f64 operand"⟩
      | .i64TruncF32S | .i64TruncF32U =>
        match thread.locals.values with
        | operand@(.f32 _) :: values =>
          match evalScalarTrunc? instr operand with
          | some (.ok value) =>
            next { thread.locals with values := value :: values }
          | some (.error reason) =>
            .ok (some (.instruction instr, ⟨.trapped reason, store⟩))
          | none => .error ⟨"invalid i64 truncation operation"⟩
        | _ => .error ⟨"i64 truncation requires one f32 operand"⟩
      | .i64TruncF64S | .i64TruncF64U =>
        match thread.locals.values with
        | operand@(.f64 _) :: values =>
          match evalScalarTrunc? instr operand with
          | some (.ok value) =>
            next { thread.locals with values := value :: values }
          | some (.error reason) =>
            .ok (some (.instruction instr, ⟨.trapped reason, store⟩))
          | none => .error ⟨"invalid i64 truncation operation"⟩
        | _ => .error ⟨"i64 truncation requires one f64 operand"⟩
      | .vConst bits =>
        next { thread.locals with values := .v128 bits :: thread.locals.values }
      | .vUnOp op =>
        match thread.locals.values with
        | .v128 value :: values =>
          next { thread.locals with values := .v128 (op.eval value) :: values }
        | _ => .error ⟨"SIMD unary operation requires one v128 operand"⟩
      | .vBinOp op =>
        match thread.locals.values with
        | .v128 rhs :: .v128 lhs :: values =>
          next { thread.locals with
            values := .v128 (op.eval lhs rhs) :: values }
        | _ => .error ⟨"SIMD binary operation requires two v128 operands"⟩
      | .vBitselect =>
        match thread.locals.values with
        | .v128 mask :: .v128 rhs :: .v128 lhs :: values =>
          next { thread.locals with
            values := .v128
              ((lhs &&& mask) ||| (rhs &&& ~~~mask)) :: values }
        | _ => .error ⟨"v128.bitselect requires three v128 operands"⟩
      | .vTestOp op =>
        match thread.locals.values with
        | .v128 value :: values =>
          next { thread.locals with values := .i32 (op.eval value) :: values }
        | _ => .error ⟨"SIMD test operation requires one v128 operand"⟩
      | .vShiftOp op =>
        match thread.locals.values with
        | .i32 amount :: .v128 value :: values =>
          next { thread.locals with
            values := .v128 (op.eval value amount) :: values }
        | _ => .error ⟨"SIMD shift requires v128 and i32 operands"⟩
      | .vSplat shape =>
        match thread.locals.values with
        | value :: values =>
          match value.scalarBitsFor? shape with
          | some bits =>
            next { thread.locals with
              values := .v128 (Simd.splat shape bits) :: values }
          | none =>
            .error ⟨"SIMD splat operand has the wrong scalar type"⟩
        | _ => .error ⟨"SIMD splat requires one scalar operand"⟩
      | .vExtractLane shape signed lane =>
        match thread.locals.values with
        | .v128 value :: values =>
          next { thread.locals with values :=
            (simdExtractLane shape signed lane value) :: values }
        | _ => .error ⟨"SIMD extract_lane requires one v128 operand"⟩
      | .vReplaceLane shape lane =>
        match thread.locals.values with
        | replacement :: .v128 value :: values =>
          match replacement.scalarBitsFor? shape with
          | some bits =>
            next { thread.locals with values :=
              (.v128 (Simd.setLane shape.laneBits lane value bits)) :: values }
          | none =>
            .error ⟨"SIMD replace_lane operand has the wrong scalar type"⟩
        | _ => .error ⟨"SIMD replace_lane requires scalar and v128 operands"⟩
      | .vShuffle indices =>
        match thread.locals.values with
        | .v128 rhs :: .v128 lhs :: values =>
          next { thread.locals with values :=
            (.v128 (Simd.shuffle indices lhs rhs)) :: values }
        | _ => .error ⟨"i8x16.shuffle requires two v128 operands"⟩
      | .vFma shape neg =>
        match thread.locals.values with
        | .v128 addend :: .v128 rhs :: .v128 lhs :: values =>
          next { thread.locals with values :=
            (.v128 (Simd.fma shape neg lhs rhs addend)) :: values }
        | _ => .error ⟨"relaxed SIMD multiply-add requires three v128 operands"⟩
      | .vDotAdd =>
        match thread.locals.values with
        | .v128 addend :: .v128 rhs :: .v128 lhs :: values =>
          next { thread.locals with values :=
            (.v128 (Simd.dotAdd lhs rhs addend)) :: values }
        | _ => .error ⟨"relaxed SIMD dot-add requires three v128 operands"⟩
      | .v128Load offset =>
        match thread.locals.values with
        | address :: values =>
          match memoryAddress? address with
          | some (logicalAddress, physicalAddress) =>
            if logicalAddress + offset.toNat + 16 >
                store.wasm.mem.pages * 65536 then
              .ok (some
                (.instruction instr, ⟨.trapped .outOfBoundsMemory, store⟩))
            else
              next { thread.locals with values :=
                (.v128 (readV128 store.wasm.mem (physicalAddress + offset))) ::
                  values }
          | none => .error ⟨"v128.load requires one integer address operand"⟩
        | _ => .error ⟨"v128.load requires one integer address operand"⟩
      | .v128Store offset =>
        match thread.locals.values with
        | .v128 value :: address :: values =>
          match memoryAddress? address with
          | some (logicalAddress, physicalAddress) =>
            if logicalAddress + offset.toNat + 16 >
                store.wasm.mem.pages * 65536 then
              .ok (some
                (.instruction instr, ⟨.trapped .outOfBoundsMemory, store⟩))
            else
              next { thread.locals with values }
                (setMemory store
                  (writeV128 store.wasm.mem (physicalAddress + offset) value))
          | none =>
            .error ⟨"v128.store requires v128 and integer address operands"⟩
        | _ => .error ⟨"v128.store requires v128 and integer address operands"⟩
      | .v128LoadExt srcBits signed offset =>
        match thread.locals.values with
        | address :: values =>
          match memoryAddress? address with
          | some (logicalAddress, physicalAddress) =>
            if logicalAddress + offset.toNat + 8 >
                store.wasm.mem.pages * 65536 then
              .ok (some
                (.instruction instr, ⟨.trapped .outOfBoundsMemory, store⟩))
            else
              next { thread.locals with values :=
                (.v128 (loadV128Ext store.wasm.mem (physicalAddress + offset)
                  srcBits signed)) :: values }
          | none =>
            .error ⟨"v128.load_ext requires one integer address operand"⟩
        | _ => .error ⟨"v128.load_ext requires one integer address operand"⟩
      | .v128LoadSplat bits offset =>
        match thread.locals.values with
        | address :: values =>
          match memoryAddress? address with
          | some (logicalAddress, physicalAddress) =>
            if logicalAddress + offset.toNat + bits / 8 >
                store.wasm.mem.pages * 65536 then
              .ok (some
                (.instruction instr, ⟨.trapped .outOfBoundsMemory, store⟩))
            else
              let lane :=
                readLaneNat store.wasm.mem (physicalAddress + offset) bits
              next { thread.locals with values :=
                (.v128 (Simd.ofLanes bits
                  (List.replicate (128 / bits) lane))) :: values }
          | none =>
            .error ⟨"v128.load_splat requires one integer address operand"⟩
        | _ => .error ⟨"v128.load_splat requires one integer address operand"⟩
      | .v128LoadZero bits offset =>
        match thread.locals.values with
        | address :: values =>
          match memoryAddress? address with
          | some (logicalAddress, physicalAddress) =>
            if logicalAddress + offset.toNat + bits / 8 >
                store.wasm.mem.pages * 65536 then
              .ok (some
                (.instruction instr, ⟨.trapped .outOfBoundsMemory, store⟩))
            else
              let lane :=
                readLaneNat store.wasm.mem (physicalAddress + offset) bits
              next { thread.locals with values :=
                (.v128 (BitVec.ofNat 128 lane)) :: values }
          | none =>
            .error ⟨"v128.load_zero requires one integer address operand"⟩
        | _ => .error ⟨"v128.load_zero requires one integer address operand"⟩
      | .v128LoadLane bits lane offset =>
        match thread.locals.values with
        | .v128 vector :: address :: values =>
          match memoryAddress? address with
          | some (logicalAddress, physicalAddress) =>
            if logicalAddress + offset.toNat + bits / 8 >
                store.wasm.mem.pages * 65536 then
              .ok (some
                (.instruction instr, ⟨.trapped .outOfBoundsMemory, store⟩))
            else
              let laneValue :=
                readLaneNat store.wasm.mem (physicalAddress + offset) bits
              next { thread.locals with values :=
                (.v128 (Simd.setLane bits lane vector laneValue)) :: values }
          | none =>
            .error ⟨"v128.load_lane requires v128 and integer address operands"⟩
        | _ =>
          .error ⟨"v128.load_lane requires v128 and integer address operands"⟩
      | .v128StoreLane bits lane offset =>
        match thread.locals.values with
        | .v128 vector :: address :: values =>
          match memoryAddress? address with
          | some (logicalAddress, physicalAddress) =>
            if logicalAddress + offset.toNat + bits / 8 >
                store.wasm.mem.pages * 65536 then
              .ok (some
                (.instruction instr, ⟨.trapped .outOfBoundsMemory, store⟩))
            else
              next { thread.locals with values }
                (setMemory store
                  (writeLaneNat store.wasm.mem (physicalAddress + offset) bits
                    (Simd.getLane bits lane vector)))
          | none =>
            .error ⟨"v128.store_lane requires v128 and integer address operands"⟩
        | _ =>
          .error ⟨"v128.store_lane requires v128 and integer address operands"⟩
      | .eqz =>
        match thread.locals.values with
        | .i32 value :: values =>
            next { thread.locals with
              values := .i32 (if value = 0 then 1 else 0) :: values }
        | _ => .error ⟨"i32.eqz requires one i32 operand"⟩
      | .eq =>
        match thread.locals.values with
        | .i32 rhs :: .i32 lhs :: values =>
            next { thread.locals with
              values := .i32 (if lhs = rhs then 1 else 0) :: values }
        | _ => .error ⟨"i32.eq requires two i32 operands"⟩
      | .ne =>
        match thread.locals.values with
        | .i32 rhs :: .i32 lhs :: values =>
            next { thread.locals with
              values := .i32 (if lhs ≠ rhs then 1 else 0) :: values }
        | _ => .error ⟨"i32.ne requires two i32 operands"⟩
      | .ltU =>
        match thread.locals.values with
        | .i32 rhs :: .i32 lhs :: values =>
            next { thread.locals with
              values := .i32 (if lhs < rhs then 1 else 0) :: values }
        | _ => .error ⟨"i32.lt_u requires two i32 operands"⟩
      | .gtU =>
        match thread.locals.values with
        | .i32 rhs :: .i32 lhs :: values =>
            next { thread.locals with
              values := .i32 (if lhs > rhs then 1 else 0) :: values }
        | _ => .error ⟨"i32.gt_u requires two i32 operands"⟩
      | .leU =>
        match thread.locals.values with
        | .i32 rhs :: .i32 lhs :: values =>
            next { thread.locals with
              values := .i32 (if lhs ≤ rhs then 1 else 0) :: values }
        | _ => .error ⟨"i32.le_u requires two i32 operands"⟩
      | .geU =>
        match thread.locals.values with
        | .i32 rhs :: .i32 lhs :: values =>
            next { thread.locals with
              values := .i32 (if lhs ≥ rhs then 1 else 0) :: values }
        | _ => .error ⟨"i32.ge_u requires two i32 operands"⟩
      | .ltS =>
        match thread.locals.values with
        | .i32 rhs :: .i32 lhs :: values =>
          next { thread.locals with
            values := .i32 (if lhs.toInt32 < rhs.toInt32 then 1 else 0) :: values }
        | _ => .error ⟨"i32.lt_s requires two i32 operands"⟩
      | .gtS =>
        match thread.locals.values with
        | .i32 rhs :: .i32 lhs :: values =>
          next { thread.locals with
            values := .i32 (if lhs.toInt32 > rhs.toInt32 then 1 else 0) :: values }
        | _ => .error ⟨"i32.gt_s requires two i32 operands"⟩
      | .leS =>
        match thread.locals.values with
        | .i32 rhs :: .i32 lhs :: values =>
          next { thread.locals with
            values := .i32 (if lhs.toInt32 ≤ rhs.toInt32 then 1 else 0) :: values }
        | _ => .error ⟨"i32.le_s requires two i32 operands"⟩
      | .geS =>
        match thread.locals.values with
        | .i32 rhs :: .i32 lhs :: values =>
          next { thread.locals with
            values := .i32 (if lhs.toInt32 ≥ rhs.toInt32 then 1 else 0) :: values }
        | _ => .error ⟨"i32.ge_s requires two i32 operands"⟩
      | .eqzI64 =>
        match thread.locals.values with
        | .i64 value :: values =>
          next { thread.locals with
            values := .i32 (if value = 0 then 1 else 0) :: values }
        | _ => .error ⟨"i64.eqz requires one i64 operand"⟩
      | .eqI64 =>
        match thread.locals.values with
        | .i64 rhs :: .i64 lhs :: values =>
          next { thread.locals with
            values := .i32 (if lhs = rhs then 1 else 0) :: values }
        | _ => .error ⟨"i64.eq requires two i64 operands"⟩
      | .neI64 =>
        match thread.locals.values with
        | .i64 rhs :: .i64 lhs :: values =>
          next { thread.locals with
            values := .i32 (if lhs ≠ rhs then 1 else 0) :: values }
        | _ => .error ⟨"i64.ne requires two i64 operands"⟩
      | .ltUI64 =>
        match thread.locals.values with
        | .i64 rhs :: .i64 lhs :: values =>
          next { thread.locals with
            values := .i32 (if lhs < rhs then 1 else 0) :: values }
        | _ => .error ⟨"i64.lt_u requires two i64 operands"⟩
      | .ltSI64 =>
        match thread.locals.values with
        | .i64 rhs :: .i64 lhs :: values =>
          next { thread.locals with
            values := .i32 (if lhs.toInt64 < rhs.toInt64 then 1 else 0) :: values }
        | _ => .error ⟨"i64.lt_s requires two i64 operands"⟩
      | .gtUI64 =>
        match thread.locals.values with
        | .i64 rhs :: .i64 lhs :: values =>
          next { thread.locals with
            values := .i32 (if lhs > rhs then 1 else 0) :: values }
        | _ => .error ⟨"i64.gt_u requires two i64 operands"⟩
      | .gtSI64 =>
        match thread.locals.values with
        | .i64 rhs :: .i64 lhs :: values =>
          next { thread.locals with
            values := .i32 (if lhs.toInt64 > rhs.toInt64 then 1 else 0) :: values }
        | _ => .error ⟨"i64.gt_s requires two i64 operands"⟩
      | .leUI64 =>
        match thread.locals.values with
        | .i64 rhs :: .i64 lhs :: values =>
          next { thread.locals with
            values := .i32 (if lhs ≤ rhs then 1 else 0) :: values }
        | _ => .error ⟨"i64.le_u requires two i64 operands"⟩
      | .leSI64 =>
        match thread.locals.values with
        | .i64 rhs :: .i64 lhs :: values =>
          next { thread.locals with
            values := .i32 (if lhs.toInt64 ≤ rhs.toInt64 then 1 else 0) :: values }
        | _ => .error ⟨"i64.le_s requires two i64 operands"⟩
      | .geUI64 =>
        match thread.locals.values with
        | .i64 rhs :: .i64 lhs :: values =>
          next { thread.locals with
            values := .i32 (if lhs ≥ rhs then 1 else 0) :: values }
        | _ => .error ⟨"i64.ge_u requires two i64 operands"⟩
      | .geSI64 =>
        match thread.locals.values with
        | .i64 rhs :: .i64 lhs :: values =>
          next { thread.locals with
            values := .i32 (if lhs.toInt64 ≥ rhs.toInt64 then 1 else 0) :: values }
        | _ => .error ⟨"i64.ge_s requires two i64 operands"⟩
      | .wrapI64 =>
        match thread.locals.values with
        | .i64 value :: values =>
          next { thread.locals with
            values := .i32 (wrap64To32 value) :: values }
        | _ => .error ⟨"i32.wrap_i64 requires one i64 operand"⟩
      | .extendUI32 =>
        match thread.locals.values with
        | .i32 value :: values =>
          next { thread.locals with
            values := .i64 (extendUnsigned32To64 value) :: values }
        | _ => .error ⟨"i64.extend_i32_u requires one i32 operand"⟩
      | .extendSI32 =>
        match thread.locals.values with
        | .i32 value :: values =>
          next { thread.locals with
            values := .i64 (extendSigned32To64 value) :: values }
        | _ => .error ⟨"i64.extend_i32_s requires one i32 operand"⟩
      | .extend8S =>
        match thread.locals.values with
        | .i32 value :: values =>
          next { thread.locals with values := .i32 (extend8To32 value) :: values }
        | _ => .error ⟨"i32.extend8_s requires one i32 operand"⟩
      | .extend16S =>
        match thread.locals.values with
        | .i32 value :: values =>
          next { thread.locals with values := .i32 (extend16To32 value) :: values }
        | _ => .error ⟨"i32.extend16_s requires one i32 operand"⟩
      | .extend8SI64 =>
        match thread.locals.values with
        | .i64 value :: values =>
          next { thread.locals with values := .i64 (extend8To64 value) :: values }
        | _ => .error ⟨"i64.extend8_s requires one i64 operand"⟩
      | .extend16SI64 =>
        match thread.locals.values with
        | .i64 value :: values =>
          next { thread.locals with values := .i64 (extend16To64 value) :: values }
        | _ => .error ⟨"i64.extend16_s requires one i64 operand"⟩
      | .extend32SI64 =>
        match thread.locals.values with
        | .i64 value :: values =>
          next { thread.locals with values := .i64 (extend32To64 value) :: values }
        | _ => .error ⟨"i64.extend32_s requires one i64 operand"⟩
      | .load8U offset =>
        match thread.locals.values with
        | .i32 address :: values =>
          if address.toNat + offset.toNat + 1 > store.wasm.mem.pages * 65536 then
            .ok (some (.instruction instr, ⟨.trapped .outOfBoundsMemory, store⟩))
          else
            next { thread.locals with
              values := .i32
                (store.wasm.mem.read8 (address + offset)).toUInt32 :: values }
        | .i64 address :: values =>
          if address.toNat + offset.toNat + 1 > store.wasm.mem.pages * 65536 then
            .ok (some (.instruction instr, ⟨.trapped .outOfBoundsMemory, store⟩))
          else
            next { thread.locals with
              values := .i32
                (store.wasm.mem.read8
                  (address.toUInt32 + offset)).toUInt32 :: values }
        | _ => .error ⟨"i32.load8_u requires one i32 address operand"⟩
      | .load8S offset =>
        match thread.locals.values with
        | .i32 address :: values =>
          if address.toNat + offset.toNat + 1 > store.wasm.mem.pages * 65536 then
            .ok (some (.instruction instr, ⟨.trapped .outOfBoundsMemory, store⟩))
          else
            next { thread.locals with
              values := .i32
                (extend8To32
                  (store.wasm.mem.read8 (address + offset)).toUInt32) :: values }
        | .i64 address :: values =>
          if address.toNat + offset.toNat + 1 > store.wasm.mem.pages * 65536 then
            .ok (some (.instruction instr, ⟨.trapped .outOfBoundsMemory, store⟩))
          else
            next { thread.locals with
              values := .i32
                (extend8To32
                  (store.wasm.mem.read8
                    (address.toUInt32 + offset)).toUInt32) :: values }
        | _ => .error ⟨"i32.load8_s requires one i32 address operand"⟩
      | .load16U offset =>
        match thread.locals.values with
        | .i32 address :: values =>
          if address.toNat + offset.toNat + 2 > store.wasm.mem.pages * 65536 then
            .ok (some (.instruction instr, ⟨.trapped .outOfBoundsMemory, store⟩))
          else
            next { thread.locals with
              values := .i32
                (store.wasm.mem.read16 (address + offset)) :: values }
        | .i64 address :: values =>
          if address.toNat + offset.toNat + 2 > store.wasm.mem.pages * 65536 then
            .ok (some (.instruction instr, ⟨.trapped .outOfBoundsMemory, store⟩))
          else
            next { thread.locals with
              values := .i32
                (store.wasm.mem.read16 (address.toUInt32 + offset)) :: values }
        | _ => .error ⟨"i32.load16_u requires one i32 address operand"⟩
      | .load16S offset =>
        match thread.locals.values with
        | .i32 address :: values =>
          if address.toNat + offset.toNat + 2 > store.wasm.mem.pages * 65536 then
            .ok (some (.instruction instr, ⟨.trapped .outOfBoundsMemory, store⟩))
          else
            next { thread.locals with
              values := .i32
                (extend16To32
                  (store.wasm.mem.read16 (address + offset))) :: values }
        | .i64 address :: values =>
          if address.toNat + offset.toNat + 2 > store.wasm.mem.pages * 65536 then
            .ok (some (.instruction instr, ⟨.trapped .outOfBoundsMemory, store⟩))
          else
            next { thread.locals with
              values := .i32
                (extend16To32
                  (store.wasm.mem.read16
                    (address.toUInt32 + offset))) :: values }
        | _ => .error ⟨"i32.load16_s requires one i32 address operand"⟩
      | .store8 offset =>
        match thread.locals.values with
        | .i32 value :: .i32 address :: values =>
          if address.toNat + offset.toNat + 1 > store.wasm.mem.pages * 65536 then
            .ok (some (.instruction instr, ⟨.trapped .outOfBoundsMemory, store⟩))
          else
            next { thread.locals with values := values }
              (setMemory store
                (store.wasm.mem.write8 (address + offset) value.toUInt8))
        | .i32 value :: .i64 address :: values =>
          if address.toNat + offset.toNat + 1 > store.wasm.mem.pages * 65536 then
            .ok (some (.instruction instr, ⟨.trapped .outOfBoundsMemory, store⟩))
          else
            next { thread.locals with values := values }
              (setMemory store
                (store.wasm.mem.write8
                  (address.toUInt32 + offset) value.toUInt8))
        | _ => .error ⟨"i32.store8 requires i32 value and address operands"⟩
      | .store16 offset =>
        match thread.locals.values with
        | .i32 value :: .i32 address :: values =>
          if address.toNat + offset.toNat + 2 > store.wasm.mem.pages * 65536 then
            .ok (some (.instruction instr, ⟨.trapped .outOfBoundsMemory, store⟩))
          else
            next { thread.locals with values }
              (setMemory store
                (store.wasm.mem.write16 (address + offset) value))
        | .i32 value :: .i64 address :: values =>
          if address.toNat + offset.toNat + 2 > store.wasm.mem.pages * 65536 then
            .ok (some (.instruction instr, ⟨.trapped .outOfBoundsMemory, store⟩))
          else
            next { thread.locals with values }
              (setMemory store
                (store.wasm.mem.write16
                  (address.toUInt32 + offset) value))
        | _ => .error ⟨"i32.store16 requires i32 value and address operands"⟩
      | .load32 offset =>
        match thread.locals.values with
        | .i32 address :: values =>
          if address.toNat + offset.toNat + 4 > store.wasm.mem.pages * 65536 then
            .ok (some (.instruction instr, ⟨.trapped .outOfBoundsMemory, store⟩))
          else
            next { thread.locals with
              values := .i32 (store.wasm.mem.read32 (address + offset)) :: values }
        | .i64 address :: values =>
          if address.toNat + offset.toNat + 4 > store.wasm.mem.pages * 65536 then
            .ok (some (.instruction instr, ⟨.trapped .outOfBoundsMemory, store⟩))
          else
            next { thread.locals with
              values := .i32
                (store.wasm.mem.read32 (address.toUInt32 + offset)) :: values }
        | _ => .error ⟨"i32.load requires one i32 address operand"⟩
      | .store32 offset =>
        match thread.locals.values with
        | .i32 value :: .i32 address :: values =>
          if address.toNat + offset.toNat + 4 > store.wasm.mem.pages * 65536 then
            .ok (some (.instruction instr, ⟨.trapped .outOfBoundsMemory, store⟩))
          else
            next { thread.locals with values := values }
              (setMemory store (store.wasm.mem.write32 (address + offset) value))
        | .i32 value :: .i64 address :: values =>
          if address.toNat + offset.toNat + 4 > store.wasm.mem.pages * 65536 then
            .ok (some (.instruction instr, ⟨.trapped .outOfBoundsMemory, store⟩))
          else
            next { thread.locals with values := values }
              (setMemory store
                (store.wasm.mem.write32 (address.toUInt32 + offset) value))
        | _ => .error ⟨"i32.store requires i32 value and address operands"⟩
      | .load64 offset =>
        match thread.locals.values with
        | address :: values =>
          match memoryAddress? address with
          | some (logicalAddress, physicalAddress) =>
            if logicalAddress + offset.toNat + 8 >
                store.wasm.mem.pages * 65536 then
              .ok (some
                (.instruction instr, ⟨.trapped .outOfBoundsMemory, store⟩))
            else
              next { thread.locals with
                values := .i64
                  (store.wasm.mem.read64 (physicalAddress + offset)) :: values }
          | none => .error ⟨"i64.load requires one integer address operand"⟩
        | _ => .error ⟨"i64.load requires one integer address operand"⟩
      | .store64 offset =>
        match thread.locals.values with
        | .i64 value :: address :: values =>
          match memoryAddress? address with
          | some (logicalAddress, physicalAddress) =>
            if logicalAddress + offset.toNat + 8 >
                store.wasm.mem.pages * 65536 then
              .ok (some
                (.instruction instr, ⟨.trapped .outOfBoundsMemory, store⟩))
            else
              next { thread.locals with values }
                (setMemory store
                  (store.wasm.mem.write64 (physicalAddress + offset) value))
          | none =>
            .error ⟨"i64.store requires i64 value and integer address operands"⟩
        | _ =>
          .error ⟨"i64.store requires i64 value and integer address operands"⟩
      | .f32Load offset =>
        match thread.locals.values with
        | address :: values =>
          match memoryAddress? address with
          | some (logicalAddress, physicalAddress) =>
            if logicalAddress + offset.toNat + 4 >
                store.wasm.mem.pages * 65536 then
              .ok (some
                (.instruction instr, ⟨.trapped .outOfBoundsMemory, store⟩))
            else
              next { thread.locals with
                values := .f32
                  (store.wasm.mem.read32 (physicalAddress + offset)) :: values }
          | none => .error ⟨"f32.load requires one integer address operand"⟩
        | _ => .error ⟨"f32.load requires one integer address operand"⟩
      | .f32Store offset =>
        match thread.locals.values with
        | .f32 value :: address :: values =>
          match memoryAddress? address with
          | some (logicalAddress, physicalAddress) =>
            if logicalAddress + offset.toNat + 4 >
                store.wasm.mem.pages * 65536 then
              .ok (some
                (.instruction instr, ⟨.trapped .outOfBoundsMemory, store⟩))
            else
              next { thread.locals with values }
                (setMemory store
                  (store.wasm.mem.write32 (physicalAddress + offset) value))
          | none =>
            .error ⟨"f32.store requires f32 value and integer address operands"⟩
        | _ =>
          .error ⟨"f32.store requires f32 value and integer address operands"⟩
      | .f64Load offset =>
        match thread.locals.values with
        | address :: values =>
          match memoryAddress? address with
          | some (logicalAddress, physicalAddress) =>
            if logicalAddress + offset.toNat + 8 >
                store.wasm.mem.pages * 65536 then
              .ok (some
                (.instruction instr, ⟨.trapped .outOfBoundsMemory, store⟩))
            else
              next { thread.locals with
                values := .f64
                  (store.wasm.mem.read64 (physicalAddress + offset)) :: values }
          | none => .error ⟨"f64.load requires one integer address operand"⟩
        | _ => .error ⟨"f64.load requires one integer address operand"⟩
      | .f64Store offset =>
        match thread.locals.values with
        | .f64 value :: address :: values =>
          match memoryAddress? address with
          | some (logicalAddress, physicalAddress) =>
            if logicalAddress + offset.toNat + 8 >
                store.wasm.mem.pages * 65536 then
              .ok (some
                (.instruction instr, ⟨.trapped .outOfBoundsMemory, store⟩))
            else
              next { thread.locals with values }
                (setMemory store
                  (store.wasm.mem.write64 (physicalAddress + offset) value))
          | none =>
            .error ⟨"f64.store requires f64 value and integer address operands"⟩
        | _ =>
          .error ⟨"f64.store requires f64 value and integer address operands"⟩
      | .load8UI64 offset =>
        match thread.locals.values with
        | address :: values =>
          match memoryAddress? address with
          | some (logicalAddress, physicalAddress) =>
            if logicalAddress + offset.toNat + 1 >
                store.wasm.mem.pages * 65536 then
              .ok (some
                (.instruction instr, ⟨.trapped .outOfBoundsMemory, store⟩))
            else
              next { thread.locals with
                values := .i64
                  (store.wasm.mem.read8
                    (physicalAddress + offset)).toUInt64 :: values }
          | none => .error ⟨"i64.load8_u requires one integer address operand"⟩
        | _ => .error ⟨"i64.load8_u requires one integer address operand"⟩
      | .load8SI64 offset =>
        match thread.locals.values with
        | address :: values =>
          match memoryAddress? address with
          | some (logicalAddress, physicalAddress) =>
            if logicalAddress + offset.toNat + 1 >
                store.wasm.mem.pages * 65536 then
              .ok (some
                (.instruction instr, ⟨.trapped .outOfBoundsMemory, store⟩))
            else
              next { thread.locals with
                values := .i64
                  (extend8To64
                    (store.wasm.mem.read8
                      (physicalAddress + offset)).toUInt64) :: values }
          | none => .error ⟨"i64.load8_s requires one integer address operand"⟩
        | _ => .error ⟨"i64.load8_s requires one integer address operand"⟩
      | .load16UI64 offset =>
        match thread.locals.values with
        | address :: values =>
          match memoryAddress? address with
          | some (logicalAddress, physicalAddress) =>
            if logicalAddress + offset.toNat + 2 >
                store.wasm.mem.pages * 65536 then
              .ok (some
                (.instruction instr, ⟨.trapped .outOfBoundsMemory, store⟩))
            else
              next { thread.locals with
                values := .i64
                  (store.wasm.mem.read16
                    (physicalAddress + offset)).toUInt64 :: values }
          | none => .error ⟨"i64.load16_u requires one integer address operand"⟩
        | _ => .error ⟨"i64.load16_u requires one integer address operand"⟩
      | .load16SI64 offset =>
        match thread.locals.values with
        | address :: values =>
          match memoryAddress? address with
          | some (logicalAddress, physicalAddress) =>
            if logicalAddress + offset.toNat + 2 >
                store.wasm.mem.pages * 65536 then
              .ok (some
                (.instruction instr, ⟨.trapped .outOfBoundsMemory, store⟩))
            else
              next { thread.locals with
                values := .i64
                  (extend16To64
                    (store.wasm.mem.read16
                      (physicalAddress + offset)).toUInt64) :: values }
          | none => .error ⟨"i64.load16_s requires one integer address operand"⟩
        | _ => .error ⟨"i64.load16_s requires one integer address operand"⟩
      | .load32UI64 offset =>
        match thread.locals.values with
        | address :: values =>
          match memoryAddress? address with
          | some (logicalAddress, physicalAddress) =>
            if logicalAddress + offset.toNat + 4 >
                store.wasm.mem.pages * 65536 then
              .ok (some
                (.instruction instr, ⟨.trapped .outOfBoundsMemory, store⟩))
            else
              next { thread.locals with
                values := .i64
                  (store.wasm.mem.read32
                    (physicalAddress + offset)).toUInt64 :: values }
          | none => .error ⟨"i64.load32_u requires one integer address operand"⟩
        | _ => .error ⟨"i64.load32_u requires one integer address operand"⟩
      | .load32SI64 offset =>
        match thread.locals.values with
        | address :: values =>
          match memoryAddress? address with
          | some (logicalAddress, physicalAddress) =>
            if logicalAddress + offset.toNat + 4 >
                store.wasm.mem.pages * 65536 then
              .ok (some
                (.instruction instr, ⟨.trapped .outOfBoundsMemory, store⟩))
            else
              next { thread.locals with
                values := .i64
                  (extend32To64
                    (store.wasm.mem.read32
                      (physicalAddress + offset)).toUInt64) :: values }
          | none => .error ⟨"i64.load32_s requires one integer address operand"⟩
        | _ => .error ⟨"i64.load32_s requires one integer address operand"⟩
      | .store8I64 offset =>
        match thread.locals.values with
        | .i64 value :: address :: values =>
          match memoryAddress? address with
          | some (logicalAddress, physicalAddress) =>
            if logicalAddress + offset.toNat + 1 >
                store.wasm.mem.pages * 65536 then
              .ok (some
                (.instruction instr, ⟨.trapped .outOfBoundsMemory, store⟩))
            else
              next { thread.locals with values }
                (setMemory store
                  (store.wasm.mem.write8
                    (physicalAddress + offset) value.toUInt8))
          | none =>
            .error ⟨"i64.store8 requires i64 value and integer address operands"⟩
        | _ =>
          .error ⟨"i64.store8 requires i64 value and integer address operands"⟩
      | .store16I64 offset =>
        match thread.locals.values with
        | .i64 value :: address :: values =>
          match memoryAddress? address with
          | some (logicalAddress, physicalAddress) =>
            if logicalAddress + offset.toNat + 2 >
                store.wasm.mem.pages * 65536 then
              .ok (some
                (.instruction instr, ⟨.trapped .outOfBoundsMemory, store⟩))
            else
              next { thread.locals with values }
                (setMemory store
                  (store.wasm.mem.write16
                    (physicalAddress + offset) value.toUInt32))
          | none =>
            .error ⟨"i64.store16 requires i64 value and integer address operands"⟩
        | _ =>
          .error ⟨"i64.store16 requires i64 value and integer address operands"⟩
      | .store32I64 offset =>
        match thread.locals.values with
        | .i64 value :: address :: values =>
          match memoryAddress? address with
          | some (logicalAddress, physicalAddress) =>
            if logicalAddress + offset.toNat + 4 >
                store.wasm.mem.pages * 65536 then
              .ok (some
                (.instruction instr, ⟨.trapped .outOfBoundsMemory, store⟩))
            else
              next { thread.locals with values }
                (setMemory store
                  (store.wasm.mem.write32
                    (physicalAddress + offset) value.toUInt32))
          | none =>
            .error ⟨"i64.store32 requires i64 value and integer address operands"⟩
        | _ =>
          .error ⟨"i64.store32 requires i64 value and integer address operands"⟩
      | .memorySize =>
        next { thread.locals with
          values :=
            sizeValue store.runtime.currentModule.memIs64 store.wasm.mem.pages ::
              thread.locals.values }
      | .memoryGrow =>
        match thread.locals.values with
        | .i32 delta :: values =>
          match store.wasm.mem.grow delta
              (store.wasm.memoryCap store.runtime.currentModule 0) with
          | some (memory, previousPages) =>
            next { thread.locals with
              values := .i32 previousPages.toUInt32 :: values }
              (setMemory store memory)
          | none =>
            next { thread.locals with
              values := .i32 (0xFFFFFFFF : UInt32) :: values }
        | .i64 delta :: values =>
          if delta.toNat ≥ 2 ^ 32 then
            next { thread.locals with
              values := .i64 (0xFFFFFFFFFFFFFFFF : UInt64) :: values }
          else
            match store.wasm.mem.grow delta.toUInt32
                (store.wasm.memoryCap store.runtime.currentModule 0) with
            | some (memory, previousPages) =>
              next { thread.locals with
                values := .i64 previousPages.toUInt64 :: values }
                (setMemory store memory)
            | none =>
              next { thread.locals with
                values := .i64 (0xFFFFFFFFFFFFFFFF : UInt64) :: values }
        | _ =>
          .error ⟨"small-step memory.grow requires one integer delta operand"⟩
      | .memoryFill =>
        match thread.locals.values with
        | .i32 len :: .i32 value :: .i32 destination :: values =>
          if destination.toNat + len.toNat >
              store.wasm.mem.pages * 65536 then
            .ok (some (.instruction instr,
              ⟨.trapped .outOfBoundsMemory, store⟩))
          else
            next { thread.locals with values }
              (setMemory store
                (store.wasm.mem.fill destination.toNat len.toNat value.toUInt8))
        | .i64 len :: .i32 value :: .i64 destination :: values =>
          if destination.toNat + len.toNat >
              store.wasm.mem.pages * 65536 then
            .ok (some (.instruction instr,
              ⟨.trapped .outOfBoundsMemory, store⟩))
          else
            next { thread.locals with values }
              (setMemory store
                (store.wasm.mem.fill destination.toNat len.toNat value.toUInt8))
        | _ =>
          .error ⟨"memory.fill requires destination, i32 value, and length operands"⟩
      | .memoryCopy =>
        match thread.locals.values with
        | .i32 len :: .i32 source :: .i32 destination :: values =>
          if destination.toNat + len.toNat >
                store.wasm.mem.pages * 65536 ∨
              source.toNat + len.toNat >
                store.wasm.mem.pages * 65536 then
            .ok (some (.instruction instr,
              ⟨.trapped .outOfBoundsMemory, store⟩))
          else
            next { thread.locals with values }
              (setMemory store
                (store.wasm.mem.copy destination.toNat source.toNat len.toNat))
        | .i64 len :: .i64 source :: .i64 destination :: values =>
          if destination.toNat + len.toNat >
                store.wasm.mem.pages * 65536 ∨
              source.toNat + len.toNat >
                store.wasm.mem.pages * 65536 then
            .ok (some (.instruction instr,
              ⟨.trapped .outOfBoundsMemory, store⟩))
          else
            next { thread.locals with values }
              (setMemory store
                (store.wasm.mem.copy destination.toNat source.toNat len.toNat))
        | _ =>
          .error ⟨"memory.copy requires destination, source, and length operands"⟩
      | .memoryInit segmentIndex =>
        match thread.locals.values with
        | .i32 len :: .i32 source :: .i32 destination :: values =>
          match store.wasm.dataSegments[segmentIndex]? with
          | none =>
            .error ⟨s!"memory.init segment index {segmentIndex} is invalid"⟩
          | some none =>
            if 0 < len.toNat ∨
                destination.toNat + len.toNat >
                  store.wasm.mem.pages * 65536 then
              .ok (some (.instruction instr,
                ⟨.trapped .outOfBoundsMemory, store⟩))
            else
              next { thread.locals with values }
          | some (some segmentBytes) =>
            if source.toNat + len.toNat > segmentBytes.length ∨
                destination.toNat + len.toNat >
                  store.wasm.mem.pages * 65536 then
              .ok (some (.instruction instr,
                ⟨.trapped .outOfBoundsMemory, store⟩))
            else
              next { thread.locals with values }
                (setMemory store
                  (store.wasm.mem.writeBytesFrom destination.toNat
                    segmentBytes source.toNat len.toNat))
        | .i32 len :: .i32 source :: .i64 destination :: values =>
          match store.wasm.dataSegments[segmentIndex]? with
          | none =>
            .error ⟨s!"memory.init segment index {segmentIndex} is invalid"⟩
          | some none =>
            if 0 < len.toNat ∨
                destination.toNat + len.toNat >
                  store.wasm.mem.pages * 65536 then
              .ok (some (.instruction instr,
                ⟨.trapped .outOfBoundsMemory, store⟩))
            else
              next { thread.locals with values }
          | some (some segmentBytes) =>
            if source.toNat + len.toNat > segmentBytes.length ∨
                destination.toNat + len.toNat >
                  store.wasm.mem.pages * 65536 then
              .ok (some (.instruction instr,
                ⟨.trapped .outOfBoundsMemory, store⟩))
            else
              next { thread.locals with values }
                (setMemory store
                  (store.wasm.mem.writeBytesFrom destination.toNat
                    segmentBytes source.toNat len.toNat))
        | _ =>
          .error ⟨"memory.init requires destination, source, and length operands"⟩
      | .dataDrop segmentIndex =>
        match store.wasm.dataSegments[segmentIndex]? with
        | none =>
          .error ⟨s!"data.drop segment index {segmentIndex} is invalid"⟩
        | some _ =>
          next thread.locals
            (setDataSegments store
              (store.wasm.dataSegments.set segmentIndex none))
      | .memoryCopyBetween destinationMemory sourceMemory =>
        match thread.locals.values with
        | lengthValue :: sourceValue :: destinationValue :: values =>
          match lengthValue.addrNat?, sourceValue.addrNat?,
              destinationValue.addrNat? with
          | some length, some source, some destination =>
            match memoryAt? store destinationMemory,
                memoryAt? store sourceMemory with
            | some destinationMem, some sourceMem =>
              if destination + length > destinationMem.pages * 65536 ∨
                  source + length > sourceMem.pages * 65536 then
                .ok (some
                  (.instruction instr, ⟨.trapped .outOfBoundsMemory, store⟩))
              else
                let memory :=
                  destinationMem.writeBytes destination
                    (sourceMem.readBytes source length)
                next { thread.locals with values }
                  (setMemoryAt store destinationMemory memory)
            | _, _ =>
              .error ⟨"memory.copy memory index is invalid"⟩
          | _, _, _ =>
            .error ⟨"memory.copy requires integer destination, source, and length operands"⟩
        | _ =>
          .error ⟨"memory.copy requires destination, source, and length operands"⟩
      | .gc operation =>
        match execGcOp store.runtime.currentModule store.wasm thread.locals operation with
        | .Fallthrough wasm locals =>
          next locals { store with wasm }
        | .Trap wasm message =>
          .ok (some (.instruction instr,
            ⟨.trapped (gcTrapReasonOfMessage message), { store with wasm }⟩))
        | .Break depth wasm locals =>
          match branchTarget? thread.resultArity depth thread.control
              locals.values with
          | some (code, control, values) =>
            .ok (some (.instruction instr,
              ⟨.running
                { thread with
                  locals := { locals with values }
                  code
                  control },
                { store with wasm }⟩))
          | none =>
            .error ⟨s!"GC branch depth {depth} is invalid"⟩
        | .Invalid message => .error ⟨message⟩
        | _ =>
          .error ⟨"GC instruction produced an invalid control result"⟩
      | .memOp _ _ =>
        .error ⟨"indexed memory instruction must be handled by stepChecked?"⟩
      | .f32Const _ | .f64Const _
        | .f32Abs | .f32Neg | .f32Sqrt | .f32Ceil | .f32Floor
        | .f32Trunc | .f32Nearest
        | .f64Abs | .f64Neg | .f64Sqrt | .f64Ceil | .f64Floor
        | .f64Trunc | .f64Nearest
        | .f32ConvertI32S | .f32ConvertI32U
        | .f32ConvertI64S | .f32ConvertI64U
        | .f64ConvertI32S | .f64ConvertI32U
        | .f64ConvertI64S | .f64ConvertI64U
        | .i32TruncSatF32S | .i32TruncSatF32U
        | .i32TruncSatF64S | .i32TruncSatF64U
        | .i64TruncSatF32S | .i64TruncSatF32U
        | .i64TruncSatF64S | .i64TruncSatF64U
        | .f32DemoteF64 | .f64PromoteF32
        | .i32ReinterpretF32 | .i64ReinterpretF64
        | .f32ReinterpretI32 | .f64ReinterpretI64
        | .f32Add | .f32Sub | .f32Mul | .f32Div
        | .f32Min | .f32Max | .f32Copysign
        | .f64Add | .f64Sub | .f64Mul | .f64Div
        | .f64Min | .f64Max | .f64Copysign
        | .f32Eq | .f32Ne | .f32Lt | .f32Gt | .f32Le | .f32Ge
        | .f64Eq | .f64Ne | .f64Lt | .f64Gt | .f64Le | .f64Ge =>
        match evalScalarFloat0? instr with
        | some value =>
          next { thread.locals with
            values := value :: thread.locals.values }
        | none =>
          match thread.locals.values with
          | operand :: values =>
            match evalScalarFloat1? instr operand with
            | some value =>
              next { thread.locals with values := value :: values }
            | none =>
              match thread.locals.values with
              | rhs :: lhs :: values =>
                match evalScalarFloat2? instr lhs rhs with
                | some value =>
                  next { thread.locals with values := value :: values }
                | none =>
                  .error ⟨s!"scalar float instruction has invalid operands: {repr instr}"⟩
              | _ =>
                .error ⟨s!"scalar float instruction has too few operands: {repr instr}"⟩
          | [] =>
            .error ⟨s!"scalar float instruction has no operands: {repr instr}"⟩

/-- Checked executable presentation. Indexed-memory instructions are a
nonrecursive wrapper around the ordinary one-instruction stepper: the selected
memory and declaration are focused into slot zero, the wrapped instruction
takes exactly one plain step, and the resulting memory is restored to its
stable index. -/
def stepChecked?
    (config : Config α) : Except InternalError (Option (StepKind × Config α)) :=
  match config with
  | ⟨.running thread, store⟩ =>
    match thread.code with
    | .memOp memoryIndex inner :: rest =>
      if isMemOp inner then
        .error ⟨"nested indexed-memory instruction is invalid"⟩
      else
        match enterIndexedMemory? store memoryIndex with
        | none =>
          .error ⟨s!"memory index {memoryIndex} is invalid"⟩
        | some indexedStore =>
          let indexedConfig : Config α :=
            ⟨.running { thread with code := [inner] }, indexedStore⟩
          match stepPlainChecked? indexedConfig with
          | .error error => .error error
          | .ok none =>
            .error ⟨"indexed memory instruction did not take a step"⟩
          | .ok (some (_, stepped)) =>
            .ok (some (.instruction (.memOp memoryIndex inner),
              resumeAfterIndexedMemory rest store memoryIndex stepped))
    | _ => stepPlainChecked? config
  | _ => stepPlainChecked? config

attribute [local simp] stepPlainChecked?

def stepUnchecked? (config : Config α) : Option (StepKind × Config α) :=
  match stepChecked? config with
  | .error _ => none
  | .ok result => result

private theorem scalarFloat0_checked
    {instruction : Instruction} {value : Value}
    {params localValues values : List Value} {code : Program}
    {arity : Nat} {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {store : MachineStore α}
    (heval : evalScalarFloat0? instruction = some value) :
    stepChecked?
      ⟨.running ⟨⟨params, localValues, values⟩,
        instruction :: code, arity, remainder, controls, calls⟩, store⟩ =
      .ok (some (.instruction instruction,
        ⟨.running ⟨⟨params, localValues, value :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩)) := by
  cases instruction <;>
    simp_all [stepChecked?, evalScalarFloat0?]

private theorem scalarFloat1_checked
    {instruction : Instruction} {operand value : Value}
    {params localValues values : List Value} {code : Program}
    {arity : Nat} {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {store : MachineStore α}
    (hzero : evalScalarFloat0? instruction = none)
    (heval : evalScalarFloat1? instruction operand = some value) :
    stepChecked?
      ⟨.running ⟨⟨params, localValues, operand :: values⟩,
        instruction :: code, arity, remainder, controls, calls⟩, store⟩ =
      .ok (some (.instruction instruction,
        ⟨.running ⟨⟨params, localValues, value :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩)) := by
  cases instruction <;>
    simp_all [stepChecked?, evalScalarFloat0?, evalScalarFloat1?]
  all_goals cases operand <;>
    simp_all [stepChecked?, evalScalarFloat0?,
      evalScalarFloat1?, evalScalarFloat2?]

private theorem scalarFloat2_checked
    {instruction : Instruction} {lhs rhs value : Value}
    {params localValues values : List Value} {code : Program}
    {arity : Nat} {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {store : MachineStore α}
    (hzero : evalScalarFloat0? instruction = none)
    (hunary : evalScalarFloat1? instruction rhs = none)
    (heval : evalScalarFloat2? instruction lhs rhs = some value) :
    stepChecked?
      ⟨.running ⟨⟨params, localValues, rhs :: lhs :: values⟩,
        instruction :: code, arity, remainder, controls, calls⟩, store⟩ =
      .ok (some (.instruction instruction,
        ⟨.running ⟨⟨params, localValues, value :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩)) := by
  cases instruction <;>
    simp_all [stepChecked?, evalScalarFloat0?,
      evalScalarFloat1?, evalScalarFloat2?]
  all_goals cases lhs <;> cases rhs <;>
    simp_all [stepChecked?, evalScalarFloat0?,
      evalScalarFloat1?, evalScalarFloat2?]

/-- Authoritative relational semantics for the migrated instruction slice.
The executable stepper below is proved to decide exactly these constructors;
the relation does not mention `stepChecked?`. -/
inductive Step : Config α → StepKind → Config α → Prop where
  | finish :
      Step ⟨.running ⟨locals, [], arity, remainder, [], []⟩, store⟩
        (.administrative .finish)
        ⟨.done (locals.values.take arity ++ remainder), store⟩
  | exitControl
      (hkind : frame.kind.isThrowing = false) :
      Step ⟨.running
          ⟨locals, [], arity, remainder, frame :: controls, calls⟩, store⟩
        (.administrative .exitControl)
        ⟨.running
          ⟨{ locals with
              values := locals.values.take frame.resultArity ++ frame.belowStack },
            frame.continuation, arity, remainder, controls, calls⟩,
          store⟩
  | unwindExceptionFrame
      (hthrow : throwingFrame.kind = .throwing tag arguments)
      (hhandler :
        match handler.kind with
        | .block | .loop => True
        | .tryTable catches => matchingCatch? tag catches = none
        | .throwing _ _ => False) :
      Step
        ⟨.running
          ⟨locals, [], arity, remainder,
            throwingFrame :: handler :: outer,
            calls⟩,
          store⟩
        (.administrative .unwindException)
        ⟨.running
          ⟨locals, [], arity, remainder,
            throwingFrame :: outer,
            calls⟩,
          store⟩
  | unwindNestedException
      (hthrow : throwingFrame.kind = .throwing tag arguments)
      (hhandler : handler.kind = .throwing previousTag previousArguments) :
      Step
        ⟨.running
          ⟨locals, [], arity, remainder,
            throwingFrame :: handler :: outer,
            calls⟩,
          store⟩
        (.administrative .unwindException)
        ⟨.running
          ⟨locals, [], arity, remainder,
            throwingFrame :: outer,
            calls⟩,
          store⟩
  | catchException
      (hthrow : throwingFrame.kind = .throwing tag arguments)
      (hmatch : matchingCatch? tag catches = some clause)
      (htarget :
        branchTarget? arity (catchLabel clause) outer
            ((prepareCatch tag arguments clause store).1 ++ belowStack) =
          some (targetCode, targetControl, targetValues)) :
      Step
        ⟨.running
          ⟨locals, [], arity, remainder,
            throwingFrame ::
              { kind := .tryTable catches
                paramArity := handlerParamArity
                resultArity := handlerResultArity
                body := handlerBody
                continuation := handlerContinuation
                belowStack } :: outer,
            calls⟩,
          store⟩
        (.administrative .catchException)
        ⟨.running
          ⟨{ locals with values := targetValues }, targetCode,
            arity, remainder, targetControl, calls⟩,
          (prepareCatch tag arguments clause store).2⟩
  | unwindExceptionCall
      (hthrow : throwingFrame.kind = .throwing tag arguments) :
      Step
        ⟨.running
          ⟨locals, [], arity, remainder,
            [throwingFrame],
            caller :: calls⟩,
          store⟩
        (.administrative .unwindException)
        ⟨.running
          (resumeExceptionCaller
            throwingFrame caller calls),
          store⟩
  | uncaughtException
      (hthrow : throwingFrame.kind = .throwing tag arguments) :
      Step
        ⟨.running
          ⟨locals, [], arity, remainder,
            [throwingFrame],
            []⟩,
          store⟩
        (.administrative .unwindException)
        ⟨.trapped (.uncaughtException tag arguments), store⟩
  | returnFromFunction :
      Step ⟨.running
          ⟨locals, .ret :: code, arity, remainder, controls, []⟩, store⟩
        (.administrative .returnFromFunction)
        ⟨.done (locals.values.take arity ++ remainder), store⟩
  | returnFromCallFallthrough
      (hsame : caller.returningInstance = store.runtime.entry) :
      Step ⟨.running
          ⟨locals, [], arity, remainder, [], caller :: calls⟩, store⟩
        (.administrative .returnFromCall)
        ⟨.running
          (resumeCaller
            ⟨locals, [], arity, remainder, [], caller :: calls⟩ caller calls),
          store⟩
  | returnFromCallExplicit
      (hsame : caller.returningInstance = store.runtime.entry) :
      Step ⟨.running
          ⟨locals, .ret :: code, arity, remainder, controls, caller :: calls⟩,
          store⟩
        (.administrative .returnFromCall)
        ⟨.running
          (resumeCaller
            ⟨locals, .ret :: code, arity, remainder, controls, caller :: calls⟩
            caller calls),
          store⟩
  | callCrossInstance
      (himports : functionIndex < store.runtime.currentModule.imports.length)
      (himport : store.runtime.currentModule.imports[functionIndex] = imp)
      (hnoHost : store.runtime.currentHost.funcs.length ≤ functionIndex)
      (hresolved : store.runtime.currentInstance.resolvedImports[functionIndex]? =
          some (.wasm calleeId localIdx))
      (hcallee : store.runtime.instances[calleeId.id]? = some calleeInstance)
      (hfn : calleeInstance.module.funcs[localIdx]? = some fn) :
      Step ⟨.running
          ⟨⟨params, localValues, values⟩, .call functionIndex :: code,
            arity, remainder, controls, calls⟩, store⟩
        (.administrative .callCrossInstance)
        ⟨.running
          ⟨fn.toLocals (values.take imp.params.length).reverse,
            fn.body, fn.results.length, [], [],
            { locals := ⟨params, localValues, values.drop imp.params.length⟩
              continuation := code
              resultArity := arity
              callerRemainder := remainder
              control := controls
              returningInstance := store.runtime.entry } :: calls⟩,
          { runtime := { instances := store.runtime.instances, entry := calleeId }
            wasm := store.wasm }⟩
  | returnFromCallCrossInstanceFallthrough
      (hdiff : caller.returningInstance ≠ store.runtime.entry) :
      Step ⟨.running
          ⟨locals, [], arity, remainder, [], caller :: calls⟩, store⟩
        (.administrative .returnFromCallCrossInstance)
        ⟨.running
          (resumeCaller
            ⟨locals, [], arity, remainder, [], caller :: calls⟩ caller calls),
          { store with runtime := { store.runtime with entry := caller.returningInstance } }⟩
  | returnFromCallCrossInstanceExplicit
      (hdiff : caller.returningInstance ≠ store.runtime.entry) :
      Step ⟨.running
          ⟨locals, .ret :: code, arity, remainder, controls, caller :: calls⟩, store⟩
        (.administrative .returnFromCallCrossInstance)
        ⟨.running
          (resumeCaller
            ⟨locals, .ret :: code, arity, remainder, controls, caller :: calls⟩
            caller calls),
          { store with runtime := { store.runtime with entry := caller.returningInstance } }⟩
  | block :
      Step ⟨.running
          ⟨⟨params, localValues, values⟩,
            .block paramArity resultArity body paramTypes resultTypes :: code,
            arity, remainder, controls, calls⟩, store⟩
        (.instruction
          (.block paramArity resultArity body paramTypes resultTypes))
        ⟨.running
          ⟨⟨params, localValues, values⟩, body, arity, remainder,
            { kind := .block, paramArity, resultArity, body,
              continuation := code,
              belowStack := values.drop paramArity } :: controls, calls⟩, store⟩
  | loop :
      Step ⟨.running
          ⟨⟨params, localValues, values⟩,
            .loop paramArity resultArity body paramTypes resultTypes :: code,
            arity, remainder, controls, calls⟩, store⟩
        (.instruction
          (.loop paramArity resultArity body paramTypes resultTypes))
        ⟨.running
          ⟨⟨params, localValues, values⟩, body, arity, remainder,
            { kind := .loop, paramArity, resultArity, body,
              continuation := code,
              belowStack := values.drop paramArity } :: controls, calls⟩, store⟩
  | tryTable :
      Step ⟨.running
          ⟨⟨params, localValues, values⟩,
            .tryTable paramArity resultArity catches body
              paramTypes resultTypes :: code,
            arity, remainder, controls, calls⟩, store⟩
        (.instruction
          (.tryTable paramArity resultArity catches body
            paramTypes resultTypes))
        ⟨.running
          ⟨⟨params, localValues, values⟩, body, arity, remainder,
            { kind := .tryTable catches, paramArity, resultArity, body,
              continuation := code,
              belowStack := values.drop paramArity } :: controls, calls⟩, store⟩
  | throwI
      (htag : store.runtime.currentModule.tags[tagIndex]? = some tagType)
      (hargs : tagType.params.length ≤ values.length) :
      Step ⟨.running
          ⟨⟨params, localValues, values⟩, .throwI tagIndex :: code,
            arity, remainder, controls, calls⟩, store⟩
        (.instruction (.throwI tagIndex))
        ⟨.running
          ⟨⟨params, localValues, values.drop tagType.params.length⟩,
            [], arity, remainder,
            { kind := .throwing (canonicalTagIndex store tagIndex)
                (values.take tagType.params.length)
              paramArity := 0
              resultArity := 0
              body := []
              continuation := []
              belowStack := [] } :: controls,
            calls⟩,
          store⟩
  | throwRefNull :
      Step ⟨.running
          ⟨⟨params, localValues, .exnref none :: values⟩,
            .throwRef :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .throwRef)
        ⟨.trapped .nullExceptionReference, store⟩
  | throwRef
      (hexception :
        store.wasm.exns[exceptionIndex]? = some (tag, arguments)) :
      Step ⟨.running
          ⟨⟨params, localValues, .exnref (some exceptionIndex) :: values⟩,
            .throwRef :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .throwRef)
        ⟨.running
          ⟨⟨params, localValues, values⟩, [], arity, remainder,
            { kind := .throwing tag arguments
              paramArity := 0
              resultArity := 0
              body := []
              continuation := []
              belowStack := [] } :: controls,
            calls⟩,
          store⟩
  | iff
      (h : selectedBody = if condition ≠ 0 then thenBody else elseBody) :
      Step ⟨.running
          ⟨⟨params, localValues, .i32 condition :: values⟩,
            .iff paramArity resultArity thenBody elseBody
              paramTypes resultTypes :: code,
            arity, remainder, controls, calls⟩, store⟩
        (.instruction
          (.iff paramArity resultArity thenBody elseBody
            paramTypes resultTypes))
        ⟨.running
          ⟨⟨params, localValues, values⟩,
            selectedBody,
            arity, remainder,
            { kind := .block, paramArity, resultArity,
              body := selectedBody,
              continuation := code,
              belowStack := values.drop paramArity } :: controls, calls⟩, store⟩
  | br
      (h : branchTarget? arity depth controls values =
        some (targetCode, targetControl, targetValues)) :
      Step ⟨.running
          ⟨⟨params, localValues, values⟩, .br depth :: code,
            arity, remainder, controls, calls⟩, store⟩
        (.instruction (.br depth))
        ⟨.running
          ⟨⟨params, localValues, targetValues⟩, targetCode,
            arity, remainder, targetControl, calls⟩, store⟩
  | brIfZero :
      Step ⟨.running
          ⟨⟨params, localValues, .i32 0 :: values⟩, .br_if depth :: code,
            arity, remainder, controls, calls⟩, store⟩
        (.instruction (.br_if depth))
        ⟨.running
          ⟨⟨params, localValues, values⟩, code,
            arity, remainder, controls, calls⟩, store⟩
  | brIf
      (hcondition : condition ≠ 0)
      (h : branchTarget? arity depth controls values =
        some (targetCode, targetControl, targetValues)) :
      Step ⟨.running
          ⟨⟨params, localValues, .i32 condition :: values⟩,
            .br_if depth :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.br_if depth))
        ⟨.running
          ⟨⟨params, localValues, targetValues⟩, targetCode,
            arity, remainder, targetControl, calls⟩, store⟩
  | brTable
      (h : branchTarget? arity (targets[index.toNat]?.getD defaultTarget)
          controls values =
        some (targetCode, targetControl, targetValues)) :
      Step ⟨.running
          ⟨⟨params, localValues, .i32 index :: values⟩,
            .brTable targets defaultTarget :: code,
            arity, remainder, controls, calls⟩, store⟩
        (.instruction (.brTable targets defaultTarget))
        ⟨.running
          ⟨⟨params, localValues, targetValues⟩, targetCode,
            arity, remainder, targetControl, calls⟩, store⟩
  | callHostReturn
      (himports : functionIndex < store.runtime.currentModule.imports.length)
      (himport : store.runtime.currentModule.imports[functionIndex] = imp)
      (hhost : store.runtime.currentHost.funcs[functionIndex]? = some hostFunction)
      (hinvoke :
        hostFunction.invoke store.wasm
          (values.take imp.params.length).reverse = .Return results wasm) :
      Step ⟨.running ⟨⟨params, localValues, values⟩,
          .call functionIndex :: code,
          arity, remainder, controls, calls⟩, store⟩
        (.host functionIndex)
        ⟨.running ⟨⟨params, localValues,
            results.take imp.results.length ++
              values.drop imp.params.length⟩,
          code, arity, remainder, controls, calls⟩,
          { store with wasm }⟩
  | callHostTrap
      (himports : functionIndex < store.runtime.currentModule.imports.length)
      (himport : store.runtime.currentModule.imports[functionIndex] = imp)
      (hhost : store.runtime.currentHost.funcs[functionIndex]? = some hostFunction)
      (hinvoke :
        hostFunction.invoke store.wasm
          (values.take imp.params.length).reverse = .Trap wasm message) :
      Step ⟨.running ⟨⟨params, localValues, values⟩,
          .call functionIndex :: code,
          arity, remainder, controls, calls⟩, store⟩
        (.host functionIndex)
        ⟨.trapped (.host message), { store with wasm }⟩
  | callHostThrow
      (himports : functionIndex < store.runtime.currentModule.imports.length)
      (himport : store.runtime.currentModule.imports[functionIndex] = imp)
      (hhost : store.runtime.currentHost.funcs[functionIndex]? = some hostFunction)
      (hinvoke :
        hostFunction.invoke store.wasm
          (values.take imp.params.length).reverse =
            .Throw wasm tag arguments) :
      Step ⟨.running ⟨⟨params, localValues, values⟩,
          .call functionIndex :: code,
          arity, remainder, controls, calls⟩, store⟩
        (.host functionIndex)
        ⟨.running
          ⟨⟨params, localValues, values.drop imp.params.length⟩,
            [], arity, remainder,
            [{ kind := .throwing tag arguments
               paramArity := 0
               resultArity := 0
               body := []
               continuation := []
               belowStack := [] }] ++ controls,
            calls⟩,
          { store with wasm }⟩
  | call
      (himports : ¬functionIndex < store.runtime.currentModule.imports.length)
      (hfn : store.runtime.currentModule.funcs[
          functionIndex - store.runtime.currentModule.imports.length]? = some fn) :
      Step ⟨.running
          ⟨⟨params, localValues, values⟩, .call functionIndex :: code,
            arity, remainder, controls, calls⟩, store⟩
        (.instruction (.call functionIndex))
        ⟨.running
          ⟨fn.toLocals (values.take fn.numParams).reverse,
            fn.body, fn.results.length, [], [],
            { locals := ⟨params, localValues, values.drop fn.numParams⟩
              continuation := code
              resultArity := arity
              callerRemainder := remainder
              control := controls
              returningInstance := store.runtime.entry } :: calls⟩,
          store⟩
  | returnCallHostReturn
      (himports : functionIndex < store.runtime.currentModule.imports.length)
      (himport : store.runtime.currentModule.imports[functionIndex] = imp)
      (hhost : store.runtime.currentHost.funcs[functionIndex]? = some hostFunction)
      (hinvoke :
        hostFunction.invoke store.wasm
          (values.take imp.params.length).reverse = .Return results wasm) :
      Step ⟨.running ⟨⟨params, localValues, values⟩,
          .returnCall functionIndex :: code,
          arity, remainder, controls, calls⟩, store⟩
        (.host functionIndex)
        ⟨.running ⟨⟨params, localValues,
            results.take imp.results.length⟩,
          [], arity, remainder, [], calls⟩,
          { store with wasm }⟩
  | returnCallHostTrap
      (himports : functionIndex < store.runtime.currentModule.imports.length)
      (himport : store.runtime.currentModule.imports[functionIndex] = imp)
      (hhost : store.runtime.currentHost.funcs[functionIndex]? = some hostFunction)
      (hinvoke :
        hostFunction.invoke store.wasm
          (values.take imp.params.length).reverse = .Trap wasm message) :
      Step ⟨.running ⟨⟨params, localValues, values⟩,
          .returnCall functionIndex :: code,
          arity, remainder, controls, calls⟩, store⟩
        (.host functionIndex)
        ⟨.trapped (.host message), { store with wasm }⟩
  | returnCallHostThrow
      (himports : functionIndex < store.runtime.currentModule.imports.length)
      (himport : store.runtime.currentModule.imports[functionIndex] = imp)
      (hhost : store.runtime.currentHost.funcs[functionIndex]? = some hostFunction)
      (hinvoke :
        hostFunction.invoke store.wasm
          (values.take imp.params.length).reverse =
            .Throw wasm tag arguments) :
      Step ⟨.running ⟨⟨params, localValues, values⟩,
          .returnCall functionIndex :: code,
          arity, remainder, controls, calls⟩, store⟩
        (.host functionIndex)
        ⟨.running
          ⟨⟨params, localValues, []⟩,
            [], arity, remainder,
            [{ kind := .throwing tag arguments
               paramArity := 0
               resultArity := 0
               body := []
               continuation := []
               belowStack := [] }],
            calls⟩,
          { store with wasm }⟩
  | returnCall
      (himports : ¬functionIndex < store.runtime.currentModule.imports.length)
      (hfn : store.runtime.currentModule.funcs[
          functionIndex - store.runtime.currentModule.imports.length]? = some fn) :
      Step ⟨.running
          ⟨⟨params, localValues, values⟩, .returnCall functionIndex :: code,
            arity, remainder, controls, calls⟩, store⟩
        (.instruction (.returnCall functionIndex))
        ⟨.running
          ⟨fn.toLocals (values.take fn.numParams).reverse,
            fn.body, arity, remainder, [], calls⟩,
          store⟩
  | callIndirectUndefined
      (hselector : selector.addrNat? = some elementIndex)
      (htable : store.wasm.tables[tableIndex]? = some table)
      (helement : ¬elementIndex < table.length) :
      Step ⟨.running ⟨⟨params, localValues, selector :: values⟩,
          .callIndirect typeIndex tableIndex :: code,
          arity, remainder, controls, calls⟩, store⟩
        (.instruction (.callIndirect typeIndex tableIndex))
        ⟨.trapped .undefinedElement, store⟩
  | callIndirectUninitialized
      (hselector : selector.addrNat? = some elementIndex)
      (htable : store.wasm.tables[tableIndex]? = some table)
      (helement : table[elementIndex]? = some (.funcref none)) :
      Step ⟨.running ⟨⟨params, localValues, selector :: values⟩,
          .callIndirect typeIndex tableIndex :: code,
          arity, remainder, controls, calls⟩, store⟩
        (.instruction (.callIndirect typeIndex tableIndex))
        ⟨.trapped (.uninitializedElement elementIndex), store⟩
  | callIndirectForeignTypeMismatch
      (hselector : selector.addrNat? = some elementIndex)
      (htable : store.wasm.tables[tableIndex]? = some table)
      (helement : table[elementIndex]? = some (.funcref (some functionIndex)))
      (hforeign : isForeignFunctionIndex
        store.runtime.currentModule.imports.length functionIndex = true)
      (hhost : store.runtime.currentHost.foreignFuncs[
        functionIndex - foreignFunctionBase]? = some hostFunction)
      (hexpected : store.runtime.currentModule.types[typeIndex]? = some expected)
      (htype : (hostFunction.params == expected.params &&
        hostFunction.results == expected.results) = false) :
      Step ⟨.running ⟨⟨params, localValues, selector :: values⟩,
          .callIndirect typeIndex tableIndex :: code,
          arity, remainder, controls, calls⟩, store⟩
        (.instruction (.callIndirect typeIndex tableIndex))
        ⟨.trapped .indirectCallTypeMismatch, store⟩
  | callIndirectForeignReturn
      (hselector : selector.addrNat? = some elementIndex)
      (htable : store.wasm.tables[tableIndex]? = some table)
      (helement : table[elementIndex]? = some (.funcref (some functionIndex)))
      (hforeign : isForeignFunctionIndex
        store.runtime.currentModule.imports.length functionIndex = true)
      (hhost : store.runtime.currentHost.foreignFuncs[
        functionIndex - foreignFunctionBase]? = some hostFunction)
      (hexpected : store.runtime.currentModule.types[typeIndex]? = some expected)
      (htype : (hostFunction.params == expected.params &&
        hostFunction.results == expected.results) = true)
      (hinvoke : hostFunction.invoke store.wasm
        (values.take hostFunction.params.length).reverse =
          .Return results wasm) :
      Step ⟨.running ⟨⟨params, localValues, selector :: values⟩,
          .callIndirect typeIndex tableIndex :: code,
          arity, remainder, controls, calls⟩, store⟩
        (.host functionIndex)
        ⟨.running ⟨⟨params, localValues,
            results.take hostFunction.results.length ++
              values.drop hostFunction.params.length⟩,
          code, arity, remainder, controls, calls⟩,
          { store with wasm }⟩
  | callIndirectForeignTrap
      (hselector : selector.addrNat? = some elementIndex)
      (htable : store.wasm.tables[tableIndex]? = some table)
      (helement : table[elementIndex]? = some (.funcref (some functionIndex)))
      (hforeign : isForeignFunctionIndex
        store.runtime.currentModule.imports.length functionIndex = true)
      (hhost : store.runtime.currentHost.foreignFuncs[
        functionIndex - foreignFunctionBase]? = some hostFunction)
      (hexpected : store.runtime.currentModule.types[typeIndex]? = some expected)
      (htype : (hostFunction.params == expected.params &&
        hostFunction.results == expected.results) = true)
      (hinvoke : hostFunction.invoke store.wasm
        (values.take hostFunction.params.length).reverse =
          .Trap wasm message) :
      Step ⟨.running ⟨⟨params, localValues, selector :: values⟩,
          .callIndirect typeIndex tableIndex :: code,
          arity, remainder, controls, calls⟩, store⟩
        (.host functionIndex)
        ⟨.trapped (.host message), { store with wasm }⟩
  | callIndirectForeignThrow
      (hselector : selector.addrNat? = some elementIndex)
      (htable : store.wasm.tables[tableIndex]? = some table)
      (helement : table[elementIndex]? = some (.funcref (some functionIndex)))
      (hforeign : isForeignFunctionIndex
        store.runtime.currentModule.imports.length functionIndex = true)
      (hhost : store.runtime.currentHost.foreignFuncs[
        functionIndex - foreignFunctionBase]? = some hostFunction)
      (hexpected : store.runtime.currentModule.types[typeIndex]? = some expected)
      (htype : (hostFunction.params == expected.params &&
        hostFunction.results == expected.results) = true)
      (hinvoke : hostFunction.invoke store.wasm
        (values.take hostFunction.params.length).reverse =
          .Throw wasm tag arguments) :
      Step ⟨.running ⟨⟨params, localValues, selector :: values⟩,
          .callIndirect typeIndex tableIndex :: code,
          arity, remainder, controls, calls⟩, store⟩
        (.host functionIndex)
        ⟨.running
          ⟨⟨params, localValues, values.drop hostFunction.params.length⟩,
            [], arity, remainder,
            { kind := .throwing tag arguments
              paramArity := 0
              resultArity := 0
              body := []
              continuation := []
              belowStack := [] } :: controls,
            calls⟩,
          { store with wasm }⟩
  | callIndirectHostTypeMismatch
      (hselector : selector.addrNat? = some elementIndex)
      (htable : store.wasm.tables[tableIndex]? = some table)
      (helement : table[elementIndex]? = some (.funcref (some functionIndex)))
      (himports : functionIndex < store.runtime.currentModule.imports.length)
      (himport : store.runtime.currentModule.imports[functionIndex] = imp)
      (hhost : store.runtime.currentHost.funcs[functionIndex]? = some hostFunction)
      (hsignature : store.runtime.currentModule.funcSig? functionIndex = some signature)
      (hexpected : store.runtime.currentModule.types[typeIndex]? = some expected)
      (htype : store.runtime.currentModule.indirectCallTypeOk
        functionIndex typeIndex signature expected = false) :
      Step ⟨.running ⟨⟨params, localValues, selector :: values⟩,
          .callIndirect typeIndex tableIndex :: code,
          arity, remainder, controls, calls⟩, store⟩
        (.instruction (.callIndirect typeIndex tableIndex))
        ⟨.trapped .indirectCallTypeMismatch, store⟩
  | callIndirectHostReturn
      (hselector : selector.addrNat? = some elementIndex)
      (htable : store.wasm.tables[tableIndex]? = some table)
      (helement : table[elementIndex]? = some (.funcref (some functionIndex)))
      (himports : functionIndex < store.runtime.currentModule.imports.length)
      (himport : store.runtime.currentModule.imports[functionIndex] = imp)
      (hhost : store.runtime.currentHost.funcs[functionIndex]? = some hostFunction)
      (hsignature : store.runtime.currentModule.funcSig? functionIndex = some signature)
      (hexpected : store.runtime.currentModule.types[typeIndex]? = some expected)
      (htype : store.runtime.currentModule.indirectCallTypeOk
        functionIndex typeIndex signature expected = true)
      (hinvoke :
        hostFunction.invoke store.wasm
          (values.take imp.params.length).reverse = .Return results wasm) :
      Step ⟨.running ⟨⟨params, localValues, selector :: values⟩,
          .callIndirect typeIndex tableIndex :: code,
          arity, remainder, controls, calls⟩, store⟩
        (.host functionIndex)
        ⟨.running ⟨⟨params, localValues,
            results.take imp.results.length ++ values.drop imp.params.length⟩,
          code, arity, remainder, controls, calls⟩,
          { store with wasm }⟩
  | callIndirectHostTrap
      (hselector : selector.addrNat? = some elementIndex)
      (htable : store.wasm.tables[tableIndex]? = some table)
      (helement : table[elementIndex]? = some (.funcref (some functionIndex)))
      (himports : functionIndex < store.runtime.currentModule.imports.length)
      (himport : store.runtime.currentModule.imports[functionIndex] = imp)
      (hhost : store.runtime.currentHost.funcs[functionIndex]? = some hostFunction)
      (hsignature : store.runtime.currentModule.funcSig? functionIndex = some signature)
      (hexpected : store.runtime.currentModule.types[typeIndex]? = some expected)
      (htype : store.runtime.currentModule.indirectCallTypeOk
        functionIndex typeIndex signature expected = true)
      (hinvoke :
        hostFunction.invoke store.wasm
          (values.take imp.params.length).reverse = .Trap wasm message) :
      Step ⟨.running ⟨⟨params, localValues, selector :: values⟩,
          .callIndirect typeIndex tableIndex :: code,
          arity, remainder, controls, calls⟩, store⟩
        (.host functionIndex)
        ⟨.trapped (.host message), { store with wasm }⟩
  | callIndirectHostThrow
      (hselector : selector.addrNat? = some elementIndex)
      (htable : store.wasm.tables[tableIndex]? = some table)
      (helement : table[elementIndex]? = some (.funcref (some functionIndex)))
      (himports : functionIndex < store.runtime.currentModule.imports.length)
      (himport : store.runtime.currentModule.imports[functionIndex] = imp)
      (hhost : store.runtime.currentHost.funcs[functionIndex]? = some hostFunction)
      (hsignature : store.runtime.currentModule.funcSig? functionIndex = some signature)
      (hexpected : store.runtime.currentModule.types[typeIndex]? = some expected)
      (htype : store.runtime.currentModule.indirectCallTypeOk
        functionIndex typeIndex signature expected = true)
      (hinvoke :
        hostFunction.invoke store.wasm
          (values.take imp.params.length).reverse =
            .Throw wasm tag arguments) :
      Step ⟨.running ⟨⟨params, localValues, selector :: values⟩,
          .callIndirect typeIndex tableIndex :: code,
          arity, remainder, controls, calls⟩, store⟩
        (.host functionIndex)
        ⟨.running
          ⟨⟨params, localValues, values.drop imp.params.length⟩,
            [], arity, remainder,
            { kind := .throwing tag arguments
              paramArity := 0
              resultArity := 0
              body := []
              continuation := []
              belowStack := [] } :: controls,
            calls⟩,
          { store with wasm }⟩
  | callIndirectCrossInstanceTypeMismatch
      (hselector : selector.addrNat? = some elementIndex)
      (htable : store.wasm.tables[tableIndex]? = some table)
      (helement : table[elementIndex]? = some (.funcref (some functionIndex)))
      (himports : functionIndex < store.runtime.currentModule.imports.length)
      (himport : store.runtime.currentModule.imports[functionIndex] = imp)
      (hnoHost : store.runtime.currentHost.funcs.length ≤ functionIndex)
      (hsignature : store.runtime.currentModule.funcSig? functionIndex = some signature)
      (hexpected : store.runtime.currentModule.types[typeIndex]? = some expected)
      (hresolved : store.runtime.currentInstance.resolvedImports[functionIndex]? =
          some (.wasm calleeId localIdx))
      (htype : store.runtime.currentModule.indirectCallTypeOk
        functionIndex typeIndex signature expected = false) :
      Step ⟨.running ⟨⟨params, localValues, selector :: values⟩,
          .callIndirect typeIndex tableIndex :: code,
          arity, remainder, controls, calls⟩, store⟩
        (.instruction (.callIndirect typeIndex tableIndex))
        ⟨.trapped .indirectCallTypeMismatch, store⟩
  | callIndirectCrossInstance
      (hselector : selector.addrNat? = some elementIndex)
      (htable : store.wasm.tables[tableIndex]? = some table)
      (helement : table[elementIndex]? = some (.funcref (some functionIndex)))
      (himports : functionIndex < store.runtime.currentModule.imports.length)
      (himport : store.runtime.currentModule.imports[functionIndex] = imp)
      (hnoHost : store.runtime.currentHost.funcs.length ≤ functionIndex)
      (hsignature : store.runtime.currentModule.funcSig? functionIndex = some signature)
      (hexpected : store.runtime.currentModule.types[typeIndex]? = some expected)
      (hresolved : store.runtime.currentInstance.resolvedImports[functionIndex]? =
          some (.wasm calleeId localIdx))
      (htype : store.runtime.currentModule.indirectCallTypeOk
        functionIndex typeIndex signature expected = true)
      (hcallee : store.runtime.instances[calleeId.id]? = some calleeInstance)
      (hfn : calleeInstance.module.funcs[localIdx]? = some fn) :
      Step ⟨.running ⟨⟨params, localValues, selector :: values⟩,
          .callIndirect typeIndex tableIndex :: code,
          arity, remainder, controls, calls⟩, store⟩
        (.administrative .callCrossInstance)
        ⟨.running
          ⟨fn.toLocals (values.take imp.params.length).reverse,
            fn.body, fn.results.length, [], [],
            { locals := ⟨params, localValues, values.drop imp.params.length⟩
              continuation := code
              resultArity := arity
              callerRemainder := remainder
              control := controls
              returningInstance := store.runtime.entry } :: calls⟩,
          { runtime := { instances := store.runtime.instances, entry := calleeId }
            wasm := store.wasm }⟩
  | callIndirectTypeMismatch
      (hselector : selector.addrNat? = some elementIndex)
      (htable : store.wasm.tables[tableIndex]? = some table)
      (helement : table[elementIndex]? = some (.funcref (some functionIndex)))
      (himports : ¬functionIndex < store.runtime.currentModule.imports.length)
      (hnotforeign : isForeignFunctionIndex
        store.runtime.currentModule.imports.length functionIndex = false)
      (hfn : store.runtime.currentModule.funcs[
        functionIndex - store.runtime.currentModule.imports.length]? = some fn)
      (hsignature : store.runtime.currentModule.funcSig? functionIndex = some signature)
      (hexpected : store.runtime.currentModule.types[typeIndex]? = some expected)
      (htype : store.runtime.currentModule.indirectCallTypeOk
        functionIndex typeIndex signature expected = false) :
      Step ⟨.running ⟨⟨params, localValues, selector :: values⟩,
          .callIndirect typeIndex tableIndex :: code,
          arity, remainder, controls, calls⟩, store⟩
        (.instruction (.callIndirect typeIndex tableIndex))
        ⟨.trapped .indirectCallTypeMismatch, store⟩
  | callIndirect
      (hselector : selector.addrNat? = some elementIndex)
      (htable : store.wasm.tables[tableIndex]? = some table)
      (helement : table[elementIndex]? = some (.funcref (some functionIndex)))
      (himports : ¬functionIndex < store.runtime.currentModule.imports.length)
      (hnotforeign : isForeignFunctionIndex
        store.runtime.currentModule.imports.length functionIndex = false)
      (hfn : store.runtime.currentModule.funcs[
        functionIndex - store.runtime.currentModule.imports.length]? = some fn)
      (hsignature : store.runtime.currentModule.funcSig? functionIndex = some signature)
      (hexpected : store.runtime.currentModule.types[typeIndex]? = some expected)
      (htype : store.runtime.currentModule.indirectCallTypeOk
        functionIndex typeIndex signature expected = true) :
      Step ⟨.running ⟨⟨params, localValues, selector :: values⟩,
          .callIndirect typeIndex tableIndex :: code,
          arity, remainder, controls, calls⟩, store⟩
        (.instruction (.callIndirect typeIndex tableIndex))
        ⟨.running
          ⟨fn.toLocals (values.take fn.numParams).reverse,
            fn.body, fn.results.length, [], [],
            { locals := ⟨params, localValues, values.drop fn.numParams⟩
              continuation := code
              resultArity := arity
              callerRemainder := remainder
              control := controls
              returningInstance := store.runtime.entry } :: calls⟩,
          store⟩
  | returnCallIndirectUndefined
      (hselector : selector.addrNat? = some elementIndex)
      (htable : store.wasm.tables[tableIndex]? = some table)
      (helement : ¬elementIndex < table.length) :
      Step ⟨.running ⟨⟨params, localValues, selector :: values⟩,
          .returnCallIndirect typeIndex tableIndex :: code,
          arity, remainder, controls, calls⟩, store⟩
        (.instruction (.returnCallIndirect typeIndex tableIndex))
        ⟨.trapped .undefinedElement, store⟩
  | returnCallIndirectUninitialized
      (hselector : selector.addrNat? = some elementIndex)
      (htable : store.wasm.tables[tableIndex]? = some table)
      (helement : table[elementIndex]? = some (.funcref none)) :
      Step ⟨.running ⟨⟨params, localValues, selector :: values⟩,
          .returnCallIndirect typeIndex tableIndex :: code,
          arity, remainder, controls, calls⟩, store⟩
        (.instruction (.returnCallIndirect typeIndex tableIndex))
        ⟨.trapped (.uninitializedElement elementIndex), store⟩
  | returnCallIndirectHostTypeMismatch
      (hselector : selector.addrNat? = some elementIndex)
      (htable : store.wasm.tables[tableIndex]? = some table)
      (helement : table[elementIndex]? = some (.funcref (some functionIndex)))
      (himports : functionIndex < store.runtime.currentModule.imports.length)
      (himport : store.runtime.currentModule.imports[functionIndex] = imp)
      (hhost : store.runtime.currentHost.funcs[functionIndex]? = some hostFunction)
      (hsignature : store.runtime.currentModule.funcSig? functionIndex = some signature)
      (hexpected : store.runtime.currentModule.types[typeIndex]? = some expected)
      (htype : store.runtime.currentModule.indirectCallTypeOk
        functionIndex typeIndex signature expected = false) :
      Step ⟨.running ⟨⟨params, localValues, selector :: values⟩,
          .returnCallIndirect typeIndex tableIndex :: code,
          arity, remainder, controls, calls⟩, store⟩
        (.instruction (.returnCallIndirect typeIndex tableIndex))
        ⟨.trapped .indirectCallTypeMismatch, store⟩
  | returnCallIndirectHostReturn
      (hselector : selector.addrNat? = some elementIndex)
      (htable : store.wasm.tables[tableIndex]? = some table)
      (helement : table[elementIndex]? = some (.funcref (some functionIndex)))
      (himports : functionIndex < store.runtime.currentModule.imports.length)
      (himport : store.runtime.currentModule.imports[functionIndex] = imp)
      (hhost : store.runtime.currentHost.funcs[functionIndex]? = some hostFunction)
      (hsignature : store.runtime.currentModule.funcSig? functionIndex = some signature)
      (hexpected : store.runtime.currentModule.types[typeIndex]? = some expected)
      (htype : store.runtime.currentModule.indirectCallTypeOk
        functionIndex typeIndex signature expected = true)
      (hinvoke :
        hostFunction.invoke store.wasm
          (values.take imp.params.length).reverse = .Return results wasm) :
      Step ⟨.running ⟨⟨params, localValues, selector :: values⟩,
          .returnCallIndirect typeIndex tableIndex :: code,
          arity, remainder, controls, calls⟩, store⟩
        (.host functionIndex)
        ⟨.running ⟨⟨params, localValues,
            results.take imp.results.length⟩,
          [], arity, remainder, [], calls⟩,
          { store with wasm }⟩
  | returnCallIndirectHostTrap
      (hselector : selector.addrNat? = some elementIndex)
      (htable : store.wasm.tables[tableIndex]? = some table)
      (helement : table[elementIndex]? = some (.funcref (some functionIndex)))
      (himports : functionIndex < store.runtime.currentModule.imports.length)
      (himport : store.runtime.currentModule.imports[functionIndex] = imp)
      (hhost : store.runtime.currentHost.funcs[functionIndex]? = some hostFunction)
      (hsignature : store.runtime.currentModule.funcSig? functionIndex = some signature)
      (hexpected : store.runtime.currentModule.types[typeIndex]? = some expected)
      (htype : store.runtime.currentModule.indirectCallTypeOk
        functionIndex typeIndex signature expected = true)
      (hinvoke :
        hostFunction.invoke store.wasm
          (values.take imp.params.length).reverse = .Trap wasm message) :
      Step ⟨.running ⟨⟨params, localValues, selector :: values⟩,
          .returnCallIndirect typeIndex tableIndex :: code,
          arity, remainder, controls, calls⟩, store⟩
        (.host functionIndex)
        ⟨.trapped (.host message), { store with wasm }⟩
  | returnCallIndirectHostThrow
      (hselector : selector.addrNat? = some elementIndex)
      (htable : store.wasm.tables[tableIndex]? = some table)
      (helement : table[elementIndex]? = some (.funcref (some functionIndex)))
      (himports : functionIndex < store.runtime.currentModule.imports.length)
      (himport : store.runtime.currentModule.imports[functionIndex] = imp)
      (hhost : store.runtime.currentHost.funcs[functionIndex]? = some hostFunction)
      (hsignature : store.runtime.currentModule.funcSig? functionIndex = some signature)
      (hexpected : store.runtime.currentModule.types[typeIndex]? = some expected)
      (htype : store.runtime.currentModule.indirectCallTypeOk
        functionIndex typeIndex signature expected = true)
      (hinvoke :
        hostFunction.invoke store.wasm
          (values.take imp.params.length).reverse =
            .Throw wasm tag arguments) :
      Step ⟨.running ⟨⟨params, localValues, selector :: values⟩,
          .returnCallIndirect typeIndex tableIndex :: code,
          arity, remainder, controls, calls⟩, store⟩
        (.host functionIndex)
        ⟨.running
          ⟨⟨params, localValues, []⟩,
            [], arity, remainder,
            [{ kind := .throwing tag arguments
               paramArity := 0
               resultArity := 0
               body := []
               continuation := []
               belowStack := [] }],
            calls⟩,
          { store with wasm }⟩
  | returnCallIndirectTypeMismatch
      (hselector : selector.addrNat? = some elementIndex)
      (htable : store.wasm.tables[tableIndex]? = some table)
      (helement : table[elementIndex]? = some (.funcref (some functionIndex)))
      (himports : ¬functionIndex < store.runtime.currentModule.imports.length)
      (hfn : store.runtime.currentModule.funcs[
        functionIndex - store.runtime.currentModule.imports.length]? = some fn)
      (hsignature : store.runtime.currentModule.funcSig? functionIndex = some signature)
      (hexpected : store.runtime.currentModule.types[typeIndex]? = some expected)
      (htype : store.runtime.currentModule.indirectCallTypeOk
        functionIndex typeIndex signature expected = false) :
      Step ⟨.running ⟨⟨params, localValues, selector :: values⟩,
          .returnCallIndirect typeIndex tableIndex :: code,
          arity, remainder, controls, calls⟩, store⟩
        (.instruction (.returnCallIndirect typeIndex tableIndex))
        ⟨.trapped .indirectCallTypeMismatch, store⟩
  | returnCallIndirect
      (hselector : selector.addrNat? = some elementIndex)
      (htable : store.wasm.tables[tableIndex]? = some table)
      (helement : table[elementIndex]? = some (.funcref (some functionIndex)))
      (himports : ¬functionIndex < store.runtime.currentModule.imports.length)
      (hfn : store.runtime.currentModule.funcs[
        functionIndex - store.runtime.currentModule.imports.length]? = some fn)
      (hsignature : store.runtime.currentModule.funcSig? functionIndex = some signature)
      (hexpected : store.runtime.currentModule.types[typeIndex]? = some expected)
      (htype : store.runtime.currentModule.indirectCallTypeOk
        functionIndex typeIndex signature expected = true) :
      Step ⟨.running ⟨⟨params, localValues, selector :: values⟩,
          .returnCallIndirect typeIndex tableIndex :: code,
          arity, remainder, controls, calls⟩, store⟩
        (.instruction (.returnCallIndirect typeIndex tableIndex))
        ⟨.running
          ⟨fn.toLocals (values.take fn.numParams).reverse,
            fn.body, arity, remainder, [], calls⟩,
          store⟩
  | refNull :
      Step ⟨.running ⟨⟨params, localValues, values⟩,
          .refNull staticType :: code,
            arity, remainder, controls, calls⟩, store⟩
        (.instruction (.refNull staticType))
        ⟨.running ⟨⟨params, localValues, .funcref none :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | refNullExtern :
      Step ⟨.running ⟨⟨params, localValues, values⟩,
          .refNullExtern staticType :: code,
            arity, remainder, controls, calls⟩, store⟩
        (.instruction (.refNullExtern staticType))
        ⟨.running ⟨⟨params, localValues, .externref none :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | refNullExn :
      Step ⟨.running ⟨⟨params, localValues, values⟩,
          .refNullExn staticType :: code,
            arity, remainder, controls, calls⟩, store⟩
        (.instruction (.refNullExn staticType))
        ⟨.running ⟨⟨params, localValues, .exnref none :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | refFunc :
      Step ⟨.running ⟨⟨params, localValues, values⟩,
          .refFunc functionIndex :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.refFunc functionIndex))
        ⟨.running ⟨⟨params, localValues, .funcref (some functionIndex) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | callRefNull :
      Step ⟨.running ⟨⟨params, localValues, .funcref none :: values⟩,
          .callRef typeIndex :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.callRef typeIndex))
        ⟨.trapped .nullFunctionReference, store⟩
  | callRefHostReturn
      (himports : functionIndex < store.runtime.currentModule.imports.length)
      (himport : store.runtime.currentModule.imports[functionIndex] = imp)
      (hhost : store.runtime.currentHost.funcs[functionIndex]? = some hostFunction)
      (hinvoke :
        hostFunction.invoke store.wasm
          (values.take imp.params.length).reverse = .Return results wasm) :
      Step ⟨.running ⟨⟨params, localValues,
          .funcref (some functionIndex) :: values⟩,
          .callRef typeIndex :: code, arity, remainder, controls, calls⟩, store⟩
        (.host functionIndex)
        ⟨.running ⟨⟨params, localValues,
            results.take imp.results.length ++ values.drop imp.params.length⟩,
          code, arity, remainder, controls, calls⟩,
          { store with wasm }⟩
  | callRefHostTrap
      (himports : functionIndex < store.runtime.currentModule.imports.length)
      (himport : store.runtime.currentModule.imports[functionIndex] = imp)
      (hhost : store.runtime.currentHost.funcs[functionIndex]? = some hostFunction)
      (hinvoke :
        hostFunction.invoke store.wasm
          (values.take imp.params.length).reverse = .Trap wasm message) :
      Step ⟨.running ⟨⟨params, localValues,
          .funcref (some functionIndex) :: values⟩,
          .callRef typeIndex :: code, arity, remainder, controls, calls⟩, store⟩
        (.host functionIndex)
        ⟨.trapped (.host message), { store with wasm }⟩
  | callRefHostThrow
      (himports : functionIndex < store.runtime.currentModule.imports.length)
      (himport : store.runtime.currentModule.imports[functionIndex] = imp)
      (hhost : store.runtime.currentHost.funcs[functionIndex]? = some hostFunction)
      (hinvoke :
        hostFunction.invoke store.wasm
          (values.take imp.params.length).reverse =
            .Throw wasm tag arguments) :
      Step ⟨.running ⟨⟨params, localValues,
          .funcref (some functionIndex) :: values⟩,
          .callRef typeIndex :: code, arity, remainder, controls, calls⟩, store⟩
        (.host functionIndex)
        ⟨.running
          ⟨⟨params, localValues, values.drop imp.params.length⟩,
            [], arity, remainder,
            { kind := .throwing tag arguments
              paramArity := 0
              resultArity := 0
              body := []
              continuation := []
              belowStack := [] } :: controls,
            calls⟩,
          { store with wasm }⟩
  | callRef
      (himports : ¬functionIndex < store.runtime.currentModule.imports.length)
      (hfn : store.runtime.currentModule.funcs[
        functionIndex - store.runtime.currentModule.imports.length]? = some fn) :
      Step ⟨.running ⟨⟨params, localValues,
          .funcref (some functionIndex) :: values⟩,
          .callRef typeIndex :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.callRef typeIndex))
        ⟨.running
          ⟨fn.toLocals (values.take fn.numParams).reverse,
            fn.body, fn.results.length, [], [],
            { locals := ⟨params, localValues, values.drop fn.numParams⟩
              continuation := code
              resultArity := arity
              callerRemainder := remainder
              control := controls
              returningInstance := store.runtime.entry } :: calls⟩,
          store⟩
  | returnCallRefNull :
      Step ⟨.running ⟨⟨params, localValues, .funcref none :: values⟩,
          .returnCallRef typeIndex :: code,
          arity, remainder, controls, calls⟩, store⟩
        (.instruction (.returnCallRef typeIndex))
        ⟨.trapped .nullFunctionReference, store⟩
  | returnCallRefHostReturn
      (himports : functionIndex < store.runtime.currentModule.imports.length)
      (himport : store.runtime.currentModule.imports[functionIndex] = imp)
      (hhost : store.runtime.currentHost.funcs[functionIndex]? = some hostFunction)
      (hinvoke :
        hostFunction.invoke store.wasm
          (values.take imp.params.length).reverse = .Return results wasm) :
      Step ⟨.running ⟨⟨params, localValues,
          .funcref (some functionIndex) :: values⟩,
          .returnCallRef typeIndex :: code,
          arity, remainder, controls, calls⟩, store⟩
        (.host functionIndex)
        ⟨.running ⟨⟨params, localValues,
            results.take imp.results.length⟩,
          [], arity, remainder, [], calls⟩,
          { store with wasm }⟩
  | returnCallRefHostTrap
      (himports : functionIndex < store.runtime.currentModule.imports.length)
      (himport : store.runtime.currentModule.imports[functionIndex] = imp)
      (hhost : store.runtime.currentHost.funcs[functionIndex]? = some hostFunction)
      (hinvoke :
        hostFunction.invoke store.wasm
          (values.take imp.params.length).reverse = .Trap wasm message) :
      Step ⟨.running ⟨⟨params, localValues,
          .funcref (some functionIndex) :: values⟩,
          .returnCallRef typeIndex :: code,
          arity, remainder, controls, calls⟩, store⟩
        (.host functionIndex)
        ⟨.trapped (.host message), { store with wasm }⟩
  | returnCallRefHostThrow
      (himports : functionIndex < store.runtime.currentModule.imports.length)
      (himport : store.runtime.currentModule.imports[functionIndex] = imp)
      (hhost : store.runtime.currentHost.funcs[functionIndex]? = some hostFunction)
      (hinvoke :
        hostFunction.invoke store.wasm
          (values.take imp.params.length).reverse =
            .Throw wasm tag arguments) :
      Step ⟨.running ⟨⟨params, localValues,
          .funcref (some functionIndex) :: values⟩,
          .returnCallRef typeIndex :: code,
          arity, remainder, controls, calls⟩, store⟩
        (.host functionIndex)
        ⟨.running
          ⟨⟨params, localValues, []⟩,
            [], arity, remainder,
            [{ kind := .throwing tag arguments
               paramArity := 0
               resultArity := 0
               body := []
               continuation := []
               belowStack := [] }],
            calls⟩,
          { store with wasm }⟩
  | returnCallRef
      (himports : ¬functionIndex < store.runtime.currentModule.imports.length)
      (hfn : store.runtime.currentModule.funcs[
        functionIndex - store.runtime.currentModule.imports.length]? = some fn) :
      Step ⟨.running ⟨⟨params, localValues,
          .funcref (some functionIndex) :: values⟩,
          .returnCallRef typeIndex :: code,
          arity, remainder, controls, calls⟩, store⟩
        (.instruction (.returnCallRef typeIndex))
        ⟨.running
          ⟨fn.toLocals (values.take fn.numParams).reverse,
            fn.body, arity, remainder, [], calls⟩,
          store⟩
  | refIsNullTrue
      (h : value.isNullRef? = some true) :
      Step ⟨.running ⟨⟨params, localValues, value :: values⟩,
          .refIsNull :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .refIsNull)
        ⟨.running ⟨⟨params, localValues, .i32 1 :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | refIsNullFalse
      (h : value.isNullRef? = some false) :
      Step ⟨.running ⟨⟨params, localValues, value :: values⟩,
          .refIsNull :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .refIsNull)
        ⟨.running ⟨⟨params, localValues, .i32 0 :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | refAsNonNullTrap
      (h : value.isNullRef? = some true) :
      Step ⟨.running ⟨⟨params, localValues, value :: values⟩,
          .refAsNonNull :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .refAsNonNull)
        ⟨.trapped .nullReference, store⟩
  | refAsNonNull
      (h : value.isNullRef? = some false) :
      Step ⟨.running ⟨⟨params, localValues, value :: values⟩,
          .refAsNonNull :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .refAsNonNull)
        ⟨.running ⟨⟨params, localValues, value :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | brOnNullBranch
      (hnull : value.isNullRef? = some true)
      (htarget : branchTarget? arity depth controls values =
        some (targetCode, targetControl, targetValues)) :
      Step ⟨.running ⟨⟨params, localValues, value :: values⟩,
          .brOnNull depth :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.brOnNull depth))
        ⟨.running ⟨⟨params, localValues, targetValues⟩,
          targetCode, arity, remainder, targetControl, calls⟩, store⟩
  | brOnNullFallthrough
      (hnull : value.isNullRef? = some false) :
      Step ⟨.running ⟨⟨params, localValues, value :: values⟩,
          .brOnNull depth :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.brOnNull depth))
        ⟨.running ⟨⟨params, localValues, value :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | brOnNonNullFallthrough
      (hnull : value.isNullRef? = some true) :
      Step ⟨.running ⟨⟨params, localValues, value :: values⟩,
          .brOnNonNull depth :: code,
          arity, remainder, controls, calls⟩, store⟩
        (.instruction (.brOnNonNull depth))
        ⟨.running ⟨⟨params, localValues, values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | brOnNonNullBranch
      (hnull : value.isNullRef? = some false)
      (htarget : branchTarget? arity depth controls (value :: values) =
        some (targetCode, targetControl, targetValues)) :
      Step ⟨.running ⟨⟨params, localValues, value :: values⟩,
          .brOnNonNull depth :: code,
          arity, remainder, controls, calls⟩, store⟩
        (.instruction (.brOnNonNull depth))
        ⟨.running ⟨⟨params, localValues, targetValues⟩,
          targetCode, arity, remainder, targetControl, calls⟩, store⟩
  | tableGetTrap
      (hindex : index.addrNat? = some elementIndex)
      (htable : store.wasm.tables[tableIndex]? = some table)
      (hbound : ¬elementIndex < table.length) :
      Step ⟨.running ⟨⟨params, localValues, index :: values⟩,
          .tableGet tableIndex :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.tableGet tableIndex))
        ⟨.trapped .outOfBoundsTable, store⟩
  | tableGet
      (hindex : index.addrNat? = some elementIndex)
      (htable : store.wasm.tables[tableIndex]? = some table)
      (helement : table[elementIndex]? = some value) :
      Step ⟨.running ⟨⟨params, localValues, index :: values⟩,
          .tableGet tableIndex :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.tableGet tableIndex))
        ⟨.running ⟨⟨params, localValues, value :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | tableSize
      (htable : store.wasm.tables[tableIndex]? = some table) :
      Step ⟨.running ⟨⟨params, localValues, values⟩,
          .tableSize tableIndex :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.tableSize tableIndex))
        ⟨.running ⟨⟨params, localValues,
            sizeValue (store.runtime.currentModule.tableIs64 tableIndex)
              table.length :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | tableSetTrap
      (hindex : index.addrNat? = some elementIndex)
      (htable : store.wasm.tables[tableIndex]? = some table)
      (hbound : ¬elementIndex < table.length) :
      Step ⟨.running ⟨⟨params, localValues, value :: index :: values⟩,
          .tableSet tableIndex :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.tableSet tableIndex))
        ⟨.trapped .outOfBoundsTable, store⟩
  | tableSet
      (hindex : index.addrNat? = some elementIndex)
      (htable : store.wasm.tables[tableIndex]? = some table)
      (hbound : elementIndex < table.length) :
      Step ⟨.running ⟨⟨params, localValues, value :: index :: values⟩,
          .tableSet tableIndex :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.tableSet tableIndex))
        ⟨.running ⟨⟨params, localValues, values⟩,
          code, arity, remainder, controls, calls⟩,
          setTables store
            (listSetAt store.wasm.tables tableIndex
              (listSetAt table elementIndex value))⟩
  | tableGrow32
      (htable : store.wasm.tables[tableIndex]? = some table)
      (hbound : table.length + delta.toNat ≤
        store.runtime.currentModule.tableCap tableIndex) :
      Step ⟨.running ⟨⟨params, localValues,
          .i32 delta :: initial :: values⟩,
          .tableGrow tableIndex :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.tableGrow tableIndex))
        ⟨.running ⟨⟨params, localValues,
            .i32 table.length.toUInt32 :: values⟩,
          code, arity, remainder, controls, calls⟩,
          setTables store
            (listSetAt store.wasm.tables tableIndex
              (table ++ List.replicate delta.toNat initial))⟩
  | tableGrow32Failure
      (htable : store.wasm.tables[tableIndex]? = some table)
      (hbound : ¬table.length + delta.toNat ≤
        store.runtime.currentModule.tableCap tableIndex) :
      Step ⟨.running ⟨⟨params, localValues,
          .i32 delta :: initial :: values⟩,
          .tableGrow tableIndex :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.tableGrow tableIndex))
        ⟨.running ⟨⟨params, localValues,
            .i32 (0xFFFFFFFF : UInt32) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | tableGrow64
      (htable : store.wasm.tables[tableIndex]? = some table)
      (hbound : table.length + delta.toNat ≤
        store.runtime.currentModule.tableCap tableIndex) :
      Step ⟨.running ⟨⟨params, localValues,
          .i64 delta :: initial :: values⟩,
          .tableGrow tableIndex :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.tableGrow tableIndex))
        ⟨.running ⟨⟨params, localValues,
            .i64 table.length.toUInt64 :: values⟩,
          code, arity, remainder, controls, calls⟩,
          setTables store
            (listSetAt store.wasm.tables tableIndex
              (table ++ List.replicate delta.toNat initial))⟩
  | tableGrow64Failure
      (htable : store.wasm.tables[tableIndex]? = some table)
      (hbound : ¬table.length + delta.toNat ≤
        store.runtime.currentModule.tableCap tableIndex) :
      Step ⟨.running ⟨⟨params, localValues,
          .i64 delta :: initial :: values⟩,
          .tableGrow tableIndex :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.tableGrow tableIndex))
        ⟨.running ⟨⟨params, localValues,
            .i64 (0xFFFFFFFFFFFFFFFF : UInt64) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | tableFillTrap
      (hlength : length.addrNat? = some lengthNat)
      (hdestination : destination.addrNat? = some destinationNat)
      (htable : store.wasm.tables[tableIndex]? = some table)
      (hbound : destinationNat + lengthNat > table.length) :
      Step ⟨.running ⟨⟨params, localValues,
          length :: value :: destination :: values⟩,
          .tableFill tableIndex :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.tableFill tableIndex))
        ⟨.trapped .outOfBoundsTable, store⟩
  | tableFill
      (hlength : length.addrNat? = some lengthNat)
      (hdestination : destination.addrNat? = some destinationNat)
      (htable : store.wasm.tables[tableIndex]? = some table)
      (hbound : destinationNat + lengthNat ≤ table.length) :
      Step ⟨.running ⟨⟨params, localValues,
          length :: value :: destination :: values⟩,
          .tableFill tableIndex :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.tableFill tableIndex))
        ⟨.running ⟨⟨params, localValues, values⟩,
          code, arity, remainder, controls, calls⟩,
          setTables store
            (listSetAt store.wasm.tables tableIndex
              (listWriteAt table destinationNat
                (List.replicate lengthNat value)))⟩
  | tableCopyTrap
      (hlength : length.addrNat? = some lengthNat)
      (hsource : source.addrNat? = some sourceNat)
      (hdestination : destination.addrNat? = some destinationNat)
      (hdestinationTable :
        store.wasm.tables[destinationTableIndex]? = some destinationTable)
      (hsourceTable :
        store.wasm.tables[sourceTableIndex]? = some sourceTable)
      (hbound : destinationNat + lengthNat > destinationTable.length ∨
        sourceNat + lengthNat > sourceTable.length) :
      Step ⟨.running ⟨⟨params, localValues,
          length :: source :: destination :: values⟩,
          .tableCopy destinationTableIndex sourceTableIndex :: code,
          arity, remainder, controls, calls⟩, store⟩
        (.instruction (.tableCopy destinationTableIndex sourceTableIndex))
        ⟨.trapped .outOfBoundsTable, store⟩
  | tableCopy
      (hlength : length.addrNat? = some lengthNat)
      (hsource : source.addrNat? = some sourceNat)
      (hdestination : destination.addrNat? = some destinationNat)
      (hdestinationTable :
        store.wasm.tables[destinationTableIndex]? = some destinationTable)
      (hsourceTable :
        store.wasm.tables[sourceTableIndex]? = some sourceTable)
      (hdestinationBound :
        destinationNat + lengthNat ≤ destinationTable.length)
      (hsourceBound : sourceNat + lengthNat ≤ sourceTable.length) :
      Step ⟨.running ⟨⟨params, localValues,
          length :: source :: destination :: values⟩,
          .tableCopy destinationTableIndex sourceTableIndex :: code,
          arity, remainder, controls, calls⟩, store⟩
        (.instruction (.tableCopy destinationTableIndex sourceTableIndex))
        ⟨.running ⟨⟨params, localValues, values⟩,
          code, arity, remainder, controls, calls⟩,
          setTables store
            (listSetAt store.wasm.tables destinationTableIndex
              (listWriteAt destinationTable destinationNat
                ((sourceTable.drop sourceNat).take lengthNat)))⟩
  | tableInitTrap
      (hdestination : destination.addrNat? = some destinationNat)
      (htable : store.wasm.tables[tableIndex]? = some table)
      (hsegment :
        store.wasm.elementSegments[elementIndex]? = some segmentState)
      (hvalues : segmentValues =
        elementSegmentValues store elementIndex segmentState)
      (hbound : source.toNat + length.toNat > segmentValues.length ∨
        destinationNat + length.toNat > table.length) :
      Step ⟨.running ⟨⟨params, localValues,
          .i32 length :: .i32 source :: destination :: values⟩,
          .tableInit tableIndex elementIndex :: code,
          arity, remainder, controls, calls⟩, store⟩
        (.instruction (.tableInit tableIndex elementIndex))
        ⟨.trapped .outOfBoundsTable, store⟩
  | tableInit
      (hdestination : destination.addrNat? = some destinationNat)
      (htable : store.wasm.tables[tableIndex]? = some table)
      (hsegment :
        store.wasm.elementSegments[elementIndex]? = some segmentState)
      (hvalues : segmentValues =
        elementSegmentValues store elementIndex segmentState)
      (hsourceBound : source.toNat + length.toNat ≤ segmentValues.length)
      (hdestinationBound :
        destinationNat + length.toNat ≤ table.length) :
      Step ⟨.running ⟨⟨params, localValues,
          .i32 length :: .i32 source :: destination :: values⟩,
          .tableInit tableIndex elementIndex :: code,
          arity, remainder, controls, calls⟩, store⟩
        (.instruction (.tableInit tableIndex elementIndex))
        ⟨.running ⟨⟨params, localValues, values⟩,
          code, arity, remainder, controls, calls⟩,
          setTables store
            (listSetAt store.wasm.tables tableIndex
              (listWriteAt table destinationNat
                ((segmentValues.drop source.toNat).take length.toNat)))⟩
  | elemDrop
      (hsegment : store.wasm.elementSegments[elementIndex]?.isSome = true) :
      Step ⟨.running ⟨locals,
          .elemDrop elementIndex :: code,
          arity, remainder, controls, calls⟩, store⟩
        (.instruction (.elemDrop elementIndex))
        ⟨.running ⟨locals, code, arity, remainder, controls, calls⟩,
          setElementSegments store
            (store.wasm.elementSegments.set elementIndex none)⟩
  | scalarFloat0
      (heval : evalScalarFloat0? instruction = some value) :
      Step ⟨.running ⟨⟨params, localValues, values⟩,
          instruction :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction instruction)
        ⟨.running ⟨⟨params, localValues, value :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | scalarFloat1
      (heval : evalScalarFloat0? instruction = none)
      (hresult : evalScalarFloat1? instruction operand = some value) :
      Step ⟨.running ⟨⟨params, localValues, operand :: values⟩,
          instruction :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction instruction)
        ⟨.running ⟨⟨params, localValues, value :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | scalarFloat2
      (heval : evalScalarFloat0? instruction = none)
      (hunary : evalScalarFloat1? instruction rhs = none)
      (hresult : evalScalarFloat2? instruction lhs rhs = some value) :
      Step ⟨.running ⟨⟨params, localValues, rhs :: lhs :: values⟩,
          instruction :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction instruction)
        ⟨.running ⟨⟨params, localValues, value :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | scalarTruncSuccess
      (hresult : evalScalarTrunc? instruction operand = some (.ok value)) :
      Step ⟨.running ⟨⟨params, localValues, operand :: values⟩,
          instruction :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction instruction)
        ⟨.running ⟨⟨params, localValues, value :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | scalarTruncTrap
      (hresult : evalScalarTrunc? instruction operand = some (.error reason)) :
      Step ⟨.running ⟨⟨params, localValues, operand :: values⟩,
          instruction :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction instruction) ⟨.trapped reason, store⟩
  | vConst :
      Step ⟨.running ⟨⟨params, localValues, values⟩,
          .vConst bits :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.vConst bits))
        ⟨.running ⟨⟨params, localValues, .v128 bits :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | vUnOp :
      Step ⟨.running ⟨⟨params, localValues, .v128 value :: values⟩,
          .vUnOp op :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.vUnOp op))
        ⟨.running ⟨⟨params, localValues, .v128 (op.eval value) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | vBinOp :
      Step ⟨.running ⟨⟨params, localValues,
          .v128 rhs :: .v128 lhs :: values⟩,
          .vBinOp op :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.vBinOp op))
        ⟨.running ⟨⟨params, localValues,
          .v128 (op.eval lhs rhs) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | vBitselect :
      Step ⟨.running ⟨⟨params, localValues,
          .v128 mask :: .v128 rhs :: .v128 lhs :: values⟩,
          .vBitselect :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .vBitselect)
        ⟨.running ⟨⟨params, localValues,
          .v128 ((lhs &&& mask) ||| (rhs &&& ~~~mask)) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | vTestOp :
      Step ⟨.running ⟨⟨params, localValues, .v128 value :: values⟩,
          .vTestOp op :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.vTestOp op))
        ⟨.running ⟨⟨params, localValues, .i32 (op.eval value) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | vShiftOp :
      Step ⟨.running ⟨⟨params, localValues,
          .i32 amount :: .v128 value :: values⟩,
          .vShiftOp op :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.vShiftOp op))
        ⟨.running ⟨⟨params, localValues,
          .v128 (op.eval value amount) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | vSplat
      (hbits : value.scalarBitsFor? shape = some bits) :
      Step ⟨.running ⟨⟨params, localValues, value :: values⟩,
          .vSplat shape :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.vSplat shape))
        ⟨.running ⟨⟨params, localValues,
          .v128 (Simd.splat shape bits) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | vExtractLane :
      Step ⟨.running ⟨⟨params, localValues, .v128 value :: values⟩,
          .vExtractLane shape signed lane :: code,
          arity, remainder, controls, calls⟩, store⟩
        (.instruction (.vExtractLane shape signed lane))
        ⟨.running ⟨⟨params, localValues,
          simdExtractLane shape signed lane value :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | vReplaceLane
      (hbits : replacement.scalarBitsFor? shape = some bits) :
      Step ⟨.running ⟨⟨params, localValues,
          replacement :: .v128 value :: values⟩,
          .vReplaceLane shape lane :: code,
          arity, remainder, controls, calls⟩, store⟩
        (.instruction (.vReplaceLane shape lane))
        ⟨.running ⟨⟨params, localValues,
          .v128 (Simd.setLane shape.laneBits lane value bits) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | vShuffle :
      Step ⟨.running ⟨⟨params, localValues,
          .v128 rhs :: .v128 lhs :: values⟩,
          .vShuffle indices :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.vShuffle indices))
        ⟨.running ⟨⟨params, localValues,
          .v128 (Simd.shuffle indices lhs rhs) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | vFma :
      Step ⟨.running ⟨⟨params, localValues,
          .v128 addend :: .v128 rhs :: .v128 lhs :: values⟩,
          .vFma shape neg :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.vFma shape neg))
        ⟨.running ⟨⟨params, localValues,
          .v128 (Simd.fma shape neg lhs rhs addend) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | vDotAdd :
      Step ⟨.running ⟨⟨params, localValues,
          .v128 addend :: .v128 rhs :: .v128 lhs :: values⟩,
          .vDotAdd :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .vDotAdd)
        ⟨.running ⟨⟨params, localValues,
          .v128 (Simd.dotAdd lhs rhs addend) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | v128LoadTrap
      (haddress : memoryAddress? address = some (logicalAddress, physicalAddress))
      (hbound :
        logicalAddress + offset.toNat + 16 > store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues, address :: values⟩,
          .v128Load offset :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.v128Load offset))
        ⟨.trapped .outOfBoundsMemory, store⟩
  | v128Load
      (haddress : memoryAddress? address = some (logicalAddress, physicalAddress))
      (hbound :
        logicalAddress + offset.toNat + 16 ≤ store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues, address :: values⟩,
          .v128Load offset :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.v128Load offset))
        ⟨.running ⟨⟨params, localValues,
          .v128 (readV128 store.wasm.mem (physicalAddress + offset)) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | v128StoreTrap
      (haddress : memoryAddress? address = some (logicalAddress, physicalAddress))
      (hbound :
        logicalAddress + offset.toNat + 16 > store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues,
          .v128 value :: address :: values⟩,
          .v128Store offset :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.v128Store offset))
        ⟨.trapped .outOfBoundsMemory, store⟩
  | v128Store
      (haddress : memoryAddress? address = some (logicalAddress, physicalAddress))
      (hbound :
        logicalAddress + offset.toNat + 16 ≤ store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues,
          .v128 value :: address :: values⟩,
          .v128Store offset :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.v128Store offset))
        ⟨.running ⟨⟨params, localValues, values⟩,
          code, arity, remainder, controls, calls⟩,
          setMemory store
            (writeV128 store.wasm.mem (physicalAddress + offset) value)⟩
  | v128LoadExtTrap
      (haddress : memoryAddress? address = some (logicalAddress, physicalAddress))
      (hbound :
        logicalAddress + offset.toNat + 8 > store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues, address :: values⟩,
          .v128LoadExt srcBits signed offset :: code,
          arity, remainder, controls, calls⟩, store⟩
        (.instruction (.v128LoadExt srcBits signed offset))
        ⟨.trapped .outOfBoundsMemory, store⟩
  | v128LoadExt
      (haddress : memoryAddress? address = some (logicalAddress, physicalAddress))
      (hbound :
        logicalAddress + offset.toNat + 8 ≤ store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues, address :: values⟩,
          .v128LoadExt srcBits signed offset :: code,
          arity, remainder, controls, calls⟩, store⟩
        (.instruction (.v128LoadExt srcBits signed offset))
        ⟨.running ⟨⟨params, localValues,
          .v128 (loadV128Ext store.wasm.mem (physicalAddress + offset)
            srcBits signed) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | v128LoadSplatTrap
      (haddress : memoryAddress? address = some (logicalAddress, physicalAddress))
      (hbound :
        logicalAddress + offset.toNat + bits / 8 >
          store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues, address :: values⟩,
          .v128LoadSplat bits offset :: code,
          arity, remainder, controls, calls⟩, store⟩
        (.instruction (.v128LoadSplat bits offset))
        ⟨.trapped .outOfBoundsMemory, store⟩
  | v128LoadSplat
      (haddress : memoryAddress? address = some (logicalAddress, physicalAddress))
      (hbound :
        logicalAddress + offset.toNat + bits / 8 ≤
          store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues, address :: values⟩,
          .v128LoadSplat bits offset :: code,
          arity, remainder, controls, calls⟩, store⟩
        (.instruction (.v128LoadSplat bits offset))
        ⟨.running ⟨⟨params, localValues,
          .v128 (Simd.ofLanes bits
            (List.replicate (128 / bits)
              (readLaneNat store.wasm.mem (physicalAddress + offset) bits))) ::
            values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | v128LoadZeroTrap
      (haddress : memoryAddress? address = some (logicalAddress, physicalAddress))
      (hbound :
        logicalAddress + offset.toNat + bits / 8 >
          store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues, address :: values⟩,
          .v128LoadZero bits offset :: code,
          arity, remainder, controls, calls⟩, store⟩
        (.instruction (.v128LoadZero bits offset))
        ⟨.trapped .outOfBoundsMemory, store⟩
  | v128LoadZero
      (haddress : memoryAddress? address = some (logicalAddress, physicalAddress))
      (hbound :
        logicalAddress + offset.toNat + bits / 8 ≤
          store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues, address :: values⟩,
          .v128LoadZero bits offset :: code,
          arity, remainder, controls, calls⟩, store⟩
        (.instruction (.v128LoadZero bits offset))
        ⟨.running ⟨⟨params, localValues,
          .v128 (BitVec.ofNat 128
            (readLaneNat store.wasm.mem (physicalAddress + offset) bits)) ::
            values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | v128LoadLaneTrap
      (haddress : memoryAddress? address = some (logicalAddress, physicalAddress))
      (hbound :
        logicalAddress + offset.toNat + bits / 8 >
          store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues,
          .v128 vector :: address :: values⟩,
          .v128LoadLane bits lane offset :: code,
          arity, remainder, controls, calls⟩, store⟩
        (.instruction (.v128LoadLane bits lane offset))
        ⟨.trapped .outOfBoundsMemory, store⟩
  | v128LoadLane
      (haddress : memoryAddress? address = some (logicalAddress, physicalAddress))
      (hbound :
        logicalAddress + offset.toNat + bits / 8 ≤
          store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues,
          .v128 vector :: address :: values⟩,
          .v128LoadLane bits lane offset :: code,
          arity, remainder, controls, calls⟩, store⟩
        (.instruction (.v128LoadLane bits lane offset))
        ⟨.running ⟨⟨params, localValues,
          .v128 (Simd.setLane bits lane vector
            (readLaneNat store.wasm.mem (physicalAddress + offset) bits)) ::
            values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | v128StoreLaneTrap
      (haddress : memoryAddress? address = some (logicalAddress, physicalAddress))
      (hbound :
        logicalAddress + offset.toNat + bits / 8 >
          store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues,
          .v128 vector :: address :: values⟩,
          .v128StoreLane bits lane offset :: code,
          arity, remainder, controls, calls⟩, store⟩
        (.instruction (.v128StoreLane bits lane offset))
        ⟨.trapped .outOfBoundsMemory, store⟩
  | v128StoreLane
      (haddress : memoryAddress? address = some (logicalAddress, physicalAddress))
      (hbound :
        logicalAddress + offset.toNat + bits / 8 ≤
          store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues,
          .v128 vector :: address :: values⟩,
          .v128StoreLane bits lane offset :: code,
          arity, remainder, controls, calls⟩, store⟩
        (.instruction (.v128StoreLane bits lane offset))
        ⟨.running ⟨⟨params, localValues, values⟩,
          code, arity, remainder, controls, calls⟩,
          setMemory store
            (writeLaneNat store.wasm.mem (physicalAddress + offset) bits
              (Simd.getLane bits lane vector))⟩
  | unreachable :
      Step ⟨.running ⟨locals, .unreachable :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .unreachable) ⟨.trapped .unreachable, store⟩
  | nop :
      Step ⟨.running ⟨locals, .nop :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .nop)
        ⟨.running ⟨locals, code, arity, remainder, controls, calls⟩, store⟩
  | drop :
      Step ⟨.running
          ⟨⟨params, localValues, value :: values⟩,
            .drop :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .drop)
        ⟨.running
          ⟨⟨params, localValues, values⟩,
            code, arity, remainder, controls, calls⟩, store⟩
  | select
      (h : selected = if condition ≠ 0 then first else second) :
      Step ⟨.running
          ⟨⟨params, localValues, .i32 condition :: second :: first :: values⟩,
            .select :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .select)
        ⟨.running
          ⟨⟨params, localValues, selected :: values⟩,
            code, arity, remainder, controls, calls⟩, store⟩
  | const :
      Step ⟨.running ⟨⟨params, localValues, values⟩,
          .const value :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.const value))
        ⟨.running ⟨⟨params, localValues, .i32 value :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | constI64 :
      Step ⟨.running ⟨⟨params, localValues, values⟩,
          .constI64 value :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.constI64 value))
        ⟨.running ⟨⟨params, localValues, .i64 value :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | localGet (h : (⟨params, localValues, values⟩ : Locals).get index = some value) :
      Step ⟨.running ⟨⟨params, localValues, values⟩,
          .localGet index :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.localGet index))
        ⟨.running ⟨⟨params, localValues, value :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | localSet {locals' : Locals} {index : Nat} {value : Value}
      (h : (⟨params, localValues, value :: values⟩ : Locals).set? index value =
        some locals') :
      Step ⟨.running ⟨⟨params, localValues, value :: values⟩,
          .localSet index :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.localSet index))
        ⟨.running ⟨{ locals' with values := values }, code, arity, remainder, controls, calls⟩, store⟩
  | globalGet {store : MachineStore α} {index : Nat} {value : Value}
      (h : globalAt? store index = some value) :
      Step ⟨.running ⟨⟨params, localValues, values⟩,
          .globalGet index :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.globalGet index))
        ⟨.running ⟨⟨params, localValues, value :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | globalSet {store : MachineStore α} {index : Nat} {value : Value}
      (h : (globalAt? store index).isSome = true) :
      Step ⟨.running ⟨⟨params, localValues, value :: values⟩,
          .globalSet index :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.globalSet index))
        ⟨.running ⟨⟨params, localValues, values⟩, code, arity, remainder, controls, calls⟩,
          setGlobal store index value⟩
  | add :
      Step ⟨.running ⟨⟨params, localValues, .i32 a :: .i32 b :: values⟩,
          .add :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .add)
        ⟨.running ⟨⟨params, localValues, .i32 (a + b) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | sub :
      Step ⟨.running ⟨⟨params, localValues, .i32 a :: .i32 b :: values⟩,
          .sub :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .sub)
        ⟨.running ⟨⟨params, localValues, .i32 (b - a) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | mul :
      Step ⟨.running ⟨⟨params, localValues, .i32 a :: .i32 b :: values⟩,
          .mul :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .mul)
        ⟨.running ⟨⟨params, localValues, .i32 (a * b) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | and :
      Step ⟨.running ⟨⟨params, localValues, .i32 rhs :: .i32 lhs :: values⟩,
          .and :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .and)
        ⟨.running ⟨⟨params, localValues, .i32 (lhs &&& rhs) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | or :
      Step ⟨.running ⟨⟨params, localValues, .i32 rhs :: .i32 lhs :: values⟩,
          .or :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .or)
        ⟨.running ⟨⟨params, localValues, .i32 (lhs ||| rhs) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | xor :
      Step ⟨.running ⟨⟨params, localValues, .i32 rhs :: .i32 lhs :: values⟩,
          .xor :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .xor)
        ⟨.running ⟨⟨params, localValues, .i32 (lhs ^^^ rhs) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | shl :
      Step ⟨.running ⟨⟨params, localValues, .i32 rhs :: .i32 lhs :: values⟩,
          .shl :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .shl)
        ⟨.running ⟨⟨params, localValues, .i32 (lhs <<< (rhs % 32)) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | shrU :
      Step ⟨.running ⟨⟨params, localValues, .i32 rhs :: .i32 lhs :: values⟩,
          .shrU :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .shrU)
        ⟨.running ⟨⟨params, localValues, .i32 (lhs >>> (rhs % 32)) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | shrS :
      Step ⟨.running ⟨⟨params, localValues, .i32 rhs :: .i32 lhs :: values⟩,
          .shrS :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .shrS)
        ⟨.running ⟨⟨params, localValues,
          .i32 (UInt32.ofNat
            (BitVec.sshiftRight lhs.toBitVec (rhs % 32).toNat).toNat) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | rotl :
      Step ⟨.running ⟨⟨params, localValues, .i32 rhs :: .i32 lhs :: values⟩,
          .rotl :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .rotl)
        ⟨.running ⟨⟨params, localValues,
          .i32 (rotateLeft32 lhs rhs) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | rotr :
      Step ⟨.running ⟨⟨params, localValues, .i32 rhs :: .i32 lhs :: values⟩,
          .rotr :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .rotr)
        ⟨.running ⟨⟨params, localValues,
          .i32 (rotateRight32 lhs rhs) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | clz :
      Step ⟨.running ⟨⟨params, localValues, .i32 value :: values⟩,
          .clz :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .clz)
        ⟨.running ⟨⟨params, localValues,
          .i32 (UInt32.ofNat (clz32 32 value)) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | ctz :
      Step ⟨.running ⟨⟨params, localValues, .i32 value :: values⟩,
          .ctz :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .ctz)
        ⟨.running ⟨⟨params, localValues,
          .i32 (UInt32.ofNat (ctz32 32 value)) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | popcnt :
      Step ⟨.running ⟨⟨params, localValues, .i32 value :: values⟩,
          .popcnt :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .popcnt)
        ⟨.running ⟨⟨params, localValues,
          .i32 (UInt32.ofNat (popcnt32 32 value 0)) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | addI64 :
      Step ⟨.running
          ⟨⟨params, localValues, .i64 rhs :: .i64 lhs :: values⟩,
            .addI64 :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .addI64)
        ⟨.running
          ⟨⟨params, localValues, .i64 (lhs + rhs) :: values⟩,
            code, arity, remainder, controls, calls⟩, store⟩
  | subI64 :
      Step ⟨.running
          ⟨⟨params, localValues, .i64 rhs :: .i64 lhs :: values⟩,
            .subI64 :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .subI64)
        ⟨.running
          ⟨⟨params, localValues, .i64 (lhs - rhs) :: values⟩,
            code, arity, remainder, controls, calls⟩, store⟩
  | mulI64 :
      Step ⟨.running
          ⟨⟨params, localValues, .i64 rhs :: .i64 lhs :: values⟩,
            .mulI64 :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .mulI64)
        ⟨.running
          ⟨⟨params, localValues, .i64 (lhs * rhs) :: values⟩,
            code, arity, remainder, controls, calls⟩, store⟩
  | andI64 :
      Step ⟨.running ⟨⟨params, localValues, .i64 rhs :: .i64 lhs :: values⟩,
          .andI64 :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .andI64)
        ⟨.running ⟨⟨params, localValues, .i64 (lhs &&& rhs) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | orI64 :
      Step ⟨.running ⟨⟨params, localValues, .i64 rhs :: .i64 lhs :: values⟩,
          .orI64 :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .orI64)
        ⟨.running ⟨⟨params, localValues, .i64 (lhs ||| rhs) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | xorI64 :
      Step ⟨.running ⟨⟨params, localValues, .i64 rhs :: .i64 lhs :: values⟩,
          .xorI64 :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .xorI64)
        ⟨.running ⟨⟨params, localValues, .i64 (lhs ^^^ rhs) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | shlI64 :
      Step ⟨.running ⟨⟨params, localValues, .i64 rhs :: .i64 lhs :: values⟩,
          .shlI64 :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .shlI64)
        ⟨.running ⟨⟨params, localValues, .i64 (lhs <<< (rhs % 64)) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | shrUI64 :
      Step ⟨.running ⟨⟨params, localValues, .i64 rhs :: .i64 lhs :: values⟩,
          .shrUI64 :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .shrUI64)
        ⟨.running ⟨⟨params, localValues, .i64 (lhs >>> (rhs % 64)) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | shrSI64 :
      Step ⟨.running ⟨⟨params, localValues, .i64 rhs :: .i64 lhs :: values⟩,
          .shrSI64 :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .shrSI64)
        ⟨.running ⟨⟨params, localValues,
          .i64 (UInt64.ofNat
            (BitVec.sshiftRight lhs.toBitVec (rhs % 64).toNat).toNat) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | rotlI64 :
      Step ⟨.running ⟨⟨params, localValues, .i64 rhs :: .i64 lhs :: values⟩,
          .rotlI64 :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .rotlI64)
        ⟨.running ⟨⟨params, localValues,
          .i64 (rotateLeft64 lhs rhs) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | rotrI64 :
      Step ⟨.running ⟨⟨params, localValues, .i64 rhs :: .i64 lhs :: values⟩,
          .rotrI64 :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .rotrI64)
        ⟨.running ⟨⟨params, localValues,
          .i64 (rotateRight64 lhs rhs) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | clzI64 :
      Step ⟨.running ⟨⟨params, localValues, .i64 value :: values⟩,
          .clzI64 :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .clzI64)
        ⟨.running ⟨⟨params, localValues,
          .i64 (UInt64.ofNat (clz64 64 value)) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | ctzI64 :
      Step ⟨.running ⟨⟨params, localValues, .i64 value :: values⟩,
          .ctzI64 :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .ctzI64)
        ⟨.running ⟨⟨params, localValues,
          .i64 (UInt64.ofNat (ctz64 64 value)) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | popcntI64 :
      Step ⟨.running ⟨⟨params, localValues, .i64 value :: values⟩,
          .popcntI64 :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .popcntI64)
        ⟨.running ⟨⟨params, localValues,
          .i64 (UInt64.ofNat (popcnt64 64 value 0)) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | divUZero :
      Step ⟨.running ⟨⟨params, localValues, .i32 0 :: .i32 dividend :: values⟩,
          .divU :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .divU) ⟨.trapped .integerDivideByZero, store⟩
  | divU {divisor : UInt32} (h : divisor ≠ 0) :
      Step ⟨.running ⟨⟨params, localValues, .i32 divisor :: .i32 dividend :: values⟩,
          .divU :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .divU)
        ⟨.running ⟨⟨params, localValues, .i32 (dividend / divisor) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | divSZero :
      Step ⟨.running ⟨⟨params, localValues, .i32 0 :: .i32 dividend :: values⟩,
          .divS :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .divS) ⟨.trapped .integerDivideByZero, store⟩
  | divSOverflow :
      Step ⟨.running
          ⟨⟨params, localValues, .i32 0xFFFFFFFF :: .i32 0x80000000 :: values⟩,
            .divS :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .divS) ⟨.trapped .integerOverflow, store⟩
  | divS {divisor : UInt32}
      (hzero : divisor ≠ 0)
      (hoverflow : divisor = 0xFFFFFFFF → dividend ≠ 0x80000000) :
      Step ⟨.running ⟨⟨params, localValues, .i32 divisor :: .i32 dividend :: values⟩,
          .divS :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .divS)
        ⟨.running ⟨⟨params, localValues,
          .i32 (signedDiv32 dividend divisor) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | remUZero :
      Step ⟨.running ⟨⟨params, localValues, .i32 0 :: .i32 dividend :: values⟩,
          .remU :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .remU) ⟨.trapped .integerDivideByZero, store⟩
  | remU {divisor : UInt32} (h : divisor ≠ 0) :
      Step ⟨.running ⟨⟨params, localValues, .i32 divisor :: .i32 dividend :: values⟩,
          .remU :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .remU)
        ⟨.running ⟨⟨params, localValues, .i32 (dividend % divisor) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | remSZero :
      Step ⟨.running ⟨⟨params, localValues, .i32 0 :: .i32 dividend :: values⟩,
          .remS :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .remS) ⟨.trapped .integerDivideByZero, store⟩
  | remS {divisor : UInt32} (h : divisor ≠ 0) :
      Step ⟨.running ⟨⟨params, localValues, .i32 divisor :: .i32 dividend :: values⟩,
          .remS :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .remS)
        ⟨.running ⟨⟨params, localValues,
          .i32 (signedRem32 dividend divisor) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | divUI64Zero :
      Step ⟨.running ⟨⟨params, localValues, .i64 0 :: .i64 dividend :: values⟩,
          .divUI64 :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .divUI64) ⟨.trapped .integerDivideByZero, store⟩
  | divUI64 {divisor : UInt64} (h : divisor ≠ 0) :
      Step ⟨.running ⟨⟨params, localValues, .i64 divisor :: .i64 dividend :: values⟩,
          .divUI64 :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .divUI64)
        ⟨.running ⟨⟨params, localValues, .i64 (dividend / divisor) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | divSI64Zero :
      Step ⟨.running ⟨⟨params, localValues, .i64 0 :: .i64 dividend :: values⟩,
          .divSI64 :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .divSI64) ⟨.trapped .integerDivideByZero, store⟩
  | divSI64Overflow :
      Step ⟨.running
          ⟨⟨params, localValues,
            .i64 0xFFFFFFFFFFFFFFFF :: .i64 0x8000000000000000 :: values⟩,
            .divSI64 :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .divSI64) ⟨.trapped .integerOverflow, store⟩
  | divSI64 {divisor : UInt64}
      (hzero : divisor ≠ 0)
      (hoverflow :
        divisor = 0xFFFFFFFFFFFFFFFF → dividend ≠ 0x8000000000000000) :
      Step ⟨.running ⟨⟨params, localValues, .i64 divisor :: .i64 dividend :: values⟩,
          .divSI64 :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .divSI64)
        ⟨.running ⟨⟨params, localValues,
          .i64 (signedDiv64 dividend divisor) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | remUI64Zero :
      Step ⟨.running ⟨⟨params, localValues, .i64 0 :: .i64 dividend :: values⟩,
          .remUI64 :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .remUI64) ⟨.trapped .integerDivideByZero, store⟩
  | remUI64 {divisor : UInt64} (h : divisor ≠ 0) :
      Step ⟨.running ⟨⟨params, localValues, .i64 divisor :: .i64 dividend :: values⟩,
          .remUI64 :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .remUI64)
        ⟨.running ⟨⟨params, localValues, .i64 (dividend % divisor) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | remSI64Zero :
      Step ⟨.running ⟨⟨params, localValues, .i64 0 :: .i64 dividend :: values⟩,
          .remSI64 :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .remSI64) ⟨.trapped .integerDivideByZero, store⟩
  | remSI64 {divisor : UInt64} (h : divisor ≠ 0) :
      Step ⟨.running ⟨⟨params, localValues, .i64 divisor :: .i64 dividend :: values⟩,
          .remSI64 :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .remSI64)
        ⟨.running ⟨⟨params, localValues,
          .i64 (signedRem64 dividend divisor) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | eqz (h : result = if value = 0 then 1 else 0) :
      Step ⟨.running ⟨⟨params, localValues, .i32 value :: values⟩,
          .eqz :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .eqz)
        ⟨.running ⟨⟨params, localValues,
          .i32 result :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | eq (h : result = if lhs = rhs then 1 else 0) :
      Step ⟨.running ⟨⟨params, localValues, .i32 rhs :: .i32 lhs :: values⟩,
          .eq :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .eq)
        ⟨.running ⟨⟨params, localValues,
          .i32 result :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | ne (h : result = if lhs ≠ rhs then 1 else 0) :
      Step ⟨.running ⟨⟨params, localValues, .i32 rhs :: .i32 lhs :: values⟩,
          .ne :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .ne)
        ⟨.running ⟨⟨params, localValues,
          .i32 result :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | ltU (h : result = if lhs < rhs then 1 else 0) :
      Step ⟨.running ⟨⟨params, localValues, .i32 rhs :: .i32 lhs :: values⟩,
          .ltU :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .ltU)
        ⟨.running ⟨⟨params, localValues,
          .i32 result :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | gtU (h : result = if lhs > rhs then 1 else 0) :
      Step ⟨.running ⟨⟨params, localValues, .i32 rhs :: .i32 lhs :: values⟩,
          .gtU :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .gtU)
        ⟨.running ⟨⟨params, localValues,
          .i32 result :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | leU (h : result = if lhs ≤ rhs then 1 else 0) :
      Step ⟨.running ⟨⟨params, localValues, .i32 rhs :: .i32 lhs :: values⟩,
          .leU :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .leU)
        ⟨.running ⟨⟨params, localValues,
          .i32 result :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | geU (h : result = if lhs ≥ rhs then 1 else 0) :
      Step ⟨.running ⟨⟨params, localValues, .i32 rhs :: .i32 lhs :: values⟩,
          .geU :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .geU)
        ⟨.running ⟨⟨params, localValues,
          .i32 result :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | ltS (h : result = if lhs.toInt32 < rhs.toInt32 then 1 else 0) :
      Step ⟨.running ⟨⟨params, localValues, .i32 rhs :: .i32 lhs :: values⟩,
          .ltS :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .ltS)
        ⟨.running ⟨⟨params, localValues, .i32 result :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | gtS (h : result = if lhs.toInt32 > rhs.toInt32 then 1 else 0) :
      Step ⟨.running ⟨⟨params, localValues, .i32 rhs :: .i32 lhs :: values⟩,
          .gtS :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .gtS)
        ⟨.running ⟨⟨params, localValues, .i32 result :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | leS (h : result = if lhs.toInt32 ≤ rhs.toInt32 then 1 else 0) :
      Step ⟨.running ⟨⟨params, localValues, .i32 rhs :: .i32 lhs :: values⟩,
          .leS :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .leS)
        ⟨.running ⟨⟨params, localValues, .i32 result :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | geS (h : result = if lhs.toInt32 ≥ rhs.toInt32 then 1 else 0) :
      Step ⟨.running ⟨⟨params, localValues, .i32 rhs :: .i32 lhs :: values⟩,
          .geS :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .geS)
        ⟨.running ⟨⟨params, localValues, .i32 result :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | eqzI64 (h : result = if value = 0 then 1 else 0) :
      Step ⟨.running ⟨⟨params, localValues, .i64 value :: values⟩,
          .eqzI64 :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .eqzI64)
        ⟨.running ⟨⟨params, localValues, .i32 result :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | eqI64 (h : result = if lhs = rhs then 1 else 0) :
      Step ⟨.running ⟨⟨params, localValues, .i64 rhs :: .i64 lhs :: values⟩,
          .eqI64 :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .eqI64)
        ⟨.running ⟨⟨params, localValues, .i32 result :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | neI64 (h : result = if lhs ≠ rhs then 1 else 0) :
      Step ⟨.running ⟨⟨params, localValues, .i64 rhs :: .i64 lhs :: values⟩,
          .neI64 :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .neI64)
        ⟨.running ⟨⟨params, localValues, .i32 result :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | ltUI64 (h : result = if lhs < rhs then 1 else 0) :
      Step ⟨.running ⟨⟨params, localValues, .i64 rhs :: .i64 lhs :: values⟩,
          .ltUI64 :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .ltUI64)
        ⟨.running ⟨⟨params, localValues, .i32 result :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | ltSI64 (h : result = if lhs.toInt64 < rhs.toInt64 then 1 else 0) :
      Step ⟨.running ⟨⟨params, localValues, .i64 rhs :: .i64 lhs :: values⟩,
          .ltSI64 :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .ltSI64)
        ⟨.running ⟨⟨params, localValues, .i32 result :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | gtUI64 (h : result = if lhs > rhs then 1 else 0) :
      Step ⟨.running ⟨⟨params, localValues, .i64 rhs :: .i64 lhs :: values⟩,
          .gtUI64 :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .gtUI64)
        ⟨.running ⟨⟨params, localValues, .i32 result :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | gtSI64 (h : result = if lhs.toInt64 > rhs.toInt64 then 1 else 0) :
      Step ⟨.running ⟨⟨params, localValues, .i64 rhs :: .i64 lhs :: values⟩,
          .gtSI64 :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .gtSI64)
        ⟨.running ⟨⟨params, localValues, .i32 result :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | leUI64 (h : result = if lhs ≤ rhs then 1 else 0) :
      Step ⟨.running ⟨⟨params, localValues, .i64 rhs :: .i64 lhs :: values⟩,
          .leUI64 :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .leUI64)
        ⟨.running ⟨⟨params, localValues, .i32 result :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | leSI64 (h : result = if lhs.toInt64 ≤ rhs.toInt64 then 1 else 0) :
      Step ⟨.running ⟨⟨params, localValues, .i64 rhs :: .i64 lhs :: values⟩,
          .leSI64 :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .leSI64)
        ⟨.running ⟨⟨params, localValues, .i32 result :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | geUI64 (h : result = if lhs ≥ rhs then 1 else 0) :
      Step ⟨.running ⟨⟨params, localValues, .i64 rhs :: .i64 lhs :: values⟩,
          .geUI64 :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .geUI64)
        ⟨.running ⟨⟨params, localValues, .i32 result :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | geSI64 (h : result = if lhs.toInt64 ≥ rhs.toInt64 then 1 else 0) :
      Step ⟨.running ⟨⟨params, localValues, .i64 rhs :: .i64 lhs :: values⟩,
          .geSI64 :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .geSI64)
        ⟨.running ⟨⟨params, localValues, .i32 result :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | wrapI64 :
      Step ⟨.running ⟨⟨params, localValues, .i64 value :: values⟩,
          .wrapI64 :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .wrapI64)
        ⟨.running ⟨⟨params, localValues, .i32 (wrap64To32 value) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | extendUI32 :
      Step ⟨.running ⟨⟨params, localValues, .i32 value :: values⟩,
          .extendUI32 :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .extendUI32)
        ⟨.running ⟨⟨params, localValues,
          .i64 (extendUnsigned32To64 value) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | extendSI32 :
      Step ⟨.running ⟨⟨params, localValues, .i32 value :: values⟩,
          .extendSI32 :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .extendSI32)
        ⟨.running ⟨⟨params, localValues,
          .i64 (extendSigned32To64 value) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | extend8S :
      Step ⟨.running ⟨⟨params, localValues, .i32 value :: values⟩,
          .extend8S :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .extend8S)
        ⟨.running ⟨⟨params, localValues, .i32 (extend8To32 value) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | extend16S :
      Step ⟨.running ⟨⟨params, localValues, .i32 value :: values⟩,
          .extend16S :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .extend16S)
        ⟨.running ⟨⟨params, localValues, .i32 (extend16To32 value) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | extend8SI64 :
      Step ⟨.running ⟨⟨params, localValues, .i64 value :: values⟩,
          .extend8SI64 :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .extend8SI64)
        ⟨.running ⟨⟨params, localValues, .i64 (extend8To64 value) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | extend16SI64 :
      Step ⟨.running ⟨⟨params, localValues, .i64 value :: values⟩,
          .extend16SI64 :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .extend16SI64)
        ⟨.running ⟨⟨params, localValues, .i64 (extend16To64 value) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | extend32SI64 :
      Step ⟨.running ⟨⟨params, localValues, .i64 value :: values⟩,
          .extend32SI64 :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .extend32SI64)
        ⟨.running ⟨⟨params, localValues, .i64 (extend32To64 value) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | load8UTrap
      (h : address.toNat + offset.toNat + 1 > store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues, .i32 address :: values⟩,
          .load8U offset :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.load8U offset)) ⟨.trapped .outOfBoundsMemory, store⟩
  | load8U
      (h : address.toNat + offset.toNat + 1 ≤ store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues, .i32 address :: values⟩,
          .load8U offset :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.load8U offset))
        ⟨.running ⟨⟨params, localValues,
          .i32 (store.wasm.mem.read8 (address + offset)).toUInt32 :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | load8STrap
      (h : address.toNat + offset.toNat + 1 > store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues, .i32 address :: values⟩,
          .load8S offset :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.load8S offset)) ⟨.trapped .outOfBoundsMemory, store⟩
  | load8S
      (h : address.toNat + offset.toNat + 1 ≤ store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues, .i32 address :: values⟩,
          .load8S offset :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.load8S offset))
        ⟨.running ⟨⟨params, localValues,
          .i32 (extend8To32
            (store.wasm.mem.read8 (address + offset)).toUInt32) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | load16UTrap
      (h : address.toNat + offset.toNat + 2 > store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues, .i32 address :: values⟩,
          .load16U offset :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.load16U offset)) ⟨.trapped .outOfBoundsMemory, store⟩
  | load16U
      (h : address.toNat + offset.toNat + 2 ≤ store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues, .i32 address :: values⟩,
          .load16U offset :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.load16U offset))
        ⟨.running ⟨⟨params, localValues,
          .i32 (store.wasm.mem.read16 (address + offset)) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | load16STrap
      (h : address.toNat + offset.toNat + 2 > store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues, .i32 address :: values⟩,
          .load16S offset :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.load16S offset)) ⟨.trapped .outOfBoundsMemory, store⟩
  | load16S
      (h : address.toNat + offset.toNat + 2 ≤ store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues, .i32 address :: values⟩,
          .load16S offset :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.load16S offset))
        ⟨.running ⟨⟨params, localValues,
          .i32 (extend16To32
            (store.wasm.mem.read16 (address + offset))) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | store8Trap
      (h : address.toNat + offset.toNat + 1 > store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues,
          .i32 value :: .i32 address :: values⟩,
          .store8 offset :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.store8 offset)) ⟨.trapped .outOfBoundsMemory, store⟩
  | store8
      (h : address.toNat + offset.toNat + 1 ≤ store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues,
          .i32 value :: .i32 address :: values⟩,
          .store8 offset :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.store8 offset))
        ⟨.running ⟨⟨params, localValues, values⟩, code, arity, remainder, controls, calls⟩,
          setMemory store
            (store.wasm.mem.write8 (address + offset) value.toUInt8)⟩
  | store16Trap
      (h : address.toNat + offset.toNat + 2 > store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues,
          .i32 value :: .i32 address :: values⟩,
          .store16 offset :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.store16 offset)) ⟨.trapped .outOfBoundsMemory, store⟩
  | store16
      (h : address.toNat + offset.toNat + 2 ≤ store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues,
          .i32 value :: .i32 address :: values⟩,
          .store16 offset :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.store16 offset))
        ⟨.running ⟨⟨params, localValues, values⟩,
          code, arity, remainder, controls, calls⟩,
          setMemory store
            (store.wasm.mem.write16 (address + offset) value)⟩
  | load32Trap
      (h : address.toNat + offset.toNat + 4 > store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues, .i32 address :: values⟩,
          .load32 offset :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.load32 offset)) ⟨.trapped .outOfBoundsMemory, store⟩
  | load32
      (h : address.toNat + offset.toNat + 4 ≤ store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues, .i32 address :: values⟩,
          .load32 offset :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.load32 offset))
        ⟨.running ⟨⟨params, localValues,
          .i32 (store.wasm.mem.read32 (address + offset)) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | store32Trap
      (h : address.toNat + offset.toNat + 4 > store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues,
          .i32 value :: .i32 address :: values⟩,
          .store32 offset :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.store32 offset)) ⟨.trapped .outOfBoundsMemory, store⟩
  | store32
      (h : address.toNat + offset.toNat + 4 ≤ store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues,
          .i32 value :: .i32 address :: values⟩,
          .store32 offset :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.store32 offset))
        ⟨.running ⟨⟨params, localValues, values⟩, code, arity, remainder, controls, calls⟩,
          setMemory store (store.wasm.mem.write32 (address + offset) value)⟩
  | load8UMemory64Trap
      (h : address.toNat + offset.toNat + 1 > store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues, .i64 address :: values⟩,
          .load8U offset :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.load8U offset)) ⟨.trapped .outOfBoundsMemory, store⟩
  | load8UMemory64
      (h : address.toNat + offset.toNat + 1 ≤ store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues, .i64 address :: values⟩,
          .load8U offset :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.load8U offset))
        ⟨.running ⟨⟨params, localValues,
          .i32 (store.wasm.mem.read8
            (address.toUInt32 + offset)).toUInt32 :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | load8SMemory64Trap
      (h : address.toNat + offset.toNat + 1 > store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues, .i64 address :: values⟩,
          .load8S offset :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.load8S offset)) ⟨.trapped .outOfBoundsMemory, store⟩
  | load8SMemory64
      (h : address.toNat + offset.toNat + 1 ≤ store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues, .i64 address :: values⟩,
          .load8S offset :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.load8S offset))
        ⟨.running ⟨⟨params, localValues,
          .i32 (extend8To32
            (store.wasm.mem.read8
              (address.toUInt32 + offset)).toUInt32) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | load16UMemory64Trap
      (h : address.toNat + offset.toNat + 2 > store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues, .i64 address :: values⟩,
          .load16U offset :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.load16U offset)) ⟨.trapped .outOfBoundsMemory, store⟩
  | load16UMemory64
      (h : address.toNat + offset.toNat + 2 ≤ store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues, .i64 address :: values⟩,
          .load16U offset :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.load16U offset))
        ⟨.running ⟨⟨params, localValues,
          .i32 (store.wasm.mem.read16
            (address.toUInt32 + offset)) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | load16SMemory64Trap
      (h : address.toNat + offset.toNat + 2 > store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues, .i64 address :: values⟩,
          .load16S offset :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.load16S offset)) ⟨.trapped .outOfBoundsMemory, store⟩
  | load16SMemory64
      (h : address.toNat + offset.toNat + 2 ≤ store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues, .i64 address :: values⟩,
          .load16S offset :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.load16S offset))
        ⟨.running ⟨⟨params, localValues,
          .i32 (extend16To32
            (store.wasm.mem.read16
              (address.toUInt32 + offset))) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | store8Memory64Trap
      (h : address.toNat + offset.toNat + 1 > store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues,
          .i32 value :: .i64 address :: values⟩,
          .store8 offset :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.store8 offset)) ⟨.trapped .outOfBoundsMemory, store⟩
  | store8Memory64
      (h : address.toNat + offset.toNat + 1 ≤ store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues,
          .i32 value :: .i64 address :: values⟩,
          .store8 offset :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.store8 offset))
        ⟨.running ⟨⟨params, localValues, values⟩,
          code, arity, remainder, controls, calls⟩,
          setMemory store
            (store.wasm.mem.write8
              (address.toUInt32 + offset) value.toUInt8)⟩
  | store16Memory64Trap
      (h : address.toNat + offset.toNat + 2 > store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues,
          .i32 value :: .i64 address :: values⟩,
          .store16 offset :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.store16 offset)) ⟨.trapped .outOfBoundsMemory, store⟩
  | store16Memory64
      (h : address.toNat + offset.toNat + 2 ≤ store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues,
          .i32 value :: .i64 address :: values⟩,
          .store16 offset :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.store16 offset))
        ⟨.running ⟨⟨params, localValues, values⟩,
          code, arity, remainder, controls, calls⟩,
          setMemory store
            (store.wasm.mem.write16
              (address.toUInt32 + offset) value)⟩
  | load32Memory64Trap
      (h : address.toNat + offset.toNat + 4 > store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues, .i64 address :: values⟩,
          .load32 offset :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.load32 offset)) ⟨.trapped .outOfBoundsMemory, store⟩
  | load32Memory64
      (h : address.toNat + offset.toNat + 4 ≤ store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues, .i64 address :: values⟩,
          .load32 offset :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.load32 offset))
        ⟨.running ⟨⟨params, localValues,
          .i32 (store.wasm.mem.read32
            (address.toUInt32 + offset)) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | store32Memory64Trap
      (h : address.toNat + offset.toNat + 4 > store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues,
          .i32 value :: .i64 address :: values⟩,
          .store32 offset :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.store32 offset)) ⟨.trapped .outOfBoundsMemory, store⟩
  | store32Memory64
      (h : address.toNat + offset.toNat + 4 ≤ store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues,
          .i32 value :: .i64 address :: values⟩,
          .store32 offset :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.store32 offset))
        ⟨.running ⟨⟨params, localValues, values⟩,
          code, arity, remainder, controls, calls⟩,
          setMemory store
            (store.wasm.mem.write32
              (address.toUInt32 + offset) value)⟩
  | load64Trap
      (haddress : memoryAddress? address = some (logicalAddress, physicalAddress))
      (h : logicalAddress + offset.toNat + 8 >
        store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues, address :: values⟩,
          .load64 offset :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.load64 offset)) ⟨.trapped .outOfBoundsMemory, store⟩
  | load64
      (haddress : memoryAddress? address = some (logicalAddress, physicalAddress))
      (h : logicalAddress + offset.toNat + 8 ≤
        store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues, address :: values⟩,
          .load64 offset :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.load64 offset))
        ⟨.running ⟨⟨params, localValues,
          .i64 (store.wasm.mem.read64 (physicalAddress + offset)) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | store64Trap
      (haddress : memoryAddress? address = some (logicalAddress, physicalAddress))
      (h : logicalAddress + offset.toNat + 8 >
        store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues,
          .i64 value :: address :: values⟩,
          .store64 offset :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.store64 offset)) ⟨.trapped .outOfBoundsMemory, store⟩
  | store64
      (haddress : memoryAddress? address = some (logicalAddress, physicalAddress))
      (h : logicalAddress + offset.toNat + 8 ≤
        store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues,
          .i64 value :: address :: values⟩,
          .store64 offset :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.store64 offset))
        ⟨.running ⟨⟨params, localValues, values⟩,
          code, arity, remainder, controls, calls⟩,
          setMemory store
            (store.wasm.mem.write64 (physicalAddress + offset) value)⟩
  | f32LoadTrap
      (haddress : memoryAddress? address = some (logicalAddress, physicalAddress))
      (h : logicalAddress + offset.toNat + 4 >
        store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues, address :: values⟩,
          .f32Load offset :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.f32Load offset)) ⟨.trapped .outOfBoundsMemory, store⟩
  | f32Load
      (haddress : memoryAddress? address = some (logicalAddress, physicalAddress))
      (h : logicalAddress + offset.toNat + 4 ≤
        store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues, address :: values⟩,
          .f32Load offset :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.f32Load offset))
        ⟨.running ⟨⟨params, localValues,
          .f32 (store.wasm.mem.read32 (physicalAddress + offset)) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | f32StoreTrap
      (haddress : memoryAddress? address = some (logicalAddress, physicalAddress))
      (h : logicalAddress + offset.toNat + 4 >
        store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues,
          .f32 value :: address :: values⟩,
          .f32Store offset :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.f32Store offset)) ⟨.trapped .outOfBoundsMemory, store⟩
  | f32Store
      (haddress : memoryAddress? address = some (logicalAddress, physicalAddress))
      (h : logicalAddress + offset.toNat + 4 ≤
        store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues,
          .f32 value :: address :: values⟩,
          .f32Store offset :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.f32Store offset))
        ⟨.running ⟨⟨params, localValues, values⟩,
          code, arity, remainder, controls, calls⟩,
          setMemory store
            (store.wasm.mem.write32 (physicalAddress + offset) value)⟩
  | f64LoadTrap
      (haddress : memoryAddress? address = some (logicalAddress, physicalAddress))
      (h : logicalAddress + offset.toNat + 8 >
        store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues, address :: values⟩,
          .f64Load offset :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.f64Load offset)) ⟨.trapped .outOfBoundsMemory, store⟩
  | f64Load
      (haddress : memoryAddress? address = some (logicalAddress, physicalAddress))
      (h : logicalAddress + offset.toNat + 8 ≤
        store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues, address :: values⟩,
          .f64Load offset :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.f64Load offset))
        ⟨.running ⟨⟨params, localValues,
          .f64 (store.wasm.mem.read64 (physicalAddress + offset)) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | f64StoreTrap
      (haddress : memoryAddress? address = some (logicalAddress, physicalAddress))
      (h : logicalAddress + offset.toNat + 8 >
        store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues,
          .f64 value :: address :: values⟩,
          .f64Store offset :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.f64Store offset)) ⟨.trapped .outOfBoundsMemory, store⟩
  | f64Store
      (haddress : memoryAddress? address = some (logicalAddress, physicalAddress))
      (h : logicalAddress + offset.toNat + 8 ≤
        store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues,
          .f64 value :: address :: values⟩,
          .f64Store offset :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.f64Store offset))
        ⟨.running ⟨⟨params, localValues, values⟩,
          code, arity, remainder, controls, calls⟩,
          setMemory store
            (store.wasm.mem.write64 (physicalAddress + offset) value)⟩
  | load8UI64Trap
      (haddress : memoryAddress? address = some (logicalAddress, physicalAddress))
      (h : logicalAddress + offset.toNat + 1 >
        store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues, address :: values⟩,
          .load8UI64 offset :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.load8UI64 offset))
        ⟨.trapped .outOfBoundsMemory, store⟩
  | load8UI64
      (haddress : memoryAddress? address = some (logicalAddress, physicalAddress))
      (h : logicalAddress + offset.toNat + 1 ≤
        store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues, address :: values⟩,
          .load8UI64 offset :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.load8UI64 offset))
        ⟨.running ⟨⟨params, localValues,
          .i64 (store.wasm.mem.read8
            (physicalAddress + offset)).toUInt64 :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | load8SI64Trap
      (haddress : memoryAddress? address = some (logicalAddress, physicalAddress))
      (h : logicalAddress + offset.toNat + 1 >
        store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues, address :: values⟩,
          .load8SI64 offset :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.load8SI64 offset))
        ⟨.trapped .outOfBoundsMemory, store⟩
  | load8SI64
      (haddress : memoryAddress? address = some (logicalAddress, physicalAddress))
      (h : logicalAddress + offset.toNat + 1 ≤
        store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues, address :: values⟩,
          .load8SI64 offset :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.load8SI64 offset))
        ⟨.running ⟨⟨params, localValues,
          .i64 (extend8To64
            (store.wasm.mem.read8
              (physicalAddress + offset)).toUInt64) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | load16UI64Trap
      (haddress : memoryAddress? address = some (logicalAddress, physicalAddress))
      (h : logicalAddress + offset.toNat + 2 >
        store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues, address :: values⟩,
          .load16UI64 offset :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.load16UI64 offset))
        ⟨.trapped .outOfBoundsMemory, store⟩
  | load16UI64
      (haddress : memoryAddress? address = some (logicalAddress, physicalAddress))
      (h : logicalAddress + offset.toNat + 2 ≤
        store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues, address :: values⟩,
          .load16UI64 offset :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.load16UI64 offset))
        ⟨.running ⟨⟨params, localValues,
          .i64 (store.wasm.mem.read16
            (physicalAddress + offset)).toUInt64 :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | load16SI64Trap
      (haddress : memoryAddress? address = some (logicalAddress, physicalAddress))
      (h : logicalAddress + offset.toNat + 2 >
        store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues, address :: values⟩,
          .load16SI64 offset :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.load16SI64 offset))
        ⟨.trapped .outOfBoundsMemory, store⟩
  | load16SI64
      (haddress : memoryAddress? address = some (logicalAddress, physicalAddress))
      (h : logicalAddress + offset.toNat + 2 ≤
        store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues, address :: values⟩,
          .load16SI64 offset :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.load16SI64 offset))
        ⟨.running ⟨⟨params, localValues,
          .i64 (extend16To64
            (store.wasm.mem.read16
              (physicalAddress + offset)).toUInt64) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | load32UI64Trap
      (haddress : memoryAddress? address = some (logicalAddress, physicalAddress))
      (h : logicalAddress + offset.toNat + 4 >
        store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues, address :: values⟩,
          .load32UI64 offset :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.load32UI64 offset))
        ⟨.trapped .outOfBoundsMemory, store⟩
  | load32UI64
      (haddress : memoryAddress? address = some (logicalAddress, physicalAddress))
      (h : logicalAddress + offset.toNat + 4 ≤
        store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues, address :: values⟩,
          .load32UI64 offset :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.load32UI64 offset))
        ⟨.running ⟨⟨params, localValues,
          .i64 (store.wasm.mem.read32
            (physicalAddress + offset)).toUInt64 :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | load32SI64Trap
      (haddress : memoryAddress? address = some (logicalAddress, physicalAddress))
      (h : logicalAddress + offset.toNat + 4 >
        store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues, address :: values⟩,
          .load32SI64 offset :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.load32SI64 offset))
        ⟨.trapped .outOfBoundsMemory, store⟩
  | load32SI64
      (haddress : memoryAddress? address = some (logicalAddress, physicalAddress))
      (h : logicalAddress + offset.toNat + 4 ≤
        store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues, address :: values⟩,
          .load32SI64 offset :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.load32SI64 offset))
        ⟨.running ⟨⟨params, localValues,
          .i64 (extend32To64
            (store.wasm.mem.read32
              (physicalAddress + offset)).toUInt64) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | store8I64Trap
      (haddress : memoryAddress? address = some (logicalAddress, physicalAddress))
      (h : logicalAddress + offset.toNat + 1 >
        store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues,
          .i64 value :: address :: values⟩,
          .store8I64 offset :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.store8I64 offset))
        ⟨.trapped .outOfBoundsMemory, store⟩
  | store8I64
      (haddress : memoryAddress? address = some (logicalAddress, physicalAddress))
      (h : logicalAddress + offset.toNat + 1 ≤
        store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues,
          .i64 value :: address :: values⟩,
          .store8I64 offset :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.store8I64 offset))
        ⟨.running ⟨⟨params, localValues, values⟩,
          code, arity, remainder, controls, calls⟩,
          setMemory store
            (store.wasm.mem.write8
              (physicalAddress + offset) value.toUInt8)⟩
  | store16I64Trap
      (haddress : memoryAddress? address = some (logicalAddress, physicalAddress))
      (h : logicalAddress + offset.toNat + 2 >
        store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues,
          .i64 value :: address :: values⟩,
          .store16I64 offset :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.store16I64 offset))
        ⟨.trapped .outOfBoundsMemory, store⟩
  | store16I64
      (haddress : memoryAddress? address = some (logicalAddress, physicalAddress))
      (h : logicalAddress + offset.toNat + 2 ≤
        store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues,
          .i64 value :: address :: values⟩,
          .store16I64 offset :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.store16I64 offset))
        ⟨.running ⟨⟨params, localValues, values⟩,
          code, arity, remainder, controls, calls⟩,
          setMemory store
            (store.wasm.mem.write16
              (physicalAddress + offset) value.toUInt32)⟩
  | store32I64Trap
      (haddress : memoryAddress? address = some (logicalAddress, physicalAddress))
      (h : logicalAddress + offset.toNat + 4 >
        store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues,
          .i64 value :: address :: values⟩,
          .store32I64 offset :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.store32I64 offset))
        ⟨.trapped .outOfBoundsMemory, store⟩
  | store32I64
      (haddress : memoryAddress? address = some (logicalAddress, physicalAddress))
      (h : logicalAddress + offset.toNat + 4 ≤
        store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues,
          .i64 value :: address :: values⟩,
          .store32I64 offset :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction (.store32I64 offset))
        ⟨.running ⟨⟨params, localValues, values⟩,
          code, arity, remainder, controls, calls⟩,
          setMemory store
            (store.wasm.mem.write32
              (physicalAddress + offset) value.toUInt32)⟩
  | memorySize :
      Step ⟨.running ⟨⟨params, localValues, values⟩,
          .memorySize :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .memorySize)
        ⟨.running ⟨⟨params, localValues,
          sizeValue store.runtime.currentModule.memIs64 store.wasm.mem.pages :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | memoryGrowSuccess
      (h : store.wasm.mem.grow delta
        (store.wasm.memoryCap store.runtime.currentModule 0) =
        some (memory, previousPages)) :
      Step ⟨.running ⟨⟨params, localValues, .i32 delta :: values⟩,
          .memoryGrow :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .memoryGrow)
        ⟨.running ⟨⟨params, localValues,
          .i32 previousPages.toUInt32 :: values⟩,
          code, arity, remainder, controls, calls⟩,
          setMemory store memory⟩
  | memoryGrowFailure
      (h : store.wasm.mem.grow delta
        (store.wasm.memoryCap store.runtime.currentModule 0) = none) :
      Step ⟨.running ⟨⟨params, localValues, .i32 delta :: values⟩,
          .memoryGrow :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .memoryGrow)
        ⟨.running ⟨⟨params, localValues,
          .i32 (0xFFFFFFFF : UInt32) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | memoryGrow64TooLarge
      (h : delta.toNat ≥ 2 ^ 32) :
      Step ⟨.running ⟨⟨params, localValues, .i64 delta :: values⟩,
          .memoryGrow :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .memoryGrow)
        ⟨.running ⟨⟨params, localValues,
          .i64 (0xFFFFFFFFFFFFFFFF : UInt64) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | memoryGrow64Success
      (hsmall : delta.toNat < 2 ^ 32)
      (h : store.wasm.mem.grow delta.toUInt32
        (store.wasm.memoryCap store.runtime.currentModule 0) =
          some (memory, previousPages)) :
      Step ⟨.running ⟨⟨params, localValues, .i64 delta :: values⟩,
          .memoryGrow :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .memoryGrow)
        ⟨.running ⟨⟨params, localValues,
          .i64 previousPages.toUInt64 :: values⟩,
          code, arity, remainder, controls, calls⟩,
          setMemory store memory⟩
  | memoryGrow64Failure
      (hsmall : delta.toNat < 2 ^ 32)
      (h : store.wasm.mem.grow delta.toUInt32
        (store.wasm.memoryCap store.runtime.currentModule 0) = none) :
      Step ⟨.running ⟨⟨params, localValues, .i64 delta :: values⟩,
          .memoryGrow :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .memoryGrow)
        ⟨.running ⟨⟨params, localValues,
          .i64 (0xFFFFFFFFFFFFFFFF : UInt64) :: values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | memoryFill32Trap
      (h : destination.toNat + len.toNat >
        store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues,
          .i32 len :: .i32 value :: .i32 destination :: values⟩,
          .memoryFill :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .memoryFill)
        ⟨.trapped .outOfBoundsMemory, store⟩
  | memoryFill32
      (h : destination.toNat + len.toNat ≤
        store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues,
          .i32 len :: .i32 value :: .i32 destination :: values⟩,
          .memoryFill :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .memoryFill)
        ⟨.running ⟨⟨params, localValues, values⟩,
          code, arity, remainder, controls, calls⟩,
          setMemory store
            (store.wasm.mem.fill destination.toNat len.toNat value.toUInt8)⟩
  | memoryFill64Trap
      (h : destination.toNat + len.toNat >
        store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues,
          .i64 len :: .i32 value :: .i64 destination :: values⟩,
          .memoryFill :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .memoryFill)
        ⟨.trapped .outOfBoundsMemory, store⟩
  | memoryFill64
      (h : destination.toNat + len.toNat ≤
        store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues,
          .i64 len :: .i32 value :: .i64 destination :: values⟩,
          .memoryFill :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .memoryFill)
        ⟨.running ⟨⟨params, localValues, values⟩,
          code, arity, remainder, controls, calls⟩,
          setMemory store
            (store.wasm.mem.fill destination.toNat len.toNat value.toUInt8)⟩
  | memoryCopy32Trap
      (h : destination.toNat + len.toNat >
          store.wasm.mem.pages * 65536 ∨
        source.toNat + len.toNat >
          store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues,
          .i32 len :: .i32 source :: .i32 destination :: values⟩,
          .memoryCopy :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .memoryCopy)
        ⟨.trapped .outOfBoundsMemory, store⟩
  | memoryCopy32
      (hdestination : destination.toNat + len.toNat ≤
        store.wasm.mem.pages * 65536)
      (hsource : source.toNat + len.toNat ≤
        store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues,
          .i32 len :: .i32 source :: .i32 destination :: values⟩,
          .memoryCopy :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .memoryCopy)
        ⟨.running ⟨⟨params, localValues, values⟩,
          code, arity, remainder, controls, calls⟩,
          setMemory store
            (store.wasm.mem.copy destination.toNat source.toNat len.toNat)⟩
  | memoryCopy64Trap
      (h : destination.toNat + len.toNat >
          store.wasm.mem.pages * 65536 ∨
        source.toNat + len.toNat >
          store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues,
          .i64 len :: .i64 source :: .i64 destination :: values⟩,
          .memoryCopy :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .memoryCopy)
        ⟨.trapped .outOfBoundsMemory, store⟩
  | memoryCopy64
      (hdestination : destination.toNat + len.toNat ≤
        store.wasm.mem.pages * 65536)
      (hsource : source.toNat + len.toNat ≤
        store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues,
          .i64 len :: .i64 source :: .i64 destination :: values⟩,
          .memoryCopy :: code, arity, remainder, controls, calls⟩, store⟩
        (.instruction .memoryCopy)
        ⟨.running ⟨⟨params, localValues, values⟩,
          code, arity, remainder, controls, calls⟩,
          setMemory store
            (store.wasm.mem.copy destination.toNat source.toNat len.toNat)⟩
  | memoryInit32DroppedTrap
      (hsegment : store.wasm.dataSegments[segmentIndex]? = some none)
      (h : 0 < len.toNat ∨ destination.toNat + len.toNat >
        store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues,
          .i32 len :: .i32 source :: .i32 destination :: values⟩,
          .memoryInit segmentIndex :: code,
          arity, remainder, controls, calls⟩, store⟩
        (.instruction (.memoryInit segmentIndex))
        ⟨.trapped .outOfBoundsMemory, store⟩
  | memoryInit32Dropped
      (hsegment : store.wasm.dataSegments[segmentIndex]? = some none)
      (h : ¬(0 < len.toNat ∨ destination.toNat + len.toNat >
        store.wasm.mem.pages * 65536)) :
      Step ⟨.running ⟨⟨params, localValues,
          .i32 len :: .i32 source :: .i32 destination :: values⟩,
          .memoryInit segmentIndex :: code,
          arity, remainder, controls, calls⟩, store⟩
        (.instruction (.memoryInit segmentIndex))
        ⟨.running ⟨⟨params, localValues, values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | memoryInit32Trap
      (hsegment :
        store.wasm.dataSegments[segmentIndex]? = some (some segmentBytes))
      (h : source.toNat + len.toNat > segmentBytes.length ∨
        destination.toNat + len.toNat >
          store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues,
          .i32 len :: .i32 source :: .i32 destination :: values⟩,
          .memoryInit segmentIndex :: code,
          arity, remainder, controls, calls⟩, store⟩
        (.instruction (.memoryInit segmentIndex))
        ⟨.trapped .outOfBoundsMemory, store⟩
  | memoryInit32
      (hsegment :
        store.wasm.dataSegments[segmentIndex]? = some (some segmentBytes))
      (hsource : source.toNat + len.toNat ≤ segmentBytes.length)
      (hdestination : destination.toNat + len.toNat ≤
        store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues,
          .i32 len :: .i32 source :: .i32 destination :: values⟩,
          .memoryInit segmentIndex :: code,
          arity, remainder, controls, calls⟩, store⟩
        (.instruction (.memoryInit segmentIndex))
        ⟨.running ⟨⟨params, localValues, values⟩,
          code, arity, remainder, controls, calls⟩,
          setMemory store
            (store.wasm.mem.writeBytesFrom destination.toNat
              segmentBytes source.toNat len.toNat)⟩
  | memoryInit64DroppedTrap
      (hsegment : store.wasm.dataSegments[segmentIndex]? = some none)
      (h : 0 < len.toNat ∨ destination.toNat + len.toNat >
        store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues,
          .i32 len :: .i32 source :: .i64 destination :: values⟩,
          .memoryInit segmentIndex :: code,
          arity, remainder, controls, calls⟩, store⟩
        (.instruction (.memoryInit segmentIndex))
        ⟨.trapped .outOfBoundsMemory, store⟩
  | memoryInit64Dropped
      (hsegment : store.wasm.dataSegments[segmentIndex]? = some none)
      (h : ¬(0 < len.toNat ∨ destination.toNat + len.toNat >
        store.wasm.mem.pages * 65536)) :
      Step ⟨.running ⟨⟨params, localValues,
          .i32 len :: .i32 source :: .i64 destination :: values⟩,
          .memoryInit segmentIndex :: code,
          arity, remainder, controls, calls⟩, store⟩
        (.instruction (.memoryInit segmentIndex))
        ⟨.running ⟨⟨params, localValues, values⟩,
          code, arity, remainder, controls, calls⟩, store⟩
  | memoryInit64Trap
      (hsegment :
        store.wasm.dataSegments[segmentIndex]? = some (some segmentBytes))
      (h : source.toNat + len.toNat > segmentBytes.length ∨
        destination.toNat + len.toNat >
          store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues,
          .i32 len :: .i32 source :: .i64 destination :: values⟩,
          .memoryInit segmentIndex :: code,
          arity, remainder, controls, calls⟩, store⟩
        (.instruction (.memoryInit segmentIndex))
        ⟨.trapped .outOfBoundsMemory, store⟩
  | memoryInit64
      (hsegment :
        store.wasm.dataSegments[segmentIndex]? = some (some segmentBytes))
      (hsource : source.toNat + len.toNat ≤ segmentBytes.length)
      (hdestination : destination.toNat + len.toNat ≤
        store.wasm.mem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues,
          .i32 len :: .i32 source :: .i64 destination :: values⟩,
          .memoryInit segmentIndex :: code,
          arity, remainder, controls, calls⟩, store⟩
        (.instruction (.memoryInit segmentIndex))
        ⟨.running ⟨⟨params, localValues, values⟩,
          code, arity, remainder, controls, calls⟩,
          setMemory store
            (store.wasm.mem.writeBytesFrom destination.toNat
              segmentBytes source.toNat len.toNat)⟩
  | dataDrop
      (hsegment : (store.wasm.dataSegments[segmentIndex]?).isSome = true) :
      Step ⟨.running ⟨locals, .dataDrop segmentIndex :: code,
          arity, remainder, controls, calls⟩, store⟩
        (.instruction (.dataDrop segmentIndex))
        ⟨.running ⟨locals, code, arity, remainder, controls, calls⟩,
          setDataSegments store
            (store.wasm.dataSegments.set segmentIndex none)⟩
  | gcFallthrough
      (heval :
        execGcOp store.runtime.currentModule store.wasm locals operation =
          .Fallthrough wasm locals') :
      Step
        ⟨.running ⟨locals, .gc operation :: code,
          arity, remainder, controls, calls⟩, store⟩
        (.instruction (.gc operation))
        ⟨.running ⟨locals', code, arity, remainder, controls, calls⟩,
          { store with wasm }⟩
  | gcTrap
      (heval :
        execGcOp store.runtime.currentModule store.wasm locals operation =
          .Trap wasm message) :
      Step
        ⟨.running ⟨locals, .gc operation :: code,
          arity, remainder, controls, calls⟩, store⟩
        (.instruction (.gc operation))
        ⟨.trapped (gcTrapReasonOfMessage message), { store with wasm }⟩
  | gcBranch
      (heval :
        execGcOp store.runtime.currentModule store.wasm locals operation =
          .Break depth wasm locals')
      (htarget :
        branchTarget? arity depth controls locals'.values =
          some (targetCode, targetControls, targetValues)) :
      Step
        ⟨.running ⟨locals, .gc operation :: code,
          arity, remainder, controls, calls⟩, store⟩
        (.instruction (.gc operation))
        ⟨.running
          ⟨{ locals' with values := targetValues },
            targetCode, arity, remainder, targetControls, calls⟩,
          { store with wasm }⟩
  | memoryCopyBetweenTrap
      (hlength : lengthValue.addrNat? = some length)
      (hsource : sourceValue.addrNat? = some source)
      (hdestination : destinationValue.addrNat? = some destination)
      (hdestinationMemory :
        memoryAt? store destinationMemory = some destinationMem)
      (hsourceMemory : memoryAt? store sourceMemory = some sourceMem)
      (hbound :
        destination + length > destinationMem.pages * 65536 ∨
          source + length > sourceMem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues,
          lengthValue :: sourceValue :: destinationValue :: values⟩,
          .memoryCopyBetween destinationMemory sourceMemory :: code,
          arity, remainder, controls, calls⟩, store⟩
        (.instruction (.memoryCopyBetween destinationMemory sourceMemory))
        ⟨.trapped .outOfBoundsMemory, store⟩
  | memoryCopyBetween
      (hlength : lengthValue.addrNat? = some length)
      (hsource : sourceValue.addrNat? = some source)
      (hdestination : destinationValue.addrNat? = some destination)
      (hdestinationMemory :
        memoryAt? store destinationMemory = some destinationMem)
      (hsourceMemory : memoryAt? store sourceMemory = some sourceMem)
      (hbound :
        destination + length ≤ destinationMem.pages * 65536)
      (hsourceBound : source + length ≤ sourceMem.pages * 65536) :
      Step ⟨.running ⟨⟨params, localValues,
          lengthValue :: sourceValue :: destinationValue :: values⟩,
          .memoryCopyBetween destinationMemory sourceMemory :: code,
          arity, remainder, controls, calls⟩, store⟩
        (.instruction (.memoryCopyBetween destinationMemory sourceMemory))
        ⟨.running ⟨⟨params, localValues, values⟩,
          code, arity, remainder, controls, calls⟩,
          setMemoryAt store destinationMemory
            (destinationMem.writeBytes destination
              (sourceMem.readBytes source length))⟩
  | memOp
      (hinner : isMemOp inner = false)
      (henter : enterIndexedMemory? store memoryIndex = some indexedStore)
      (hstep :
        Step
          ⟨.running
            { locals := locals
              code := [inner]
              resultArity := arity
              callerRemainder := remainder
              control := controls
              calls := calls },
            indexedStore⟩
          innerKind stepped) :
      Step
        ⟨.running
          { locals := locals
            code := .memOp memoryIndex inner :: rest
            resultArity := arity
            callerRemainder := remainder
            control := controls
            calls := calls },
          store⟩
        (.instruction (.memOp memoryIndex inner))
        (resumeAfterIndexedMemory rest store memoryIndex stepped)
set_option maxHeartbeats 5000000 in
theorem stepChecked?_sound {config config' : Config α} {kind : StepKind} :
    stepChecked? config = .ok (some (kind, config')) → Step config kind config' :=
by
  intro h
  cases config
  rename_i expr store
  cases expr with
  | done => simp [stepChecked?] at h
  | trapped => simp [stepChecked?] at h
  | running thread =>
    cases thread
    rename_i locals code arity remainder controls calls
    cases locals
    rename_i params localValues operands
    cases code with
    | nil =>
      cases controls with
      | nil =>
        cases calls with
        | nil =>
          simp [stepChecked?] at h
          obtain ⟨rfl, rfl⟩ := h
          exact .finish
        | cons caller calls =>
          by_cases hrc : caller.returningInstance = store.runtime.entry
          · simp [stepChecked?, hrc] at h
            obtain ⟨rfl, rfl⟩ := h
            exact .returnFromCallFallthrough hrc
          · simp [stepChecked?] at h
            rw [if_neg hrc] at h
            simp at h
            obtain ⟨rfl, rfl⟩ := h
            exact .returnFromCallCrossInstanceFallthrough hrc
      | cons frame controls =>
        cases controls with
        | nil =>
          cases hk : frame.kind with
          | throwing tag arguments =>
            cases calls with
            | nil =>
              simp [stepChecked?, hk] at h
              obtain ⟨rfl, rfl⟩ := h
              exact .uncaughtException hk
            | cons caller calls =>
              simp [stepChecked?, hk] at h
              obtain ⟨rfl, rfl⟩ := h
              exact .unwindExceptionCall hk
          | block | loop | tryTable =>
            simp [stepChecked?, hk] at h
            obtain ⟨rfl, rfl⟩ := h
            apply Step.exitControl
            simp [ControlKind.isThrowing, hk]
        | cons handler outer =>
          rcases handler with
            ⟨handlerKind, handlerParamArity, handlerResultArity,
              handlerBody, handlerContinuation, handlerBelowStack⟩
          cases hk : frame.kind with
          | block | loop | tryTable =>
            simp [stepChecked?, hk] at h
            obtain ⟨rfl, rfl⟩ := h
            apply Step.exitControl
            simp [ControlKind.isThrowing, hk]
          | throwing tag arguments =>
            cases hh : handlerKind with
            | block | loop =>
              simp [stepChecked?, hk, hh] at h
              obtain ⟨rfl, rfl⟩ := h
              apply Step.unwindExceptionFrame hk
              simp
            | throwing =>
              simp [stepChecked?, hk, hh] at h
              obtain ⟨rfl, rfl⟩ := h
              exact Step.unwindNestedException hk rfl
            | tryTable catches =>
              cases hm : matchingCatch? tag catches with
              | none =>
                simp [stepChecked?, hk, hh, hm] at h
                obtain ⟨rfl, rfl⟩ := h
                apply Step.unwindExceptionFrame hk
                simp [hm]
              | some clause =>
                cases ht : branchTarget? arity (catchLabel clause) outer
                    ((prepareCatch tag arguments clause store).1 ++
                      handlerBelowStack) with
                | none =>
                  simp [stepChecked?, hk, hh, hm, ht] at h
                | some target =>
                  rcases target with ⟨targetCode, targetControl, targetValues⟩
                  simp [stepChecked?, hk, hh, hm, ht] at h
                  obtain ⟨rfl, rfl⟩ := h
                  exact Step.catchException hk hm ht
    | cons instr code =>
      cases hinstr : instr
      case memOp memoryIndex inner =>
        subst instr
        cases hi : isMemOp inner with
        | true =>
          rw [stepChecked?] at h
          simp only [hi] at h
          cases h
        | false =>
          rw [stepChecked?] at h
          simp only [hi] at h
          cases he : enterIndexedMemory? store memoryIndex with
          | none =>
            try simp only [he] at h
            cases h
          | some indexedStore =>
            try simp only [he] at h
            cases hs : stepPlainChecked?
                ⟨.running
                  { locals := { params, locals := localValues, values := operands }
                    code := [inner]
                    resultArity := arity
                    callerRemainder := remainder
                    control := controls
                    calls := calls },
                  indexedStore⟩ with
            | error error =>
              try simp only [hs] at h
              cases h
            | ok result =>
              cases result with
              | none =>
                try simp only [hs] at h
                cases h
              | some transition =>
                rcases transition with ⟨innerKind, stepped⟩
                try simp only [hs] at h
                obtain ⟨rfl, rfl⟩ := h
                apply Step.memOp hi he
                apply stepChecked?_sound (kind := innerKind)
                cases inner <;>
                  simp_all only [stepChecked?, isMemOp, Bool.true_eq_false]
      all_goals simp_all [stepChecked?, evalScalarFloat0?,
        evalScalarFloat1?, evalScalarTrunc?, evalScalarFloat2?,
        Locals.get, Locals.set?]
      all_goals (repeat' first | split at h | simp_all [setGlobal, setMemory])
      all_goals rcases h with ⟨rfl, rfl⟩
      all_goals
        first
        | exact Step.returnFromFunction
        | (exact Step.returnFromCallExplicit ‹_›)
        | (exact Step.returnFromCallCrossInstanceExplicit ‹_›)
        | exact Step.unreachable
        | exact Step.nop
        | exact Step.block
        | exact Step.loop
        | exact Step.tryTable
        | (apply Step.throwI <;> assumption)
        | exact Step.throwRefNull
        | (apply Step.throwRef <;> assumption)
        | (apply Step.iff <;> simp_all)
        | (apply Step.br <;> simp_all)
        | exact Step.brIfZero
        | (apply Step.brIf <;> simp_all)
        | (apply Step.brTable <;> simp_all)
        | solve_by_elim [Step.callHostReturn, Step.callHostTrap,
            Step.callHostThrow,
            Step.returnCallHostReturn, Step.returnCallHostTrap,
            Step.returnCallHostThrow]
        | (apply Step.callCrossInstance <;>
            (first | assumption | simp_all [getElem?_eq_getElem]))
        | (apply Step.call <;> simp_all)
        | (apply Step.returnCall <;> simp_all)
        | (apply Step.callIndirectUndefined <;> first | assumption | omega)
        | (apply Step.callIndirectUninitialized <;> assumption)
        | solve
          | (apply Step.callIndirectForeignTypeMismatch <;>
              first | assumption | simp_all)
        | solve
          | (apply Step.callIndirectForeignReturn <;>
              first | assumption | simp_all)
        | solve
          | (apply Step.callIndirectForeignTrap <;>
              first | assumption | simp_all)
        | solve
          | (apply Step.callIndirectForeignThrow <;>
              first | assumption | simp_all)
        | (apply Step.callIndirectHostTypeMismatch <;> assumption)
        | (apply Step.callIndirectHostReturn <;> assumption)
        | (apply Step.callIndirectHostTrap <;> assumption)
        | (apply Step.callIndirectHostThrow <;> assumption)
        | (apply Step.callIndirectCrossInstanceTypeMismatch <;> assumption)
        | (apply Step.callIndirectCrossInstance <;>
            (first | assumption | simp_all [getElem?_eq_getElem]))
        | (apply Step.returnCallIndirectHostTypeMismatch <;> assumption)
        | (apply Step.returnCallIndirectHostReturn <;> assumption)
        | (apply Step.returnCallIndirectHostTrap <;> assumption)
        | (apply Step.returnCallIndirectHostThrow <;> assumption)
        | solve
          | (apply Step.callIndirectTypeMismatch <;>
              first | assumption | omega)
        | solve
          | (apply Step.callIndirect <;>
              first | assumption | omega)
        | (apply Step.returnCallIndirectUndefined <;> first | assumption | omega)
        | (apply Step.returnCallIndirectUninitialized <;> assumption)
        | (apply Step.returnCallIndirectTypeMismatch <;> first | assumption | omega)
        | (apply Step.returnCallIndirect <;> first | assumption | omega)
        | exact Step.refNull
        | exact Step.refNullExtern
        | exact Step.refNullExn
        | exact Step.refFunc
        | exact Step.callRefNull
        | solve_by_elim [Step.callRefHostReturn, Step.callRefHostTrap,
            Step.callRefHostThrow,
            Step.returnCallRefHostReturn, Step.returnCallRefHostTrap,
            Step.returnCallRefHostThrow]
        | (apply Step.callRef <;> first | assumption | omega)
        | exact Step.returnCallRefNull
        | (apply Step.returnCallRef <;> first | assumption | omega)
        | (apply Step.refIsNullTrue <;> assumption)
        | (apply Step.refIsNullFalse <;> assumption)
        | (apply Step.refAsNonNullTrap <;> simp_all)
        | (apply Step.refAsNonNull <;> simp_all)
        | (apply Step.brOnNullBranch <;> assumption)
        | (apply Step.brOnNullFallthrough <;> assumption)
        | (apply Step.brOnNonNullFallthrough <;> assumption)
        | (apply Step.brOnNonNullBranch <;> assumption)
        | (apply Step.tableGetTrap <;> first | assumption | omega)
        | (apply Step.tableGet <;> assumption)
        | (apply Step.tableSize <;> assumption)
        | (apply Step.tableSetTrap <;> first | assumption | omega)
        | (apply Step.tableSet <;> assumption)
        | (apply Step.tableGrow32 <;> assumption)
        | (apply Step.tableGrow32Failure <;> first | assumption | omega)
        | (apply Step.tableGrow64 <;> assumption)
        | (apply Step.tableGrow64Failure <;> first | assumption | omega)
        | (apply Step.tableFillTrap <;> first | assumption | omega)
        | (apply Step.tableFill <;> first | assumption | omega)
        | (apply Step.tableCopyTrap <;> first | assumption | omega)
        | (apply Step.tableCopy <;> first | assumption | omega)
        | (apply Step.tableInitTrap <;> first | rfl | assumption | omega)
        | (apply Step.tableInit <;> first | rfl | assumption | omega)
        | (apply Step.elemDrop <;> simp_all)
        | exact Step.const
        | exact Step.constI64
        | exact Step.drop
        | (apply Step.select <;> simp_all)
        | exact Step.add
        | exact Step.sub
        | exact Step.mul
        | exact Step.and
        | exact Step.or
        | exact Step.xor
        | exact Step.shl
        | exact Step.shrU
        | simpa using (Step.shrS (α := α))
        | exact Step.rotl
        | exact Step.rotr
        | exact Step.clz
        | exact Step.ctz
        | exact Step.popcnt
        | exact Step.addI64
        | exact Step.subI64
        | exact Step.mulI64
        | exact Step.andI64
        | exact Step.orI64
        | exact Step.xorI64
        | exact Step.shlI64
        | exact Step.shrUI64
        | simpa using (Step.shrSI64 (α := α))
        | exact Step.rotlI64
        | exact Step.rotrI64
        | exact Step.clzI64
        | exact Step.ctzI64
        | exact Step.popcntI64
        | exact Step.divUZero
        | exact Step.divSZero
        | exact Step.divSOverflow
        | exact Step.remUZero
        | exact Step.remSZero
        | exact Step.divUI64Zero
        | exact Step.divSI64Zero
        | exact Step.divSI64Overflow
        | exact Step.remUI64Zero
        | exact Step.remSI64Zero
        | (apply Step.eqz <;> simp_all)
        | (apply Step.eq <;> simp_all)
        | (apply Step.ne <;> simp_all)
        | (apply Step.ltU <;> simp_all)
        | (apply Step.gtU <;> simp_all)
        | (apply Step.leU <;> simp_all)
        | (apply Step.geU <;> simp_all)
        | (apply Step.ltS <;> simp_all)
        | (apply Step.gtS <;> simp_all)
        | (apply Step.leS <;> simp_all)
        | (apply Step.geS <;> simp_all)
        | (apply Step.eqzI64 <;> simp_all)
        | (apply Step.eqI64 <;> simp_all)
        | (apply Step.neI64 <;> simp_all)
        | (apply Step.ltUI64 <;> simp_all)
        | (apply Step.ltSI64 <;> simp_all)
        | (apply Step.gtUI64 <;> simp_all)
        | (apply Step.gtSI64 <;> simp_all)
        | (apply Step.leUI64 <;> simp_all)
        | (apply Step.leSI64 <;> simp_all)
        | (apply Step.geUI64 <;> simp_all)
        | (apply Step.geSI64 <;> simp_all)
        | exact Step.wrapI64
        | exact Step.extendUI32
        | exact Step.extendSI32
        | exact Step.extend8S
        | exact Step.extend16S
        | exact Step.extend8SI64
        | exact Step.extend16SI64
        | exact Step.extend32SI64
        | apply Step.load8UTrap <;> omega
        | apply Step.load8U <;> omega
        | apply Step.load8STrap <;> omega
        | apply Step.load8S <;> omega
        | apply Step.load16UTrap <;> omega
        | apply Step.load16U <;> omega
        | apply Step.load16STrap <;> omega
        | apply Step.load16S <;> omega
        | apply Step.store8Trap <;> omega
        | apply Step.store8 <;> omega
        | apply Step.store16Trap <;> omega
        | apply Step.store16 <;> omega
        | apply Step.load32Trap <;> omega
        | apply Step.load32 <;> omega
        | apply Step.store32Trap <;> omega
        | apply Step.store32 <;> omega
        | apply Step.load8UMemory64Trap <;> omega
        | apply Step.load8UMemory64 <;> omega
        | apply Step.load8SMemory64Trap <;> omega
        | apply Step.load8SMemory64 <;> omega
        | apply Step.load16UMemory64Trap <;> omega
        | apply Step.load16UMemory64 <;> omega
        | apply Step.load16SMemory64Trap <;> omega
        | apply Step.load16SMemory64 <;> omega
        | apply Step.store8Memory64Trap <;> omega
        | apply Step.store8Memory64 <;> omega
        | apply Step.store16Memory64Trap <;> omega
        | apply Step.store16Memory64 <;> omega
        | apply Step.load32Memory64Trap <;> omega
        | apply Step.load32Memory64 <;> omega
        | apply Step.store32Memory64Trap <;> omega
        | apply Step.store32Memory64 <;> omega
        | apply Step.load64Trap <;> first | rfl | omega
        | apply Step.load64 <;> first | rfl | omega
        | apply Step.store64Trap <;> first | rfl | omega
        | apply Step.store64 <;> first | rfl | omega
        | apply Step.f32LoadTrap <;> first | rfl | omega
        | apply Step.f32Load <;> first | rfl | omega
        | apply Step.f32StoreTrap <;> first | rfl | omega
        | apply Step.f32Store <;> first | rfl | omega
        | apply Step.f64LoadTrap <;> first | rfl | omega
        | apply Step.f64Load <;> first | rfl | omega
        | apply Step.f64StoreTrap <;> first | rfl | omega
        | apply Step.f64Store <;> first | rfl | omega
        | apply Step.load8UI64Trap <;> first | rfl | omega
        | apply Step.load8UI64 <;> first | rfl | omega
        | apply Step.load8SI64Trap <;> first | rfl | omega
        | apply Step.load8SI64 <;> first | rfl | omega
        | apply Step.load16UI64Trap <;> first | rfl | omega
        | apply Step.load16UI64 <;> first | rfl | omega
        | apply Step.load16SI64Trap <;> first | rfl | omega
        | apply Step.load16SI64 <;> first | rfl | omega
        | apply Step.load32UI64Trap <;> first | rfl | omega
        | apply Step.load32UI64 <;> first | rfl | omega
        | apply Step.load32SI64Trap <;> first | rfl | omega
        | apply Step.load32SI64 <;> first | rfl | omega
        | apply Step.store8I64Trap <;> first | rfl | omega
        | apply Step.store8I64 <;> first | rfl | omega
        | apply Step.store16I64Trap <;> first | rfl | omega
        | apply Step.store16I64 <;> first | rfl | omega
        | apply Step.store32I64Trap <;> first | rfl | omega
        | apply Step.store32I64 <;> first | rfl | omega
        | exact Step.memorySize
        | (apply Step.memoryGrowSuccess <;> assumption)
        | (apply Step.memoryGrowFailure <;> assumption)
        | (apply Step.memoryGrow64TooLarge <;> omega)
        | (apply Step.memoryGrow64Success <;> first | assumption | omega)
        | (apply Step.memoryGrow64Failure <;> first | assumption | omega)
        | (apply Step.memoryFill32Trap <;> omega)
        | (apply Step.memoryFill32 <;> omega)
        | (apply Step.memoryFill64Trap <;> omega)
        | (apply Step.memoryFill64 <;> omega)
        | (apply Step.memoryCopy32Trap <;> omega)
        | (apply Step.memoryCopy32 <;> omega)
        | (apply Step.memoryCopy64Trap <;> omega)
        | (apply Step.memoryCopy64 <;> omega)
        | (apply Step.memoryInit32DroppedTrap <;> first | assumption | omega)
        | (apply Step.memoryInit32Dropped <;> first | assumption | omega)
        | (apply Step.memoryInit32Trap <;> first | assumption | omega)
        | (apply Step.memoryInit32 <;> first | assumption | omega)
        | (apply Step.memoryInit64DroppedTrap <;> first | assumption | omega)
        | (apply Step.memoryInit64Dropped <;> first | assumption | omega)
        | (apply Step.memoryInit64Trap <;> first | assumption | omega)
        | (apply Step.memoryInit64 <;> first | assumption | omega)
        | (apply Step.dataDrop <;> simp_all)
        | (apply Step.gcFallthrough <;> assumption)
        | (apply Step.gcTrap <;> assumption)
        | (apply Step.gcBranch <;> assumption)
        | (apply Step.memoryCopyBetweenTrap <;>
            first | assumption | omega)
        | (apply Step.memoryCopyBetween <;>
            first | assumption | omega)
        | apply Step.localGet <;> simp_all [Locals.get]
        | apply Step.localSet <;> simp_all [Locals.set?]
        | apply Step.globalGet <;> simp_all
        | apply Step.globalSet <;> simp_all
        | (apply Step.divU; simp_all)
        | (apply Step.divS <;> simp_all)
        | (apply Step.remU <;> simp_all)
        | (apply Step.remS <;> simp_all)
        | (apply Step.divUI64 <;> simp_all)
        | (apply Step.divSI64 <;> simp_all)
        | (apply Step.remUI64 <;> simp_all)
        | (apply Step.remSI64 <;> simp_all)
        | exact Step.vConst
        | exact Step.vUnOp
        | exact Step.vBinOp
        | exact Step.vBitselect
        | exact Step.vTestOp
        | exact Step.vShiftOp
        | (apply Step.vSplat <;> assumption)
        | simpa using (Step.vExtractLane (α := α))
        | (apply Step.vReplaceLane <;> assumption)
        | exact Step.vShuffle
        | exact Step.vFma
        | exact Step.vDotAdd
        | (apply Step.v128LoadTrap <;> first | assumption | omega)
        | (apply Step.v128Load <;> first | assumption | omega)
        | (apply Step.v128StoreTrap <;> first | assumption | omega)
        | (apply Step.v128Store <;> first | assumption | omega)
        | (apply Step.v128LoadExtTrap <;> first | assumption | omega)
        | (apply Step.v128LoadExt <;> first | assumption | omega)
        | (apply Step.v128LoadSplatTrap <;> first | assumption | omega)
        | (apply Step.v128LoadSplat <;> first | assumption | omega)
        | (apply Step.v128LoadZeroTrap <;> first | assumption | omega)
        | (apply Step.v128LoadZero <;> first | assumption | omega)
        | (apply Step.v128LoadLaneTrap <;> first | assumption | omega)
        | (apply Step.v128LoadLane <;> first | assumption | omega)
        | (apply Step.v128StoreLaneTrap <;> first | assumption | omega)
        | (apply Step.v128StoreLane <;> first | assumption | omega)
        | solve
          | (apply Step.scalarFloat0 <;> simp_all [evalScalarFloat0?])
        | solve
          | (apply Step.scalarFloat1 <;>
              simp_all [evalScalarFloat0?, evalScalarFloat1?])
        | solve
          | (apply Step.scalarTruncSuccess <;>
              repeat' first | split at * | simp_all [evalScalarTrunc?])
        | solve
          | (apply Step.scalarTruncTrap <;>
              repeat' first | split at * | simp_all [evalScalarTrunc?])
        | solve
          | (apply Step.scalarFloat2 <;>
              simp_all [evalScalarFloat0?, evalScalarFloat1?,
                evalScalarFloat2?])
termination_by firstMemOpDepth config
decreasing_by
  subst_vars
  simp [firstMemOpDepth, isMemOp] <;> assumption

set_option maxHeartbeats 5000000 in
theorem stepChecked?_complete {config config' : Config α} {kind : StepKind} :
    Step config kind config' → stepChecked? config = .ok (some (kind, config')) :=
by
  intro h
  cases h
  case exitControl =>
    rename_i locals arity remainder frame controls calls store hkind
    cases controls with
    | nil =>
      cases hk : frame.kind <;>
        simp_all [stepChecked?, ControlKind.isThrowing]
    | cons handler outer =>
      cases hk : frame.kind <;>
        simp_all [stepChecked?, ControlKind.isThrowing]
  case unwindExceptionFrame =>
    rename_i locals arity remainder throwingFrame handler outer calls store
      tag arguments hthrow hhandler
    cases hh : handler.kind <;>
      simp_all [stepChecked?]
  case unwindNestedException =>
    simp_all [stepChecked?]
  case catchException =>
    simp_all [stepChecked?]
  case unwindExceptionCall => simp_all [stepChecked?]
  case uncaughtException => simp_all [stepChecked?]
  case tryTable => simp [stepChecked?]
  case throwI => simp_all [stepChecked?]
  case throwRefNull => simp [stepChecked?]
  case throwRef => simp_all [stepChecked?]
  case memOp =>
    rename_i inner store memoryIndex indexedStore locals arity remainder
      controls calls innerKind stepped rest hinner henter hstep
    have ih := stepChecked?_complete hstep
    have hplain :
        stepPlainChecked?
          ⟨.running
            { locals
              code := [inner]
              resultArity := arity
              callerRemainder := remainder
              control := controls
              calls },
            indexedStore⟩ =
          .ok (some (innerKind, stepped)) := by
      cases inner <;>
        simp_all only [stepChecked?, isMemOp, Bool.true_eq_false]
    simp only [stepChecked?, hinner, henter, hplain]
    rfl
  case scalarFloat0 => apply scalarFloat0_checked <;> assumption
  case scalarFloat1 => apply scalarFloat1_checked <;> assumption
  case scalarFloat2 => apply scalarFloat2_checked <;> assumption
  case scalarTruncSuccess instruction operand value params localValues values
      code arity remainder controls calls store hresult =>
    cases hi : instruction <;> cases ho : operand <;>
      simp_all [stepChecked?, evalScalarTrunc?]
  case scalarTruncTrap instruction operand reason params localValues values
      code arity remainder controls calls store hresult =>
    cases hi : instruction <;> cases ho : operand <;>
      simp_all [stepChecked?, evalScalarTrunc?]
  case vConst => simp [stepChecked?]
  case vUnOp => simp [stepChecked?]
  case vBinOp => simp [stepChecked?]
  case vBitselect => simp [stepChecked?]
  case vTestOp => simp [stepChecked?]
  case vShiftOp => simp [stepChecked?]
  case vSplat => simp_all [stepChecked?]
  case vExtractLane => simp [stepChecked?]
  case vReplaceLane => simp_all [stepChecked?]
  case vShuffle => simp [stepChecked?]
  case vFma => simp [stepChecked?]
  case vDotAdd => simp [stepChecked?]
  case v128LoadTrap => simp_all [stepChecked?]
  case v128Load => simp_all [stepChecked?]
  case v128StoreTrap => simp_all [stepChecked?]
  case v128Store => simp_all [stepChecked?]
  case v128LoadExtTrap => simp_all [stepChecked?]
  case v128LoadExt => simp_all [stepChecked?]
  case v128LoadSplatTrap => simp_all [stepChecked?]
  case v128LoadSplat => simp_all [stepChecked?]
  case v128LoadZeroTrap => simp_all [stepChecked?]
  case v128LoadZero => simp_all [stepChecked?]
  case v128LoadLaneTrap => simp_all [stepChecked?]
  case v128LoadLane => simp_all [stepChecked?]
  case v128StoreLaneTrap => simp_all [stepChecked?]
  case v128StoreLane => simp_all [stepChecked?]
  case brOnNullBranch => simp_all [stepChecked?]
  case brOnNullFallthrough => simp_all [stepChecked?]
  case brOnNonNullFallthrough => simp_all [stepChecked?]
  case brOnNonNullBranch => simp_all [stepChecked?]
  case gcFallthrough => simp_all [stepChecked?]
  case gcTrap => simp_all [stepChecked?]
  case gcBranch => simp_all [stepChecked?]
  case memoryCopyBetweenTrap => simp_all [stepChecked?]
  case memoryCopyBetween => simp_all [stepChecked?]
  case callHostReturn => simp_all [stepChecked?]
  case callHostTrap => simp_all [stepChecked?]
  case callHostThrow => simp_all [stepChecked?]
  case returnCallHostReturn => simp_all [stepChecked?]
  case returnCallHostTrap => simp_all [stepChecked?]
  case returnCallHostThrow => simp_all [stepChecked?]
  case callRefHostReturn => simp_all [stepChecked?]
  case callRefHostTrap => simp_all [stepChecked?]
  case callRefHostThrow => simp_all [stepChecked?]
  case returnCallRefHostReturn => simp_all [stepChecked?]
  case returnCallRefHostTrap => simp_all [stepChecked?]
  case returnCallRefHostThrow => simp_all [stepChecked?]
  case callIndirectHostTypeMismatch =>
    simp_all [stepChecked?, isForeignFunctionIndex] <;> omega
  case callIndirectHostReturn =>
    simp_all [stepChecked?, isForeignFunctionIndex] <;> omega
  case callIndirectHostTrap =>
    simp_all [stepChecked?, isForeignFunctionIndex] <;> omega
  case callIndirectHostThrow =>
    simp_all [stepChecked?, isForeignFunctionIndex] <;> omega
  case callIndirectForeignTypeMismatch =>
    simp_all [stepChecked?, Bool.and_eq_true]
  case callIndirectForeignReturn =>
    simp_all [stepChecked?, Bool.and_eq_true]
  case callIndirectForeignTrap =>
    simp_all [stepChecked?, Bool.and_eq_true]
  case callIndirectForeignThrow =>
    simp_all [stepChecked?, Bool.and_eq_true]
  case callIndirectCrossInstanceTypeMismatch =>
    simp_all [stepChecked?, isForeignFunctionIndex] <;> omega
  case callIndirectCrossInstance =>
    simp_all [stepChecked?, isForeignFunctionIndex] <;> omega
  case callIndirectTypeMismatch hselector htable helement himports
      hnotforeign hfn hsignature hexpected htype =>
    simp_all [stepChecked?]
  case callIndirect hselector htable helement himports
      hnotforeign hfn hsignature hexpected htype =>
    simp_all [stepChecked?]
  case returnCallIndirectHostTypeMismatch => simp_all [stepChecked?]
  case returnCallIndirectHostReturn => simp_all [stepChecked?]
  case returnCallIndirectHostTrap => simp_all [stepChecked?]
  case returnCallIndirectHostThrow => simp_all [stepChecked?]
  case callCrossInstance => simp_all [stepChecked?]
  case returnFromCallCrossInstanceFallthrough hdiff =>
    simp [stepChecked?, if_neg hdiff]
  case returnFromCallCrossInstanceExplicit hdiff =>
    simp [stepChecked?, if_neg hdiff]
  all_goals
    simp_all [stepChecked?, returnedValues, globalAt?, canonicalGlobalIndex,
      setGlobal, setMemory,
      setDataSegments, setTables, setElementSegments,
      Locals.get, Locals.set?] <;>
    omega

termination_by firstMemOpDepth config
decreasing_by
  subst_vars
  simp [firstMemOpDepth, isMemOp] <;> assumption

theorem step_iff {config config' : Config α} {kind : StepKind} :
    stepChecked? config = .ok (some (kind, config')) ↔ Step config kind config' :=
  ⟨stepChecked?_sound, stepChecked?_complete⟩

theorem step_deterministic {config next₁ next₂ : Config α} {kind₁ kind₂ : StepKind}
    (h₁ : Step config kind₁ next₁) (h₂ : Step config kind₂ next₂) :
    kind₁ = kind₂ ∧ next₁ = next₂ := by
  have e₁ := stepChecked?_complete h₁
  have e₂ := stepChecked?_complete h₂
  rw [e₁] at e₂
  exact Prod.mk.inj (Option.some.inj (Except.ok.inj e₂))

theorem done_terminal {values : List Value} {store : MachineStore α} {kind config'} :
    ¬ Step ⟨.done values, store⟩ kind config' := by
  intro h
  cases h

theorem trapped_terminal {reason : TrapReason} {store : MachineStore α} {kind config'} :
    ¬ Step ⟨.trapped reason, store⟩ kind config' := by
  intro h
  cases h

private theorem prepareCatch_runtime
    (tag : Nat) (arguments : List Value) (clause : CatchClause)
    (store : MachineStore α) :
    (prepareCatch tag arguments clause store).2.runtime = store.runtime := by
  cases clause <;> rfl

private theorem setMemoryAt_runtime
    (store : MachineStore α) (index : Nat) (memory : Mem) :
    (setMemoryAt store index memory).runtime = store.runtime := by
  dsimp only [setMemoryAt]
  split <;> rfl

private theorem resumeAfterIndexedMemory_runtime
    (rest : Program) (original : MachineStore α) (index : Nat)
    (config : Config α) :
    (resumeAfterIndexedMemory rest original index config).store.runtime =
      original.runtime := by
  simp [resumeAfterIndexedMemory, leaveIndexedMemory, setMemoryAt_runtime]

theorem instances_preserved {config config' : Config α} {kind}
    (h : Step config kind config') :
    config'.store.runtime.instances = config.store.runtime.instances := by
  cases h <;> try rfl
  case catchException => simp [prepareCatch_runtime]
  case memoryCopyBetween => simp [setMemoryAt_runtime]
  case memOp => simp [resumeAfterIndexedMemory_runtime]

theorem runtime_preserved {config config' : Config α} {kind}
    (h : Step config kind config')
    (hnot : kind ≠ .administrative .returnFromCallCrossInstance)
    (hnot2 : kind ≠ .administrative .callCrossInstance) :
    config'.store.runtime = config.store.runtime := by
  cases h <;> try rfl
  case callCrossInstance => exact absurd rfl hnot2
  case callIndirectCrossInstance => exact absurd rfl hnot2
  case returnFromCallCrossInstanceFallthrough => exact absurd rfl hnot
  case returnFromCallCrossInstanceExplicit => exact absurd rfl hnot
  case catchException => apply prepareCatch_runtime
  case memoryCopyBetween => apply setMemoryAt_runtime
  case memOp => apply resumeAfterIndexedMemory_runtime

theorem memory_step_globals_preserved {config config' : Config α} {kind}
    (h : Step config kind config')
    (hk : (∃ offset, kind = .instruction (.load8U offset)) ∨
      (∃ offset, kind = .instruction (.store8 offset)) ∨
      (∃ offset, kind = .instruction (.load32 offset)) ∨
      (∃ offset, kind = .instruction (.store32 offset)) ∨
      kind = .instruction .memorySize ∨
      kind = .instruction .memoryGrow ∨
      kind = .instruction .memoryFill ∨
      kind = .instruction .memoryCopy ∨
      (∃ index, kind = .instruction (.memoryInit index)) ∨
      ∃ index, kind = .instruction (.dataDrop index)) :
    config'.store.wasm.globals = config.store.wasm.globals := by
  cases h <;> simp_all [setMemory, setDataSegments]

/-- Growing memory changes only the primary memory component. In particular,
resource arrays and host state retain their stable identities. -/
theorem memory_grow_store_frame {config config' : Config α}
    (h : Step config (.instruction .memoryGrow) config') :
    config'.store.wasm.globals = config.store.wasm.globals ∧
    config'.store.wasm.extraMems = config.store.wasm.extraMems ∧
    config'.store.wasm.dataSegments = config.store.wasm.dataSegments ∧
    config'.store.wasm.tables = config.store.wasm.tables ∧
    config'.store.wasm.elementSegments = config.store.wasm.elementSegments ∧
    config'.store.wasm.exns = config.store.wasm.exns ∧
    config'.store.wasm.gcHeap = config.store.wasm.gcHeap ∧
    config'.store.wasm.host = config.store.wasm.host := by
  cases h <;> simp_all [setMemory]

theorem memory_fill_store_frame {config config' : Config α}
    (h : Step config (.instruction .memoryFill) config') :
    config'.store.wasm.globals = config.store.wasm.globals ∧
    config'.store.wasm.extraMems = config.store.wasm.extraMems ∧
    config'.store.wasm.dataSegments = config.store.wasm.dataSegments ∧
    config'.store.wasm.tables = config.store.wasm.tables ∧
    config'.store.wasm.elementSegments = config.store.wasm.elementSegments ∧
    config'.store.wasm.exns = config.store.wasm.exns ∧
    config'.store.wasm.gcHeap = config.store.wasm.gcHeap ∧
    config'.store.wasm.host = config.store.wasm.host := by
  cases h <;> simp_all [setMemory]

theorem memory_copy_store_frame {config config' : Config α}
    (h : Step config (.instruction .memoryCopy) config') :
    config'.store.wasm.globals = config.store.wasm.globals ∧
    config'.store.wasm.extraMems = config.store.wasm.extraMems ∧
    config'.store.wasm.dataSegments = config.store.wasm.dataSegments ∧
    config'.store.wasm.tables = config.store.wasm.tables ∧
    config'.store.wasm.elementSegments = config.store.wasm.elementSegments ∧
    config'.store.wasm.exns = config.store.wasm.exns ∧
    config'.store.wasm.gcHeap = config.store.wasm.gcHeap ∧
    config'.store.wasm.host = config.store.wasm.host := by
  cases h <;> simp_all [setMemory]

theorem memory_init_store_frame {config config' : Config α} {segmentIndex}
    (h : Step config (.instruction (.memoryInit segmentIndex)) config') :
    config'.store.wasm.globals = config.store.wasm.globals ∧
    config'.store.wasm.extraMems = config.store.wasm.extraMems ∧
    config'.store.wasm.dataSegments = config.store.wasm.dataSegments ∧
    config'.store.wasm.tables = config.store.wasm.tables ∧
    config'.store.wasm.elementSegments = config.store.wasm.elementSegments ∧
    config'.store.wasm.exns = config.store.wasm.exns ∧
    config'.store.wasm.gcHeap = config.store.wasm.gcHeap ∧
    config'.store.wasm.host = config.store.wasm.host := by
  cases h <;> simp_all [setMemory]

theorem data_drop_memory_preserved {config config' : Config α} {segmentIndex}
    (h : Step config (.instruction (.dataDrop segmentIndex)) config') :
    config'.store.wasm.mem = config.store.wasm.mem := by
  cases h <;> rfl

/-- `data.drop` replaces one status entry without renumbering or resizing the
runtime segment registry. -/
theorem data_drop_segments_length_preserved
    {config config' : Config α} {segmentIndex}
    (h : Step config (.instruction (.dataDrop segmentIndex)) config') :
    config'.store.wasm.dataSegments.length =
      config.store.wasm.dataSegments.length := by
  cases h <;> simp_all [setDataSegments]

/-- Table instructions may replace table contents but frame every unrelated
runtime resource, including linear memories and host state. -/
theorem table_step_store_frame {config config' : Config α} {kind}
    (h : Step config kind config')
    (hk : (∃ index, kind = .instruction (.tableGet index)) ∨
      (∃ index, kind = .instruction (.tableSize index)) ∨
      (∃ index, kind = .instruction (.tableSet index)) ∨
      (∃ index, kind = .instruction (.tableGrow index)) ∨
      (∃ index, kind = .instruction (.tableFill index)) ∨
      (∃ destination source,
        kind = .instruction (.tableCopy destination source)) ∨
      ∃ tableIndex elementIndex,
        kind = .instruction (.tableInit tableIndex elementIndex)) :
    config'.store.wasm.globals = config.store.wasm.globals ∧
    config'.store.wasm.mem = config.store.wasm.mem ∧
    config'.store.wasm.extraMems = config.store.wasm.extraMems ∧
    config'.store.wasm.dataSegments = config.store.wasm.dataSegments ∧
    config'.store.wasm.elementSegments = config.store.wasm.elementSegments ∧
    config'.store.wasm.exns = config.store.wasm.exns ∧
    config'.store.wasm.gcHeap = config.store.wasm.gcHeap ∧
    config'.store.wasm.host = config.store.wasm.host := by
  cases h <;> simp_all [setTables]

/-- Dropping an element segment changes only the segment-status array. -/
theorem elem_drop_store_frame {config config' : Config α} {elementIndex}
    (h : Step config (.instruction (.elemDrop elementIndex)) config') :
    config'.store.wasm.globals = config.store.wasm.globals ∧
    config'.store.wasm.mem = config.store.wasm.mem ∧
    config'.store.wasm.extraMems = config.store.wasm.extraMems ∧
    config'.store.wasm.dataSegments = config.store.wasm.dataSegments ∧
    config'.store.wasm.tables = config.store.wasm.tables ∧
    config'.store.wasm.exns = config.store.wasm.exns ∧
    config'.store.wasm.gcHeap = config.store.wasm.gcHeap ∧
    config'.store.wasm.host = config.store.wasm.host := by
  cases h <;> simp_all [setElementSegments]

/-- Finite traces of the authoritative one-step relation. -/
inductive Steps : Config α → List StepKind → Config α → Prop where
  | refl (config) : Steps config [] config
  | cons (head : Step config kind next) (tail : Steps next trace final) :
      Steps config (kind :: trace) final

theorem Steps.single (step : Step config kind next) :
    Steps config [kind] next :=
  .cons step (.refl next)

theorem Steps.trans
    (first : Steps config trace₁ middle)
    (suffix : Steps middle trace₂ final) :
    Steps config (trace₁ ++ trace₂) final := by
  induction first with
  | refl => exact suffix
  | cons head tail ih => exact .cons head (ih suffix)

/-- A configuration is valid for the migrated machine when no state reachable
through the authoritative semantics can produce an internal checked-step
error. This invariant is deliberately semantic: decode/type validation will
eventually be proved to establish it for instantiated entry points. -/
def Config.Safe (config : Config α) : Prop :=
  ∀ {trace final}, Steps config trace final →
    ∃ result, stepChecked? final = .ok result

structure ValidConfig (α : Type) where
  config : Config α
  safe : config.Safe

instance : Coe (ValidConfig α) (Config α) := ⟨ValidConfig.config⟩

theorem Config.Safe.current {config : Config α} (h : config.Safe) :
    ∃ result, stepChecked? config = .ok result :=
  h (.refl config)

theorem Config.Safe.of_step {config next : Config α} {kind}
    (hsafe : config.Safe) (hstep : Step config kind next) :
    next.Safe := by
  intro trace final htrace
  exact hsafe (.cons hstep htrace)

theorem stepUnchecked?_eq_some_iff {config : Config α} {transition} :
    stepUnchecked? config = some transition ↔
      stepChecked? config = .ok (some transition) := by
  cases h : stepChecked? config with
  | error error => simp [stepUnchecked?, h]
  | ok result =>
    cases result <;> simp [stepUnchecked?, h]

/-- Error-free executable stepping for validated configurations. -/
def step? (valid : ValidConfig α) : Option (StepKind × ValidConfig α) :=
  match hs : stepUnchecked? valid.config with
  | none => none
  | some (kind, next) =>
      some (kind,
        ⟨next, Config.Safe.of_step valid.safe
          (stepChecked?_sound (stepUnchecked?_eq_some_iff.mp hs))⟩)

theorem step?_erase (valid : ValidConfig α) :
    (step? valid).map (fun transition =>
      (transition.1, transition.2.config)) =
      stepUnchecked? valid.config := by
  unfold step?
  split <;> simp_all

theorem step?_sound {valid : ValidConfig α} {kind} {next : ValidConfig α}
    (h : step? valid = some (kind, next)) :
    Step valid.config kind next.config := by
  have erased := step?_erase valid
  rw [h] at erased
  simp at erased
  exact stepChecked?_sound (stepUnchecked?_eq_some_iff.mp erased.symm)

theorem step?_complete {valid : ValidConfig α} {kind} {next : Config α}
    (h : Step valid.config kind next) :
    step? valid =
      some (kind, ⟨next, Config.Safe.of_step valid.safe h⟩) := by
  have hs : stepUnchecked? valid.config = some (kind, next) :=
    stepUnchecked?_eq_some_iff.mpr (stepChecked?_complete h)
  unfold step?
  split <;> simp_all

theorem done_safe (values : List Value) (store : MachineStore α) :
    Config.Safe ⟨.done values, store⟩ := by
  intro trace final htrace
  cases htrace with
  | refl => exact ⟨none, by simp [stepChecked?]⟩
  | cons head _ => exact False.elim (done_terminal head)

theorem trapped_safe (reason : TrapReason) (store : MachineStore α) :
    Config.Safe ⟨.trapped reason, store⟩ := by
  intro trace final htrace
  cases htrace with
  | refl => exact ⟨none, by simp [stepChecked?]⟩
  | cons head _ => exact False.elim (trapped_terminal head)

/-- Partial correctness for the small-step semantics. Traps and divergence do
not establish the postcondition. -/
def PartiallyMeets (initial : Config α)
    (post : List Value → MachineStore α → Prop) : Prop :=
  ∀ trace values store, Steps initial trace ⟨.done values, store⟩ → post values store

/-- Finite-trace total correctness, used to preserve termination results which
already have a concrete terminating execution argument. -/
def TerminatesWith (initial : Config α)
    (post : List Value → MachineStore α → Prop) : Prop :=
  ∃ trace values store, Steps initial trace ⟨.done values, store⟩ ∧ post values store

/-- Finite-trace trapping behavior.  Traps are terminal non-values, so they
have a separate specification rather than being folded into
`TerminatesWith`. -/
def TrapsWith (initial : Config α) (reason : TrapReason)
    (post : MachineStore α → Prop) : Prop :=
  ∃ trace store, Steps initial trace ⟨.trapped reason, store⟩ ∧ post store

/-- Package an explicit finite trapping execution and its postcondition. -/
theorem TrapsWith.of_steps
    (execution : Steps initial trace ⟨.trapped reason, store⟩)
    (hpost : post store) :
    TrapsWith initial reason post :=
  ⟨trace, store, execution, hpost⟩

/-- Strengthen the store postcondition of a trapping execution. -/
theorem TrapsWith.mono
    (h : TrapsWith initial reason post)
    (hpost : ∀ store, post store → post' store) :
    TrapsWith initial reason post' := by
  obtain ⟨trace, store, execution, hp⟩ := h
  exact ⟨trace, store, execution, hpost store hp⟩

/-- Prefix a trapping execution by an already-proved finite trace. -/
theorem TrapsWith.prependSteps
    (initialSteps : Steps initial trace middle)
    (suffix : TrapsWith middle reason post) :
    TrapsWith initial reason post := by
  obtain ⟨tail, store, execution, hp⟩ := suffix
  exact ⟨trace ++ tail, store, initialSteps.trans execution, hp⟩

/-- One-step specialization of `TrapsWith.prependSteps`. -/
theorem TrapsWith.prepend
    (head : Step initial kind next)
    (tail : TrapsWith next reason post) :
    TrapsWith initial reason post :=
  TrapsWith.prependSteps (.single head) tail

/-- Package an explicit finite execution and its postcondition. -/
theorem TerminatesWith.of_steps
    (execution : Steps initial trace ⟨.done values, store⟩)
    (hpost : post values store) :
    TerminatesWith initial post :=
  ⟨trace, values, store, execution, hpost⟩

/-- A normally terminal configuration terminates in the empty trace. -/
theorem TerminatesWith.done
    {values : List Value} {store : MachineStore α}
    (hpost : post values store) :
    TerminatesWith ⟨.done values, store⟩ post :=
  ⟨[], values, store, .refl _, hpost⟩

/-- Strengthen the postcondition of an existing terminating execution. -/
theorem TerminatesWith.mono
    (h : TerminatesWith initial post)
    (hpost : ∀ values store, post values store → post' values store) :
    TerminatesWith initial post' := by
  obtain ⟨trace, values, store, execution, hp⟩ := h
  exact ⟨trace, values, store, execution, hpost values store hp⟩

/-- Prefix a terminating execution by an already-proved finite trace. -/
theorem TerminatesWith.prependSteps
    (initialSteps : Steps initial trace middle)
    (suffix : TerminatesWith middle post) :
    TerminatesWith initial post := by
  obtain ⟨tail, values, store, execution, hp⟩ := suffix
  exact ⟨trace ++ tail, values, store, initialSteps.trans execution, hp⟩

/-- One-step specialization of `TerminatesWith.prependSteps`. -/
theorem TerminatesWith.prepend
    (head : Step initial kind next)
    (tail : TerminatesWith next post) :
    TerminatesWith initial post :=
  TerminatesWith.prependSteps (.single head) tail

/-- Combine an independently established finite terminating trace with partial
correctness.  This lets Iris proofs own semantic invariants while a separate
well-founded argument carries only termination. -/
theorem TerminatesWith.of_termination_and_partial
    (termination : TerminatesWith initial (fun _ _ => True))
    (correctness : PartiallyMeets initial post) :
    TerminatesWith initial post := by
  obtain ⟨trace, values, store, execution, _⟩ := termination
  exact ⟨trace, values, store, execution, correctness trace values store execution⟩

def initConfig (instance_ : ModuleInstance α) (entry : Nat) (initial : Store α)
    (params : List Value) : Except InternalError (Config α) :=
  let runtime : RuntimeEnv α := { instances := #[instance_], entry := ⟨0⟩ }
  if entry < instance_.module.imports.length then
    match instance_.module.imports[entry]?, instance_.host.funcs[entry]? with
    | some imp, some _ =>
      let callerRemainder := params.drop imp.params.length
      .ok ⟨.running
        { locals := { values := params.take imp.params.length }
          code := [.call entry]
          resultArity := imp.results.length
          callerRemainder },
        { runtime, wasm := initial }⟩
    | _, _ => .error ⟨s!"unresolved host function: index {entry}"⟩
  else
    match instance_.module.funcs[entry - instance_.module.imports.length]? with
    | none => .error ⟨s!"function index {entry} is invalid"⟩
    | some fn =>
      let callerRemainder := params.drop fn.numParams
      let locals := fn.toLocals (params.take fn.numParams).reverse
      .ok ⟨.running
        { locals, code := fn.body, resultArity := fn.results.length, callerRemainder },
        { runtime, wasm := initial }⟩

-- add a new module instance with explicit resolved imports to an existing config
def instantiate (config : Config α) (newModule : Module)
    (hostEnv : HostEnv α)
    (resolvedImports : Array (ResolvedImport α)) :
    Except InternalError (Config α × ModuleInstanceId) :=
  let newInstanceId : ModuleInstanceId := ⟨config.store.runtime.instances.size⟩
  let newInstance : ModuleInstance α :=
    { module := newModule, host := hostEnv, resolvedImports }
  let newRuntime : RuntimeEnv α :=
    { config.store.runtime with
      instances := config.store.runtime.instances.push newInstance }
  .ok (⟨config.expr, { config.store with runtime := newRuntime }⟩, newInstanceId)

-- single-module entry point; resolves all imports as host functions
def initSingleModuleConfig (m : Module) (hostEnv : HostEnv α)
    (entry : Nat) (initial : Store α) (params : List Value) :
    Except InternalError (Config α) :=
  let resolvedImports := hostEnv.funcs.toArray.map .host
  initConfig { module := m, host := hostEnv, resolvedImports } entry initial params

inductive RunnerResult (α : Type) where
  | success (values : List Value) (store : MachineStore α)
  | trapped (reason : TrapReason) (store : MachineStore α)
  | outOfFuel (config : Config α)
  | internalError (error : InternalError) (config : Config α)

def RunnerResult.values? : RunnerResult α → Option (List Value)
  | .success values _ => some values
  | _ => none

def RunnerResult.trapReason? : RunnerResult α → Option TrapReason
  | .trapped reason _ => some reason
  | _ => none

def RunnerResult.finalConfig? : RunnerResult α → Option (Config α)
  | .success values store => some ⟨.done values, store⟩
  | .trapped reason store => some ⟨.trapped reason, store⟩
  | .outOfFuel config => some config
  | .internalError _ _ => none

structure TraceResult (α : Type) where
  trace : List StepKind
  result : RunnerResult α

def runSteps : Nat → Config α → TraceResult α
  | 0, config =>
    match config.expr with
    | .done values => ⟨[], .success values config.store⟩
    | .trapped reason => ⟨[], .trapped reason config.store⟩
    | .running _ => ⟨[], .outOfFuel config⟩
  | fuel + 1, config =>
    match config.expr with
    | .done values => ⟨[], .success values config.store⟩
    | .trapped reason => ⟨[], .trapped reason config.store⟩
    | .running _ =>
      match stepChecked? config with
      | .error error => ⟨[], .internalError error config⟩
      | .ok none => ⟨[], .internalError ⟨"running configuration has no successor"⟩ config⟩
      | .ok (some (kind, next)) =>
        let tail := runSteps fuel next
        ⟨kind :: tail.trace, tail.result⟩

/-- A relational trace is executable with exactly one unit of fuel per
transition. At a nonterminal endpoint, exhausting exactly that fuel returns
the endpoint as `outOfFuel`; terminal endpoints retain their terminal result.
-/
theorem runSteps_finalConfig_of_steps
    {config final : Config α} {trace : List StepKind}
    (h : Steps config trace final) :
    (runSteps trace.length config).result =
      match final.expr with
      | .done values => .success values final.store
      | .trapped reason => .trapped reason final.store
      | .running _ => .outOfFuel final := by
  induction h with
  | refl config =>
    rcases config with ⟨expr, store⟩
    cases expr <;> rfl
  | @cons config kind next trace final head _ ih =>
    rcases config with ⟨expr, store⟩
    cases expr with
    | done values => exact False.elim (done_terminal head)
    | trapped reason => exact False.elim (trapped_terminal head)
    | running thread =>
      simp [runSteps, stepChecked?_complete head, ih]

/-- A relational trace to normal completion is executable with exactly one
unit of fuel per transition. This is the symbolic counterpart of proving a
closed `runSteps` computation by reduction and keeps clients independent of
the private checked-step implementation. -/
theorem runSteps_eq_success_of_steps
    {config : Config α} {trace : List StepKind}
    {values : List Value} {store : MachineStore α}
    (h : Steps config trace ⟨.done values, store⟩) :
    (runSteps trace.length config).result = .success values store := by
  exact runSteps_finalConfig_of_steps h

theorem runSteps_sound {fuel : Nat} {config final : Config α}
    (h : (runSteps fuel config).result.finalConfig? = some final) :
    Steps config (runSteps fuel config).trace final := by
  induction fuel generalizing config final with
  | zero =>
    rcases config with ⟨expr, store⟩
    cases expr <;> simp_all [runSteps, RunnerResult.finalConfig?]
    all_goals subst final
    all_goals exact .refl _
  | succ fuel ih =>
    rcases config with ⟨expr, store⟩
    cases expr with
    | done =>
      simp_all [runSteps, RunnerResult.finalConfig?]
      exact .refl _
    | trapped =>
      simp_all [runSteps, RunnerResult.finalConfig?]
      exact .refl _
    | running thread =>
      let config : Config α := ⟨.running thread, store⟩
      cases hs : stepChecked? config with
      | error error => simp [runSteps, config, hs, RunnerResult.finalConfig?] at h
      | ok result =>
        cases result with
        | none => simp [runSteps, config, hs, RunnerResult.finalConfig?] at h
        | some transition =>
          rcases transition with ⟨kind, next⟩
          have head : Step config kind next := stepChecked?_sound hs
          have tail : Steps next (runSteps fuel next).trace final := by
            apply ih
            simpa [runSteps, config, hs] using h
          simpa [runSteps, config, hs] using Steps.cons head tail

theorem runSteps_success_terminates {fuel : Nat} {config : Config α}
    {values : List Value} {store : MachineStore α}
    (h : (runSteps fuel config).result = .success values store)
    (post : List Value → MachineStore α → Prop)
    (hp : post values store) :
    TerminatesWith config post := by
  refine ⟨(runSteps fuel config).trace, values, store, ?_, hp⟩
  apply runSteps_sound
  simp [h, RunnerResult.finalConfig?]

/-- A state-sensitive executable check yields a fuel-free relational
termination theorem. The fuel remains confined to the proof, while `post`
may inspect both returned values and the reached machine store. -/
theorem runSteps_result_terminates {fuel : Nat} {config : Config α}
    {post : List Value → MachineStore α → Prop}
    (h :
      match (runSteps fuel config).result with
      | .success values store => post values store
      | .trapped _ _ | .outOfFuel _ | .internalError _ _ => False) :
    TerminatesWith config post := by
  cases hr : (runSteps fuel config).result with
  | success values store =>
      apply runSteps_success_terminates hr post
      simpa [hr] using h
  | trapped reason store =>
      simp [hr] at h
  | outOfFuel final =>
      simp [hr] at h
  | internalError error final =>
      simp [hr] at h

/-- Boolean-checking variant of `runSteps_result_terminates`. This is useful
for `native_decide` regression witnesses: the outer proposition is always a
decidable equality even when Lean cannot synthesize `Decidable (post v σ)`
under an opaque runner-result match. -/
theorem runSteps_checked_terminates {fuel : Nat} {config : Config α}
    (check : List Value → MachineStore α → Bool)
    {post : List Value → MachineStore α → Prop}
    (h :
      (match (runSteps fuel config).result with
      | .success values store => check values store
      | .trapped _ _ | .outOfFuel _ | .internalError _ _ => false) = true)
    (hcheck : ∀ values store, check values store = true → post values store) :
    TerminatesWith config post := by
  cases hr : (runSteps fuel config).result with
  | success values store =>
      apply runSteps_success_terminates hr post
      apply hcheck
      simpa [hr] using h
  | trapped reason store =>
      simp [hr] at h
  | outOfFuel final =>
      simp [hr] at h
  | internalError error final =>
      simp [hr] at h

/-- A trapped runner result yields a fuel-free relational trap
specification. -/
theorem runSteps_trapped_trapsWith {fuel : Nat} {config : Config α}
    {reason : TrapReason} {store : MachineStore α}
    (h : (runSteps fuel config).result = .trapped reason store)
    (post : MachineStore α → Prop)
    (hp : post store) :
    TrapsWith config reason post := by
  refine ⟨(runSteps fuel config).trace, store, ?_, hp⟩
  apply runSteps_sound
  simp [h, RunnerResult.finalConfig?]

/-- A projected structured trap reason is enough to obtain fuel-free
relational trapping, even when the host-parametric store has no decidable
equality. -/
theorem runSteps_trapReason_trapsWith {fuel : Nat} {config : Config α}
    {reason : TrapReason}
    (h : (runSteps fuel config).result.trapReason? = some reason) :
    TrapsWith config reason (fun _ => True) := by
  cases hr : (runSteps fuel config).result with
  | success values store =>
    simp [RunnerResult.trapReason?, hr] at h
  | trapped actual store =>
    have : actual = reason := by
      simpa [RunnerResult.trapReason?, hr] using h
    subst actual
    apply runSteps_trapped_trapsWith hr
    trivial
  | outOfFuel final =>
    simp [RunnerResult.trapReason?, hr] at h
  | internalError error final =>
    simp [RunnerResult.trapReason?, hr] at h

/-- A successful value projection is sufficient for a fuel-free relational
termination result when the client postcondition depends only on values. This
is useful for decoded configurations whose runtime host fields intentionally
do not have propositional equality instances. -/
theorem runSteps_values_terminates {fuel : Nat} {config : Config α}
    {values : List Value}
    (h : (runSteps fuel config).result.values? = some values) :
    TerminatesWith config (fun actual _ => actual = values) := by
  cases hr : (runSteps fuel config).result with
  | success actual store =>
    have : actual = values := by
      simpa [RunnerResult.values?, hr] using h
    subst actual
    apply runSteps_success_terminates hr
    rfl
  | trapped | outOfFuel | internalError =>
    simp [RunnerResult.values?, hr] at h

theorem steps_irreducible_deterministic
    {config final₁ final₂ : Config α} {trace₁ trace₂ : List StepKind}
    (h₁ : Steps config trace₁ final₁)
    (h₂ : Steps config trace₂ final₂)
    (hirr₁ : ∀ kind next, ¬ Step final₁ kind next)
    (hirr₂ : ∀ kind next, ¬ Step final₂ kind next) :
    final₁ = final₂ := by
  induction h₁ generalizing trace₂ final₂ with
  | refl =>
    cases h₂ with
    | refl => rfl
    | cons head _ => exact False.elim (hirr₁ _ _ head)
  | cons head₁ tail₁ ih =>
    cases h₂ with
    | refl => exact False.elim (hirr₂ _ _ head₁)
    | cons head₂ tail₂ =>
      obtain ⟨rfl, rfl⟩ := step_deterministic head₁ head₂
      exact ih tail₂ hirr₁ hirr₂

theorem steps_done_deterministic
    {config : Config α} {trace₁ trace₂ : List StepKind}
    {values₁ values₂ : List Value} {store₁ store₂ : MachineStore α}
    (h₁ : Steps config trace₁ ⟨.done values₁, store₁⟩)
    (h₂ : Steps config trace₂ ⟨.done values₂, store₂⟩) :
    values₁ = values₂ ∧ store₁ = store₂ := by
  have hconfig := steps_irreducible_deterministic h₁ h₂
    (fun _ _ => done_terminal) (fun _ _ => done_terminal)
  have parts := Config.mk.inj hconfig
  exact ⟨Expr.done.inj parts.1, parts.2⟩

/-- Determinism rules out a normally completed and a trapped terminal trace
from the same initial machine. -/
theorem steps_done_ne_trapped
    {config : Config α} {doneTrace trapTrace : List StepKind}
    {values : List Value} {doneStore trapStore : MachineStore α}
    {reason : TrapReason}
    (doneSteps : Steps config doneTrace ⟨.done values, doneStore⟩)
    (trapSteps : Steps config trapTrace ⟨.trapped reason, trapStore⟩) :
    False := by
  have hconfig := steps_irreducible_deterministic doneSteps trapSteps
    (fun _ _ => done_terminal) (fun _ _ => trapped_terminal)
  cases hconfig

/-- A deterministic initial machine cannot satisfy both a normal-termination
and a trapping specification. -/
theorem TerminatesWith.not_trapsWith
    (done : TerminatesWith initial donePost)
    (trapped : TrapsWith initial reason trapPost) :
    False := by
  obtain ⟨doneTrace, values, doneStore, doneSteps, _⟩ := done
  obtain ⟨trapTrace, trapStore, trapSteps, _⟩ := trapped
  exact steps_done_ne_trapped doneSteps trapSteps

theorem steps_comparable
    {config final₁ final₂ : Config α} {trace₁ trace₂ : List StepKind}
    (h₁ : Steps config trace₁ final₁)
    (h₂ : Steps config trace₂ final₂) :
    (∃ suffix, Steps final₁ suffix final₂) ∨
      ∃ suffix, Steps final₂ suffix final₁ := by
  induction h₁ generalizing trace₂ final₂ with
  | refl => exact .inl ⟨trace₂, h₂⟩
  | cons head₁ tail₁ ih =>
    cases h₂ with
    | refl => exact .inr ⟨_, .cons head₁ tail₁⟩
    | cons head₂ tail₂ =>
      obtain ⟨rfl, rfl⟩ := step_deterministic head₁ head₂
      exact ih tail₂

theorem checked_ok_of_steps_to_done
    {config : Config α} {trace : List StepKind}
    {values : List Value} {store : MachineStore α}
    (h : Steps config trace ⟨.done values, store⟩) :
    ∃ result, stepChecked? config = .ok result := by
  cases h with
  | refl => exact ⟨none, by simp [stepChecked?]⟩
  | cons head _ => exact ⟨some (_, _), stepChecked?_complete head⟩

theorem steps_from_done_eq
    {values : List Value} {store : MachineStore α}
    {trace : List StepKind} {final : Config α}
    (h : Steps ⟨.done values, store⟩ trace final) :
    final = ⟨.done values, store⟩ := by
  cases h with
  | refl => rfl
  | cons head _ => exact False.elim (done_terminal head)

theorem safe_of_steps_to_done
    {config : Config α} {trace : List StepKind}
    {values : List Value} {store : MachineStore α}
    (execution : Steps config trace ⟨.done values, store⟩) :
    config.Safe := by
  intro reachedTrace final reached
  rcases steps_comparable execution reached with towardFinal | towardDone
  · obtain ⟨suffix, hterminal⟩ := towardFinal
    have : final = ⟨.done values, store⟩ := steps_from_done_eq hterminal
    subst final
    exact ⟨none, by simp [stepChecked?]⟩
  · obtain ⟨suffix, hdone⟩ := towardDone
    exact checked_ok_of_steps_to_done hdone

theorem runSteps_success_partiallyMeets {fuel : Nat} {config : Config α}
    {values : List Value} {store : MachineStore α}
    (h : (runSteps fuel config).result = .success values store)
    (post : List Value → MachineStore α → Prop)
    (hp : post values store) :
    PartiallyMeets config post := by
  intro trace values' store' htrace
  have executed : Steps config (runSteps fuel config).trace ⟨.done values, store⟩ := by
    apply runSteps_sound
    simp [h, RunnerResult.finalConfig?]
  obtain ⟨rfl, rfl⟩ := steps_done_deterministic executed htrace
  exact hp

/-- Partial-correctness companion to `runSteps_values_terminates`. -/
theorem runSteps_values_partiallyMeets {fuel : Nat} {config : Config α}
    {values : List Value}
    (h : (runSteps fuel config).result.values? = some values) :
    PartiallyMeets config (fun actual _ => actual = values) := by
  cases hr : (runSteps fuel config).result with
  | success actual store =>
    have : actual = values := by
      simpa [RunnerResult.values?, hr] using h
    subst actual
    apply runSteps_success_partiallyMeets hr
    rfl
  | trapped | outOfFuel | internalError =>
    simp [RunnerResult.values?, hr] at h

theorem safe_of_runSteps_success {fuel : Nat} {config : Config α}
    {values : List Value} {store : MachineStore α}
    (h : (runSteps fuel config).result = .success values store) :
    config.Safe := by
  apply safe_of_steps_to_done
  apply runSteps_sound (fuel := fuel)
  rw [h]
  rfl

end SmallStep
end Wasm
