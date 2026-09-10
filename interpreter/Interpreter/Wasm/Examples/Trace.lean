import Interpreter.Wasm.Trace
import Interpreter.Wasm.Examples.GlobalCounter
import Interpreter.Wasm.Examples.MemReplace
import Interpreter.Wasm.Examples.EvenOddRec
import Interpreter.Wasm.Examples.TrapDivZero
import Interpreter.Wasm.Examples.InfiniteLoop

/-! ## Traceability regression examples

These executable checks cover aggregation and ordering independently of the
semantic proofs in the source examples.  They exercise globals, locals,
memory, recursive function entry/exit, a trap, and an out-of-fuel prefix.
-/

namespace Wasm
namespace SmallStep

def tickObserved : TracedRun Unit :=
  runTraced 6 0 (tickConfig tickInitialStore)

example : tickObserved.summary.instructions = 5 := by native_decide
example : tickObserved.summary.instructionCount "globalGet" = 2 := by native_decide
example : tickObserved.summary.instructionCount "globalSet" = 1 := by native_decide
example : tickObserved.summary.globalReads = 2 := by native_decide
example : tickObserved.summary.globalWrites = 1 := by native_decide
example : tickObserved.summary.functionEntryCount "0:0" = 1 := by native_decide
example : tickObserved.summary.functionExits = 1 := by native_decide

def replaceObserved : TracedRun Unit :=
  runTraced 8 0 (replaceConfig replaceModule.initialStore 99)

example : replaceObserved.summary.instructionCount "load32" = 1 := by native_decide
example : replaceObserved.summary.instructionCount "store32" = 1 := by native_decide
example : replaceObserved.summary.localReads = 2 := by native_decide
example : replaceObserved.summary.localWrites = 1 := by native_decide
example : replaceObserved.summary.memoryLoads = 1 := by native_decide
example : replaceObserved.summary.memoryStores = 1 := by native_decide

def memoryPattern : List TraceEvent → List (MemoryAccessKind × Option Nat × Option Nat)
  | [] => []
  | .memory _ _ kind _ _ address _ _ byteCount _ _ :: rest =>
      (kind, address, byteCount) :: memoryPattern rest
  | _ :: rest => memoryPattern rest

example : memoryPattern replaceObserved.events =
    [(.load, some 0, some 4), (.store, some 0, some 4)] := by native_decide

def enteredFunctions : List TraceEvent → List Nat
  | [] => []
  | .functionEnter _ invocation _ _ false :: rest =>
      invocation.function.functionIndex :: enteredFunctions rest
  | _ :: rest => enteredFunctions rest

def exitedFunctions : List TraceEvent → List Nat
  | [] => []
  | .functionExit _ invocation _ _ :: rest =>
      invocation.function.functionIndex :: exitedFunctions rest
  | _ :: rest => exitedFunctions rest

def parityObserved : TracedRun Unit := runTraced 100 0 (evenConfig 3)

example : enteredFunctions parityObserved.events = [0, 1, 0, 1] := by native_decide
example : exitedFunctions parityObserved.events = [1, 0, 1, 0] := by native_decide
example : parityObserved.summary.functionEntryCount "0:0" = 2 := by native_decide
example : parityObserved.summary.functionEntryCount "0:1" = 2 := by native_decide

def trappedObserved : TracedRun Unit := runTraced 3 0 (trapDivZeroConfig 7 0)

def endedWithTrap : List TraceEvent → Bool
  | [] => false
  | .runEnd _ (.trapped .integerDivideByZero) :: _ => true
  | _ :: rest => endedWithTrap rest

example : trappedObserved.summary.instructions = 3 := by native_decide
example : endedWithTrap trappedObserved.events = true := by native_decide

def infiniteModule : Module := { funcs := [{ body := InfiniteLoop }] }
def infiniteObserved : TracedRun Unit :=
  runTraced 5 0 (infiniteOuterConfig infiniteModule infiniteModule.initialStore {})

def endedOutOfFuel : List TraceEvent → Bool
  | [] => false
  | .runEnd _ .outOfFuel :: _ => true
  | _ :: rest => endedOutOfFuel rest

example : infiniteObserved.summary.transitions = 5 := by native_decide
example : infiniteObserved.summary.instructions = 5 := by native_decide
example : endedOutOfFuel infiniteObserved.events = true := by native_decide


/-! Nested exits must describe the callee, including its outcome and only its
own declared results, even when the caller has other operands on its stack. -/

private def observeModule (m : Module) : List TraceEvent :=
  match initConfig { module := m, host := ({} : HostEnv Unit) } 0 m.initialStore [] with
  | .ok config => (runTraced 30 0 config).events
  | .error _ => []

private def exitRecords : List TraceEvent → List (Nat × String × List Value)
  | [] => []
  | .functionExit _ invocation outcome results :: rest =>
      let label := match outcome with
        | .returned => "returned"
        | .trapped reason => "trapped: " ++ reason.message
        | .threw tag _ => s!"threw: {tag}"
        | .tailCall => "tail_call"
        | .internalError _ => "internal_error"
      (invocation.function.functionIndex, label, results) :: exitRecords rest
  | _ :: rest => exitRecords rest

example : exitRecords (observeModule
    { funcs := [{ body := [.call 1] }, { body := [.call 2] },
                { body := [.unreachable] }] }) =
    [(2, "trapped: unreachable", []), (1, "trapped: unreachable", []),
     (0, "trapped: unreachable", [])] := by native_decide

example : exitRecords (observeModule
    { funcs :=
        [{ body := [.const 99, .call 1, .drop, .drop], results := [.i32] },
         { body := [.const 7, .const 8], results := [.i32, .i32] }] }) =
    [(1, "returned", [.i32 8, .i32 7]), (0, "returned", [.i32 99])] := by native_decide

example : exitRecords (observeModule
    { funcs := [{ body := [.call 1], results := [.i32] },
                { body := [.const 7, .ret, .const 8], results := [.i32] }] }) =
    [(1, "returned", [.i32 7]), (0, "returned", [.i32 7])] := by native_decide

example : (exitRecords (observeModule
    { tags := [{ params := [.i32] }]
      funcs := [{ body := [.call 1] }, { body := [.const 7, .throwI 0] }] })).take 1 =
    [(1, "threw: 0", [])] := by native_decide

end SmallStep
end Wasm
