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

end SmallStep
end Wasm
