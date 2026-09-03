import Project.GcdStdio.Spec
import Project.Mergesort.Contracts

/-!
# Contracts for the generated GCD stream wrapper

The generated program has a deliberately small reachable call graph.  These
contracts use the same continuation-passing shape as the merge-sort example,
but specialize allocation to the single sixteen-byte input buffer requested by
the driver.
-/

namespace Project.GcdStdio.Contracts

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open scoped Wasm.SmallStep.Outcome

abbrev HeapIProp := IProp (WasmHeapGF Universal.State)

abbrev callExpr := Project.Mergesort.Contracts.callExpr
abbrev resumeExpr := Project.Mergesort.Contracts.resumeExpr

def ResumeWP [WasmSmallStepGS hlc Universal.State]
    (results : List Value)
    (callerLocals : Locals) (stack : List Value)
    (code : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (s : Stuckness) (E : CoPset)
    (Phi : ObservableOutcome → HeapIProp) : HeapIProp :=
  WP (resumeExpr results callerLocals stack code arity remainder controls calls)
    @ s; E [{ Phi }]

def CallContract [WasmSmallStepGS hlc Universal.State]
    (absoluteIndex : Nat) (operands : List Value)
    (callerLocals : Locals) (stack : List Value)
    (code : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (s : Stuckness) (E : CoPset)
    (Phi : ObservableOutcome → HeapIProp)
    (resources : HeapIProp) : Prop :=
  resources ⊢ WP (callExpr absoluteIndex operands callerLocals stack code arity
    remainder controls calls) @ s; E [{ Phi }]

def ByteSlice [WasmHeapGS Universal.State]
    (base : UInt32) (bytes : List UInt8) : HeapIProp :=
  Project.Mergesort.Representations.ByteSlice base bytes

def Streams [WasmHostStateGS Universal.State]
    (input output : List UInt8) (raised : Bool) : HeapIProp :=
  Project.Mergesort.Representations.Streams input output raised

def RuntimeContext [WasmSmallStepGS hlc Universal.State] : HeapIProp := iprop(
  runtimeModuleOwn ⟨0⟩ Project.GcdStdio.module ∗
  hostEnvOwn 0 (Universal.envFor Project.GcdStdio.module))

def StackPointer [WasmGlobalGS Universal.State] (value : UInt32) : HeapIProp :=
  globalPointsToAt 0 0 (.i32 value)

def entryStackTop : UInt32 := 1048576
def entryStackLow : UInt32 := 1048560
def allocatorCursor : UInt32 := 1048576
def heapBase : UInt32 := 1048592
def allocatedFinish : UInt32 := 1048608

def KernelContinuation [WasmSmallStepGS hlc Universal.State]
    (a b : UInt64)
    (callerLocals : Locals) (stack : List Value)
    (code : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (s : Stuckness) (E : CoPset)
    (Phi : ObservableOutcome → HeapIProp) : HeapIProp := iprop(
  RuntimeContext -∗
  ResumeWP [.i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))]
    callerLocals stack code arity remainder controls calls s E Phi)

/-- Local `func1`, absolute index 4: the register-only `num-integer` kernel. -/
def Func1Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (a b : UInt64)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Phi : ObservableOutcome → HeapIProp},
    CallContract 4 [.i64 b, .i64 a]
      callerLocals stack code arity remainder controls calls s E Phi iprop(
        RuntimeContext ∗
        KernelContinuation a b callerLocals stack code arity remainder
          controls calls s E Phi)

def readContractAt [WasmSmallStepGS hlc Universal.State]
    (absoluteIndex : Nat)
    (operands : UInt32 → UInt32 → List Value) : Prop :=
  ∀ (ptr requested : UInt32) (buffer input output : List UInt8)
    (raised : Bool)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Phi : ObservableOutcome → HeapIProp},
    let count := min requested.toNat input.length
    CallContract absoluteIndex (operands ptr requested)
      callerLocals stack code arity remainder controls calls s E Phi iprop(
        RuntimeContext ∗ Streams input output raised ∗ ByteSlice ptr buffer ∗
        ⌜requested.toNat = buffer.length ∧ 0 < requested.toNat⌝ ∗
        (RuntimeContext -∗ Streams (input.drop count) output raised -∗
          ByteSlice ptr (input.take count ++ buffer.drop count) -∗
          ⌜count ≤ requested.toNat⌝ -∗
          ResumeWP [.i32 (UInt32.ofNat count)] callerLocals stack code arity
            remainder controls calls s E Phi))

def writeContractAt [WasmSmallStepGS hlc Universal.State]
    (absoluteIndex : Nat)
    (operands : UInt32 → UInt32 → List Value) : Prop :=
  ∀ (ptr requested : UInt32) (bytes input output : List UInt8)
    (raised : Bool)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Phi : ObservableOutcome → HeapIProp},
    CallContract absoluteIndex (operands ptr requested)
      callerLocals stack code arity remainder controls calls s E Phi iprop(
        RuntimeContext ∗ Streams input output raised ∗ ByteSlice ptr bytes ∗
        ⌜requested.toNat = bytes.length ∧ 0 < requested.toNat⌝ ∗
        (RuntimeContext -∗ Streams input (output ++ bytes) raised -∗
          ByteSlice ptr bytes -∗
          ResumeWP [] callerLocals stack code arity remainder controls calls
            s E Phi))

def Import0Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  readContractAt (hlc := hlc) 0
    (fun ptr requested => [.i32 ptr, .i32 requested])

def Import1Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  writeContractAt (hlc := hlc) 1
    (fun ptr requested => [.i32 ptr, .i32 requested])

/-- Local `func7`, absolute index 10: the generated read shim. -/
def Func7Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  readContractAt (hlc := hlc) 10
    (fun ptr requested => [.i32 requested, .i32 ptr])

/-- Local `func8`, absolute index 11: the generated write shim. -/
def Func8Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  writeContractAt (hlc := hlc) 11
    (fun ptr requested => [.i32 requested, .i32 ptr])

end Project.GcdStdio.Contracts
