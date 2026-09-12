import Project.RustHashMap.Spec
import CodeLib.SepLogic.ByteSlice
import CodeLib.SepLogic.SmallStepOutcomeLanguage
import CodeLib.SepLogic.SmallStepTotalLifting

/-!
# Call contracts for the generated hash map module

This file states the call-site shapes that the body proofs of the generated
`rust_hash_map` module use.  It follows `Project.Mergesort.Contracts` and
`Project.Mergesort.Representations`, with three changes:

* the module is `Project.RustHashMap.«module»`;
* byte ownership is `Wasm.SepLogic.Slices.ByteSlice 0`, the reusable slice
  from `CodeLib.SepLogic.ByteSlice`, not a local copy;
* the physical constants are the ones of this module: the allocator cursor
  at `1049496`, the heap base at `1049568`.

The file contains contracts for the three imports and for the three
generated shims that call them: the OOM shim (local `func56`, absolute
index 59), the read shim (local `func60`, absolute 63), and the write shim
(local `func61`, absolute 64).  Contracts for the other generated functions
follow in later files.  A contract is an interface, not a body proof.

Local index `n` names `Project.RustHashMap.funcN`.  The absolute Wasm index is
`n + 3`, because the module has three imports.
-/

namespace Project.RustHashMap.Contracts

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open scoped Wasm.SmallStep.Outcome

abbrev HeapIProp := IProp (WasmHeapGF Universal.State)

/-! ## Physical layout of the module -/

/-- The static that holds the bump allocator's `next` pointer. -/
def allocatorCursor : UInt32 := 1049496

/-- `__heap_base`, the first address the bump allocator hands out. -/
def heapBase : UInt32 := 1049568

/-- The initial value of the shadow-stack pointer, mutable global zero. -/
def entryStackTop : UInt32 := 1048576

/-- The first of the three thread-local cells of `RandomState`: `k0` at
1049512, `k1` at 1049520, and the state byte at 1049528. -/
def randomStateCell : UInt32 := 1049512

/-- The size of the thread-local region.  It holds the two eight-byte
seeds, the state byte, and seven bytes of padding. -/
def randomStateSize : Nat := 24

/-- The size of the one data segment.  It starts at `entryStackTop` and
ends at `allocatorCursor`, so it is 1049496 minus 1048576 bytes.  It holds
the static strings and the `Location` records that the compiled error
paths pass by pointer. -/
def dataSegmentSize : Nat := 920

/-! ## Call-site shapes -/

/-- A call site with its top-of-stack operands already in machine order. -/
def callExpr (absoluteIndex : Nat) (operands : List Value)
    (callerLocals : Locals) (stack : List Value)
    (code : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame) :
    Expr Universal.State :=
  .running
    ⟨{ callerLocals with values := operands ++ stack },
      .call absoluteIndex :: code, arity, remainder, controls, calls⟩

/-- The caller state after a normal return, with result operands in machine
top-of-stack order. -/
def resumeExpr (results : List Value)
    (callerLocals : Locals) (stack : List Value)
    (code : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame) :
    Expr Universal.State :=
  .running
    ⟨{ callerLocals with values := results ++ stack },
      code, arity, remainder, controls, calls⟩

def ResumeWP [WasmSmallStepGS hlc Universal.State]
    (results : List Value)
    (callerLocals : Locals) (stack : List Value)
    (code : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (s : Stuckness) (E : CoPset)
    (Φ : ObservableOutcome → HeapIProp) : HeapIProp :=
  WP (resumeExpr results callerLocals stack code arity remainder controls calls)
    @ s; E [{ Φ }]

def CallContract [WasmSmallStepGS hlc Universal.State]
    (absoluteIndex : Nat) (operands : List Value)
    (callerLocals : Locals) (stack : List Value)
    (code : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (s : Stuckness) (E : CoPset)
    (Φ : ObservableOutcome → HeapIProp)
    (resources : HeapIProp) : Prop :=
  resources ⊢ WP (callExpr absoluteIndex operands callerLocals stack code arity
    remainder controls calls) @ s; E [{ Φ }]

/-! ## Host state and runtime identity -/

/-- Complete ownership of the Universal host state.  The unused random
component stays existential; both streams and the OOM marker are fixed. -/
def Streams [WasmHostStateGS Universal.State]
    (input output : List UInt8) (raised : Bool) : HeapIProp :=
  iprop(∃ random : Random.State,
    hostStateOwn
      ({ stdio := { input := input, output := output }
         random := random
         oom := { raised := raised } } : Universal.State))

/-- Runtime identity for a running expression.  It holds the exclusive
current-instance token: a normal return gives it back, a terminal host trap
consumes it.  No host state, global, heap, or stack ownership is hidden here. -/
def RuntimeContext [WasmRuntimeModuleGS Universal.State]
    [WasmInstanceGS Universal.State] [WasmHostEnvGS Universal.State] :
    HeapIProp :=
  iprop(runtimeModuleOwn ⟨0⟩ Project.RustHashMap.«module» ∗
    hostEnvOwn 0 (Universal.envFor Project.RustHashMap.«module»))

/-- Open the module and host-environment resources of a runtime context. -/
macro "iopen_map_runtime " runtime:ident " with " pattern:icasesPat : tactic => do
  let selected ← `(selPat| $runtime:ident)
  let resource ← `(pmTerm| $runtime:ident)
  `(tactic|
    (isimp only [Project.RustHashMap.Contracts.RuntimeContext] at $selected
     icases $resource with $pattern))

/-- Reassemble a runtime context from its two resources. -/
macro "iclose_map_runtime " runtime:ident " with " moduleOwn:ident hostEnv:ident : tactic => do
  let runtimePattern ← `(icasesPat| $runtime:ident)
  let moduleFrame ← `(frameIdent| $moduleOwn:ident)
  let hostFrame ← `(frameIdent| $hostEnv:ident)
  let moduleSelected ← `(selPat| $moduleOwn:ident)
  let hostSelected ← `(selPat| $hostEnv:ident)
  `(tactic|
    (ihave $runtimePattern : RuntimeContext $$ [$moduleFrame $hostFrame]
     · unfold RuntimeContext
       iframe $moduleSelected $hostSelected))

/-! ## The stdio contract shapes -/

/-- A call that reads at most `requested` bytes into the buffer at `ptr`.
`operands` places the two arguments in machine order, so the same shape
serves the import and the generated shim. -/
def readContractAt [WasmSmallStepGS hlc Universal.State]
    (absoluteIndex : Nat)
    (operands : UInt32 → UInt32 → List Value) : Prop :=
  ∀ (ptr requested : UInt32) (buffer input output : List UInt8)
    (raised : Bool)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    let count := min requested.toNat input.length
    CallContract absoluteIndex (operands ptr requested)
      callerLocals stack code arity remainder controls calls s E Φ iprop(
        RuntimeContext ∗
        Streams input output raised ∗
        Slices.ByteSlice 0 ptr buffer ∗
        ⌜requested.toNat = buffer.length ∧ 0 < requested.toNat⌝ ∗
        (RuntimeContext -∗
          Streams (input.drop count) output raised -∗
          Slices.ByteSlice 0 ptr (input.take count ++ buffer.drop count) -∗
          ⌜count ≤ requested.toNat⌝ -∗
          ResumeWP [.i32 (UInt32.ofNat count)] callerLocals stack code arity
            remainder controls calls s E Φ))

/-- A call that writes the `requested` bytes at `ptr` to the output stream. -/
def writeContractAt [WasmSmallStepGS hlc Universal.State]
    (absoluteIndex : Nat)
    (operands : UInt32 → UInt32 → List Value) : Prop :=
  ∀ (ptr requested : UInt32) (bytes input output : List UInt8)
    (raised : Bool)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    CallContract absoluteIndex (operands ptr requested)
      callerLocals stack code arity remainder controls calls s E Φ iprop(
        RuntimeContext ∗
        Streams input output raised ∗
        Slices.ByteSlice 0 ptr bytes ∗
        ⌜requested.toNat = bytes.length ∧ 0 < requested.toNat⌝ ∗
        (RuntimeContext -∗
          Streams input (output ++ bytes) raised -∗
          Slices.ByteSlice 0 ptr bytes -∗
          ResumeWP [] callerLocals stack code arity remainder controls calls
            s E Φ))

/-! ## Imports 0 to 2 -/

/-- Import 0, `stdio.read`. -/
def Import0Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  readContractAt (hlc := hlc) 0
    (fun ptr requested => [.i32 ptr, .i32 requested])

/-- Import 1, `stdio.write`. -/
def Import1Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  writeContractAt (hlc := hlc) 1
    (fun ptr requested => [.i32 ptr, .i32 requested])

/-- Import 2, the terminal `talos.oom` outcome.  The host trap consumes the
runtime context, so the terminal continuation gets only the host state. -/
def Import2Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (input output : List UInt8) (raised : Bool)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    CallContract 2 [] callerLocals stack code arity remainder controls calls
      s E Φ iprop(
        RuntimeContext ∗ Streams input output raised ∗
        (Streams input output true -∗
          Φ (.trapped (.host OOM.trapMessage))))

/-! ## The generated shims -/

/-- Local `func56`, absolute index 59: the OOM shim.  It calls import 2 and
then holds an `unreachable` that no execution reaches. -/
def Func56Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (input output : List UInt8) (raised : Bool)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    CallContract 59 [] callerLocals stack code arity remainder controls calls
      s E Φ iprop(
        RuntimeContext ∗ Streams input output raised ∗
        (Streams input output true -∗
          Φ (.trapped (.host OOM.trapMessage))))

/-- Local `func60`, absolute index 63: the read shim.  It takes the pointer
first and the count second, and swaps them for the import. -/
def Func60Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  readContractAt (hlc := hlc) 63
    (fun ptr requested => [.i32 requested, .i32 ptr])

/-- Local `func61`, absolute index 64: the write shim, with the same operand
swap as the read shim. -/
def Func61Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  writeContractAt (hlc := hlc) 64
    (fun ptr requested => [.i32 requested, .i32 ptr])

end Project.RustHashMap.Contracts
