import Project.RustHashMap.InsertTailDefs
import Project.RustHashMap.DriverTailProof

/-!
# The tail of the `map_insert` driver: the contract

`Project.RustHashMap.InsertTailDefs` cuts the code of the `map_insert`
driver after the read phase into fragments.  This file states what the
tail proves.  The statement is the interface between the read phase,
which `Project.RustHashMap.InsertRead` proves, and the body proof that
comes next.

## Why the contract has two conclusions

The read phase of `map_insert` leaves the seventh block at two places,
and the two exits carry different code, different control stacks and
different resources:

* The non-empty arm stops at WAT 123 with the code `insRest7` inside
  `insControls7`.  It still holds the input vector and the chunk buffer
  that the read loop filled.
* The empty arm stops at WAT 173 with the code `insAfter7` inside
  `insControls6`.  It holds the empty vector and the 256 zero bytes of
  the `memory.fill`, and `AfterReadIns` does not describe it.

So `InsertTailSpec` is the conjunction of `InsertTailNonEmptySpec` and
`InsertTailEmptySpec`.  The driver does `by_cases input = []` and gives
one of the two to each continuation of `twp_insert_read_phase`.  The
`map_remove` twin needs one conclusion only, because its read phase has
one exit.

## What the tail takes

The tail takes three things beyond the resources of its read phase:

* 14080 bytes below the reserve, which together with the sixteen bytes
  of the reserve make the region that the callees need;
* the whole data segment, out of which absolute `func 55` cuts its two
  static messages, "failed to fill whole buffer" at 1049080 and "Not
  all bytes read" at 1049107;
* on the non-empty arm only, the `RandomState` cells, which
  `collect_entries` reads and writes, and the bound on the input length,
  so that the stored length word reads back as the number of input
  bytes.

The empty arm asks for neither of the last two.  It runs the first error
arm and the reject exit, which call absolute `func 55` and absolute
`func 52` and nothing else, so it reaches no table and no input word.

The tail gives back the runtime, the restored stack pointer and the
output stream, through `Project.RustHashMap.DriverTailProof.TailDone`.
It drops the stack bytes, the bump heap and every live block, which is
sound because `ExportSuccess` names only the output stream.

## The depths and the callees

The deepest callee is `sorted_entries`, absolute `func 7`, so the region
below the frame is `insertCalleeDepth` bytes, which is `serializeDepth`.
The borsh decoder, `borsh::io::Error::new`, `collect_entries`, the
insert shim and the reply writer take less, and `decoderDepth_le_insert`,
`errorNewDepth_le_insert`, `collectDepth_le_insert`,
`insertWrapDepth_le_insert` and `replyDepth_le_insert` state that.

Five of the seven callees are proved already: `Func1Spec` by
`Project.RustHashMap.Func1Proof.func1_correct`, `Func52Spec` by
`Func52Proof.func52_correct`, `Func49Spec` by `Func49Proof`,
`Func4Spec` by `Func4Proof.func4_correct` and `Func5Spec` by
`Func5Proof.func5_correct`.  Two are open here:
`Project.RustHashMap.CollectContract.Func2Spec`, and
`Project.RustHashMap.MapOpContracts.Func3Spec`, which
`Func3Proof.func3_correct_of` gives under `Func15InsertSpec`.  So the
theorem that discharges this contract is

```
twp_insert_tail (hfunc2 : Func2Spec) (hfunc3 : Func3Spec) :
  InsertTailSpec
```

and its two halves are `twp_insert_tail_nonempty` and
`twp_insert_tail_empty`.

## The continuation of the read phase

`twp_insert_read_phase` takes the code after the outer block as
`afterRead`.  In the driver that code is the stack epilogue, so
`afterRead` is `insEpilogue ++ afterTail`, and the `afterTail` that
`TailDone` names follows the epilogue.
-/

namespace Project.RustHashMap.InsertTailContracts

open Wasm Wasm.RustStd
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open Project.RustHashMap.Allocator
open Project.RustHashMap.AllocatorContracts
open Project.RustHashMap.EntryContracts
open Project.RustHashMap.VecGrow
open Project.RustHashMap.BodyContracts
open Project.RustHashMap.CollectContract
open Project.RustHashMap.EntriesContracts
open Project.RustHashMap.MapOpContracts
open Project.RustHashMap.InsertRead
open Project.RustHashMap.InsertTailDefs
open scoped Wasm.SmallStep.Outcome

/-- An empty input carries no key and no value, so `map_insert` writes
nothing on the empty arm. -/
theorem insertOutput_nil :
    Project.RustHashMap.Spec.insertOutput [] = [] := rfl

/-- The contract of the `map_insert` driver on the non-empty exit of its
read phase, WAT 123.

The driver frame holds 368 bytes.  The entries vector header for
`call 5` sits at frame offsets 8 to 20, the input vector header at 24 to
36, the map slot that overlays it at 24 to 56, the chunk buffer at 56 to
312, the decode header at 312 to 320 and the output slot of the borsh
decoder at 336 to 352.  The tail reuses the first 40 bytes of the chunk
buffer as the output slot of the insert shim, and the 12 bytes at 64 as
the output header of `sorted_entries`.

The tail has two exits.  The reject exit frees the decoded error and the
input buffer, and it writes nothing; `Spec.insertOutput` is the empty
list there, because the read phase rejects the input.  The accept exit
writes the displaced value as a borsh `Option<u32>` and then the map
that stays.  An allocator failure inside a callee raises
`talos.oom`. -/
def InsertTailNonEmptySpec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (heapId : GName) (capacity ptr byte length : UInt32)
    (input output : List UInt8)
    (reserve head mid chunk top : List UInt8)
    (extra keysBefore dataBytes : List UInt8)
    (storedCursor : UInt32) (frontier : Nat) (history : AllocationHistory)
    (afterTail : Program)
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp},
    input ≠ [] →
    iprop(
      AfterReadIns heapId capacity ptr input reserve head mid chunk top
        storedCursor frontier history output ∗
      Slices.ByteSlice 0
        (func0Base - UInt32.ofNat insertCalleeDepth) extra ∗
      Slices.ByteSlice 0 randomStateCell keysBefore ∗
      Slices.ByteSlice 0 entryStackTop dataBytes ∗
      ⌜extra.length = 14080 ∧ keysBefore.length = randomStateSize ∧
        dataBytes.length = dataSegmentSize ∧
        input.length < UInt32.size⌝ ∗
      (DriverTailProof.TailDone
          (output ++ Project.RustHashMap.Spec.insertOutput input)
          afterTail arity remainder controls calls s E Φ ∗
        (ExportOOM -∗ Φ (.trapped (.host OOM.trapMessage))))) ⊢
      WP (.running
        ⟨afterReadLocalsIns byte length, insRest7, arity, remainder,
          insControls7 (insEpilogue ++ afterTail) ++ controls, calls⟩ :
            Expr Universal.State) @ s; E [{ Φ }]

/-- The contract of the `map_insert` driver on the empty exit of its
read phase, WAT 173.

The input stream was empty, so the vector still holds the empty
allocation of the frame setup and the chunk buffer still holds the 256
zero bytes of the `memory.fill`.  The arm writes an empty slice into the
decode header and falls into the first error arm, which builds the
"failed to fill whole buffer" error and leaves through the reject exit.
It writes nothing, and `insertOutput_nil` says that the public answer is
empty as well. -/
def InsertTailEmptySpec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (heapId : GName) (input output : List UInt8)
    (reserve head mid top extra dataBytes : List UInt8)
    (storedCursor : UInt32) (frontier : Nat) (history : AllocationHistory)
    (afterTail : Program)
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp},
    input = [] →
    iprop(
      EmptyArmIns heapId reserve head mid top storedCursor frontier
        history output ∗
      Slices.ByteSlice 0
        (func0Base - UInt32.ofNat insertCalleeDepth) extra ∗
      Slices.ByteSlice 0 entryStackTop dataBytes ∗
      ⌜extra.length = 14080 ∧ dataBytes.length = dataSegmentSize⌝ ∗
      (DriverTailProof.TailDone
          (output ++ Project.RustHashMap.Spec.insertOutput input)
          afterTail arity remainder controls calls s E Φ ∗
        (ExportOOM -∗ Φ (.trapped (.host OOM.trapMessage))))) ⊢
      WP (.running
        ⟨emptyArmLocals, insAfter7, arity, remainder,
          insControls6 (insEpilogue ++ afterTail) ++ controls, calls⟩ :
            Expr Universal.State) @ s; E [{ Φ }]

/-- The contract of the `map_insert` driver after its read phase: one
conclusion for each exit of the seventh block. -/
def InsertTailSpec [WasmSmallStepGS hlc Universal.State] : Prop :=
  InsertTailNonEmptySpec (hlc := hlc) ∧ InsertTailEmptySpec (hlc := hlc)

end Project.RustHashMap.InsertTailContracts
