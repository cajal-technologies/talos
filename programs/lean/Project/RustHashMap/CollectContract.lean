import Project.RustHashMap.BodyContracts
import CodeLib.RustStd.HashMap.ProbeWasm

/-!
# The call contract of `collect_entries`

Absolute `func 5`, Lean `Project.RustHashMap.funcs[2]`.  The Rust source is
`collect_entries(entries: Vec<(u32, u32)>) -> HashMap<u32, u32>`, which is
`entries.into_iter().collect()`.  The `map_len` driver calls it once, at WAT
lines 5513 to 5519, with the 32-byte map output slot at frame offset 24 and
the `Vec<(u32, u32)>` header at frame offset 12.

This module states the contract only.  It proves nothing about the body.
The body is the compiled hash table: the inlined SipHash-1-3, the probe
loop, `reserve_rehash_inner` (`func 17`) and `insert` (`func 18`).

## Shape

The file follows `Project.RustHashMap.BodyContracts`.  It reuses
`StackBelow` for the stack region below the caller, and it uses the same
two-arm continuation: a normal arm and an out-of-memory arm, joined by
`∧`.  The operand list is `[.i32 vecHeader, .i32 mapSlot]`, because
`callExpr` puts the last pushed argument first, and the driver pushes the
map slot first.  `Func1Spec` orders its two arguments the same way.

## What the callee takes and what it gives back

`collect_entries` reads the three header words of the vector and never
writes them, so the contract returns them unchanged.  It reads the pair
buffer and then releases it with `call 60`, whose body is empty, so the
contract takes the buffer and does not give it back.  A caller that still
needs those bytes cannot use this contract.

The two SipHash seeds come from the thread-local cells at 1049512 and
1049520, with the state byte at 1049528.  The first call in a run writes
all three; every later call reads `k0` and `k1` and bumps `k0` by one.  The
contract owns the region as raw bytes and hands it back with the contents
changed, and the continuation names the two seeds the run used.  No caller
can predict them, because they are addresses of the run.

## The postcondition the driver needs

`MapAt 0 mapSlot k0 k1 entries` is the map value that `HashMap::from_iter`
builds from the pairs in wire order.  It carries the four table words at
`mapSlot + 0`, the control bytes, every bucket, and the two seeds at
`mapSlot + 16` and `mapSlot + 24`.  The word at offset 12 of the map value,
which is frame offset 36 in the driver, is `items`.  The driver writes that
word to the output stream, and `Project.RustHashMap.Spec.lenOutput` names
`HashMap.len`, so the contract states the equation between the two counts
as a pure conjunct.  Without it the driver cannot close its own contract.

## Outcomes

There are two.  A normal return leaves the map in the slot.  A failed
allocation inside `RandomState::new` or inside `reserve_rehash_inner`
raises the terminal `talos.oom` host trap.  The capacity overflow panic of
`func 17` is a third exit of the compiled code.  The body proof must show
that it is not reachable, because `func 58` refuses any allocation whose
end passes `isize::MAX` and raises `talos.oom` first.
-/

namespace Project.RustHashMap.CollectContract

open Wasm Wasm.RustStd
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open Project.RustHashMap.Allocator
open Project.RustHashMap.AllocatorContracts
open Project.RustHashMap.EntryContracts
open Project.RustHashMap.VecGrow
open Project.RustHashMap.BodyContracts
open scoped Wasm.SmallStep.Outcome

/-! ## Constants -/

/-- The stack that `collect_entries` takes below the caller.  Its own frame
is 48 bytes.  The rest is the deepest chain below it: `func 18` with 16
bytes, `func 17` with 32 bytes, and the allocator and the thread-local
initializer through 16, 83 and 58.  This number is measured from the WAT
and is not proved.  A body proof that needs more must raise it here. -/
def collectDepth : Nat := 192

/-- The codec of one wire pair: the key in the first four bytes, the value
in the next four.  The compiled loop stores each key at `buffer + 8 i` and
each value at `buffer + 8 i + 4`, so the buffer holds the pairs in wire
order. -/
def entryCodec : WordCodec (UInt32 × UInt32) :=
  HashMap.pairCodec WordCodec.u32le WordCodec.u32le

/-! ## `collect_entries` -/

/-- Absolute `func 5`, local `func2`: `collect_entries`.

The arguments in source order are the 32-byte map output slot and the
pointer to the `Vec<(u32, u32)>` header, which holds the capacity at offset
0, the buffer pointer at offset 4 and the entry count at offset 8.

The function reads the two SipHash seeds from the thread-local cells,
copies the static empty table into its frame, reserves room for `len`
entries, inserts each pair in wire order, frees the pair buffer, and copies
the 32-byte map value into the output slot.

The normal arm gives the map value back as `MapAt`.  The table is the one
`Table.ofEntries` builds under `SipHash.hashU32 k0 k1`, and its `items`
count equals `HashMap.len (HashMap.ofEntries entries)`, which is the count
the driver writes out.  A repeated key raises no error; the later value
replaces the earlier one, and the two counts differ from `entries.length`
together.

The out-of-memory arm is the terminal `talos.oom` host trap.  It consumes
every resource, as in `Func1Spec`. -/
def Func2Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (sp mapSlot vecHeader cap ptr len : UInt32)
    (heapId : GName) (entries : RustStd.HashMap.Map UInt32 UInt32)
    (payload spare mapBefore keysBefore below : List UInt8)
    (storedCursor : UInt32) (frontier : Nat) (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    CallContract 5 [.i32 vecHeader, .i32 mapSlot]
      callerLocals stack code arity remainder controls calls s E Φ iprop(
        RuntimeContext ∗
        StackPointer sp ∗
        StackBelow sp collectDepth below ∗
        Slices.ByteSlice 0 mapSlot mapBefore ∗
        pointsTo_u32 0 vecHeader cap ∗
        pointsTo_u32 0 (vecHeader + 4) ptr ∗
        pointsTo_u32 0 (vecHeader + 8) len ∗
        Slices.ByteSlice 0 ptr (payload ++ spare) ∗
        Slices.ByteSlice 0 randomStateCell keysBefore ∗
        BumpHeap heapId storedCursor frontier history ∗
        Streams input output raised ∗
        ⌜mapBefore.length = 32 ∧ keysBefore.length = randomStateSize ∧
          payload = entryCodec.serialize entries ∧
          entries.length = len.toNat ∧ len.toNat ≤ cap.toNat ∧
          spare.length = 8 * (cap.toNat - len.toNat) ∧
          collectDepth ≤ sp.toNat ∧ mapSlot.toNat + 32 < UInt32.size ∧
          vecHeader.toNat + 12 < UInt32.size⌝ ∗
        (-- the normal arm
         (∀ k0 : UInt64, ∀ k1 : UInt64, ∀ below' : List UInt8,
            ∀ keysAfter : List UInt8, ∀ storedCursor' : UInt32,
            ∀ frontier' : Nat, ∀ history' : AllocationHistory,
            RuntimeContext -∗
            StackPointer sp -∗
            StackBelow sp collectDepth below' -∗
            RustStd.HashMap.Table.MapAt 0 mapSlot k0 k1 entries -∗
            pointsTo_u32 0 vecHeader cap -∗
            pointsTo_u32 0 (vecHeader + 4) ptr -∗
            pointsTo_u32 0 (vecHeader + 8) len -∗
            Slices.ByteSlice 0 randomStateCell keysAfter -∗
            BumpHeap heapId storedCursor' frontier' history' -∗
            Streams input output raised -∗
            ⌜keysAfter.length = randomStateSize ∧
              (RustStd.HashMap.Table.ofEntries
                  (RustStd.HashMap.SipHash.hashU32 k0 k1) entries).items =
                RustStd.HashMap.len (RustStd.HashMap.ofEntries entries)⌝ -∗
            ResumeWP [] callerLocals stack code arity remainder controls
              calls s E Φ) ∧
         -- the out-of-memory arm
         (∀ remaining' : List UInt8,
            Streams remaining' output true -∗
              Φ (.trapped (.host OOM.trapMessage)))))

end Project.RustHashMap.CollectContract
