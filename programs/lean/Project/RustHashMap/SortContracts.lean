import Project.RustHashMap.BodyContracts
import Project.RustHashMap.SortModels

/-!
# Call contracts of the five bodies of the compiled pair sort

`sorted_entries`, absolute `func 7`, sorts its entry list by key.  The
compiled sort is five functions of
`programs/rust/build/rust_hash_map/program.wat`:

| Absolute | Local | Rust | WAT | Contract |
| --- | --- | --- | --- | --- |
| 14 | 11 | `ipnsort` | 2635-2848 | `Func11Spec` |
| 15 | 12 | `insertion_sort_shift_left` | 2849-2952 | `Func12Spec` |
| 23 | 20 | `median3_rec` | 5598-5669 | `Func20Spec` |
| 24 | 21 | `quicksort` | 5670-8663 | `Func21Spec` |
| 25 | 22 | `heapsort` | 8664-8809 | `Func22Spec` |

This module states one contract for each.  Nothing is proved here; a
contract is an interface.  The pure models are in
`Project.RustHashMap.SortModels`.

## Which bodies commit a frame

Only absolute `func 24` commits a frame.  It lowers the stack pointer by
256 bytes at WAT 5672 to 5676 and restores it on every exit.

Absolute `func 15`, `func 23` and `func 25` hold no `global.get 0` at
all, and they call nothing that does: `func 15` and `func 25` call
nothing, and `func 23` calls only itself.  Their contracts therefore take
`RuntimeContext` and the buffer alone, in the shape of
`Project.RustHashMap.LookupContracts.Func9Spec`.  There is no
`StackPointer`, no `StackBelow` and no ledger row.

Absolute `func 14` holds no `global.get 0` either, but it ends with
`call 24` at WAT 2847, so it does take stack below its caller.  Its
contract keeps the two stack resources and its depth is the depth of the
one call it makes.

## What every sort contract promises

A sort contract promises two facts about its output and no more: the
output is a permutation of the input, and the output is in key order.
`Table.eq_sortByKey_of_perm_of_sorted` turns that pair into the
`sortByKey` that `Project.RustHashMap.Spec` names, so no caller has to
know which kernel ran.

`SortPost` and `SortPostFrameless` name the two shapes of that promise
once.  `SortPost` also gives back one resource that the callee only
borrows, which is how absolute `func 24` returns the ancestor cell.  The
other callers pass `emp` there.
-/

namespace Project.RustHashMap.SortContracts

open Wasm Wasm.RustStd
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open Project.RustHashMap.EntryContracts
open Project.RustHashMap.BodyContracts
open Project.RustHashMap.SortModels
open scoped Wasm.SmallStep.Outcome

/-! ## The stack constants of the sort -/

/-- The stack that `quicksort`, absolute `func 24`, takes below its
caller.  Its own frame is 256 bytes, at WAT 5672 to 5676, and the body
calls itself once per level.  `limit` counts the levels that the body
still allows, so the deepest run holds `limit + 1` frames. -/
def quicksortDepth (limit : Nat) : Nat := 256 * (limit + 1)

/-- The recursion limit that absolute `func 14` passes to `quicksort`.
The compiled form at WAT 2836 to 2845 is `((len ||| 1).clz <<< 1) ^^^ 62`.
`Nat.log2` is the same number, because `clz x` is `31 - Nat.log2 x` for a
nonzero `x`, which `CodeLib.RustStd.HashMap.CapacityClz.clz32_eq`
states. -/
def sortLimit (len : Nat) : Nat := 2 * Nat.log2 (len ||| 1)

/-- The stack that absolute `func 14` takes below its caller.  The body
commits no frame of its own, so this is the depth of its one call. -/
def sortDepth (len : Nat) : Nat := 256 * (2 * Nat.log2 (len ||| 1) + 1)

theorem sortDepth_eq_quicksortDepth (len : Nat) :
    sortDepth len = quicksortDepth (sortLimit len) := rfl

/-- The sort never takes more than 55 quicksort frames.  A table has at
most `2 ^ 27` buckets, so `Nat.log2 (len ||| 1)` is at most 27 and the
limit is at most 54.  The writer of `sorted_entries` carries the literal
that this bound gives. -/
theorem sortDepth_le {len : Nat} (hlen : len ≤ 2 ^ 27) :
    sortDepth len ≤ 256 * 55 := by
  unfold sortDepth
  have hlt : len ||| 1 < 2 ^ 28 := by
    refine Nat.or_lt_two_pow ?_ ?_ <;> omega
  have hne : len ||| 1 ≠ 0 := by
    intro hzero
    have hbit := Nat.testBit_lor len 1 0
    simp [hzero] at hbit
  have hlog : Nat.log2 (len ||| 1) < 28 := (Nat.log2_lt hne).2 hlt
  omega

/-! ## The two shapes of a sort result -/

/-- The success continuation of a sort body that commits stack.  The
callee gives back the stack pointer, the region below it, the buffer with
the entries reordered, and `kept`, which is whatever the callee only
borrows.  The two pure facts are the whole promise. -/
def SortPost [WasmSmallStepGS hlc Universal.State]
    (v : UInt32) (pairs : List (UInt32 × UInt32)) (sp : UInt32)
    (depth : Nat) (kept : HeapIProp)
    (callerLocals : Locals) (stack : List Value)
    (code : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (s : Stuckness) (E : CoPset)
    (Φ : ObservableOutcome → HeapIProp) : HeapIProp :=
  iprop(∀ out : List (UInt32 × UInt32), ∀ below' : List UInt8,
    RuntimeContext -∗
    StackPointer sp -∗
    StackBelow sp depth below' -∗
    HashMap.Table.PairSlice 0 v out -∗
    kept -∗
    ⌜out.Perm pairs ∧ HashMap.Table.SortedByKey out⌝ -∗
    ResumeWP [] callerLocals stack code arity remainder controls calls
      s E Φ)

/-- The success continuation of a sort body that commits no stack. -/
def SortPostFrameless [WasmSmallStepGS hlc Universal.State]
    (v : UInt32) (pairs : List (UInt32 × UInt32))
    (callerLocals : Locals) (stack : List Value)
    (code : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (s : Stuckness) (E : CoPset)
    (Φ : ObservableOutcome → HeapIProp) : HeapIProp :=
  iprop(∀ out : List (UInt32 × UInt32),
    RuntimeContext -∗
    HashMap.Table.PairSlice 0 v out -∗
    ⌜out.Perm pairs ∧ HashMap.Table.SortedByKey out⌝ -∗
    ResumeWP [] callerLocals stack code arity remainder controls calls
      s E Φ)

/-! ## The ancestor pivot of `quicksort` -/

/-- The ancestor pivot that `quicksort` carries down its recursion: the
address of the entry that holds it.  The body reads one `i32` there, the
key, at WAT 5763 to 5764.  The top call carries none. -/
def AncestorCell [WasmHeapGS Universal.State] :
    Option (UInt32 × UInt32) → HeapIProp
  | none => iprop(emp)
  | some (p, k) => iprop(pointsTo_u32 0 p k)

/-- The operand that carries the ancestor pivot.  The top call passes the
null pointer, which absolute `func 14` writes as `i32.const 0` at WAT
2839 and which the body tests at WAT 5760 to 5762. -/
def ancestorArg : Option (UInt32 × UInt32) → UInt32
  | none => 0
  | some (p, _) => p

/-- Every key of the run is above the ancestor pivot key.

This is the fact that kills the dead arm X-F24-EQUAL of
`Analysis/scope-and-exclusions.md`.  The guard at WAT 5760 to 5771 reads
the ancestor key and the pivot key and takes the equal-partition path,
WAT 5758 to 5976, when the ancestor key is not below the pivot key.  With
this hypothesis the guard is false at every level. -/
def AncestorBelow (anc : Option (UInt32 × UInt32))
    (pairs : List (UInt32 × UInt32)) : Prop :=
  ∀ p k, anc = some (p, k) → ∀ x ∈ pairs, k < x.1

/-! ## `insertion_sort_shift_left`, absolute `func 15` -/

/-- Absolute `func 15`, local `func12`, WAT 2849 to 2952.  The arguments
in source order are the buffer, its length and the offset, so local 0 is
the buffer, local 1 the length and local 2 the offset.  The body reads no
stream, allocates nothing and commits no frame.

The first `offset` entries are already in key order, and the loop puts
each later entry into place.  `SortModels.insertionShiftLeft` is the
model, and `SortModels.insertionShiftLeft_perm` and
`SortModels.insertionShiftLeft_sorted` give the two facts of the post.

The bound `offset <= len` kills the dead arm X-F15-OFFSET of
`Analysis/scope-and-exclusions.md`: the guard at WAT 2855 leaves the
block when the offset is above the length, and the block ends in the
`unreachable` at WAT 2951. -/
def Func12Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (v len offset : UInt32) (pairs : List (UInt32 × UInt32))
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    CallContract 15 [.i32 offset, .i32 len, .i32 v]
      callerLocals stack code arity remainder controls calls s E Φ iprop(
        RuntimeContext ∗
        HashMap.Table.PairSlice 0 v pairs ∗
        ⌜pairs.length = len.toNat ∧ 1 ≤ offset.toNat ∧
          offset.toNat ≤ len.toNat ∧
          HashMap.Table.SortedByKey (pairs.take offset.toNat) ∧
          v.toNat + 8 * len.toNat < UInt32.size⌝ ∗
        SortPostFrameless v pairs callerLocals stack code arity remainder
          controls calls s E Φ)

/-! ## `heapsort`, absolute `func 25` -/

/-- Absolute `func 25`, local `func22`, WAT 8664 to 8809.  The arguments
in source order are the buffer, its length and the comparison closure, so
local 0 is the buffer, local 1 the length and local 2 the closure.  The
key order is inlined, so local 2 is never read; absolute `func 24` passes
an uninitialized register there at WAT 8688.

The body reads no stream, allocates nothing and commits no frame.
`SortModels.heapsortModel` is the model.  It has no dead arm: both loop
phases run for every length. -/
def Func22Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (v len env : UInt32) (pairs : List (UInt32 × UInt32))
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    CallContract 25 [.i32 env, .i32 len, .i32 v]
      callerLocals stack code arity remainder controls calls s E Φ iprop(
        RuntimeContext ∗
        HashMap.Table.PairSlice 0 v pairs ∗
        ⌜pairs.length = len.toNat ∧
          v.toNat + 8 * len.toNat < UInt32.size⌝ ∗
        SortPostFrameless v pairs callerLocals stack code arity remainder
          controls calls s E Φ)

/-! ## `median3_rec`, absolute `func 23` -/

/-- Absolute `func 23`, local `func20`, WAT 5598 to 5669.  The four
arguments in source order are three entry addresses and a length, so
local 0, local 1 and local 2 are the addresses and local 3 is the length.
The body returns one `i32`, one of the three addresses.

The body calls only itself, three times, at WAT 5621, 5634 and 5647, and
commits no frame.  It reads the key word of three entries and writes
nothing.

The contract promises only that the answer is an entry address of the
same buffer.  The median property is not stated, because absolute
`func 24` uses the answer as a pivot and every entry of the buffer serves
as a pivot.  A contract that named the median would make the body proof
carry the whole recursion for nothing. -/
def Func20Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (v a b c n : UInt32) (ia ib ic : Nat)
    (pairs : List (UInt32 × UInt32))
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    CallContract 23 [.i32 n, .i32 c, .i32 b, .i32 a]
      callerLocals stack code arity remainder controls calls s E Φ iprop(
        RuntimeContext ∗
        HashMap.Table.PairSlice 0 v pairs ∗
        ⌜a = v + UInt32.ofNat (8 * ia) ∧ b = v + UInt32.ofNat (8 * ib) ∧
          c = v + UInt32.ofNat (8 * ic) ∧ 1 ≤ n.toNat ∧
          ia + n.toNat ≤ pairs.length ∧ ib + n.toNat ≤ pairs.length ∧
          ic + n.toNat ≤ pairs.length ∧
          v.toNat + 8 * pairs.length < UInt32.size⌝ ∗
        (∀ r : UInt32,
          RuntimeContext -∗
          HashMap.Table.PairSlice 0 v pairs -∗
          ⌜∃ ir : Nat, ir < pairs.length ∧
            r = v + UInt32.ofNat (8 * ir)⌝ -∗
          ResumeWP [.i32 r] callerLocals stack code arity remainder
            controls calls s E Φ))

/-! ## `ipnsort`, absolute `func 14` -/

/-- Absolute `func 14`, local `func11`, WAT 2635 to 2848.  The arguments
in source order are the buffer, its length and the comparison closure, so
local 0 is the buffer, local 1 the length and local 2 the closure.

The body picks one of three kernels by length.  Below 2 entries it
returns at once.  Below 21 entries it runs the small sort in place and
then `call 15` with the offset 1.  Otherwise it ends with `call 24` at
WAT 2847.  It commits no frame, so `sortDepth` is the depth of that one
call.

The length bound `2 ^ 27` is the bound that every caller has: absolute
`func 7` sorts one entry per table bucket and the table has at most
`2 ^ 27` buckets. -/
def Func11Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (sp v len env : UInt32) (pairs : List (UInt32 × UInt32))
    (below : List UInt8)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    CallContract 14 [.i32 env, .i32 len, .i32 v]
      callerLocals stack code arity remainder controls calls s E Φ iprop(
        RuntimeContext ∗
        StackPointer sp ∗
        StackBelow sp (sortDepth len.toNat) below ∗
        HashMap.Table.PairSlice 0 v pairs ∗
        ⌜pairs.length = len.toNat ∧ len.toNat ≤ 2 ^ 27 ∧
          v.toNat + 8 * len.toNat < UInt32.size ∧
          sortDepth len.toNat ≤ sp.toNat⌝ ∗
        SortPost v pairs sp (sortDepth len.toNat) iprop(emp) callerLocals
          stack code arity remainder controls calls s E Φ)

/-! ## `quicksort`, absolute `func 24` -/

/-- Absolute `func 24`, local `func21`, WAT 5670 to 8663.  The five
arguments in source order are the buffer, its length, the ancestor pivot
address, the recursion limit and the comparison closure, so local 0 is
the buffer, local 1 the length, local 2 the ancestor, local 3 the limit
and local 4 the closure.  Absolute `func 14` passes them in that order at
WAT 2835 to 2847.

The body takes the frame of 256 bytes, picks a pivot with `call 23`,
partitions, and recurses.  It falls back to `call 25` when the limit runs
out, which is the live edge X-F24-HEAP.

Two dead arms need the precondition.  X-F24-EQUAL, WAT 5758 to 5976, is
the equal-partition path that `AncestorBelow` kills.  X-F24-ORDER, the
`call 107` and `unreachable` at WAT 8656 to 8657, is the panic that a
comparison which is not a strict total order raises; `NodupKeys` on
distinct keys gives the strict order, and
`SortModels.BimergeExhausts` is the property that the body proof needs
there. -/
def Func21Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (sp v len limit env : UInt32) (anc : Option (UInt32 × UInt32))
    (pairs : List (UInt32 × UInt32)) (below : List UInt8)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    CallContract 24
      [.i32 env, .i32 limit, .i32 (ancestorArg anc), .i32 len, .i32 v]
      callerLocals stack code arity remainder controls calls s E Φ iprop(
        RuntimeContext ∗
        StackPointer sp ∗
        StackBelow sp (quicksortDepth limit.toNat) below ∗
        HashMap.Table.PairSlice 0 v pairs ∗
        AncestorCell anc ∗
        ⌜pairs.length = len.toNat ∧ len.toNat ≤ 2 ^ 27 ∧
          HashMap.NodupKeys pairs ∧ AncestorBelow anc pairs ∧
          v.toNat + 8 * len.toNat < UInt32.size ∧
          quicksortDepth limit.toNat ≤ sp.toNat ∧
          (∀ p k, anc = some (p, k) → p ≠ 0)⌝ ∗
        SortPost v pairs sp (quicksortDepth limit.toNat) (AncestorCell anc)
          callerLocals stack code arity remainder controls calls s E Φ)

end Project.RustHashMap.SortContracts
