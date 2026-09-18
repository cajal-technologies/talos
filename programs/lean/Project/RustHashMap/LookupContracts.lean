import Project.RustHashMap.Contracts
import CodeLib.RustStd.HashMap.ProbeWasm
import CodeLib.RustStd.HashMap.OptionOut
import CodeLib.RustStd.HashMap.TableRefinement

/-!
# The contracts of the two lookup kernels

`HashMap::contains_key` is absolute `func 12` and `HashMap::get` is
absolute `func 20` of `programs/rust/build/rust_hash_map/program.wat`.
This module states one contract for each.  Nothing is proved here; a
contract is an interface.

## Both kernels are frameless

Neither body starts with the `global.get 0` and `i32.sub` pair that commits
a shadow frame.  Absolute `func 12` declares ten locals and absolute
`func 20` declares fourteen, and every one of them is a register.  Both
contracts therefore take `RuntimeContext` alone, in the shape of
`Project.RustHashMap.DropErrorContracts.Func44Spec` and of
`Project.RustHashMap.VecGrow.Func30Spec`.  There is no `StackPointer`, no
`StackBelow`, and no ledger row: a frameless body adds no stack depth to
the caller, so the stack accounting has nothing to record.

## Why `HashMapAt` and not `MapAt`

`Table.MapAt` fixes the table to `Table.ofEntries`, which hides the
invariant that the probe loop needs.  Both bodies walk the control bytes,
so the precondition names the table itself and carries `Table.WF` and
`Table.Clean` beside it.  This is the shape of
`Project.RustHashMap.CollectBodyContracts.Func15Spec`.

`Table.WF` alone does not stop the walk.  It relates the control bytes to
the slots and says nothing about the counters, so it admits a table whose
every byte is full.  `Table.Clean` ties `growthLeft + items` to the
capacity, and `Project.RustHashMap.LookupPures.exists_empty_of_clean`
turns that into one `EMPTY` byte.  Unlike the insert contract, neither
lookup contract needs `1 <= t.growthLeft`: a lookup writes no byte, so a
table that `Table.ofEntries` filled to the last slot is still in range.

Both contracts also take `map.toNat + 32 < UInt32.size`, because both
bodies read the four header words and the two seed cells, which is the
whole 32-byte map value.

## The arms

Absolute `func 12` has no dead arm.  The guard at WAT 2288 to 2291 reads
the item count at `map + 12` and returns `0` when it is zero;
`Project.RustHashMap.LookupPures.containsKey_eq_false_of_items_zero` says
the model agrees.  The probe loop at WAT 2452 to 2552 leaves through the
key match or through the `EMPTY` byte, and the two exits push `1` and `0`.

Absolute `func 20` has the same guard at WAT 4774 to 4779 and the same two
loop exits.  The `some` arm reads the value word at `bucket - 4`, WAT 5041
to 5045, and the `none` arm leaves the payload word untouched.  Word 0 of
the output slot is the discriminant and word 1 is the payload, which is
`Table.optionU32At`; the payload of `none` is free there, and that is what
the compiled `none` arm leaves behind.

## What each contract returns

Absolute `func 12` returns one `i32`, `1` or `0`.  Absolute `func 20`
returns nothing and writes the eight-byte out-parameter that its first
argument names.  Both give the map value back unchanged, because neither
body writes a control byte or a slot.
-/

namespace Project.RustHashMap.LookupContracts

open Wasm Wasm.RustStd
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open scoped Wasm.SmallStep.Outcome

/-! ## Absolute `func 12`, local `func9`: `contains_key` -/

/-- Absolute `func 12`, WAT 2286 to 2554.  The arguments in source order are
the map value and the key, so the operand list below carries the key on
top.  The body reads the map and writes nothing, and it returns `1` when
the key has an entry.

The body allocates nothing, touches no stream and commits no frame, so the
contract takes the runtime context and the map value only.  There is no
dead arm and no ledger row. -/
def Func9Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (map key : UInt32) (k0 k1 : UInt64)
    (t : HashMap.Table UInt32 UInt32)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    CallContract 12 [.i32 key, .i32 map]
      callerLocals stack code arity remainder controls calls s E Φ iprop(
        RuntimeContext ∗
        HashMap.Table.HashMapAt 0 map k0 k1 t ∗
        ⌜HashMap.Table.WF (HashMap.SipHash.hashU32 k0 k1) t ∧
          HashMap.Table.Clean t ∧ map.toNat + 32 < UInt32.size⌝ ∗
        (RuntimeContext -∗
          HashMap.Table.HashMapAt 0 map k0 k1 t -∗
          ResumeWP
            [.i32 (if HashMap.Table.containsKey
                (HashMap.SipHash.hashU32 k0 k1) t key = true
              then (1 : UInt32) else 0)]
            callerLocals stack code arity remainder controls calls s E Φ))

/-! ## Absolute `func 20`, local `func17`: `get` -/

/-- Absolute `func 20`, WAT 4771 to 5056.  The arguments in source order are
the eight-byte output slot, the map value and the key, so the operand list
below carries the key on top and the slot at the bottom.

The two stores at WAT 5050 to 5055 build `Table.optionU32At`: the
discriminant at `out` and the payload at `out + 4`.  The `some` arm loads
the payload from the value half of the found bucket at WAT 5041 to 5045.
The `none` arm writes the discriminant `0` and leaves local 13 at whatever
the loop left, which is why the payload word of `none` is free.

The body allocates nothing, touches no stream and commits no frame.  There
is no dead arm and no ledger row. -/
def Func17Spec [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (out map key : UInt32) (k0 k1 : UInt64)
    (t : HashMap.Table UInt32 UInt32) (outBefore : List UInt8)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    CallContract 20 [.i32 key, .i32 map, .i32 out]
      callerLocals stack code arity remainder controls calls s E Φ iprop(
        RuntimeContext ∗
        Slices.ByteSlice 0 out outBefore ∗
        HashMap.Table.HashMapAt 0 map k0 k1 t ∗
        ⌜outBefore.length = 8 ∧ out.toNat + 8 < UInt32.size ∧
          map.toNat + 32 < UInt32.size ∧
          HashMap.Table.WF (HashMap.SipHash.hashU32 k0 k1) t ∧
          HashMap.Table.Clean t⌝ ∗
        (RuntimeContext -∗
          HashMap.Table.optionU32At 0 out
            (HashMap.Table.get (HashMap.SipHash.hashU32 k0 k1) t key) -∗
          HashMap.Table.HashMapAt 0 map k0 k1 t -∗
          ResumeWP [] callerLocals stack code arity remainder controls
            calls s E Φ))

end Project.RustHashMap.LookupContracts
