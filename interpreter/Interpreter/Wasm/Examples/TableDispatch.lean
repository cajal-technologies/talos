import Interpreter.Wasm.Decoder.Wat
import Interpreter.Wasm.Wp.Tactic

/-! ## Example: table instructions (`table.get`, `table.size`)

    A *dispatch table* is a `funcref` table whose slots hold references to
    functions; `call_indirect` then jumps through a slot chosen at runtime.
    This file exercises the two read-only table instructions that inspect
    such a table without dispatching:

    * `table.size t` — push the table's current length (an `i32`);
    * `table.get  t` — pop an `i32` index `i` and push `tables[t][i]` as a
      `funcref` (trapping `out of bounds table access` when `i` is past the
      end). The pushed `funcref` is exactly the value the reference
      instructions from `RefIsNull` already know how to test, so the two
      slices compose: `table.get` then `ref.is_null` asks "is slot `i`
      null?".

    Two halves, as usual:
    * `tableProbeSpec` is a Hoare-style `wp` proof about the AST directly.
      Because `table.get`/`table.size` read the store, the proof is stated
      for *any* store whose table 0 has the concrete contents we care about
      (the `htbl` hypothesis), mirroring how the memory examples pin
      `st.mem` with a hypothesis.
    * the `Decoded` section feeds real `.wat` text through the decoder and
      checks, by computation (`native_decide`), that it lowers to the right
      instructions and that the whole dispatch table runs correctly —
      including a genuine `call_indirect` through the slots `table.get`
      reads. -/

namespace Wasm

/-- `TableProbe` reads table 0 three ways: it asks whether slot 2 is null
(`table.get` then `ref.is_null`) and then pushes the table's size. Run
against a table `[some 0, some 1, none]` it leaves the operand stack
`[.i32 3, .i32 1]` (top first): slot 2 is null so `ref.is_null ⇒ 1`, and
the table has length 3. -/
def TableProbe : Program := [
  .const 2,      .tableGet 0,   -- read slot 2 (the null slot) → funcref none
  .refIsNull,                   -- test it             → push i32 1 (is null)
  .tableSize 0                  -- table length        → push i32 3
]

theorem tableProbeSpec (m : Module) (st : Store Unit)
    (htbl : st.tables = [[some 0, some 1, none]]) :
    wp m TableProbe
        (fun c => c = .Fallthrough st
                    { params := [], locals := [], values := [.i32 3, .i32 1] })
        st { params := [], locals := [], values := [] } := by
  unfold TableProbe
  wp_run
  simp [htbl]

namespace Decoded

/-- A `.wat` dispatch table. `$f0`/`$f1` (indices 0 and 1) are the dispatch
targets; the table holds references to them in slots 0 and 1, leaving slot
2 null. `sz` returns `table.size`; `is_null` returns whether the requested
slot is null (`table.get` ⨾ `ref.is_null`); `dispatch` calls through the
chosen slot with `call_indirect`. -/
def dispatchWat : String := "
(module
  (type $sig (func (result i32)))
  (func $f0 (result i32) i32.const 10)
  (func $f1 (result i32) i32.const 20)
  (table 3 funcref)
  (elem (i32.const 0) $f0 $f1)
  (func $sz (export \"sz\") (result i32)
    table.size)
  (func $is_null (export \"is_null\") (param i32) (result i32)
    local.get 0
    table.get
    ref.is_null)
  (func $dispatch (export \"dispatch\") (param i32) (result i32)
    local.get 0
    call_indirect (type $sig)))
"

private def decoded : Wasm.Module :=
  match Wasm.Decoder.Wat.decode dispatchWat with
  | .ok m    => m
  | .error _ => default

/-- Decoding succeeds with all five functions (rules out the `default`
fallback above; `Instruction` has no `DecidableEq`, so we check a
decidable projection rather than the bodies directly). -/
theorem decodes_five_funcs : decoded.funcs.length = 5 := by native_decide

/-- The active element segment populates table 0 as `[some 0, some 1, none]`:
slots 0 and 1 reference `$f0`/`$f1`, slot 2 stays null. This pins down the
`(elem (i32.const 0) $f0 $f1)` decode and the initial-store construction. -/
theorem table_populated :
    (decoded.initialStore (α := Unit)).tables = [[some 0, some 1, none]] := by
  native_decide

private def runVals (idx : Nat) (args : List Value) : List Value :=
  match run 20 decoded idx (decoded.initialStore (α := Unit)) args with
  | .Success vs _ => vs
  | _ => []

/-- End-to-end (decode → run): `table.size` reports the declared length 3. -/
theorem sz_runs : runVals 2 [] = [.i32 3] := by native_decide

/-- End-to-end (decode → run): slot 0 references `$f0`, so it is not null
(`table.get 0` ⨾ `ref.is_null` ⇒ 0); slot 2 is the null slot (⇒ 1). -/
theorem is_null_slot0_runs : runVals 3 [.i32 0] = [.i32 0] := by native_decide
theorem is_null_slot2_runs : runVals 3 [.i32 2] = [.i32 1] := by native_decide

/-- End-to-end (decode → run): dispatching through slot 0 calls `$f0`
(⇒ 10) and through slot 1 calls `$f1` (⇒ 20). The same refs `table.get`
reads above are the ones `call_indirect` jumps through here. -/
theorem dispatch_slot0_runs : runVals 4 [.i32 0] = [.i32 10] := by native_decide
theorem dispatch_slot1_runs : runVals 4 [.i32 1] = [.i32 20] := by native_decide

end Decoded
end Wasm
