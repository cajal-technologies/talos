import Interpreter.Wasm.Decoder.Wat
import Interpreter.Wasm.Wp.Tactic

/-! ## Example: `table.set`

    `table.set t` pops a `funcref` from the top of the stack and an i32 index
    from just below it, then writes the funcref into `tables[t][i]`.  The i32
    must be pushed *before* the funcref so that the funcref ends up on top.

    Two halves:
    * `tableSetRoundTripSpec` proves the AST program directly via `wp_run`:
      write `funcref 0` into slot 1, then read it back with `table.get`.
    * the `Decoded` section feeds `.wat` text through the decoder and checks
      the write-then-read round-trip and the null-slot case (`native_decide`). -/

namespace Wasm

/-- `TableSetRoundTrip` writes `funcref 0` into slot 1 of table 0 and then
reads it back.  The i32 index is pushed first so the funcref sits on top when
`table.set` executes.  Against a starting table `[some 0, none]` the final
stack holds `[.funcref (some 0)]` and table 0 is `[some 0, some 0]`. -/
def TableSetRoundTrip : Program := [
  .const 1,     -- push index 1 (i32; goes below on stack)
  .refFunc 0,   -- push funcref 0 (lands on top)
  .tableSet 0,  -- tables[0][1] := funcref 0
  .const 1,     -- push index 1
  .tableGet 0   -- push tables[0][1] = funcref (some 0)
]

theorem tableSetRoundTripSpec (m : Module) (st : Store Unit)
    (htbl : st.tables = [[some 0, none]]) :
    wp m TableSetRoundTrip
        (fun c => c = .Fallthrough { st with tables := [[some 0, some 0]] }
                    { params := [], locals := [], values := [.funcref (some 0)] })
        st { params := [], locals := [], values := [] } := by
  unfold TableSetRoundTrip
  wp_run
  simp [htbl]

namespace Decoded

/-- A `.wat` module with a 2-slot funcref table and two exported functions:
`set_and_check` writes `funcref $f0` into the given slot then reads it back,
returning 0 (not null); `check_null` reads a never-written slot, returning 1
(null). -/
def tableSetWat : String := "
(module
  (func $f0 (result i32) i32.const 7)
  (table 2 funcref)
  (func $set_and_check (export \"set_and_check\") (param i32) (result i32)
    local.get 0
    ref.func $f0
    table.set
    local.get 0
    table.get
    ref.is_null)
  (func $check_null (export \"check_null\") (param i32) (result i32)
    local.get 0
    table.get
    ref.is_null))
"

private def decoded : Wasm.Module :=
  match Wasm.Decoder.Wat.decode tableSetWat with
  | .ok m    => m
  | .error _ => default

theorem decodes_three_funcs : decoded.funcs.length = 3 := by native_decide

private def runVals (idx : Nat) (args : List Value) : List Value :=
  match run 20 decoded idx (decoded.initialStore (α := Unit)) args with
  | .Success vs _ => vs
  | _ => []

/-- `set_and_check 1` writes funcref $f0 into slot 1, reads it back, and
returns 0 (not null). -/
theorem set_and_check_slot1 : runVals 1 [.i32 1] = [.i32 0] := by native_decide

/-- Slot 0 is never written; `check_null 0` reads it and returns 1 (null). -/
theorem check_null_slot0 : runVals 2 [.i32 0] = [.i32 1] := by native_decide

end Decoded
end Wasm
