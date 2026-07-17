import Interpreter.Wasm.Decoder.Wat
import Interpreter.Wasm.Wp.Tactic
import Interpreter.Wasm.Examples.Harness

/-! ## Example: const-expr data/elem segment offsets

    An active data or element segment's offset is a constant expression,
    not just a literal: wasm 1.0 permits `global.get`, and the
    extended-const proposal adds `i32.add`/`i32.sub`/`i32.mul` (i64
    ditto). Talos keeps such offsets as a program in
    `DataSegment.offsetExpr` / `ElementSegment.offsetExpr`; the segment
    is skipped by `Module.initialStore` and written at instantiation by
    `Module.runActiveSegments`, once `Module.runConstGlobals` has put
    the globals in place.

    This module is the regression test for issue #101, where such
    segments landed at offset 0: the data below must end up at byte 4,
    and the table entry at slot 2, or the theorems fail the build. -/

namespace Wasm
open Wasm.Examples
namespace SegmentOffsetExpr

/-- A module whose data segment lands at `global.get $o = 4` and whose
element segment lands at `global.get $t = 2`. `readByte4` observes the
data placement; `callAt2` observes the element placement (it traps if
the funcref landed at slot 0 instead). -/
def segmentOffsetWat : String := "
(module
  (global $o i32 (i32.const 4))
  (global $t i32 (i32.const 2))
  (memory 1)
  (data (offset (global.get $o)) \"ABCD\")
  (table 4 funcref)
  (elem (offset (global.get $t)) $f42)
  (type $ri (func (result i32)))
  (func $f42 (type $ri) (i32.const 42))
  (func $readByte4 (export \"readByte4\") (result i32)
    (i32.load8_u (i32.const 4)))
  (func $callAt2 (export \"callAt2\") (result i32)
    (call_indirect (type $ri) (i32.const 2))))
"

private def decoded : Wasm.Module := decodeOrDefault segmentOffsetWat

/-- The non-literal offsets are kept as programs rather than collapsed
to a `0` placeholder: both segments carry a non-empty `offsetExpr`. -/
theorem decoded_segments_keep_offsetExpr :
    ((decoded.memory.bind (·.data[0]?)).map (·.offsetExpr.isEmpty)).getD true = false
    ∧ (decoded.elements[0]?.map (·.offsetExpr.isEmpty)).getD true = false := by
  constructor <;> native_decide

/-- The instantiated store used by the theorems below: base store, then
global initializers, then the deferred const-expr-offset segments. -/
private def store0 : Store Unit :=
  let m := decoded
  m.runActiveSegments 64 (m.runConstGlobals 64 (m.initialStore (α := Unit)) {}) {}

/-- `runActiveSegments` writes the data segment at the evaluated offset:
byte 4 holds `'A' = 65`. The issue-#101 behaviour — the segment landing
at offset 0 — would leave byte 4 zero. -/
theorem readByte4_returns_65 :
    runValues 64 decoded ((decoded.findExport "readByte4").getD 0) store0 []
      = [.i32 65] := by
  native_decide

/-- Likewise the element segment: the funcref lands in table slot 2, so
`call_indirect` at index 2 reaches `$f42`. With the segment at slot 0
this call trapped on a null table entry. -/
theorem callAt2_returns_42 :
    runValues 64 decoded ((decoded.findExport "callAt2").getD 0) store0 []
      = [.i32 42] := by
  native_decide

/-- And nothing leaked to the old placeholder location: byte 0 of the
memory is still zero (the segment was *moved*, not duplicated). -/
theorem byte0_still_zero : store0.mem.read8 0 = 0 := by
  native_decide

end SegmentOffsetExpr
end Wasm
