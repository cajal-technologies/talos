import CodeLib.RustStd.Frame
import Interpreter.Wasm.Wp.Tactic
import Interpreter.Wasm.Wp.Block
import CodeLib.Entry

/-!
# `u64::sub` — reusable body theorem

`u64::sub a b = a - b`. At `opt-level = 0` the `-` operator is inlined to a
single `i64.sub`, so the exported `sub` is its own body (no inner `call`, no
stack frame, no memory spill). `-` on `UInt64` is the wrapping subtraction,
which is exactly what the unchecked `i64.sub` computes — so no underflow
precondition is needed.

Stated in `wp` form about the body. The post-condition keeps the
`globals`/`mem.pages` frame (trivially preserved here, since `sub` mutates no
state) so the theorem still composes under the `call` rule. Because the body
uses neither the shadow stack nor memory, the `sp`/`hsp`/`hlo`/`hhi`
hypotheses of the spill-frame template are dropped.
-/

namespace Wasm.RustStd.U64

open Wasm

/-- Verbatim opt-0 body of `sub`. -/
def subBody : Program :=
  [
  .localGet 0,
  .localGet 1,
  .subI64,
  .ret
]

def subFunc : Function :=
  { params := [.i64, .i64], locals := [], body := subBody, results := [.i64] }

set_option maxRecDepth 4096 in
/-- `u64::sub a b = a - b` (wrapping; `-` on `UInt64` is the wrapping sub). -/
theorem sub_wp {α} {m : Module} {env : HostEnv α} (st : Store α)
    (a : UInt64) (b : UInt64) (vs : List Value) :
    wp m subBody
      (Returns (.i64 (a - b) :: vs)
        (fun st' => st'.globals = st.globals ∧ st'.mem.pages = st.mem.pages))
      st ⟨[.i64 a, .i64 b], [], vs⟩ env := by
  unfold subBody Returns
  wp_run
  simp

end Wasm.RustStd.U64
