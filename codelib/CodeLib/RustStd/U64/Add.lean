import CodeLib.RustStd.Frame
import Interpreter.Wasm.Wp.Tactic
import Interpreter.Wasm.Wp.Block
import CodeLib.Entry

/-!
# `u64::add` — reusable body theorem

`u64::add a b = a + b`. At `opt-level = 0` the `+` operator is inlined to a
single `i64.add`, so the exported `add` is its own body (no inner `call`, no
stack frame, no memory spill). `+` on `UInt64` is the wrapping addition, which
is exactly what the unchecked `i64.add` computes — so no overflow precondition
is needed.

Stated in `wp` form about the body. The post-condition keeps the
`globals`/`mem.pages` frame (trivially preserved here, since `add` mutates no
state) so the theorem still composes under the `call` rule. Because the body
uses neither the shadow stack nor memory, the `sp`/`hsp`/`hlo`/`hhi`
hypotheses of the spill-frame template are dropped.
-/

namespace Wasm.RustStd.U64

open Wasm

/-- Verbatim opt-0 body of `add`. -/
def addBody : Program :=
  [
  .localGet 0,
  .localGet 1,
  .addI64,
  .ret
]

def addFunc : Function :=
  { params := [.i64, .i64], locals := [], body := addBody, results := [.i64] }

set_option maxRecDepth 4096 in
/-- `u64::add a b = a + b` (wrapping; `+` on `UInt64` is the wrapping add). -/
theorem add_wp {α} {m : Module} {env : HostEnv α} (st : Store α)
    (a : UInt64) (b : UInt64) (vs : List Value) :
    wp m addBody
      (Returns (.i64 (a + b) :: vs)
        (fun st' => st'.globals = st.globals ∧ st'.mem.pages = st.mem.pages))
      st ⟨[.i64 a, .i64 b], [], vs⟩ env := by
  unfold addBody Returns
  wp_run
  simp

end Wasm.RustStd.U64
