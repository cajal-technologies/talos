import CodeLib.RustStd.Frame
import Interpreter.Wasm.Wp.Tactic
import Interpreter.Wasm.Wp.Block
import CodeLib.Entry

/-!
# `u64::mul` — reusable body theorem

`u64::mul a b = a * b`. At `opt-level = 0` the `*` operator is inlined to a
single `i64.mul`, so the exported `mul` is its own body (no inner `call`, no
stack frame, no memory spill). `*` on `UInt64` is the wrapping multiplication,
which is exactly what the unchecked `i64.mul` computes — so no overflow
precondition is needed.

Stated in `wp` form about the body. The post-condition keeps the
`globals`/`mem.pages` frame (trivially preserved here, since `mul` mutates no
state) so the theorem still composes under the `call` rule. Because the body
uses neither the shadow stack nor memory, the `sp`/`hsp`/`hlo`/`hhi`
hypotheses of the spill-frame template are dropped.
-/

namespace Wasm.RustStd.U64

open Wasm

/-- Verbatim opt-0 body of `mul`. -/
def mulBody : Program :=
  [
  .localGet 0,
  .localGet 1,
  .mulI64,
  .ret
]

def mulFunc : Function :=
  { params := [.i64, .i64], locals := [], body := mulBody, results := [.i64] }

set_option maxRecDepth 4096 in
/-- `u64::mul a b = a * b` (wrapping; `*` on `UInt64` is the wrapping mul). -/
theorem mul_wp {α} {m : Module} {env : HostEnv α} (st : Store α)
    (a : UInt64) (b : UInt64) (vs : List Value) :
    wp m mulBody
      (Returns (.i64 (a * b) :: vs)
        (fun st' => st'.globals = st.globals ∧ st'.mem.pages = st.mem.pages))
      st ⟨[.i64 a, .i64 b], [], vs⟩ env := by
  unfold mulBody Returns
  wp_run
  simp

end Wasm.RustStd.U64
