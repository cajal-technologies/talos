import CodeLib.RustStd.Frame
import Interpreter.Wasm.Wp.Tactic
import Interpreter.Wasm.Wp.Block
import CodeLib.Entry

/-!
# `u64::div` — reusable body theorem

`u64::div a b = a / b`. At `opt-level = 0` the `/` operator is inlined directly
into the export: no inner `call`, no stack frame, no memory spill. Unlike `+`,
`-`, `*` — whose overflow checks are off under the corpus's release build
(`[profile.release]` with `overflow-checks` defaulting off), so they compile to a
bare wrapping `i64.{add,sub,mul}` — unsigned division is **always** guarded
against a zero divisor, even with overflow checks off: dividing by zero is UB in
LLVM, so rustc must emit the check unconditionally. Hence the body is a `block`
that checks `b == 0` and, when true, breaks out to a panic stub
(`const …; call …; unreachable`, "attempt to divide by zero"). Otherwise the
guard falls through, `i64.div_u` does not trap, and the function returns the
unsigned quotient `a / b` (exactly `UInt64` division).

The panic stub's `const` (a `&Location` pointer) and `call` (the panic handler)
indices are **crate-specific**: a `div` compiled into a different module gets a
different tail. But with `b ≠ 0` that tail is never reached — the guard block
returns first. So `div_wp` is stated over the shared guard `block` (`divGuard`)
followed by an **arbitrary** `tail`, which lets the one CodeLib theorem be
reused under `call` for *any* crate's `div`, regardless of its panic tail (see
`Project.RustU64Tests`). `divBody`/`divFunc` instantiate `tail` at the verbatim
`rust_u64` tail for the per-crate spec.

Stated in `wp` form about the body. The post-condition keeps the
`globals`/`mem.pages` frame (trivially preserved here, since `div` mutates no
state) so the theorem composes under the `call` rule. Because the body uses
neither the shadow stack nor memory, the `sp`/`hsp`/`hlo`/`hhi` hypotheses of
the spill-frame template are dropped; the only hypothesis is the
divisor-nonzero side-condition `hb`.
-/

namespace Wasm.RustStd.U64

open Wasm

/-- The crate-independent guard `block` every opt-0 `u64 / u64` compiles to:
check `b == 0`, break to the panic tail when true, otherwise `i64.div_u` and
return. This prefix is identical across crates; only the trailing panic stub
differs. -/
def divGuard : Instruction :=
  .block 0 0 [
    .localGet 1,
    .constI64 (0 : UInt64),
    .eqI64,
    .const (1 : UInt32),
    .and,
    .br_if 0,
    .localGet 0,
    .localGet 1,
    .divUI64,
    .ret
  ]

/-- Verbatim opt-0 body of `rust_u64::div`: the shared guard followed by this
crate's panic tail (`const`/`call`/`unreachable`). -/
def divBody : Program :=
  divGuard :: [.const (1048600 : UInt32), .call 56, .unreachable]

def divFunc : Function :=
  { params := [.i64, .i64], locals := [], body := divBody, results := [.i64] }

set_option maxRecDepth 4096 in
/-- `u64::div a b = a / b` (unsigned quotient; requires `b ≠ 0`, else the
division traps). Generic in the panic `tail` after the guard `block`: that tail
is unreachable when `b ≠ 0`, so the theorem composes under `call` for any
crate's `div`. -/
theorem div_wp {α} {m : Module} {env : HostEnv α} (st : Store α)
    (a : UInt64) (b : UInt64) (vs : List Value) (tail : Program) (hb : b ≠ 0) :
    wp m (divGuard :: tail)
      (Returns (.i64 (a / b) :: vs)
        (fun st' => st'.globals = st.globals ∧ st'.mem.pages = st.mem.pages))
      st ⟨[.i64 a, .i64 b], [], vs⟩ env := by
  unfold divGuard Returns
  apply wp_block_cons
  wp_run
  simp [hb]

end Wasm.RustStd.U64
