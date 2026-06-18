import CodeLib.RustStd.Frame
import Interpreter.Wasm.Wp.Tactic
import Interpreter.Wasm.Wp.Block
import CodeLib.Entry

/-!
# `u64::abs_diff` — reusable body theorem (Group B)

`abs_diff` is **not** an intrinsic: at `opt-level = 0` it is compiled to a
real, separately-callable leaf function (`core::num::<impl u64>::abs_diff`)
that callers invoke via `call`. That is the genuine "prove once, reuse across
calls" target — the same body appears byte-for-byte in every crate that uses
`abs_diff`, only the function index differs.

Stated in **weakest-precondition** form about the body — no module/index or
host-function hypotheses, no `TerminatesWith`. `of_returns_wp` lifts it to the
`TerminatesWith` the call rule consumes, so a caller (e.g. Manhattan distance)
reuses this directly.
-/

namespace Wasm.RustStd.U64

open Wasm

/-- The opt-0 body of `u64::abs_diff`: branch on `a < b`, subtract the smaller
from the larger, spill to `[fp+8]`, reload, return. -/
def absDiffBody : Program :=
  [ .globalGet 0, .const (16 : UInt32), .sub, .localSet 2,
    .block 0 0 [
      .block 0 0 [
        .localGet 0, .localGet 1, .ltUI64, .const (1 : UInt32), .and, .br_if 0,
        .localGet 2, .localGet 0, .localGet 1, .subI64, .store64 (8 : UInt32), .br 1 ],
      .localGet 2, .localGet 1, .localGet 0, .subI64, .store64 (8 : UInt32) ],
    .localGet 2, .load64 (8 : UInt32), .ret ]

/-- The `Function` record `abs_diff` decodes to. -/
def absDiffFunc : Function :=
  { params := [.i64, .i64], locals := [.i32], body := absDiffBody, results := [.i64] }

set_option maxRecDepth 4096 in
/-- Running `abs_diff`'s body with `a` in local 0 and `b` in local 1 returns
the absolute difference `if a < b then b - a else a - b` on top of the stack,
leaving the stack pointer (global 0) and the memory size untouched. -/
theorem absDiff_wp {α} {m : Module} {env : HostEnv α} (st : Store α)
    (sp : UInt32) (a b : UInt64) (vs : List Value)
    (hsp : st.globals.globals[0]? = some (.i32 sp))
    (hlo : 16 ≤ sp.toNat) (hhi : sp.toNat ≤ st.mem.pages * 65536) :
    wp m absDiffBody
      (Returns (.i64 (if a < b then b - a else a - b) :: vs)
        (fun st' => st'.globals = st.globals ∧ st'.mem.pages = st.mem.pages))
      st ⟨[.i64 a, .i64 b], [.i32 0], vs⟩ env := by
  unfold absDiffBody Returns
  wp_run
  simp only [hsp]
  apply wp_block_cons
  apply wp_block_cons
  wp_run
  have hle : (16 : UInt32) ≤ sp := UInt32.le_iff_toNat_le.mpr (by simpa using hlo)
  have hsub : (sp - 16).toNat = sp.toNat - 16 := UInt32.toNat_sub_of_le sp 16 hle
  have hnt : ¬ ((sp - 16).toNat + 8 + 8 > st.mem.pages * 65536) := by rw [hsub]; omega
  have h8 : ((8 : UInt32)).toNat = 8 := rfl
  by_cases hab : a < b <;>
    simp [hab, h8, hnt, Mem.read64_write64_same, Mem.write64_pages]

end Wasm.RustStd.U64
