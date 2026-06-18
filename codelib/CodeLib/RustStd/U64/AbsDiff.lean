import CodeLib.RustStd.Frame
import Interpreter.Wasm.Wp.Tactic
import Interpreter.Wasm.Wp.Block
import CodeLib.Entry

/-!
# `u64::abs_diff` — reusable body theorem (Group B)

`abs_diff` is **not** an intrinsic: at `opt-level = 0` it is compiled to a
real, separately-callable leaf function (`core::num::<impl u64>::abs_diff`)
that callers invoke via `call`. That is the genuine "prove once, reuse
across calls" target — the same body appears, byte-for-byte, in every crate
that uses `abs_diff`, only the function index differs.

The theorem is *body-parametric*: it holds for this exact body at any index
in any module with a stack-pointer global and enough memory. A caller in
another crate discharges its own `call abs_diff` by feeding this theorem to
the interpreter's `wp_call_tw` rule.
-/

namespace Wasm.RustStd.U64

open Wasm

/-- The opt-0 body of `u64::abs_diff`: branch on `a < b`, subtract the
smaller from the larger, spill to `[fp+8]`, reload, return. -/
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
/-- `abs_diff a b` returns the absolute difference of its `u64` arguments.
Reusable across modules/calls via `hf` (this body is function `id`), `hsp`
(global 0 is the stack pointer `sp`), and the no-trap bounds on `sp`.

Argument order: the wasm calling convention reverses the operand stack into
locals, so the args read `.i64 b :: .i64 a :: rest` (giving local 0 = `a`,
local 1 = `b`). The trailing `rest` is the **stack frame**: any operands the
caller left *below* the arguments. Carrying it explicitly is what lets this
spec compose under a `call` when earlier results are still on the stack
(e.g. the second `abs_diff` call inside Manhattan distance). -/
theorem absDiff_terminates {α} (env : HostEnv α) (m : Module) (id : Nat)
    (st : Store α) (a b : UInt64) (sp : UInt32) (rest : List Value)
    (hf : m.funcs[id - m.imports.length]? = some absDiffFunc)
    (hsp : st.globals.globals[0]? = some (.i32 sp))
    (hlo : 16 ≤ sp.toNat) (hhi : sp.toNat ≤ st.mem.pages * 65536)
    (hImp : m.imports[id]? = none) :
    TerminatesWith env m id st (.i64 b :: .i64 a :: rest)
      (fun st' rs => rs = .i64 (if a < b then b - a else a - b) :: rest
        ∧ st'.globals = st.globals ∧ st'.mem.pages = st.mem.pages) := by
  refine TerminatesWith.of_wp_entry_for (f := absDiffFunc) hf ?_ hImp
  unfold absDiffFunc absDiffBody
  wp_run
  simp only [hsp, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    List.length_cons, List.length_nil,
    Nat.reduceLT, Nat.reduceAdd, Nat.reduceSub, reduceIte, List.set_cons_zero]
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
