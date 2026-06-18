import CodeLib.RustStd.Frame
import Interpreter.Wasm.Wp.Tactic
import CodeLib.Entry

/-!
# `u64::count_ones` — reusable body theorem (Group A)

`count_ones` is a compiler intrinsic: at `opt-level = 0` its body is the
`i64.popcnt` core wrapped in the standard frame spill. The theorem is stated
in **weakest-precondition** form, directly about the body — no module/index
or host-function hypotheses, no `TerminatesWith`. `of_returns_wp` lifts it to
the `TerminatesWith` form a concrete crate (or a caller) needs.
-/

namespace Wasm.RustStd.U64

open Wasm

/-- The opt-0 body of `u64::count_ones`: frame setup, `popcnt`, spill the
result to `[fp+12]`, reload it, return. -/
def countOnesBody : Program :=
  [ .globalGet 0, .const (16 : UInt32), .sub, .localSet 1,
    .localGet 1, .localGet 0, .popcntI64, .wrapI64, .store32 (12 : UInt32),
    .localGet 1, .load32 (12 : UInt32), .ret ]

/-- The `Function` record `count_ones` decodes to. -/
def countOnesFunc : Function :=
  { params := [.i64], locals := [.i32], body := countOnesBody, results := [.i32] }

set_option maxRecDepth 4096 in
/-- Running `count_ones`'s body with `v` in local 0 returns the population
count of `v` on top of the stack, leaving the stack pointer (global 0) and the
memory size untouched. `sp` is the stack-pointer value; `16 ≤ sp ≤ pages·64KiB`
are the no-trap bounds on the frame spill. -/
theorem countOnes_wp {α} {m : Module} {env : HostEnv α} (st : Store α)
    (sp : UInt32) (v : UInt64) (vs : List Value)
    (hsp : st.globals.globals[0]? = some (.i32 sp))
    (hlo : 16 ≤ sp.toNat) (hhi : sp.toNat ≤ st.mem.pages * 65536) :
    wp m countOnesBody
      (Returns (.i32 (UInt32.ofNat (popcnt64 64 v 0)) :: vs)
        (fun st' => st'.globals = st.globals ∧ st'.mem.pages = st.mem.pages))
      st ⟨[.i64 v], [.i32 0], vs⟩ env := by
  unfold countOnesBody Returns
  wp_run
  have hle : (16 : UInt32) ≤ sp := UInt32.le_iff_toNat_le.mpr (by simpa using hlo)
  have hsub : (sp - 16).toNat = sp.toNat - 16 := UInt32.toNat_sub_of_le sp 16 hle
  have hp32 : popcnt64 64 v 0 < 2 ^ 32 := popcnt64_lt_2pow32 v
  have hp64 : popcnt64 64 v 0 < 2 ^ 64 := by omega
  have h12 : ((12 : UInt32)).toNat = 12 := rfl
  have hnt : ¬ ((sp - 16).toNat + 12 + 4 > st.mem.pages * 65536) := by rw [hsub]; omega
  have key : (UInt64.ofNat (popcnt64 64 v 0)).toNat % 2 ^ 32 = popcnt64 64 v 0 := by
    have hb : (UInt64.ofNat (popcnt64 64 v 0)).toNat = popcnt64 64 v 0 % 2 ^ 64 := by
      show (BitVec.ofNat 64 (popcnt64 64 v 0)).toNat = popcnt64 64 v 0 % 2 ^ 64
      exact BitVec.toNat_ofNat _ _
    rw [hb, Nat.mod_eq_of_lt hp64]; exact Nat.mod_eq_of_lt hp32
  simp only [hsp, List.length_cons, List.length_nil, Nat.reduceLT, Nat.reduceAdd,
    Nat.reduceSub, reduceIte, List.set_cons_zero, List.getElem?_cons_zero,
    h12, hnt, Mem.read32_write32_same, Mem.write32_pages, key,
    Continuation.Return.injEq, exists_eq_left', and_true]

end Wasm.RustStd.U64
