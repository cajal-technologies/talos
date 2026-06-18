import CodeLib.RustStd.Frame
import Interpreter.Wasm.Wp.Tactic
import CodeLib.Entry

/-!
# `u64::count_ones` — reusable body theorem (Group A)

`count_ones` is a compiler intrinsic: at `opt-level = 0` its body is the
`i64.popcnt` core wrapped in the standard frame spill. The theorem here is
*body-parametric* — it holds for this exact body at **any** index in **any**
module, given a stack-pointer global and enough memory not to trap. A
concrete crate discharges those hypotheses with `rfl` / `decide`.

Caveat (Group A): because this is an inlined intrinsic, other crates that
call `x.count_ones()` will not contain this function — they inline
`i64.popcnt` directly. Genuine cross-*call* reuse is the Group B story
(`AbsDiff`); here reuse is exercised by a crate re-exporting the body.
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
/-- `count_ones` returns the population count of its `u64` argument. Reusable
across modules: supply `hf` (this body is function `id`), `hsp` (global 0 is
the stack pointer `sp`), and the no-trap bounds on `sp`. -/
theorem countOnes_terminates {α} (env : HostEnv α) (m : Module) (id : Nat)
    (st : Store α) (v : UInt64) (sp : UInt32)
    (hf : m.funcs[id - m.imports.length]? = some countOnesFunc)
    (hsp : st.globals.globals[0]? = some (.i32 sp))
    (hlo : 16 ≤ sp.toNat) (hhi : sp.toNat ≤ st.mem.pages * 65536)
    (hImp : m.imports[id]? = none) :
    TerminatesWith env m id st [.i64 v]
      (fun _ rs => rs = [.i32 (UInt32.ofNat (popcnt64 64 v 0))]) := by
  refine TerminatesWith.of_wp_entry_for (f := countOnesFunc) hf ?_ hImp
  unfold countOnesFunc countOnesBody
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
  simp only [hsp, List.reverse_cons, List.reverse_nil, List.nil_append, List.length_cons,
    List.length_nil, Nat.sub_self, List.set_cons_zero, List.getElem?_cons_zero,
    Nat.reduceAdd, Nat.reduceLT, reduceIte, h12, hnt, Mem.read32_write32_same,
    Mem.write32_pages, List.append_nil, key]

end Wasm.RustStd.U64
