import CodeLib.RustStd.Frame
import Interpreter.Wasm.Wp.Tactic
import Interpreter.Wasm.Wp.Block
import CodeLib.Entry

/-! `u64::min` — `core::cmp::Ord::min`, the framed inner function the exported
`min` wrapper `call`s. Same shape as `max` (spill both operands, compare, spill
the loser); only the two branch stores swap. Reusable via the call rule. -/

set_option linter.unusedSimpArgs false

namespace Wasm.RustStd.U64
open Wasm

/-- Verbatim opt-0 body of `core::cmp::Ord::min` for `u64`. -/
def minBody : Program :=
  [ .globalGet 0, .const (32 : UInt32), .sub, .localSet 2,
    .localGet 2, .localGet 0, .store64 (8 : UInt32),
    .localGet 2, .localGet 1, .store64 (16 : UInt32),
    .block 0 0 [
      .block 0 0 [
        .localGet 2, .load64 (16 : UInt32), .localGet 2, .load64 (8 : UInt32), .ltUI64,
        .const (1 : UInt32), .and, .br_if 0,
        .localGet 2, .localGet 2, .load64 (8 : UInt32), .store64 (24 : UInt32), .br 1 ],
      .localGet 2, .localGet 2, .load64 (16 : UInt32), .store64 (24 : UInt32) ],
    .localGet 2, .load64 (24 : UInt32), .ret ]

def minFunc : Function :=
  { params := [.i64, .i64], locals := [.i32], body := minBody, results := [.i64] }

set_option maxRecDepth 4096 in
theorem min_wp {α} {m : Module} {env : HostEnv α} (st : Store α)
    (sp : UInt32) (a b : UInt64) (vs : List Value)
    (hsp : st.globals.globals[0]? = some (.i32 sp))
    (hlo : 32 ≤ sp.toNat) (hhi : sp.toNat ≤ st.mem.pages * 65536) :
    wp m minBody
      (Returns (.i64 (if b < a then b else a) :: vs)
        (fun st' => st'.globals = st.globals ∧ st'.mem.pages = st.mem.pages))
      st ⟨[.i64 a, .i64 b], [.i32 0], vs⟩ env := by
  unfold minBody Returns
  have hle  : (32 : UInt32) ≤ sp := UInt32.le_iff_toNat_le.mpr (by simpa using hlo)
  have hle24 : (24 : UInt32) ≤ sp := UInt32.le_iff_toNat_le.mpr (by simpa using (by omega : 24 ≤ sp.toNat))
  have hle16 : (16 : UInt32) ≤ sp := UInt32.le_iff_toNat_le.mpr (by simpa using (by omega : 16 ≤ sp.toNat))
  have hsub   : (sp - 32).toNat = sp.toNat - 32 := UInt32.toNat_sub_of_le sp 32 hle
  have hsub24 : (sp - 24).toNat = sp.toNat - 24 := UInt32.toNat_sub_of_le sp 24 hle24
  have hsub16 : (sp - 16).toNat = sp.toNat - 16 := UInt32.toNat_sub_of_le sp 16 hle16
  have h8  : (8  : UInt32).toNat = 8  := rfl
  have h16 : (16 : UInt32).toNat = 16 := rfl
  have h24 : (24 : UInt32).toNat = 24 := rfl
  have hnt8  : ¬ ((sp - 32).toNat + 8  + 8 > st.mem.pages * 65536) := by rw [hsub]; omega
  have hnt16 : ¬ ((sp - 32).toNat + 16 + 8 > st.mem.pages * 65536) := by rw [hsub]; omega
  have hnt24 : ¬ ((sp - 32).toNat + 24 + 8 > st.mem.pages * 65536) := by rw [hsub]; omega
  have e8  : (sp - 32) + 8  = sp - 24 := by bv_decide
  have e16 : (sp - 32) + 16 = sp - 16 := by bv_decide
  have hd : ((sp - 32) + 8).toNat + 8 ≤ ((sp - 32) + 16).toNat := by
    rw [e8, e16, hsub24, hsub16]; omega
  have hr16 : ((st.mem.write64 ((sp - 32) + 8) a).write64 ((sp - 32) + 16) b).read64 ((sp - 32) + 16) = b :=
    Mem.read64_write64_same _ _ _
  have hr8 : ((st.mem.write64 ((sp - 32) + 8) a).write64 ((sp - 32) + 16) b).read64 ((sp - 32) + 8) = a := by
    rw [Mem.read64_write64_disjoint _ ((sp - 32) + 8) ((sp - 32) + 16) b (Or.inl hd)]
    exact Mem.read64_write64_same _ _ _
  simp only [wp_simp, Locals.get, Locals.set?, Function.toLocals,
    Function.numParams, Function.numLocals, List.take, List.drop, List.replicate, List.length,
    List.map, ValueType.zero, List.headD, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.set_cons_zero, List.set_cons_succ,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte, hsp, hnt8, hnt16,
    h8, h16, h24, Mem.write64_pages]
  apply wp_block_cons
  apply wp_block_cons
  by_cases hba : b < a <;>
    simp [hba, hnt8, hnt16, hnt24, h8, h16, h24, hr8, hr16, Mem.read64_write64_same,
      Mem.write64_pages] <;>
    omega

end Wasm.RustStd.U64
