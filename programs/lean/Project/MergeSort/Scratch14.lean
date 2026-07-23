import Project.MergeSort.SortSepLogic

namespace Wasm.SepLogic.MergeSort

variable [WasmHeapGS]

open Wasm Wasm.SepLogic Project.MergeSort Project.MergeSort.Spec Project.MergeSort.Framing
open Iris.BI

-- scratch file to develop func14_iProp proof interactively
example
    (env : HostEnv Unit) (st : Store Unit)
    (out ptr len mid pl : UInt32) (a b c d : UInt32)
    (hb : out.toNat + 16 ≤ st.mem.pages * 65536) :
    arrayAt out [a, b, c, d] ⊢
    wp_wasm «module» st
      (func14Def.toLocals [.i32 out, .i32 ptr, .i32 len, .i32 mid, .i32 pl])
      func14 env
      (fun st' vs => vs = [] ∧
        st' = { st with mem :=
          (((st.mem.write32 out ptr).write32 (out + 4) mid).write32
            (out + 8) (ptr + mid <<< 2)).write32 (out + 12) (len - mid) }) := by
  simp only [arrayAt_cons, arrayAt_nil]
  sorry

end Wasm.SepLogic.MergeSort
