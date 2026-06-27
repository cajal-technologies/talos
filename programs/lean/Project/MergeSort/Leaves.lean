import Project.MergeSort.Framing
import CodeLib.Entry
import Interpreter.Wasm.Wp.Tactic
import Interpreter.Wasm.Wp.Block

/-!
# Phase B — leaf function specs (split_at_mut)

`func14` is the inner store-the-two-descriptors helper of `split_at_mut`:
given `(out, ptr, len, mid)` it writes the pair of `(ptr,len)` slice
descriptors `(ptr, mid)` and `(ptr + 4*mid, len - mid)` into the 16-byte
struct at `out`. No stack frame, no calls.
-/

namespace Project.MergeSort.Leaves

open Wasm Project.MergeSort

set_option maxRecDepth 8192 in
theorem func14_tw (env : HostEnv Unit) (st : Store Unit)
    (out ptr len mid pl : UInt32)
    (hb : out.toNat + 16 ≤ st.mem.pages * 65536) :
    TerminatesWith env «module» 14 st
      [.i32 pl, .i32 mid, .i32 len, .i32 ptr, .i32 out]
      (fun st' vs => vs = [] ∧
        st' = { st with mem :=
          (((st.mem.write32 out ptr).write32 (out + 4) mid).write32
            (out + 8) (ptr + mid <<< 2)).write32 (out + 12) (len - mid) }) := by
  apply TerminatesWith.of_wp_entry_for (f := func14Def) rfl
  unfold func14Def func14
  wp_run
  simp
  refine ⟨by omega, by omega, by omega, by omega, ?_⟩
  rw [UInt32.add_comm (mid <<< 2) ptr]

end Project.MergeSort.Leaves
