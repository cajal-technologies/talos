import Interpreter.Wasm

namespace Wasm.SepLogic

open Wasm

axiom dlmalloc_alloc_spec
    (env : HostEnv Unit) (m : Module)
    (st : Store Unit) (n : UInt32)
    (hpristine : ∀ i, i < 1050240 →
      st.mem.bytes i = (m.initialStore (α := Unit)).mem.bytes i)
    (hmargin : 1050240 + 4 * n.toNat ≤ st.mem.pages * 65536) :
    TerminatesWith env m 5 st [.i32 n]
      (fun st' rs => ∃ ptr : UInt32,
        rs = [.i32 ptr] ∧
        1050240 ≤ ptr.toNat ∧
        ptr.toNat + 4 * n.toNat ≤ st'.mem.pages * 65536 ∧
        st'.mem.pages * 65536 ≤ 4294967296 ∧
        (∀ i, i ≥ 1050240 + 4 * n.toNat →
          st'.mem.bytes i = st.mem.bytes i))

end Wasm.SepLogic
