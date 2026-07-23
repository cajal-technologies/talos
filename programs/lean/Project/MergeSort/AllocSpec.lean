import Interpreter.Wasm
import Project.MergeSort.Program

namespace Wasm.SepLogic
open Wasm Project.MergeSort

axiom dlmalloc_alloc_spec
    (env : HostEnv Unit)
    (st : Store Unit) (n : UInt32)
    (hpristine : ∀ i, i < 1050240 →
      st.mem.bytes i = («module».initialStore (α := Unit)).mem.bytes i)
    (hmargin : 1050240 + 4 * n.toNat ≤ st.mem.pages * 65536) :
    TerminatesWith env «module» 5 st [.i32 n]
      (fun st' rs => ∃ ptr : UInt32,
        rs = [.i32 ptr] ∧
        1050240 ≤ ptr.toNat ∧
        ptr.toNat + 4 * n.toNat ≤ st'.mem.pages * 65536 ∧
        st'.mem.pages * 65536 ≤ 4294967296 ∧
        st'.globals = st.globals ∧
        (∀ i, i ≥ 1050240 + 4 * n.toNat →
          st'.mem.bytes i = st.mem.bytes i))

axiom run_env_indep
    (hm : «module».imports.length = 0)
    (fuel id : Nat) (st : Store Unit) (args : List Value)
    (env env' : HostEnv Unit) :
    run fuel «module» id st args env = run fuel «module» id st args env'

end Wasm.SepLogic
