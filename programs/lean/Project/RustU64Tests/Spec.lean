import Project.RustU64Tests.Program
import Interpreter.Wasm.Wp.Call

/-!
# Reuse tests for the `CodeLib/RustStd/U64` corpus

One module exercising each proven u64 std theorem through the `call` rule.
Each section reuses a CodeLib `…_wp` theorem as a black box (via
`of_returns_wp` + `wp_call_tw`) — none of the std bodies are re-proven here.
Add a new section per CodeLib function as the corpus grows.
-/

namespace Project.RustU64Tests.Spec

open Wasm Wasm.RustStd.U64

/-! ## `u64::sub` — `sub_chain3 a b c = (a - b) - c`

`sub` (export idx 0) compiles to the frame-less body that is definitionally
CodeLib's `subFunc`, so each `.call 0` in `sub_chain3` reuses `sub_wp`. -/

/-- `sub` specialized to a call site (operands `b :: a :: rest` on the stack).
No `hsp`/`hhi` side-conditions: `sub` touches neither the shadow stack nor
memory, so `sub_wp` carries no frame hypotheses. -/
private theorem sub_call {env : HostEnv Unit} (st : Store Unit) (a b : UInt64)
    (rest : List Value) :
    TerminatesWith env «module» 0 st (.i64 b :: .i64 a :: rest)
      (fun st' vs => vs = .i64 (a - b) :: rest
        ∧ st'.globals = st.globals ∧ st'.mem.pages = st.mem.pages) :=
  TerminatesWith.of_returns_wp (f := subFunc)
    (rs := [.i64 (a - b)]) rfl rfl
    (sub_wp st a b []) rfl   -- ★ REUSE: the proven CodeLib theorem

@[spec_of "rust-exported" "rust_u64_tests::sub_chain3"]
def SubChain3Spec : Prop :=
  ∀ (env : HostEnv Unit) (a b c : UInt64),
    TerminatesWith env «module» 1 «module».initialStore [.i64 c, .i64 b, .i64 a]
      (fun _ rs => rs = [.i64 (a - b - c)])

set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.SubChain3Spec]
theorem sub_chain3_correct : SubChain3Spec := by
  intro env a b c
  apply TerminatesWith.of_wp_entry_for (f := func1Def) rfl
  unfold func1Def func1
  wp_run
  apply wp_call_tw (sub_call «module».initialStore a b [])          -- ★ REUSE: sub(a, b)
  intro st1 vs1 h1
  obtain ⟨hvs1, _, _⟩ := h1   -- `sub` is frame-less, so the globals/pages facts are unused here
  subst hvs1
  wp_run
  apply wp_call_tw (sub_call st1 (a - b) c [])                      -- ★ REUSE: sub(a-b, c)
  intro st2 vs2 h2
  obtain ⟨hvs2, _, _⟩ := h2
  subst hvs2
  wp_run
  simp

end Project.RustU64Tests.Spec
