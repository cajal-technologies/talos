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

/-! ## `u64::div` — `div_chain a b c = (a / b) / c`

`div` (export idx 0) inlines the guarded `i64.div_u`. Its opt-0 body shares the
`divGuard` block with CodeLib's `divFunc`; only the (unreachable, since the
divisors are nonzero) panic tail differs. `div_wp` is generic in that tail, so
each `.call 0` in `div_chain` reuses it. -/

/-- `div` specialized to a call site (operands `b :: a :: rest` on the stack,
divisor `b ≠ 0`). No `hsp`/`hhi` side-conditions: `div` touches neither the
shadow stack nor memory, so `div_wp` carries no frame hypotheses. The panic
`tail` of this crate's `div` (idx 0) is inferred from `func0Def.body`. -/
private theorem div_call {env : HostEnv Unit} (st : Store Unit) (a b : UInt64)
    (rest : List Value) (hb : b ≠ 0) :
    TerminatesWith env «module» 0 st (.i64 b :: .i64 a :: rest)
      (fun st' vs => vs = .i64 (a / b) :: rest
        ∧ st'.globals = st.globals ∧ st'.mem.pages = st.mem.pages) :=
  TerminatesWith.of_returns_wp (f := func0Def)
    (rs := [.i64 (a / b)]) rfl rfl
    (div_wp st a b [] _ hb) rfl   -- ★ REUSE: the proven CodeLib theorem

@[spec_of "rust-exported" "rust_u64_tests::div_chain"]
def DivChainSpec : Prop :=
  ∀ (env : HostEnv Unit) (a b c : UInt64), b ≠ 0 → c ≠ 0 →
    TerminatesWith env «module» 1 «module».initialStore [.i64 c, .i64 b, .i64 a]
      (fun _ rs => rs = [.i64 (a / b / c)])

set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.DivChainSpec]
theorem div_chain_correct : DivChainSpec := by
  intro env a b c hb hc
  apply TerminatesWith.of_wp_entry_for (f := func1Def) rfl
  unfold func1Def func1
  wp_run
  apply wp_call_tw (div_call «module».initialStore a b [] hb)        -- ★ REUSE: div(a, b)
  intro st1 vs1 h1
  obtain ⟨hvs1, hg1, hp1⟩ := h1
  subst hvs1
  wp_run
  apply wp_call_tw (div_call st1 (a / b) c [] hc)                    -- ★ REUSE: div(a/b, c)
  intro st2 vs2 h2
  obtain ⟨hvs2, _, _⟩ := h2
  subst hvs2
  wp_run
  simp

end Project.RustU64Tests.Spec
