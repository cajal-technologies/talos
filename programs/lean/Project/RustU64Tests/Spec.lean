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

/-! ## `u64::add` — `add_sum3 a b c = (a + b) + c`

`add` (export idx 0) compiles to the frame-less body that is definitionally
CodeLib's `addFunc`, so each `.call 0` in `add_sum3` reuses `add_wp`. -/

/-- `add` specialized to a call site (operands `b :: a :: rest` on the stack).
No `hsp`/`hhi` side-conditions: `add` touches neither the shadow stack nor
memory, so `add_wp` carries no frame hypotheses. -/
private theorem add_call {env : HostEnv Unit} (st : Store Unit) (a b : UInt64)
    (rest : List Value) :
    TerminatesWith env «module» 0 st (.i64 b :: .i64 a :: rest)
      (fun st' vs => vs = .i64 (a + b) :: rest
        ∧ st'.globals = st.globals ∧ st'.mem.pages = st.mem.pages) :=
  TerminatesWith.of_returns_wp (f := addFunc)
    (rs := [.i64 (a + b)]) rfl rfl
    (add_wp st a b []) rfl   -- ★ REUSE: the proven CodeLib theorem

@[spec_of "rust-exported" "rust_u64_tests::add_sum3"]
def AddSum3Spec : Prop :=
  ∀ (env : HostEnv Unit) (a b c : UInt64),
    TerminatesWith env «module» 1 «module».initialStore [.i64 c, .i64 b, .i64 a]
      (fun _ rs => rs = [.i64 (a + b + c)])

set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.AddSum3Spec]
theorem add_sum3_correct : AddSum3Spec := by
  intro env a b c
  apply TerminatesWith.of_wp_entry_for (f := func1Def) rfl
  unfold func1Def func1
  wp_run
  apply wp_call_tw (add_call «module».initialStore a b [])          -- ★ REUSE: add(a, b)
  intro st1 vs1 h1
  obtain ⟨hvs1, hg1, hp1⟩ := h1
  subst hvs1
  wp_run
  apply wp_call_tw (add_call st1 (a + b) c [])                      -- ★ REUSE: add(a+b, c)
  intro st2 vs2 h2
  obtain ⟨hvs2, _, _⟩ := h2
  subst hvs2
  wp_run
  simp

/-! ## `u64::sub` — `sub_chain3 a b c = (a - b) - c`

`sub` (export idx 6) compiles to the frame-less body that is definitionally
CodeLib's `subFunc`, so each `.call 6` in `sub_chain3` reuses `sub_wp`. -/

/-- `sub` specialized to a call site (operands `b :: a :: rest` on the stack).
No `hsp`/`hhi` side-conditions: `sub` touches neither the shadow stack nor
memory, so `sub_wp` carries no frame hypotheses. -/
private theorem sub_call {env : HostEnv Unit} (st : Store Unit) (a b : UInt64)
    (rest : List Value) :
    TerminatesWith env «module» 6 st (.i64 b :: .i64 a :: rest)
      (fun st' vs => vs = .i64 (a - b) :: rest
        ∧ st'.globals = st.globals ∧ st'.mem.pages = st.mem.pages) :=
  TerminatesWith.of_returns_wp (f := subFunc)
    (rs := [.i64 (a - b)]) rfl rfl
    (sub_wp st a b []) rfl   -- ★ REUSE: the proven CodeLib theorem

@[spec_of "rust-exported" "rust_u64_tests::sub_chain3"]
def SubChain3Spec : Prop :=
  ∀ (env : HostEnv Unit) (a b c : UInt64),
    TerminatesWith env «module» 7 «module».initialStore [.i64 c, .i64 b, .i64 a]
      (fun _ rs => rs = [.i64 (a - b - c)])

set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.SubChain3Spec]
theorem sub_chain3_correct : SubChain3Spec := by
  intro env a b c
  apply TerminatesWith.of_wp_entry_for (f := func7Def) rfl
  unfold func7Def func7
  wp_run
  apply wp_call_tw (sub_call «module».initialStore a b [])          -- ★ REUSE: sub(a, b)
  intro st1 vs1 h1
  obtain ⟨hvs1, _, _⟩ := h1
  subst hvs1
  wp_run
  apply wp_call_tw (sub_call st1 (a - b) c [])                      -- ★ REUSE: sub(a-b, c)
  intro st2 vs2 h2
  obtain ⟨hvs2, _, _⟩ := h2
  subst hvs2
  wp_run
  simp

/-! ## `u64::mul` — `mul_prod3 a b c = (a * b) * c`

`mul` (export idx 4) compiles to the frame-less body that is definitionally
CodeLib's `mulFunc`, so each `.call 4` in `mul_prod3` reuses `mul_wp`. -/

/-- `mul` specialized to a call site (operands `b :: a :: rest` on the stack).
No `hsp`/`hhi` side-conditions: `mul` touches neither the shadow stack nor
memory, so `mul_wp` carries no frame hypotheses. -/
private theorem mul_call {env : HostEnv Unit} (st : Store Unit) (a b : UInt64)
    (rest : List Value) :
    TerminatesWith env «module» 4 st (.i64 b :: .i64 a :: rest)
      (fun st' vs => vs = .i64 (a * b) :: rest
        ∧ st'.globals = st.globals ∧ st'.mem.pages = st.mem.pages) :=
  TerminatesWith.of_returns_wp (f := mulFunc)
    (rs := [.i64 (a * b)]) rfl rfl
    (mul_wp st a b []) rfl   -- ★ REUSE: the proven CodeLib theorem

@[spec_of "rust-exported" "rust_u64_tests::mul_prod3"]
def MulProd3Spec : Prop :=
  ∀ (env : HostEnv Unit) (a b c : UInt64),
    TerminatesWith env «module» 5 «module».initialStore [.i64 c, .i64 b, .i64 a]
      (fun _ rs => rs = [.i64 (a * b * c)])

set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.MulProd3Spec]
theorem mul_prod3_correct : MulProd3Spec := by
  intro env a b c
  apply TerminatesWith.of_wp_entry_for (f := func5Def) rfl
  unfold func5Def func5
  wp_run
  apply wp_call_tw (mul_call «module».initialStore a b [])          -- ★ REUSE: mul(a, b)
  intro st1 vs1 h1
  obtain ⟨hvs1, hg1, hp1⟩ := h1
  subst hvs1
  wp_run
  apply wp_call_tw (mul_call st1 (a * b) c [])                      -- ★ REUSE: mul(a*b, c)
  intro st2 vs2 h2
  obtain ⟨hvs2, _, _⟩ := h2
  subst hvs2
  wp_run
  simp

/-! ## `u64::div` — `div_chain a b c = (a / b) / c`

`div` (export idx 2) inlines the guarded `i64.div_u`. Its opt-0 body shares the
`divGuard` block with CodeLib's `divFunc`; only the (unreachable, since the
divisors are nonzero) panic tail differs. `div_wp` is generic in that tail, so
each `.call 2` in `div_chain` reuses it. -/

/-- `div` specialized to a call site (operands `b :: a :: rest` on the stack,
divisor `b ≠ 0`). No `hsp`/`hhi` side-conditions: `div` touches neither the
shadow stack nor memory, so `div_wp` carries no frame hypotheses. The panic
`tail` of this crate's `div` shim (idx 2) is inferred from `func2Def.body`. -/
private theorem div_call {env : HostEnv Unit} (st : Store Unit) (a b : UInt64)
    (rest : List Value) (hb : b ≠ 0) :
    TerminatesWith env «module» 2 st (.i64 b :: .i64 a :: rest)
      (fun st' vs => vs = .i64 (a / b) :: rest
        ∧ st'.globals = st.globals ∧ st'.mem.pages = st.mem.pages) :=
  TerminatesWith.of_returns_wp (f := func2Def)
    (rs := [.i64 (a / b)]) rfl rfl
    (div_wp st a b [] _ hb) rfl   -- ★ REUSE: the proven CodeLib theorem

@[spec_of "rust-exported" "rust_u64_tests::div_chain"]
def DivChainSpec : Prop :=
  ∀ (env : HostEnv Unit) (a b c : UInt64), b ≠ 0 → c ≠ 0 →
    TerminatesWith env «module» 3 «module».initialStore [.i64 c, .i64 b, .i64 a]
      (fun _ rs => rs = [.i64 (a / b / c)])

set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.DivChainSpec]
theorem div_chain_correct : DivChainSpec := by
  intro env a b c hb hc
  apply TerminatesWith.of_wp_entry_for (f := func3Def) rfl
  unfold func3Def func3
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
