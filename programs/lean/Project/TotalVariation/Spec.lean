import Project.TotalVariation.Program
import Interpreter.Wasm.Wp.Call

/-!
# `total_variation a b c = |a-b| + |b-c|`

Reuses `absDiff_wp` (proven once in CodeLib): each `call` to the inner
`abs_diff` is discharged by bridging that theorem to `TerminatesWith` via
`of_returns_wp` and feeding it to the call rule `wp_call_tw`. Nothing is added
to CodeLib; the body of `abs_diff` is never re-proven here.
-/

namespace Project.TotalVariation.Spec

open Wasm Wasm.RustStd.U64

/-- `abs_diff` specialized to a call site (operands `b :: a :: rest` on the stack). -/
private theorem absDiff_call {env : HostEnv Unit} (st : Store Unit) (a b : UInt64)
    (rest : List Value)
    (hsp : st.globals.globals[0]? = some (.i32 1048576))
    (hhi : 1048576 ≤ st.mem.pages * 65536) :
    TerminatesWith env «module» 0 st (.i64 b :: .i64 a :: rest)
      (fun st' vs => vs = .i64 (if a < b then b - a else a - b) :: rest
        ∧ st'.globals = st.globals ∧ st'.mem.pages = st.mem.pages) :=
  TerminatesWith.of_returns_wp (f := absDiffFunc)
    (rs := [.i64 (if a < b then b - a else a - b)]) rfl rfl
    (absDiff_wp st 1048576 a b [] hsp (by decide) hhi) rfl

@[spec_of "rust-exported" "total_variation::total_variation"]
def TotalVariationSpec : Prop :=
  ∀ (env : HostEnv Unit) (a b c : UInt64),
    TerminatesWith env «module» 1 «module».initialStore [.i64 c, .i64 b, .i64 a]
      (fun _ rs => rs = [.i64 ((if a < b then b - a else a - b)
                             + (if b < c then c - b else b - c))])

set_option maxRecDepth 4096 in
@[proves Project.TotalVariation.Spec.TotalVariationSpec]
theorem total_variation_correct : TotalVariationSpec := by
  intro env a b c
  apply TerminatesWith.of_wp_entry_for (f := func1Def) rfl
  unfold func1Def func1
  wp_run
  apply wp_call_tw (absDiff_call «module».initialStore a b [] rfl (by decide))
  intro st1 vs1 h1
  obtain ⟨hvs1, hg1, hp1⟩ := h1
  subst hvs1
  wp_run
  apply wp_call_tw (absDiff_call st1 b c [.i64 (if a < b then b - a else a - b)]
    (by rw [hg1]; rfl) (by rw [hp1]; decide))
  intro st2 vs2 h2
  obtain ⟨hvs2, _, _⟩ := h2
  subst hvs2
  wp_run
  simp

end Project.TotalVariation.Spec
