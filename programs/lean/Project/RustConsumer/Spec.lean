import Project.RustConsumer.Program
import Interpreter.Wasm.Wp.Call

/-!
# Specification for `rust_consumer` — cross-crate, cross-call reuse

`rust_consumer` is structurally different from `rust_std`: a single 4-argument
export `manhattan` that calls `u64::abs_diff` **twice** and sums the results.
Its `abs_diff` body (`func0`) is emitted byte-for-byte identically, so the
reusable `absDiff_wp` applies — bridged to `TerminatesWith` via `of_returns_wp`
and fed to the call rule `wp_call_tw` once per call. The second call relies on
the frame facts (globals + page count unchanged) returned by the first.
-/

namespace Project.RustConsumer.Spec

open Wasm Wasm.RustStd.U64

/-- The reusable abs_diff fact specialized to a call site in this module: at
store `st` (with the standard SP global and ≥16 pages) and operand stack
`.i64 b :: .i64 a :: rest`, calling function 0 returns `|a-b|` on top of `rest`
and preserves globals/page-count. -/
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

set_option maxRecDepth 4096 in
/-- `manhattan px py cx cy = abs_diff px cx + abs_diff py cy`. -/
@[spec_of "rust-exported" "rust_consumer::manhattan"]
theorem manhattan_spec (env : HostEnv Unit) (px py cx cy : UInt64) :
    TerminatesWith env «module» 1 «module».initialStore [.i64 cy, .i64 cx, .i64 py, .i64 px]
      (fun _ rs => rs = [.i64 ((if px < cx then cx - px else px - cx)
                             + (if py < cy then cy - py else py - cy))]) := by
  apply TerminatesWith.of_wp_entry_for (f := func1Def) rfl
  unfold func1Def func1
  wp_run
  apply wp_call_tw (absDiff_call «module».initialStore px cx [] rfl (by decide))
  intro st1 vs1 h1
  obtain ⟨hvs1, hg1, hp1⟩ := h1
  subst hvs1
  wp_run
  apply wp_call_tw (absDiff_call st1 py cy [.i64 (if px < cx then cx - px else px - cx)]
    (by rw [hg1]; rfl) (by rw [hp1]; decide))
  intro st2 vs2 h2
  obtain ⟨hvs2, _, _⟩ := h2
  subst hvs2
  wp_run
  simp

end Project.RustConsumer.Spec
