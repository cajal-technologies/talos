import Project.RustConsumer.Program
import Interpreter.Wasm.Wp.Call

/-!
# Specification for `rust_consumer` — cross-crate, cross-call reuse

`rust_consumer` is a structurally different program from `rust_std`: a single
4-argument export `manhattan` that calls `u64::abs_diff` **twice** (once per
axis) and sums the results. It shares no shape with the demo crate — yet its
`abs_diff` body (`func0`) is emitted byte-for-byte identically.

`manhattan_spec` is proved entirely by **reusing** `absDiff_terminates` from
`CodeLib.RustStd.U64`, fed through the interpreter's direct-call rule
`wp_call_tw` once per call. The second call relies on the *frame conditions*
of `absDiff_terminates` (globals and page count unchanged) to re-establish its
own no-trap hypotheses after the first call mutated memory.
-/

namespace Project.RustConsumer.Spec

open Wasm Wasm.RustStd.U64

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
  -- first call: abs_diff(px, cx), nothing else on the stack
  apply wp_call_tw
  · exact absDiff_terminates env «module» 0 «module».initialStore px cx 1048576 []
      rfl rfl (by decide) (by decide) rfl
  · intro st1 vs1 h1
    obtain ⟨hvs1, hg1, hp1⟩ := h1
    subst hvs1
    wp_run
    -- second call: abs_diff(py, cy), with the first result still on the stack.
    -- its no-trap hypotheses are re-established from the frame conditions hg1/hp1.
    apply wp_call_tw
    · exact absDiff_terminates env «module» 0 st1 py cy 1048576
        [.i64 (if px < cx then cx - px else px - cx)]
        rfl (by rw [hg1]; rfl) (by decide) (by rw [hp1]; decide) rfl
    · intro st2 vs2 h2
      obtain ⟨hvs2, _, _⟩ := h2
      subst hvs2
      wp_run
      simp

end Project.RustConsumer.Spec
