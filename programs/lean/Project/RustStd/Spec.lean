import Project.RustStd.Program

/-!
# Specifications for `rust_std`

Thin per-crate instantiations: every proof just plugs this module's own
functions into the reusable, body-parametric theorems in
`CodeLib.RustStd.U64`. The hypotheses (function index, stack-pointer
global, memory bounds) are all discharged by `rfl` / `decide`.
-/

namespace Project.RustStd.Spec

open Wasm Wasm.RustStd.U64

/-- `count_ones` (export index 1) — Group A. Reuses `countOnes_terminates`. -/
@[spec_of "rust-exported" "rust_std::count_ones"]
theorem count_ones_spec (env : HostEnv Unit) (v : UInt64) :
    TerminatesWith env «module» 1 «module».initialStore [.i64 v]
      (fun _ rs => rs = [.i32 (UInt32.ofNat (popcnt64 64 v 0))]) :=
  countOnes_terminates env «module» 1 «module».initialStore v 1048576
    rfl rfl (by decide) (by decide) rfl

/-- The inner `core::num::<impl u64>::abs_diff` (function index 0) — Group B.
Reuses `absDiff_terminates`. This is the body that other crates will also
contain and call. -/
@[spec_of "rust-exported" "rust_std::abs_diff"]
theorem abs_diff_spec (env : HostEnv Unit) (a b : UInt64) :
    TerminatesWith env «module» 0 «module».initialStore [.i64 b, .i64 a]
      (fun _ rs => rs = [.i64 (if a < b then b - a else a - b)]) :=
  (absDiff_terminates env «module» 0 «module».initialStore a b 1048576 []
    rfl rfl (by decide) (by decide) rfl).mono (fun _ _ h => h.1)

end Project.RustStd.Spec
