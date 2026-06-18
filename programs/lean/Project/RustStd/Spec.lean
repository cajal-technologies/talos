import Project.RustStd.Program

/-!
# Specifications for `rust_std`

Per-crate instantiations: each export's total-correctness spec is obtained by
bridging the reusable wp-form theorems in `CodeLib.RustStd.U64`
(`countOnes_wp`, `absDiff_wp`) to `TerminatesWith` via `of_returns_wp`. The
module index, stack-pointer global, and memory bounds are discharged by
`rfl` / `decide`.
-/

namespace Project.RustStd.Spec

open Wasm Wasm.RustStd.U64

/-- `count_ones` (export index 1) — Group A. Reuses `countOnes_wp`. -/
@[spec_of "rust-exported" "rust_std::count_ones"]
theorem count_ones_spec (env : HostEnv Unit) (v : UInt64) :
    TerminatesWith env «module» 1 «module».initialStore [.i64 v]
      (fun _ rs => rs = [.i32 (UInt32.ofNat (popcnt64 64 v 0))]) :=
  (TerminatesWith.of_returns_wp (f := countOnesFunc)
      (rs := [.i32 (UInt32.ofNat (popcnt64 64 v 0))]) rfl rfl
      (countOnes_wp «module».initialStore 1048576 v [] rfl (by decide) (by decide))
      rfl).mono (fun _ _ h => h.1)

/-- The inner `core::num::<impl u64>::abs_diff` (function index 0) — Group B.
Reuses `absDiff_wp`. -/
@[spec_of "rust-exported" "rust_std::abs_diff"]
theorem abs_diff_spec (env : HostEnv Unit) (a b : UInt64) :
    TerminatesWith env «module» 0 «module».initialStore [.i64 b, .i64 a]
      (fun _ rs => rs = [.i64 (if a < b then b - a else a - b)]) :=
  (TerminatesWith.of_returns_wp (f := absDiffFunc)
      (rs := [.i64 (if a < b then b - a else a - b)]) rfl rfl
      (absDiff_wp «module».initialStore 1048576 a b [] rfl (by decide) (by decide))
      rfl).mono (fun _ _ h => h.1)

end Project.RustStd.Spec
