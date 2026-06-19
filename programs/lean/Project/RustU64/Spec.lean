import Project.RustU64.Program

namespace Project.RustU64.Spec

open Wasm Wasm.RustStd.U64

@[spec_of "rust-internal" "core::num::abs_diff"]
def AbsDiffSpec : Prop :=
  ∀ (env : HostEnv Unit) (a b : UInt64),
    TerminatesWith env «module» 0 «module».initialStore [.i64 b, .i64 a]
      (fun _ rs => rs = [.i64 (if a < b then b - a else a - b)])

@[proves Project.RustU64.Spec.AbsDiffSpec]
theorem abs_diff_correct : AbsDiffSpec := by
  intro env a b
  exact (TerminatesWith.of_returns_wp (f := absDiffFunc)
      (rs := [.i64 (if a < b then b - a else a - b)]) rfl rfl
      (absDiff_wp «module».initialStore 1048576 a b [] rfl (by decide) (by decide))
      rfl).mono (fun _ _ h => h.1)

-- `mul` is `a * b` inlined to a single `i64.mul` (export index 3), so the
-- proved function is a direct crate export, hence `rust-exported`.
@[spec_of "rust-exported" "rust_u64::mul"]
def MulSpec : Prop :=
  ∀ (env : HostEnv Unit) (a b : UInt64),
    TerminatesWith env «module» 3 «module».initialStore [.i64 b, .i64 a]
      (fun _ rs => rs = [.i64 (a * b)])

@[proves Project.RustU64.Spec.MulSpec]
theorem mul_correct : MulSpec := by
  intro env a b
  exact (TerminatesWith.of_returns_wp (f := mulFunc)
      (rs := [.i64 (a * b)]) rfl rfl
      (mul_wp «module».initialStore a b [])
      rfl).mono (fun _ _ h => h.1)

end Project.RustU64.Spec
