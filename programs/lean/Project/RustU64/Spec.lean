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

-- `add` is `a + b` inlined to a single `i64.add`, a direct crate export.
@[spec_of "rust-exported" "rust_u64::add"]
def AddSpec : Prop :=
  ∀ (env : HostEnv Unit) (a b : UInt64),
    TerminatesWith env «module» 2 «module».initialStore [.i64 b, .i64 a]
      (fun _ rs => rs = [.i64 (a + b)])

@[proves Project.RustU64.Spec.AddSpec]
theorem add_correct : AddSpec := by
  intro env a b
  exact (TerminatesWith.of_returns_wp (f := addFunc)
      (rs := [.i64 (a + b)]) rfl rfl
      (add_wp «module».initialStore a b [])
      rfl).mono (fun _ _ h => h.1)

-- `sub` is `a - b` inlined to a single `i64.sub`, a direct crate export.
@[spec_of "rust-exported" "rust_u64::sub"]
def SubSpec : Prop :=
  ∀ (env : HostEnv Unit) (a b : UInt64),
    TerminatesWith env «module» 3 «module».initialStore [.i64 b, .i64 a]
      (fun _ rs => rs = [.i64 (a - b)])

@[proves Project.RustU64.Spec.SubSpec]
theorem sub_correct : SubSpec := by
  intro env a b
  exact (TerminatesWith.of_returns_wp (f := subFunc)
      (rs := [.i64 (a - b)]) rfl rfl
      (sub_wp «module».initialStore a b [])
      rfl).mono (fun _ _ h => h.1)

end Project.RustU64.Spec
