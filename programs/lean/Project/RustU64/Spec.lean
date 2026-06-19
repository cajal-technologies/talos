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

-- `mul` is `a * b` inlined to a single `i64.mul`, a direct crate export.
@[spec_of "rust-exported" "rust_u64::mul"]
def MulSpec : Prop :=
  ∀ (env : HostEnv Unit) (a b : UInt64),
    TerminatesWith env «module» 4 «module».initialStore [.i64 b, .i64 a]
      (fun _ rs => rs = [.i64 (a * b)])

@[proves Project.RustU64.Spec.MulSpec]
theorem mul_correct : MulSpec := by
  intro env a b
  exact (TerminatesWith.of_returns_wp (f := mulFunc)
      (rs := [.i64 (a * b)]) rfl rfl
      (mul_wp «module».initialStore a b [])
      rfl).mono (fun _ _ h => h.1)

-- `div` is `a / b` inlined (the body guards the `i64.div_u` against a zero
-- divisor and panics otherwise); a direct crate export. With `b ≠ 0` the
-- guard falls through and the function returns the unsigned quotient.
@[spec_of "rust-exported" "rust_u64::div"]
def DivSpec : Prop :=
  ∀ (env : HostEnv Unit) (a b : UInt64), b ≠ 0 →
    TerminatesWith env «module» 5 «module».initialStore [.i64 b, .i64 a]
      (fun _ rs => rs = [.i64 (a / b)])

@[proves Project.RustU64.Spec.DivSpec]
theorem div_correct : DivSpec := by
  intro env a b hb
  exact (TerminatesWith.of_returns_wp (f := divFunc)
      (rs := [.i64 (a / b)]) rfl rfl
      (div_wp «module».initialStore a b [] _ hb) rfl).mono (fun _ _ h => h.1)

end Project.RustU64.Spec
