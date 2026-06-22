import Project.RustU64.Program

/-!
# `rust_u64` per-crate specs (abs_diff + operators add .. shr)

Each spec is discharged by reusing the per-function CodeLib theorem from
`CodeLib/RustStd/U64/<Fn>.lean` (`addBodyWp`, …, `divBodyWp`, `shlBodyWp`, …),
which is itself built on the type-agnostic trunk `CodeLib/RustStd/UInt.lean`.
No operator body is re-proven here — `of_returns_wp` bridges the reusable `wp`
fact to `TerminatesWith`.
-/

namespace Project.RustU64.Spec

open Wasm Wasm.RustStd Wasm.RustStd.U64

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

@[spec_of "rust-exported" "rust_u64::add"]
def AddSpec : Prop :=
  ∀ (env : HostEnv Unit) (a b : UInt64),
    TerminatesWith env «module» 2 «module».initialStore [.i64 b, .i64 a]
      (fun _ rs => rs = [.i64 (a + b)])
@[proves Project.RustU64.Spec.AddSpec]
theorem add_correct : AddSpec := by
  intro env a b
  exact (TerminatesWith.of_returns_wp (f := func2Def) (rs := [.i64 (a + b)]) rfl rfl
      (addBodyWp «module».initialStore a b []) rfl).mono (fun _ _ h => h.1)

@[spec_of "rust-exported" "rust_u64::sub"]
def SubSpec : Prop :=
  ∀ (env : HostEnv Unit) (a b : UInt64),
    TerminatesWith env «module» 8 «module».initialStore [.i64 b, .i64 a]
      (fun _ rs => rs = [.i64 (a - b)])
@[proves Project.RustU64.Spec.SubSpec]
theorem sub_correct : SubSpec := by
  intro env a b
  exact (TerminatesWith.of_returns_wp (f := func8Def) (rs := [.i64 (a - b)]) rfl rfl
      (subBodyWp «module».initialStore a b []) rfl).mono (fun _ _ h => h.1)

@[spec_of "rust-exported" "rust_u64::mul"]
def MulSpec : Prop :=
  ∀ (env : HostEnv Unit) (a b : UInt64),
    TerminatesWith env «module» 9 «module».initialStore [.i64 b, .i64 a]
      (fun _ rs => rs = [.i64 (a * b)])
@[proves Project.RustU64.Spec.MulSpec]
theorem mul_correct : MulSpec := by
  intro env a b
  exact (TerminatesWith.of_returns_wp (f := func9Def) (rs := [.i64 (a * b)]) rfl rfl
      (mulBodyWp «module».initialStore a b []) rfl).mono (fun _ _ h => h.1)

@[spec_of "rust-exported" "rust_u64::div"]
def DivSpec : Prop :=
  ∀ (env : HostEnv Unit) (a b : UInt64), b ≠ 0 →
    TerminatesWith env «module» 6 «module».initialStore [.i64 b, .i64 a]
      (fun _ rs => rs = [.i64 (a / b)])
@[proves Project.RustU64.Spec.DivSpec]
theorem div_correct : DivSpec := by
  intro env a b hb
  exact (TerminatesWith.of_returns_wp (f := func6Def) (rs := [.i64 (a / b)]) rfl rfl
      (divBodyWp «module».initialStore a b [] hb) rfl).mono (fun _ _ h => h.1)

@[spec_of "rust-exported" "rust_u64::rem"]
def RemSpec : Prop :=
  ∀ (env : HostEnv Unit) (a b : UInt64), b ≠ 0 →
    TerminatesWith env «module» 10 «module».initialStore [.i64 b, .i64 a]
      (fun _ rs => rs = [.i64 (a % b)])
@[proves Project.RustU64.Spec.RemSpec]
theorem rem_correct : RemSpec := by
  intro env a b hb
  exact (TerminatesWith.of_returns_wp (f := func10Def) (rs := [.i64 (a % b)]) rfl rfl
      (remBodyWp «module».initialStore a b [] hb) rfl).mono (fun _ _ h => h.1)

@[spec_of "rust-exported" "rust_u64::bitand"]
def BitAndSpec : Prop :=
  ∀ (env : HostEnv Unit) (a b : UInt64),
    TerminatesWith env «module» 3 «module».initialStore [.i64 b, .i64 a]
      (fun _ rs => rs = [.i64 (a &&& b)])
@[proves Project.RustU64.Spec.BitAndSpec]
theorem bitand_correct : BitAndSpec := by
  intro env a b
  exact (TerminatesWith.of_returns_wp (f := func3Def) (rs := [.i64 (a &&& b)]) rfl rfl
      (bitandBodyWp «module».initialStore a b []) rfl).mono (fun _ _ h => h.1)

@[spec_of "rust-exported" "rust_u64::bitor"]
def BitOrSpec : Prop :=
  ∀ (env : HostEnv Unit) (a b : UInt64),
    TerminatesWith env «module» 4 «module».initialStore [.i64 b, .i64 a]
      (fun _ rs => rs = [.i64 (a ||| b)])
@[proves Project.RustU64.Spec.BitOrSpec]
theorem bitor_correct : BitOrSpec := by
  intro env a b
  exact (TerminatesWith.of_returns_wp (f := func4Def) (rs := [.i64 (a ||| b)]) rfl rfl
      (bitorBodyWp «module».initialStore a b []) rfl).mono (fun _ _ h => h.1)

@[spec_of "rust-exported" "rust_u64::bitxor"]
def BitXorSpec : Prop :=
  ∀ (env : HostEnv Unit) (a b : UInt64),
    TerminatesWith env «module» 5 «module».initialStore [.i64 b, .i64 a]
      (fun _ rs => rs = [.i64 (a ^^^ b)])
@[proves Project.RustU64.Spec.BitXorSpec]
theorem bitxor_correct : BitXorSpec := by
  intro env a b
  exact (TerminatesWith.of_returns_wp (f := func5Def) (rs := [.i64 (a ^^^ b)]) rfl rfl
      (bitxorBodyWp «module».initialStore a b []) rfl).mono (fun _ _ h => h.1)

@[spec_of "rust-exported" "rust_u64::not"]
def NotSpec : Prop :=
  ∀ (env : HostEnv Unit) (a : UInt64),
    TerminatesWith env «module» 11 «module».initialStore [.i64 a]
      (fun _ rs => rs = [.i64 (~~~a)])
@[proves Project.RustU64.Spec.NotSpec]
theorem not_correct : NotSpec := by
  intro env a
  exact (TerminatesWith.of_returns_wp (f := func11Def) (rs := [.i64 (~~~a)]) rfl rfl
      (notBodyWp «module».initialStore a []) rfl).mono (fun _ _ h => h.1)

@[spec_of "rust-exported" "rust_u64::shl"]
def ShlSpec : Prop :=
  ∀ (env : HostEnv Unit) (a : UInt64) (b : UInt32),
    TerminatesWith env «module» 12 «module».initialStore [.i32 b, .i64 a]
      (fun _ rs => rs = [.i64 (a <<< (b.toUInt64 % 64))])
@[proves Project.RustU64.Spec.ShlSpec]
theorem shl_correct : ShlSpec := by
  intro env a b
  exact (TerminatesWith.of_returns_wp (f := func12Def) (rs := [.i64 (a <<< (b.toUInt64 % 64))])
      rfl rfl (shlBodyWp «module».initialStore a b []) rfl).mono (fun _ _ h => h.1)

@[spec_of "rust-exported" "rust_u64::shr"]
def ShrSpec : Prop :=
  ∀ (env : HostEnv Unit) (a : UInt64) (b : UInt32),
    TerminatesWith env «module» 13 «module».initialStore [.i32 b, .i64 a]
      (fun _ rs => rs = [.i64 (a >>> (b.toUInt64 % 64))])
@[proves Project.RustU64.Spec.ShrSpec]
theorem shr_correct : ShrSpec := by
  intro env a b
  exact (TerminatesWith.of_returns_wp (f := func13Def) (rs := [.i64 (a >>> (b.toUInt64 % 64))])
      rfl rfl (shrBodyWp «module».initialStore a b []) rfl).mono (fun _ _ h => h.1)

@[spec_of "rust-exported" "rust_u64::eq"]
def EqSpec : Prop :=
  ∀ (env : HostEnv Unit) (a b : UInt64),
    TerminatesWith env «module» 14 «module».initialStore [.i64 b, .i64 a]
      (fun _ rs => rs = [.i32 (if a = b then 1 else 0)])
@[proves Project.RustU64.Spec.EqSpec]
theorem eq_correct : EqSpec := by
  intro env a b
  exact (TerminatesWith.of_returns_wp (f := func14Def) (rs := [.i32 (if a = b then 1 else 0)]) rfl rfl
      (eqBodyWp «module».initialStore a b []) rfl).mono (fun _ _ h => h.1)

@[spec_of "rust-exported" "rust_u64::ne"]
def NeSpec : Prop :=
  ∀ (env : HostEnv Unit) (a b : UInt64),
    TerminatesWith env «module» 19 «module».initialStore [.i64 b, .i64 a]
      (fun _ rs => rs = [.i32 (if a ≠ b then 1 else 0)])
@[proves Project.RustU64.Spec.NeSpec]
theorem ne_correct : NeSpec := by
  intro env a b
  exact (TerminatesWith.of_returns_wp (f := func19Def) (rs := [.i32 (if a ≠ b then 1 else 0)]) rfl rfl
      (neBodyWp «module».initialStore a b []) rfl).mono (fun _ _ h => h.1)

@[spec_of "rust-exported" "rust_u64::lt"]
def LtSpec : Prop :=
  ∀ (env : HostEnv Unit) (a b : UInt64),
    TerminatesWith env «module» 18 «module».initialStore [.i64 b, .i64 a]
      (fun _ rs => rs = [.i32 (if a < b then 1 else 0)])
@[proves Project.RustU64.Spec.LtSpec]
theorem lt_correct : LtSpec := by
  intro env a b
  exact (TerminatesWith.of_returns_wp (f := func18Def) (rs := [.i32 (if a < b then 1 else 0)]) rfl rfl
      (ltBodyWp «module».initialStore a b []) rfl).mono (fun _ _ h => h.1)

@[spec_of "rust-exported" "rust_u64::le"]
def LeSpec : Prop :=
  ∀ (env : HostEnv Unit) (a b : UInt64),
    TerminatesWith env «module» 17 «module».initialStore [.i64 b, .i64 a]
      (fun _ rs => rs = [.i32 (if a ≤ b then 1 else 0)])
@[proves Project.RustU64.Spec.LeSpec]
theorem le_correct : LeSpec := by
  intro env a b
  exact (TerminatesWith.of_returns_wp (f := func17Def) (rs := [.i32 (if a ≤ b then 1 else 0)]) rfl rfl
      (leBodyWp «module».initialStore a b []) rfl).mono (fun _ _ h => h.1)

@[spec_of "rust-exported" "rust_u64::gt"]
def GtSpec : Prop :=
  ∀ (env : HostEnv Unit) (a b : UInt64),
    TerminatesWith env «module» 16 «module».initialStore [.i64 b, .i64 a]
      (fun _ rs => rs = [.i32 (if a > b then 1 else 0)])
@[proves Project.RustU64.Spec.GtSpec]
theorem gt_correct : GtSpec := by
  intro env a b
  exact (TerminatesWith.of_returns_wp (f := func16Def) (rs := [.i32 (if a > b then 1 else 0)]) rfl rfl
      (gtBodyWp «module».initialStore a b []) rfl).mono (fun _ _ h => h.1)

@[spec_of "rust-exported" "rust_u64::ge"]
def GeSpec : Prop :=
  ∀ (env : HostEnv Unit) (a b : UInt64),
    TerminatesWith env «module» 15 «module».initialStore [.i64 b, .i64 a]
      (fun _ rs => rs = [.i32 (if a ≥ b then 1 else 0)])
@[proves Project.RustU64.Spec.GeSpec]
theorem ge_correct : GeSpec := by
  intro env a b
  exact (TerminatesWith.of_returns_wp (f := func15Def) (rs := [.i32 (if a ≥ b then 1 else 0)]) rfl rfl
      (geBodyWp «module».initialStore a b []) rfl).mono (fun _ _ h => h.1)

end Project.RustU64.Spec
