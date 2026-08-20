import Project.RustU64.Program

/-!
# `rust_u64` per-crate specs (abs_diff + operators add .. shr)

Every spec is now a small-step `PartiallyMeets` theorem proved through
iris-lean. `abs_diff` reuses its authoritative physical-memory/global body
contract; pure operators use closed adequacy and primitive instruction rules.
The guarded division and remainder proofs follow the successful nonzero path
through their generated blocks, so the imported panic tails are unreachable.
-/

namespace Project.RustU64.Spec

open Wasm Wasm.RustStd Wasm.RustStd.U64
open Iris Iris.ProgramLogic Language.Notation

private def pureBinaryConfig (body : Program)
    (a b : UInt64) : SmallStep.Config Unit :=
  { expr := .running
      ⟨⟨[.i64 a, .i64 b], [], []⟩, body, 1, [], [], []⟩
    store :=
      { runtime := { instances := #[{ module := «module», host := {} }], entry := ⟨0⟩ }
        wasm := «module».initialStore } }

private def shiftConfig (body : Program)
    (a : UInt64) (b : UInt32) : SmallStep.Config Unit :=
  { expr := .running
      ⟨⟨[.i64 a, .i32 b], [], []⟩, body, 1, [], [], []⟩
    store :=
      { runtime := { instances := #[{ module := «module», host := {} }], entry := ⟨0⟩ }
        wasm := «module».initialStore } }

private def unaryConfig (body : Program)
    (a : UInt64) : SmallStep.Config Unit :=
  { expr := .running
      ⟨⟨[.i64 a], [], []⟩, body, 1, [], [], []⟩
    store :=
      { runtime := { instances := #[{ module := «module», host := {} }], entry := ⟨0⟩ }
        wasm := «module».initialStore } }

@[spec_of "rust-internal" "core::num::abs_diff"]
def AbsDiffSpec : Prop :=
  ∀ (a b : UInt64),
    SmallStep.PartiallyMeets
      (absDiffBodyConfig «module» «module».initialStore a b 0)
      (fun rs _store =>
        rs = [.i64 (if a < b then b - a else a - b)])

@[proves Project.RustU64.Spec.AbsDiffSpec]
theorem abs_diff_correct : AbsDiffSpec := by
  intro a b
  apply absDiff_smallStep_partiallyMeets_of_store
  · rfl
  · native_decide

@[spec_of "rust-exported" "rust_u64::add"]
def AddSpec : Prop :=
  ∀ (a b : UInt64),
    SmallStep.PartiallyMeets (pureBinaryConfig func2 a b)
      (fun rs _store => rs = [.i64 (a + b)])
@[proves Project.RustU64.Spec.AddSpec]
theorem add_correct : AddSpec := by
  intro a b
  apply SmallStep.wasm_smallStep_partiallyMeets (α := Unit)
  intro gs
  simp only [pureBinaryConfig, func2]
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_addI64
  inext
  iapply SmallStep.wp_returnFromFunction
  inext
  iapply wp_value'
  ipureintro
  rfl

@[spec_of "rust-exported" "rust_u64::sub"]
def SubSpec : Prop :=
  ∀ (a b : UInt64),
    SmallStep.PartiallyMeets (pureBinaryConfig func8 a b)
      (fun rs _store => rs = [.i64 (a - b)])
@[proves Project.RustU64.Spec.SubSpec]
theorem sub_correct : SubSpec := by
  intro a b
  apply SmallStep.wasm_smallStep_partiallyMeets (α := Unit)
  intro gs
  simp only [pureBinaryConfig, func8]
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_subI64
  inext
  iapply SmallStep.wp_returnFromFunction
  inext
  iapply wp_value'
  ipureintro
  rfl

@[spec_of "rust-exported" "rust_u64::mul"]
def MulSpec : Prop :=
  ∀ (a b : UInt64),
    SmallStep.PartiallyMeets (pureBinaryConfig func9 a b)
      (fun rs _store => rs = [.i64 (a * b)])
@[proves Project.RustU64.Spec.MulSpec]
theorem mul_correct : MulSpec := by
  intro a b
  apply SmallStep.wasm_smallStep_partiallyMeets (α := Unit)
  intro gs
  simp only [pureBinaryConfig, func9]
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_mulI64
  inext
  iapply SmallStep.wp_returnFromFunction
  inext
  iapply wp_value'
  ipureintro
  rfl

@[spec_of "rust-exported" "rust_u64::div"]
def DivSpec : Prop :=
  ∀ (a b : UInt64), b ≠ 0 →
    SmallStep.PartiallyMeets (pureBinaryConfig func6 a b)
      (fun rs _store => rs = [.i64 (a / b)])
@[proves Project.RustU64.Spec.DivSpec]
theorem div_correct : DivSpec := by
  intro a b hb
  apply SmallStep.wasm_smallStep_partiallyMeets (α := Unit)
  intro gs
  simp only [pureBinaryConfig, func6]
  iapply SmallStep.wp_block
  inext
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_constI64
  inext
  iapply SmallStep.wp_eqI64 (result := 0) (by simp [hb])
  inext
  iapply SmallStep.wp_const
  inext
  iapply SmallStep.wp_and
  inext
  rw [show (0 &&& 1 : UInt32) = 0 by decide]
  iapply SmallStep.wp_brIfZero
  inext
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_divUI64 hb
  inext
  iapply SmallStep.wp_returnFromFunction
  inext
  iapply wp_value'
  ipureintro
  rfl

@[spec_of "rust-exported" "rust_u64::rem"]
def RemSpec : Prop :=
  ∀ (a b : UInt64), b ≠ 0 →
    SmallStep.PartiallyMeets (pureBinaryConfig func10 a b)
      (fun rs _store => rs = [.i64 (a % b)])
@[proves Project.RustU64.Spec.RemSpec]
theorem rem_correct : RemSpec := by
  intro a b hb
  apply SmallStep.wasm_smallStep_partiallyMeets (α := Unit)
  intro gs
  simp only [pureBinaryConfig, func10]
  iapply SmallStep.wp_block
  inext
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_constI64
  inext
  iapply SmallStep.wp_eqI64 (result := 0) (by simp [hb])
  inext
  iapply SmallStep.wp_const
  inext
  iapply SmallStep.wp_and
  inext
  rw [show (0 &&& 1 : UInt32) = 0 by decide]
  iapply SmallStep.wp_brIfZero
  inext
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_remUI64 hb
  inext
  iapply SmallStep.wp_returnFromFunction
  inext
  iapply wp_value'
  ipureintro
  rfl

@[spec_of "rust-exported" "rust_u64::bitand"]
def BitAndSpec : Prop :=
  ∀ (a b : UInt64),
    SmallStep.PartiallyMeets (pureBinaryConfig func3 a b)
      (fun rs _store => rs = [.i64 (a &&& b)])
@[proves Project.RustU64.Spec.BitAndSpec]
theorem bitand_correct : BitAndSpec := by
  intro a b
  apply SmallStep.wasm_smallStep_partiallyMeets (α := Unit)
  intro gs
  simp only [pureBinaryConfig, func3]
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_andI64
  inext
  iapply SmallStep.wp_returnFromFunction
  inext
  iapply wp_value'
  ipureintro
  rfl

@[spec_of "rust-exported" "rust_u64::bitor"]
def BitOrSpec : Prop :=
  ∀ (a b : UInt64),
    SmallStep.PartiallyMeets (pureBinaryConfig func4 a b)
      (fun rs _store => rs = [.i64 (a ||| b)])
@[proves Project.RustU64.Spec.BitOrSpec]
theorem bitor_correct : BitOrSpec := by
  intro a b
  apply SmallStep.wasm_smallStep_partiallyMeets (α := Unit)
  intro gs
  simp only [pureBinaryConfig, func4]
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_orI64
  inext
  iapply SmallStep.wp_returnFromFunction
  inext
  iapply wp_value'
  ipureintro
  rfl

@[spec_of "rust-exported" "rust_u64::bitxor"]
def BitXorSpec : Prop :=
  ∀ (a b : UInt64),
    SmallStep.PartiallyMeets (pureBinaryConfig func5 a b)
      (fun rs _store => rs = [.i64 (a ^^^ b)])
@[proves Project.RustU64.Spec.BitXorSpec]
theorem bitxor_correct : BitXorSpec := by
  intro a b
  apply SmallStep.wasm_smallStep_partiallyMeets (α := Unit)
  intro gs
  simp only [pureBinaryConfig, func5]
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_xorI64
  inext
  iapply SmallStep.wp_returnFromFunction
  inext
  iapply wp_value'
  ipureintro
  rfl

@[spec_of "rust-exported" "rust_u64::not"]
def NotSpec : Prop :=
  ∀ (a : UInt64),
    SmallStep.PartiallyMeets (unaryConfig func11 a)
      (fun rs _store => rs = [.i64 (~~~a)])
@[proves Project.RustU64.Spec.NotSpec]
theorem not_correct : NotSpec := by
  intro a
  apply SmallStep.wasm_smallStep_partiallyMeets (α := Unit)
  intro gs
  simp only [unaryConfig, func11]
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_constI64
  inext
  iapply SmallStep.wp_xorI64
  inext
  rw [show a ^^^ (18446744073709551615 : UInt64) = ~~~a by
    bv_decide]
  iapply SmallStep.wp_returnFromFunction
  inext
  iapply wp_value'
  ipureintro
  rfl

@[spec_of "rust-exported" "rust_u64::shl"]
def ShlSpec : Prop :=
  ∀ (a : UInt64) (b : UInt32),
    SmallStep.PartiallyMeets (shiftConfig func12 a b)
      (fun rs _store => rs = [.i64 (a <<< (b.toUInt64 % 64))])
@[proves Project.RustU64.Spec.ShlSpec]
theorem shl_correct : ShlSpec := by
  intro a b
  apply SmallStep.wasm_smallStep_partiallyMeets (α := Unit)
  intro gs
  simp only [shiftConfig, func12]
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_const
  inext
  iapply SmallStep.wp_and
  inext
  rw [UInt32.and_comm b 63]
  iapply SmallStep.wp_extendUI32
  inext
  iapply SmallStep.wp_shlI64
  inext
  rw [shiftAmount_norm]
  iapply SmallStep.wp_returnFromFunction
  inext
  iapply wp_value'
  ipureintro
  rfl

@[spec_of "rust-exported" "rust_u64::shr"]
def ShrSpec : Prop :=
  ∀ (a : UInt64) (b : UInt32),
    SmallStep.PartiallyMeets (shiftConfig func13 a b)
      (fun rs _store => rs = [.i64 (a >>> (b.toUInt64 % 64))])
@[proves Project.RustU64.Spec.ShrSpec]
theorem shr_correct : ShrSpec := by
  intro a b
  apply SmallStep.wasm_smallStep_partiallyMeets (α := Unit)
  intro gs
  simp only [shiftConfig, func13]
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_const
  inext
  iapply SmallStep.wp_and
  inext
  rw [UInt32.and_comm b 63]
  iapply SmallStep.wp_extendUI32
  inext
  iapply SmallStep.wp_shrUI64
  inext
  rw [shiftAmount_norm]
  iapply SmallStep.wp_returnFromFunction
  inext
  iapply wp_value'
  ipureintro
  rfl

end Project.RustU64.Spec
