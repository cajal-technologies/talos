import Project.RustU64Tests.Program

/-!
# Reuse tests for the `CodeLib/RustStd/U64` corpus

Two structurally-distinct functions per operator, each using the operator inline
the way real client code emits it (no shim and no `.call`). Every public spec is
now a small-step `PartiallyMeets` theorem proved through iris-lean. The guarded
div/rem functions follow their nonzero branch and return before the panic tail;
the shift functions prove the emitted mask/extend sequence normalizes counts
modulo 64.
-/

namespace Project.RustU64Tests.Spec

open Wasm Wasm.RustStd Wasm.RustStd.U64
open Iris Iris.ProgramLogic Language.Notation

private def ternaryConfig (body : Program)
    (a b c : UInt64) : SmallStep.Config Unit :=
  { expr := .running
      ⟨⟨[.i64 a, .i64 b, .i64 c], [], []⟩,
        body, 1, [], [], []⟩
    store :=
      { runtime := { module := «module», host := {} }
        wasm := «module».initialStore } }

private def binaryConfig (body : Program)
    (a b : UInt64) : SmallStep.Config Unit :=
  { expr := .running
      ⟨⟨[.i64 a, .i64 b], [], []⟩, body, 1, [], [], []⟩
    store :=
      { runtime := { module := «module», host := {} }
        wasm := «module».initialStore } }

private def unaryConfig (body : Program)
    (a : UInt64) : SmallStep.Config Unit :=
  { expr := .running
      ⟨⟨[.i64 a], [], []⟩, body, 1, [], [], []⟩
    store :=
      { runtime := { module := «module», host := {} }
        wasm := «module».initialStore } }

private def shiftValueConfig (body : Program)
    (a : UInt64) (n : UInt32) (b : UInt64) : SmallStep.Config Unit :=
  { expr := .running
      ⟨⟨[.i64 a, .i32 n, .i64 b], [], []⟩,
        body, 1, [], [], []⟩
    store :=
      { runtime := { module := «module», host := {} }
        wasm := «module».initialStore } }

private def shiftTwiceConfig (body : Program)
    (a : UInt64) (n m : UInt32) : SmallStep.Config Unit :=
  { expr := .running
      ⟨⟨[.i64 a, .i32 n, .i32 m], [], []⟩,
        body, 1, [], [], []⟩
    store :=
      { runtime := { module := «module», host := {} }
        wasm := «module».initialStore } }

/-! ## add -/
@[spec_of "rust-exported" "rust_u64_tests::add_chain"]
def AddChainSpec : Prop := ∀ (a b c : UInt64),
  SmallStep.PartiallyMeets (ternaryConfig func0 a b c)
    (fun rs _store => rs = [.i64 (a + b + c)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.AddChainSpec]
theorem add_chain_correct : AddChainSpec := by
  intro a b c
  apply SmallStep.wasm_smallStep_partiallyMeets.{0} (α := Unit)
  intro gs
  simp only [ternaryConfig, func0]
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_addI64
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

@[spec_of "rust-exported" "rust_u64_tests::add_then_mul"]
def AddThenMulSpec : Prop := ∀ (a b c : UInt64),
  SmallStep.PartiallyMeets (ternaryConfig func1 a b c)
    (fun rs _store => rs = [.i64 ((a + b) * c)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.AddThenMulSpec]
theorem add_then_mul_correct : AddThenMulSpec := by
  intro a b c
  apply SmallStep.wasm_smallStep_partiallyMeets.{0} (α := Unit)
  intro gs
  simp only [ternaryConfig, func1]
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_addI64
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

/-! ## sub -/
@[spec_of "rust-exported" "rust_u64_tests::sub_chain"]
def SubChainSpec : Prop := ∀ (a b c : UInt64),
  SmallStep.PartiallyMeets (ternaryConfig func18 a b c)
    (fun rs _store => rs = [.i64 (a - b - c)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.SubChainSpec]
theorem sub_chain_correct : SubChainSpec := by
  intro a b c
  apply SmallStep.wasm_smallStep_partiallyMeets.{0} (α := Unit)
  intro gs
  simp only [ternaryConfig, func18]
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_subI64
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

@[spec_of "rust-exported" "rust_u64_tests::sub_then_add"]
def SubThenAddSpec : Prop := ∀ (a b c : UInt64),
  SmallStep.PartiallyMeets (ternaryConfig func19 a b c)
    (fun rs _store => rs = [.i64 ((a - b) + c)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.SubThenAddSpec]
theorem sub_then_add_correct : SubThenAddSpec := by
  intro a b c
  apply SmallStep.wasm_smallStep_partiallyMeets.{0} (α := Unit)
  intro gs
  simp only [ternaryConfig, func19]
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_subI64
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

/-! ## mul -/
@[spec_of "rust-exported" "rust_u64_tests::mul_chain"]
def MulChainSpec : Prop := ∀ (a b c : UInt64),
  SmallStep.PartiallyMeets (ternaryConfig func6 a b c)
    (fun rs _store => rs = [.i64 (a * b * c)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.MulChainSpec]
theorem mul_chain_correct : MulChainSpec := by
  intro a b c
  apply SmallStep.wasm_smallStep_partiallyMeets.{0} (α := Unit)
  intro gs
  simp only [ternaryConfig, func6]
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_mulI64
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

@[spec_of "rust-exported" "rust_u64_tests::mul_then_add"]
def MulThenAddSpec : Prop := ∀ (a b c : UInt64),
  SmallStep.PartiallyMeets (ternaryConfig func7 a b c)
    (fun rs _store => rs = [.i64 (a * b + c)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.MulThenAddSpec]
theorem mul_then_add_correct : MulThenAddSpec := by
  intro a b c
  apply SmallStep.wasm_smallStep_partiallyMeets.{0} (α := Unit)
  intro gs
  simp only [ternaryConfig, func7]
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_mulI64
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

/-! ## bitand -/
@[spec_of "rust-exported" "rust_u64_tests::and_chain"]
def AndChainSpec : Prop := ∀ (a b c : UInt64),
  SmallStep.PartiallyMeets (ternaryConfig func2 a b c)
    (fun rs _store => rs = [.i64 (a &&& b &&& c)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.AndChainSpec]
theorem and_chain_correct : AndChainSpec := by
  intro a b c
  apply SmallStep.wasm_smallStep_partiallyMeets.{0} (α := Unit)
  intro gs
  simp only [ternaryConfig, func2]
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_andI64
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

@[spec_of "rust-exported" "rust_u64_tests::and_then_or"]
def AndThenOrSpec : Prop := ∀ (a b c : UInt64),
  SmallStep.PartiallyMeets (ternaryConfig func3 a b c)
    (fun rs _store => rs = [.i64 ((a &&& b) ||| c)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.AndThenOrSpec]
theorem and_then_or_correct : AndThenOrSpec := by
  intro a b c
  apply SmallStep.wasm_smallStep_partiallyMeets.{0} (α := Unit)
  intro gs
  simp only [ternaryConfig, func3]
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_andI64
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

/-! ## bitor -/
@[spec_of "rust-exported" "rust_u64_tests::or_chain"]
def OrChainSpec : Prop := ∀ (a b c : UInt64),
  SmallStep.PartiallyMeets (ternaryConfig func10 a b c)
    (fun rs _store => rs = [.i64 (a ||| b ||| c)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.OrChainSpec]
theorem or_chain_correct : OrChainSpec := by
  intro a b c
  apply SmallStep.wasm_smallStep_partiallyMeets.{0} (α := Unit)
  intro gs
  simp only [ternaryConfig, func10]
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_orI64
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

@[spec_of "rust-exported" "rust_u64_tests::or_then_xor"]
def OrThenXorSpec : Prop := ∀ (a b c : UInt64),
  SmallStep.PartiallyMeets (ternaryConfig func11 a b c)
    (fun rs _store => rs = [.i64 ((a ||| b) ^^^ c)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.OrThenXorSpec]
theorem or_then_xor_correct : OrThenXorSpec := by
  intro a b c
  apply SmallStep.wasm_smallStep_partiallyMeets.{0} (α := Unit)
  intro gs
  simp only [ternaryConfig, func11]
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_orI64
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

/-! ## bitxor -/
@[spec_of "rust-exported" "rust_u64_tests::xor_chain"]
def XorChainSpec : Prop := ∀ (a b c : UInt64),
  SmallStep.PartiallyMeets (ternaryConfig func20 a b c)
    (fun rs _store => rs = [.i64 (a ^^^ b ^^^ c)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.XorChainSpec]
theorem xor_chain_correct : XorChainSpec := by
  intro a b c
  apply SmallStep.wasm_smallStep_partiallyMeets.{0} (α := Unit)
  intro gs
  simp only [ternaryConfig, func20]
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_xorI64
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

@[spec_of "rust-exported" "rust_u64_tests::xor_then_and"]
def XorThenAndSpec : Prop := ∀ (a b c : UInt64),
  SmallStep.PartiallyMeets (ternaryConfig func21 a b c)
    (fun rs _store => rs = [.i64 ((a ^^^ b) &&& c)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.XorThenAndSpec]
theorem xor_then_and_correct : XorThenAndSpec := by
  intro a b c
  apply SmallStep.wasm_smallStep_partiallyMeets.{0} (α := Unit)
  intro gs
  simp only [ternaryConfig, func21]
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_xorI64
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

/-! ## not -/
@[spec_of "rust-exported" "rust_u64_tests::not_twice"]
def NotTwiceSpec : Prop := ∀ (a : UInt64),
  SmallStep.PartiallyMeets (unaryConfig func9 a)
    (fun rs _store => rs = [.i64 (~~~(~~~a))])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.NotTwiceSpec]
theorem not_twice_correct : NotTwiceSpec := by
  intro a
  apply SmallStep.wasm_smallStep_partiallyMeets.{0} (α := Unit)
  intro gs
  simp only [unaryConfig, func9]
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_constI64
  inext
  iapply SmallStep.wp_xorI64
  inext
  rw [show a ^^^ (18446744073709551615 : UInt64) = ~~~a by bv_decide]
  iapply SmallStep.wp_constI64
  inext
  iapply SmallStep.wp_xorI64
  inext
  rw [show (~~~a) ^^^ (18446744073709551615 : UInt64) = ~~~(~~~a) by
    bv_decide]
  iapply SmallStep.wp_returnFromFunction
  inext
  iapply wp_value'
  ipureintro
  rfl

@[spec_of "rust-exported" "rust_u64_tests::not_then_xor"]
def NotThenXorSpec : Prop := ∀ (a b : UInt64),
  SmallStep.PartiallyMeets (binaryConfig func8 a b)
    (fun rs _store => rs = [.i64 ((~~~a) ^^^ b)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.NotThenXorSpec]
theorem not_then_xor_correct : NotThenXorSpec := by
  intro a b
  apply SmallStep.wasm_smallStep_partiallyMeets.{0} (α := Unit)
  intro gs
  simp only [binaryConfig, func8]
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_constI64
  inext
  iapply SmallStep.wp_xorI64
  inext
  rw [show a ^^^ (18446744073709551615 : UInt64) = ~~~a by bv_decide]
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_xorI64
  inext
  iapply SmallStep.wp_returnFromFunction
  inext
  iapply wp_value'
  ipureintro
  rfl

/-! ## div (divisor nonzero) -/
@[spec_of "rust-exported" "rust_u64_tests::div_then_add"]
def DivThenAddSpec : Prop := ∀ (a b c : UInt64), b ≠ 0 →
  SmallStep.PartiallyMeets (ternaryConfig func4 a b c)
    (fun rs _store => rs = [.i64 (a / b + c)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.DivThenAddSpec]
theorem div_then_add_correct : DivThenAddSpec := by
  intro a b c hb
  apply SmallStep.wasm_smallStep_partiallyMeets.{0} (α := Unit)
  intro gs
  simp only [ternaryConfig, func4]
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
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_addI64
  inext
  iapply SmallStep.wp_returnFromFunction
  inext
  iapply wp_value'
  ipureintro
  rfl

@[spec_of "rust-exported" "rust_u64_tests::div_then_mul"]
def DivThenMulSpec : Prop := ∀ (a b c : UInt64), b ≠ 0 →
  SmallStep.PartiallyMeets (ternaryConfig func5 a b c)
    (fun rs _store => rs = [.i64 (a / b * c)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.DivThenMulSpec]
theorem div_then_mul_correct : DivThenMulSpec := by
  intro a b c hb
  apply SmallStep.wasm_smallStep_partiallyMeets.{0} (α := Unit)
  intro gs
  simp only [ternaryConfig, func5]
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
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_mulI64
  inext
  iapply SmallStep.wp_returnFromFunction
  inext
  iapply wp_value'
  ipureintro
  rfl

/-! ## rem (divisor nonzero) -/
@[spec_of "rust-exported" "rust_u64_tests::rem_then_add"]
def RemThenAddSpec : Prop := ∀ (a b c : UInt64), b ≠ 0 →
  SmallStep.PartiallyMeets (ternaryConfig func12 a b c)
    (fun rs _store => rs = [.i64 (a % b + c)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.RemThenAddSpec]
theorem rem_then_add_correct : RemThenAddSpec := by
  intro a b c hb
  apply SmallStep.wasm_smallStep_partiallyMeets.{0} (α := Unit)
  intro gs
  simp only [ternaryConfig, func12]
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
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_addI64
  inext
  iapply SmallStep.wp_returnFromFunction
  inext
  iapply wp_value'
  ipureintro
  rfl

@[spec_of "rust-exported" "rust_u64_tests::rem_then_mul"]
def RemThenMulSpec : Prop := ∀ (a b c : UInt64), b ≠ 0 →
  SmallStep.PartiallyMeets (ternaryConfig func13 a b c)
    (fun rs _store => rs = [.i64 (a % b * c)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.RemThenMulSpec]
theorem rem_then_mul_correct : RemThenMulSpec := by
  intro a b c hb
  apply SmallStep.wasm_smallStep_partiallyMeets.{0} (α := Unit)
  intro gs
  simp only [ternaryConfig, func13]
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
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_mulI64
  inext
  iapply SmallStep.wp_returnFromFunction
  inext
  iapply wp_value'
  ipureintro
  rfl

/-! ## shl / shr — mask, extend, then shift -/
@[spec_of "rust-exported" "rust_u64_tests::shl_then_add"]
def ShlThenAddSpec : Prop := ∀ (a : UInt64) (n : UInt32) (b : UInt64),
  SmallStep.PartiallyMeets (shiftValueConfig func14 a n b)
    (fun rs _store => rs = [.i64 ((a <<< (n.toUInt64 % 64)) + b)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.ShlThenAddSpec]
theorem shl_then_add_correct : ShlThenAddSpec := by
  intro a n b
  apply SmallStep.wasm_smallStep_partiallyMeets.{0} (α := Unit)
  intro gs
  simp only [shiftValueConfig, func14]
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_const
  inext
  iapply SmallStep.wp_and
  inext
  rw [UInt32.and_comm n 63]
  iapply SmallStep.wp_extendUI32
  inext
  iapply SmallStep.wp_shlI64
  inext
  rw [shiftAmount_norm]
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_addI64
  inext
  iapply SmallStep.wp_returnFromFunction
  inext
  iapply wp_value'
  ipureintro
  rfl

@[spec_of "rust-exported" "rust_u64_tests::shl_twice"]
def ShlTwiceSpec : Prop := ∀ (a : UInt64) (n m : UInt32),
  SmallStep.PartiallyMeets (shiftTwiceConfig func15 a n m)
    (fun rs _store =>
      rs = [.i64 ((a <<< (n.toUInt64 % 64)) <<< (m.toUInt64 % 64))])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.ShlTwiceSpec]
theorem shl_twice_correct : ShlTwiceSpec := by
  intro a n m
  apply SmallStep.wasm_smallStep_partiallyMeets.{0} (α := Unit)
  intro gs
  simp only [shiftTwiceConfig, func15]
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_const
  inext
  iapply SmallStep.wp_and
  inext
  rw [UInt32.and_comm n 63]
  iapply SmallStep.wp_extendUI32
  inext
  iapply SmallStep.wp_shlI64
  inext
  rw [shiftAmount_norm]
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_const
  inext
  iapply SmallStep.wp_and
  inext
  rw [UInt32.and_comm m 63]
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

@[spec_of "rust-exported" "rust_u64_tests::shr_then_sub"]
def ShrThenSubSpec : Prop := ∀ (a : UInt64) (n : UInt32) (b : UInt64),
  SmallStep.PartiallyMeets (shiftValueConfig func16 a n b)
    (fun rs _store => rs = [.i64 ((a >>> (n.toUInt64 % 64)) - b)])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.ShrThenSubSpec]
theorem shr_then_sub_correct : ShrThenSubSpec := by
  intro a n b
  apply SmallStep.wasm_smallStep_partiallyMeets.{0} (α := Unit)
  intro gs
  simp only [shiftValueConfig, func16]
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_const
  inext
  iapply SmallStep.wp_and
  inext
  rw [UInt32.and_comm n 63]
  iapply SmallStep.wp_extendUI32
  inext
  iapply SmallStep.wp_shrUI64
  inext
  rw [shiftAmount_norm]
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_subI64
  inext
  iapply SmallStep.wp_returnFromFunction
  inext
  iapply wp_value'
  ipureintro
  rfl

@[spec_of "rust-exported" "rust_u64_tests::shr_twice"]
def ShrTwiceSpec : Prop := ∀ (a : UInt64) (n m : UInt32),
  SmallStep.PartiallyMeets (shiftTwiceConfig func17 a n m)
    (fun rs _store =>
      rs = [.i64 ((a >>> (n.toUInt64 % 64)) >>> (m.toUInt64 % 64))])
set_option maxRecDepth 4096 in
@[proves Project.RustU64Tests.Spec.ShrTwiceSpec]
theorem shr_twice_correct : ShrTwiceSpec := by
  intro a n m
  apply SmallStep.wasm_smallStep_partiallyMeets.{0} (α := Unit)
  intro gs
  simp only [shiftTwiceConfig, func17]
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_const
  inext
  iapply SmallStep.wp_and
  inext
  rw [UInt32.and_comm n 63]
  iapply SmallStep.wp_extendUI32
  inext
  iapply SmallStep.wp_shrUI64
  inext
  rw [shiftAmount_norm]
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_const
  inext
  iapply SmallStep.wp_and
  inext
  rw [UInt32.and_comm m 63]
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

end Project.RustU64Tests.Spec
