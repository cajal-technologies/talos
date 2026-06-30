import Project.RustArray.Program
import Interpreter.Wasm.Wp.Call

/-!
# Specs for the `rust_array` slice primitive corpus

Two layers, both discharged by reusing the `CodeLib/RustStd/Array` chunks:

* the internal raw `(ptr, len)` bodies (`func0` = `len`, `func2` = `is_empty`),
  reusing `lenBodyWp` / `isEmptyBodyWp`; and
* the exported ABI wrappers (`func4` = `len`, `func5` = `is_empty`), which receive
  the slice as a fat pointer in linear memory: they `load32` the `(dataPtr, len)`
  fields back with `fatPtrLoadWp` and then `call` the bodies above (`is_empty`
  through the `crate::is_empty` re-mask wrapper `func1`). The export specs are
  therefore conditional on the caller having laid a fat pointer in memory at the
  argument pointer `p` — the shared `FatPtrAt` contract (`dataPtr` at `p+0`, `len`
  at `p+4`, in bounds). They are *conditional total correctness*: given that
  contract the call terminates with the right value; the out-of-bounds case
  (where the `load32` traps) is outside the contract and deliberately not
  asserted.
-/

namespace Project.RustArray.Spec

open Wasm Wasm.RustStd Wasm.RustStd.Array

/-! ## Internal `(ptr, len)` bodies -/

@[spec_of "rust-internal" "rust_array::len"]
def LenSpec : Prop := ∀ (env : HostEnv Unit) (ptr len : UInt32),
  TerminatesWith env «module» 0 «module».initialStore [.i32 len, .i32 ptr]
    (fun _ rs => rs = [.i32 len])

@[proves Project.RustArray.Spec.LenSpec]
theorem len_correct : LenSpec := by
  intro env ptr len
  exact (TerminatesWith.of_returns_wp (f := func0Def) (rs := [.i32 len]) rfl rfl
      (lenBodyWp «module».initialStore 1 len [] rfl) rfl).mono (fun _ _ h => h.1)

@[spec_of "rust-internal" "rust_array::is_empty"]
def IsEmptySpec : Prop := ∀ (env : HostEnv Unit) (ptr len : UInt32),
  TerminatesWith env «module» 2 «module».initialStore [.i32 len, .i32 ptr]
    (fun _ rs => rs = [.i32 (isEmptyValue len)])

@[proves Project.RustArray.Spec.IsEmptySpec]
theorem is_empty_correct : IsEmptySpec := by
  intro env ptr len
  exact (TerminatesWith.of_returns_wp (f := func2Def) (rs := [.i32 (isEmptyValue len)]) rfl rfl
      (isEmptyBodyWp «module».initialStore 1 len [] rfl) rfl).mono (fun _ _ h => h.1)

/-! ## Call bridges for the exported wrappers

Each bridge is the callee's behaviour at the export's store, reusing the body
chunk above; `wp_call_tw` threads it through the `.call` in the wrapper. -/

/-- `func0` (`len` body) as a callee: returns the length argument. -/
private theorem len_call {env : HostEnv Unit} (st : Store Unit)
    (dataPtr len : UInt32) (rest : List Value) :
    TerminatesWith env «module» 0 st (.i32 len :: .i32 dataPtr :: rest)
      (fun st' vs => vs = .i32 len :: rest ∧ framePost st st') :=
  TerminatesWith.of_returns_wp (f := func0Def) (rs := [.i32 len]) rfl rfl
    (lenBodyWp st 1 len [] rfl) rfl

/-- `func2` (`is_empty` leaf body) as a callee: returns `isEmptyValue len`,
reusing the CodeLib leaf bridge `isEmptyBodyTerminates`. -/
private theorem isEmptyLeaf_call {env : HostEnv Unit} (st : Store Unit)
    (dataPtr len : UInt32) (rest : List Value) :
    TerminatesWith env «module» 2 st (.i32 len :: .i32 dataPtr :: rest)
      (fun st' vs => vs = .i32 (isEmptyValue len) :: rest ∧ framePost st st') :=
  isEmptyBodyTerminates st dataPtr len rest rfl rfl rfl rfl

/-- `func1` (`crate::is_empty`) as a callee: calls the leaf `is_empty` and
re-masks the bool with `& 1`, which `isEmptyValue_and_one` collapses. -/
private theorem crateIsEmpty_call {env : HostEnv Unit} (st : Store Unit)
    (dataPtr len : UInt32) (rest : List Value) :
    TerminatesWith env «module» 1 st (.i32 len :: .i32 dataPtr :: rest)
      (fun _ vs => vs = .i32 (isEmptyValue len) :: rest) := by
  apply TerminatesWith.of_wp_entry_for (f := func1Def) rfl
  unfold func1Def func1
  wp_run
  apply wp_call_tw (isEmptyLeaf_call st dataPtr len [])
  intro st1 vs1 h1
  obtain ⟨hvs1, _⟩ := h1
  subst hvs1
  wp_run
  rw [isEmptyValue_and_one]
  simp

/-! ## Exported ABI wrappers (fat pointer in memory) -/

@[spec_of "rust-exported" "rust_array::len"]
def LenExportSpec : Prop := ∀ (env : HostEnv Unit) (st : Store Unit) (p dataPtr len : UInt32),
  FatPtrAt st p dataPtr len →
  TerminatesWith env «module» 4 st [.i32 p]
    (fun _ rs => rs = [.i32 len])

@[proves Project.RustArray.Spec.LenExportSpec]
theorem len_export_correct : LenExportSpec := by
  intro env st p dataPtr len hfat
  apply TerminatesWith.of_wp_entry_for (f := func4Def) rfl
  unfold func4Def func4
  load_fat_ptr p, dataPtr, len using hfat
  apply wp_call_tw (len_call st dataPtr len [])
  intro st1 vs1 h1
  obtain ⟨hvs1, _⟩ := h1
  subst hvs1
  wp_run
  simp

@[spec_of "rust-exported" "rust_array::is_empty"]
def IsEmptyExportSpec : Prop := ∀ (env : HostEnv Unit) (st : Store Unit) (p dataPtr len : UInt32),
  FatPtrAt st p dataPtr len →
  TerminatesWith env «module» 5 st [.i32 p]
    (fun _ rs => rs = [.i32 (isEmptyValue len)])

@[proves Project.RustArray.Spec.IsEmptyExportSpec]
theorem is_empty_export_correct : IsEmptyExportSpec := by
  intro env st p dataPtr len hfat
  apply TerminatesWith.of_wp_entry_for (f := func5Def) rfl
  unfold func5Def func5
  load_fat_ptr p, dataPtr, len using hfat
  apply wp_call_tw (crateIsEmpty_call st dataPtr len [])
  intro st1 vs1 h1
  subst h1
  wp_run
  rw [isEmptyValue_and_one]
  simp

end Project.RustArray.Spec
