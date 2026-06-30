import Project.RustArrayTests.Program
import Interpreter.Wasm.Wp.Call

/-!
# Reuse tests for the `CodeLib/RustStd/Array` corpus
-/

namespace Project.RustArrayTests.Spec

open Wasm Wasm.RustStd Wasm.RustStd.Array

-- The export proofs below unfold the 9-function module deep enough to need a
-- raised recursion limit; set it once for the file.
set_option maxRecDepth 4096

/-! ## Shared call bridges

Each bridge proves an impl body's behaviour at an *arbitrary* store (the impls
touch no memory), reusing the CodeLib `Array` chunks. They serve both layers: the
internal specs below are each just the matching bridge at `«module».initialStore`
with no extra stack, and the exported wrappers `call` the same body after
marshalling the fat pointer back from memory. -/

private theorem isEmpty_call {env : HostEnv Unit} (st : Store Unit)
    (ptr len : UInt32) (rest : List Value) :
    TerminatesWith env «module» 3 st (.i32 len :: .i32 ptr :: rest)
      (fun st' vs => vs = .i32 (isEmptyValue len) :: rest ∧ framePost st st') :=
  isEmptyBodyTerminates st ptr len rest rfl rfl rfl rfl

private theorem lenPlusOne_call {env : HostEnv Unit} (st : Store Unit)
    (dataPtr len : UInt32) (rest : List Value) :
    TerminatesWith env «module» 1 st (.i32 len :: .i32 dataPtr :: rest)
      (fun _ vs => vs = .i32 (len + 1) :: rest) := by
  apply TerminatesWith.of_wp_entry_for (f := func1Def) rfl
  unfold func1Def func1
  wp_run
  simp [UInt32.add_comm 1 len]

private theorem lenPlusArg_call {env : HostEnv Unit} (st : Store Unit)
    (dataPtr len n : UInt32) (rest : List Value) :
    TerminatesWith env «module» 0 st (.i32 n :: .i32 len :: .i32 dataPtr :: rest)
      (fun _ vs => vs = .i32 (len + n) :: rest) := by
  apply TerminatesWith.of_wp_entry_for (f := func0Def) rfl
  unfold func0Def func0
  wp_run
  simp [UInt32.add_comm n len]

private theorem emptyPlusThree_call {env : HostEnv Unit} (st : Store Unit)
    (dataPtr len : UInt32) (rest : List Value) :
    TerminatesWith env «module» 4 st (.i32 len :: .i32 dataPtr :: rest)
      (fun _ vs => vs = .i32 (isEmptyValue len + 3) :: rest) := by
  apply TerminatesWith.of_wp_entry_for (f := func4Def) rfl
  unfold func4Def func4
  wp_run
  apply wp_call_tw (isEmpty_call st dataPtr len [])
  intro st1 vs1 h1
  obtain ⟨hvs1, _, _⟩ := h1
  subst hvs1
  wp_run
  rw [isEmptyValue_and_one]
  rw [UInt32.add_comm 3 (isEmptyValue len)]
  simp

private theorem emptyXorFlag_call {env : HostEnv Unit} (st : Store Unit)
    (dataPtr len flag : UInt32) (rest : List Value) :
    TerminatesWith env «module» 2 st (.i32 flag :: .i32 len :: .i32 dataPtr :: rest)
      (fun _ vs => vs = .i32 (isEmptyValue len ^^^ flag) :: rest) := by
  apply TerminatesWith.of_wp_entry_for (f := func2Def) rfl
  unfold func2Def func2
  wp_run
  apply wp_call_tw (isEmpty_call st dataPtr len [])
  intro st1 vs1 h1
  obtain ⟨hvs1, _, _⟩ := h1
  subst hvs1
  wp_run
  rw [isEmptyValue_and_one]
  simp

/-! ## Internal impl-body specs

Each is the matching call bridge at `«module».initialStore` with an empty trailing
stack. -/

@[spec_of "rust-internal" "rust_array_tests::len_plus_one"]
def LenPlusOneSpec : Prop := ∀ (env : HostEnv Unit) (ptr len : UInt32),
  TerminatesWith env «module» 1 «module».initialStore [.i32 len, .i32 ptr]
    (fun _ rs => rs = [.i32 (len + 1)])

@[proves Project.RustArrayTests.Spec.LenPlusOneSpec]
theorem len_plus_one_correct : LenPlusOneSpec := by
  intro env ptr len
  exact lenPlusOne_call «module».initialStore ptr len []

@[spec_of "rust-internal" "rust_array_tests::len_plus_arg"]
def LenPlusArgSpec : Prop := ∀ (env : HostEnv Unit) (ptr len n : UInt32),
  TerminatesWith env «module» 0 «module».initialStore [.i32 n, .i32 len, .i32 ptr]
    (fun _ rs => rs = [.i32 (len + n)])

@[proves Project.RustArrayTests.Spec.LenPlusArgSpec]
theorem len_plus_arg_correct : LenPlusArgSpec := by
  intro env ptr len n
  exact lenPlusArg_call «module».initialStore ptr len n []

@[spec_of "rust-internal" "rust_array_tests::empty_plus_three"]
def EmptyPlusThreeSpec : Prop := ∀ (env : HostEnv Unit) (ptr len : UInt32),
  TerminatesWith env «module» 4 «module».initialStore [.i32 len, .i32 ptr]
    (fun _ rs => rs = [.i32 (isEmptyValue len + 3)])

@[proves Project.RustArrayTests.Spec.EmptyPlusThreeSpec]
theorem empty_plus_three_correct : EmptyPlusThreeSpec := by
  intro env ptr len
  exact emptyPlusThree_call «module».initialStore ptr len []

@[spec_of "rust-internal" "rust_array_tests::empty_xor_flag"]
def EmptyXorFlagSpec : Prop := ∀ (env : HostEnv Unit) (ptr len flag : UInt32),
  TerminatesWith env «module» 2 «module».initialStore [.i32 flag, .i32 len, .i32 ptr]
    (fun _ rs => rs = [.i32 (isEmptyValue len ^^^ flag)])

@[proves Project.RustArrayTests.Spec.EmptyXorFlagSpec]
theorem empty_xor_flag_correct : EmptyXorFlagSpec := by
  intro env ptr len flag
  exact emptyXorFlag_call «module».initialStore ptr len flag []

/-! ## Exported ABI wrappers (fat pointer in memory)

The internal specs above verify the inlined-reuse impl bodies. The wasm exports
(`func5`–`func8`) receive the slice as a fat pointer in linear memory: each loads
`(dataPtr, len)` back with `fatPtrLoadWp` and calls the impl body above. So, like
the `rust_u64_tests` crate, the actual exported functions are verified — but
unlike that scalar crate, here end-to-end through the memory marshalling,
conditional on the shared `FatPtrAt` ABI contract, reusing the same call
bridges. -/

@[spec_of "rust-exported" "rust_array_tests::len_plus_one"]
def LenPlusOneExportSpec : Prop :=
  ∀ (env : HostEnv Unit) (st : Store Unit) (p dataPtr len : UInt32),
    FatPtrAt st p dataPtr len →
    TerminatesWith env «module» 8 st [.i32 p] (fun _ rs => rs = [.i32 (len + 1)])

@[proves Project.RustArrayTests.Spec.LenPlusOneExportSpec]
theorem len_plus_one_export_correct : LenPlusOneExportSpec := by
  intro env st p dataPtr len hfat
  apply TerminatesWith.of_wp_entry_for (f := func8Def) rfl
  unfold func8Def func8
  load_fat_ptr p, dataPtr, len using hfat
  apply wp_call_tw (lenPlusOne_call st dataPtr len [])
  intro st1 vs1 h1
  subst h1
  wp_run
  simp

@[spec_of "rust-exported" "rust_array_tests::len_plus_arg"]
def LenPlusArgExportSpec : Prop :=
  ∀ (env : HostEnv Unit) (st : Store Unit) (p dataPtr len n : UInt32),
    FatPtrAt st p dataPtr len →
    TerminatesWith env «module» 7 st [.i32 n, .i32 p] (fun _ rs => rs = [.i32 (len + n)])

@[proves Project.RustArrayTests.Spec.LenPlusArgExportSpec]
theorem len_plus_arg_export_correct : LenPlusArgExportSpec := by
  intro env st p dataPtr len n hfat
  apply TerminatesWith.of_wp_entry_for (f := func7Def) rfl
  unfold func7Def func7
  load_fat_ptr p, dataPtr, len using hfat
  wp_run
  apply wp_call_tw (lenPlusArg_call st dataPtr len n [])
  intro st1 vs1 h1
  subst h1
  wp_run
  simp

@[spec_of "rust-exported" "rust_array_tests::empty_plus_three"]
def EmptyPlusThreeExportSpec : Prop :=
  ∀ (env : HostEnv Unit) (st : Store Unit) (p dataPtr len : UInt32),
    FatPtrAt st p dataPtr len →
    TerminatesWith env «module» 5 st [.i32 p] (fun _ rs => rs = [.i32 (isEmptyValue len + 3)])

@[proves Project.RustArrayTests.Spec.EmptyPlusThreeExportSpec]
theorem empty_plus_three_export_correct : EmptyPlusThreeExportSpec := by
  intro env st p dataPtr len hfat
  apply TerminatesWith.of_wp_entry_for (f := func5Def) rfl
  unfold func5Def func5
  load_fat_ptr p, dataPtr, len using hfat
  apply wp_call_tw (emptyPlusThree_call st dataPtr len [])
  intro st1 vs1 h1
  subst h1
  wp_run
  simp

@[spec_of "rust-exported" "rust_array_tests::empty_xor_flag"]
def EmptyXorFlagExportSpec : Prop :=
  ∀ (env : HostEnv Unit) (st : Store Unit) (p dataPtr len flag : UInt32),
    FatPtrAt st p dataPtr len →
    TerminatesWith env «module» 6 st [.i32 flag, .i32 p]
      (fun _ rs => rs = [.i32 (isEmptyValue len ^^^ flag)])

@[proves Project.RustArrayTests.Spec.EmptyXorFlagExportSpec]
theorem empty_xor_flag_export_correct : EmptyXorFlagExportSpec := by
  intro env st p dataPtr len flag hfat
  apply TerminatesWith.of_wp_entry_for (f := func6Def) rfl
  unfold func6Def func6
  load_fat_ptr p, dataPtr, len using hfat
  wp_run
  apply wp_call_tw (emptyXorFlag_call st dataPtr len flag [])
  intro st1 vs1 h1
  subst h1
  wp_run
  simp

end Project.RustArrayTests.Spec
