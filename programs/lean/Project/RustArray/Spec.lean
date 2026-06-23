import Project.RustArray.Program

/-!
# Specs for the `rust_array` slice primitive corpus
-/

namespace Project.RustArray.Spec

open Wasm Wasm.RustStd Wasm.RustStd.Array

/-! The reusable slice primitive bodies are the internal raw `(ptr, len)`
functions. The exported ABI wrappers unpack a fat pointer from memory before
calling these bodies. -/

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

end Project.RustArray.Spec
