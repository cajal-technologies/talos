import Project.IsEven.Program

/-!
# Specification for `is_even`
-/

namespace Project.IsEven.Spec

open Wasm

/-- The exported `is_even` returns `1` for even inputs and `0` otherwise.

Informal spec:
For any input `n : UInt32`, the wasm export `is_even` terminates and
leaves a single i32 on the value stack, equal to `1` when `n` is even
and `0` otherwise. The result is independent of the initial store. -/
@[spec_of "rust-exported" "is_even::is_even"]
def IsEvenSpec : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (n : UInt32),
    TerminatesWith env «module» 0 initial [.i32 n]
      (fun _ rs => rs = [.i32 (if n.toNat % 2 = 0 then 1 else 0)])

@[proves Project.IsEven.Spec.IsEvenSpec]
theorem is_even_correct : IsEvenSpec := by
  intro env initial n
  apply TerminatesWith.of_wp_entry (f := ⟨[.i32], [], func0, [.i32]⟩) rfl
  intro initial'
  unfold func0
  wp_run
  simp [UInt32.and_one_eq_zero_iff_toNat_mod_two, UInt32.and_comm]

end Project.IsEven.Spec
