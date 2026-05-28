import Programs.Simple.IsEven.Program

/-!
# Specification for `is_even`

The exported `is_even` function returns `1` if its `i32` argument is even,
`0` otherwise.

The proof is deferred — this file currently states the spec only. Discharge
via the `wp` framework (`wp_run`, etc.) on `Wasm.run`.
-/

namespace Programs.Simple.IsEven.Spec

open Wasm

/-- `is_even n` terminates with `[1]` when `n` is even, `[0]` otherwise. -/
theorem is_even_correct (initial : Store) (n : UInt32) :
    TerminatesWith «module» 0 initial [.i32 n]
      (fun _ rs => rs = [.i32 (if n.toNat % 2 = 0 then 1 else 0)]) := by
  apply TerminatesWith.of_wp_entry (f := ⟨[.i32], [], func0, [.i32]⟩) rfl
  intro initial'
  unfold func0
  wp_run
  simp [UInt32.and_one_eq_zero_iff_toNat_mod_two, UInt32.and_comm]

end Programs.Simple.IsEven.Spec
