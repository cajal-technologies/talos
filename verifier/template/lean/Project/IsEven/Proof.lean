import Project.IsEven.Spec

namespace Project.IsEven.Proof

open Wasm Project.IsEven Project.IsEven.Spec

theorem is_even_spec : IsEvenSpec := by
  intro initial n
  apply TerminatesWith.of_wp_entry
    (f := ⟨[.i32], [], func0, [.i32]⟩) rfl
  unfold func0
  wp_run
  simp [UInt32.and_one_eq_zero_iff_toNat_mod_two, UInt32.and_comm]

end Project.IsEven.Proof
