import Project.IsOdd.Spec

namespace Project.IsOdd.Proof

open Wasm Project.IsOdd Project.IsOdd.Spec

@[proves Project.IsOdd.Spec.IsOddSpec]
theorem is_odd_spec : IsOddSpec := by
  intro initial n
  wasm_entry
  simp only [func0Def]
  unfold func0
  wp_run
  simp [UInt32.and_comm]

end Project.IsOdd.Proof
