import HexEncodeStdio.ResourceProof

/-! # Verifier registrations for the hex encoder

The total functional contract covers every input. The stronger memory contract
guarantees normal return within its explicit input bound. Numerical work and
runner budgets remain in the separate proof APIs.
-/

namespace Project.HexStdio.Proof

open Wasm Project.HexEncodeStdio

/-- Register the existing total success-or-OOM theorem with the verifier. -/
@[proves Project.HexStdio.Spec.EncodeSpec]
theorem encode_total_correct : Spec.EncodeSpec := by
  intro input
  exact Blueprint.encode_export_outcome input

/-- Register normal return and every-prefix physical-memory bounds without
an assumed execution or allocator-success premise. -/
@[proves Project.HexStdio.Spec.EncodeMemorySpec]
theorem encode_memory_correct : Spec.EncodeMemorySpec := by
  intro input hbound
  obtain ⟨initial, initialized, ⟨trace, store, amount, execution, encoded, _, _⟩,
    pageBounds, _⟩ := ResourceProof.named_export_resources input hbound
  constructor
  · exact ⟨initial, initialized, trace, [], store, execution.erase, rfl, encoded⟩
  · intro configured hstart prefixTrace reached partialExecution
    rw [initialized] at hstart
    cases Option.some.inj hstart
    simpa only [ResourceBounds.pageBound, AllocatorResourceCost.requiredPages,
      ResourceBounds.completeFrontierBound_eq, Spec.encodePageBound, Nat.add_comm]
      using pageBounds prefixTrace reached partialExecution

end Project.HexStdio.Proof
