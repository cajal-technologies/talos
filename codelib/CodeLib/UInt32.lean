/-!
# `UInt32` arithmetic helpers used by corpus specs

Small bridge lemmas connecting `UInt32` bitwise operations to the
`Nat` view that user-facing specifications prefer.

`and_one_eq_zero_iff_toNat_mod_two` is consumed by the verifier's scaffolded
starter proof (`verifier/template/project/lean/Project/IsEven/Spec.lean`), so
the module is live even though nothing in `programs/lean` references it yet. It
overlaps the width-generic parity bridge in `UInt64.lean`; both are candidates
to fold into one shared low-bit lemma once that consolidation is done (keep this
public name as a corollary — the template simp-references it).
-/

namespace Wasm

/-- `n &&& 1 = 0` (bitwise low-bit zero) is equivalent to
`n.toNat % 2 = 0` (semantic evenness). The forward proof factors
through `BitVec.toNat_and` and the standard `Nat.and_one_is_mod`. -/
theorem UInt32.and_one_eq_zero_iff_toNat_mod_two (n : UInt32) :
    n &&& 1 = 0 ↔ n.toNat % 2 = 0 := by
  have hN : (n &&& 1).toNat = n.toNat % 2 := by
    show (n.toBitVec &&& (1 : UInt32).toBitVec).toNat = _
    rw [BitVec.toNat_and]
    show n.toNat &&& 1 = _
    exact Nat.and_one_is_mod n.toNat
  constructor
  · intro h
    have : (n &&& 1).toNat = (0 : UInt32).toNat := by rw [h]
    rw [hN] at this
    simpa using this
  · intro h
    have h1 : (n &&& 1).toNat = 0 := by rw [hN]; exact h
    have h2 : (n &&& 1).toNat = (0 : UInt32).toNat := by simpa using h1
    exact UInt32.toNat.inj h2

end Wasm
