import Project.SwapElements.Program

/-!
# Shared address vocabulary for `swap_elements`

These definitions are independent of either the legacy big-step proof or the
authoritative small-step Iris proof.  Both optimization levels use them to
state element-wise memory properties.
-/

namespace Project.SwapElements.Spec

open Wasm

/-- Byte address of the `k`-th `u64` element of an array based at `ptr`. -/
@[reducible] def elemAddr (ptr k : UInt32) : UInt32 := ptr + 8 * k

/-- Address arithmetic emitted by the generated code. -/
theorem elemAddr_of_shl (ptr k : UInt32) :
    k <<< (3 % 32 : UInt32) + ptr = elemAddr ptr k :=
  MemRegion.slot64_of_shl ptr k

/-- A non-wrapping element address agrees with natural-number arithmetic. -/
theorem elemAddr_toNat (ptr k : UInt32)
    (h : ptr.toNat + 8 * k.toNat < 4294967296) :
    (elemAddr ptr k).toNat = ptr.toNat + 8 * k.toNat :=
  MemRegion.slot64_base_toNat ptr k h

/-- Distinct non-wrapping `u64` elements occupy disjoint byte ranges. -/
theorem elemAddr_disjoint (ptr k l : UInt32)
    (hk : ptr.toNat + 8 * k.toNat < 4294967296)
    (hl : ptr.toNat + 8 * l.toNat < 4294967296)
    (hkl : k ≠ l) :
    (elemAddr ptr k).toNat + 8 ≤ (elemAddr ptr l).toNat
      ∨ (elemAddr ptr l).toNat + 8 ≤ (elemAddr ptr k).toNat :=
  MemRegion.slot64_disjoint ptr k l hk hl hkl

end Project.SwapElements.Spec
