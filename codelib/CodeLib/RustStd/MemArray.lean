import CodeLib.RustStd.Region

/-!
# `CodeLib.RustStd.MemArray`

The address bridge between a `u64`/`u32` array slot index and its wasm address:
the `k`-th slot of an array based at `base` lives at `base + 8 * k` (resp.
`base + 4 * k`), and as long as that does not wrap it denotes the integer
`base.toNat + 8 * k` (resp. `base.toNat + 4 * k`).

This file used to also carry a `List UInt64` *view* of an array in linear memory
(`Mem.words64 base n` and a 32-bit twin, plus their `length`/`getElem`/`ext`
lemmas and their interaction with `write64`). That view had no consumers: it was
written for a merge_sort `wordsAt` view that never landed, and every array proof
in the tree works directly through `MemRegion` framing instead. Only the two
address lemmas below were ever used, so the view has been removed.
-/

namespace Wasm

/-- The wasm address of the `k`-th `u64` slot, `base + 8 * k`, is the integer
`base.toNat + 8 * k` as long as it does not wrap. Shared address bridge for the
`u64` array loops. -/
theorem Mem.words64_slotAddr_toNat (base : UInt32) (k : Nat)
    (h : base.toNat + 8 * k < 4294967296) :
    (base + 8 * UInt32.ofNat k).toNat = base.toNat + 8 * k := by
  have hsize : (UInt32.size : Nat) = 4294967296 := rfl
  have hkn : (UInt32.ofNat k).toNat = k :=
    UInt32.toNat_ofNat_of_lt' (by omega : k < UInt32.size)
  have := MemRegion.slot64_base_toNat base (UInt32.ofNat k) (by rw [hkn]; omega)
  rw [hkn] at this; exact this

/-- The wasm address of the `k`-th `u32` slot, `base + 4 * k`, is the integer
`base.toNat + 4 * k` as long as it does not wrap. The 32-bit twin of
`Mem.words64_slotAddr_toNat`. -/
theorem Mem.words32_slotAddr_toNat (base : UInt32) (k : Nat)
    (h : base.toNat + 4 * k < 4294967296) :
    (base + 4 * UInt32.ofNat k).toNat = base.toNat + 4 * k := by
  have hsize : (UInt32.size : Nat) = 4294967296 := rfl
  have hkn : (UInt32.ofNat k).toNat = k :=
    UInt32.toNat_ofNat_of_lt' (by omega : k < UInt32.size)
  have := MemRegion.slot32_base_toNat base (UInt32.ofNat k) (by rw [hkn]; omega)
  rw [hkn] at this; exact this

end Wasm
