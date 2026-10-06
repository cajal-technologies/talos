import CodeLib.RustStd.HashMap.TableMem

/-!
# A freshly allocated table

`rust_hash_map` builds a new table in func 17 at WAT lines 3665 to 3728 of
`programs/rust/build/rust_hash_map/program.wat`.  The code there is:

* local 12 is `buckets + 8`, the number of control bytes.
* local 11 is `buckets << 3`, the number of bytes of the bucket area.
* local 9 is the sum, and two guards reject an overflow and a request
  above `2147483640`.
* `call 58` allocates local 9 bytes with alignment 8 into local 22.
* local 9 becomes `local 22 + local 11`, the control pointer.
* `memory.fill` writes `255` over local 12 bytes at that pointer.

`Table.newEmpty buckets` is the model of the same table: its control bytes
are `List.replicate (buckets + 8) EMPTY` and its slots are
`List.replicate buckets none`.

This file turns the allocation and the fill into `TableBody`.
`twp_memoryFill32` leaves `pointsToBytes` of a `List.replicate`, which is
already the control list of `newEmpty` once `toUInt8_fillByte` renames the
byte.  The bucket area needs more work, because `slotsBefore` walks down
from the control pointer in eight-byte steps while the allocation is one
flat byte range.  `slotsBefore_replicate_none` does that walk.
`TableBody_newEmpty` puts the header, the bucket area and the control
bytes together.
-/

namespace Wasm.RustStd.HashMap.Table

open Wasm.SepLogic Wasm.SepLogic.Slices Iris Std

/-! ## The filled byte -/

/-- `memory.fill` pushes `255` as an `i32`, and the rule keeps its low
byte.  That byte is `EMPTY`. -/
theorem toUInt8_fillByte : (255 : UInt32).toUInt8 = EMPTY := by decide

/-- The control bytes of a fresh table. -/
theorem newEmpty_ctrl (buckets : Nat) {K V : Type} :
    (newEmpty buckets : Table K V).ctrl = List.replicate (buckets + 8) EMPTY := rfl

/-- The slots of a fresh table. -/
theorem newEmpty_slots (buckets : Nat) {K V : Type} :
    (newEmpty buckets : Table K V).slots = List.replicate buckets none := rfl

section Memory

variable {α : Type} [WasmHeapGS α]

/-! ## The bucket area -/

/-- Eight owned bytes with no defined content are one empty slot. -/
theorem slotCell_none_of_ByteSlice (memId : Nat) (addr : UInt32)
    (bytes : List UInt8) (hlen : bytes.length = 8) :
    Slices.ByteSlice (α := α) memId addr bytes ⊢ slotCell memId addr none := by
  unfold Slices.ByteSlice slotCell
  iintro ⟨%_hnowrap, Hbytes⟩
  iexists bytes
  isplitl_pureexact hlen
  iexact Hbytes

/-- A flat range of `8 * n` bytes below the control pointer is `n` empty
slots.  The allocation of func 17 gives the range; `newEmpty` asks for the
slots. -/
theorem slotsBefore_replicate_none (memId : Nat) (n : Nat) :
    ∀ (lo : UInt32) (bytes : List UInt8), bytes.length = 8 * n →
      Slices.ByteSlice (α := α) memId lo bytes ⊢
        slotsBefore memId (lo + UInt32.ofNat (8 * n)) (List.replicate n none) := by
  induction n with
  | zero =>
    intro lo bytes hlen
    have hnil : bytes = [] := by
      cases bytes with
      | nil => rfl
      | cons _b _rest => simp at hlen
    subst hnil
    simp only [List.replicate_zero, slotsBefore]
    unfold Slices.ByteSlice
    iintro ⟨%_hnowrap, Hemp⟩
    iapply (pointsToBytes_nil memId lo).mp
    iexact Hemp
  | succ k ih =>
    intro lo bytes hlen
    have htake : (bytes.take (8 * k)).length = 8 * k := by
      rw [List.length_take]; omega
    have hdrop : (bytes.drop (8 * k)).length = 8 := by
      rw [List.length_drop]; omega
    have hsplit := ByteSlice_append (α := α) memId lo
      (bytes.take (8 * k)) (bytes.drop (8 * k))
    rw [List.take_append_drop, htake] at hsplit
    have hlo : lo + UInt32.ofNat (8 * (k + 1)) - 8 = lo + UInt32.ofNat (8 * k) := by
      rw [Nat.mul_succ, UInt32.ofNat_add, ← UInt32.add_assoc,
        show UInt32.ofNat 8 = (8 : UInt32) from rfl, UInt32.add_sub_cancel]
    iintro Hbytes
    icases hsplit.mp $$ Hbytes with ⟨Hlow, Hhigh⟩
    simp only [List.replicate_succ, slotsBefore]
    rw [hlo]
    isplitl [Hhigh]
    · iapply (slotCell_none_of_ByteSlice memId (lo + UInt32.ofNat (8 * k))
        (bytes.drop (8 * k)) hdrop)
      iexact Hhigh
    · iapply (ih lo (bytes.take (8 * k)) htake)
      iexact Hlow

/-! ## The whole table -/

/-- The allocation and the fill of func 17 are `TableBody` of
`Table.newEmpty`.  `lo` is the allocated base, `ctrl` is `lo + 8 * buckets`
as the code computes it, and the control bytes are the ones `memory.fill`
leaves. -/
theorem TableBody_newEmpty (memId : Nat) (base lo ctrl : UInt32) (buckets : Nat)
    (slotBytes : List UInt8) (hslots : slotBytes.length = 8 * buckets)
    (hctrl : lo + UInt32.ofNat (8 * buckets) = ctrl)
    (hfit : 8 * buckets ≤ ctrl.toNat)
    (hnowrap : ctrl.toNat + (buckets + 8) < UInt32.size) :
    iprop(tableHeader memId base ctrl (UInt32.ofNat (buckets - 1))
        (UInt32.ofNat (bucketMaskToCapacity (buckets - 1))) 0 ∗
      Slices.ByteSlice memId lo slotBytes ∗
      pointsToBytes memId ctrl (List.replicate (buckets + 8) EMPTY)) ⊢
      TableBody (α := α) memId base ctrl (newEmpty buckets) := by
  unfold TableBody
  simp only [newEmpty]
  iintro ⟨Hheader, Hslots, Hctrl⟩
  isplitl_pureexact hfit
  isplitl [Hheader]
  · iexact Hheader
  · isplitl [Hctrl]
    · unfold Slices.ByteSlice
      isplitl_pureexact (show ctrl.toNat + (List.replicate (buckets + 8) EMPTY).length
          < UInt32.size by rw [List.length_replicate]; exact hnowrap)
      iexact Hctrl
    · rw [← hctrl]
      iapply (slotsBefore_replicate_none memId buckets lo slotBytes hslots)
      iexact Hslots

end Memory

end Wasm.RustStd.HashMap.Table
