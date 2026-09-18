import CodeLib.RustStd.HashMap.TableMem
import CodeLib.RustStd.HashMap.TableRefinement

/-!
# Writing one control byte

`Table.ByteSlice_ctrlAt` in `CodeLib.RustStd.HashMap.TableMem` focuses the
control byte of bucket `i` inside the byte slice of a table.  It never puts
a new byte back.  Both bodies that change a table store control bytes: func
18 at WAT lines 4457 to 4476 and func 17 at WAT lines 4049 to 4067 of
`programs/rust/build/rust_hash_map/program.wat`.  A body proof needs the
other direction.

`ByteSlice_set` is that direction.  The byte slice of a list with a new
byte at `i` splits into the same prefix, the new byte, and the same
suffix.  With `ByteSlice_ctrlAt` it turns one `i32.store8` into one
`List.set`.

`Table.setCtrl` writes two positions, `i` and `index2 t.buckets i`, and the
compiled code writes the same two.  `index2_eq_of_le` says which two they
are.  `setCtrl_ctrl_of_le` and `setCtrl_ctrl_of_lt` name the two cases as
list equations, so a memory proof applies `ByteSlice_set` once when the
bucket is at or above 8 and twice when it is below 8.
-/

namespace Wasm.RustStd.HashMap.Table

open Wasm.SepLogic Wasm.SepLogic.Slices Iris Std

variable {K V : Type}

/-! ## The memory step -/

section Memory

variable {α : Type} [WasmHeapGS α]

/-- Put a new byte at `i` of an owned byte range.  This is the write form
of `ByteSlice_window` at one byte, and the converse of `ByteSlice_ctrlAt`. -/
theorem ByteSlice_set (memId : Nat) (ptr : UInt32) (bytes : List UInt8)
    {i : Nat} (hi : i < bytes.length) (c : UInt8) :
    Slices.ByteSlice (α := α) memId ptr (bytes.set i c) ⊣⊢
      iprop(Slices.ByteSlice memId ptr (bytes.take i) ∗
        (⌜(ptr + UInt32.ofNat i).toNat + 1 < UInt32.size⌝ ∗
          (⟨memId, ptr + UInt32.ofNat i⟩ ↦w c)) ∗
        Slices.ByteSlice memId (ptr + UInt32.ofNat (i + 1))
          (bytes.drop (i + 1))) := by
  have hset : i < (bytes.set i c).length := by
    rw [List.length_set]
    exact hi
  refine (ByteSlice_window memId ptr (bytes.set i c) i 1 (by omega)).trans ?_
  rw [List.take_set_of_le (Nat.le_refl i),
    List.drop_set_of_lt (Nat.lt_succ_self i)]
  refine BI.sep_congr .rfl (BI.sep_congr ?_ .rfl)
  have hbyte : ((bytes.set i c).drop i).take 1 = [c] := by
    rw [List.drop_eq_getElem_cons hset, List.take_succ_cons, List.take_zero,
      List.getElem_set_self]
  rw [hbyte]
  exact ByteSlice_singleton memId _ _

end Memory

/-! ## The two positions of `setCtrl` -/

/-- At a bucket at or above 8 the mirror is the bucket itself, so `setCtrl`
changes one byte. -/
theorem setCtrl_ctrl_of_le (t : Table K V) {i : Nat} (hb : t.buckets ∣ 2 ^ 32)
    (h8 : 8 ≤ t.buckets) (hi : i < t.buckets) (hi8 : 8 ≤ i) (c : UInt8) :
    (setCtrl t i c).ctrl = t.ctrl.set i c := by
  unfold setCtrl
  rw [index2_eq_of_le hb h8 hi, if_neg (by omega), List.set_set]

/-- Below bucket 8 the mirror is `i + buckets`, at the tail of the control
bytes, so `setCtrl` changes two bytes. -/
theorem setCtrl_ctrl_of_lt (t : Table K V) {i : Nat} (hb : t.buckets ∣ 2 ^ 32)
    (h8 : 8 ≤ t.buckets) (hi : i < 8) (c : UInt8) :
    (setCtrl t i c).ctrl = (t.ctrl.set i c).set (i + t.buckets) c := by
  unfold setCtrl
  rw [index2_eq_of_le hb h8 (by omega), if_pos hi]

/-- `setCtrl` keeps the length of the control bytes. -/
theorem length_setCtrl_ctrl (t : Table K V) (i : Nat) (c : UInt8) :
    (setCtrl t i c).ctrl.length = t.ctrl.length := by
  unfold setCtrl
  simp

end Wasm.RustStd.HashMap.Table
