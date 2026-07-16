import Iris
import Iris.BI.Lib.GenHeap
import Interpreter.Wasm
/-! # Wasm Memory as an Iris GenHeap
Instantiates iris-lean's GenHeap for Wasm byte-level memory.
Location = UInt32 (byte address), Value = Option UInt8 (byte).
-/
namespace Wasm.SepLogic
open Iris Std
abbrev WasmHeapMap := fun V => ExtTreeMap UInt32 V compare
abbrev WasmHeapGF : BundledGFunctors
  | 0 => ⟨InvMapF, by infer_instance⟩
  | 1 => ⟨constOF (DisjointLeibnizSet CoPset), by infer_instance⟩
  | 2 => ⟨constOF (DisjointLeibnizSet PosSet), by infer_instance⟩
  | 3 => ⟨Auth.AuthURF (constOF Credit), by infer_instance⟩
  | 4 => ⟨constOF (HeapView UInt32 (Agree (DiscreteO (Option UInt8))) WasmHeapMap), by infer_instance⟩
  | 5 => ⟨constOF (HeapView UInt32 (Agree (DiscreteO GName)) WasmHeapMap), by infer_instance⟩
  | 6 => ⟨constOF MetaUR, by infer_instance⟩
  | _ => ⟨constOF Unit, by infer_instance⟩
-- Wire genHeapPreS (following HeapLang's instHeapLangGS_HeapLangS)
instance instWasmHeapPreS : genHeapPreS UInt32 (Option UInt8) WasmHeapGF WasmHeapMap where
  heap := by constructor; exists 4
  metaInfo := by constructor; exists 5
  metaData := by exists 6
-- The full genHeap instance with ghost names
class WasmHeapGS extends genHeapGS UInt32 (Option UInt8) WasmHeapGF WasmHeapMap
/-! ## Points-to assertions

Byte-level `↦w` plus multi-byte and array derived forms.

**Address arithmetic caveat:** the multi-byte assertions below compute
their footprint with `UInt32` addition (`addr + 1`, …), which wraps
mod 2^32, whereas the interpreter's `Mem.read64`/`write64` index bytes at
`addr.toNat + k : Nat` with no wraparound. The two footprints agree only
when the access does not overflow the 32-bit address space (e.g.
`addr.toNat + 8 ≤ 2^32` for `pointsTo_u64`, and
`ptr.toNat + 4 * xs.length ≤ 2^32` for `arrayAt`). Any future rule
bridging these assertions to `Mem.read*/write*` must carry such a
no-overflow side condition — without it the ghost footprint at high
addresses wraps to low addresses and the bridge would be unprovable (or
unsound if forced). -/
section PointsTo
variable [inst : WasmHeapGS]
-- Notation for Wasm points-to (scoped: available inside this namespace
-- and via `open Wasm.SepLogic`, without leaking through the CodeLib umbrella)
scoped notation:50 addr:50 " ↦w " v:50 => pointsTo (L := UInt32) (V := Option UInt8)
    (GF := WasmHeapGF) (H := WasmHeapMap) addr (DFrac.own 1) (some v)
-- Multi-byte: u64 as 8 consecutive owned bytes (little-endian)
def pointsTo_u64 (addr : UInt32) (v : UInt64) : IProp WasmHeapGF :=
  let byte (n : Nat) : UInt8 := ⟨(v.toNat / (256 ^ n)) % 256, by omega⟩
  iprop%
    (addr ↦w byte 0) ∗ ((addr + 1) ↦w byte 1) ∗
    ((addr + 2) ↦w byte 2) ∗ ((addr + 3) ↦w byte 3) ∗
    ((addr + 4) ↦w byte 4) ∗ ((addr + 5) ↦w byte 5) ∗
    ((addr + 6) ↦w byte 6) ∗ ((addr + 7) ↦w byte 7)
-- Multi-byte: u32 as 4 consecutive owned bytes (little-endian)
def pointsTo_u32 (addr : UInt32) (v : UInt32) : IProp WasmHeapGF :=
  let byte (n : Nat) : UInt8 := ⟨(v.toNat / (256 ^ n)) % 256, by omega⟩
  iprop%
    (addr ↦w byte 0) ∗ ((addr + 1) ↦w byte 1) ∗
    ((addr + 2) ↦w byte 2) ∗ ((addr + 3) ↦w byte 3)
-- Array ownership: n consecutive u32 elements at ptr
-- arrayAt ptr [x₀, x₁, ..., xₙ₋₁] = pointsTo_u32 ptr x₀ ∗ pointsTo_u32 (ptr+4) x₁ ∗ ...
def arrayAt (ptr : UInt32) (xs : List UInt32) : IProp WasmHeapGF :=
  match xs with
  | [] => iprop% emp
  | x :: rest => iprop% (pointsTo_u32 ptr x) ∗ (arrayAt (ptr + 4) rest)
-- element-offset arithmetic shared by the arrayAt lemmas: stepping past
-- the head element shifts the base by one 4-byte stride
omit inst in
private theorem elem_offset_succ (ptr : UInt32) (k : Nat) :
    ptr + 4 * UInt32.ofNat (k + 1) = (ptr + 4) + 4 * UInt32.ofNat k := by
  symm
  rw [UInt32.ofNat_add, show UInt32.ofNat 1 = 1 from rfl, UInt32.mul_add, UInt32.mul_one]
  rw [UInt32.add_assoc ptr 4, UInt32.add_comm 4, ← UInt32.add_assoc]

-- arrayAt splits across ++ : ownership of a concatenation is
-- ownership of both halves (merge_sort_into splits data at mid)
theorem arrayAt_append (ptr : UInt32) (xs ys : List UInt32) :
    arrayAt ptr (xs ++ ys) ⊣⊢
    arrayAt ptr xs ∗ arrayAt (ptr + 4 * UInt32.ofNat xs.length) ys := by
  induction xs generalizing ptr with
  | nil => simp [arrayAt]; exact BI.emp_sep.symm
  | cons x rest ih =>
    simp only [List.cons_append, List.length_cons, arrayAt]
    rw [elem_offset_succ]
    exact (BI.sep_congr_right (ih (ptr + 4))).trans BI.sep_assoc.symm

-- update element k: give back a cell with a NEW value,
-- own the updated array (merge writes out[k] = v)
theorem arrayAt_set (ptr : UInt32) (xs : List UInt32) (k : Nat)
    (v : UInt32) (hk : k < xs.length) :
    arrayAt ptr xs ⊢
    pointsTo_u32 (ptr + 4 * UInt32.ofNat k) xs[k] ∗
    (pointsTo_u32 (ptr + 4 * UInt32.ofNat k) v -∗ arrayAt ptr (xs.set k v)) := by
  induction xs generalizing ptr k with
  | nil => simp at hk
  | cons x rest ih =>
    cases k with
    | zero =>
      simp only [List.getElem_cons_zero, List.set_cons_zero, arrayAt]
      rw [show ptr + 4 * UInt32.ofNat 0 = ptr from by simp [UInt32.ofNat]]
      exact BI.sep_mono .rfl (BI.wand_intro BI.sep_symm)
    | succ k' =>
      simp only [List.length_cons] at hk
      have hk' : k' < rest.length := by omega
      simp only [List.getElem_cons_succ, List.set_cons_succ, arrayAt]
      rw [elem_offset_succ]
      exact (BI.sep_mono_right (ih (ptr + 4) k' hk')).trans
        (BI.sep_left_comm.mp.trans (BI.sep_mono_right
          (BI.wand_intro (BI.sep_assoc.mp.trans (BI.sep_mono_right BI.wand_elim_left)))))

-- extract element k: whole-array ownership gives the single
-- cell plus everything else (merge reads left[i], right[j]).
-- The special case of arrayAt_set that writes back the value just read.
theorem arrayAt_get (ptr : UInt32) (xs : List UInt32) (k : Nat)
    (hk : k < xs.length) :
    arrayAt ptr xs ⊢
    pointsTo_u32 (ptr + 4 * UInt32.ofNat k) xs[k] ∗
    (pointsTo_u32 (ptr + 4 * UInt32.ofNat k) xs[k] -∗ arrayAt ptr xs) := by
  have h := arrayAt_set ptr xs k xs[k] hk
  rwa [List.set_getElem_self] at h
end PointsTo
end Wasm.SepLogic
