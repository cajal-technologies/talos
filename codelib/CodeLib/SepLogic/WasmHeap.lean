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
  | 4 => ⟨constOF (HeapView UInt32 (Agree (LeibnizO (Option UInt8))) WasmHeapMap), by infer_instance⟩
  | 5 => ⟨constOF (HeapView UInt32 (Agree (LeibnizO GName)) WasmHeapMap), by infer_instance⟩
  | 6 => ⟨constOF MetaUR, by infer_instance⟩
  | _ => ⟨constOF Unit, by infer_instance⟩
-- Wire genHeapPreS (following HeapLang's instHeapLangGS_HeapLangS)
instance instWasmHeapPreS : genHeapPreS UInt32 (Option UInt8) WasmHeapGF WasmHeapMap where
  heap := by constructor; exists 4
  metaInfo := by constructor; exists 5
  metaData := by exists 6
-- The full genHeap instance with ghost names
class WasmHeapGS extends genHeapGS UInt32 (Option UInt8) WasmHeapGF WasmHeapMap
-- Now test: does the points-to notation work?
section Test
variable [inst : WasmHeapGS]
-- This is the payoff: addr ↦ byte for Wasm memory
#check (pointsTo (L := UInt32) (V := Option UInt8) (GF := WasmHeapGF) (H := WasmHeapMap))
-- Notation for Wasm points-to
notation:50 addr:50 " ↦w " v:50 => pointsTo (L := UInt32) (V := Option UInt8)
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
-- arrayAt splits across ++ : ownership of a concatenation is
-- ownership of both halves (merge_sort_into splits data at mid)
theorem arrayAt_append (ptr : UInt32) (xs ys : List UInt32) :
    arrayAt ptr (xs ++ ys) ⊣⊢
    arrayAt ptr xs ∗ arrayAt (ptr + 4 * UInt32.ofNat xs.length) ys := by
  induction xs generalizing ptr with
  | nil => simp [arrayAt]; exact BI.emp_sep.symm
  | cons x rest ih =>
    simp only [List.cons_append, List.length_cons, arrayAt]
    rw [show ptr + 4 * UInt32.ofNat (rest.length + 1) = (ptr + 4) + 4 * UInt32.ofNat rest.length from by
      symm
      rw [UInt32.ofNat_add, show UInt32.ofNat 1 = 1 from rfl, UInt32.mul_add, UInt32.mul_one]
      rw [UInt32.add_assoc ptr 4, UInt32.add_comm 4, ← UInt32.add_assoc]]
    exact (BI.sep_congr_right (ih (ptr + 4))).trans BI.sep_assoc.symm

-- extract element k: whole-array ownership gives the single
-- cell plus everything else (merge reads left[i], right[j])
theorem arrayAt_get (ptr : UInt32) (xs : List UInt32) (k : Nat)
    (hk : k < xs.length) :
    arrayAt ptr xs ⊢
    pointsTo_u32 (ptr + 4 * UInt32.ofNat k) xs[k] ∗
    (pointsTo_u32 (ptr + 4 * UInt32.ofNat k) xs[k] -∗ arrayAt ptr xs) := by
  induction xs generalizing ptr k with
  | nil => simp at hk
  | cons x rest ih =>
    cases k with
    | zero =>
      simp only [List.getElem_cons_zero, arrayAt]
      rw [show ptr + 4 * UInt32.ofNat 0 = ptr from by simp [UInt32.ofNat]]
      exact BI.sep_mono .rfl (BI.wand_intro BI.sep_symm)
    | succ k' =>
      simp only [List.length_cons] at hk
      have hk' : k' < rest.length := by omega
      simp only [List.getElem_cons_succ, arrayAt]
      rw [show ptr + 4 * UInt32.ofNat (k' + 1) = (ptr + 4) + 4 * UInt32.ofNat k' from by
        symm
        rw [UInt32.ofNat_add, show UInt32.ofNat 1 = 1 from rfl, UInt32.mul_add, UInt32.mul_one]
        rw [UInt32.add_assoc ptr 4, UInt32.add_comm 4, ← UInt32.add_assoc]]
      exact (BI.sep_mono_right (ih (ptr + 4) k' hk')).trans
        (BI.sep_left_comm.mp.trans (BI.sep_mono_right
          (BI.wand_intro (BI.sep_assoc.mp.trans (BI.sep_mono_right BI.wand_elim_left)))))

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
      rw [show ptr + 4 * UInt32.ofNat (k' + 1) = (ptr + 4) + 4 * UInt32.ofNat k' from by
        symm
        rw [UInt32.ofNat_add, show UInt32.ofNat 1 = 1 from rfl, UInt32.mul_add, UInt32.mul_one]
        rw [UInt32.add_assoc ptr 4, UInt32.add_comm 4, ← UInt32.add_assoc]]
      exact (BI.sep_mono_right (ih (ptr + 4) k' hk')).trans
        (BI.sep_left_comm.mp.trans (BI.sep_mono_right
          (BI.wand_intro (BI.sep_assoc.mp.trans (BI.sep_mono_right BI.wand_elim_left)))))
#check @pointsTo_u64
#check @pointsTo_u32
#check @arrayAt
end Test

section
open Wasm

/-- Exclusive ownership of function slot `idx` in module `m`:
    the function table entry equals `f`. Prop-level (not iProp) —
    for single-module proofs this suffices; the linking theorem's
    structure provides the ownership discipline. -/
def funcPointsTo (m : Module) (idx : Nat) (f : Function) : Prop :=
  m.funcs[idx]? = some f

notation m " ↦func[" idx "] " f => funcPointsTo m idx f

end

end Wasm.SepLogic