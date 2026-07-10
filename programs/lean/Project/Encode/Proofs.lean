import Project.Encode.Program
import CodeLib
import Interpreter.Wasm.Wp.Call

/-!
# Proof of `EncodeSpec` (in progress)

General total-correctness proof of `encode`, built bottom-up like `gcd_u64`:
`encode` (func 8) → `encode::encode` (func 7) → `<[T]>::to_vec` (func 1) →
`ConvertVec::to_vec` (func 2, the `Vec` build + `memory.copy`) → `with_capacity_in`
(func 6) → … → `dlmalloc::malloc` (func 29).

Everything above `func6` is loop-free; the allocator (`func6` downward) has the
loops and is discharged separately. This file lands the loop-free layers.
-/

namespace Project.Encode.Proofs

open Wasm Project.Encode

/-- The exported `encode` (func 8) loads the `&str` fields `(dataPtr, len)` from
the argument struct at `argPtr` and forwards to the pure `encode::encode`
(func 7). So whatever post `func7` guarantees, the export guarantees — given the
struct is readable at `argPtr`. -/
theorem func8_of_func7 (env : HostEnv Unit) (st : Store Unit)
    (retPtr argPtr dataPtr len : UInt32) (P : Store Unit → Prop)
    (hdata : st.mem.read32 argPtr = dataPtr)
    (hlen : st.mem.read32 (argPtr + 4) = len)
    (hb : argPtr.toNat + 8 ≤ st.mem.pages * 65536)
    (hf7 : TerminatesWith env «module» 7 st [.i32 len, .i32 dataPtr, .i32 retPtr]
             (fun st' _ => P st')) :
    TerminatesWith env «module» 8 st [.i32 argPtr, .i32 retPtr] (fun st' _ => P st') := by
  apply TerminatesWith.of_wp_entry_for (f := func8Def) rfl
  unfold func8Def func8
  wp_run
  simp only [List.length_cons, List.length_nil, List.getElem?_cons_zero,
    List.getElem?_cons_succ, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, Nat.reduceAdd, Nat.reduceLT, reduceIte,
    show UInt32.toNat 0 = 0 from rfl, show UInt32.toNat 4 = 4 from rfl, Nat.add_zero]
  simp only [show argPtr + (0 : UInt32) = argPtr from by simp, hdata, hlen]
  rw [if_neg (by omega), if_neg (by omega)]
  apply wp_call_tw hf7
  intro st' vs hP
  wp_run
  exact hP

/-- `encode::encode` (func 7) is a thin pass-through to `<[T]>::to_vec` (func 1). -/
theorem func7_of_func1 (env : HostEnv Unit) (st : Store Unit)
    (sret dataPtr len : UInt32) (P : Store Unit → Prop)
    (hf1 : TerminatesWith env «module» 1 st [.i32 len, .i32 dataPtr, .i32 sret]
             (fun st' _ => P st')) :
    TerminatesWith env «module» 7 st [.i32 len, .i32 dataPtr, .i32 sret]
      (fun st' _ => P st') := by
  apply TerminatesWith.of_wp_entry_for (f := func7Def) rfl
  unfold func7Def func7
  wp_run
  apply wp_call_tw hf1
  intro st' vs hP
  wp_run
  exact hP

/-- `<[T]>::to_vec` (func 1) is a thin pass-through to `ConvertVec::to_vec` (func 2). -/
theorem func1_of_func2 (env : HostEnv Unit) (st : Store Unit)
    (sret dataPtr len : UInt32) (P : Store Unit → Prop)
    (hf2 : TerminatesWith env «module» 2 st [.i32 len, .i32 dataPtr, .i32 sret]
             (fun st' _ => P st')) :
    TerminatesWith env «module» 1 st [.i32 len, .i32 dataPtr, .i32 sret]
      (fun st' _ => P st') := by
  apply TerminatesWith.of_wp_entry_for (f := func1Def) rfl
  unfold func1Def func1
  wp_run
  apply wp_call_tw hf2
  intro st' vs hP
  wp_run
  exact hP

end Project.Encode.Proofs
