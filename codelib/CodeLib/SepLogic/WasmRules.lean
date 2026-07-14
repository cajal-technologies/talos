import CodeLib.SepLogic.WasmHeap
import Interpreter.Wasm

/-! # Bridge: Talos Mem ↔ iris-lean GenHeap

The state interpretation maintains agreement between
the abstract GenHeap state σ and physical Mem.bytes.
We never build σ explicitly — GenHeap tracks it internally.
-/

namespace Wasm.SepLogic

open Iris Wasm Std

variable [inst : WasmHeapGS]

/-! Agreement: wherever GenHeap has an entry, Mem agrees. -/

def heapAgreesWithMem (σ : WasmHeapMap (Option UInt8)) (mem : Mem) : Prop :=
  ∀ (addr : UInt32) (v : UInt8),
    get? σ addr = some (some v) → mem.bytes addr.toNat = v

/-! Soundness of load:
If GenHeap says addr ↦ v and σ agrees with Mem,
then Mem.read8 addr = v. -/

theorem load_sound (σ : WasmHeapMap (Option UInt8)) (mem : Mem)
    (addr : UInt32) (v : UInt8)
    (h_agree : heapAgreesWithMem σ mem)
    (h_own : get? σ addr = some (some v)) :
    mem.bytes addr.toNat = v :=
  h_agree addr v h_own

/-! Soundness of store:
After Mem.write8, the updated σ still agrees with new Mem. -/

theorem store_sound (σ : WasmHeapMap (Option UInt8)) (mem : Mem)
    (addr : UInt32) (old_v new_v : UInt8)
    (h_agree : heapAgreesWithMem σ mem)
    (h_own : get? σ addr = some (some old_v)) :
    heapAgreesWithMem (insert σ addr (some new_v))
      ⟨mem.pages, fun n =>
        if n = addr.toNat then new_v else mem.bytes n⟩ := by
  intro addr' v' h_get
  by_cases h : addr' = addr
  · subst h
    simp [get?_insert_eq rfl] at h_get
    simp [h_get]
  · simp [get?_insert_ne (Ne.symm h)] at h_get
    have hne : addr'.toNat ≠ addr.toNat :=
      fun h' => h (UInt32.ext h')
    exact (if_neg hne).trans (h_agree addr' v' h_get)

end Wasm.SepLogic
