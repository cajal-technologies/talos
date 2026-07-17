import CodeLib.SepLogic.WasmHeap
import Interpreter.Wasm

/-! # Bridge: Talos Mem ↔ iris-lean GenHeap

Defines `heapAgreesWithMem` — the agreement predicate between an abstract
GenHeap state σ and physical memory — together with per-byte load/store
soundness lemmas for it, stated against the interpreter's `Mem.read8` /
`Mem.write8` API so they apply directly to interpreter-produced states.

**Status: not yet wired into the WP.** Nothing in `wp_wasm_F`,
`wasm_adequacy`, or `wasm_heap_adequacy` currently asserts this agreement:
the ghost heap threaded through `wp_wasm` is a free-floating resource, so a
`pointsTo` fact does not (yet) imply anything about `st.mem`. These
definitions are the intended ingredient for a future state interpretation
that maintains `heapAgreesWithMem σ st.mem` across steps; until that lands,
memory facts in program proofs must come from pure hypotheses about
`st.mem` (as the load/store rules in `Adequacy.lean` require).
-/

namespace Wasm.SepLogic

open Iris Wasm Std

/-! Agreement: wherever GenHeap has an entry, Mem agrees. -/

def heapAgreesWithMem (σ : WasmHeapMap (Option UInt8)) (mem : Mem) : Prop :=
  ∀ (addr : UInt32) (v : UInt8),
    get? σ addr = some (some v) → mem.read8 addr = v

/-! Soundness of load:
If GenHeap says addr ↦ v and σ agrees with Mem,
then Mem.read8 addr = v. -/

theorem load_sound (σ : WasmHeapMap (Option UInt8)) (mem : Mem)
    (addr : UInt32) (v : UInt8)
    (h_agree : heapAgreesWithMem σ mem)
    (h_own : get? σ addr = some (some v)) :
    mem.read8 addr = v :=
  h_agree addr v h_own

/-! Soundness of store:
After Mem.write8, the updated σ still agrees with the new Mem. -/

theorem store_sound (σ : WasmHeapMap (Option UInt8)) (mem : Mem)
    (addr : UInt32) (new_v : UInt8)
    (h_agree : heapAgreesWithMem σ mem) :
    heapAgreesWithMem (insert σ addr (some new_v)) (mem.write8 addr new_v) := by
  intro addr' v' h_get
  by_cases h : addr' = addr
  · subst h
    simp [get?_insert_eq rfl] at h_get
    simp [Mem.write8, Mem.read8, h_get]
  · simp [get?_insert_ne (Ne.symm h)] at h_get
    have hne : addr'.toNat ≠ addr.toNat :=
      fun h' => h (UInt32.ext h')
    simpa [Mem.write8, Mem.read8, hne] using h_agree addr' v' h_get

end Wasm.SepLogic
