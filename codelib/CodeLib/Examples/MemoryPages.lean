import CodeLib.SepLogic.WasmHeap

/-! # Migrating page updates

These examples check the legacy update and the exact update followed by freezing.
-/

namespace Wasm.Examples.MemoryPages

open Iris Wasm.SepLogic

/-- A full-authority caller can still grow using a monotonicity proof. -/
example [WasmMemoryPagesGS α] [WasmMemoryPagesLegacy α]
    (old newPages : Nat) (hmono : old ≤ newPages) :
    memoryPagesAuth (α := α) old ==∗ memoryPagesAuth newPages ∗ memoryPagesOwn newPages :=
  memoryPagesAuth_update old newPages hmono

/-- The exact-mode client can grow and then freeze its updated count. -/
example [gs : WasmMemoryPagesGS α] (hhalf : gs.stateFrac = (1 : Qp).half)
    (old newPages : Nat) (hmono : old ≤ newPages) :
    memoryPagesAuth (α := α) old ∗ memoryPagesHalf old ==∗
      memoryPagesAuth newPages ∗ memoryPagesFrozen newPages ∗ memoryPagesOwn newPages := by
  fail_if_success have : WasmMemoryPagesLegacy α := inferInstance
  iintro Hboth
  imod memoryPagesAuth_update_exact old newPages hhalf hmono $$ Hboth with
    ⟨Hstate, Hhalf, Hsnapshot⟩
  imod memoryPagesHalf_freeze newPages $$ Hhalf with Hfrozen
  imodintro
  iframe Hstate Hfrozen Hsnapshot

end Wasm.Examples.MemoryPages
