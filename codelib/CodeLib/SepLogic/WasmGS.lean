import CodeLib.SepLogic.SmallStepState

/-!
# Abstract ghost-functor instance context for the Wasm small-step layer

Mirrors the HeapLang pattern in iris-lean:
- `WasmGpreS` collects pre-allocation ElemG obligations (for adequacy).
- `WasmGS` is parameterised over any `BundledGFunctors` and carries the
  same ghost-state components as `WasmSmallStepGS`, each decomposed to its
  raw `ElemG` / `GhostMapG` obligation over the abstract `GF`.
- `instWasmGS_of_WasmSmallStepGS` bridges the concrete world: every existing
  user of `[WasmSmallStepGS hlc α]` automatically gets `[WasmGS hlc (WasmHeapGF α) α]`
  without any change to their code.
-/

namespace Wasm.SmallStep

open Iris Iris.ProgramLogic Std
open Wasm.SepLogic

/-! ## Pre-allocation obligations (for adequacy) -/

/-- Ghost-functor pre-S class for Wasm, mirroring `HeapLangGpreS`. -/
class WasmGpreS (hlc : outParam HasLC) (GF : BundledGFunctors) (α : outParam Type)
    extends InvGpreS GF where
  heap_pre : genHeapPreS MemoryKey (Option UInt8) GF WasmHeapMap

attribute [reducible, instance] WasmGpreS.heap_pre

/-- `WasmHeapGF α` satisfies `WasmGpreS` without any existing allocation.
Mirrors `instHeapLangGS_HeapLangS` in iris-lean. -/
instance instWasmGpreS_WasmHeapGF : WasmGpreS HasLC.hasLC (WasmHeapGF α) α where
  toWsatGpreS := by
    constructor
    · exists 0
    · exists 1
    · exists 2
  toLcGpreS := by
    constructor
    exists 3
  heap_pre := inferInstance

/-! ## Consumer: abstract ghost-map lookup over an abstract GF -/

/-- Abstract form of `WasmHeap.globalPointsTo_lookup`: the ghost-map lookup
lemma for Wasm globals, stated over any `GF` satisfying `[WasmGS hlc GF α]`.
Only `WasmGS.globalGS` (a `GhostMapG` obligation) and `WasmGS.globalName`
are used; there is no `stateInterp` or WP in sight.

The concrete lemma `WasmHeap.globalPointsTo_lookup` is the special case
`GF = WasmHeapGF α`, recovered via `instWasmGS_of_WasmSmallStepGS` below. -/
theorem globalPointsTo_lookup_gf [g : WasmGS hlc GF α]
    (σ : WasmGlobalMap Value) (key : GlobalKey) (value : Value) :
    (ghost_map_auth g.globalName (DFrac.own 1) σ : IProp GF) -∗
      ghost_map_elem g.globalName (DFrac.own 1) key value -∗
      iprop(⌜get? σ key = some value⌝) := by
  iapply ghost_map_lookup

/-- Specialising `globalPointsTo_lookup_gf` to `GF = WasmHeapGF α` via
`instWasmGS_of_WasmSmallStepGS` recovers `WasmHeap.globalPointsTo_lookup`.
`g.globalName` reduces definitionally to `gs.global.globalName`. -/
example [gs : WasmSmallStepGS hlc α]
    (σ : WasmGlobalMap Value) (key : GlobalKey) (value : Value) :
    (ghost_map_auth gs.global.globalName (DFrac.own 1) σ : IProp (WasmHeapGF α)) -∗
      ghost_map_elem gs.global.globalName (DFrac.own 1) key value -∗
      iprop(⌜get? σ key = some value⌝) :=
  globalPointsTo_lookup_gf σ key value

end Wasm.SmallStep
