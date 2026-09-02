import CodeLib.SepLogic.SmallStepState

/-!
# Shared pieces of the small-step ghost-state initialisation

Every adequacy entry point in `CodeLib.SepLogic.SmallStepAdequacy` opens with
the same preamble: allocate one ghost resource per `WasmHeapGF` slot, then
bundle the results into a `WasmSmallStepGS`.  The two parts of that preamble
that are *literally* the same everywhere live here.

* `GhostSlot.*` names the `WasmHeapGF` slot each ghost map or element lives in.
  Previously every entry point repeated the raw slot numbers, and several
  functors occur at more than one slot (`Auth.AuthRF (OptionOF (Excl.ExclOF
  (constOF (DiscreteO Nat))))` sits at both 14 and 18), so a transposed number
  still type-checks and only shows up as a mysteriously failing proof.  Each
  number is now written exactly once.
* `smallStepGS` performs the final field-by-field assembly of the fifteen
  component ghost states, which is byte-identical at every site.

The parts that genuinely differ between entry points — which maps start empty
and which start populated, whether the runtime module and host env maps get an
entry for the entry instance, whether the exclusive fragments are kept or
cleared — stay at their call sites.
-/

namespace Wasm.SmallStep

open Iris Iris.ProgramLogic Std
open Wasm.SepLogic

variable {α : Type}

namespace GhostSlot

/-- Ghost map of Wasm globals: `WasmHeapGF` slot 7. -/
@[reducible] def globalMap :
    GhostMapG (WasmHeapGF α) GlobalKey Value WasmGlobalMap := by
  constructor
  exists 7

/-- Ghost map of instantiated runtime modules: `WasmHeapGF` slot 8. -/
@[reducible] def runtimeModuleMap :
    GhostMapG (WasmHeapGF α) Nat Module WasmRuntimeModuleMap := by
  constructor
  exists 8

/-- Ghost map of data segments: `WasmHeapGF` slot 9. -/
@[reducible] def dataSegmentMap :
    GhostMapG (WasmHeapGF α) DataSegmentKey (Option (List UInt8))
      WasmDataSegmentMap := by
  constructor
  exists 9

/-- Ghost map of tables: `WasmHeapGF` slot 10. -/
@[reducible] def tableMap :
    GhostMapG (WasmHeapGF α) TableKey TableInst WasmTableMap := by
  constructor
  exists 10

/-- Ghost map of element segments: `WasmHeapGF` slot 11. -/
@[reducible] def elementSegmentMap :
    GhostMapG (WasmHeapGF α) ElementSegmentKey (Option (List (Option Nat)))
      WasmElementSegmentMap := by
  constructor
  exists 11

/-- Ghost map of host environments: `WasmHeapGF` slot 12. -/
@[reducible] def hostEnvMap :
    GhostMapG (WasmHeapGF α) Nat (HostEnv α) WasmHostEnvMap := by
  constructor
  exists 12

/-- Exclusive-auth element holding the host state: `WasmHeapGF` slot 13. -/
@[reducible] def hostStateElem :
    ElemG (WasmHeapGF α)
      (Auth.AuthRF (OptionOF (Excl.ExclOF (constOF (DiscreteO α))))) := by
  exists 13

/-- Exclusive-auth element holding the current instance id: `WasmHeapGF` slot
14.  Slot 18 carries the same functor, so this number must not be guessed. -/
@[reducible] def instanceElem :
    ElemG (WasmHeapGF α)
      (Auth.AuthRF (OptionOF (Excl.ExclOF (constOF (DiscreteO Nat))))) := by
  exists 14

/-- Agreement element holding the runtime instance table: `WasmHeapGF` slot
15. -/
@[reducible] def runtimeInstancesElem :
    ElemG (WasmHeapGF α)
      (constOF (Agree (DiscreteO (Array (ModuleInstance α))))) := by
  exists 15

/-- Ghost map of in-flight exception payloads: `WasmHeapGF` slot 16. -/
@[reducible] def exceptionMap :
    GhostMapG (WasmHeapGF α) Nat (Nat × List Value) WasmExceptionMap := by
  constructor
  exists 16

/-- Agreement element holding the entry instance's tag table: `WasmHeapGF`
slot 17. -/
@[reducible] def tagTableElem :
    ElemG (WasmHeapGF α) (constOF (Agree (DiscreteO (List Nat)))) := by
  exists 17

end GhostSlot

/-- Assemble the small-step ghost state from the invariant ghost state and the
fourteen Wasm component ghost states, the latter taken from the ambient
instance context (every one of them is a local instance at the point where an
adequacy proof builds its `WasmSmallStepGS`).  Every adequacy entry point
allocates the same components and wires them up the same way; the wiring is
written once here. -/
@[reducible] def smallStepGS (hlc : HasLC)
    (invGS : InvGS_gen hlc (WasmHeapGF α))
    [wasmHeapGS : WasmHeapGS α]
    [heapDomainGS : WasmHeapDomainGS α]
    [memoryPagesGS : WasmMemoryPagesGS α]
    [wasmGlobalGS : WasmGlobalGS α]
    [wasmDataSegmentGS : WasmDataSegmentGS α]
    [wasmTableGS : WasmTableGS α]
    [wasmElementSegmentGS : WasmElementSegmentGS α]
    [wasmExceptionGS : WasmExceptionGS α]
    [tagTableGS : WasmTagTableGS α]
    [runtimeGS : WasmRuntimeModuleGS α]
    [hostEnvGS : WasmHostEnvGS α]
    [hostStateGS : WasmHostStateGS α]
    [instanceGS : WasmInstanceGS α]
    [runtimeInstancesGS : WasmRuntimeInstancesGS α] :
    WasmSmallStepGS hlc α :=
  { toInvGS_gen := invGS
    toWasmHeapGS := wasmHeapGS
    heapDomain := heapDomainGS
    memoryPages := memoryPagesGS
    global := wasmGlobalGS
    dataSegment := wasmDataSegmentGS
    table := wasmTableGS
    elementSegment := wasmElementSegmentGS
    exception := wasmExceptionGS
    tagTable := tagTableGS
    runtime := runtimeGS
    hostEnv := hostEnvGS
    hostState := hostStateGS
    instanceGS := instanceGS
    runtimeInstances := runtimeInstancesGS }

end Wasm.SmallStep
