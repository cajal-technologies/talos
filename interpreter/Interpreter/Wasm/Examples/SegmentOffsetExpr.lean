import Interpreter.Wasm.Decoder.Wat
import Interpreter.Wasm.SmallStep

/-! ## Example: const-expression data/element segment offsets

    Active segment offsets may use constant expressions such as
    `global.get`. Instantiation must evaluate those expressions before the
    small-step machine observes memory and table contents.
-/

namespace Wasm
open SmallStep
namespace SegmentOffsetExpr

def segmentOffsetWat : String := "
(module
  (global $o i32 (i32.const 4))
  (global $t i32 (i32.const 2))
  (memory 1)
  (data (offset (global.get $o)) \"ABCD\")
  (table 4 funcref)
  (elem (offset (global.get $t)) $f42)
  (type $ri (func (result i32)))
  (func $f42 (type $ri) (i32.const 42))
  (func $readByte4 (export \"readByte4\") (result i32)
    (i32.load8_u (i32.const 4)))
  (func $callAt2 (export \"callAt2\") (result i32)
    (call_indirect (type $ri) (i32.const 2))))
"

private def decoded : Wasm.Module :=
  match Wasm.Decoder.Wat.decode segmentOffsetWat with
  | .ok module => module
  | .error _ => default

theorem decoded_segments_keep_offsetExpr :
    ((decoded.memory.bind (·.data[0]?)).map (·.offsetExpr.isEmpty)).getD true = false
    ∧ (decoded.elements[0]?.map (·.offsetExpr.isEmpty)).getD true = false := by
  constructor <;> native_decide

private def store0 : Store Unit :=
  let module := decoded
  module.runActiveSegments 64
    (module.runConstGlobals 64 (module.initialStore (α := Unit)) {}) {}

def segmentMachineStore : MachineStore Unit :=
  { runtime := { module := decoded, host := {} }
    wasm := store0 }

private def functionConfig (index : Nat) : Config Unit :=
  { expr := .running
      { locals := {}
        code := decoded.funcs[index]!.body
        resultArity := decoded.funcs[index]!.results.length
        callerRemainder := [] }
    store := segmentMachineStore }

def readByte4Config : Config Unit := functionConfig 1
def callAt2Config : Config Unit := functionConfig 2

private def readByte4StoreOK : RunnerResult Unit → Bool
  | .success _ store =>
      store.wasm.mem.read8 4 == 65 &&
      store.wasm.mem.read8 0 == 0
  | _ => false

private theorem readByte4_store_ok :
    readByte4StoreOK (runSteps 3 readByte4Config).result = true := by
  native_decide

theorem readByte4_returns_65 :
    (runSteps 3 readByte4Config).result.values? =
      some [.i32 65] := by
  native_decide

theorem readByte4_spec :
    TerminatesWith readByte4Config (fun values store =>
      values = [.i32 65] ∧
      store.wasm.mem.read8 4 = 65 ∧
      store.wasm.mem.read8 0 = 0) := by
  have hcheck := readByte4_store_ok
  have hvalues := readByte4_returns_65
  generalize hr : (runSteps 3 readByte4Config).result = result at hcheck
  rw [hr] at hvalues
  cases result with
  | success values store =>
    apply runSteps_success_terminates hr
    have hv : values = [.i32 65] := by
      simpa [RunnerResult.values?] using hvalues
    have hs :
        store.wasm.mem.read8 4 = 65 ∧
        store.wasm.mem.read8 0 = 0 := by
      simpa [readByte4StoreOK] using hcheck
    exact ⟨hv, hs⟩
  | trapped | outOfFuel | internalError =>
    simp [RunnerResult.values?] at hvalues

theorem readByte4_partial :
    PartiallyMeets readByte4Config (fun values store =>
      values = [.i32 65] ∧ store.wasm.mem.read8 4 = 65) := by
  have hcheck := readByte4_store_ok
  have hvalues := readByte4_returns_65
  generalize hr : (runSteps 3 readByte4Config).result = result at hcheck
  rw [hr] at hvalues
  cases result with
  | success values store =>
    apply runSteps_success_partiallyMeets hr
    constructor
    · simpa [RunnerResult.values?] using hvalues
    · have hs :
          store.wasm.mem.read8 4 = 65 ∧
          store.wasm.mem.read8 0 = 0 := by
        simpa [readByte4StoreOK] using hcheck
      exact hs.1
  | trapped | outOfFuel | internalError =>
    simp [RunnerResult.values?] at hvalues

theorem callAt2_returns_42 :
    (runSteps 16 callAt2Config).result.values? =
      some [.i32 42] := by
  native_decide

theorem callAt2_spec :
    TerminatesWith callAt2Config (fun values _ =>
      values = [.i32 42]) := by
  have hvalues := callAt2_returns_42
  generalize hr : (runSteps 16 callAt2Config).result = result
  rw [hr] at hvalues
  cases result with
  | success values store =>
    apply runSteps_success_terminates hr
    simpa [RunnerResult.values?] using hvalues
  | trapped | outOfFuel | internalError =>
    simp [RunnerResult.values?] at hvalues

theorem callAt2_partial :
    PartiallyMeets callAt2Config (fun values _ =>
      values = [.i32 42]) := by
  have hvalues := callAt2_returns_42
  generalize hr : (runSteps 16 callAt2Config).result = result
  rw [hr] at hvalues
  cases result with
  | success values store =>
    apply runSteps_success_partiallyMeets hr
    simpa [RunnerResult.values?] using hvalues
  | trapped | outOfFuel | internalError =>
    simp [RunnerResult.values?] at hvalues

theorem byte0_still_zero : store0.mem.read8 0 = 0 := by
  native_decide

end SegmentOffsetExpr
end Wasm
