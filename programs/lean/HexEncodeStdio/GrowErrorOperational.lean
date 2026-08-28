import HexEncodeStdio.VectorGrowOperational

namespace Submission.HexDecodeStdio

open Wasm Project.HexStdio Project.HexStdio.Spec
open Wasm.SmallStep

def growResultErrStore (store : MachineStore Universal.State)
    (out : UInt32) : MachineStore Universal.State :=
  let mem := (store.wasm.mem.write32 (out + 4) 0).write32 out 1
  { store with wasm := { store.wasm with mem := mem } }

/-- A size with the signed high bit set is rejected by the RawVec wrapper;
it returns its error record without invoking the allocator. -/
theorem grow_result_negative
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (out oldPtr oldSize newSize : UInt32)
    (hmod : store.runtime.currentModule = «module»)
    (hneg : newSize.toInt32 < UInt32.toInt32 0)
    (hout4 : out.toNat + 4 + 4 ≤ store.wasm.mem.pages * 65536)
    (hout0 : out.toNat + 4 ≤ store.wasm.mem.pages * 65536) :
    Reaches
      ⟨.running
        ⟨⟨outerParams, outerLocalValues,
            [.i32 newSize, .i32 oldSize, .i32 oldPtr, .i32 out] ++ stack⟩,
          [.call 7] ++ code, arity, remainder, controls, calls⟩,
        store⟩
      (growResultFinal (growResultErrStore store out)
        outerParams outerLocalValues stack code arity remainder controls calls) := by
  have hnot : ¬7 < store.runtime.currentModule.imports.length := by
    rw [hmod]; decide
  have hfn : store.runtime.currentModule.funcs[
      7 - store.runtime.currentModule.imports.length]? = some func4Def := by
    rw [hmod]; rfl
  apply Reaches.prepend (Step.call hnot hfn)
  simp [func4Def, Function.toLocals, Function.numParams,
    func4_decomposition, growResultBody]
  apply Reaches.prepend Step.block
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend
    (Step.ltS (result := 1) (Eq.symm (if_pos hneg)))
  apply Reaches.prepend (Step.brIf (condition := 1) (by decide) rfl)
  simp [growResultErrorTail, growResultOuterControl]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.store32 (by simpa using hout4))
  rw [setMemory_eq]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.store32 (by
    simpa [setMemory_eq] using hout0))
  rw [setMemory_eq]
  apply Reaches.prepend (Step.returnFromCallFallthrough rfl)
  simp [growResultFinal, growResultErrStore, resumeCaller]
  exact ⟨[], .refl _⟩

end Submission.HexDecodeStdio
