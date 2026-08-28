import HexEncodeStdio.ReadToEndTransition

namespace Project.HexEncodeStdio

open Wasm Project.HexStdio Project.HexStdio.Spec
open Wasm.SmallStep

/-- If the bump allocator's signed-address guard fails during a
`read_to_end` reallocation, the generated vector-growth wrapper reaches the
distinguished OOM host trap. -/
theorem read_to_end_grow_signed_oom
    (input consumed remaining : List UInt8)
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (out frame chunk capacity data length filled scratch9 status bump : UInt32)
    (hinv : ReadToEndInv input consumed remaining store capacity data length bump)
    (hnegative :
      (allocatorFinish (readToEndNewCapacity capacity) 1 bump).toInt32 <
        UInt32.toInt32 0) :
    TrapsWith
      (readToEndGrowCallConfig store outerParams outerLocalValues stack code
        arity remainder controls calls out frame chunk capacity data length
        filled scratch9 status)
      (.host OOM.trapMessage)
      (fun final => final.wasm.host.oom.raised = true) := by
  let params : List Value := [.i32 out]
  let localValues : List Value :=
    [.i32 frame, .i32 chunk, .i32 capacity, .i32 length, .i32 filled,
      .i32 data, .i32 (readToEndNewCapacity capacity),
      .i32 (capacity <<< 1), .i32 scratch9, .i32 0, .i32 status,
      .i32 0, .i32 0, .i64 0]
  let growthCalls : List CallFrame :=
    { locals := ⟨outerParams, outerLocalValues, stack⟩
      continuation := code
      resultArity := arity
      callerRemainder := remainder
      control := controls
      returningInstance := store.runtime.entry } :: calls
  let reallocCalls : List CallFrame :=
    { locals := ⟨params, localValues, []⟩
      continuation := readToEndGrowthCheck.drop 23
      resultArity := 0
      callerRemainder := []
      control := readToEndGrowthControls
      returningInstance := store.runtime.entry } :: growthCalls
  have hprefix := grow_result_realloc_prefix store params localValues []
    (readToEndGrowthCheck.drop 23) 0 [] readToEndGrowthControls growthCalls
    (frame + 16) capacity data (readToEndNewCapacity capacity)
    hinv.runtime_module
    (readToEndNewCapacity_nonnegative capacity hinv.capacity_small)
    (by
      intro hz
      have hp := hinv.capacity_pos
      rw [hz] at hp
      simp at hp)
  have htrap := reallocator_signed_limit_traps store
    ([.i32 (frame + 16), .i32 capacity, .i32 data,
      .i32 (readToEndNewCapacity capacity)]) [] []
    [.localSet 1, .br 1] 0 []
    [growResultDispatchControl, growResultAllocateControl,
      growResultOuterControl]
    reallocCalls data capacity 1 (readToEndNewCapacity capacity) bump
    hinv.runtime_module hinv.runtime_host hinv.bump_eq
    (by have := hinv.pages_lower; omega)
    hinv.allocator_first_ok hinv.allocator_second_ok hnegative
  have hfull := TrapsWith.prependReaches hprefix (by
    simpa [growResultReallocatorCall, params, localValues, growthCalls,
      reallocCalls]
      using htrap)
  simpa [readToEndGrowCallConfig, params, localValues, growthCalls] using hfull

end Project.HexEncodeStdio
