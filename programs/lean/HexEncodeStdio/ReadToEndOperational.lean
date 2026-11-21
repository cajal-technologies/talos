import HexEncodeStdio.ReadChunkFull
import HexDecodeStdio.ReadToEndSteps

namespace Project.HexEncodeStdio

open Wasm Project.HexStdio Project.HexStdio.Spec
open Wasm.SmallStep

/-! The `read_to_end` configurations and legs this file builds on live in
`HexDecodeStdio.ReadToEndProgram` and `HexDecodeStdio.ReadToEndSteps`, shared
with the decode proofs, and are re-exported under this namespace. -/
export Project.HexDecodeStdio (
  readToEndAfterFirstRead func7_first_read_split readToEndFrameStore
  readToEndFrameStore_runtime readToEndFrameStore_pages
  read_to_end_to_first_chunk readToEndFinishedStore readToEndOuterBody
  readToEndMiddleBody readToEndInnerBody readToEndLoopBody
  readToEndIterationOuter readToEndIteration1 readToEndIteration2
  readToEndIteration3 readToEndIteration4 readToEndIteration5
  readToEndIteration6 readToEndGrowthCheck readToEndLoopControls
  readToEndDirectControls readToEndLoopConfig readToEndDirectConfig
  readToEndTarget readToEndRemaining readToEndDestination readToEndFillStore
  readToEndAfterAdapterConfig readToEndAfterReadSuccessConfig
  readToEndLengthStore readToEndReturnConfig readToEndContinuedLoopConfig
  readToEndContinuedDirectConfig readToEndContinuedAfterAdapterConfig
  readToEndNewCapacity readToEndGrowthControls readToEndGrowCallConfig
  readToEndAfterGrowConfig readToEndGrownDirectConfig
  readToEndGrownAfterAdapterConfig readToEndGrowFinishedStore
  read_to_end_after_first_nonempty_to_loop read_to_end_loop_skip_growth
  read_to_end_continued_loop_skip_growth read_to_end_loop_to_grow
  read_to_end_continued_loop_to_grow read_to_end_after_grow_success
  read_to_end_direct_read read_to_end_continued_direct_read
  read_to_end_continued_direct_read_no_fill read_to_end_grown_direct_read
  read_to_end_after_adapter_success
  read_to_end_continued_after_adapter_success
  read_to_end_grown_after_adapter_success read_to_end_after_read_eof
  read_to_end_after_read_spare_lt read_to_end_after_read_partial
  read_to_end_after_read_full_double read_to_end_after_read_full_saturate
  read_to_end_return read_to_end_after_first_eof)

/-- Invoke the byte-vector grow routine, preserving its normal result store
or propagating the distinguished allocator OOM trap. -/
theorem read_to_end_grow_call_outcome
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (out frame chunk capacity data length filled scratch9 status oldBump : UInt32)
    (hmod : store.runtime.currentModule = «module»)
    (henv : store.runtime.currentHost = Universal.envFor «module»)
    (hread : store.wasm.mem.read32 1053960 = oldBump)
    (hbound : 1053960 + 4 ≤ store.wasm.mem.pages * 65536)
    (hpages : store.wasm.mem.pages < 4294967295)
    (hnonneg : ¬ (readToEndNewCapacity capacity).toInt32 <
      UInt32.toInt32 0)
    (hptr : allocatorPtr oldBump 1 ≠ 0)
    (hout : (frame + 16).toNat + 12 ≤
      store.wasm.mem.pages * 65536)
    (hsource : data.toNat +
        (reallocatorCopyLen capacity
          (readToEndNewCapacity capacity)).toNat ≤
      store.wasm.mem.pages * 65536)
    (hdestination : allocatorRequiredPages
          (readToEndNewCapacity capacity) 1 oldBump ≤
        UInt32.ofNat store.wasm.mem.pages →
      (allocatorPtr oldBump 1).toNat +
          (reallocatorCopyLen capacity
            (readToEndNewCapacity capacity)).toNat ≤
        store.wasm.mem.pages * 65536)
    (hgrownBounds : ∀ memory previousPages,
      store.wasm.mem.grow
          (allocatorRequiredPages (readToEndNewCapacity capacity) 1 oldBump -
            UInt32.ofNat store.wasm.mem.pages)
          (store.wasm.memoryCap store.runtime.currentModule 0) =
            some (memory, previousPages) →
      data.toNat +
          (reallocatorCopyLen capacity
            (readToEndNewCapacity capacity)).toNat ≤
            memory.pages * 65536 ∧
      (allocatorPtr oldBump 1).toNat +
          (reallocatorCopyLen capacity
            (readToEndNewCapacity capacity)).toNat ≤
            memory.pages * 65536) :
    ReachesOrOOM
      (readToEndGrowCallConfig store outerParams outerLocalValues stack code
        arity remainder controls calls out frame chunk capacity data length
        filled scratch9 status)
      (fun final => ∃ allocStore,
        ByteGrowSuccess store capacity data (readToEndNewCapacity capacity)
            oldBump allocStore ∧
        final = readToEndAfterGrowConfig
          (growResultOkStore allocStore (frame + 16)
            (allocatorPtr oldBump 1) (readToEndNewCapacity capacity))
          outerParams outerLocalValues stack code arity remainder controls
          calls out frame chunk capacity data length filled scratch9 status) := by
  have hgrow := byte_grow_call_outcome store
    [.i32 out]
    [.i32 frame, .i32 chunk, .i32 capacity, .i32 length, .i32 filled,
      .i32 data, .i32 (readToEndNewCapacity capacity),
      .i32 (capacity <<< 1), .i32 scratch9, .i32 0, .i32 status,
      .i32 0, .i32 0, .i64 0]
    [] (readToEndGrowthCheck.drop 23) 0 [] readToEndGrowthControls
    ({ locals := ⟨outerParams, outerLocalValues, stack⟩
       continuation := code
       resultArity := arity
       callerRemainder := remainder
       control := controls
       returningInstance := store.runtime.entry } :: calls)
    (frame + 16) capacity data (readToEndNewCapacity capacity) oldBump
    hmod henv hread hbound hpages hnonneg hptr hout hsource hdestination
    hgrownBounds
  rcases hgrow with ⟨allocStore, hsuccess, hreach⟩ | htrap
  · left
    refine ⟨_, ?_, ⟨allocStore, hsuccess, rfl⟩⟩
    have hruntime :
        (growResultOkStore allocStore (frame + 16)
          (allocatorPtr oldBump 1)
          (readToEndNewCapacity capacity)).runtime = store.runtime := by
      calc
        _ = allocStore.runtime := rfl
        _ = store.runtime := hsuccess.runtime_eq
    simpa [readToEndGrowCallConfig, readToEndAfterGrowConfig,
      growResultFinal, hruntime] using hreach
  · exact Or.inr (by
      simpa [readToEndGrowCallConfig] using htrap)

end Project.HexEncodeStdio
