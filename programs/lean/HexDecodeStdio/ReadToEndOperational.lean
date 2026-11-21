import HexDecodeStdio.ReadChunkFull
import HexDecodeStdio.ReadToEnd
import HexDecodeStdio.ReadToEndSteps

namespace Project.HexDecodeStdio

open Wasm Project.HexStdio Project.HexStdio.Spec
open Wasm.SmallStep

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
  rcases hgrow with ⟨allocStore, _hfinish, hsuccess, hreach⟩ | htrap
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

end Project.HexDecodeStdio
