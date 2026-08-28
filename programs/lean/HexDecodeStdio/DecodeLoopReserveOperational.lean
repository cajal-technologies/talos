import HexDecodeStdio.DecodeSecondPairCompose

namespace Submission.HexDecodeStdio

open Wasm Project.HexStdio Project.HexStdio.Spec
open Wasm.SmallStep

def decodeCoreLoopReserveBody : Program :=
  coreStructuredBody (coreFirstInstruction decodeCoreLoopBody)

def decodeLoopReserveConfig (store : MachineStore Universal.State)
    (data len ptr outLen : UInt32) (seed pending : UInt8)
    (returningInstance : ModuleInstanceId) : Config Universal.State :=
  ⟨.running ⟨⟨[.i32 decodeResultOut, .i32 pending.toUInt32, .i32 outLen],
      [.i32 coreFrame, .i32 ptr, .i32 seed.toUInt32],
      [.i32 1, .i32 outLen, .i32 (coreFrame + 60)]⟩,
    [.call 5] ++ decodeCoreLoopReserveBody.drop 12, 0, [],
    coreBlockControl decodeCoreLoopReserveBody (decodeCoreLoopBody.drop 1) ::
      decodeCoreLoopControl ::
      coreBlockControl decodeCoreFirstResultBody (decodeCoreInner.drop 33) ::
      decodeCoreControls,
    [{ locals := ⟨[], decodePostReadLocals data, []⟩
       continuation := decodeAfterCore
       resultArity := 0
       callerRemainder := []
       control := []
       returningInstance := returningInstance }]⟩, store⟩

set_option maxRecDepth 100000 in
theorem decode_loop_full_to_reserve
    (store : MachineStore Universal.State)
    (data len ptr capacity outLen remaining : UInt32)
    (seed pending : UInt8) (returningInstance : ModuleInstanceId)
    (hpages : 17 ≤ store.wasm.mem.pages)
    (hcapacity : store.wasm.mem.read32 (coreFrame + 60) = capacity)
    (hfull : outLen = capacity)
    (hmarker : store.wasm.mem.read32 (loopIterator + 16) = loopError)
    (herror : store.wasm.mem.read32 loopError = 1114114)
    (hremaining : store.wasm.mem.read32 (loopIterator + 4) = remaining)
    (hchunk : store.wasm.mem.read32 (loopIterator + 8) = 2) :
    Reaches (decodeLoopHeadConfig store data len ptr outLen seed pending
        returningInstance)
      (decodeLoopReserveConfig store data len ptr outLen seed pending
        returningInstance) := by
  simp only [decodeLoopHeadConfig, decodeCoreLoopBody,
    decodeCoreAfterSecondPair, decodeCoreAfterInitialAlloc,
    decodeCoreFirstResultBody, decodeCoreInner, decodeCoreOuter4,
    decodeCoreOuter3, decodeCoreOuter2, decodeCoreOuter1,
    coreStructuredBody, coreFirstInstruction, func5, List.drop]
  apply Reaches.prepend Step.block
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load32 (by
    change 1048496 ≤ store.wasm.mem.pages * 65536
    omega))
  rw [hcapacity]
  apply Reaches.prepend (Step.ne (result := 0) (by simp [hfull]))
  apply Reaches.prepend Step.brIfZero
  apply Reaches.prepend Step.block
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load32 (by
    change 1048524 ≤ store.wasm.mem.pages * 65536
    omega))
  rw [show coreFrame + 88 = loopIterator + 16 by decide, hmarker]
  apply Reaches.prepend (Step.load32 (by
    change 1048468 ≤ store.wasm.mem.pages * 65536
    omega))
  simp only [UInt32.add_zero]
  rw [herror]
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.ne (result := 0) rfl)
  apply Reaches.prepend Step.brIfZero
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load32 (by
    change 1048512 ≤ store.wasm.mem.pages * 65536
    omega))
  rw [show coreFrame + 76 = loopIterator + 4 by decide, hremaining]
  by_cases hz : remaining = 0
  · apply Reaches.prepend (Step.eqz (result := 1) (by simp [hz]))
    apply Reaches.prepend (Step.brIf (condition := 1) (by decide) rfl)
    simp
    apply Reaches.prepend (Step.localGet rfl)
    apply Reaches.prepend Step.const
    apply Reaches.prepend Step.add
    apply Reaches.prepend (Step.localGet rfl)
    apply Reaches.prepend Step.const
    simp [decodeLoopReserveConfig, decodeCoreLoopReserveBody,
      decodeCoreLoopControl, decodeCoreAfterLoop, coreBlockControl]
    exact ⟨[], .refl _⟩
  · apply Reaches.prepend (Step.eqz (result := 0) (by simp [hz]))
    apply Reaches.prepend Step.brIfZero
    apply Reaches.prepend (Step.localGet rfl)
    apply Reaches.prepend (Step.load32 (by
      change 1048516 ≤ store.wasm.mem.pages * 65536
      omega))
    rw [show coreFrame + 80 = loopIterator + 8 by decide, hchunk]
    apply Reaches.prepend (Step.eqz (result := 0) rfl)
    apply Reaches.prepend Step.brIfZero
    apply Reaches.prepend (Step.exitControl rfl)
    simp
    apply Reaches.prepend (Step.localGet rfl)
    apply Reaches.prepend Step.const
    apply Reaches.prepend Step.add
    apply Reaches.prepend (Step.localGet rfl)
    apply Reaches.prepend Step.const
    simp [decodeLoopReserveConfig, decodeCoreLoopReserveBody,
      decodeCoreLoopControl, decodeCoreAfterLoop, coreBlockControl]
    exact ⟨[], .refl _⟩

def decodeLoopReservedStore (allocStore : MachineStore Universal.State)
    (oldBump newCapacity : UInt32) : MachineStore Universal.State :=
  reserveFinishStore
    (growResultOkStore allocStore ((coreFrame - 16) + 4)
      (allocatorPtr oldBump 1) newCapacity)
    (coreFrame + 60) (allocatorPtr oldBump 1) newCapacity coreFrame

set_option maxRecDepth 100000 in
theorem decode_loop_after_reserve_append
    (allocStore : MachineStore Universal.State)
    (data len oldPtr outLen oldBump newCapacity : UInt32)
    (seed pending : UInt8) (returningInstance : ModuleInstanceId)
    (hpages : 17 ≤ allocStore.wasm.mem.pages)
    (hptrRead :
      (decodeLoopReservedStore allocStore oldBump newCapacity).wasm.mem.read32
        (coreFrame + 64) = allocatorPtr oldBump 1)
    (hwrite : (allocatorPtr oldBump 1 + outLen).toNat + 1 ≤
      allocStore.wasm.mem.pages * 65536) :
    let reserved := decodeLoopReservedStore allocStore oldBump newCapacity
    Reaches
      (growResultFinal reserved
        [.i32 decodeResultOut, .i32 pending.toUInt32, .i32 outLen]
        [.i32 coreFrame, .i32 oldPtr, .i32 seed.toUInt32] []
        (decodeCoreLoopReserveBody.drop 12) 0 []
        (coreBlockControl decodeCoreLoopReserveBody
            (decodeCoreLoopBody.drop 1) ::
          decodeCoreLoopControl ::
          coreBlockControl decodeCoreFirstResultBody
            (decodeCoreInner.drop 33) :: decodeCoreControls)
        [{ locals := ⟨[], decodePostReadLocals data, []⟩
           continuation := decodeAfterCore
           resultArity := 0
           callerRemainder := []
           control := []
           returningInstance := returningInstance }])
      (decodeLoopCallConfig
        (decodeLoopAppendStore reserved (allocatorPtr oldBump 1) outLen pending)
        data len (allocatorPtr oldBump 1) outLen seed pending
        returningInstance) := by
  dsimp only
  let reserved := decodeLoopReservedStore allocStore oldBump newCapacity
  have hreservedPages : reserved.wasm.mem.pages =
      allocStore.wasm.mem.pages := by
    simp [reserved, decodeLoopReservedStore]
  simp only [growResultFinal, decodeCoreLoopReserveBody, decodeCoreLoopBody,
    decodeCoreAfterSecondPair, decodeCoreAfterInitialAlloc,
    decodeCoreFirstResultBody, decodeCoreInner, decodeCoreOuter4,
    decodeCoreOuter3, decodeCoreOuter2, decodeCoreOuter1,
    coreStructuredBody, coreFirstInstruction, func5, List.drop]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load32 (by
    change 1048500 ≤ allocStore.wasm.mem.pages * 65536
    omega))
  rw [hptrRead]
  apply Reaches.prepend (Step.localSet rfl)
  apply Reaches.prepend (Step.exitControl rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.add
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.store8
    (address := outLen + allocatorPtr oldBump 1) (offset := 0)
    (value := pending.toUInt32) (by
      rw [hreservedPages]
      simpa [UInt32.add_comm] using hwrite))
  rw [setMemory_eq]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.add
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend (Step.store32 (by
    change 1048504 ≤ allocStore.wasm.mem.pages * 65536
    omega))
  rw [setMemory_eq]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.add
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.add
  simp [decodeLoopCallConfig, decodeLoopAppendStore, reserved,
    decodeCoreLoopBody, decodeCoreLoopControl, decodeCoreAfterLoop,
    coreBlockControl]
  exact ⟨[], .refl _⟩

end Submission.HexDecodeStdio
