import HexDecodeStdio.DecodeCoreOperational
import HexDecodeStdio.ReserveOutcome

namespace Submission.HexDecodeStdio

open Wasm Project.HexStdio Project.HexStdio.Spec
open Wasm.SmallStep

def decodeCoreLoopBody : Program :=
  coreStructuredBody (coreFirstInstruction (decodeCoreAfterSecondPair.drop 9))

def decodeCoreAfterLoop : Program := decodeCoreAfterSecondPair.drop 10

def decodeCoreLoopControl : ControlFrame :=
  { kind := .loop, paramArity := 0, resultArity := 0,
    body := decodeCoreLoopBody, continuation := decodeCoreAfterLoop,
    belowStack := [] }

def decodeAfterPairConfig (store : MachineStore Universal.State)
    (data len ptr : UInt32) (seed pending : UInt8)
    (returningInstance : ModuleInstanceId) : Config Universal.State :=
  ⟨.running ⟨⟨[.i32 decodeResultOut, .i32 8, .i32 1],
      [.i32 coreFrame, .i32 ptr, .i32 seed.toUInt32], []⟩,
    decodeCoreAfterSecondPair, 0, [],
    coreBlockControl decodeCoreFirstResultBody (decodeCoreInner.drop 33) ::
      decodeCoreControls,
    [{ locals := ⟨[], decodePostReadLocals data, []⟩
       continuation := decodeAfterCore
       resultArity := 0
       callerRemainder := []
       control := []
       returningInstance := returningInstance }]⟩, store⟩

def decodeLoopHeadConfig (store : MachineStore Universal.State)
    (data len ptr outLen : UInt32) (seed pending : UInt8)
    (returningInstance : ModuleInstanceId) : Config Universal.State :=
  ⟨.running ⟨⟨[.i32 decodeResultOut, .i32 pending.toUInt32, .i32 outLen],
      [.i32 coreFrame, .i32 ptr, .i32 seed.toUInt32], []⟩,
    decodeCoreLoopBody, 0, [],
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
theorem decode_after_pair_to_loop
    (store : MachineStore Universal.State) (data len ptr : UInt32)
    (seed pending : UInt8) (returningInstance : ModuleInstanceId)
    (hpages : 17 ≤ store.wasm.mem.pages)
    (htag : store.wasm.mem.read8 decodeSecondPairOut = 1)
    (hpending : store.wasm.mem.read8 (decodeSecondPairOut + 1) = pending) :
    Reaches (decodeAfterPairConfig store data len ptr seed pending
        returningInstance)
      (decodeLoopHeadConfig store data len ptr 1 seed pending
        returningInstance) := by
  simp only [decodeAfterPairConfig, decodeCoreAfterSecondPair,
    decodeCoreAfterInitialAlloc, decodeCoreFirstResultBody, decodeCoreInner,
    decodeCoreOuter4, decodeCoreOuter3, decodeCoreOuter2, decodeCoreOuter1,
    coreStructuredBody, coreFirstInstruction, func5, List.drop]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load8U (by
    change 1048449 ≤ store.wasm.mem.pages * 65536
    omega))
  rw [show coreFrame + 16 = decodeSecondPairOut by decide, htag]
  apply Reaches.prepend (Step.eqz (result := 0) rfl)
  apply Reaches.prepend Step.brIfZero
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load8U (by
    change 1048450 ≤ store.wasm.mem.pages * 65536
    omega))
  rw [show coreFrame + 17 = decodeSecondPairOut + 1 by decide, hpending]
  apply Reaches.prepend (Step.localSet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.localSet rfl)
  apply Reaches.prepend Step.loop
  simp [decodeLoopHeadConfig, decodeCoreLoopBody, decodeCoreAfterLoop,
    decodeCoreLoopControl, coreBlockControl]
  exact ⟨[], .refl _⟩

def decodeLoopAppendStore (store : MachineStore Universal.State)
    (ptr outLen : UInt32) (pending : UInt8) :
    MachineStore Universal.State :=
  let mem0 := store.wasm.mem.write8 (outLen + ptr) pending
  let mem1 := mem0.write32 (coreFrame + 68) (1 + outLen)
  { store with wasm := { store.wasm with mem := mem1 } }

def decodeLoopCallConfig (store : MachineStore Universal.State)
    (data len ptr outLen : UInt32) (seed pending : UInt8)
    (returningInstance : ModuleInstanceId) : Config Universal.State :=
  let nextLen := 1 + outLen
  ⟨.running ⟨⟨[.i32 decodeResultOut, .i32 pending.toUInt32, .i32 nextLen],
      [.i32 coreFrame, .i32 ptr, .i32 seed.toUInt32],
      [.i32 loopIterator, .i32 loopPairOut]⟩,
    [.call 3] ++ decodeCoreLoopBody.drop 19, 0, [],
    decodeCoreLoopControl ::
      coreBlockControl decodeCoreFirstResultBody (decodeCoreInner.drop 33) ::
      decodeCoreControls,
    [{ locals := ⟨[], decodePostReadLocals data, []⟩
       continuation := decodeAfterCore
       resultArity := 0
       callerRemainder := []
       control := []
       returningInstance := returningInstance }]⟩,
    store⟩

set_option maxRecDepth 100000 in
theorem decode_loop_append_no_grow
    (store : MachineStore Universal.State)
    (data len ptr capacity outLen : UInt32) (seed pending : UInt8)
    (returningInstance : ModuleInstanceId)
    (hpages : 17 ≤ store.wasm.mem.pages)
    (hcapacity : store.wasm.mem.read32 (coreFrame + 60) = capacity)
    (hne : outLen ≠ capacity)
    (hwrite : (ptr + outLen).toNat + 1 ≤
      store.wasm.mem.pages * 65536) :
    Reaches (decodeLoopHeadConfig store data len ptr outLen seed pending
        returningInstance)
      (decodeLoopCallConfig (decodeLoopAppendStore store ptr outLen pending)
        data len ptr outLen seed pending returningInstance) := by
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
  apply Reaches.prepend (Step.ne (result := 1) (by simp [hne]))
  apply Reaches.prepend (Step.brIf (condition := 1) (by decide) rfl)
  simp
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.add
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.store8 (address := outLen + ptr) (offset := 0)
    (value := pending.toUInt32) (by
      simpa [UInt32.add_comm] using hwrite))
  rw [setMemory_eq]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.add
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend (Step.store32 (by
    change 1048504 ≤ store.wasm.mem.pages * 65536
    omega))
  rw [setMemory_eq]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.add
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.add
  simp [decodeLoopCallConfig, decodeLoopAppendStore, decodeCoreLoopBody,
    decodeCoreLoopControl, decodeCoreAfterLoop, coreBlockControl]
  exact ⟨[], .refl _⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem decode_loop_pair_valid_next
    (store : MachineStore Universal.State)
    (data len ptr outLen inputPtr remaining chunkIndex : UInt32)
    (seed pending hi lo : UInt8) (hiRoute loRoute : HexRoute)
    (returningInstance : ModuleInstanceId)
    (hmod : store.runtime.currentModule = «module»)
    (hpages : 17 ≤ store.wasm.mem.pages)
    (hpagesMax : store.wasm.mem.pages ≤ 65536)
    (hinput : inputPtr.toNat + 2 ≤ store.wasm.mem.pages * 65536)
    (hinputLower : 1054000 ≤ inputPtr.toNat)
    (hlen : 2 ≤ remaining.toNat)
    (hlenRead : store.wasm.mem.read32 (loopIterator + 4) = remaining)
    (herrorRead : store.wasm.mem.read32 (loopIterator + 16) = loopError)
    (hchunkRead : store.wasm.mem.read32 (loopIterator + 8) = 2)
    (hptrRead : store.wasm.mem.read32 loopIterator = inputPtr)
    (hindexRead : store.wasm.mem.read32 (loopIterator + 12) = chunkIndex)
    (hhiRead : store.wasm.mem.read8 inputPtr = hi)
    (hloRead : store.wasm.mem.read8 (inputPtr + 1) = lo)
    (hhi : hiRoute.valid hi) (hlo : loRoute.valid lo) :
    let next := (loRoute.nibble lo).toUInt8 |||
      ((hiRoute.nibble hi).toUInt8 <<< (4 : UInt8))
    let paired := decodeLoopPairValidStore store inputPtr remaining chunkIndex next
    Reaches (decodeLoopCallConfig store data len ptr outLen seed pending
        returningInstance)
      (decodeLoopHeadConfig paired data len ptr (1 + outLen) seed next
        returningInstance) := by
  dsimp only
  let next := (loRoute.nibble lo).toUInt8 |||
    ((hiRoute.nibble hi).toUInt8 <<< (4 : UInt8))
  let paired := decodeLoopPairValidStore store inputPtr remaining chunkIndex next
  have hpair := decodeLoopPair_valid_reaches store inputPtr loopError remaining
    chunkIndex hi lo hmod hpages hpagesMax hinput hinputLower hlen hlenRead
    herrorRead hchunkRead hptrRead hindexRead hhiRead hloRead hiRoute loRoute
    hhi hlo
    [.i32 decodeResultOut, .i32 pending.toUInt32, .i32 (1 + outLen)]
    [.i32 coreFrame, .i32 ptr, .i32 seed.toUInt32] []
    (decodeCoreLoopBody.drop 19) 0 []
    (decodeCoreLoopControl ::
      coreBlockControl decodeCoreFirstResultBody (decodeCoreInner.drop 33) ::
      decodeCoreControls)
    [{ locals := ⟨[], decodePostReadLocals data, []⟩
       continuation := decodeAfterCore
       resultArity := 0
       callerRemainder := []
       control := []
       returningInstance := returningInstance }]
  apply (show Reaches (decodeLoopCallConfig store data len ptr outLen seed
      pending returningInstance) _ by
    simpa [decodeLoopCallConfig, next, paired] using hpair).trans
  simp only [decodeCoreLoopBody, decodeCoreAfterSecondPair,
    decodeCoreAfterInitialAlloc, decodeCoreFirstResultBody, decodeCoreInner,
    decodeCoreOuter4, decodeCoreOuter3, decodeCoreOuter2, decodeCoreOuter1,
    coreStructuredBody, coreFirstInstruction, func5, List.drop]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load8U (by
    rw [show (1048432 : UInt32).toNat + (9 : UInt32).toNat + 1 =
      1048442 by decide]
    simp only [decodeLoopPairValidStore, decodeLoopPairBaseStore,
      Mem.write8, Mem.write32_pages]
    omega))
  have hpayload : paired.wasm.mem.read8 (loopPairOut + 1) = next := by
    simp [paired, decodeLoopPairValidStore, decodeLoopPairBaseStore,
      Mem.read8, Mem.write8]
  rw [show coreFrame + 9 = loopPairOut + 1 by decide, hpayload]
  apply Reaches.prepend (Step.localSet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load8U (by
    rw [show (1048432 : UInt32).toNat + (8 : UInt32).toNat + 1 =
      1048441 by decide]
    simp only [decodeLoopPairValidStore, decodeLoopPairBaseStore,
      Mem.write8, Mem.write32_pages]
    omega))
  have htag : paired.wasm.mem.read8 loopPairOut = 1 := by
    simp [paired, decodeLoopPairValidStore, decodeLoopPairBaseStore,
      Mem.read8, Mem.write8]
  rw [show coreFrame + 8 = loopPairOut by decide, htag]
  apply Reaches.prepend (Step.brIf (condition := 1) (by decide) rfl)
  simp [decodeLoopHeadConfig, paired, next, decodeCoreLoopBody,
    decodeCoreLoopControl, decodeCoreAfterLoop, coreBlockControl]
  exact ⟨[], .refl _⟩

def decodeAfterLoopPairConfig (store : MachineStore Universal.State)
    (data len ptr outLen : UInt32) (seed pending : UInt8)
    (returningInstance : ModuleInstanceId) : Config Universal.State :=
  ⟨.running ⟨⟨[.i32 decodeResultOut, .i32 pending.toUInt32,
        .i32 (1 + outLen)],
      [.i32 coreFrame, .i32 ptr, .i32 seed.toUInt32], []⟩,
    decodeCoreLoopBody.drop 19, 0, [],
    decodeCoreLoopControl ::
      coreBlockControl decodeCoreFirstResultBody (decodeCoreInner.drop 33) ::
      decodeCoreControls,
    [{ locals := ⟨[], decodePostReadLocals data, []⟩
       continuation := decodeAfterCore
       resultArity := 0
       callerRemainder := []
       control := []
       returningInstance := returningInstance }]⟩, store⟩

def decodeLoopExitConfig (store : MachineStore Universal.State)
    (data len ptr outLen : UInt32) (seed payload : UInt8)
    (returningInstance : ModuleInstanceId) : Config Universal.State :=
  ⟨.running ⟨⟨[.i32 decodeResultOut, .i32 payload.toUInt32,
        .i32 (1 + outLen)],
      [.i32 coreFrame, .i32 ptr, .i32 seed.toUInt32], []⟩,
    decodeCoreAfterLoop, 0, [],
    coreBlockControl decodeCoreFirstResultBody (decodeCoreInner.drop 33) ::
      decodeCoreControls,
    [{ locals := ⟨[], decodePostReadLocals data, []⟩
       continuation := decodeAfterCore
       resultArity := 0
       callerRemainder := []
       control := []
       returningInstance := returningInstance }]⟩, store⟩

set_option maxRecDepth 100000 in
theorem decode_loop_pair_zero_exit
    (store : MachineStore Universal.State)
    (data len ptr outLen : UInt32) (seed pending payload : UInt8)
    (returningInstance : ModuleInstanceId)
    (hpages : 17 ≤ store.wasm.mem.pages)
    (htag : store.wasm.mem.read8 loopPairOut = 0)
    (hpayload : store.wasm.mem.read8 (loopPairOut + 1) = payload) :
    Reaches (decodeAfterLoopPairConfig store data len ptr outLen seed pending
        returningInstance)
      (decodeLoopExitConfig store data len ptr outLen seed payload
        returningInstance) := by
  simp only [decodeAfterLoopPairConfig, decodeCoreLoopBody,
    decodeCoreAfterSecondPair, decodeCoreAfterInitialAlloc,
    decodeCoreFirstResultBody, decodeCoreInner, decodeCoreOuter4,
    decodeCoreOuter3, decodeCoreOuter2, decodeCoreOuter1,
    coreStructuredBody, coreFirstInstruction, func5, List.drop]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load8U (by
    change 1048442 ≤ store.wasm.mem.pages * 65536
    omega))
  rw [show coreFrame + 9 = loopPairOut + 1 by decide, hpayload]
  apply Reaches.prepend (Step.localSet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load8U (by
    change 1048441 ≤ store.wasm.mem.pages * 65536
    omega))
  rw [show coreFrame + 8 = loopPairOut by decide, htag]
  apply Reaches.prepend Step.brIfZero
  apply Reaches.prepend (Step.exitControl rfl)
  simp [decodeLoopExitConfig, decodeCoreAfterLoop, decodeCoreLoopControl,
    coreBlockControl]
  exact ⟨[], .refl _⟩

set_option maxRecDepth 100000 in
theorem decode_loop_pair_empty_exit
    (store : MachineStore Universal.State)
    (data len ptr outLen : UInt32) (seed pending : UInt8)
    (returningInstance : ModuleInstanceId)
    (hmod : store.runtime.currentModule = «module»)
    (hpages : 17 ≤ store.wasm.mem.pages)
    (hlenRead : store.wasm.mem.read32 (loopIterator + 4) = 0) :
    let paired := decodeLoopPairEmptyStore store
    Reaches (decodeLoopCallConfig store data len ptr outLen seed pending
        returningInstance)
      (decodeLoopExitConfig paired data len ptr outLen seed 0
        returningInstance) := by
  dsimp only
  let paired := decodeLoopPairEmptyStore store
  have hpair := decodeLoopPair_empty_reaches store hmod hpages hlenRead
    [.i32 decodeResultOut, .i32 pending.toUInt32, .i32 (1 + outLen)]
    [.i32 coreFrame, .i32 ptr, .i32 seed.toUInt32] []
    (decodeCoreLoopBody.drop 19) 0 []
    (decodeCoreLoopControl ::
      coreBlockControl decodeCoreFirstResultBody (decodeCoreInner.drop 33) ::
      decodeCoreControls)
    [{ locals := ⟨[], decodePostReadLocals data, []⟩
       continuation := decodeAfterCore
       resultArity := 0
       callerRemainder := []
       control := []
       returningInstance := returningInstance }]
  have hpair' : Reaches
      (decodeLoopCallConfig store data len ptr outLen seed pending
        returningInstance)
      (decodeAfterLoopPairConfig paired data len ptr outLen seed pending
        returningInstance) := by
    simpa [decodeLoopCallConfig, decodeAfterLoopPairConfig, paired] using hpair
  apply hpair'.trans
  apply decode_loop_pair_zero_exit paired data len ptr outLen seed pending 0
    returningInstance
  · change 17 ≤ store.wasm.mem.pages
    exact hpages
  · simp [paired, decodeLoopPairEmptyStore, Mem.read8, Mem.write8]
  · simp [paired, decodeLoopPairEmptyStore, Mem.read8, Mem.write8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem decode_loop_pair_invalid_high_exit
    (store : MachineStore Universal.State)
    (data len ptr outLen inputPtr remaining chunkIndex : UInt32)
    (seed pending hi lo : UInt8) (returningInstance : ModuleInstanceId)
    (hmod : store.runtime.currentModule = «module»)
    (hpages : 17 ≤ store.wasm.mem.pages)
    (hpagesMax : store.wasm.mem.pages ≤ 65536)
    (hinput : inputPtr.toNat + 2 ≤ store.wasm.mem.pages * 65536)
    (hinputLower : 1054000 ≤ inputPtr.toNat)
    (hlen : 2 ≤ remaining.toNat)
    (hlenRead : store.wasm.mem.read32 (loopIterator + 4) = remaining)
    (herrorRead : store.wasm.mem.read32 (loopIterator + 16) = loopError)
    (hchunkRead : store.wasm.mem.read32 (loopIterator + 8) = 2)
    (hptrRead : store.wasm.mem.read32 loopIterator = inputPtr)
    (hindexRead : store.wasm.mem.read32 (loopIterator + 12) = chunkIndex)
    (hhiRead : store.wasm.mem.read8 inputPtr = hi)
    (hloRead : store.wasm.mem.read8 (inputPtr + 1) = lo)
    (hhi : hexValue hi = none) :
    let index := ((chunkIndex <<< (1 : UInt32)) &&& 255 |||
      (chunkIndex <<< (1 : UInt32)) &&& 4294967040)
    let paired := decodeLoopPairInvalidStore store inputPtr remaining
      chunkIndex hi index
    Reaches (decodeLoopCallConfig store data len ptr outLen seed pending
        returningInstance)
      (decodeLoopExitConfig paired data len ptr outLen seed hi
        returningInstance) := by
  dsimp only
  let index := ((chunkIndex <<< (1 : UInt32)) &&& 255 |||
    (chunkIndex <<< (1 : UInt32)) &&& 4294967040)
  let paired := decodeLoopPairInvalidStore store inputPtr remaining
    chunkIndex hi index
  have hpair := decodeLoopPair_invalid_high_reaches store inputPtr remaining
    chunkIndex hi lo hmod hpages hpagesMax hinput hinputLower hlen hlenRead
    herrorRead hchunkRead hptrRead hindexRead hhiRead hloRead hhi
    [.i32 decodeResultOut, .i32 pending.toUInt32, .i32 (1 + outLen)]
    [.i32 coreFrame, .i32 ptr, .i32 seed.toUInt32] []
    (decodeCoreLoopBody.drop 19) 0 []
    (decodeCoreLoopControl ::
      coreBlockControl decodeCoreFirstResultBody (decodeCoreInner.drop 33) ::
      decodeCoreControls)
    [{ locals := ⟨[], decodePostReadLocals data, []⟩
       continuation := decodeAfterCore
       resultArity := 0
       callerRemainder := []
       control := []
       returningInstance := returningInstance }]
  have hpair' : Reaches
      (decodeLoopCallConfig store data len ptr outLen seed pending
        returningInstance)
      (decodeAfterLoopPairConfig paired data len ptr outLen seed pending
        returningInstance) := by
    simpa [decodeLoopCallConfig, decodeAfterLoopPairConfig, paired, index]
      using hpair
  apply hpair'.trans
  apply decode_loop_pair_zero_exit paired data len ptr outLen seed pending hi
    returningInstance
  · change 17 ≤ store.wasm.mem.pages
    exact hpages
  · simp [paired, decodeLoopPairInvalidStore, Mem.read8, Mem.write8]
  · simp [paired, decodeLoopPairInvalidStore, Mem.read8, Mem.write8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem decode_loop_pair_invalid_low_exit
    (store : MachineStore Universal.State)
    (data len ptr outLen inputPtr remaining chunkIndex : UInt32)
    (seed pending hi lo : UInt8) (hiRoute : HexRoute)
    (returningInstance : ModuleInstanceId)
    (hmod : store.runtime.currentModule = «module»)
    (hpages : 17 ≤ store.wasm.mem.pages)
    (hpagesMax : store.wasm.mem.pages ≤ 65536)
    (hinput : inputPtr.toNat + 2 ≤ store.wasm.mem.pages * 65536)
    (hinputLower : 1054000 ≤ inputPtr.toNat)
    (hlen : 2 ≤ remaining.toNat)
    (hlenRead : store.wasm.mem.read32 (loopIterator + 4) = remaining)
    (herrorRead : store.wasm.mem.read32 (loopIterator + 16) = loopError)
    (hchunkRead : store.wasm.mem.read32 (loopIterator + 8) = 2)
    (hptrRead : store.wasm.mem.read32 loopIterator = inputPtr)
    (hindexRead : store.wasm.mem.read32 (loopIterator + 12) = chunkIndex)
    (hhiRead : store.wasm.mem.read8 inputPtr = hi)
    (hloRead : store.wasm.mem.read8 (inputPtr + 1) = lo)
    (hhi : hiRoute.valid hi) (hlo : hexValue lo = none) :
    let index := ((((chunkIndex <<< (1 : UInt32)) ||| 1) &&& 255) |||
      (chunkIndex <<< (1 : UInt32)) &&& 4294967040)
    let paired := decodeLoopPairInvalidStore store inputPtr remaining
      chunkIndex lo index
    Reaches (decodeLoopCallConfig store data len ptr outLen seed pending
        returningInstance)
      (decodeLoopExitConfig paired data len ptr outLen seed lo
        returningInstance) := by
  dsimp only
  let index := ((((chunkIndex <<< (1 : UInt32)) ||| 1) &&& 255) |||
    (chunkIndex <<< (1 : UInt32)) &&& 4294967040)
  let paired := decodeLoopPairInvalidStore store inputPtr remaining
    chunkIndex lo index
  have hpair := decodeLoopPair_invalid_low_reaches store inputPtr remaining
    chunkIndex hi lo hmod hpages hpagesMax hinput hinputLower hlen hlenRead
    herrorRead hchunkRead hptrRead hindexRead hhiRead hloRead hiRoute hhi hlo
    [.i32 decodeResultOut, .i32 pending.toUInt32, .i32 (1 + outLen)]
    [.i32 coreFrame, .i32 ptr, .i32 seed.toUInt32] []
    (decodeCoreLoopBody.drop 19) 0 []
    (decodeCoreLoopControl ::
      coreBlockControl decodeCoreFirstResultBody (decodeCoreInner.drop 33) ::
      decodeCoreControls)
    [{ locals := ⟨[], decodePostReadLocals data, []⟩
       continuation := decodeAfterCore
       resultArity := 0
       callerRemainder := []
       control := []
       returningInstance := returningInstance }]
  have hpair' : Reaches
      (decodeLoopCallConfig store data len ptr outLen seed pending
        returningInstance)
      (decodeAfterLoopPairConfig paired data len ptr outLen seed pending
        returningInstance) := by
    simpa [decodeLoopCallConfig, decodeAfterLoopPairConfig, paired, index]
      using hpair
  apply hpair'.trans
  apply decode_loop_pair_zero_exit paired data len ptr outLen seed pending lo
    returningInstance
  · change 17 ≤ store.wasm.mem.pages
    exact hpages
  · simp [paired, decodeLoopPairInvalidStore, Mem.read8, Mem.write8]
  · simp [paired, decodeLoopPairInvalidStore, Mem.read8, Mem.write8]

end Submission.HexDecodeStdio
