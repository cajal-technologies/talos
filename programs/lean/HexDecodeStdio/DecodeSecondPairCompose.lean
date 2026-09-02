import HexDecodeStdio.DecodeLoopReturnOperational

namespace Project.HexDecodeStdio

open Wasm Project.HexStdio Project.HexStdio.Spec
open Wasm.SmallStep

set_option maxRecDepth 100000 in
theorem decode_second_pair_empty_to_post
    (store : MachineStore Universal.State)
    (data len ptr : UInt32) (seed : UInt8)
    (returningInstance : ModuleInstanceId)
    (hmod : store.runtime.currentModule = «module»)
    (hpages : 17 ≤ store.wasm.mem.pages)
    (hlenRead :
      (decodeInitialVectorStore store ptr seed).wasm.mem.read32
        (secondIterator + 4) = 0) :
    let initial := decodeInitialVectorStore store ptr seed
    let paired := decodeSecondPairEmptyStore initial
    Reaches (decodeSecondPairConfig store data len ptr seed returningInstance)
      (decodePostLoopConfig paired data len ptr 8 1 seed
        returningInstance) := by
  dsimp only
  let initial := decodeInitialVectorStore store ptr seed
  let paired := decodeSecondPairEmptyStore initial
  have hpair := decodeSecondPair_empty_reaches initial
    (by simpa [initial, decodeInitialVectorStore] using hmod)
    (by change 17 ≤ store.wasm.mem.pages; exact hpages)
    hlenRead
    [.i32 decodeResultOut, .i32 8, .i32 1]
    [.i32 coreFrame, .i32 ptr, .i32 seed.toUInt32] []
    decodeCoreAfterSecondPair 0 []
    (coreBlockControl decodeCoreFirstResultBody (decodeCoreInner.drop 33) ::
      decodeCoreControls)
    [{ locals := ⟨[], decodePostReadLocals data, []⟩
       continuation := decodeAfterCore
       resultArity := 0
       callerRemainder := []
       control := []
       returningInstance := returningInstance }]
  have hpair' : Reaches
      (decodeSecondPairConfig store data len ptr seed returningInstance)
      (decodeAfterPairConfig paired data len ptr seed 0 returningInstance) := by
    simpa [decodeSecondPairConfig, decodeAfterPairConfig, initial, paired]
      using hpair
  apply hpair'.trans
  apply decode_second_pair_zero_to_post paired data len ptr seed
    returningInstance
  · change 17 ≤ store.wasm.mem.pages
    exact hpages
  · simp [paired, decodeSecondPairEmptyStore, Mem.read8, Mem.write8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem decode_second_pair_valid_to_loop
    (store : MachineStore Universal.State)
    (data len ptr inputPtr remaining chunkIndex : UInt32)
    (seed hi lo : UInt8) (hiRoute loRoute : HexRoute)
    (returningInstance : ModuleInstanceId)
    (hmod : store.runtime.currentModule = «module»)
    (hpages : 17 ≤ store.wasm.mem.pages)
    (hpagesMax : store.wasm.mem.pages ≤ 65536)
    (hinput : inputPtr.toNat + 2 ≤ store.wasm.mem.pages * 65536)
    (hinputLower : 1054000 ≤ inputPtr.toNat)
    (hlen : 2 ≤ remaining.toNat)
    (hlenRead : (decodeInitialVectorStore store ptr seed).wasm.mem.read32
      (secondIterator + 4) = remaining)
    (herrorRead : (decodeInitialVectorStore store ptr seed).wasm.mem.read32
      (secondIterator + 16) = secondError)
    (hchunkRead : (decodeInitialVectorStore store ptr seed).wasm.mem.read32
      (secondIterator + 8) = 2)
    (hptrRead : (decodeInitialVectorStore store ptr seed).wasm.mem.read32
      secondIterator = inputPtr)
    (hindexRead : (decodeInitialVectorStore store ptr seed).wasm.mem.read32
      (secondIterator + 12) = chunkIndex)
    (hhiRead : (decodeInitialVectorStore store ptr seed).wasm.mem.read8
      inputPtr = hi)
    (hloRead : (decodeInitialVectorStore store ptr seed).wasm.mem.read8
      (inputPtr + 1) = lo)
    (hhi : hiRoute.valid hi) (hlo : loRoute.valid lo) :
    let initial := decodeInitialVectorStore store ptr seed
    let next := (loRoute.nibble lo).toUInt8 |||
      ((hiRoute.nibble hi).toUInt8 <<< (4 : UInt8))
    let paired := decodeSecondPairValidStore initial inputPtr remaining
      chunkIndex next
    Reaches (decodeSecondPairConfig store data len ptr seed returningInstance)
      (decodeLoopHeadConfig paired data len ptr 1 seed next
        returningInstance) := by
  dsimp only
  let initial := decodeInitialVectorStore store ptr seed
  let next := (loRoute.nibble lo).toUInt8 |||
    ((hiRoute.nibble hi).toUInt8 <<< (4 : UInt8))
  let paired := decodeSecondPairValidStore initial inputPtr remaining
    chunkIndex next
  have hpair := decodeSecondPair_valid_reaches initial inputPtr secondError
    remaining chunkIndex hi lo
    (by simpa [initial, decodeInitialVectorStore] using hmod)
    (by change 17 ≤ store.wasm.mem.pages; exact hpages)
    (by change store.wasm.mem.pages ≤ 65536; exact hpagesMax)
    (by change inputPtr.toNat + 2 ≤ store.wasm.mem.pages * 65536;
        exact hinput)
    hinputLower hlen hlenRead herrorRead hchunkRead hptrRead hindexRead
    hhiRead hloRead hiRoute loRoute hhi hlo
    [.i32 decodeResultOut, .i32 8, .i32 1]
    [.i32 coreFrame, .i32 ptr, .i32 seed.toUInt32] []
    decodeCoreAfterSecondPair 0 []
    (coreBlockControl decodeCoreFirstResultBody (decodeCoreInner.drop 33) ::
      decodeCoreControls)
    [{ locals := ⟨[], decodePostReadLocals data, []⟩
       continuation := decodeAfterCore
       resultArity := 0
       callerRemainder := []
       control := []
       returningInstance := returningInstance }]
  have hpair' : Reaches
      (decodeSecondPairConfig store data len ptr seed returningInstance)
      (decodeAfterPairConfig paired data len ptr seed next
        returningInstance) := by
    simpa [decodeSecondPairConfig, decodeAfterPairConfig, initial, paired,
      next] using hpair
  apply hpair'.trans
  apply decode_after_pair_to_loop paired data len ptr seed next
    returningInstance
  · change 17 ≤ store.wasm.mem.pages
    exact hpages
  · simp [paired, decodeSecondPairValidStore, decodeSecondPairBaseStore,
      Mem.read8, Mem.write8]
  · simp [paired, decodeSecondPairValidStore, decodeSecondPairBaseStore,
      Mem.read8, Mem.write8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem decode_second_pair_invalid_high_to_post
    (store : MachineStore Universal.State)
    (data len ptr inputPtr remaining chunkIndex : UInt32)
    (seed hi lo : UInt8) (returningInstance : ModuleInstanceId)
    (hmod : store.runtime.currentModule = «module»)
    (hpages : 17 ≤ store.wasm.mem.pages)
    (hpagesMax : store.wasm.mem.pages ≤ 65536)
    (hinput : inputPtr.toNat + 2 ≤ store.wasm.mem.pages * 65536)
    (hinputLower : 1054000 ≤ inputPtr.toNat)
    (hlen : 2 ≤ remaining.toNat)
    (hlenRead : (decodeInitialVectorStore store ptr seed).wasm.mem.read32
      (secondIterator + 4) = remaining)
    (herrorRead : (decodeInitialVectorStore store ptr seed).wasm.mem.read32
      (secondIterator + 16) = secondError)
    (hchunkRead : (decodeInitialVectorStore store ptr seed).wasm.mem.read32
      (secondIterator + 8) = 2)
    (hptrRead : (decodeInitialVectorStore store ptr seed).wasm.mem.read32
      secondIterator = inputPtr)
    (hindexRead : (decodeInitialVectorStore store ptr seed).wasm.mem.read32
      (secondIterator + 12) = chunkIndex)
    (hhiRead : (decodeInitialVectorStore store ptr seed).wasm.mem.read8
      inputPtr = hi)
    (hloRead : (decodeInitialVectorStore store ptr seed).wasm.mem.read8
      (inputPtr + 1) = lo)
    (hhi : hexValue hi = none) :
    let initial := decodeInitialVectorStore store ptr seed
    let index := ((chunkIndex <<< (1 : UInt32)) &&& 255 |||
      (chunkIndex <<< (1 : UInt32)) &&& 4294967040)
    let paired := decodeSecondPairInvalidStore initial inputPtr remaining
      chunkIndex hi index
    Reaches (decodeSecondPairConfig store data len ptr seed returningInstance)
      (decodePostLoopConfig paired data len ptr 8 1 seed
        returningInstance) := by
  dsimp only
  let initial := decodeInitialVectorStore store ptr seed
  let index := ((chunkIndex <<< (1 : UInt32)) &&& 255 |||
    (chunkIndex <<< (1 : UInt32)) &&& 4294967040)
  let paired := decodeSecondPairInvalidStore initial inputPtr remaining
    chunkIndex hi index
  have hpair := decodeSecondPair_invalid_high_reaches initial inputPtr remaining
    chunkIndex hi lo
    (by simpa [initial, decodeInitialVectorStore] using hmod)
    (by change 17 ≤ store.wasm.mem.pages; exact hpages)
    (by change store.wasm.mem.pages ≤ 65536; exact hpagesMax)
    (by change inputPtr.toNat + 2 ≤ store.wasm.mem.pages * 65536;
        exact hinput)
    hinputLower hlen hlenRead herrorRead hchunkRead hptrRead hindexRead
    hhiRead hloRead hhi
    [.i32 decodeResultOut, .i32 8, .i32 1]
    [.i32 coreFrame, .i32 ptr, .i32 seed.toUInt32] []
    decodeCoreAfterSecondPair 0 []
    (coreBlockControl decodeCoreFirstResultBody (decodeCoreInner.drop 33) ::
      decodeCoreControls)
    [{ locals := ⟨[], decodePostReadLocals data, []⟩
       continuation := decodeAfterCore
       resultArity := 0
       callerRemainder := []
       control := []
       returningInstance := returningInstance }]
  have hpair' : Reaches
      (decodeSecondPairConfig store data len ptr seed returningInstance)
      (decodeAfterPairConfig paired data len ptr seed 0 returningInstance) := by
    simpa [decodeSecondPairConfig, decodeAfterPairConfig, initial, paired,
      index] using hpair
  apply hpair'.trans
  apply decode_second_pair_zero_to_post paired data len ptr seed
    returningInstance
  · change 17 ≤ store.wasm.mem.pages
    exact hpages
  · simp [paired, decodeSecondPairInvalidStore, Mem.read8, Mem.write8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem decode_second_pair_invalid_low_to_post
    (store : MachineStore Universal.State)
    (data len ptr inputPtr remaining chunkIndex : UInt32)
    (seed hi lo : UInt8) (hiRoute : HexRoute)
    (returningInstance : ModuleInstanceId)
    (hmod : store.runtime.currentModule = «module»)
    (hpages : 17 ≤ store.wasm.mem.pages)
    (hpagesMax : store.wasm.mem.pages ≤ 65536)
    (hinput : inputPtr.toNat + 2 ≤ store.wasm.mem.pages * 65536)
    (hinputLower : 1054000 ≤ inputPtr.toNat)
    (hlen : 2 ≤ remaining.toNat)
    (hlenRead : (decodeInitialVectorStore store ptr seed).wasm.mem.read32
      (secondIterator + 4) = remaining)
    (herrorRead : (decodeInitialVectorStore store ptr seed).wasm.mem.read32
      (secondIterator + 16) = secondError)
    (hchunkRead : (decodeInitialVectorStore store ptr seed).wasm.mem.read32
      (secondIterator + 8) = 2)
    (hptrRead : (decodeInitialVectorStore store ptr seed).wasm.mem.read32
      secondIterator = inputPtr)
    (hindexRead : (decodeInitialVectorStore store ptr seed).wasm.mem.read32
      (secondIterator + 12) = chunkIndex)
    (hhiRead : (decodeInitialVectorStore store ptr seed).wasm.mem.read8
      inputPtr = hi)
    (hloRead : (decodeInitialVectorStore store ptr seed).wasm.mem.read8
      (inputPtr + 1) = lo)
    (hhi : hiRoute.valid hi) (hlo : hexValue lo = none) :
    let initial := decodeInitialVectorStore store ptr seed
    let index := ((((chunkIndex <<< (1 : UInt32)) ||| 1) &&& 255) |||
      (chunkIndex <<< (1 : UInt32)) &&& 4294967040)
    let paired := decodeSecondPairInvalidStore initial inputPtr remaining
      chunkIndex lo index
    Reaches (decodeSecondPairConfig store data len ptr seed returningInstance)
      (decodePostLoopConfig paired data len ptr 8 1 seed
        returningInstance) := by
  dsimp only
  let initial := decodeInitialVectorStore store ptr seed
  let index := ((((chunkIndex <<< (1 : UInt32)) ||| 1) &&& 255) |||
    (chunkIndex <<< (1 : UInt32)) &&& 4294967040)
  let paired := decodeSecondPairInvalidStore initial inputPtr remaining
    chunkIndex lo index
  have hpair := decodeSecondPair_invalid_low_reaches initial inputPtr remaining
    chunkIndex hi lo
    (by simpa [initial, decodeInitialVectorStore] using hmod)
    (by change 17 ≤ store.wasm.mem.pages; exact hpages)
    (by change store.wasm.mem.pages ≤ 65536; exact hpagesMax)
    (by change inputPtr.toNat + 2 ≤ store.wasm.mem.pages * 65536;
        exact hinput)
    hinputLower hlen hlenRead herrorRead hchunkRead hptrRead hindexRead
    hhiRead hloRead hiRoute hhi hlo
    [.i32 decodeResultOut, .i32 8, .i32 1]
    [.i32 coreFrame, .i32 ptr, .i32 seed.toUInt32] []
    decodeCoreAfterSecondPair 0 []
    (coreBlockControl decodeCoreFirstResultBody (decodeCoreInner.drop 33) ::
      decodeCoreControls)
    [{ locals := ⟨[], decodePostReadLocals data, []⟩
       continuation := decodeAfterCore
       resultArity := 0
       callerRemainder := []
       control := []
       returningInstance := returningInstance }]
  have hpair' : Reaches
      (decodeSecondPairConfig store data len ptr seed returningInstance)
      (decodeAfterPairConfig paired data len ptr seed 0 returningInstance) := by
    simpa [decodeSecondPairConfig, decodeAfterPairConfig, initial, paired,
      index] using hpair
  apply hpair'.trans
  apply decode_second_pair_zero_to_post paired data len ptr seed
    returningInstance
  · change 17 ≤ store.wasm.mem.pages
    exact hpages
  · simp [paired, decodeSecondPairInvalidStore, Mem.read8, Mem.write8]

end Project.HexDecodeStdio
