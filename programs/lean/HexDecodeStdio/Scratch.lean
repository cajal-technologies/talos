import HexDecodeStdio.DecodePairOperational

open Wasm Project.HexStdio Wasm.SmallStep
open Project.HexDecodeStdio

def pairStore (bytes : List UInt8) : MachineStore Universal.State :=
  let initial : Store Universal.State := «module».initialStore
  let m0 := initial.mem.write32 (coreIterator + 4) (UInt32.ofNat bytes.length)
  let m1 := m0.write32 (coreIterator + 16) coreError
  let m2 := m1.write32 (coreIterator + 8) 2
  let m3 := m2.write32 coreIterator 1054000
  let m4 := m3.write32 (coreIterator + 12) 0
  let m5 := m4.write32 coreError 1114114
  let m6 := m5.write32 (coreError + 4) 0
  let m7 := m6.writeBytes 1054000 bytes
  { runtime := { instances := #[{ module := «module», host := Universal.envFor «module» }], entry := ⟨0⟩ }
    wasm := { initial with mem := m7 } }

def pairConfig (bytes : List UInt8) : Config Universal.State :=
  ⟨.running ⟨⟨[], [], [.i32 coreIterator, .i32 corePairOut]⟩,
    [.call 3], 0, [], [], []⟩, pairStore bytes⟩

#eval (runSteps 200 (pairConfig [0x64, 0x65])).trace.length
#eval (runSteps 200 (pairConfig [0x7a, 0x65])).trace.length
#eval (runSteps 200 (pairConfig [])).trace.length
#eval (runSteps 200 (pairConfig [0x31, 0x32])).trace.length
#eval (runSteps 200 (pairConfig [0x31, 0x61])).trace.length
#eval (runSteps 200 (pairConfig [0x31, 0x41])).trace.length
#eval (runSteps 200 (pairConfig [0x61, 0x32])).trace.length
#eval (runSteps 200 (pairConfig [0x61, 0x61])).trace.length
#eval (runSteps 200 (pairConfig [0x61, 0x41])).trace.length
#eval (runSteps 200 (pairConfig [0x41, 0x32])).trace.length
#eval (runSteps 200 (pairConfig [0x41, 0x61])).trace.length
#eval (runSteps 200 (pairConfig [0x41, 0x41])).trace.length

set_option maxRecDepth 100000 in
example :
    (runSteps 123 (pairConfig [0x64, 0x65])).result.finalConfig? =
      some ⟨.running ⟨⟨[], [], []⟩, [], 0, [], [], []⟩,
        decodePairValidStore (pairStore [0x64, 0x65]) 1054000 2 0 0xde⟩ := by
  rfl

def fixedRuntime : RuntimeEnv Universal.State :=
  { instances := #[{ module := «module», host := Universal.envFor «module» }], entry := ⟨0⟩ }

/-- A symbolic decimal pair requires a valid iterator frame and readable
input bytes. Reuse the operational trace instead of unfolding a fixed fuel. -/
example (store : MachineStore Universal.State)
    (inputPtr len chunkIndex : UInt32) (hi lo : UInt8)
    (hmod : store.runtime.currentModule = «module»)
    (hpages : 17 ≤ store.wasm.mem.pages)
    (hpagesMax : store.wasm.mem.pages ≤ 65536)
    (hinput : inputPtr.toNat + 2 ≤ store.wasm.mem.pages * 65536)
    (hinputLower : 1054000 ≤ inputPtr.toNat)
    (hlen : 2 ≤ len.toNat)
    (hlenRead : store.wasm.mem.read32 (coreIterator + 4) = len)
    (herrorRead : store.wasm.mem.read32 (coreIterator + 16) = coreError)
    (hchunkRead : store.wasm.mem.read32 (coreIterator + 8) = 2)
    (hptrRead : store.wasm.mem.read32 coreIterator = inputPtr)
    (hindexRead : store.wasm.mem.read32 (coreIterator + 12) = chunkIndex)
    (hhiRead : store.wasm.mem.read8 inputPtr = hi)
    (hloRead : store.wasm.mem.read8 (inputPtr + 1) = lo)
    (hhi : HexRoute.decimal.valid hi) (hlo : HexRoute.decimal.valid lo) :
    Reaches (pairStandaloneConfig store)
      (pairStandaloneReturn (decodePairValidStore store inputPtr len chunkIndex
        ((HexRoute.decimal.nibble lo |||
          (HexRoute.decimal.nibble hi <<< (4 : UInt32))).toUInt8))) := by
  exact decodePair_valid_reaches store inputPtr coreError len chunkIndex hi lo
    hmod hpages hpagesMax hinput hinputLower hlen hlenRead herrorRead
    hchunkRead hptrRead hindexRead hhiRead hloRead .decimal .decimal hhi hlo
    [] [] [] [] 0 [] [] []
