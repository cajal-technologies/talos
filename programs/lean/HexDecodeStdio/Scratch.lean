import HexDecodeStdio.DecodePairOperational

open Wasm Project.HexStdio Wasm.SmallStep
open Submission.HexDecodeStdio

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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
example (store : MachineStore Universal.State)
    (inputPtr len chunkIndex : UInt32) (hi lo oldTag oldPayload : UInt8)
    (hhi : HexRoute.decimal.valid hi) (hlo : HexRoute.decimal.valid lo) :
    let base := { store with runtime := fixedRuntime }
    (runSteps 133 (pairStandaloneConfig
      (pairPreparedStore base inputPtr len chunkIndex hi lo oldTag oldPayload))).result.finalConfig? =
      some (pairStandaloneReturn
        (decodePairValidStore
          (pairPreparedStore base inputPtr len chunkIndex hi lo oldTag oldPayload)
          inputPtr len chunkIndex
          ((HexRoute.decimal.nibble lo |||
            (HexRoute.decimal.nibble hi <<< (4 : UInt32))).toUInt8))) := by
  dsimp only
  simp only [HexRoute.valid] at hhi hlo
  rcases hhi with ⟨hhiU, hhiL, hhiD⟩
  rcases hlo with ⟨hloU, hloL, hloD⟩
  simp (config := { maxSteps := 1000000 }) [runSteps, pairStandaloneConfig,
    pairStandaloneReturn, pairPreparedStore, decodePairValidStore,
    decodePairBaseStore, fixedRuntime, hhiU, hhiL, hhiD, hloU, hloL, hloD]
