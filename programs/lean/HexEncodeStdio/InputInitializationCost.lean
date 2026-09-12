import HexEncodeStdio.ReadToEndResourceCost
import HexEncodeStdio.ReadToEndInitial

/-! The first successful physical input allocation initializes both the
existing byte-level invariant and the numerical capacity/bump potentials. -/

namespace Project.HexEncodeStdio.InputInitializationCost

open Wasm Wasm.SmallStep

/-- The first read's existing semantic invariant supplies exact contents,
while its actual initial pointer and capacity establish the resource bounds. -/
theorem first_bounded_invariant
    (input bytes : List UInt8)
    (allocStore : MachineStore Universal.State)
    (hbytes : bytes = input.take 32) (hnil : bytes ≠ [])
    (hsuccess :
      let entryStore := encodeFrameStore input
      let framed := readToEndFrameStore entryStore readToEndStack
      let after := readAdapterResultStore
        (readChunkFrameStore framed firstChunkFrame)
        firstChunkResult firstChunkBuffer bytes
      let count := UInt32.ofNat bytes.length
      ByteGrowSuccess (reserveFrameStore after (firstChunkFrame - 16))
        0 1 (reserveNewCapacity 0 count 0) 0 allocStore) :
    let count := UInt32.ofNat bytes.length
    let capacity := reserveNewCapacity 0 count 0
    let data := allocatorPtr 0 1
    let bump := allocatorFinish capacity 1 0
    let reserved := reserveFinishStore
      (growResultOkStore allocStore ((firstChunkFrame - 16) + 4)
        data capacity)
      readToEndVector data capacity firstChunkFrame
    let finalStore := readChunkFinishedStore
      (readChunkCopiedStore reserved data firstChunkBuffer count)
      readToEndResult readToEndVector count 0 readToEndStack
    ReadToEndResourceCost.BoundedReadInv input bytes (input.drop bytes.length) finalStore capacity data
      count bump := by
  have initial := first_nonempty_read_invariant input bytes allocStore hbytes hnil hsuccess
  dsimp only at initial ⊢
  have hcount : bytes.length ≤ input.length := by
    rw [hbytes, List.length_take]
    omega
  have hsmall : bytes.length ≤ 32 := by
    rw [hbytes, List.length_take]
    omega
  have hcapacity := first_capacity_toNat bytes hnil hsmall
  refine { toReadToEndInv := initial, capacity_upper := ?_, bump_upper := ?_ }
  · rw [hcapacity]
    exact (ReadToEndResourceCost.initial_potentials input.length bytes.length hcount).1
  · have actual := initial.data_capacity_bump
    have base : (allocatorPtr 0 1).toNat = 1054000 := by decide
    rw [base] at actual
    omega

end Project.HexEncodeStdio.InputInitializationCost
