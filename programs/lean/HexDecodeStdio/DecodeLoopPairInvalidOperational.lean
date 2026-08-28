import HexDecodeStdio.DecodeLoopPairOperational
import HexDecodeStdio.HexMath

namespace Submission.HexDecodeStdio

open Wasm Project.HexStdio Project.HexStdio.Spec
open Wasm.SmallStep

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem decodeLoopPair_invalid_high_reaches
    (store : MachineStore Universal.State)
    (inputPtr len chunkIndex : UInt32) (hi lo : UInt8)
    (hmod : store.runtime.currentModule = «module»)
    (hpages : 17 ≤ store.wasm.mem.pages)
    (hpagesMax : store.wasm.mem.pages ≤ 65536)
    (hinput : inputPtr.toNat + 2 ≤ store.wasm.mem.pages * 65536)
    (hinputLower : 1054000 ≤ inputPtr.toNat)
    (hlen : 2 ≤ len.toNat)
    (hlenRead : store.wasm.mem.read32 (loopIterator + 4) = len)
    (herrorRead : store.wasm.mem.read32 (loopIterator + 16) = loopError)
    (hchunkRead : store.wasm.mem.read32 (loopIterator + 8) = 2)
    (hptrRead : store.wasm.mem.read32 loopIterator = inputPtr)
    (hindexRead : store.wasm.mem.read32 (loopIterator + 12) = chunkIndex)
    (hhiRead : store.wasm.mem.read8 inputPtr = hi)
    (hloRead : store.wasm.mem.read8 (inputPtr + 1) = lo)
    (hhi : hexValue hi = none)
    (callerParams callerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame) :
    Reaches
      ⟨.running ⟨⟨callerParams, callerLocalValues,
          .i32 loopIterator :: .i32 loopPairOut :: stack⟩,
        .call 3 :: code, arity, remainder, controls, calls⟩, store⟩
      ⟨.running ⟨⟨callerParams, callerLocalValues, stack⟩,
        code, arity, remainder, controls, calls⟩,
        decodeLoopPairInvalidStore store inputPtr len chunkIndex hi
          ((chunkIndex <<< (1 : UInt32)) &&& 255 |||
            (chunkIndex <<< (1 : UInt32)) &&& 4294967040)⟩ := by
  subst len
  subst chunkIndex
  subst inputPtr
  subst hi
  subst lo
  let len := store.wasm.mem.read32 (loopIterator + 4)
  let errorPtr := store.wasm.mem.read32 (loopIterator + 16)
  let chunkIndex := store.wasm.mem.read32 (loopIterator + 12)
  let inputPtr := store.wasm.mem.read32 loopIterator
  let hi := store.wasm.mem.read8 inputPtr
  let lo := store.wasm.mem.read8 (inputPtr + 1)
  obtain ⟨hhiUpper, hhiLower, hhiDigit⟩ :=
    Submission.HexDecodeStdio.hexValue_none_tests hi hhi
  simp only [hi, Mem.read8] at hhiUpper hhiLower hhiDigit
  have hlenA : 2 ≤ len.toNat := by simpa only [len] using hlen
  change 2 ≤ (store.wasm.mem.read32 1048508).toNat at hlenA
  have hinputA : inputPtr.toNat + 2 ≤ store.wasm.mem.pages * 65536 := by
    simpa only [inputPtr] using hinput
  have hinputLowerA : 1054000 ≤ inputPtr.toNat := by
    simpa only [inputPtr] using hinputLower
  norm_num at hlen
  have hiterNat : (1048504 : UInt32).toNat = 1048504 := by decide
  have hlenAddrNat : (1048508 : UInt32).toNat = 1048508 := by decide
  have hframe : 1048524 ≤ store.wasm.mem.pages * 65536 := by omega
  have hinput1 : (inputPtr + 1).toNat = inputPtr.toNat + 1 := by
    rw [UInt32.toNat_add]
    simp only [UInt32.toNat_ofNat]
    rw [Nat.mod_eq_of_lt]
    omega
  have hinput1Mod :
      (inputPtr.toNat + (1 : UInt32).toNat) % 4294967296 =
        (inputPtr + 1).toNat := by
    exact (UInt32.toNat_add inputPtr 1).symm
  have hhi0 : inputPtr.toNat ≠ (1048504 : UInt32).toNat := by
    norm_num
    omega
  have hhi1 : inputPtr.toNat ≠ (1048504 : UInt32).toNat + 1 := by
    norm_num
    omega
  have hhi2 : inputPtr.toNat ≠ (1048504 : UInt32).toNat + 2 := by
    norm_num
    omega
  have hhi3 : inputPtr.toNat ≠ (1048504 : UInt32).toNat + 3 := by
    norm_num
    omega
  have hhi4 : inputPtr.toNat ≠ (1048508 : UInt32).toNat := by
    norm_num
    omega
  have hhi5 : inputPtr.toNat ≠ (1048508 : UInt32).toNat + 1 := by
    norm_num
    omega
  have hhi6 : inputPtr.toNat ≠ (1048508 : UInt32).toNat + 2 := by
    norm_num
    omega
  have hhi7 : inputPtr.toNat ≠ (1048508 : UInt32).toNat + 3 := by
    norm_num
    omega
  have hlo0 : (inputPtr + 1).toNat ≠ (1048504 : UInt32).toNat := by
    rw [hinput1]
    norm_num
    omega
  have hlo1 : (inputPtr + 1).toNat ≠ (1048504 : UInt32).toNat + 1 := by
    rw [hinput1]
    norm_num
    omega
  have hlo2 : (inputPtr + 1).toNat ≠ (1048504 : UInt32).toNat + 2 := by
    rw [hinput1]
    norm_num
    omega
  have hlo3 : (inputPtr + 1).toNat ≠ (1048504 : UInt32).toNat + 3 := by
    rw [hinput1]
    norm_num
    omega
  have hlo4 : (inputPtr + 1).toNat ≠ (1048508 : UInt32).toNat := by
    rw [hinput1]
    norm_num
    omega
  have hlo5 : (inputPtr + 1).toNat ≠ (1048508 : UInt32).toNat + 1 := by
    rw [hinput1]
    norm_num
    omega
  have hlo6 : (inputPtr + 1).toNat ≠ (1048508 : UInt32).toNat + 2 := by
    rw [hinput1]
    norm_num
    omega
  have hlo7 : (inputPtr + 1).toNat ≠ (1048508 : UInt32).toNat + 3 := by
    rw [hinput1]
    norm_num
    omega
  apply Reaches.prepend (Step.call (fn := func0Def)
    (by simp [hmod]; decide)
    (by simp [hmod]; rfl))
  simp [func0Def, Function.toLocals, Function.numParams, ValueType.zero, func0]
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load32 (by change 1048512 ≤ _; omega))
  apply Reaches.prepend (Step.localTee rfl)
  have hlen0 : len ≠ 0 := by
    intro hz
    have hnat := congrArg UInt32.toNat hz
    change (store.wasm.mem.read32 1048508).toNat = 0 at hnat
    norm_num at hnat
    omega
  apply Reaches.prepend (Step.brIf hlen0 rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load32 (by change 1048524 ≤ _; omega))
  apply Reaches.prepend (Step.localSet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load32 (by change 1048516 ≤ _; omega))
  change store.wasm.mem.read32 (loopIterator + 8) = 2 at hchunkRead
  rw [hchunkRead]
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.ltU rfl)
  apply Reaches.prepend (Step.select (selected := .i32 2) (by
    simp
    intro hle
    apply UInt32.toNat_inj.mp
    have hleNat := UInt32.le_iff_toNat_le.mp hle
    change (store.wasm.mem.read32 1048508).toNat ≤ (2 : Nat) at hleNat
    change (2 : Nat) = (store.wasm.mem.read32 1048508).toNat
    omega))
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend Step.sub
  apply Reaches.prepend (Step.store32 (by change 1048512 ≤ _; omega))
  rw [setMemory_eq]
  dsimp only
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load32 (by
    change 1048508 ≤ store.wasm.mem.pages * 65536
    omega))
  simp only [UInt32.add_zero]
  rw [Mem.read32_write32_disjoint _ (loopIterator + 4) loopIterator _
    (by decide)]
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.add
  apply Reaches.prepend (Step.store32 (by
    change 1048508 ≤ store.wasm.mem.pages * 65536
    omega))
  rw [setMemory_eq]
  dsimp only
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  simp
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.eqz rfl)
  simp
  apply Reaches.prepend Step.brIfZero
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load32 (by
    change 1048520 ≤ store.wasm.mem.pages * 65536
    omega))
  rw [Mem.read32_write32_disjoint _ loopIterator (loopIterator + 12) _
    (by decide)]
  norm_num
  rw [Mem.read32_write32_disjoint _ (1048508 : UInt32)
    (loopIterator + 12) _ (by decide)]
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.shl
  apply Reaches.prepend (Step.localSet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load8U (by
    change inputPtr.toNat + 1 ≤ store.wasm.mem.pages * 65536
    exact Nat.le_trans (by omega) hinputA))
  simp only [Mem.read8, Mem.write32]
  simp only [UInt32.add_zero]
  simp only [show (1048504 : UInt32).toNat = 1048504 by decide,
    show (1048508 : UInt32).toNat = 1048508 by decide]
  change (store.wasm.mem.read32 1048504).toNat ≠ 1048504 at hhi0
  change (store.wasm.mem.read32 1048504).toNat ≠ 1048505 at hhi1
  change (store.wasm.mem.read32 1048504).toNat ≠ 1048506 at hhi2
  change (store.wasm.mem.read32 1048504).toNat ≠ 1048507 at hhi3
  change (store.wasm.mem.read32 1048504).toNat ≠ 1048508 at hhi4
  change (store.wasm.mem.read32 1048504).toNat ≠ 1048509 at hhi5
  change (store.wasm.mem.read32 1048504).toNat ≠ 1048510 at hhi6
  change (store.wasm.mem.read32 1048504).toNat ≠ 1048511 at hhi7
  rw [if_neg hhi0, if_neg hhi1, if_neg hhi2, if_neg hhi3,
    if_neg hhi4, if_neg hhi5, if_neg hhi6, if_neg hhi7]
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.add
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.and
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.ltU rfl)
  change ¬ (4294967231 +
    (store.wasm.mem.bytes (store.wasm.mem.read32 1048504).toNat).toUInt32 &&&
      255 < 6) at hhiUpper
  change ¬ (4294967199 +
    (store.wasm.mem.bytes (store.wasm.mem.read32 1048504).toNat).toUInt32 &&&
      255 < 6) at hhiLower
  change ¬ (4294967248 +
    (store.wasm.mem.bytes (store.wasm.mem.read32 1048504).toNat).toUInt32 &&&
      255 < 10) at hhiDigit
  simp [hhiUpper]
  apply Reaches.prepend Step.brIfZero
  apply Reaches.prepend Step.block
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.add
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.and
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.ltU rfl)
  simp [hhiLower]
  apply Reaches.prepend Step.brIfZero
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localSet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.add
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.and
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.ltU rfl)
  simp [hhiDigit]
  apply Reaches.prepend Step.brIfZero
  apply Reaches.prepend (Step.br rfl)
  simp
  change store.wasm.mem.read32 1048520 = 1048464 at herrorRead
  rw [herrorRead]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.and
  apply Reaches.prepend (Step.store32 (by
    change 1048468 ≤ store.wasm.mem.pages * 65536
    omega))
  rw [setMemory_eq]
  dsimp only
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.and
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.and
  apply Reaches.prepend Step.or
  apply Reaches.prepend (Step.store32 (by
    change 1048472 ≤ store.wasm.mem.pages * 65536
    omega))
  rw [setMemory_eq]
  dsimp only
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.localSet rfl)
  apply Reaches.prepend (Step.br rfl)
  simp
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.add
  apply Reaches.prepend (Step.store32 (by
    change 1048520 ≤ store.wasm.mem.pages * 65536
    omega))
  rw [setMemory_eq]
  dsimp only
  apply Reaches.prepend (Step.exitControl rfl)
  simp
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.store8 (by
    change 1048442 ≤ store.wasm.mem.pages * 65536
    omega))
  rw [setMemory_eq]
  dsimp only
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.and
  simp
  apply Reaches.prepend (Step.store8 (by
    change 1048441 ≤ store.wasm.mem.pages * 65536
    omega))
  rw [setMemory_eq]
  dsimp only
  apply Reaches.prepend (Step.returnFromCallFallthrough (by simp))
  simp [decodeLoopPairInvalidStore, decodeLoopPairBaseStore, Mem.write32]
  exact ⟨[], .refl _⟩

end Submission.HexDecodeStdio
