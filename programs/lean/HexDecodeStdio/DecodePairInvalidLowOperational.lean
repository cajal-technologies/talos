import HexDecodeStdio.DecodePairInvalidOperational
import HexDecodeStdio.HexMath

namespace Project.HexDecodeStdio

open Wasm Project.HexStdio Project.HexStdio.Spec
open Wasm.SmallStep

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem decodePair_invalid_low_reaches
    (store : MachineStore Universal.State)
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
    (hiRoute : HexRoute)
    (hhi : hiRoute.valid hi)
    (hlo : hexValue lo = none)
    (callerParams callerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame) :
    Reaches
      ⟨.running ⟨⟨callerParams, callerLocalValues,
          .i32 coreIterator :: .i32 corePairOut :: stack⟩,
        .call 3 :: code, arity, remainder, controls, calls⟩, store⟩
      ⟨.running ⟨⟨callerParams, callerLocalValues, stack⟩,
        code, arity, remainder, controls, calls⟩,
        decodePairInvalidStore store inputPtr len chunkIndex lo
          ((((chunkIndex <<< (1 : UInt32)) ||| 1) &&& 255) |||
            (chunkIndex <<< (1 : UInt32)) &&& 4294967040)⟩ := by
  subst len
  subst chunkIndex
  subst inputPtr
  subst hi
  subst lo
  let len := store.wasm.mem.read32 (coreIterator + 4)
  let errorPtr := store.wasm.mem.read32 (coreIterator + 16)
  let chunkIndex := store.wasm.mem.read32 (coreIterator + 12)
  let inputPtr := store.wasm.mem.read32 coreIterator
  let hi := store.wasm.mem.read8 inputPtr
  let lo := store.wasm.mem.read8 (inputPtr + 1)
  obtain ⟨hloUpper, hloLower, hloDigit⟩ :=
    Project.HexDecodeStdio.hexValue_none_tests lo hlo
  have hlenA : 2 ≤ len.toNat := by simpa only [len] using hlen
  change 2 ≤ (store.wasm.mem.read32 1048476).toNat at hlenA
  have hinputA : inputPtr.toNat + 2 ≤ store.wasm.mem.pages * 65536 := by
    simpa only [inputPtr] using hinput
  have hinputLowerA : 1054000 ≤ inputPtr.toNat := by
    simpa only [inputPtr] using hinputLower
  norm_num at hlen
  have hiterNat : (1048472 : UInt32).toNat = 1048472 := by decide
  have hlenAddrNat : (1048476 : UInt32).toNat = 1048476 := by decide
  have hframe : 1048492 ≤ store.wasm.mem.pages * 65536 := by omega
  have hinput1 : (inputPtr + 1).toNat = inputPtr.toNat + 1 := by
    rw [UInt32.toNat_add]
    simp only [UInt32.toNat_ofNat]
    rw [Nat.mod_eq_of_lt]
    omega
  have hinput1Mod :
      (inputPtr.toNat + (1 : UInt32).toNat) % 4294967296 =
        (inputPtr + 1).toNat := by
    exact (UInt32.toNat_add inputPtr 1).symm
  have hhi0 : inputPtr.toNat ≠ (1048472 : UInt32).toNat := by
    norm_num
    omega
  have hhi1 : inputPtr.toNat ≠ (1048472 : UInt32).toNat + 1 := by
    norm_num
    omega
  have hhi2 : inputPtr.toNat ≠ (1048472 : UInt32).toNat + 2 := by
    norm_num
    omega
  have hhi3 : inputPtr.toNat ≠ (1048472 : UInt32).toNat + 3 := by
    norm_num
    omega
  have hhi4 : inputPtr.toNat ≠ (1048476 : UInt32).toNat := by
    norm_num
    omega
  have hhi5 : inputPtr.toNat ≠ (1048476 : UInt32).toNat + 1 := by
    norm_num
    omega
  have hhi6 : inputPtr.toNat ≠ (1048476 : UInt32).toNat + 2 := by
    norm_num
    omega
  have hhi7 : inputPtr.toNat ≠ (1048476 : UInt32).toNat + 3 := by
    norm_num
    omega
  have hlo0 : (inputPtr + 1).toNat ≠ (1048472 : UInt32).toNat := by
    rw [hinput1]
    norm_num
    omega
  have hlo1 : (inputPtr + 1).toNat ≠ (1048472 : UInt32).toNat + 1 := by
    rw [hinput1]
    norm_num
    omega
  have hlo2 : (inputPtr + 1).toNat ≠ (1048472 : UInt32).toNat + 2 := by
    rw [hinput1]
    norm_num
    omega
  have hlo3 : (inputPtr + 1).toNat ≠ (1048472 : UInt32).toNat + 3 := by
    rw [hinput1]
    norm_num
    omega
  have hlo4 : (inputPtr + 1).toNat ≠ (1048476 : UInt32).toNat := by
    rw [hinput1]
    norm_num
    omega
  have hlo5 : (inputPtr + 1).toNat ≠ (1048476 : UInt32).toNat + 1 := by
    rw [hinput1]
    norm_num
    omega
  have hlo6 : (inputPtr + 1).toNat ≠ (1048476 : UInt32).toNat + 2 := by
    rw [hinput1]
    norm_num
    omega
  have hlo7 : (inputPtr + 1).toNat ≠ (1048476 : UInt32).toNat + 3 := by
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
  apply Reaches.prepend (Step.load32 (by change 1048480 ≤ _; omega))
  apply Reaches.prepend (Step.localTee rfl)
  have hlen0 : len ≠ 0 := by
    intro hz
    have hnat := congrArg UInt32.toNat hz
    change (store.wasm.mem.read32 1048476).toNat = 0 at hnat
    norm_num at hnat
    omega
  apply Reaches.prepend (Step.brIf hlen0 rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load32 (by change 1048492 ≤ _; omega))
  apply Reaches.prepend (Step.localSet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load32 (by change 1048484 ≤ _; omega))
  change store.wasm.mem.read32 (coreIterator + 8) = 2 at hchunkRead
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
    change (store.wasm.mem.read32 1048476).toNat ≤ (2 : Nat) at hleNat
    change (2 : Nat) = (store.wasm.mem.read32 1048476).toNat
    omega))
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend Step.sub
  apply Reaches.prepend (Step.store32 (by change 1048480 ≤ _; omega))
  rw [setMemory_eq]
  dsimp only
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load32 (by
    change 1048476 ≤ store.wasm.mem.pages * 65536
    omega))
  simp only [UInt32.add_zero]
  rw [Mem.read32_write32_disjoint _ (coreIterator + 4) coreIterator _
    (by decide)]
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.add
  apply Reaches.prepend (Step.store32 (by
    change 1048476 ≤ store.wasm.mem.pages * 65536
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
    change 1048488 ≤ store.wasm.mem.pages * 65536
    omega))
  rw [Mem.read32_write32_disjoint _ coreIterator (coreIterator + 12) _
    (by decide)]
  norm_num
  rw [Mem.read32_write32_disjoint _ (1048476 : UInt32)
    (coreIterator + 12) _ (by decide)]
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
  simp only [show (1048472 : UInt32).toNat = 1048472 by decide,
    show (1048476 : UInt32).toNat = 1048476 by decide]
  change (store.wasm.mem.read32 1048472).toNat ≠ 1048472 at hhi0
  change (store.wasm.mem.read32 1048472).toNat ≠ 1048473 at hhi1
  change (store.wasm.mem.read32 1048472).toNat ≠ 1048474 at hhi2
  change (store.wasm.mem.read32 1048472).toNat ≠ 1048475 at hhi3
  change (store.wasm.mem.read32 1048472).toNat ≠ 1048476 at hhi4
  change (store.wasm.mem.read32 1048472).toNat ≠ 1048477 at hhi5
  change (store.wasm.mem.read32 1048472).toNat ≠ 1048478 at hhi6
  change (store.wasm.mem.read32 1048472).toNat ≠ 1048479 at hhi7
  rw [if_neg hhi0, if_neg hhi1, if_neg hhi2, if_neg hhi3,
    if_neg hhi4, if_neg hhi5, if_neg hhi6, if_neg hhi7]
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.add
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.and
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.ltU rfl)
  cases hiRoute <;> simp only [HexRoute.valid, Mem.read8, inputPtr,
      coreIterator] at hhi <;>
    first
    | (rcases hhi with ⟨hhiUpper, hhiLower, hhiDigit⟩
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
       apply Reaches.prepend (Step.brIf (by decide) rfl)
       simp)
    | (rcases hhi with ⟨hhiUpper, hhiLower⟩
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
       apply Reaches.prepend (Step.brIf (by decide) rfl)
       simp
       apply Reaches.prepend (Step.localGet rfl)
       apply Reaches.prepend Step.const
       apply Reaches.prepend Step.add
       apply Reaches.prepend (Step.localSet rfl)
       apply Reaches.prepend (Step.br rfl))
    | (simp [hhi]
       apply Reaches.prepend (Step.brIf (by decide) rfl)
       simp
       apply Reaches.prepend (Step.localGet rfl)
       apply Reaches.prepend Step.const
       apply Reaches.prepend Step.add
       apply Reaches.prepend (Step.localSet rfl)
       apply Reaches.prepend (Step.exitControl rfl)
       simp)
  all_goals
    apply Reaches.prepend (Step.localGet rfl)
    apply Reaches.prepend Step.const
    apply Reaches.prepend (Step.eq rfl)
    simp
    apply Reaches.prepend Step.brIfZero
    apply Reaches.prepend (Step.localGet rfl)
    apply Reaches.prepend (Step.load8U (by
      change inputPtr.toNat + 1 + 1 ≤ store.wasm.mem.pages * 65536
      exact hinputA))
    simp only [Mem.read8, Mem.write32]
    have hinput1Mod' :
        ((store.wasm.mem.read32 1048472).toNat + 1) % 4294967296 =
          (store.wasm.mem.read32 1048472 + 1).toNat := by
      simpa only [inputPtr, coreIterator, UInt32.toNat_ofNat] using hinput1Mod
    simp only [lo, Mem.read8, inputPtr, coreIterator] at hloUpper hloLower hloDigit
    rw [← hinput1Mod'] at hloUpper hloLower hloDigit
    rw [hinput1Mod']
    change (store.wasm.mem.read32 1048472 + 1).toNat ≠ 1048472 at hlo0
    change (store.wasm.mem.read32 1048472 + 1).toNat ≠ 1048473 at hlo1
    change (store.wasm.mem.read32 1048472 + 1).toNat ≠ 1048474 at hlo2
    change (store.wasm.mem.read32 1048472 + 1).toNat ≠ 1048475 at hlo3
    change (store.wasm.mem.read32 1048472 + 1).toNat ≠ 1048476 at hlo4
    change (store.wasm.mem.read32 1048472 + 1).toNat ≠ 1048477 at hlo5
    change (store.wasm.mem.read32 1048472 + 1).toNat ≠ 1048478 at hlo6
    change (store.wasm.mem.read32 1048472 + 1).toNat ≠ 1048479 at hlo7
    rw [if_neg hlo0, if_neg hlo1, if_neg hlo2, if_neg hlo3,
      if_neg hlo4, if_neg hlo5, if_neg hlo6, if_neg hlo7]
    apply Reaches.prepend (Step.localTee rfl)
    apply Reaches.prepend Step.const
    apply Reaches.prepend Step.add
    apply Reaches.prepend Step.const
    apply Reaches.prepend Step.and
    apply Reaches.prepend Step.const
    apply Reaches.prepend (Step.ltU rfl)
    simp [hloUpper]
    apply Reaches.prepend Step.brIfZero
    apply Reaches.prepend (Step.localGet rfl)
    apply Reaches.prepend Step.const
    apply Reaches.prepend Step.add
    apply Reaches.prepend Step.const
    apply Reaches.prepend Step.and
    apply Reaches.prepend Step.const
    apply Reaches.prepend (Step.ltU rfl)
    simp [hloLower]
    apply Reaches.prepend Step.brIfZero
    apply Reaches.prepend (Step.localGet rfl)
    apply Reaches.prepend Step.const
    apply Reaches.prepend Step.add
    apply Reaches.prepend (Step.localTee rfl)
    apply Reaches.prepend Step.const
    apply Reaches.prepend Step.and
    apply Reaches.prepend Step.const
    apply Reaches.prepend (Step.ltU rfl)
    simp [hloDigit]
    apply Reaches.prepend Step.brIfZero
    apply Reaches.prepend (Step.localGet rfl)
    apply Reaches.prepend Step.const
    apply Reaches.prepend Step.or
    apply Reaches.prepend (Step.localSet rfl)
    apply Reaches.prepend (Step.exitControl rfl)
    simp
    change store.wasm.mem.read32 1048488 = 1048464 at herrorRead
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
      change 1048488 ≤ store.wasm.mem.pages * 65536
      omega))
    rw [setMemory_eq]
    dsimp only
    apply Reaches.prepend (Step.exitControl rfl)
    simp
    apply Reaches.prepend (Step.localGet rfl)
    apply Reaches.prepend (Step.localGet rfl)
    apply Reaches.prepend (Step.store8 (by
      change 1048458 ≤ store.wasm.mem.pages * 65536
      omega))
    rw [setMemory_eq]
    dsimp only
    apply Reaches.prepend (Step.localGet rfl)
    apply Reaches.prepend (Step.localGet rfl)
    apply Reaches.prepend Step.const
    apply Reaches.prepend Step.and
    simp
    apply Reaches.prepend (Step.store8 (by
      change 1048457 ≤ store.wasm.mem.pages * 65536
      omega))
    rw [setMemory_eq]
    dsimp only
    apply Reaches.prepend (Step.returnFromCallFallthrough (by simp))
    simp [decodePairInvalidStore, Mem.write32]
    exact ⟨[], .refl _⟩

end Project.HexDecodeStdio
