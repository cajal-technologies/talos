import HexDecodeStdio.DecodeIteratorInvalidLow
import HexDecodeStdio.StoreFacts
import HexDecodeStdio.HexMath

namespace Project.HexDecodeStdio

open Wasm Project.HexStdio Project.HexStdio.Spec
open Wasm.SmallStep

/-! Concrete operational summaries for the two-byte iterator. -/

@[simp] abbrev secondCoreFrame : UInt32 := 1048432
@[simp] abbrev secondPairOut : UInt32 := 1048448
@[simp] abbrev secondError : UInt32 := 1048464
@[simp] abbrev secondIterator : UInt32 := 1048504

def decodeSecondPairBaseStore (store : MachineStore Universal.State)
    (inputPtr len chunkIndex : UInt32) : MachineStore Universal.State :=
  let mem1 := store.wasm.mem.write32 (secondIterator + 4) (len - 2)
  let mem2 := mem1.write32 secondIterator (2 + inputPtr)
  { store with wasm := { store.wasm with
      mem := mem2.write32 (secondIterator + 12) (1 + chunkIndex) } }

def decodeSecondPairValidStore (store : MachineStore Universal.State)
    (inputPtr len chunkIndex : UInt32) (byte : UInt8) :
    MachineStore Universal.State :=
  let base := decodeSecondPairBaseStore store inputPtr len chunkIndex
  let mem1 := base.wasm.mem.write8 (secondPairOut + 1) byte
  { base with wasm := { base.wasm with mem := mem1.write8 secondPairOut 1 } }

def decodeSecondPairInvalidStore (store : MachineStore Universal.State)
    (inputPtr len chunkIndex : UInt32) (bad : UInt8) (index : UInt32) :
    MachineStore Universal.State :=
  let mem1 := store.wasm.mem.write32 (secondIterator + 4) (len - 2)
  let mem2 := mem1.write32 secondIterator (2 + inputPtr)
  let mem3 := mem2.write32 secondError (bad.toUInt32 &&& 255)
  let mem4 := mem3.write32 (secondError + 4) index
  let mem5 := mem4.write32 (secondIterator + 12) (1 + chunkIndex)
  let mem6 := mem5.write8 (secondPairOut + 1) bad
  { store with wasm := { store.wasm with mem := mem6.write8 secondPairOut 0 } }

def decodeSecondPairEmptyStore (store : MachineStore Universal.State) :
    MachineStore Universal.State :=
  let mem1 := store.wasm.mem.write8 (secondPairOut + 1) 0
  { store with wasm := { store.wasm with mem := mem1.write8 secondPairOut 0 } }

def secondPairPreparedStore (store : MachineStore Universal.State)
    (inputPtr len chunkIndex : UInt32) (hi lo oldTag oldPayload : UInt8) :
    MachineStore Universal.State :=
  let mem0 := store.wasm.mem.write32 (secondIterator + 4) len
  let mem1 := mem0.write32 (secondIterator + 16) secondError
  let mem2 := mem1.write32 (secondIterator + 8) 2
  let mem3 := mem2.write32 secondIterator inputPtr
  let mem4 := mem3.write32 (secondIterator + 12) chunkIndex
  let mem5 := mem4.write32 secondError 1114114
  let mem6 := mem5.write32 (secondError + 4) 0
  let mem7 := mem6.write8 inputPtr hi
  let mem8 := mem7.write8 (inputPtr + 1) lo
  let mem9 := mem8.write8 secondPairOut oldTag
  { store with wasm := { store.wasm with
      mem := mem9.write8 (secondPairOut + 1) oldPayload } }

def secondPairStandaloneConfig (store : MachineStore Universal.State) :
    Config Universal.State :=
  ⟨.running ⟨⟨[], [], [.i32 secondIterator, .i32 secondPairOut]⟩,
    [.call 3], 0, [], [], []⟩, store⟩

def secondPairStandaloneReturn (store : MachineStore Universal.State) :
    Config Universal.State :=
  ⟨.running ⟨⟨[], [], []⟩, [], 0, [], [], []⟩, store⟩

def secondKeep32 (value : UInt32) : UInt32 := value

theorem second_core_addresses :
    secondPairOut + 1 = 1048449 ∧ secondIterator + 4 = 1048508 ∧
    secondIterator + 8 = 1048512 ∧ secondIterator + 12 = 1048516 ∧
    secondIterator + 16 = 1048520 ∧ secondError + 4 = 1048468 := by
  decide

set_option maxRecDepth 100000 in
theorem decodeSecondPair_empty_reaches
    (store : MachineStore Universal.State)
    (hmod : store.runtime.currentModule = «module»)
    (hpages : 17 ≤ store.wasm.mem.pages)
    (hlenRead : store.wasm.mem.read32 (secondIterator + 4) = 0)
    (callerParams callerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame) :
    Reaches
      ⟨.running ⟨⟨callerParams, callerLocalValues,
          .i32 secondIterator :: .i32 secondPairOut :: stack⟩,
        .call 3 :: code, arity, remainder, controls, calls⟩, store⟩
      ⟨.running ⟨⟨callerParams, callerLocalValues, stack⟩,
        code, arity, remainder, controls, calls⟩,
        decodeSecondPairEmptyStore store⟩ := by
  apply Reaches.prepend (Step.call (fn := func0Def)
    (by simp [hmod]; decide) (by simp [hmod]; rfl))
  simp [func0Def, Function.toLocals, Function.numParams, ValueType.zero, func0]
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load32 (by
    change 1048512 ≤ store.wasm.mem.pages * 65536
    omega))
  rw [hlenRead]
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend Step.brIfZero
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.localSet rfl)
  apply Reaches.prepend (Step.br rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.store8 (by
    change 1048450 ≤ store.wasm.mem.pages * 65536
    omega))
  rw [setMemory_eq]
  dsimp only
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.and
  simp
  apply Reaches.prepend (Step.store8 (by
    change 1048449 ≤ store.wasm.mem.pages * 65536
    omega))
  rw [setMemory_eq]
  dsimp only
  apply Reaches.prepend (Step.returnFromCallFallthrough (by simp))
  simp [decodeSecondPairEmptyStore]
  exact ⟨[], .refl _⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem decodeSecondPair_valid_reaches
    (store : MachineStore Universal.State)
    (inputPtr errorPtr len chunkIndex : UInt32) (hi lo : UInt8)
    (hmod : store.runtime.currentModule = «module»)
    (hpages : 17 ≤ store.wasm.mem.pages)
    (hpagesMax : store.wasm.mem.pages ≤ 65536)
    (hinput : inputPtr.toNat + 2 ≤ store.wasm.mem.pages * 65536)
    (hinputLower : 1054000 ≤ inputPtr.toNat)
    (hlen : 2 ≤ len.toNat)
    (hlenRead : store.wasm.mem.read32 (secondIterator + 4) = len)
    (herrorRead : store.wasm.mem.read32 (secondIterator + 16) = errorPtr)
    (hchunkRead : store.wasm.mem.read32 (secondIterator + 8) = 2)
    (hptrRead : store.wasm.mem.read32 secondIterator = inputPtr)
    (hindexRead : store.wasm.mem.read32 (secondIterator + 12) = chunkIndex)
    (hhiRead : store.wasm.mem.read8 inputPtr = hi)
    (hloRead : store.wasm.mem.read8 (inputPtr + 1) = lo)
    (hiRoute loRoute : HexRoute)
    (hhi : hiRoute.valid hi)
    (hlo : loRoute.valid lo)
    (callerParams callerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame) :
    Reaches
      ⟨.running ⟨⟨callerParams, callerLocalValues,
          .i32 secondIterator :: .i32 secondPairOut :: stack⟩,
        .call 3 :: code, arity, remainder, controls, calls⟩, store⟩
      ⟨.running ⟨⟨callerParams, callerLocalValues, stack⟩,
        code, arity, remainder, controls, calls⟩,
        decodeSecondPairValidStore store inputPtr len chunkIndex
          ((loRoute.nibble lo |||
            (hiRoute.nibble hi <<< (4 : UInt32))).toUInt8)⟩ := by
  subst len
  subst errorPtr
  subst chunkIndex
  subst inputPtr
  subst hi
  subst lo
  let len := store.wasm.mem.read32 (secondIterator + 4)
  let errorPtr := store.wasm.mem.read32 (secondIterator + 16)
  let chunkIndex := store.wasm.mem.read32 (secondIterator + 12)
  let inputPtr := store.wasm.mem.read32 secondIterator
  let hi := store.wasm.mem.read8 inputPtr
  let lo := store.wasm.mem.read8 (inputPtr + 1)
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
  change store.wasm.mem.read32 (secondIterator + 8) = 2 at hchunkRead
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
  rw [Mem.read32_write32_disjoint _ (secondIterator + 4) secondIterator _
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
  rw [Mem.read32_write32_disjoint _ secondIterator (secondIterator + 12) _
    (by decide)]
  norm_num
  rw [Mem.read32_write32_disjoint _ (1048508 : UInt32)
    (secondIterator + 12) _ (by decide)]
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
  cases hiRoute <;> simp only [HexRoute.valid, Mem.read8, inputPtr,
      secondIterator] at hhi <;>
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
        ((store.wasm.mem.read32 1048504).toNat + 1) % 4294967296 =
          (store.wasm.mem.read32 1048504 + 1).toNat := by
      simpa only [inputPtr, secondIterator, UInt32.toNat_ofNat] using hinput1Mod
    simp only [HexRoute.valid, Mem.read8, inputPtr, secondIterator] at hlo
    rw [← hinput1Mod'] at hlo
    rw [hinput1Mod']
    change (store.wasm.mem.read32 1048504 + 1).toNat ≠ 1048504 at hlo0
    change (store.wasm.mem.read32 1048504 + 1).toNat ≠ 1048505 at hlo1
    change (store.wasm.mem.read32 1048504 + 1).toNat ≠ 1048506 at hlo2
    change (store.wasm.mem.read32 1048504 + 1).toNat ≠ 1048507 at hlo3
    change (store.wasm.mem.read32 1048504 + 1).toNat ≠ 1048508 at hlo4
    change (store.wasm.mem.read32 1048504 + 1).toNat ≠ 1048509 at hlo5
    change (store.wasm.mem.read32 1048504 + 1).toNat ≠ 1048510 at hlo6
    change (store.wasm.mem.read32 1048504 + 1).toNat ≠ 1048511 at hlo7
    rw [if_neg hlo0, if_neg hlo1, if_neg hlo2, if_neg hlo3,
      if_neg hlo4, if_neg hlo5, if_neg hlo6, if_neg hlo7]
    apply Reaches.prepend (Step.localTee rfl)
    apply Reaches.prepend Step.const
    apply Reaches.prepend Step.add
    apply Reaches.prepend Step.const
    apply Reaches.prepend Step.and
    apply Reaches.prepend Step.const
    apply Reaches.prepend (Step.ltU rfl)
    cases loRoute <;> simp only [HexRoute.valid] at hlo <;>
      first
      | (rcases hlo with ⟨hloUpper, hloLower, hloDigit⟩
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
         apply Reaches.prepend (Step.brIf (by decide) rfl)
         simp)
      | (rcases hlo with ⟨hloUpper, hloLower⟩
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
         apply Reaches.prepend (Step.brIf (by decide) rfl)
         simp
         apply Reaches.prepend (Step.localGet rfl)
         apply Reaches.prepend Step.const
         apply Reaches.prepend Step.add
         apply Reaches.prepend (Step.localSet rfl)
         apply Reaches.prepend (Step.br rfl))
      | (simp [hlo]
         apply Reaches.prepend (Step.brIf (by decide) rfl)
         simp
         apply Reaches.prepend (Step.localGet rfl)
         apply Reaches.prepend Step.const
         apply Reaches.prepend Step.add
         apply Reaches.prepend (Step.localSet rfl)
         apply Reaches.prepend (Step.br rfl))
    all_goals
      apply Reaches.prepend (Step.localGet rfl)
      apply Reaches.prepend (Step.localGet rfl)
      apply Reaches.prepend Step.const
      apply Reaches.prepend Step.shl
      apply Reaches.prepend Step.or
      apply Reaches.prepend (Step.localSet rfl)
      apply Reaches.prepend Step.const
      apply Reaches.prepend (Step.localSet rfl)
      apply Reaches.prepend (Step.exitControl rfl)
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
        change 1048450 ≤ store.wasm.mem.pages * 65536
        omega))
      rw [setMemory_eq]
      dsimp only
      apply Reaches.prepend (Step.localGet rfl)
      apply Reaches.prepend (Step.localGet rfl)
      apply Reaches.prepend Step.const
      apply Reaches.prepend Step.and
      simp
      apply Reaches.prepend (Step.store8 (by
        change 1048449 ≤ store.wasm.mem.pages * 65536
        omega))
      rw [setMemory_eq]
      dsimp only
      apply Reaches.prepend (Step.returnFromCallFallthrough (by simp))
      simp [decodeSecondPairValidStore, decodeSecondPairBaseStore,
        HexRoute.nibble, Mem.write32]
      exact ⟨[], .refl _⟩

end Project.HexDecodeStdio
