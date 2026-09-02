import HexDecodeStdio.DecodeIteratorInvalidLow
import HexDecodeStdio.StoreFacts
import HexDecodeStdio.HexMath

namespace Project.HexDecodeStdio

open Wasm Project.HexStdio Project.HexStdio.Spec
open Wasm.SmallStep

/-! Concrete operational summaries for the two-byte iterator. -/

@[simp] abbrev coreFrame : UInt32 := 1048432
@[simp] abbrev corePairOut : UInt32 := 1048456
@[simp] abbrev coreError : UInt32 := 1048464
@[simp] abbrev coreIterator : UInt32 := 1048472

def decodePairBaseStore (store : MachineStore Universal.State)
    (inputPtr len chunkIndex : UInt32) : MachineStore Universal.State :=
  let mem1 := store.wasm.mem.write32 (coreIterator + 4) (len - 2)
  let mem2 := mem1.write32 coreIterator (2 + inputPtr)
  { store with wasm := { store.wasm with
      mem := mem2.write32 (coreIterator + 12) (1 + chunkIndex) } }

def decodePairValidStore (store : MachineStore Universal.State)
    (inputPtr len chunkIndex : UInt32) (byte : UInt8) :
    MachineStore Universal.State :=
  let base := decodePairBaseStore store inputPtr len chunkIndex
  let mem1 := base.wasm.mem.write8 (corePairOut + 1) byte
  { base with wasm := { base.wasm with mem := mem1.write8 corePairOut 1 } }

def decodePairInvalidStore (store : MachineStore Universal.State)
    (inputPtr len chunkIndex : UInt32) (bad : UInt8) (index : UInt32) :
    MachineStore Universal.State :=
  let mem1 := store.wasm.mem.write32 (coreIterator + 4) (len - 2)
  let mem2 := mem1.write32 coreIterator (2 + inputPtr)
  let mem3 := mem2.write32 coreError (bad.toUInt32 &&& 255)
  let mem4 := mem3.write32 (coreError + 4) index
  let mem5 := mem4.write32 (coreIterator + 12) (1 + chunkIndex)
  let mem6 := mem5.write8 (corePairOut + 1) bad
  { store with wasm := { store.wasm with mem := mem6.write8 corePairOut 0 } }

def decodePairEmptyStore (store : MachineStore Universal.State) :
    MachineStore Universal.State :=
  let mem1 := store.wasm.mem.write8 (corePairOut + 1) 0
  { store with wasm := { store.wasm with mem := mem1.write8 corePairOut 0 } }

def pairPreparedStore (store : MachineStore Universal.State)
    (inputPtr len chunkIndex : UInt32) (hi lo oldTag oldPayload : UInt8) :
    MachineStore Universal.State :=
  let mem0 := store.wasm.mem.write32 (coreIterator + 4) len
  let mem1 := mem0.write32 (coreIterator + 16) coreError
  let mem2 := mem1.write32 (coreIterator + 8) 2
  let mem3 := mem2.write32 coreIterator inputPtr
  let mem4 := mem3.write32 (coreIterator + 12) chunkIndex
  let mem5 := mem4.write32 coreError 1114114
  let mem6 := mem5.write32 (coreError + 4) 0
  let mem7 := mem6.write8 inputPtr hi
  let mem8 := mem7.write8 (inputPtr + 1) lo
  let mem9 := mem8.write8 corePairOut oldTag
  { store with wasm := { store.wasm with
      mem := mem9.write8 (corePairOut + 1) oldPayload } }

def pairStandaloneConfig (store : MachineStore Universal.State) :
    Config Universal.State :=
  ⟨.running ⟨⟨[], [], [.i32 coreIterator, .i32 corePairOut]⟩,
    [.call 3], 0, [], [], []⟩, store⟩

def pairStandaloneReturn (store : MachineStore Universal.State) :
    Config Universal.State :=
  ⟨.running ⟨⟨[], [], []⟩, [], 0, [], [], []⟩, store⟩

def keep32 (value : UInt32) : UInt32 := value

theorem core_addresses :
    corePairOut + 1 = 1048457 ∧ coreIterator + 4 = 1048476 ∧
    coreIterator + 8 = 1048480 ∧ coreIterator + 12 = 1048484 ∧
    coreIterator + 16 = 1048488 ∧ coreError + 4 = 1048468 := by
  decide

set_option maxRecDepth 100000 in
theorem decodePair_empty_reaches
    (store : MachineStore Universal.State)
    (hmod : store.runtime.currentModule = «module»)
    (hpages : 17 ≤ store.wasm.mem.pages)
    (hlenRead : store.wasm.mem.read32 (coreIterator + 4) = 0)
    (callerParams callerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame) :
    Reaches
      ⟨.running ⟨⟨callerParams, callerLocalValues,
          .i32 coreIterator :: .i32 corePairOut :: stack⟩,
        .call 3 :: code, arity, remainder, controls, calls⟩, store⟩
      ⟨.running ⟨⟨callerParams, callerLocalValues, stack⟩,
        code, arity, remainder, controls, calls⟩,
        decodePairEmptyStore store⟩ := by
  apply Reaches.prepend (Step.call (fn := func0Def)
    (by simp [hmod]; decide) (by simp [hmod]; rfl))
  simp [func0Def, Function.toLocals, Function.numParams, ValueType.zero, func0]
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load32 (by
    change 1048480 ≤ store.wasm.mem.pages * 65536
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
  simp [decodePairEmptyStore]
  exact ⟨[], .refl _⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem decodePair_valid_reaches
    (store : MachineStore Universal.State)
    (inputPtr errorPtr len chunkIndex : UInt32) (hi lo : UInt8)
    (hmod : store.runtime.currentModule = «module»)
    (hpages : 17 ≤ store.wasm.mem.pages)
    (hpagesMax : store.wasm.mem.pages ≤ 65536)
    (hinput : inputPtr.toNat + 2 ≤ store.wasm.mem.pages * 65536)
    (hinputLower : 1054000 ≤ inputPtr.toNat)
    (hlen : 2 ≤ len.toNat)
    (hlenRead : store.wasm.mem.read32 (coreIterator + 4) = len)
    (herrorRead : store.wasm.mem.read32 (coreIterator + 16) = errorPtr)
    (hchunkRead : store.wasm.mem.read32 (coreIterator + 8) = 2)
    (hptrRead : store.wasm.mem.read32 coreIterator = inputPtr)
    (hindexRead : store.wasm.mem.read32 (coreIterator + 12) = chunkIndex)
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
          .i32 coreIterator :: .i32 corePairOut :: stack⟩,
        .call 3 :: code, arity, remainder, controls, calls⟩, store⟩
      ⟨.running ⟨⟨callerParams, callerLocalValues, stack⟩,
        code, arity, remainder, controls, calls⟩,
        decodePairValidStore store inputPtr len chunkIndex
          ((loRoute.nibble lo |||
            (hiRoute.nibble hi <<< (4 : UInt32))).toUInt8)⟩ := by
  subst len
  subst errorPtr
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
    simp only [HexRoute.valid, Mem.read8, inputPtr, coreIterator] at hlo
    rw [← hinput1Mod'] at hlo
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
      simp [decodePairValidStore, decodePairBaseStore,
        HexRoute.nibble, Mem.write32]
      exact ⟨[], .refl _⟩

end Project.HexDecodeStdio
