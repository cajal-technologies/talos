import HexDecodeStdio.DecodePairInvalidLowOperational
import HexDecodeStdio.DecodeAllocatorFacts
import HexDecodeStdio.ReadToEndInitial

namespace Project.HexDecodeStdio

open Wasm Project.HexStdio Project.HexStdio.Spec
open Wasm.SmallStep

abbrev decodePostReadLocals (data : UInt32) : List Value :=
  [.i32 decodeStack, .i32 data, .i32 0, .i32 0, .i32 0, .i32 0]

@[simp] abbrev decodeResultOut : UInt32 := decodeStack + 24

def decodeAfterCore : Program := decodeAfterRead.drop 9

theorem decodeAfterRead_core_split :
    decodeAfterRead =
      [.localGet 0, .const 24, .add, .localGet 0, .load32 40,
        .localTee 1, .localGet 0, .load32 44, .call 8] ++
      decodeAfterCore := by
  rfl

def decodeCoreCallConfig (store : MachineStore Universal.State)
    (data len : UInt32) : Config Universal.State :=
  ⟨.running ⟨⟨[], decodePostReadLocals data,
      [.i32 len, .i32 data, .i32 decodeResultOut]⟩,
    [.call 8] ++ decodeAfterCore, 0, [], [], []⟩, store⟩

def decodeAfterCoreConfig (store : MachineStore Universal.State)
    (data : UInt32) : Config Universal.State :=
  ⟨.running ⟨⟨[], decodePostReadLocals data, []⟩,
    decodeAfterCore, 0, [], [], []⟩, store⟩

def decodeOddStore (store : MachineStore Universal.State) :
    MachineStore Universal.State :=
  let mem := store.wasm.mem.write64 decodeResultOut 4785076751564800
  let globals := { globals :=
    store.wasm.globals.globals.set 0 (.i32 decodeStack) }
  { store with wasm := { store.wasm with mem := mem, globals := globals } }

theorem decode_after_read_to_core_call
    (store : MachineStore Universal.State) (data len : UInt32)
    (hdata : store.wasm.mem.read32 (decodeStack + 40) = data)
    (hlen : store.wasm.mem.read32 (decodeStack + 44) = len)
    (hbound : decodeStack.toNat + 48 ≤ store.wasm.mem.pages * 65536) :
    Reaches (decodeAfterReadConfig store) (decodeCoreCallConfig store data len) := by
  simp only [decodeAfterReadConfig]
  rw [decodeAfterRead_core_split]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.add
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load32 (by
    change decodeStack.toNat + 40 + 4 ≤ _
    omega))
  rw [hdata]
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load32 (by
    change decodeStack.toNat + 44 + 4 ≤ _
    exact hbound))
  rw [hlen]
  simp [decodeAfterReadConfig, decodeCoreCallConfig, decodePostReadLocals]
  exact ⟨[], .refl _⟩

set_option maxRecDepth 100000 in
theorem decode_core_odd_reaches
    (store : MachineStore Universal.State) (data len : UInt32)
    (hmod : store.runtime.currentModule = «module»)
    (hglobal : globalAt? store 0 = some (.i32 decodeStack))
    (hpages : 17 ≤ store.wasm.mem.pages)
    (hodd : len &&& (1 : UInt32) ≠ 0) :
    Reaches (decodeCoreCallConfig store data len)
      (decodeAfterCoreConfig (decodeOddStore store) data) := by
  have hzero : 0 < store.wasm.globals.globals.length := by
    apply (getElem?_eq_some_iff.mp (show
      store.wasm.globals.globals[0]? = some (.i32 decodeStack) by
        simpa only [globalAt?, canonicalGlobalIndex_zero] using hglobal)).1
  apply Reaches.prepend (Step.call (fn := func5Def)
    (by simp [decodeCoreCallConfig, hmod]; decide)
    (by simp [decodeCoreCallConfig, hmod]; rfl))
  simp [func5Def, Function.toLocals, Function.numParams, ValueType.zero, func5]
  apply Reaches.prepend (Step.globalGet hglobal)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.sub
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend (Step.globalSet (by simp [hglobal]))
  rw [setGlobal_zero_eq]
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.localSet rfl)
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.and
  apply Reaches.prepend (Step.brIf hodd rfl)
  simp
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.constI64
  apply Reaches.prepend (Step.store64 rfl (by
    change 1048560 ≤ store.wasm.mem.pages * 65536
    omega))
  rw [setMemory_eq]
  dsimp only
  apply Reaches.prepend (Step.exitControl rfl)
  simp
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.add
  apply Reaches.prepend (Step.globalSet (by
    simpa [globalAt?] using hzero))
  rw [setGlobal_zero_eq]
  apply Reaches.prepend (Step.returnFromCallExplicit rfl)
  simp [decodeCoreCallConfig, decodeAfterCoreConfig, decodeOddStore,
    decodePostReadLocals]
  exact ⟨[], .refl _⟩

def coreFirstInstruction : Program → Instruction
  | instruction :: _ => instruction
  | [] => .unreachable

def coreStructuredBody : Instruction → Program
  | .block _ _ body _ _ => body
  | .loop _ _ body _ _ => body
  | _ => []

def decodeCoreOuter1 : Program :=
  coreStructuredBody (coreFirstInstruction (func5.drop 7))

def decodeCoreOuter2 : Program :=
  coreStructuredBody (coreFirstInstruction decodeCoreOuter1)

def decodeCoreOuter3 : Program :=
  coreStructuredBody (coreFirstInstruction decodeCoreOuter2)

def decodeCoreOuter4 : Program :=
  coreStructuredBody (coreFirstInstruction decodeCoreOuter3)

def decodeCoreInner : Program :=
  coreStructuredBody (coreFirstInstruction decodeCoreOuter4)

def coreBlockControl (body continuation : Program) : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body, continuation, belowStack := [] }

def decodeCoreControls : List ControlFrame :=
  coreBlockControl decodeCoreInner (decodeCoreOuter4.drop 1) ::
  coreBlockControl decodeCoreOuter4 (decodeCoreOuter3.drop 1) ::
  coreBlockControl decodeCoreOuter3 (decodeCoreOuter2.drop 1) ::
  coreBlockControl decodeCoreOuter2 (decodeCoreOuter1.drop 1) ::
  coreBlockControl decodeCoreOuter1 (func5.drop 8) :: []

def decodeCoreAfterFirstPair : Program := decodeCoreInner.drop 28

def decodeEvenPreparedStore (store : MachineStore Universal.State)
    (data len : UInt32) : MachineStore Universal.State :=
  let globals := { globals :=
    store.wasm.globals.globals.set 0 (.i32 coreFrame) }
  let mem0 := store.wasm.mem.write32 coreError 1114114
  let mem1 := mem0.write64 (coreFrame + 48) 2
  let mem2 := mem1.write32 (coreFrame + 44) len
  let mem3 := mem2.write32 (coreFrame + 40) data
  let mem4 := mem3.write32 (coreFrame + 56) coreError
  { store with wasm := { store.wasm with globals := globals, mem := mem4 } }

def decodeFirstPairConfig (store : MachineStore Universal.State)
    (data len : UInt32) : Config Universal.State :=
  ⟨.running ⟨⟨[.i32 decodeResultOut, .i32 data, .i32 len],
      [.i32 coreFrame, .i32 1, .i32 0],
      [.i32 coreIterator, .i32 corePairOut]⟩,
    [.call 3] ++ decodeCoreAfterFirstPair, 0, [], decodeCoreControls,
    [{ locals := ⟨[], decodePostReadLocals data, []⟩
       continuation := decodeAfterCore
       resultArity := 0
       callerRemainder := []
       control := []
       returningInstance := store.runtime.entry }]⟩,
    decodeEvenPreparedStore store data len⟩

set_option maxRecDepth 100000 in
theorem decode_core_even_to_first_pair
    (store : MachineStore Universal.State) (data len : UInt32)
    (hmod : store.runtime.currentModule = «module»)
    (hglobal : globalAt? store 0 = some (.i32 decodeStack))
    (hpages : 17 ≤ store.wasm.mem.pages)
    (heven : len &&& (1 : UInt32) = 0) :
    Reaches (decodeCoreCallConfig store data len)
      (decodeFirstPairConfig store data len) := by
  apply Reaches.prepend (Step.call (fn := func5Def)
    (by simp [hmod]; decide) (by simp [hmod]; rfl))
  simp [func5Def, Function.toLocals, Function.numParams, ValueType.zero, func5]
  apply Reaches.prepend (Step.globalGet hglobal)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.sub
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend (Step.globalSet (by simp [hglobal]))
  rw [setGlobal_zero_eq]
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.localSet rfl)
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.and
  rw [heven]
  apply Reaches.prepend Step.brIfZero
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.store32 (by
    change 1048468 ≤ store.wasm.mem.pages * 65536
    omega))
  rw [setMemory_eq]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.constI64
  apply Reaches.prepend (Step.store64 rfl (by
    change 1048488 ≤ store.wasm.mem.pages * 65536
    omega))
  rw [setMemory_eq]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.store32 (by
    change 1048480 ≤ store.wasm.mem.pages * 65536
    omega))
  rw [setMemory_eq]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.store32 (by
    change 1048476 ≤ store.wasm.mem.pages * 65536
    omega))
  rw [setMemory_eq]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.add
  apply Reaches.prepend (Step.store32 (by
    change 1048492 ≤ store.wasm.mem.pages * 65536
    omega))
  rw [setMemory_eq]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.add
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.add
  simp [decodeFirstPairConfig, decodeEvenPreparedStore, decodeCoreCallConfig,
    decodeCoreAfterFirstPair, decodeCoreControls, coreBlockControl,
    decodeCoreInner, decodeCoreOuter4, decodeCoreOuter3, decodeCoreOuter2,
    decodeCoreOuter1, coreStructuredBody, coreFirstInstruction, func5]
  exact ⟨[], .refl _⟩

def decodeEmptyCoreStore (store : MachineStore Universal.State)
    (data : UInt32) : MachineStore Universal.State :=
  let paired := decodePairEmptyStore (decodeEvenPreparedStore store data 0)
  let mem0 := paired.wasm.mem.write32 (decodeResultOut + 8) 0
  let mem1 := mem0.write32 (decodeResultOut + 4) 1
  let mem2 := mem1.write32 decodeResultOut 0
  let globals := { globals :=
    paired.wasm.globals.globals.set 0 (.i32 decodeStack) }
  { paired with wasm := { paired.wasm with mem := mem2, globals := globals } }

def decodeAfterFirstPairConfig (store : MachineStore Universal.State)
    (data len : UInt32) : Config Universal.State :=
  ⟨.running ⟨⟨[.i32 decodeResultOut, .i32 data, .i32 len],
      [.i32 coreFrame, .i32 1, .i32 0], []⟩,
    decodeCoreAfterFirstPair, 0, [], decodeCoreControls,
    [{ locals := ⟨[], decodePostReadLocals data, []⟩
       continuation := decodeAfterCore
       resultArity := 0
       callerRemainder := []
       control := []
       returningInstance := store.runtime.entry }]⟩, store⟩

def decodeInvalidCoreStore (store : MachineStore Universal.State)
    (bad index : UInt32) : MachineStore Universal.State :=
  let mem0 := store.wasm.mem.write32 (decodeResultOut + 8) index
  let mem1 := mem0.write32 (decodeResultOut + 4) bad
  let mem2 := mem1.write32 decodeResultOut 2147483648
  let globals := { globals :=
    store.wasm.globals.globals.set 0 (.i32 decodeStack) }
  { store with wasm := { store.wasm with mem := mem2, globals := globals } }

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem decode_core_invalid_suffix
    (store : MachineStore Universal.State) (data len bad index : UInt32)
    (hpages : 17 ≤ store.wasm.mem.pages)
    (hglobal : globalAt? store 0 = some (.i32 coreFrame))
    (htag : store.wasm.mem.read8 corePairOut = 0)
    (hmarker : store.wasm.mem.read32 coreError = bad)
    (hmarkerNe : bad ≠ 1114114)
    (hindex : store.wasm.mem.read32 (coreError + 4) = index) :
    Reaches (decodeAfterFirstPairConfig store data len)
      (decodeAfterCoreConfig (decodeInvalidCoreStore store bad index) data) := by
  simp only [decodeAfterFirstPairConfig, decodeCoreAfterFirstPair,
    decodeCoreInner, decodeCoreOuter4, decodeCoreOuter3, decodeCoreOuter2,
    decodeCoreOuter1, coreStructuredBody, coreFirstInstruction, func5,
    List.drop]
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.localSet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.localSet rfl)
  apply Reaches.prepend Step.block
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load8U (by
    change 1048457 ≤ store.wasm.mem.pages * 65536
    omega))
  rw [show coreFrame + 24 = corePairOut by decide, htag]
  apply Reaches.prepend (Step.eqz (result := 1) rfl)
  apply Reaches.prepend (Step.brIf (condition := 1) (by decide) rfl)
  apply Reaches.prepend Step.block
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load32 (by
    change 1048468 ≤ store.wasm.mem.pages * 65536
    omega))
  rw [show coreFrame + 32 = coreError by decide, hmarker]
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.eq (result := 0) (by simp [hmarkerNe]))
  apply Reaches.prepend Step.brIfZero
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load32 (by
    change 1048472 ≤ store.wasm.mem.pages * 65536
    omega))
  rw [show coreFrame + 36 = coreError + 4 by decide, hindex]
  apply Reaches.prepend (Step.store32 (by
    change 1048564 ≤ store.wasm.mem.pages * 65536
    omega))
  rw [setMemory_eq]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.store32 (by
    change 1048560 ≤ store.wasm.mem.pages * 65536
    omega))
  rw [setMemory_eq]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.store32 (by
    change 1048556 ≤ store.wasm.mem.pages * 65536
    omega))
  rw [setMemory_eq]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.eqz (result := 1) rfl)
  apply Reaches.prepend (Step.brIf (condition := 1) (by decide) rfl)
  simp [decodeCoreControls, coreBlockControl]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.add
  have hzero : 0 < store.wasm.globals.globals.length := by
    apply (getElem?_eq_some_iff.mp (show
      store.wasm.globals.globals[0]? = some (.i32 coreFrame) by
        simpa only [globalAt?, canonicalGlobalIndex_zero] using hglobal)).1
  apply Reaches.prepend (Step.globalSet (by
    simpa [globalAt?] using hzero))
  rw [setGlobal_zero_eq]
  apply Reaches.prepend (Step.returnFromCallExplicit rfl)
  simp [decodeAfterCoreConfig, decodeInvalidCoreStore, decodePostReadLocals]
  exact ⟨[], .refl _⟩

theorem Mem.read8_write32_disjoint_core (m : Mem) (writeAddr readAddr : UInt32)
    (value : UInt32)
    (h : readAddr.toNat < writeAddr.toNat ∨
      writeAddr.toNat + 4 ≤ readAddr.toNat) :
    (m.write32 writeAddr value).read8 readAddr = m.read8 readAddr := by
  simpa only [Mem.read8] using
    (Mem.write32_bytes_of_disjoint m writeAddr value readAddr.toNat h)

theorem Mem.read8_write64_disjoint_core (m : Mem) (writeAddr readAddr : UInt32)
    (value : UInt64)
    (h : readAddr.toNat < writeAddr.toNat ∨
      writeAddr.toNat + 8 ≤ readAddr.toNat) :
    (m.write64 writeAddr value).read8 readAddr = m.read8 readAddr := by
  simpa only [Mem.read8] using
    (Mem.write64_bytes_of_disjoint m writeAddr value readAddr.toNat h)

theorem decodeEvenPreparedStore_read8_of_lower
    (store : MachineStore Universal.State) (data len addr : UInt32)
    (hlower : 1054000 ≤ addr.toNat) :
    (decodeEvenPreparedStore store data len).wasm.mem.read8 addr =
      store.wasm.mem.read8 addr := by
  simp only [decodeEvenPreparedStore]
  rw [Mem.read8_write32_disjoint_core _ (coreFrame + 56) addr _ (by
    right; change 1048492 ≤ addr.toNat; omega)]
  rw [Mem.read8_write32_disjoint_core _ (coreFrame + 40) addr _ (by
    right; change 1048476 ≤ addr.toNat; omega)]
  rw [Mem.read8_write32_disjoint_core _ (coreFrame + 44) addr _ (by
    right; change 1048480 ≤ addr.toNat; omega)]
  rw [Mem.read8_write64_disjoint_core _ (coreFrame + 48) addr _ (by
    right; change 1048488 ≤ addr.toNat; omega)]
  rw [Mem.read8_write32_disjoint_core _ coreError addr _ (by
    right; change 1048468 ≤ addr.toNat; omega)]

theorem decodeEvenPreparedStore_global_zero
    (store : MachineStore Universal.State) (data len : UInt32)
    (hglobal : globalAt? store 0 = some (.i32 decodeStack)) :
    globalAt? (decodeEvenPreparedStore store data len) 0 =
      some (.i32 coreFrame) := by
  simp only [globalAt?, canonicalGlobalIndex_zero] at hglobal ⊢
  have hzero : 0 < store.wasm.globals.globals.length :=
    (getElem?_eq_some_iff.mp hglobal).1
  simpa [decodeEvenPreparedStore] using
    (List.getElem?_set_eq_of_lt (.i32 coreFrame) hzero)

set_option maxRecDepth 100000 in
theorem decode_core_invalid_high_first_reaches
    (store : MachineStore Universal.State) (data len : UInt32)
    (hi lo : UInt8)
    (hmod : store.runtime.currentModule = «module»)
    (hglobal : globalAt? store 0 = some (.i32 decodeStack))
    (hpages : 17 ≤ store.wasm.mem.pages)
    (hpagesMax : store.wasm.mem.pages ≤ 65536)
    (heven : len &&& (1 : UInt32) = 0)
    (hlen : 2 ≤ len.toNat)
    (hdataLower : 1054000 ≤ data.toNat)
    (hinput : data.toNat + 2 ≤ store.wasm.mem.pages * 65536)
    (hhiRead : store.wasm.mem.read8 data = hi)
    (hloRead : store.wasm.mem.read8 (data + 1) = lo)
    (hhi : hexValue hi = none) :
    let paired := decodePairInvalidStore
      (decodeEvenPreparedStore store data len) data len 0 hi 0
    Reaches (decodeCoreCallConfig store data len)
      (decodeAfterCoreConfig
        (decodeInvalidCoreStore paired (hi.toUInt32 &&& 255) 0) data) := by
  dsimp only
  have hprefix := decode_core_even_to_first_pair store data len hmod hglobal
    hpages heven
  apply hprefix.trans
  let prepared := decodeEvenPreparedStore store data len
  have hlenRead : prepared.wasm.mem.read32 (coreIterator + 4) = len := by
    simp [prepared, decodeEvenPreparedStore, Mem.read32, Mem.write32,
      Mem.write64] <;> bv_decide
  have herrorRead : prepared.wasm.mem.read32 (coreIterator + 16) =
      coreError := by
    simp [prepared, decodeEvenPreparedStore, Mem.read32, Mem.write32,
      Mem.write64] <;> bv_decide
  have hchunkRead : prepared.wasm.mem.read32 (coreIterator + 8) = 2 := by
    simp [prepared, decodeEvenPreparedStore, Mem.read32, Mem.write32,
      Mem.write64] <;> bv_decide
  have hptrRead : prepared.wasm.mem.read32 coreIterator = data := by
    simp [prepared, decodeEvenPreparedStore, Mem.read32, Mem.write32,
      Mem.write64] <;> bv_decide
  have hindexRead : prepared.wasm.mem.read32 (coreIterator + 12) = 0 := by
    simp [prepared, decodeEvenPreparedStore, Mem.read32, Mem.write32,
      Mem.write64] <;> bv_decide
  have hhiPrepared : prepared.wasm.mem.read8 data = hi := by
    rw [decodeEvenPreparedStore_read8_of_lower store data len data hdataLower,
      hhiRead]
  have hloLower : 1054000 ≤ (data + 1).toNat := by
    rw [UInt32.toNat_add]
    simp only [UInt32.toNat_ofNat]
    rw [Nat.mod_eq_of_lt]
    · omega
    · have hp := hinput
      omega
  have hloPrepared : prepared.wasm.mem.read8 (data + 1) = lo := by
    rw [decodeEvenPreparedStore_read8_of_lower store data len (data + 1)
      hloLower, hloRead]
  have hpair := decodePair_invalid_high_reaches prepared data len 0 hi lo
    (by simpa [prepared, decodeEvenPreparedStore] using hmod)
    (by simpa [prepared, decodeEvenPreparedStore] using hpages)
    (by simpa [prepared, decodeEvenPreparedStore] using hpagesMax)
    (by simpa [prepared, decodeEvenPreparedStore] using hinput)
    hdataLower hlen hlenRead herrorRead hchunkRead hptrRead hindexRead
    hhiPrepared hloPrepared hhi
    [.i32 decodeResultOut, .i32 data, .i32 len]
    [.i32 coreFrame, .i32 1, .i32 0] [] decodeCoreAfterFirstPair 0 []
    decodeCoreControls
    [{ locals := ⟨[], decodePostReadLocals data, []⟩
       continuation := decodeAfterCore
       resultArity := 0
       callerRemainder := []
       control := []
       returningInstance := store.runtime.entry }]
  have hpair' : Reaches (decodeFirstPairConfig store data len)
      (decodeAfterFirstPairConfig
        (decodePairInvalidStore prepared data len 0 hi 0) data len) := by
    have hruntime : (decodePairInvalidStore prepared data len 0 hi 0).runtime.entry =
        store.runtime.entry := rfl
    simpa [prepared, decodeFirstPairConfig, decodeAfterFirstPairConfig,
      hruntime] using hpair
  apply hpair'.trans
  let paired := decodePairInvalidStore prepared data len 0 hi 0
  have htag : paired.wasm.mem.read8 corePairOut = 0 := by
    simp [paired, decodePairInvalidStore, Mem.read8, Mem.write8]
  have hmarker : paired.wasm.mem.read32 coreError = hi.toUInt32 &&& 255 := by
    simp only [paired, decodePairInvalidStore]
    rw [Mem.read32_write8_disjoint _ corePairOut coreError _ (by decide)]
    rw [Mem.read32_write8_disjoint _ (corePairOut + 1) coreError _
      (by decide)]
    rw [Mem.read32_write32_disjoint _ (coreIterator + 12) coreError _
      (by decide)]
    rw [Mem.read32_write32_disjoint _ (coreError + 4) coreError _
      (by decide)]
    simp [Mem.read32, Mem.write32]
    bv_decide
  have hindex : paired.wasm.mem.read32 (coreError + 4) = 0 := by
    simp only [paired, decodePairInvalidStore]
    rw [Mem.read32_write8_disjoint _ corePairOut (coreError + 4) _
      (by decide)]
    rw [Mem.read32_write8_disjoint _ (corePairOut + 1) (coreError + 4) _
      (by decide)]
    rw [Mem.read32_write32_disjoint _ (coreIterator + 12) (coreError + 4) _
      (by decide)]
    simp [Mem.read32, Mem.write32]
  exact decode_core_invalid_suffix paired data len (hi.toUInt32 &&& 255) 0
    (by change 17 ≤ store.wasm.mem.pages; exact hpages)
    (by
      change globalAt? prepared 0 = some (.i32 coreFrame)
      exact decodeEvenPreparedStore_global_zero store data len hglobal)
    htag hmarker (by bv_decide) hindex

set_option maxRecDepth 100000 in
theorem decode_core_invalid_low_first_reaches
    (store : MachineStore Universal.State) (data len : UInt32)
    (hi lo : UInt8) (hiRoute : HexRoute)
    (hmod : store.runtime.currentModule = «module»)
    (hglobal : globalAt? store 0 = some (.i32 decodeStack))
    (hpages : 17 ≤ store.wasm.mem.pages)
    (hpagesMax : store.wasm.mem.pages ≤ 65536)
    (heven : len &&& (1 : UInt32) = 0)
    (hlen : 2 ≤ len.toNat)
    (hdataLower : 1054000 ≤ data.toNat)
    (hinput : data.toNat + 2 ≤ store.wasm.mem.pages * 65536)
    (hhiRead : store.wasm.mem.read8 data = hi)
    (hloRead : store.wasm.mem.read8 (data + 1) = lo)
    (hhi : hiRoute.valid hi)
    (hlo : hexValue lo = none) :
    let paired := decodePairInvalidStore
      (decodeEvenPreparedStore store data len) data len 0 lo 1
    Reaches (decodeCoreCallConfig store data len)
      (decodeAfterCoreConfig
        (decodeInvalidCoreStore paired (lo.toUInt32 &&& 255) 1) data) := by
  dsimp only
  have hprefix := decode_core_even_to_first_pair store data len hmod hglobal
    hpages heven
  apply hprefix.trans
  let prepared := decodeEvenPreparedStore store data len
  have hlenRead : prepared.wasm.mem.read32 (coreIterator + 4) = len := by
    simp [prepared, decodeEvenPreparedStore, Mem.read32, Mem.write32,
      Mem.write64] <;> bv_decide
  have herrorRead : prepared.wasm.mem.read32 (coreIterator + 16) =
      coreError := by
    simp [prepared, decodeEvenPreparedStore, Mem.read32, Mem.write32,
      Mem.write64] <;> bv_decide
  have hchunkRead : prepared.wasm.mem.read32 (coreIterator + 8) = 2 := by
    simp [prepared, decodeEvenPreparedStore, Mem.read32, Mem.write32,
      Mem.write64] <;> bv_decide
  have hptrRead : prepared.wasm.mem.read32 coreIterator = data := by
    simp [prepared, decodeEvenPreparedStore, Mem.read32, Mem.write32,
      Mem.write64] <;> bv_decide
  have hindexRead : prepared.wasm.mem.read32 (coreIterator + 12) = 0 := by
    simp [prepared, decodeEvenPreparedStore, Mem.read32, Mem.write32,
      Mem.write64] <;> bv_decide
  have hhiPrepared : prepared.wasm.mem.read8 data = hi := by
    rw [decodeEvenPreparedStore_read8_of_lower store data len data hdataLower,
      hhiRead]
  have hloLower : 1054000 ≤ (data + 1).toNat := by
    rw [UInt32.toNat_add]
    simp only [UInt32.toNat_ofNat]
    rw [Nat.mod_eq_of_lt]
    · omega
    · have hp := hinput
      omega
  have hloPrepared : prepared.wasm.mem.read8 (data + 1) = lo := by
    rw [decodeEvenPreparedStore_read8_of_lower store data len (data + 1)
      hloLower, hloRead]
  have hpair := decodePair_invalid_low_reaches prepared data len 0 hi lo
    (by simpa [prepared, decodeEvenPreparedStore] using hmod)
    (by simpa [prepared, decodeEvenPreparedStore] using hpages)
    (by simpa [prepared, decodeEvenPreparedStore] using hpagesMax)
    (by simpa [prepared, decodeEvenPreparedStore] using hinput)
    hdataLower hlen hlenRead herrorRead hchunkRead hptrRead hindexRead
    hhiPrepared hloPrepared hiRoute hhi hlo
    [.i32 decodeResultOut, .i32 data, .i32 len]
    [.i32 coreFrame, .i32 1, .i32 0] [] decodeCoreAfterFirstPair 0 []
    decodeCoreControls
    [{ locals := ⟨[], decodePostReadLocals data, []⟩
       continuation := decodeAfterCore
       resultArity := 0
       callerRemainder := []
       control := []
       returningInstance := store.runtime.entry }]
  have hone : ((((0 : UInt32) <<< (1 : UInt32)) ||| 1) &&& 255 |||
      ((0 : UInt32) <<< (1 : UInt32)) &&& 4294967040) = 1 := by decide
  rw [hone] at hpair
  have hpair' : Reaches (decodeFirstPairConfig store data len)
      (decodeAfterFirstPairConfig
        (decodePairInvalidStore prepared data len 0 lo 1) data len) := by
    have hruntime : (decodePairInvalidStore prepared data len 0 lo 1).runtime.entry =
        store.runtime.entry := rfl
    simpa [prepared, decodeFirstPairConfig, decodeAfterFirstPairConfig,
      hruntime] using hpair
  apply hpair'.trans
  let paired := decodePairInvalidStore prepared data len 0 lo 1
  have htag : paired.wasm.mem.read8 corePairOut = 0 := by
    simp [paired, decodePairInvalidStore, Mem.read8, Mem.write8]
  have hmarker : paired.wasm.mem.read32 coreError = lo.toUInt32 &&& 255 := by
    simp only [paired, decodePairInvalidStore]
    rw [Mem.read32_write8_disjoint _ corePairOut coreError _ (by decide)]
    rw [Mem.read32_write8_disjoint _ (corePairOut + 1) coreError _
      (by decide)]
    rw [Mem.read32_write32_disjoint _ (coreIterator + 12) coreError _
      (by decide)]
    rw [Mem.read32_write32_disjoint _ (coreError + 4) coreError _
      (by decide)]
    simp [Mem.read32, Mem.write32]
    bv_decide
  have hindex : paired.wasm.mem.read32 (coreError + 4) = 1 := by
    simp only [paired, decodePairInvalidStore]
    rw [Mem.read32_write8_disjoint _ corePairOut (coreError + 4) _
      (by decide)]
    rw [Mem.read32_write8_disjoint _ (corePairOut + 1) (coreError + 4) _
      (by decide)]
    rw [Mem.read32_write32_disjoint _ (coreIterator + 12) (coreError + 4) _
      (by decide)]
    simp [Mem.read32, Mem.write32]
    bv_decide
  exact decode_core_invalid_suffix paired data len (lo.toUInt32 &&& 255) 1
    (by change 17 ≤ store.wasm.mem.pages; exact hpages)
    (by
      change globalAt? prepared 0 = some (.i32 coreFrame)
      exact decodeEvenPreparedStore_global_zero store data len hglobal)
    htag hmarker (by bv_decide) hindex

def decodeCoreFirstResultBody : Program :=
  coreStructuredBody (coreFirstInstruction (decodeCoreAfterFirstPair.drop 4))

def decodeCoreAfterInitialAlloc : Program := decodeCoreFirstResultBody.drop 16

def decodeInitialAllocConfig (store : MachineStore Universal.State)
    (data len : UInt32) (byte : UInt8) : Config Universal.State :=
  ⟨.running ⟨⟨[.i32 decodeResultOut, .i32 8, .i32 1],
      [.i32 coreFrame, .i32 1, .i32 byte.toUInt32],
      [.i32 1, .i32 8]⟩,
    [.call 15] ++ decodeCoreAfterInitialAlloc, 0, [],
    coreBlockControl decodeCoreFirstResultBody (decodeCoreInner.drop 33) ::
      decodeCoreControls,
    [{ locals := ⟨[], decodePostReadLocals data, []⟩
       continuation := decodeAfterCore
       resultArity := 0
       callerRemainder := []
       control := []
       returningInstance := store.runtime.entry }]⟩, store⟩

set_option maxRecDepth 100000 in
theorem decode_after_first_valid_to_alloc
    (store : MachineStore Universal.State) (data len : UInt32) (byte : UInt8)
    (hmod : store.runtime.currentModule = «module»)
    (hpages : 17 ≤ store.wasm.mem.pages)
    (htag : store.wasm.mem.read8 corePairOut = 1)
    (hpayload : store.wasm.mem.read8 (corePairOut + 1) = byte)
    (herrorPtr : store.wasm.mem.read32 (coreIterator + 16) = coreError)
    (hmarker : store.wasm.mem.read32 coreError = 1114114)
    (hremaining : store.wasm.mem.read32 (coreIterator + 4) = len - 2)
    (hchunk : store.wasm.mem.read32 (coreIterator + 8) = 2) :
    Reaches (decodeAfterFirstPairConfig store data len)
      (decodeInitialAllocConfig store data len byte) := by
  simp only [decodeAfterFirstPairConfig, decodeCoreAfterFirstPair,
    decodeCoreInner, decodeCoreOuter4, decodeCoreOuter3, decodeCoreOuter2,
    decodeCoreOuter1, coreStructuredBody, coreFirstInstruction, func5,
    List.drop]
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.localSet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.localSet rfl)
  apply Reaches.prepend Step.block
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load8U (by
    change 1048457 ≤ store.wasm.mem.pages * 65536
    omega))
  rw [show coreFrame + 24 = corePairOut by decide, htag]
  apply Reaches.prepend (Step.eqz (result := 0) rfl)
  apply Reaches.prepend Step.brIfZero
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load8U (by
    change 1048458 ≤ store.wasm.mem.pages * 65536
    omega))
  rw [show coreFrame + 25 = corePairOut + 1 by decide, hpayload]
  apply Reaches.prepend (Step.localSet rfl)
  apply Reaches.prepend Step.block
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load32 (by
    change 1048492 ≤ store.wasm.mem.pages * 65536
    omega))
  rw [show coreFrame + 56 = coreIterator + 16 by decide]
  rw [herrorPtr]
  apply Reaches.prepend (Step.load32 (by
    change 1048468 ≤ store.wasm.mem.pages * 65536
    omega))
  simp only [UInt32.add_zero]
  rw [hmarker]
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.ne (result := 0) rfl)
  apply Reaches.prepend Step.brIfZero
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load32 (by
    change 1048480 ≤ store.wasm.mem.pages * 65536
    omega))
  rw [show coreFrame + 44 = coreIterator + 4 by decide, hremaining]
  by_cases hz : len - 2 = 0
  · apply Reaches.prepend (Step.eqz (result := 1) (by simp [hz]))
    apply Reaches.prepend (Step.brIf (condition := 1) (by decide) rfl)
    simp
    apply Reaches.prepend (Step.call (fn := func11Def)
      (by simp [hmod]; decide) (by simp [hmod]; rfl))
    simp [func11Def, Function.toLocals, Function.numParams, func11]
    apply Reaches.prepend (Step.returnFromCallExplicit rfl)
    apply Reaches.prepend Step.const
    apply Reaches.prepend (Step.localSet rfl)
    apply Reaches.prepend Step.const
    apply Reaches.prepend (Step.localSet rfl)
    apply Reaches.prepend Step.const
    apply Reaches.prepend Step.const
    simp [decodeInitialAllocConfig, decodeCoreFirstResultBody,
      decodeCoreAfterInitialAlloc, coreBlockControl]
    exact ⟨[], .refl _⟩
  · apply Reaches.prepend (Step.eqz (result := 0) (by simp [hz]))
    apply Reaches.prepend Step.brIfZero
    apply Reaches.prepend (Step.localGet rfl)
    apply Reaches.prepend (Step.load32 (by
      change 1048484 ≤ store.wasm.mem.pages * 65536
      omega))
    rw [show coreFrame + 48 = coreIterator + 8 by decide, hchunk]
    apply Reaches.prepend (Step.eqz (result := 0) rfl)
    apply Reaches.prepend Step.brIfZero
    apply Reaches.prepend (Step.exitControl rfl)
    simp
    apply Reaches.prepend (Step.call (fn := func11Def)
      (by simp [hmod]; decide) (by simp [hmod]; rfl))
    simp [func11Def, Function.toLocals, Function.numParams, func11]
    apply Reaches.prepend (Step.returnFromCallExplicit rfl)
    apply Reaches.prepend Step.const
    apply Reaches.prepend (Step.localSet rfl)
    apply Reaches.prepend Step.const
    apply Reaches.prepend (Step.localSet rfl)
    apply Reaches.prepend Step.const
    apply Reaches.prepend Step.const
    simp [decodeInitialAllocConfig, decodeCoreFirstResultBody,
      decodeCoreAfterInitialAlloc, coreBlockControl]
    exact ⟨[], .refl _⟩

set_option maxRecDepth 100000 in
theorem decode_core_valid_first_to_alloc_reaches
    (store : MachineStore Universal.State) (data len : UInt32)
    (hi lo : UInt8) (hiRoute loRoute : HexRoute)
    (hmod : store.runtime.currentModule = «module»)
    (hglobal : globalAt? store 0 = some (.i32 decodeStack))
    (hpages : 17 ≤ store.wasm.mem.pages)
    (hpagesMax : store.wasm.mem.pages ≤ 65536)
    (heven : len &&& (1 : UInt32) = 0)
    (hlen : 2 ≤ len.toNat)
    (hdataLower : 1054000 ≤ data.toNat)
    (hinput : data.toNat + 2 ≤ store.wasm.mem.pages * 65536)
    (hhiRead : store.wasm.mem.read8 data = hi)
    (hloRead : store.wasm.mem.read8 (data + 1) = lo)
    (hhi : hiRoute.valid hi) (hlo : loRoute.valid lo) :
    let byte := (loRoute.nibble lo).toUInt8 |||
      (hiRoute.nibble hi).toUInt8 <<< (4 : UInt8)
    let paired := decodePairValidStore
      (decodeEvenPreparedStore store data len) data len 0 byte
    Reaches (decodeCoreCallConfig store data len)
      (decodeInitialAllocConfig paired data len byte) := by
  dsimp only
  have hprefix := decode_core_even_to_first_pair store data len hmod hglobal
    hpages heven
  apply hprefix.trans
  let prepared := decodeEvenPreparedStore store data len
  let byte := (loRoute.nibble lo).toUInt8 |||
    (hiRoute.nibble hi).toUInt8 <<< (4 : UInt8)
  have hlenRead : prepared.wasm.mem.read32 (coreIterator + 4) = len := by
    simp [prepared, decodeEvenPreparedStore, Mem.read32, Mem.write32,
      Mem.write64] <;> bv_decide
  have herrorRead : prepared.wasm.mem.read32 (coreIterator + 16) =
      coreError := by
    simp [prepared, decodeEvenPreparedStore, Mem.read32, Mem.write32,
      Mem.write64] <;> bv_decide
  have hchunkRead : prepared.wasm.mem.read32 (coreIterator + 8) = 2 := by
    simp [prepared, decodeEvenPreparedStore, Mem.read32, Mem.write32,
      Mem.write64] <;> bv_decide
  have hptrRead : prepared.wasm.mem.read32 coreIterator = data := by
    simp [prepared, decodeEvenPreparedStore, Mem.read32, Mem.write32,
      Mem.write64] <;> bv_decide
  have hindexRead : prepared.wasm.mem.read32 (coreIterator + 12) = 0 := by
    simp [prepared, decodeEvenPreparedStore, Mem.read32, Mem.write32,
      Mem.write64] <;> bv_decide
  have hhiPrepared : prepared.wasm.mem.read8 data = hi := by
    rw [decodeEvenPreparedStore_read8_of_lower store data len data hdataLower,
      hhiRead]
  have hloLower : 1054000 ≤ (data + 1).toNat := by
    rw [UInt32.toNat_add]
    simp only [UInt32.toNat_ofNat]
    rw [Nat.mod_eq_of_lt]
    · omega
    · omega
  have hloPrepared : prepared.wasm.mem.read8 (data + 1) = lo := by
    rw [decodeEvenPreparedStore_read8_of_lower store data len (data + 1)
      hloLower, hloRead]
  have hpair := decodePair_valid_reaches prepared data coreError len 0 hi lo
    (by simpa [prepared, decodeEvenPreparedStore] using hmod)
    (by simpa [prepared, decodeEvenPreparedStore] using hpages)
    (by simpa [prepared, decodeEvenPreparedStore] using hpagesMax)
    (by simpa [prepared, decodeEvenPreparedStore] using hinput)
    hdataLower hlen hlenRead herrorRead hchunkRead hptrRead hindexRead
    hhiPrepared hloPrepared hiRoute loRoute hhi hlo
    [.i32 decodeResultOut, .i32 data, .i32 len]
    [.i32 coreFrame, .i32 1, .i32 0] [] decodeCoreAfterFirstPair 0 []
    decodeCoreControls
    [{ locals := ⟨[], decodePostReadLocals data, []⟩
       continuation := decodeAfterCore
       resultArity := 0
       callerRemainder := []
       control := []
       returningInstance := store.runtime.entry }]
  have hpair' : Reaches (decodeFirstPairConfig store data len)
      (decodeAfterFirstPairConfig
        (decodePairValidStore prepared data len 0 byte) data len) := by
    have hruntime : (decodePairValidStore prepared data len 0 byte).runtime.entry =
        store.runtime.entry := rfl
    simpa [prepared, byte, decodeFirstPairConfig, decodeAfterFirstPairConfig,
      hruntime] using hpair
  apply hpair'.trans
  let paired := decodePairValidStore prepared data len 0 byte
  have htag : paired.wasm.mem.read8 corePairOut = 1 := by
    simp [paired, decodePairValidStore, Mem.read8, Mem.write8]
  have hpayload : paired.wasm.mem.read8 (corePairOut + 1) = byte := by
    simp [paired, decodePairValidStore, Mem.read8, Mem.write8]
  have herrorPtr' : paired.wasm.mem.read32 (coreIterator + 16) = coreError := by
    simp only [paired, decodePairValidStore, decodePairBaseStore]
    rw [Mem.read32_write8_disjoint _ corePairOut (coreIterator + 16) _
      (by decide)]
    rw [Mem.read32_write8_disjoint _ (corePairOut + 1)
      (coreIterator + 16) _ (by decide)]
    rw [Mem.read32_write32_disjoint _ (coreIterator + 12)
      (coreIterator + 16) _ (by decide)]
    rw [Mem.read32_write32_disjoint _ coreIterator (coreIterator + 16) _
      (by decide)]
    rw [Mem.read32_write32_disjoint _ (coreIterator + 4)
      (coreIterator + 16) _ (by decide)]
    exact herrorRead
  have hmarker' : paired.wasm.mem.read32 coreError = 1114114 := by
    simp only [paired, decodePairValidStore, decodePairBaseStore]
    rw [Mem.read32_write8_disjoint _ corePairOut coreError _ (by decide)]
    rw [Mem.read32_write8_disjoint _ (corePairOut + 1) coreError _
      (by decide)]
    rw [Mem.read32_write32_disjoint _ (coreIterator + 12) coreError _
      (by decide)]
    rw [Mem.read32_write32_disjoint _ coreIterator coreError _ (by decide)]
    rw [Mem.read32_write32_disjoint _ (coreIterator + 4) coreError _
      (by decide)]
    simp [prepared, decodeEvenPreparedStore, Mem.read32, Mem.write32,
      Mem.write64]
    bv_decide
  have hremaining : paired.wasm.mem.read32 (coreIterator + 4) = len - 2 := by
    simp only [paired, decodePairValidStore, decodePairBaseStore]
    rw [Mem.read32_write8_disjoint _ corePairOut (coreIterator + 4) _
      (by decide)]
    rw [Mem.read32_write8_disjoint _ (corePairOut + 1) (coreIterator + 4) _
      (by decide)]
    rw [Mem.read32_write32_disjoint _ (coreIterator + 12)
      (coreIterator + 4) _ (by decide)]
    rw [Mem.read32_write32_disjoint _ coreIterator (coreIterator + 4) _
      (by decide)]
    simp [Mem.read32, Mem.write32]
    bv_decide
  have hchunk' : paired.wasm.mem.read32 (coreIterator + 8) = 2 := by
    simp only [paired, decodePairValidStore, decodePairBaseStore]
    rw [Mem.read32_write8_disjoint _ corePairOut (coreIterator + 8) _
      (by decide)]
    rw [Mem.read32_write8_disjoint _ (corePairOut + 1) (coreIterator + 8) _
      (by decide)]
    rw [Mem.read32_write32_disjoint _ (coreIterator + 12)
      (coreIterator + 8) _ (by decide)]
    rw [Mem.read32_write32_disjoint _ coreIterator (coreIterator + 8) _
      (by decide)]
    rw [Mem.read32_write32_disjoint _ (coreIterator + 4)
      (coreIterator + 8) _ (by decide)]
    exact hchunkRead
  exact decode_after_first_valid_to_alloc paired data len byte
    (by simpa [paired, prepared, decodePairValidStore,
      decodePairBaseStore, decodeEvenPreparedStore] using hmod)
    (by change 17 ≤ store.wasm.mem.pages; exact hpages)
    htag hpayload herrorPtr' hmarker' hremaining hchunk'

def decodeAfterInitialAllocConfig (store : MachineStore Universal.State)
    (data len : UInt32) (byte : UInt8) (ptr : UInt32)
    (returningInstance : ModuleInstanceId) :
    Config Universal.State :=
  ⟨.running ⟨⟨[.i32 decodeResultOut, .i32 8, .i32 1],
      [.i32 coreFrame, .i32 1, .i32 byte.toUInt32], [.i32 ptr]⟩,
    decodeCoreAfterInitialAlloc, 0, [],
    coreBlockControl decodeCoreFirstResultBody (decodeCoreInner.drop 33) ::
      decodeCoreControls,
    [{ locals := ⟨[], decodePostReadLocals data, []⟩
       continuation := decodeAfterCore
       resultArity := 0
       callerRemainder := []
       control := []
       returningInstance := returningInstance }]⟩, store⟩

set_option maxRecDepth 100000 in
theorem decode_initial_alloc_outcome
    (store : MachineStore Universal.State) (data len oldBump : UInt32)
    (byte : UInt8)
    (hmod : store.runtime.currentModule = «module»)
    (henv : store.runtime.currentHost = Universal.envFor «module»)
    (hbump : store.wasm.mem.read32 1053960 = oldBump)
    (hbumpBound : 1053960 + 4 ≤ store.wasm.mem.pages * 65536)
    (hpages : store.wasm.mem.pages < 4294967295)
    (hbumpNe : oldBump ≠ 0) (hbumpSmall : oldBump.toNat < 2 ^ 31) :
    (∃ allocStore,
        oldBump.toNat + 8 < 2 ^ 31 ∧
        ByteGrowSuccess store 0 1 8 oldBump allocStore ∧
        Reaches (decodeInitialAllocConfig store data len byte)
          (decodeAfterInitialAllocConfig allocStore data len byte
            (allocatorPtr oldBump 1) store.runtime.entry)) ∨
      TrapsWith (decodeInitialAllocConfig store data len byte)
        (.host OOM.trapMessage)
        (fun final => final.wasm.host.oom.raised = true) := by
  have houtcome := allocator_eight_call_outcome store
    [.i32 decodeResultOut, .i32 8, .i32 1]
    [.i32 coreFrame, .i32 1, .i32 byte.toUInt32] []
    decodeCoreAfterInitialAlloc 0 []
    (coreBlockControl decodeCoreFirstResultBody (decodeCoreInner.drop 33) ::
      decodeCoreControls)
    [{ locals := ⟨[], decodePostReadLocals data, []⟩
       continuation := decodeAfterCore
       resultArity := 0
       callerRemainder := []
       control := []
       returningInstance := store.runtime.entry }]
    oldBump hmod henv hbump hbumpBound hpages hbumpNe hbumpSmall
  rcases houtcome with ⟨hfinish, ⟨hfit, hreach⟩ |
      ⟨memory, previousPages, hgrow, hreach⟩⟩ | htrap
  · left
    refine ⟨allocatorBumpStore store (allocatorFinish 8 1 oldBump), hfinish,
      .freshNoGrow rfl hfit, ?_⟩
    simpa [decodeInitialAllocConfig, decodeAfterInitialAllocConfig] using hreach
  · left
    refine ⟨allocatorBumpStore (allocatorGrownStore store memory)
        (allocatorFinish 8 1 oldBump), hfinish,
      .freshGrow rfl memory previousPages hgrow, ?_⟩
    have hruntime :
        (allocatorBumpStore (allocatorGrownStore store memory)
          (allocatorFinish 8 1 oldBump)).runtime.entry = store.runtime.entry := rfl
    simpa [decodeInitialAllocConfig, decodeAfterInitialAllocConfig,
      hruntime] using hreach
  · right
    simpa [decodeInitialAllocConfig] using htrap

def decodeCoreAfterSecondPair : Program := decodeCoreAfterInitialAlloc.drop 34

@[simp] abbrev decodeSecondPairOut : UInt32 := 1048448

def decodeInitialVectorStore (store : MachineStore Universal.State)
    (ptr : UInt32) (byte : UInt8) : MachineStore Universal.State :=
  let mem0 := store.wasm.mem.write8 ptr byte
  let mem1 := mem0.write32 (coreFrame + 68) 1
  let mem2 := mem1.write32 (coreFrame + 64) ptr
  let mem3 := mem2.write32 (coreFrame + 60) 8
  let mem4 := mem3.write32 (coreFrame + 88) (mem3.read32 (coreFrame + 56))
  let mem5 := mem4.write64 (coreFrame + 80) (mem4.read64 (coreFrame + 48))
  let mem6 := mem5.write64 (coreFrame + 72) (mem5.read64 (coreFrame + 40))
  { store with wasm := { store.wasm with mem := mem6 } }

def decodeSecondPairConfig (store : MachineStore Universal.State)
    (data len ptr : UInt32) (byte : UInt8)
    (returningInstance : ModuleInstanceId) : Config Universal.State :=
  ⟨.running ⟨⟨[.i32 decodeResultOut, .i32 8, .i32 1],
      [.i32 coreFrame, .i32 ptr, .i32 byte.toUInt32],
      [.i32 loopIterator, .i32 decodeSecondPairOut]⟩,
    [.call 3] ++ decodeCoreAfterSecondPair, 0, [],
    coreBlockControl decodeCoreFirstResultBody (decodeCoreInner.drop 33) ::
      decodeCoreControls,
    [{ locals := ⟨[], decodePostReadLocals data, []⟩
       continuation := decodeAfterCore
       resultArity := 0
       callerRemainder := []
       control := []
       returningInstance := returningInstance }]⟩,
    decodeInitialVectorStore store ptr byte⟩

set_option maxRecDepth 100000 in
theorem decode_after_initial_alloc_to_second_pair
    (store : MachineStore Universal.State) (data len ptr : UInt32)
    (byte : UInt8) (returningInstance : ModuleInstanceId)
    (hpages : 17 ≤ store.wasm.mem.pages)
    (hptr : ptr ≠ 0)
    (hptrBound : ptr.toNat + 1 ≤ store.wasm.mem.pages * 65536) :
    Reaches (decodeAfterInitialAllocConfig store data len byte ptr
        returningInstance)
      (decodeSecondPairConfig store data len ptr byte returningInstance) := by
  simp only [decodeAfterInitialAllocConfig, decodeCoreAfterInitialAlloc,
    decodeCoreFirstResultBody, decodeCoreAfterFirstPair, decodeCoreInner,
    decodeCoreOuter4, decodeCoreOuter3, decodeCoreOuter2, decodeCoreOuter1,
    coreStructuredBody, coreFirstInstruction, func5, List.drop]
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend (Step.eqz (result := 0) (by simp [hptr]))
  apply Reaches.prepend Step.brIfZero
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.store8 (address := ptr) (offset := 0)
    (value := byte.toUInt32) (by simpa using hptrBound))
  rw [setMemory_eq]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.store32 (by
    change 1048504 ≤ store.wasm.mem.pages * 65536
    omega))
  rw [setMemory_eq]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.store32 (by
    change 1048500 ≤ store.wasm.mem.pages * 65536
    omega))
  rw [setMemory_eq]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.store32 (by
    change 1048496 ≤ store.wasm.mem.pages * 65536
    omega))
  rw [setMemory_eq]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load32 (by
    change 1048492 ≤ store.wasm.mem.pages * 65536
    omega))
  apply Reaches.prepend (Step.store32 (by
    change 1048524 ≤ store.wasm.mem.pages * 65536
    omega))
  rw [setMemory_eq]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load64 rfl (by
    change 1048488 ≤ store.wasm.mem.pages * 65536
    omega))
  apply Reaches.prepend (Step.store64 rfl (by
    change 1048520 ≤ store.wasm.mem.pages * 65536
    omega))
  rw [setMemory_eq]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load64 rfl (by
    change 1048480 ≤ store.wasm.mem.pages * 65536
    omega))
  apply Reaches.prepend (Step.store64 rfl (by
    change 1048512 ≤ store.wasm.mem.pages * 65536
    omega))
  rw [setMemory_eq]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.add
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.add
  simp [decodeSecondPairConfig, decodeInitialVectorStore,
    decodeCoreAfterSecondPair, coreBlockControl]
  exact ⟨[], .refl _⟩

set_option maxRecDepth 100000 in
theorem decode_core_empty_reaches
    (store : MachineStore Universal.State) (data : UInt32)
    (hmod : store.runtime.currentModule = «module»)
    (hglobal : globalAt? store 0 = some (.i32 decodeStack))
    (hpages : 17 ≤ store.wasm.mem.pages) :
    Reaches (decodeCoreCallConfig store data 0)
      (decodeAfterCoreConfig (decodeEmptyCoreStore store data) data) := by
  have hprefix := decode_core_even_to_first_pair store data 0 hmod hglobal
    hpages (by decide)
  apply hprefix.trans
  have hlen : (decodeEvenPreparedStore store data 0).wasm.mem.read32
      (coreIterator + 4) = 0 := by
    simp [decodeEvenPreparedStore, Mem.read32, Mem.write32, Mem.write64] <;>
      bv_decide
  have hmarker : (decodePairEmptyStore
      (decodeEvenPreparedStore store data 0)).wasm.mem.read32 coreError =
      1114114 := by
    simp only [decodePairEmptyStore, decodeEvenPreparedStore]
    rw [Mem.read32_write8_disjoint _ corePairOut coreError _ (by decide)]
    rw [Mem.read32_write8_disjoint _ (corePairOut + 1) coreError _
      (by decide)]
    rw [Mem.read32_write32_disjoint _ (coreFrame + 56) coreError _
      (by decide)]
    rw [Mem.read32_write32_disjoint _ (coreFrame + 40) coreError _
      (by decide)]
    rw [Mem.read32_write32_disjoint _ (coreFrame + 44) coreError _
      (by decide)]
    rw [Mem.read32_write64_disjoint _ coreError (coreFrame + 48) _
      (by decide)]
    simp [Mem.read32, Mem.write32]
    bv_decide
  have hmarker32 : (decodePairEmptyStore
      (decodeEvenPreparedStore store data 0)).wasm.mem.read32
      (coreFrame + 32) = 1114114 := by simpa using hmarker
  dsimp only [decodePairEmptyStore] at hmarker32
  change (((decodeEvenPreparedStore store data 0).wasm.mem.write8
      1048457 0).write8 1048456 0).read32 1048464 = 1114114 at hmarker32
  have hpair := decodePair_empty_reaches
    (decodeEvenPreparedStore store data 0)
    (by simpa [decodeEvenPreparedStore] using hmod)
    (by simpa [decodeEvenPreparedStore] using hpages) hlen
    [.i32 decodeResultOut, .i32 data, .i32 0]
    [.i32 coreFrame, .i32 1, .i32 0] [] decodeCoreAfterFirstPair 0 []
    decodeCoreControls
    [{ locals := ⟨[], decodePostReadLocals data, []⟩
       continuation := decodeAfterCore
       resultArity := 0
       callerRemainder := []
       control := []
       returningInstance := store.runtime.entry }]
  apply hpair.trans
  simp only [decodeCoreAfterFirstPair, decodeCoreInner, decodeCoreOuter4,
    decodeCoreOuter3, decodeCoreOuter2, decodeCoreOuter1,
    coreStructuredBody, coreFirstInstruction, func5, List.drop]
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.localSet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.localSet rfl)
  apply Reaches.prepend Step.block
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load8U (by
    change 1048457 ≤ store.wasm.mem.pages * 65536
    omega))
  simp [decodePairEmptyStore]
  apply Reaches.prepend (Step.eqz (result := 1) rfl)
  apply Reaches.prepend (Step.brIf (condition := 1) (by decide) rfl)
  apply Reaches.prepend Step.block
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load32 (by
    change 1048468 ≤ store.wasm.mem.pages * 65536
    omega))
  rw [show (1048432 : UInt32) + 32 = 1048464 by decide, hmarker32]
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.eq (result := 1) rfl)
  apply Reaches.prepend (Step.brIf (condition := 1) (by decide) rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.store32 (by
    change 1048564 ≤ store.wasm.mem.pages * 65536
    omega))
  rw [setMemory_eq]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.store32 (by
    change 1048560 ≤ store.wasm.mem.pages * 65536
    omega))
  rw [setMemory_eq]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.store32 (by
    change 1048556 ≤ store.wasm.mem.pages * 65536
    omega))
  rw [setMemory_eq]
  apply Reaches.prepend (Step.br rfl)
  simp [decodeCoreControls, coreBlockControl]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.add
  have hzero : 0 < store.wasm.globals.globals.length := by
    apply (getElem?_eq_some_iff.mp (show
      store.wasm.globals.globals[0]? = some (.i32 decodeStack) by
        simpa only [globalAt?, canonicalGlobalIndex_zero] using hglobal)).1
  have hzeroPrepared : 0 <
      (decodeEvenPreparedStore store data 0).wasm.globals.globals.length := by
    simpa [decodeEvenPreparedStore] using hzero
  apply Reaches.prepend (Step.globalSet (by
    simpa [globalAt?] using hzeroPrepared))
  rw [setGlobal_zero_eq]
  apply Reaches.prepend (Step.returnFromCallExplicit rfl)
  simp [decodeAfterCoreConfig, decodeEmptyCoreStore, decodePairEmptyStore,
    decodeEvenPreparedStore, decodePostReadLocals]
  exact ⟨[], .refl _⟩

end Project.HexDecodeStdio
