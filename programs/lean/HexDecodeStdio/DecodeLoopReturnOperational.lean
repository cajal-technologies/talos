import HexDecodeStdio.DecodeLoopOperational
import HexDecodeStdio.DecodeSecondPairInvalidLowOperational

namespace Submission.HexDecodeStdio

open Wasm Project.HexStdio Project.HexStdio.Spec
open Wasm.SmallStep

def decodePostLoopConfig (store : MachineStore Universal.State)
    (data len ptr capacity outLen : UInt32) (seed : UInt8)
    (returningInstance : ModuleInstanceId) : Config Universal.State :=
  ⟨.running ⟨⟨[.i32 decodeResultOut, .i32 capacity, .i32 outLen],
      [.i32 coreFrame, .i32 ptr, .i32 seed.toUInt32], []⟩,
    decodeCoreInner.drop 33, 0, [], decodeCoreControls,
    [{ locals := ⟨[], decodePostReadLocals data, []⟩
       continuation := decodeAfterCore
       resultArity := 0
       callerRemainder := []
       control := []
       returningInstance := returningInstance }]⟩, store⟩

set_option maxRecDepth 100000 in
theorem decode_second_pair_zero_to_post
    (store : MachineStore Universal.State)
    (data len ptr : UInt32) (seed : UInt8)
    (returningInstance : ModuleInstanceId)
    (hpages : 17 ≤ store.wasm.mem.pages)
    (htag : store.wasm.mem.read8 decodeSecondPairOut = 0) :
    Reaches (decodeAfterPairConfig store data len ptr seed 0
        returningInstance)
      (decodePostLoopConfig store data len ptr 8 1 seed
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
  apply Reaches.prepend (Step.eqz (result := 1) rfl)
  apply Reaches.prepend (Step.brIf (condition := 1) (by decide) rfl)
  simp [decodePostLoopConfig, coreBlockControl]
  exact ⟨[], .refl _⟩

set_option maxRecDepth 100000 in
theorem decode_loop_exit_to_post
    (store : MachineStore Universal.State)
    (data len ptr capacity previousLen : UInt32) (seed payload : UInt8)
    (returningInstance : ModuleInstanceId)
    (hpages : 17 ≤ store.wasm.mem.pages)
    (hptr : store.wasm.mem.read32 (coreFrame + 64) = ptr)
    (hcapacity : store.wasm.mem.read32 (coreFrame + 60) = capacity) :
    Reaches (decodeLoopExitConfig store data len ptr previousLen seed payload
        returningInstance)
      (decodePostLoopConfig store data len ptr capacity (1 + previousLen) seed
        returningInstance) := by
  simp only [decodeLoopExitConfig, decodeCoreAfterLoop,
    decodeCoreAfterSecondPair, decodeCoreAfterInitialAlloc,
    decodeCoreFirstResultBody, decodeCoreInner, decodeCoreOuter4,
    decodeCoreOuter3, decodeCoreOuter2, decodeCoreOuter1,
    coreStructuredBody, coreFirstInstruction, func5, List.drop]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load32 (by
    change 1048500 ≤ store.wasm.mem.pages * 65536
    omega))
  rw [hptr]
  apply Reaches.prepend (Step.localSet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load32 (by
    change 1048496 ≤ store.wasm.mem.pages * 65536
    omega))
  rw [hcapacity]
  apply Reaches.prepend (Step.localSet rfl)
  apply Reaches.prepend (Step.exitControl rfl)
  simp [decodePostLoopConfig, decodeCoreControls, coreBlockControl]
  exact ⟨[], .refl _⟩

def decodeLoopSuccessStore (store : MachineStore Universal.State)
    (ptr capacity outLen : UInt32) : MachineStore Universal.State :=
  let mem0 := store.wasm.mem.write32 (decodeResultOut + 8) outLen
  let mem1 := mem0.write32 (decodeResultOut + 4) ptr
  let mem2 := mem1.write32 decodeResultOut capacity
  let globals := { globals :=
    store.wasm.globals.globals.set 0 (.i32 decodeStack) }
  { store with wasm := { store.wasm with mem := mem2, globals := globals } }

set_option maxRecDepth 100000 in
theorem decode_post_loop_success_reaches
    (store : MachineStore Universal.State)
    (data len ptr capacity outLen : UInt32) (seed : UInt8)
    (returningInstance : ModuleInstanceId)
    (hpages : 17 ≤ store.wasm.mem.pages)
    (hglobal : globalAt? store 0 = some (.i32 coreFrame))
    (hmarker : store.wasm.mem.read32 coreError = 1114114)
    (hreturning : returningInstance = store.runtime.entry) :
    Reaches (decodePostLoopConfig store data len ptr capacity outLen seed
        returningInstance)
      (decodeAfterCoreConfig
        (decodeLoopSuccessStore store ptr capacity outLen) data) := by
  simp only [decodePostLoopConfig, decodeCoreInner, decodeCoreOuter4,
    decodeCoreOuter3, decodeCoreOuter2, decodeCoreOuter1,
    coreStructuredBody, coreFirstInstruction, func5, List.drop]
  apply Reaches.prepend Step.block
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load32 (by
    change 1048468 ≤ store.wasm.mem.pages * 65536
    omega))
  rw [show coreFrame + 32 = coreError by decide, hmarker]
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.eq (result := 1) rfl)
  apply Reaches.prepend (Step.brIf (condition := 1) (by decide) rfl)
  simp
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
      store.wasm.globals.globals[0]? = some (.i32 coreFrame) by
        simpa only [globalAt?, canonicalGlobalIndex_zero] using hglobal)).1
  apply Reaches.prepend (Step.globalSet (by simpa [globalAt?] using hzero))
  rw [setGlobal_zero_eq]
  apply Reaches.prepend (Step.returnFromCallExplicit (by
    simpa [decodeLoopSuccessStore] using hreturning))
  simp [decodeAfterCoreConfig, decodeLoopSuccessStore, decodePostReadLocals]
  exact ⟨[], .refl _⟩

theorem dealloc_noop_reaches
    (store : MachineStore Universal.State)
    (params locals stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (hmod : store.runtime.currentModule = «module») :
    Reaches
      ⟨.running ⟨⟨params, locals, stack⟩, [.call 17] ++ code,
        arity, remainder, controls, calls⟩, store⟩
      ⟨.running ⟨⟨params, locals, stack.drop 3⟩, code,
        arity, remainder, controls, calls⟩, store⟩ := by
  apply Reaches.prepend (Step.call (fn := func14Def)
    (by simp [hmod]; decide) (by simp [hmod]; rfl))
  simp [func14Def, Function.toLocals, Function.numParams,
    ValueType.zero, func14]
  apply Reaches.prepend (Step.returnFromCallFallthrough (by simp))
  exact ⟨[], .refl _⟩

def decodeInvalidFieldsStore (store : MachineStore Universal.State)
    (bad index : UInt32) : MachineStore Universal.State :=
  let mem0 := store.wasm.mem.write32 (decodeResultOut + 8) index
  let mem1 := mem0.write32 (decodeResultOut + 4) bad
  let mem2 := mem1.write32 decodeResultOut 2147483648
  { store with wasm := { store.wasm with mem := mem2 } }

def decodeCorePostLoopBlock : Program :=
  coreStructuredBody (coreFirstInstruction (decodeCoreInner.drop 33))

def decodeCorePostLoopAfterBlock : Program := (decodeCoreInner.drop 33).drop 1

set_option maxRecDepth 100000 in
theorem decode_post_loop_invalid_reaches
    (store : MachineStore Universal.State)
    (data len ptr capacity outLen bad index : UInt32) (seed : UInt8)
    (returningInstance : ModuleInstanceId)
    (hmod : store.runtime.currentModule = «module»)
    (hpages : 17 ≤ store.wasm.mem.pages)
    (hglobal : globalAt? store 0 = some (.i32 coreFrame))
    (hmarker : store.wasm.mem.read32 coreError = bad)
    (hmarkerNe : bad ≠ 1114114)
    (hindex : store.wasm.mem.read32 (coreError + 4) = index)
    (hcapacity : capacity ≠ 0)
    (hreturning : returningInstance = store.runtime.entry) :
    Reaches (decodePostLoopConfig store data len ptr capacity outLen seed
        returningInstance)
      (decodeAfterCoreConfig (decodeInvalidCoreStore store bad index) data) := by
  simp only [decodePostLoopConfig, decodeCoreInner, decodeCoreOuter4,
    decodeCoreOuter3, decodeCoreOuter2, decodeCoreOuter1,
    coreStructuredBody, coreFirstInstruction, func5, List.drop]
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
  apply Reaches.prepend (Step.eqz (result := 0) (by simp [hcapacity]))
  apply Reaches.prepend Step.brIfZero
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.call (fn := func14Def)
    (by simp [hmod]; decide)
    (by simp [hmod, decodeInvalidFieldsStore]; rfl))
  simp [func14Def, Function.toLocals, Function.numParams, func14]
  apply Reaches.prepend (Step.returnFromCallFallthrough (by simp))
  apply Reaches.prepend (Step.br rfl)
  simp [decodeCoreControls, coreBlockControl]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.add
  have hzero : 0 < store.wasm.globals.globals.length := by
    apply (getElem?_eq_some_iff.mp (show
      store.wasm.globals.globals[0]? = some (.i32 coreFrame) by
        simpa only [globalAt?, canonicalGlobalIndex_zero] using hglobal)).1
  apply Reaches.prepend (Step.globalSet (by
    simpa [globalAt?, decodeInvalidCoreStore] using hzero))
  rw [setGlobal_zero_eq]
  apply Reaches.prepend (Step.returnFromCallExplicit (by
    simpa [decodeInvalidCoreStore] using hreturning))
  simp [decodeAfterCoreConfig, decodeInvalidCoreStore,
    decodePostReadLocals]
  exact ⟨[], .refl _⟩

end Submission.HexDecodeStdio
