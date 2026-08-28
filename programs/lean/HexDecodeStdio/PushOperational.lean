import HexDecodeStdio.ReserveOperational
import HexDecodeStdio.DecodeCore

namespace Submission.HexDecodeStdio

open Wasm Project.HexStdio Project.HexStdio.Spec
open Wasm.SmallStep
open Wasm.SepLogic

/-! Exact small-step facts for the `RawVec` helpers used when the exported
decoder prepends its one-byte status marker (module functions 61 and 62). -/

def pushGrowNegative : Program :=
  [.localGet 3, .const 0, .geS, .br_if 0,
    .const 1, .localSet 1, .const 4, .localSet 2,
    .const 0, .localSet 3, .br 1]

def pushGrowDispatch : Program :=
  [.localGet 1, .eqz, .br_if 0,
    .localGet 2, .localGet 1, .const 1, .localGet 3, .call 18,
    .localSet 1, .br 1]

def pushGrowZeroSize : Program :=
  [.localGet 3, .br_if 0,
    .const 1, .localSet 1, .br 2]

def pushGrowAlloc : Program :=
  [.block 0 0 pushGrowDispatch, .block 0 0 pushGrowZeroSize,
    .call 14, .localGet 3, .const 1, .call 15, .localSet 1]

def pushGrowCheck : Program :=
  [.block 0 0 pushGrowAlloc,
    .localGet 1, .br_if 0,
    .const 1, .localSet 1,
    .localGet 0, .const 1, .store32 4, .br 1]

def pushGrowSuccess : Program :=
  [.block 0 0 pushGrowCheck,
    .localGet 0, .localGet 1, .store32 4,
    .const 0, .localSet 1]

def pushGrowBody : Program :=
  [.block 0 0 pushGrowNegative, .block 0 0 pushGrowSuccess,
    .const 8, .localSet 2]

def pushGrowTail : Program :=
  [.localGet 0, .localGet 2, .add, .localGet 3, .store32 0,
    .localGet 0, .localGet 1, .store32 0]

def pushGrowOkStore (store : MachineStore Universal.State)
    (out ptr newSize : UInt32) : MachineStore Universal.State :=
  let mem1 := store.wasm.mem.write32 (out + 4) ptr
  let mem2 := mem1.write32 (out + 8) newSize
  { store with wasm := { store.wasm with mem := mem2.write32 out 0 } }

theorem pushGrowOkStore_read_ptr
    (store : MachineStore Universal.State) (out ptr size : UInt32)
    (h4 : (out + 4).toNat = out.toNat + 4)
    (h8 : (out + 8).toNat = out.toNat + 8) :
    (pushGrowOkStore store out ptr size).wasm.mem.read32 (out + 4) = ptr := by
  simp only [pushGrowOkStore]
  rw [Mem.read32_write32_disjoint]
  · rw [Mem.read32_write32_disjoint]
    · exact Mem.read32_write32_same _ _ _
    · left
      omega
  · right
    omega

theorem func58_decomposition :
    func58 = [.block 0 0 pushGrowBody] ++ pushGrowTail := by
  rfl

def pushGrowOuterControl : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0
    body := pushGrowBody, continuation := pushGrowTail, belowStack := [] }

def pushGrowSuccessControl : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0
    body := pushGrowSuccess, continuation := [.const 8, .localSet 2]
    belowStack := [] }

def pushGrowCheckControl : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0
    body := pushGrowCheck
    continuation := [.localGet 0, .localGet 1, .store32 4,
      .const 0, .localSet 1]
    belowStack := [] }

def pushGrowAllocControl : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0
    body := pushGrowAlloc
    continuation := [.localGet 1, .br_if 0,
      .const 1, .localSet 1, .localGet 0, .const 1, .store32 4, .br 1]
    belowStack := [] }

def pushGrowAllocatorCall
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (out oldPtr newSize : UInt32) : Config Universal.State :=
  ⟨.running
    ⟨⟨[.i32 out, .i32 0, .i32 oldPtr, .i32 newSize], [],
        [.i32 1, .i32 newSize]⟩,
      [.call 15, .localSet 1], 0, [],
      [pushGrowAllocControl, pushGrowCheckControl,
        pushGrowSuccessControl, pushGrowOuterControl],
      { locals := ⟨outerParams, outerLocalValues, stack⟩
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls
        returningInstance := store.runtime.entry } :: calls⟩,
    store⟩

def pushGrowAfterAllocator
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (out oldPtr newSize ptr : UInt32) : Config Universal.State :=
  ⟨.running
    ⟨⟨[.i32 out, .i32 0, .i32 oldPtr, .i32 newSize], [], [.i32 ptr]⟩,
      [.localSet 1], 0, [],
      [pushGrowAllocControl, pushGrowCheckControl,
        pushGrowSuccessControl, pushGrowOuterControl],
      { locals := ⟨outerParams, outerLocalValues, stack⟩
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls
        returningInstance := store.runtime.entry } :: calls⟩,
    store⟩

theorem push_grow_fresh_prefix
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (out oldPtr newSize : UInt32)
    (hmod : store.runtime.currentModule = «module»)
    (hnonneg : ¬ newSize.toInt32 < UInt32.toInt32 0)
    (hsize : newSize ≠ 0) :
    Reaches
      ⟨.running
        ⟨⟨outerParams, outerLocalValues,
            [.i32 newSize, .i32 oldPtr, .i32 0, .i32 out] ++ stack⟩,
          [.call 61] ++ code, arity, remainder, controls, calls⟩, store⟩
      (pushGrowAllocatorCall store outerParams outerLocalValues stack code
        arity remainder controls calls out oldPtr newSize) := by
  have hnot : ¬61 < store.runtime.currentModule.imports.length := by
    rw [hmod]; decide
  have hfn : store.runtime.currentModule.funcs[
      61 - store.runtime.currentModule.imports.length]? = some func58Def := by
    rw [hmod]; rfl
  apply Reaches.prepend (Step.call hnot hfn)
  simp [func58Def, Function.toLocals, Function.numParams,
    func58_decomposition, pushGrowBody]
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.geS (result := 1) (by
    split <;> simp_all))
  apply Reaches.prepend (Step.brIf (condition := 1) (by decide) rfl)
  simp [pushGrowNegative]
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.eqz (result := 1) (by simp))
  apply Reaches.prepend (Step.brIf (condition := 1) (by decide) rfl)
  simp [pushGrowDispatch]
  apply Reaches.prepend Step.block
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.brIf (condition := newSize) hsize rfl)
  simp [pushGrowZeroSize]
  have hnot14 : ¬14 < store.runtime.currentModule.imports.length := by
    rw [hmod]; decide
  have hfn14 : store.runtime.currentModule.funcs[
      14 - store.runtime.currentModule.imports.length]? = some func11Def := by
    rw [hmod]; rfl
  apply Reaches.prepend (Step.call hnot14 hfn14)
  simp [func11Def, Function.toLocals, Function.numParams, func11]
  apply Reaches.prepend (Step.returnFromCallExplicit rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  simp [pushGrowAllocatorCall, pushGrowAllocControl, pushGrowCheckControl,
    pushGrowSuccessControl, pushGrowOuterControl, pushGrowAlloc,
    pushGrowCheck, pushGrowSuccess, pushGrowTail]
  exact ⟨[], .refl _⟩

theorem push_grow_fresh_success_suffix
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (out oldPtr newSize ptr : UInt32)
    (hptr : ptr ≠ 0)
    (hout : out.toNat + 12 ≤ store.wasm.mem.pages * 65536)
    (hout8NoWrap : (out + 8).toNat = out.toNat + 8)
    (hreturn : store.runtime.entry = store.runtime.entry) :
    Reaches
      (pushGrowAfterAllocator store outerParams outerLocalValues stack code
        arity remainder controls calls out oldPtr newSize ptr)
      (growResultFinal (pushGrowOkStore store out ptr newSize)
        outerParams outerLocalValues stack code arity remainder controls calls) := by
  simp only [pushGrowAfterAllocator]
  apply Reaches.prepend (Step.localSet rfl)
  apply Reaches.prepend (Step.exitControl rfl)
  simp [pushGrowAllocControl]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.brIf (condition := ptr) hptr rfl)
  simp [pushGrowCheckControl]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.store32 (address := out) (offset := 4) (by
    simpa using (show out.toNat + 4 + 4 ≤
      store.wasm.mem.pages * 65536 by omega)))
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.localSet rfl)
  apply Reaches.prepend (Step.exitControl rfl)
  simp [pushGrowSuccessControl]
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.localSet rfl)
  apply Reaches.prepend (Step.exitControl rfl)
  simp [pushGrowOuterControl]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.add
  apply Reaches.prepend (Step.localGet rfl)
  rw [show 8 + out = out + 8 by bv_decide]
  apply Reaches.prepend (Step.store32 (address := out + 8) (offset := 0) (by
    simpa [setMemory_eq] using
      (show (out + 8).toNat + 4 ≤ store.wasm.mem.pages * 65536 by
        rw [hout8NoWrap]
        omega)))
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.store32 (address := out) (offset := 0) (by
    simpa [setMemory_eq] using (show out.toNat + 4 ≤
      store.wasm.mem.pages * 65536 by omega)))
  apply Reaches.prepend (Step.returnFromCallFallthrough hreturn)
  simp [growResultFinal, pushGrowOkStore, setMemory_eq,
    pushGrowAllocControl, pushGrowCheckControl, pushGrowSuccessControl,
    pushGrowOuterControl, pushGrowAlloc, pushGrowCheck, pushGrowSuccess,
    pushGrowTail]
  exact ⟨[], .refl _⟩

set_option maxRecDepth 5000 in
theorem push_grow_fresh_outcome
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (out oldPtr newSize oldBump : UInt32)
    (hmod : store.runtime.currentModule = «module»)
    (henv : store.runtime.currentHost = Universal.envFor «module»)
    (hread : store.wasm.mem.read32 1053960 = oldBump)
    (hbound : 1053960 + 4 ≤ store.wasm.mem.pages * 65536)
    (hpages : store.wasm.mem.pages < 4294967295)
    (hnonneg : ¬ newSize.toInt32 < UInt32.toInt32 0)
    (hsize : newSize ≠ 0)
    (hptr : allocatorPtr oldBump 1 ≠ 0)
    (houtNoWrap : out.toNat + 12 < UInt32.size)
    (hout : out.toNat + 12 ≤ store.wasm.mem.pages * 65536) :
    (∃ allocStore,
      ByteGrowSuccess store 0 oldPtr newSize oldBump allocStore ∧
      Reaches
        ⟨.running
          ⟨⟨outerParams, outerLocalValues,
              [.i32 newSize, .i32 oldPtr, .i32 0, .i32 out] ++ stack⟩,
            [.call 61] ++ code, arity, remainder, controls, calls⟩, store⟩
        (growResultFinal
          (pushGrowOkStore allocStore out (allocatorPtr oldBump 1) newSize)
          outerParams outerLocalValues stack code arity remainder controls
          calls)) ∨
    TrapsWith
      ⟨.running
        ⟨⟨outerParams, outerLocalValues,
            [.i32 newSize, .i32 oldPtr, .i32 0, .i32 out] ++ stack⟩,
          [.call 61] ++ code, arity, remainder, controls, calls⟩, store⟩
      (.host OOM.trapMessage)
      (fun final => final.wasm.host.oom.raised = true) := by
  let initial : Config Universal.State :=
    ⟨.running
      ⟨⟨outerParams, outerLocalValues,
          [.i32 newSize, .i32 oldPtr, .i32 0, .i32 out] ++ stack⟩,
        [.call 61] ++ code, arity, remainder, controls, calls⟩, store⟩
  have hprefix := push_grow_fresh_prefix store outerParams outerLocalValues
    stack code arity remainder controls calls out oldPtr newSize hmod hnonneg
    hsize
  have hout8NoWrap : (out + 8).toNat = out.toNat + 8 := by
    apply UInt32.add_ofNat_toNat_noWrap out 8 (by decide)
    norm_num [UInt32.size] at houtNoWrap ⊢
    omega
  have halloc := allocator_call_outcome store
    ([.i32 out, .i32 0, .i32 oldPtr, .i32 newSize]) [] []
    [.localSet 1] 0 []
    [pushGrowAllocControl, pushGrowCheckControl,
      pushGrowSuccessControl, pushGrowOuterControl]
    ({ locals := ⟨outerParams, outerLocalValues, stack⟩
       continuation := code
       resultArity := arity
       callerRemainder := remainder
       control := controls
       returningInstance := store.runtime.entry } :: calls)
    newSize 1 oldBump hmod henv hread hbound (by omega)
  rcases halloc with ⟨_hsafe, (⟨henough, halloc⟩ |
      ⟨memory, previousPages, hgrow, halloc⟩)⟩ | htrap
  · left
    let allocStore := allocatorBumpStore store (allocatorFinish newSize 1 oldBump)
    refine ⟨allocStore, .freshNoGrow rfl ?_, ?_⟩
    · exact henough
    have hafter : Reaches
        (pushGrowAllocatorCall store outerParams outerLocalValues stack code
          arity remainder controls calls out oldPtr newSize)
        (pushGrowAfterAllocator allocStore outerParams outerLocalValues stack
          code arity remainder controls calls out oldPtr newSize
          (allocatorPtr oldBump 1)) := by
      simpa [pushGrowAllocatorCall, pushGrowAfterAllocator, allocStore,
        allocatorBumpStore] using halloc
    exact hprefix.trans (hafter.trans
      (push_grow_fresh_success_suffix allocStore outerParams outerLocalValues
        stack code arity remainder controls calls out oldPtr newSize
        (allocatorPtr oldBump 1) hptr (by
          rw [show allocStore.wasm.mem.pages = store.wasm.mem.pages by rfl]
          exact hout) hout8NoWrap rfl))
  · left
    let allocStore := allocatorBumpStore (allocatorGrownStore store memory)
      (allocatorFinish newSize 1 oldBump)
    refine ⟨allocStore, .freshGrow rfl memory previousPages hgrow, ?_⟩
    have hafter : Reaches
        (pushGrowAllocatorCall store outerParams outerLocalValues stack code
          arity remainder controls calls out oldPtr newSize)
        (pushGrowAfterAllocator allocStore outerParams outerLocalValues stack
          code arity remainder controls calls out oldPtr newSize
          (allocatorPtr oldBump 1)) := by
      simpa [pushGrowAllocatorCall, pushGrowAfterAllocator, allocStore,
        allocatorBumpStore, allocatorGrownStore] using halloc
    have hfacts := mem_grow_some_facts store.wasm.mem memory
      (allocatorRequiredPages newSize 1 oldBump -
        UInt32.ofNat store.wasm.mem.pages)
      (store.wasm.memoryCap store.runtime.currentModule 0) previousPages hgrow
    have hmono : store.wasm.mem.pages ≤ memory.pages := by
      rw [hfacts.2]
      exact Nat.le_add_right _ _
    exact hprefix.trans (hafter.trans
      (push_grow_fresh_success_suffix allocStore outerParams outerLocalValues
        stack code arity remainder controls calls out oldPtr newSize
        (allocatorPtr oldBump 1) hptr (by
          have hpagesEq : allocStore.wasm.mem.pages = memory.pages := by
            simp [allocStore, allocatorBumpStore, allocatorGrownStore]
          rw [hpagesEq]
          exact le_trans hout (Nat.mul_le_mul_right 65536 hmono))
        hout8NoWrap rfl))
  · right
    exact TrapsWith.prependReaches hprefix (by
      simpa [pushGrowAllocatorCall] using htrap)

/-! Function 62 grows the initially empty status vector to capacity eight. -/

def pushReserveAfterGrow : Program := func59.drop 24

theorem push_reserve_to_grow
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (vector sp : UInt32)
    (hmod : store.runtime.currentModule = «module»)
    (hglobal : globalAt? store 0 = some (.i32 sp))
    (hcapacity : store.wasm.mem.read32 vector = 0)
    (hdata : store.wasm.mem.read32 (vector + 4) = 1)
    (hvectorBound : vector.toNat + 4 ≤ store.wasm.mem.pages * 65536)
    (hvectorDataBound : vector.toNat + 4 + 4 ≤
      store.wasm.mem.pages * 65536) :
    Reaches
      ⟨.running
        ⟨⟨outerParams, outerLocalValues, .i32 vector :: stack⟩,
          [.call 62] ++ code, arity, remainder, controls, calls⟩, store⟩
      ⟨.running
        ⟨⟨[.i32 vector], [.i32 (sp - 16), .i32 8, .i32 0],
            [.i32 8, .i32 1, .i32 0, .i32 ((sp - 16) + 4)]⟩,
          [.call 61] ++ pushReserveAfterGrow, 0, [], [],
          { locals := ⟨outerParams, outerLocalValues, stack⟩
            continuation := code
            resultArity := arity
            callerRemainder := remainder
            control := controls
            returningInstance := store.runtime.entry } :: calls⟩,
        reserveFrameStore store (sp - 16)⟩ := by
  have hnot : ¬62 < store.runtime.currentModule.imports.length := by
    rw [hmod]; decide
  have hfn : store.runtime.currentModule.funcs[
      62 - store.runtime.currentModule.imports.length]? = some func59Def := by
    rw [hmod]; rfl
  apply Reaches.prepend (Step.call hnot hfn)
  simp [func59Def, Function.toLocals, Function.numParams,
    pushReserveAfterGrow, func59]
  apply Reaches.prepend (Step.globalGet hglobal)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.sub
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend (Step.globalSet (by simp [hglobal]))
  rw [setGlobal_zero_eq]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.add
  rw [show 4 + (sp - 16) = (sp - 16) + 4 by bv_decide]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load32 (address := vector) (offset := 0)
    (by simpa [reserveFrameStore] using hvectorBound))
  simp only [reserveFrameStore, UInt32.add_zero, hcapacity]
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load32 (address := vector) (offset := 4)
    (by simpa [reserveFrameStore] using hvectorDataBound))
  simp only [reserveFrameStore, hdata]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.shl
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.gtU (result := 0) (by decide))
  apply Reaches.prepend (Step.select (selected := .i32 8) (by decide))
  apply Reaches.prepend (Step.localTee rfl)
  simp [pushReserveAfterGrow, reserveFrameStore]
  exact ⟨[], .refl _⟩

theorem push_reserve_success_suffix
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (returningInstance : ModuleInstanceId)
    (vector frame ptr sp : UInt32)
    (htag : store.wasm.mem.read32 (frame + 4) = 0)
    (hptr : store.wasm.mem.read32 (frame + 8) = ptr)
    (hframe4 : frame.toNat + 4 + 4 ≤ store.wasm.mem.pages * 65536)
    (hframe8 : frame.toNat + 8 + 4 ≤ store.wasm.mem.pages * 65536)
    (hvector : vector.toNat + 4 ≤ store.wasm.mem.pages * 65536)
    (hvector4 : vector.toNat + 4 + 4 ≤ store.wasm.mem.pages * 65536)
    (hglobal : (globalAt? store 0).isSome = true)
    (hrestore : frame + 16 = sp)
    (hreturn : returningInstance = store.runtime.entry) :
    Reaches
      ⟨.running
        ⟨⟨[.i32 vector], [.i32 frame, .i32 8, .i32 0], []⟩,
          pushReserveAfterGrow, 0, [], [],
          { locals := ⟨outerParams, outerLocalValues, stack⟩
            continuation := code
            resultArity := arity
            callerRemainder := remainder
            control := controls
            returningInstance := returningInstance } :: calls⟩, store⟩
      (growResultFinal (reserveFinishStore store vector ptr 8 sp)
        outerParams outerLocalValues stack code arity remainder controls calls) := by
  simp only [pushReserveAfterGrow, func59, List.drop]
  apply Reaches.prepend Step.block
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load32 (address := frame) (offset := 4) hframe4)
  simp only [htag]
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.ne (result := 1) (by decide))
  apply Reaches.prepend (Step.brIf (condition := 1) (by decide) rfl)
  simp
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load32 (address := frame) (offset := 8) hframe8)
  simp only [hptr]
  apply Reaches.prepend (Step.localSet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.store32 (address := vector) (offset := 0) hvector)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.store32 (address := vector) (offset := 4) (by
    simpa [setMemory_eq] using hvector4))
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.add
  rw [show 16 + frame = sp by rw [UInt32.add_comm, hrestore]]
  apply Reaches.prepend (Step.globalSet (by
    simpa [setMemory_eq, globalAt?] using hglobal))
  rw [setGlobal_zero_eq]
  apply Reaches.prepend (Step.returnFromCallFallthrough hreturn)
  simp [growResultFinal, reserveFinishStore, reserveVectorStore, setMemory_eq]
  exact ⟨[], .refl _⟩

set_option maxRecDepth 5000 in
theorem push_reserve_initial_outcome
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (vector sp oldBump : UInt32)
    (hmod : store.runtime.currentModule = «module»)
    (henv : store.runtime.currentHost = Universal.envFor «module»)
    (hglobal : globalAt? store 0 = some (.i32 sp))
    (hcapacity : store.wasm.mem.read32 vector = 0)
    (hdata : store.wasm.mem.read32 (vector + 4) = 1)
    (hbump : store.wasm.mem.read32 1053960 = oldBump)
    (hbumpBound : 1053960 + 4 ≤ store.wasm.mem.pages * 65536)
    (hpages : store.wasm.mem.pages ≤ 65536)
    (hptr : allocatorPtr oldBump 1 ≠ 0)
    (hframe : (sp - 16).toNat + 16 ≤ store.wasm.mem.pages * 65536)
    (hframeNoWrap : (sp - 16).toNat + 16 < UInt32.size)
    (houtNoWrap : ((sp - 16) + 4).toNat = (sp - 16).toNat + 4)
    (hrestore : (sp - 16) + 16 = sp)
    (hvectorBound : vector.toNat + 4 ≤ store.wasm.mem.pages * 65536)
    (hvectorDataBound : vector.toNat + 4 + 4 ≤
      store.wasm.mem.pages * 65536) :
    (∃ allocStore,
      ByteGrowSuccess (reserveFrameStore store (sp - 16)) 0 1 8 oldBump
        allocStore ∧
      Reaches
        ⟨.running
          ⟨⟨outerParams, outerLocalValues, .i32 vector :: stack⟩,
            [.call 62] ++ code, arity, remainder, controls, calls⟩, store⟩
        (growResultFinal
          (reserveFinishStore
            (pushGrowOkStore allocStore ((sp - 16) + 4)
              (allocatorPtr oldBump 1) 8)
            vector (allocatorPtr oldBump 1) 8 sp)
          outerParams outerLocalValues stack code arity remainder controls
          calls)) ∨
    TrapsWith
      ⟨.running
        ⟨⟨outerParams, outerLocalValues, .i32 vector :: stack⟩,
          [.call 62] ++ code, arity, remainder, controls, calls⟩, store⟩
      (.host OOM.trapMessage)
      (fun final => final.wasm.host.oom.raised = true) := by
  let frame := sp - 16
  let base := reserveFrameStore store frame
  let out := frame + 4
  have hprefix := push_reserve_to_grow store outerParams outerLocalValues stack
    code arity remainder controls calls vector sp hmod hglobal hcapacity hdata
    hvectorBound hvectorDataBound
  have hbaseMod : base.runtime.currentModule = «module» := by
    simpa [base, reserveFrameStore] using hmod
  have hbaseEnv : base.runtime.currentHost = Universal.envFor «module» := by
    simpa [base, reserveFrameStore] using henv
  have hbaseBump : base.wasm.mem.read32 1053960 = oldBump := by
    simpa [base, reserveFrameStore] using hbump
  have hbaseBound : 1053960 + 4 ≤ base.wasm.mem.pages * 65536 := by
    simpa [base, reserveFrameStore] using hbumpBound
  have hbasePages : base.wasm.mem.pages < 4294967295 := by
    simp only [base, reserveFrameStore]
    omega
  have houtBound : out.toNat + 12 ≤ base.wasm.mem.pages * 65536 := by
    simp only [out, base, reserveFrameStore]
    rw [houtNoWrap]
    exact hframe
  have hgrow := push_grow_fresh_outcome base
    ([.i32 vector]) [.i32 frame, .i32 8, .i32 0] [] pushReserveAfterGrow
    0 [] []
    ({ locals := ⟨outerParams, outerLocalValues, stack⟩
       continuation := code
       resultArity := arity
       callerRemainder := remainder
       control := controls
       returningInstance := store.runtime.entry } :: calls)
    out 1 8 oldBump hbaseMod hbaseEnv hbaseBump hbaseBound hbasePages
    (by decide) (by decide) hptr (by
      simp only [out]
      rw [houtNoWrap]
      norm_num [UInt32.size] at hframeNoWrap ⊢
      omega) houtBound
  rcases hgrow with ⟨allocStore, hsuccess, hreach⟩ | htrap
  · left
    refine ⟨allocStore, hsuccess, ?_⟩
    let postGrow := pushGrowOkStore allocStore out (allocatorPtr oldBump 1) 8
    have hmono := hsuccess.pages_mono
    have hpostPages : postGrow.wasm.mem.pages = allocStore.wasm.mem.pages := by
      simp [postGrow, pushGrowOkStore]
    have htag : postGrow.wasm.mem.read32 (frame + 4) = 0 := by
      simp [postGrow, pushGrowOkStore, out]
    have houtRoom : out.toNat + 12 < 4294967296 := by
      simp only [out]
      rw [houtNoWrap]
      norm_num [UInt32.size] at hframeNoWrap
      omega
    have hout4NoWrap : (out + 4).toNat = out.toNat + 4 := by
      exact UInt32.add_ofNat_toNat_noWrap out 4 (by decide) (by omega)
    have hout8NoWrap : (out + 8).toNat = out.toNat + 8 := by
      exact UInt32.add_ofNat_toNat_noWrap out 8 (by decide) (by omega)
    have hptrRead : postGrow.wasm.mem.read32 (frame + 8) =
        allocatorPtr oldBump 1 := by
      rw [show frame + 8 = out + 4 by simp [out]; bv_decide]
      exact pushGrowOkStore_read_ptr allocStore out
        (allocatorPtr oldBump 1) 8 hout4NoWrap hout8NoWrap
    have hpostGlobal : (globalAt? postGrow 0).isSome = true := by
      have hb := reserveFrameStore_global_zero store frame sp hglobal
      have ha := hsuccess.globalAt_eq 0
      simpa [postGrow, pushGrowOkStore, base, globalAt?] using
        congrArg Option.isSome (ha.trans hb)
    have hbaseFrame : frame.toNat + 16 ≤
        base.wasm.mem.pages * 65536 := by
      simpa [base, frame, reserveFrameStore] using hframe
    have hpostFrame4 : frame.toNat + 4 + 4 ≤
        postGrow.wasm.mem.pages * 65536 := by
      rw [hpostPages]
      exact le_trans (show frame.toNat + 4 + 4 ≤
        base.wasm.mem.pages * 65536 by omega)
        (Nat.mul_le_mul_right 65536 hmono)
    have hpostFrame8 : frame.toNat + 8 + 4 ≤
        postGrow.wasm.mem.pages * 65536 := by
      rw [hpostPages]
      exact le_trans (show frame.toNat + 8 + 4 ≤
        base.wasm.mem.pages * 65536 by omega)
        (Nat.mul_le_mul_right 65536 hmono)
    have hpostVector : vector.toNat + 4 ≤
        postGrow.wasm.mem.pages * 65536 := by
      rw [hpostPages]
      exact le_trans hvectorBound (Nat.mul_le_mul_right 65536 hmono)
    have hpostVector4 : vector.toNat + 4 + 4 ≤
        postGrow.wasm.mem.pages * 65536 := by
      rw [hpostPages]
      exact le_trans hvectorDataBound (Nat.mul_le_mul_right 65536 hmono)
    have hsuffix := push_reserve_success_suffix postGrow outerParams
      outerLocalValues stack code arity remainder controls calls
      store.runtime.entry vector frame
      (allocatorPtr oldBump 1) sp htag hptrRead hpostFrame4 hpostFrame8
      hpostVector hpostVector4 hpostGlobal hrestore (by
        have hruntime : postGrow.runtime = store.runtime := by
          calc
            postGrow.runtime = allocStore.runtime := by rfl
            _ = base.runtime := hsuccess.runtime_eq
            _ = store.runtime := by rfl
        exact congrArg RuntimeEnv.entry hruntime.symm)
    simpa [base, frame, out, postGrow] using hprefix.trans (hreach.trans hsuffix)
  · right
    exact TrapsWith.prependReaches hprefix (by
      simpa [base, frame, out] using htrap)

end Submission.HexDecodeStdio
