import HexEncodeStdio.VectorGrowOperational

namespace Submission.HexDecodeStdio

open Wasm Project.HexStdio Project.HexStdio.Spec
open Wasm.SmallStep

/-! Operational control flow for module function 5 (`func2Def`), the byte
vector reserve routine used by `read_chunk` and by the decoder's final append.
-/

def reserveRequired (length additional : UInt32) : UInt32 :=
  length + additional

def reserveDoubled (capacity : UInt32) : UInt32 :=
  capacity <<< 1

def reserveCandidate (length additional capacity : UInt32) : UInt32 :=
  if reserveRequired length additional > reserveDoubled capacity then
    reserveRequired length additional
  else reserveDoubled capacity

def reserveNewCapacity (length additional capacity : UInt32) : UInt32 :=
  if reserveCandidate length additional capacity > 8 then
    reserveCandidate length additional capacity
  else 8

def reserveAfterGrow : Program := func2.drop 31

theorem func2_prefix_split :
    func2 =
      [.globalGet 0, .const 16, .sub, .localTee 3, .globalSet 0,
        .block 0 0
          [.localGet 2, .localGet 1, .add, .localTee 1,
            .localGet 2, .geU, .br_if 0,
            .const 0, .const 0, .call 60, .unreachable],
        .localGet 3, .const 4, .add,
        .localGet 0, .load32 0, .localTee 2,
        .localGet 0, .load32 4,
        .localGet 1, .localGet 2, .const 1, .shl, .localTee 2,
        .localGet 1, .localGet 2, .gtU, .select, .localTee 2,
        .const 8, .localGet 2, .const 8, .gtU, .select, .localTee 2,
        .call 7] ++ reserveAfterGrow := by
  rfl

def reserveFrameStore (store : MachineStore Universal.State)
    (frame : UInt32) : MachineStore Universal.State :=
  { store with wasm := { store.wasm with globals :=
      { globals := store.wasm.globals.globals.set 0 (.i32 frame) } } }

@[simp] theorem reserveFrameStore_runtime
    (store : MachineStore Universal.State) (frame : UInt32) :
    (reserveFrameStore store frame).runtime = store.runtime := by
  rfl

theorem reserveFrameStore_global_zero
    (store : MachineStore Universal.State) (frame old : UInt32)
    (hglobal : globalAt? store 0 = some (.i32 old)) :
    globalAt? (reserveFrameStore store frame) 0 = some (.i32 frame) := by
  simp only [globalAt?, canonicalGlobalIndex_zero] at hglobal ⊢
  have hzero : 0 < store.wasm.globals.globals.length :=
    (getElem?_eq_some_iff.mp hglobal).1
  simpa [reserveFrameStore] using
    (List.getElem?_set_eq_of_lt (.i32 frame) hzero)

@[simp] theorem reserveFrameStore_memoryCap
    (store : MachineStore Universal.State) (frame : UInt32)
    (m : Module) (index : Nat) :
    (reserveFrameStore store frame).wasm.memoryCap m index =
      store.wasm.memoryCap m index := by
  rfl

@[simp] theorem reserveFrameStore_mem
    (store : MachineStore Universal.State) (frame : UInt32) :
    (reserveFrameStore store frame).wasm.mem = store.wasm.mem := by
  rfl

def reserveGrowCall
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (vector length additional capacity data sp : UInt32) :
    Config Universal.State :=
  let required := reserveRequired length additional
  let newCapacity := reserveNewCapacity length additional capacity
  let frame := sp - 16
  ⟨.running
    ⟨⟨[.i32 vector, .i32 required, .i32 newCapacity], [.i32 frame],
        [.i32 newCapacity, .i32 data, .i32 capacity, .i32 (frame + 4)]⟩,
      [.call 7] ++ reserveAfterGrow, 0, [], [],
      { locals := ⟨outerParams, outerLocalValues, stack⟩
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls
        returningInstance := store.runtime.entry } :: calls⟩,
    reserveFrameStore store frame⟩

def reserveVectorStore (store : MachineStore Universal.State)
    (vector data capacity : UInt32) : MachineStore Universal.State :=
  let mem1 := store.wasm.mem.write32 vector capacity
  { store with wasm := { store.wasm with mem := mem1.write32 (vector + 4) data } }

def reserveFinishStore (store : MachineStore Universal.State)
    (vector data capacity sp : UInt32) : MachineStore Universal.State :=
  let stored := reserveVectorStore store vector data capacity
  { stored with wasm := { stored.wasm with globals :=
      { globals := stored.wasm.globals.globals.set 0 (.i32 sp) } } }

@[simp] theorem growResultOkStore_pages
    (store : MachineStore Universal.State) (out ptr size : UInt32) :
    (growResultOkStore store out ptr size).wasm.mem.pages =
      store.wasm.mem.pages := by
  rfl

theorem growResultOkStore_read_tag
    (store : MachineStore Universal.State) (out ptr size : UInt32) :
    (growResultOkStore store out ptr size).wasm.mem.read32 out = 0 := by
  simp [growResultOkStore]

theorem growResultOkStore_read_ptr
    (store : MachineStore Universal.State) (out ptr size : UInt32)
    (hnext : (out + 4).toNat = out.toNat + 4) :
    (growResultOkStore store out ptr size).wasm.mem.read32 (out + 4) = ptr := by
  simp only [growResultOkStore]
  rw [Mem.read32_write32_disjoint]
  · exact Mem.read32_write32_same _ _ _
  · right
    omega

inductive ByteGrowSuccess
    (store : MachineStore Universal.State)
    (oldCapacity oldPtr newCapacity oldBump : UInt32) :
    MachineStore Universal.State → Prop
  | freshNoGrow (hzero : oldCapacity = 0)
      (hfit : allocatorRequiredPages newCapacity 1 oldBump ≤
        UInt32.ofNat store.wasm.mem.pages)
      (hfinishNonnegative :
        ¬ (allocatorFinish newCapacity 1 oldBump).toInt32 < UInt32.toInt32 0) :
      ByteGrowSuccess store oldCapacity oldPtr newCapacity oldBump
        (allocatorBumpStore store
          (allocatorFinish newCapacity 1 oldBump))
  | freshGrow (hzero : oldCapacity = 0) (memory : Mem) (previousPages : Nat)
      (hnotfit : ¬ allocatorRequiredPages newCapacity 1 oldBump ≤
        UInt32.ofNat store.wasm.mem.pages)
      (hgrow : store.wasm.mem.grow
          (allocatorRequiredPages newCapacity 1 oldBump -
            UInt32.ofNat store.wasm.mem.pages)
          (store.wasm.memoryCap store.runtime.currentModule 0) =
            some (memory, previousPages))
      (hfinishNonnegative :
        ¬ (allocatorFinish newCapacity 1 oldBump).toInt32 < UInt32.toInt32 0) :
      ByteGrowSuccess store oldCapacity oldPtr newCapacity oldBump
        (allocatorBumpStore (allocatorGrownStore store memory)
          (allocatorFinish newCapacity 1 oldBump))
  | reallocNoGrow (hnonzero : oldCapacity ≠ 0)
      (hfit : allocatorRequiredPages newCapacity 1 oldBump ≤
        UInt32.ofNat store.wasm.mem.pages) :
      ByteGrowSuccess store oldCapacity oldPtr newCapacity oldBump
        (reallocatorResultStore store oldPtr oldCapacity 1 newCapacity oldBump)
  | reallocGrow (hnonzero : oldCapacity ≠ 0) (memory : Mem)
      (previousPages : Nat)
      (hgrow : store.wasm.mem.grow
          (allocatorRequiredPages newCapacity 1 oldBump -
            UInt32.ofNat store.wasm.mem.pages)
          (store.wasm.memoryCap store.runtime.currentModule 0) =
            some (memory, previousPages)) :
      ByteGrowSuccess store oldCapacity oldPtr newCapacity oldBump
        (reallocatorResultStore (allocatorGrownStore store memory)
          oldPtr oldCapacity 1 newCapacity oldBump)

theorem ByteGrowSuccess.pages_mono
    {store final : MachineStore Universal.State}
    {oldCapacity oldPtr newCapacity oldBump : UInt32}
    (h : ByteGrowSuccess store oldCapacity oldPtr newCapacity oldBump final) :
    store.wasm.mem.pages ≤ final.wasm.mem.pages := by
  cases h with
  | freshNoGrow hzero hfit hfinishNonnegative => simp [allocatorBumpStore]
  | freshGrow hzero memory previousPages hnotfit hgrow hfinishNonnegative =>
      have hfacts := mem_grow_some_facts store.wasm.mem memory
        (allocatorRequiredPages newCapacity 1 oldBump -
          UInt32.ofNat store.wasm.mem.pages)
        (store.wasm.memoryCap store.runtime.currentModule 0)
        previousPages hgrow
      simp [allocatorBumpStore, allocatorGrownStore, hfacts.2]
  | reallocNoGrow hnonzero hfit => simp
  | reallocGrow hnonzero memory previousPages hgrow =>
      have hfacts := mem_grow_some_facts store.wasm.mem memory
        (allocatorRequiredPages newCapacity 1 oldBump -
          UInt32.ofNat store.wasm.mem.pages)
        (store.wasm.memoryCap store.runtime.currentModule 0)
        previousPages hgrow
      simp [allocatorGrownStore, hfacts.2]

theorem ByteGrowSuccess.globalAt_eq
    {store final : MachineStore Universal.State}
    {oldCapacity oldPtr newCapacity oldBump : UInt32}
    (h : ByteGrowSuccess store oldCapacity oldPtr newCapacity oldBump final)
    (index : Nat) :
    globalAt? final index = globalAt? store index := by
  cases h with
  | freshNoGrow hzero hfit hfinishNonnegative => rfl
  | freshGrow hzero memory previousPages hnotfit hgrow hfinishNonnegative => rfl
  | reallocNoGrow hnonzero hfit =>
      simp only [reallocatorResultStore]
      split <;> rfl
  | reallocGrow hnonzero memory previousPages hgrow =>
      simp only [reallocatorResultStore]
      split <;> rfl

theorem ByteGrowSuccess.runtime_eq
    {store final : MachineStore Universal.State}
    {oldCapacity oldPtr newCapacity oldBump : UInt32}
    (h : ByteGrowSuccess store oldCapacity oldPtr newCapacity oldBump final) :
    final.runtime = store.runtime := by
  cases h with
  | freshNoGrow hzero hfit hfinishNonnegative => rfl
  | freshGrow hzero memory previousPages hnotfit hgrow hfinishNonnegative => rfl
  | reallocNoGrow hnonzero hfit =>
      exact reallocatorResultStore_runtime _ _ _ _ _ _
  | reallocGrow hnonzero memory previousPages hgrow =>
      exact (reallocatorResultStore_runtime _ _ _ _ _ _).trans rfl

@[simp] theorem growResultOkStore_globalAt
    (store : MachineStore Universal.State) (out ptr size : UInt32)
    (index : Nat) :
    globalAt? (growResultOkStore store out ptr size) index =
      globalAt? store index := by
  rfl

theorem byte_grow_call_outcome
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (out oldCapacity oldPtr newCapacity oldBump : UInt32)
    (hmod : store.runtime.currentModule = «module»)
    (henv : store.runtime.currentHost = Universal.envFor «module»)
    (hread : store.wasm.mem.read32 1053960 = oldBump)
    (hbound : 1053960 + 4 ≤ store.wasm.mem.pages * 65536)
    (hpages : store.wasm.mem.pages < 4294967295)
    (hnonneg : ¬ newCapacity.toInt32 < UInt32.toInt32 0)
    (hptr : allocatorPtr oldBump 1 ≠ 0)
    (hout : out.toNat + 12 ≤ store.wasm.mem.pages * 65536)
    (hsource : oldPtr.toNat +
        (reallocatorCopyLen oldCapacity newCapacity).toNat ≤
      store.wasm.mem.pages * 65536)
    (hdestination : allocatorRequiredPages newCapacity 1 oldBump ≤
        UInt32.ofNat store.wasm.mem.pages →
      (allocatorPtr oldBump 1).toNat +
          (reallocatorCopyLen oldCapacity newCapacity).toNat ≤
        store.wasm.mem.pages * 65536)
    (hgrownBounds : ∀ memory previousPages,
      store.wasm.mem.grow
          (allocatorRequiredPages newCapacity 1 oldBump -
            UInt32.ofNat store.wasm.mem.pages)
          (store.wasm.memoryCap store.runtime.currentModule 0) =
            some (memory, previousPages) →
      oldPtr.toNat + (reallocatorCopyLen oldCapacity newCapacity).toNat ≤
          memory.pages * 65536 ∧
      (allocatorPtr oldBump 1).toNat +
          (reallocatorCopyLen oldCapacity newCapacity).toNat ≤
          memory.pages * 65536) :
    (∃ allocStore,
      ByteGrowSuccess store oldCapacity oldPtr newCapacity oldBump allocStore ∧
      Reaches
        ⟨.running
          ⟨⟨outerParams, outerLocalValues,
              [.i32 newCapacity, .i32 oldPtr, .i32 oldCapacity, .i32 out] ++
                stack⟩,
            [.call 7] ++ code, arity, remainder, controls, calls⟩,
          store⟩
        (growResultFinal
          (growResultOkStore allocStore out (allocatorPtr oldBump 1)
            newCapacity)
          outerParams outerLocalValues stack code arity remainder controls
          calls)) ∨
    TrapsWith
      ⟨.running
        ⟨⟨outerParams, outerLocalValues,
            [.i32 newCapacity, .i32 oldPtr, .i32 oldCapacity, .i32 out] ++
              stack⟩,
          [.call 7] ++ code, arity, remainder, controls, calls⟩,
        store⟩
      (.host OOM.trapMessage)
      (fun final => final.wasm.host.oom.raised = true) := by
  by_cases hzero : oldCapacity = 0
  · subst oldCapacity
    rcases grow_result_fresh_outcome store outerParams outerLocalValues stack
      code arity remainder controls calls out oldPtr newCapacity oldBump hmod
      henv hread hbound hpages hnonneg hptr hout with
      (⟨hfit, hfinishNonnegative, hreach⟩ |
        ⟨memory, previousPages, hnotfit, hgrow, hfinishNonnegative, hreach⟩) | htrap
    · left
      exact ⟨allocatorBumpStore store
          (allocatorFinish newCapacity 1 oldBump),
        .freshNoGrow rfl hfit hfinishNonnegative, hreach⟩
    · left
      exact ⟨allocatorBumpStore (allocatorGrownStore store memory)
          (allocatorFinish newCapacity 1 oldBump),
        .freshGrow rfl memory previousPages hnotfit hgrow hfinishNonnegative,
        hreach⟩
    · exact Or.inr htrap
  · rcases grow_result_realloc_outcome store outerParams outerLocalValues stack
      code arity remainder controls calls out oldCapacity oldPtr newCapacity
      oldBump hmod henv hread hbound hpages hnonneg hzero hptr hout hsource
      hdestination hgrownBounds with
      (⟨hfit, hreach⟩ | ⟨memory, previousPages, hgrow, hreach⟩) | htrap
    · left
      exact ⟨reallocatorResultStore store oldPtr oldCapacity 1 newCapacity
          oldBump, .reallocNoGrow hzero hfit, hreach⟩
    · left
      exact ⟨reallocatorResultStore (allocatorGrownStore store memory)
          oldPtr oldCapacity 1 newCapacity oldBump,
        .reallocGrow hzero memory previousPages hgrow, hreach⟩
    · exact Or.inr htrap

set_option maxHeartbeats 4000000 in
theorem reserve_to_grow_call
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (vector length additional capacity data sp : UInt32)
    (hmod : store.runtime.currentModule = «module»)
    (hglobal : globalAt? store 0 = some (.i32 sp))
    (hsum : reserveRequired length additional ≥ additional)
    (hcapacity : store.wasm.mem.read32 vector = capacity)
    (hdata : store.wasm.mem.read32 (vector + 4) = data)
    (hcapBound : vector.toNat + 4 ≤ store.wasm.mem.pages * 65536)
    (hdataBound : vector.toNat + 4 + 4 ≤
      store.wasm.mem.pages * 65536) :
    Reaches
      ⟨.running
        ⟨⟨outerParams, outerLocalValues,
            [.i32 additional, .i32 length, .i32 vector] ++ stack⟩,
          [.call 5] ++ code, arity, remainder, controls, calls⟩,
        store⟩
      (reserveGrowCall store outerParams outerLocalValues stack code arity
        remainder controls calls vector length additional capacity data sp) := by
  have hnot : ¬5 < store.runtime.currentModule.imports.length := by
    rw [hmod]; decide
  have hfn : store.runtime.currentModule.funcs[
      5 - store.runtime.currentModule.imports.length]? = some func2Def := by
    rw [hmod]; rfl
  apply Reaches.prepend (Step.call hnot hfn)
  simp [func2Def, Function.toLocals, Function.numParams,
    func2_prefix_split]
  apply Reaches.prepend (Step.globalGet hglobal)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.sub
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend (Step.globalSet (by simp [hglobal]))
  rw [setGlobal_zero_eq]
  apply Reaches.prepend Step.block
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.add
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend (Step.localGet rfl)
  have hsum' : length + additional ≥ additional := by
    simpa only [reserveRequired] using hsum
  apply Reaches.prepend (Step.geU (result := 1)
    (Eq.symm (if_pos hsum')))
  apply Reaches.prepend (Step.brIf (condition := 1) (by decide) rfl)
  simp [reserveRequired]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.add
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load32 (address := vector) (offset := 0)
    (by simpa [reserveFrameStore] using hcapBound))
  simp only [reserveFrameStore, UInt32.add_zero, hcapacity]
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load32 (address := vector) (offset := 4)
    (by simpa [reserveFrameStore] using hdataBound))
  simp only [reserveFrameStore, hdata]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.shl
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.gtU
    (result := if reserveRequired length additional >
        reserveDoubled capacity then 1 else 0) (by
      simp [reserveRequired, reserveDoubled]))
  apply Reaches.prepend (Step.select (selected := .i32
    (reserveCandidate length additional capacity)) (by
      by_cases h : capacity <<< 1 < length + additional
      · simp [reserveCandidate, reserveRequired, reserveDoubled, h]
      · simp [reserveCandidate, reserveRequired, reserveDoubled, h]))
  apply Reaches.prepend (Step.localTee rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.gtU
    (result := if reserveCandidate length additional capacity > 8
      then 1 else 0) (by simp))
  apply Reaches.prepend (Step.select (selected := .i32
    (reserveNewCapacity length additional capacity)) (by
      by_cases h : (8 : UInt32) < reserveCandidate length additional capacity
      · simp [reserveNewCapacity, h]
      · simp [reserveNewCapacity, h]))
  apply Reaches.prepend (Step.localTee rfl)
  rw [show 4 + (sp - 16) = (sp - 16) + 4 by bv_decide]
  simp [reserveGrowCall, reserveFrameStore, reserveNewCapacity,
    reserveCandidate, reserveRequired, reserveDoubled]
  exact ⟨[], .refl _⟩

theorem reserve_success_suffix
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (returningInstance : ModuleInstanceId)
    (vector required newCapacity data frame sp : UInt32)
    (htag : store.wasm.mem.read32 (frame + 4) = 0)
    (hdata : store.wasm.mem.read32 (frame + 8) = data)
    (htagBound : frame.toNat + 4 + 4 ≤ store.wasm.mem.pages * 65536)
    (hdataBound : frame.toNat + 8 + 4 ≤ store.wasm.mem.pages * 65536)
    (hvectorBound : vector.toNat + 4 ≤ store.wasm.mem.pages * 65536)
    (hvectorDataBound : vector.toNat + 4 + 4 ≤
      store.wasm.mem.pages * 65536)
    (hglobal : (globalAt? store 0).isSome = true)
    (hreturn : returningInstance = store.runtime.entry)
    (hrestore : frame + 16 = sp) :
    Reaches
      ⟨.running
        ⟨⟨[.i32 vector, .i32 required, .i32 newCapacity], [.i32 frame], []⟩,
          reserveAfterGrow, 0, [], [],
          { locals := ⟨outerParams, outerLocalValues, stack⟩
            continuation := code
            resultArity := arity
            callerRemainder := remainder
            control := controls
            returningInstance := returningInstance } :: calls⟩,
        store⟩
      (growResultFinal (reserveFinishStore store vector data newCapacity sp)
        outerParams outerLocalValues stack code arity remainder controls calls) := by
  simp only [reserveAfterGrow, func2, List.drop]
  apply Reaches.prepend Step.block
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load32 (address := frame) (offset := 4) htagBound)
  simp only [htag]
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.ne (result := 1) (by simp))
  apply Reaches.prepend (Step.brIf (condition := 1) (by decide) rfl)
  simp
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.load32 (address := frame) (offset := 8) hdataBound)
  simp only [hdata]
  apply Reaches.prepend (Step.localSet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend
    (Step.store32 (address := vector) (offset := 0) hvectorBound)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend
    (Step.store32 (address := vector) (offset := 4) (by
      simpa [setMemory_eq] using hvectorDataBound))
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend Step.add
  have hrestore' : 16 + frame = sp := by
    rw [show 16 + frame = frame + 16 by bv_decide, hrestore]
  rw [hrestore']
  apply Reaches.prepend (Step.globalSet (by
    simpa [setMemory_eq, globalAt?] using hglobal))
  rw [setGlobal_zero_eq]
  apply Reaches.prepend (Step.returnFromCallFallthrough hreturn)
  simp [growResultFinal, reserveFinishStore, reserveVectorStore,
    setMemory_eq]
  exact ⟨[], .refl _⟩

theorem reserve_call_outcome
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (vector length additional capacity data sp oldBump : UInt32)
    (hmod : store.runtime.currentModule = «module»)
    (henv : store.runtime.currentHost = Universal.envFor «module»)
    (hglobal : globalAt? store 0 = some (.i32 sp))
    (hsum : reserveRequired length additional ≥ additional)
    (hcapacity : store.wasm.mem.read32 vector = capacity)
    (hdata : store.wasm.mem.read32 (vector + 4) = data)
    (hbump : store.wasm.mem.read32 1053960 = oldBump)
    (hbumpBound : 1053960 + 4 ≤ store.wasm.mem.pages * 65536)
    (hpages : store.wasm.mem.pages ≤ 65536)
    (hnonneg : ¬ (reserveNewCapacity length additional capacity).toInt32 <
      UInt32.toInt32 0)
    (hptr : allocatorPtr oldBump 1 ≠ 0)
    (hframe : (sp - 16).toNat + 16 ≤ store.wasm.mem.pages * 65536)
    (houtNoWrap : ((sp - 16) + 4).toNat = (sp - 16).toNat + 4)
    (houtNext : (((sp - 16) + 4) + 4).toNat =
      ((sp - 16) + 4).toNat + 4)
    (hrestore : (sp - 16) + 16 = sp)
    (hvectorBound : vector.toNat + 4 ≤ store.wasm.mem.pages * 65536)
    (hvectorDataBound : vector.toNat + 4 + 4 ≤
      store.wasm.mem.pages * 65536)
    (hsource : data.toNat +
        (reallocatorCopyLen capacity
          (reserveNewCapacity length additional capacity)).toNat ≤
      store.wasm.mem.pages * 65536)
    (hdestination : allocatorRequiredPages
          (reserveNewCapacity length additional capacity) 1 oldBump ≤
        UInt32.ofNat store.wasm.mem.pages →
      (allocatorPtr oldBump 1).toNat +
          (reallocatorCopyLen capacity
            (reserveNewCapacity length additional capacity)).toNat ≤
        store.wasm.mem.pages * 65536)
    (hgrownBounds : ∀ memory previousPages,
      store.wasm.mem.grow
          (allocatorRequiredPages
              (reserveNewCapacity length additional capacity) 1 oldBump -
            UInt32.ofNat store.wasm.mem.pages)
          (store.wasm.memoryCap store.runtime.currentModule 0) =
            some (memory, previousPages) →
      data.toNat +
          (reallocatorCopyLen capacity
            (reserveNewCapacity length additional capacity)).toNat ≤
            memory.pages * 65536 ∧
      (allocatorPtr oldBump 1).toNat +
          (reallocatorCopyLen capacity
            (reserveNewCapacity length additional capacity)).toNat ≤
            memory.pages * 65536) :
    (∃ allocStore,
      ByteGrowSuccess (reserveFrameStore store (sp - 16)) capacity data
          (reserveNewCapacity length additional capacity) oldBump allocStore ∧
      Reaches
        ⟨.running
          ⟨⟨outerParams, outerLocalValues,
              [.i32 additional, .i32 length, .i32 vector] ++ stack⟩,
            [.call 5] ++ code, arity, remainder, controls, calls⟩,
          store⟩
        (growResultFinal
          (reserveFinishStore
            (growResultOkStore allocStore ((sp - 16) + 4)
              (allocatorPtr oldBump 1)
              (reserveNewCapacity length additional capacity))
            vector (allocatorPtr oldBump 1)
              (reserveNewCapacity length additional capacity) sp)
          outerParams outerLocalValues stack code arity remainder controls
          calls)) ∨
    TrapsWith
      ⟨.running
        ⟨⟨outerParams, outerLocalValues,
            [.i32 additional, .i32 length, .i32 vector] ++ stack⟩,
          [.call 5] ++ code, arity, remainder, controls, calls⟩,
        store⟩
      (.host OOM.trapMessage)
      (fun final => final.wasm.host.oom.raised = true) := by
  let initial : Config Universal.State :=
    ⟨.running
      ⟨⟨outerParams, outerLocalValues,
          [.i32 additional, .i32 length, .i32 vector] ++ stack⟩,
        [.call 5] ++ code, arity, remainder, controls, calls⟩,
      store⟩
  let base := reserveFrameStore store (sp - 16)
  let newCapacity := reserveNewCapacity length additional capacity
  let out := (sp - 16) + 4
  have hprefix : Reaches initial
      (reserveGrowCall store outerParams outerLocalValues stack code arity
        remainder controls calls vector length additional capacity data sp) :=
    reserve_to_grow_call store outerParams outerLocalValues stack code arity
      remainder controls calls vector length additional capacity data sp hmod
      hglobal hsum hcapacity hdata hvectorBound hvectorDataBound
  have hbaseMod : base.runtime.currentModule = «module» := by
    simpa [base, reserveFrameStore] using hmod
  have hbaseEnv : base.runtime.currentHost = Universal.envFor «module» := by
    simpa [base, reserveFrameStore] using henv
  have hbaseBump : base.wasm.mem.read32 1053960 = oldBump := by
    simpa [base, reserveFrameStore] using hbump
  have hbaseBumpBound : 1053960 + 4 ≤ base.wasm.mem.pages * 65536 := by
    simpa [base, reserveFrameStore] using hbumpBound
  have hbasePages : base.wasm.mem.pages < 4294967295 := by
    have : base.wasm.mem.pages ≤ 65536 := by
      simpa [base, reserveFrameStore] using hpages
    omega
  have houtBound : out.toNat + 12 ≤ base.wasm.mem.pages * 65536 := by
    simp only [out, base, reserveFrameStore]
    rw [houtNoWrap]
    exact hframe
  have hbaseSource : data.toNat +
      (reallocatorCopyLen capacity newCapacity).toNat ≤
        base.wasm.mem.pages * 65536 := by
    simpa [base, reserveFrameStore, newCapacity] using hsource
  have hbaseDestination : allocatorRequiredPages newCapacity 1 oldBump ≤
      UInt32.ofNat base.wasm.mem.pages →
    (allocatorPtr oldBump 1).toNat +
        (reallocatorCopyLen capacity newCapacity).toNat ≤
      base.wasm.mem.pages * 65536 := by
    simpa [base, reserveFrameStore, newCapacity] using hdestination
  have hbaseGrown : ∀ memory previousPages,
      base.wasm.mem.grow
          (allocatorRequiredPages newCapacity 1 oldBump -
            UInt32.ofNat base.wasm.mem.pages)
          (base.wasm.memoryCap base.runtime.currentModule 0) =
            some (memory, previousPages) →
      data.toNat + (reallocatorCopyLen capacity newCapacity).toNat ≤
          memory.pages * 65536 ∧
      (allocatorPtr oldBump 1).toNat +
          (reallocatorCopyLen capacity newCapacity).toNat ≤
          memory.pages * 65536 := by
    intro memory previousPages hgrow
    apply hgrownBounds memory previousPages
    simpa only [base, newCapacity, reserveFrameStore_memoryCap,
      reserveFrameStore_runtime, reserveFrameStore_mem] using hgrow
  have hgrow := byte_grow_call_outcome base
    ([.i32 vector, .i32 (reserveRequired length additional), .i32 newCapacity])
    [.i32 (sp - 16)] [] reserveAfterGrow 0 [] []
    ({ locals := ⟨outerParams, outerLocalValues, stack⟩
       continuation := code
       resultArity := arity
       callerRemainder := remainder
       control := controls
       returningInstance := store.runtime.entry } :: calls)
    out capacity data newCapacity oldBump hbaseMod hbaseEnv hbaseBump
    hbaseBumpBound hbasePages (by simpa [newCapacity] using hnonneg) hptr
    houtBound hbaseSource hbaseDestination hbaseGrown
  rcases hgrow with ⟨allocStore, hsuccess, hreach⟩ | htrap
  · left
    refine ⟨allocStore, hsuccess, ?_⟩
    have hcall : Reaches
        (reserveGrowCall store outerParams outerLocalValues stack code arity
          remainder controls calls vector length additional capacity data sp)
        (growResultFinal
          (growResultOkStore allocStore out (allocatorPtr oldBump 1)
            newCapacity)
          [.i32 vector, .i32 (reserveRequired length additional),
            .i32 newCapacity]
          [.i32 (sp - 16)] [] reserveAfterGrow 0 [] []
          ({ locals := ⟨outerParams, outerLocalValues, stack⟩
             continuation := code
             resultArity := arity
             callerRemainder := remainder
             control := controls
             returningInstance := store.runtime.entry } :: calls)) := by
      simpa [reserveGrowCall, base, out, newCapacity] using hreach
    let postGrow := growResultOkStore allocStore out
      (allocatorPtr oldBump 1) newCapacity
    have hmono := hsuccess.pages_mono
    have hbasePagesEq : base.wasm.mem.pages = store.wasm.mem.pages := by
      rfl
    have hpostPages : postGrow.wasm.mem.pages = allocStore.wasm.mem.pages := by
      simp [postGrow]
    have htag : postGrow.wasm.mem.read32 ((sp - 16) + 4) = 0 := by
      simpa [postGrow, out] using growResultOkStore_read_tag allocStore out
        (allocatorPtr oldBump 1) newCapacity
    have hdata' : postGrow.wasm.mem.read32 ((sp - 16) + 8) =
        allocatorPtr oldBump 1 := by
      rw [show (sp - 16) + 8 = out + 4 by simp [out]; bv_decide]
      exact growResultOkStore_read_ptr allocStore out
        (allocatorPtr oldBump 1) newCapacity houtNext
    have hpostGlobal : (globalAt? postGrow 0).isSome = true := by
      have hbaseGlobal := reserveFrameStore_global_zero store (sp - 16) sp
        hglobal
      have hallocGlobal := hsuccess.globalAt_eq 0
      have hallocSome : (globalAt? allocStore 0).isSome = true := by
        rw [hallocGlobal, hbaseGlobal]
        rfl
      simpa [postGrow] using hallocSome
    have hpostRuntime : postGrow.runtime = store.runtime := by
      calc
        postGrow.runtime = allocStore.runtime := by rfl
        _ = base.runtime := hsuccess.runtime_eq
        _ = store.runtime := by rfl
    have hpostFrame4 : (sp - 16).toNat + 4 + 4 ≤
        postGrow.wasm.mem.pages * 65536 := by
      rw [hpostPages]
      calc
        (sp - 16).toNat + 4 + 4 ≤ store.wasm.mem.pages * 65536 := by omega
        _ = base.wasm.mem.pages * 65536 := by rw [hbasePagesEq]
        _ ≤ allocStore.wasm.mem.pages * 65536 := Nat.mul_le_mul_right _ hmono
    have hpostFrame8 : (sp - 16).toNat + 8 + 4 ≤
        postGrow.wasm.mem.pages * 65536 := by
      rw [hpostPages]
      calc
        (sp - 16).toNat + 8 + 4 ≤ store.wasm.mem.pages * 65536 := by omega
        _ = base.wasm.mem.pages * 65536 := by rw [hbasePagesEq]
        _ ≤ allocStore.wasm.mem.pages * 65536 := Nat.mul_le_mul_right _ hmono
    have hpostVector : vector.toNat + 4 ≤
        postGrow.wasm.mem.pages * 65536 := by
      rw [hpostPages]
      calc
        vector.toNat + 4 ≤ store.wasm.mem.pages * 65536 := hvectorBound
        _ = base.wasm.mem.pages * 65536 := by rw [hbasePagesEq]
        _ ≤ allocStore.wasm.mem.pages * 65536 := Nat.mul_le_mul_right _ hmono
    have hpostVectorData : vector.toNat + 4 + 4 ≤
        postGrow.wasm.mem.pages * 65536 := by
      rw [hpostPages]
      calc
        vector.toNat + 4 + 4 ≤ store.wasm.mem.pages * 65536 :=
          hvectorDataBound
        _ = base.wasm.mem.pages * 65536 := by rw [hbasePagesEq]
        _ ≤ allocStore.wasm.mem.pages * 65536 := Nat.mul_le_mul_right _ hmono
    have hsuffix := reserve_success_suffix postGrow outerParams
      outerLocalValues stack code arity remainder controls calls
      store.runtime.entry vector
      (reserveRequired length additional) newCapacity (allocatorPtr oldBump 1)
      (sp - 16) sp htag hdata' hpostFrame4 hpostFrame8 hpostVector
      hpostVectorData hpostGlobal (by rw [hpostRuntime]) hrestore
    simpa [initial, postGrow, out, newCapacity] using
      hprefix.trans (hcall.trans hsuffix)
  · right
    have hcallTrap : TrapsWith
        (reserveGrowCall store outerParams outerLocalValues stack code arity
          remainder controls calls vector length additional capacity data sp)
        (.host OOM.trapMessage)
        (fun final => final.wasm.host.oom.raised = true) := by
      simpa [reserveGrowCall, base, out, newCapacity] using htrap
    have hfull := TrapsWith.prependReaches hprefix hcallTrap
    simpa [initial] using hfull

end Submission.HexDecodeStdio
