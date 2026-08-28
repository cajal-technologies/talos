import HexDecodeStdio.ReallocatorOperational

namespace Submission.HexDecodeStdio

open Wasm Project.HexStdio Project.HexStdio.Spec
open Wasm.SmallStep

/-! Operational composition for Rust's `RawVec` allocation-result wrapper
(module function 7 / generated `func4Def`).  Keeping this boundary in the
small-step semantics preserves the distinguished OOM trap. -/

def growResultDispatch : Program :=
  [.localGet 1, .eqz, .br_if 0,
    .localGet 2, .localGet 1, .const 1, .localGet 3, .call 18,
    .localSet 1, .br 1]

def growResultAllocate : Program :=
  [.block 0 0 growResultDispatch,
    .call 14, .localGet 3, .const 1, .call 15, .localSet 1]

def growResultCheck : Program :=
  [.localGet 1, .br_if 0,
    .localGet 0, .localGet 3, .store32 8,
    .localGet 0, .const 1, .store32 4,
    .localGet 0, .const 1, .store32 0, .ret]

def growResultSuccess : Program :=
  [.block 0 0 growResultCheck,
    .localGet 0, .localGet 3, .store32 8,
    .localGet 0, .localGet 1, .store32 4,
    .localGet 0, .const 0, .store32 0, .ret]

def growResultBody : Program :=
  [.localGet 3, .const 0, .ltS, .br_if 0,
    .block 0 0 growResultAllocate] ++ growResultSuccess

def growResultErrorTail : Program :=
  [.localGet 0, .const 0, .store32 4,
    .localGet 0, .const 1, .store32 0]

theorem func4_decomposition :
    func4 = [.block 0 0 growResultBody] ++ growResultErrorTail := by
  rfl

def growResultOuterControl : ControlFrame :=
  { kind := .block
    paramArity := 0
    resultArity := 0
    body := growResultBody
    continuation := growResultErrorTail
    belowStack := [] }

def growResultAllocateControl : ControlFrame :=
  { kind := .block
    paramArity := 0
    resultArity := 0
    body := growResultAllocate
    continuation := growResultSuccess
    belowStack := [] }

def growResultDispatchControl : ControlFrame :=
  { kind := .block
    paramArity := 0
    resultArity := 0
    body := growResultDispatch
    continuation :=
      [.call 14, .localGet 3, .const 1, .call 15, .localSet 1]
    belowStack := [] }

def growResultOkStore (store : MachineStore Universal.State)
    (out ptr newSize : UInt32) : MachineStore Universal.State :=
  let mem1 := store.wasm.mem.write32 (out + 8) newSize
  let mem2 := mem1.write32 (out + 4) ptr
  { store with wasm := { store.wasm with mem := mem2.write32 out 0 } }

@[simp] theorem reallocatorResultStore_runtime
    (store : MachineStore Universal.State)
    (oldPtr oldSize align newSize oldBump : UInt32) :
    (reallocatorResultStore store oldPtr oldSize align newSize oldBump).runtime =
      store.runtime := by
  simp only [reallocatorResultStore]
  split <;> rfl

@[simp] theorem reallocatorResultStore_pages
    (store : MachineStore Universal.State)
    (oldPtr oldSize align newSize oldBump : UInt32) :
    (reallocatorResultStore store oldPtr oldSize align newSize oldBump).wasm.mem.pages =
      store.wasm.mem.pages := by
  simp only [reallocatorResultStore]
  split <;> simp [allocatorBumpStore, Mem.copy]

def growResultFreshMiddle
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (out oldSize newSize : UInt32) : Config Universal.State :=
  ⟨.running
    ⟨⟨[.i32 out, .i32 0, .i32 oldSize, .i32 newSize], [], []⟩,
      [.call 14, .localGet 3, .const 1, .call 15, .localSet 1],
      0, [], [growResultAllocateControl, growResultOuterControl],
      { locals := ⟨outerParams, outerLocalValues, stack⟩
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls
        returningInstance := store.runtime.entry } :: calls⟩,
    store⟩

def growResultAllocatorCall
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (out oldSize newSize : UInt32) : Config Universal.State :=
  ⟨.running
    ⟨⟨[.i32 out, .i32 0, .i32 oldSize, .i32 newSize], [],
        [.i32 1, .i32 newSize]⟩,
      [.call 15, .localSet 1], 0, [],
      [growResultAllocateControl, growResultOuterControl],
      { locals := ⟨outerParams, outerLocalValues, stack⟩
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls
        returningInstance := store.runtime.entry } :: calls⟩,
    store⟩

def growResultAfterAllocator
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (out oldSize newSize ptr : UInt32) : Config Universal.State :=
  ⟨.running
    ⟨⟨[.i32 out, .i32 0, .i32 oldSize, .i32 newSize], [], [.i32 ptr]⟩,
      [.localSet 1], 0, [],
      [growResultAllocateControl, growResultOuterControl],
      { locals := ⟨outerParams, outerLocalValues, stack⟩
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls
        returningInstance := store.runtime.entry } :: calls⟩,
    store⟩

def growResultReallocatorCall
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (out oldCapacity oldPtr newSize : UInt32) : Config Universal.State :=
  ⟨.running
    ⟨⟨[.i32 out, .i32 oldCapacity, .i32 oldPtr, .i32 newSize], [],
        [.i32 newSize, .i32 1, .i32 oldCapacity, .i32 oldPtr]⟩,
      [.call 18, .localSet 1, .br 1], 0, [],
      [growResultDispatchControl, growResultAllocateControl,
        growResultOuterControl],
      { locals := ⟨outerParams, outerLocalValues, stack⟩
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls
        returningInstance := store.runtime.entry } :: calls⟩,
    store⟩

def growResultAfterReallocator
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (out oldCapacity oldPtr newSize ptr : UInt32) : Config Universal.State :=
  ⟨.running
    ⟨⟨[.i32 out, .i32 oldCapacity, .i32 oldPtr, .i32 newSize], [], [.i32 ptr]⟩,
      [.localSet 1, .br 1], 0, [],
      [growResultDispatchControl, growResultAllocateControl,
        growResultOuterControl],
      { locals := ⟨outerParams, outerLocalValues, stack⟩
        continuation := code
        resultArity := arity
        callerRemainder := remainder
        control := controls
        returningInstance := store.runtime.entry } :: calls⟩,
    store⟩

def growResultFinal
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame) :
    Config Universal.State :=
  ⟨.running
    ⟨⟨outerParams, outerLocalValues, stack⟩, code, arity, remainder,
      controls, calls⟩, store⟩

theorem grow_result_fresh_prefix
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (out oldSize newSize : UInt32)
    (hmod : store.runtime.currentModule = «module»)
    (hnonneg : ¬ newSize.toInt32 < UInt32.toInt32 0) :
    Reaches
      ⟨.running
        ⟨⟨outerParams, outerLocalValues,
            [.i32 newSize, .i32 oldSize, .i32 0, .i32 out] ++ stack⟩,
          [.call 7] ++ code, arity, remainder, controls, calls⟩,
        store⟩
      (growResultFreshMiddle store outerParams outerLocalValues stack code
        arity remainder controls calls out oldSize newSize) := by
  have hnot : ¬7 < store.runtime.currentModule.imports.length := by
    rw [hmod]; decide
  have hfn : store.runtime.currentModule.funcs[
      7 - store.runtime.currentModule.imports.length]? = some func4Def := by
    rw [hmod]; rfl
  apply Reaches.prepend (Step.call hnot hfn)
  simp [func4Def, Function.toLocals, Function.numParams,
    func4_decomposition, growResultBody]
  apply Reaches.prepend Step.block
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend
    (Step.ltS (result := 0) (Eq.symm (if_neg hnonneg)))
  apply Reaches.prepend Step.brIfZero
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.eqz (result := 1) (by simp))
  apply Reaches.prepend (Step.brIf (condition := 1) (by decide) rfl)
  simp [growResultFreshMiddle, growResultAllocateControl,
    growResultOuterControl, growResultAllocate, growResultDispatch,
    growResultSuccess, growResultCheck, growResultErrorTail]
  exact ⟨[], .refl _⟩

theorem grow_result_fresh_to_allocator
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (out oldSize newSize : UInt32)
    (hmod : store.runtime.currentModule = «module») :
    Reaches
      (growResultFreshMiddle store outerParams outerLocalValues stack code
        arity remainder controls calls out oldSize newSize)
      (growResultAllocatorCall store outerParams outerLocalValues stack code
        arity remainder controls calls out oldSize newSize) := by
  have hnot : ¬14 < store.runtime.currentModule.imports.length := by
    rw [hmod]; decide
  have hfn : store.runtime.currentModule.funcs[
      14 - store.runtime.currentModule.imports.length]? = some func11Def := by
    rw [hmod]; rfl
  simp only [growResultFreshMiddle]
  apply Reaches.prepend (Step.call hnot hfn)
  simp [func11Def, Function.toLocals, Function.numParams, func11]
  apply Reaches.prepend (Step.returnFromCallExplicit rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  simp [growResultAllocatorCall]
  exact ⟨[], .refl _⟩

theorem grow_result_realloc_prefix
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (out oldCapacity oldPtr newSize : UInt32)
    (hmod : store.runtime.currentModule = «module»)
    (hnonneg : ¬ newSize.toInt32 < UInt32.toInt32 0)
    (holdCapacity : oldCapacity ≠ 0) :
    Reaches
      ⟨.running
        ⟨⟨outerParams, outerLocalValues,
            [.i32 newSize, .i32 oldPtr, .i32 oldCapacity, .i32 out] ++ stack⟩,
          [.call 7] ++ code, arity, remainder, controls, calls⟩,
        store⟩
      (growResultReallocatorCall store outerParams outerLocalValues stack code
        arity remainder controls calls out oldCapacity oldPtr newSize) := by
  have hnot : ¬7 < store.runtime.currentModule.imports.length := by
    rw [hmod]; decide
  have hfn : store.runtime.currentModule.funcs[
      7 - store.runtime.currentModule.imports.length]? = some func4Def := by
    rw [hmod]; rfl
  apply Reaches.prepend (Step.call hnot hfn)
  simp [func4Def, Function.toLocals, Function.numParams,
    func4_decomposition, growResultBody]
  apply Reaches.prepend Step.block
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend
    (Step.ltS (result := 0) (Eq.symm (if_neg hnonneg)))
  apply Reaches.prepend Step.brIfZero
  apply Reaches.prepend Step.block
  apply Reaches.prepend Step.block
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.eqz (result := 0) (by simp [holdCapacity]))
  apply Reaches.prepend Step.brIfZero
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.localGet rfl)
  simp [growResultReallocatorCall, growResultDispatchControl,
    growResultAllocateControl, growResultOuterControl,
    growResultDispatch, growResultAllocate, growResultSuccess,
    growResultCheck, growResultErrorTail]
  exact ⟨[], .refl _⟩

theorem grow_result_realloc_success_suffix
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (out oldCapacity oldPtr newSize ptr : UInt32)
    (hptr : ptr ≠ 0)
    (hout8 : out.toNat + 8 + 4 ≤ store.wasm.mem.pages * 65536)
    (hout4 : out.toNat + 4 + 4 ≤ store.wasm.mem.pages * 65536)
    (hout0 : out.toNat + 4 ≤ store.wasm.mem.pages * 65536) :
    Reaches
      (growResultAfterReallocator store outerParams outerLocalValues stack code
        arity remainder controls calls out oldCapacity oldPtr newSize ptr)
      (growResultFinal (growResultOkStore store out ptr newSize)
        outerParams outerLocalValues stack code arity remainder controls calls) := by
  simp only [growResultAfterReallocator]
  apply Reaches.prepend (Step.localSet rfl)
  apply Reaches.prepend (Step.br rfl)
  apply Reaches.prepend Step.block
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.brIf (condition := ptr) hptr rfl)
  simp
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.store32 (address := out) (offset := 8) hout8)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.store32 (address := out) (offset := 4) (by
    simpa [setMemory_eq] using hout4))
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.store32 (address := out) (offset := 0) (by
    simpa [setMemory_eq] using hout0))
  apply Reaches.prepend (Step.returnFromCallExplicit rfl)
  simp [growResultFinal, growResultOkStore, setMemory_eq]
  exact ⟨[], .refl _⟩

theorem grow_result_success_suffix
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (out oldSize newSize ptr : UInt32)
    (hptr : ptr ≠ 0)
    (hout8 : out.toNat + 8 + 4 ≤ store.wasm.mem.pages * 65536)
    (hout4 : out.toNat + 4 + 4 ≤ store.wasm.mem.pages * 65536)
    (hout0 : out.toNat + 4 ≤ store.wasm.mem.pages * 65536) :
    Reaches
      (growResultAfterAllocator store outerParams outerLocalValues stack code
        arity remainder controls calls out oldSize newSize ptr)
      (growResultFinal (growResultOkStore store out ptr newSize)
        outerParams outerLocalValues stack code arity remainder controls calls) := by
  simp only [growResultAfterAllocator]
  apply Reaches.prepend (Step.localSet rfl)
  apply Reaches.prepend (Step.exitControl rfl)
  apply Reaches.prepend Step.block
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.brIf (condition := ptr) hptr rfl)
  simp [growResultSuccess, growResultCheck]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.store32 (address := out) (offset := 8) hout8)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.store32 (address := out) (offset := 4) (by
    simpa [setMemory_eq] using hout4))
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend (Step.store32 (address := out) (offset := 0) (by
    simpa [setMemory_eq] using hout0))
  apply Reaches.prepend (Step.returnFromCallExplicit rfl)
  simp [growResultFinal, growResultOkStore, setMemory_eq]
  exact ⟨[], .refl _⟩

/-- Exact outcome of function 7 when growing an as-yet unallocated byte
vector.  Successful memory growth and the no-growth case are kept separate so
callers can retain a concrete memory; all allocator failures are the public
OOM trap. -/
theorem grow_result_fresh_outcome
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (out oldSize newSize oldBump : UInt32)
    (hmod : store.runtime.currentModule = «module»)
    (henv : store.runtime.currentHost = Universal.envFor «module»)
    (hread : store.wasm.mem.read32 1053960 = oldBump)
    (hbound : 1053960 + 4 ≤ store.wasm.mem.pages * 65536)
    (hpages : store.wasm.mem.pages < 4294967295)
    (hnonneg : ¬ newSize.toInt32 < UInt32.toInt32 0)
    (hptr : allocatorPtr oldBump 1 ≠ 0)
    (hout : out.toNat + 12 ≤ store.wasm.mem.pages * 65536) :
    ((¬(allocatorFinish newSize 1 oldBump).toInt32 < UInt32.toInt32 0) ∧
      (((allocatorRequiredPages newSize 1 oldBump ≤
          UInt32.ofNat store.wasm.mem.pages) ∧ Reaches
        ⟨.running
          ⟨⟨outerParams, outerLocalValues,
              [.i32 newSize, .i32 oldSize, .i32 0, .i32 out] ++ stack⟩,
            [.call 7] ++ code, arity, remainder, controls, calls⟩,
          store⟩
        (growResultFinal
          (growResultOkStore
            (allocatorBumpStore store
              (allocatorFinish newSize 1 oldBump))
            out (allocatorPtr oldBump 1) newSize)
          outerParams outerLocalValues stack code arity remainder controls
          calls)) ∨
      ∃ memory previousPages,
        store.wasm.mem.grow
            (allocatorRequiredPages newSize 1 oldBump -
              UInt32.ofNat store.wasm.mem.pages)
            (store.wasm.memoryCap store.runtime.currentModule 0) =
              some (memory, previousPages) ∧
        Reaches
          ⟨.running
            ⟨⟨outerParams, outerLocalValues,
                [.i32 newSize, .i32 oldSize, .i32 0, .i32 out] ++ stack⟩,
              [.call 7] ++ code, arity, remainder, controls, calls⟩,
            store⟩
          (growResultFinal
            (growResultOkStore
              (allocatorBumpStore (allocatorGrownStore store memory)
                (allocatorFinish newSize 1 oldBump))
              out (allocatorPtr oldBump 1) newSize)
            outerParams outerLocalValues stack code arity remainder controls
            calls))) ∨
      TrapsWith
        ⟨.running
          ⟨⟨outerParams, outerLocalValues,
              [.i32 newSize, .i32 oldSize, .i32 0, .i32 out] ++ stack⟩,
            [.call 7] ++ code, arity, remainder, controls, calls⟩,
          store⟩
        (.host OOM.trapMessage)
        (fun final => final.wasm.host.oom.raised = true) := by
  let initial : Config Universal.State :=
    ⟨.running
      ⟨⟨outerParams, outerLocalValues,
          [.i32 newSize, .i32 oldSize, .i32 0, .i32 out] ++ stack⟩,
        [.call 7] ++ code, arity, remainder, controls, calls⟩,
      store⟩
  have hprefix : Reaches initial
      (growResultAllocatorCall store outerParams outerLocalValues stack code
        arity remainder controls calls out oldSize newSize) :=
    (grow_result_fresh_prefix store outerParams outerLocalValues stack code
      arity remainder controls calls out oldSize newSize hmod hnonneg).trans
    (grow_result_fresh_to_allocator store outerParams outerLocalValues stack
      code arity remainder controls calls out oldSize newSize hmod)
  have halloc := allocator_call_outcome store
    ([.i32 out, .i32 0, .i32 oldSize, .i32 newSize]) [] []
    [.localSet 1] 0 []
    [growResultAllocateControl, growResultOuterControl]
    ({ locals := ⟨outerParams, outerLocalValues, stack⟩
       continuation := code
       resultArity := arity
       callerRemainder := remainder
       control := controls
       returningInstance := store.runtime.entry } :: calls)
    newSize 1 oldBump hmod henv hread hbound hpages
  rcases halloc with ⟨hsafe, (⟨henough, halloc⟩ |
      ⟨memory, previousPages, hgrow, halloc⟩)⟩ | htrap
  · left
    refine ⟨hsafe, Or.inl ?_⟩
    refine ⟨henough, ?_⟩
    have hafter : Reaches
        (growResultAllocatorCall store outerParams outerLocalValues stack code
          arity remainder controls calls out oldSize newSize)
        (growResultAfterAllocator
          (allocatorBumpStore store (allocatorFinish newSize 1 oldBump))
          outerParams outerLocalValues stack code arity remainder controls calls
          out oldSize newSize (allocatorPtr oldBump 1)) := by
      simpa [growResultAllocatorCall, growResultAfterAllocator,
        allocatorBumpStore, allocatorGrownStore] using halloc
    have hsuffix := grow_result_success_suffix
        (allocatorBumpStore store (allocatorFinish newSize 1 oldBump))
        outerParams outerLocalValues stack code arity remainder controls calls
        out oldSize newSize (allocatorPtr oldBump 1) hptr
        (by simpa [allocatorBumpStore] using (show out.toNat + 8 + 4 ≤
          store.wasm.mem.pages * 65536 by omega)
        )
        (by simpa [allocatorBumpStore] using (show out.toNat + 4 + 4 ≤
          store.wasm.mem.pages * 65536 by omega)
        )
        (by simpa [allocatorBumpStore] using (show out.toNat + 4 ≤
          store.wasm.mem.pages * 65536 by omega)
        )
    simpa [initial] using hprefix.trans (hafter.trans hsuffix)
  · left
    refine ⟨hsafe, Or.inr ?_⟩
    refine ⟨memory, previousPages, hgrow, ?_⟩
    have hfacts := mem_grow_some_facts store.wasm.mem memory
      (allocatorRequiredPages newSize 1 oldBump -
        UInt32.ofNat store.wasm.mem.pages)
      (store.wasm.memoryCap store.runtime.currentModule 0)
      previousPages hgrow
    have houtGrown : out.toNat + 12 ≤ memory.pages * 65536 := by
      calc
        out.toNat + 12 ≤ store.wasm.mem.pages * 65536 := hout
        _ ≤ memory.pages * 65536 := by rw [hfacts.2]; omega
    have hafter : Reaches
        (growResultAllocatorCall store outerParams outerLocalValues stack code
          arity remainder controls calls out oldSize newSize)
        (growResultAfterAllocator
          (allocatorBumpStore (allocatorGrownStore store memory)
            (allocatorFinish newSize 1 oldBump))
          outerParams outerLocalValues stack code arity remainder controls calls
          out oldSize newSize (allocatorPtr oldBump 1)) := by
      simpa [growResultAllocatorCall, growResultAfterAllocator,
        allocatorBumpStore, allocatorGrownStore] using halloc
    have hsuffix := grow_result_success_suffix
        (allocatorBumpStore (allocatorGrownStore store memory)
          (allocatorFinish newSize 1 oldBump))
        outerParams outerLocalValues stack code arity remainder controls calls
        out oldSize newSize (allocatorPtr oldBump 1) hptr
        (by simpa [allocatorBumpStore, allocatorGrownStore] using
        (show out.toNat + 8 + 4 ≤ memory.pages * 65536 by omega)
        )
        (by simpa [allocatorBumpStore, allocatorGrownStore] using
        (show out.toNat + 4 + 4 ≤ memory.pages * 65536 by omega)
        )
        (by simpa [allocatorBumpStore, allocatorGrownStore] using
        (show out.toNat + 4 ≤ memory.pages * 65536 by omega)
        )
    simpa [initial] using hprefix.trans (hafter.trans hsuffix)
  · right
    have hfull := TrapsWith.prependReaches hprefix (by
      simpa [growResultAllocatorCall] using htrap)
    simpa [initial] using hfull

/-- Exact outcome of function 7 when it reallocates an existing byte vector. -/
theorem grow_result_realloc_outcome
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (out oldCapacity oldPtr newSize oldBump : UInt32)
    (hmod : store.runtime.currentModule = «module»)
    (henv : store.runtime.currentHost = Universal.envFor «module»)
    (hread : store.wasm.mem.read32 1053960 = oldBump)
    (hbound : 1053960 + 4 ≤ store.wasm.mem.pages * 65536)
    (hpages : store.wasm.mem.pages < 4294967295)
    (hnonneg : ¬ newSize.toInt32 < UInt32.toInt32 0)
    (holdCapacity : oldCapacity ≠ 0)
    (hptr : allocatorPtr oldBump 1 ≠ 0)
    (hout : out.toNat + 12 ≤ store.wasm.mem.pages * 65536)
    (hsource : oldPtr.toNat +
        (reallocatorCopyLen oldCapacity newSize).toNat ≤
      store.wasm.mem.pages * 65536)
    (hdestination : allocatorRequiredPages newSize 1 oldBump ≤
        UInt32.ofNat store.wasm.mem.pages →
      (allocatorPtr oldBump 1).toNat +
          (reallocatorCopyLen oldCapacity newSize).toNat ≤
        store.wasm.mem.pages * 65536)
    (hgrownBounds : ∀ memory previousPages,
      store.wasm.mem.grow
          (allocatorRequiredPages newSize 1 oldBump -
            UInt32.ofNat store.wasm.mem.pages)
          (store.wasm.memoryCap store.runtime.currentModule 0) =
            some (memory, previousPages) →
      oldPtr.toNat + (reallocatorCopyLen oldCapacity newSize).toNat ≤
          memory.pages * 65536 ∧
      (allocatorPtr oldBump 1).toNat +
          (reallocatorCopyLen oldCapacity newSize).toNat ≤
          memory.pages * 65536) :
    ((¬(allocatorFinish newSize 1 oldBump).toInt32 < UInt32.toInt32 0) ∧
      (((allocatorRequiredPages newSize 1 oldBump ≤
          UInt32.ofNat store.wasm.mem.pages) ∧ Reaches
        ⟨.running
          ⟨⟨outerParams, outerLocalValues,
              [.i32 newSize, .i32 oldPtr, .i32 oldCapacity, .i32 out] ++ stack⟩,
            [.call 7] ++ code, arity, remainder, controls, calls⟩,
          store⟩
        (growResultFinal
          (growResultOkStore
            (reallocatorResultStore store oldPtr oldCapacity 1 newSize oldBump)
            out (allocatorPtr oldBump 1) newSize)
          outerParams outerLocalValues stack code arity remainder controls
          calls)) ∨
      ∃ memory previousPages,
        store.wasm.mem.grow
            (allocatorRequiredPages newSize 1 oldBump -
              UInt32.ofNat store.wasm.mem.pages)
            (store.wasm.memoryCap store.runtime.currentModule 0) =
              some (memory, previousPages) ∧
        Reaches
          ⟨.running
            ⟨⟨outerParams, outerLocalValues,
                [.i32 newSize, .i32 oldPtr, .i32 oldCapacity, .i32 out] ++ stack⟩,
              [.call 7] ++ code, arity, remainder, controls, calls⟩,
            store⟩
          (growResultFinal
            (growResultOkStore
              (reallocatorResultStore (allocatorGrownStore store memory)
                oldPtr oldCapacity 1 newSize oldBump)
              out (allocatorPtr oldBump 1) newSize)
            outerParams outerLocalValues stack code arity remainder controls
            calls))) ∨
      TrapsWith
        ⟨.running
          ⟨⟨outerParams, outerLocalValues,
              [.i32 newSize, .i32 oldPtr, .i32 oldCapacity, .i32 out] ++ stack⟩,
            [.call 7] ++ code, arity, remainder, controls, calls⟩,
          store⟩
        (.host OOM.trapMessage)
        (fun final => final.wasm.host.oom.raised = true) := by
  let initial : Config Universal.State :=
    ⟨.running
      ⟨⟨outerParams, outerLocalValues,
          [.i32 newSize, .i32 oldPtr, .i32 oldCapacity, .i32 out] ++ stack⟩,
        [.call 7] ++ code, arity, remainder, controls, calls⟩,
      store⟩
  have hprefix : Reaches initial
      (growResultReallocatorCall store outerParams outerLocalValues stack code
        arity remainder controls calls out oldCapacity oldPtr newSize) :=
    grow_result_realloc_prefix store outerParams outerLocalValues stack code
      arity remainder controls calls out oldCapacity oldPtr newSize hmod
      hnonneg holdCapacity
  have halloc := reallocator_call_outcome store
    ([.i32 out, .i32 oldCapacity, .i32 oldPtr, .i32 newSize]) [] []
    [.localSet 1, .br 1] 0 []
    [growResultDispatchControl, growResultAllocateControl,
      growResultOuterControl]
    ({ locals := ⟨outerParams, outerLocalValues, stack⟩
       continuation := code
       resultArity := arity
       callerRemainder := remainder
       control := controls
       returningInstance := store.runtime.entry } :: calls)
    oldPtr oldCapacity 1 newSize oldBump hmod henv hread hbound hpages hsource
    hdestination hgrownBounds
  rcases halloc with ⟨hsafe, (⟨henough, halloc⟩ |
      ⟨memory, previousPages, hgrow, halloc⟩)⟩ | htrap
  · left
    refine ⟨hsafe, Or.inl ?_⟩
    refine ⟨henough, ?_⟩
    have hafter : Reaches
        (growResultReallocatorCall store outerParams outerLocalValues stack code
          arity remainder controls calls out oldCapacity oldPtr newSize)
        (growResultAfterReallocator
          (reallocatorResultStore store oldPtr oldCapacity 1 newSize oldBump)
          outerParams outerLocalValues stack code arity remainder controls calls
          out oldCapacity oldPtr newSize (allocatorPtr oldBump 1)) := by
      simpa [growResultReallocatorCall, growResultAfterReallocator,
        reallocatorResultStore_runtime] using halloc
    have hsuffix := grow_result_realloc_success_suffix
      (reallocatorResultStore store oldPtr oldCapacity 1 newSize oldBump)
      outerParams outerLocalValues stack code arity remainder controls calls
      out oldCapacity oldPtr newSize (allocatorPtr oldBump 1) hptr
      (by simpa only [reallocatorResultStore_pages] using
        (show out.toNat + 8 + 4 ≤ store.wasm.mem.pages * 65536 by omega))
      (by simpa only [reallocatorResultStore_pages] using
        (show out.toNat + 4 + 4 ≤ store.wasm.mem.pages * 65536 by omega))
      (by simpa only [reallocatorResultStore_pages] using
        (show out.toNat + 4 ≤ store.wasm.mem.pages * 65536 by omega))
    simpa [initial] using hprefix.trans (hafter.trans hsuffix)
  · left
    refine ⟨hsafe, Or.inr ?_⟩
    refine ⟨memory, previousPages, hgrow, ?_⟩
    have hfacts := mem_grow_some_facts store.wasm.mem memory
      (allocatorRequiredPages newSize 1 oldBump -
        UInt32.ofNat store.wasm.mem.pages)
      (store.wasm.memoryCap store.runtime.currentModule 0)
      previousPages hgrow
    have houtGrown : out.toNat + 12 ≤ memory.pages * 65536 := by
      calc
        out.toNat + 12 ≤ store.wasm.mem.pages * 65536 := hout
        _ ≤ memory.pages * 65536 := by rw [hfacts.2]; omega
    have hafter : Reaches
        (growResultReallocatorCall store outerParams outerLocalValues stack code
          arity remainder controls calls out oldCapacity oldPtr newSize)
        (growResultAfterReallocator
          (reallocatorResultStore (allocatorGrownStore store memory)
            oldPtr oldCapacity 1 newSize oldBump)
          outerParams outerLocalValues stack code arity remainder controls calls
          out oldCapacity oldPtr newSize (allocatorPtr oldBump 1)) := by
      simpa [growResultReallocatorCall, growResultAfterReallocator,
        reallocatorResultStore_runtime, allocatorGrownStore] using halloc
    have hsuffix := grow_result_realloc_success_suffix
      (reallocatorResultStore (allocatorGrownStore store memory)
        oldPtr oldCapacity 1 newSize oldBump)
      outerParams outerLocalValues stack code arity remainder controls calls
      out oldCapacity oldPtr newSize (allocatorPtr oldBump 1) hptr
      (by simpa only [reallocatorResultStore_pages, allocatorGrownStore] using
        (show out.toNat + 8 + 4 ≤ memory.pages * 65536 by omega))
      (by simpa only [reallocatorResultStore_pages, allocatorGrownStore] using
        (show out.toNat + 4 + 4 ≤ memory.pages * 65536 by omega))
      (by simpa only [reallocatorResultStore_pages, allocatorGrownStore] using
        (show out.toNat + 4 ≤ memory.pages * 65536 by omega))
    simpa [initial] using hprefix.trans (hafter.trans hsuffix)
  · right
    have hfull := TrapsWith.prependReaches hprefix (by
      simpa [growResultReallocatorCall] using htrap)
    simpa [initial] using hfull

end Submission.HexDecodeStdio
