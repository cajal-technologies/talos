import HexDecodeStdio.ReallocatorOperational
import HexDecodeStdio.VectorGrowSteps

namespace Project.HexDecodeStdio

open Wasm Project.HexStdio Project.HexStdio.Spec
open Wasm.SmallStep

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

end Project.HexDecodeStdio
