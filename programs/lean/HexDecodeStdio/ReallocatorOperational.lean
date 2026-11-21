import HexDecodeStdio.AllocatorOperational
import HexDecodeStdio.ReallocatorSteps

namespace Project.HexDecodeStdio

open Wasm Project.HexStdio Project.HexStdio.Spec
open Wasm.SmallStep

/-- Exhaustive outcome of one reallocator invocation.  The side conditions
are precisely the source/destination bounds needed by its final `memory.copy`;
vector callers derive them from their capacity invariant. -/
theorem reallocator_call_outcome
    (store : MachineStore Universal.State)
    (params localValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (oldPtr oldSize align newSize oldBump : UInt32)
    (hmod : store.runtime.currentModule = «module»)
    (henv : store.runtime.currentHost = Universal.envFor «module»)
    (hread : store.wasm.mem.read32 1053960 = oldBump)
    (hbound : 1053960 + 4 ≤ store.wasm.mem.pages * 65536)
    (hpages : store.wasm.mem.pages < 4294967295)
    (hsource : oldPtr.toNat + (reallocatorCopyLen oldSize newSize).toNat ≤
      store.wasm.mem.pages * 65536)
    (hdestination : allocatorRequiredPages newSize align oldBump ≤
        UInt32.ofNat store.wasm.mem.pages →
      (allocatorPtr oldBump align).toNat +
          (reallocatorCopyLen oldSize newSize).toNat ≤
        store.wasm.mem.pages * 65536)
    (hgrownBounds : ∀ memory previousPages,
      store.wasm.mem.grow
          (allocatorRequiredPages newSize align oldBump -
            UInt32.ofNat store.wasm.mem.pages)
          (store.wasm.memoryCap store.runtime.currentModule 0) =
            some (memory, previousPages) →
      oldPtr.toNat + (reallocatorCopyLen oldSize newSize).toNat ≤
          memory.pages * 65536 ∧
      (allocatorPtr oldBump align).toNat +
          (reallocatorCopyLen oldSize newSize).toNat ≤
          memory.pages * 65536) :
    ((¬(allocatorFinish newSize align oldBump).toInt32 < UInt32.toInt32 0) ∧
      ((allocatorRequiredPages newSize align oldBump ≤
          UInt32.ofNat store.wasm.mem.pages) ∧ Reaches
        ⟨.running
          ⟨⟨params, localValues,
              [.i32 newSize, .i32 align, .i32 oldSize, .i32 oldPtr] ++ stack⟩,
            [.call 18] ++ code, arity, remainder, controls, calls⟩,
          store⟩
        ⟨.running
          ⟨⟨params, localValues, .i32 (allocatorPtr oldBump align) :: stack⟩,
            code, arity, remainder, controls, calls⟩,
          reallocatorResultStore store oldPtr oldSize align newSize oldBump⟩ ∨
      ∃ memory previousPages,
        store.wasm.mem.grow
            (allocatorRequiredPages newSize align oldBump -
              UInt32.ofNat store.wasm.mem.pages)
            (store.wasm.memoryCap store.runtime.currentModule 0) =
              some (memory, previousPages) ∧
        Reaches
          ⟨.running
            ⟨⟨params, localValues,
                [.i32 newSize, .i32 align, .i32 oldSize, .i32 oldPtr] ++ stack⟩,
              [.call 18] ++ code, arity, remainder, controls, calls⟩,
            store⟩
          ⟨.running
            ⟨⟨params, localValues, .i32 (allocatorPtr oldBump align) :: stack⟩,
              code, arity, remainder, controls, calls⟩,
            reallocatorResultStore (allocatorGrownStore store memory)
              oldPtr oldSize align newSize oldBump⟩)) ∨
      TrapsWith
        ⟨.running
          ⟨⟨params, localValues,
              [.i32 newSize, .i32 align, .i32 oldSize, .i32 oldPtr] ++ stack⟩,
            [.call 18] ++ code, arity, remainder, controls, calls⟩,
          store⟩
        (.host OOM.trapMessage)
        (fun final => final.wasm.host.oom.raised = true) := by
  by_cases hfirst : allocatorBase oldBump +
      ((0xffffffff : UInt32) + align) < (0xffffffff : UInt32) + align
  · right
    exact reallocator_first_overflow_traps store params localValues stack code
      arity remainder controls calls oldPtr oldSize align newSize oldBump
      hmod henv hread hbound hfirst
  by_cases hsecond : allocatorFinish newSize align oldBump <
      allocatorPtr oldBump align
  · right
    exact reallocator_size_overflow_traps store params localValues stack code
      arity remainder controls calls oldPtr oldSize align newSize oldBump
      hmod henv hread hbound hfirst hsecond
  by_cases hnegative :
      (allocatorFinish newSize align oldBump).toInt32 < UInt32.toInt32 0
  · right
    exact reallocator_signed_limit_traps store params localValues stack code
      arity remainder controls calls oldPtr oldSize align newSize oldBump
      hmod henv hread hbound hfirst hsecond hnegative
  by_cases henough : allocatorRequiredPages newSize align oldBump ≤
      UInt32.ofNat store.wasm.mem.pages
  · left
    refine ⟨hnegative, Or.inl ?_⟩
    exact ⟨henough, reallocator_no_grow_steps store params localValues stack code
      arity remainder controls calls oldPtr oldSize align newSize oldBump hmod
      hread hbound hfirst hsecond hnegative henough hsource
      (hdestination henough)⟩
  · cases hgrow : store.wasm.mem.grow
        (allocatorRequiredPages newSize align oldBump -
          UInt32.ofNat store.wasm.mem.pages)
        (store.wasm.memoryCap store.runtime.currentModule 0) with
    | none =>
        right
        exact reallocator_grow_failure_traps store params localValues stack
          code arity remainder controls calls oldPtr oldSize align newSize
          oldBump hmod henv hread hbound hfirst hsecond hnegative henough hgrow
    | some result =>
        rcases result with ⟨memory, previousPages⟩
        left
        refine ⟨hnegative, Or.inr ?_⟩
        refine ⟨memory, previousPages, rfl, ?_⟩
        have hfacts := mem_grow_some_facts store.wasm.mem memory
          (allocatorRequiredPages newSize align oldBump -
            UInt32.ofNat store.wasm.mem.pages)
          (store.wasm.memoryCap store.runtime.currentModule 0)
          previousPages hgrow
        have hboundGrown : 1053960 + 4 ≤ memory.pages * 65536 := by
          calc
            1053960 + 4 ≤ store.wasm.mem.pages * 65536 := hbound
            _ ≤ (store.wasm.mem.pages +
                (allocatorRequiredPages newSize align oldBump -
                  UInt32.ofNat store.wasm.mem.pages).toNat) * 65536 := by omega
            _ = memory.pages * 65536 := by rw [hfacts.2]
        have hresult : previousPages.toUInt32 ≠ (0xffffffff : UInt32) := by
          rw [hfacts.1]
          intro heq
          have heqNat := congrArg UInt32.toNat heq
          rw [UInt32.toNat_ofNat_of_lt'
            (by simpa only [UInt32.size] using
              (show store.wasm.mem.pages < 4294967296 by omega))] at heqNat
          have hmax : (0xffffffff : UInt32).toNat = 4294967295 := by decide
          rw [hmax] at heqNat
          omega
        have hb := hgrownBounds memory previousPages hgrow
        exact reallocator_grow_success_steps store params localValues stack
          code arity remainder controls calls oldPtr oldSize align newSize
          oldBump memory previousPages hmod hread hbound hboundGrown hfirst
          hsecond hnegative henough hgrow hresult hb.1 hb.2
end Project.HexDecodeStdio
