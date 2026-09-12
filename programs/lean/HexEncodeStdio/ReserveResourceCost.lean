import HexEncodeStdio.ReallocatorResourceCost
import HexEncodeStdio.ReserveOperational

/-! Actual reserve/grow calls of the generated hex consumer. -/
set_option maxRecDepth 20000
namespace Project.HexEncodeStdio.ReserveResourceCost
open Wasm Wasm.SmallStep Project.HexStdio

private def freshPrefixTrace : List StepKind :=
  [.instruction (.call 7),.instruction (.block 0 0 growResultBody),
    .instruction (.localGet 3),.instruction (.const 0),.instruction .ltS,.instruction (.br_if 0),
    .instruction (.block 0 0 growResultAllocate),.instruction (.block 0 0 growResultDispatch),
    .instruction (.localGet 1),.instruction .eqz,.instruction (.br_if 0)]
private def freshCallTrace : List StepKind :=
  [.instruction (.call 14),.administrative .returnFromCall,.instruction (.localGet 3),.instruction (.const 1)]
private def reallocPrefixTrace : List StepKind :=
  freshPrefixTrace ++ [.instruction (.localGet 2),.instruction (.localGet 1),
    .instruction (.const 1),.instruction (.localGet 3)]
private def resultTail : List StepKind :=
  [.instruction (.block 0 0 growResultCheck),.instruction (.localGet 1),.instruction (.br_if 0)] ++
  ((growResultSuccess.drop 1).take 9).map StepKind.instruction ++ [.administrative .returnFromCall]
private def freshSuffixTrace : List StepKind :=
  [.instruction (.localSet 1),.administrative .exitControl] ++ resultTail
private def reallocSuffixTrace : List StepKind :=
  [.instruction (.localSet 1),.instruction (.br 1)] ++ resultTail

private theorem grow_result_fresh_prefix_cost
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (out oldSize newSize : UInt32)
    (hmod : store.runtime.currentModule = «module»)
    (hnonneg : ¬ newSize.toInt32 < UInt32.toInt32 0) :
    CostedSteps CostedStdIO.work
      ⟨.running
        ⟨⟨outerParams, outerLocalValues,
            [.i32 newSize, .i32 oldSize, .i32 0, .i32 out] ++ stack⟩,
          [.call 7] ++ code, arity, remainder, controls, calls⟩,
        store⟩ freshPrefixTrace
      (growResultFreshMiddle store outerParams outerLocalValues stack code
        arity remainder controls calls out oldSize newSize) 11 := by
  apply Steps.with_unit_cost
  · unfold freshPrefixTrace
    have hnot : ¬7 < store.runtime.currentModule.imports.length := by
      rw [hmod]; decide
    have hfn : store.runtime.currentModule.funcs[
        7 - store.runtime.currentModule.imports.length]? = some func4Def := by
      rw [hmod]; rfl
    apply Steps.cons (Step.call hnot hfn)
    simp [func4Def, Function.toLocals, Function.numParams,
      func4_decomposition, growResultBody]
    apply Steps.cons Step.block
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons Step.const
    apply Steps.cons
      (Step.ltS (result := 0) (Eq.symm (if_neg hnonneg)))
    apply Steps.cons Step.brIfZero
    apply Steps.cons Step.block
    apply Steps.cons Step.block
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons (Step.eqz (result := 1) (by simp))
    apply Steps.cons (Step.brIf (condition := 1) (by decide) rfl)
    simp [growResultFreshMiddle, growResultAllocateControl,
      growResultOuterControl, growResultAllocate, growResultDispatch,
      growResultSuccess, growResultCheck, growResultErrorTail]
    exact Steps.refl _
  · intro before kind after member
    fin_cases member <;> rfl

private theorem grow_result_fresh_to_allocator_cost
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (out oldSize newSize : UInt32)
    (hmod : store.runtime.currentModule = «module») :
    CostedSteps CostedStdIO.work
      (growResultFreshMiddle store outerParams outerLocalValues stack code
        arity remainder controls calls out oldSize newSize) freshCallTrace
      (growResultAllocatorCall store outerParams outerLocalValues stack code
        arity remainder controls calls out oldSize newSize) 4 := by
  apply Steps.with_unit_cost
  · unfold freshCallTrace
    have hnot : ¬14 < store.runtime.currentModule.imports.length := by
      rw [hmod]; decide
    have hfn : store.runtime.currentModule.funcs[
        14 - store.runtime.currentModule.imports.length]? = some func11Def := by
      rw [hmod]; rfl
    simp only [growResultFreshMiddle]
    apply Steps.cons (Step.call hnot hfn)
    simp [func11Def, Function.toLocals, Function.numParams, func11]
    apply Steps.cons (Step.returnFromCallExplicit rfl)
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons Step.const
    simp [growResultAllocatorCall]
    exact Steps.refl _
  · intro before kind after member
    fin_cases member <;> rfl

private theorem grow_result_realloc_prefix_cost
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (out oldCapacity oldPtr newSize : UInt32)
    (hmod : store.runtime.currentModule = «module»)
    (hnonneg : ¬ newSize.toInt32 < UInt32.toInt32 0)
    (holdCapacity : oldCapacity ≠ 0) :
    CostedSteps CostedStdIO.work
      ⟨.running
        ⟨⟨outerParams, outerLocalValues,
            [.i32 newSize, .i32 oldPtr, .i32 oldCapacity, .i32 out] ++ stack⟩,
          [.call 7] ++ code, arity, remainder, controls, calls⟩,
        store⟩ reallocPrefixTrace
      (growResultReallocatorCall store outerParams outerLocalValues stack code
        arity remainder controls calls out oldCapacity oldPtr newSize) 15 := by
  apply Steps.with_unit_cost
  · unfold reallocPrefixTrace
    have hnot : ¬7 < store.runtime.currentModule.imports.length := by
      rw [hmod]; decide
    have hfn : store.runtime.currentModule.funcs[
        7 - store.runtime.currentModule.imports.length]? = some func4Def := by
      rw [hmod]; rfl
    apply Steps.cons (Step.call hnot hfn)
    simp [func4Def, Function.toLocals, Function.numParams,
      func4_decomposition, growResultBody]
    apply Steps.cons Step.block
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons Step.const
    apply Steps.cons
      (Step.ltS (result := 0) (Eq.symm (if_neg hnonneg)))
    apply Steps.cons Step.brIfZero
    apply Steps.cons Step.block
    apply Steps.cons Step.block
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons (Step.eqz (result := 0) (by simp [holdCapacity]))
    apply Steps.cons Step.brIfZero
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons Step.const
    apply Steps.cons (Step.localGet rfl)
    simp [growResultReallocatorCall, growResultDispatchControl,
      growResultAllocateControl, growResultOuterControl,
      growResultDispatch, growResultAllocate, growResultSuccess,
      growResultCheck, growResultErrorTail]
    exact Steps.refl _
  · intro before kind after member
    fin_cases member <;> rfl

private theorem grow_result_realloc_success_suffix_cost
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (out oldCapacity oldPtr newSize ptr : UInt32)
    (hptr : ptr ≠ 0)
    (hout8 : out.toNat + 8 + 4 ≤ store.wasm.mem.pages * 65536)
    (hout4 : out.toNat + 4 + 4 ≤ store.wasm.mem.pages * 65536)
    (hout0 : out.toNat + 4 ≤ store.wasm.mem.pages * 65536) :
    CostedSteps CostedStdIO.work
      (growResultAfterReallocator store outerParams outerLocalValues stack code
        arity remainder controls calls out oldCapacity oldPtr newSize ptr) reallocSuffixTrace
      (growResultFinal (growResultOkStore store out ptr newSize)
        outerParams outerLocalValues stack code arity remainder controls calls) 15 := by
  apply Steps.with_unit_cost
  · unfold reallocSuffixTrace
    simp only [growResultAfterReallocator]
    apply Steps.cons (Step.localSet rfl)
    apply Steps.cons (Step.br rfl)
    apply Steps.cons Step.block
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons (Step.brIf (condition := ptr) hptr rfl)
    simp
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons (Step.store32 rfl (address := .i32 (out)) (offset := 8) hout8)
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons (Step.store32 rfl (address := .i32 (out)) (offset := 4) (by
      simpa [setMemory_eq] using hout4))
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons Step.const
    apply Steps.cons (Step.store32 rfl (address := .i32 (out)) (offset := 0) (by
      simpa [setMemory_eq] using hout0))
    apply Steps.cons (Step.returnFromCallExplicit rfl)
    simp [growResultFinal, growResultOkStore, setMemory_eq]
    exact Steps.refl _
  · intro before kind after member
    fin_cases member <;> rfl

private theorem grow_result_success_suffix_cost
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (out oldSize newSize ptr : UInt32)
    (hptr : ptr ≠ 0)
    (hout8 : out.toNat + 8 + 4 ≤ store.wasm.mem.pages * 65536)
    (hout4 : out.toNat + 4 + 4 ≤ store.wasm.mem.pages * 65536)
    (hout0 : out.toNat + 4 ≤ store.wasm.mem.pages * 65536) :
    CostedSteps CostedStdIO.work
      (growResultAfterAllocator store outerParams outerLocalValues stack code
        arity remainder controls calls out oldSize newSize ptr) freshSuffixTrace
      (growResultFinal (growResultOkStore store out ptr newSize)
        outerParams outerLocalValues stack code arity remainder controls calls) 15 := by
  apply Steps.with_unit_cost
  · unfold freshSuffixTrace
    simp only [growResultAfterAllocator]
    apply Steps.cons (Step.localSet rfl)
    apply Steps.cons (Step.exitControl rfl)
    apply Steps.cons Step.block
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons (Step.brIf (condition := ptr) hptr rfl)
    simp []
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons (Step.store32 rfl (address := .i32 (out)) (offset := 8) hout8)
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons (Step.store32 rfl (address := .i32 (out)) (offset := 4) (by
      simpa [setMemory_eq] using hout4))
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons Step.const
    apply Steps.cons (Step.store32 rfl (address := .i32 (out)) (offset := 0) (by
      simpa [setMemory_eq] using hout0))
    apply Steps.cons (Step.returnFromCallExplicit rfl)
    simp [growResultFinal, growResultOkStore, setMemory_eq]
    exact Steps.refl _
  · intro before kind after member
    fin_cases member <;> rfl

def allocationStore (store : MachineStore Universal.State) (capacity pointer size bump : UInt32) :
    MachineStore Universal.State :=
  if capacity=0 then AllocatorResourceCost.finalStore store ((allocatorBase bump).toNat+size.toNat)
  else ReallocatorResourceCost.finalStore store pointer capacity size bump

@[simp] theorem allocationStore_pages (store : MachineStore Universal.State) (capacity pointer size bump : UInt32) :
    (allocationStore store capacity pointer size bump).wasm.mem.pages=
      max store.wasm.mem.pages (AllocatorResourceCost.requiredPages ((allocatorBase bump).toNat+size.toNat)) := by
  unfold allocationStore
  split <;> simp

@[simp] theorem allocationStore_runtime (store : MachineStore Universal.State) (capacity pointer size bump : UInt32) :
    (allocationStore store capacity pointer size bump).runtime=store.runtime := by
  unfold allocationStore
  split
  · exact (AllocatorResourceCost.finalStore_frame _ _).1
  · exact (ReallocatorResourceCost.finalStore_frame _ _ _ _ _).1

theorem allocation_success (store : MachineStore Universal.State) (capacity pointer size bump : UInt32)
    (hcap : store.wasm.memoryCap store.runtime.currentModule 0=Module.memoryHardCap)
    (hpages : store.wasm.mem.pages≤Module.memoryHardCap)
    (hfit : (allocatorBase bump).toNat+size.toNat<2147483648) :
    ByteGrowSuccess store capacity pointer size bump (allocationStore store capacity pointer size bump) := by
  let frontier := (allocatorBase bump).toNat
  have hrequired := AllocatorResourceCost.required_toNat size bump frontier rfl hfit
  have hfinishNat := AllocatorResourceCost.finish_toNat size bump frontier rfl hfit
  have hfinish : UInt32.ofNat (frontier+size.toNat)=allocatorFinish size 1 bump := by
    rw [← hfinishNat,UInt32.ofNat_toNat]
  have hnegative := AllocatorResourceCost.nonnegative (allocatorFinish size 1 bump) (by rw [hfinishNat];exact hfit)
  have hpagesNat := UInt32.toNat_ofNat_of_lt' (lt_of_le_of_lt hpages (by decide : Module.memoryHardCap<UInt32.size))
  have hcompare : allocatorRequiredPages size 1 bump≤UInt32.ofNat store.wasm.mem.pages ↔
      AllocatorResourceCost.requiredPages (frontier+size.toNat)≤store.wasm.mem.pages := by
    rw [UInt32.le_iff_toNat_le,hrequired,hpagesNat]
  dsimp only [frontier] at hrequired hfinish hcompare
  by_cases henough : AllocatorResourceCost.requiredPages ((allocatorBase bump).toNat+size.toNat)≤store.wasm.mem.pages
  · by_cases hzero : capacity=0
    · simpa only [allocationStore,if_pos hzero,AllocatorResourceCost.finalStore,
        AllocatorResourceCost.grownMemory,max_eq_left henough,allocatorGrownStore,hfinish]
        using (ByteGrowSuccess.freshNoGrow (store:=store) (oldPtr:=pointer) (newCapacity:=size) (oldBump:=bump)
          hzero (hcompare.mpr henough) hnegative)
    · simpa only [allocationStore,if_neg hzero,ReallocatorResourceCost.finalStore,
        AllocatorResourceCost.grownMemory,max_eq_left henough,allocatorGrownStore]
        using (ByteGrowSuccess.reallocNoGrow (store:=store) (oldPtr:=pointer) (newCapacity:=size) (oldBump:=bump)
          hzero (hcompare.mpr henough))
  · have hneed := fun h => henough (hcompare.mp h)
    have hbound : (allocatorRequiredPages size 1 bump).toNat≤32768 := by
      rw [hrequired];exact (AllocatorResourceCost.required_bound _ hfit).1
    have hgrow := AllocatorResourceCost.grow_success store (allocatorRequiredPages size 1 bump) hcap hpages hbound hneed
    let memory : Mem := { store.wasm.mem with pages := (allocatorRequiredPages size 1 bump).toNat }
    by_cases hzero : capacity=0
    · simpa only [allocationStore,if_pos hzero,AllocatorResourceCost.finalStore,
        AllocatorResourceCost.grownMemory,max_eq_right (Nat.le_of_not_ge henough),
        memory,hrequired,hfinish] using
        (ByteGrowSuccess.freshGrow (store:=store) (oldPtr:=pointer) (newCapacity:=size) (oldBump:=bump)
          hzero memory store.wasm.mem.pages hneed hgrow hnegative)
    · simpa only [allocationStore,if_neg hzero,ReallocatorResourceCost.finalStore,
        AllocatorResourceCost.grownMemory,max_eq_right (Nat.le_of_not_ge henough),memory,hrequired] using
        (ByteGrowSuccess.reallocGrow (store:=store) (oldPtr:=pointer) (newCapacity:=size) (oldBump:=bump)
          hzero memory store.wasm.mem.pages hgrow)

/-- Actual call7 byte-grow wrapper, including allocator selection, result-slot
stores and caller return. Its successful outcome is derived from initial facts. -/
theorem byte_grow_cost (store : MachineStore Universal.State)
    (params localValues stack : List Value) (code : Program) (arity : Nat)
    (remainder : List Value) (controls : List ControlFrame) (calls : List CallFrame)
    (out capacity pointer size bump : UInt32)
    (hmodule : store.runtime.currentModule=Project.HexStdio.module)
    (hcap : store.wasm.memoryCap store.runtime.currentModule 0=Module.memoryHardCap)
    (hpages : store.wasm.mem.pages≤Module.memoryHardCap)
    (hread : store.wasm.mem.read32 1053960=bump)
    (hcursor : 1053960+4≤store.wasm.mem.pages*65536)
    (hfit : (allocatorBase bump).toNat+size.toNat<2147483648)
    (hold : capacity.toNat<size.toNat)
    (hsource : pointer.toNat+capacity.toNat≤store.wasm.mem.pages*65536)
    (hout : out.toNat+12≤store.wasm.mem.pages*65536) :
    ∃ trace, trace.length≤(if capacity=0 then 86 else 105) ∧
      CostedSteps CostedStdIO.work
        ⟨.running ⟨⟨params,localValues,[.i32 size,.i32 pointer,.i32 capacity,.i32 out]++stack⟩,
          .call 7::code,arity,remainder,controls,calls⟩,store⟩ trace
        (growResultFinal (growResultOkStore (allocationStore store capacity pointer size bump)
          out (allocatorPtr bump 1) size) params localValues stack code arity remainder controls calls)
        (trace.length+capacity.toNat+65536*
          (AllocatorResourceCost.requiredPages ((allocatorBase bump).toNat+size.toNat)-store.wasm.mem.pages)) ∧
      ByteGrowSuccess store capacity pointer size bump (allocationStore store capacity pointer size bump) ∧
      ∀ kind ∈ trace, PrimaryMemoryKind kind := by
  let frontier := (allocatorBase bump).toNat
  have hnonneg := AllocatorResourceCost.nonnegative size (by omega)
  have hptr : allocatorPtr bump 1≠0 := by
    rw [AllocatorResourceCost.ptr_one,allocatorBase]
    split <;> simp_all
  have hpointer : allocatorPtr bump 1=UInt32.ofNat frontier := by
    rw [AllocatorResourceCost.ptr_one,UInt32.ofNat_toNat]
  have success := allocation_success store capacity pointer size bump hcap hpages hfit
  have hmono := success.pages_mono
  have hout' := hout.trans (Nat.mul_le_mul_right 65536 hmono)
  let saved : CallFrame :=
    { locals:=⟨params,localValues,stack⟩,continuation:=code,resultArity:=arity,
      callerRemainder:=remainder,control:=controls,returningInstance:=store.runtime.entry }
  by_cases hzero : capacity=0
  · subst capacity
    have first := (grow_result_fresh_prefix_cost store params localValues stack code arity remainder controls calls
      out pointer size hmodule hnonneg).trans
      (grow_result_fresh_to_allocator_cost store params localValues stack code arity remainder controls calls
        out pointer size hmodule)
    obtain ⟨allocTrace,allocLength,allocRun,_,allocLabels⟩ := AllocatorResourceCost.allocator_byte_cost store
      [.i32 out,.i32 0,.i32 pointer,.i32 size] [] [] [.localSet 1] 0 []
      [growResultAllocateControl,growResultOuterControl] (saved::calls)
      size bump frontier hmodule hcap hpages hread hcursor rfl hfit
    let allocated := allocationStore store 0 pointer size bump
    have after : CostedSteps CostedStdIO.work
        (growResultAllocatorCall store params localValues stack code arity remainder controls calls out pointer size)
        allocTrace (growResultAfterAllocator allocated params localValues stack code arity remainder controls calls
          out pointer size (allocatorPtr bump 1))
        (allocTrace.length+65536*(AllocatorResourceCost.requiredPages (frontier+size.toNat)-store.wasm.mem.pages)) := by
      simpa only [growResultAllocatorCall,growResultAfterAllocator,allocationStore,
        allocated,ite_true,saved,hpointer,AllocatorResourceCost.finalStore,allocatorBumpStore,
        allocatorGrownStore,AllocatorMemoryCost.callConfig,AllocatorMemoryCost.returnConfig,
        List.cons_append,List.nil_append] using allocRun
    have haout : out.toNat+12≤allocated.wasm.mem.pages*65536 := hout'
    have tail := grow_result_success_suffix_cost allocated params localValues stack code arity remainder controls calls
      out pointer size (allocatorPtr bump 1) hptr (by omega) (by omega) (by omega)
    refine ⟨(freshPrefixTrace++freshCallTrace)++allocTrace++freshSuffixTrace,?_,?_,success,?_⟩
    · simp only [List.length_append]
      change 11+4+allocTrace.length+15≤86
      split_ifs at allocLength <;> omega
    · have run := (first.trans after).trans tail
      convert run using 1 <;> try rfl
      simp only [List.length_append]
      change (11+4+allocTrace.length+15)+0+65536*_=11+4+(allocTrace.length+65536*_)+15
      dsimp only [frontier]
      omega
    · intro kind member
      simp only [List.mem_append] at member
      rcases member with ((hm|hm)|hm)|hm
      · fin_cases hm <;> trivial
      · fin_cases hm <;> trivial
      · exact allocLabels kind hm
      · fin_cases hm <;> trivial
  · have hpositive : 0<capacity.toNat := by
      by_contra hn
      have hz : capacity.toNat=0 := by omega
      exact hzero (UInt32.toNat.inj hz)
    have first := grow_result_realloc_prefix_cost store params localValues stack code arity remainder controls calls
      out capacity pointer size hmodule hnonneg hzero
    obtain ⟨allocTrace,allocLength,allocRun,allocLabels⟩ := ReallocatorResourceCost.reallocator_byte_cost store
      [.i32 out,.i32 capacity,.i32 pointer,.i32 size] [] [] [.localSet 1,.br 1] 0 []
      [growResultDispatchControl,growResultAllocateControl,growResultOuterControl] (saved::calls)
      pointer capacity size bump frontier hmodule hcap hpages hread hcursor rfl hfit hpositive (Nat.le_of_lt hold) hsource
    let allocated := allocationStore store capacity pointer size bump
    have after : CostedSteps CostedStdIO.work
        (growResultReallocatorCall store params localValues stack code arity remainder controls calls out capacity pointer size)
        allocTrace (growResultAfterReallocator allocated params localValues stack code arity remainder controls calls
          out capacity pointer size (allocatorPtr bump 1))
        (allocTrace.length+capacity.toNat+65536*(AllocatorResourceCost.requiredPages (frontier+size.toNat)-store.wasm.mem.pages)) := by
      simpa only [growResultReallocatorCall,growResultAfterReallocator,allocationStore,allocated,if_neg hzero,
        saved,hpointer,ReallocatorResourceCost.finalStore,reallocatorResultStore_runtime,allocatorGrownStore,
        List.cons_append,List.nil_append] using allocRun
    have haout : out.toNat+12≤allocated.wasm.mem.pages*65536 := hout'
    have tail := grow_result_realloc_success_suffix_cost allocated params localValues stack code arity remainder controls calls
      out capacity pointer size (allocatorPtr bump 1) hptr (by omega) (by omega) (by omega)
    refine ⟨reallocPrefixTrace++allocTrace++reallocSuffixTrace,?_,?_,success,?_⟩
    · simp only [if_neg hzero,List.length_append]
      change 15+allocTrace.length+15≤105
      split_ifs at allocLength <;> omega
    · have run := (first.trans after).trans tail
      convert run using 1 <;> try rfl
      simp only [List.length_append]
      change (15+allocTrace.length+15)+capacity.toNat+65536*_=15+(allocTrace.length+capacity.toNat+65536*_)+15
      dsimp only [frontier]
      omega
    · intro kind member
      simp only [List.mem_append] at member
      rcases member with (hm|hm)|hm
      · fin_cases hm <;> trivial
      · exact allocLabels kind hm
      · fin_cases hm <;> trivial

private def reservePrefixTrace : List StepKind :=
  [.instruction (.call 5)] ++ (func2.take 5).map StepKind.instruction ++
  [.instruction (.block 0 0 [.localGet 2,.localGet 1,.add,.localTee 1,.localGet 2,.geU,.br_if 0,.const 0,.const 0,.call 60,.unreachable])] ++
  ([.localGet 2,.localGet 1,.add,.localTee 1,.localGet 2,.geU,.br_if 0,.const 0,.const 0,.call 60,.unreachable].take 7).map StepKind.instruction ++
  ((func2.drop 6).take 24).map StepKind.instruction
private def reserveBlockAt (program : Program) (index : Nat) : Program :=
  match program[index]? with
  | some (.block _ _ body) => body
  | _ => []
private def reserveSuffixTrace : List StepKind :=
  [.instruction (.block 0 0 (reserveBlockAt reserveAfterGrow 0)),
    .instruction (.localGet 3),.instruction (.load32 4),.instruction (.const 1),.instruction .ne,.instruction (.br_if 0)] ++
  (reserveAfterGrow.drop 1).map StepKind.instruction ++ [.administrative .returnFromCall]

private theorem reserve_to_grow_call_cost
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
    CostedSteps CostedStdIO.work
      ⟨.running
        ⟨⟨outerParams, outerLocalValues,
            [.i32 additional, .i32 length, .i32 vector] ++ stack⟩,
          [.call 5] ++ code, arity, remainder, controls, calls⟩,
        store⟩
      reservePrefixTrace
      (reserveGrowCall store outerParams outerLocalValues stack code arity
        remainder controls calls vector length additional capacity data sp) 38 := by
  apply Steps.with_unit_cost
  · unfold reservePrefixTrace
    have hnot : ¬5 < store.runtime.currentModule.imports.length := by
      rw [hmod]; decide
    have hfn : store.runtime.currentModule.funcs[
        5 - store.runtime.currentModule.imports.length]? = some func2Def := by
      rw [hmod]; rfl
    apply Steps.cons (Step.call hnot hfn)
    simp [func2Def, Function.toLocals, Function.numParams,
      func2_prefix_split]
    apply Steps.cons (Step.globalGet hglobal)
    apply Steps.cons Step.const
    apply Steps.cons Step.sub
    apply Steps.cons (Step.localTee rfl)
    apply Steps.cons (Step.globalSet (by simp [hglobal]))
    rw [setGlobal_zero_eq]
    apply Steps.cons Step.block
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons Step.add
    apply Steps.cons (Step.localTee rfl)
    apply Steps.cons (Step.localGet rfl)
    have hsum' : length + additional ≥ additional := by
      simpa only [reserveRequired] using hsum
    apply Steps.cons (Step.geU (result := 1)
      (Eq.symm (if_pos hsum')))
    apply Steps.cons (Step.brIf (condition := 1) (by decide) rfl)
    simp []
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons Step.const
    apply Steps.cons Step.add
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons (Step.load32 rfl (address := .i32 (vector)) (offset := 0)
      (by simpa [reserveFrameStore] using hcapBound))
    simp only [UInt32.add_zero, hcapacity]
    apply Steps.cons (Step.localTee rfl)
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons (Step.load32 rfl (address := .i32 (vector)) (offset := 4)
      (by simpa [reserveFrameStore] using hdataBound))
    simp only [hdata]
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons Step.const
    apply Steps.cons Step.shl
    apply Steps.cons (Step.localTee rfl)
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons (Step.gtU
      (result := if reserveRequired length additional >
          reserveDoubled capacity then 1 else 0) (by
        simp [reserveRequired, reserveDoubled]))
    apply Steps.cons (Step.select (selected := .i32
      (reserveCandidate length additional capacity)) (by
        by_cases h : capacity <<< 1 < length + additional
        · simp [reserveCandidate, reserveRequired, reserveDoubled, h]
        · simp [reserveCandidate, reserveRequired, reserveDoubled, h]))
    apply Steps.cons (Step.localTee rfl)
    apply Steps.cons Step.const
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons Step.const
    apply Steps.cons (Step.gtU
      (result := if reserveCandidate length additional capacity > 8
        then 1 else 0) (by simp))
    apply Steps.cons (Step.select (selected := .i32
      (reserveNewCapacity length additional capacity)) (by
        by_cases h : (8 : UInt32) < reserveCandidate length additional capacity
        · simp [reserveNewCapacity, h]
        · simp [reserveNewCapacity, h]))
    apply Steps.cons (Step.localTee rfl)
    rw [show 4 + (sp - 16) = (sp - 16) + 4 by bv_normalize (config := { enums := false })]
    simp [reserveGrowCall, reserveFrameStore, reserveNewCapacity,
      reserveCandidate, reserveRequired, reserveDoubled]
    exact Steps.refl _
  · intro before kind after member
    fin_cases member <;> rfl

private theorem reserve_success_suffix_cost
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
    CostedSteps CostedStdIO.work
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
      reserveSuffixTrace
      (growResultFinal (reserveFinishStore store vector data newCapacity sp)
        outerParams outerLocalValues stack code arity remainder controls calls) 20 := by
  apply Steps.with_unit_cost
  · unfold reserveSuffixTrace
    simp only [reserveAfterGrow, func2, List.drop]
    apply Steps.cons Step.block
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons (Step.load32 rfl (address := .i32 (frame)) (offset := 4) htagBound)
    simp only [htag]
    apply Steps.cons Step.const
    apply Steps.cons (Step.ne (result := 1) (by simp))
    apply Steps.cons (Step.brIf (condition := 1) (by decide) rfl)
    simp
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons (Step.load32 rfl (address := .i32 (frame)) (offset := 8) hdataBound)
    simp only [hdata]
    apply Steps.cons (Step.localSet rfl)
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons
      (Step.store32 rfl (address := .i32 (vector)) (offset := 0) hvectorBound)
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons
      (Step.store32 rfl (address := .i32 (vector)) (offset := 4) (by
        simpa [setMemory_eq] using hvectorDataBound))
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons Step.const
    apply Steps.cons Step.add
    have hrestore' : 16 + frame = sp := by
      rw [show 16 + frame = frame + 16 by bv_normalize (config := { enums := false }), hrestore]
    rw [hrestore']
    apply Steps.cons (Step.globalSet (by
      simpa [setMemory_eq, globalAt?] using hglobal))
    rw [setGlobal_zero_eq]
    apply Steps.cons (Step.returnFromCallFallthrough hreturn)
    simp [growResultFinal, reserveFinishStore, reserveVectorStore,
      setMemory_eq]
    exact Steps.refl _
  · intro before kind after member
    fin_cases member <;> rfl


/-- Exact concrete store returned by reserve, including its scratch slots and
vector header writes and restoration of the original stack-pointer global. -/
def finalStore (store : MachineStore Universal.State)
    (vector length additional capacity data sp bump : UInt32) : MachineStore Universal.State :=
  let size := reserveNewCapacity length additional capacity
  reserveFinishStore
    (growResultOkStore (allocationStore (reserveFrameStore store (sp-16)) capacity data size bump)
      ((sp-16)+4) (allocatorPtr bump 1) size)
    vector (allocatorPtr bump 1) size sp

/-- Initial-state-only successful reserve execution. The generated allocator
selects and performs any necessary physical growth; no future trace is assumed. -/
theorem reserve_cost
    (store : MachineStore Universal.State)
    (params localValues stack : List Value) (code : Program) (arity : Nat)
    (remainder : List Value) (controls : List ControlFrame) (calls : List CallFrame)
    (vector length additional capacity data sp bump : UInt32)
    (hmodule : store.runtime.currentModule=Project.HexStdio.module)
    (hcap : store.wasm.memoryCap store.runtime.currentModule 0=Module.memoryHardCap)
    (hpages : store.wasm.mem.pages≤Module.memoryHardCap)
    (hglobal : globalAt? store 0=some (.i32 sp))
    (hsum : reserveRequired length additional≥additional)
    (hcapacity : store.wasm.mem.read32 vector=capacity)
    (hdata : store.wasm.mem.read32 (vector+4)=data)
    (hread : store.wasm.mem.read32 1053960=bump)
    (hcursor : 1053960+4≤store.wasm.mem.pages*65536)
    (hfit : (allocatorBase bump).toNat+(reserveNewCapacity length additional capacity).toNat<2147483648)
    (hold : capacity.toNat<(reserveNewCapacity length additional capacity).toNat)
    (hsource : data.toNat+capacity.toNat≤store.wasm.mem.pages*65536)
    (hframe : (sp-16).toNat+16≤store.wasm.mem.pages*65536)
    (houtNoWrap : ((sp-16)+4).toNat=(sp-16).toNat+4)
    (houtNext : (((sp-16)+4)+4).toNat=((sp-16)+4).toNat+4)
    (hvector : vector.toNat+8≤store.wasm.mem.pages*65536) :
    ∃ trace, trace.length≤(if capacity=0 then 144 else 163) ∧
      CostedSteps CostedStdIO.work
        ⟨.running ⟨⟨params,localValues,[.i32 additional,.i32 length,.i32 vector]++stack⟩,
          .call 5::code,arity,remainder,controls,calls⟩,store⟩ trace
        (growResultFinal (finalStore store vector length additional capacity data sp bump)
          params localValues stack code arity remainder controls calls)
        (trace.length+capacity.toNat+65536*
          (AllocatorResourceCost.requiredPages ((allocatorBase bump).toNat+
            (reserveNewCapacity length additional capacity).toNat)-store.wasm.mem.pages)) ∧
      ByteGrowSuccess (reserveFrameStore store (sp-16)) capacity data
        (reserveNewCapacity length additional capacity) bump
        (allocationStore (reserveFrameStore store (sp-16)) capacity data
          (reserveNewCapacity length additional capacity) bump) ∧
      ∀kind∈trace, PrimaryMemoryKind kind := by
  let base := reserveFrameStore store (sp-16)
  let size := reserveNewCapacity length additional capacity
  let out := (sp-16)+4
  let saved : CallFrame :=
    { locals:=⟨params,localValues,stack⟩,continuation:=code,resultArity:=arity,
      callerRemainder:=remainder,control:=controls,returningInstance:=store.runtime.entry }
  have first := reserve_to_grow_call_cost store params localValues stack code arity remainder controls calls
    vector length additional capacity data sp hmodule hglobal hsum hcapacity hdata (by omega) (by omega)
  obtain ⟨growTrace,growLength,growRun,success,growLabels⟩ := byte_grow_cost base
    [.i32 vector,.i32 (reserveRequired length additional),.i32 size] [.i32 (sp-16)] []
    reserveAfterGrow 0 [] [] (saved::calls) out capacity data size bump hmodule hcap hpages hread hcursor
    hfit hold hsource (by dsimp only [out,base,reserveFrameStore];rw [houtNoWrap];exact hframe)
  let allocated := allocationStore base capacity data size bump
  let post := growResultOkStore allocated out (allocatorPtr bump 1) size
  have after : CostedSteps CostedStdIO.work
      (reserveGrowCall store params localValues stack code arity remainder controls calls
        vector length additional capacity data sp)
      growTrace (growResultFinal post
        [.i32 vector,.i32 (reserveRequired length additional),.i32 size] [.i32 (sp-16)] []
        reserveAfterGrow 0 [] [] (saved::calls))
      (growTrace.length+capacity.toNat+65536*
        (AllocatorResourceCost.requiredPages ((allocatorBase bump).toNat+size.toNat)-store.wasm.mem.pages)) := by
    simpa only [reserveGrowCall,base,size,out,post,allocated,saved,List.cons_append,List.nil_append,reserveFrameStore_mem]
      using growRun
  have hmono : store.wasm.mem.pages≤post.wasm.mem.pages := success.pages_mono
  have hmemory := Nat.mul_le_mul_right 65536 hmono
  have htag : post.wasm.mem.read32 ((sp-16)+4)=0 := growResultOkStore_read_tag _ _ _ _
  have hptr : post.wasm.mem.read32 ((sp-16)+8)=allocatorPtr bump 1 := by
    rw [show (sp-16)+8=out+4 by dsimp only [out];bv_normalize (config := {enums:=false})]
    exact growResultOkStore_read_ptr _ _ _ _ houtNext
  have hsome : (globalAt? post 0).isSome=true := by
    change (globalAt? allocated 0).isSome=true
    rw [success.globalAt_eq 0,reserveFrameStore_global_zero store (sp-16) sp hglobal]
    rfl
  have hruntime : post.runtime=store.runtime := success.runtime_eq
  have tail := reserve_success_suffix_cost post params localValues stack code arity remainder controls calls
    store.runtime.entry vector (reserveRequired length additional) size (allocatorPtr bump 1) (sp-16) sp
    htag hptr
    ((Nat.add_le_add_left (by decide : 4+4≤16) (sp-16).toNat).trans (hframe.trans hmemory))
    ((Nat.add_le_add_left (by decide : 8+4≤16) (sp-16).toNat).trans (hframe.trans hmemory))
    ((Nat.add_le_add_left (by decide : 4≤8) vector.toNat).trans (hvector.trans hmemory))
    (hvector.trans hmemory) hsome (by rw [hruntime])
    (by bv_normalize (config := {enums:=false}))
  refine ⟨reservePrefixTrace++growTrace++reserveSuffixTrace,?_,?_,success,?_⟩
  · simp only [List.length_append]
    change 38+growTrace.length+20≤_
    split_ifs at growLength ⊢ <;> omega
  · have run := (first.trans after).trans tail
    convert run using 1 <;> try rfl
    simp only [List.length_append]
    change 38+growTrace.length+20+capacity.toNat+65536*_=
      38+(growTrace.length+capacity.toNat+65536*_)+20
    dsimp only [size]
    omega
  · intro kind member
    simp only [List.mem_append] at member
    rcases member with (hm|hm)|hm
    · fin_cases hm <;> trivial
    · exact growLabels kind hm
    · fin_cases hm <;> trivial

/-- A first byte-vector allocation of at most 32 bytes cannot grow the
canonical seventeen-page initial memory, for every successful outcome store. -/
theorem first_allocation_pages {store final : MachineStore Universal.State}
    {pointer size : UInt32} (success : ByteGrowSuccess store 0 pointer size 0 final)
    (hpages : store.wasm.mem.pages=17) (hsize : size.toNat≤32) :
    final.wasm.mem.pages=17 := by
  have hfit : 1054000+size.toNat<2147483648 := by omega
  have required := AllocatorResourceCost.required_toNat size 0 1054000 rfl hfit
  have hrequired : allocatorRequiredPages size 1 0≤UInt32.ofNat store.wasm.mem.pages := by
    rw [UInt32.le_iff_toNat_le,required,hpages]
    change (65535+(1054000+size.toNat))/65536≤17
    omega
  cases success with
  | freshNoGrow => exact hpages
  | freshGrow _ _ _ hnotfit => exact False.elim (hnotfit hrequired)
  | reallocNoGrow hne => exact False.elim (hne rfl)
  | reallocGrow hne => exact False.elim (hne rfl)

end Project.HexEncodeStdio.ReserveResourceCost
