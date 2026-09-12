import HexEncodeStdio.AllocatorResourceCost
import CodeLib.SepLogic.CostedLoop

/-! Actual copying reallocator traces for the hex consumer. -/
namespace Project.HexEncodeStdio.ReallocatorResourceCost

open Wasm Wasm.SmallStep Project.HexStdio

private def blockAt (program : Program) (index : Nat) : Program :=
  match program[index]? with
  | some (.block _ _ body) => body
  | _ => []
private def outer := blockAt func15 0
private def growth := blockAt outer 31
private def copying := blockAt outer 35

private def prefixTrace (grows : Bool) : List StepKind :=
  [.instruction (.call 18), .instruction (.block 0 0 outer)] ++
  (outer.take 31).map StepKind.instruction ++
  [.instruction (.block 0 0 growth)] ++
  (if grows then growth.map StepKind.instruction ++ [.administrative .exitControl]
   else (growth.take 10).map StepKind.instruction) ++
  ((outer.drop 32).take 3).map StepKind.instruction ++
  [.instruction (.block 0 0 copying)] ++ (copying.take 15).map StepKind.instruction

private def callerFrame (store : MachineStore Universal.State)
    (params localValues stack : List Value) (code : Program) (arity : Nat)
    (remainder : List Value) (controls : List ControlFrame) : CallFrame :=
  { locals := ⟨params,localValues,stack⟩, continuation := code, resultArity := arity,
    callerRemainder := remainder, control := controls, returningInstance := store.runtime.entry }

private def outerFrame : ControlFrame :=
  { kind := .block,paramArity := 0,resultArity := 0,body := outer,
    continuation := [.call 16,.unreachable],belowStack := [] }
private def copyFrame : ControlFrame :=
  { kind := .block,paramArity := 0,resultArity := 0,body := copying,
    continuation := [.localGet 2,.ret],belowStack := [] }

private def beforeCopy (store : MachineStore Universal.State) (memory : Mem)
    (params localValues stack : List Value) (code : Program) (arity : Nat)
    (remainder : List Value) (controls : List ControlFrame) (calls : List CallFrame)
    (oldPtr oldSize align newSize oldBump : UInt32) : Config Universal.State :=
  let pointer := allocatorPtr oldBump align
  let count := reallocatorCopyLen oldSize newSize
  ⟨.running ⟨⟨[.i32 oldPtr,.i32 oldSize,.i32 pointer,.i32 newSize],
    [.i32 count,.i32 (allocatorRequiredPages newSize align oldBump),.i32 (UInt32.ofNat store.wasm.mem.pages)],
    [.i32 count,.i32 oldPtr,.i32 pointer]⟩,
    [.memoryCopy],1,[],[copyFrame,outerFrame],
    callerFrame store params localValues stack code arity remainder controls::calls⟩,
    allocatorBumpStore (allocatorGrownStore store memory) (allocatorFinish newSize align oldBump)⟩
private theorem no_grow_prefix
    (store : MachineStore Universal.State)
    (params localValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (oldPtr oldSize align newSize oldBump : UInt32)
    (hmod : store.runtime.currentModule = «module»)
    (hread : store.wasm.mem.read32 1053960 = oldBump)
    (hbound : 1053960 + 4 ≤ store.wasm.mem.pages * 65536)
    (hfirst : ¬ allocatorBase oldBump + ((0xffffffff : UInt32) + align) <
      (0xffffffff : UInt32) + align)
    (hsecond : ¬ allocatorFinish newSize align oldBump <
      allocatorPtr oldBump align)
    (hnegative : ¬ (allocatorFinish newSize align oldBump).toInt32 <
      UInt32.toInt32 0)
    (henough : allocatorRequiredPages newSize align oldBump ≤
      UInt32.ofNat store.wasm.mem.pages)
    (hptrNonzero : allocatorPtr oldBump align ≠ 0)
    (hcopyNonzero : reallocatorCopyLen oldSize newSize ≠ 0) :
    Steps
      ⟨.running ⟨⟨params,localValues,[.i32 newSize,.i32 align,.i32 oldSize,.i32 oldPtr] ++ stack⟩,
        .call 18::code,arity,remainder,controls,calls⟩,store⟩
      (prefixTrace false)
      (beforeCopy store store.wasm.mem params localValues stack code arity remainder controls calls
        oldPtr oldSize align newSize oldBump) := by
  unfold prefixTrace
  have hnot : ¬18 < store.runtime.currentModule.imports.length := by
    rw [hmod]; decide
  have hfn : store.runtime.currentModule.funcs[
      18 - store.runtime.currentModule.imports.length]? = some func15Def := by
    rw [hmod]; rfl
  apply Steps.cons (Step.call hnot hfn)
  simp [func15Def, Function.toLocals, Function.numParams,
    ValueType.zero, func15]
  apply Steps.cons Step.block
  apply Steps.cons (Step.localGet rfl)
  apply Steps.cons Step.const
  apply Steps.cons Step.add
  apply Steps.cons (Step.localTee rfl)
  apply Steps.cons Step.const
  apply Steps.cons
    (Step.load32 rfl (address := .i32 (0)) (offset := 1053960) (by simpa using hbound))
  simp only [UInt32.zero_add, hread]
  apply Steps.cons (Step.localTee rfl)
  apply Steps.cons Step.const
  apply Steps.cons (Step.localGet rfl)
  apply Steps.cons (Step.select
    (selected := .i32 (allocatorBase oldBump)) (by
      simp only [allocatorBase]
      by_cases h : oldBump = 0 <;> simp [h]))
  apply Steps.cons Step.add
  apply Steps.cons (Step.localTee rfl)
  apply Steps.cons (Step.localGet rfl)
  apply Steps.cons (Step.ltU (result := 0) (by simp [hfirst]))
  apply Steps.cons Step.brIfZero
  apply Steps.cons (Step.localGet rfl)
  apply Steps.cons Step.const
  apply Steps.cons (Step.localGet rfl)
  apply Steps.cons Step.sub
  apply Steps.cons Step.and
  apply Steps.cons (Step.localTee rfl)
  apply Steps.cons (Step.localGet rfl)
  apply Steps.cons Step.add
  apply Steps.cons (Step.localTee rfl)
  apply Steps.cons (Step.localGet rfl)
  have hsecond' : ¬
      newSize + ((allocatorBase oldBump + (0xffffffff + align)) &&& (-align)) <
        ((allocatorBase oldBump + (0xffffffff + align)) &&& (-align)) := by
    simpa [allocatorFinish, allocatorPtr, UInt32.sub_eq_add_neg] using hsecond
  apply Steps.cons (Step.ltU (result := 0) (by simp [hsecond']))
  apply Steps.cons Step.brIfZero
  apply Steps.cons (Step.localGet rfl)
  apply Steps.cons Step.const
  have hnegative' : ¬
      (newSize + ((allocatorBase oldBump + (0xffffffff + align)) &&&
        (-align))).toInt32 < UInt32.toInt32 0 := by
    simpa [allocatorFinish, allocatorPtr, UInt32.sub_eq_add_neg]
      using hnegative
  apply Steps.cons
    (Step.ltS (result := 0) (if_neg hnegative').symm)
  apply Steps.cons Step.brIfZero
  apply Steps.cons Step.block
  apply Steps.cons (Step.localGet rfl)
  apply Steps.cons Step.const
  apply Steps.cons Step.add
  apply Steps.cons Step.const
  apply Steps.cons Step.shrU
  apply Steps.cons (Step.localTee rfl)
  apply Steps.cons Step.memorySize
  rw [hmod]
  have hm64 : «module».memIs64 = false := rfl
  rw [hm64]
  simp only [sizeValue, Bool.false_eq_true, if_false]
  apply Steps.cons (Step.localTee rfl)
  have henough' :
      ((65535 + (newSize + ((allocatorBase oldBump +
        (0xffffffff + align)) &&& (-align)))) >>> (16 % 32)) ≤
          UInt32.ofNat store.wasm.mem.pages := by
    simpa [allocatorRequiredPages, allocatorFinish, allocatorPtr,
      UInt32.sub_eq_add_neg] using henough
  apply Steps.cons
    (Step.leU (result := 1) (if_pos henough').symm)
  apply Steps.cons (Step.brIf (condition := 1) (by decide) rfl)
  apply Steps.cons Step.const
  apply Steps.cons (Step.localGet rfl)
  apply Steps.cons
    (Step.store32 rfl (address := .i32 (0)) (offset := 1053960)
      (by simpa using hbound))
  simp only [setMemory_eq]
  apply Steps.cons Step.block
  apply Steps.cons (Step.localGet rfl)
  apply Steps.cons (Step.eqz rfl)
  have hptr : (allocatorBase oldBump + (0xffffffff + align)) &&& (0 - align) ≠ 0 := hptrNonzero
  rw [if_neg hptr]
  have hptrDef : allocatorPtr oldBump align ≠ 0 := by
    simpa [allocatorPtr] using hptr
  have hptrNeg :
      (allocatorBase oldBump + (0xffffffff + align)) &&& (-align) ≠ 0 := by
    simpa [UInt32.sub_eq_add_neg] using hptr
  apply Steps.cons Step.brIfZero
  apply Steps.cons (Step.localGet rfl)
  apply Steps.cons (Step.localGet rfl)
  apply Steps.cons (Step.localGet rfl)
  apply Steps.cons (Step.localGet rfl)
  apply Steps.cons (Step.ltU rfl)
  apply Steps.cons (Step.select rfl)
  have hselect :
      (if (if newSize < oldSize then (1 : UInt32) else 0) ≠ 0 then
          Value.i32 newSize else Value.i32 oldSize) =
        .i32 (reallocatorCopyLen oldSize newSize) := by
    by_cases h : newSize < oldSize <;> simp [h, reallocatorCopyLen]
  rw [hselect]
  apply Steps.cons (Step.localTee rfl)
  apply Steps.cons (Step.eqz rfl)
  have hlen := hcopyNonzero
  rw [if_neg hlen]
  apply Steps.cons Step.brIfZero
  apply Steps.cons (Step.localGet rfl)
  apply Steps.cons (Step.localGet rfl)
  apply Steps.cons (Step.localGet rfl)
  simp only [beforeCopy,callerFrame,copyFrame,outerFrame,copying,outer,blockAt,
    allocatorBumpStore,allocatorGrownStore,allocatorFinish,allocatorPtr,allocatorRequiredPages,
    UInt32.sub_eq_add_neg,UInt32.zero_add,func15]
  exact Steps.refl _

private theorem grow_prefix
    (store : MachineStore Universal.State)
    (params localValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (oldPtr oldSize align newSize oldBump : UInt32)
    (memory : Mem) (previousPages : Nat)
    (hmod : store.runtime.currentModule = «module»)
    (hread : store.wasm.mem.read32 1053960 = oldBump)
    (hbound : 1053960 + 4 ≤ store.wasm.mem.pages * 65536)
    (hboundGrown : 1053960 + 4 ≤ memory.pages * 65536)
    (hfirst : ¬ allocatorBase oldBump + ((0xffffffff : UInt32) + align) <
      (0xffffffff : UInt32) + align)
    (hsecond : ¬ allocatorFinish newSize align oldBump <
      allocatorPtr oldBump align)
    (hnegative : ¬ (allocatorFinish newSize align oldBump).toInt32 <
      UInt32.toInt32 0)
    (hneed : ¬ allocatorRequiredPages newSize align oldBump ≤
      UInt32.ofNat store.wasm.mem.pages)
    (hgrow : store.wasm.mem.grow
        (allocatorRequiredPages newSize align oldBump -
          UInt32.ofNat store.wasm.mem.pages)
        (store.wasm.memoryCap store.runtime.currentModule 0) =
          some (memory, previousPages))
    (hresult : previousPages.toUInt32 ≠ (0xffffffff : UInt32))
    (hptrNonzero : allocatorPtr oldBump align ≠ 0)
    (hcopyNonzero : reallocatorCopyLen oldSize newSize ≠ 0) :
    Steps
      ⟨.running ⟨⟨params,localValues,[.i32 newSize,.i32 align,.i32 oldSize,.i32 oldPtr] ++ stack⟩,
        .call 18::code,arity,remainder,controls,calls⟩,store⟩
      (prefixTrace true)
      (beforeCopy store memory params localValues stack code arity remainder controls calls
        oldPtr oldSize align newSize oldBump) := by
  unfold prefixTrace
  have hnot : ¬18 < store.runtime.currentModule.imports.length := by
    rw [hmod]; decide
  have hfn : store.runtime.currentModule.funcs[
      18 - store.runtime.currentModule.imports.length]? = some func15Def := by
    rw [hmod]; rfl
  apply Steps.cons (Step.call hnot hfn)
  simp [func15Def, Function.toLocals, Function.numParams,
    ValueType.zero, func15]
  apply Steps.cons Step.block
  apply Steps.cons (Step.localGet rfl)
  apply Steps.cons Step.const
  apply Steps.cons Step.add
  apply Steps.cons (Step.localTee rfl)
  apply Steps.cons Step.const
  apply Steps.cons
    (Step.load32 rfl (address := .i32 (0)) (offset := 1053960) (by simpa using hbound))
  simp only [UInt32.zero_add, hread]
  apply Steps.cons (Step.localTee rfl)
  apply Steps.cons Step.const
  apply Steps.cons (Step.localGet rfl)
  apply Steps.cons (Step.select
    (selected := .i32 (allocatorBase oldBump)) (by
      simp only [allocatorBase]
      by_cases h : oldBump = 0 <;> simp [h]))
  apply Steps.cons Step.add
  apply Steps.cons (Step.localTee rfl)
  apply Steps.cons (Step.localGet rfl)
  apply Steps.cons (Step.ltU (result := 0) (by simp [hfirst]))
  apply Steps.cons Step.brIfZero
  apply Steps.cons (Step.localGet rfl)
  apply Steps.cons Step.const
  apply Steps.cons (Step.localGet rfl)
  apply Steps.cons Step.sub
  apply Steps.cons Step.and
  apply Steps.cons (Step.localTee rfl)
  apply Steps.cons (Step.localGet rfl)
  apply Steps.cons Step.add
  apply Steps.cons (Step.localTee rfl)
  apply Steps.cons (Step.localGet rfl)
  have hsecond' : ¬
      newSize + ((allocatorBase oldBump + (0xffffffff + align)) &&& (-align)) <
        ((allocatorBase oldBump + (0xffffffff + align)) &&& (-align)) := by
    simpa [allocatorFinish, allocatorPtr, UInt32.sub_eq_add_neg] using hsecond
  apply Steps.cons (Step.ltU (result := 0) (by simp [hsecond']))
  apply Steps.cons Step.brIfZero
  apply Steps.cons (Step.localGet rfl)
  apply Steps.cons Step.const
  have hnegative' : ¬
      (newSize + ((allocatorBase oldBump + (0xffffffff + align)) &&&
        (-align))).toInt32 < UInt32.toInt32 0 := by
    simpa [allocatorFinish, allocatorPtr, UInt32.sub_eq_add_neg]
      using hnegative
  apply Steps.cons
    (Step.ltS (result := 0) (if_neg hnegative').symm)
  apply Steps.cons Step.brIfZero
  apply Steps.cons Step.block
  apply Steps.cons (Step.localGet rfl)
  apply Steps.cons Step.const
  apply Steps.cons Step.add
  apply Steps.cons Step.const
  apply Steps.cons Step.shrU
  apply Steps.cons (Step.localTee rfl)
  apply Steps.cons Step.memorySize
  rw [hmod]
  have hm64 : «module».memIs64 = false := rfl
  rw [hm64]
  simp only [sizeValue, Bool.false_eq_true, if_false]
  apply Steps.cons (Step.localTee rfl)
  have hneed' : ¬
      ((65535 + (newSize + ((allocatorBase oldBump +
        (0xffffffff + align)) &&& (-align)))) >>> (16 % 32)) ≤
          UInt32.ofNat store.wasm.mem.pages := by
    simpa [allocatorRequiredPages, allocatorFinish, allocatorPtr,
      UInt32.sub_eq_add_neg] using hneed
  apply Steps.cons
    (Step.leU (result := 0) (if_neg hneed').symm)
  apply Steps.cons Step.brIfZero
  apply Steps.cons (Step.localGet rfl)
  apply Steps.cons (Step.localGet rfl)
  apply Steps.cons Step.sub
  apply Steps.cons (Step.memoryGrowSuccess (by
    simpa [allocatorRequiredPages, allocatorFinish, allocatorPtr,
      UInt32.sub_eq_add_neg] using hgrow))
  rw [setMemory_eq]
  apply Steps.cons Step.const
  apply Steps.cons (Step.eq (result := 0) (by simp [hresult]))
  apply Steps.cons Step.brIfZero
  apply Steps.cons (Step.exitControl rfl)
  apply Steps.cons Step.const
  apply Steps.cons (Step.localGet rfl)
  apply Steps.cons
    (Step.store32 rfl (address := .i32 (0)) (offset := 1053960)
      (by simpa using hboundGrown))
  simp only [setMemory_eq]
  apply Steps.cons Step.block
  apply Steps.cons (Step.localGet rfl)
  apply Steps.cons (Step.eqz rfl)
  have hptr : (allocatorBase oldBump + (0xffffffff + align)) &&& (0 - align) ≠ 0 := hptrNonzero
  rw [if_neg hptr]
  have hptrDef : allocatorPtr oldBump align ≠ 0 := by
    simpa [allocatorPtr] using hptr
  have hptrNeg :
      (allocatorBase oldBump + (0xffffffff + align)) &&& (-align) ≠ 0 := by
    simpa [UInt32.sub_eq_add_neg] using hptr
  apply Steps.cons Step.brIfZero
  apply Steps.cons (Step.localGet rfl)
  apply Steps.cons (Step.localGet rfl)
  apply Steps.cons (Step.localGet rfl)
  apply Steps.cons (Step.localGet rfl)
  apply Steps.cons (Step.ltU rfl)
  apply Steps.cons (Step.select rfl)
  have hselect :
      (if (if newSize < oldSize then (1 : UInt32) else 0) ≠ 0 then
          Value.i32 newSize else Value.i32 oldSize) =
        .i32 (reallocatorCopyLen oldSize newSize) := by
    by_cases h : newSize < oldSize <;> simp [h, reallocatorCopyLen]
  rw [hselect]
  apply Steps.cons (Step.localTee rfl)
  apply Steps.cons (Step.eqz rfl)
  have hlen := hcopyNonzero
  rw [if_neg hlen]
  apply Steps.cons Step.brIfZero
  apply Steps.cons (Step.localGet rfl)
  apply Steps.cons (Step.localGet rfl)
  apply Steps.cons (Step.localGet rfl)
  simp only [beforeCopy,callerFrame,copyFrame,outerFrame,copying,outer,blockAt,
    allocatorBumpStore,allocatorGrownStore,allocatorFinish,allocatorPtr,allocatorRequiredPages,
    UInt32.sub_eq_add_neg,UInt32.zero_add,func15]
  exact Steps.refl _

private theorem prefixTrace_length (grows : Bool) :
    (prefixTrace grows).length = if grows then 71 else 63 := by cases grows <;> rfl

private theorem prefixTrace_labels (grows : Bool) :
    ∀ kind ∈ prefixTrace grows, GrowthCostKind kind := by
  cases grows <;> intro kind member <;> fin_cases member <;> trivial

private def tailTrace : List StepKind :=
  [.instruction .memoryCopy,.administrative .exitControl,.instruction (.localGet 2),
    .administrative .returnFromCall]

private theorem copy_return_cost (store : MachineStore Universal.State) (memory : Mem)
    (params localValues stack : List Value) (code : Program) (arity : Nat)
    (remainder : List Value) (controls : List ControlFrame) (calls : List CallFrame)
    (oldPtr oldSize align newSize oldBump : UInt32)
    (hptr : allocatorPtr oldBump align ≠ 0)
    (hcopy : reallocatorCopyLen oldSize newSize ≠ 0)
    (hsource : oldPtr.toNat+(reallocatorCopyLen oldSize newSize).toNat≤memory.pages*65536)
    (hdestination : (allocatorPtr oldBump align).toNat+(reallocatorCopyLen oldSize newSize).toNat≤memory.pages*65536) :
    CostedSteps CostedStdIO.work
      (beforeCopy store memory params localValues stack code arity remainder controls calls oldPtr oldSize align newSize oldBump)
      tailTrace
      ⟨.running ⟨⟨params,localValues,.i32 (allocatorPtr oldBump align)::stack⟩,
        code,arity,remainder,controls,calls⟩,
        reallocatorResultStore (allocatorGrownStore store memory) oldPtr oldSize align newSize oldBump⟩
      (4+(reallocatorCopyLen oldSize newSize).toNat) := by
  let ptr := allocatorPtr oldBump align
  let count := reallocatorCopyLen oldSize newSize
  let ps : List Value := [.i32 oldPtr,.i32 oldSize,.i32 ptr,.i32 newSize]
  let ls : List Value := [.i32 count,.i32 (allocatorRequiredPages newSize align oldBump),.i32 (UInt32.ofNat store.wasm.mem.pages)]
  let frames := callerFrame store params localValues stack code arity remainder controls::calls
  let allocated := allocatorBumpStore (allocatorGrownStore store memory) (allocatorFinish newSize align oldBump)
  let copied : MachineStore Universal.State :=
    { allocated with wasm := { allocated.wasm with mem := allocated.wasm.mem.copy ptr.toNat oldPtr.toNat count.toNat } }
  have copyRun := memoryCopy32_costed allocated ps ls [] [] 1 [] [copyFrame,outerFrame] frames
    ptr oldPtr count hdestination hsource CostedStdIO.hostBytes
  have tail : Steps
      ⟨.running ⟨⟨ps,ls,[]⟩,[],1,[],[copyFrame,outerFrame],frames⟩,copied⟩
      [.administrative .exitControl,.instruction (.localGet 2),.administrative .returnFromCall]
      ⟨.running ⟨⟨params,localValues,.i32 ptr::stack⟩,code,arity,remainder,controls,calls⟩,copied⟩ := by
    wasm_steps [(.exitControl rfl),(.localGet rfl)]
    exact Steps.single (Step.returnFromCallExplicit rfl)
  have tailCost := tail.with_unit_cost (charge := CostedStdIO.work) (by
    intro before kind after member
    fin_cases member <;> rfl)
  have run := copyRun.trans tailCost
  convert run using 1 <;>
    simp [beforeCopy,ps,ls,ptr,count,frames,allocated,copied,tailTrace,
      reallocatorResultStore,hptr,hcopy,Nat.add_comm,Nat.add_left_comm]
  omega

/-- The actual bump commit and copying result after any necessary growth. -/
def finalStore (store : MachineStore Universal.State) (oldPtr oldSize size bump : UInt32) :
    MachineStore Universal.State :=
  reallocatorResultStore
    (allocatorGrownStore store (AllocatorResourceCost.grownMemory store.wasm.mem
      ((allocatorBase bump).toNat + size.toNat))) oldPtr oldSize 1 size bump

/-- The actual copying call18 terminates normally from initial request and
physical-source facts. The returned store records growth, cursor commit and
old-allocation copying; no future execution or grow-success premise is used. -/
theorem reallocator_byte_cost (store : MachineStore Universal.State)
    (params localValues stack : List Value) (code : Program) (arity : Nat)
    (remainder : List Value) (controls : List ControlFrame) (calls : List CallFrame)
    (oldPtr oldSize size bump : UInt32) (frontier : Nat)
    (hmodule : store.runtime.currentModule = Project.HexStdio.module)
    (hcap : store.wasm.memoryCap store.runtime.currentModule 0 = Module.memoryHardCap)
    (hpages : store.wasm.mem.pages ≤ Module.memoryHardCap)
    (hread : store.wasm.mem.read32 1053960 = bump)
    (hcursor : 1053960 + 4 ≤ store.wasm.mem.pages * 65536)
    (hfrontier : (allocatorBase bump).toNat = frontier)
    (hfit : frontier + size.toNat < 2147483648)
    (hpositive : 0 < oldSize.toNat) (hle : oldSize.toNat ≤ size.toNat)
    (hsource : oldPtr.toNat + oldSize.toNat ≤ store.wasm.mem.pages * 65536) :
    ∃ trace, trace.length =
        (if AllocatorResourceCost.requiredPages (frontier + size.toNat) ≤ store.wasm.mem.pages then 67 else 75) ∧
      CostedSteps CostedStdIO.work
        ⟨.running ⟨⟨params,localValues,[.i32 size,.i32 1,.i32 oldSize,.i32 oldPtr] ++ stack⟩,
          .call 18::code,arity,remainder,controls,calls⟩,store⟩ trace
        ⟨.running ⟨⟨params,localValues,.i32 (UInt32.ofNat frontier)::stack⟩,
          code,arity,remainder,controls,calls⟩,finalStore store oldPtr oldSize size bump⟩
        (trace.length+oldSize.toNat+65536*
          (AllocatorResourceCost.requiredPages (frontier+size.toNat)-store.wasm.mem.pages)) ∧
      ∀ kind ∈ trace, PrimaryMemoryKind kind := by
  have hfinishNat := AllocatorResourceCost.finish_toNat size bump frontier hfrontier hfit
  have hrequired := AllocatorResourceCost.required_toNat size bump frontier hfrontier hfit
  have hfirst : ¬ allocatorBase bump + ((0xffffffff : UInt32)+1) < (0xffffffff : UInt32)+1 := by simp
  have hsecond : ¬ allocatorFinish size 1 bump < allocatorPtr bump 1 := by
    rw [UInt32.not_lt,UInt32.le_iff_toNat_le,hfinishNat,AllocatorResourceCost.ptr_one,hfrontier]
    omega
  have hnegative := AllocatorResourceCost.nonnegative (allocatorFinish size 1 bump) (by rw [hfinishNat]; exact hfit)
  have hptr : allocatorPtr bump 1 = UInt32.ofNat frontier := by
    rw [AllocatorResourceCost.ptr_one,← hfrontier,UInt32.ofNat_toNat]
  have hptrNe : allocatorPtr bump 1 ≠ 0 := by
    rw [AllocatorResourceCost.ptr_one,allocatorBase]
    split <;> simp_all
  have hcopy : reallocatorCopyLen oldSize size = oldSize := by
    unfold reallocatorCopyLen
    rw [if_neg (by rw [UInt32.not_lt,UInt32.le_iff_toNat_le];exact hle)]
  have hcopyNe : reallocatorCopyLen oldSize size ≠ 0 := by
    rw [hcopy]
    intro hz
    rw [hz] at hpositive
    contradiction
  have hpagesNat := UInt32.toNat_ofNat_of_lt' (lt_of_le_of_lt hpages (by decide : Module.memoryHardCap<UInt32.size))
  have hcompare : allocatorRequiredPages size 1 bump≤UInt32.ofNat store.wasm.mem.pages ↔
      AllocatorResourceCost.requiredPages (frontier+size.toNat)≤store.wasm.mem.pages := by
    rw [UInt32.le_iff_toNat_le,hrequired,hpagesNat]
  have hendCover := (AllocatorResourceCost.required_bound _ hfit).2
  have hptrNat : (allocatorPtr bump 1).toNat = frontier := by rw [AllocatorResourceCost.ptr_one,hfrontier]
  by_cases henough : AllocatorResourceCost.requiredPages (frontier+size.toNat)≤store.wasm.mem.pages
  · have first := no_grow_prefix store params localValues stack code arity remainder controls calls
      oldPtr oldSize 1 size bump hmodule hread hcursor hfirst hsecond hnegative
      (hcompare.mpr henough) hptrNe hcopyNe
    have firstCost := first.growth_byteWork (prefixTrace_labels false) CostedStdIO.hostBytes
    have tail := copy_return_cost store store.wasm.mem params localValues stack code arity remainder controls calls
      oldPtr oldSize 1 size bump hptrNe hcopyNe (by simpa only [hcopy] using hsource)
      (by rw [hcopy,hptrNat];have hp:=Nat.mul_le_mul_right 65536 henough;omega)
    refine ⟨prefixTrace false++tailTrace,?_,?_,?_⟩
    · rw [List.length_append,prefixTrace_length,if_pos henough]
      rfl
    · have run := firstCost.trans tail
      convert run using 1
      · simp only [finalStore,AllocatorResourceCost.grownMemory,hfrontier,max_eq_left henough,hptr]
      · simp only [List.length_append,prefixTrace_length,tailTrace,List.length_cons,List.length_nil,
          beforeCopy,allocatorBumpStore,allocatorGrownStore,Mem.write32_pages,hcopy,Bool.false_eq_true,
          ite_false,Nat.sub_self,Nat.mul_zero,Nat.add_zero,Nat.sub_eq_zero_of_le henough]
        omega
    · intro kind member
      rcases List.mem_append.mp member with hm | hm
      · exact (prefixTrace_labels false kind hm).primary
      · fin_cases hm <;> trivial
  · have hneed := fun h => henough (hcompare.mp h)
    have hrequiredBound : (allocatorRequiredPages size 1 bump).toNat≤32768 := by
      rw [hrequired];exact (AllocatorResourceCost.required_bound _ hfit).1
    have hgrow := AllocatorResourceCost.grow_success store (allocatorRequiredPages size 1 bump)
      hcap hpages hrequiredBound hneed
    let memory : Mem := { store.wasm.mem with pages := (allocatorRequiredPages size 1 bump).toNat }
    have hbefore : store.wasm.mem.pages≤memory.pages := by change _≤(allocatorRequiredPages size 1 bump).toNat;rw [hrequired];omega
    have hresult : store.wasm.mem.pages.toUInt32≠(0xffffffff : UInt32) := by
      intro hz
      have hh := congrArg UInt32.toNat hz
      rw [hpagesNat] at hh
      have : store.wasm.mem.pages≤65536 := hpages
      change store.wasm.mem.pages=4294967295 at hh
      omega
    have first := grow_prefix store params localValues stack code arity remainder controls calls
      oldPtr oldSize 1 size bump memory store.wasm.mem.pages hmodule hread hcursor
      (hcursor.trans (Nat.mul_le_mul_right 65536 hbefore)) hfirst hsecond hnegative hneed hgrow hresult hptrNe hcopyNe
    have firstCost := first.growth_byteWork (prefixTrace_labels true) CostedStdIO.hostBytes
    have tail := copy_return_cost store memory params localValues stack code arity remainder controls calls
      oldPtr oldSize 1 size bump hptrNe hcopyNe
      (by rw [hcopy];exact hsource.trans (Nat.mul_le_mul_right 65536 hbefore))
      (by rw [hcopy,hptrNat];change frontier+oldSize.toNat≤(allocatorRequiredPages size 1 bump).toNat*65536;rw [hrequired];omega)
    refine ⟨prefixTrace true++tailTrace,?_,?_,?_⟩
    · rw [List.length_append,prefixTrace_length,if_neg henough]
      rfl
    · have run := firstCost.trans tail
      convert run using 1
      · simp only [finalStore,AllocatorResourceCost.grownMemory,hfrontier,
          max_eq_right (Nat.le_of_not_ge henough),memory,hrequired,hptr]
      · simp only [List.length_append,prefixTrace_length,tailTrace,List.length_cons,List.length_nil,
          beforeCopy,allocatorBumpStore,allocatorGrownStore,Mem.write32_pages,memory,hrequired,hcopy,ite_true]
        omega
    · intro kind member
      rcases List.mem_append.mp member with hm | hm
      · exact (prefixTrace_labels true kind hm).primary
      · fin_cases hm <;> trivial

@[simp] theorem finalStore_pages (store : MachineStore Universal.State) (oldPtr oldSize size bump : UInt32) :
    (finalStore store oldPtr oldSize size bump).wasm.mem.pages =
      max store.wasm.mem.pages (AllocatorResourceCost.requiredPages ((allocatorBase bump).toNat+size.toNat)) := by
  dsimp only [finalStore,reallocatorResultStore]
  split <;> rfl

theorem finalStore_frame (store : MachineStore Universal.State) (oldPtr oldSize size bump : UInt32) :
    (finalStore store oldPtr oldSize size bump).runtime = store.runtime ∧
    (finalStore store oldPtr oldSize size bump).wasm.globals = store.wasm.globals ∧
    (finalStore store oldPtr oldSize size bump).wasm.host = store.wasm.host ∧
    (finalStore store oldPtr oldSize size bump).wasm.memoryCaps = store.wasm.memoryCaps ∧
    (finalStore store oldPtr oldSize size bump).wasm.globalIds = store.wasm.globalIds ∧
    (finalStore store oldPtr oldSize size bump).wasm.memoryIds = store.wasm.memoryIds := by
  dsimp only [finalStore,reallocatorResultStore]
  split <;> exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

private theorem copy_word_before (memory : Mem) (destination source count : Nat) (address : UInt32)
    (h : address.toNat+4≤destination) :
    (memory.copy destination source count).read32 address=memory.read32 address := by
  simp only [Mem.read32,Mem.copy]
  rw [if_neg,if_neg,if_neg,if_neg]
  all_goals omega

theorem finalStore_cursor (store : MachineStore Universal.State) (oldPtr oldSize size bump : UInt32)
    (hseparate : 1053960+4≤(allocatorPtr bump 1).toNat) :
    (finalStore store oldPtr oldSize size bump).wasm.mem.read32 1053960 = allocatorFinish size 1 bump := by
  dsimp only [finalStore,reallocatorResultStore]
  split
  · exact Mem.read32_write32_same _ _ _
  · rw [copy_word_before _ _ _ _ _ hseparate]
    exact Mem.read32_write32_same _ _ _

end Project.HexEncodeStdio.ReallocatorResourceCost
