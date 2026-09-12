import HexEncodeStdio.TotalWrite
import CodeLib.SepLogic.HostMemoryTrace
import CodeLib.SepLogic.CostedLoop
import CodeLib.SepLogic.CostedStepsStdIO

/-! Actual work of the generated hex consumer's Universal write path. -/
namespace Project.HexEncodeStdio.WriteResourceCost

open Wasm Wasm.SmallStep Project.HexStdio

set_option maxRecDepth 100000

private theorem read8_write32_disjoint (m : Mem) (writeAddr readAddr : UInt32)
    (value : UInt32) (h : readAddr.toNat < writeAddr.toNat ∨ writeAddr.toNat+4≤readAddr.toNat) :
    (m.write32 writeAddr value).read8 readAddr=m.read8 readAddr := by
  simpa only [Mem.read8] using Mem.write32_bytes_of_disjoint m writeAddr value readAddr.toNat h

def universalWriteStore (store : MachineStore Universal.State)
    (bytes : List UInt8) : MachineStore Universal.State :=
  { store with wasm := { store.wasm with host := TotalWrite.afterWrite store.wasm.host bytes } }

def writeAdapterResultStore (store : MachineStore Universal.State)
    (out : UInt32) (bytes : List UInt8) (length : UInt32) : MachineStore Universal.State :=
  let written := universalWriteStore store bytes
  { written with wasm := { written.wasm with mem :=
      (written.wasm.mem.write8 out 4).write32 (out+4) length } }

abbrev writeAllOuterBody := TotalWrite.writeOuterBody
abbrev writeAllLoopBody := TotalWrite.writeLoopBody
abbrev writeAllAfterAdapter := TotalWrite.writeAfterCall

def writeAllOuterControl : ControlFrame :=
  {kind := .block,paramArity := 0,resultArity := 0,body := writeAllOuterBody,
    continuation := func8.drop 6,belowStack := []}
def writeAllLoopControl : ControlFrame :=
  {kind := .loop,paramArity := 0,resultArity := 0,body := writeAllLoopBody,
    continuation := writeAllOuterBody.drop 4,belowStack := []}

def writeAllFrameStore (store : MachineStore Universal.State) (sp : UInt32) : MachineStore Universal.State :=
  {store with wasm := {store.wasm with globals :=
    {globals := store.wasm.globals.globals.set 0 (.i32 (sp-16))}}}

def writeAllResultStore (store : MachineStore Universal.State)
    (sp : UInt32) (bytes : List UInt8) (length : UInt32) : MachineStore Universal.State :=
  let written := writeAdapterResultStore (writeAllFrameStore store sp) (sp-16) bytes length
  {written with wasm := {written.wasm with globals :=
    {globals := written.wasm.globals.globals.set 0 (.i32 sp)}}}

/-- The generated write adapter executes eleven transitions and transfers the
actual requested bytes before storing its successful tag and count. -/
theorem write_adapter_cost (store : MachineStore Universal.State)
    (callerLocals : Locals) (stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value) (controls : List ControlFrame) (calls : List CallFrame)
    (out ignored pointer length : UInt32) (bytes : List UInt8)
    (hmodule : store.runtime.currentModule=Project.HexStdio.module)
    (hhost : store.runtime.currentHost=Universal.envFor Project.HexStdio.module)
    (hread : store.wasm.mem.readBytes pointer.toNat length.toNat=bytes)
    (hphysical : pointer.toNat+length.toNat≤store.wasm.mem.pages*65536)
    (hframe : out.toNat+8≤store.wasm.mem.pages*65536) :
    ∃ trace, CostedSteps CostedStdIO.work
      ⟨.running ⟨{callerLocals with values := [.i32 length,.i32 pointer,.i32 ignored,.i32 out]++stack},
        .call 20 :: code,arity,remainder,controls,calls⟩,store⟩ trace
      ⟨.running ⟨{callerLocals with values := stack},code,arity,remainder,controls,calls⟩,
        writeAdapterResultStore store out bytes length⟩ (11+length.toNat) ∧ (∀ kind ∈ trace,HostPrimaryMemoryKind kind) := by
  let frame : CallFrame :=
    {locals := {callerLocals with values := stack},continuation := code,
      resultArity := arity,callerRemainder := remainder,control := controls,
      returningInstance := store.runtime.entry}
  let params : List Value := [.i32 out,.i32 ignored,.i32 pointer,.i32 length]
  have pre : CostedSteps CostedStdIO.work
      ⟨.running ⟨{callerLocals with values := [.i32 length,.i32 pointer,.i32 ignored,.i32 out]++stack},
        .call 20 :: code,arity,remainder,controls,calls⟩,store⟩
      [.instruction (.call 20),.instruction (.localGet 3),.instruction (.localGet 2)]
      ⟨.running ⟨⟨params,[],[.i32 pointer,.i32 length]⟩,.call 1 :: func17.drop 3,
        0,[],[],frame::calls⟩,store⟩ 3 := by
    apply Steps.with_unit_cost
    · wasm_steps [(.call (fn := func17Def) (by rw [hmodule];decide) (by rw [hmodule];rfl)),
        (.localGet rfl)]
      exact Steps.single (.localGet rfl)
    · intro before kind after member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl|rfl <;> rfl
  have host := CostedStdIO.write_call_costed store 1 params [] [] (func17.drop 3)
    0 [] [] (frame::calls) length pointer (by rw [hmodule];decide)
    (by simpa only [hmodule] using (show Project.HexStdio.module.imports[1]=StdIO.imports[1] from rfl))
    (by rw [hhost];exact CostedStdIO.writeHost_resolves Project.HexStdio.module 1 (by decide) rfl)
    hphysical
  have hstore : {store with wasm := CostedStdIO.writeStore store.wasm length pointer}=
      universalWriteStore store bytes := by
    simp only [CostedStdIO.writeStore,universalWriteStore,TotalWrite.afterWrite,hread]
  rw [hstore] at host
  have tail : CostedSteps CostedStdIO.work
      ⟨.running ⟨⟨params,[],[]⟩,func17.drop 3,0,[],[],frame::calls⟩,
        universalWriteStore store bytes⟩
      [.instruction (.localGet 0),.instruction (.const 4),.instruction (.store8 0),
        .instruction (.localGet 0),.instruction (.localGet 3),.instruction (.store32 4),
        .administrative .returnFromCall]
      ⟨.running ⟨{callerLocals with values := stack},code,arity,remainder,controls,calls⟩,
        writeAdapterResultStore store out bytes length⟩ 7 := by
    apply Steps.with_unit_cost
    · simp only [func17,List.drop]
      wasm_steps [(.localGet rfl),.const,
        (.store8 rfl (by change out.toNat+0+1≤store.wasm.mem.pages*65536;omega)),
        (.localGet rfl),(.localGet rfl),
        (.store32 rfl (by change out.toNat+4+4≤store.wasm.mem.pages*65536;omega))]
      simp only [setMemory_eq,UInt32.add_zero]
      exact Steps.single (.returnFromCallFallthrough rfl)
    · intro before kind after member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  have full := (pre.trans host).trans tail
  rw [show 3+(1+length.toNat)+7=11+length.toNat by omega] at full
  refine ⟨_,full,?_⟩
  simp [HostPrimaryMemoryKind,PrimaryMemoryKind]

private def writeLocals (pointer length frame tag : UInt32) (values : List Value := []) : Locals :=
  ⟨[.i32 pointer,.i32 length],[.i32 frame,.i32 tag,.i32 0,.i32 0,.i32 0,.i64 0],values⟩

private def writePrefixTrace : List StepKind :=
  [.instruction (.call 11),.instruction (.globalGet 0),.instruction (.const 16),
    .instruction .sub,.instruction (.localTee 2),.instruction (.globalSet 0),
    .instruction (.block 0 0 writeAllOuterBody),.instruction (.localGet 1),
    .instruction .eqz,.instruction (.br_if 0),.instruction (.loop 0 0 writeAllLoopBody),
    .instruction (.localGet 2),.instruction (.localGet 2),.instruction (.const 15),
    .instruction .add,.instruction (.localGet 0),.instruction (.localGet 1)]

private def writeTailTrace : List StepKind :=
  [.instruction (.block 0 0 TotalWrite.writeBlock0),
    .instruction (.block 0 0 TotalWrite.writeBlock1),
    .instruction (.block 0 0 TotalWrite.writeBlock2),
    .instruction (.block 0 0 TotalWrite.writeBlock3),
    .instruction (.block 0 0 TotalWrite.writeBlock4),
    .instruction (.block 0 0 TotalWrite.writeBlock5),
    .instruction (.block 0 0 TotalWrite.writeBlock6),
    .instruction (.localGet 2),.instruction (.load8U 0),.instruction (.localTee 3),
    .instruction (.const 4),.instruction .eq,.instruction (.br_if 0),
    .instruction (.block 0 0 TotalWrite.writeCountBlock),
    .instruction (.localGet 2),.instruction (.load32 4),.instruction (.localTee 3),
    .instruction (.br_if 0),.instruction (.localGet 1),.instruction (.localGet 3),
    .instruction .ltU,.instruction (.br_if 3),.instruction (.localGet 0),
    .instruction (.localGet 3),.instruction .add,.instruction (.localSet 0),
    .instruction (.localGet 1),.instruction (.localGet 3),.instruction .sub,
    .instruction (.localTee 1),.instruction (.br_if 6),.instruction (.br 7),
    .instruction (.localGet 2),.instruction (.const 16),.instruction .add,
    .instruction (.globalSet 0),.administrative .returnFromCall]

/-- The full generated nonempty write_all call performs one Universal-host
write and returns to the exact saved caller. Its work is 65 plus output bytes. -/
theorem write_all_nonempty_cost (store : MachineStore Universal.State)
    (callerLocals : Locals) (stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value) (controls : List ControlFrame) (calls : List CallFrame)
    (pointer length sp : UInt32) (bytes : List UInt8)
    (hmodule : store.runtime.currentModule=Project.HexStdio.module)
    (hhost : store.runtime.currentHost=Universal.envFor Project.HexStdio.module)
    (hglobal : globalAt? store 0=some (.i32 sp)) (hne : length≠0)
    (hread : store.wasm.mem.readBytes pointer.toNat length.toNat=bytes)
    (hphysical : pointer.toNat+length.toNat≤store.wasm.mem.pages*65536)
    (hframe : (sp-16).toNat+16≤store.wasm.mem.pages*65536)
    (hframeWrap : (sp-16).toNat+16<UInt32.size) :
    ∃ trace, CostedSteps CostedStdIO.work
      ⟨.running ⟨{callerLocals with values := [.i32 length,.i32 pointer]++stack},
        .call 11::code,arity,remainder,controls,calls⟩,store⟩ trace
      ⟨.running ⟨{callerLocals with values := stack},code,arity,remainder,controls,calls⟩,
        writeAllResultStore store sp bytes length⟩ (65+length.toNat) ∧ (∀ kind ∈ trace,HostPrimaryMemoryKind kind) := by
  let frame := sp-16
  change frame.toNat+16≤store.wasm.mem.pages*65536 at hframe
  change frame.toNat+16<UInt32.size at hframeWrap
  let framed := writeAllFrameStore store sp
  let caller : CallFrame :=
    {locals := {callerLocals with values := stack},continuation := code,
      resultArity := arity,callerRemainder := remainder,control := controls,
      returningInstance := store.runtime.entry}
  have pre : CostedSteps CostedStdIO.work
      ⟨.running ⟨{callerLocals with values := [.i32 length,.i32 pointer]++stack},
        .call 11::code,arity,remainder,controls,calls⟩,store⟩ writePrefixTrace
      ⟨.running ⟨writeLocals pointer length frame 0
        [.i32 length,.i32 pointer,.i32 (15+frame),.i32 frame],
        .call 20::writeAllAfterAdapter,0,[],[writeAllLoopControl,writeAllOuterControl],caller::calls⟩,
        framed⟩ 17 := by
    apply Steps.with_unit_cost
    · unfold writePrefixTrace
      wasm_steps [(.call (fn := func8Def) (by rw [hmodule];decide) (by rw [hmodule];rfl)),
        (.globalGet hglobal),.const,.sub,(.localTee rfl),(.globalSet (by rw [hglobal];rfl)),
        .block,(.localGet rfl),(.eqz (result := 0) (by simp [hne])),.brIfZero,.loop,
        (.localGet rfl),(.localGet rfl),.const,.add,(.localGet rfl)]
      exact Steps.single (.localGet rfl)
    · intro before kind after member
      simp only [writePrefixTrace,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  obtain ⟨adapterTrace,adapter,adapterPrimary⟩ := write_adapter_cost framed (writeLocals pointer length frame 0)
    [] writeAllAfterAdapter 0 [] [writeAllLoopControl,writeAllOuterControl] (caller::calls)
    frame (15+frame) pointer length bytes hmodule hhost hread hphysical (by change frame.toNat+8≤store.wasm.mem.pages*65536;omega)
  let written := writeAdapterResultStore framed frame bytes length
  have hframe4 : (frame+4).toNat=frame.toNat+4 := by
    rw [UInt32.toNat_add]
    exact Nat.mod_eq_of_lt (by change frame.toNat+4<UInt32.size;omega)
  have htag : written.wasm.mem.read8 frame=4 := by
    unfold written writeAdapterResultStore
    rw [read8_write32_disjoint _ (frame+4) frame length
      (Or.inl (by rw [hframe4];omega))]
    simp [Mem.read8,Mem.write8]
  have hcount : written.wasm.mem.read32 (frame+4)=length := Mem.read32_write32_same _ _ _
  have tail : CostedSteps CostedStdIO.work
      ⟨.running ⟨writeLocals pointer length frame 0,writeAllAfterAdapter,0,[],
        [writeAllLoopControl,writeAllOuterControl],caller::calls⟩,written⟩ writeTailTrace
      ⟨.running ⟨{callerLocals with values := stack},code,arity,remainder,controls,calls⟩,
        writeAllResultStore store sp bytes length⟩ 37 := by
    apply Steps.with_unit_cost
    · simp only [writeTailTrace,writeAllAfterAdapter,
        TotalWrite.writeAfterCall,TotalWrite.writeLoopBody,TotalWrite.writeOuterBody,func8]
      wasm_steps [.block,.block,.block,.block,.block,.block,.block,
        (.localGet rfl),(.load8U rfl (by change frame.toNat+0+1≤store.wasm.mem.pages*65536;omega))]
      rw [UInt32.add_zero,htag]
      wasm_steps [(.localTee rfl),.const,(.eq (result := 1) (by rfl)),(.brIf (by decide) rfl),
        .block,(.localGet rfl),(.load32 rfl (by change frame.toNat+4+4≤store.wasm.mem.pages*65536;omega))]
      rw [hcount]
      wasm_steps [(.localTee rfl),(.brIf hne rfl),(.localGet rfl),(.localGet rfl),
        (.ltU (result := 0) (by simp)),.brIfZero,
        (.localGet rfl),(.localGet rfl),.add,(.localSet rfl),(.localGet rfl),(.localGet rfl),.sub,
        (.localTee rfl)]
      rw [UInt32.sub_self]
      wasm_steps [.brIfZero,(.br rfl),(.localGet rfl),.const,.add]
      rw [show (16:UInt32)+frame=sp by dsimp [frame];rw [UInt32.add_comm,UInt32.sub_add_cancel]]
      have hg : (globalAt? written 0).isSome=true := by
        have hzero := (getElem?_eq_some_iff.mp (show store.wasm.globals.globals[0]?=some (.i32 sp) by
          simpa only [globalAt?,canonicalGlobalIndex_zero] using hglobal)).1
        change (written.wasm.globals.globals[0]?).isSome=true
        rw [List.getElem?_eq_getElem (by simpa only [written,framed,writeAdapterResultStore,
          universalWriteStore,writeAllFrameStore,List.length_set] using hzero)]
        rfl
      wasm_steps [(.globalSet hg)]
      exact Steps.single (.returnFromCallFallthrough rfl)
    · intro before kind after member
      simp only [writeTailTrace,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|
        rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  have full := (pre.trans adapter).trans tail
  rw [show 17+(11+length.toNat)+37=65+length.toNat by omega] at full
  refine ⟨_,full,?_⟩
  intro kind member
  simp only [List.mem_append] at member
  rcases member with (member|member)|member
  · simp only [writePrefixTrace,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> trivial
  · exact adapterPrimary kind member
  · simp only [writeTailTrace,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> trivial

def writeAllEmptyResultStore (store : MachineStore Universal.State) (sp : UInt32) :
    MachineStore Universal.State :=
  let framed := writeAllFrameStore store sp
  {framed with wasm := {framed.wasm with globals :=
    {globals := framed.wasm.globals.globals.set 0 (.i32 sp)}}}

/-- Empty output follows the generated outer-block skip; no host write occurs. -/
theorem write_all_empty_cost (store : MachineStore Universal.State)
    (callerLocals : Locals) (stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value) (controls : List ControlFrame) (calls : List CallFrame)
    (pointer sp : UInt32)
    (hmodule : store.runtime.currentModule=Project.HexStdio.module)
    (hglobal : globalAt? store 0=some (.i32 sp)) :
    ∃ trace, CostedSteps CostedStdIO.work
      ⟨.running ⟨{callerLocals with values := [.i32 0,.i32 pointer]++stack},
        .call 11::code,arity,remainder,controls,calls⟩,store⟩ trace
      ⟨.running ⟨{callerLocals with values := stack},code,arity,remainder,controls,calls⟩,
        writeAllEmptyResultStore store sp⟩ 15 ∧ (∀ kind ∈ trace,HostPrimaryMemoryKind kind) := by
  let trace : List StepKind :=
    [.instruction (.call 11),.instruction (.globalGet 0),.instruction (.const 16),
      .instruction .sub,.instruction (.localTee 2),.instruction (.globalSet 0),
      .instruction (.block 0 0 writeAllOuterBody),.instruction (.localGet 1),
      .instruction .eqz,.instruction (.br_if 0),.instruction (.localGet 2),
      .instruction (.const 16),.instruction .add,.instruction (.globalSet 0),
      .administrative .returnFromCall]
  refine ⟨trace,?_,?_⟩
  rotate_left
  · intro kind member
    simp only [trace,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> trivial
  apply Steps.with_unit_cost
  · unfold trace
    wasm_steps [(.call (fn := func8Def) (by rw [hmodule];decide) (by rw [hmodule];rfl)),
      (.globalGet hglobal),.const,.sub,(.localTee rfl),(.globalSet (by rw [hglobal];rfl)),
      .block,(.localGet rfl),(.eqz (result := 1) rfl),(.brIf (by decide) rfl),
      (.localGet rfl),.const,.add]
    rw [show (16:UInt32)+(sp-16)=sp by rw [UInt32.add_comm,UInt32.sub_add_cancel]]
    have hzero := (getElem?_eq_some_iff.mp (show store.wasm.globals.globals[0]?=some (.i32 sp) by
      simpa only [globalAt?,canonicalGlobalIndex_zero] using hglobal)).1
    apply Steps.cons (.globalSet (by simpa [globalAt?,setGlobal_zero_eq,List.length_set] using hzero))
    exact Steps.single (.returnFromCallFallthrough rfl)
  · intro before kind after member
    simp only [trace,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

end Project.HexEncodeStdio.WriteResourceCost
