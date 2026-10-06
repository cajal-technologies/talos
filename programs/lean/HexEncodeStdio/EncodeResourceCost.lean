import HexEncodeStdio.TotalEncodeLoop
import HexEncodeStdio.TotalEncodeFunction
import CodeLib.SepLogic.CostedLoop
import CodeLib.SepLogic.HostMemoryTrace
import CodeLib.SepLogic.CostedStepsStdIO

/-! Concrete transitions and numerical work for the generated hexadecimal encoder. -/
namespace Project.HexEncodeStdio.EncodeResourceCost

open Wasm Wasm.SmallStep Project.HexStdio

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

abbrev sentinel : UInt32 := 1114112

/-- The iterator's common reset, performed on every actual call. -/
def iteratorResetStore (store : MachineStore Universal.State) (pointer : UInt32) :
    MachineStore Universal.State :=
  {store with wasm := {store.wasm with mem := store.wasm.mem.write32 pointer sentinel}}

def iteratorBody : Program :=
  match Project.HexStdio.func18[6]? with
  | some (Instruction.block _ _ body _ _) => body
  | _ => []

/-- Saved low digit: reset the iterator sentinel and return to the saved caller. -/
theorem iterator_low_cost (store : MachineStore Universal.State)
    (callerLocals : Locals) (stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value) (controls : List ControlFrame) (calls : List CallFrame)
    (pointer saved : UInt32)
    (hmodule : store.runtime.currentModule=Project.HexStdio.module)
    (hread : store.wasm.mem.read32 pointer=saved) (hsaved : saved≠sentinel)
    (hphysical : pointer.toNat+4≤store.wasm.mem.pages*65536) :
    ∃ trace, CostedSteps CostedStdIO.work
      ⟨.running ⟨{callerLocals with values := .i32 pointer::stack},
        .call 21::code,arity,remainder,controls,calls⟩,store⟩ trace
      ⟨.running ⟨{callerLocals with values := .i32 saved::stack},
        code,arity,remainder,controls,calls⟩,iteratorResetStore store pointer⟩ 14 ∧ (∀ kind ∈ trace, HostPrimaryMemoryKind kind) := by
  let trace : List StepKind :=
    [.instruction (.call 21),.instruction (.localGet 0),.instruction (.load32 0),
      .instruction (.localSet 1),.instruction (.localGet 0),.instruction (.const sentinel),
      .instruction (.store32 0),.instruction (.block 0 0 iteratorBody),
      .instruction (.localGet 1),.instruction (.const sentinel),.instruction .ne,
      .instruction (.br_if 0),.instruction (.localGet 1),.administrative .returnFromCall]
  refine ⟨trace,?_,?_⟩
  rotate_left
  · intro kind member
    simp only [trace,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp only [HostPrimaryMemoryKind,PrimaryMemoryKind]
  apply Steps.with_unit_cost
  · unfold trace
    wasm_steps [(.call (fn := func18Def) (by rw [hmodule];decide) (by rw [hmodule];rfl)),
      (.localGet rfl),(.load32 rfl (by simpa using hphysical))]
    rw [UInt32.add_zero,hread]
    wasm_steps [(.localSet rfl),(.localGet rfl),.const,
      (.store32 rfl (by simpa using hphysical)),.block,(.localGet rfl),.const,
      (.ne (result := 1) (by simp [hsaved])),(.brIf (by decide) rfl),(.localGet rfl)]
    simp only [setMemory_eq,UInt32.add_zero]
    exact Steps.single (.returnFromCallFallthrough rfl)
  · intro before kind after member
    simp only [trace,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

/-- Exhausted source: the actual iterator checks equal cursor/end fields,
returns the sentinel, and leaves every byte except its reset word unchanged. -/
theorem iterator_end_cost (store : MachineStore Universal.State)
    (callerLocals : Locals) (stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value) (controls : List ControlFrame) (calls : List CallFrame)
    (pointer finish : UInt32)
    (hmodule : store.runtime.currentModule=Project.HexStdio.module)
    (hread : store.wasm.mem.read32 pointer=sentinel)
    (hcursor : store.wasm.mem.read32 (pointer+4)=finish)
    (hend : store.wasm.mem.read32 (pointer+8)=finish)
    (hphysical : pointer.toNat+12≤store.wasm.mem.pages*65536)
    (hnowrap : pointer.toNat+12<UInt32.size) :
    ∃ trace, CostedSteps CostedStdIO.work
      ⟨.running ⟨{callerLocals with values := .i32 pointer::stack},
        .call 21::code,arity,remainder,controls,calls⟩,store⟩ trace
      ⟨.running ⟨{callerLocals with values := .i32 sentinel::stack},
        code,arity,remainder,controls,calls⟩,iteratorResetStore store pointer⟩ 23 ∧ (∀ kind ∈ trace, HostPrimaryMemoryKind kind) := by
  have h4 : (pointer+4).toNat=pointer.toNat+4 := by
    rw [UInt32.toNat_add];exact Nat.mod_eq_of_lt (by change pointer.toNat+4<UInt32.size;omega)
  have h8 : (pointer+8).toNat=pointer.toNat+8 := by
    rw [UInt32.toNat_add];exact Nat.mod_eq_of_lt (by change pointer.toNat+8<UInt32.size;omega)
  have hcursor' : (store.wasm.mem.write32 pointer sentinel).read32 (pointer+4)=finish := by
    rw [Mem.read32_write32_disjoint _ _ _ _ (by right;rw [h4]),hcursor]
  have hend' : (store.wasm.mem.write32 pointer sentinel).read32 (pointer+8)=finish := by
    rw [Mem.read32_write32_disjoint _ _ _ _ (by right;rw [h8];omega),hend]
  let trace : List StepKind :=
    [.instruction (.call 21),.instruction (.localGet 0),.instruction (.load32 0),
      .instruction (.localSet 1),.instruction (.localGet 0),.instruction (.const sentinel),
      .instruction (.store32 0),.instruction (.block 0 0 iteratorBody),
      .instruction (.localGet 1),.instruction (.const sentinel),.instruction .ne,
      .instruction (.br_if 0),.instruction (.const sentinel),.instruction (.localSet 1),
      .instruction (.localGet 0),.instruction (.load32 4),.instruction (.localTee 2),
      .instruction (.localGet 0),.instruction (.load32 8),.instruction .eq,
      .instruction (.br_if 0),.instruction (.localGet 1),.administrative .returnFromCall]
  refine ⟨trace,?_,?_⟩
  rotate_left
  · intro kind member
    simp only [trace,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp only [HostPrimaryMemoryKind,PrimaryMemoryKind]
  apply Steps.with_unit_cost
  · unfold trace
    wasm_steps [(.call (fn := func18Def) (by rw [hmodule];decide) (by rw [hmodule];rfl)),
      (.localGet rfl),(.load32 rfl (by change pointer.toNat+0+4≤_;omega))]
    rw [UInt32.add_zero,hread]
    wasm_steps [(.localSet rfl),(.localGet rfl),.const,
      (.store32 rfl (by change pointer.toNat+0+4≤_;omega)),.block,(.localGet rfl),.const,
      (.ne (result := 0) rfl),.brIfZero,.const,(.localSet rfl),(.localGet rfl),
      (.load32 rfl (by change pointer.toNat+4+4≤store.wasm.mem.pages*65536;omega))]
    simp only [setMemory_eq,UInt32.add_zero]
    rw [hcursor']
    wasm_steps [(.localTee rfl),(.localGet rfl),
      (.load32 rfl (by change pointer.toNat+8+4≤store.wasm.mem.pages*65536;omega))]
    rw [hend']
    wasm_steps [(.eq (result := 1) (by simp)),(.brIf (by decide) rfl),(.localGet rfl)]
    exact Steps.single (.returnFromCallFallthrough rfl)
  · intro before kind after member
    simp only [trace,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|
      rfl|rfl|rfl|rfl|rfl <;> rfl

/-- The input-consuming iterator update; all writes are in its two state words. -/
def iteratorHighStore (store : MachineStore Universal.State) (pointer index : UInt32)
    (low : UInt8) : MachineStore Universal.State :=
  {store with wasm := {store.wasm with mem :=
    ((store.wasm.mem.write32 pointer sentinel).write32 (pointer+4) (index+1)).write32 pointer low.toUInt32}}

theorem offset_toNat (pointer : UInt32) (offset : Nat)
    (h : pointer.toNat+offset<UInt32.size) :
    (pointer+UInt32.ofNat offset).toNat=pointer.toNat+offset := by
  have hoff : offset<UInt32.size := by omega
  rw [UInt32.toNat_add,UInt32.toNat_ofNat_of_lt' hoff,Nat.mod_eq_of_lt h]

/-- A remaining input byte is read from the actual evolving store. Its two
lookup bytes are returned/saved; all write addresses precede the ASCII table. -/
theorem iterator_high_cost (store : MachineStore Universal.State)
    (callerLocals : Locals) (stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value) (controls : List ControlFrame) (calls : List CallFrame)
    (pointer index finish : UInt32) (byte low high : UInt8)
    (hmodule : store.runtime.currentModule=Project.HexStdio.module)
    (hread : store.wasm.mem.read32 pointer=sentinel)
    (hcursor : store.wasm.mem.read32 (pointer+4)=index)
    (hend : store.wasm.mem.read32 (pointer+8)=finish)
    (htable : store.wasm.mem.read32 (pointer+12)=1048576)
    (hbyte : store.wasm.mem.read8 index=byte)
    (hlow : store.wasm.mem.read8 (1048576+UInt32.ofNat (byte.toNat%16))=low)
    (hhigh : store.wasm.mem.read8 (1048576+UInt32.ofNat (byte.toNat/16))=high)
    (hne : index≠finish)
    (hframe : pointer.toNat+16≤1048576)
    (hindex : 1048592 ≤ index.toNat)
    (hphysical : index.toNat+1≤store.wasm.mem.pages*65536) :
    ∃ trace, CostedSteps CostedStdIO.work
      ⟨.running ⟨{callerLocals with values := .i32 pointer::stack},
        .call 21::code,arity,remainder,controls,calls⟩,store⟩ trace
      ⟨.running ⟨{callerLocals with values := .i32 high.toUInt32::stack},
        code,arity,remainder,controls,calls⟩,iteratorHighStore store pointer index low⟩ 48 ∧
      (∀ kind ∈ trace,HostPrimaryMemoryKind kind) := by
  have h4 := offset_toNat pointer 4 (by norm_num [UInt32.size];omega)
  have h8 := offset_toNat pointer 8 (by norm_num [UInt32.size];omega)
  have h12 := offset_toNat pointer 12 (by norm_num [UInt32.size];omega)
  change (pointer+4).toNat=pointer.toNat+4 at h4
  change (pointer+8).toNat=pointer.toNat+8 at h8
  change (pointer+12).toNat=pointer.toNat+12 at h12
  have hlowlt : byte.toNat%16<16 := Nat.mod_lt _ (by decide)
  have hhighlt : byte.toNat/16<16 := by have := byte.toNat_lt;omega
  have hloff := offset_toNat 1048576 (byte.toNat%16) (by change 1048576+byte.toNat%16<UInt32.size;norm_num [UInt32.size];omega)
  have hhioff := offset_toNat 1048576 (byte.toNat/16) (by change 1048576+byte.toNat/16<UInt32.size;norm_num [UInt32.size];omega)
  change (1048576+UInt32.ofNat (byte.toNat%16)).toNat=1048576+byte.toNat%16 at hloff
  change (1048576+UInt32.ofNat (byte.toNat/16)).toNat=1048576+byte.toNat/16 at hhioff
  let reset := store.wasm.mem.write32 pointer sentinel
  let advanced := reset.write32 (pointer+4) (index+1)
  have hc : reset.read32 (pointer+4)=index := by
    rw [Mem.read32_write32_disjoint _ _ _ _ (by right;exact h4.ge),hcursor]
  have he : reset.read32 (pointer+8)=finish := by
    rw [Mem.read32_write32_disjoint _ _ _ _ (by right;rw [h8];omega),hend]
  have ht : advanced.read32 (pointer+12)=1048576 := by
    rw [Mem.read32_write32_disjoint _ _ _ _ (by right;rw [h4,h12];omega),
      Mem.read32_write32_disjoint _ _ _ _ (by right;rw [h12];omega),htable]
  have advanced_byte (address : UInt32) (ha : 1048576≤address.toNat) :
      advanced.read8 address=store.wasm.mem.read8 address := by
    simp only [advanced,reset,Mem.read8]
    rw [Mem.write32_bytes_of_disjoint _ _ _ _ (by right;rw [h4];omega),
      Mem.write32_bytes_of_disjoint _ _ _ _ (by right;omega)]
  have hb : advanced.read8 index=byte := (advanced_byte index (by omega)).trans hbyte
  have hl : advanced.read8 (UInt32.ofNat (byte.toNat%16)+1048576)=low := by
    rw [UInt32.add_comm,advanced_byte _ (by rw [hloff];omega),hlow]
  have hh : (advanced.write32 pointer low.toUInt32).read8
      (UInt32.ofNat (byte.toNat/16)+1048576)=high := by
    rw [UInt32.add_comm]
    simp only [Mem.read8]
    rw [Mem.write32_bytes_of_disjoint _ _ _ _ (by right;rw [hhioff];omega)]
    exact (advanced_byte _ (by rw [hhioff];omega)).trans hhigh
  let trace : List StepKind :=
    [.instruction (.call 21),.instruction (.localGet 0),.instruction (.load32 0),
      .instruction (.localSet 1),.instruction (.localGet 0),.instruction (.const sentinel),
      .instruction (.store32 0),.instruction (.block 0 0 iteratorBody),
      .instruction (.localGet 1),.instruction (.const sentinel),.instruction .ne,
      .instruction (.br_if 0),.instruction (.const sentinel),.instruction (.localSet 1),
      .instruction (.localGet 0),.instruction (.load32 4),.instruction (.localTee 2),
      .instruction (.localGet 0),.instruction (.load32 8),.instruction .eq,
      .instruction (.br_if 0),.instruction (.localGet 0),.instruction (.localGet 2),
      .instruction (.const 1),.instruction .add,.instruction (.store32 4),
      .instruction (.localGet 0),.instruction (.localGet 0),.instruction (.load32 12),
      .instruction (.localTee 1),.instruction (.localGet 2),.instruction (.load8U 0),
      .instruction (.localTee 2),.instruction (.const 15),.instruction .and,
      .instruction .add,.instruction (.load8U 0),.instruction (.store32 0),
      .instruction (.localGet 1),.instruction (.localGet 2),.instruction (.const 4),
      .instruction .shrU,.instruction .add,.instruction (.load8U 0),
      .instruction (.localSet 1),.administrative .exitControl,
      .instruction (.localGet 1),.administrative .returnFromCall]
  refine ⟨trace,?_,?_⟩
  · apply Steps.with_unit_cost
    · unfold trace
      wasm_steps [(.call (fn := func18Def) (by rw [hmodule];decide) (by rw [hmodule];rfl)),
        (.localGet rfl),(.load32 rfl (by change pointer.toNat+0+4≤_;omega))]
      rw [UInt32.add_zero,hread]
      wasm_steps [(.localSet rfl),(.localGet rfl),.const,
        (.store32 rfl (by change pointer.toNat+0+4≤_;omega)),.block,(.localGet rfl),.const,
        (.ne (result := 0) rfl),.brIfZero,.const,(.localSet rfl),(.localGet rfl),
        (.load32 rfl (by change pointer.toNat+4+4≤store.wasm.mem.pages*65536;omega))]
      simp only [setMemory_eq,UInt32.add_zero]
      rw [hc]
      wasm_steps [(.localTee rfl),(.localGet rfl),
        (.load32 rfl (by change pointer.toNat+8+4≤store.wasm.mem.pages*65536;omega))]
      rw [he]
      wasm_steps [(.eq (result := 0) (by simp [hne])),.brIfZero,
        (.localGet rfl),(.localGet rfl),.const,.add,
        (.store32 rfl (by change pointer.toNat+4+4≤store.wasm.mem.pages*65536;omega))]
      simp only [setMemory_eq]
      rw [UInt32.add_comm (1:UInt32) index]
      wasm_steps [(.localGet rfl),(.localGet rfl),
        (.load32 rfl (by change pointer.toNat+12+4≤store.wasm.mem.pages*65536;omega))]
      rw [ht]
      wasm_steps [(.localTee rfl),(.localGet rfl),
        (.load8U rfl (by change index.toNat+0+1≤store.wasm.mem.pages*65536;omega))]
      rw [UInt32.add_zero,hb]
      wasm_steps [(.localTee rfl),.const,.and]
      rw [Hex.low_nibble_u32]
      wasm_steps [.add]
      have hlowPhysical : (UInt32.ofNat (byte.toNat%16)+1048576).toNat+0+1≤store.wasm.mem.pages*65536 := by
        rw [UInt32.add_comm,hloff];omega
      wasm_steps [(.load8U rfl (by
        simp only [show (0:UInt32).toNat=0 from rfl]
        exact hlowPhysical))]
      rw [UInt32.add_zero,hl]
      wasm_steps [(.store32 rfl (by change pointer.toNat+0+4≤store.wasm.mem.pages*65536;omega)),
        (.localGet rfl),(.localGet rfl),.const,.shrU]
      rw [show (4:UInt32)%32=4 by decide,Hex.high_nibble_u32]
      wasm_steps [.add]
      simp only [setMemory_eq]
      have hhighPhysical : (UInt32.ofNat (byte.toNat/16)+1048576).toNat+0+1≤store.wasm.mem.pages*65536 := by
        rw [UInt32.add_comm,hhioff];omega
      wasm_steps [(.load8U rfl (by
        simp only [show (0:UInt32).toNat=0 from rfl]
        exact hhighPhysical))]
      simp only [UInt32.add_zero]
      rw [hh]
      wasm_steps [(.localSet rfl),(.exitControl rfl),(.localGet rfl)]
      exact Steps.single (.returnFromCallFallthrough rfl)
    · intro before kind after member
      simp only [trace,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  · intro kind member
    simp only [trace,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp only [HostPrimaryMemoryKind,PrimaryMemoryKind]

def encodeLocals (result position char sp width ascii destination tmp1 tmp2 : UInt32)
    (values : List Value := []) : Locals :=
  ⟨[.i32 result,.i32 position,.i32 char],
    [.i32 sp,.i32 width,.i32 ascii,.i32 destination,.i32 tmp1,.i32 tmp2],values⟩

private def blockBodyAt (code : Program) (index : Nat) : Program :=
  match code[index]? with
  | some (Instruction.block _ _ body _ _) => body
  | _ => []

abbrev loopBody := TotalEncodeLoop.encodeLoopBody
abbrev loopCallTail := TotalEncodeLoop.encodeLoopCallTail

def asciiStore (store : MachineStore Universal.State) (sp output position digit : UInt32) :
    MachineStore Universal.State :=
  {store with wasm := {store.wasm with mem :=
    (store.wasm.mem.write8 (output+position) digit.toUInt8).write32 (sp+12) (position+1)}}

/-- One actual ASCII digit iteration up to its iterator call. Capacity is
checked by the generated branch before the output byte and length are stored. -/
theorem ascii_store_cost (store : MachineStore Universal.State)
    (result position digit sp width ascii destination tmp1 tmp2 capacity output : UInt32)
    (arity : Nat) (remainder : List Value) (controls : List ControlFrame) (calls : List CallFrame)
    (hdigit : digit<128) (hroom : (1:UInt32)≤capacity-position)
    (hcapacity : store.wasm.mem.read32 (sp+4)=capacity)
    (houtput : store.wasm.mem.read32 (sp+8)=output)
    (hstack : sp.toNat+16≤store.wasm.mem.pages*65536)
    (hphysical : (output+position).toNat+1≤store.wasm.mem.pages*65536) :
    ∃ trace, CostedSteps CostedStdIO.work
      ⟨.running ⟨encodeLocals result position digit sp width ascii destination tmp1 tmp2,
        loopBody,arity,remainder,controls,calls⟩,store⟩ trace
      ⟨.running ⟨encodeLocals result (position+1) digit sp 1 1 (output+position) tmp1 tmp2
        [.i32 (sp+16)],loopCallTail,arity,remainder,controls,calls⟩,
        asciiStore store sp output position digit⟩ 43 ∧
      (∀ kind ∈ trace,HostPrimaryMemoryKind kind) := by
  let classify := blockBodyAt loopBody 0
  let classifyInner := blockBodyAt classify 0
  let capacityBlock := blockBodyAt loopBody 3
  let outputBlock := blockBodyAt loopBody 9
  let outputInner := blockBodyAt outputBlock 0
  let trace : List StepKind :=
    [.instruction (.block 0 0 classify),.instruction (.block 0 0 classifyInner),
      .instruction (.localGet 2),.instruction (.const 128),.instruction .ltU,
      .instruction (.localTee 5),.instruction .eqz,.instruction (.br_if 0),
      .instruction (.const 1),.instruction (.localSet 4),.instruction (.br 1),
      .instruction (.localGet 1),.instruction (.localSet 6),.instruction (.block 0 0 capacityBlock),
      .instruction (.localGet 4),.instruction (.localGet 3),.instruction (.load32 4),
      .instruction (.localGet 1),.instruction .sub,.instruction .leU,.instruction (.br_if 0),
      .instruction (.localGet 3),.instruction (.load32 8),.instruction (.localGet 6),
      .instruction .add,.instruction (.localSet 6),.instruction (.block 0 0 outputBlock),
      .instruction (.block 0 0 outputInner),.instruction (.localGet 5),.instruction (.br_if 0),
      .instruction (.localGet 6),.instruction (.localGet 2),.instruction (.store8 0),
      .administrative .exitControl,.instruction (.localGet 3),.instruction (.localGet 4),
      .instruction (.localGet 1),.instruction .add,.instruction (.localTee 1),
      .instruction (.store32 12),.instruction (.localGet 3),.instruction (.const 16),.instruction .add]
  refine ⟨trace,?_,?_⟩
  · apply Steps.with_unit_cost
    · unfold trace
      wasm_steps [.block,.block,(.localGet rfl),.const,(.ltU (result := 1) (by simp [hdigit])),
        (.localTee rfl),(.eqz (result := 0) rfl),.brIfZero,.const,(.localSet rfl),(.br rfl),
        (.localGet rfl),(.localSet rfl),.block,(.localGet rfl),(.localGet rfl),
        (.load32 rfl (by change sp.toNat+4+4≤store.wasm.mem.pages*65536;omega))]
      rw [hcapacity]
      wasm_steps [(.localGet rfl),.sub,(.leU (result := 1) (by simp [hroom])),(.brIf (by decide) rfl),
        (.localGet rfl),(.load32 rfl (by change sp.toNat+8+4≤store.wasm.mem.pages*65536;omega))]
      rw [houtput]
      wasm_steps [(.localGet rfl),.add,(.localSet rfl),.block,.block,(.localGet rfl),
        (.brIf (by decide) rfl),(.localGet rfl),(.localGet rfl)]
      rw [UInt32.add_comm position output]
      wasm_steps [(.store8 rfl (by simpa using hphysical)),(.exitControl rfl),
        (.localGet rfl),(.localGet rfl),(.localGet rfl),.add,(.localTee rfl),
        (.store32 rfl (by change sp.toNat+12+4≤store.wasm.mem.pages*65536;omega)),
        (.localGet rfl),.const]
      apply Steps.cons Step.add
      simp only [setMemory_eq,UInt32.add_zero,UInt32.add_comm (16:UInt32) sp]
      exact Steps.refl _
    · intro before kind after member
      simp only [trace,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  · intro kind member
    simp only [trace,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp only [HostPrimaryMemoryKind,PrimaryMemoryKind]

theorem continue_cost (store : MachineStore Universal.State)
    (result position oldDigit digit width ascii destination tmp1 tmp2 : UInt32)
    (arity : Nat) (remainder : List Value) (afterLoop : Program)
    (controls : List ControlFrame) (calls : List CallFrame) (hne : digit≠sentinel) :
    ∃ trace, CostedSteps CostedStdIO.work
      ⟨.running ⟨encodeLocals result position oldDigit 1048512 width ascii destination tmp1 tmp2 [.i32 digit],
        loopCallTail.drop 1,arity,remainder,TotalEncodeLoop.encodeLoopFrame afterLoop::controls,calls⟩,store⟩ trace
      ⟨.running ⟨encodeLocals result position digit 1048512 width ascii destination tmp1 tmp2,
        loopBody,arity,remainder,TotalEncodeLoop.encodeLoopFrame afterLoop::controls,calls⟩,store⟩ 4 ∧
      (∀ kind ∈ trace,HostPrimaryMemoryKind kind) := by
  let trace : List StepKind := [.instruction (.localTee 2),.instruction (.const sentinel),
    .instruction .ne,.instruction (.br_if 0)]
  refine ⟨trace,?_,?_⟩
  · apply Steps.with_unit_cost
    · unfold trace
      wasm_steps [(.localTee rfl),.const,(.ne (result := 1) (by simp [hne]))]
      exact Steps.single (.brIf (by decide) rfl)
    · intro before kind after member
      simp only [trace,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl|rfl|rfl <;> rfl
  · intro kind member
    simp only [trace,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl <;> simp only [HostPrimaryMemoryKind,PrimaryMemoryKind]

theorem exit_cost (store : MachineStore Universal.State)
    (result position oldDigit width ascii destination tmp1 tmp2 : UInt32)
    (arity : Nat) (remainder : List Value) (afterLoop : Program)
    (controls : List ControlFrame) (calls : List CallFrame) :
    ∃ trace, CostedSteps CostedStdIO.work
      ⟨.running ⟨encodeLocals result position oldDigit 1048512 width ascii destination tmp1 tmp2 [.i32 sentinel],
        loopCallTail.drop 1,arity,remainder,TotalEncodeLoop.encodeLoopFrame afterLoop::controls,calls⟩,store⟩ trace
      ⟨.running ⟨encodeLocals result position sentinel 1048512 width ascii destination tmp1 tmp2,
        afterLoop,arity,remainder,controls,calls⟩,store⟩ 5 ∧
      (∀ kind ∈ trace,HostPrimaryMemoryKind kind) := by
  let trace : List StepKind := [.instruction (.localTee 2),.instruction (.const sentinel),
    .instruction .ne,.instruction (.br_if 0),.administrative .exitControl]
  refine ⟨trace,?_,?_⟩
  · apply Steps.with_unit_cost
    · unfold trace
      wasm_steps [(.localTee rfl),.const,(.ne (result := 0) rfl),.brIfZero]
      exact Steps.single (.exitControl rfl)
    · intro before kind after member
      simp only [trace,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl|rfl|rfl|rfl <;> rfl
  · intro kind member
    simp only [trace,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl <;> simp only [HostPrimaryMemoryKind,PrimaryMemoryKind]

/-- Concrete vector and iterator words in the canonical encoder frame. -/
structure Fields (memory : Mem) (capacity output position saved cursor finish : UInt32) : Prop where
  capacity : memory.read32 1048516=capacity
  output : memory.read32 1048520=output
  position : memory.read32 1048524=position
  saved : memory.read32 1048528=saved
  cursor : memory.read32 1048532=cursor
  finish : memory.read32 1048536=finish
  table : memory.read32 1048540=1048576

/-- Every actual lookup-table byte takes the generated ASCII arm. -/
def AsciiTable (memory : Mem) : Prop :=
  ∀ i, i<16 → (memory.read8 (1048576+UInt32.ofNat i)).toUInt32<128

private theorem read32_write8_before (memory : Mem) (address readAddress : UInt32) (value : UInt8)
    (h : readAddress.toNat+4≤address.toNat) :
    (memory.write8 address value).read32 readAddress=memory.read32 readAddress := by
  simp only [Mem.read32,Mem.write8,
    show readAddress.toNat≠address.toNat by omega,
    show readAddress.toNat+1≠address.toNat by omega,
    show readAddress.toNat+2≠address.toNat by omega,
    show readAddress.toNat+3≠address.toNat by omega,↓reduceIte]

theorem ascii_fields (store : MachineStore Universal.State)
    (capacity output position saved cursor finish digit : UInt32)
    (fields : Fields store.wasm.mem capacity output position saved cursor finish)
    (hphysical : 1048592 ≤ (output+position).toNat) :
    Fields (asciiStore store 1048512 output position digit).wasm.mem
      capacity output (position+1) saved cursor finish := by
  constructor
  all_goals simp only [asciiStore]
  · rw [Mem.read32_write32_disjoint _ _ _ _ (by decide),read32_write8_before _ _ _ _ (by change 1048516+4≤_;omega)]
    exact fields.capacity
  · rw [Mem.read32_write32_disjoint _ _ _ _ (by decide),read32_write8_before _ _ _ _ (by change 1048520+4≤_;omega)]
    exact fields.output
  · exact Mem.read32_write32_same _ _ _
  · rw [Mem.read32_write32_disjoint _ _ _ _ (by decide),read32_write8_before _ _ _ _ (by change 1048528+4≤_;omega)]
    exact fields.saved
  · rw [Mem.read32_write32_disjoint _ _ _ _ (by decide),read32_write8_before _ _ _ _ (by change 1048532+4≤_;omega)]
    exact fields.cursor
  · rw [Mem.read32_write32_disjoint _ _ _ _ (by decide),read32_write8_before _ _ _ _ (by change 1048536+4≤_;omega)]
    exact fields.finish
  · rw [Mem.read32_write32_disjoint _ _ _ _ (by decide),read32_write8_before _ _ _ _ (by change 1048540+4≤_;omega)]
    exact fields.table

theorem low_fields (store : MachineStore Universal.State)
    (capacity output position saved cursor finish : UInt32)
    (fields : Fields store.wasm.mem capacity output position saved cursor finish) :
    Fields (iteratorResetStore store 1048528).wasm.mem
      capacity output position sentinel cursor finish := by
  constructor
  all_goals simp only [iteratorResetStore]
  · rw [Mem.read32_write32_disjoint _ _ _ _ (by decide)];exact fields.capacity
  · rw [Mem.read32_write32_disjoint _ _ _ _ (by decide)];exact fields.output
  · rw [Mem.read32_write32_disjoint _ _ _ _ (by decide)];exact fields.position
  · exact Mem.read32_write32_same _ _ _
  · rw [Mem.read32_write32_disjoint _ _ _ _ (by decide)];exact fields.cursor
  · rw [Mem.read32_write32_disjoint _ _ _ _ (by decide)];exact fields.finish
  · rw [Mem.read32_write32_disjoint _ _ _ _ (by decide)];exact fields.table

theorem high_fields (store : MachineStore Universal.State)
    (capacity output position saved cursor finish : UInt32) (low : UInt8)
    (fields : Fields store.wasm.mem capacity output position saved cursor finish) :
    Fields (iteratorHighStore store 1048528 cursor low).wasm.mem
      capacity output position low.toUInt32 (cursor+1) finish := by
  constructor
  all_goals simp only [iteratorHighStore]
  · rw [Mem.read32_write32_disjoint _ _ _ _ (by decide),Mem.read32_write32_disjoint _ _ _ _ (by decide),
      Mem.read32_write32_disjoint _ _ _ _ (by decide)];exact fields.capacity
  · rw [Mem.read32_write32_disjoint _ _ _ _ (by decide),Mem.read32_write32_disjoint _ _ _ _ (by decide),
      Mem.read32_write32_disjoint _ _ _ _ (by decide)];exact fields.output
  · rw [Mem.read32_write32_disjoint _ _ _ _ (by decide),Mem.read32_write32_disjoint _ _ _ _ (by decide),
      Mem.read32_write32_disjoint _ _ _ _ (by decide)];exact fields.position
  · exact Mem.read32_write32_same _ _ _
  · rw [Mem.read32_write32_disjoint _ _ _ _ (by decide)];exact Mem.read32_write32_same _ _ _
  · rw [Mem.read32_write32_disjoint _ _ _ _ (by decide),Mem.read32_write32_disjoint _ _ _ _ (by decide),
      Mem.read32_write32_disjoint _ _ _ _ (by decide)];exact fields.finish
  · rw [Mem.read32_write32_disjoint _ _ _ _ (by decide),Mem.read32_write32_disjoint _ _ _ _ (by decide),
      Mem.read32_write32_disjoint _ _ _ _ (by decide)];exact fields.table

/-- Memory outside the encoder frame and below its output allocation is framed. -/
def Framed (before after : Mem) (output : UInt32) : Prop :=
  after.pages=before.pages ∧ ∀ address,
    (address<1048516 ∨ 1048544≤address) → address<output.toNat → after.bytes address=before.bytes address

theorem Framed.refl (memory : Mem) (output : UInt32) : Framed memory memory output := ⟨rfl,by intros;rfl⟩

theorem Framed.trans {first second third : Mem} {output : UInt32}
    (left : Framed first second output) (right : Framed second third output) : Framed first third output := by
  refine ⟨right.1.trans left.1,?_⟩
  intro address outside beforeOutput
  rw [right.2 address outside beforeOutput,left.2 address outside beforeOutput]

theorem Framed.ascii {before after : Mem} {output : UInt32}
    (frame : Framed before after output) (htable : AsciiTable before)
    (houtput : 1048592 ≤ output.toNat) : AsciiTable after := by
  intro i hi
  have hoff := offset_toNat 1048576 i (by change 1048576+i<UInt32.size;norm_num [UInt32.size];omega)
  change (1048576+UInt32.ofNat i).toNat=1048576+i at hoff
  simp only [Mem.read8]
  rw [frame.2 _ (by right;rw [hoff];omega) (by rw [hoff];omega)]
  exact htable i hi

theorem ascii_framed (store : MachineStore Universal.State) (output position digit : UInt32)
    (haddr : output.toNat ≤ (output+position).toNat) :
    Framed store.wasm.mem (asciiStore store 1048512 output position digit).wasm.mem output := by
  refine ⟨rfl,?_⟩
  intro address outside beforeOutput
  simp only [asciiStore]
  rw [Mem.write32_bytes_of_disjoint _ _ _ _ (by change address<1048524 ∨ 1048524+4≤address;omega)]
  simp only [Mem.write8,show address≠(output+position).toNat by omega,↓reduceIte]

theorem low_framed (store : MachineStore Universal.State) (output : UInt32) :
    Framed store.wasm.mem (iteratorResetStore store 1048528).wasm.mem output := by
  refine ⟨rfl,?_⟩
  intro address outside beforeOutput
  exact Mem.write32_bytes_of_disjoint _ _ _ _ (by change address<1048528 ∨ 1048528+4≤address;omega)

theorem high_framed (store : MachineStore Universal.State) (output cursor : UInt32) (low : UInt8) :
    Framed store.wasm.mem (iteratorHighStore store 1048528 cursor low).wasm.mem output := by
  refine ⟨rfl,?_⟩
  intro address outside beforeOutput
  simp only [iteratorHighStore]
  rw [Mem.write32_bytes_of_disjoint _ _ _ _ (by change address<1048528 ∨ 1048528+4≤address;omega),
    Mem.write32_bytes_of_disjoint _ _ _ _ (by change address<1048532 ∨ 1048532+4≤address;omega),
    Mem.write32_bytes_of_disjoint _ _ _ _ (by change address<1048528 ∨ 1048528+4≤address;omega)]

structure Context where
  result : UInt32 := 1048564
  tmp1 : UInt32 := 0
  tmp2 : UInt32 := 0
  arity : Nat := 0
  remainder : List Value := []
  afterLoop : Program := []
  controls : List ControlFrame := []
  calls : List CallFrame := []

def headConfig (ctx : Context) (store : MachineStore Universal.State)
    (position digit width ascii destination : UInt32) : Config Universal.State :=
  ⟨.running ⟨encodeLocals ctx.result position digit 1048512 width ascii destination ctx.tmp1 ctx.tmp2,
    loopBody,ctx.arity,ctx.remainder,TotalEncodeLoop.encodeLoopFrame ctx.afterLoop::ctx.controls,ctx.calls⟩,store⟩

def tailConfig (ctx : Context) (store : MachineStore Universal.State)
    (position digit destination : UInt32) : Config Universal.State :=
  ⟨.running ⟨encodeLocals ctx.result position digit 1048512 1 1 destination ctx.tmp1 ctx.tmp2 [.i32 1048528],
    loopCallTail,ctx.arity,ctx.remainder,TotalEncodeLoop.encodeLoopFrame ctx.afterLoop::ctx.controls,ctx.calls⟩,store⟩

def pairStore (store : MachineStore Universal.State) (output position high low : UInt32) :
    MachineStore Universal.State :=
  asciiStore (iteratorResetStore (asciiStore store 1048512 output position high) 1048528)
    1048512 output (position+1) low

theorem ascii_ne_sentinel {digit : UInt32} (ascii : digit<128) : digit≠sentinel := by
  intro equality
  subst digit
  exact (by decide : ¬(sentinel:UInt32)<128) ascii

theorem natural_room (p : Nat) (capacity : UInt32) (h : p<capacity.toNat) :
    (1:UInt32)≤capacity-UInt32.ofNat p := by
  have hp : p<UInt32.size := lt_trans h capacity.toNat_lt
  have hle : UInt32.ofNat p≤capacity := by
    apply UInt32.le_iff_toNat_le_toNat.mpr
    rw [UInt32.toNat_ofNat_of_lt' hp];omega
  apply UInt32.le_iff_toNat_le_toNat.mpr
  rw [UInt32.toNat_sub_of_le capacity (UInt32.ofNat p) hle,UInt32.toNat_ofNat_of_lt' hp]
  change 1≤capacity.toNat-p
  omega

theorem natural_succ (p : Nat) (_h : p+1<UInt32.size) :
    UInt32.ofNat p+1=UInt32.ofNat (p+1) := by
  rw [show (1:UInt32)=UInt32.ofNat 1 from rfl,UInt32.ofNat_add]

/-- A high/low digit pair executes both generated stores and the saved-digit
iterator branch. The endpoint is the next actual iterator call. -/
theorem byte_pair_cost (ctx : Context) (store : MachineStore Universal.State)
    (p : Nat) (capacity output cursor finish high low width ascii destination : UInt32)
    (hmodule : store.runtime.currentModule=Project.HexStdio.module)
    (fields : Fields store.wasm.mem capacity output (UInt32.ofNat p) low cursor finish)
    (hhigh : high<128) (hlow : low<128)
    (hcapacity : p+2≤capacity.toNat)
    (houtput : 1048592 ≤ output.toNat)
    (hphysical : output.toNat+(p+2)≤store.wasm.mem.pages*65536)
    (hnowrap : output.toNat+(p+2)<UInt32.size) :
    ∃ trace, CostedSteps CostedStdIO.work
      (headConfig ctx store (UInt32.ofNat p) high width ascii destination) trace
      (tailConfig ctx (pairStore store output (UInt32.ofNat p) high low)
        (UInt32.ofNat (p+2)) low (output+UInt32.ofNat (p+1))) 104 ∧
      (∀ kind ∈ trace,HostPrimaryMemoryKind kind) ∧
      Fields (pairStore store output (UInt32.ofNat p) high low).wasm.mem
        capacity output (UInt32.ofNat (p+2)) sentinel cursor finish ∧
      Framed store.wasm.mem (pairStore store output (UInt32.ofNat p) high low).wasm.mem output := by
  have hp : p+2<UInt32.size := by omega
  have hsucc := natural_succ p (by omega)
  have hsucc2 := natural_succ (p+1) (by omega)
  have ha := offset_toNat output p (by omega)
  have hb := offset_toNat output (p+1) (by omega)
  let first := asciiStore store 1048512 output (UInt32.ofNat p) high
  let middle := iteratorResetStore first 1048528
  have hstack : (1048512:UInt32).toNat+16≤store.wasm.mem.pages*65536 := by change 1048512+16≤_;omega
  obtain ⟨a,asteps,aprimary⟩ := ascii_store_cost store ctx.result (UInt32.ofNat p) high 1048512
    width ascii destination ctx.tmp1 ctx.tmp2 capacity output ctx.arity ctx.remainder
    (TotalEncodeLoop.encodeLoopFrame ctx.afterLoop::ctx.controls) ctx.calls hhigh
    (natural_room p capacity (by omega)) fields.capacity fields.output hstack
    (by rw [ha];omega)
  have firstFields := ascii_fields store capacity output (UInt32.ofNat p) low cursor finish high fields
    (by rw [ha];omega)
  obtain ⟨b,bsteps,bprimary⟩ := iterator_low_cost first
    (encodeLocals ctx.result (UInt32.ofNat p+1) high 1048512 1 1 (output+UInt32.ofNat p) ctx.tmp1 ctx.tmp2)
    [] (loopCallTail.drop 1) ctx.arity ctx.remainder
    (TotalEncodeLoop.encodeLoopFrame ctx.afterLoop::ctx.controls) ctx.calls 1048528 low hmodule
    firstFields.saved (ascii_ne_sentinel hlow) (by change 1048528+4≤store.wasm.mem.pages*65536;omega)
  obtain ⟨c,csteps,cprimary⟩ := continue_cost middle ctx.result (UInt32.ofNat p+1) high low
    1 1 (output+UInt32.ofNat p) ctx.tmp1 ctx.tmp2 ctx.arity ctx.remainder ctx.afterLoop ctx.controls ctx.calls
    (ascii_ne_sentinel hlow)
  have middleFields := low_fields first capacity output (UInt32.ofNat p+1) low cursor finish firstFields
  rw [hsucc] at middleFields
  obtain ⟨d,dsteps,dprimary⟩ := ascii_store_cost middle ctx.result (UInt32.ofNat (p+1)) low 1048512
    1 1 (output+UInt32.ofNat p) ctx.tmp1 ctx.tmp2 capacity output ctx.arity ctx.remainder
    (TotalEncodeLoop.encodeLoopFrame ctx.afterLoop::ctx.controls) ctx.calls hlow
    (natural_room (p+1) capacity (by omega)) middleFields.capacity middleFields.output hstack
    (by change (output+UInt32.ofNat (p+1)).toNat+1≤store.wasm.mem.pages*65536;rw [hb];omega)
  rw [hsucc] at asteps bsteps csteps
  have full := ((asteps.trans bsteps).trans csteps).trans dsteps
  refine ⟨((a++b)++c)++d,?_,?_,?_,?_⟩
  · simpa only [headConfig,tailConfig,pairStore,first,middle,hsucc,hsucc2,Nat.add_assoc,
      show (1048512:UInt32)+16=1048528 from rfl,show (1:Nat)+1=2 from rfl,
      show (43:Nat)+(14+(4+43))=104 from rfl] using full
  · intro kind member
    simp only [List.mem_append] at member
    rcases member with ((member|member)|member)|member
    · exact aprimary kind member
    · exact bprimary kind member
    · exact cprimary kind member
    · exact dprimary kind member
  · have result := ascii_fields middle capacity output (UInt32.ofNat (p+1)) sentinel cursor finish low
      middleFields (by rw [hb];omega)
    simpa only [pairStore,hsucc,hsucc2,Nat.add_assoc] using result
  · have f1 := ascii_framed store output (UInt32.ofNat p) high (by rw [ha];omega)
    have f2 := low_framed first output
    have f3 := ascii_framed middle output (UInt32.ofNat (p+1)) low (by rw [hb];omega)
    simpa only [pairStore,hsucc] using (f1.trans f2).trans f3

def finishStore (store : MachineStore Universal.State) (result sp length : UInt32)
    (pair : UInt64) : MachineStore Universal.State :=
  {store with wasm := {store.wasm with
    mem := (store.wasm.mem.write32 (result+8) length).write64 result pair
    globals := {globals := store.wasm.globals.globals.set 0 (.i32 (sp+32))}}}

/-- Publish the actual length and capacity/pointer pair, then restore the
encoder stack frame. The source and caller state are carried unchanged. -/
theorem finish_body_cost (store : MachineStore Universal.State)
    (result position char sp width ascii destination tmp1 tmp2 length : UInt32)
    (pair : UInt64) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (hglobal : (globalAt? store 0).isSome=true)
    (hlength : store.wasm.mem.read32 (sp+12)=length)
    (hpair : store.wasm.mem.read64 (sp+4)=pair)
    (hstack : sp.toNat+16≤store.wasm.mem.pages*65536)
    (hresult : result.toNat+12≤store.wasm.mem.pages*65536)
    (hdisjoint : (result+8).toNat+4≤(sp+4).toNat ∨ (sp+4).toNat+8≤(result+8).toNat) :
    ∃ trace, CostedSteps CostedStdIO.work
      ⟨.running ⟨encodeLocals result position char sp width ascii destination tmp1 tmp2,
        TotalEncodeFunction.func6FinishCode,arity,remainder,controls,calls⟩,store⟩ trace
      ⟨.running ⟨encodeLocals result position char sp width ascii destination tmp1 tmp2,
        [],arity,remainder,controls,calls⟩,finishStore store result sp length pair⟩ 12 ∧
      (∀ kind ∈ trace,HostPrimaryMemoryKind kind) := by
  have hpair' : (store.wasm.mem.write32 (result+8) length).read64 (sp+4)=pair := by
    rw [Mem.read64_write32_disjoint _ _ _ _ hdisjoint,hpair]
  let trace : List StepKind :=
    [.instruction (.localGet 0),.instruction (.localGet 3),.instruction (.load32 12),
      .instruction (.store32 8),.instruction (.localGet 0),.instruction (.localGet 3),
      .instruction (.load64 4),.instruction (.store64 0),.instruction (.localGet 3),
      .instruction (.const 32),.instruction .add,.instruction (.globalSet 0)]
  refine ⟨trace,?_,?_⟩
  · apply Steps.with_unit_cost
    · unfold trace
      wasm_steps [(.localGet rfl),(.localGet rfl),(.load32 rfl (by change sp.toNat+12+4≤store.wasm.mem.pages*65536;omega))]
      rw [hlength]
      wasm_steps [(.store32 rfl (by change result.toNat+8+4≤store.wasm.mem.pages*65536;omega)),(.localGet rfl),(.localGet rfl),
        (.load64 rfl (by change sp.toNat+4+8≤store.wasm.mem.pages*65536;omega))]
      simp only [setMemory_eq]
      rw [hpair']
      wasm_steps [(.store64 rfl (by change result.toNat+0+8≤store.wasm.mem.pages*65536;omega)),
        (.localGet rfl),.const,.add]
      rw [UInt32.add_comm (32:UInt32) sp]
      simp only [setMemory_eq,UInt32.add_zero]
      exact Steps.single (.globalSet (by exact hglobal))
    · intro before kind after member
      simp only [trace,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  · intro kind member
    simp only [trace,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp only [HostPrimaryMemoryKind,PrimaryMemoryKind]

end Project.HexEncodeStdio.EncodeResourceCost
