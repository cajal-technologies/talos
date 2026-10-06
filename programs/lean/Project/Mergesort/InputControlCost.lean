import Project.Mergesort.InputCost

/-! # Actual control and append costs of the generated input loop -/

namespace Project.Mergesort.InputControlCost

open Wasm Wasm.SmallStep Wasm.SmallStep.CostedStdIO
open Project.Mergesort.DriverProof Project.Mergesort.Representations

structure Context where
  stack : List Value := []
  afterLoop : Program := []
  arity : Nat := 0
  remainder : List Value := []
  controls : List ControlFrame := []
  calls : List CallFrame := []

def phaseFrame (ctx : Context) : ControlFrame :=
  { func3ReadPhaseFrame ctx.afterLoop with belowStack := ctx.stack }

def innerFrame (ctx : Context) : ControlFrame :=
  { func3ReadInnerFrame with belowStack := ctx.stack }

def loopFrame (ctx : Context) : ControlFrame :=
  { kind := .loop, paramArity := 0, resultArity := 0, body := func3ReadLoopBody,
    continuation := [], belowStack := ctx.stack }

def loopControls (ctx : Context) : List ControlFrame :=
  loopFrame ctx :: innerFrame ctx :: phaseFrame ctx :: ctx.controls

def head (store : MachineStore Universal.State) (locals : Locals) (ctx : Context) :
    Config Universal.State :=
  ⟨.running ⟨{ locals with values := ctx.stack }, func3ReadLoopBody,
    ctx.arity, ctx.remainder, loopControls ctx, ctx.calls⟩, store⟩

def afterClassify (store : MachineStore Universal.State) (locals : Locals)
    (flag : UInt32) (ctx : Context) : Config Universal.State :=
  ⟨.running ⟨{ locals with values := .i32 flag :: ctx.stack }, [.br_if 2, .br 0],
    ctx.arity, ctx.remainder, loopControls ctx, ctx.calls⟩, store⟩

/-- Enter both generated blocks and the actual loop instruction. -/
theorem phase_entry_cost (store : MachineStore Universal.State) (locals : Locals) (ctx : Context) :
    CostedSteps work
      ⟨.running ⟨{ locals with values := ctx.stack },
        .block 0 0 func3ReadPhaseBody :: ctx.afterLoop,
        ctx.arity, ctx.remainder, ctx.controls, ctx.calls⟩, store⟩
      [.instruction (.block 0 0 func3ReadPhaseBody),
        .instruction (.block 0 0 func3ReadLoopBlockBody), .instruction (.loop 0 0 func3ReadLoopBody)]
      (head store locals ctx) 3 := by
  apply Steps.with_unit_cost
  · wasm_steps [.block, .block]
    exact Steps.single Step.loop
  · intro before kind after member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> rfl

/-- EOF leaves the loop and both enclosing blocks in the actual branch step. -/
theorem eof_exit_cost (store : MachineStore Universal.State) (locals : Locals) (ctx : Context) :
    CostedSteps work (afterClassify store locals 1 ctx) [.instruction (.br_if 2)]
      ⟨.running ⟨{ locals with values := ctx.stack }, ctx.afterLoop,
        ctx.arity, ctx.remainder, ctx.controls, ctx.calls⟩, store⟩ 1 :=
  CostedSteps.single (Step.brIf (by decide) rfl)

/-- A nonempty read takes the zero branch test and real loop back-edge. -/
theorem continue_cost (store : MachineStore Universal.State) (locals : Locals) (ctx : Context) :
    CostedSteps work (afterClassify store locals 0 ctx)
      [.instruction (.br_if 2), .instruction (.br 0)] (head store locals ctx) 2 := by
  apply Steps.with_unit_cost
  · apply Steps.cons Step.brIfZero
    exact Steps.single (Step.br rfl)
  · intro before kind after member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rfl

/-- The actual oversized-read guard accepts each possible host chunk count. -/
theorem count_guard_cost (store : MachineStore Universal.State) (locals : Locals)
    (count : Nat) (hcount : count ≤ 256)
    (hlocal : locals.get 3 = some (.i32 (UInt32.ofNat count)))
    (stack : List Value) (code : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame) :
    CostedSteps work
      ⟨.running ⟨{ locals with values := stack },
        [.localGet 3, .const 257, .geU, .br_if 1] ++ code,
        arity, remainder, controls, calls⟩, store⟩
      [.instruction (.localGet 3), .instruction (.const 257), .instruction .geU,
        .instruction (.br_if 1)]
      ⟨.running ⟨{ locals with values := stack }, code,
        arity, remainder, controls, calls⟩, store⟩ 4 := by
  have hword : UInt32.ofNat count < 257 := by
    rw [UInt32.lt_iff_toNat_lt, UInt32.toNat_ofNat_of_lt' (by norm_num [UInt32.size]; omega)]
    change count < 257
    omega
  apply Steps.with_unit_cost
  · wasm_steps [(.localGet (by exact hlocal)), .const,
      (.geU (result := 0) (by simp [UInt32.not_le.mpr hword]))]
    exact Steps.single Step.brIfZero
  · intro before kind after member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> rfl

/-- Enough capacity takes the generated block branch, preserving the whole store. -/
theorem capacity_fits_cost (store : MachineStore Universal.State) (locals : Locals)
    (current length capacity : UInt32)
    (hlocal0 : locals.get 0 = some (.i32 driverBase))
    (hlocal3 : locals.get 3 = some (.i32 current))
    (hlocal6 : locals.get 6 = some (.i32 length))
    (hcapacity : store.wasm.mem.read32 driverBase = capacity)
    (hbound : driverBase.toNat + 4 ≤ store.wasm.mem.pages * 65536)
    (hfits : current ≤ capacity - length)
    (stack : List Value) (code : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame) :
    CostedSteps work
      ⟨.running ⟨{ locals with values := stack }, .block 0 0 func3CapacityBody :: code,
        arity, remainder, controls, calls⟩, store⟩
      [.instruction (.block 0 0 func3CapacityBody), .instruction (.localGet 3),
        .instruction (.localGet 0), .instruction (.load32 0), .instruction (.localGet 6),
        .instruction .sub, .instruction .leU, .instruction (.br_if 0)]
      ⟨.running ⟨{ locals with values := stack }, code,
        arity, remainder, controls, calls⟩, store⟩ 8 := by
  apply Steps.with_unit_cost
  · wasm_steps [.block, (.localGet (by exact hlocal3)), (.localGet (by exact hlocal0)),
      (.load32 rfl (by simpa using hbound))]
    rw [UInt32.add_zero, hcapacity]
    wasm_steps [(.localGet (by exact hlocal6)), .sub, (.leU (result := 1) (by simp [hfits]))]
    exact Steps.single (Step.brIf (by decide) rfl)
  · intro before kind after member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private def appendCopyBody : Program :=
  [.localGet 3, .eqz, .br_if 0,
    .localGet 1, .localGet 6, .add,
    .localGet 0, .const 12, .add,
    .localGet 3, .memoryCopy]

private def appendCommitBody : Program :=
  [.localGet 0, .localGet 6, .localGet 3, .add, .localTee 6, .store32 8]

def appendedStore (store : MachineStore Universal.State) (dataPtr : UInt32) (length current : Nat) :
    MachineStore Universal.State :=
  { store with wasm := { store.wasm with mem :=
      ((store.wasm.mem.copy ((dataPtr + UInt32.ofNat length).toNat) ((driverBase + 12).toNat) current).write32
        (driverBase + 8) (UInt32.ofNat (length + current))) } }

/-- The actual nonempty append: block entry, byte-sensitive memory copy,
block exit, updated count local and physical Vec-length commit. -/
theorem append_cost (store : MachineStore Universal.State) (dataPtr : UInt32)
    (length current : Nat) (aux2 aux4 aux5 aux7 aux8 aux9 aux10 : UInt32)
    (stack : List Value) (code : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (hpositive : 0 < current) (hcurrent : current < UInt32.size)
    (hdestination : (dataPtr + UInt32.ofNat length).toNat + current ≤ store.wasm.mem.pages * 65536)
    (hchunk : (driverBase + 12).toNat + current ≤ store.wasm.mem.pages * 65536)
    (hheader : (driverBase + 8).toNat + 4 ≤ store.wasm.mem.pages * 65536) :
    ∃ trace, trace.length = 19 ∧
      CostedSteps work
        ⟨.running ⟨func3AppendLocals dataPtr (UInt32.ofNat current) (UInt32.ofNat length)
          aux2 aux4 aux5 aux7 aux8 aux9 aux10 stack,
          func3AppendBody ++ code, arity, remainder, controls, calls⟩, store⟩ trace
        ⟨.running ⟨func3AppendLocals dataPtr (UInt32.ofNat current) (UInt32.ofNat (length + current))
          aux2 aux4 aux5 aux7 aux8 aux9 aux10 stack,
          code, arity, remainder, controls, calls⟩, appendedStore store dataPtr length current⟩
        (19 + current) := by
  let L := func3AppendLocals dataPtr (UInt32.ofNat current) (UInt32.ofNat length)
    aux2 aux4 aux5 aux7 aux8 aux9 aux10 []
  let frame : ControlFrame :=
    { kind := .block, paramArity := 0, resultArity := 0, body := appendCopyBody,
      continuation := appendCommitBody ++ code, belowStack := stack }
  let copied : MachineStore Universal.State :=
    { store with wasm := { store.wasm with mem :=
        (store.wasm.mem.copy ((dataPtr + UInt32.ofNat length).toNat) ((driverBase + 12).toNat) current) } }
  have hcountNat : (UInt32.ofNat current).toNat = current := UInt32.toNat_ofNat_of_lt' hcurrent
  have hnonzero : UInt32.ofNat current ≠ 0 := by
    intro h
    have hz := congrArg UInt32.toNat h
    rw [hcountNat] at hz
    change current = 0 at hz
    omega
  have scalarRun : Steps
      ⟨.running ⟨{ L with values := stack }, func3AppendBody ++ code,
        arity, remainder, controls, calls⟩, store⟩
      [.instruction (.block 0 0 appendCopyBody), .instruction (.localGet 3),
        .instruction .eqz, .instruction (.br_if 0), .instruction (.localGet 1),
        .instruction (.localGet 6), .instruction .add, .instruction (.localGet 0),
        .instruction (.const 12), .instruction .add, .instruction (.localGet 3)]
      ⟨.running ⟨{ L with values := [.i32 (UInt32.ofNat current), .i32 (driverBase + 12),
          .i32 (dataPtr + UInt32.ofNat length)] ++ stack },
        [.memoryCopy], arity, remainder, frame :: controls, calls⟩, store⟩ := by
    wasm_steps [.block, (.localGet rfl), (.eqz (result := 0) (by simp [hnonzero])),
      .brIfZero, (.localGet rfl), (.localGet rfl), .add,
      (.localGet rfl), .const, .add]
    rw [show (12 : UInt32) + driverBase = driverBase + 12 by decide,
      UInt32.add_comm (UInt32.ofNat length) dataPtr]
    exact Steps.single (.localGet rfl)
  have scalarCost := scalarRun.with_unit_cost (charge := work) (by
    intro before kind after member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
  have copyCost := memoryCopy32_costed store L.params L.locals stack [] arity remainder
    (frame :: controls) calls (dataPtr + UInt32.ofNat length) (driverBase + 12)
    (UInt32.ofNat current) (by simpa only [hcountNat] using hdestination)
    (by simpa only [hcountNat] using hchunk) hostBytes
  simp only [hcountNat] at copyCost
  have commit : Steps
      ⟨.running ⟨{ L with values := stack }, [], arity, remainder, frame :: controls, calls⟩, copied⟩
      [.administrative .exitControl, .instruction (.localGet 0), .instruction (.localGet 6),
        .instruction (.localGet 3), .instruction .add, .instruction (.localTee 6),
        .instruction (.store32 8)]
      ⟨.running ⟨func3AppendLocals dataPtr (UInt32.ofNat current) (UInt32.ofNat (length + current))
          aux2 aux4 aux5 aux7 aux8 aux9 aux10 stack,
        code, arity, remainder, controls, calls⟩, appendedStore store dataPtr length current⟩ := by
    wasm_steps [(.exitControl rfl), (.localGet rfl), (.localGet rfl), (.localGet rfl), .add]
    rw [UInt32.add_comm (UInt32.ofNat current) (UInt32.ofNat length), ← UInt32.ofNat_add]
    wasm_steps [(.localTee rfl)]
    exact Steps.single (Step.store32 rfl hheader)
  have commitCost := commit.with_unit_cost (charge := work) (by
    intro before kind after member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
  refine ⟨[.instruction (.block 0 0 appendCopyBody), .instruction (.localGet 3),
      .instruction .eqz, .instruction (.br_if 0), .instruction (.localGet 1),
      .instruction (.localGet 6), .instruction .add, .instruction (.localGet 0),
      .instruction (.const 12), .instruction .add, .instruction (.localGet 3)] ++
      [.instruction .memoryCopy] ++
      [.administrative .exitControl, .instruction (.localGet 0), .instruction (.localGet 6),
      .instruction (.localGet 3), .instruction .add, .instruction (.localTee 6),
      .instruction (.store32 8)], rfl, ?_⟩
  have result := (scalarCost.trans copyCost).trans commitCost
  convert result using 1
  · rfl
  · simp only [List.length_cons, List.length_nil]
    omega

set_option maxRecDepth 65536 in
/-- One actual fitting-capacity iteration through its next read and EOF test.
The final generated branch pair is pending. This theorem assumes only this
iteration's physical header and byte ranges; it is not a whole-loop theorem. -/
theorem fitting_iteration_cost (store : MachineStore Universal.State) (dataPtr capacity : UInt32)
    (length current : Nat) (aux2 aux4 aux5 aux7 aux8 aux9 aux10 : UInt32) (ctx : Context)
    (hpositive : 0 < current) (hcurrent : current ≤ 256)
    (hcapacity : store.wasm.mem.read32 driverBase = capacity)
    (hfits : UInt32.ofNat current ≤ capacity - UInt32.ofNat length)
    (hdestination : (dataPtr + UInt32.ofNat length).toNat + current ≤ store.wasm.mem.pages * 65536)
    (hchunk : (driverBase + 12).toNat + 256 ≤ store.wasm.mem.pages * 65536)
    (hmodule : store.runtime.currentModule = Project.Mergesort.module)
    (hhost : store.runtime.currentHost = Universal.envFor Project.Mergesort.module) :
    let L := func3AppendLocals dataPtr (UInt32.ofNat current) (UInt32.ofNat length)
      aux2 aux4 aux5 aux7 aux8 aux9 aux10 []
    let nextCount := InputCost.readCount store 256
    let nextLocals := func3AppendLocals dataPtr (UInt32.ofNat nextCount) (UInt32.ofNat (length + current))
      aux2 aux4 aux5 aux7 aux8 aux9 aux10 []
    let nextStore := InputCost.readResult (appendedStore store dataPtr length current) 256 (driverBase + 12)
    ∃ trace, trace.length = 42 ∧
      CostedSteps work (head store L ctx) trace
        (afterClassify nextStore nextLocals (if nextCount = 0 then 1 else 0) ctx)
        (42 + current + nextCount) := by
  intro L nextCount nextLocals nextStore
  have hg := count_guard_cost store L current hcurrent rfl ctx.stack
    ([.block 0 0 func3CapacityBody] ++ func3AppendBody ++ func3ReadClassifyBody ++ [.br_if 2, .br 0])
    ctx.arity ctx.remainder (loopControls ctx) ctx.calls
  have hc := capacity_fits_cost store L (UInt32.ofNat current) (UInt32.ofNat length) capacity
    rfl rfl rfl hcapacity (by exact le_trans (by decide : driverBase.toNat + 4 ≤ (driverBase + 12).toNat) (by omega)) hfits
    ctx.stack (func3AppendBody ++ func3ReadClassifyBody ++ [.br_if 2, .br 0])
    ctx.arity ctx.remainder (loopControls ctx) ctx.calls
  obtain ⟨appendTrace, appendLength, ha⟩ := append_cost store dataPtr length current
    aux2 aux4 aux5 aux7 aux8 aux9 aux10 ctx.stack
    (func3ReadClassifyBody ++ [.br_if 2, .br 0]) ctx.arity ctx.remainder (loopControls ctx) ctx.calls
    hpositive (by norm_num [UInt32.size]; omega) hdestination (by omega)
    (by exact le_trans (by decide : (driverBase + 8).toNat + 4 ≤ (driverBase + 12).toNat) (by omega))
  obtain ⟨readTrace, readLength, hr⟩ := InputCost.read_classify_cost
    (appendedStore store dataPtr length current) dataPtr (UInt32.ofNat current)
    (UInt32.ofNat (length + current)) aux2 aux4 aux5 aux7 aux8 aux9 aux10 ctx.stack
    [.br_if 2, .br 0] ctx.arity ctx.remainder (loopControls ctx) ctx.calls hmodule hhost
    (by have hb := InputCost.readCount_bound (appendedStore store dataPtr length current)
        change (driverBase + 12).toNat + _ ≤ store.wasm.mem.pages * 65536
        omega)
  have hgc : CostedSteps work (head store L ctx)
      ([.instruction (.localGet 3), .instruction (.const 257), .instruction .geU, .instruction (.br_if 1)] ++
      [.instruction (.block 0 0 func3CapacityBody), .instruction (.localGet 3),
        .instruction (.localGet 0), .instruction (.load32 0), .instruction (.localGet 6),
        .instruction .sub, .instruction .leU, .instruction (.br_if 0)])
      ⟨.running ⟨{ L with values := ctx.stack },
        func3AppendBody ++ (func3ReadClassifyBody ++ [.br_if 2, .br 0]),
        ctx.arity, ctx.remainder, loopControls ctx, ctx.calls⟩, store⟩ 12 := by
    simpa only [head, func3ReadLoopBody, List.append_assoc, List.cons_append, List.nil_append] using hg.trans hc
  have ha' : CostedSteps work
      ⟨.running ⟨{ L with values := ctx.stack },
        func3AppendBody ++ (func3ReadClassifyBody ++ [.br_if 2, .br 0]),
        ctx.arity, ctx.remainder, loopControls ctx, ctx.calls⟩, store⟩ appendTrace
      ⟨.running ⟨func3AppendLocals dataPtr (UInt32.ofNat current) (UInt32.ofNat (length + current))
          aux2 aux4 aux5 aux7 aux8 aux9 aux10 ctx.stack,
        func3ReadClassifyBody ++ [.br_if 2, .br 0],
        ctx.arity, ctx.remainder, loopControls ctx, ctx.calls⟩,
        appendedStore store dataPtr length current⟩ (19 + current) := ha
  have result := (hgc.trans ha').trans hr
  refine ⟨([.instruction (.localGet 3), .instruction (.const 257), .instruction .geU, .instruction (.br_if 1)] ++
      [.instruction (.block 0 0 func3CapacityBody), .instruction (.localGet 3),
        .instruction (.localGet 0), .instruction (.load32 0), .instruction (.localGet 6),
        .instruction .sub, .instruction .leU, .instruction (.br_if 0)]) ++ appendTrace ++ readTrace, ?_, ?_⟩
  · simp only [List.length_append, appendLength, readLength, List.length_cons, List.length_nil]
  · convert result using 1
    · rfl
    · change 42 + current + nextCount = 12 + (19 + current) + (11 + nextCount)
      omega

/-- A nonempty input executes the first read, leaves the initial block,
initializes the vector locals and enters the active generated loop. -/
theorem initial_nonempty_cost (store : MachineStore Universal.State) (ctx : Context)
    (hinput : store.wasm.host.stdio.input ≠ [])
    (hmodule : store.runtime.currentModule = Project.Mergesort.module)
    (hhost : store.runtime.currentHost = Universal.envFor Project.Mergesort.module)
    (hchunk : (driverBase + 12).toNat + 256 ≤ store.wasm.mem.pages * 65536) :
    let count := InputCost.readCount store 256
    let nextStore := InputCost.readResult store 256 (driverBase + 12)
    let nextLocals := func3AppendLocals 1 (UInt32.ofNat count) 0 4 0 0 0 0 0 0 []
    ∃ trace, trace.length = 19 ∧
      CostedSteps work
        ⟨.running ⟨{ func3InitializedLocals with values := ctx.stack },
          .block 0 0 func3InitialReadBody :: func3AfterInitialRead ctx.afterLoop,
          ctx.arity, ctx.remainder, ctx.controls, ctx.calls⟩, store⟩ trace
        (head nextStore nextLocals ctx) (19 + count) := by
  intro count nextStore nextLocals
  let frame : ControlFrame :=
    { func3InitialReadFrame ctx.afterLoop with belowStack := ctx.stack }
  have hcountBound : count ≤ 256 := InputCost.readCount_bound store
  have hcountNonzero : UInt32.ofNat count ≠ 0 := by
    have hn : count ≠ 0 := fun h => hinput ((InputCost.readCount_zero_iff store).mp h)
    intro hz
    have hzNat := congrArg UInt32.toNat hz
    rw [UInt32.toNat_ofNat_of_lt' (by norm_num [UInt32.size]; omega)] at hzNat
    exact hn hzNat
  have entered : CostedSteps work
      ⟨.running ⟨{ func3InitializedLocals with values := ctx.stack },
        .block 0 0 func3InitialReadBody :: func3AfterInitialRead ctx.afterLoop,
        ctx.arity, ctx.remainder, ctx.controls, ctx.calls⟩, store⟩
      [.instruction (.block 0 0 func3InitialReadBody)]
      ⟨.running ⟨{ func3InitializedLocals with values := ctx.stack },
        func3InitialReadBody, ctx.arity, ctx.remainder, frame :: ctx.controls, ctx.calls⟩, store⟩ 1 :=
    CostedSteps.single Step.block
  obtain ⟨readTrace, readLength, readRun⟩ := InputCost.read_chunk_cost store func3InitializedLocals ctx.stack
    ([.localTee 3, .br_if 0] ++ func3EmptyInputSuffix) ctx.arity ctx.remainder
    (frame :: ctx.controls) ctx.calls rfl hmodule hhost (by omega)
  have suffix : Steps
      ⟨.running ⟨{ func3InitializedLocals with values := .i32 (UInt32.ofNat count) :: ctx.stack },
        [.localTee 3, .br_if 0] ++ func3EmptyInputSuffix,
        ctx.arity, ctx.remainder, frame :: ctx.controls, ctx.calls⟩, nextStore⟩
      [.instruction (.localTee 3), .instruction (.br_if 0), .instruction (.const 0),
        .instruction (.localSet 6), .instruction (.const 1), .instruction (.localSet 1)]
      ⟨.running ⟨{ nextLocals with values := ctx.stack },
        .block 0 0 func3ReadPhaseBody :: ctx.afterLoop,
        ctx.arity, ctx.remainder, ctx.controls, ctx.calls⟩, nextStore⟩ := by
    wasm_steps [(.localTee rfl), (.brIf hcountNonzero rfl), .const, (.localSet rfl), .const]
    simp only [frame, func3InitialReadFrame, List.take_zero, List.nil_append]
    exact Steps.single (.localSet (locals' := { nextLocals with values := .i32 1 :: ctx.stack }) rfl)
  have suffixCost := suffix.with_unit_cost (charge := work) (by
    intro before kind after member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
  have nextEntry := phase_entry_cost nextStore nextLocals ctx
  have readRun' : CostedSteps work
      ⟨.running ⟨{ func3InitializedLocals with values := ctx.stack },
        func3InitialReadBody, ctx.arity, ctx.remainder, frame :: ctx.controls, ctx.calls⟩, store⟩
      readTrace
      ⟨.running ⟨{ func3InitializedLocals with values := .i32 (UInt32.ofNat count) :: ctx.stack },
        [.localTee 3, .br_if 0] ++ func3EmptyInputSuffix,
        ctx.arity, ctx.remainder, frame :: ctx.controls, ctx.calls⟩, nextStore⟩ (9 + count) := readRun
  have joined := ((entered.trans readRun').trans suffixCost).trans nextEntry
  refine ⟨[.instruction (.block 0 0 func3InitialReadBody)] ++ readTrace ++
    [.instruction (.localTee 3), .instruction (.br_if 0), .instruction (.const 0),
      .instruction (.localSet 6), .instruction (.const 1), .instruction (.localSet 1)] ++
    [.instruction (.block 0 0 func3ReadPhaseBody),
      .instruction (.block 0 0 func3ReadLoopBlockBody), .instruction (.loop 0 0 func3ReadLoopBody)], ?_, ?_⟩
  · simp only [List.length_append, readLength, List.length_cons, List.length_nil]
  · convert joined using 1
    simp only [List.length_cons, List.length_nil]
    omega


def capacityFrame (stack : List Value) (code : Program) : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0, body := func3CapacityBody,
    continuation := code, belowStack := stack }

def capacityReload : Program :=
  [.localGet 0, .load32 4, .localSet 1, .localGet 0, .load32 8, .localSet 6]

/-- The non-fitting branch performs the actual header test and prepares all
five reserve arguments in their generated order. -/
theorem capacity_reserve_prefix (store : MachineStore Universal.State) (locals : Locals)
    (current length capacity : UInt32)
    (hlocal0 : locals.get 0 = some (.i32 driverBase))
    (hlocal3 : locals.get 3 = some (.i32 current))
    (hlocal6 : locals.get 6 = some (.i32 length))
    (hcapacity : store.wasm.mem.read32 driverBase = capacity)
    (hbound : driverBase.toNat + 4 ≤ store.wasm.mem.pages * 65536)
    (hreserve : ¬ current ≤ capacity - length)
    (stack : List Value) (code : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame) :
    CostedSteps work
      ⟨.running ⟨{ locals with values := stack }, .block 0 0 func3CapacityBody :: code,
        arity, remainder, controls, calls⟩, store⟩
      [.instruction (.block 0 0 func3CapacityBody), .instruction (.localGet 3),
        .instruction (.localGet 0), .instruction (.load32 0), .instruction (.localGet 6),
        .instruction .sub, .instruction .leU, .instruction (.br_if 0),
        .instruction (.localGet 0), .instruction (.localGet 6), .instruction (.localGet 3),
        .instruction (.const 1), .instruction (.const 1)]
      ⟨.running ⟨{ locals with values :=
          [.i32 1, .i32 1, .i32 current, .i32 length, .i32 driverBase] ++ stack },
        .call 4 :: capacityReload, arity, remainder,
        capacityFrame stack code :: controls, calls⟩, store⟩ 13 := by
  apply Steps.with_unit_cost
  · wasm_steps [.block, (.localGet (by exact hlocal3)), (.localGet (by exact hlocal0)),
      (.load32 rfl (by simpa using hbound))]
    rw [UInt32.add_zero, hcapacity]
    wasm_steps [(.localGet (by exact hlocal6)), .sub, (.leU (result := 0) (by simp [hreserve])),
      .brIfZero, (.localGet (by exact hlocal0)), (.localGet (by exact hlocal6)),
      (.localGet (by exact hlocal3)), .const]
    exact Steps.single Step.const
  · intro before kind after member
    fin_cases member <;> rfl

/-- A returned reserve reloads its actual pointer and length words and leaves
the capacity block, retaining the surrounding caller stack and controls. -/
theorem capacity_reserve_suffix (store : MachineStore Universal.State)
    (oldPtr newPtr current length aux2 aux4 aux5 aux7 aux8 aux9 aux10 : UInt32)
    (hpointer : store.wasm.mem.read32 (driverBase + 4) = newPtr)
    (hlength : store.wasm.mem.read32 (driverBase + 8) = length)
    (hbound : driverBase.toNat + 12 ≤ store.wasm.mem.pages * 65536)
    (stack : List Value) (code : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame) :
    CostedSteps work
      ⟨.running ⟨func3AppendLocals oldPtr current length aux2 aux4 aux5 aux7 aux8 aux9 aux10 stack,
        capacityReload, arity, remainder, capacityFrame stack code :: controls, calls⟩, store⟩
      [.instruction (.localGet 0), .instruction (.load32 4), .instruction (.localSet 1),
        .instruction (.localGet 0), .instruction (.load32 8), .instruction (.localSet 6),
        .administrative .exitControl]
      ⟨.running ⟨func3AppendLocals newPtr current length aux2 aux4 aux5 aux7 aux8 aux9 aux10 stack,
        code, arity, remainder, controls, calls⟩, store⟩ 7 := by
  apply Steps.with_unit_cost
  · wasm_steps [(.localGet rfl)]
    apply Steps.cons (Step.load32 (logicalAddress := driverBase.toNat) (physicalAddress := driverBase)
      rfl (by change driverBase.toNat + 4 + 4 ≤ store.wasm.mem.pages * 65536; omega))
    rw [hpointer]
    wasm_steps [(.localSet rfl), (.localGet rfl)]
    apply Steps.cons (Step.load32 (logicalAddress := driverBase.toNat) (physicalAddress := driverBase)
      rfl (by change driverBase.toNat + 8 + 4 ≤ store.wasm.mem.pages * 65536; omega))
    rw [hlength]
    wasm_steps [(.localSet rfl)]
    exact Steps.single (Step.exitControl rfl)
  · intro before kind after member
    fin_cases member <;> rfl

end Project.Mergesort.InputControlCost
