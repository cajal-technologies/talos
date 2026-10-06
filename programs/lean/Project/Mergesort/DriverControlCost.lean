import Project.Mergesort.SortExecutionCost
import Project.Mergesort.OutputResources

/-!
# Work of the generated driver control segments

Scalar setup, guards, no-op allocation markers and physical deallocation calls
are explicit transitions. The sort and output segments reuse their complete
operational certificates, preserving the actual physical store at each join.
-/

namespace Project.Mergesort.DriverControlCost

open Wasm Wasm.SmallStep Project.Mergesort.DriverProof
open Project.Mergesort.Representations

/-- The generated allocation marker returns without changing the store. -/
theorem marker_call_cost (store : MachineStore α) (caller : ThreadState α)
    (hmodule : store.runtime.currentModule = Project.Mergesort.module)
    (hostBytes : Config α → Nat → Config α → Nat) :
    CostedSteps (byteWork hostBytes)
      ⟨.running { caller with code := .call 7 :: caller.code }, store⟩
      [.instruction (.call 7), .administrative .returnFromCall]
      ⟨.running caller, store⟩ 2 := by
  apply Steps.with_unit_cost
  · apply Steps.cons (Step.call (fn := func4Def)
      (by rw [hmodule]; decide) (by rw [hmodule]; rfl))
    exact Steps.single (Step.returnFromCallExplicit rfl)
  · intro before kind after member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rfl

/-- The compiled physical deallocator is a two-transition call/return. Its
logical retirement is separate; the machine preserves every store field. -/
theorem deallocate_call_cost (store : MachineStore α) (caller : ThreadState α)
    (pointer size alignment : UInt32)
    (hmodule : store.runtime.currentModule = Project.Mergesort.module)
    (hostBytes : Config α → Nat → Config α → Nat) :
    CostedSteps (byteWork hostBytes)
      ⟨.running { caller with
        code := .call 10 :: caller.code
        locals := { caller.locals with values :=
          [.i32 alignment, .i32 size, .i32 pointer] ++ caller.locals.values } }, store⟩
      [.instruction (.call 10), .administrative .returnFromCall]
      ⟨.running caller, store⟩ 2 := by
  apply Steps.with_unit_cost
  · apply Steps.cons (Step.call (fn := func7Def)
      (by rw [hmodule]; decide) (by rw [hmodule]; rfl))
    exact Steps.single (Step.returnFromCallFallthrough rfl)
  · intro before kind after member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rfl

/-- Four generated loads followed by the complete actual recursive call. -/
theorem sort_phase_cost (store : MachineStore α) (values scratch inputPtr : UInt32)
    (n : Nat) (aux1 aux3 aux6 aux5 aux10 : UInt32)
    (code : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (hmodule : store.runtime.currentModule = Project.Mergesort.module)
    (hvaluesWrap : values.toNat + 4*n < UInt32.size)
    (hscratchWrap : scratch.toNat + 4*n < UInt32.size)
    (hvalues : values.toNat + 4*n ≤ store.wasm.mem.pages * 65536)
    (hscratch : scratch.toNat + 4*n ≤ store.wasm.mem.pages * 65536)
    (hostBytes : Config α → Nat → Config α → Nat) :
    let locals := func3AppendLocals aux1 aux3 aux6 values inputPtr aux5
      (UInt32.ofNat (4*n)) scratch (UInt32.ofNat n) aux10 []
    ∃ trace memory amount,
      CostedSteps (byteWork hostBytes)
        ⟨.running ⟨locals, [.localGet 2, .localGet 9, .localGet 8, .localGet 9, .call 5] ++ code,
          arity, remainder, controls, calls⟩, store⟩ trace
        ⟨.running ⟨locals, code, arity, remainder, controls, calls⟩,
          { store with wasm := { store.wasm with mem := memory } }⟩ amount ∧
      memory.pages = store.wasm.mem.pages ∧
      amount ≤ SortWorkBudget.budget n + 4 := by
  intro locals
  have setup : Steps
      ⟨.running ⟨locals, [.localGet 2, .localGet 9, .localGet 8, .localGet 9, .call 5] ++ code,
        arity, remainder, controls, calls⟩, store⟩
      [.instruction (.localGet 2), .instruction (.localGet 9),
        .instruction (.localGet 8), .instruction (.localGet 9)]
      ⟨.running ⟨{ locals with values := [.i32 (UInt32.ofNat n), .i32 scratch,
        .i32 (UInt32.ofNat n), .i32 values] }, .call 5 :: code,
        arity, remainder, controls, calls⟩, store⟩ := by
    wasm_steps [(.localGet rfl), (.localGet rfl), (.localGet rfl)]
    exact Steps.single (.localGet rfl)
  have setupCost := setup.with_unit_cost (charge := byteWork hostBytes) (by
    intro before kind after member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> rfl)
  obtain ⟨trace, memory, amount, execution, pages, bound⟩ :=
    SortExecutionCost.sort_call_cost n store values scratch locals [] code arity
      remainder controls calls hmodule hvaluesWrap hscratchWrap hvalues hscratch hostBytes
  refine ⟨_ ++ trace, memory, 4+amount, setupCost.trans execution, pages, by omega⟩

/-- The actual store sequence of the generated output loop. -/
def outputStore (store : MachineStore Universal.State) (cursor : UInt32) : Nat →
    MachineStore Universal.State
  | 0 => store
  | n+1 => outputStore (OutputCost.nextStore store cursor) (cursor+4) n

/-- Output preserves the runtime, globals and physical page count needed by
subsequent cleanup. Memory and host output follow the concrete operations. -/
theorem outputStore_frame (store : MachineStore Universal.State) (cursor : UInt32) (n : Nat) :
    (outputStore store cursor n).runtime = store.runtime ∧
      (outputStore store cursor n).wasm.globals = store.wasm.globals ∧
      (outputStore store cursor n).wasm.mem.pages = store.wasm.mem.pages := by
  induction n generalizing store cursor with
  | zero => exact ⟨rfl, rfl, rfl⟩
  | succ n ih => exact ih (OutputCost.nextStore store cursor) (cursor+4)

/-- Existing per-iteration certificates composed with an explicit final store,
so cleanup can read the runtime and global fields of that same store. -/
theorem output_body_cost (n : Nat) (hpositive : 0<n)
    (store : MachineStore Universal.State) (aux : OutputCost.Aux) (cursor : UInt32)
    (ctx : OutputCost.OutputContext)
    (hmodule : store.runtime.currentModule = Project.Mergesort.module)
    (hhost : store.runtime.currentHost.funcs[1]? = some CostedStdIO.writeHost)
    (hcount : 4*n < UInt32.size) (haddress : cursor.toNat+4*n ≤ UInt32.size)
    (hread : cursor.toNat+4*n ≤ store.wasm.mem.pages*65536)
    (hframe : 1048576 ≤ store.wasm.mem.pages*65536) :
    ∃ trace, CostedSteps CostedStdIO.work
      (OutputCost.loopHead store aux cursor (UInt32.ofNat (4*n)) ctx) trace
      (OutputCost.loopResume (outputStore store cursor n) aux
        (cursor+UInt32.ofNat (4*n)) ctx) (26*n+1) := by
  induction n generalizing store cursor with
  | zero => omega
  | succ n ih =>
    by_cases hz : n=0
    · subst n
      obtain ⟨trace, _, run⟩ := OutputCost.iteration_exit_segment store aux cursor
        hmodule hhost (by simpa using hread) hframe ctx
      exact ⟨trace, run⟩
    · have hp : 0<n := by omega
      have hcursor : (cursor+4).toNat = cursor.toNat+4 := by
        rw [UInt32.toNat_add]
        exact Nat.mod_eq_of_lt (by change cursor.toNat+4<UInt32.size; omega)
      have hpages : (OutputCost.nextStore store cursor).wasm.mem.pages = store.wasm.mem.pages := rfl
      obtain ⟨trace, _, run⟩ := OutputCost.iteration_continue_cost store aux cursor n
        hp (by omega) hmodule hhost (by omega) hframe ctx
      obtain ⟨tail, rest⟩ := ih hp (OutputCost.nextStore store cursor) (cursor+4)
        hmodule hhost (by omega) (by rw [hcursor]; omega)
        (by rw [hcursor,hpages]; omega) (by simpa only [hpages] using hframe)
      have hadvance : (cursor+4)+UInt32.ofNat (4*n) = cursor+UInt32.ofNat (4*(n+1)) := by
        rw [Nat.mul_add, Nat.mul_one, UInt32.ofNat_add]
        change (cursor+4)+UInt32.ofNat (4*n) = cursor+(UInt32.ofNat (4*n)+4)
        ac_rfl
      refine ⟨trace++tail, ?_⟩
      have joined := run.trans rest
      rw [hadvance] at joined
      convert joined using 1 <;> first | rfl | omega

/-- Generated output-block guard, local initialization, whole loop and block
exit. The final store is explicit and the caller continuation is unexecuted. -/
theorem output_phase_cost (store : MachineStore Universal.State) (values : UInt32)
    (n : Nat) (aux1 aux3 aux6 aux4 aux5 aux7 aux8 aux10 : UInt32)
    (afterOutput : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (hpositive : 0<n) (hcount : 4*n<UInt32.size)
    (hmodule : store.runtime.currentModule = Project.Mergesort.module)
    (hhost : store.runtime.currentHost = Universal.envFor Project.Mergesort.module)
    (haddress : values.toNat+4*n ≤ UInt32.size)
    (hread : values.toNat+4*n ≤ store.wasm.mem.pages*65536)
    (hframe : 1048576 ≤ store.wasm.mem.pages*65536) :
    ∃ trace, CostedSteps CostedStdIO.work
      ⟨.running ⟨func3AppendLocals aux1 aux3 aux6 values aux4 aux5 aux7 aux8
        (UInt32.ofNat n) aux10 [], .block 0 0 func3OutputBlockBody :: afterOutput,
        arity, remainder, controls, calls⟩, store⟩ trace
      ⟨.running ⟨func3AppendLocals aux1 (values+UInt32.ofNat (4*n)) 0 values
        aux4 aux5 aux7 aux8 (UInt32.ofNat n) aux10 [], afterOutput,
        arity, remainder, controls, calls⟩, outputStore store values n⟩ (26*n+13) := by
  let aux : OutputCost.Aux := ⟨.i32 aux1,.i32 values,.i32 aux4,.i32 aux5,
    .i32 aux7,.i32 aux8,.i32 (UInt32.ofNat n),.i32 aux10⟩
  let ctx : OutputCost.OutputContext :=
    { arity,remainder,controls :=
      { kind := .block, paramArity := 0, resultArity := 0,body := func3OutputBlockBody,
        continuation := afterOutput,belowStack := [] } :: controls,calls }
  have hn : UInt32.ofNat n ≠ 0 := by
    intro heq
    have hh := congrArg UInt32.toNat heq
    rw [UInt32.toNat_ofNat_of_lt' (by omega : n<UInt32.size)] at hh
    change n=0 at hh
    omega
  let setupTrace : List StepKind := [.instruction (.block 0 0 func3OutputBlockBody),
    .instruction (.localGet 9),.instruction .eqz,.instruction (.br_if 0),
    .instruction (.localGet 9),.instruction (.const 2),.instruction .shl,
    .instruction (.localSet 6),.instruction (.localGet 2),.instruction (.localSet 3),
    .instruction (.loop 0 0 OutputCost.outputBody)]
  have setup : Steps
      ⟨.running ⟨func3AppendLocals aux1 aux3 aux6 values aux4 aux5 aux7 aux8
        (UInt32.ofNat n) aux10 [], .block 0 0 func3OutputBlockBody :: afterOutput,
        arity, remainder, controls, calls⟩, store⟩ setupTrace
      (OutputCost.loopHead store aux values (UInt32.ofNat (4*n)) ctx) := by
    unfold setupTrace
    wasm_steps [.block]
    unfold func3OutputBlockBody
    wasm_steps [(.localGet rfl),(.eqz (result := 0) (by simp [hn])),.brIfZero,
      (.localGet rfl),.const,.shl]
    rw [MemRegion.shl2_eq_mul4]
    have hb : 4*UInt32.ofNat n = UInt32.ofNat (4*n) := by rw [UInt32.ofNat_mul]; rfl
    rw [hb]
    wasm_steps [(.localSet rfl),(.localGet rfl),(.localSet rfl)]
    exact Steps.single Step.loop
  have setupCost := setup.with_unit_cost (charge := CostedStdIO.work) (by
    intro before kind after member
    simp only [setupTrace,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl)
  have hh : store.runtime.currentHost.funcs[1]?=some CostedStdIO.writeHost := by
    rw [hhost]
    exact CostedStdIO.writeHost_resolves Project.Mergesort.module 1 (by decide) rfl
  obtain ⟨trace,run⟩ := output_body_cost n hpositive store aux values ctx
    hmodule hh hcount haddress hread hframe
  have exited : CostedSteps CostedStdIO.work
      (OutputCost.loopResume (outputStore store values n) aux
        (values+UInt32.ofNat (4*n)) ctx) [.administrative .exitControl]
      ⟨.running ⟨func3AppendLocals aux1 (values+UInt32.ofNat (4*n)) 0 values
        aux4 aux5 aux7 aux8 (UInt32.ofNat n) aux10 [],afterOutput,
        arity,remainder,controls,calls⟩,outputStore store values n⟩ 1 :=
    CostedSteps.single (.exitControl rfl)
  refine ⟨setupTrace++trace++[.administrative .exitControl],?_⟩
  convert (setupCost.trans run).trans exited using 1
  change 26*n+13 = 11+(26*n+1)+1
  omega

private def valuesDeallocBody : Program :=
  [.localGet 1,.eqz,.br_if 0,.localGet 2,.localGet 1,.const 2,.shl,.const 4,.call 10]
private def scratchDeallocBody : Program :=
  [.localGet 5,.br_if 0,.localGet 8,.localGet 10,.const 4,.call 10]
private def inputDeallocTail : Program :=
  [.localGet 0,.load32 0,.localTee 3,.eqz,.br_if 0,.localGet 4,.localGet 3,.const 1,.call 10]

private theorem cleanup_shape : func3NonemptyCleanup =
    [.block 0 0 valuesDeallocBody,.block 0 0 scratchDeallocBody]++inputDeallocTail := rfl

private def cleanupPrefixTrace : List StepKind :=
  [.instruction (.block 0 0 valuesDeallocBody),.instruction (.localGet 1),
    .instruction .eqz,.instruction (.br_if 0),.instruction (.localGet 2),
    .instruction (.localGet 1),.instruction (.const 2),.instruction .shl,
    .instruction (.const 4),.instruction (.call 10),.administrative .returnFromCall,
    .administrative .exitControl,.instruction (.block 0 0 scratchDeallocBody),
    .instruction (.localGet 5),.instruction (.br_if 0),.instruction (.localGet 8),
    .instruction (.localGet 10),.instruction (.const 4),.instruction (.call 10),
    .administrative .returnFromCall,.administrative .exitControl]

/-- Both work-array deallocation calls and their generated guards/exits. -/
theorem work_cleanup_cost (store : MachineStore α) (n : UInt32)
    (outputCursor final6 values inputPtr bytes scratch : UInt32)
    (calls : List CallFrame) (hpositive : n≠0)
    (hmodule : store.runtime.currentModule = Project.Mergesort.module)
    (hostBytes : Config α → Nat → Config α → Nat) :
    CostedSteps (byteWork hostBytes)
      ⟨.running ⟨func3AppendLocals n outputCursor final6 values inputPtr 0 bytes scratch n bytes [],
        func3NonemptyCleanup,0,[],[func3CleanupOuterFrame func3DriverBody],calls⟩,store⟩
      cleanupPrefixTrace
      ⟨.running ⟨func3AppendLocals n outputCursor final6 values inputPtr 0 bytes scratch n bytes [],
        inputDeallocTail,0,[],[func3CleanupOuterFrame func3DriverBody],calls⟩,store⟩ 21 := by
  apply Steps.with_unit_cost
  · rw [cleanup_shape]
    unfold cleanupPrefixTrace
    wasm_steps [.block]
    unfold valuesDeallocBody
    wasm_steps [(.localGet rfl),(.eqz (result := 0) (by simp [hpositive])),.brIfZero,
      (.localGet rfl),(.localGet rfl),.const,.shl,.const,
      (.call (fn := func7Def) (by rw [hmodule];decide) (by rw [hmodule];rfl)),
      (.returnFromCallFallthrough rfl),(.exitControl rfl),.block]
    unfold scratchDeallocBody
    wasm_steps [(.localGet rfl),.brIfZero,(.localGet rfl),(.localGet rfl),.const,
      (.call (fn := func7Def) (by rw [hmodule];decide) (by rw [hmodule];rfl)),
      (.returnFromCallFallthrough rfl)]
    exact Steps.single (.exitControl rfl)
  · intro before kind after member
    simp only [cleanupPrefixTrace,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|
      rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

/-- Input-vector deallocation (or its real empty-capacity skip) followed by
stack restoration. No assumption about the loaded capacity is needed. -/
theorem input_cleanup_cost (store : MachineStore α) (n : UInt32)
    (outputCursor final6 values inputPtr bytes scratch : UInt32)
    (calls : List CallFrame)
    (hmodule : store.runtime.currentModule = Project.Mergesort.module)
    (hframe : driverBase.toNat+4 ≤ store.wasm.mem.pages*65536)
    (hglobal : (globalAt? store 0).isSome = true)
    (hostBytes : Config α → Nat → Config α → Nat) :
    ∃ trace, trace.length ≤ 15 ∧ CostedSteps (byteWork hostBytes)
      ⟨.running ⟨func3AppendLocals n outputCursor final6 values inputPtr 0 bytes scratch n bytes [],
        inputDeallocTail,0,[],[func3CleanupOuterFrame func3DriverBody],calls⟩,store⟩ trace
      ⟨.running ⟨func3AppendLocals n (store.wasm.mem.read32 driverBase) final6 values inputPtr
        0 bytes scratch n bytes [],[],0,[],[],calls⟩,
        { store with wasm := { store.wasm with globals :=
          { globals := store.wasm.globals.globals.set 0 (.i32 entryStackTop) } } }⟩ trace.length := by
  let capacity := store.wasm.mem.read32 driverBase
  let cleanupLoadTrace : List StepKind := [.instruction (.localGet 0),.instruction (.load32 0),
    .instruction (.localTee 3),.instruction .eqz,.instruction (.br_if 0)]
  let restore : List StepKind := [.instruction (.localGet 0),.instruction (.const 272),
    .instruction .add,.instruction (.globalSet 0)]
  by_cases hz : capacity=0
  · refine ⟨cleanupLoadTrace++restore,by decide,?_⟩
    apply Steps.with_unit_cost
    · unfold inputDeallocTail cleanupLoadTrace restore
      wasm_steps [(.localGet rfl),(.load32 rfl hframe),(.localTee rfl)]
      rw [show driverBase+0=driverBase from UInt32.add_zero _]
      wasm_steps [(.eqz (result := 1) (by change _ = if capacity = 0 then _ else _; simp [hz])),(.brIf (by decide) rfl)]
      wasm_steps [(.localGet rfl),.const,.add]
      convert Steps.single (Step.globalSet hglobal) using 1
      simp only [setGlobal_zero_eq]
      rfl
    · intro before kind after member
      simp only [cleanupLoadTrace,restore,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with (rfl|rfl|rfl|rfl|rfl)|(rfl|rfl|rfl|rfl) <;> rfl
  · let deallocate : List StepKind := [.instruction (.localGet 4),.instruction (.localGet 3),
      .instruction (.const 1),.instruction (.call 10),.administrative .returnFromCall,
      .administrative .exitControl]
    refine ⟨cleanupLoadTrace++deallocate++restore,by decide,?_⟩
    apply Steps.with_unit_cost
    · unfold inputDeallocTail cleanupLoadTrace deallocate restore
      wasm_steps [(.localGet rfl),(.load32 rfl hframe),(.localTee rfl)]
      rw [show driverBase+0=driverBase from UInt32.add_zero _]
      wasm_steps [(.eqz (result := 0) (by change _ = if capacity = 0 then _ else _; simp [hz])),.brIfZero,
        (.localGet rfl),(.localGet rfl),.const,
        (.call (fn := func7Def) (by rw [hmodule];decide) (by rw [hmodule];rfl)),
        (.returnFromCallFallthrough rfl),(.exitControl rfl),(.localGet rfl),.const,.add]
      convert Steps.single (Step.globalSet hglobal) using 1
      simp only [setGlobal_zero_eq]
      rfl
    · intro before kind after member
      simp only [cleanupLoadTrace,deallocate,restore,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with ((rfl|rfl|rfl|rfl|rfl)|(rfl|rfl|rfl|rfl|rfl|rfl))|
        (rfl|rfl|rfl|rfl) <;> rfl

/-- A successful scratch pointer takes the generated depth-four branch after
restoring the element count and clearing the physical deallocation skip flag. -/
theorem scratch_success_cost (store : MachineStore α) (n : Nat)
    (final1 final3 final6 values source final5 final8 scratch : UInt32)
    (calls : List CallFrame) (hbyteBound : 4*n < UInt32.size) (hscratch : scratch ≠ 0)
    (hostBytes : Config α → Nat → Config α → Nat) :
    CostedSteps (byteWork hostBytes)
      ⟨.running ⟨func3AppendLocals final1 final3 final6 values source final5
        (UInt32.ofNat (4*n)) final8 (UInt32.ofNat n) (UInt32.ofNat (4*n)) [.i32 scratch],
        func3ScratchSuccessTail,0,[],func3ScratchSuccessControls,calls⟩,store⟩
      (func3ScratchSuccessTail.map StepKind.instruction)
      ⟨.running ⟨func3AppendLocals (UInt32.ofNat n) final3 final6 values source 0
        (UInt32.ofNat (4*n)) scratch (UInt32.ofNat n) (UInt32.ofNat (4*n)) [],
        func3SortAndCleanup,0,[],[func3CleanupOuterFrame func3DriverBody],calls⟩,store⟩ 10 := by
  have hshift : UInt32.ofNat (4*n) >>> (2 : UInt32) = UInt32.ofNat n := by
    apply UInt32.toNat.inj
    rw [UInt32.toNat_shiftRight,UInt32.toNat_ofNat_of_lt' hbyteBound,
      UInt32.toNat_ofNat_of_lt' (by omega : n < UInt32.size)]
    rw [show (2 : UInt32).toNat % 32 = 2 by decide,Nat.shiftRight_eq_div_pow]
    norm_num
  apply Steps.with_unit_cost
  · simp only [func3ScratchSuccessTail,List.map_cons,List.map_nil]
    wasm_steps [(.localTee rfl),(.eqz (result := 0) (by simp [hscratch])),.brIfZero,
      (.localGet rfl),.const,.shrU]
    rw [show (2 : UInt32) % 32 = 2 by decide,hshift]
    wasm_steps [(.localSet rfl),.const,(.localSet rfl)]
    exact Steps.single (.br func3_scratch_success_branch)
  · intro before kind after member
    simp only [func3ScratchSuccessTail,List.map_cons,List.map_nil,
      List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

/-- Output also retains global identity aliases, so cleanup may use the same
physical global lookup as the entry state. -/
theorem outputStore_globalAt (store : MachineStore Universal.State) (cursor : UInt32)
    (n index : Nat) : globalAt? (outputStore store cursor n) index = globalAt? store index := by
  induction n generalizing store cursor with
  | zero => rfl
  | succ n ih => exact ih (OutputCost.nextStore store cursor) (cursor+4)

/-- The entire nonempty continuation from the scratch allocator's returned
pointer through recursive sorting, output, deallocation and restored stack.
Every phase consumes the actual preceding store. -/
theorem after_scratch_cost (store : MachineStore Universal.State) (n : Nat)
    (final1 final3 final6 values source final5 final8 scratch : UInt32)
    (calls : List CallFrame) (hpositive : 0<n) (hscratch : scratch ≠ 0)
    (hmodule : store.runtime.currentModule = Project.Mergesort.module)
    (hhost : store.runtime.currentHost = Universal.envFor Project.Mergesort.module)
    (hvaluesWrap : values.toNat+4*n < UInt32.size)
    (hscratchWrap : scratch.toNat+4*n < UInt32.size)
    (hvalues : values.toNat+4*n ≤ store.wasm.mem.pages*65536)
    (hscratchBounds : scratch.toNat+4*n ≤ store.wasm.mem.pages*65536)
    (hframe : 1048576 ≤ store.wasm.mem.pages*65536)
    (hglobal : (globalAt? store 0).isSome = true) :
    ∃ trace finalStore finalLocals amount,
      CostedSteps CostedStdIO.work
        ⟨.running ⟨func3AppendLocals final1 final3 final6 values source final5
          (UInt32.ofNat (4*n)) final8 (UInt32.ofNat n) (UInt32.ofNat (4*n)) [.i32 scratch],
          func3ScratchSuccessTail,0,[],func3ScratchSuccessControls,calls⟩,store⟩ trace
        ⟨.running ⟨finalLocals,[],0,[],[],calls⟩,finalStore⟩ amount ∧
      finalStore.wasm.mem.pages = store.wasm.mem.pages ∧
      amount ≤ SortWorkBudget.budget n+26*n+63 := by
  have hcount : 4*n<UInt32.size := by omega
  have hn : UInt32.ofNat n ≠ 0 := by
    intro hh
    have := congrArg UInt32.toNat hh
    rw [UInt32.toNat_ofNat_of_lt' (by omega : n<UInt32.size)] at this
    change n=0 at this
    omega
  have success := scratch_success_cost store n final1 final3 final6 values source final5
    final8 scratch calls hcount hscratch CostedStdIO.hostBytes
  obtain ⟨sortTrace,memory,sortAmount,sortRun,pages,sortBound⟩ := sort_phase_cost store
    values scratch source n (UInt32.ofNat n) final3 final6 0 (UInt32.ofNat (4*n))
    (.block 0 0 func3OutputBlockBody :: func3NonemptyCleanup) 0 []
    [func3CleanupOuterFrame func3DriverBody] calls hmodule hvaluesWrap hscratchWrap
    hvalues hscratchBounds CostedStdIO.hostBytes
  let sortedStore := { store with wasm := { store.wasm with mem := memory } }
  obtain ⟨outputTrace,outputRun⟩ := output_phase_cost sortedStore values n
    (UInt32.ofNat n) final3 final6 source 0 (UInt32.ofNat (4*n)) scratch
    (UInt32.ofNat (4*n)) func3NonemptyCleanup 0 []
    [func3CleanupOuterFrame func3DriverBody] calls hpositive hcount hmodule hhost
    (by omega) (by simpa only [sortedStore,pages] using hvalues)
    (by simpa only [sortedStore,pages] using hframe)
  let emitted := outputStore sortedStore values n
  have emittedFrame := outputStore_frame sortedStore values n
  have emittedModule : emitted.runtime.currentModule = Project.Mergesort.module := by
    change (outputStore sortedStore values n).runtime.currentModule = _
    rw [emittedFrame.1]; exact hmodule
  have emittedPages : emitted.wasm.mem.pages=store.wasm.mem.pages := by
    exact emittedFrame.2.2.trans pages
  have emittedGlobal : (globalAt? emitted 0).isSome=true := by
    rw [show globalAt? emitted 0 = globalAt? sortedStore 0 from outputStore_globalAt _ _ _ _]
    exact hglobal
  have workCleanup := work_cleanup_cost emitted (UInt32.ofNat n)
    (values+UInt32.ofNat (4*n)) 0 values source (UInt32.ofNat (4*n)) scratch calls
    hn emittedModule CostedStdIO.hostBytes
  obtain ⟨cleanupTrace,cleanupBound,cleanupRun⟩ := input_cleanup_cost emitted
    (UInt32.ofNat n) (values+UInt32.ofNat (4*n)) 0 values source (UInt32.ofNat (4*n))
    scratch calls emittedModule (by rw [emittedPages]; exact Nat.le_trans (by decide : driverBase.toNat+4≤1048576) hframe)
    emittedGlobal CostedStdIO.hostBytes
  refine ⟨_,_,_,_,(((success.trans sortRun).trans outputRun).trans workCleanup).trans cleanupRun,emittedPages,?_⟩
  omega

end Project.Mergesort.DriverControlCost
