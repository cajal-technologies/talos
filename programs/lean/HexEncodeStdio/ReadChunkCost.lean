import HexEncodeStdio.ReadChunkOperational
import CodeLib.SepLogic.CostedStepsStdIO
import CodeLib.SepLogic.CostedLoop
import CodeLib.SepLogic.HostMemoryTrace

/-! # Numerical work of the actual generated hex input reader -/

namespace Project.HexEncodeStdio.ReadChunkCost

open Wasm Wasm.SmallStep Wasm.SmallStep.CostedStdIO Project.HexStdio

/-- A concrete generated segment with scalar transitions and byte work kept
separate. The byte term is charged on its actual execution, including EOF. -/
def ReadCostRun (initial final : Config Universal.State) (scalar bytes : Nat) : Prop :=
  ∃ trace, CostedSteps work initial trace final (scalar + bytes) ∧
    trace.length = scalar ∧ (∀ kind ∈ trace, HostPrimaryMemoryKind kind)

theorem ReadCostRun.reaches {initial final : Config Universal.State} {scalar bytes : Nat}
    (h : ReadCostRun initial final scalar bytes) : Reaches initial final := by
  obtain ⟨trace, run, _, _⟩ := h
  exact ⟨trace, run.erase⟩

theorem ReadCostRun.prepend {initial middle final : Config Universal.State}
    {kind : StepKind} {scalar bytes : Nat}
    (head : Step initial kind middle)
    (unit : work initial kind middle = 1)
    (allowed : HostPrimaryMemoryKind kind)
    (tail : ReadCostRun middle final scalar bytes) :
    ReadCostRun initial final (scalar + 1) bytes := by
  obtain ⟨trace, run, length, labels⟩ := tail
  refine ⟨kind :: trace, ?_, by simp [length], ?_⟩
  · simpa only [unit, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      CostedSteps.cons head run
  · intro next member
    rcases List.mem_cons.mp member with rfl | rest
    · exact allowed
    · exact labels next rest

theorem ReadCostRun.prepend_bulk {initial middle final : Config Universal.State}
    {kind : StepKind} {scalar bytes bulk : Nat}
    (head : Step initial kind middle)
    (charge : work initial kind middle = 1 + bulk)
    (allowed : HostPrimaryMemoryKind kind)
    (tail : ReadCostRun middle final scalar bytes) :
    ReadCostRun initial final (scalar + 1) (bulk + bytes) := by
  obtain ⟨trace, run, length, labels⟩ := tail
  refine ⟨kind :: trace, ?_, by simp [length], ?_⟩
  · simpa only [charge, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      CostedSteps.cons head run
  · intro next member
    rcases List.mem_cons.mp member with rfl | rest
    · exact allowed
    · exact labels next rest

/-- Exact actual adapter trace. The call to import zero is one host step. -/
def readTrace : List StepKind :=
  [.instruction (.call 19), .instruction (.localGet 3), .instruction (.localGet 2),
    .host 0, .instruction (.localSet 2), .instruction (.localGet 0),
    .instruction (.const 4), .instruction (.store8 0), .instruction (.localGet 0),
    .instruction (.localGet 2), .instruction (.store32 4), .administrative .returnFromCall]

/-- Generated absolute call19 returns after twelve transitions, charging the
actual transferred byte count. The status/count writes and original caller
resumption use the same physical successor store as the host transfer. -/
theorem read_adapter_cost (store : MachineStore Universal.State)
    (params localValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value) (controls : List ControlFrame) (calls : List CallFrame)
    (out ignored pointer requested : UInt32)
    (hmodule : store.runtime.currentModule = Project.HexStdio.module)
    (hhost : store.runtime.currentHost = Universal.envFor Project.HexStdio.module)
    (hread : pointer.toNat + (store.wasm.host.stdio.input.take requested.toNat).length ≤
      store.wasm.mem.pages * 65536)
    (hresult : out.toNat + 8 ≤ store.wasm.mem.pages * 65536) :
    CostedSteps work
      ⟨.running ⟨⟨params, localValues,
          [.i32 requested, .i32 pointer, .i32 ignored, .i32 out] ++ stack⟩,
        .call 19 :: code, arity, remainder, controls, calls⟩, store⟩ readTrace
      ⟨.running ⟨⟨params, localValues, stack⟩, code, arity, remainder, controls, calls⟩,
        readAdapterResultStore store out pointer (store.wasm.host.stdio.input.take requested.toNat)⟩
      (12 + min requested.toNat store.wasm.host.stdio.input.length) := by
  let bytes := store.wasm.host.stdio.input.take requested.toNat
  let read := universalReadStore store pointer bytes
  let caller : CallFrame :=
    { locals := ⟨params, localValues, stack⟩, continuation := code,
      resultArity := arity, callerRemainder := remainder, control := controls,
      returningInstance := store.runtime.entry }
  have first : Steps
      ⟨.running ⟨⟨params, localValues,
          [.i32 requested, .i32 pointer, .i32 ignored, .i32 out] ++ stack⟩,
        .call 19 :: code, arity, remainder, controls, calls⟩, store⟩
      [.instruction (.call 19), .instruction (.localGet 3), .instruction (.localGet 2)]
      ⟨.running ⟨⟨[.i32 out, .i32 ignored, .i32 pointer, .i32 requested], [],
          [.i32 pointer, .i32 requested]⟩, .call 0 :: func16.drop 3,
        0, [], [], caller :: calls⟩, store⟩ := by
    apply Steps.cons (Step.call (fn := func16Def)
      (by rw [hmodule]; decide) (by rw [hmodule]; rfl))
    simp only [func16Def, Function.toLocals, Function.numParams, func16]
    apply Steps.cons (Step.localGet rfl)
    exact Steps.single (Step.localGet rfl)
  have firstCost := first.with_unit_cost (charge := work) (by
    intro before kind after member
    fin_cases member <;> rfl)
  have hostRun := read_call_costed store 0
    [.i32 out, .i32 ignored, .i32 pointer, .i32 requested] [] [] (func16.drop 3)
    0 [] [] (caller :: calls) requested pointer (by rw [hmodule]; decide)
    (by simp only [hmodule]; rfl)
    (by rw [hhost]; exact readHost_resolves Project.HexStdio.module 0 (by decide) rfl) hread
  have suffix : Steps
      ⟨.running ⟨⟨[.i32 out, .i32 ignored, .i32 pointer, .i32 requested], [],
          [.i32 (UInt32.ofNat bytes.length)]⟩, func16.drop 3,
        0, [], [], caller :: calls⟩, read⟩
      [.instruction (.localSet 2), .instruction (.localGet 0), .instruction (.const 4),
        .instruction (.store8 0), .instruction (.localGet 0), .instruction (.localGet 2),
        .instruction (.store32 4), .administrative .returnFromCall]
      ⟨.running ⟨⟨params, localValues, stack⟩, code, arity, remainder, controls, calls⟩,
        readAdapterResultStore store out pointer bytes⟩ := by
    simp only [func16, List.drop]
    wasm_steps [(.localSet rfl), (.localGet rfl), .const]
    apply Steps.cons (Step.store8 (address := .i32 out) (offset := 0) rfl
      (by change out.toNat + 0 + 1 ≤ store.wasm.mem.pages * 65536; omega))
    rw [setMemory_eq]
    wasm_steps [(.localGet rfl), (.localGet rfl)]
    apply Steps.cons (Step.store32 (address := .i32 out) (offset := 4) rfl
      (by change out.toNat + 4 + 4 ≤ store.wasm.mem.pages * 65536; omega))
    rw [setMemory_eq]
    simp only [UInt32.add_zero]
    exact Steps.single (Step.returnFromCallFallthrough rfl)
  have suffixCost := suffix.with_unit_cost (charge := work) (by
    intro before kind after member
    fin_cases member <;> rfl)
  have complete := (firstCost.trans hostRun).trans suffixCost
  convert complete using 1
  · rfl
  · change 12 + min requested.toNat store.wasm.host.stdio.input.length =
      3 + (1 + min requested.toNat store.wasm.host.stdio.input.length) + 8
    omega

theorem read_trace_length : readTrace.length = 12 := rfl

theorem read_adapter_run
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (out ignored pointer length : UInt32) (bytes : List UInt8)
    (hmod : store.runtime.currentModule = «module»)
    (henv : store.runtime.currentHost = Universal.envFor «module»)
    (hbytes : bytes = store.wasm.host.stdio.input.take length.toNat)
    (hreadBound : pointer.toNat + bytes.length ≤
      store.wasm.mem.pages * 65536)
    (_houtBound : out.toNat + 1 ≤ store.wasm.mem.pages * 65536)
    (hout4Bound : out.toNat + 4 + 4 ≤
      store.wasm.mem.pages * 65536) :
    ReadCostRun
      ({ expr := .running
          ⟨⟨outerParams, outerLocalValues,
              [.i32 length, .i32 pointer, .i32 ignored, .i32 out] ++ stack⟩,
            [.call 19] ++ code, arity, remainder, controls, calls⟩
         store := store } : Config Universal.State)
      ({ expr := .running
          ⟨⟨outerParams, outerLocalValues, stack⟩,
            code, arity, remainder, controls, calls⟩
         store := readAdapterResultStore store out pointer bytes } :
        Config Universal.State) 12 bytes.length := by
  refine ⟨readTrace, ?_, rfl, ?_⟩
  · subst bytes
    simpa only [List.length_take, List.cons_append, List.nil_append] using read_adapter_cost store outerParams outerLocalValues
      stack code arity remainder controls calls out ignored pointer length hmod henv
      hreadBound (by omega)
  · intro kind member
    simp only [readTrace, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      trivial

/-- EOF still runs the complete adapter and writes a zero count. -/
theorem read_adapter_eof_cost (store : MachineStore Universal.State)
    (params localValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value) (controls : List ControlFrame) (calls : List CallFrame)
    (out ignored pointer requested : UInt32)
    (hmodule : store.runtime.currentModule = Project.HexStdio.module)
    (hhost : store.runtime.currentHost = Universal.envFor Project.HexStdio.module)
    (hinput : store.wasm.host.stdio.input = [])
    (hread : pointer.toNat ≤ store.wasm.mem.pages * 65536)
    (hresult : out.toNat + 8 ≤ store.wasm.mem.pages * 65536) :
    CostedSteps work
      ⟨.running ⟨⟨params, localValues,
          [.i32 requested, .i32 pointer, .i32 ignored, .i32 out] ++ stack⟩,
        .call 19 :: code, arity, remainder, controls, calls⟩, store⟩ readTrace
      ⟨.running ⟨⟨params, localValues, stack⟩, code, arity, remainder, controls, calls⟩,
        readAdapterResultStore store out pointer []⟩ 12 := by
  simpa only [hinput, List.take_nil, List.length_nil, Nat.min_zero, Nat.add_zero] using
    read_adapter_cost store params localValues stack code arity remainder controls calls
      out ignored pointer requested hmodule hhost (by simpa only [hinput, List.take_nil,
        List.length_nil, Nat.add_zero] using hread) hresult


/-- Actual fixed-size first read_chunk entry, its stack zero stores and the
complete read adapter. The first request is 32 bytes; transfer can be smaller
or zero. No allocation or successful continuation is assumed here. -/
theorem first_chunk_read_run (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value) (controls : List ControlFrame) (calls : List CallFrame)
    (out ignored vector sp : UInt32)
    (hmod : store.runtime.currentModule = Project.HexStdio.module)
    (henv : store.runtime.currentHost = Universal.envFor Project.HexStdio.module)
    (hglobal : globalAt? store 0 = some (.i32 sp))
    (h8no : ((sp - 48) + 8).toNat = (sp - 48).toNat + 8)
    (h40no : ((sp - 48) + 40).toNat = (sp - 48).toNat + 40)
    (hframe : (sp - 48).toNat + 48 ≤ store.wasm.mem.pages * 65536) :
    ReadCostRun
      ⟨.running ⟨⟨outerParams, outerLocalValues,
          [.i32 vector, .i32 ignored, .i32 out] ++ stack⟩,
        .call 4 :: code, arity, remainder, controls, calls⟩, store⟩
      (readChunkAfterReadConfig
        (readAdapterResultStore (readChunkFrameStore store (sp - 48))
          ((sp - 48) + 40) ((sp - 48) + 8) (store.wasm.host.stdio.input.take 32))
        outerParams outerLocalValues stack code arity remainder controls calls
        out ignored vector (sp - 48))
      38 (min 32 store.wasm.host.stdio.input.length) := by
  let framed := readChunkFrameStore store (sp - 48)
  let caller : CallFrame :=
    { locals := ⟨outerParams, outerLocalValues, stack⟩, continuation := code,
      resultArity := arity, callerRemainder := remainder, control := controls,
      returningInstance := store.runtime.entry }
  have prefixRun : Steps
      ⟨.running ⟨⟨outerParams, outerLocalValues,
          [.i32 vector, .i32 ignored, .i32 out] ++ stack⟩,
        .call 4 :: code, arity, remainder, controls, calls⟩, store⟩
      ([.instruction (.call 4)] ++ (func1.take 25).map StepKind.instruction)
      ⟨.running ⟨⟨[.i32 out, .i32 ignored, .i32 vector],
          [.i32 (sp - 48), .i32 0, .i32 0, .i32 0, .i32 0],
          [.i32 32, .i32 ((sp - 48) + 8), .i32 ignored, .i32 ((sp - 48) + 40)]⟩,
        .call 19 :: readChunkAfterRead, 0, [], [], caller :: calls⟩, framed⟩ := by
    have hnot : ¬4 < store.runtime.currentModule.imports.length := by
      rw [hmod]
      decide
    have hfn : store.runtime.currentModule.funcs[
        4 - store.runtime.currentModule.imports.length]? = some func1Def := by
      rw [hmod]
      rfl
    apply Steps.cons (Step.call hnot hfn)
    simp [func1Def, Function.toLocals, Function.numParams, func1]
    apply Steps.cons (Step.globalGet hglobal)
    apply Steps.cons Step.const
    apply Steps.cons Step.sub
    apply Steps.cons (Step.localTee rfl)
    apply Steps.cons (Step.globalSet (by simp [hglobal]))
    rw [setGlobal_zero_eq]
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons Step.constI64
    apply Steps.cons (Step.store64 rfl (by
      simpa using (show (sp - 48).toNat + 32 + 8 ≤
        store.wasm.mem.pages * 65536 by omega)))
    rw [setMemory_eq]
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons Step.constI64
    apply Steps.cons (Step.store64 rfl (by
      simpa using (show (sp - 48).toNat + 24 + 8 ≤
        store.wasm.mem.pages * 65536 by omega)))
    rw [setMemory_eq]
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons Step.constI64
    apply Steps.cons (Step.store64 rfl (by
      simpa using (show (sp - 48).toNat + 16 + 8 ≤
        store.wasm.mem.pages * 65536 by omega)))
    rw [setMemory_eq]
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons Step.constI64
    apply Steps.cons (Step.store64 rfl (by
      simpa using (show (sp - 48).toNat + 8 + 8 ≤
        store.wasm.mem.pages * 65536 by omega)))
    rw [setMemory_eq]
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons Step.const
    apply Steps.cons Step.add
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons (Step.localGet rfl)
    apply Steps.cons Step.const
    apply Steps.cons Step.add
    apply Steps.cons Step.const
    rw [show 8 + (sp - 48) = (sp - 48) + 8 by exact UInt32.add_comm _ _,
      show 40 + (sp - 48) = (sp - 48) + 40 by exact UInt32.add_comm _ _]
    exact Steps.refl _
  have prefixCost := prefixRun.with_unit_cost (charge := work) (by
    intro before kind after member
    fin_cases member <;> rfl)
  have adapter := read_adapter_cost framed
    [.i32 out, .i32 ignored, .i32 vector]
    [.i32 (sp - 48), .i32 0, .i32 0, .i32 0, .i32 0] []
    readChunkAfterRead 0 [] [] (caller :: calls)
    ((sp - 48) + 40) ignored ((sp - 48) + 8) 32 hmod henv
    (by change ((sp - 48) + 8).toNat + (store.wasm.host.stdio.input.take 32).length ≤ _
        have hc : (store.wasm.host.stdio.input.take 32).length ≤ 32 := List.length_take_le _ _
        rw [h8no]
        change (sp - 48).toNat + 8 + _ ≤ store.wasm.mem.pages * 65536
        omega)
    (by change ((sp - 48) + 40).toNat + 8 ≤ store.wasm.mem.pages * 65536
        rw [h40no]
        omega)
  refine ⟨([.instruction (.call 4)] ++ (func1.take 25).map StepKind.instruction) ++ readTrace,
    ?_, rfl, ?_⟩
  · convert prefixCost.trans adapter using 1
    · rfl
    · change 38 + min 32 store.wasm.host.stdio.input.length =
        26 + (12 + min 32 store.wasm.host.stdio.input.length)
      omega
  · intro kind member
    fin_cases member <;> trivial

theorem first_chunk_read_cost (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value) (controls : List ControlFrame) (calls : List CallFrame)
    (out ignored vector sp : UInt32)
    (hmod : store.runtime.currentModule = Project.HexStdio.module)
    (henv : store.runtime.currentHost = Universal.envFor Project.HexStdio.module)
    (hglobal : globalAt? store 0 = some (.i32 sp))
    (h8no : ((sp - 48) + 8).toNat = (sp - 48).toNat + 8)
    (h40no : ((sp - 48) + 40).toNat = (sp - 48).toNat + 40)
    (hframe : (sp - 48).toNat + 48 ≤ store.wasm.mem.pages * 65536) :
    ∃ trace, trace.length = 38 ∧ CostedSteps work
      ⟨.running ⟨⟨outerParams, outerLocalValues,
          [.i32 vector, .i32 ignored, .i32 out] ++ stack⟩,
        .call 4 :: code, arity, remainder, controls, calls⟩, store⟩ trace
      (readChunkAfterReadConfig
        (readAdapterResultStore (readChunkFrameStore store (sp - 48))
          ((sp - 48) + 40) ((sp - 48) + 8) (store.wasm.host.stdio.input.take 32))
        outerParams outerLocalValues stack code arity remainder controls calls
        out ignored vector (sp - 48))
      (38 + min 32 store.wasm.host.stdio.input.length) := by
  obtain ⟨trace, execution, length, _⟩ := first_chunk_read_run store outerParams outerLocalValues stack code arity remainder controls calls out ignored vector sp hmod henv hglobal h8no h40no hframe
  exact ⟨trace, length, execution⟩

end Project.HexEncodeStdio.ReadChunkCost
