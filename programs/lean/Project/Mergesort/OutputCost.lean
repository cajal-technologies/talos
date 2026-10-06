import Project.Mergesort.Spec
import CodeLib.RustStd.MemArray
import CodeLib.SepLogic.CostedLoop
import CodeLib.SepLogic.CostedStepsStdIO

set_option maxRecDepth 1048576

/-!
# Cost of the compiled merge-sort output loop

The annotation below uses the authoritative small-step semantics and the
concrete Universal stdio writer. It bounds the output phase;
`ExportWorkProof.named_export_work` composes it with reading, allocation and
sorting for the complete invocation. Work counts semantic transitions plus
transferred bytes; it does not measure the reference interpreter's internal
list operations or wall-clock time.
-/

namespace Project.Mergesort.OutputCost

open Wasm Wasm.SmallStep
open Wasm.SmallStep.CostedStdIO

private def bodyOf : Instruction → Program
  | .block _ _ body _ _ | .loop _ _ body _ _ => body
  | _ => []

/-- The loop is extracted from the generated `func3` AST, so the certificate
cannot silently drift to a similar handwritten program. -/
def outputBody : Program :=
  bodyOf ((bodyOf ((bodyOf (func3[21]?.getD .nop))[6]?.getD .nop))[9]?.getD .nop)

theorem output_body_generated : outputBody =
    [.localGet 0, .localGet 3, .load32 0, .store32 268,
      .localGet 0, .const 268, .add, .const 4, .call 14,
      .localGet 3, .const 4, .add, .localSet 3,
      .localGet 6, .const 4294967292, .add, .localTee 6, .br_if 0] := rfl

/-- Exact generated call-14 shim. -/
theorem write_shim_body : func11 = [.localGet 1, .localGet 0, .call 1] := rfl

def writeTrace : List StepKind :=
  [.instruction (.call 14), .instruction (.localGet 1),
    .instruction (.localGet 0), .host 1, .administrative .returnFromCall]

/-- Call entry, both generated local loads, actual host transfer, and call
return are all charged. Arbitrary caller frames are preserved. -/
theorem write_shim_cost
    (store : MachineStore Universal.State)
    (params localValues values : List Value) (code : Program) (arity : Nat)
    (remainder : List Value) (controls : List ControlFrame) (calls : List CallFrame)
    (length pointer : UInt32)
    (hmodule : store.runtime.currentModule = Project.Mergesort.module)
    (hhost : store.runtime.currentHost.funcs[1]? = some writeHost)
    (hbound : pointer.toNat + length.toNat ≤ store.wasm.mem.pages * 65536) :
    CostedSteps work
      ⟨.running ⟨⟨params, localValues, .i32 length :: .i32 pointer :: values⟩,
        .call 14 :: code, arity, remainder, controls, calls⟩, store⟩
      writeTrace
      ⟨.running ⟨⟨params, localValues, values⟩, code, arity, remainder, controls, calls⟩,
        { store with wasm := writeStore store.wasm length pointer }⟩
      (length.toNat + 5) := by
  let caller : CallFrame :=
    { locals := ⟨params, localValues, values⟩, continuation := code,
      resultArity := arity, callerRemainder := remainder, control := controls,
      returningInstance := store.runtime.entry }
  have preExecution : Steps
      ⟨.running ⟨⟨params, localValues, .i32 length :: .i32 pointer :: values⟩,
        .call 14 :: code, arity, remainder, controls, calls⟩, store⟩
      [.instruction (.call 14), .instruction (.localGet 1), .instruction (.localGet 0)]
      ⟨.running ⟨⟨[.i32 pointer, .i32 length], [], [.i32 pointer, .i32 length]⟩,
        [.call 1], 0, [], [], caller :: calls⟩, store⟩ := by
    wasm_steps [(.call (fn := func11Def) (by rw [hmodule]; decide)
      (by rw [hmodule]; rfl)), (.localGet rfl)]
    exact Steps.single (.localGet rfl)
  have prefixCost := preExecution.with_unit_cost (charge := work) (by
    intro before kind after member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> rfl)
  have transfer := write_call_costed store 1 [.i32 pointer, .i32 length] [] [] []
    0 [] [] (caller :: calls) length pointer
    (by rw [hmodule]; decide) (by simpa only [hmodule] using
      (show Project.Mergesort.module.imports[1] = StdIO.imports[1] from rfl)) hhost hbound
  have suffix : CostedSteps work
      ⟨.running ⟨⟨[.i32 pointer, .i32 length], [], []⟩,
        [], 0, [], [], caller :: calls⟩,
        { store with wasm := writeStore store.wasm length pointer }⟩
      [.administrative .returnFromCall]
      ⟨.running ⟨⟨params, localValues, values⟩, code, arity, remainder, controls, calls⟩,
        { store with wasm := writeStore store.wasm length pointer }⟩ 1 :=
    CostedSteps.single (.returnFromCallFallthrough rfl)
  convert prefixCost.trans (transfer.trans suffix) using 1 <;> simp [writeTrace]
  omega

/-- Local slots not changed by the output loop. Their values are arbitrary. -/
structure Aux where
  a1 : Value
  a2 : Value
  a4 : Value
  a5 : Value
  a7 : Value
  a8 : Value
  a9 : Value
  a10 : Value

def outputLocals (aux : Aux) (cursor countdown : UInt32)
    (values : List Value := []) : Locals :=
  { locals := [.i32 1048304, aux.a1, aux.a2, .i32 cursor, aux.a4, aux.a5,
      .i32 countdown, aux.a7, aux.a8, aux.a9, aux.a10]
    values := values }

/-- The surrounding Wasm continuation is preserved by the output segment.
The generated zero-parameter driver enters this loop with an empty operand
stack; this record does not generalize that local stack shape. -/
structure OutputContext where
  continuation : Program := []
  arity : Nat := 0
  remainder : List Value := []
  controls : List ControlFrame := []
  calls : List CallFrame := []

def loopFrame (ctx : OutputContext := {}) : ControlFrame :=
  { kind := .loop, paramArity := 0, resultArity := 0,
    body := outputBody, continuation := ctx.continuation, belowStack := [] }

def loopHead (store : MachineStore Universal.State) (aux : Aux)
    (cursor countdown : UInt32) (ctx : OutputContext := {}) : Config Universal.State :=
  ⟨.running ⟨outputLocals aux cursor countdown, outputBody, ctx.arity, ctx.remainder,
      loopFrame ctx :: ctx.controls, ctx.calls⟩, store⟩

def stagedStore (store : MachineStore Universal.State) (cursor : UInt32) :
    MachineStore Universal.State :=
  { store with wasm := { store.wasm with
      mem := store.wasm.mem.write32 1048572 (store.wasm.mem.read32 (cursor + 0)) } }

def nextStore (store : MachineStore Universal.State) (cursor : UInt32) :
    MachineStore Universal.State :=
  let staged := stagedStore store cursor
  { staged with wasm := writeStore staged.wasm 4 1048572 }

private def afterWrite : Program :=
  [.localGet 3, .const 4, .add, .localSet 3, .localGet 6,
    .const 4294967292, .add, .localTee 6, .br_if 0]

private def beforeBranch (store : MachineStore Universal.State) (aux : Aux)
    (cursor countdown : UInt32) (ctx : OutputContext := {}) : Config Universal.State :=
  ⟨.running ⟨outputLocals aux (cursor + 4) (countdown + 4294967292)
      [.i32 (countdown + 4294967292)], [.br_if 0], ctx.arity, ctx.remainder,
      loopFrame ctx :: ctx.controls, ctx.calls⟩, nextStore store cursor⟩

/-- One generated iteration up to its branch: the scratch store, complete
call-14 wrapper, concrete four-byte write, and updated loop counters. -/
theorem iteration_prefix_cost
    (store : MachineStore Universal.State) (aux : Aux) (cursor countdown : UInt32)
    (hmodule : store.runtime.currentModule = Project.Mergesort.module)
    (hhost : store.runtime.currentHost.funcs[1]? = some writeHost)
    (hread : cursor.toNat + 4 ≤ store.wasm.mem.pages * 65536)
    (hframe : 1048576 ≤ store.wasm.mem.pages * 65536)
    (ctx : OutputContext := {}) :
    ∃ trace, trace.length = 21 ∧
      CostedSteps work (loopHead store aux cursor countdown ctx) trace
        (beforeBranch store aux cursor countdown ctx) 25 := by
  let preTrace : List StepKind :=
    [.instruction (.localGet 0), .instruction (.localGet 3),
      .instruction (.load32 0), .instruction (.store32 268),
      .instruction (.localGet 0), .instruction (.const 268),
      .instruction .add, .instruction (.const 4)]
  have preExecution : Steps (loopHead store aux cursor countdown ctx) preTrace
      ⟨.running ⟨outputLocals aux cursor countdown [.i32 4, .i32 1048572],
        .call 14 :: afterWrite, ctx.arity, ctx.remainder, loopFrame ctx :: ctx.controls, ctx.calls⟩, stagedStore store cursor⟩ := by
    unfold loopHead
    rw [output_body_generated]
    wasm_steps [(.localGet rfl), (.localGet rfl),
      (.load32 rfl (by simpa using hread)), (.store32 rfl hframe),
      (.localGet rfl), .const, .add]
    exact Steps.single .const
  have preCost := preExecution.with_unit_cost (charge := work) (by
    intro before kind after member
    simp only [preTrace, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
  have writeCost := write_shim_cost (stagedStore store cursor)
    [] (outputLocals aux cursor countdown).locals [] afterWrite ctx.arity ctx.remainder (loopFrame ctx :: ctx.controls) ctx.calls
    4 1048572 hmodule hhost hframe
  let postTrace : List StepKind :=
    [.instruction (.localGet 3), .instruction (.const 4), .instruction .add,
      .instruction (.localSet 3), .instruction (.localGet 6),
      .instruction (.const 4294967292), .instruction .add,
      .instruction (.localTee 6)]
  have postExecution : Steps
      ⟨.running ⟨outputLocals aux cursor countdown,
        afterWrite, ctx.arity, ctx.remainder, loopFrame ctx :: ctx.controls, ctx.calls⟩, nextStore store cursor⟩
      postTrace (beforeBranch store aux cursor countdown ctx) := by
    wasm_steps [(.localGet rfl), .const, .add, (.localSet rfl),
      (.localGet rfl), .const, .add]
    exact Steps.single (.localTee (by simp [outputLocals, UInt32.add_comm]))
  have postCost := postExecution.with_unit_cost (charge := work) (by
    intro before kind after member
    simp only [postTrace, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
  exact ⟨_, rfl, preCost.trans (writeCost.trans postCost)⟩

private theorem countdown_step (n : Nat) :
    UInt32.ofNat (4 * (n + 1)) + 4294967292 = UInt32.ofNat (4 * n) := by
  rw [Nat.mul_add, Nat.mul_one, UInt32.ofNat_add, UInt32.add_assoc]
  exact UInt32.add_zero _

private theorem next_pages (store : MachineStore Universal.State) (cursor : UInt32) :
    (nextStore store cursor).wasm.mem.pages = store.wasm.mem.pages := rfl

private theorem next_output_length
    (store : MachineStore Universal.State) (cursor : UInt32) :
    (nextStore store cursor).wasm.host.stdio.output.length =
      store.wasm.host.stdio.output.length + 4 := by
  simp [nextStore, stagedStore, writeStore, Mem.readBytes]

/-- A taken back-edge completes one generated iteration, including its four
transferred bytes. The next loop head carries the actual changed store. -/
theorem iteration_continue_cost
    (store : MachineStore Universal.State) (aux : Aux) (cursor : UInt32) (n : Nat)
    (hpositive : 0 < n) (hcount : 4 * n < UInt32.size)
    (hmodule : store.runtime.currentModule = Project.Mergesort.module)
    (hhost : store.runtime.currentHost.funcs[1]? = some writeHost)
    (hread : cursor.toNat + 4 ≤ store.wasm.mem.pages * 65536)
    (hframe : 1048576 ≤ store.wasm.mem.pages * 65536)
    (ctx : OutputContext := {}) :
    ∃ trace, trace.length = 22 ∧
      CostedSteps work (loopHead store aux cursor (UInt32.ofNat (4 * (n + 1))) ctx)
        trace (loopHead (nextStore store cursor) aux (cursor + 4) (UInt32.ofNat (4 * n)) ctx)
        26 := by
  obtain ⟨trace, length, pre⟩ := iteration_prefix_cost store aux cursor
    (UInt32.ofNat (4 * (n + 1))) hmodule hhost hread hframe ctx
  have nonzero : UInt32.ofNat (4 * (n + 1)) + 4294967292 ≠ 0 := by
    rw [countdown_step]
    intro zero
    have := congrArg UInt32.toNat zero
    rw [UInt32.toNat_ofNat_of_lt' hcount] at this
    change 4 * n = 0 at this
    omega
  have branch : CostedSteps work
      (beforeBranch store aux cursor (UInt32.ofNat (4 * (n + 1))) ctx)
      [.instruction (.br_if 0)]
      (loopHead (nextStore store cursor) aux (cursor + 4) (UInt32.ofNat (4 * n)) ctx) 1 := by
    unfold beforeBranch loopHead
    rw [← countdown_step n]
    exact CostedSteps.single (.brIf nonzero rfl)
  refine ⟨_, by simp [length], pre.trans branch⟩

/-- Resume exactly the enclosing continuation after the output loop. -/
def loopResume (store : MachineStore Universal.State) (aux : Aux)
    (cursor : UInt32) (ctx : OutputContext) : Config Universal.State :=
  ⟨.running ⟨outputLocals aux cursor 0, ctx.continuation,
      ctx.arity, ctx.remainder, ctx.controls, ctx.calls⟩, store⟩

/-- The last iteration exits only its own loop frame. The caller's
continuation remains unexecuted; no synthetic `finish` is charged. -/
theorem iteration_exit_segment
    (store : MachineStore Universal.State) (aux : Aux) (cursor : UInt32)
    (hmodule : store.runtime.currentModule = Project.Mergesort.module)
    (hhost : store.runtime.currentHost.funcs[1]? = some writeHost)
    (hread : cursor.toNat + 4 ≤ store.wasm.mem.pages * 65536)
    (hframe : 1048576 ≤ store.wasm.mem.pages * 65536) (ctx : OutputContext) :
    ∃ trace, trace.length = 23 ∧
      CostedSteps work (loopHead store aux cursor 4 ctx) trace
        (loopResume (nextStore store cursor) aux (cursor + 4) ctx) 27 := by
  obtain ⟨trace, length, pre⟩ := iteration_prefix_cost store aux cursor 4
    hmodule hhost hread hframe ctx
  have suffix : Steps (beforeBranch store aux cursor 4 ctx)
      [.instruction (.br_if 0), .administrative .exitControl]
      (loopResume (nextStore store cursor) aux (cursor + 4) ctx) := by
    wasm_steps [.brIfZero]
    exact Steps.single (.exitControl rfl)
  have suffixCost := suffix.with_unit_cost (charge := work) (by
    intro before kind after member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rfl)
  exact ⟨_, by simp [length], pre.trans suffixCost⟩

/-- The last iteration falls through the loop and finishes normally. Both
administrative transitions are charged. -/
theorem iteration_exit_cost
    (store : MachineStore Universal.State) (aux : Aux) (cursor : UInt32)
    (hmodule : store.runtime.currentModule = Project.Mergesort.module)
    (hhost : store.runtime.currentHost.funcs[1]? = some writeHost)
    (hread : cursor.toNat + 4 ≤ store.wasm.mem.pages * 65536)
    (hframe : 1048576 ≤ store.wasm.mem.pages * 65536) :
    ∃ trace, trace.length = 24 ∧
      CostedSteps work (loopHead store aux cursor 4) trace
        ⟨.done [], nextStore store cursor⟩ 28 := by
  obtain ⟨trace, length, pre⟩ := iteration_prefix_cost store aux cursor 4
    hmodule hhost hread hframe
  have suffix : Steps (beforeBranch store aux cursor 4)
      [.instruction (.br_if 0), .administrative .exitControl, .administrative .finish]
      ⟨.done [], nextStore store cursor⟩ := by
    wasm_steps [.brIfZero, (.exitControl rfl)]
    exact Steps.single .finish
  have suffixCost := suffix.with_unit_cost (charge := work) (by
    intro before kind after member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> rfl)
  exact ⟨_, by simp [length], pre.trans suffixCost⟩

/-- All positive iterations of the actual compiled output loop. The bounds
prevent wrap of accessed source addresses and nonzero byte countdowns, and
require the source range and scratch slot to lie in the real physical memory.
No disjointness assumption is needed for this cost-only theorem. The stronger
`output_loop_segment_serializes` theorem proves the concrete output contents. -/
theorem loop_exact_cost
    (n : Nat) (hpositive : 0 < n)
    (store : MachineStore Universal.State) (aux : Aux) (cursor : UInt32)
    (hmodule : store.runtime.currentModule = Project.Mergesort.module)
    (hhost : store.runtime.currentHost.funcs[1]? = some writeHost)
    (hcount : 4 * n < UInt32.size)
    (haddress : cursor.toNat + 4 * n ≤ UInt32.size)
    (hread : cursor.toNat + 4 * n ≤ store.wasm.mem.pages * 65536)
    (hframe : 1048576 ≤ store.wasm.mem.pages * 65536) :
    ∃ trace finalStore,
      CostedSteps work (loopHead store aux cursor (UInt32.ofNat (4 * n))) trace
        ⟨.done [], finalStore⟩ (26 * n + 2) ∧
      trace.length = 22 * n + 2 ∧
      finalStore.wasm.host.stdio.output.length = store.wasm.host.stdio.output.length + 4 * n ∧
      finalStore.wasm.mem.pages = store.wasm.mem.pages := by
  induction n generalizing store aux cursor with
  | zero => omega
  | succ n ih =>
      by_cases zero : n = 0
      · subst n
        obtain ⟨trace, length, execution⟩ := iteration_exit_cost store aux cursor
          hmodule hhost (by simpa using hread) hframe
        exact ⟨trace, nextStore store cursor, execution, length,
          next_output_length store cursor, next_pages store cursor⟩
      · have positive : 0 < n := by omega
        obtain ⟨trace, length, execution⟩ := iteration_continue_cost store aux cursor n
          positive (by omega) hmodule hhost (by omega) hframe
        have cursorStep : (cursor + 4).toNat = cursor.toNat + 4 := by
          rw [UInt32.toNat_add]
          exact Nat.mod_eq_of_lt (by change cursor.toNat + 4 < UInt32.size; omega)
        obtain ⟨tail, finalStore, tailExecution, tailLength, outputLength, pages⟩ :=
          ih positive (nextStore store cursor) aux (cursor + 4) hmodule hhost
            (by omega) (by rw [cursorStep]; omega)
            (by rw [cursorStep, next_pages]; omega) (by simpa only [next_pages] using hframe)
        refine ⟨trace ++ tail, finalStore, ?_, ?_, ?_, ?_⟩
        · convert execution.trans tailExecution using 1
          omega
        · simp only [List.length_append, length, tailLength]
          omega
        · rw [next_output_length] at outputLength
          omega
        · simpa only [next_pages] using pages

def loopEntry (store : MachineStore Universal.State) (aux : Aux)
    (cursor : UInt32) (n : Nat) (ctx : OutputContext := {}) : Config Universal.State :=
  ⟨.running ⟨outputLocals aux cursor (UInt32.ofNat (4 * n)),
      .loop 0 0 outputBody :: ctx.continuation, ctx.arity, ctx.remainder,
      ctx.controls, ctx.calls⟩, store⟩

private theorem next_output
    (store : MachineStore Universal.State) (cursor : UInt32) :
    (nextStore store cursor).wasm.host.stdio.output =
      store.wasm.host.stdio.output ++ Spec.encodeWord (store.wasm.mem.read32 cursor) := by
  have mask (value : UInt8) : value &&& 255 = value := UInt8.and_neg_one
  simp [nextStore, stagedStore, writeStore, Mem.readBytes, Mem.write32,
    List.range_succ, Spec.encodeWord, UInt32.toUInt8_and, mask]

private theorem readWords32_write32_outside
    (memory : Mem) (destination value cursor : UInt32) (n : Nat)
    (hbound : cursor.toNat + 4 * n ≤ UInt32.size)
    (hdisjoint : destination.toNat + 4 ≤ cursor.toNat ∨
      cursor.toNat + 4 * n ≤ destination.toNat) :
    (memory.write32 destination value).readWords32 cursor n =
      memory.readWords32 cursor n := by
  induction n generalizing cursor with
  | zero => rfl
  | succ n ih =>
      rw [Mem.readWords32, Mem.readWords32,
        Mem.read32_write32_disjoint memory destination cursor value (by omega)]
      congr 1
      by_cases zero : n = 0
      · simp [zero, Mem.readWords32]
      · have cursorStep : (cursor + 4).toNat = cursor.toNat + 4 := by
          rw [UInt32.toNat_add]
          exact Nat.mod_eq_of_lt (by change cursor.toNat + 4 < UInt32.size; omega)
        apply ih (cursor + 4) <;> rw [cursorStep] <;> omega

private theorem advance_cursor (cursor : UInt32) (n : Nat) :
    (cursor + 4) + UInt32.ofNat (4 * n) = cursor + UInt32.ofNat (4 * (n + 1)) := by
  rw [Nat.mul_add, Nat.mul_one, UInt32.ofNat_add]
  change (cursor + 4) + UInt32.ofNat (4 * n) = cursor + (UInt32.ofNat (4 * n) + 4)
  ac_rfl

/-- The complete compiled loop, from its body head to its actual caller
continuation, with the source words serialized on this same costed trace.
The source range is physically readable and disjoint from the four-byte
scratch slot. The concrete memory and host transitions establish the
serialization on the same constructed trace. -/
theorem loop_segment_serializes
    (n : Nat) (hpositive : 0 < n)
    (store : MachineStore Universal.State) (aux : Aux) (cursor : UInt32)
    (ctx : OutputContext)
    (hmodule : store.runtime.currentModule = Project.Mergesort.module)
    (hhost : store.runtime.currentHost.funcs[1]? = some writeHost)
    (hcount : 4 * n < UInt32.size)
    (haddress : cursor.toNat + 4 * n ≤ UInt32.size)
    (hread : cursor.toNat + 4 * n ≤ store.wasm.mem.pages * 65536)
    (hframe : 1048576 ≤ store.wasm.mem.pages * 65536)
    (hdisjoint : 1048576 ≤ cursor.toNat ∨ cursor.toNat + 4 * n ≤ 1048572) :
    ∃ trace finalStore,
      CostedSteps work (loopHead store aux cursor (UInt32.ofNat (4 * n)) ctx) trace
        (loopResume finalStore aux (cursor + UInt32.ofNat (4 * n)) ctx) (26 * n + 1) ∧
      trace.length = 22 * n + 1 ∧
      finalStore.wasm.host.stdio.output = store.wasm.host.stdio.output ++
        Spec.encodeValues (store.wasm.mem.readWords32 cursor n) ∧
      finalStore.wasm.mem.pages = store.wasm.mem.pages := by
  induction n generalizing store aux cursor with
  | zero => omega
  | succ n ih =>
      by_cases zero : n = 0
      · subst n
        obtain ⟨trace, length, execution⟩ := iteration_exit_segment store aux cursor
          hmodule hhost (by simpa using hread) hframe ctx
        refine ⟨trace, nextStore store cursor, execution, length, ?_, next_pages store cursor⟩
        simpa [Mem.readWords32, Spec.encodeValues, Spec.u32Codec,
          WordCodec.serialize_cons, WordCodec.serialize_nil] using next_output store cursor
      · have positive : 0 < n := by omega
        obtain ⟨trace, length, execution⟩ := iteration_continue_cost store aux cursor n
          positive (by omega) hmodule hhost (by omega) hframe ctx
        have cursorStep : (cursor + 4).toNat = cursor.toNat + 4 := by
          rw [UInt32.toNat_add]
          exact Nat.mod_eq_of_lt (by change cursor.toNat + 4 < UInt32.size; omega)
        obtain ⟨tail, finalStore, tailExecution, tailLength, output, pages⟩ :=
          ih positive (nextStore store cursor) aux (cursor + 4) hmodule hhost
            (by omega) (by rw [cursorStep]; omega)
            (by rw [cursorStep, next_pages]; omega) (by simpa only [next_pages] using hframe)
            (by rw [cursorStep]; omega)
        have sourcePreserved :
            (nextStore store cursor).wasm.mem.readWords32 (cursor + 4) n =
              store.wasm.mem.readWords32 (cursor + 4) n := by
          apply readWords32_write32_outside
          · rw [cursorStep]; omega
          · change 1048576 ≤ (cursor + 4).toNat ∨ (cursor + 4).toNat + 4 * n ≤ 1048572
            rw [cursorStep]; omega
        refine ⟨trace ++ tail, finalStore, ?_, ?_, ?_, ?_⟩
        · have combined := execution.trans tailExecution
          rw [advance_cursor] at combined
          convert combined using 1
          omega
        · simp only [List.length_append, length, tailLength]
          omega
        · rw [sourcePreserved, next_output] at output
          simpa [Mem.readWords32, Spec.encodeValues, Spec.u32Codec,
            WordCodec.serialize_cons, List.append_assoc] using output
        · simpa only [next_pages] using pages

/-- Caller-framed output execution with exact work and canonical serialized
bytes. The continuation, arity, remainder, outer control frames, and call
frames are identical at entry and resumption. Only the loop's own entry and
exit contribute overhead, so the cost is `26*n + 2`, with `22*n + 2` steps. -/
theorem output_loop_segment_serializes
    (n : Nat) (hpositive : 0 < n)
    (store : MachineStore Universal.State) (aux : Aux) (cursor : UInt32)
    (ctx : OutputContext)
    (hmodule : store.runtime.currentModule = Project.Mergesort.module)
    (hhost : store.runtime.currentHost = Universal.envFor Project.Mergesort.module)
    (hcount : 4 * n < UInt32.size)
    (haddress : cursor.toNat + 4 * n ≤ UInt32.size)
    (hread : cursor.toNat + 4 * n ≤ store.wasm.mem.pages * 65536)
    (hframe : 1048576 ≤ store.wasm.mem.pages * 65536)
    (hdisjoint : 1048576 ≤ cursor.toNat ∨ cursor.toNat + 4 * n ≤ 1048572) :
    ∃ trace finalStore,
      CostedSteps work (loopEntry store aux cursor n ctx) trace
        (loopResume finalStore aux (cursor + UInt32.ofNat (4 * n)) ctx) (26 * n + 2) ∧
      trace.length = 22 * n + 2 ∧
      finalStore.wasm.host.stdio.output = store.wasm.host.stdio.output ++
        Spec.encodeValues (store.wasm.mem.readWords32 cursor n) ∧
      finalStore.wasm.mem.pages = store.wasm.mem.pages := by
  have resolved : store.runtime.currentHost.funcs[1]? = some writeHost := by
    rw [hhost]
    exact writeHost_resolves Project.Mergesort.module 1 (by decide) rfl
  obtain ⟨trace, finalStore, body, length, output, pages⟩ :=
    loop_segment_serializes n hpositive store aux cursor ctx
      hmodule resolved hcount haddress hread hframe hdisjoint
  have entry : CostedSteps work (loopEntry store aux cursor n ctx)
      [.instruction (.loop 0 0 outputBody)]
      (loopHead store aux cursor (UInt32.ofNat (4 * n)) ctx) 1 :=
    CostedSteps.single Step.loop
  refine ⟨.instruction (.loop 0 0 outputBody) :: trace, finalStore, ?_, ?_, output, pages⟩
  · have combined := entry.trans body
    rw [show 1 + (26 * n + 1) = 26 * n + 2 by omega] at combined
    exact combined
  · simp only [List.length_cons, length]

/-- Closed execution of the extracted output loop under the actual Universal
host. For `n > 0` it returns normally after exactly `22*n + 3` transitions,
charges `26*n + 3` work units, writes `4*n` bytes, and leaves page count fixed.
This starts at the loop instruction, with its already-initialized locals; it
is not a bound for the enclosing driver or named export. -/
theorem output_loop_exact_cost
    (n : Nat) (hpositive : 0 < n)
    (store : MachineStore Universal.State) (aux : Aux) (cursor : UInt32)
    (hmodule : store.runtime.currentModule = Project.Mergesort.module)
    (hhost : store.runtime.currentHost = Universal.envFor Project.Mergesort.module)
    (hcount : 4 * n < UInt32.size)
    (haddress : cursor.toNat + 4 * n ≤ UInt32.size)
    (hread : cursor.toNat + 4 * n ≤ store.wasm.mem.pages * 65536)
    (hframe : 1048576 ≤ store.wasm.mem.pages * 65536) :
    ∃ trace finalStore,
      CostedSteps work (loopEntry store aux cursor n) trace
        ⟨.done [], finalStore⟩ (26 * n + 3) ∧
      trace.length = 22 * n + 3 ∧
      finalStore.wasm.host.stdio.output.length = store.wasm.host.stdio.output.length + 4 * n ∧
      finalStore.wasm.mem.pages = store.wasm.mem.pages := by
  have resolved : store.runtime.currentHost.funcs[1]? = some writeHost := by
    rw [hhost]
    exact writeHost_resolves Project.Mergesort.module 1 (by decide) rfl
  obtain ⟨trace, finalStore, body, length, outputLength, pages⟩ :=
    loop_exact_cost n hpositive store aux cursor hmodule resolved hcount haddress hread hframe
  have entry : CostedSteps work (loopEntry store aux cursor n)
      [.instruction (.loop 0 0 outputBody)]
      (loopHead store aux cursor (UInt32.ofNat (4 * n))) 1 :=
    CostedSteps.single Step.loop
  refine ⟨.instruction (.loop 0 0 outputBody) :: trace, finalStore, ?_, ?_, outputLength, pages⟩
  · have combined := entry.trans body
    rw [show 1 + (26 * n + 2) = 26 * n + 3 by omega] at combined
    exact combined
  · simp only [List.length_cons, length]

/-- Compatibility bridge for arbitrary functional specifications, such as
ones obtained from an existing Iris proof, on this exact costed execution.
The concrete serialization property is proved separately by
`output_loop_segment_serializes`.
The heap-owning driver integration is provided by
`OutputResources.output_resources`; this generic bridge keeps its functional
adequacy premise explicit. -/
theorem output_loop_with_post
    (n : Nat) (hpositive : 0 < n)
    (store : MachineStore Universal.State) (aux : Aux) (cursor : UInt32)
    (hmodule : store.runtime.currentModule = Project.Mergesort.module)
    (hhost : store.runtime.currentHost = Universal.envFor Project.Mergesort.module)
    (hcount : 4 * n < UInt32.size)
    (haddress : cursor.toNat + 4 * n ≤ UInt32.size)
    (hread : cursor.toNat + 4 * n ≤ store.wasm.mem.pages * 65536)
    (hframe : 1048576 ≤ store.wasm.mem.pages * 65536)
    (post : List Value → MachineStore Universal.State → Prop)
    (functional : PartiallyMeets (loopEntry store aux cursor n) post) :
    ∃ trace finalStore,
      CostedSteps work (loopEntry store aux cursor n) trace
        ⟨.done [], finalStore⟩ (26 * n + 3) ∧
      trace.length = 22 * n + 3 ∧ post [] finalStore := by
  obtain ⟨trace, finalStore, execution, length, _outputLength, _pages⟩ :=
    output_loop_exact_cost n hpositive store aux cursor
      hmodule hhost hcount haddress hread hframe
  exact ⟨trace, finalStore, execution, length, execution.meets_post functional⟩

private def testStore : MachineStore Universal.State :=
  let m := Project.Mergesort.module
  { runtime := { instances := #[{ module := m, host := Universal.envFor m }], entry := ⟨0⟩ }
    wasm := { mem := ((Mem.empty 17).write32 1024 7).write32 1028 9, globals := ⟨[]⟩, host := default } }

private def testAux : Aux :=
  ⟨.i32 0, .i32 1024, .i32 0, .i32 0, .i32 0, .i32 0, .i32 2, .i32 0⟩

/-- The generated two-iteration loop has 47 transitions and 55 work units. -/
theorem two_words_cost :
    ∃ trace finalStore,
      CostedSteps work (loopEntry testStore testAux 1024 2) trace
        ⟨.done [], finalStore⟩ 55 ∧ trace.length = 47 ∧
      finalStore.wasm.host.stdio.output.length = 8 := by
  obtain ⟨trace, finalStore, execution, length, outputLength, _pages⟩ :=
    output_loop_exact_cost 2 (by decide) testStore testAux 1024
      rfl rfl (by decide) (by decide) (by decide) (by decide)
  exact ⟨trace, finalStore, execution, length, outputLength⟩

/-- Independent reduction through Talos's existing executable small-step
runner exercises the taken and final branches and the real output bytes. -/
theorem two_words_runner :
    (runSteps 47 (loopEntry testStore testAux 1024 2)).result.values? = some [] ∧
    (runSteps 47 (loopEntry testStore testAux 1024 2)).result.finalConfig?.map
      (fun final => final.store.wasm.host.stdio.output) = some [7, 0, 0, 0, 9, 0, 0, 0] := by
  exact ⟨rfl, rfl⟩

private def testContext : OutputContext :=
  { continuation := [.unreachable], arity := 1, remainder := [.i32 19]
    controls :=
      [{ kind := .block, paramArity := 0, resultArity := 1,
         body := [.nop], continuation := [.nop], belowStack := [.i32 61] }]
    calls :=
      [{ locals := ⟨[.i32 17], [], [.i32 31]⟩, continuation := [.nop],
         resultArity := 1, callerRemainder := [.i32 41], control := [],
         returningInstance := ⟨0⟩ }] }

/-- A nonempty caller context receives exactly the same source serialization
after 46 transitions and 54 work units. Its unreachable continuation has not
run, and its outer control/call frames remain present. -/
theorem two_words_context_cost :
    ∃ trace finalStore,
      CostedSteps work (loopEntry testStore testAux 1024 2 testContext) trace
        (loopResume finalStore testAux 1032 testContext) 54 ∧ trace.length = 46 ∧
      finalStore.wasm.host.stdio.output = [7, 0, 0, 0, 9, 0, 0, 0] := by
  obtain ⟨trace, finalStore, execution, length, output, _pages⟩ :=
    output_loop_segment_serializes 2 (by decide) testStore testAux 1024 testContext
      rfl rfl (by decide) (by decide) (by decide) (by decide) (by decide)
  exact ⟨trace, finalStore, execution, length, output⟩

/-- Existing-runner check of the exact caller-framed endpoint. At 46 steps
the loop has resumed its caller; one further step executes the caller's trap.
That step is deliberately outside the certified output-phase budget. -/
theorem two_words_context_runner :
    (runSteps 46 (loopEntry testStore testAux 1024 2 testContext)).result =
      .outOfFuel (loopResume (nextStore (nextStore testStore 1024) 1028)
        testAux 1032 testContext) ∧
    (runSteps 47 (loopEntry testStore testAux 1024 2 testContext)).result.trapReason? =
      some .unreachable := by
  exact ⟨rfl, rfl⟩

end Project.Mergesort.OutputCost
