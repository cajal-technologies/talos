import Project.Mergesort.OutputCost
import CodeLib.SepLogic.HostMemoryTrace

/-!
# Physical memory effects of the generated stdio wrappers

The generated reader is local `func10`, absolute call 13; the writer is local
`func11`, absolute call 14. Each certificate includes call entry, the generated
operand rearrangement, the concrete Universal host operation, and return to
the original caller. Reads transfer their actual available prefix, including
partial reads and zero bytes at EOF. These are segments of the actual program,
not a guarantee about the caller's subsequent instructions.
-/

namespace Project.Mergesort.StdIOMemoryEffects

open Wasm Wasm.SmallStep Wasm.SmallStep.CostedStdIO

/-- Exact generated reader body and result signature. -/
theorem read_shim_generated :
    func10 = [.localGet 1, .localGet 0, .call 0] ∧
      func10Def.results = [.i32] := ⟨rfl, rfl⟩

def readTrace : List StepKind :=
  [.instruction (.call 13), .instruction (.localGet 1),
    .instruction (.localGet 0), .host 0, .administrative .returnFromCall]

/-- Actual host transfer count; the requested length need not be available. -/
def readCount (store : MachineStore Universal.State) (length : UInt32) : Nat :=
  min length.toNat store.wasm.host.stdio.input.length

def readFinalStore (store : MachineStore Universal.State) (length pointer : UInt32) :
    MachineStore Universal.State :=
  { store with wasm := readStore store.wasm length pointer }

def writeFinalStore (store : MachineStore Universal.State) (length pointer : UInt32) :
    MachineStore Universal.State :=
  { store with wasm := writeStore store.wasm length pointer }

/-- The returned count is exact in UInt32, including a maximal request. -/
theorem read_count_toNat (store : MachineStore Universal.State) (length : UInt32) :
    (UInt32.ofNat (readCount store length)).toNat = readCount store length := by
  apply UInt32.toNat_ofNat_of_lt'
  have hlength := length.toBitVec.isLt
  change length.toNat < UInt32.size at hlength
  exact lt_of_le_of_lt (min_le_left _ _) hlength

/-- A successful actual call 13 returns its transfer count and preserves all
caller frames. Its physical bound covers the bytes actually read, not the
possibly larger requested length. -/
theorem read_shim_cost
    (store : MachineStore Universal.State)
    (params localValues values : List Value) (code : Program) (arity : Nat)
    (remainder : List Value) (controls : List ControlFrame) (calls : List CallFrame)
    (length pointer : UInt32)
    (hmodule : store.runtime.currentModule = Project.Mergesort.module)
    (hhost : store.runtime.currentHost.funcs[0]? = some readHost)
    (hbound : pointer.toNat + readCount store length ≤ store.wasm.mem.pages * 65536) :
    CostedSteps work
      ⟨.running ⟨⟨params, localValues, .i32 length :: .i32 pointer :: values⟩,
        .call 13 :: code, arity, remainder, controls, calls⟩, store⟩
      readTrace
      ⟨.running ⟨⟨params, localValues,
          .i32 (UInt32.ofNat (readCount store length)) :: values⟩,
        code, arity, remainder, controls, calls⟩, readFinalStore store length pointer⟩
      (readCount store length + 5) := by
  let caller : CallFrame :=
    { locals := ⟨params, localValues, values⟩, continuation := code,
      resultArity := arity, callerRemainder := remainder, control := controls,
      returningInstance := store.runtime.entry }
  have preExecution : Steps
      ⟨.running ⟨⟨params, localValues, .i32 length :: .i32 pointer :: values⟩,
        .call 13 :: code, arity, remainder, controls, calls⟩, store⟩
      [.instruction (.call 13), .instruction (.localGet 1), .instruction (.localGet 0)]
      ⟨.running ⟨⟨[.i32 pointer, .i32 length], [], [.i32 pointer, .i32 length]⟩,
        [.call 0], 1, [], [], caller :: calls⟩, store⟩ := by
    wasm_steps [(.call (fn := func10Def) (by rw [hmodule]; decide)
      (by rw [hmodule]; rfl)), (.localGet rfl)]
    exact Steps.single (.localGet rfl)
  have prefixCost := preExecution.with_unit_cost (charge := work) (by
    intro before kind after member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> rfl)
  have transfer := read_call_costed store 0 [.i32 pointer, .i32 length] [] [] []
    1 [] [] (caller :: calls) length pointer
    (by rw [hmodule]; decide) (by simpa only [hmodule] using
      (show Project.Mergesort.module.imports[0] = StdIO.imports[0] from rfl)) hhost
    (by simpa only [List.length_take, readCount] using hbound)
  have suffix : CostedSteps work
      ⟨.running ⟨⟨[.i32 pointer, .i32 length], [],
          [.i32 (UInt32.ofNat (readCount store length))]⟩,
        [], 1, [], [], caller :: calls⟩, readFinalStore store length pointer⟩
      [.administrative .returnFromCall]
      ⟨.running ⟨⟨params, localValues,
          .i32 (UInt32.ofNat (readCount store length)) :: values⟩,
        code, arity, remainder, controls, calls⟩, readFinalStore store length pointer⟩ 1 :=
    CostedSteps.single (.returnFromCallFallthrough rfl)
  simp only [List.length_take] at transfer
  convert prefixCost.trans (transfer.trans suffix) using 1 <;>
    simp [readTrace, readCount]
  omega

/-- A successful actual call 14 uses the already checked output wrapper
certificate and leaves the exact memory object unchanged. -/
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
      OutputCost.writeTrace
      ⟨.running ⟨⟨params, localValues, values⟩, code, arity, remainder, controls, calls⟩,
        writeFinalStore store length pointer⟩ (length.toNat + 5) :=
  OutputCost.write_shim_cost store params localValues values code arity
    remainder controls calls length pointer hmodule hhost hbound

/-- Reading changes only the transferred byte range and the input stream.
The same concrete final store retains the runtime, caps, and physical pages. -/
theorem read_final_effects (store : MachineStore Universal.State) (length pointer : UInt32) :
    (readFinalStore store length pointer).runtime = store.runtime ∧
    (readFinalStore store length pointer).wasm.mem.pages = store.wasm.mem.pages ∧
    (readFinalStore store length pointer).wasm.memoryCaps = store.wasm.memoryCaps ∧
    (readFinalStore store length pointer).wasm.mem =
      store.wasm.mem.writeBytes pointer.toNat (store.wasm.host.stdio.input.take length.toNat) ∧
    (readFinalStore store length pointer).wasm.host =
      { store.wasm.host with stdio :=
        { input := store.wasm.host.stdio.input.drop (readCount store length),
          output := store.wasm.host.stdio.output } } := by
  simp [readFinalStore, readStore, readCount]

/-- Writing preserves the entire memory and appends exactly its requested
bytes to output. The other Universal host components remain unchanged. -/
theorem write_final_effects (store : MachineStore Universal.State) (length pointer : UInt32) :
    (writeFinalStore store length pointer).runtime = store.runtime ∧
    (writeFinalStore store length pointer).wasm.mem = store.wasm.mem ∧
    (writeFinalStore store length pointer).wasm.memoryCaps = store.wasm.memoryCaps ∧
    (writeFinalStore store length pointer).wasm.host =
      { store.wasm.host with stdio :=
        { input := store.wasm.host.stdio.input,
          output := store.wasm.host.stdio.output ++
            store.wasm.mem.readBytes pointer.toNat length.toNat } } :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Every label of the generated reader is admitted by the host-aware trace
rule; the host's actual page preservation is a separate checked premise. -/
theorem read_trace_allowed : ∀ kind ∈ readTrace, HostPrimaryMemoryKind kind := by
  simp [readTrace, HostPrimaryMemoryKind, PrimaryMemoryKind]

theorem write_trace_allowed :
    ∀ kind ∈ OutputCost.writeTrace, HostPrimaryMemoryKind kind := by
  simp [OutputCost.writeTrace, HostPrimaryMemoryKind, PrimaryMemoryKind]

/-- Every actual prefix through the reader's return has exactly its starting
page count. The concrete Universal host is certified; no claim is inferred
from a bare host label, and later caller instructions are outside the bound. -/
theorem read_shim_prefix_pages
    (store : MachineStore Universal.State)
    (params localValues values : List Value) (code : Program) (arity : Nat)
    (remainder : List Value) (controls : List ControlFrame) (calls : List CallFrame)
    (length pointer : UInt32)
    (hmodule : store.runtime.currentModule = Project.Mergesort.module)
    (hhost : store.runtime.currentHost = Universal.envFor Project.Mergesort.module)
    (hbound : pointer.toNat + readCount store length ≤ store.wasm.mem.pages * 65536)
    {prefixTrace : List StepKind} {middle : Config Universal.State}
    (first : Steps
      ⟨.running ⟨⟨params, localValues, .i32 length :: .i32 pointer :: values⟩,
        .call 13 :: code, arity, remainder, controls, calls⟩, store⟩ prefixTrace middle)
    (hlen : prefixTrace.length ≤ 5) :
    middle.store.wasm.mem.pages = store.wasm.mem.pages := by
  have execution := read_shim_cost store params localValues values code arity
    remainder controls calls length pointer hmodule (by
      rw [hhost]
      exact readHost_resolves Project.Mergesort.module 0 (by decide) rfl) hbound
  have pages := execution.erase.primary_pages_at_prefix_with_hosts first
    (by simpa [readTrace] using hlen)
    (by simpa only [hhost] using Universal.envFor_preservesPrimaryPages Project.Mergesort.module)
    read_trace_allowed
  change store.wasm.mem.pages ≤ middle.store.wasm.mem.pages ∧
    middle.store.wasm.mem.pages ≤ (readFinalStore store length pointer).wasm.mem.pages at pages
  rw [(read_final_effects store length pointer).2.1] at pages
  exact Nat.le_antisymm pages.2 pages.1

/-- The writer also preserves pages at every actual prefix up to its return,
including the concrete output transfer and arbitrary surrounding caller state. -/
theorem write_shim_prefix_pages
    (store : MachineStore Universal.State)
    (params localValues values : List Value) (code : Program) (arity : Nat)
    (remainder : List Value) (controls : List ControlFrame) (calls : List CallFrame)
    (length pointer : UInt32)
    (hmodule : store.runtime.currentModule = Project.Mergesort.module)
    (hhost : store.runtime.currentHost = Universal.envFor Project.Mergesort.module)
    (hbound : pointer.toNat + length.toNat ≤ store.wasm.mem.pages * 65536)
    {prefixTrace : List StepKind} {middle : Config Universal.State}
    (first : Steps
      ⟨.running ⟨⟨params, localValues, .i32 length :: .i32 pointer :: values⟩,
        .call 14 :: code, arity, remainder, controls, calls⟩, store⟩ prefixTrace middle)
    (hlen : prefixTrace.length ≤ 5) :
    middle.store.wasm.mem.pages = store.wasm.mem.pages := by
  have execution := write_shim_cost store params localValues values code arity
    remainder controls calls length pointer hmodule (by
      rw [hhost]
      exact writeHost_resolves Project.Mergesort.module 1 (by decide) rfl) hbound
  have pages := execution.erase.primary_pages_at_prefix_with_hosts first
    (by simpa [OutputCost.writeTrace] using hlen)
    (by simpa only [hhost] using Universal.envFor_preservesPrimaryPages Project.Mergesort.module)
    write_trace_allowed
  change store.wasm.mem.pages ≤ middle.store.wasm.mem.pages ∧
    middle.store.wasm.mem.pages ≤ store.wasm.mem.pages at pages
  exact Nat.le_antisymm pages.2 pages.1

private def testStore (input : List UInt8) : MachineStore Universal.State :=
  let m := Project.Mergesort.module
  { runtime := { instances := #[{ module := m, host := Universal.envFor m }], entry := ⟨0⟩ }
    wasm := { mem := (Mem.empty 1).write8 65533 99, globals := ⟨[]⟩, host := { stdio := { input := input, output := [91] } }, memoryCaps := [Module.memoryHardCap] } }

private def testCall (store : MachineStore Universal.State) (index : Nat)
    (length pointer : UInt32) : Config Universal.State :=
  ⟨.running ⟨⟨[.i32 101], [.i32 102], [.i32 length, .i32 pointer, .i32 103]⟩,
      [.call index, .unreachable], 1, [.i32 104], [], []⟩, store⟩

/-- A 64-byte request with two input bytes transfers only those two, exactly
at the end of a physical page. Caller state and the existing output survive. -/
theorem partial_read_runner :
    (runSteps 5 (testCall (testStore [7, 8]) 13 64 65534)).result =
      .outOfFuel
        ⟨.running ⟨⟨[.i32 101], [.i32 102], [.i32 2, .i32 103]⟩,
          [.unreachable], 1, [.i32 104], [], []⟩,
          readFinalStore (testStore [7, 8]) 64 65534⟩ ∧
    (readFinalStore (testStore [7, 8]) 64 65534).wasm.mem.readBytes 65533 3 = [99, 7, 8] ∧
    (readFinalStore (testStore [7, 8]) 64 65534).wasm.host.stdio.input = [] ∧
    (readFinalStore (testStore [7, 8]) 64 65534).wasm.host.stdio.output = [91] :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- EOF and a zero-length request both return zero, including a pointer just
past the final byte. The ordinary pointer-plus-actual-transfer bound holds. -/
theorem zero_read_runner :
    (runSteps 5 (testCall (testStore []) 13 64 65536)).result.finalConfig?.map
      (fun config => config.expr) =
      some (.running ⟨⟨[.i32 101], [.i32 102], [.i32 0, .i32 103]⟩,
        [.unreachable], 1, [.i32 104], [], []⟩) ∧
    (runSteps 5 (testCall (testStore [7, 8]) 13 0 65536)).result.finalConfig?.map
      (fun config => config.store.wasm.host.stdio.input) = some [7, 8] :=
  ⟨rfl, rfl⟩

/-- The actual writer appends the memory bytes in order. Its caller's trap
is one transition after the wrapper returns and is outside the segment. -/
theorem write_runner :
    (runSteps 5 (testCall (readFinalStore (testStore [7, 8]) 64 65534) 14 2 65534)).result.finalConfig?.map
      (fun config => config.store.wasm.host.stdio.output) = some [91, 7, 8] ∧
    (runSteps 6 (testCall (readFinalStore (testStore [7, 8]) 64 65534) 14 2 65534)).result.trapReason? =
      some .unreachable := ⟨rfl, rfl⟩

end Project.Mergesort.StdIOMemoryEffects
