import CodeLib.SepLogic.CostedSteps
import Interpreter.Wasm.Host.Universal

/-!
# Concrete Universal stdio charges

Charge successful reads by bytes consumed from input and successful writes by
bytes appended to output. The lemmas below connect these observable deltas to
the actual lifted Universal host implementations and authoritative host-call
steps. Partial reads charge their actual transfer, including zero at EOF.

These local execution rules supply the host-transfer terms for composed
whole-program bounds. They do not extract a numerical budget from an Iris
functional proof. Other Universal components leave stdio unchanged.
-/

namespace Wasm.SmallStep.CostedStdIO

def lens : HostLens Universal.State StdIO.State :=
  { get := Universal.State.stdio
    set := fun whole part => { whole with stdio := part } }

def readHost : HostFn Universal.State := StdIO.readHost.lift lens
def writeHost : HostFn Universal.State := StdIO.writeHost.lift lens

/-- Host transfer bytes, determined by the concrete before/after host states.
The index is deliberately irrelevant, so imports may appear in any order. -/
def hostBytes (before : Config Universal.State) (_index : Nat)
    (after : Config Universal.State) : Nat :=
  (before.store.wasm.host.stdio.input.length - after.store.wasm.host.stdio.input.length) +
  (after.store.wasm.host.stdio.output.length - before.store.wasm.host.stdio.output.length)

abbrev work : StepCost Universal.State := byteWork hostBytes

def readStore (store : Store Universal.State) (length pointer : UInt32) :
    Store Universal.State :=
  let bytes := store.host.stdio.input.take length.toNat
  { store with
    mem := store.mem.writeBytes pointer.toNat bytes
    host := { store.host with stdio :=
      { input := store.host.stdio.input.drop bytes.length
        output := store.host.stdio.output } } }

def writeStore (store : Store Universal.State) (length pointer : UInt32) :
    Store Universal.State :=
  { store with host := { store.host with stdio :=
    { input := store.host.stdio.input
      output := store.host.stdio.output ++ store.mem.readBytes pointer.toNat length.toNat } } }

theorem readHost_resolves (m : Module) (index : Nat)
    (hindex : index < m.imports.length)
    (himport : m.imports[index] = StdIO.imports[0]) :
    (Universal.envFor m).funcs[index]? = some readHost := by
  change (Universal.registry.envFor m).funcs[index]? = some readHost
  rw [Universal.registry.envFor_getElem? m hindex, himport]
  rfl

theorem writeHost_resolves (m : Module) (index : Nat)
    (hindex : index < m.imports.length)
    (himport : m.imports[index] = StdIO.imports[1]) :
    (Universal.envFor m).funcs[index]? = some writeHost := by
  change (Universal.registry.envFor m).funcs[index]? = some writeHost
  rw [Universal.registry.envFor_getElem? m hindex, himport]
  rfl

theorem readHost_invoke (store : Store Universal.State) (length pointer : UInt32)
    (hbound : pointer.toNat +
      (store.host.stdio.input.take length.toNat).length ≤ store.mem.pages * 65536) :
    readHost.invoke store [.i32 length, .i32 pointer] =
      .Return [.i32 (UInt32.ofNat (store.host.stdio.input.take length.toNat).length)]
        (readStore store length pointer) := by
  simp only [readHost, HostFn.lift, StdIO.readHost, StdIO.readResult,
    Store.focus, Store.mapHost, lens]
  rw [if_pos]
  · rfl
  · exact decide_eq_true hbound

theorem writeHost_invoke (store : Store Universal.State) (length pointer : UInt32)
    (hbound : pointer.toNat + length.toNat ≤ store.mem.pages * 65536) :
    writeHost.invoke store [.i32 length, .i32 pointer] =
      .Return [] (writeStore store length pointer) := by
  simp only [writeHost, HostFn.lift, StdIO.writeHost, StdIO.writeResult,
    Store.focus, Store.mapHost, lens]
  rw [if_pos]
  · rfl
  · exact decide_eq_true hbound

/-- A successful read charges exactly its actual byte transfer, not its request
size. This equation holds for every caller control state. -/
theorem read_charge (store : MachineStore Universal.State)
    (beforeExpr afterExpr : Expr Universal.State) (index : Nat)
    (length pointer : UInt32) :
    work ⟨beforeExpr, store⟩ (.host index)
      ⟨afterExpr, { store with wasm := readStore store.wasm length pointer }⟩ =
      1 + min length.toNat store.wasm.host.stdio.input.length := by
  simp only [work, byteWork, hostBytes, readStore, List.length_drop, List.length_take,
    Nat.sub_self, Nat.add_zero]
  omega

theorem write_charge (store : MachineStore Universal.State)
    (beforeExpr afterExpr : Expr Universal.State) (index : Nat)
    (length pointer : UInt32) :
    work ⟨beforeExpr, store⟩ (.host index)
      ⟨afterExpr, { store with wasm := writeStore store.wasm length pointer }⟩ =
      1 + length.toNat := by
  simp [work, byteWork, hostBytes, writeStore, Mem.readBytes]

/-- An authoritative call to the concrete Universal reader with arbitrary
frames and import position. The precondition is a physical byte-range bound. -/
theorem read_call_costed
    (store : MachineStore Universal.State) (index : Nat)
    (params localValues values : List Value) (code : Program) (arity : Nat)
    (remainder : List Value) (controls : List ControlFrame) (calls : List CallFrame)
    (length pointer : UInt32)
    (hindex : index < store.runtime.currentModule.imports.length)
    (himport : store.runtime.currentModule.imports[index] = StdIO.imports[0])
    (hhost : store.runtime.currentHost.funcs[index]? = some readHost)
    (hbound : pointer.toNat +
      (store.wasm.host.stdio.input.take length.toNat).length ≤
        store.wasm.mem.pages * 65536) :
    CostedSteps work
      ⟨.running ⟨⟨params, localValues, .i32 pointer :: .i32 length :: values⟩,
        .call index :: code, arity, remainder, controls, calls⟩, store⟩
      [.host index]
      ⟨.running ⟨⟨params, localValues,
        .i32 (UInt32.ofNat (store.wasm.host.stdio.input.take length.toNat).length) :: values⟩,
        code, arity, remainder, controls, calls⟩,
        { store with wasm := readStore store.wasm length pointer }⟩
      (1 + min length.toNat store.wasm.host.stdio.input.length) := by
  have step := Step.callHostReturn
    (params := params) (localValues := localValues)
    (values := .i32 pointer :: .i32 length :: values)
    (code := code) (arity := arity) (remainder := remainder)
    (controls := controls) (calls := calls)
    hindex himport hhost (readHost_invoke store.wasm length pointer hbound)
  simpa [StdIO.imports, read_charge] using CostedSteps.single (charge := work) step

/-- An authoritative call to the concrete Universal writer charges every byte
read from memory and appended to the host's output stream. -/
theorem write_call_costed
    (store : MachineStore Universal.State) (index : Nat)
    (params localValues values : List Value) (code : Program) (arity : Nat)
    (remainder : List Value) (controls : List ControlFrame) (calls : List CallFrame)
    (length pointer : UInt32)
    (hindex : index < store.runtime.currentModule.imports.length)
    (himport : store.runtime.currentModule.imports[index] = StdIO.imports[1])
    (hhost : store.runtime.currentHost.funcs[index]? = some writeHost)
    (hbound : pointer.toNat + length.toNat ≤ store.wasm.mem.pages * 65536) :
    CostedSteps work
      ⟨.running ⟨⟨params, localValues, .i32 pointer :: .i32 length :: values⟩,
        .call index :: code, arity, remainder, controls, calls⟩, store⟩
      [.host index]
      ⟨.running ⟨⟨params, localValues, values⟩,
        code, arity, remainder, controls, calls⟩,
        { store with wasm := writeStore store.wasm length pointer }⟩
      (1 + length.toNat) := by
  have step := Step.callHostReturn
    (params := params) (localValues := localValues)
    (values := .i32 pointer :: .i32 length :: values)
    (code := code) (arity := arity) (remainder := remainder)
    (controls := controls) (calls := calls)
    hindex himport hhost (writeHost_invoke store.wasm length pointer hbound)
  simpa [StdIO.imports, write_charge] using
    CostedSteps.single (charge := work) step

end Wasm.SmallStep.CostedStdIO
