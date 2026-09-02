import HexDecodeStdio.HostIO
import HexDecodeStdio.AllocatorOperational

namespace Project.HexDecodeStdio

open Wasm Project.HexStdio Project.HexStdio.Spec
open Wasm.SmallStep

/-! Exact small-step adapters for the two universal StdIO calls.  The Iris
lemmas in `HostIO` carry byte ownership; these relational lemmas carry the
concrete store, which is what an enclosing allocator-OOM outcome needs. -/

def universalReadStore (store : MachineStore Universal.State)
    (pointer : UInt32) (bytes : List UInt8) : MachineStore Universal.State :=
  { store with wasm :=
      { store.wasm with
        mem := store.wasm.mem.writeBytes pointer.toNat bytes
        host := afterUniversalRead store.wasm.host bytes.length } }

def readAdapterResultStore (store : MachineStore Universal.State)
    (out pointer : UInt32) (bytes : List UInt8) :
    MachineStore Universal.State :=
  let readStore := universalReadStore store pointer bytes
  { readStore with wasm := { readStore.wasm with mem :=
      ((readStore.wasm.mem.write8 out 4).write32 (out + 4)
        (UInt32.ofNat bytes.length)) } }

@[simp] theorem universalReadStore_runtime
    (store : MachineStore Universal.State) (pointer : UInt32)
    (bytes : List UInt8) :
    (universalReadStore store pointer bytes).runtime = store.runtime := by
  rfl

@[simp] theorem universalReadStore_pages
    (store : MachineStore Universal.State) (pointer : UInt32)
    (bytes : List UInt8) :
    (universalReadStore store pointer bytes).wasm.mem.pages =
      store.wasm.mem.pages := by
  rfl

@[simp] theorem readAdapterResultStore_runtime
    (store : MachineStore Universal.State) (out pointer : UInt32)
    (bytes : List UInt8) :
    (readAdapterResultStore store out pointer bytes).runtime = store.runtime := by
  rfl

@[simp] theorem readAdapterResultStore_pages
    (store : MachineStore Universal.State) (out pointer : UInt32)
    (bytes : List UInt8) :
    (readAdapterResultStore store out pointer bytes).wasm.mem.pages =
      store.wasm.mem.pages := by
  rfl

theorem read_adapter_reaches
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
    (houtBound : out.toNat + 1 ≤ store.wasm.mem.pages * 65536)
    (hout4Bound : out.toNat + 4 + 4 ≤
      store.wasm.mem.pages * 65536) :
    Project.HexDecodeStdio.Reaches
      ({ expr := .running
          ⟨⟨outerParams, outerLocalValues,
              [.i32 length, .i32 pointer, .i32 ignored, .i32 out] ++ stack⟩,
            [.call 19] ++ code, arity, remainder, controls, calls⟩
         store := store } : Config Universal.State)
      ({ expr := .running
          ⟨⟨outerParams, outerLocalValues, stack⟩,
            code, arity, remainder, controls, calls⟩
         store := readAdapterResultStore store out pointer bytes } :
        Config Universal.State) := by
  have hnot : ¬19 < store.runtime.currentModule.imports.length := by
    rw [hmod]
    decide
  have hfn : store.runtime.currentModule.funcs[
      19 - store.runtime.currentModule.imports.length]? = some func16Def := by
    rw [hmod]
    rfl
  apply Reaches.prepend (Step.call hnot hfn)
  simp [func16Def, Function.toLocals, Function.numParams,
    ValueType.zero, func16]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  have himplen : 0 < store.runtime.currentModule.imports.length := by
    rw [hmod]
    decide
  let readImport : ImportDecl :=
    { module := "stdio", name := "read", params := [.i32, .i32],
      results := [.i32] }
  have himpModule : «module».imports[0] = readImport := by
    decide
  have himp : store.runtime.currentModule.imports[0] = readImport := by
    simpa only [hmod] using himpModule
  have hhost : store.runtime.currentHost.funcs[0]? =
      some (StdIO.readHost.lift universalStdIOLens) := by
    rw [henv]
    exact universal_read_function
  have hinvoke :
      (StdIO.readHost.lift universalStdIOLens).invoke store.wasm
          [.i32 length, .i32 pointer] =
        .Return [.i32 (UInt32.ofNat bytes.length)]
          (universalReadStore store pointer bytes).wasm := by
    have hret := universal_read_return store.wasm length pointer bytes
      hbytes hreadBound
    simpa [universalReadStore, afterUniversalRead] using hret
  have hinvoke' :
      (StdIO.readHost.lift universalStdIOLens).invoke store.wasm
          (([.i32 pointer, .i32 length].take readImport.params.length).reverse) =
        .Return [.i32 (UInt32.ofNat bytes.length)]
          (universalReadStore store pointer bytes).wasm := by
    simpa [readImport] using hinvoke
  apply Reaches.prepend
    (Step.callHostReturn (functionIndex := 0)
      (imp := readImport)
      (hostFunction := StdIO.readHost.lift universalStdIOLens)
      (params := [.i32 out, .i32 ignored, .i32 pointer, .i32 length])
      (localValues := []) (values := [.i32 pointer, .i32 length])
      (results := [.i32 (UInt32.ofNat bytes.length)])
      (wasm := (universalReadStore store pointer bytes).wasm)
      (code := func16.drop 3) (arity := 0) (remainder := [])
      (controls := [])
      (calls :=
        { locals := ⟨outerParams, outerLocalValues, stack⟩
          continuation := code
          resultArity := arity
          callerRemainder := remainder
          control := controls
          returningInstance := store.runtime.entry } :: calls)
      himplen himp hhost hinvoke')
  apply Reaches.prepend (Step.localSet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend
    (Step.store8 (address := out) (offset := 0) (by
      simpa [universalReadStore] using houtBound))
  rw [setMemory_eq]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  have hpages :
      ((store.wasm.mem.writeBytes pointer.toNat bytes).write8 out 4).pages =
        store.wasm.mem.pages := by
    rfl
  apply Reaches.prepend
    (Step.store32 (address := out) (offset := 4) (by
      simpa [universalReadStore, hpages] using hout4Bound))
  rw [setMemory_eq]
  apply Reaches.prepend (Step.returnFromCallFallthrough (by
    simp [universalReadStore]))
  simp [readAdapterResultStore, universalReadStore, resumeCaller]
  exact ⟨[], .refl _⟩

def universalWriteStore (store : MachineStore Universal.State)
    (bytes : List UInt8) : MachineStore Universal.State :=
  { store with wasm := { store.wasm with
      host := (afterUniversalWrite store.wasm.host bytes) } }

def writeAdapterResultStore (store : MachineStore Universal.State)
    (out : UInt32) (bytes : List UInt8) (length : UInt32) :
    MachineStore Universal.State :=
  let writeStore := universalWriteStore store bytes
  { writeStore with wasm := { writeStore.wasm with mem :=
      ((writeStore.wasm.mem.write8 out 4).write32 (out + 4) length) } }

@[simp] theorem universalWriteStore_runtime
    (store : MachineStore Universal.State) (bytes : List UInt8) :
    (universalWriteStore store bytes).runtime = store.runtime := by
  rfl

@[simp] theorem universalWriteStore_pages
    (store : MachineStore Universal.State) (bytes : List UInt8) :
    (universalWriteStore store bytes).wasm.mem.pages =
      store.wasm.mem.pages := by
  rfl

@[simp] theorem writeAdapterResultStore_runtime
    (store : MachineStore Universal.State) (out : UInt32)
    (bytes : List UInt8) (length : UInt32) :
    (writeAdapterResultStore store out bytes length).runtime = store.runtime := by
  rfl

@[simp] theorem writeAdapterResultStore_pages
    (store : MachineStore Universal.State) (out : UInt32)
    (bytes : List UInt8) (length : UInt32) :
    (writeAdapterResultStore store out bytes length).wasm.mem.pages =
      store.wasm.mem.pages := by
  rfl

theorem write_adapter_reaches
    (store : MachineStore Universal.State)
    (outerParams outerLocalValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (out ignored pointer length : UInt32) (bytes : List UInt8)
    (hmod : store.runtime.currentModule = «module»)
    (henv : store.runtime.currentHost = Universal.envFor «module»)
    (hlen : bytes.length = length.toNat)
    (hread : store.wasm.mem.readBytes pointer.toNat length.toNat = bytes)
    (hwriteBound : pointer.toNat + length.toNat ≤
      store.wasm.mem.pages * 65536)
    (houtBound : out.toNat + 1 ≤ store.wasm.mem.pages * 65536)
    (hout4Bound : out.toNat + 4 + 4 ≤
      store.wasm.mem.pages * 65536) :
    Reaches
      ({ expr := .running
          ⟨⟨outerParams, outerLocalValues,
              [.i32 length, .i32 pointer, .i32 ignored, .i32 out] ++ stack⟩,
            [.call 20] ++ code, arity, remainder, controls, calls⟩
         store := store } : Config Universal.State)
      ({ expr := .running
          ⟨⟨outerParams, outerLocalValues, stack⟩,
            code, arity, remainder, controls, calls⟩
         store := writeAdapterResultStore store out bytes length } :
        Config Universal.State) := by
  have hnot : ¬20 < store.runtime.currentModule.imports.length := by
    rw [hmod]
    decide
  have hfn : store.runtime.currentModule.funcs[
      20 - store.runtime.currentModule.imports.length]? = some func17Def := by
    rw [hmod]
    rfl
  apply Reaches.prepend (Step.call hnot hfn)
  simp [func17Def, Function.toLocals, Function.numParams, func17]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  have himplen : 1 < store.runtime.currentModule.imports.length := by
    rw [hmod]
    decide
  let writeImport : ImportDecl :=
    { module := "stdio", name := "write", params := [.i32, .i32],
      results := [] }
  have himpModule : «module».imports[1] = writeImport := by
    decide
  have himp : store.runtime.currentModule.imports[1] = writeImport := by
    simpa only [hmod] using himpModule
  have hhost : store.runtime.currentHost.funcs[1]? =
      some (StdIO.writeHost.lift universalStdIOLens) := by
    rw [henv]
    exact universal_write_function
  have hinvoke :
      (StdIO.writeHost.lift universalStdIOLens).invoke store.wasm
          [.i32 length, .i32 pointer] =
        .Return [] (universalWriteStore store bytes).wasm := by
    have hret := universal_write_return store.wasm length pointer bytes
      hlen hread hwriteBound
    simpa [universalWriteStore, afterUniversalWrite] using hret
  have hinvoke' :
      (StdIO.writeHost.lift universalStdIOLens).invoke store.wasm
          (([.i32 pointer, .i32 length].take writeImport.params.length).reverse) =
        .Return [] (universalWriteStore store bytes).wasm := by
    simpa [writeImport] using hinvoke
  have hhostStep :=
    Step.callHostReturn (functionIndex := 1)
      (imp := writeImport)
      (hostFunction := StdIO.writeHost.lift universalStdIOLens)
      (params := [.i32 out, .i32 ignored, .i32 pointer, .i32 length])
      (localValues := []) (values := [.i32 pointer, .i32 length])
      (results := []) (wasm := (universalWriteStore store bytes).wasm)
      (code := func17.drop 3) (arity := 0) (remainder := [])
      (controls := [])
      (calls :=
        { locals := ⟨outerParams, outerLocalValues, stack⟩
          continuation := code
          resultArity := arity
          callerRemainder := remainder
          control := controls
          returningInstance := store.runtime.entry } :: calls)
      himplen himp hhost hinvoke'
  apply Reaches.prepend (by simpa [func17] using hhostStep)
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend Step.const
  apply Reaches.prepend
    (Step.store8 (address := out) (offset := 0) (by
      simpa [universalWriteStore] using houtBound))
  rw [setMemory_eq]
  apply Reaches.prepend (Step.localGet rfl)
  apply Reaches.prepend (Step.localGet rfl)
  have hpages :
      (store.wasm.mem.write8 out 4).pages = store.wasm.mem.pages := by
    rfl
  apply Reaches.prepend
    (Step.store32 (address := out) (offset := 4) (by
      simpa [universalWriteStore, hpages] using hout4Bound))
  rw [setMemory_eq]
  apply Reaches.prepend (Step.returnFromCallFallthrough (by simp))
  simp [writeAdapterResultStore, universalWriteStore, resumeCaller]
  exact ⟨[], .refl _⟩

end Project.HexDecodeStdio
