import Project.Mergesort.SortProof

/-!
# Structural contracts for the generated stream wrapper

The exported Rust driver is local `func3` (absolute function index 6).  This
file proves the host-state transfers used by the outcome-sensitive stream
contracts and records the generated support-function indices they call.
-/

namespace Project.Mergesort.WrapperProof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep

def frameSize : UInt32 := 272
def initialStackTop : UInt32 := 1048576
def frame : UInt32 := initialStackTop - frameSize
def chunk : UInt32 := frame + 12
def heapBase : UInt32 := 1049536

def readHost : HostFn Universal.State :=
  (Universal.registry.entryFor Project.Mergesort.module.imports[0]).fn

def writeHost : HostFn Universal.State :=
  (Universal.registry.entryFor Project.Mergesort.module.imports[1]).fn

def oomHost : HostFn Universal.State :=
  (Universal.registry.entryFor Project.Mergesort.module.imports[2]).fn

def stdioLens : HostLens Universal.State StdIO.State :=
  { get := Universal.State.stdio
    set := fun whole part => { whole with stdio := part } }

def oomLens : HostLens Universal.State OOM.State :=
  { get := Universal.State.oom
    set := fun whole part => { whole with oom := part } }

theorem readHost_eq : readHost = StdIO.readHost.lift stdioLens := by rfl

theorem writeHost_eq : writeHost = StdIO.writeHost.lift stdioLens := by rfl

theorem oomHost_eq : oomHost = OOM.oomHost.lift oomLens := by rfl

theorem readHost_resolves :
    (Universal.envFor Project.Mergesort.module).funcs[0]? = some readHost := by
  exact Universal.registry.envFor_getElem? Project.Mergesort.module (by decide)

theorem writeHost_resolves :
    (Universal.envFor Project.Mergesort.module).funcs[1]? = some writeHost := by
  exact Universal.registry.envFor_getElem? Project.Mergesort.module (by decide)

theorem oomHost_resolves :
    (Universal.envFor Project.Mergesort.module).funcs[2]? = some oomHost := by
  exact Universal.registry.envFor_getElem? Project.Mergesort.module (by decide)

theorem readHost_invoke_of_bound
    (store : Store Universal.State) (length pointer : UInt32)
    (hbound : pointer.toNat +
      (store.host.stdio.input.take length.toNat).length ≤
        store.mem.pages * 65536) :
    readHost.invoke store [.i32 length, .i32 pointer] =
      .Return [.i32 (UInt32.ofNat
        (store.host.stdio.input.take length.toNat).length)]
        { store with
          mem := store.mem.writeBytes pointer.toNat
            (store.host.stdio.input.take length.toNat)
          host := { store.host with
            stdio :=
              { input := store.host.stdio.input.drop
                  (store.host.stdio.input.take length.toNat).length
                output := store.host.stdio.output } } } := by
  rw [readHost_eq]
  simp only [HostFn.lift, StdIO.readHost, StdIO.readResult, Store.focus,
    Store.mapHost, stdioLens]
  rw [if_pos]
  · rfl
  · exact decide_eq_true hbound

theorem writeHost_invoke_of_bound
    (store : Store Universal.State) (length pointer : UInt32)
    (hbound : pointer.toNat + length.toNat ≤
      store.mem.pages * 65536) :
    writeHost.invoke store [.i32 length, .i32 pointer] =
      .Return []
        { store with
          host := { store.host with
            stdio :=
              { input := store.host.stdio.input
                output := store.host.stdio.output ++
                  store.mem.readBytes pointer.toNat length.toNat } } } := by
  rw [writeHost_eq]
  simp only [HostFn.lift, StdIO.writeHost, StdIO.writeResult, Store.focus,
    Store.mapHost, stdioLens]
  rw [if_pos]
  · rfl
  · exact decide_eq_true hbound

theorem oomHost_invoke (store : Store Universal.State) :
    oomHost.invoke store [] =
      .Trap
        { store with
          host := { store.host with oom := { raised := true } } }
        OOM.trapMessage := by
  rw [oomHost_eq]
  rfl

def afterWrite (host : Universal.State) (bytes : List UInt8) :
    Universal.State :=
  { host with
    stdio :=
      { input := host.stdio.input
        output := host.stdio.output ++ bytes } }

theorem writeTransfer
    [WasmSmallStepGS hlc Universal.State]
    (host : Universal.State) (pointer length : UInt32)
    (bytes : List UInt8)
    (hlength : length.toNat = bytes.length)
    (hpos : 0 < bytes.length)
    (hnowrap : pointer.toNat + bytes.length < UInt32.size)
    (store : MachineStore Universal.State) (ns : Nat)
    (obs : List StepKind) (nt : Nat)
    (_hmodule : store.runtime.currentModule = Project.Mergesort.module)
    (results : List Value) (postWasm : Store Universal.State)
    (hinvoke : writeHost.invoke store.wasm [.i32 length, .i32 pointer] =
      .Return results postWasm) :
    (hostStateOwn host ∗ pointsToBytes 0 pointer bytes) ∗
      stateInterp (GF := WasmHeapGF Universal.State) store ns obs nt ==∗
    (⌜results = []⌝ ∗ hostStateOwn (afterWrite host bytes) ∗
      pointsToBytes 0 pointer bytes) ∗
      stateInterp (GF := WasmHeapGF Universal.State)
        { store with wasm := postWasm } ns obs nt := by
  iintro ⟨⟨Hhost, Hbytes⟩, Hstate⟩
  ihave %hhostEq : ⌜store.wasm.host = host⌝ $$ [Hstate Hhost]
  · iapply stateInterp_host_agree store ns obs nt host
    iframe Hstate Hhost
  ihave %hfacts :
      ⌜∀ i b, bytes[i]? = some b →
        store.wasm.mem.read8 (pointer + UInt32.ofNat i) = b ∧
        (pointer + UInt32.ofNat i).toNat <
          store.wasm.mem.pages * 65536⌝ $$ [Hstate Hbytes]
  · imod stateInterp_pointsToBytes_agree store ns obs nt pointer bytes $$
        [$Hstate $Hbytes] with %hfacts
    ipureexact hfacts
  have hbound : pointer.toNat + length.toNat ≤
      store.wasm.mem.pages * 65536 := by
    rw [hlength]
    exact pointsToBytes_facts_bound hfacts hpos hnowrap
  have hread : store.wasm.mem.readBytes pointer.toNat length.toNat = bytes := by
    rw [hlength]
    apply pointsToBytes_facts_readBytes
    · intro i b hb
      exact (hfacts i b hb).1
    · exact hnowrap
  have hconcrete := writeHost_invoke_of_bound store.wasm length pointer hbound
  rw [hconcrete] at hinvoke
  have hresults := HostResult.Return.inj hinvoke
  have hresultValues : results = [] := hresults.1.symm
  have hpost : postWasm =
      { store.wasm with
        host := { store.wasm.host with
          stdio :=
            { input := store.wasm.host.stdio.input
              output := store.wasm.host.stdio.output ++ bytes } } } := by
    rw [← hresults.2]
    simp only [hread]
  subst results
  subst postWasm
  ihave HhostActual : hostStateOwn store.wasm.host $$ [Hhost]
  · rw [hhostEq]
    iexact Hhost
  imod stateInterp_host_set store ns obs nt (afterWrite host bytes) $$
      [$Hstate $HhostActual] with ⟨Hstate, Hhost⟩
  imodintro
  isplitl [Hhost Hbytes]
  · isplitl_pureexact rfl
    · isplitl_exact Hhost
      · iexact Hbytes
  · isimp only [afterWrite] at Hstate
    rw [hhostEq]
    iexact Hstate

def afterRead (host : Universal.State) (count : Nat) : Universal.State :=
  { host with
    stdio :=
      { input := host.stdio.input.drop count
        output := host.stdio.output } }

theorem readTransfer
    [WasmSmallStepGS hlc Universal.State]
    (host : Universal.State) (pointer length : UInt32)
    (buffer : List UInt8)
    (hlength : buffer.length = length.toNat)
    (hpos : 0 < buffer.length)
    (hnowrap : pointer.toNat + buffer.length < UInt32.size)
    (store : MachineStore Universal.State) (ns : Nat)
    (obs : List StepKind) (nt : Nat)
    (_hmodule : store.runtime.currentModule = Project.Mergesort.module)
    (results : List Value) (postWasm : Store Universal.State)
    (hinvoke : readHost.invoke store.wasm [.i32 length, .i32 pointer] =
      .Return results postWasm) :
    (hostStateOwn host ∗ pointsToBytes 0 pointer buffer) ∗
      stateInterp (GF := WasmHeapGF Universal.State) store ns obs nt ==∗
    (⌜results = [.i32 (UInt32.ofNat
        (host.stdio.input.take length.toNat).length)]⌝ ∗
      hostStateOwn
        (afterRead host (host.stdio.input.take length.toNat).length) ∗
      pointsToBytes 0 pointer
        (host.stdio.input.take length.toNat ++
          buffer.drop (host.stdio.input.take length.toNat).length)) ∗
      stateInterp (GF := WasmHeapGF Universal.State)
        { store with wasm := postWasm } ns obs nt := by
  let incoming := host.stdio.input.take length.toNat
  iintro ⟨⟨Hhost, Hbuffer⟩, Hstate⟩
  ihave %hhostEq : ⌜store.wasm.host = host⌝ $$ [Hstate Hhost]
  · iapply stateInterp_host_agree store ns obs nt host
    iframe Hstate Hhost
  ihave %hfacts :
      ⌜∀ i b, buffer[i]? = some b →
        store.wasm.mem.read8 (pointer + UInt32.ofNat i) = b ∧
        (pointer + UInt32.ofNat i).toNat <
          store.wasm.mem.pages * 65536⌝ $$ [Hstate Hbuffer]
  · imod stateInterp_pointsToBytes_agree store ns obs nt pointer buffer $$
        [$Hstate $Hbuffer] with %hfacts
    ipureexact hfacts
  have hbufferBound : pointer.toNat + buffer.length ≤
      store.wasm.mem.pages * 65536 :=
    pointsToBytes_facts_bound hfacts hpos hnowrap
  have hincomingLength : incoming.length ≤ buffer.length := by
    dsimp only [incoming]
    rw [hlength]
    exact List.length_take_le _ _
  have hincomingBound : pointer.toNat + incoming.length ≤
      store.wasm.mem.pages * 65536 := by omega
  have hincomingNoWrap : pointer.toNat + incoming.length < UInt32.size := by
    omega
  have hphysicalIncoming :
      store.wasm.host.stdio.input.take length.toNat = incoming := by
    rw [hhostEq]
  have hconcrete := readHost_invoke_of_bound store.wasm length pointer (by
    rw [hphysicalIncoming]
    exact hincomingBound)
  rw [hconcrete] at hinvoke
  have hresults := HostResult.Return.inj hinvoke
  have hresultValues : results =
      [.i32 (UInt32.ofNat incoming.length)] := by
    rw [← hresults.1]
    rw [hphysicalIncoming]
  have hpost : postWasm =
      { store.wasm with
        mem := store.wasm.mem.writeBytes pointer.toNat incoming
        host := { store.wasm.host with
          stdio :=
            { input := store.wasm.host.stdio.input.drop incoming.length
              output := store.wasm.host.stdio.output } } } := by
    rw [← hresults.2]
    simp only [hphysicalIncoming]
  subst results
  subst postWasm
  have hprefixLength : (buffer.take incoming.length).length = incoming.length := by
    rw [List.length_take_of_le hincomingLength]
  ihave Hparts :
      pointsToBytes 0 pointer (buffer.take incoming.length) ∗
      pointsToBytes 0
        (pointer + UInt32.ofNat (buffer.take incoming.length).length)
        (buffer.drop incoming.length) $$ [Hbuffer]
  · iapply (pointsToBytes_append 0 pointer
      (buffer.take incoming.length) (buffer.drop incoming.length)).mp
    rw [List.take_append_drop]
    iexact Hbuffer
  icases Hparts with ⟨Hprefix, Hsuffix⟩
  isimp only [hprefixLength] at Hsuffix
  imod stateInterp_write_bytes store ns obs nt pointer
      (buffer.take incoming.length) incoming hprefixLength
      hincomingBound hincomingNoWrap $$ [$Hstate $Hprefix] with
      ⟨Hstate, Hprefix⟩
  let memoryStore : MachineStore Universal.State :=
    { store with wasm :=
        { store.wasm with mem :=
            store.wasm.mem.writeBytes pointer.toNat incoming } }
  have hmemoryHost : memoryStore.wasm.host = host := by
    dsimp only [memoryStore]
    exact hhostEq
  ihave HhostActual : hostStateOwn memoryStore.wasm.host $$ [Hhost]
  · rw [hmemoryHost]
    iexact Hhost
  imod stateInterp_host_set memoryStore ns obs nt
      (afterRead host incoming.length) $$ [$Hstate $HhostActual] with
      ⟨Hstate, Hhost⟩
  ihave Hbuffer :
      pointsToBytes 0 pointer
        (incoming ++ buffer.drop incoming.length) $$ [Hprefix Hsuffix]
  · iapply (pointsToBytes_append 0 pointer incoming
      (buffer.drop incoming.length)).mpr
    isplitl_exact Hprefix
    · iexact Hsuffix
  imodintro
  isplitl [Hhost Hbuffer]
  · isplitl_pureexact rfl
    · isplitl_exact Hhost
      · iexact Hbuffer
  · isimp only [memoryStore, afterRead] at Hstate
    rw [hhostEq]
    iexact Hstate

def afterOom (host : Universal.State) : Universal.State :=
  { host with oom := { raised := true } }

theorem oomTransfer
    [WasmSmallStepGS hlc Universal.State]
    (host : Universal.State)
    (store : MachineStore Universal.State) (ns : Nat)
    (obs : List StepKind) (nt : Nat)
    (_hmodule : store.runtime.currentModule = Project.Mergesort.module)
    (postWasm : Store Universal.State) (message : String)
    (hinvoke : oomHost.invoke store.wasm [] = .Trap postWasm message) :
    hostStateOwn host ∗
      stateInterp (GF := WasmHeapGF Universal.State) store ns obs nt ==∗
    (⌜message = OOM.trapMessage⌝ ∗ hostStateOwn (afterOom host)) ∗
      stateInterp (GF := WasmHeapGF Universal.State)
        { store with wasm := postWasm } ns obs nt := by
  iintro ⟨Hhost, Hstate⟩
  ihave %hhostEq : ⌜store.wasm.host = host⌝ $$ [Hstate Hhost]
  · iapply stateInterp_host_agree store ns obs nt host
    iframe Hstate Hhost
  have hconcrete := oomHost_invoke store.wasm
  rw [hconcrete] at hinvoke
  have hresult := HostResult.Trap.inj hinvoke
  have hpost : postWasm =
      { store.wasm with
        host := { store.wasm.host with oom := { raised := true } } } :=
    hresult.1.symm
  have hmessage : message = OOM.trapMessage := hresult.2.symm
  subst postWasm
  subst message
  ihave HhostActual : hostStateOwn store.wasm.host $$ [Hhost]
  · rw [hhostEq]
    iexact Hhost
  imod stateInterp_host_set store ns obs nt (afterOom host) $$
      [$Hstate $HhostActual] with ⟨Hstate, Hhost⟩
  imodintro
  isplitl [Hhost]
  · isplitl_pureexact rfl
    · iexact Hhost
  · isimp only [afterOom] at Hstate
    rw [hhostEq]
    iexact Hstate

theorem func4_index : Project.Mergesort.module.funcs[4]? =
    some Project.Mergesort.func4Def := by rfl

theorem func6_index : Project.Mergesort.module.funcs[6]? =
    some Project.Mergesort.func6Def := by rfl

theorem func7_index : Project.Mergesort.module.funcs[7]? =
    some Project.Mergesort.func7Def := by rfl

theorem func10_index : Project.Mergesort.module.funcs[10]? =
    some Project.Mergesort.func10Def := by rfl

theorem func11_index : Project.Mergesort.module.funcs[11]? =
    some Project.Mergesort.func11Def := by rfl

end Project.Mergesort.WrapperProof
