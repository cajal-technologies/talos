import HexDecodeStdio.DecodeSpec
import HexDecodeStdio.MemoryBytes
import HexDecodeStdio.DecodeIterator

namespace Project.HexDecodeStdio

open Wasm Project.HexStdio Project.HexStdio.Spec
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep

variable {hlc : outParam HasLC}

/-- The universal host lens for standard I/O. -/
def universalStdIOLens : HostLens Universal.State StdIO.State :=
  { get := Universal.State.stdio
    set := fun whole part => { whole with stdio := part } }

theorem universal_read_function :
    (Universal.envFor «module»).funcs[0]? =
      some (StdIO.readHost.lift universalStdIOLens) := by
  have hs := universal_env_satisfies.lookup (i := 0) (by decide)
  obtain ⟨_hostFn, _contract, _hfn, _hcontract, _hsound⟩ := hs
  rfl

theorem universal_write_function :
    (Universal.envFor «module»).funcs[1]? =
      some (StdIO.writeHost.lift universalStdIOLens) := by
  have hs := universal_env_satisfies.lookup (i := 1) (by decide)
  obtain ⟨_hostFn, _contract, _hfn, _hcontract, _hsound⟩ := hs
  rfl

theorem universal_write_return
    (store : Store Universal.State) (length pointer : UInt32)
    (bytes : List UInt8)
    (hlen : bytes.length = length.toNat)
    (hread : store.mem.readBytes pointer.toNat length.toNat = bytes)
    (hbound : pointer.toNat + length.toNat ≤ store.mem.pages * 65536) :
    (StdIO.writeHost.lift universalStdIOLens).invoke store
        [.i32 length, .i32 pointer] =
      .Return []
        { store with host :=
            { store.host with stdio :=
                { input := store.host.stdio.input
                  output := store.host.stdio.output ++ bytes } } } := by
  simp only [HostFn.lift, StdIO.writeHost, StdIO.writeResult,
    Store.focus, Store.mapHost, universalStdIOLens]
  rw [if_pos]
  · simp only [Store.unfocus, Store.mapHost]
    rw [hread]
  · simp only [StdIO.rangeInBounds]
    exact decide_eq_true hbound

theorem universal_read_return
    (store : Store Universal.State) (length pointer : UInt32)
    (bytes : List UInt8)
    (hbytes : bytes = store.host.stdio.input.take length.toNat)
    (hbound : pointer.toNat + bytes.length ≤ store.mem.pages * 65536) :
    (StdIO.readHost.lift universalStdIOLens).invoke store
        [.i32 length, .i32 pointer] =
      .Return [.i32 (UInt32.ofNat bytes.length)]
        { store with
          mem := store.mem.writeBytes pointer.toNat bytes
          host :=
            { store.host with stdio :=
                { input := store.host.stdio.input.drop bytes.length
                  output := store.host.stdio.output } } } := by
  subst bytes
  simp only [HostFn.lift, StdIO.readHost, StdIO.readResult,
    Store.focus, Store.mapHost, universalStdIOLens]
  rw [if_pos]
  · rfl
  · simp only [StdIO.rangeInBounds]
    exact decide_eq_true hbound

def afterUniversalWrite (host : Universal.State) (bytes : List UInt8) :
    Universal.State :=
  { host with stdio :=
      { input := host.stdio.input
        output := host.stdio.output ++ bytes } }

def afterUniversalRead (host : Universal.State) (count : Nat) :
    Universal.State :=
  { host with stdio :=
      { input := host.stdio.input.drop count
        output := host.stdio.output } }

theorem universal_write_is_return
    [WasmSmallStepGS hlc Universal.State]
    (host : Universal.State)
    (store : MachineStore Universal.State) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (length pointer : UInt32) (bytes : List UInt8)
    (hlen : bytes.length = length.toNat) (hne : bytes ≠ [])
    (hnowrap : pointer.toNat + bytes.length < UInt32.size) :
    hostStateOwn host ∗ pointsToBytes 0 pointer bytes ∗
        stateInterp (GF := WasmHeapGF Universal.State)
          store steps observations threads ==∗
      hostStateOwn host ∗ pointsToBytes 0 pointer bytes ∗
        stateInterp (GF := WasmHeapGF Universal.State)
          store steps observations threads ∗
        ⌜(StdIO.writeHost.lift universalStdIOLens).invoke store.wasm
            [.i32 length, .i32 pointer] =
          .Return []
            { store.wasm with host :=
                afterUniversalWrite host bytes }⌝ := by
  iintro ⟨Hhost, Hbytes, Hstate⟩
  ihave %hhost : ⌜store.wasm.host = host⌝ $$ [Hstate Hhost]
  · iapply stateInterp_host_agree
    iframe
  ihave %hfacts :
      ⌜∀ i b, bytes[i]? = some b →
          store.wasm.mem.read8 (pointer + UInt32.ofNat i) = b ∧
          (pointer + UInt32.ofNat i).toNat <
            store.wasm.mem.pages * 65536⌝ $$ [Hstate Hbytes]
  · imod stateInterp_pointsToBytes_agree store steps observations threads
      pointer bytes $$ [$Hstate $Hbytes] with %hfacts
    ipureintro
    exact hfacts
  have hread : store.wasm.mem.readBytes pointer.toNat length.toNat = bytes := by
    rw [← hlen]
    apply Mem.readBytes_eq_of_read8
    · intro i hi
      exact (hfacts i bytes[i] (List.getElem?_eq_getElem hi)).1
    · exact hnowrap
  have hbound : pointer.toNat + length.toNat ≤
      store.wasm.mem.pages * 65536 := by
    rw [← hlen]
    apply pointsToBytes_facts_bound hfacts
    · exact List.length_pos_of_ne_nil hne
    · simpa only [UInt32.size] using hnowrap
  have hret := universal_write_return store.wasm length pointer bytes
    hlen hread hbound
  imodintro
  isplitl [Hhost]
  · iexact Hhost
  isplitl [Hbytes]
  · iexact Hbytes
  isplitl [Hstate]
  · iexact Hstate
  ipureintro
  simpa only [afterUniversalWrite, hhost] using hret

/-- Ghost-state transfer for a successful universal-host write. -/
theorem universal_write_transfer
    [WasmSmallStepGS hlc Universal.State]
    (host : Universal.State)
    (store : MachineStore Universal.State) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (length pointer : UInt32) (bytes : List UInt8)
    (hlen : bytes.length = length.toNat)
    (hne : bytes ≠ [])
    (hnowrap : pointer.toNat + bytes.length < UInt32.size)
    (results : List Value) (postWasm : Store Universal.State)
    (hinvoke : (StdIO.writeHost.lift universalStdIOLens).invoke store.wasm
      [.i32 length, .i32 pointer] = .Return results postWasm) :
    hostStateOwn host ∗ pointsToBytes 0 pointer bytes ∗
        stateInterp (GF := WasmHeapGF Universal.State)
          store steps observations threads ==∗
      ⌜results = []⌝ ∗
        hostStateOwn (afterUniversalWrite host bytes) ∗
        pointsToBytes 0 pointer bytes ∗
        stateInterp (GF := WasmHeapGF Universal.State)
          { store with wasm := postWasm } steps observations threads := by
  iintro ⟨Hhost, Hbytes, Hstate⟩
  ihave %hhost : ⌜store.wasm.host = host⌝ $$ [Hstate Hhost]
  · iapply stateInterp_host_agree
    iframe
  ihave %hfacts :
      ⌜∀ i b, bytes[i]? = some b →
          store.wasm.mem.read8 (pointer + UInt32.ofNat i) = b ∧
          (pointer + UInt32.ofNat i).toNat <
            store.wasm.mem.pages * 65536⌝ $$ [Hstate Hbytes]
  · imod stateInterp_pointsToBytes_agree store steps observations threads
      pointer bytes $$ [$Hstate $Hbytes] with %hfacts
    ipureintro
    exact hfacts
  have hread : store.wasm.mem.readBytes pointer.toNat length.toNat = bytes := by
    rw [← hlen]
    apply Mem.readBytes_eq_of_read8
    · intro i hi
      exact (hfacts i bytes[i] (List.getElem?_eq_getElem hi)).1
    · exact hnowrap
  have hbound : pointer.toNat + length.toNat ≤
      store.wasm.mem.pages * 65536 := by
    rw [← hlen]
    apply pointsToBytes_facts_bound hfacts
    · exact List.length_pos_of_ne_nil hne
    · simpa only [UInt32.size] using hnowrap
  have hexpected := universal_write_return store.wasm length pointer bytes
    hlen hread hbound
  rw [hexpected] at hinvoke
  have hresults : results = [] := (HostResult.Return.inj hinvoke).1.symm
  have hpost : postWasm =
      { store.wasm with host := afterUniversalWrite host bytes } := by
    have hp := (HostResult.Return.inj hinvoke).2.symm
    simpa only [afterUniversalWrite, hhost] using hp
  subst postWasm
  ihave HhostPhysical : hostStateOwn store.wasm.host $$ [Hhost]
  · rw [hhost]
    iexact Hhost
  imod stateInterp_host_set store steps observations threads
      (afterUniversalWrite host bytes) $$ [$Hstate $HhostPhysical] with
    ⟨Hstate, Hhost⟩
  imodintro
  isplitr
  · ipureintro
    exact hresults
  · iframe

/-- Ghost-state transfer for a successful universal-host read. -/
theorem universal_read_transfer
    [WasmSmallStepGS hlc Universal.State]
    (host : Universal.State)
    (store : MachineStore Universal.State) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (length pointer : UInt32) (oldBytes bytes : List UInt8)
    (hbytes : bytes = host.stdio.input.take length.toNat)
    (hlen : oldBytes.length = bytes.length)
    (hbound : pointer.toNat + bytes.length ≤
      store.wasm.mem.pages * 65536)
    (hnowrap : pointer.toNat + bytes.length < UInt32.size)
    (results : List Value) (postWasm : Store Universal.State)
    (hinvoke : (StdIO.readHost.lift universalStdIOLens).invoke store.wasm
      [.i32 length, .i32 pointer] = .Return results postWasm) :
    hostStateOwn host ∗ pointsToBytes 0 pointer oldBytes ∗
        stateInterp (GF := WasmHeapGF Universal.State)
          store steps observations threads ==∗
      ⌜results = [.i32 (UInt32.ofNat bytes.length)]⌝ ∗
        hostStateOwn (afterUniversalRead host bytes.length) ∗
        pointsToBytes 0 pointer bytes ∗
        stateInterp (GF := WasmHeapGF Universal.State)
          { store with wasm := postWasm } steps observations threads := by
  iintro ⟨Hhost, Hbytes, Hstate⟩
  ihave %hhost : ⌜store.wasm.host = host⌝ $$ [Hstate Hhost]
  · iapply stateInterp_host_agree
    iframe
  have hbytesPhysical : bytes =
      store.wasm.host.stdio.input.take length.toNat := by
    simpa only [hhost] using hbytes
  have hexpected := universal_read_return store.wasm length pointer bytes
    hbytesPhysical hbound
  rw [hexpected] at hinvoke
  have hresults : results = [.i32 (UInt32.ofNat bytes.length)] :=
    (HostResult.Return.inj hinvoke).1.symm
  have hpostRaw := (HostResult.Return.inj hinvoke).2.symm
  have hpost : postWasm =
      { store.wasm with
        mem := store.wasm.mem.writeBytes pointer.toNat bytes
        host := afterUniversalRead host bytes.length } := by
    simpa only [afterUniversalRead, hhost] using hpostRaw
  subst postWasm
  imod stateInterp_writeBytes store steps observations threads pointer
      oldBytes bytes hlen hbound hnowrap $$ [$Hstate $Hbytes] with
    ⟨Hstate, Hbytes⟩
  let memoryStore : MachineStore Universal.State :=
    { store with wasm :=
        { store.wasm with
          mem := store.wasm.mem.writeBytes pointer.toNat bytes } }
  ihave HhostPhysical : hostStateOwn memoryStore.wasm.host $$ [Hhost]
  · simp only [memoryStore]
    rw [hhost]
    iexact Hhost
  imod stateInterp_host_set memoryStore steps observations threads
      (afterUniversalRead host bytes.length) $$
      [$Hstate $HhostPhysical] with ⟨Hstate, Hhost⟩
  imodintro
  isplitr
  · ipureintro
    exact hresults
  · isimp only [memoryStore, afterUniversalRead, hhost] at Hstate
    isplitl [Hhost]
    · iexact Hhost
    isplitl [Hbytes]
    · iexact Hbytes
    rw [hhost]
    iexact Hstate

theorem universal_read_is_return
    [WasmSmallStepGS hlc Universal.State]
    (host : Universal.State)
    (store : MachineStore Universal.State) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (length pointer : UInt32) (oldBytes bytes : List UInt8)
    (hbytes : bytes = host.stdio.input.take length.toNat)
    (hbound : pointer.toNat + bytes.length ≤
      store.wasm.mem.pages * 65536) :
    hostStateOwn host ∗ pointsToBytes 0 pointer oldBytes ∗
        stateInterp (GF := WasmHeapGF Universal.State)
          store steps observations threads ==∗
      hostStateOwn host ∗ pointsToBytes 0 pointer oldBytes ∗
        stateInterp (GF := WasmHeapGF Universal.State)
          store steps observations threads ∗
        ⌜(StdIO.readHost.lift universalStdIOLens).invoke store.wasm
            [.i32 length, .i32 pointer] =
          .Return [.i32 (UInt32.ofNat bytes.length)]
            { store.wasm with
              mem := store.wasm.mem.writeBytes pointer.toNat bytes
              host := afterUniversalRead host bytes.length }⌝ := by
  iintro ⟨Hhost, Hbytes, Hstate⟩
  ihave %hhost : ⌜store.wasm.host = host⌝ $$ [Hstate Hhost]
  · iapply stateInterp_host_agree
    iframe
  have hbytesPhysical : bytes =
      store.wasm.host.stdio.input.take length.toNat := by
    simpa only [hhost] using hbytes
  have hret := universal_read_return store.wasm length pointer bytes
    hbytesPhysical hbound
  imodintro
  isplitl [Hhost]
  · iexact Hhost
  isplitl [Hbytes]
  · iexact Hbytes
  isplitl [Hstate]
  · iexact Hstate
  ipureintro
  simpa only [afterUniversalRead, hhost] using hret

/-- Read transfer while owning the whole destination buffer.  The unread
suffix is framed and the returned prefix is replaced with the host bytes. -/
theorem universal_read_buffer_transfer
    [WasmSmallStepGS hlc Universal.State]
    (host : Universal.State)
    (store : MachineStore Universal.State) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (length pointer : UInt32) (buffer bytes : List UInt8)
    (hbytes : bytes = host.stdio.input.take length.toNat)
    (hbuffer : buffer.length = length.toNat)
    (hlength : length ≠ 0)
    (hnowrap : pointer.toNat + buffer.length < UInt32.size)
    (results : List Value) (postWasm : Store Universal.State)
    (hinvoke : (StdIO.readHost.lift universalStdIOLens).invoke store.wasm
      [.i32 length, .i32 pointer] = .Return results postWasm) :
    hostStateOwn host ∗ pointsToBytes 0 pointer buffer ∗
        stateInterp (GF := WasmHeapGF Universal.State)
          store steps observations threads ==∗
      ⌜results = [.i32 (UInt32.ofNat bytes.length)]⌝ ∗
        hostStateOwn (afterUniversalRead host bytes.length) ∗
        pointsToBytes 0 pointer (bytes ++ buffer.drop bytes.length) ∗
        stateInterp (GF := WasmHeapGF Universal.State)
          { store with wasm := postWasm } steps observations threads := by
  iintro ⟨Hhost, Hbuffer, Hstate⟩
  have hle : bytes.length ≤ buffer.length := by
    rw [hbytes, hbuffer, List.length_take]
    omega
  have hpfxlen : (buffer.take bytes.length).length = bytes.length := by
    simp [List.length_take, hle]
  have hsplit : buffer.take bytes.length ++ buffer.drop bytes.length = buffer :=
    List.take_append_drop bytes.length buffer
  ihave %hfacts :
      ⌜∀ i b, buffer[i]? = some b →
          store.wasm.mem.read8 (pointer + UInt32.ofNat i) = b ∧
          (pointer + UInt32.ofNat i).toNat <
            store.wasm.mem.pages * 65536⌝ $$ [Hstate Hbuffer]
  · imod stateInterp_pointsToBytes_agree store steps observations threads
      pointer buffer $$ [$Hstate $Hbuffer] with %hfacts
    ipureintro
    exact hfacts
  ihave Hsplit : pointsToBytes 0 pointer
      (buffer.take bytes.length ++ buffer.drop bytes.length) $$ [Hbuffer]
  · rw [hsplit]
    iexact Hbuffer
  ihave ⟨Hprefix, Hsuffix⟩ :=
    (pointsToBytes_append 0 pointer (buffer.take bytes.length)
      (buffer.drop bytes.length)).mp $$ Hsplit
  have hphysicalFull : pointer.toNat + buffer.length ≤
      store.wasm.mem.pages * 65536 := by
    apply pointsToBytes_facts_bound hfacts
    · rw [hbuffer]
      apply Nat.pos_of_ne_zero
      intro hz
      apply hlength
      exact UInt32.toNat_inj.mp (by simpa using hz)
    · simpa only [UInt32.size] using hnowrap
  have hphysical : pointer.toNat + bytes.length ≤
      store.wasm.mem.pages * 65536 := by omega
  have hnowrapPrefix : pointer.toNat + bytes.length < UInt32.size := by
    omega
  imod universal_read_transfer host store steps observations threads length
      pointer (buffer.take bytes.length) bytes hbytes hpfxlen hphysical
      hnowrapPrefix results postWasm hinvoke $$
      [$Hhost $Hprefix $Hstate] with
      ⟨%hresults, Hhost, Hprefix, Hstate⟩
  imodintro
  isplitr
  · ipureintro
    exact hresults
  isplitl [Hhost]
  · iexact Hhost
  isplitl [Hprefix Hsuffix]
  · iapply (pointsToBytes_append 0 pointer bytes
      (buffer.drop bytes.length)).mpr
    isplitl [Hprefix]
    · iexact Hprefix
    · have haddr :
          pointer + UInt32.ofNat (buffer.take bytes.length).length =
            pointer + UInt32.ofNat bytes.length := by rw [hpfxlen]
      rw [← haddr]
      iexact Hsuffix
  · iexact Hstate

/-- The generated four-argument write adapter (module function 20) calls the
universal `stdio.write` import and records its successful result. -/
theorem twp_write_adapter
    [WasmSmallStepGS hlc Universal.State]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Universal.State)}
    (host : Universal.State) (out ignored pointer length : UInt32)
    (bytes : List UInt8) (oldTag : UInt8) (oldCount : UInt32)
    (hlen : bytes.length = length.toNat) (hne : bytes ≠ [])
    (hnowrap : pointer.toNat + bytes.length < UInt32.size)
    (houtCount : Offset32Facts out 4)
    (callerLocals : Locals) (stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame) :
    runtimeModuleOwn ⟨0⟩ «module» ∗
      hostEnvOwn 0 (Universal.envFor «module») ∗
      hostStateOwn host ∗
      pointsToBytes 0 pointer bytes ∗
      pointsTo (GF := WasmHeapGF Universal.State) (H := WasmHeapMap)
        ⟨0, out⟩ (DFrac.own 1) (some oldTag) ∗
      pointsTo_u32 0 (out + 4) oldCount -∗
    (runtimeModuleOwn ⟨0⟩ «module» ∗
      hostStateOwn (afterUniversalWrite host bytes) ∗
      pointsToBytes 0 pointer bytes ∗
      pointsTo (GF := WasmHeapGF Universal.State) (H := WasmHeapMap)
        ⟨0, out⟩ (DFrac.own 1) (some (4 : UInt8)) ∗
      pointsTo_u32 0 (out + 4) length -∗
      WP (.running
        ⟨{ callerLocals with values := stack }, code, arity, remainder,
          controls, calls⟩ : Expr Universal.State) @ s; E [{ Φ }]) -∗
    WP (.running
      ⟨{ callerLocals with values :=
          [.i32 length, .i32 pointer, .i32 ignored, .i32 out] ++ stack },
        [.call 20] ++ code, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Henv, Hhost, Hbytes, Htag, Hcount⟩ Hcont
  simp only [List.singleton_append]
  iapply twp_call «module» 20 func17Def (by decide) rfl ⟨0⟩ $$ Hruntime
  iintro Hruntime
  simp [func17Def, Function.toLocals, Function.numParams,
    ValueType.zero, func17]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply hdtwp_callHost «module» 1
      { module := "stdio", name := "write", params := [.i32, .i32],
        results := [] }
      (StdIO.writeHost.lift universalStdIOLens)
      (by decide) rfl (Universal.envFor «module»)
      universal_write_function
      (iprop(hostStateOwn host ∗ pointsToBytes 0 pointer bytes ∗
        (pointsTo (GF := WasmHeapGF Universal.State) (H := WasmHeapMap)
          ⟨0, out⟩ (DFrac.own 1) (some oldTag)) ∗
        pointsTo_u32 0 (out + 4) oldCount ∗
        (runtimeModuleOwn ⟨0⟩ «module» ∗
          hostStateOwn (afterUniversalWrite host bytes) ∗
          pointsToBytes 0 pointer bytes ∗
          (pointsTo (GF := WasmHeapGF Universal.State) (H := WasmHeapMap)
            ⟨0, out⟩ (DFrac.own 1) (some (4 : UInt8))) ∗
          pointsTo_u32 0 (out + 4) length -∗
          WP (.running
            ⟨{ callerLocals with values := stack }, code, arity, remainder,
              controls, calls⟩ : Expr Universal.State) @ s; E [{ Φ }])))
      (fun results => iprop(⌜results = []⌝ ∗
        hostStateOwn (afterUniversalWrite host bytes) ∗
        pointsToBytes 0 pointer bytes ∗
        (pointsTo (GF := WasmHeapGF Universal.State) (H := WasmHeapMap)
          ⟨0, out⟩ (DFrac.own 1) (some oldTag)) ∗
        pointsTo_u32 0 (out + 4) oldCount ∗
        (runtimeModuleOwn ⟨0⟩ «module» ∗
          hostStateOwn (afterUniversalWrite host bytes) ∗
          pointsToBytes 0 pointer bytes ∗
          (pointsTo (GF := WasmHeapGF Universal.State) (H := WasmHeapMap)
            ⟨0, out⟩ (DFrac.own 1) (some (4 : UInt8))) ∗
          pointsTo_u32 0 (out + 4) length -∗
          WP (.running
            ⟨{ callerLocals with values := stack }, code, arity, remainder,
              controls, calls⟩ : Expr Universal.State) @ s; E [{ Φ }])))
      (iprop(False)) (iprop(False)) ⟨0⟩
      (fun store ns obs nt _ results postWasm hinvoke => by
        iintro ⟨⟨Hhost0, Hbytes0, Htag0, Hcount0, Hcont0⟩,
          Hstate0⟩
        imod universal_write_transfer host store ns obs nt length pointer
          bytes hlen hne hnowrap results postWasm hinvoke $$
          [$Hhost0 $Hbytes0 $Hstate0] with
          ⟨%hresults, Hhost1, Hbytes1, Hstate1⟩
        imodintro
        isplitl [Hhost1 Hbytes1 Htag0 Hcount0 Hcont0]
        · isplitr
          · ipureintro
            exact hresults
          · iframe
        · iexact Hstate1)
      (fun store ns obs nt _ postWasm msg hinvoke => by
        iintro ⟨⟨Hhost0, Hbytes0, Htag0, Hcount0, Hcont0⟩,
          Hstate0⟩
        imod universal_write_is_return host store ns obs nt length pointer
          bytes hlen hne hnowrap $$ [$Hhost0 $Hbytes0 $Hstate0] with
          ⟨Hhost1, Hbytes1, Hstate1, %hret⟩
        simp only [List.length_cons, List.length_nil, List.take_succ_cons,
          List.take_zero, List.reverse_cons, List.reverse_nil,
          List.nil_append, List.singleton_append] at hinvoke
        rw [hret] at hinvoke
        contradiction)
      (fun store ns obs nt _ postWasm tag xs hinvoke => by
        iintro ⟨⟨Hhost0, Hbytes0, Htag0, Hcount0, Hcont0⟩,
          Hstate0⟩
        imod universal_write_is_return host store ns obs nt length pointer
          bytes hlen hne hnowrap $$ [$Hhost0 $Hbytes0 $Hstate0] with
          ⟨Hhost1, Hbytes1, Hstate1, %hret⟩
        simp only [List.length_cons, List.length_nil, List.take_succ_cons,
          List.take_zero, List.reverse_cons, List.reverse_nil,
          List.nil_append, List.singleton_append] at hinvoke
        rw [hret] at hinvoke
        contradiction)
      $$ [$Hhost $Hbytes $Htag $Hcount $Hcont] Hruntime Henv
  · iintro %pre %results %post %hinvoke
      ⟨⟨%hresults, Hhost, Hbytes, Htag, Hcount, Hcont⟩, Hruntime⟩
    subst results
    simp only [List.take_zero, List.nil_append, List.drop_succ_cons,
      List.drop_zero]
    iapply twp_localGet rfl
    iapply twp_const
    iapply twp_store8_addr oldTag $$ Htag
    iintro Htag
    iapply twp_localGet rfl
    iapply twp_localGet rfl
    iapply twp_store32 oldCount houtCount.noWrap houtCount.one
      houtCount.two houtCount.three $$ Hcount
    iintro Hcount
    iapply hdtwp_returnFromCallFallthrough $$ Hruntime
    iintro Hruntime
    simp
    iapply Hcont
    iframe
  · iintro %pre %post %msg %hinvoke Hfalse
    iexfalso
    iexact Hfalse
  · iintro %pre %post %tag %xs %hinvoke Hfalse
    iexfalso
    iexact Hfalse

/-- Stack-normalized form of `twp_write_adapter` for callers with no values
below the adapter arguments. -/
theorem twp_write_adapter_no_stack
    [WasmSmallStepGS hlc Universal.State]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Universal.State)}
    (host : Universal.State) (out ignored pointer length : UInt32)
    (bytes : List UInt8) (oldTag : UInt8) (oldCount : UInt32)
    (hlen : bytes.length = length.toNat) (hne : bytes ≠ [])
    (hnowrap : pointer.toNat + bytes.length < UInt32.size)
    (houtCount : Offset32Facts out 4)
    (params localValues : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame) :
    runtimeModuleOwn ⟨0⟩ «module» ∗
      hostEnvOwn 0 (Universal.envFor «module») ∗
      hostStateOwn host ∗
      pointsToBytes 0 pointer bytes ∗
      pointsTo (GF := WasmHeapGF Universal.State) (H := WasmHeapMap)
        ⟨0, out⟩ (DFrac.own 1) (some oldTag) ∗
      pointsTo_u32 0 (out + 4) oldCount -∗
    (runtimeModuleOwn ⟨0⟩ «module» ∗
      hostStateOwn (afterUniversalWrite host bytes) ∗
      pointsToBytes 0 pointer bytes ∗
      pointsTo (GF := WasmHeapGF Universal.State) (H := WasmHeapMap)
        ⟨0, out⟩ (DFrac.own 1) (some (4 : UInt8)) ∗
      pointsTo_u32 0 (out + 4) length -∗
      WP (.running
        ⟨⟨params, localValues, []⟩, code, arity, remainder,
          controls, calls⟩ : Expr Universal.State) @ s; E [{ Φ }]) -∗
    WP (.running
      ⟨⟨params, localValues,
          [.i32 length, .i32 pointer, .i32 ignored, .i32 out]⟩,
        .call 20 :: code, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }] := by
  simpa only [List.singleton_append, List.append_nil] using
    (twp_write_adapter (s := s) (E := E) (Φ := Φ) host out ignored
      pointer length bytes oldTag oldCount hlen hne hnowrap houtCount
      ⟨params, localValues, []⟩ [] code arity remainder controls calls)

/-- The generated four-argument read adapter (module function 19) calls the
universal `stdio.read` import and records the byte count it returned. -/
theorem twp_read_adapter
    [WasmSmallStepGS hlc Universal.State]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Universal.State)}
    (host : Universal.State) (out ignored pointer length : UInt32)
    (buffer bytes : List UInt8) (oldTag : UInt8) (oldCount : UInt32)
    (hbytes : bytes = host.stdio.input.take length.toNat)
    (hbuffer : buffer.length = length.toNat)
    (hlength : length ≠ 0)
    (hnowrap : pointer.toNat + buffer.length < UInt32.size)
    (houtCount : Offset32Facts out 4)
    (callerLocals : Locals) (stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame) :
    runtimeModuleOwn ⟨0⟩ «module» ∗
      hostEnvOwn 0 (Universal.envFor «module») ∗
      hostStateOwn host ∗
      pointsToBytes 0 pointer buffer ∗
      pointsTo (GF := WasmHeapGF Universal.State) (H := WasmHeapMap)
        ⟨0, out⟩ (DFrac.own 1) (some oldTag) ∗
      pointsTo_u32 0 (out + 4) oldCount -∗
    (runtimeModuleOwn ⟨0⟩ «module» ∗
      hostStateOwn (afterUniversalRead host bytes.length) ∗
      pointsToBytes 0 pointer (bytes ++ buffer.drop bytes.length) ∗
      pointsTo (GF := WasmHeapGF Universal.State) (H := WasmHeapMap)
        ⟨0, out⟩ (DFrac.own 1) (some (4 : UInt8)) ∗
      pointsTo_u32 0 (out + 4) (UInt32.ofNat bytes.length) -∗
      WP (.running
        ⟨{ callerLocals with values := stack }, code, arity, remainder,
          controls, calls⟩ : Expr Universal.State) @ s; E [{ Φ }]) -∗
    WP (.running
      ⟨{ callerLocals with values :=
          [.i32 length, .i32 pointer, .i32 ignored, .i32 out] ++ stack },
        [.call 19] ++ code, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Henv, Hhost, Hbytes, Htag, Hcount⟩ Hcont
  simp only [List.singleton_append]
  iapply twp_call «module» 19 func16Def (by decide) rfl ⟨0⟩ $$ Hruntime
  iintro Hruntime
  simp [func16Def, Function.toLocals, Function.numParams,
    ValueType.zero, func16]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply hdtwp_callHost «module» 0
      { module := "stdio", name := "read", params := [.i32, .i32],
        results := [.i32] }
      (StdIO.readHost.lift universalStdIOLens)
      (by decide) rfl (Universal.envFor «module»)
      universal_read_function
      (iprop(hostStateOwn host ∗ pointsToBytes 0 pointer buffer ∗
        (pointsTo (GF := WasmHeapGF Universal.State) (H := WasmHeapMap)
          ⟨0, out⟩ (DFrac.own 1) (some oldTag)) ∗
        pointsTo_u32 0 (out + 4) oldCount ∗
        (runtimeModuleOwn ⟨0⟩ «module» ∗
          hostStateOwn (afterUniversalRead host bytes.length) ∗
          pointsToBytes 0 pointer (bytes ++ buffer.drop bytes.length) ∗
          (pointsTo (GF := WasmHeapGF Universal.State) (H := WasmHeapMap)
            ⟨0, out⟩ (DFrac.own 1) (some (4 : UInt8))) ∗
          pointsTo_u32 0 (out + 4) (UInt32.ofNat bytes.length) -∗
          WP (.running
            ⟨{ callerLocals with values := stack }, code, arity, remainder,
              controls, calls⟩ : Expr Universal.State) @ s; E [{ Φ }])))
      (fun results => iprop(
        ⌜results = [.i32 (UInt32.ofNat bytes.length)]⌝ ∗
        hostStateOwn (afterUniversalRead host bytes.length) ∗
        pointsToBytes 0 pointer (bytes ++ buffer.drop bytes.length) ∗
        (pointsTo (GF := WasmHeapGF Universal.State) (H := WasmHeapMap)
          ⟨0, out⟩ (DFrac.own 1) (some oldTag)) ∗
        pointsTo_u32 0 (out + 4) oldCount ∗
        (runtimeModuleOwn ⟨0⟩ «module» ∗
          hostStateOwn (afterUniversalRead host bytes.length) ∗
          pointsToBytes 0 pointer (bytes ++ buffer.drop bytes.length) ∗
          (pointsTo (GF := WasmHeapGF Universal.State) (H := WasmHeapMap)
            ⟨0, out⟩ (DFrac.own 1) (some (4 : UInt8))) ∗
          pointsTo_u32 0 (out + 4) (UInt32.ofNat bytes.length) -∗
          WP (.running
            ⟨{ callerLocals with values := stack }, code, arity, remainder,
              controls, calls⟩ : Expr Universal.State) @ s; E [{ Φ }])))
      (iprop(False)) (iprop(False)) ⟨0⟩
      (fun store ns obs nt _ results postWasm hinvoke => by
        iintro ⟨⟨Hhost0, Hbytes0, Htag0, Hcount0, Hcont0⟩, Hstate0⟩
        imod universal_read_buffer_transfer host store ns obs nt length pointer
          buffer bytes hbytes hbuffer hlength hnowrap results postWasm
          hinvoke $$ [$Hhost0 $Hbytes0 $Hstate0] with
          ⟨%hresults, Hhost1, Hbytes1, Hstate1⟩
        imodintro
        isplitl [Hhost1 Hbytes1 Htag0 Hcount0 Hcont0]
        · isplitr
          · ipureintro
            exact hresults
          · iframe
        · iexact Hstate1)
      (fun store ns obs nt _ postWasm msg hinvoke => by
        iintro ⟨⟨Hhost0, Hbytes0, Htag0, Hcount0, Hcont0⟩, Hstate0⟩
        ihave %holdFacts :
            ⌜∀ i b, buffer[i]? = some b →
                store.wasm.mem.read8 (pointer + UInt32.ofNat i) = b ∧
                (pointer + UInt32.ofNat i).toNat <
                  store.wasm.mem.pages * 65536⌝ $$ [Hstate0 Hbytes0]
        · imod stateInterp_pointsToBytes_agree store ns obs nt pointer
              buffer $$ [$Hstate0 $Hbytes0] with %holdFacts
          ipureintro
          exact holdFacts
        have hphysicalFull : pointer.toNat + buffer.length ≤
            store.wasm.mem.pages * 65536 := by
          apply pointsToBytes_facts_bound holdFacts
          · rw [hbuffer]
            apply Nat.pos_of_ne_zero
            intro hz
            apply hlength
            exact UInt32.toNat_inj.mp (by simpa using hz)
          · simpa only [UInt32.size] using hnowrap
        have hphysical : pointer.toNat + bytes.length ≤
            store.wasm.mem.pages * 65536 := by
          have hle : bytes.length ≤ buffer.length := by
            rw [hbytes, hbuffer, List.length_take]
            omega
          omega
        imod universal_read_is_return host store ns obs nt length pointer
          buffer bytes hbytes hphysical $$
          [$Hhost0 $Hbytes0 $Hstate0] with
          ⟨Hhost1, Hbytes1, Hstate1, %hret⟩
        simp only [List.length_cons, List.length_nil, List.take_succ_cons,
          List.take_zero, List.reverse_cons, List.reverse_nil,
          List.nil_append, List.singleton_append] at hinvoke
        rw [hret] at hinvoke
        contradiction)
      (fun store ns obs nt _ postWasm tag xs hinvoke => by
        iintro ⟨⟨Hhost0, Hbytes0, Htag0, Hcount0, Hcont0⟩, Hstate0⟩
        ihave %holdFacts :
            ⌜∀ i b, buffer[i]? = some b →
                store.wasm.mem.read8 (pointer + UInt32.ofNat i) = b ∧
                (pointer + UInt32.ofNat i).toNat <
                  store.wasm.mem.pages * 65536⌝ $$ [Hstate0 Hbytes0]
        · imod stateInterp_pointsToBytes_agree store ns obs nt pointer
              buffer $$ [$Hstate0 $Hbytes0] with %holdFacts
          ipureintro
          exact holdFacts
        have hphysicalFull : pointer.toNat + buffer.length ≤
            store.wasm.mem.pages * 65536 := by
          apply pointsToBytes_facts_bound holdFacts
          · rw [hbuffer]
            apply Nat.pos_of_ne_zero
            intro hz
            apply hlength
            exact UInt32.toNat_inj.mp (by simpa using hz)
          · simpa only [UInt32.size] using hnowrap
        have hphysical : pointer.toNat + bytes.length ≤
            store.wasm.mem.pages * 65536 := by
          have hle : bytes.length ≤ buffer.length := by
            rw [hbytes, hbuffer, List.length_take]
            omega
          omega
        imod universal_read_is_return host store ns obs nt length pointer
          buffer bytes hbytes hphysical $$
          [$Hhost0 $Hbytes0 $Hstate0] with
          ⟨Hhost1, Hbytes1, Hstate1, %hret⟩
        simp only [List.length_cons, List.length_nil, List.take_succ_cons,
          List.take_zero, List.reverse_cons, List.reverse_nil,
          List.nil_append, List.singleton_append] at hinvoke
        rw [hret] at hinvoke
        contradiction)
      $$ [$Hhost $Hbytes $Htag $Hcount $Hcont] Hruntime Henv
  · iintro %pre %results %post %hinvoke
      ⟨⟨%hresults, Hhost, Hbytes, Htag, Hcount, Hcont⟩, Hruntime⟩
    subst results
    simp
    iapply twp_localSet rfl
    iapply twp_localGet rfl
    iapply twp_const
    iapply twp_store8_addr oldTag $$ Htag
    iintro Htag
    iapply twp_localGet rfl
    iapply twp_localGet rfl
    iapply twp_store32 oldCount houtCount.noWrap houtCount.one
      houtCount.two houtCount.three $$ Hcount
    iintro Hcount
    iapply hdtwp_returnFromCallFallthrough $$ Hruntime
    iintro Hruntime
    simp
    iapply Hcont
    iframe
  · iintro %pre %post %msg %hinvoke Hfalse
    iexfalso
    iexact Hfalse
  · iintro %pre %post %tag %xs %hinvoke Hfalse
    iexfalso
    iexact Hfalse

/-- Stack-normalized form of `twp_read_adapter`. -/
theorem twp_read_adapter_no_stack
    [WasmSmallStepGS hlc Universal.State]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Universal.State)}
    (host : Universal.State) (out ignored pointer length : UInt32)
    (buffer bytes : List UInt8) (oldTag : UInt8) (oldCount : UInt32)
    (hbytes : bytes = host.stdio.input.take length.toNat)
    (hbuffer : buffer.length = length.toNat)
    (hlength : length ≠ 0)
    (hnowrap : pointer.toNat + buffer.length < UInt32.size)
    (houtCount : Offset32Facts out 4)
    (params localValues : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame) :
    runtimeModuleOwn ⟨0⟩ «module» ∗
      hostEnvOwn 0 (Universal.envFor «module») ∗
      hostStateOwn host ∗
      pointsToBytes 0 pointer buffer ∗
      pointsTo (GF := WasmHeapGF Universal.State) (H := WasmHeapMap)
        ⟨0, out⟩ (DFrac.own 1) (some oldTag) ∗
      pointsTo_u32 0 (out + 4) oldCount -∗
    (runtimeModuleOwn ⟨0⟩ «module» ∗
      hostStateOwn (afterUniversalRead host bytes.length) ∗
      pointsToBytes 0 pointer (bytes ++ buffer.drop bytes.length) ∗
      pointsTo (GF := WasmHeapGF Universal.State) (H := WasmHeapMap)
        ⟨0, out⟩ (DFrac.own 1) (some (4 : UInt8)) ∗
      pointsTo_u32 0 (out + 4) (UInt32.ofNat bytes.length) -∗
      WP (.running
        ⟨⟨params, localValues, []⟩, code, arity, remainder,
          controls, calls⟩ : Expr Universal.State) @ s; E [{ Φ }]) -∗
    WP (.running
      ⟨⟨params, localValues,
          [.i32 length, .i32 pointer, .i32 ignored, .i32 out]⟩,
        .call 19 :: code, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }] := by
  simpa only [List.singleton_append, List.append_nil] using
    (twp_read_adapter (s := s) (E := E) (Φ := Φ) host out ignored
      pointer length buffer bytes oldTag oldCount hbytes hbuffer hlength
      hnowrap houtCount ⟨params, localValues, []⟩ [] code arity remainder
      controls calls)

end Project.HexDecodeStdio
