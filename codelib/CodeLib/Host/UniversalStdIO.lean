import CodeLib.SepLogic.SmallStepTotalLifting
import CodeLib.SepLogic.SmallStepState
import Interpreter.Wasm.Host.Universal

/-!
# Generic stdio host-call rules for any module importing StdIO ++ OOM

Lifted versions of the universal-read and universal-write total-WP rules,
parametrised by any `Module` whose import list is exactly
`StdIO.imports ++ OOM.imports`.  Instantiate at a concrete module to get
the module-specific versions back.
-/

namespace Wasm.SmallStep

open Wasm
open Iris Iris.BI Iris.ProgramLogic Language.Notation Iris.Std
open Wasm.SepLogic

/-! ## Universal-state host-function definitions -/

def universalReadHost : HostFn Universal.State :=
  StdIO.readHost.lift
    { get := Universal.State.stdio
      set := fun whole part => { whole with stdio := part } }

def universalWriteHost : HostFn Universal.State :=
  StdIO.writeHost.lift
    { get := Universal.State.stdio
      set := fun whole part => { whole with stdio := part } }

/-! ## Resolver lemma -/

/-- For any module importing `StdIO.imports ++ OOM.imports`, the universal
environment resolves position 0 to the read host and position 1 to the write
host. -/
theorem Universal.envFor_stdio_funcs (m : Module)
    (hm : m.imports = StdIO.imports ++ OOM.imports) :
    (Universal.envFor m).funcs[0]? = some universalReadHost ∧
    (Universal.envFor m).funcs[1]? = some universalWriteHost := by
  have h0 : 0 < m.imports.length := by rw [hm]; decide
  have h1 : 1 < m.imports.length := by rw [hm]; decide
  refine ⟨?_, ?_⟩
  · simp only [Universal.envFor]
    rw [HostRegistry.envFor_getElem? Universal.registry m h0]
    have him0 : m.imports[0] = (StdIO.imports ++ OOM.imports)[0]'(by decide) :=
      Option.some.inj
        ((List.getElem?_eq_getElem h0).symm.trans
          ((show m.imports[0]? = (StdIO.imports ++ OOM.imports)[0]? from by rw [hm]).trans
            (List.getElem?_eq_getElem (by decide))))
    rw [him0]; rfl
  · simp only [Universal.envFor]
    rw [HostRegistry.envFor_getElem? Universal.registry m h1]
    have him1 : m.imports[1] = (StdIO.imports ++ OOM.imports)[1]'(by decide) :=
      Option.some.inj
        ((List.getElem?_eq_getElem h1).symm.trans
          ((show m.imports[1]? = (StdIO.imports ++ OOM.imports)[1]? from by rw [hm]).trans
            (List.getElem?_eq_getElem (by decide))))
    rw [him1]; rfl

/-! ## State-update helpers -/

def afterRead (host : Universal.State) (bytes : List UInt8) : Universal.State :=
  { host with stdio :=
      { input := host.stdio.input.drop bytes.length
        output := host.stdio.output } }

def bytesRead (host : Universal.State) (length : UInt32) : List UInt8 :=
  host.stdio.input.take length.toNat

def afterWrite (host : Universal.State) (bytes : List UInt8) : Universal.State :=
  { host with stdio :=
      { input := host.stdio.input
        output := host.stdio.output ++ bytes } }

/-! ## Write-bytes state update -/

private theorem writeBytes_singleton (mem : Mem) (addr : UInt32) (byte : UInt8) :
    mem.writeBytes addr.toNat [byte] = mem.write8 addr byte := by
  cases mem
  simp only [Mem.writeBytes, Mem.write8, List.length_cons, List.length_nil]
  congr 1
  funext i
  by_cases hrange : addr.toNat ≤ i ∧ i < addr.toNat + 1
  · have heq : i = addr.toNat := by omega
    subst heq; simp
  · simp only [dite_eq_right hrange]
    by_cases h : i = addr.toNat
    · subst h; exact absurd ⟨Nat.le_refl _, Nat.lt_succ_self _⟩ hrange
    · rw [ite_eq_right h]

private theorem writeBytes_nil (mem : Mem) (addr : UInt32) :
    mem.writeBytes addr.toNat [] = mem := by
  cases mem
  simp only [Mem.writeBytes, List.length_nil, Nat.add_zero]
  congr
  funext i
  split <;> rename_i h
  · omega
  · rfl

private theorem writeBytes_cons (mem : Mem) (addr : UInt32)
    (byte : UInt8) (bytes : List UInt8)
    (haddr : addr.toNat + bytes.length + 1 < UInt32.size) :
    mem.writeBytes addr.toNat (byte :: bytes) =
      (mem.write8 addr byte).writeBytes (addr + 1).toNat bytes := by
  rw [show byte :: bytes = [byte] ++ bytes by rfl,
    Mem.writeBytes_append, writeBytes_singleton]
  congr 2
  have ha : addr.toNat + 1 < UInt32.size := by omega
  simp only [List.length_singleton]
  exact (UInt32.add_ofNat_toNat_noWrap addr 1 (by decide) ha).symm

/-- Update an owned byte range by the same bulk write performed by the read
host. -/
theorem stateInterp_writeBytes_exact {hlc : HasLC} {α : Type}
    [WasmSmallStepGS hlc α]
    (store : MachineStore α) (steps : Nat)
    (observations : List StepKind) (threads : Nat)
    (addr : UInt32) (old new : List UInt8)
    (hlen : old.length = new.length)
    (haddr : addr.toNat + old.length < UInt32.size) :
    stateInterp (GF := WasmHeapGF α) store steps observations threads ∗
      pointsToBytes 0 addr old ==∗
      stateInterp (GF := WasmHeapGF α)
        { store with wasm :=
            { store.wasm with mem := store.wasm.mem.writeBytes addr.toNat new } }
        steps observations threads ∗
      pointsToBytes 0 addr new := by
  induction old generalizing store addr new with
  | nil =>
      cases new with
      | nil =>
          have heq :
              ({ store with wasm :=
                  { store.wasm with
                    mem := store.wasm.mem.writeBytes addr.toNat [] } } :
                MachineStore α) = store := by
            rw [writeBytes_nil]
          rw [heq]
          iintro H
          imodintro
          iexact H
      | cons newHead newTail => simp at hlen
  | cons oldHead oldTail ih =>
      cases new with
      | nil => simp at hlen
      | cons newHead newTail =>
          have htail : oldTail.length = newTail.length := by simpa using hlen
          iintro ⟨Hstate, Hold⟩
          ihave Hold := (pointsToBytes_cons 0 addr oldHead oldTail).mp $$ Hold
          icases Hold with ⟨Hhead, Htail⟩
          ihave %hheadBound :
              ⌜addr.toNat < store.wasm.mem.pages * 65536⌝ $$ [Hstate Hhead]
          · imod stateInterp_pointsTo_inBounds store steps observations threads
                addr oldHead $$ [$Hstate $Hhead] with %hbound
            ipureintro
            exact hbound
          imod stateInterp_store8 store steps observations threads addr oldHead
              newHead hheadBound $$ [$Hstate $Hhead] with ⟨Hstate, Hhead⟩
          have ha : addr.toNat + 1 < UInt32.size := by
            simp only [List.length_cons] at haddr; omega
          have hone : (addr + 1).toNat = addr.toNat + 1 := by
            change (addr + UInt32.ofNat 1).toNat = addr.toNat + 1
            exact UInt32.add_ofNat_toNat_noWrap addr 1 (by decide) ha
          have hnext : (addr + 1).toNat + oldTail.length < UInt32.size := by
            simp only [List.length_cons] at haddr; rw [hone]; omega
          imod ih { store with wasm :=
                { store.wasm with mem := store.wasm.mem.write8 addr newHead } }
              (addr + 1) newTail htail hnext $$ [$Hstate $Htail] with
            ⟨Hstate, Htail⟩
          imodintro
          have hmem := writeBytes_cons store.wasm.mem addr newHead newTail (by
            simp only [List.length_cons] at haddr; rw [htail] at haddr; omega)
          isplitl [Hstate]
          · rw [hmem]
            iexact Hstate
          · iapply (pointsToBytes_cons 0 addr newHead newTail).mpr
            iframe

/-! ## Read-bytes helper -/

private theorem readBytes_eq_of_facts (mem : Mem) (addr : UInt32)
    (bytes : List UInt8)
    (hfacts : ∀ i b, bytes[i]? = some b →
      mem.read8 (addr + UInt32.ofNat i) = b ∧
      (addr + UInt32.ofNat i).toNat < mem.pages * 65536)
    (hnowrap : addr.toNat + bytes.length < UInt32.size) :
    mem.readBytes addr.toNat bytes.length = bytes := by
  apply List.ext_getElem
  · simp [Mem.readBytes]
  · intro i hleft hright
    have hi : i < bytes.length := by
      simpa [Mem.readBytes] using hleft
    have hget : bytes[i]? = some bytes[i] := List.getElem?_eq_getElem hright
    have hbyte := (hfacts i bytes[i] hget).1
    have hisize : i < UInt32.size := by
      calc
        i < bytes.length := hi
        _ ≤ addr.toNat + bytes.length := Nat.le_add_left _ _
        _ < UInt32.size := hnowrap
    have hadd : addr.toNat + i < UInt32.size := by omega
    simp only [Mem.readBytes, List.getElem_map, List.getElem_range,
      Mem.read8] at hbyte ⊢
    rw [UInt32.add_ofNat_toNat_noWrap addr i hisize hadd] at hbyte
    exact hbyte

/-! ## Generalized read rule -/

/-- A universal-host read call for any module importing StdIO ++ OOM. -/
theorem twp_universal_read {hlc : HasLC}
    [WasmSmallStepGS hlc Universal.State]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Universal.State)}
    (m : Module) (hm : m.imports = StdIO.imports ++ OOM.imports)
    (ptr length : UInt32) (old : List UInt8) (host : Universal.State)
    (hlen : length.toNat = old.length) (hpos : 0 < old.length)
    (hnowrap : ptr.toNat + old.length < UInt32.size)
    {params localValues values : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (callerId : ModuleInstanceId) :
    pointsToBytes 0 ptr old -∗
    hostStateOwn host -∗
    runtimeModuleOwn callerId m -∗
    hostEnvOwn callerId.id (Universal.envFor m) -∗
    (pointsToBytes 0 ptr
        (bytesRead host length ++ old.drop (bytesRead host length).length) -∗
      hostStateOwn (afterRead host (bytesRead host length)) -∗
      runtimeModuleOwn callerId m -∗
      hostEnvOwn callerId.id (Universal.envFor m) -∗
      WP (.running
        ⟨⟨params, localValues,
            .i32 (UInt32.ofNat (bytesRead host length).length) :: values⟩,
          code, arity, remainder, controls, calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }]) -∗
    WP (.running
      ⟨⟨params, localValues, .i32 ptr :: .i32 length :: values⟩,
        .call 0 :: code, arity, remainder, controls, calls⟩ :
          Expr Universal.State) @ s; E [{ Φ }] := by
  let read := bytesRead host length
  have hread_le : read.length ≤ old.length := by
    simp only [read, bytesRead, List.length_take, hlen]
    omega
  have htakeLen : (old.take read.length).length = read.length :=
    List.length_take_of_le hread_le
  obtain ⟨hhostFn, _⟩ := Universal.envFor_stdio_funcs m hm
  have himlen0 : 0 < m.imports.length := by rw [hm]; decide
  have htransfer : ∀ (store : MachineStore Universal.State) ns obs nt,
      store.runtime.currentModule = m →
      store.runtime.currentHost = Universal.envFor m →
      iprop(pointsToBytes 0 ptr old ∗ hostStateOwn host) ∗
          stateInterp (GF := WasmHeapGF Universal.State) store ns obs nt ==∗
        ∃ results postWasm,
          ⌜universalReadHost.invoke store.wasm
              ((.i32 ptr :: .i32 length :: values).take
                m.imports[0].params.length).reverse =
            .Return results postWasm⌝ ∗
          iprop(⌜results = [.i32 (UInt32.ofNat read.length)]⌝ ∗
            pointsToBytes 0 ptr (read ++ old.drop read.length) ∗
            hostStateOwn (afterRead host read)) ∗
          stateInterp (GF := WasmHeapGF Universal.State)
            { store with wasm := postWasm } ns obs nt := by
    intro store ns obs nt hmodule henv
    iintro ⟨⟨Hold, Hhost⟩, Hσ⟩
    ihave %Hfacts : ⌜∀ i b, old[i]? = some b →
        store.wasm.mem.read8 (ptr + UInt32.ofNat i) = b ∧
        (ptr + UInt32.ofNat i).toNat <
          store.wasm.mem.pages * 65536⌝ $$ [Hσ Hold]
    · imod stateInterp_pointsToBytes_agree store ns obs nt ptr old
          $$ [$Hσ $Hold] with %Hfacts
      ipureintro
      exact Hfacts
    have hbound : ptr.toNat + old.length ≤ store.wasm.mem.pages * 65536 :=
      pointsToBytes_facts_bound Hfacts hpos hnowrap
    ihave ⟨Hprefix, Hsuffix⟩ :
        (iprop% pointsToBytes 0 ptr (old.take read.length) ∗
          pointsToBytes 0 (ptr + UInt32.ofNat read.length)
            (old.drop read.length)) $$ [Hold]
    · ihave Hold' : pointsToBytes 0 ptr
          (old.take read.length ++ old.drop read.length) $$ [Hold]
      · rw [List.take_append_drop]; iexact Hold
      ihave Hsplit :=
          (pointsToBytes_append 0 ptr (old.take read.length)
            (old.drop read.length)).mp $$ Hold'
      rw [← show ptr + UInt32.ofNat (old.take read.length).length =
          ptr + UInt32.ofNat read.length from by rw [htakeLen]]
      iexact Hsplit
    imod stateInterp_writeBytes_exact store ns obs nt ptr (old.take read.length)
        read htakeLen (by
          rw [List.length_take_of_le hread_le]
          omega) $$ [$Hσ $Hprefix] with ⟨Hσ, Hprefix⟩
    let newHost := afterRead host read
    imod stateInterp_host_set_expected
        { store with wasm :=
            { store.wasm with mem := store.wasm.mem.writeBytes ptr.toNat read } }
        ns obs nt host newHost $$ [$Hσ $Hhost] with
      ⟨%HhostPhysical, Hσ, Hhost⟩
    have hhostActual : store.wasm.host = host := by
      simpa using HhostPhysical
    have hcapNat : ptr.toNat + read.length ≤
        store.wasm.mem.pages * 65536 := by omega
    have him0_inner : m.imports[0] = (StdIO.imports ++ OOM.imports)[0]'(by decide) :=
      Option.some.inj
        ((List.getElem?_eq_getElem himlen0).symm.trans
          ((show m.imports[0]? = (StdIO.imports ++ OOM.imports)[0]? from by rw [hm]).trans
            (List.getElem?_eq_getElem (by decide))))
    have hparamLen : m.imports[0].params.length = 2 := by rw [him0_inner]; decide
    have hinvoke : universalReadHost.invoke store.wasm [.i32 length, .i32 ptr] =
        .Return [.i32 (UInt32.ofNat read.length)]
          { store.wasm with
            mem := store.wasm.mem.writeBytes ptr.toNat read
            host := newHost } := by
      simp +instances only [universalReadHost, HostFn.lift, StdIO.readHost, StdIO.readResult]
      simp +instances only [Store.focus, Store.mapHost]
      simp +instances only [hhostActual]
      rw [ite_eq_left (by
        simp only [StdIO.rangeInBounds, StdIO.byteCapacity]
        apply decide_eq_true
        simpa only [read, bytesRead] using hcapNat)]
      simp [Store.unfocus, Store.mapHost, read, bytesRead, newHost, afterRead]
    imodintro
    iexists [.i32 (UInt32.ofNat read.length)]
    iexists { store.wasm with
      mem := store.wasm.mem.writeBytes ptr.toNat read
      host := newHost }
    isplit
    · ipureintro
      rw [hparamLen]
      exact hinvoke
    isplitl [Hprefix Hsuffix Hhost]
    · isplit
      · ipureintro; rfl
      isplitl [Hprefix Hsuffix]
      · iapply (pointsToBytes_append 0 ptr read (old.drop read.length)).mpr
        have haddr : ptr + UInt32.ofNat read.length =
            ptr + UInt32.ofNat (old.take read.length).length := by rw [htakeLen]
        rw [haddr]
        iframe
      · iexact Hhost
    · iexact Hσ
  iintro Hold Hhost Hruntime Henv Hnext
  iapply twp_callHost_return_fupd
    m 0 m.imports[0]
    universalReadHost himlen0 rfl (Universal.envFor m)
    hhostFn (iprop(pointsToBytes 0 ptr old ∗ hostStateOwn host))
    (fun results => iprop(
      ⌜results = [.i32 (UInt32.ofNat read.length)]⌝ ∗
      pointsToBytes 0 ptr (read ++ old.drop read.length) ∗
      hostStateOwn (afterRead host read))) callerId
      htransfer $$ [$Hold $Hhost] Hruntime Henv
  iintro %preWasm %results %postWasm %hinvoke ⟨HQ, Hruntime, Henv⟩
  icases HQ with ⟨%hresults, Hbytes, Hhost⟩
  subst results
  have him0_outer : m.imports[0] = (StdIO.imports ++ OOM.imports)[0]'(by decide) :=
    Option.some.inj
      ((List.getElem?_eq_getElem himlen0).symm.trans
        ((show m.imports[0]? = (StdIO.imports ++ OOM.imports)[0]? from by rw [hm]).trans
          (List.getElem?_eq_getElem (by decide))))
  have hresultLen : m.imports[0].results.length = 1 := by rw [him0_outer]; decide
  have hparamLen : m.imports[0].params.length = 2 := by rw [him0_outer]; decide
  simp only [hresultLen, hparamLen, List.take_succ_cons, List.take_zero,
    List.nil_append, List.drop_succ_cons, List.drop_zero, List.cons_append]
  simp only [read]
  iapply Hnext $$ Hbytes Hhost Hruntime Henv

/-! ## Generalized write rule -/

/-- A universal-host write call for any module importing StdIO ++ OOM. -/
theorem twp_universal_write {hlc : HasLC}
    [WasmSmallStepGS hlc Universal.State]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Universal.State)}
    (m : Module) (hm : m.imports = StdIO.imports ++ OOM.imports)
    (ptr length : UInt32) (bytes : List UInt8) (host : Universal.State)
    (hlen : length.toNat = bytes.length)
    (hpos : 0 < bytes.length)
    (hnowrap : ptr.toNat + bytes.length < UInt32.size)
    {params localValues values : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (callerId : ModuleInstanceId) :
    pointsToBytes 0 ptr bytes -∗
    hostStateOwn host -∗
    runtimeModuleOwn callerId m -∗
    hostEnvOwn callerId.id (Universal.envFor m) -∗
    (pointsToBytes 0 ptr bytes -∗
      hostStateOwn (afterWrite host bytes) -∗
      runtimeModuleOwn callerId m -∗
      hostEnvOwn callerId.id (Universal.envFor m) -∗
      WP (.running
        ⟨⟨params, localValues, values⟩, code,
          arity, remainder, controls, calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }]) -∗
    WP (.running
      ⟨⟨params, localValues, .i32 ptr :: .i32 length :: values⟩,
        .call 1 :: code, arity, remainder, controls, calls⟩ :
          Expr Universal.State) @ s; E [{ Φ }] := by
  obtain ⟨_, hhostFn⟩ := Universal.envFor_stdio_funcs m hm
  have himlen1 : 1 < m.imports.length := by rw [hm]; decide
  have htransfer : ∀ (store : MachineStore Universal.State) ns obs nt,
      store.runtime.currentModule = m →
      store.runtime.currentHost = Universal.envFor m →
      iprop(pointsToBytes 0 ptr bytes ∗ hostStateOwn host) ∗
          stateInterp (GF := WasmHeapGF Universal.State) store ns obs nt ==∗
        ∃ results postWasm,
          ⌜universalWriteHost.invoke store.wasm
              ((.i32 ptr :: .i32 length :: values).take
                m.imports[1].params.length).reverse =
            .Return results postWasm⌝ ∗
          iprop(pointsToBytes 0 ptr bytes ∗
            hostStateOwn (afterWrite host bytes)) ∗
          stateInterp (GF := WasmHeapGF Universal.State)
            { store with wasm := postWasm } ns obs nt := by
    intro store ns obs nt hmodule henv
    iintro ⟨⟨Hbytes, Hhost⟩, Hσ⟩
    ihave %Hfacts : ⌜∀ i b, bytes[i]? = some b →
        store.wasm.mem.read8 (ptr + UInt32.ofNat i) = b ∧
        (ptr + UInt32.ofNat i).toNat <
          store.wasm.mem.pages * 65536⌝ $$ [Hσ Hbytes]
    · imod stateInterp_pointsToBytes_agree store ns obs nt ptr bytes
          $$ [$Hσ $Hbytes] with %Hfacts
      ipureintro
      exact Hfacts
    have hbound : ptr.toNat + bytes.length ≤
        store.wasm.mem.pages * 65536 :=
      pointsToBytes_facts_bound Hfacts hpos hnowrap
    have hread : store.wasm.mem.readBytes ptr.toNat bytes.length = bytes :=
      readBytes_eq_of_facts store.wasm.mem ptr bytes Hfacts hnowrap
    let newHost := afterWrite host bytes
    let newWasm : Store Universal.State := { store.wasm with host := newHost }
    have hparamLen : m.imports[1].params.length = 2 := by
      have him1 : m.imports[1] = (StdIO.imports ++ OOM.imports)[1]'(by decide) :=
        Option.some.inj
          ((List.getElem?_eq_getElem himlen1).symm.trans
            ((show m.imports[1]? = (StdIO.imports ++ OOM.imports)[1]? from by rw [hm]).trans
              (List.getElem?_eq_getElem (by decide))))
      rw [him1]; decide
    imod stateInterp_host_set_expected
        store ns obs nt host newHost $$ [$Hσ $Hhost] with
      ⟨%HhostPhysical, Hσ, Hhost⟩
    have hinvoke : universalWriteHost.invoke store.wasm [.i32 length, .i32 ptr] =
        .Return [] newWasm := by
      simp only [universalWriteHost, HostFn.lift]
      simp only [StdIO.writeHost, StdIO.writeResult]
      rw [ite_eq_left]
      · simp [Store.focus, Store.mapHost, Store.unfocus, newWasm, newHost,
          afterWrite, hread, hlen, HhostPhysical]
      · simp only [StdIO.rangeInBounds, StdIO.byteCapacity]
        apply decide_eq_true
        change ptr.toNat + length.toNat ≤ store.wasm.mem.pages * 65536
        simpa only [hlen] using hbound
    imodintro
    iexists [], newWasm
    isplit
    · ipureintro
      rw [hparamLen]
      exact hinvoke
    isplitl [Hbytes Hhost]
    · isplitl [Hbytes]
      · iexact Hbytes
      · iexact Hhost
    · iexact Hσ
  iintro Hbytes Hhost Hruntime Henv Hnext
  iapply twp_callHost_return_fupd
    m 1 m.imports[1]
    universalWriteHost himlen1 rfl
    (Universal.envFor m) hhostFn
    (iprop(pointsToBytes 0 ptr bytes ∗ hostStateOwn host))
    (fun _ => iprop(pointsToBytes 0 ptr bytes ∗
      hostStateOwn (afterWrite host bytes))) callerId htransfer
      $$ [$Hbytes $Hhost] Hruntime Henv
  iintro %preWasm %results %postWasm %hinvoke ⟨HQ, Hruntime, Henv⟩
  have him1_write : m.imports[1] = (StdIO.imports ++ OOM.imports)[1]'(by decide) :=
    Option.some.inj
      ((List.getElem?_eq_getElem himlen1).symm.trans
        ((show m.imports[1]? = (StdIO.imports ++ OOM.imports)[1]? from by rw [hm]).trans
          (List.getElem?_eq_getElem (by decide))))
  have hresults : results = [] := by
    have hpl : m.imports[1].params.length = 2 := by rw [him1_write]; decide
    have hargs : ((.i32 ptr :: .i32 length :: values).take
        m.imports[1].params.length).reverse =
        [.i32 length, .i32 ptr] := by rw [hpl]; rfl
    rw [hargs] at hinvoke
    by_cases hb : StdIO.rangeInBounds
        (preWasm.focus
          { get := Universal.State.stdio
            set := fun whole part => { whole with stdio := part } })
        ptr.toNat length.toNat
    · simp [universalWriteHost, HostFn.lift,
        StdIO.writeHost, StdIO.writeResult, hb] at hinvoke
      exact hinvoke.1
    · simp [universalWriteHost, HostFn.lift,
        StdIO.writeHost, StdIO.writeResult, hb] at hinvoke
  subst results
  icases HQ with ⟨Hbytes, Hhost⟩
  have hresultLen : m.imports[1].results.length = 0 := by rw [him1_write]; decide
  have hparamLen : m.imports[1].params.length = 2 := by rw [him1_write]; decide
  simp only [hresultLen, hparamLen, List.take_zero, List.nil_append,
    List.drop_succ_cons, List.drop_zero]
  iapply Hnext $$ Hbytes Hhost Hruntime Henv

end Wasm.SmallStep
