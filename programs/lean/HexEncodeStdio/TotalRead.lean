import Mathlib
import CodeLib
import Project.HexStdio.Spec
import HexEncodeStdio.Host
import HexEncodeStdio.TotalHost
import HexEncodeStdio.Helpers
import HexEncodeStdio.TotalHelpers
import HexEncodeStdio.TotalIterator

namespace Submission.TotalRead

open Wasm
open Iris Iris.BI Iris.ProgramLogic Language.Notation Iris.Std
open Wasm.SepLogic Wasm.SmallStep

def afterRead (host : Universal.State) (bytes : List UInt8) : Universal.State :=
  { host with stdio :=
      { input := host.stdio.input.drop bytes.length
        output := host.stdio.output } }

def bytesRead (host : Universal.State) (length : UInt32) : List UInt8 :=
  host.stdio.input.take length.toNat

private theorem writeBytes_singleton (mem : Mem) (addr : UInt32) (byte : UInt8) :
    mem.writeBytes addr.toNat [byte] = mem.write8 addr byte := by
  cases mem
  simp only [Mem.writeBytes, Mem.write8, List.length_cons, List.length_nil,
    Nat.add_zero]
  congr
  funext i
  by_cases hrange : addr.toNat ≤ i ∧ i < addr.toNat + 1
  · have h : i = addr.toNat := by omega
    subst i
    simp
  · by_cases h : i = addr.toNat
    · subst i
      exfalso
      exact hrange (by omega)
    · simp [h, hrange]
      intro hle hle'
      exact False.elim (h (Nat.le_antisymm hle' hle))

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
  have ha : addr.toNat + 1 < UInt32.size := by
    norm_num [UInt32.size] at haddr ⊢
    omega
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
            norm_num [UInt32.size] at haddr ⊢
            omega
          have hone : (addr + 1).toNat = addr.toNat + 1 := by
            change (addr + UInt32.ofNat 1).toNat = addr.toNat + 1
            exact UInt32.add_ofNat_toNat_noWrap addr 1 (by decide) ha
          have hnext : (addr + 1).toNat + oldTail.length < UInt32.size := by
            rw [hone]
            norm_num [UInt32.size] at haddr ⊢
            omega
          imod ih { store with wasm :=
                { store.wasm with mem := store.wasm.mem.write8 addr newHead } }
              (addr + 1) newTail htail hnext $$ [$Hstate $Htail] with
            ⟨Hstate, Htail⟩
          imodintro
          have hmem := writeBytes_cons store.wasm.mem addr newHead newTail (by
            norm_num [UInt32.size] at haddr ⊢
            rw [htail] at haddr
            omega)
          isplitl [Hstate]
          · rw [hmem]
            iexact Hstate
          · iapply (pointsToBytes_cons 0 addr newHead newTail).mpr
            iframe

/-- A universal-host read call returns the maximal requested prefix, writes it
into the owned buffer, and consumes precisely that prefix from stdin. -/
theorem twp_universal_read {hlc : HasLC}
    [WasmSmallStepGS hlc Universal.State]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Universal.State)}
    (ptr length : UInt32) (old : List UInt8) (host : Universal.State)
    (hlen : length.toNat = old.length) (hpos : 0 < old.length)
    (hnowrap : ptr.toNat + old.length < UInt32.size)
    {params localValues values : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (callerId : ModuleInstanceId) :
    pointsToBytes 0 ptr old -∗
    hostStateOwn host -∗
    runtimeModuleOwn callerId Project.HexStdio.«module» -∗
    hostEnvOwn callerId.id (Universal.envFor Project.HexStdio.«module») -∗
    (pointsToBytes 0 ptr
        (bytesRead host length ++ old.drop (bytesRead host length).length) -∗
      hostStateOwn (afterRead host (bytesRead host length)) -∗
      runtimeModuleOwn callerId Project.HexStdio.«module» -∗
      hostEnvOwn callerId.id (Universal.envFor Project.HexStdio.«module») -∗
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
  obtain ⟨hostFn, hhostFn, hresolve⟩ := Submission.Host.universal_read_resolver
  have htransfer : ∀ (store : MachineStore Universal.State) ns obs nt,
      store.runtime.currentModule = Project.HexStdio.«module» →
      store.runtime.currentHost = Universal.envFor Project.HexStdio.«module» →
      iprop(pointsToBytes 0 ptr old ∗ hostStateOwn host) ∗
          stateInterp (GF := WasmHeapGF Universal.State) store ns obs nt ==∗
        ∃ results postWasm,
          ⌜hostFn.invoke store.wasm
              ((.i32 ptr :: .i32 length :: values).take
                Project.HexStdio.«module».imports[0].params.length).reverse =
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
    ihave Hold := Submission.Helpers.pointsToBytes_take_drop 0 ptr old
      read.length hread_le $$ Hold
    icases Hold with ⟨Hprefix, Hsuffix⟩
    imod stateInterp_writeBytes_exact store ns obs nt ptr (old.take read.length)
        read htakeLen (by
          rw [List.length_take_of_le hread_le]
          omega) $$ [$Hσ $Hprefix] with ⟨Hσ, Hprefix⟩
    let newHost := afterRead host read
    imod Submission.TotalHost.stateInterp_host_set_expected
        { store with wasm :=
            { store.wasm with mem := store.wasm.mem.writeBytes ptr.toNat read } }
        ns obs nt host newHost $$ [$Hσ $Hhost] with
      ⟨%HhostPhysical, Hσ, Hhost⟩
    have hhostActual : store.wasm.host = host := by
      simpa using HhostPhysical
    have hcapNat : ptr.toNat + read.length ≤
        store.wasm.mem.pages * 65536 := by omega
    have hinvoke : hostFn.invoke store.wasm [.i32 length, .i32 ptr] =
        .Return [.i32 (UInt32.ofNat read.length)]
          { store.wasm with
            mem := store.wasm.mem.writeBytes ptr.toNat read
            host := newHost } := by
      rw [hresolve]
      simp only [Submission.Host.universalReadHost, HostFn.lift,
        StdIO.readHost, StdIO.readResult]
      simp only [Store.focus, Store.mapHost]
      rw [hhostActual]
      rw [if_pos (by
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
      convert hinvoke using 1 <;> rfl
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
  iapply Submission.TotalHost.twp_callHost_return_fupd
    Project.HexStdio.«module» 0 Project.HexStdio.«module».imports[0]
    hostFn (by decide) rfl (Universal.envFor Project.HexStdio.«module»)
    hhostFn (iprop(pointsToBytes 0 ptr old ∗ hostStateOwn host))
    (fun results => iprop(
      ⌜results = [.i32 (UInt32.ofNat read.length)]⌝ ∗
      pointsToBytes 0 ptr (read ++ old.drop read.length) ∗
      hostStateOwn (afterRead host read))) callerId
      htransfer $$ [$Hold $Hhost] Hruntime Henv
  iintro %preWasm %results %postWasm %hinvoke ⟨HQ, Hruntime, Henv⟩
  icases HQ with ⟨%hresults, Hbytes, Hhost⟩
  subst results
  have hresultLen :
      Project.HexStdio.«module».imports[0].results.length = 1 := by rfl
  have hparamLen :
      Project.HexStdio.«module».imports[0].params.length = 2 := by rfl
  simp only [hresultLen, hparamLen, List.take_succ_cons, List.take_zero,
    List.nil_append, List.drop_succ_cons, List.drop_zero, List.cons_append]
  simp only [read]
  iapply Hnext $$ Hbytes Hhost Hruntime Henv

private abbrev func16Locals (result ignored ptr length : UInt32)
    (values : List Value := []) : Locals :=
  ⟨[.i32 result, .i32 ignored, .i32 ptr, .i32 length], [], values⟩

/-- Body contract for generated WAT function 19, the Rust `Read::read`
adapter. -/
theorem func16_body {hlc : HasLC}
    [WasmSmallStepGS hlc Universal.State]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Universal.State)}
    (result ignored ptr length : UInt32) (old : List UInt8)
    (host : Universal.State) (oldTag : UInt8) (oldLength : UInt32)
    (hlen : length.toNat = old.length) (hpos : 0 < old.length)
    (hptr : ptr.toNat + old.length < UInt32.size)
    (hresult : result.toNat + 8 < UInt32.size)
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn ⟨0⟩ Project.HexStdio.«module» ∗
      hostEnvOwn 0 (Universal.envFor Project.HexStdio.«module») ∗
      hostStateOwn host ∗ pointsToBytes 0 ptr old ∗
      (⟨0, result⟩ ↦w oldTag) ∗
      pointsTo_u32 0 (result + 4) oldLength ∗
      (runtimeModuleOwn ⟨0⟩ Project.HexStdio.«module» -∗
        hostEnvOwn 0 (Universal.envFor Project.HexStdio.«module») -∗
        hostStateOwn (afterRead host (bytesRead host length)) -∗
        pointsToBytes 0 ptr
          (bytesRead host length ++ old.drop (bytesRead host length).length) -∗
        (⟨0, result⟩ ↦w (4 : UInt8)) -∗
        pointsTo_u32 0 (result + 4)
          (UInt32.ofNat (bytesRead host length).length) -∗
        WP (.running
          ⟨func16Locals result ignored
              (UInt32.ofNat (bytesRead host length).length) length,
            [], arity, remainder, controls, calls⟩ : Expr Universal.State)
          @ s; E [{ Φ }]) ⊢
      WP (.running
        ⟨func16Locals result ignored ptr length,
          Project.HexStdio.func16, arity, remainder, controls, calls⟩ :
            Expr Universal.State) @ s; E [{ Φ }] := by
  obtain ⟨r4, r5, r6, r7⟩ :=
    Submission.Helpers.wordAccessFacts result 4 (by
      norm_num [UInt32.size] at hresult ⊢
      omega)
  iintro ⟨Hruntime, Henv, Hhost, Hbytes, Htag, Hlength, Hnext⟩
  simp only [Project.HexStdio.func16, func16Locals]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_universal_read ptr length old host hlen hpos hptr ⟨0⟩
      (params := [.i32 result, .i32 ignored, .i32 ptr, .i32 length])
      (localValues := []) (values := [])
      (code := [.localSet 2, .localGet 0, .const 4, .store8 0,
        .localGet 0, .localGet 2, .store32 4])
      $$ Hbytes Hhost Hruntime Henv
  iintro Hbytes Hhost Hruntime Henv
  iapply twp_localSet rfl
  iapply twp_localGet rfl
  iapply twp_const
  iapply Submission.TotalHelpers.twp_store8_zero oldTag $$ Htag
  iintro Htag
  ihave Htag' : (⟨0, result⟩ ↦w (4 : UInt8)) $$ [Htag]
  · norm_num
    iexact Htag
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 oldLength r4 r5 r6 r7 $$ Hlength
  iintro Hlength
  simp [func16Locals, List.set]
  iapply Hnext $$ Hruntime Henv Hhost Hbytes Htag' Hlength

/-- Caller-side total contract for generated WAT function 19. -/
theorem twp_call_func16 {hlc : HasLC}
    [WasmSmallStepGS hlc Universal.State]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Universal.State)}
    (result ignored ptr length : UInt32) (old : List UInt8)
    (host : Universal.State) (oldTag : UInt8) (oldLength : UInt32)
    (hlen : length.toNat = old.length) (hpos : 0 < old.length)
    (hptr : ptr.toNat + old.length < UInt32.size)
    (hresult : result.toNat + 8 < UInt32.size)
    {callerLocals : Locals} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {stack : List Value} :
    runtimeModuleOwn ⟨0⟩ Project.HexStdio.«module» ∗
      hostEnvOwn 0 (Universal.envFor Project.HexStdio.«module») ∗
      hostStateOwn host ∗ pointsToBytes 0 ptr old ∗
      (⟨0, result⟩ ↦w oldTag) ∗
      pointsTo_u32 0 (result + 4) oldLength ∗
      (runtimeModuleOwn ⟨0⟩ Project.HexStdio.«module» -∗
        hostEnvOwn 0 (Universal.envFor Project.HexStdio.«module») -∗
        hostStateOwn (afterRead host (bytesRead host length)) -∗
        pointsToBytes 0 ptr
          (bytesRead host length ++ old.drop (bytesRead host length).length) -∗
        (⟨0, result⟩ ↦w (4 : UInt8)) -∗
        pointsTo_u32 0 (result + 4)
          (UInt32.ofNat (bytesRead host length).length) -∗
        WP (.running ⟨{ callerLocals with values := stack }, code,
          arity, remainder, controls, calls⟩ : Expr Universal.State)
          @ s; E [{ Φ }]) ⊢
      WP (.running
        ⟨{ callerLocals with values :=
            (.i32 length :: .i32 ptr :: .i32 ignored :: .i32 result :: stack) },
          .call 19 :: code, arity, remainder, controls, calls⟩ :
            Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Henv, Hhost, Hbytes, Htag, Hlength, Hnext⟩
  iapply Wasm.SmallStep.twp_call Project.HexStdio.«module» 19
    Project.HexStdio.func16Def (by decide) (by rfl) ⟨0⟩ $$ Hruntime
  iintro Hruntime
  simp [Project.HexStdio.func16Def, Function.toLocals, Function.numParams,
    ValueType.zero]
  iapply func16_body result ignored ptr length old host oldTag oldLength
    hlen hpos hptr hresult (controls := [])
    (calls :=
      { locals := { callerLocals with values := stack }, continuation := code,
        resultArity := arity, callerRemainder := remainder, control := controls,
        returningInstance := ⟨0⟩ } :: calls)
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Henv]
  · iexact Henv
  isplitl [Hhost]
  · iexact Hhost
  isplitl [Hbytes]
  · iexact Hbytes
  isplitl [Htag]
  · iexact Htag
  isplitl [Hlength]
  · iexact Hlength
  iintro Hruntime Henv Hhost Hbytes Htag Hlength
  iapply Submission.TotalIterator.hdtwp_returnFromCallFallthrough' $$ Hruntime
  iintro Hruntime
  simp only [List.take_zero, List.nil_append]
  iapply Hnext $$ Hruntime Henv Hhost Hbytes Htag Hlength

end Submission.TotalRead
