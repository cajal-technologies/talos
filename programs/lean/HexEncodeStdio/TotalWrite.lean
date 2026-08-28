import Mathlib
import CodeLib
import Project.HexStdio.Spec
import HexEncodeStdio.Host
import HexEncodeStdio.TotalHost
import HexEncodeStdio.TotalHelpers
import HexEncodeStdio.TotalIterator

namespace Project.HexEncodeStdio.TotalWrite

open Wasm
open Iris Iris.BI Iris.ProgramLogic Language.Notation Iris.Std
open Wasm.SepLogic Wasm.SmallStep

def afterWrite (host : Universal.State) (bytes : List UInt8) : Universal.State :=
  { host with stdio :=
      { input := host.stdio.input
        output := host.stdio.output ++ bytes } }

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

/-- A universal-host write call returns, preserves its owned byte range, and
appends exactly that range to the observable output. -/
theorem twp_universal_write {hlc : HasLC}
    [WasmSmallStepGS hlc Universal.State]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Universal.State)}
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
    runtimeModuleOwn callerId Project.HexStdio.«module» -∗
    hostEnvOwn callerId.id
      (Universal.envFor Project.HexStdio.«module») -∗
    (pointsToBytes 0 ptr bytes -∗
      hostStateOwn (afterWrite host bytes) -∗
      runtimeModuleOwn callerId Project.HexStdio.«module» -∗
      hostEnvOwn callerId.id
        (Universal.envFor Project.HexStdio.«module») -∗
      WP (.running
        ⟨⟨params, localValues, values⟩, code,
          arity, remainder, controls, calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }]) -∗
    WP (.running
      ⟨⟨params, localValues, .i32 ptr :: .i32 length :: values⟩,
        .call 1 :: code, arity, remainder, controls, calls⟩ :
          Expr Universal.State) @ s; E [{ Φ }] := by
  obtain ⟨hostFn, hhostFn, hresolve⟩ := Project.HexEncodeStdio.Host.universal_write_resolver
  have htransfer : ∀ (store : MachineStore Universal.State) ns obs nt,
      store.runtime.currentModule = Project.HexStdio.«module» →
      store.runtime.currentHost =
        Universal.envFor Project.HexStdio.«module» →
      iprop(pointsToBytes 0 ptr bytes ∗ hostStateOwn host) ∗
          stateInterp (GF := WasmHeapGF Universal.State) store ns obs nt ==∗
        ∃ results postWasm,
          ⌜hostFn.invoke store.wasm
              ((.i32 ptr :: .i32 length :: values).take
                Project.HexStdio.«module».imports[1].params.length).reverse =
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
    imod Project.HexEncodeStdio.TotalHost.stateInterp_host_set_expected
        store ns obs nt host newHost $$ [$Hσ $Hhost] with
      ⟨%HhostPhysical, Hσ, Hhost⟩
    have hinvoke : hostFn.invoke store.wasm [.i32 length, .i32 ptr] =
        .Return [] newWasm := by
      rw [hresolve]
      simp only [Project.HexEncodeStdio.Host.universalWriteHost, HostFn.lift]
      simp only [StdIO.writeHost, StdIO.writeResult]
      rw [if_pos]
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
      convert hinvoke using 1 <;> rfl
    isplitl [Hbytes Hhost]
    · isplitl [Hbytes]
      · iexact Hbytes
      · iexact Hhost
    · iexact Hσ
  iintro Hbytes Hhost Hruntime Henv Hnext
  iapply Project.HexEncodeStdio.TotalHost.twp_callHost_return_fupd
    Project.HexStdio.«module» 1 Project.HexStdio.«module».imports[1]
    hostFn (by decide) rfl
    (Universal.envFor Project.HexStdio.«module») hhostFn
    (iprop(pointsToBytes 0 ptr bytes ∗ hostStateOwn host))
    (fun _ => iprop(pointsToBytes 0 ptr bytes ∗
      hostStateOwn (afterWrite host bytes))) callerId htransfer
      $$ [$Hbytes $Hhost] Hruntime Henv
  iintro %preWasm %results %postWasm %hinvoke ⟨HQ, Hruntime, Henv⟩
  have hresults : results = [] := by
    have hargs :
        ((.i32 ptr :: .i32 length :: values).take
          Project.HexStdio.«module».imports[1].params.length).reverse =
          [.i32 length, .i32 ptr] := by rfl
    rw [hargs] at hinvoke
    rw [hresolve] at hinvoke
    by_cases hb : StdIO.rangeInBounds
        (preWasm.focus
          { get := Universal.State.stdio
            set := fun whole part => { whole with stdio := part } })
        ptr.toNat length.toNat
    · simp [Project.HexEncodeStdio.Host.universalWriteHost, HostFn.lift,
        StdIO.writeHost, StdIO.writeResult, hb] at hinvoke
      exact hinvoke.1
    · simp [Project.HexEncodeStdio.Host.universalWriteHost, HostFn.lift,
        StdIO.writeHost, StdIO.writeResult, hb] at hinvoke
  subst results
  icases HQ with ⟨Hbytes, Hhost⟩
  have hresultLen :
      Project.HexStdio.«module».imports[1].results.length = 0 := by rfl
  have hparamLen :
      Project.HexStdio.«module».imports[1].params.length = 2 := by rfl
  simp only [hresultLen, hparamLen, List.take_zero, List.nil_append,
    List.drop_succ_cons, List.drop_zero]
  iapply Hnext $$ Hbytes Hhost Hruntime Henv

private abbrev func17Locals (result ignored ptr length : UInt32)
    (values : List Value := []) : Locals :=
  ⟨[.i32 result, .i32 ignored, .i32 ptr, .i32 length], [], values⟩

/-- Body contract for generated WAT function 20, the Rust `Write::write`
adapter.  The universal write host consumes the whole supplied slice, after
which the adapter stores the successful `Result` tag and byte count. -/
theorem func17_body {hlc : HasLC}
    [WasmSmallStepGS hlc Universal.State]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Universal.State)}
    (result ignored ptr length : UInt32) (bytes : List UInt8)
    (host : Universal.State) (oldTag : UInt8) (oldLength : UInt32)
    (hlen : length.toNat = bytes.length) (hpos : 0 < bytes.length)
    (hptr : ptr.toNat + bytes.length < UInt32.size)
    (hresult : result.toNat + 8 < UInt32.size)
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn ⟨0⟩ Project.HexStdio.«module» ∗
      hostEnvOwn 0 (Universal.envFor Project.HexStdio.«module») ∗
      hostStateOwn host ∗ pointsToBytes 0 ptr bytes ∗
      (⟨0, result⟩ ↦w oldTag) ∗
      pointsTo_u32 0 (result + 4) oldLength ∗
      (runtimeModuleOwn ⟨0⟩ Project.HexStdio.«module» -∗
        hostEnvOwn 0 (Universal.envFor Project.HexStdio.«module») -∗
        hostStateOwn (afterWrite host bytes) -∗
        pointsToBytes 0 ptr bytes -∗
        (⟨0, result⟩ ↦w (4 : UInt8)) -∗
        pointsTo_u32 0 (result + 4) length -∗
        WP (.running
          ⟨func17Locals result ignored ptr length, [],
            arity, remainder, controls, calls⟩ : Expr Universal.State)
          @ s; E [{ Φ }]) ⊢
      WP (.running
        ⟨func17Locals result ignored ptr length,
          Project.HexStdio.func17, arity, remainder, controls, calls⟩ :
            Expr Universal.State) @ s; E [{ Φ }] := by
  obtain ⟨r4, r5, r6, r7⟩ :=
    Project.HexEncodeStdio.Helpers.wordAccessFacts result 4 (by
      norm_num [UInt32.size] at hresult ⊢
      omega)
  iintro ⟨Hruntime, Henv, Hhost, Hbytes, Htag, Hlength, Hnext⟩
  simp only [Project.HexStdio.func17, func17Locals]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_universal_write ptr length bytes host hlen hpos hptr ⟨0⟩
      (params := [.i32 result, .i32 ignored, .i32 ptr, .i32 length])
      (localValues := []) (values := [])
      (code := [.localGet 0, .const 4, .store8 0,
        .localGet 0, .localGet 3, .store32 4])
      $$ Hbytes Hhost Hruntime Henv
  iintro Hbytes Hhost Hruntime Henv
  iapply twp_localGet rfl
  iapply twp_const
  iapply Project.HexEncodeStdio.TotalHelpers.twp_store8_zero oldTag $$ Htag
  iintro Htag
  ihave Htag' : (⟨0, result⟩ ↦w (4 : UInt8)) $$ [Htag]
  · norm_num
    iexact Htag
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 oldLength r4 r5 r6 r7 $$ Hlength
  iintro Hlength
  iapply Hnext $$ Hruntime Henv Hhost Hbytes Htag' Hlength

/-- Caller-side contract for generated WAT function 20. -/
theorem twp_call_func17 {hlc : HasLC}
    [WasmSmallStepGS hlc Universal.State]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Universal.State)}
    (result ignored ptr length : UInt32) (bytes : List UInt8)
    (host : Universal.State) (oldTag : UInt8) (oldLength : UInt32)
    (hlen : length.toNat = bytes.length) (hpos : 0 < bytes.length)
    (hptr : ptr.toNat + bytes.length < UInt32.size)
    (hresult : result.toNat + 8 < UInt32.size)
    {callerLocals : Locals} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {stack : List Value} :
    runtimeModuleOwn ⟨0⟩ Project.HexStdio.«module» ∗
      hostEnvOwn 0 (Universal.envFor Project.HexStdio.«module») ∗
      hostStateOwn host ∗ pointsToBytes 0 ptr bytes ∗
      (⟨0, result⟩ ↦w oldTag) ∗
      pointsTo_u32 0 (result + 4) oldLength ∗
      (runtimeModuleOwn ⟨0⟩ Project.HexStdio.«module» -∗
        hostEnvOwn 0 (Universal.envFor Project.HexStdio.«module») -∗
        hostStateOwn (afterWrite host bytes) -∗
        pointsToBytes 0 ptr bytes -∗
        (⟨0, result⟩ ↦w (4 : UInt8)) -∗
        pointsTo_u32 0 (result + 4) length -∗
        WP (.running ⟨{ callerLocals with values := stack }, code,
          arity, remainder, controls, calls⟩ : Expr Universal.State)
          @ s; E [{ Φ }]) ⊢
      WP (.running
        ⟨{ callerLocals with values :=
            (.i32 length :: .i32 ptr :: .i32 ignored :: .i32 result :: stack) },
          .call 20 :: code, arity, remainder, controls, calls⟩ :
            Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Henv, Hhost, Hbytes, Htag, Hlength, Hnext⟩
  iapply Wasm.SmallStep.twp_call Project.HexStdio.«module» 20
    Project.HexStdio.func17Def (by decide) (by rfl) ⟨0⟩ $$ Hruntime
  iintro Hruntime
  simp [Project.HexStdio.func17Def, Function.toLocals, Function.numParams,
    ValueType.zero]
  iapply func17_body result ignored ptr length bytes host oldTag oldLength
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
  iapply Project.HexEncodeStdio.TotalIterator.hdtwp_returnFromCallFallthrough' $$ Hruntime
  iintro Hruntime
  simp only [List.take_zero, List.nil_append]
  iapply Hnext $$ Hruntime Henv Hhost Hbytes Htag Hlength

def writeOuterBody : Program :=
  match Project.HexStdio.func8[5]? with
  | some (Instruction.block _ _ body _ _) => body
  | _ => []

def writeLoopBody : Program :=
  match writeOuterBody[3]? with
  | some (Instruction.loop _ _ body _ _) => body
  | _ => []

theorem writeOuterBody_eq : writeOuterBody =
    [.localGet 1, .eqz, .br_if 0,
      .loop 0 0 writeLoopBody [] []] := by rfl

theorem func8_eq : Project.HexStdio.func8 =
    [.globalGet 0, .const 16, .sub, .localTee 2, .globalSet 0,
      .block 0 0 writeOuterBody [] [],
      .localGet 2, .const 16, .add, .globalSet 0] := by rfl

def writeAfterCall : Program := writeLoopBody.drop 7

theorem writeLoopBody_eq : writeLoopBody =
    [.localGet 2, .localGet 2, .const 15, .add,
      .localGet 0, .localGet 1, .call 20] ++ writeAfterCall := by rfl

def writeBlock0 : Program :=
  match writeAfterCall[0]? with
  | some (Instruction.block _ _ body _ _) => body
  | _ => []

def writeBlock1 : Program :=
  match writeBlock0[0]? with
  | some (Instruction.block _ _ body _ _) => body
  | _ => []

def writeBlock2 : Program :=
  match writeBlock1[0]? with
  | some (Instruction.block _ _ body _ _) => body
  | _ => []

def writeBlock3 : Program :=
  match writeBlock2[0]? with
  | some (Instruction.block _ _ body _ _) => body
  | _ => []

def writeBlock4 : Program :=
  match writeBlock3[0]? with
  | some (Instruction.block _ _ body _ _) => body
  | _ => []

def writeBlock5 : Program :=
  match writeBlock4[0]? with
  | some (Instruction.block _ _ body _ _) => body
  | _ => []

def writeBlock6 : Program :=
  match writeBlock5[0]? with
  | some (Instruction.block _ _ body _ _) => body
  | _ => []

def writeBlock5Tail : Program := writeBlock5.drop 1

def writeCountBlock : Program :=
  match writeBlock5Tail[0]? with
  | some (Instruction.block _ _ body _ _) => body
  | _ => []

def writeAfterCount : Program := writeBlock5Tail.drop 1

theorem writeAfterCall_eq : writeAfterCall =
    [.block 0 0 writeBlock0 [] [], .localGet 1, .br_if 0] := by rfl

theorem writeBlock0_eq : writeBlock0 =
    .block 0 0 writeBlock1 [] [] :: writeBlock0.drop 1 := by rfl
theorem writeBlock1_eq : writeBlock1 =
    .block 0 0 writeBlock2 [] [] :: writeBlock1.drop 1 := by rfl
theorem writeBlock2_eq : writeBlock2 =
    .block 0 0 writeBlock3 [] [] :: writeBlock2.drop 1 := by rfl
theorem writeBlock3_eq : writeBlock3 =
    .block 0 0 writeBlock4 [] [] :: writeBlock3.drop 1 := by rfl
theorem writeBlock4_eq : writeBlock4 =
    .block 0 0 writeBlock5 [] [] :: writeBlock4.drop 1 := by rfl
theorem writeBlock5_eq : writeBlock5 =
    .block 0 0 writeBlock6 [] [] :: writeBlock5Tail := by rfl
theorem writeBlock6_eq : writeBlock6 =
    [.localGet 2, .load8U 0, .localTee 3, .const 4, .eq, .br_if 0,
      .localGet 2, .localSet 4,
      .block 0 0 [.localGet 3, .brTable [4, 0, 3, 2] 4] [] [],
      .localGet 2, .load8U 1, .const 35, .eq, .br_if 6, .br 3] := by rfl
theorem writeBlock5Tail_eq : writeBlock5Tail =
    .block 0 0 writeCountBlock [] [] :: writeAfterCount := by rfl
theorem writeCountBlock_eq : writeCountBlock =
    [.localGet 2, .load32 4, .localTee 3, .br_if 0,
      .const 1049812, .localSet 4, .br 3] := by rfl
theorem writeAfterCount_eq : writeAfterCount =
    [.localGet 1, .localGet 3, .ltU, .br_if 3,
      .localGet 0, .localGet 3, .add, .localSet 0,
      .localGet 1, .localGet 3, .sub, .localTee 1,
      .br_if 6, .br 7] := by rfl

private abbrev func8Locals (ptr length stackPtr tag tmp4 tmp5 tmp6 : UInt32)
    (tmp7 : UInt64) (values : List Value := []) : Locals :=
  ⟨[.i32 ptr, .i32 length],
    [.i32 stackPtr, .i32 tag, .i32 tmp4, .i32 tmp5, .i32 tmp6, .i64 tmp7],
    values⟩

/-- The nonempty write loop executes exactly once under the universal host,
because that host writes the entire requested slice. -/
theorem func8_after_prologue_nonempty {hlc : HasLC}
    [WasmSmallStepGS hlc Universal.State]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Universal.State)}
    (ptr length stackPtr : UInt32) (bytes : List UInt8)
    (host : Universal.State) (oldTag : UInt8) (oldLength : UInt32)
    (tmp4 tmp5 tmp6 : UInt32) (tmp7 : UInt64)
    (hlen : length.toNat = bytes.length) (hpos : 0 < bytes.length)
    (hptr : ptr.toNat + bytes.length < UInt32.size)
    (hstack : stackPtr.toNat + 16 < UInt32.size)
    {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn ⟨0⟩ Project.HexStdio.«module» ∗
      hostEnvOwn 0 (Universal.envFor Project.HexStdio.«module») ∗
      hostStateOwn host ∗ globalPointsToAt 0 0 (.i32 stackPtr) ∗
      pointsToBytes 0 ptr bytes ∗ (⟨0, stackPtr⟩ ↦w oldTag) ∗
      pointsTo_u32 0 (stackPtr + 4) oldLength ∗
      (runtimeModuleOwn ⟨0⟩ Project.HexStdio.«module» -∗
        hostEnvOwn 0 (Universal.envFor Project.HexStdio.«module») -∗
        hostStateOwn (afterWrite host bytes) -∗
        globalPointsToAt 0 0 (.i32 (stackPtr + 16)) -∗
        pointsToBytes 0 ptr bytes -∗
        (⟨0, stackPtr⟩ ↦w (4 : UInt8)) -∗
        pointsTo_u32 0 (stackPtr + 4) length -∗
        WP (.running
          ⟨func8Locals (ptr + length) 0 stackPtr length tmp4 tmp5 tmp6 tmp7,
            [], arity, remainder, controls, calls⟩ : Expr Universal.State)
          @ s; E [{ Φ }]) ⊢
      WP (.running
        ⟨func8Locals ptr length stackPtr 0 tmp4 tmp5 tmp6 tmp7,
          .block 0 0 writeOuterBody [] [] ::
            [.localGet 2, .const 16, .add, .globalSet 0],
          arity, remainder, controls, calls⟩ : Expr Universal.State)
        @ s; E [{ Φ }] := by
  obtain ⟨p4, p5, p6, p7⟩ :=
    Project.HexEncodeStdio.Helpers.wordAccessFacts stackPtr 4 (by
      norm_num [UInt32.size] at hstack ⊢
      omega)
  iintro ⟨Hruntime, Henv, Hhost, Hglobal, Hbytes, Htag, Hlength, Hnext⟩
  have hlength_ne : length ≠ 0 := by
    intro hzero
    have hz : length.toNat = 0 := congrArg UInt32.toNat hzero
    norm_num at hz
    omega
  iapply twp_block
  rw [writeOuterBody_eq]
  iapply twp_localGet rfl
  iapply twp_eqz (result := 0) (by simp [hlength_ne])
  iapply twp_brIfZero
  iapply twp_loop
  rw [writeLoopBody_eq]
  simp only [List.cons_append, List.nil_append]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_call_func17 stackPtr (15 + stackPtr) ptr length bytes host
    oldTag oldLength hlen hpos hptr (by
      norm_num [UInt32.size] at hstack ⊢
      omega)
    (callerLocals := func8Locals ptr length stackPtr 0 tmp4 tmp5 tmp6 tmp7)
    (stack := []) (code := writeAfterCall)
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
  rw [writeAfterCall_eq]
  iapply twp_block
  rw [writeBlock0_eq]
  iapply twp_block
  rw [writeBlock1_eq]
  iapply twp_block
  rw [writeBlock2_eq]
  iapply twp_block
  rw [writeBlock3_eq]
  iapply twp_block
  rw [writeBlock4_eq]
  iapply twp_block
  rw [writeBlock5_eq]
  iapply twp_block
  rw [writeBlock6_eq]
  iapply twp_localGet rfl
  iapply Project.HexEncodeStdio.TotalIterator.twp_load8U_zero (4 : UInt8) $$ Htag
  iintro Htag
  iapply twp_localTee rfl
  iapply twp_const
  iapply Project.HexEncodeStdio.TotalIterator.hdtwp_eq (result := 1) (by simp)
  iapply twp_brIf (by decide) rfl
  rw [writeBlock5Tail_eq]
  iapply twp_block
  rw [writeCountBlock_eq]
  iapply twp_localGet rfl
  iapply twp_load32 length p4 p5 p6 p7 $$ Hlength
  iintro Hlength
  iapply twp_localTee rfl
  iapply twp_brIf hlength_ne rfl
  rw [writeAfterCount_eq]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_ltU (result := 0) (by simp)
  iapply twp_brIfZero
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_add
  iapply twp_localSet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_sub
  iapply twp_localTee rfl
  simp [func8Locals, List.set]
  iapply twp_brIfZero
  iapply twp_br (by rfl)
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  iapply twp_globalSet $$ Hglobal
  iintro Hglobal
  ihave Hglobal' :
      globalPointsToAt 0 0 (.i32 (stackPtr + 16)) $$ [Hglobal]
  · rw [UInt32.add_comm stackPtr 16]
    iexact Hglobal
  simp [func8Locals, List.set, UInt32.add_comm ptr length]
  iapply Hnext $$ Hruntime Henv Hhost Hglobal' Hbytes Htag Hlength

/-- Caller-side total contract for generated WAT function 11 on a nonempty
slice.  The function reserves its 16-byte frame, performs the complete write,
restores the stack global, and returns to its caller. -/
theorem twp_call_func8_nonempty {hlc : HasLC}
    [WasmSmallStepGS hlc Universal.State]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Universal.State)}
    (ptr length stackPtr : UInt32) (bytes : List UInt8)
    (host : Universal.State) (oldTag : UInt8) (oldLength : UInt32)
    (hlen : length.toNat = bytes.length) (hpos : 0 < bytes.length)
    (hptr : ptr.toNat + bytes.length < UInt32.size)
    (hstack : stackPtr.toNat + 16 < UInt32.size)
    {callerLocals : Locals} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {stack : List Value} :
    runtimeModuleOwn ⟨0⟩ Project.HexStdio.«module» ∗
      hostEnvOwn 0 (Universal.envFor Project.HexStdio.«module») ∗
      hostStateOwn host ∗
      globalPointsToAt 0 0 (.i32 (stackPtr + 16)) ∗
      pointsToBytes 0 ptr bytes ∗ (⟨0, stackPtr⟩ ↦w oldTag) ∗
      pointsTo_u32 0 (stackPtr + 4) oldLength ∗
      (runtimeModuleOwn ⟨0⟩ Project.HexStdio.«module» -∗
        hostEnvOwn 0 (Universal.envFor Project.HexStdio.«module») -∗
        hostStateOwn (afterWrite host bytes) -∗
        globalPointsToAt 0 0 (.i32 (stackPtr + 16)) -∗
        pointsToBytes 0 ptr bytes -∗
        (⟨0, stackPtr⟩ ↦w (4 : UInt8)) -∗
        pointsTo_u32 0 (stackPtr + 4) length -∗
        WP (.running ⟨{ callerLocals with values := stack }, code,
          arity, remainder, controls, calls⟩ : Expr Universal.State)
          @ s; E [{ Φ }]) ⊢
      WP (.running
        ⟨{ callerLocals with values := .i32 length :: .i32 ptr :: stack },
          .call 11 :: code, arity, remainder, controls, calls⟩ :
            Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Henv, Hhost, Hglobal, Hbytes, Htag, Hlength, Hnext⟩
  iapply Wasm.SmallStep.twp_call Project.HexStdio.«module» 11
    Project.HexStdio.func8Def (by decide) (by rfl) ⟨0⟩ $$ Hruntime
  iintro Hruntime
  simp [Project.HexStdio.func8Def, Function.toLocals, Function.numParams,
    ValueType.zero]
  rw [func8_eq]
  iapply twp_globalGet $$ Hglobal
  iintro Hglobal
  iapply twp_const
  iapply twp_sub
  rw [show stackPtr + 16 - 16 = stackPtr by bv_decide]
  iapply twp_localTee rfl
  iapply twp_globalSet $$ Hglobal
  iintro Hglobal
  simp [func8Locals, List.set]
  iapply func8_after_prologue_nonempty ptr length stackPtr bytes host oldTag
    oldLength 0 0 0 0 hlen hpos hptr hstack (controls := [])
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
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Hbytes]
  · iexact Hbytes
  isplitl [Htag]
  · iexact Htag
  isplitl [Hlength]
  · iexact Hlength
  iintro Hruntime Henv Hhost Hglobal Hbytes Htag Hlength
  iapply Project.HexEncodeStdio.TotalIterator.hdtwp_returnFromCallFallthrough' $$ Hruntime
  iintro Hruntime
  simp only [List.take_zero, List.nil_append]
  iapply Hnext $$ Hruntime Henv Hhost Hglobal Hbytes Htag Hlength

end Project.HexEncodeStdio.TotalWrite
