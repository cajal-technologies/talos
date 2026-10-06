import CodeLib
import Project.HexStdio.Spec
import HexEncodeStdio.Host
import HexEncodeStdio.Helpers
import HexEncodeStdio.TotalHelpers
import HexEncodeStdio.TotalIterator

namespace Project.HexEncodeStdio.TotalRead

open Wasm
open Iris Iris.BI Iris.ProgramLogic Language.Notation Iris.Std
open Wasm.SepLogic Wasm.SmallStep

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
          Expr Universal.State) @ s; E [{ Φ }] :=
  Wasm.SmallStep.twp_universal_read Project.HexStdio.«module»
    Project.HexStdio.Spec.module_imports ptr length old host
    hlen hpos hnowrap callerId

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
    Project.HexEncodeStdio.Helpers.wordAccessFacts result 4 (by
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
  iapply Project.HexEncodeStdio.TotalHelpers.twp_store8_zero oldTag $$ Htag
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
  iapply Project.HexEncodeStdio.TotalIterator.twp_returnFromCallFallthrough' $$ Hruntime
  iintro Hruntime
  simp only [List.take_zero, List.nil_append]
  iapply Hnext $$ Hruntime Henv Hhost Hbytes Htag Hlength

end Project.HexEncodeStdio.TotalRead
