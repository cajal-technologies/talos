import HexEncodeStdio.TotalRealloc

namespace Project.HexEncodeStdio.TotalVecAlloc

open Wasm Project.HexStdio
open Iris Iris.BI Iris.ProgramLogic Language.Notation Iris.Std
open Wasm.SepLogic Wasm.SmallStep

private abbrev allocLocals (result oldSize oldPtr newSize : UInt32)
    (values : List Value := []) : Locals :=
  ⟨[.i32 result, .i32 oldSize, .i32 oldPtr, .i32 newSize], [], values⟩

private abbrev func4ReallocChoice : Program :=
  [.localGet 1, .eqz, .br_if 0, .localGet 2, .localGet 1, .const 1,
   .localGet 3, .call 18, .localSet 1, .br 1]

private abbrev func4AllocChoice : Program :=
  [.block 0 0 func4ReallocChoice [] [], .call 14, .localGet 3, .const 1,
   .call 15, .localSet 1]

private abbrev func4SuccessCheck : Program :=
  [.localGet 1, .br_if 0, .localGet 0, .localGet 3, .store32 8,
   .localGet 0, .const 1, .store32 4, .localGet 0, .const 1, .store32 0,
   .ret]

private abbrev func4SuccessTail : Program :=
  [.block 0 0 func4SuccessCheck [] [], .localGet 0, .localGet 3,
   .store32 8, .localGet 0, .localGet 1, .store32 4, .localGet 0,
   .const 0, .store32 0, .ret]

private abbrev func4MainBody : Program :=
  [.localGet 3, .const 0, .ltS, .br_if 0,
   .block 0 0 func4AllocChoice [] []] ++ func4SuccessTail

private abbrev func4NegativeTail : Program :=
  [.localGet 0, .const 0, .store32 4, .localGet 0, .const 1, .store32 0]

private abbrev func4AllocControls
    (result oldSize oldPtr newSize : UInt32) : List ControlFrame :=
  [{ kind := .block, paramArity := 0, resultArity := 0,
       body := func4AllocChoice, continuation := func4SuccessTail,
       belowStack := [] },
   { kind := .block, paramArity := 0, resultArity := 0,
       body := func4MainBody, continuation := func4NegativeTail,
       belowStack := [] }]

/-- Generated function 11 (Wasm index 14) is the allocator hook and returns
immediately in this module. -/
private theorem twp_call_func11 {hlc : HasLC}
    [WasmSmallStepGS hlc Universal.State]
    {E : CoPset} {Φ : List Value → IProp (WasmHeapGF Universal.State)}
    (callerLocals : Locals) (stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame) :
    runtimeModuleOwn ⟨0⟩ «module» ∗
      (runtimeModuleOwn ⟨0⟩ «module» -∗
        WP (.running ⟨{ callerLocals with values := stack }, code, arity,
          remainder, controls, calls⟩ : Expr Universal.State) @
          Stuckness.MaybeStuck; E [{ Φ }]) -∗
    WP (.running ⟨{ callerLocals with values := stack }, .call 14 :: code,
      arity, remainder, controls, calls⟩ : Expr Universal.State) @
      Stuckness.MaybeStuck; E [{ Φ }] := by
  iintro ⟨Hruntime, Hnext⟩
  iapply twp_call «module» 14 func11Def (by decide) rfl ⟨0⟩ $$ Hruntime
  iintro Hruntime
  simp [func11Def, Function.toLocals, Function.numParams, func11]
  iapply twp_returnFromCallExplicit
      (module := «module») (returningInstance := ⟨0⟩) $$ Hruntime
  iintro Hruntime
  simp
  iapply Hnext $$ Hruntime

/-- Syntactic presentation of the allocator rule for a concrete local frame.
This avoids record-update metavariables at generated call sites. -/
private theorem func12_alloc_outcome_explicit {hlc : HasLC}
    [WasmSmallStepGS hlc Universal.State]
    {E : CoPset} {Φ : List Value → IProp (WasmHeapGF Universal.State)}
    (size align oldBump : UInt32) (host : Universal.State)
    (owned : List UInt8) (params localValues stack : List Value)
    (code : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame) :
    runtimeModuleOwn ⟨0⟩ «module» ∗
      hostEnvOwn 0 (Universal.envFor «module») ∗ hostStateOwn host ∗
      pointsTo_u32 0 1053960 oldBump ∗
      pointsToBytes 0 (Project.HexEncodeStdio.TotalAllocator.allocPtr align oldBump) owned -∗
    (runtimeModuleOwn ⟨0⟩ «module» ∗
      hostEnvOwn 0 (Universal.envFor «module») ∗ hostStateOwn host ∗
      pointsTo_u32 0 1053960
        (size + Project.HexEncodeStdio.TotalAllocator.allocPtr align oldBump) ∗
      pointsToBytes 0 (Project.HexEncodeStdio.TotalAllocator.allocPtr align oldBump) owned -∗
      WP (.running ⟨⟨params, localValues,
          .i32 (Project.HexEncodeStdio.TotalAllocator.allocPtr align oldBump) :: stack⟩,
        code, arity, remainder, controls, calls⟩ : Expr Universal.State) @
        Stuckness.MaybeStuck; E [{ Φ }]) -∗
    WP (.running ⟨⟨params, localValues,
        [.i32 align, .i32 size] ++ stack⟩,
      [.call 15] ++ code, arity, remainder, controls, calls⟩ :
      Expr Universal.State) @ Stuckness.MaybeStuck; E [{ Φ }] := by
  simpa using Project.HexEncodeStdio.TotalAllocator.func12_alloc_outcome size align oldBump
    host owned ⟨params, localValues, []⟩ stack code arity remainder controls
    calls

/-- Fresh-allocation leg of generated vector allocation wrapper `func4`
(Wasm index 7).  A successful return publishes the allocated pointer and the
requested capacity in the caller's three-word result record.  Allocator
failure terminates via the Universal OOM host. -/
theorem func4_alloc_fresh {hlc : HasLC}
    [WasmSmallStepGS hlc Universal.State]
    {E : CoPset} {Φ : List Value → IProp (WasmHeapGF Universal.State)}
    (result ignored newSize oldBump : UInt32) (host : Universal.State)
    (arena : List UInt8) (old0 old4 old8 : UInt32)
    (hnegative : ¬ newSize.toInt32 < UInt32.toInt32 0)
    (hresult : result.toNat + 12 < UInt32.size)
    (callerLocals : Locals) (stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (R : IProp (WasmHeapGF Universal.State)) :
    R ∗ runtimeModuleOwn ⟨0⟩ «module» ∗
      hostEnvOwn 0 (Universal.envFor «module») ∗ hostStateOwn host ∗
      pointsTo_u32 0 1053960 oldBump ∗
      pointsToBytes 0 (Project.HexEncodeStdio.TotalAllocator.allocPtr 1 oldBump) arena ∗
      pointsTo_u32 0 result old0 ∗ pointsTo_u32 0 (result + 4) old4 ∗
      pointsTo_u32 0 (result + 8) old8 -∗
    (R ∗ runtimeModuleOwn ⟨0⟩ «module» ∗
      hostEnvOwn 0 (Universal.envFor «module») ∗ hostStateOwn host ∗
      pointsTo_u32 0 1053960
        (newSize + Project.HexEncodeStdio.TotalAllocator.allocPtr 1 oldBump) ∗
      pointsToBytes 0 (Project.HexEncodeStdio.TotalAllocator.allocPtr 1 oldBump) arena ∗
      pointsTo_u32 0 result 0 ∗
      pointsTo_u32 0 (result + 4)
        (Project.HexEncodeStdio.TotalAllocator.allocPtr 1 oldBump) ∗
      pointsTo_u32 0 (result + 8) newSize -∗
      WP (.running ⟨{ callerLocals with values := stack }, code, arity,
        remainder, controls, calls⟩ : Expr Universal.State) @
        Stuckness.MaybeStuck; E [{ Φ }]) -∗
    WP (.running
      ⟨{ callerLocals with values :=
          [.i32 newSize, .i32 ignored, .i32 0, .i32 result] ++ stack },
        .call 7 :: code, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ Stuckness.MaybeStuck; E [{ Φ }] := by
  let ptr := Project.HexEncodeStdio.TotalAllocator.allocPtr 1 oldBump
  have hptrNe : ptr ≠ 0 := by
    simp [ptr]
    by_cases h : oldBump = 0 <;> simp [h]
  obtain ⟨r0, r1, r2, r3⟩ :=
    Project.HexEncodeStdio.Helpers.wordAccessFacts result 0 (by
      norm_num [UInt32.size] at hresult ⊢
      omega)
  obtain ⟨r4, r5, r6, r7⟩ :=
    Project.HexEncodeStdio.Helpers.wordAccessFacts result 4 (by omega)
  obtain ⟨r8, r9, r10, r11⟩ :=
    Project.HexEncodeStdio.Helpers.wordAccessFacts result 8 (by omega)
  iintro ⟨HR, Hruntime, Henv, Hhost, Hbump, Harena, H0, H4, H8⟩ Hnext
  iapply twp_call «module» 7 func4Def (by decide) rfl ⟨0⟩ $$ Hruntime
  iintro Hruntime
  simp [func4Def, Function.toLocals, Function.numParams, func4]
  iapply twp_block
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_ltS rfl
  simp only [hnegative, ↓reduceIte]
  iapply twp_brIfZero
  iapply twp_block
  iapply twp_block
  iapply twp_localGet rfl
  iapply twp_eqz rfl
  iapply twp_brIf (by decide) rfl
  simp
  iapply twp_call «module» 14 func11Def (by decide) rfl ⟨0⟩ $$ Hruntime
  iintro Hruntime
  simp [func11Def, Function.toLocals, Function.numParams, func11]
  iapply twp_returnFromCallExplicit
      (module := «module») (returningInstance := ⟨0⟩) $$ Hruntime
  iintro Hruntime
  simp
  iapply twp_localGet rfl
  iapply twp_const
  isimp only [← Project.HexEncodeStdio.TotalAllocator.allocPtr_align_one] at Harena
  iapply func12_alloc_outcome_explicit newSize 1 oldBump host arena
      [.i32 result, .i32 0, .i32 ignored, .i32 newSize] [] [] [.localSet 1]
      0 [] (func4AllocControls result 0 ignored newSize)
      ({ locals := { callerLocals with values := stack },
         continuation := code, resultArity := arity,
         callerRemainder := remainder, control := controls,
         returningInstance := ⟨0⟩ } :: calls) $$
      [$Hruntime $Henv $Hhost $Hbump $Harena]
  iintro ⟨Hruntime, Henv, Hhost, Hbump, Harena⟩
  simp [allocLocals]
  iapply twp_localSet rfl
  iapply twp_exitControl rfl
  iapply twp_block
  iapply twp_localGet rfl
  iapply twp_brIf (by simpa [ptr] using hptrNe) rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 old8 r8 r9 r10 r11 $$ H8
  iintro H8
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 old4 r4 r5 r6 r7 $$ H4
  iintro H4
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_store32 old0 r0 r1 r2 r3 $$ H0
  iintro H0
  iapply twp_returnFromCallExplicit
      (module := «module») (returningInstance := ⟨0⟩) $$ Hruntime
  iintro Hruntime
  simp
  isimp only [← ptr] at Harena Hbump
  iapply Hnext
  iframe

end Project.HexEncodeStdio.TotalVecAlloc
