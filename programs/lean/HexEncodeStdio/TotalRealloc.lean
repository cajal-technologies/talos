import HexEncodeStdio.TotalAllocator

namespace Submission.TotalRealloc

open Wasm Project.HexStdio
open Iris Iris.BI Iris.ProgramLogic Language.Notation Iris.Std
open Wasm.SepLogic Wasm.SmallStep

private theorem module_memIs64 : «module».memIs64 = false := by rfl

private theorem twp_store_bump
    {hlc : HasLC} [WasmSmallStepGS hlc Universal.State]
    {E : CoPset} {Φ : List Value → IProp (WasmHeapGF Universal.State)}
    {params localValues values : List Value} {value : UInt32}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (oldWord : UInt32) :
    pointsTo_u32 0 1053960 oldWord -∗
    (pointsTo_u32 0 1053960 value -∗
      WP (.running ⟨⟨params, localValues, values⟩,
        code, arity, remainder, controls, calls⟩ : Expr Universal.State) @
        Stuckness.MaybeStuck; E [{ Φ }]) -∗
    WP (.running
      ⟨⟨params, localValues, .i32 value :: .i32 0 :: values⟩,
        .store32 1053960 :: code, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ Stuckness.MaybeStuck; E [{ Φ }] := by
  simpa only [UInt32.zero_add] using
    (twp_store32 (α := Universal.State) (s := Stuckness.MaybeStuck)
      (E := E) (Φ := Φ) (address := 0) (offset := 1053960)
      (value := value) (params := params) (localValues := localValues)
      (values := values) (code := code) (arity := arity)
      (remainder := remainder) (controls := controls) (calls := calls)
      oldWord (by decide) (by decide) (by decide) (by decide))

/-- Complete total caller contract for generated realloc (`func15`, Wasm index
18) in the byte-vector case.  The generated callers always use alignment one
and grow rather than shrink.  Arithmetic overflow and failed memory growth
terminate through the Universal OOM host; an ordinary return preserves the old
bytes and copies them into the front of the supplied new arena. -/
theorem func15_realloc_outcome {hlc : HasLC}
    [WasmSmallStepGS hlc Universal.State]
    {E : CoPset} {Φ : List Value → IProp (WasmHeapGF Universal.State)}
    (oldPtr oldSize newSize oldBump : UInt32) (host : Universal.State)
    (oldBytes newArena : List UInt8)
    (hlenOld : oldBytes.length = oldSize.toNat)
    (hlenNew : newArena.length = newSize.toNat)
    (hpos : 0 < oldSize.toNat)
    (hle : oldSize.toNat ≤ newSize.toNat)
    (hfinish : (Submission.TotalAllocator.allocPtr 1 oldBump).toNat +
        newSize.toNat < 2147483648)
    (hnegative : ¬ (newSize +
        Submission.TotalAllocator.allocPtr 1 oldBump).toInt32 <
        UInt32.toInt32 0)
    (hnowrapOld : oldPtr.toNat + oldSize.toNat < UInt32.size)
    (callerLocals : Locals) (stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame) :
    runtimeModuleOwn ⟨0⟩ «module» ∗
      hostEnvOwn 0 (Universal.envFor «module») ∗
      hostStateOwn host ∗
      pointsTo_u32 0 1053960 oldBump ∗
      pointsToBytes 0 oldPtr oldBytes ∗
      pointsToBytes 0 (Submission.TotalAllocator.allocPtr 1 oldBump)
        newArena -∗
    (runtimeModuleOwn ⟨0⟩ «module» ∗
      hostEnvOwn 0 (Universal.envFor «module») ∗
      hostStateOwn host ∗
      pointsTo_u32 0 1053960
        (newSize + Submission.TotalAllocator.allocPtr 1 oldBump) ∗
      pointsToBytes 0 oldPtr oldBytes ∗
      pointsToBytes 0 (Submission.TotalAllocator.allocPtr 1 oldBump)
        (oldBytes ++ newArena.drop oldSize.toNat) -∗
      WP (.running
        ⟨{ callerLocals with values :=
            (Value.i32 (Submission.TotalAllocator.allocPtr 1 oldBump) :: stack) },
          code, arity, remainder, controls, calls⟩ : Expr Universal.State) @
          Stuckness.MaybeStuck; E [{ Φ }]) -∗
    WP (.running
      ⟨{ callerLocals with values :=
          [.i32 newSize, .i32 1, .i32 oldSize, .i32 oldPtr] ++ stack },
        [.call 18] ++ code, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ Stuckness.MaybeStuck; E [{ Φ }] := by
  let ptr := Submission.TotalAllocator.allocPtr 1 oldBump
  have hptr : ptr = if oldBump = 0 then 1054000 else oldBump := by
    simp [ptr]
  have hptrNe : ptr ≠ 0 := by
    rw [hptr]
    by_cases h : oldBump = 0 <;> simp [h]
  have hptrMask : ptr &&& ((0 : UInt32) - 1) = ptr := by bv_decide
  have hnowrapNew : ptr.toNat + newSize.toNat < UInt32.size := by
    change ptr.toNat + newSize.toNat < 2147483648 at hfinish
    norm_num [UInt32.size]
    omega
  have hfinishNoWrap : (newSize + ptr).toNat =
      newSize.toNat + ptr.toNat := by
    rw [UInt32.toNat_add]
    change ptr.toNat + newSize.toNat < 2147483648 at hfinish
    omega
  have hoverflow₂ : ¬ newSize + ptr < ptr := by
    rw [UInt32.not_lt, UInt32.le_iff_toNat_le, hfinishNoWrap]
    omega
  change ¬ (newSize + ptr).toInt32 < UInt32.toInt32 0 at hnegative
  iintro ⟨Hruntime, Henv, Hhost, Hbump, Hold, Hnew⟩ Hnext
  simp only [List.singleton_append]
  iapply twp_call «module» 18 func15Def (by decide) rfl ⟨0⟩ $$ Hruntime
  iintro Hruntime
  simp [func15Def, Function.toLocals, Function.numParams,
    ValueType.zero, func15]
  iapply twp_block
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  iapply twp_localTee rfl
  iapply twp_const
  ihave Hbump0 : pointsTo_u32 0 ((0 : UInt32) + 1053960) oldBump $$ [Hbump]
  · norm_num
    iexact Hbump
  iapply twp_load32 (address := 0) (offset := 1053960) oldBump
      (by decide) (by decide) (by decide) (by decide) $$ Hbump0
  iintro Hbump
  ihave HbumpNorm : pointsTo_u32 0 1053960 oldBump $$ [Hbump]
  · isimp only [UInt32.zero_add] at Hbump
    iexact Hbump
  iapply twp_localTee rfl
  iapply twp_const
  iapply twp_localGet rfl
  iapply hdtwp_select rfl
  simp
  rw [show (if oldBump = 0 then Value.i32 1054000 else Value.i32 oldBump) =
      Value.i32 ptr by rw [hptr]; by_cases h : oldBump = 0 <;> simp [h]]
  iapply twp_add
  iapply twp_localTee rfl
  iapply twp_localGet rfl
  iapply twp_ltU rfl
  simp
  iapply twp_brIfZero
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_localGet rfl
  iapply twp_sub
  iapply twp_and
  rw [hptrMask]
  iapply twp_localTee rfl
  iapply twp_localGet rfl
  iapply twp_add
  iapply twp_localTee rfl
  iapply twp_localGet rfl
  iapply twp_ltU rfl
  simp only [hoverflow₂, ↓reduceIte]
  iapply twp_brIfZero
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_ltS rfl
  simp only [hnegative, ↓reduceIte]
  iapply twp_brIfZero
  iapply twp_block
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  iapply twp_const
  iapply hdtwp_shrU
  iapply twp_localTee rfl
  isimp only [← hptr] at Hnew Hnext
  ihave HmemorySize : runtimeModuleOwn ⟨0⟩ «module» ∗
      (hostEnvOwn 0 (Universal.envFor «module») ∗
        hostStateOwn host ∗ pointsTo_u32 0 1053960 oldBump ∗
        pointsToBytes 0 oldPtr oldBytes ∗ pointsToBytes 0 ptr newArena ∗
        (runtimeModuleOwn ⟨0⟩ «module» ∗
          hostEnvOwn 0 (Universal.envFor «module») ∗ hostStateOwn host ∗
          pointsTo_u32 0 1053960 (newSize + ptr) ∗
          pointsToBytes 0 oldPtr oldBytes ∗
          pointsToBytes 0 ptr (oldBytes ++ newArena.drop oldSize.toNat) -∗
          WP (.running
            ⟨{ callerLocals with values := .i32 ptr :: stack }, code, arity,
              remainder, controls, calls⟩ : Expr Universal.State) @
              Stuckness.MaybeStuck; E [{ Φ }])) $$
      [Hruntime Henv Hhost HbumpNorm Hold Hnew Hnext]
  · iframe
  iapply hdtwp_memorySize «module» ⟨0⟩ _ $$ HmemorySize
  iintro %pages ⟨Hruntime, Henv, Hhost, Hbump, Hold, Hnew, Hnext⟩
  rw [module_memIs64]
  simp only [sizeValue, Bool.false_eq_true, if_false]
  iapply twp_localTee rfl
  iapply hdtwp_leU rfl
  by_cases henough :
      ((65535 + (newSize + ptr)) >>> (16 % 32)) ≤ UInt32.ofNat pages
  · rw [if_pos henough]
    iapply twp_brIf (by decide) rfl
    simp
    iapply twp_const
    iapply twp_localGet rfl
    iapply twp_store_bump oldBump $$ Hbump
    iintro Hbump
    ihave HcopyNext :
        runtimeModuleOwn ⟨0⟩ «module» -∗
          pointsToBytes 0 oldPtr oldBytes -∗
          pointsToBytes 0 ptr (oldBytes ++ newArena.drop oldSize.toNat) -∗
          (hostEnvOwn 0 (Universal.envFor «module») ∗
            hostStateOwn host ∗
            pointsTo_u32 0 1053960 (newSize + ptr)) -∗
          WP (.running
            ⟨{ callerLocals with values := .i32 ptr :: stack }, code, arity,
              remainder, controls, calls⟩ : Expr Universal.State) @
              Stuckness.MaybeStuck; E [{ Φ }] $$ [Hnext]
    · iintro Hruntime Hold Hnew ⟨Henv, Hhost, Hbump⟩
      iapply Hnext
      iframe
    iapply Submission.TotalAllocator.func15_copy_return oldPtr oldSize ptr
      newSize (newSize + ptr) ((65535 + (newSize + ptr)) >>> 16)
      (UInt32.ofNat pages) oldBytes newArena hlenOld hlenNew hpos hle hptrNe
      hnowrapOld hnowrapNew callerLocals stack code arity remainder controls
      _ calls (iprop% hostEnvOwn 0 (Universal.envFor «module») ∗
        hostStateOwn host ∗ pointsTo_u32 0 1053960 (newSize + ptr))
      $$ [$Hruntime $Hold $Hnew $Henv $Hhost $Hbump $HcopyNext]
  · simp only [henough, ↓reduceIte]
    iapply twp_brIfZero
    iapply twp_localGet rfl
    iapply twp_localGet rfl
    iapply twp_sub
    ihave HmemoryGrow : runtimeModuleOwn ⟨0⟩ «module» ∗
        (hostEnvOwn 0 (Universal.envFor «module») ∗ hostStateOwn host ∗
          pointsTo_u32 0 1053960 oldBump ∗ pointsToBytes 0 oldPtr oldBytes ∗
          pointsToBytes 0 ptr newArena ∗
          (runtimeModuleOwn ⟨0⟩ «module» ∗
            hostEnvOwn 0 (Universal.envFor «module») ∗ hostStateOwn host ∗
            pointsTo_u32 0 1053960 (newSize + ptr) ∗
            pointsToBytes 0 oldPtr oldBytes ∗
            pointsToBytes 0 ptr (oldBytes ++ newArena.drop oldSize.toNat) -∗
            WP (.running
              ⟨{ callerLocals with values := .i32 ptr :: stack }, code, arity,
                remainder, controls, calls⟩ : Expr Universal.State) @
                Stuckness.MaybeStuck; E [{ Φ }])) $$
        [Hruntime Henv Hhost Hbump Hold Hnew Hnext]
    · iframe
    iapply hdtwp_memoryGrow «module» ⟨0⟩ _ $$ HmemoryGrow
    iintro %growResult ⟨Hruntime, Henv, Hhost, Hbump, Hold, Hnew, Hnext⟩
    iapply twp_const
    iapply hdtwp_eq rfl
    by_cases hgrow : growResult = (0xffffffff : UInt32)
    · simp only [hgrow, ↓reduceIte]
      iapply twp_brIf (by decide) rfl
      simp
      iapply Submission.HexDecodeStdio.twp_oom_wrapper_locals host
        (stack := []) (code := [.unreachable])
      iframe
    · simp only [hgrow, ↓reduceIte]
      iapply twp_brIfZero
      iapply twp_exitControl rfl
      simp
      iapply twp_const
      iapply twp_localGet rfl
      iapply twp_store_bump oldBump $$ Hbump
      iintro Hbump
      ihave HcopyNext :
          runtimeModuleOwn ⟨0⟩ «module» -∗
            pointsToBytes 0 oldPtr oldBytes -∗
            pointsToBytes 0 ptr (oldBytes ++ newArena.drop oldSize.toNat) -∗
            (hostEnvOwn 0 (Universal.envFor «module») ∗
              hostStateOwn host ∗
              pointsTo_u32 0 1053960 (newSize + ptr)) -∗
            WP (.running
              ⟨{ callerLocals with values := .i32 ptr :: stack }, code, arity,
                remainder, controls, calls⟩ : Expr Universal.State) @
                Stuckness.MaybeStuck; E [{ Φ }] $$ [Hnext]
      · iintro Hruntime Hold Hnew ⟨Henv, Hhost, Hbump⟩
        iapply Hnext
        iframe
      iapply Submission.TotalAllocator.func15_copy_return oldPtr oldSize ptr
        newSize (newSize + ptr) ((65535 + (newSize + ptr)) >>> 16)
        (UInt32.ofNat pages) oldBytes newArena hlenOld hlenNew hpos hle hptrNe
        hnowrapOld hnowrapNew callerLocals stack code arity remainder controls
        _ calls (iprop% hostEnvOwn 0 (Universal.envFor «module») ∗
          hostStateOwn host ∗ pointsTo_u32 0 1053960 (newSize + ptr))
        $$ [$Hruntime $Hold $Hnew $Henv $Hhost $Hbump $HcopyNext]

end Submission.TotalRealloc
