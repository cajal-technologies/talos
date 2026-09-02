import HexEncodeStdio.HDAllocator
import HexEncodeStdio.HDGrow
import HexEncodeStdio.Helpers

namespace Project.HexEncodeStdio.TotalAllocator

open Wasm Project.HexStdio
open Iris Iris.BI Iris.ProgramLogic Language.Notation
open Wasm.SepLogic Wasm.SmallStep

/-- The address returned by the generated bump allocator on its ordinary
return path. -/
def allocPtr (align oldBump : UInt32) : UInt32 :=
  ((if oldBump = 0 then 1054000 else oldBump) +
      ((0xffffffff : UInt32) + align)) &&& (-align)

@[simp] theorem allocPtr_align_one (oldBump : UInt32) :
    allocPtr 1 oldBump = if oldBump = 0 then 1054000 else oldBump := by
  simp only [allocPtr]
  have hmask : (0xffffffff : UInt32) + 1 = 0 := by bv_decide
  have hneg : -(1 : UInt32) = 0xffffffff := by bv_decide
  rw [hmask, hneg]
  bv_decide

@[simp] theorem allocPtr_initial_one : allocPtr 1 0 = 1054000 := by
  simp

/-- Ownership-producing total rule used at either allocator's `memory.grow`.
The failure continuation receives the architectural `-1`; on success the
continuation owns every byte in every newly exposed page. -/
theorem memoryGrow_alloc_outcome {hlc : HasLC} {α : Type}
    [WasmSmallStepGS hlc α]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF α)}
    {params localValues values : List Value} {delta : UInt32}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (runtimeModule : Module) (instanceId : ModuleInstanceId)
    (R : IProp (WasmHeapGF α))
    (hpages : ∀ (store : MachineStore α) (memory : Mem)
        (previousPages : Nat),
      store.runtime.currentModule = runtimeModule →
      store.wasm.mem.grow delta
          (store.wasm.memoryCap store.runtime.currentModule 0) =
        some (memory, previousPages) →
      memory.pages < 65536)
    (Hfail : runtimeModuleOwn instanceId runtimeModule ∗ R -∗
      WP (.running ⟨⟨params, localValues,
          .i32 (0xffffffff : UInt32) :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }])
    (Hsuccess : ∀ (store : MachineStore α) (memory : Mem)
        (previousPages : Nat)
        (hgrow : store.wasm.mem.grow delta
          (store.wasm.memoryCap store.runtime.currentModule 0) =
            some (memory, previousPages)),
      runtimeModuleOwn instanceId runtimeModule ∗ R ∗
          pointsToBytes 0 (UInt32.ofNat (previousPages * 65536))
            ((List.range (delta.toNat * 65536)).map fun i =>
              memory.read8
                (UInt32.ofNat (previousPages * 65536) + UInt32.ofNat i)) -∗
      WP (.running ⟨⟨params, localValues,
          .i32 previousPages.toUInt32 :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }]) :
    runtimeModuleOwn instanceId runtimeModule ∗ R -∗
    WP (.running ⟨⟨params, localValues, .i32 delta :: values⟩,
        .memoryGrow :: code, arity, remainder, controls, calls⟩ : Expr α) @
      s; E [{ Φ }] := by
  exact Project.HexEncodeStdio.twp_memoryGrow_fresh runtimeModule
    instanceId R hpages Hfail Hsuccess

/-- Caller-facing total contract for generated function 12 (Wasm index 15).

The caller supplies ownership of the range it intends to use at the allocator's
deterministic return address.  That ownership is framed through all allocator
steps.  Every non-returning arithmetic-overflow or failed-`memory.grow` path is
discharged by the Universal OOM host contract. -/
theorem func12_alloc_outcome {hlc : HasLC}
    [WasmSmallStepGS hlc Universal.State]
    {E : CoPset} {Φ : List Value → IProp (WasmHeapGF Universal.State)}
    (size align oldBump : UInt32) (host : Universal.State)
    (owned : List UInt8)
    (callerLocals : Locals) (stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame) :
    runtimeModuleOwn ⟨0⟩ «module» ∗
      hostEnvOwn 0 (Universal.envFor «module») ∗
      hostStateOwn host ∗
      pointsTo_u32 0 1053960 oldBump ∗
      pointsToBytes 0 (allocPtr align oldBump) owned -∗
    (runtimeModuleOwn ⟨0⟩ «module» ∗
      hostEnvOwn 0 (Universal.envFor «module») ∗
      hostStateOwn host ∗
      pointsTo_u32 0 1053960 (size + allocPtr align oldBump) ∗
      pointsToBytes 0 (allocPtr align oldBump) owned -∗
      WP (.running
        ⟨{ callerLocals with values :=
            (Value.i32 (allocPtr align oldBump) :: stack) },
          code, arity, remainder, controls, calls⟩ : Expr Universal.State) @
          Stuckness.MaybeStuck; E [{ Φ }]) -∗
    WP (.running
      ⟨{ callerLocals with values := [.i32 align, .i32 size] ++ stack },
        [.call 15] ++ code, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ Stuckness.MaybeStuck; E [{ Φ }] := by
  iintro ⟨Hruntime, Henv, Hhost, Hbump, Howned⟩ Hnext
  iapply Project.HexEncodeStdio.twp_allocator size align oldBump host
    callerLocals stack code arity remainder controls calls $$
      [$Hruntime $Henv $Hhost $Hbump]
  iintro ⟨Hruntime, Henv, Hhost, Hbump⟩
  isimp only [allocPtr] at Howned Hnext
  simp only [zero_sub]
  iapply Hnext
  iframe

/-- Arena form of `func12_alloc_outcome`.  This is the form used by callers:
the successful allocation is split from the front of the currently owned free
arena, while the untouched suffix remains available for the next allocation.
The initial arena is supplied by the adequacy heap map; newly grown page ranges
are supplied by `memoryGrow_alloc_outcome`. -/
theorem func12_alloc_from_arena {hlc : HasLC}
    [WasmSmallStepGS hlc Universal.State]
    {E : CoPset} {Φ : List Value → IProp (WasmHeapGF Universal.State)}
    (size align oldBump : UInt32) (host : Universal.State)
    (arena : List UInt8) (hsize : size.toNat ≤ arena.length)
    (callerLocals : Locals) (stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame) :
    runtimeModuleOwn ⟨0⟩ «module» ∗
      hostEnvOwn 0 (Universal.envFor «module») ∗
      hostStateOwn host ∗
      pointsTo_u32 0 1053960 oldBump ∗
      pointsToBytes 0 (allocPtr align oldBump) arena -∗
    (runtimeModuleOwn ⟨0⟩ «module» ∗
      hostEnvOwn 0 (Universal.envFor «module») ∗
      hostStateOwn host ∗
      pointsTo_u32 0 1053960 (size + allocPtr align oldBump) ∗
      pointsToBytes 0 (allocPtr align oldBump) (arena.take size.toNat) ∗
      pointsToBytes 0
        (allocPtr align oldBump + UInt32.ofNat size.toNat)
        (arena.drop size.toNat) -∗
      WP (.running
        ⟨{ callerLocals with values :=
            (Value.i32 (allocPtr align oldBump) :: stack) },
          code, arity, remainder, controls, calls⟩ : Expr Universal.State) @
          Stuckness.MaybeStuck; E [{ Φ }]) -∗
    WP (.running
      ⟨{ callerLocals with values := [.i32 align, .i32 size] ++ stack },
        [.call 15] ++ code, arity, remainder, controls, calls⟩ :
      Expr Universal.State) @ Stuckness.MaybeStuck; E [{ Φ }] := by
  iintro ⟨Hruntime, Henv, Hhost, Hbump, Harena⟩ Hnext
  iapply func12_alloc_outcome size align oldBump host arena callerLocals stack
      code arity remainder controls calls $$
    [$Hruntime $Henv $Hhost $Hbump $Harena]
  iintro ⟨Hruntime, Henv, Hhost, Hbump, Harena⟩
  ihave Harena := Project.HexEncodeStdio.Helpers.pointsToBytes_take_drop 0
    (allocPtr align oldBump) arena size.toNat hsize $$ Harena
  icases Harena with ⟨Hallocated, Hfree⟩
  iapply Hnext
  iframe

/-- The copy block at the end of generated realloc (`func15`). -/
def reallocCopyBlock : Instruction := .block 0 0
  [.localGet 2, .eqz, .br_if 0,
   .localGet 3, .localGet 1, .localGet 3, .localGet 1, .ltU, .select,
   .localTee 4, .eqz, .br_if 0,
   .localGet 2, .localGet 0, .localGet 4, .memoryCopy] [] []

/-- Successful post-allocation half of generated `func15`.  For the vector
growth case (`oldSize ≤ newSize`) it copies exactly the initialized old bytes,
returns the old range unchanged, and exposes the initialized prefix together
with the untouched tail of the new allocation. -/
theorem func15_copy_return {hlc : HasLC}
    [WasmSmallStepGS hlc Universal.State]
    {E : CoPset} {Φ : List Value → IProp (WasmHeapGF Universal.State)}
    (oldPtr oldSize newPtr newSize finish requiredPages pages : UInt32)
    (oldBytes newArena : List UInt8)
    (hlenOld : oldBytes.length = oldSize.toNat)
    (hlenNew : newArena.length = newSize.toNat)
    (hpos : 0 < oldSize.toNat)
    (hle : oldSize.toNat ≤ newSize.toNat)
    (hnewPtr : newPtr ≠ 0)
    (hnowrapOld : oldPtr.toNat + oldSize.toNat < UInt32.size)
    (hnowrapNew : newPtr.toNat + newSize.toNat < UInt32.size)
    (callerLocals : Locals) (stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (callerControls controls : List ControlFrame) (calls : List CallFrame)
    (R : IProp (WasmHeapGF Universal.State)) :
    runtimeModuleOwn ⟨0⟩ «module» ∗
      pointsToBytes 0 oldPtr oldBytes ∗
      pointsToBytes 0 newPtr newArena ∗
      R ∗
      (runtimeModuleOwn ⟨0⟩ «module» -∗
        pointsToBytes 0 oldPtr oldBytes -∗
        pointsToBytes 0 newPtr
          (oldBytes ++ newArena.drop oldSize.toNat) -∗
        R -∗
        WP (.running
          ⟨{ callerLocals with values := .i32 newPtr :: stack },
            code, arity, remainder, callerControls, calls⟩ :
            Expr Universal.State) @ Stuckness.MaybeStuck; E [{ Φ }]) -∗
    WP (.running
      ⟨⟨[.i32 oldPtr, .i32 oldSize, .i32 newPtr, .i32 newSize],
          [.i32 finish, .i32 requiredPages, .i32 pages], []⟩,
        [.block 0 0
            [.localGet 2, .eqz, .br_if 0,
             .localGet 3, .localGet 1, .localGet 3, .localGet 1, .ltU,
             .select, .localTee 4, .eqz, .br_if 0,
             .localGet 2, .localGet 0, .localGet 4, .memoryCopy] [] [],
          .localGet 2, .ret], 1, [], controls,
        { locals := { callerLocals with values := stack },
          continuation := code, resultArity := arity,
          callerRemainder := remainder, control := callerControls,
          returningInstance := ⟨0⟩ } :: calls⟩ : Expr Universal.State) @
          Stuckness.MaybeStuck; E [{ Φ }] := by
  have hnotlt : ¬ newSize < oldSize := by
    rw [UInt32.not_lt]
    exact hle
  have holdNe : oldSize ≠ 0 := by
    intro hz
    subst oldSize
    simp at hpos
  have hlenTake : (newArena.take oldSize.toNat).length = oldSize.toNat :=
    List.length_take_of_le (by rw [hlenNew]; exact hle)
  iintro ⟨Hruntime, Hold, Hnew, HR, Hnext⟩
  iapply twp_block
  iapply twp_localGet rfl
  iapply twp_eqz rfl
  simp only [hnewPtr, ↓reduceIte]
  iapply twp_brIfZero
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_ltU rfl
  simp only [hnotlt, ↓reduceIte]
  iapply twp_select rfl
  simp
  iapply twp_localTee rfl
  iapply twp_eqz rfl
  simp only [holdNe, ↓reduceIte]
  iapply twp_brIfZero
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  ihave Hnew := Project.HexEncodeStdio.Helpers.pointsToBytes_take_drop 0 newPtr
    newArena oldSize.toNat (by rw [hlenNew]; exact hle) $$ Hnew
  icases Hnew with ⟨HnewPrefix, HnewSuffix⟩
  iapply twp_memoryCopy32 (len := oldSize)
      (newArena.take oldSize.toNat) oldBytes
      (by simpa [hlenTake]) (by simpa [hlenOld]) hpos
      (by omega) hnowrapOld $$ Hold HnewPrefix
  iintro Hold HnewPrefix
  iapply twp_exitControl rfl
  iapply twp_localGet rfl
  iapply twp_returnFromCallExplicit
      (module := «module») (returningInstance := ⟨0⟩) $$ Hruntime
  iintro Hruntime
  simp
  ihave Hnew : pointsToBytes 0 newPtr
      (oldBytes ++ newArena.drop oldSize.toNat) $$ [HnewPrefix HnewSuffix]
  · iapply (pointsToBytes_append 0 newPtr oldBytes
      (newArena.drop oldSize.toNat)).mpr
    rw [hlenOld, UInt32.ofNat_toNat]
    iframe
  iapply Hnext $$ Hruntime Hold Hnew HR

end Project.HexEncodeStdio.TotalAllocator
