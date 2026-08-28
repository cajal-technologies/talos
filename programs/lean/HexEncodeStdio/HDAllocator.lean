import Project.HexStdio.Spec
import CodeLib.SepLogic.SmallStepTotalLiftingAux

namespace Project.HexEncodeStdio

open Wasm Project.HexStdio Project.HexStdio.Spec
open Iris Iris.ProgramLogic Language.Notation
open Wasm.SepLogic Wasm.SmallStep

variable {hlc : outParam HasLC}

private theorem module_memIs64 : «module».memIs64 = false := by
  rfl

/-- The lens used by the universal host to embed the OOM component. -/
def universalOOMLens : HostLens Universal.State OOM.State :=
  { get := Universal.State.oom
    set := fun whole part => { whole with oom := part } }

theorem universal_oom_function :
    (Universal.envFor «module»).funcs[2]? =
      some (OOM.oomHost.lift universalOOMLens) := by
  have hs := universal_env_satisfies.lookup (i := 2) (by decide)
  obtain ⟨_hostFn, _contract, _hfn, _hcontract, _hsound⟩ := hs
  rfl

private theorem oomTrapTransfer
    [WasmSmallStepGS hlc Universal.State]
    (host : Universal.State)
    (store : MachineStore Universal.State) (ns : Nat)
    (obs : List StepKind) (nt : Nat)
    (_ : store.runtime.currentModule = «module»)
    (postWasm : Store Universal.State) (msg : String)
    (h : (OOM.oomHost.lift universalOOMLens).invoke store.wasm [] =
      .Trap postWasm msg) :
    hostStateOwn host ∗
        stateInterp (GF := WasmHeapGF Universal.State) store ns obs nt ==∗
      hostStateOwn {host with oom := { raised := true }} ∗
        stateInterp (GF := WasmHeapGF Universal.State)
          { store with wasm := postWasm } ns obs nt := by
  simp [OOM.oomHost, OOM.oomResult, HostFn.lift, universalOOMLens,
    Store.focus, Store.mapHost, Store.unfocus] at h
  obtain ⟨rfl, rfl⟩ := h
  iintro ⟨Hhost, Hstate⟩
  icases (stateInterp_eq store ns obs nt).mp $$ Hstate with
    ⟨%heap, %globals, %segments, %tables, %elements,
      %runtimeModules, %hostEnvs, Hheap, Hglobals, Hsegments, Htables,
      Helements, HruntimeModules, HruntimeModulePoints,
      HruntimeInstances, Hinstance, HhostEnvs, HhostAuth, %Hfacts, Hexc⟩
  ihave %heq : ⌜store.wasm.host = host⌝ $$ [HhostAuth Hhost]
  · iapply hostStateOwn_agree store.wasm.host host
    iframe
  rw [heq]
  let newHost : Universal.State := {host with oom := { raised := true }}
  imod hostStateOwn_update host newHost $$ [$HhostAuth $Hhost] with
    ⟨HhostAuth, Hhost⟩
  imodintro
  isplitl [Hhost]
  · iexact Hhost
  iapply (stateInterp_eq
    { store with wasm :=
        { store.wasm with host := newHost } } ns obs nt).mpr
  iexists heap, globals, segments, tables, elements, runtimeModules, hostEnvs
  iframe Hheap Hglobals Hsegments Htables Helements HruntimeModules
    HruntimeModulePoints HruntimeInstances Hinstance HhostEnvs HhostAuth Hexc
  ipureintro
  exact Hfacts

/-- A trapped expression is a valid terminal total-WP state when trapping is
allowed.  This is deliberately unavailable at `NotStuck`. -/
theorem twp_trapped_maybe
    [WasmSmallStepGS hlc Universal.State]
    {E : CoPset} {Φ : List Value → IProp (WasmHeapGF Universal.State)}
    (reason : TrapReason) :
    ⊢ WP (.trapped reason : Expr Universal.State) @ Stuckness.MaybeStuck; E
      [{ Φ }] := by
  iapply twp_lift_step_no_fork rfl
  iintro %store %ns %obs %nt Hstate
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    trivial
  iintro %κ %next %store' %forks %hstep
  rcases hstep with ⟨_, _, _, hwasm⟩
  exact False.elim (trapped_terminal hwasm)

/-- The private OOM wrapper (module function 16) reaches precisely the
distinguished universal-host trap and records the typed OOM marker. -/
theorem twp_oom_wrapper
    [WasmSmallStepGS hlc Universal.State]
    {E : CoPset} {Φ : List Value → IProp (WasmHeapGF Universal.State)}
    (host : Universal.State)
    (callerLocals : Locals) (stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame) :
    runtimeModuleOwn ⟨0⟩ «module» ∗
      hostEnvOwn 0 (Universal.envFor «module») ∗
      hostStateOwn host -∗
    WP (.running
      ⟨{ callerLocals with values := stack },
        [.call 16] ++ code, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ Stuckness.MaybeStuck; E [{ Φ }] := by
  iintro ⟨Hruntime, Henv, Hhost⟩
  simp only [List.singleton_append]
  iapply twp_call «module» 16 func13Def (by decide) rfl ⟨0⟩ $$ Hruntime
  iintro Hruntime
  simp [func13Def, Function.toLocals, Function.numParams,
    ValueType.zero, func13]
  iapply hdtwp_callHost «module» 2
      { module := "talos", name := "oom", params := [], results := [] }
      (OOM.oomHost.lift universalOOMLens)
      (by decide) rfl (Universal.envFor «module»)
      universal_oom_function
      (hostStateOwn host)
      (fun _ => iprop(False))
      (hostStateOwn {host with oom := { raised := true }})
      (iprop(False)) ⟨0⟩
      (fun _ _ _ _ _ results postWasm h => by
        simp [OOM.oomHost, OOM.oomResult, HostFn.lift,
          universalOOMLens, Store.focus, Store.mapHost, Store.unfocus] at h)
      (oomTrapTransfer host)
      (fun _ _ _ _ _ postWasm tag xs h => by
        simp [OOM.oomHost, OOM.oomResult, HostFn.lift,
          universalOOMLens, Store.focus, Store.mapHost, Store.unfocus] at h)
      $$ Hhost Hruntime Henv
  · iintro %pre %results %post %h ⟨Hfalse, _⟩
    iexfalso
    iexact Hfalse
  · iintro %pre %post %msg %h Hhost
    simp [OOM.oomHost, OOM.oomResult, HostFn.lift,
      universalOOMLens, Store.focus, Store.mapHost, Store.unfocus] at h
    obtain ⟨rfl, rfl⟩ := h
    iapply twp_trapped_maybe (.host OOM.trapMessage)
  · iintro %pre %post %tag %xs %h Hfalse
    iexfalso
    iexact Hfalse

/-- A syntactically normalized presentation of `twp_oom_wrapper`, useful
after the instruction rules have reduced a concrete locals record. -/
theorem twp_oom_wrapper_locals
    [WasmSmallStepGS hlc Universal.State]
    {E : CoPset} {Φ : List Value → IProp (WasmHeapGF Universal.State)}
    (host : Universal.State)
    (params localValues stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame) :
    runtimeModuleOwn ⟨0⟩ «module» ∗
      hostEnvOwn 0 (Universal.envFor «module») ∗
      hostStateOwn host -∗
    WP (.running
      ⟨⟨params, localValues, stack⟩,
        .call 16 :: code, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ Stuckness.MaybeStuck; E [{ Φ }] := by
  simpa only [List.singleton_append] using
    (twp_oom_wrapper (E := E) (Φ := Φ) host
      ⟨params, localValues, []⟩ stack code arity remainder controls calls)

/-- Rust's generated deallocator is a no-op for the bump allocator. -/
theorem twp_dealloc_noop
    [WasmSmallStepGS hlc Universal.State]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Universal.State)}
    (ptr size align : UInt32)
    (callerLocals : Locals) (stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame) :
    runtimeModuleOwn ⟨0⟩ «module» -∗
    (runtimeModuleOwn ⟨0⟩ «module» -∗
      WP (.running
        ⟨{ callerLocals with values := stack }, code, arity, remainder,
          controls, calls⟩ : Expr Universal.State) @ s; E [{ Φ }]) -∗
    WP (.running
      ⟨{ callerLocals with values :=
          [.i32 align, .i32 size, .i32 ptr] ++ stack },
        [.call 17] ++ code, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }] := by
  iintro Hruntime Hcont
  simp only [List.singleton_append]
  iapply twp_call «module» 17 func14Def (by decide) rfl ⟨0⟩ $$ Hruntime
  iintro Hruntime
  simp [func14Def, Function.toLocals, Function.numParams, func14]
  iapply hdtwp_returnFromCallFallthrough $$ Hruntime
  iintro Hruntime
  simp
  iapply Hcont
  iexact Hruntime

/-- Store rule specialized to the allocator's bump-pointer global. -/
private theorem twp_store_bump
    [WasmSmallStepGS hlc Universal.State]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Universal.State)}
    {params localValues values : List Value} {value : UInt32}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (oldWord : UInt32) :
    pointsTo_u32 0 1053960 oldWord -∗
    (pointsTo_u32 0 1053960 value -∗
      WP (.running ⟨⟨params, localValues, values⟩,
        code, arity, remainder, controls, calls⟩ : Expr Universal.State) @
        s; E [{ Φ }]) -∗
    WP (.running
      ⟨⟨params, localValues, .i32 value :: .i32 0 :: values⟩,
        .store32 1053960 :: code, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }] := by
  simpa only [UInt32.zero_add] using
    (twp_store32 (α := Universal.State) (s := s) (E := E) (Φ := Φ)
      (address := 0) (offset := 1053960) (value := value)
      (params := params) (localValues := localValues) (values := values)
      (code := code) (arity := arity) (remainder := remainder)
      (controls := controls) (calls := calls) oldWord
      (by decide) (by decide) (by decide) (by decide))

/-- Control-flow specification of the bump allocator.  On every ordinary
return it yields the aligned bump pointer and records the new end pointer;
all arithmetic-overflow and failed-growth paths terminate through OOM. -/
theorem twp_allocator
    [WasmSmallStepGS hlc Universal.State]
    {E : CoPset} {Φ : List Value → IProp (WasmHeapGF Universal.State)}
    (size align oldBump : UInt32) (host : Universal.State)
    (callerLocals : Locals) (stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame) :
    let mask := (0xffffffff : UInt32) + align
    let base := if oldBump = 0 then 1054000 else oldBump
    let candidate := base + mask
    let ptr := candidate &&& (0 - align)
    let finish := size + ptr
    runtimeModuleOwn ⟨0⟩ «module» ∗
      hostEnvOwn 0 (Universal.envFor «module») ∗
      hostStateOwn host ∗
      pointsTo_u32 0 1053960 oldBump -∗
    (runtimeModuleOwn ⟨0⟩ «module» ∗
      hostEnvOwn 0 (Universal.envFor «module») ∗
      hostStateOwn host ∗
      pointsTo_u32 0 1053960 finish -∗
      WP (.running
        ⟨{ callerLocals with values := .i32 ptr :: stack }, code, arity,
          remainder, controls, calls⟩ : Expr Universal.State) @
          Stuckness.MaybeStuck; E [{ Φ }]) -∗
    WP (.running
      ⟨{ callerLocals with values := [.i32 align, .i32 size] ++ stack },
        [.call 15] ++ code, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ Stuckness.MaybeStuck; E [{ Φ }] := by
  dsimp only
  iintro ⟨Hruntime, Henv, Hhost, Hbump⟩ Hcont
  let Finish : IProp (WasmHeapGF Universal.State) := iprop(
    runtimeModuleOwn ⟨0⟩ «module» ∗
      hostEnvOwn 0 (Universal.envFor «module») ∗
      hostStateOwn host ∗
      pointsTo_u32 0 1053960
        (size + (((if oldBump = 0 then 1054000 else oldBump) +
          (0xffffffff + align)) &&& (-align))) -∗
      WP (.running
        ⟨{ callerLocals with values :=
            (Value.i32 (((if oldBump = 0 then 1054000 else oldBump) +
              (0xffffffff + align)) &&& (-align))) :: stack },
          code, arity, remainder, controls, calls⟩ : Expr Universal.State) @
        Stuckness.MaybeStuck; E [{ Φ }])
  simp only [List.singleton_append]
  iapply twp_call «module» 15 func12Def (by decide) rfl ⟨0⟩ $$ Hruntime
  iintro Hruntime
  simp [func12Def, Function.toLocals, Function.numParams,
    ValueType.zero, func12]
  iapply twp_block
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
      (by decide) (by decide) (by decide) (by decide)
      $$ Hbump0
  iintro Hbump
  ihave HbumpNorm : pointsTo_u32 0 1053960 oldBump $$ [Hbump]
  · isimp only [UInt32.zero_add] at Hbump
    iexact Hbump
  iapply twp_localTee rfl
  iapply twp_const
  iapply twp_localGet rfl
  iapply hdtwp_select rfl
  simp [Locals.set?, Locals.set]
  rw [show (if oldBump = 0 then Value.i32 1054000 else Value.i32 oldBump) =
      Value.i32 (if oldBump = 0 then 1054000 else oldBump) by
    by_cases h : oldBump = 0 <;> simp [h]]
  iapply twp_add
  iapply twp_localTee rfl
  iapply twp_localGet rfl
  iapply twp_ltU rfl
  ihave Hoverflow₁ :
      (runtimeModuleOwn ⟨0⟩ «module» ∗
          hostEnvOwn 0 (Universal.envFor «module») ∗
          hostStateOwn host ∗ pointsTo_u32 0 1053960 oldBump ∗ Finish) ∧
        (runtimeModuleOwn ⟨0⟩ «module» ∗
          hostEnvOwn 0 (Universal.envFor «module») ∗
          hostStateOwn host ∗ pointsTo_u32 0 1053960 oldBump ∗ Finish) $$
      [Hruntime Henv Hhost HbumpNorm Hcont]
  · isplit <;> iframe
  by_cases hoverflow₁ :
      ((if oldBump = 0 then 1054000 else oldBump) +
          (0xffffffff + align : UInt32)) <
        (0xffffffff + align : UInt32)
  · rw [if_pos hoverflow₁]
    ihave ⟨Hruntime₁, Henv₁, Hhost₁, Hbump₁, Hcont₁⟩ :=
      BI.and_elim_l $$ Hoverflow₁
    iapply twp_brIf (by decide) rfl
    simp
    iapply twp_oom_wrapper_locals host (stack := []) (code := [.unreachable])
    iframe
  · rw [if_neg hoverflow₁]
    ihave ⟨Hruntime₁, Henv₁, Hhost₁, Hbump₁, Hcont₁⟩ :=
      BI.and_elim_r $$ Hoverflow₁
    iapply twp_brIfZero
    iapply twp_localGet rfl
    iapply twp_const
    iapply twp_localGet rfl
    iapply twp_sub
    iapply twp_and
    iapply twp_localTee rfl
    iapply twp_localGet rfl
    iapply twp_add
    iapply twp_localTee rfl
    iapply twp_localGet rfl
    iapply twp_ltU rfl
    ihave Hoverflow₂ :
        (runtimeModuleOwn ⟨0⟩ «module» ∗
            hostEnvOwn 0 (Universal.envFor «module») ∗
            hostStateOwn host ∗ pointsTo_u32 0 1053960 oldBump ∗ Finish) ∧
          (runtimeModuleOwn ⟨0⟩ «module» ∗
            hostEnvOwn 0 (Universal.envFor «module») ∗
            hostStateOwn host ∗ pointsTo_u32 0 1053960 oldBump ∗ Finish) $$
        [Hruntime₁ Henv₁ Hhost₁ Hbump₁ Hcont₁]
    · isplit <;> iframe
    by_cases hoverflow₂ :
        (size + (((if oldBump = 0 then 1054000 else oldBump) +
            (0xffffffff + align : UInt32)) &&& (0 - align))) <
          (((if oldBump = 0 then 1054000 else oldBump) +
            (0xffffffff + align : UInt32)) &&& (0 - align))
    · rw [if_pos hoverflow₂]
      ihave ⟨Hruntime₂, Henv₂, Hhost₂, Hbump₂, Hcont₂⟩ :=
        BI.and_elim_l $$ Hoverflow₂
      iapply twp_brIf (by decide) rfl
      simp
      iapply twp_oom_wrapper_locals host (stack := []) (code := [.unreachable])
      iframe
    · rw [if_neg hoverflow₂]
      ihave ⟨Hruntime₂, Henv₂, Hhost₂, Hbump₂, Hcont₂⟩ :=
        BI.and_elim_r $$ Hoverflow₂
      iapply twp_brIfZero
      iapply twp_localGet rfl
      iapply twp_const
      iapply twp_ltS rfl
      ihave Hsigned :
          (runtimeModuleOwn ⟨0⟩ «module» ∗
              hostEnvOwn 0 (Universal.envFor «module») ∗
              hostStateOwn host ∗ pointsTo_u32 0 1053960 oldBump ∗ Finish) ∧
            (runtimeModuleOwn ⟨0⟩ «module» ∗
              hostEnvOwn 0 (Universal.envFor «module») ∗
              hostStateOwn host ∗ pointsTo_u32 0 1053960 oldBump ∗ Finish) $$
          [Hruntime₂ Henv₂ Hhost₂ Hbump₂ Hcont₂]
      · isplit <;> iframe
      by_cases hnegative :
          (size + (((if oldBump = 0 then 1054000 else oldBump) +
            (0xffffffff + align : UInt32)) &&& (0 - align))).toInt32 <
            UInt32.toInt32 0
      · rw [if_pos hnegative]
        ihave ⟨Hruntime₃, Henv₃, Hhost₃, Hbump₃, Hcont₃⟩ :=
          BI.and_elim_l $$ Hsigned
        iapply twp_brIf (by decide) rfl
        simp
        iapply twp_oom_wrapper_locals host (stack := []) (code := [.unreachable])
        iframe
      · rw [if_neg hnegative]
        ihave ⟨Hruntime₃, Henv₃, Hhost₃, Hbump₃, Hcont₃⟩ :=
          BI.and_elim_r $$ Hsigned
        iapply twp_brIfZero
        iapply twp_localGet rfl
        iapply twp_const
        iapply twp_add
        iapply twp_const
        iapply hdtwp_shrU
        iapply twp_localTee rfl
        ihave HmemorySize : runtimeModuleOwn ⟨0⟩ «module» ∗
            (hostEnvOwn 0 (Universal.envFor «module») ∗
              hostStateOwn host ∗ pointsTo_u32 0 1053960 oldBump ∗ Finish) $$
            [Hruntime₃ Henv₃ Hhost₃ Hbump₃ Hcont₃]
        · iframe
        iapply hdtwp_memorySize «module» ⟨0⟩
            (iprop(hostEnvOwn 0 (Universal.envFor «module») ∗
              hostStateOwn host ∗ pointsTo_u32 0 1053960 oldBump ∗ Finish)) $$
          HmemorySize
        iintro %pages ⟨Hruntime₄, Henv₃, Hhost₃, Hbump₃, Hcont₃⟩
        rw [module_memIs64]
        simp only [sizeValue, Bool.false_eq_true, if_false]
        iapply twp_localTee rfl
        iapply hdtwp_leU rfl
        ihave Henough :
            (runtimeModuleOwn ⟨0⟩ «module» ∗
                hostEnvOwn 0 (Universal.envFor «module») ∗
                hostStateOwn host ∗ pointsTo_u32 0 1053960 oldBump ∗ Finish) ∧
              (runtimeModuleOwn ⟨0⟩ «module» ∗
                hostEnvOwn 0 (Universal.envFor «module») ∗
                hostStateOwn host ∗ pointsTo_u32 0 1053960 oldBump ∗ Finish) $$
            [Hruntime₄ Henv₃ Hhost₃ Hbump₃ Hcont₃]
        · isplit <;> iframe
        by_cases henough :
            ((65535 + (size +
              (((if oldBump = 0 then 1054000 else oldBump) +
                (0xffffffff + align : UInt32)) &&& (0 - align)))) >>>
              (16 % 32)) ≤ UInt32.ofNat pages
        · rw [if_pos henough]
          ihave ⟨Hruntime₅, Henv₅, Hhost₅, Hbump₅, Hcont₅⟩ :=
            BI.and_elim_l $$ Henough
          iapply twp_brIf (by decide) rfl
          iapply twp_const
          iapply twp_localGet rfl
          iapply twp_store_bump oldBump $$ Hbump₅
          iintro Hbump
          iapply twp_localGet rfl
          simp
          iapply hdtwp_returnFromCallFallthrough $$ Hruntime₅
          iintro Hruntime₆
          simp
          isimp only [Finish, zero_sub] at Hcont₅
          iapply Hcont₅
          iframe
        · rw [if_neg henough]
          ihave ⟨Hruntime₅, Henv₅, Hhost₅, Hbump₅, Hcont₅⟩ :=
            BI.and_elim_r $$ Henough
          iapply twp_brIfZero
          iapply twp_localGet rfl
          iapply twp_localGet rfl
          iapply twp_sub
          ihave HmemoryGrow : runtimeModuleOwn ⟨0⟩ «module» ∗
              (hostEnvOwn 0 (Universal.envFor «module») ∗
                hostStateOwn host ∗ pointsTo_u32 0 1053960 oldBump ∗ Finish) $$
              [Hruntime₅ Henv₅ Hhost₅ Hbump₅ Hcont₅]
          · iframe
          iapply hdtwp_memoryGrow «module» ⟨0⟩
              (iprop(hostEnvOwn 0 (Universal.envFor «module») ∗
                hostStateOwn host ∗ pointsTo_u32 0 1053960 oldBump ∗ Finish)) $$
            HmemoryGrow
          iintro %growResult ⟨Hruntime₆, Henv₅, Hhost₅, Hbump₅, Hcont₅⟩
          iapply twp_const
          iapply twp_ne rfl
          ihave Hgrow :
              (runtimeModuleOwn ⟨0⟩ «module» ∗
                  hostEnvOwn 0 (Universal.envFor «module») ∗
                  hostStateOwn host ∗ pointsTo_u32 0 1053960 oldBump ∗ Finish) ∧
                (runtimeModuleOwn ⟨0⟩ «module» ∗
                  hostEnvOwn 0 (Universal.envFor «module») ∗
                  hostStateOwn host ∗ pointsTo_u32 0 1053960 oldBump ∗ Finish) $$
              [Hruntime₆ Henv₅ Hhost₅ Hbump₅ Hcont₅]
          · isplit <;> iframe
          by_cases hgrow : growResult ≠ (0xffffffff : UInt32)
          · rw [if_pos hgrow]
            ihave ⟨Hruntime₇, Henv₇, Hhost₇, Hbump₇, Hcont₇⟩ :=
              BI.and_elim_l $$ Hgrow
            iapply twp_brIf (by decide) rfl
            iapply twp_const
            iapply twp_localGet rfl
            iapply twp_store_bump oldBump $$ Hbump₇
            iintro Hbump
            iapply twp_localGet rfl
            simp
            iapply hdtwp_returnFromCallFallthrough $$ Hruntime₇
            iintro Hruntime₈
            simp
            isimp only [Finish, zero_sub] at Hcont₇
            iapply Hcont₇
            iframe
          · rw [if_neg hgrow]
            ihave ⟨Hruntime₇, Henv₇, Hhost₇, Hbump₇, Hcont₇⟩ :=
              BI.and_elim_r $$ Hgrow
            iapply twp_brIfZero
            iapply twp_exitControl rfl
            simp
            iapply twp_oom_wrapper_locals host (stack := [])
              (code := [.unreachable])
            iframe

end Project.HexEncodeStdio
