import HexEncodeStdio.HDAllocator

namespace Submission.HexDecodeStdio

open Wasm Project.HexStdio Project.HexStdio.Spec
open Wasm.SmallStep

/-- The store produced by the universal host's distinguished OOM call. -/
def oomFinalStore (store : MachineStore Universal.State) :
    MachineStore Universal.State :=
  { store with wasm := { store.wasm with host :=
      { store.wasm.host with oom := { raised := true } } } }

/-- The private OOM wrapper has an exact two-step operational trace: enter
function 16, then invoke import 2.  Keeping this fact operational (rather than
closing a `MaybeStuck` total WP) preserves both the trap reason and final host
marker required by `RunsOutOfMemory`. -/
theorem oom_wrapper_steps
    (store : MachineStore Universal.State)
    (params locals stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (hmod : store.runtime.currentModule = «module»)
    (henv : store.runtime.currentHost = Universal.envFor «module») :
    Steps
      ⟨.running ⟨⟨params, locals, stack⟩, .call 16 :: code,
        arity, remainder, controls, calls⟩, store⟩
      [.instruction (.call 16), .host 2]
      ⟨.trapped (.host OOM.trapMessage), oomFinalStore store⟩ := by
  let caller : CallFrame :=
    { locals := ⟨params, locals, stack.drop func13Def.numParams⟩
      continuation := code
      resultArity := arity
      callerRemainder := remainder
      control := controls
      returningInstance := store.runtime.entry }
  let middle : Config Universal.State :=
    ⟨.running ⟨func13Def.toLocals (stack.take func13Def.numParams).reverse,
      func13Def.body, func13Def.results.length, [], [], caller :: calls⟩, store⟩
  have hnot : ¬16 < store.runtime.currentModule.imports.length := by
    rw [hmod]
    decide
  have hfn : store.runtime.currentModule.funcs[
      16 - store.runtime.currentModule.imports.length]? = some func13Def := by
    rw [hmod]
    rfl
  apply Steps.cons (next := middle)
  · exact Step.call (functionIndex := 16) (fn := func13Def) hnot hfn
  · have himplen : 2 < store.runtime.currentModule.imports.length := by
      rw [hmod]
      decide
    have himpModule : «module».imports[2] =
        ({ module := "talos", name := "oom", params := [], results := [] } :
          ImportDecl) := by
      decide
    have himp : store.runtime.currentModule.imports[2] =
        ({ module := "talos", name := "oom", params := [], results := [] } :
          ImportDecl) := by
      simpa only [hmod] using himpModule
    have hhost : store.runtime.currentHost.funcs[2]? =
        some (OOM.oomHost.lift universalOOMLens) := by
      rw [henv]
      exact universal_oom_function
    let postWasm : Store Universal.State :=
      { store.wasm with host :=
          { store.wasm.host with oom := { raised := true } } }
    have hinvoke :
        (OOM.oomHost.lift universalOOMLens).invoke store.wasm [] =
          .Trap postWasm OOM.trapMessage := by
      simp [OOM.oomHost, OOM.oomResult, HostFn.lift, universalOOMLens,
        Store.focus, Store.mapHost, Store.unfocus, postWasm]
    have hnum : func13Def.numParams = 0 := rfl
    simp only [middle, hnum, func13Def, Function.toLocals, List.take_zero,
      List.reverse_nil, List.drop_zero] at *
    apply Steps.cons
    · simpa [func13, caller, postWasm, oomFinalStore] using
        (Step.callHostTrap (functionIndex := 2)
          (imp := { module := "talos", name := "oom", params := [], results := [] })
          (hostFunction := OOM.oomHost.lift universalOOMLens)
          (params := []) (localValues := []) (values := [])
          (code := [.unreachable]) (arity := 0) (remainder := [])
          (controls := []) (calls := caller :: calls)
          (store := store) (message := OOM.trapMessage) (wasm := postWasm)
          himplen himp hhost hinvoke)
    · exact .refl _

/-- Relational form of `oom_wrapper_steps`, ready to prepend to any finite
prefix ending immediately before the private wrapper call. -/
theorem oom_wrapper_traps
    (store : MachineStore Universal.State)
    (params locals stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (hmod : store.runtime.currentModule = «module»)
    (henv : store.runtime.currentHost = Universal.envFor «module») :
    TrapsWith
      ⟨.running ⟨⟨params, locals, stack⟩, .call 16 :: code,
        arity, remainder, controls, calls⟩, store⟩
      (.host OOM.trapMessage)
      (fun final => final.wasm.host.oom.raised = true) := by
  apply TrapsWith.of_steps
    (oom_wrapper_steps store params locals stack code arity remainder controls
      calls hmod henv)
  simp [oomFinalStore]

end Submission.HexDecodeStdio
