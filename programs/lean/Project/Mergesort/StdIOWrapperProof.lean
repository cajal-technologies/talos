import Project.Mergesort.DriverProof

/-!
# Generated StdIO import wrappers

The unchanged module reaches its two imports through tiny generated wrappers:
local `func133` forwards to `stdio.read` (absolute call 0), and local `func138`
forwards to `stdio.write` (absolute call 1).  These rules stop exactly at the
host calls so later proofs cannot accidentally hide or assume their effects.
-/

namespace Project.Mergesort.StdIOWrapperProof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep

theorem stdioReadWrapper_index :
    «module».funcs[133]? = some func133Def := by
  rfl

theorem stdioWriteWrapper_index :
    «module».funcs[138]? = some func138Def := by
  rfl

theorem stdioNoopWrapper_index :
    «module».funcs[134]? = some func134Def := by
  rfl

/-- Exact body prefix of local `func133`, ending at imported `stdio.read`. -/
theorem stdioReadWrapper_to_import_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (pointer length : UInt32)
    {calls : List CallFrame} :
    WP (.running
      ⟨⟨[.i32 pointer, .i32 length], [], [.i32 length, .i32 pointer]⟩,
        func133.drop 2, 1, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨[.i32 pointer, .i32 length], [], []⟩,
        func133, 1, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro Hcont
  simp only [func133]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  isimp at Hcont
  iexact Hcont

/-- Exact body prefix of local `func138`, ending at imported `stdio.write`. -/
theorem stdioWriteWrapper_to_import_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (pointer length : UInt32)
    {calls : List CallFrame} :
    WP (.running
      ⟨⟨[.i32 pointer, .i32 length], [], [.i32 length, .i32 pointer]⟩,
        func138.drop 2, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨[.i32 pointer, .i32 length], [], []⟩,
        func138, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro Hcont
  simp only [func138]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  isimp at Hcont
  iexact Hcont

/-- The generated local `func134` has no effects before returning. -/
theorem stdioNoopWrapper_body_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {calls : List CallFrame} :
    WP (.running
      ⟨⟨[], [], []⟩, [.ret], 0, [], [], calls⟩ : Expr α)
        @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨[], [], []⟩, func134, 0, [], [], calls⟩ : Expr α)
        @ s; E [{ Φ }] := by
  rfl

/-- Composable total call rule for the generated no-op wrapper at absolute
index 136. -/
theorem stdioNoopWrapper_call_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      (runtimeModuleOwn «module» -∗
        WP (.running
          ⟨{ callerLocals with values := stack },
            code, arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨{ callerLocals with values := stack },
        .call 136 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hcont⟩
  iapply Wasm.SmallStep.twp_call (α := α) «module» 136 func134Def
      (by decide) stdioNoopWrapper_index $$ Hruntime
  iintro Hruntime
  simp [func134Def, Function.toLocals, Function.numParams, func134]
  iapply Wasm.SmallStep.twp_returnFromCallExplicit (α := α)
  simp only [List.take, List.nil_append]
  iapply Hcont $$ Hruntime

end Project.Mergesort.StdIOWrapperProof
