import HexDecodeStdio.HostIO

namespace Project.HexDecodeStdio

open Wasm Project.HexStdio Project.HexStdio.Spec
open Iris Iris.ProgramLogic Language.Notation
open Wasm.SepLogic Wasm.SmallStep

variable {hlc : outParam HasLC}

/-- Normal, nonempty leg of Rust's generated `write_all` (module function 11).
The universal write host always reports the full requested length, so the
syntactic retry loop has one normal iteration. -/
theorem twp_write_all_nonempty
    [WasmSmallStepGS hlc Universal.State]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Universal.State)}
    (host : Universal.State) (pointer length sp : UInt32)
    (bytes : List UInt8) (oldTag : UInt8) (oldCount : UInt32)
    (hlen : bytes.length = length.toNat) (hne : bytes ≠ [])
    (hnowrap : pointer.toNat + bytes.length < UInt32.size)
    (hframe : Offset32Facts (sp - 16) 4)
    (callerLocals : Locals) (stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame) :
    runtimeModuleOwn ⟨0⟩ «module» ∗
      hostEnvOwn 0 (Universal.envFor «module») ∗
      hostStateOwn host ∗
      globalPointsToAt 0 0 (.i32 sp) ∗
      pointsToBytes 0 pointer bytes ∗
      pointsTo (GF := WasmHeapGF Universal.State) (H := WasmHeapMap)
        ⟨0, sp - 16⟩ (DFrac.own 1) (some oldTag) ∗
      pointsTo_u32 0 ((sp - 16) + 4) oldCount -∗
    (runtimeModuleOwn ⟨0⟩ «module» ∗
      hostStateOwn (afterUniversalWrite host bytes) ∗
      globalPointsToAt 0 0 (.i32 sp) ∗
      pointsToBytes 0 pointer bytes ∗
      pointsTo (GF := WasmHeapGF Universal.State) (H := WasmHeapMap)
        ⟨0, sp - 16⟩ (DFrac.own 1) (some (4 : UInt8)) ∗
      pointsTo_u32 0 ((sp - 16) + 4) length -∗
      WP (.running
        ⟨{ callerLocals with values := stack }, code, arity, remainder,
          controls, calls⟩ : Expr Universal.State) @ s; E [{ Φ }]) -∗
    WP (.running
      ⟨{ callerLocals with values := [.i32 length, .i32 pointer] ++ stack },
        [.call 11] ++ code, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Henv, Hhost, Hsp, Hbytes, Htag, Hcount⟩ Hcont
  simp only [List.singleton_append]
  iapply twp_call «module» 11 func8Def (by decide) rfl ⟨0⟩ $$ Hruntime
  iintro Hruntime
  simp [func8Def, Function.toLocals, Function.numParams,
    ValueType.zero, func8]
  iapply twp_globalGet $$ Hsp
  iintro Hsp
  iapply twp_const
  iapply twp_sub
  iapply twp_localTee rfl
  iapply twp_globalSet $$ Hsp
  iintro HframeSp
  iapply twp_block
  iapply twp_localGet rfl
  iapply twp_eqz rfl
  have hlength : length ≠ 0 := by
    intro hz
    subst length
    simp at hlen
    exact hne hlen
  simp [hlength]
  iapply twp_brIfZero
  iapply twp_loop
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_write_adapter_no_stack host (sp - 16) (15 + (sp - 16))
      pointer length bytes oldTag oldCount hlen hne hnowrap hframe
      $$ [$Hruntime $Henv $Hhost $Hbytes $Htag $Hcount]
  iintro ⟨Hruntime, Hhost, Hbytes, Htag, Hcount⟩
  iapply twp_block
  iapply twp_block
  iapply twp_block
  iapply twp_block
  iapply twp_block
  iapply twp_block
  iapply twp_block
  iapply twp_localGet rfl
  iapply twp_load8U_addr (4 : UInt8) $$ Htag
  iintro Htag
  iapply twp_localTee rfl
  iapply twp_const
  iapply hdtwp_eq rfl
  iapply twp_brIf (by decide) rfl
  simp
  iapply twp_block
  iapply twp_localGet rfl
  iapply twp_load32 length hframe.noWrap hframe.one hframe.two
      hframe.three $$ Hcount
  iintro Hcount
  iapply twp_localTee rfl
  iapply twp_brIf hlength rfl
  simp
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_ltU rfl
  simp
  iapply twp_brIfZero
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_add
  iapply twp_localSet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_sub
  iapply twp_localTee rfl
  simp
  iapply twp_brIfZero
  iapply twp_br rfl
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  have hrestore : 16 + (sp - 16) = sp := by bv_decide
  rw [hrestore]
  iapply twp_globalSet $$ HframeSp
  iintro Hsp
  iapply hdtwp_returnFromCallFallthrough $$ Hruntime
  iintro Hruntime
  simp
  iapply Hcont
  iframe

end Project.HexDecodeStdio
