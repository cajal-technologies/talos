import Project.RustHashMap.ErrorNewContracts
import Project.RustHashMap.Func40Proof

/-!
# Proof of the four-argument forwarder of the `io::Error::new` chain

Local `func39` (absolute index 42) keeps no frame.  It pushes its first
three arguments, calls absolute `func 43`, and returns.  The fourth
argument is the static pointer 1049164, and the body drops it.

`func39Depth = func40Depth`, so the stack region below the pointer
passes straight through to the callee and comes straight back.

The theorem is unconditional, because
`Project.RustHashMap.Func40Proof.func40_correct` is.
-/

namespace Project.RustHashMap.Func39Proof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open Project.RustHashMap.Allocator
open Project.RustHashMap.AllocatorContracts
open Project.RustHashMap.EntryContracts
open Project.RustHashMap.BodyContracts
open Project.RustHashMap.ErrorNewContracts
open scoped Wasm.SmallStep.Outcome

private theorem func39_index :
    Project.RustHashMap.«module».funcs[39]? =
      some Project.RustHashMap.func39Def := by rfl

set_option maxHeartbeats 2000000 in
theorem func39_correct [WasmSmallStepGS hlc Universal.State] :
    Func39Spec (hlc := hlc) := by
  unfold Func39Spec CallContract callExpr
  intro sp out msgPtr msgLen unused heapId outBefore below msgBytes
    storedCursor frontier history input output raised callerLocals stack code
    arity remainder controls calls s E Φ
  iintro ⟨Hruntime, Hsp, Hbelow, Hout, Hmsg, Hbump, Hstreams, %hfacts, Hcont⟩
  obtain ⟨houtLength, hspLow, houtNowrap, hmsgPos, hmsgLe, hmsgLength⟩ := hfacts
  have hdepth : func39Depth = func40Depth := rfl
  rw [hdepth] at hspLow
  isimp only [hdepth] at Hbelow
  iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
  simp only [List.cons_append, List.nil_append]
  wasm_twp_rebind Wasm.SmallStep.twp_call Project.RustHashMap.«module» 42
      Project.RustHashMap.func39Def (by decide) func39_index with Hmodule
  simp [Project.RustHashMap.func39Def, Project.RustHashMap.func39,
    Function.toLocals, Function.numParams]
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet]
  have Hleaf : Func40Spec (hlc := hlc) :=
    Project.RustHashMap.Func40Proof.func40_correct
  unfold Func40Spec CallContract callExpr at Hleaf
  simp only [List.cons_append, List.nil_append] at Hleaf
  iapply Hleaf (sp := sp) (out := out) (msgPtr := msgPtr) (msgLen := msgLen)
    (heapId := heapId) (outBefore := outBefore) (below := below)
    (msgBytes := msgBytes) (storedCursor := storedCursor)
    (frontier := frontier) (history := history) (input := input)
    (output := output) (raised := raised)
    (callerLocals :=
      { params := [.i32 out, .i32 msgPtr, .i32 msgLen, .i32 unused]
        locals := []
        values := [] })
    (stack := [])
  isplitl [Hmodule Henv]
  · unfold RuntimeContext
    iframe Hmodule Henv
  isplitl_exacts [Hsp Hbelow Hout Hmsg Hbump Hstreams]
  isplitl_pureexact
    ⟨houtLength, hspLow, houtNowrap, hmsgPos, hmsgLe, hmsgLength⟩
  isplit
  · iintro %ptr %blockId %below' %storedCursor' %frontier' %history'
    iintro Hruntime Hsp Hbelow Hout Hmsg Hbump Hblock Hstreams
    unfold ResumeWP resumeExpr
    simp only [List.nil_append]
    iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
    wasm_twp_return_from_call Hmodule [List.take_zero, List.nil_append]
    iclose_map_runtime Hruntime with Hmodule Henv
    isimp only [← hdepth] at Hbelow
    isimp only [WordCodec.serialize_cons, WordCodec.serialize_nil,
      List.append_nil] at Hout
    ihave Hnormal := BI.and_elim_l $$ Hcont
    ihave Hnormal := Hnormal $$ %ptr %blockId %below' %storedCursor'
      %frontier' %history'
    iapply Hnormal $$ Hruntime Hsp Hbelow Hout Hmsg Hbump Hblock Hstreams
  · iintro %remaining' Hstreams
    ihave Hoom := BI.and_elim_r $$ Hcont
    ihave Hoom := Hoom $$ %remaining'
    iapply Hoom $$ Hstreams

end Project.RustHashMap.Func39Proof
