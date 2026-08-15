import Project.Mergesort.ArgumentsProof
import Project.Mergesort.RangeProof

/-!
# Exported driver proof

The unchanged exported `func127` begins by installing its 384-byte frame and
then calls the generated buffered-I/O constructor at absolute index 137.  This
file isolates that exact entry segment before the larger input/parse/sort/output
pipeline is assembled.
-/

namespace Project.Mergesort.DriverProof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.Mergesort.FunctionSpecs
open Project.Mergesort.Machine
open Project.Mergesort.RangeProof

def exportZeroLocals : List Value :=
  List.replicate 24 (.i32 0)

def exportFramedLocals (frame : UInt32) : List Value :=
  exportZeroLocals.set 0 (.i32 frame)

def exportFrameSegment : Program :=
  [ .globalGet 0,
    .const 384,
    .sub,
    .localSet 0,
    .localGet 0,
    .globalSet 0,
    .localGet 0,
    .const 92,
    .add ]

theorem func127_eq_frameSegment :
    func127 = exportFrameSegment ++ func127.drop 9 := by
  rfl

/-- The next instruction after the frame prologue is the exact generated
buffered-I/O call, with `frame + 92` on the operand stack. -/
theorem export_frame_prefix_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (stackTop : UInt32)
    {calls : List CallFrame} :
    globalPointsTo 0 (.i32 stackTop) ∗
      (globalPointsTo 0 (.i32 (stackTop - 384)) -∗
        WP (.running
          ⟨⟨[], exportFramedLocals (stackTop - 384),
              [.i32 (92 + (stackTop - 384))]⟩,
            func127.drop 9, 0, [], [], calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[], exportZeroLocals, []⟩,
        func127, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro ⟨Hglobal, Hcont⟩
  rw [func127_eq_frameSegment]
  simp only [exportFrameSegment, List.cons_append, List.nil_append]
  iapply twp_globalGet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply twp_const
  iapply twp_sub
  iapply twp_localSet rfl
  iapply twp_localGet rfl
  iapply twp_globalSet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  isimp [exportZeroLocals, exportFramedLocals] at Hcont
  isimp [exportZeroLocals, exportFramedLocals]
  iapply Hcont $$ Hglobal

end Project.Mergesort.DriverProof
