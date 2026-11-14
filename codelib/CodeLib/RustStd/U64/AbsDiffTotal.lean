import CodeLib.RustStd.U64.AbsDiff

/-! Total contextual reasoning for the compiled `u64::abs_diff` body. -/

namespace Wasm.RustStd.U64

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic

set_option maxHeartbeats 4000000 in
/-- Total contextual rule for the compiled body. Both comparison branches
terminate at the return continuation, preserving caller-frame and stack-pointer
resources and returning ownership of the updated scratch word. -/
theorem absDiff_smallStep_twp_to_return
    [Wasm.SmallStep.WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit))
    (calls : List Wasm.SmallStep.CallFrame)
    (sp : UInt32) (a b oldScratch : UInt64)
    (hlo : 16 ≤ sp.toNat)
    (hroom : (sp - 16).toNat + 16 ≤ 4294967296)
    (hreturn :
      R ∗ globalPointsToAt 0 0 (.i32 sp) ∗
        pointsTo_u64 0 ((sp - 16) + 8)
          (if a < b then b - a else a - b) ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i64 a, .i64 b], [.i32 (sp - 16)],
            [.i64 (if a < b then b - a else a - b)]⟩,
          [.ret], 1, [], [], calls⟩ :
          Wasm.SmallStep.Expr Unit) @ s; E [{ Φ }]) :
    R ∗ globalPointsToAt 0 0 (.i32 sp) ∗
      pointsTo_u64 0 ((sp - 16) + 8) oldScratch ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i64 a, .i64 b], [.i32 0], []⟩,
        absDiffBody, 1, [], [], calls⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E
      [{ Φ }] := by
  have hle : (16 : UInt32) ≤ sp :=
    UInt32.le_iff_toNat_le.mpr (by simpa using hlo)
  have hsub : (sp - 16).toNat = sp.toNat - 16 :=
    UInt32.toNat_sub_of_le sp 16 hle
  have h8 : ((sp - 16) + 8).toNat = (sp - 16).toNat + 8 := by
    simpa using UInt32.add_ofNat_toNat_noWrap (sp - 16) 8
      (by omega) (by omega)
  obtain ⟨h9, h10, h11, h12, h13, h14, h15⟩ :=
    UInt32.addSteps8 ((sp - 16) + 8) (by omega)
  iintro ⟨HR, Hglobal, Hscratch⟩
  simp only [absDiffBody]
  wasm_twp_rebind Wasm.SmallStep.twp_globalGet with Hglobal
  wasm_twp_pures [twp_const twp_sub twp_localSet]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
    List.set]
  wasm_twp_pures [twp_block twp_block twp_localGet twp_localGet]
  by_cases hab : a < b
  · iapply Wasm.SmallStep.twp_ltUI64 (result := 1) (by simp [hab])
    wasm_twp_pures [twp_const twp_and] rewriting [show (1 &&& 1 : UInt32) = 1 by decide]
    iapply Wasm.SmallStep.twp_brIf (by decide) rfl
    simp only [List.take_nil, List.drop_nil, List.nil_append]
    wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_subI64]
    iapply Wasm.SmallStep.twp_store64 oldScratch h8 h9 h10 h11 h12 h13 h14 h15 $$
      Hscratch
    iintro Hscratch
    wasm_twp_pures [twp_exitControl twp_localGet]
    iapply Wasm.SmallStep.twp_load64 (b - a) h8 h9 h10 h11 h12 h13 h14 h15 $$
      Hscratch
    iintro Hscratch
    simp only [List.take_nil, List.nil_append]
    simp only [hab, ite_true] at hreturn
    iapply_frame hreturn
  · iapply Wasm.SmallStep.twp_ltUI64 (result := 0) (by simp [hab])
    wasm_twp_pures [twp_const twp_and] rewriting [show (0 &&& 1 : UInt32) = 0 by decide]
    wasm_twp_pures [twp_brIfZero twp_localGet twp_localGet twp_localGet twp_subI64]
    iapply Wasm.SmallStep.twp_store64 oldScratch h8 h9 h10 h11 h12 h13 h14 h15 $$
      Hscratch
    iintro Hscratch
    wasm_twp_pures [twp_br] using [List.take_nil, List.drop_nil, List.nil_append]
    wasm_twp_pures [twp_localGet]
    iapply Wasm.SmallStep.twp_load64 (a - b) h8 h9 h10 h11 h12 h13 h14 h15 $$
      Hscratch
    iintro Hscratch
    simp only [hab, ite_false] at hreturn
    iapply_frame hreturn

end Wasm.RustStd.U64
