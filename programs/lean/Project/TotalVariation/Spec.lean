import Project.TotalVariation.Program

/-!
# `total_variation a b c = |a-b| + |b-c|`

The proof uses iris-lean's WP over the small-step machine. Both generated
calls reuse the contextual `absDiff_smallStep_wp_to_return` body rule.
-/

namespace Project.TotalVariation.Spec

open Wasm Wasm.RustStd.U64
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep

def totalVariationConfig (a b c : UInt64) : Config Unit :=
  let initial := «module».initialStore
  { expr := .running
      ⟨⟨[.i64 a, .i64 b, .i64 c], [], []⟩,
        func1, 1, [], [], []⟩
    store :=
      { runtime := { module := «module», host := {} }
        wasm := { initial with mem := initial.mem.write64 1048568 0 } } }

@[spec_of "rust-exported" "total_variation::total_variation"]
def TotalVariationSpec : Prop :=
  ∀ (a b c : UInt64),
    PartiallyMeets (totalVariationConfig a b c)
      (fun rs _ => rs =
        [.i64 ((if a < b then b - a else a - b)
             + (if b < c then c - b else b - c))])

set_option maxHeartbeats 8000000 in
@[proves Project.TotalVariation.Spec.TotalVariationSpec]
theorem total_variation_correct : TotalVariationSpec := by
  intro a b c
  apply wasm_smallStep_heap_globals_runtime_partiallyMeets
      (α := Unit)
      (σ := absDiffHeap 0)
      (globalσ := absDiffGlobals)
      (φ := fun rs => rs =
        [.i64 ((if a < b then b - a else a - b)
             + (if b < c then c - b else b - c))])
  · simpa [totalVariationConfig, absDiffBodyConfig] using
      absDiffBodyHeap_agrees «module» «module».initialStore a b 0
  · apply absDiffBodyHeap_inBounds «module» «module».initialStore a b 0
    decide
  · simpa [totalVariationConfig, absDiffBodyConfig] using
      absDiffBodyGlobals_agree «module» «module».initialStore a b 0 rfl
  · intro gs
    iintro ⟨Hbytes, Hglobals, Hruntime⟩
    ihave Hscratch := absDiffHeap_pointsTo 0 $$ Hbytes
    ihave Hglobal := absDiffGlobals_pointsTo $$ Hglobals
    simp only [totalVariationConfig, func1]
    iapply wp_localGet rfl
    inext
    iapply wp_localGet rfl
    inext
    iapply wp_call «module» 0 func0Def (by simp [«module»]) (by simp [«module»]) $$
      Hruntime
    inext
    iintro Hruntime
    simp [func0Def, Function.toLocals, Function.numParams, ValueType.zero]
    rw [show func0 = absDiffBody by rfl]
    iapply absDiff_smallStep_wp_to_return
      (runtimeModuleOwn «module») _ 1048576 a b 0 (by decide) (by decide)
    · iintro ⟨Hruntime, Hglobal, Hscratch⟩
      iapply wp_returnFromCallExplicit
      inext
      iapply wp_localGet rfl
      inext
      iapply wp_localGet rfl
      inext
      simp only [List.take, UInt32.reduceSub, UInt32.reduceAdd]
      iapply wp_call «module» 0 func0Def (by simp [«module»]) (by simp [«module»]) $$
        Hruntime
      inext
      iintro Hruntime
      simp [func0Def, Function.toLocals, Function.numParams, ValueType.zero]
      rw [show func0 = absDiffBody by rfl]
      iapply absDiff_smallStep_wp_to_return
        (runtimeModuleOwn «module») _ 1048576 b c
        (if a < b then b - a else a - b) (by decide) (by decide)
      · iintro ⟨Hruntime, Hglobal, Hscratch⟩
        iapply wp_returnFromCallExplicit
        inext
        simp only [List.take, List.singleton_append]
        iapply wp_addI64
        inext
        iapply wp_returnFromFunction
        inext
        iapply wp_value'
        ipureintro
        rfl
      · simp only [UInt32.reduceSub, UInt32.reduceAdd]
        iframe
    · simp only [UInt32.reduceSub, UInt32.reduceAdd]
      iframe

end Project.TotalVariation.Spec
