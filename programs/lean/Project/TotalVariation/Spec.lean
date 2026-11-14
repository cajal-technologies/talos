import Project.TotalVariation.Program
import Project.TotalVariation.Arithmetic
import CodeLib.RustStd.U64.AbsDiffTotal

/-!
# `total_variation`: normal return and wrapping arithmetic

The original partial proof uses iris-lean's WP over the small-step machine.
The total proof uses the contextual total `abs_diff` rule twice and connects
the body configuration to the named export from the canonical initial store.
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
      { runtime := { instances := #[{ module := «module», host := {} }], entry := ⟨0⟩ }
        wasm := { initial with mem := initial.mem.write64 1048568 0 } } }

@[spec_of "rust-exported-partial" "total_variation::total_variation"]
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
  · simp only [totalVariationConfig]; decide
  · intro gs
    simp only [totalVariationConfig, RuntimeEnv.currentModule_mk1]
    iintro ⟨Hbytes, Hglobals, Hruntime⟩
    ihave Hscratch := absDiffHeap_pointsTo 0 $$ Hbytes
    ihave Hglobal := absDiffGlobals_pointsTo $$ Hglobals
    simp only [func1]
    wasm_wp_pures [wp_localGet wp_localGet]
    wasm_wp_next wp_call «module» 0 func0Def (by simp [«module»]) (by simp [«module»]) $$
      Hruntime
    iintro Hruntime
    simp [func0Def, Function.toLocals, Function.numParams, ValueType.zero]
    rw [show func0 = absDiffBody by rfl]
    iapply absDiff_smallStep_wp_to_return
      (runtimeModuleOwn ⟨0⟩ «module») _ 1048576 a b 0 (by decide) (by decide)
    · iintro ⟨Hruntime, Hglobal, Hscratch⟩
      wasm_wp_return_from_call Hruntime
      wasm_wp_pures [wp_localGet wp_localGet] using [List.take, UInt32.reduceSub, UInt32.reduceAdd]
      wasm_wp_next wp_call «module» 0 func0Def (by simp [«module»]) (by simp [«module»]) $$
        Hruntime
      iintro Hruntime
      simp [func0Def, Function.toLocals, Function.numParams, ValueType.zero]
      rw [show func0 = absDiffBody by rfl]
      iapply absDiff_smallStep_wp_to_return
        (runtimeModuleOwn ⟨0⟩ «module») _ 1048576 b c
        (if a < b then b - a else a - b) (by decide) (by decide)
      · iintro ⟨Hruntime, Hglobal, Hscratch⟩
        wasm_wp_next wp_returnFromCallExplicit $$ Hruntime
        simp only [List.take, List.singleton_append]
        wasm_wp_pures [wp_addI64]
        wasm_wp_return_value_rfl
      · simp only [UInt32.reduceSub, UInt32.reduceAdd]
        iframe
    · simp only [UInt32.reduceSub, UInt32.reduceAdd]
      iframe

/-! ## Natural-number refinement of the existing partial body contract

These are still partial-correctness statements about `totalVariationConfig`.
They neither invoke a named export nor prove that an execution terminates.
The existential is inside the result predicate: a successful raw return must
actually decode to a UInt64 satisfying the mathematical property.
-/

theorem total_variation_partial_mod (a b c : UInt64) :
    PartiallyMeets (totalVariationConfig a b c)
      (fun rs _ => ∃ out : UInt64,
        rs = [.i64 out] ∧
        out.toNat = Arithmetic.mathematicalValue a b c % (2 ^ 64)) := by
  have hpost (rs : List Value) :
      rs = [.i64 (Arithmetic.machineValue a b c)] ↔
        (∃ out : UInt64, rs = [.i64 out] ∧
          out.toNat = Arithmetic.mathematicalValue a b c % (2 ^ 64)) := by
    constructor
    · intro h
      exact ⟨Arithmetic.machineValue a b c, h, Arithmetic.machineValue_toNat a b c⟩
    · rintro ⟨out, hrs, hmath⟩
      have hout : out = Arithmetic.machineValue a b c :=
        UInt64.toNat_inj.mp (hmath.trans (Arithmetic.machineValue_toNat a b c).symm)
      simpa only [hout] using hrs
  have h := total_variation_correct a b c
  change PartiallyMeets (totalVariationConfig a b c)
    (fun rs _ => rs = [.i64 (Arithmetic.machineValue a b c)]) at h
  simpa only [hpost] using h

theorem total_variation_partial_no_overflow (a b c : UInt64)
    (hbound : Arithmetic.mathematicalValue a b c < 2 ^ 64) :
    PartiallyMeets (totalVariationConfig a b c)
      (fun rs _ => ∃ out : UInt64,
        rs = [.i64 out] ∧ out.toNat = Arithmetic.mathematicalValue a b c) := by
  simpa only [Nat.mod_eq_of_lt hbound] using total_variation_partial_mod a b c

set_option maxHeartbeats 8000000 in
/-- Compose both total `abs_diff` calls, the wrapping addition, and the final
return. Adequacy establishes an actual finite normal execution. -/
theorem total_variation_body_total (a b c : UInt64) :
    Wasm.SmallStep.TerminatesWith (totalVariationConfig a b c)
      (fun rs _ => rs = [.i64 (Arithmetic.machineValue a b c)]) := by
  apply wasm_smallStep_heap_globals_runtime_store_terminates
      (α := Unit)
      (σ := absDiffHeap 0)
      (globalσ := absDiffGlobals)
      (post := fun rs _ => rs =
        [.i64 ((if a < b then b - a else a - b)
             + (if b < c then c - b else b - c))])
  · simpa [totalVariationConfig, absDiffBodyConfig] using
      absDiffBodyHeap_agrees «module» «module».initialStore a b 0
  · apply absDiffBodyHeap_inBounds «module» «module».initialStore a b 0
    decide
  · simpa [totalVariationConfig, absDiffBodyConfig] using
      absDiffBodyGlobals_agree «module» «module».initialStore a b 0 rfl
  · simp only [totalVariationConfig]; decide
  · intro hlc gs
    simp only [totalVariationConfig, RuntimeEnv.currentModule_mk1]
    iintro ⟨Hbytes, Hglobals, Hruntime⟩
    ihave Hscratch := absDiffHeap_pointsTo 0 $$ Hbytes
    ihave Hglobal := absDiffGlobals_pointsTo $$ Hglobals
    simp only [func1]
    wasm_twp_pures [twp_localGet twp_localGet]
    iapply twp_call «module» 0 func0Def (by simp [«module»]) (by simp [«module»]) ⟨0⟩ $$
      Hruntime
    iintro Hruntime
    simp [func0Def, Function.toLocals, Function.numParams, ValueType.zero]
    rw [show func0 = absDiffBody by rfl]
    iapply absDiff_smallStep_twp_to_return
      (runtimeModuleOwn ⟨0⟩ «module») _ 1048576 a b 0 (by decide) (by decide)
    · iintro ⟨Hruntime, Hglobal, Hscratch⟩
      wasm_twp_return_from_call Hruntime
      wasm_twp_pures [twp_localGet twp_localGet] using [List.take, UInt32.reduceSub, UInt32.reduceAdd]
      iapply twp_call «module» 0 func0Def (by simp [«module»]) (by simp [«module»]) ⟨0⟩ $$
        Hruntime
      iintro Hruntime
      simp [func0Def, Function.toLocals, Function.numParams, ValueType.zero]
      rw [show func0 = absDiffBody by rfl]
      iapply absDiff_smallStep_twp_to_return
        (runtimeModuleOwn ⟨0⟩ «module») _ 1048576 b c
        (if a < b then b - a else a - b) (by decide) (by decide)
      · iintro ⟨Hruntime, Hglobal, Hscratch⟩
        wasm_twp_return_from_call Hruntime
        simp only [List.take, List.singleton_append]
        iapply twp_pureStep (.instruction .addI64) _ _ (fun _ => Step.addI64)
        wasm_twp_terminal_value twp_returnFromFunction
        iintro %store %observations Hstate
        ipureexact rfl
      · simp only [UInt32.reduceSub, UInt32.reduceAdd]
        iframe
    · simp only [UInt32.reduceSub, UInt32.reduceAdd]
      iframe

/-! ## Total correctness of the named export -/

/-- Three unsigned values in source-parameter order. -/
structure Input where
  a : UInt64
  b : UInt64
  c : UInt64

abbrev Output := UInt64

/-- Invoke the export from the module's canonical initial store. -/
def args (input : Input) : ExportCall Unit :=
  ExportCall.ofHost «module» () [.i64 input.a, .i64 input.b, .i64 input.c]

/-- Decode the export's normal return as an unsigned word. -/
def result (output : Output) : ExportReturn Unit → Prop :=
  fun returned => returned.values = [.i64 output]

/-- This generated module has no imports and needs only the empty host. -/
abbrev Runs := RunsExportWith (HostEnv.empty : HostEnv Unit) «module»

/-- The old body configuration writes a zero scratch word. The generated
module's initial memory is already zero, so this is the canonical export
entry state, including the parameter order and empty call stack. -/
theorem totalVariation_export_entry (input : Input) :
    startExportConfig? (HostEnv.empty : HostEnv Unit) «module»
      "total_variation" (args input) =
      some (totalVariationConfig input.a input.b input.c) := by
  have hmem : («module».initialStore : Store Unit).mem.write64 1048568 0 =
      («module».initialStore : Store Unit).mem := by
    change (Mem.empty 16).write64 1048568 0 = Mem.empty 16
    simp [Mem.write64, Mem.empty]
  simp only [totalVariationConfig, hmem]
  rfl

/--
Informal spec:
For every triple of unsigned 64-bit inputs, the named `total_variation` export
terminates normally from the module's canonical initial store and returns
`(|a-b| + |b-c|) mod 2^64`, with differences computed over natural numbers.
-/
@[spec_of "rust-exported" "total_variation::total_variation"]
def TotalVariationTotalSpec : Prop :=
  ∀ input : Input,
    ∃ output : Output,
      Runs "total_variation" (args input) (result output) ∧
      output.toNat = Arithmetic.mathematicalValue input.a input.b input.c % (2 ^ 64)

@[proves Project.TotalVariation.Spec.TotalVariationTotalSpec]
theorem total_variation_total_correct : TotalVariationTotalSpec := by
  intro input
  refine ⟨Arithmetic.machineValue input.a input.b input.c, ?_,
    Arithmetic.machineValue_toNat input.a input.b input.c⟩
  refine ⟨totalVariationConfig input.a input.b input.c,
    totalVariation_export_entry input, ?_⟩
  exact total_variation_body_total input.a input.b input.c

/-- Representable mathematical variation is returned exactly by the named
export, with a normal execution established rather than assumed. -/
theorem total_variation_export_no_overflow (input : Input)
    (hbound : Arithmetic.mathematicalValue input.a input.b input.c < 2 ^ 64) :
    ∃ output : Output,
      Runs "total_variation" (args input) (result output) ∧
      output.toNat = Arithmetic.mathematicalValue input.a input.b input.c := by
  simpa only [Nat.mod_eq_of_lt hbound] using total_variation_total_correct input

end Project.TotalVariation.Spec
