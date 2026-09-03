import Project.RustArray.Program

/-!
# Specs for the `rust_array` slice primitive corpus

Two layers, both proved over the authoritative small-step language:

* the internal raw `(ptr, len)` bodies (`func0` = `len`, `func2` = `is_empty`),
  using contextual iris-lean instruction rules compatible with the CodeLib
  `len_chunk` / `isEmpty_chunk` APIs; and
* the exported ABI wrappers (`func4` = `len`, `func5` = `is_empty`), which receive
  the slice as a fat pointer in linear memory: they `load32` the `(dataPtr, len)`
  fields back under authoritative byte ownership and then `call` the bodies above (`is_empty`
  through the `crate::is_empty` re-mask wrapper `func1`). The export specs are
  therefore conditional on the caller having laid a fat pointer in memory at the
  argument pointer `p` — the shared `FatPtrAt` contract (`dataPtr` at `p+0`, `len`
  at `p+4`, in bounds). They are *conditional total correctness*: given that
  contract the call terminates with the right value; the out-of-bounds case
  (where the `load32` traps) is outside the contract and deliberately not
  asserted.
-/

namespace Project.RustArray.Spec

open Wasm Wasm.RustStd Wasm.RustStd.Array
open Iris Iris.ProgramLogic Language.Notation
open Wasm.SepLogic
open Wasm.SmallStep

/-! ## Internal `(ptr, len)` body specs

Each starts the exact generated body at `«module».initialStore` with an empty
operand stack and proves its terminal small-step result. -/

private def leafConfig (body : Program) (ptr len : UInt32) :
    SmallStep.Config Unit :=
  { expr := .running
      ⟨⟨[.i32 ptr, .i32 len], [], []⟩, body, 1, [], [], []⟩
    store :=
      { runtime := { instances := #[{ module := «module», host := {} }], entry := ⟨0⟩ }
        wasm := «module».initialStore } }

private def exportConfig (env : HostEnv Unit) (st : Store Unit)
    (body : Program) (p : UInt32) : SmallStep.Config Unit :=
  { expr := .running
      ⟨⟨[.i32 p], [], []⟩, body, 1, [], [], []⟩
    store :=
      { runtime := { instances := #[{ module := «module», host := env }], entry := ⟨0⟩ }
        wasm := st } }

@[spec_of "rust-internal" "rust_array::len"]
def LenSpec : Prop := ∀ (ptr len : UInt32),
  SmallStep.PartiallyMeets (leafConfig func0 ptr len)
    (fun rs _store => rs = [.i32 len])

@[proves Project.RustArray.Spec.LenSpec]
theorem len_correct : LenSpec := by
  intro ptr len
  apply SmallStep.wasm_smallStep_partiallyMeets (α := Unit)
  intro gs
  simp only [leafConfig, func0]
  wasm_wp_pures [wp_localGet]
  wasm_wp_return_value_rfl

@[spec_of "rust-internal" "rust_array::is_empty"]
def IsEmptySpec : Prop := ∀ (ptr len : UInt32),
  SmallStep.PartiallyMeets (leafConfig func2 ptr len)
    (fun rs _store => rs = [.i32 (isEmptyValue len)])

@[proves Project.RustArray.Spec.IsEmptySpec]
theorem is_empty_correct : IsEmptySpec := by
  intro ptr len
  apply SmallStep.wasm_smallStep_partiallyMeets (α := Unit)
  intro gs
  simp only [leafConfig, func2]
  wasm_wp_pures [wp_localGet wp_const]
  wasm_wp_next SmallStep.wp_eq (result := isEmptyValue len) (by rfl)
  wasm_wp_pures [wp_const wp_and]
  rw [show isEmptyValue len &&& 1 = isEmptyValue len by
    unfold isEmptyValue
    by_cases h : len = 0 <;> simp [h]]
  wasm_wp_return_value_rfl

/-! ## Exported ABI wrappers (fat pointer in memory) -/

@[spec_of "rust-exported" "rust_array::len"]
def LenExportSpec : Prop :=
  ∀ (env : HostEnv Unit) (st : Store Unit) (p dataPtr len : UInt32),
    FatPtrAt st p dataPtr len →
    SmallStep.PartiallyMeets (exportConfig env st func4 p)
      (fun rs _store => rs = [.i32 len])

@[proves Project.RustArray.Spec.LenExportSpec]
theorem len_export_correct : LenExportSpec := by
  intro env st p dataPtr len hfat
  apply SmallStep.wasm_smallStep_heap_runtime_instance_partiallyMeets (α := Unit)
      (σ := fatPtrHeap p dataPtr len)
      (φ := fun rs => rs = [.i32 len])
  · exact fatPtrHeap_agrees _ (by simp [storeResolve, exportConfig]) hfat
  · exact fatPtrHeap_inBounds _ (by simp [storeResolve, exportConfig]) hfat
  · simp [exportConfig]
  · intro gs
    simp only [exportConfig, SmallStep.RuntimeEnv.currentModule_mk1]
    iintro ⟨Hbytes, Hruntime⟩
    ihave Hfat := fatPtrHeap_pointsTo p dataPtr len hfat.noWrap $$ Hbytes
    icases Hfat with ⟨Hdata, Hlen⟩
    obtain ⟨hp1, hp2, hp3, hp4, hp5, hp6, hp7⟩ :=
      fatPtrArithmetic_of hfat
    simp only [func4]
    wasm_wp_pures [wp_localGet]
    ihave HdataLater : ▷ pointsTo_u32 0 (p + 0) dataPtr $$ [Hdata]
    · inext
      simp only [UInt32.add_zero]
      iexact Hdata
    wasm_wp_next_bind SmallStep.wp_load32 (address := p) (offset := 0)
      dataPtr (by simp) (by simpa using hp1)
      (by simpa using hp2) (by simpa using hp3) with HdataLater => Hdata
    wasm_wp_pures [wp_localGet]
    ihave HlenLater : ▷ pointsTo_u32 0 (p + 4) len $$ [Hlen]
    · ilater_exact Hlen
    wasm_wp_next_bind SmallStep.wp_load32 (address := p) (offset := 4)
      len hp4 hp5 hp6 hp7 with HlenLater => Hlen
    wasm_wp_next_rebind SmallStep.wp_call «module» 0 func0Def
      (by simp [«module»]) (by simp [«module»]) with Hruntime
    simp [func0Def, Function.toLocals, Function.numParams, func0]
    wasm_wp_pures [wp_localGet]
    wasm_wp_next SmallStep.wp_returnFromCallExplicit $$ Hruntime
    simp only [List.take, List.singleton_append]
    wasm_wp_return_value
    iclear Hdata Hlen
    ipureexact rfl

@[spec_of "rust-exported" "rust_array::is_empty"]
def IsEmptyExportSpec : Prop :=
  ∀ (env : HostEnv Unit) (st : Store Unit) (p dataPtr len : UInt32),
    FatPtrAt st p dataPtr len →
    SmallStep.PartiallyMeets (exportConfig env st func5 p)
      (fun rs _store => rs = [.i32 (isEmptyValue len)])

@[proves Project.RustArray.Spec.IsEmptyExportSpec]
theorem is_empty_export_correct : IsEmptyExportSpec := by
  intro env st p dataPtr len hfat
  apply SmallStep.wasm_smallStep_heap_runtime_instance_partiallyMeets (α := Unit)
      (σ := fatPtrHeap p dataPtr len)
      (φ := fun rs => rs = [.i32 (isEmptyValue len)])
  · exact fatPtrHeap_agrees _ (by simp [storeResolve, exportConfig]) hfat
  · exact fatPtrHeap_inBounds _ (by simp [storeResolve, exportConfig]) hfat
  · simp [exportConfig]
  · intro gs
    simp only [exportConfig, SmallStep.RuntimeEnv.currentModule_mk1]
    iintro ⟨Hbytes, Hruntime⟩
    ihave Hfat := fatPtrHeap_pointsTo p dataPtr len hfat.noWrap $$ Hbytes
    icases Hfat with ⟨Hdata, Hlen⟩
    obtain ⟨hp1, hp2, hp3, hp4, hp5, hp6, hp7⟩ :=
      fatPtrArithmetic_of hfat
    simp only [func5]
    wasm_wp_pures [wp_localGet]
    ihave HdataLater : ▷ pointsTo_u32 0 (p + 0) dataPtr $$ [Hdata]
    · inext
      simp only [UInt32.add_zero]
      iexact Hdata
    wasm_wp_next_bind SmallStep.wp_load32 (address := p) (offset := 0)
      dataPtr (by simp) (by simpa using hp1)
      (by simpa using hp2) (by simpa using hp3) with HdataLater => Hdata
    wasm_wp_pures [wp_localGet]
    ihave HlenLater : ▷ pointsTo_u32 0 (p + 4) len $$ [Hlen]
    · ilater_exact Hlen
    wasm_wp_next_bind SmallStep.wp_load32 (address := p) (offset := 4)
      len hp4 hp5 hp6 hp7 with HlenLater => Hlen
    wasm_wp_next_rebind SmallStep.wp_call «module» 1 func1Def
      (by simp [«module»]) (by simp [«module»]) with Hruntime
    simp [func1Def, Function.toLocals, Function.numParams, func1]
    wasm_wp_pures [wp_localGet wp_localGet]
    wasm_wp_next_rebind SmallStep.wp_call «module» 2 func2Def
      (by simp [«module»]) (by simp [«module»]) with Hruntime
    simp [func2Def, Function.toLocals, Function.numParams, func2]
    wasm_wp_pures [wp_localGet wp_const]
    wasm_wp_next SmallStep.wp_eq (result := isEmptyValue len) (by rfl)
    wasm_wp_pures [wp_const wp_and]
    rw [show isEmptyValue len &&& 1 = isEmptyValue len by
      unfold isEmptyValue
      by_cases h : len = 0 <;> simp [h]]
    wasm_wp_next_rebind SmallStep.wp_returnFromCallExplicit' with Hruntime
    simp only [List.take, List.singleton_append]
    wasm_wp_pures [wp_const wp_and]
    rw [show isEmptyValue len &&& 1 = isEmptyValue len by
      unfold isEmptyValue
      by_cases h : len = 0 <;> simp [h]]
    wasm_wp_next SmallStep.wp_returnFromCallExplicit $$ Hruntime
    simp only [List.take, List.singleton_append]
    wasm_wp_pures [wp_const wp_and]
    rw [show isEmptyValue len &&& 1 = isEmptyValue len by
      unfold isEmptyValue
      by_cases h : len = 0 <;> simp [h]]
    wasm_wp_return_value
    iclear Hdata Hlen
    ipureexact rfl

end Project.RustArray.Spec
