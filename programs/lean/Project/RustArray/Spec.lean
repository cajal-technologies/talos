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

/-! ## Internal `(ptr, len)` body specs

Each starts the exact generated body at `«module».initialStore` with an empty
operand stack and proves its terminal small-step result. -/

private def leafConfig (body : Program) (ptr len : UInt32) :
    SmallStep.Config Unit :=
  { expr := .running
      ⟨⟨[.i32 ptr, .i32 len], [], []⟩, body, 1, [], [], []⟩
    store :=
      { runtime := { module := «module», host := {} }
        wasm := «module».initialStore } }

private def exportConfig (env : HostEnv Unit) (st : Store Unit)
    (body : Program) (p : UInt32) : SmallStep.Config Unit :=
  { expr := .running
      ⟨⟨[.i32 p], [], []⟩, body, 1, [], [], []⟩
    store :=
      { runtime := { module := «module», host := env }
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
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_returnFromFunction
  inext
  iapply wp_value'
  ipureintro
  rfl

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
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_const
  inext
  iapply SmallStep.wp_eq (result := isEmptyValue len) (by rfl)
  inext
  iapply SmallStep.wp_const
  inext
  iapply SmallStep.wp_and
  inext
  rw [show isEmptyValue len &&& 1 = isEmptyValue len by
    unfold isEmptyValue
    by_cases h : len = 0 <;> simp [h]]
  iapply SmallStep.wp_returnFromFunction
  inext
  iapply wp_value'
  ipureintro
  rfl

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
  apply SmallStep.wasm_smallStep_heap_runtime_partiallyMeets (α := Unit)
      (σ := fatPtrHeap p dataPtr len)
      (φ := fun rs => rs = [.i32 len])
  · exact fatPtrHeap_agrees hfat
  · exact fatPtrHeap_inBounds hfat
  · intro gs
    iintro ⟨Hbytes, Hruntime⟩
    ihave Hfat := fatPtrHeap_pointsTo p dataPtr len hfat.noWrap $$ Hbytes
    icases Hfat with ⟨Hdata, Hlen⟩
    obtain ⟨hp1, hp2, hp3, hp4, hp5, hp6, hp7⟩ :=
      fatPtrArithmetic hfat
    simp only [exportConfig, func4]
    iapply SmallStep.wp_localGet rfl
    inext
    ihave HdataLater : ▷ pointsTo_u32 (p + 0) dataPtr $$ [Hdata]
    · inext
      simp only [UInt32.add_zero]
      iexact Hdata
    iapply SmallStep.wp_load32 (address := p) (offset := 0)
      dataPtr (by simp) (by simpa using hp1)
      (by simpa using hp2) (by simpa using hp3) $$ HdataLater
    inext
    iintro Hdata
    iapply SmallStep.wp_localGet rfl
    inext
    ihave HlenLater : ▷ pointsTo_u32 (p + 4) len $$ [Hlen]
    · inext
      iexact Hlen
    iapply SmallStep.wp_load32 (address := p) (offset := 4)
      len hp4 hp5 hp6 hp7 $$ HlenLater
    inext
    iintro Hlen
    iapply SmallStep.wp_call «module» 0 func0Def
      (by simp [«module»]) (by simp [«module»]) $$ Hruntime
    inext
    iintro Hruntime
    simp [func0Def, Function.toLocals, Function.numParams, func0]
    iapply SmallStep.wp_localGet rfl
    inext
    iapply SmallStep.wp_returnFromCallExplicit
    inext
    simp only [List.take, List.singleton_append]
    iapply SmallStep.wp_returnFromFunction
    inext
    iapply wp_value'
    iclear Hdata Hlen Hruntime
    ipureintro
    rfl

@[spec_of "rust-exported" "rust_array::is_empty"]
def IsEmptyExportSpec : Prop :=
  ∀ (env : HostEnv Unit) (st : Store Unit) (p dataPtr len : UInt32),
    FatPtrAt st p dataPtr len →
    SmallStep.PartiallyMeets (exportConfig env st func5 p)
      (fun rs _store => rs = [.i32 (isEmptyValue len)])

@[proves Project.RustArray.Spec.IsEmptyExportSpec]
theorem is_empty_export_correct : IsEmptyExportSpec := by
  intro env st p dataPtr len hfat
  apply SmallStep.wasm_smallStep_heap_runtime_partiallyMeets (α := Unit)
      (σ := fatPtrHeap p dataPtr len)
      (φ := fun rs => rs = [.i32 (isEmptyValue len)])
  · exact fatPtrHeap_agrees hfat
  · exact fatPtrHeap_inBounds hfat
  · intro gs
    iintro ⟨Hbytes, Hruntime⟩
    ihave Hfat := fatPtrHeap_pointsTo p dataPtr len hfat.noWrap $$ Hbytes
    icases Hfat with ⟨Hdata, Hlen⟩
    obtain ⟨hp1, hp2, hp3, hp4, hp5, hp6, hp7⟩ :=
      fatPtrArithmetic hfat
    simp only [exportConfig, func5]
    iapply SmallStep.wp_localGet rfl
    inext
    ihave HdataLater : ▷ pointsTo_u32 (p + 0) dataPtr $$ [Hdata]
    · inext
      simp only [UInt32.add_zero]
      iexact Hdata
    iapply SmallStep.wp_load32 (address := p) (offset := 0)
      dataPtr (by simp) (by simpa using hp1)
      (by simpa using hp2) (by simpa using hp3) $$ HdataLater
    inext
    iintro Hdata
    iapply SmallStep.wp_localGet rfl
    inext
    ihave HlenLater : ▷ pointsTo_u32 (p + 4) len $$ [Hlen]
    · inext
      iexact Hlen
    iapply SmallStep.wp_load32 (address := p) (offset := 4)
      len hp4 hp5 hp6 hp7 $$ HlenLater
    inext
    iintro Hlen
    iapply SmallStep.wp_call «module» 1 func1Def
      (by simp [«module»]) (by simp [«module»]) $$ Hruntime
    inext
    iintro Hruntime
    simp [func1Def, Function.toLocals, Function.numParams, func1]
    iapply SmallStep.wp_localGet rfl
    inext
    iapply SmallStep.wp_localGet rfl
    inext
    iapply SmallStep.wp_call «module» 2 func2Def
      (by simp [«module»]) (by simp [«module»]) $$ Hruntime
    inext
    iintro Hruntime
    simp [func2Def, Function.toLocals, Function.numParams, func2]
    iapply SmallStep.wp_localGet rfl
    inext
    iapply SmallStep.wp_const
    inext
    iapply SmallStep.wp_eq (result := isEmptyValue len) (by rfl)
    inext
    iapply SmallStep.wp_const
    inext
    iapply SmallStep.wp_and
    inext
    rw [show isEmptyValue len &&& 1 = isEmptyValue len by
      unfold isEmptyValue
      by_cases h : len = 0 <;> simp [h]]
    iapply SmallStep.wp_returnFromCallExplicit
    inext
    simp only [List.take, List.singleton_append]
    iapply SmallStep.wp_const
    inext
    iapply SmallStep.wp_and
    inext
    rw [show isEmptyValue len &&& 1 = isEmptyValue len by
      unfold isEmptyValue
      by_cases h : len = 0 <;> simp [h]]
    iapply SmallStep.wp_returnFromCallExplicit
    inext
    simp only [List.take, List.singleton_append]
    iapply SmallStep.wp_const
    inext
    iapply SmallStep.wp_and
    inext
    rw [show isEmptyValue len &&& 1 = isEmptyValue len by
      unfold isEmptyValue
      by_cases h : len = 0 <;> simp [h]]
    iapply SmallStep.wp_returnFromFunction
    inext
    iapply wp_value'
    iclear Hdata Hlen Hruntime
    ipureintro
    rfl

end Project.RustArray.Spec
