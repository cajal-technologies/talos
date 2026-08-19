import Project.RustArrayTests.Program

/-!
# Reuse tests for the `CodeLib/RustStd/Array` corpus
-/

namespace Project.RustArrayTests.Spec

open Wasm Wasm.RustStd Wasm.RustStd.Array
open Iris Iris.ProgramLogic Language.Notation
open Wasm.SepLogic

-- The export proofs below unfold the 9-function module deep enough to need a
-- raised recursion limit; set it once for the file.
set_option maxRecDepth 4096

/-! ## Internal impl-body specs

Each is proved directly over its generated small-step body. -/

private def bodyConfig (body : Program) (params : List Value) :
    SmallStep.Config Unit :=
  { expr := .running ⟨⟨params, [], []⟩, body, 1, [], [], []⟩
    store :=
      { runtime := { module := «module», host := {} }
        wasm := «module».initialStore } }

private def exportConfig (env : HostEnv Unit) (st : Store Unit)
    (body : Program) (params : List Value) : SmallStep.Config Unit :=
  { expr := .running ⟨⟨params, [], []⟩, body, 1, [], [], []⟩
    store :=
      { runtime := { module := «module», host := env }
        wasm := st } }

@[spec_of "rust-internal" "rust_array_tests::len_plus_one"]
def LenPlusOneSpec : Prop := ∀ (ptr len : UInt32),
  SmallStep.PartiallyMeets
    (bodyConfig func1 [.i32 ptr, .i32 len])
    (fun rs _store => rs = [.i32 (len + 1)])

@[proves Project.RustArrayTests.Spec.LenPlusOneSpec]
theorem len_plus_one_correct : LenPlusOneSpec := by
  intro ptr len
  apply SmallStep.wasm_smallStep_partiallyMeets (α := Unit)
  intro gs
  simp only [bodyConfig, func1]
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_const
  inext
  iapply SmallStep.wp_add
  inext
  rw [UInt32.add_comm 1 len]
  iapply SmallStep.wp_returnFromFunction
  inext
  iapply wp_value'
  ipureintro
  rfl

@[spec_of "rust-internal" "rust_array_tests::len_plus_arg"]
def LenPlusArgSpec : Prop := ∀ (ptr len n : UInt32),
  SmallStep.PartiallyMeets
    (bodyConfig func0 [.i32 ptr, .i32 len, .i32 n])
    (fun rs _store => rs = [.i32 (len + n)])

@[proves Project.RustArrayTests.Spec.LenPlusArgSpec]
theorem len_plus_arg_correct : LenPlusArgSpec := by
  intro ptr len n
  apply SmallStep.wasm_smallStep_partiallyMeets (α := Unit)
  intro gs
  simp only [bodyConfig, func0]
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_add
  inext
  rw [UInt32.add_comm n len]
  iapply SmallStep.wp_returnFromFunction
  inext
  iapply wp_value'
  ipureintro
  rfl

@[spec_of "rust-internal" "rust_array_tests::empty_plus_three"]
def EmptyPlusThreeSpec : Prop := ∀ (ptr len : UInt32),
  SmallStep.PartiallyMeets
    (bodyConfig func4 [.i32 ptr, .i32 len])
    (fun rs _store => rs = [.i32 (isEmptyValue len + 3)])

@[proves Project.RustArrayTests.Spec.EmptyPlusThreeSpec]
theorem empty_plus_three_correct : EmptyPlusThreeSpec := by
  intro ptr len
  apply SmallStep.wasm_smallStep_runtime_partiallyMeets (α := Unit)
  intro gs
  simp only [bodyConfig, func4]
  iintro Hruntime
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_call «module» 3 func3Def
    (by simp [«module»]) (by simp [«module»]) $$ Hruntime
  inext
  iintro Hruntime
  simp [func3Def, Function.toLocals, Function.numParams, func3]
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
  iapply SmallStep.wp_const
  inext
  iapply SmallStep.wp_add
  inext
  rw [UInt32.add_comm 3 (isEmptyValue len)]
  iapply SmallStep.wp_returnFromFunction
  inext
  iapply wp_value'
  ipureintro
  rfl

@[spec_of "rust-internal" "rust_array_tests::empty_xor_flag"]
def EmptyXorFlagSpec : Prop := ∀ (ptr len flag : UInt32),
  SmallStep.PartiallyMeets
    (bodyConfig func2 [.i32 ptr, .i32 len, .i32 flag])
    (fun rs _store => rs = [.i32 (isEmptyValue len ^^^ flag)])

@[proves Project.RustArrayTests.Spec.EmptyXorFlagSpec]
theorem empty_xor_flag_correct : EmptyXorFlagSpec := by
  intro ptr len flag
  apply SmallStep.wasm_smallStep_runtime_partiallyMeets (α := Unit)
  intro gs
  simp only [bodyConfig, func2]
  iintro Hruntime
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_call «module» 3 func3Def
    (by simp [«module»]) (by simp [«module»]) $$ Hruntime
  inext
  iintro Hruntime
  simp [func3Def, Function.toLocals, Function.numParams, func3]
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
  iapply SmallStep.wp_localGet rfl
  inext
  iapply SmallStep.wp_xor
  inext
  iapply SmallStep.wp_returnFromFunction
  inext
  iapply wp_value'
  ipureintro
  rfl

/-! ## Exported ABI wrappers (fat pointer in memory)

The internal specs above verify the inlined-reuse impl bodies. The wasm exports
(`func5`–`func8`) receive the slice as a fat pointer in linear memory: each loads
`(dataPtr, len)` through the authoritative iris-lean fat-pointer loader and
calls the impl body above. So, like
the `rust_u64_tests` crate, the actual exported functions are verified — but
unlike that scalar crate, here end-to-end through the memory marshalling,
conditional on the shared `FatPtrAt` ABI contract, reusing the same call
bridges. -/

@[spec_of "rust-exported" "rust_array_tests::len_plus_one"]
def LenPlusOneExportSpec : Prop :=
  ∀ (env : HostEnv Unit) (st : Store Unit) (p dataPtr len : UInt32),
    FatPtrAt st p dataPtr len →
    SmallStep.PartiallyMeets
      (exportConfig env st func8 [.i32 p])
      (fun rs _store => rs = [.i32 (len + 1)])

@[proves Project.RustArrayTests.Spec.LenPlusOneExportSpec]
theorem len_plus_one_export_correct : LenPlusOneExportSpec := by
  intro env st p dataPtr len hfat
  apply SmallStep.wasm_smallStep_heap_runtime_partiallyMeets (α := Unit)
      (σ := fatPtrHeap p dataPtr len)
      (φ := fun rs => rs = [.i32 (len + 1)])
  · exact fatPtrHeap_agrees hfat
  · exact fatPtrHeap_inBounds hfat
  · intro gs
    iintro ⟨Hbytes, Hruntime⟩
    ihave Hfat := fatPtrHeap_pointsTo p dataPtr len hfat.noWrap $$ Hbytes
    icases Hfat with ⟨Hdata, Hlen⟩
    simp only [exportConfig, func8]
    ihave HdataLater : ▷ pointsTo_u32 p dataPtr $$ [Hdata]
    · inext
      iexact Hdata
    ihave HlenLater : ▷ pointsTo_u32 (p + 4) len $$ [Hlen]
    · inext
      iexact Hlen
    iapply wp_loadFatPtr 0 p dataPtr len rfl hfat.noWrap $$
      HdataLater HlenLater
    inext
    iapply SmallStep.wp_call «module» 1 func1Def
      (by simp [«module»]) (by simp [«module»]) $$ Hruntime
    inext
    iintro Hruntime
    simp [func1Def, Function.toLocals, Function.numParams, func1]
    iapply SmallStep.wp_localGet rfl
    inext
    iapply SmallStep.wp_const
    inext
    iapply SmallStep.wp_add
    inext
    rw [UInt32.add_comm 1 len]
    iapply SmallStep.wp_returnFromCallExplicit
    inext
    simp only [List.take, List.singleton_append]
    iapply SmallStep.wp_returnFromFunction
    inext
    iapply wp_value'
    iclear Hruntime
    ipureintro
    rfl

@[spec_of "rust-exported" "rust_array_tests::len_plus_arg"]
def LenPlusArgExportSpec : Prop :=
  ∀ (env : HostEnv Unit) (st : Store Unit) (p dataPtr len n : UInt32),
    FatPtrAt st p dataPtr len →
    SmallStep.PartiallyMeets
      (exportConfig env st func7 [.i32 p, .i32 n])
      (fun rs _store => rs = [.i32 (len + n)])

@[proves Project.RustArrayTests.Spec.LenPlusArgExportSpec]
theorem len_plus_arg_export_correct : LenPlusArgExportSpec := by
  intro env st p dataPtr len n hfat
  apply SmallStep.wasm_smallStep_heap_runtime_partiallyMeets (α := Unit)
      (σ := fatPtrHeap p dataPtr len)
      (φ := fun rs => rs = [.i32 (len + n)])
  · exact fatPtrHeap_agrees hfat
  · exact fatPtrHeap_inBounds hfat
  · intro gs
    iintro ⟨Hbytes, Hruntime⟩
    ihave Hfat := fatPtrHeap_pointsTo p dataPtr len hfat.noWrap $$ Hbytes
    icases Hfat with ⟨Hdata, Hlen⟩
    simp only [exportConfig, func7]
    ihave HdataLater : ▷ pointsTo_u32 p dataPtr $$ [Hdata]
    · inext
      iexact Hdata
    ihave HlenLater : ▷ pointsTo_u32 (p + 4) len $$ [Hlen]
    · inext
      iexact Hlen
    iapply wp_loadFatPtr 0 p dataPtr len rfl hfat.noWrap $$
      HdataLater HlenLater
    inext
    iapply SmallStep.wp_localGet rfl
    inext
    iapply SmallStep.wp_call «module» 0 func0Def
      (by simp [«module»]) (by simp [«module»]) $$ Hruntime
    inext
    iintro Hruntime
    simp [func0Def, Function.toLocals, Function.numParams, func0]
    iapply SmallStep.wp_localGet rfl
    inext
    iapply SmallStep.wp_localGet rfl
    inext
    iapply SmallStep.wp_add
    inext
    rw [UInt32.add_comm n len]
    iapply SmallStep.wp_returnFromCallExplicit
    inext
    simp only [List.take, List.singleton_append]
    iapply SmallStep.wp_returnFromFunction
    inext
    iapply wp_value'
    iclear Hruntime
    ipureintro
    rfl

@[spec_of "rust-exported" "rust_array_tests::empty_plus_three"]
def EmptyPlusThreeExportSpec : Prop :=
  ∀ (env : HostEnv Unit) (st : Store Unit) (p dataPtr len : UInt32),
    FatPtrAt st p dataPtr len →
    SmallStep.PartiallyMeets
      (exportConfig env st func5 [.i32 p])
      (fun rs _store => rs = [.i32 (isEmptyValue len + 3)])

@[proves Project.RustArrayTests.Spec.EmptyPlusThreeExportSpec]
theorem empty_plus_three_export_correct : EmptyPlusThreeExportSpec := by
  intro env st p dataPtr len hfat
  apply SmallStep.wasm_smallStep_heap_runtime_partiallyMeets (α := Unit)
      (σ := fatPtrHeap p dataPtr len)
      (φ := fun rs => rs = [.i32 (isEmptyValue len + 3)])
  · exact fatPtrHeap_agrees hfat
  · exact fatPtrHeap_inBounds hfat
  · intro gs
    iintro ⟨Hbytes, Hruntime⟩
    ihave Hfat := fatPtrHeap_pointsTo p dataPtr len hfat.noWrap $$ Hbytes
    icases Hfat with ⟨Hdata, Hlen⟩
    simp only [exportConfig, func5]
    ihave HdataLater : ▷ pointsTo_u32 p dataPtr $$ [Hdata]
    · inext
      iexact Hdata
    ihave HlenLater : ▷ pointsTo_u32 (p + 4) len $$ [Hlen]
    · inext
      iexact Hlen
    iapply wp_loadFatPtr 0 p dataPtr len rfl hfat.noWrap $$
      HdataLater HlenLater
    inext
    iapply SmallStep.wp_call «module» 4 func4Def
      (by simp [«module»]) (by simp [«module»]) $$ Hruntime
    inext
    iintro Hruntime
    simp [func4Def, Function.toLocals, Function.numParams, func4]
    iapply SmallStep.wp_localGet rfl
    inext
    iapply SmallStep.wp_localGet rfl
    inext
    iapply SmallStep.wp_call «module» 3 func3Def
      (by simp [«module»]) (by simp [«module»]) $$ Hruntime
    inext
    iintro Hruntime
    simp [func3Def, Function.toLocals, Function.numParams, func3]
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
    iapply SmallStep.wp_const
    inext
    iapply SmallStep.wp_add
    inext
    rw [UInt32.add_comm 3 (isEmptyValue len)]
    iapply SmallStep.wp_returnFromCallExplicit
    inext
    simp only [List.take, List.singleton_append]
    iapply SmallStep.wp_returnFromFunction
    inext
    iapply wp_value'
    iclear Hruntime
    ipureintro
    rfl

@[spec_of "rust-exported" "rust_array_tests::empty_xor_flag"]
def EmptyXorFlagExportSpec : Prop :=
  ∀ (env : HostEnv Unit) (st : Store Unit) (p dataPtr len flag : UInt32),
    FatPtrAt st p dataPtr len →
    SmallStep.PartiallyMeets
      (exportConfig env st func6 [.i32 p, .i32 flag])
      (fun rs _store => rs = [.i32 (isEmptyValue len ^^^ flag)])

@[proves Project.RustArrayTests.Spec.EmptyXorFlagExportSpec]
theorem empty_xor_flag_export_correct : EmptyXorFlagExportSpec := by
  intro env st p dataPtr len flag hfat
  apply SmallStep.wasm_smallStep_heap_runtime_partiallyMeets (α := Unit)
      (σ := fatPtrHeap p dataPtr len)
      (φ := fun rs => rs = [.i32 (isEmptyValue len ^^^ flag)])
  · exact fatPtrHeap_agrees hfat
  · exact fatPtrHeap_inBounds hfat
  · intro gs
    iintro ⟨Hbytes, Hruntime⟩
    ihave Hfat := fatPtrHeap_pointsTo p dataPtr len hfat.noWrap $$ Hbytes
    icases Hfat with ⟨Hdata, Hlen⟩
    simp only [exportConfig, func6]
    ihave HdataLater : ▷ pointsTo_u32 p dataPtr $$ [Hdata]
    · inext
      iexact Hdata
    ihave HlenLater : ▷ pointsTo_u32 (p + 4) len $$ [Hlen]
    · inext
      iexact Hlen
    iapply wp_loadFatPtr 0 p dataPtr len rfl hfat.noWrap $$
      HdataLater HlenLater
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
    iapply SmallStep.wp_localGet rfl
    inext
    iapply SmallStep.wp_call «module» 3 func3Def
      (by simp [«module»]) (by simp [«module»]) $$ Hruntime
    inext
    iintro Hruntime
    simp [func3Def, Function.toLocals, Function.numParams, func3]
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
    iapply SmallStep.wp_localGet rfl
    inext
    iapply SmallStep.wp_xor
    inext
    iapply SmallStep.wp_returnFromCallExplicit
    inext
    simp only [List.take, List.singleton_append]
    iapply SmallStep.wp_returnFromFunction
    inext
    iapply wp_value'
    iclear Hruntime
    ipureintro
    rfl

end Project.RustArrayTests.Spec
