import CodeLib.SepLogic.SmallStepAdequacy
import Interpreter.Wasm.Decoder.Wat

/-!
# Concrete examples for the Wasm small-step adequacy bridge

The worked machines that exercise the general theorems in
`CodeLib.SepLogic.SmallStepAdequacy`: globals, direct calls, manual and bulk
memory, tables and element segments, and the parametric total-correctness
examples whose hand-written modules are checked against decoded `.wat` sources.

They live here rather than beside the theory so that the many modules importing
the adequacy bridge do not pay to elaborate them.
-/

namespace Wasm.SmallStep

open Iris OFE COFE BI Iris.BI Iris.Algebra Iris.ProgramLogic
  Language.Notation Std FromMathlib LawfulSet
open Wasm.SepLogic

variable {α : Type}

private theorem sep_pair_pure_rotate
    (P Q : IProp (WasmHeapGF α)) (φ : Prop) :
    (P ∗ Q) ∗ ⌜φ⌝ ⊢ ⌜φ⌝ ∗ P ∗ Q := by
  iintro ⟨⟨HP, HQ⟩, %hφ⟩
  isplitl []
  · ipureintro
    exact hφ
  · isplitl [HP]
    · iexact HP
    · iexact HQ

private def globalGetAdequacyConfig : Config Unit :=
  let runtimeModule : Module := { funcs := [] }
  let initial : Store Unit := runtimeModule.initialStore
  { expr := .running
      ⟨⟨[], [], []⟩, [.globalGet 0], 1, [], [], []⟩
    store :=
      { runtime := { instances := #[{ module := runtimeModule, host := {} }], entry := ⟨0⟩ }
        wasm :=
          { initial with
            globals := { globals := [.i32 42] } } } }

private def global0Heap : WasmGlobalMap Value :=
  insert ∅ (⟨0, 0⟩ : GlobalKey) (.i32 42)

private theorem global0Heap_agrees :
    globalHeapAgrees global0Heap
      globalGetAdequacyConfig.store.wasm.globals := by
  intro index value hget
  simp only [global0Heap] at hget
  by_cases hindex : index = 0
  · subst index
    simp only [get?_insert_eq rfl] at hget
    obtain rfl := Option.some.inj hget
    rfl
  · rw [get?_insert_ne (fun h => hindex (congrArg GlobalKey.index h).symm),
        get?_empty] at hget
    contradiction

private theorem global0Heap_pointsTo [WasmGlobalGS α] :
    ([∗map] index ↦ value ∈ global0Heap,
      globalPointsTo index value) ⊢
      globalPointsTo ⟨0, 0⟩ (.i32 42) := by
  unfold global0Heap
  rw [(BI.BigSepM.bigSepM_insert (get?_empty (⟨0, 0⟩ : GlobalKey))).to_eq,
    BI.BigSepM.bigSepM_empty.to_eq, BI.sep_emp.to_eq]

/-- A concrete adequacy witness for authoritative globals: the WP may derive
the result of `global.get 0` only from ownership allocated for the matching
physical global in the initial machine store. -/
theorem globalGet_adequate :
    adequate Stuckness.NotStuck
      globalGetAdequacyConfig.expr globalGetAdequacyConfig.store
      (fun values _ => values = [.i32 42]) := by
  apply wasm_smallStep_heap_globals_adequacy (α := Unit)
    (σ := (∅ : WasmHeapMap (Option UInt8)))
    (globalσ := global0Heap)
    (φ := fun values => values = [.i32 42])
  · intro address value hget
    rw [get?_empty] at hget
    contradiction
  · intro address hne
    exact absurd (get?_empty address) hne
  · exact global0Heap_agrees
  · decide
  · intro gs
    simp only [BI.BigSepM.bigSepM_empty.to_eq, BI.emp_sep.to_eq]
    unfold global0Heap
    rw [(BI.BigSepM.bigSepM_insert (get?_empty (⟨0, 0⟩ : GlobalKey))).to_eq,
      BI.BigSepM.bigSepM_empty.to_eq, BI.sep_emp.to_eq]
    iintro Hglobal
    simp only [globalGetAdequacyConfig]
    simp only [← globalPointsToAt_eq]
    wasm_wp_next wp_globalGet $$ Hglobal
    iintro Hglobal
    wasm_wp_finish_value
    ipureintro
    rfl

def noopCallModule : Module :=
  { funcs := [{ body := [.ret] }] }

def noopCallConfig : Config Unit :=
  let initial : Store Unit := noopCallModule.initialStore
  { expr := .running
      ⟨⟨[], [], []⟩, [.call 0, .ret], 0, [], [], []⟩
    store :=
      { runtime := { instances := #[{ module := noopCallModule, host := {} }], entry := ⟨0⟩ }
        wasm := initial } }

/-- End-to-end adequacy for direct-call entry and administrative return. The
function lookup is justified by immutable runtime ownership, not by a theorem
premise detached from the physical `MachineStore`. -/
theorem noopCall_adequate :
    adequate Stuckness.NotStuck noopCallConfig.expr noopCallConfig.store
      (fun values _ => values = []) := by
  apply wasm_smallStep_runtime_instance_adequacy (α := Unit)
    (φ := fun values => values = [])
  · decide
  · intro gs
    simp only [noopCallConfig, RuntimeEnv.currentModule_mk1]
    iintro ⟨Hruntime, _HruntimeInstances⟩
    iclear _HruntimeInstances
    wasm_wp_next wp_call noopCallModule 0 ({ body := [.ret] } : Function)
        (by simp [noopCallModule]) rfl ⟨0⟩ $$ Hruntime
    iintro Hruntime
    simp only [noopCallModule, Function.toLocals, Function.numParams,
      List.take_nil, List.reverse_nil, List.drop_nil, List.length_nil]
    wasm_wp_next wp_returnFromCallExplicit $$ Hruntime
    wasm_wp_return_value
    ipureintro
    rfl

private def word16Heap (word : UInt32) :
    WasmHeapMap (Option UInt8) :=
  store32Heap ∅ 0 16 word

private theorem word16Heap_pointsTo (word : UInt32) [WasmHeapGS α] :
    ([∗map] address ↦ value ∈ word16Heap word,
      pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        address (DFrac.own 1) value) ⊢
      pointsTo_u32 0 16 word := by
  let σ0 : WasmHeapMap (Option UInt8) := ∅
  let σ1 := insert σ0 (⟨0, 16⟩ : MemoryKey) (some (u32Byte word 0))
  let σ2 := insert σ1 (⟨0, 17⟩ : MemoryKey) (some (u32Byte word 1))
  let σ3 := insert σ2 (⟨0, 18⟩ : MemoryKey) (some (u32Byte word 2))
  have h17 : get? σ1 ⟨0, 17⟩ = none := by
    dsimp [σ1, σ0]
    rw [get?_insert_ne (by decide), get?_empty]
  have h18 : get? σ2 ⟨0, 18⟩ = none := by
    dsimp [σ2, σ1, σ0]
    rw [get?_insert_ne (by decide), get?_insert_ne (by decide), get?_empty]
  have h19 : get? σ3 ⟨0, 19⟩ = none := by
    dsimp [σ3, σ2, σ1, σ0]
    rw [get?_insert_ne (by decide), get?_insert_ne (by decide),
      get?_insert_ne (by decide), get?_empty]
  change
    ([∗map] address ↦ value ∈
      insert σ3 (⟨0, 19⟩ : MemoryKey) (some (u32Byte word 3)),
      pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        address (DFrac.own 1) value) ⊢
      pointsTo_u32 0 16 word
  rw [(BI.BigSepM.bigSepM_insert h19).to_eq]
  rw [(BI.BigSepM.bigSepM_insert h18).to_eq]
  rw [(BI.BigSepM.bigSepM_insert h17).to_eq]
  rw [(BI.BigSepM.bigSepM_insert (get?_empty (⟨0, 16⟩ : MemoryKey))).to_eq]
  rw [BI.BigSepM.bigSepM_empty.to_eq, BI.sep_emp.to_eq]
  unfold pointsTo_u32
  simp only [UInt32.reduceAdd]
  iintro ⟨H19, H18, H17, H16⟩
  iframe

private theorem emptyHeap_agrees (resolve : Nat → Option Mem) :
    heapAgreesWithMem (∅ : WasmHeapMap (Option UInt8)) resolve :=
  heapAgreesWithMem_empty _

private theorem emptyHeap_inBounds (resolve : Nat → Option Mem) :
    heapAddressesInBounds (∅ : WasmHeapMap (Option UInt8)) resolve :=
  heapAddressesInBounds_empty _

/-- Concrete machine used to connect the clean word-roundtrip Iris contract
to iris-lean adequacy. -/
def wordRoundtripAdequacyModule : Module :=
  { funcs :=
      [{ body :=
          [ .const 16, .const 0x12345678, .store32 0,
            .const 16, .load32 0 ],
         results := [.i32] }]
    memory := some { pagesMin := 1 } }

def wordRoundtripAdequacyConfig (oldWord : UInt32) : Config Unit :=
  let initial : Store Unit := wordRoundtripAdequacyModule.initialStore
  { expr := .running
      ⟨⟨[], [], []⟩,
        [ .const 16, .const 0x12345678, .store32 0,
          .const 16, .load32 0 ],
        1, [], [], []⟩
    store :=
      { runtime := { instances := #[{ module := wordRoundtripAdequacyModule, host := {} }], entry := ⟨0⟩ }
        wasm :=
          { initial with
            mem := initial.mem.write32 16 oldWord } } }

/-- The manual 32-bit memory roundtrip is adequate for the authoritative
small-step relation: every Iris value it reaches is the stored word. This is
partial correctness, matching iris-lean's current adequacy support. -/
theorem wordRoundtrip_adequate (oldWord : UInt32) :
    adequate Stuckness.NotStuck
      (wordRoundtripAdequacyConfig oldWord).expr
      (wordRoundtripAdequacyConfig oldWord).store
      (fun values _ => values = [.i32 0x12345678]) := by
  apply wasm_smallStep_heap_adequacy (α := Unit)
    (σ := word16Heap oldWord)
    (φ := fun values => values = [.i32 0x12345678])
  · unfold word16Heap
    apply store32_sound0 (mem := wordRoundtripAdequacyModule.initialStore.mem)
      (h1 := rfl) (h2 := rfl) (h3 := rfl)
    exact emptyHeap_agrees _
  · unfold word16Heap
    apply store32_inBounds0 (mem := wordRoundtripAdequacyModule.initialStore.mem)
      (h1 := rfl) (h2 := rfl) (h3 := rfl)
    · native_decide
    · exact emptyHeap_inBounds _
  · intro gs
    iintro Hbytes
    ihave Hword := word16Heap_pointsTo oldWord $$ Hbytes
    simp only [wordRoundtripAdequacyConfig, wordRoundtripAdequacyModule]
    have hpost : ∀ values : List Value,
        (iprop% ⌜values = [.i32 0x12345678]⌝ ∗
          pointsTo_u32 0 16 0x12345678) ⊢
        (iprop% ⌜values = [.i32 0x12345678]⌝) := by
      intro values
      iintro ⟨%hvalues, _Hword⟩
      ipureintro
      exact hvalues
    iapply wp_mono hpost
    iapply wp_wordRoundtrip
    iexact Hword

/-- State-sensitive adequacy exposes the physical effect of the manual
roundtrip, not only its returned value. -/
theorem wordRoundtrip_store_partiallyMeets (oldWord : UInt32) :
    PartiallyMeets (wordRoundtripAdequacyConfig oldWord)
      (fun values store =>
        values = [.i32 0x12345678] ∧
          store.wasm.mem.read32 16 = 0x12345678) := by
  apply wasm_smallStep_heap_globals_runtime_store_partiallyMeets
    (α := Unit)
    (σ := word16Heap oldWord)
    (globalσ := (∅ : WasmGlobalMap Value))
  · unfold word16Heap
    apply store32_sound0 (mem := wordRoundtripAdequacyModule.initialStore.mem)
      (h1 := rfl) (h2 := rfl) (h3 := rfl)
    exact emptyHeap_agrees _
  · unfold word16Heap
    apply store32_inBounds0 (mem := wordRoundtripAdequacyModule.initialStore.mem)
      (h1 := rfl) (h2 := rfl) (h3 := rfl)
    · native_decide
    · exact emptyHeap_inBounds _
  · intro index value hget
    rw [get?_empty] at hget
    contradiction
  · simp only [wordRoundtripAdequacyConfig]; decide
  · intro gs
    simp only [BI.BigSepM.bigSepM_empty.to_eq]
    iintro ⟨Hbytes, _Hglobals, _Hruntime⟩
    ihave Hword := word16Heap_pointsTo oldWord $$ Hbytes
    simp only [wordRoundtripAdequacyConfig, wordRoundtripAdequacyModule]
    have hpost : ∀ values : List Value,
        (iprop% ⌜values = [.i32 0x12345678]⌝ ∗
          pointsTo_u32 0 16 0x12345678) ⊢
        (iprop% ∀ (store : MachineStore Unit)
            (observations : List StepKind),
          stateInterp (GF := WasmHeapGF Unit) store 0 [] 0 -∗
          ⌜values = [.i32 0x12345678] ∧
            store.wasm.mem.read32 16 = 0x12345678⌝) := by
      intro values
      iintro ⟨%hvalues, Hword⟩ %store %observations Hstate
      imod stateInterp_pointsTo_u32_facts
        store 0 [] 0 16 0x12345678
        (by decide) (by decide) (by decide) $$
          [$Hstate $Hword] with %Hfacts
      ipureintro
      exact ⟨hvalues, Hfacts.1⟩
    iapply wp_mono hpost
    iapply wp_wordRoundtrip
    iexact Hword

/-- Authoritative footprint for the two cells used by `wp_swapWords`. -/
private def swapWordsHeap : WasmHeapMap (Option UInt8) :=
  store32Heap (store32Heap ∅ 0 0 11) 0 4 22

private theorem swapWordsHeap_agrees (mem : Mem) :
    heapAgreesWithMem swapWordsHeap
      (fun id => if id = 0 then some ((mem.write32 0 11).write32 4 22) else none) := by
  unfold swapWordsHeap
  apply store32_sound0 (mem := mem.write32 0 11) (h1 := rfl) (h2 := rfl) (h3 := rfl)
  apply store32_sound0 (mem := mem) (h1 := rfl) (h2 := rfl) (h3 := rfl)
  exact emptyHeap_agrees _

private theorem swapWordsHeap_inBounds (memory : Mem)
    (hpages : 1 ≤ memory.pages) :
    heapAddressesInBounds swapWordsHeap
      (fun id => if id = 0 then some ((memory.write32 0 11).write32 4 22) else none) := by
  unfold swapWordsHeap
  apply store32_inBounds0 (mem := memory.write32 0 11) (h1 := rfl) (h2 := rfl) (h3 := rfl)
  · have hcapacity :
        65536 ≤ memory.pages * 65536 :=
      Nat.mul_le_mul_right 65536 hpages
    simp only [UInt32.toNat_ofNat, Mem.write32]
    omega
  · apply store32_inBounds0 (mem := memory) (h1 := rfl) (h2 := rfl) (h3 := rfl)
    · have hcapacity :
          65536 ≤ memory.pages * 65536 :=
        Nat.mul_le_mul_right 65536 hpages
      simp only [UInt32.toNat_zero, Nat.zero_add]
      omega
    · exact emptyHeap_inBounds _

private theorem swapWordsHeap_pointsTo [WasmHeapGS α] :
    ([∗map] address ↦ value ∈ swapWordsHeap,
      pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        address (DFrac.own 1) value) ⊢
      pointsTo_u32 0 0 11 ∗ pointsTo_u32 0 4 22 := by
  unfold swapWordsHeap store32Heap
  rw [(BI.BigSepM.bigSepM_insert (by native_decide)).to_eq]
  rw [(BI.BigSepM.bigSepM_insert (by native_decide)).to_eq]
  rw [(BI.BigSepM.bigSepM_insert (by native_decide)).to_eq]
  rw [(BI.BigSepM.bigSepM_insert (by native_decide)).to_eq]
  rw [(BI.BigSepM.bigSepM_insert (by native_decide)).to_eq]
  rw [(BI.BigSepM.bigSepM_insert (by native_decide)).to_eq]
  rw [(BI.BigSepM.bigSepM_insert (by native_decide)).to_eq]
  rw [(BI.BigSepM.bigSepM_insert (get?_empty (⟨0, 0⟩ : MemoryKey))).to_eq]
  rw [BI.BigSepM.bigSepM_empty.to_eq, BI.sep_emp.to_eq]
  unfold pointsTo_u32
  simp only [UInt32.reduceAdd]
  iintro ⟨H7, H6, H5, H4, H3, H2, H1, H0⟩
  iframe

def swapWordsAdequacyModule : Module :=
  { funcs :=
      [{ locals := [.i32, .i32]
         body :=
          [ .const 0, .load32 0, .localSet 0,
            .const 4, .load32 0, .localSet 1,
            .const 0, .localGet 1, .store32 0,
            .const 4, .localGet 0, .store32 0,
            .const 0, .load32 0,
            .const 4, .load32 0 ],
         results := [.i32, .i32] }]
    memory := some { pagesMin := 1 } }

def swapWordsAdequacyConfig : Config Unit :=
  let initial : Store Unit := swapWordsAdequacyModule.initialStore
  { expr := .running
      ⟨⟨[], [.i32 0, .i32 0], []⟩,
        [ .const 0, .load32 0, .localSet 0,
          .const 4, .load32 0, .localSet 1,
          .const 0, .localGet 1, .store32 0,
          .const 4, .localGet 0, .store32 0,
          .const 0, .load32 0,
          .const 4, .load32 0 ],
        2, [], [], []⟩
    store :=
      { runtime := { instances := #[{ module := swapWordsAdequacyModule, host := {} }], entry := ⟨0⟩ }
        wasm :=
          { initial with
            mem := (initial.mem.write32 0 11).write32 4 22 } } }

/-- Closed iris-lean adequacy for a genuinely mutating manual example. The
physical store initially contains `[11, 22]`; authoritative byte ownership is
allocated from that store, `wp_swapWords` proves the exchange, and adequacy
exposes the returned post-swap values without assuming any ghost resources. -/
theorem swapWords_adequate :
    adequate Stuckness.NotStuck
      swapWordsAdequacyConfig.expr swapWordsAdequacyConfig.store
      (fun values _ => values = [.i32 11, .i32 22]) := by
  apply wasm_smallStep_heap_adequacy (α := Unit)
    (σ := swapWordsHeap)
    (φ := fun values => values = [.i32 11, .i32 22])
  · apply swapWordsHeap_agrees
  · apply swapWordsHeap_inBounds
    native_decide
  · intro gs
    iintro Hbytes
    ihave Hwords := swapWordsHeap_pointsTo $$ Hbytes
    simp only [swapWordsAdequacyConfig, swapWordsAdequacyModule]
    have hpost : ∀ values : List Value,
        (iprop% ⌜values = [.i32 11, .i32 22]⌝ ∗
          pointsTo_u32 0 0 22 ∗ pointsTo_u32 0 4 11) ⊢
        (iprop% ⌜values = [.i32 11, .i32 22]⌝) := by
      intro values
      iintro ⟨%hvalues, _H0, _H4⟩
      ipureintro
      exact hvalues
    iapply wp_mono hpost
    iapply wp_swapWords
    iexact Hwords

/-- State-sensitive Iris adequacy for the two-word swap.  In addition to the
returned stack, this exposes both exchanged words in the reached physical
memory from one authoritative state interpretation. -/
theorem swapWords_store_partiallyMeets :
    PartiallyMeets swapWordsAdequacyConfig
      (fun values store =>
        values = [.i32 11, .i32 22] ∧
          store.wasm.mem.read32 0 = 22 ∧
          store.wasm.mem.read32 4 = 11) := by
  apply wasm_smallStep_heap_globals_runtime_store_partiallyMeets
    (α := Unit)
    (σ := swapWordsHeap)
    (globalσ := (∅ : WasmGlobalMap Value))
  · apply swapWordsHeap_agrees
  · apply swapWordsHeap_inBounds
    native_decide
  · intro index value hget
    rw [get?_empty] at hget
    contradiction
  · decide
  · intro gs
    simp only [BI.BigSepM.bigSepM_empty.to_eq]
    iintro ⟨Hbytes, _Hglobals, _Hruntime⟩
    ihave Hwords := swapWordsHeap_pointsTo $$ Hbytes
    simp only [swapWordsAdequacyConfig, swapWordsAdequacyModule]
    have hpost : ∀ values : List Value,
        (iprop% ⌜values = [.i32 11, .i32 22]⌝ ∗
          pointsTo_u32 0 0 22 ∗ pointsTo_u32 0 4 11) ⊢
        (iprop% ∀ (store : MachineStore Unit)
            (_observations : List StepKind),
          stateInterp (GF := WasmHeapGF Unit) store 0 [] 0 -∗
          ⌜values = [.i32 11, .i32 22] ∧
            store.wasm.mem.read32 0 = 22 ∧
            store.wasm.mem.read32 4 = 11⌝) := by
      intro values
      iintro ⟨%hvalues, H0, H4⟩ %store %_observations Hstate
      imod stateInterp_pointsTo_u32_facts_frame
        store 0 [] 0 0 22
        (by decide) (by decide) (by decide) $$
          [$Hstate $H0] with ⟨Hstate, _H0, %Hfacts0⟩
      imod stateInterp_pointsTo_u32_facts
        store 0 [] 0 4 11
        (by decide) (by decide) (by decide) $$
          [$Hstate $H4] with %Hfacts4
      ipureintro
      exact ⟨hvalues, Hfacts0.1, Hfacts4.1⟩
    iapply wp_mono hpost
    iapply wp_swapWords
    iexact Hwords

/-! ### Three-word reverse with a framed middle cell -/

private def reverseThreeWordsHeap : WasmHeapMap (Option UInt8) :=
  store32Heap swapWordsHeap 0 8 33

private theorem reverseThreeWordsHeap_agrees (mem : Mem) :
    heapAgreesWithMem reverseThreeWordsHeap
      (fun id => if id = 0 then some (((mem.write32 0 11).write32 4 22).write32 8 33) else none) := by
  unfold reverseThreeWordsHeap
  apply store32_sound0 (mem := (mem.write32 0 11).write32 4 22) (h1 := rfl) (h2 := rfl) (h3 := rfl)
  exact swapWordsHeap_agrees mem

private theorem reverseThreeWordsHeap_inBounds (memory : Mem)
    (hpages : 1 ≤ memory.pages) :
    heapAddressesInBounds reverseThreeWordsHeap
      (fun id => if id = 0 then some (((memory.write32 0 11).write32 4 22).write32 8 33) else none) := by
  unfold reverseThreeWordsHeap
  apply store32_inBounds0 (mem := (memory.write32 0 11).write32 4 22)
    (h1 := rfl) (h2 := rfl) (h3 := rfl)
  · have hcapacity :
        65536 ≤ memory.pages * 65536 :=
      Nat.mul_le_mul_right 65536 hpages
    simp only [UInt32.toNat_ofNat, Mem.write32]
    omega
  · exact swapWordsHeap_inBounds memory hpages

private theorem reverseThreeWordsHeap_pointsTo [WasmHeapGS α] :
    ([∗map] address ↦ value ∈ reverseThreeWordsHeap,
      pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        address (DFrac.own 1) value) ⊢
      pointsTo_u32 0 0 11 ∗ pointsTo_u32 0 4 22 ∗
        pointsTo_u32 0 8 33 := by
  unfold reverseThreeWordsHeap
  iintro Hheap
  ihave H8 := store32Heap_pointsTo swapWordsHeap 0 8 33
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
    (by decide) (by decide) (by decide) $$ Hheap
  icases H8 with ⟨H8, Hheap⟩
  ihave Hwords := swapWordsHeap_pointsTo $$ Hheap
  icases Hwords with ⟨H0, H4⟩
  iframe

def reverseThreeWordsAdequacyModule : Module :=
  { funcs :=
      [{ locals := [.i32, .i32]
         body :=
          [ .const 0, .load32 0, .localSet 0,
            .const 8, .load32 0, .localSet 1,
            .const 0, .localGet 1, .store32 0,
            .const 8, .localGet 0, .store32 0,
            .const 0, .load32 0,
            .const 8, .load32 0 ],
         results := [.i32, .i32] }]
    memory := some { pagesMin := 1 } }

def reverseThreeWordsAdequacyConfig : Config Unit :=
  let initial : Store Unit := reverseThreeWordsAdequacyModule.initialStore
  { expr := .running
      ⟨⟨[], [.i32 0, .i32 0], []⟩,
        [ .const 0, .load32 0, .localSet 0,
          .const 8, .load32 0, .localSet 1,
          .const 0, .localGet 1, .store32 0,
          .const 8, .localGet 0, .store32 0,
          .const 0, .load32 0,
          .const 8, .load32 0 ],
        2, [], [], []⟩
    store :=
      { runtime := { instances := #[{ module := reverseThreeWordsAdequacyModule, host := {} }], entry := ⟨0⟩ }
        wasm :=
          { initial with
            mem :=
              ((initial.mem.write32 0 11).write32 4 22).write32 8 33 } } }

/-- End-to-end Iris partial correctness for reversing three words.  The
endpoint words are exchanged in physical memory and the owned middle word is
framed unchanged. -/
theorem reverseThreeWords_store_partiallyMeets :
    PartiallyMeets reverseThreeWordsAdequacyConfig
      (fun values store =>
        values = [.i32 11, .i32 33] ∧
          store.wasm.mem.read32 0 = 33 ∧
          store.wasm.mem.read32 4 = 22 ∧
          store.wasm.mem.read32 8 = 11) := by
  apply wasm_smallStep_heap_globals_runtime_store_partiallyMeets
    (α := Unit)
    (σ := reverseThreeWordsHeap)
    (globalσ := (∅ : WasmGlobalMap Value))
  · apply reverseThreeWordsHeap_agrees
  · apply reverseThreeWordsHeap_inBounds
    native_decide
  · intro index value hget
    rw [get?_empty] at hget
    contradiction
  · decide
  · intro gs
    simp only [BI.BigSepM.bigSepM_empty.to_eq]
    iintro ⟨Hbytes, _Hglobals, _Hruntime⟩
    ihave Hwords := reverseThreeWordsHeap_pointsTo $$ Hbytes
    simp only [reverseThreeWordsAdequacyConfig,
      reverseThreeWordsAdequacyModule]
    have hpost : ∀ values : List Value,
        (iprop% ⌜values = [.i32 11, .i32 33]⌝ ∗
          pointsTo_u32 0 0 33 ∗ pointsTo_u32 0 4 22 ∗
          pointsTo_u32 0 8 11) ⊢
        (iprop% ∀ (store : MachineStore Unit)
            (_observations : List StepKind),
          stateInterp (GF := WasmHeapGF Unit) store 0 [] 0 -∗
          ⌜values = [.i32 11, .i32 33] ∧
            store.wasm.mem.read32 0 = 33 ∧
            store.wasm.mem.read32 4 = 22 ∧
            store.wasm.mem.read32 8 = 11⌝) := by
      intro values
      iintro ⟨%hvalues, H0, H4, H8⟩
        %store %_observations Hstate
      imod stateInterp_pointsTo_u32_facts_frame
        store 0 [] 0 0 33
        (by decide) (by decide) (by decide) $$
          [$Hstate $H0] with ⟨Hstate, _H0, %Hfacts0⟩
      imod stateInterp_pointsTo_u32_facts_frame
        store 0 [] 0 4 22
        (by decide) (by decide) (by decide) $$
          [$Hstate $H4] with ⟨Hstate, _H4, %Hfacts4⟩
      imod stateInterp_pointsTo_u32_facts
        store 0 [] 0 8 11
        (by decide) (by decide) (by decide) $$
          [$Hstate $H8] with %Hfacts8
      ipureintro
      exact ⟨hvalues, Hfacts0.1, Hfacts4.1, Hfacts8.1⟩
    iapply wp_mono hpost
    iapply wp_reverseThreeWords
    iexact Hwords

/-! ### Three-word partition with a pivot in its final position -/

private def partitionThreeWordsHeap : WasmHeapMap (Option UInt8) :=
  store32Heap (store32Heap (store32Heap ∅ 0 0 33) 0 4 11) 0 8 22

private theorem partitionThreeWordsHeap_agrees (memory : Mem) :
    heapAgreesWithMem partitionThreeWordsHeap
      (fun id => if id = 0 then some (((memory.write32 0 33).write32 4 11).write32 8 22) else none) := by
  unfold partitionThreeWordsHeap
  apply store32_sound0 (mem := (memory.write32 0 33).write32 4 11) (h1 := rfl) (h2 := rfl) (h3 := rfl)
  apply store32_sound0 (mem := memory.write32 0 33) (h1 := rfl) (h2 := rfl) (h3 := rfl)
  apply store32_sound0 (mem := memory) (h1 := rfl) (h2 := rfl) (h3 := rfl)
  exact emptyHeap_agrees _

private theorem partitionThreeWordsHeap_inBounds (memory : Mem)
    (hpages : 1 ≤ memory.pages) :
    heapAddressesInBounds partitionThreeWordsHeap
      (fun id => if id = 0 then some (((memory.write32 0 33).write32 4 11).write32 8 22) else none) := by
  unfold partitionThreeWordsHeap
  have hcapacity :
      65536 ≤ memory.pages * 65536 :=
    Nat.mul_le_mul_right 65536 hpages
  apply store32_inBounds0 (mem := (memory.write32 0 33).write32 4 11)
    (h1 := rfl) (h2 := rfl) (h3 := rfl)
  · simp only [UInt32.toNat_ofNat, Mem.write32]
    omega
  · apply store32_inBounds0 (mem := memory.write32 0 33) (h1 := rfl) (h2 := rfl) (h3 := rfl)
    · simp only [UInt32.toNat_ofNat, Mem.write32]
      omega
    · apply store32_inBounds0 (mem := memory) (h1 := rfl) (h2 := rfl) (h3 := rfl)
      · simp only [UInt32.toNat_ofNat]
        omega
      · exact emptyHeap_inBounds _

private theorem partitionThreeWordsHeap_pointsTo [WasmHeapGS α] :
    ([∗map] address ↦ value ∈ partitionThreeWordsHeap,
      pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        address (DFrac.own 1) value) ⊢
      pointsTo_u32 0 0 33 ∗ pointsTo_u32 0 4 11 ∗
        pointsTo_u32 0 8 22 := by
  unfold partitionThreeWordsHeap
  iintro Hheap
  ihave H8 := store32Heap_pointsTo
    (store32Heap (store32Heap ∅ 0 0 33) 0 4 11) 0 8 22
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
    (by decide) (by decide) (by decide) $$ Hheap
  icases H8 with ⟨H8, Hheap⟩
  ihave H4 := store32Heap_pointsTo (store32Heap ∅ 0 0 33) 0 4 11
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
    (by decide) (by decide) (by decide) $$ Hheap
  icases H4 with ⟨H4, Hheap⟩
  ihave H0 := store32Heap_pointsTo (∅ : WasmHeapMap (Option UInt8)) 0 0 33
    (get?_empty (⟨0, 0⟩ : MemoryKey)) (get?_empty (⟨0, 1⟩ : MemoryKey))
    (get?_empty (⟨0, 2⟩ : MemoryKey)) (get?_empty (⟨0, 3⟩ : MemoryKey))
    (by decide) (by decide) (by decide) $$ Hheap
  icases H0 with ⟨H0, _Hempty⟩
  iframe

def partitionThreeWordsAdequacyModule : Module :=
  { funcs :=
      [{ locals := [.i32, .i32, .i32]
         body :=
          [ .const 0, .load32 0, .localSet 0,
            .const 4, .load32 0, .localSet 1,
            .const 8, .load32 0, .localSet 2,
            .const 0, .localGet 1, .store32 0,
            .const 4, .localGet 2, .store32 0,
            .const 8, .localGet 0, .store32 0 ] }]
    memory := some { pagesMin := 1 } }

def partitionThreeWordsAdequacyConfig : Config Unit :=
  let initial : Store Unit := partitionThreeWordsAdequacyModule.initialStore
  { expr := .running
      ⟨⟨[], [.i32 0, .i32 0, .i32 0], []⟩,
        [ .const 0, .load32 0, .localSet 0,
          .const 4, .load32 0, .localSet 1,
          .const 8, .load32 0, .localSet 2,
          .const 0, .localGet 1, .store32 0,
          .const 4, .localGet 2, .store32 0,
          .const 8, .localGet 0, .store32 0 ],
        0, [], [], []⟩
    store :=
      { runtime := { instances := #[{ module := partitionThreeWordsAdequacyModule, host := {} }], entry := ⟨0⟩ }
        wasm :=
          { initial with
            mem := ((initial.mem.write32 0 33).write32 4 11).write32 8 22 } } }

/-- Closed state-sensitive Iris proof for the first sorting kernel.  The
physical post-state contains the same three words, with pivot `22` at address
four and the unsigned left/right partition predicates established. -/
theorem partitionThreeWords_store_partiallyMeets :
    PartiallyMeets partitionThreeWordsAdequacyConfig
      (fun values store =>
        values = [] ∧
          store.wasm.mem.read32 0 = 11 ∧
          store.wasm.mem.read32 4 = 22 ∧
          store.wasm.mem.read32 8 = 33 ∧
          store.wasm.mem.read32 0 ≤ store.wasm.mem.read32 4 ∧
          store.wasm.mem.read32 4 ≤ store.wasm.mem.read32 8) := by
  apply wasm_smallStep_heap_globals_runtime_store_partiallyMeets
    (α := Unit)
    (σ := partitionThreeWordsHeap)
    (globalσ := (∅ : WasmGlobalMap Value))
  · apply partitionThreeWordsHeap_agrees
  · apply partitionThreeWordsHeap_inBounds
    native_decide
  · intro index value hget
    rw [get?_empty] at hget
    contradiction
  · decide
  · intro gs
    simp only [BI.BigSepM.bigSepM_empty.to_eq]
    iintro ⟨Hbytes, _Hglobals, _Hruntime⟩
    ihave Hwords := partitionThreeWordsHeap_pointsTo $$ Hbytes
    simp only [partitionThreeWordsAdequacyConfig,
      partitionThreeWordsAdequacyModule]
    have hpost : ∀ values : List Value,
        (iprop% ⌜values = []⌝ ∗
          pointsTo_u32 0 0 11 ∗ pointsTo_u32 0 4 22 ∗
          pointsTo_u32 0 8 33) ⊢
        (iprop% ∀ (store : MachineStore Unit)
            (_observations : List StepKind),
          stateInterp (GF := WasmHeapGF Unit) store 0 [] 0 -∗
          ⌜values = [] ∧
            store.wasm.mem.read32 0 = 11 ∧
            store.wasm.mem.read32 4 = 22 ∧
            store.wasm.mem.read32 8 = 33 ∧
            store.wasm.mem.read32 0 ≤ store.wasm.mem.read32 4 ∧
            store.wasm.mem.read32 4 ≤ store.wasm.mem.read32 8⌝) := by
      intro values
      iintro ⟨%hvalues, H0, H4, H8⟩
        %store %_observations Hstate
      imod stateInterp_pointsTo_u32_facts_frame
        store 0 [] 0 0 11
        (by decide) (by decide) (by decide) $$
          [$Hstate $H0] with ⟨Hstate, _H0, %Hfacts0⟩
      imod stateInterp_pointsTo_u32_facts_frame
        store 0 [] 0 4 22
        (by decide) (by decide) (by decide) $$
          [$Hstate $H4] with ⟨Hstate, _H4, %Hfacts4⟩
      imod stateInterp_pointsTo_u32_facts
        store 0 [] 0 8 33
        (by decide) (by decide) (by decide) $$
          [$Hstate $H8] with %Hfacts8
      ipureintro
      exact ⟨hvalues, Hfacts0.1, Hfacts4.1, Hfacts8.1,
        by rw [Hfacts0.1, Hfacts4.1]; decide,
        by rw [Hfacts4.1, Hfacts8.1]; decide⟩
    iapply wp_mono hpost
    iapply wp_partitionThreeWords
    iexact Hwords

/-! ### Merge of two singleton sorted runs -/

private def mergeTwoWordsHeap : WasmHeapMap (Option UInt8) :=
  store32Heap (store32Heap ∅ 0 0 9) 0 4 4

private theorem mergeTwoWordsHeap_agrees (memory : Mem) :
    heapAgreesWithMem mergeTwoWordsHeap
      (fun id => if id = 0 then some ((memory.write32 0 9).write32 4 4) else none) := by
  unfold mergeTwoWordsHeap
  apply store32_sound0 (mem := memory.write32 0 9) (h1 := rfl) (h2 := rfl) (h3 := rfl)
  apply store32_sound0 (mem := memory) (h1 := rfl) (h2 := rfl) (h3 := rfl)
  exact emptyHeap_agrees _

private theorem mergeTwoWordsHeap_inBounds (memory : Mem)
    (hpages : 1 ≤ memory.pages) :
    heapAddressesInBounds mergeTwoWordsHeap
      (fun id => if id = 0 then some ((memory.write32 0 9).write32 4 4) else none) := by
  unfold mergeTwoWordsHeap
  have hcapacity :
      65536 ≤ memory.pages * 65536 :=
    Nat.mul_le_mul_right 65536 hpages
  apply store32_inBounds0 (mem := memory.write32 0 9) (h1 := rfl) (h2 := rfl) (h3 := rfl)
  · simp only [UInt32.toNat_ofNat, Mem.write32]
    omega
  · apply store32_inBounds0 (mem := memory) (h1 := rfl) (h2 := rfl) (h3 := rfl)
    · simp only [UInt32.toNat_zero, Nat.zero_add]
      omega
    · exact emptyHeap_inBounds _

private theorem mergeTwoWordsHeap_pointsTo [WasmHeapGS α] :
    ([∗map] address ↦ value ∈ mergeTwoWordsHeap,
      pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        address (DFrac.own 1) value) ⊢
      pointsTo_u32 0 0 9 ∗ pointsTo_u32 0 4 4 := by
  unfold mergeTwoWordsHeap
  iintro Hheap
  ihave H4 := store32Heap_pointsTo (store32Heap ∅ 0 0 9) 0 4 4
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
    (by decide) (by decide) (by decide) $$ Hheap
  icases H4 with ⟨H4, Hheap⟩
  ihave H0 := store32Heap_pointsTo (∅ : WasmHeapMap (Option UInt8)) 0 0 9
    (get?_empty (⟨0, 0⟩ : MemoryKey)) (get?_empty (⟨0, 1⟩ : MemoryKey))
    (get?_empty (⟨0, 2⟩ : MemoryKey)) (get?_empty (⟨0, 3⟩ : MemoryKey))
    (by decide) (by decide) (by decide) $$ Hheap
  icases H0 with ⟨H0, _Hempty⟩
  iframe

def mergeTwoWordsAdequacyModule : Module :=
  { funcs :=
      [{ locals := [.i32, .i32]
         body :=
          [ .const 0, .load32 0, .localSet 0,
            .const 4, .load32 0, .localSet 1,
            .localGet 0, .localGet 1, .ltU,
            .iff 0 0
              [ .const 0, .localGet 0, .store32 0,
                .const 4, .localGet 1, .store32 0 ]
              [ .const 0, .localGet 1, .store32 0,
                .const 4, .localGet 0, .store32 0 ] ] }]
    memory := some { pagesMin := 1 } }

def mergeTwoWordsAdequacyConfig : Config Unit :=
  let initial : Store Unit := mergeTwoWordsAdequacyModule.initialStore
  { expr := .running
      ⟨⟨[], [.i32 0, .i32 0], []⟩,
        [ .const 0, .load32 0, .localSet 0,
          .const 4, .load32 0, .localSet 1,
          .localGet 0, .localGet 1, .ltU,
          .iff 0 0
            [ .const 0, .localGet 0, .store32 0,
              .const 4, .localGet 1, .store32 0 ]
            [ .const 0, .localGet 1, .store32 0,
              .const 4, .localGet 0, .store32 0 ] ],
        0, [], [], []⟩
    store :=
      { runtime := { instances := #[{ module := mergeTwoWordsAdequacyModule, host := {} }], entry := ⟨0⟩ }
        wasm :=
          { initial with
            mem := (initial.mem.write32 0 9).write32 4 4 } } }

/-- State-sensitive Iris adequacy for a real compare-and-branch merge. The two
singleton input runs are preserved and sorted in the reached physical memory. -/
theorem mergeTwoWords_store_partiallyMeets :
    PartiallyMeets mergeTwoWordsAdequacyConfig
      (fun values store =>
        values = [] ∧
          store.wasm.mem.read32 0 = 4 ∧
          store.wasm.mem.read32 4 = 9 ∧
          store.wasm.mem.read32 0 ≤ store.wasm.mem.read32 4) := by
  apply wasm_smallStep_heap_globals_runtime_store_partiallyMeets
    (α := Unit)
    (σ := mergeTwoWordsHeap)
    (globalσ := (∅ : WasmGlobalMap Value))
  · apply mergeTwoWordsHeap_agrees
  · apply mergeTwoWordsHeap_inBounds
    native_decide
  · intro index value hget
    rw [get?_empty] at hget
    contradiction
  · decide
  · intro gs
    simp only [BI.BigSepM.bigSepM_empty.to_eq]
    iintro ⟨Hbytes, _Hglobals, _Hruntime⟩
    ihave Hwords := mergeTwoWordsHeap_pointsTo $$ Hbytes
    simp only [mergeTwoWordsAdequacyConfig,
      mergeTwoWordsAdequacyModule]
    have hpost : ∀ values : List Value,
        (iprop% ⌜values = []⌝ ∗
          pointsTo_u32 0 0 4 ∗ pointsTo_u32 0 4 9) ⊢
        (iprop% ∀ (store : MachineStore Unit)
            (_observations : List StepKind),
          stateInterp (GF := WasmHeapGF Unit) store 0 [] 0 -∗
          ⌜values = [] ∧
            store.wasm.mem.read32 0 = 4 ∧
            store.wasm.mem.read32 4 = 9 ∧
            store.wasm.mem.read32 0 ≤ store.wasm.mem.read32 4⌝) := by
      intro values
      iintro ⟨%hvalues, H0, H4⟩ %store %_observations Hstate
      imod stateInterp_pointsTo_u32_facts_frame
        store 0 [] 0 0 4
        (by decide) (by decide) (by decide) $$
          [$Hstate $H0] with ⟨Hstate, _H0, %Hfacts0⟩
      imod stateInterp_pointsTo_u32_facts
        store 0 [] 0 4 9
        (by decide) (by decide) (by decide) $$
          [$Hstate $H4] with %Hfacts4
      ipureintro
      exact ⟨hvalues, Hfacts0.1, Hfacts4.1,
        by rw [Hfacts0.1, Hfacts4.1]; decide⟩
    iapply wp_mono hpost
    iapply wp_mergeTwoWords
    iexact Hwords

/-! ### Bulk-memory examples -/

private def fillFourBytesHeap (oldWord : UInt32) :
    WasmHeapMap (Option UInt8) :=
  store32Heap (store32Heap ∅ 0 16 oldWord) 0 32 0x12345678

private theorem fillFourBytesHeap_agrees (memory : Mem)
    (oldWord : UInt32) :
    heapAgreesWithMem (fillFourBytesHeap oldWord)
      (fun id => if id = 0 then some ((memory.write32 16 oldWord).write32 32 0x12345678) else none) := by
  unfold fillFourBytesHeap
  apply store32_sound0 (mem := memory.write32 16 oldWord) (h1 := rfl) (h2 := rfl) (h3 := rfl)
  apply store32_sound0 (mem := memory) (h1 := rfl) (h2 := rfl) (h3 := rfl)
  exact emptyHeap_agrees _

private theorem fillFourBytesHeap_inBounds (memory : Mem)
    (oldWord : UInt32) (hpages : 1 ≤ memory.pages) :
    heapAddressesInBounds (fillFourBytesHeap oldWord)
      (fun id => if id = 0 then some ((memory.write32 16 oldWord).write32 32 0x12345678) else none) := by
  unfold fillFourBytesHeap
  apply store32_inBounds0 (mem := memory.write32 16 oldWord) (h1 := rfl) (h2 := rfl) (h3 := rfl)
  · have hcapacity :
        65536 ≤ memory.pages * 65536 :=
      Nat.mul_le_mul_right 65536 hpages
    simp only [UInt32.toNat_ofNat, Mem.write32]
    omega
  · apply store32_inBounds0 (mem := memory) (h1 := rfl) (h2 := rfl) (h3 := rfl)
    · have hcapacity :
          65536 ≤ memory.pages * 65536 :=
        Nat.mul_le_mul_right 65536 hpages
      simp only [UInt32.toNat_ofNat]
      omega
    · exact emptyHeap_inBounds _

private theorem fillFourBytesHeap_pointsTo (oldWord : UInt32)
    [WasmHeapGS α] :
    ([∗map] address ↦ value ∈ fillFourBytesHeap oldWord,
      pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        address (DFrac.own 1) value) ⊢
      pointsTo_u32 0 16 oldWord ∗ pointsTo_u32 0 32 0x12345678 := by
  unfold fillFourBytesHeap
  iintro Hheap
  have mk_ne : ∀ a b : UInt32, a ≠ b → (⟨0, a⟩ : MemoryKey) ≠ ⟨0, b⟩ :=
    fun a b h hh => h (congrArg MemoryKey.addr hh)
  have hnone (address : UInt32)
      (h0 : 16 ≠ address) (h1 : 16 + 1 ≠ address)
      (h2 : 16 + 2 ≠ address) (h3 : 16 + 3 ≠ address) :
      get? (store32Heap ∅ 0 16 oldWord) ⟨0, address⟩ = none := by
    unfold store32Heap
    rw [get?_insert_ne (mk_ne _ _ h3), get?_insert_ne (mk_ne _ _ h2),
      get?_insert_ne (mk_ne _ _ h1), get?_insert_ne (mk_ne _ _ h0),
      get?_empty]
  ihave H32 := store32Heap_pointsTo
    (store32Heap ∅ 0 16 oldWord) 0 32 0x12345678
    (hnone 32 (by decide) (by decide) (by decide) (by decide))
    (hnone (32 + 1) (by decide) (by decide) (by decide) (by decide))
    (hnone (32 + 2) (by decide) (by decide) (by decide) (by decide))
    (hnone (32 + 3) (by decide) (by decide) (by decide) (by decide))
    (by decide) (by decide) (by decide) $$ Hheap
  icases H32 with ⟨H32, Hheap⟩
  ihave H16 := store32Heap_pointsTo
    (∅ : WasmHeapMap (Option UInt8)) 0 16 oldWord
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
    (by decide) (by decide) (by decide) $$ Hheap
  icases H16 with ⟨H16, _Hempty⟩
  iframe

def fillFourBytesAdequacyModule : Module :=
  { funcs :=
      [{ body :=
          [ .const 16, .const 0xAB, .const 4, .memoryFill,
            .const 16, .load32 0,
            .const 32, .load32 0 ],
         results := [.i32, .i32] }]
    memory := some { pagesMin := 1 } }

def fillFourBytesAdequacyConfig (oldWord : UInt32) : Config Unit :=
  let initial : Store Unit := fillFourBytesAdequacyModule.initialStore
  { expr := .running
      ⟨⟨[], [], []⟩,
        [ .const 16, .const 0xAB, .const 4, .memoryFill,
          .const 16, .load32 0,
          .const 32, .load32 0 ],
        2, [], [], []⟩
    store :=
      { runtime := { instances := #[{ module := fillFourBytesAdequacyModule, host := {} }], entry := ⟨0⟩ }
        wasm :=
          { initial with
            mem := (initial.mem.write32 16 oldWord).write32
              32 0x12345678 } } }

/-- The four-byte fill updates its physical target and frames the disjoint
word at address 32 unchanged. -/
theorem fillFourBytes_store_partiallyMeets (oldWord : UInt32) :
    PartiallyMeets (fillFourBytesAdequacyConfig oldWord)
      (fun values store =>
        values = [.i32 0x12345678, .i32 0xABABABAB] ∧
          store.wasm.mem.read32 16 = 0xABABABAB ∧
          store.wasm.mem.read32 32 = 0x12345678) := by
  apply wasm_smallStep_heap_globals_runtime_store_partiallyMeets
    (α := Unit)
    (σ := fillFourBytesHeap oldWord)
    (globalσ := (∅ : WasmGlobalMap Value))
  · apply fillFourBytesHeap_agrees
  · apply fillFourBytesHeap_inBounds
    native_decide
  · intro index value hget
    rw [get?_empty] at hget
    contradiction
  · simp only [fillFourBytesAdequacyConfig]; decide
  · intro gs
    simp only [BI.BigSepM.bigSepM_empty.to_eq]
    iintro ⟨Hbytes, _Hglobals, _Hruntime⟩
    ihave Hwords := fillFourBytesHeap_pointsTo oldWord $$ Hbytes
    simp only [fillFourBytesAdequacyConfig, fillFourBytesAdequacyModule]
    have hpost : ∀ values : List Value,
        (iprop% ⌜values = [.i32 0x12345678, .i32 0xABABABAB]⌝ ∗
          pointsTo_u32 0 16 0xABABABAB ∗
          pointsTo_u32 0 32 0x12345678) ⊢
        (iprop% ∀ (store : MachineStore Unit)
            (_observations : List StepKind),
          stateInterp (GF := WasmHeapGF Unit) store 0 [] 0 -∗
          ⌜values = [.i32 0x12345678, .i32 0xABABABAB] ∧
            store.wasm.mem.read32 16 = 0xABABABAB ∧
            store.wasm.mem.read32 32 = 0x12345678⌝) := by
      intro values
      iintro ⟨%hvalues, H16, H32⟩
        %store %_observations Hstate
      imod stateInterp_pointsTo_u32_facts_frame
        store 0 [] 0 16 0xABABABAB
        (by decide) (by decide) (by decide) $$
          [$Hstate $H16] with ⟨Hstate, _H16, %Hfacts16⟩
      imod stateInterp_pointsTo_u32_facts
        store 0 [] 0 32 0x12345678
        (by decide) (by decide) (by decide) $$
          [$Hstate $H32] with %Hfacts32
      ipureintro
      exact ⟨hvalues, Hfacts16.1, Hfacts32.1⟩
    iapply wp_mono hpost
    iapply wp_fillFourBytes oldWord
    iexact Hwords

private def copyWordHeap (oldDestination : UInt32) :
    WasmHeapMap (Option UInt8) :=
  store32Heap (store32Heap ∅ 0 0 0x04030201) 0 8 oldDestination

private theorem copyWordHeap_agrees (memory : Mem)
    (oldDestination : UInt32) :
    heapAgreesWithMem (copyWordHeap oldDestination)
      (fun id => if id = 0 then some ((memory.write32 0 0x04030201).write32 8 oldDestination) else none) := by
  unfold copyWordHeap
  apply store32_sound0 (mem := memory.write32 0 0x04030201) (h1 := rfl) (h2 := rfl) (h3 := rfl)
  apply store32_sound0 (mem := memory) (h1 := rfl) (h2 := rfl) (h3 := rfl)
  exact emptyHeap_agrees _

private theorem copyWordHeap_inBounds (memory : Mem)
    (oldDestination : UInt32) (hpages : 1 ≤ memory.pages) :
    heapAddressesInBounds (copyWordHeap oldDestination)
      (fun id => if id = 0 then some ((memory.write32 0 0x04030201).write32 8 oldDestination) else none) := by
  unfold copyWordHeap
  apply store32_inBounds0 (mem := memory.write32 0 0x04030201) (h1 := rfl) (h2 := rfl) (h3 := rfl)
  · have hcapacity :
        65536 ≤ memory.pages * 65536 :=
      Nat.mul_le_mul_right 65536 hpages
    simp only [UInt32.toNat_ofNat, Mem.write32]
    omega
  · apply store32_inBounds0 (mem := memory) (h1 := rfl) (h2 := rfl) (h3 := rfl)
    · have hcapacity :
          65536 ≤ memory.pages * 65536 :=
        Nat.mul_le_mul_right 65536 hpages
      simp only [UInt32.toNat_zero, Nat.zero_add]
      omega
    · exact emptyHeap_inBounds _

private theorem copyWordHeap_pointsTo (oldDestination : UInt32)
    [WasmHeapGS α] :
    ([∗map] address ↦ value ∈ copyWordHeap oldDestination,
      pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        address (DFrac.own 1) value) ⊢
      pointsTo_u32 0 0 0x04030201 ∗ pointsTo_u32 0 8 oldDestination := by
  unfold copyWordHeap
  iintro Hheap
  ihave H8 := store32Heap_pointsTo
    (store32Heap ∅ 0 0 0x04030201) 0 8 oldDestination
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
    (by decide) (by decide) (by decide) $$ Hheap
  icases H8 with ⟨H8, Hheap⟩
  ihave H0 := store32Heap_pointsTo
    (∅ : WasmHeapMap (Option UInt8)) 0 0 0x04030201
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
    (by decide) (by decide) (by decide) $$ Hheap
  icases H0 with ⟨H0, _Hempty⟩
  iframe

def copyWordAdequacyModule : Module :=
  { funcs :=
      [{ body :=
          [ .const 8, .const 0, .const 4, .memoryCopy,
            .const 8, .load32 0 ],
         results := [.i32] }]
    memory := some { pagesMin := 1 } }

def copyWordAdequacyConfig (oldDestination : UInt32) : Config Unit :=
  let initial : Store Unit := copyWordAdequacyModule.initialStore
  { expr := .running
      ⟨⟨[], [], []⟩,
        [ .const 8, .const 0, .const 4, .memoryCopy,
          .const 8, .load32 0 ],
        1, [], [], []⟩
    store :=
      { runtime := { instances := #[{ module := copyWordAdequacyModule, host := {} }], entry := ⟨0⟩ }
        wasm :=
          { initial with
            mem := (initial.mem.write32 0 0x04030201).write32
              8 oldDestination } } }

/-- The aligned copy preserves the physical source word and replaces the
physical destination word with its value. -/
theorem copyWord_store_partiallyMeets (oldDestination : UInt32) :
    PartiallyMeets (copyWordAdequacyConfig oldDestination)
      (fun values store =>
        values = [.i32 0x04030201] ∧
          store.wasm.mem.read32 0 = 0x04030201 ∧
          store.wasm.mem.read32 8 = 0x04030201) := by
  apply wasm_smallStep_heap_globals_runtime_store_partiallyMeets
    (α := Unit)
    (σ := copyWordHeap oldDestination)
    (globalσ := (∅ : WasmGlobalMap Value))
  · apply copyWordHeap_agrees
  · apply copyWordHeap_inBounds
    native_decide
  · intro index value hget
    rw [get?_empty] at hget
    contradiction
  · simp only [copyWordAdequacyConfig]; decide
  · intro gs
    simp only [BI.BigSepM.bigSepM_empty.to_eq]
    iintro ⟨Hbytes, _Hglobals, _Hruntime⟩
    ihave Hwords := copyWordHeap_pointsTo oldDestination $$ Hbytes
    simp only [copyWordAdequacyConfig, copyWordAdequacyModule]
    have hpost : ∀ values : List Value,
        (iprop% ⌜values = [.i32 0x04030201]⌝ ∗
          pointsTo_u32 0 0 0x04030201 ∗
          pointsTo_u32 0 8 0x04030201) ⊢
        (iprop% ∀ (store : MachineStore Unit)
            (_observations : List StepKind),
          stateInterp (GF := WasmHeapGF Unit) store 0 [] 0 -∗
          ⌜values = [.i32 0x04030201] ∧
            store.wasm.mem.read32 0 = 0x04030201 ∧
            store.wasm.mem.read32 8 = 0x04030201⌝) := by
      intro values
      iintro ⟨%hvalues, H0, H8⟩
        %store %_observations Hstate
      imod stateInterp_pointsTo_u32_facts_frame
        store 0 [] 0 0 0x04030201
        (by decide) (by decide) (by decide) $$
          [$Hstate $H0] with ⟨Hstate, _H0, %Hfacts0⟩
      imod stateInterp_pointsTo_u32_facts
        store 0 [] 0 8 0x04030201
        (by decide) (by decide) (by decide) $$
          [$Hstate $H8] with %Hfacts8
      ipureintro
      exact ⟨hvalues, Hfacts0.1, Hfacts8.1⟩
    iapply wp_mono hpost
    iapply wp_copyWord oldDestination
    iexact Hwords

private def copyOverlapWordHeap : WasmHeapMap (Option UInt8) :=
  store64Heap ∅ 0 0 0x8877665544332211

private theorem copyOverlapWordHeap_agrees (memory : Mem) :
    heapAgreesWithMem copyOverlapWordHeap
      (fun id => if id = 0 then some (memory.write64 0 0x8877665544332211) else none) := by
  unfold copyOverlapWordHeap
  apply store64_sound0 (mem := memory)
    (h1 := rfl) (h2 := rfl) (h3 := rfl) (h4 := rfl) (h5 := rfl) (h6 := rfl) (h7 := rfl)
  exact emptyHeap_agrees _

private theorem copyOverlapWordHeap_inBounds (memory : Mem)
    (hpages : 1 ≤ memory.pages) :
    heapAddressesInBounds copyOverlapWordHeap
      (fun id => if id = 0 then some (memory.write64 0 0x8877665544332211) else none) := by
  unfold copyOverlapWordHeap
  apply store64_inBounds0 (mem := memory)
    (h1 := rfl) (h2 := rfl) (h3 := rfl) (h4 := rfl) (h5 := rfl) (h6 := rfl) (h7 := rfl)
  · have hcapacity :
        65536 ≤ memory.pages * 65536 :=
      Nat.mul_le_mul_right 65536 hpages
    simp only [UInt32.toNat_zero, Nat.zero_add]
    omega
  · exact emptyHeap_inBounds _

private theorem copyOverlapWordHeap_pointsTo [WasmHeapGS α] :
    ([∗map] address ↦ value ∈ copyOverlapWordHeap,
      pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        address (DFrac.own 1) value) ⊢
      pointsTo_u64 0 0 0x8877665544332211 := by
  unfold copyOverlapWordHeap
  iintro Hheap
  ihave Hword := store64Heap_pointsTo
    (∅ : WasmHeapMap (Option UInt8)) 0 0 0x8877665544332211
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) $$ Hheap
  icases Hword with ⟨Hword, _Hempty⟩
  iexact Hword

def copyOverlapWordAdequacyModule : Module :=
  { funcs :=
      [{ body :=
          [ .const 2, .const 0, .const 4, .memoryCopy,
            .const 0, .load64 0 ],
         results := [.i64] }]
    memory := some { pagesMin := 1 } }

def copyOverlapWordAdequacyConfig : Config Unit :=
  let initial : Store Unit := copyOverlapWordAdequacyModule.initialStore
  { expr := .running
      ⟨⟨[], [], []⟩,
        [ .const 2, .const 0, .const 4, .memoryCopy,
          .const 0, .load64 0 ],
        1, [], [], []⟩
    store :=
      { runtime := { instances := #[{ module := copyOverlapWordAdequacyModule, host := {} }], entry := ⟨0⟩ }
        wasm :=
          { initial with
            mem := initial.mem.write64 0 0x8877665544332211 } } }

/-- State-sensitive Iris adequacy for overlapping `memory.copy`: the reached
physical word is the memmove result, demonstrating that the source bytes were
snapshotted before the overlapping destination was written. -/
theorem copyOverlapWord_store_partiallyMeets :
    PartiallyMeets copyOverlapWordAdequacyConfig
      (fun values store =>
        values = [.i64 0x8877443322112211] ∧
          store.wasm.mem.read64 0 = 0x8877443322112211) := by
  apply wasm_smallStep_heap_globals_runtime_store_partiallyMeets
    (α := Unit)
    (σ := copyOverlapWordHeap)
    (globalσ := (∅ : WasmGlobalMap Value))
  · apply copyOverlapWordHeap_agrees
  · apply copyOverlapWordHeap_inBounds
    native_decide
  · intro index value hget
    rw [get?_empty] at hget
    contradiction
  · decide
  · intro gs
    simp only [BI.BigSepM.bigSepM_empty.to_eq]
    iintro ⟨Hbytes, _Hglobals, _Hruntime⟩
    ihave Hword := copyOverlapWordHeap_pointsTo $$ Hbytes
    simp only [copyOverlapWordAdequacyConfig,
      copyOverlapWordAdequacyModule]
    have hpost : ∀ values : List Value,
        (iprop% ⌜values = [.i64 0x8877443322112211]⌝ ∗
          pointsTo_u64 0 0 0x8877443322112211) ⊢
        (iprop% ∀ (store : MachineStore Unit)
            (_observations : List StepKind),
          stateInterp (GF := WasmHeapGF Unit) store 0 [] 0 -∗
          ⌜values = [.i64 0x8877443322112211] ∧
            store.wasm.mem.read64 0 = 0x8877443322112211⌝) := by
      intro values
      iintro ⟨%hvalues, Hword⟩
        %store %_observations Hstate
      imod stateInterp_pointsTo_u64_facts
        store 0 [] 0 0 0x8877443322112211
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) $$
          [$Hstate $Hword] with %Hfacts
      ipureintro
      exact ⟨hvalues, Hfacts.1⟩
    iapply wp_mono hpost
    iapply wp_copyOverlapWord
    iexact Hword

private def memoryInitDropHeap : WasmHeapMap (Option UInt8) :=
  store32Heap ∅ 0 16 0

private theorem memoryInitDropHeap_agrees (memory : Mem) :
    heapAgreesWithMem memoryInitDropHeap
      (fun id => if id = 0 then some (memory.write32 16 0) else none) := by
  unfold memoryInitDropHeap
  apply store32_sound0 (mem := memory) (h1 := rfl) (h2 := rfl) (h3 := rfl)
  exact emptyHeap_agrees _

private theorem memoryInitDropHeap_inBounds (memory : Mem)
    (hpages : 1 ≤ memory.pages) :
    heapAddressesInBounds memoryInitDropHeap
      (fun id => if id = 0 then some (memory.write32 16 0) else none) := by
  unfold memoryInitDropHeap
  apply store32_inBounds0 (mem := memory) (h1 := rfl) (h2 := rfl) (h3 := rfl)
  · have hcapacity :
        65536 ≤ memory.pages * 65536 :=
      Nat.mul_le_mul_right 65536 hpages
    simp only [UInt32.toNat_ofNat]
    omega
  · exact emptyHeap_inBounds _

private theorem memoryInitDropHeap_pointsTo [WasmHeapGS α] :
    ([∗map] address ↦ value ∈ memoryInitDropHeap,
      pointsTo (GF := WasmHeapGF α) (H := WasmHeapMap)
        address (DFrac.own 1) value) ⊢
      pointsTo_u32 0 16 0 := by
  unfold memoryInitDropHeap
  iintro Hheap
  ihave Hword := store32Heap_pointsTo
    (∅ : WasmHeapMap (Option UInt8)) 0 16 0
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) $$ Hheap
  icases Hword with ⟨Hword, _Hempty⟩
  iexact Hword

private def memoryInitDropSegments :
    WasmDataSegmentMap (Option (List UInt8)) :=
  insert ∅ (⟨0, 0⟩ : DataSegmentKey) (some [1, 2, 3, 4])

private theorem memoryInitDropSegments_agree :
    dataSegmentHeapAgrees memoryInitDropSegments
      [some [1, 2, 3, 4]] := by
  intro index value hget
  unfold memoryInitDropSegments at hget
  by_cases hindex : index = 0
  · subst index
    simp only [get?_insert_eq rfl, Option.some.injEq] at hget
    subst value
    rfl
  · rw [get?_insert_ne (fun h => hindex (congrArg DataSegmentKey.index h).symm), get?_empty] at hget
    contradiction

private theorem memoryInitDropSegments_pointsTo [WasmDataSegmentGS α] :
    ([∗map] index ↦ value ∈ memoryInitDropSegments,
      dataSegmentPointsTo index value) ⊢
      dataSegmentPointsTo ⟨0, 0⟩ (some [1, 2, 3, 4]) := by
  unfold memoryInitDropSegments
  rw [(BI.BigSepM.bigSepM_insert (get?_empty (⟨0, 0⟩ : DataSegmentKey))).to_eq,
    BI.BigSepM.bigSepM_empty.to_eq, BI.sep_emp.to_eq]

def memoryInitDropAdequacyModule : Module :=
  { funcs :=
      [{ body :=
          [ .const 16, .const 0, .const 4, .memoryInit 0,
            .dataDrop 0, .const 16, .load32 0 ],
         results := [.i32] }]
    memory := some
      { pagesMin := 1
        data := [{ offset := none, bytes := [1, 2, 3, 4] }] } }

def memoryInitDropAdequacyConfig : Config Unit :=
  let initial : Store Unit := memoryInitDropAdequacyModule.initialStore
  { expr := .running
      ⟨⟨[], [], []⟩,
        [ .const 16, .const 0, .const 4, .memoryInit 0,
          .dataDrop 0, .const 16, .load32 0 ],
        1, [], [], []⟩
    store :=
      { runtime := { instances := #[{ module := memoryInitDropAdequacyModule, host := {} }], entry := ⟨0⟩ }
        wasm := { initial with mem := initial.mem.write32 16 0 } } }

/-- Closed physical-state specification for passive data initialization and
consumption. It proves the initialized word and that the segment is dropped
in the reached machine store. -/
theorem memoryInitDrop_store_partiallyMeets :
    PartiallyMeets memoryInitDropAdequacyConfig
      (fun values store =>
        values = [.i32 0x04030201] ∧
          store.wasm.mem.read32 16 = 0x04030201 ∧
          store.wasm.dataSegments[0]? = some none) := by
  apply
    wasm_smallStep_heap_globals_segments_runtime_store_partiallyMeets
      (α := Unit)
      (σ := memoryInitDropHeap)
      (globalσ := (∅ : WasmGlobalMap Value))
      (dataSegmentσ := memoryInitDropSegments)
  · apply memoryInitDropHeap_agrees
  · apply memoryInitDropHeap_inBounds
    native_decide
  · intro index value hget
    rw [get?_empty] at hget
    contradiction
  · exact memoryInitDropSegments_agree
  · decide
  · intro gs
    simp only [BI.BigSepM.bigSepM_empty.to_eq]
    iintro ⟨Hbytes, _Hglobals, Hsegments, _Hruntime⟩
    ihave Hword := memoryInitDropHeap_pointsTo $$ Hbytes
    ihave Hsegment := memoryInitDropSegments_pointsTo $$ Hsegments
    simp only [memoryInitDropAdequacyConfig,
      memoryInitDropAdequacyModule]
    have hpost : ∀ values : List Value,
        (iprop% ⌜values = [.i32 0x04030201]⌝ ∗
          pointsTo_u32 0 16 0x04030201 ∗
          dataSegmentPointsTo ⟨0, 0⟩ none) ⊢
        (iprop% ∀ (store : MachineStore Unit)
            (_observations : List StepKind),
          stateInterp (GF := WasmHeapGF Unit) store 0 [] 0 -∗
          ⌜values = [.i32 0x04030201] ∧
            store.wasm.mem.read32 16 = 0x04030201 ∧
            store.wasm.dataSegments[0]? = some none⌝) := by
      intro values
      iintro ⟨%hvalues, Hword, Hsegment⟩
        %store %_observations Hstate
      imod stateInterp_pointsTo_u32_facts_frame
        store 0 [] 0 16 0x04030201
        (by decide) (by decide) (by decide) $$
          [$Hstate $Hword] with
        ⟨Hstate, Hword, %HwordFacts⟩
      simp only [← dataSegmentPointsToAt_eq]
      ihave_pure HsegmentFact :
          ⌜store.wasm.dataSegments[0]? = some none⌝ using
        stateInterp_dataSegment_facts store 0 [] 0 0 none $$ [Hstate Hsegment]
      ipureintro
      constructor
      · exact hvalues
      constructor
      · exact HwordFacts.1
      · exact HsegmentFact
    iapply wp_mono hpost
    iapply wp_memoryInitDrop 0
    iframe

private def tableSetGetMap : WasmTableMap TableInst :=
  insert ∅ (⟨0, 0⟩ : TableKey) [.funcref none]

private theorem tableSetGetMap_agrees :
    tableHeapAgrees tableSetGetMap [[.funcref none]] := by
  intro index table hget
  unfold tableSetGetMap at hget
  by_cases hindex : index = 0
  · subst index
    simp only [get?_insert_eq rfl, Option.some.injEq] at hget
    subst table
    rfl
  · rw [get?_insert_ne (fun h => hindex (congrArg TableKey.index h).symm), get?_empty] at hget
    contradiction

private theorem tableSetGetMap_pointsTo [WasmTableGS α] :
    ([∗map] index ↦ table ∈ tableSetGetMap,
      tablePointsTo index table) ⊢
      tablePointsTo ⟨0, 0⟩ [.funcref none] := by
  unfold tableSetGetMap
  rw [(BI.BigSepM.bigSepM_insert (get?_empty (⟨0, 0⟩ : TableKey))).to_eq,
    BI.BigSepM.bigSepM_empty.to_eq, BI.sep_emp.to_eq]

def tableSetGetAdequacyModule : Module :=
  { funcs :=
      [{ body :=
          [ .const 0, .refFunc 1, .tableSet 0,
            .const 0, .tableGet 0, .refIsNull ],
         results := [.i32] },
       { body := [] }]
    tables := [{ min := 1, max := some 1 }] }

def tableSetGetAdequacyConfig : Config Unit :=
  { expr := .running
      ⟨⟨[], [], []⟩,
        [ .const 0, .refFunc 1, .tableSet 0,
          .const 0, .tableGet 0, .refIsNull ],
        1, [], [], []⟩
    store :=
      { runtime := { instances := #[{ module := tableSetGetAdequacyModule, host := {} }], entry := ⟨0⟩ }
        wasm := tableSetGetAdequacyModule.initialStore } }

/-- End-to-end Iris regression for authoritative tables: write a non-null
function reference, read it back, and prove both the returned null-test result
and the reached physical table contents. -/
theorem tableSetGet_store_partiallyMeets :
    PartiallyMeets tableSetGetAdequacyConfig
      (fun values store =>
        values = [.i32 0] ∧
          store.wasm.tables[0]? = some [.funcref (some 1)]) := by
  apply
    wasm_smallStep_heap_globals_segments_tables_runtime_store_partiallyMeets
      (α := Unit)
      (σ := (∅ : WasmHeapMap (Option UInt8)))
      (globalσ := (∅ : WasmGlobalMap Value))
      (dataSegmentσ :=
        (∅ : WasmDataSegmentMap (Option (List UInt8))))
      (tableσ := tableSetGetMap)
      (elementSegmentσ :=
        (∅ : WasmElementSegmentMap (Option (List (Option Nat)))))
  · exact heapAgreesWithMem_empty _
  · exact heapAddressesInBounds_empty _
  · exact globalHeapAgrees_empty _
  · exact dataSegmentHeapAgrees_empty _
  · exact tableSetGetMap_agrees
  · exact elementSegmentHeapAgrees_empty _
  · decide
  · intro gs
    simp only [BI.BigSepM.bigSepM_empty.to_eq]
    simp only [runtimeModuleOwn]
    iintro ⟨_Hbytes, _Hglobals, _Hsegments, Htables, _HelementSegments, _Hruntime, _HinstFrag⟩
    ihave Htable := tableSetGetMap_pointsTo $$ Htables
    simp only [tableSetGetAdequacyConfig, tableSetGetAdequacyModule]
    have hpost : ∀ values : List Value,
        (iprop% ⌜values = [.i32 0]⌝ ∗
          tablePointsTo ⟨0, 0⟩
            (listSetAt [.funcref none] (UInt32.toNat 0)
              (.funcref (some 1)))) ⊢
        (iprop% ∀ (store : MachineStore Unit)
            (_observations : List StepKind),
          stateInterp (GF := WasmHeapGF Unit) store 0 [] 0 -∗
          ⌜values = [.i32 0] ∧
            store.wasm.tables[0]? =
              some [.funcref (some 1)]⌝) := by
      intro values
      iintro ⟨%hvalues, Htable⟩
        %store %_observations Hstate
      simp only [← tablePointsToAt_eq]
      imod stateInterp_table_facts_frame
        store 0 [] 0 0
          (listSetAt [.funcref none] (UInt32.toNat 0)
            (.funcref (some 1))) $$
          [$Hstate $Htable] with
        ⟨Hstate, Htable, %Hphysical⟩
      ipureintro
      exact ⟨hvalues, by simpa [listSetAt] using Hphysical⟩
    iapply wp_mono hpost
    wasm_wp_pures [wp_const]
    wasm_wp_next wp_pureStep _ _ _ (fun _ => Step.refFunc)
    simp only [← tablePointsToAt_eq]
    wasm_wp_next wp_tableSet rfl (by decide) $$ Htable
    iintro Htable
    wasm_wp_pures [wp_const]
    wasm_wp_next wp_tableGet (value := .funcref (some 1))
      rfl (by simp [listSetAt]) $$ Htable
    iintro Htable
    iapply wp_mono (fun _ => BI.sep_comm.mp)
    iapply wp_frame_l
    isplitl [Htable]
    · iexact Htable
    wasm_wp_next wp_refIsNull rfl
    wasm_wp_finish_value
    ipureintro
    rfl

def tableGrowFillAdequacyModule : Module :=
  { funcs :=
      [{ body :=
          [ .tableGrow 0, .const 0, .refFunc 1, .const 3, .tableFill 0,
            .const 0, .tableGet 0, .refIsNull ],
         results := [.i32] },
       { body := [] }]
    tables := [{ min := 1, max := some 3 }] }

def tableGrowFillAdequacyConfig : Config Unit :=
  { expr := .running
      ⟨⟨[], [], [.i32 2, .funcref (some 1)]⟩,
        [ .tableGrow 0, .const 0, .refFunc 1, .const 3, .tableFill 0,
          .const 0, .tableGet 0, .refIsNull ],
        1, [], [], []⟩
    store :=
      { runtime := { instances := #[{ module := tableGrowFillAdequacyModule, host := {} }], entry := ⟨0⟩ }
        wasm := tableGrowFillAdequacyModule.initialStore } }

/-- End-to-end growth regression for authoritative tables. The program grows
the table from one to three entries, fills the complete enlarged range with a
non-null function reference, reads the first entry, and proves the reached
physical table as well as the returned null test. -/
theorem tableGrowFill_store_partiallyMeets :
    PartiallyMeets tableGrowFillAdequacyConfig
      (fun values store =>
        values = [.i32 0] ∧
          store.wasm.tables[0]? =
            some [.funcref (some 1), .funcref (some 1),
              .funcref (some 1)]) := by
  apply
    wasm_smallStep_heap_globals_segments_tables_runtime_store_partiallyMeets
      (α := Unit)
      (σ := (∅ : WasmHeapMap (Option UInt8)))
      (globalσ := (∅ : WasmGlobalMap Value))
      (dataSegmentσ :=
        (∅ : WasmDataSegmentMap (Option (List UInt8))))
      (tableσ := tableSetGetMap)
      (elementSegmentσ :=
        (∅ : WasmElementSegmentMap (Option (List (Option Nat)))))
  · exact heapAgreesWithMem_empty _
  · exact heapAddressesInBounds_empty _
  · exact globalHeapAgrees_empty _
  · exact dataSegmentHeapAgrees_empty _
  · exact tableSetGetMap_agrees
  · exact elementSegmentHeapAgrees_empty _
  · decide
  · intro gs
    simp only [BI.BigSepM.bigSepM_empty.to_eq,
      tableGrowFillAdequacyConfig, RuntimeEnv.currentModule_mk1]
    iintro ⟨_Hbytes, _Hglobals, _Hsegments, Htables, _HelementSegments, HruntimeOwn⟩
    ihave Htable := tableSetGetMap_pointsTo $$ Htables
    have hpost : ∀ values : List Value,
        (iprop% ⌜values = [.i32 0]⌝ ∗
          tablePointsTo ⟨0, 0⟩
            (listWriteAt
              ([.funcref none] ++
                List.replicate (UInt32.toNat 2) (.funcref (some 1)))
              (UInt32.toNat 0)
              (List.replicate (UInt32.toNat 3)
                (.funcref (some 1))))) ⊢
        (iprop% ∀ (store : MachineStore Unit)
            (_observations : List StepKind),
          stateInterp (GF := WasmHeapGF Unit) store 0 [] 0 -∗
          ⌜values = [.i32 0] ∧
            store.wasm.tables[0]? =
              some [.funcref (some 1), .funcref (some 1),
                .funcref (some 1)]⌝) := by
      intro values
      iintro ⟨%hvalues, Htable⟩
        %store %_observations Hstate
      simp only [← tablePointsToAt_eq]
      imod stateInterp_table_facts_frame
        store 0 [] 0 0
          (listWriteAt
            ([.funcref none] ++
              List.replicate (UInt32.toNat 2) (.funcref (some 1)))
            (UInt32.toNat 0)
            (List.replicate (UInt32.toNat 3)
              (.funcref (some 1)))) $$
          [$Hstate $Htable] with
        ⟨Hstate, Htable, %Hphysical⟩
      ipureintro
      exact ⟨hvalues, by
        simpa [listWriteAt] using Hphysical⟩
    simp only [← tablePointsToAt_eq]
    wasm_wp_next wp_tableGrow32 tableGrowFillAdequacyModule ⟨0⟩
      (tableIndex := 0) (table := [.funcref none])
      (delta := 2) (initial := .funcref (some 1)) (by decide) $$
        [$Htable $HruntimeOwn]
    iintro Htable _HruntimeOwn
    simp only [tableGrowFillAdequacyModule]
    iapply wp_mono hpost
    simp only [← tablePointsToAt_eq]
    wasm_wp_pures [wp_const]
    wasm_wp_next wp_pureStep _ _ _ (fun _ => Step.refFunc)
    wasm_wp_pures [wp_const]
    wasm_wp_next wp_tableFill
      (tableIndex := 0) (destination := .i32 0) (length := .i32 3)
      (value := .funcref (some 1))
      (table :=
        [.funcref none] ++
          List.replicate (UInt32.toNat 2) (.funcref (some 1)))
      rfl rfl (by decide) $$ Htable
    iintro Htable
    wasm_wp_pures [wp_const]
    wasm_wp_next wp_tableGet (value := .funcref (some 1))
      rfl (by simp [listWriteAt]) $$ Htable
    iintro Htable
    iapply wp_mono (fun _ => BI.sep_comm.mp)
    iapply wp_frame_l
    isplitl [Htable]
    · iexact Htable
    wasm_wp_next wp_refIsNull rfl
    wasm_wp_finish_value
    ipureintro
    rfl

def tableGrow64FailureAdequacyModule : Module :=
  { funcs :=
      [{ body := [.tableGrow 0, .drop, .tableGrow 0],
         results := [.i64] }]
    tables := [{ min := 1, max := some 3, is64 := true }] }

def tableGrow64FailureAdequacyConfig : Config Unit :=
  { expr := .running
      ⟨⟨[], [],
          [.i64 2, .funcref (some 0), .i64 1, .funcref none]⟩,
        [.tableGrow 0, .drop, .tableGrow 0],
        1, [], [], []⟩
    store :=
      { runtime :=
          { instances := #[{ module := tableGrow64FailureAdequacyModule, host := {} }], entry := ⟨0⟩ }
        wasm := tableGrow64FailureAdequacyModule.initialStore } }

/-- Closed table64 regression covering both growth outcomes. The first grow
extends the table to its declared maximum, the second returns the 64-bit
all-ones failure sentinel, and the authoritative physical table remains at the
successfully grown contents. -/
theorem tableGrow64Failure_store_partiallyMeets :
    PartiallyMeets tableGrow64FailureAdequacyConfig
      (fun values store =>
        values = [.i64 (0xFFFFFFFFFFFFFFFF : UInt64)] ∧
          store.wasm.tables[0]? =
            some [.funcref none, .funcref (some 0),
              .funcref (some 0)]) := by
  apply
    wasm_smallStep_heap_globals_segments_tables_runtime_store_partiallyMeets
      (α := Unit)
      (σ := (∅ : WasmHeapMap (Option UInt8)))
      (globalσ := (∅ : WasmGlobalMap Value))
      (dataSegmentσ :=
        (∅ : WasmDataSegmentMap (Option (List UInt8))))
      (tableσ := tableSetGetMap)
      (elementSegmentσ :=
        (∅ : WasmElementSegmentMap (Option (List (Option Nat)))))
  · exact heapAgreesWithMem_empty _
  · exact heapAddressesInBounds_empty _
  · exact globalHeapAgrees_empty _
  · exact dataSegmentHeapAgrees_empty _
  · exact tableSetGetMap_agrees
  · exact elementSegmentHeapAgrees_empty _
  · decide
  · intro gs
    simp only [BI.BigSepM.bigSepM_empty.to_eq,
      tableGrow64FailureAdequacyConfig, RuntimeEnv.currentModule_mk1]
    iintro ⟨_Hbytes, _Hglobals, _Hsegments, Htables, _HelementSegments, HruntimeOwn⟩
    ihave Htable := tableSetGetMap_pointsTo $$ Htables
    have hpost : ∀ values : List Value,
        (iprop%
          ⌜values = [.i64 (0xFFFFFFFFFFFFFFFF : UInt64)]⌝ ∗
          tablePointsTo ⟨0, 0⟩
            ([.funcref none] ++
              List.replicate (UInt64.toNat 2)
                (.funcref (some 0)))) ⊢
        (iprop% ∀ (store : MachineStore Unit)
            (_observations : List StepKind),
          stateInterp (GF := WasmHeapGF Unit) store 0 [] 0 -∗
          ⌜values = [.i64 (0xFFFFFFFFFFFFFFFF : UInt64)] ∧
            store.wasm.tables[0]? =
              some [.funcref none, .funcref (some 0),
                .funcref (some 0)]⌝) := by
      intro values
      iintro ⟨%hvalues, Htable⟩
        %store %_observations Hstate
      simp only [← tablePointsToAt_eq]
      imod stateInterp_table_facts_frame
        store 0 [] 0 0
          ([.funcref none] ++
            List.replicate (UInt64.toNat 2) (.funcref (some 0))) $$
          [$Hstate $Htable] with
        ⟨Hstate, Htable, %Hphysical⟩
      ipureintro
      exact ⟨hvalues, by simpa using Hphysical⟩
    simp only [← tablePointsToAt_eq]
    wasm_wp_next wp_tableGrow64 tableGrow64FailureAdequacyModule ⟨0⟩
      (tableIndex := 0) (table := [.funcref none])
      (delta := 2) (initial := .funcref (some 0)) (by decide) $$
        [$Htable $HruntimeOwn]
    iintro Htable HruntimeOwn
    wasm_wp_next wp_pureStep _ _ _ (fun _ => Step.drop)
    wasm_wp_next wp_tableGrow64Failure tableGrow64FailureAdequacyModule ⟨0⟩
      (tableIndex := 0)
      (table :=
        [.funcref none] ++
          List.replicate (UInt64.toNat 2) (.funcref (some 0)))
      (delta := 1) (initial := .funcref none) (by decide) $$
        [$Htable $HruntimeOwn]
    iintro Htable _HruntimeOwn
    iapply wp_mono hpost
    simp only [← tablePointsToAt_eq]
    iapply wp_mono (fun _ => BI.sep_comm.mp)
    iapply wp_frame_l
    isplitl [Htable]
    · iexact Htable
    wasm_wp_finish_value
    ipureintro
    rfl

private def tableCopyOverlapMap : WasmTableMap TableInst :=
  insert ∅ (⟨0, 0⟩ : TableKey)
    [.funcref none, .funcref (some 0), .funcref (some 1),
      .funcref (some 2)]

private theorem tableCopyOverlapMap_agrees :
    tableHeapAgrees tableCopyOverlapMap
      [[.funcref none, .funcref (some 0), .funcref (some 1),
        .funcref (some 2)]] := by
  intro index table hget
  unfold tableCopyOverlapMap at hget
  by_cases hindex : index = 0
  · subst index
    simp only [get?_insert_eq rfl, Option.some.injEq] at hget
    subst table
    rfl
  · rw [get?_insert_ne (fun h => hindex (congrArg TableKey.index h).symm), get?_empty] at hget
    contradiction

private theorem tableCopyOverlapMap_pointsTo [WasmTableGS α] :
    ([∗map] index ↦ table ∈ tableCopyOverlapMap,
      tablePointsTo index table) ⊢
      tablePointsTo ⟨0, 0⟩
        [.funcref none, .funcref (some 0), .funcref (some 1),
          .funcref (some 2)] := by
  unfold tableCopyOverlapMap
  rw [(BI.BigSepM.bigSepM_insert (get?_empty (⟨0, 0⟩ : TableKey))).to_eq,
    BI.BigSepM.bigSepM_empty.to_eq, BI.sep_emp.to_eq]

def tableCopyOverlapAdequacyModule : Module :=
  { funcs := [{ body := [] }, { body := [] }, { body := [] }]
    tables := [{ min := 4, max := some 4 }] }

def tableCopyOverlapAdequacyConfig : Config Unit :=
  { expr := .running
      ⟨⟨[], [], [.i32 3, .i32 0, .i32 1]⟩,
        [.tableCopy 0 0], 0, [], [], []⟩
    store :=
      { runtime := { instances := #[{ module := tableCopyOverlapAdequacyModule, host := {} }], entry := ⟨0⟩ }
        wasm :=
          { tableCopyOverlapAdequacyModule.initialStore with
            tables :=
              [[.funcref none, .funcref (some 0),
                .funcref (some 1), .funcref (some 2)]] } } }

/-- Closed overlapping `table.copy` regression. Copying entries `[0, 3)` to
offset one must snapshot the old source range rather than cascading writes. -/
theorem tableCopyOverlap_store_partiallyMeets :
    PartiallyMeets tableCopyOverlapAdequacyConfig
      (fun values store =>
        values = [] ∧
          store.wasm.tables[0]? =
            some [.funcref none, .funcref none, .funcref (some 0),
              .funcref (some 1)]) := by
  apply
    wasm_smallStep_heap_globals_segments_tables_runtime_store_partiallyMeets
      (α := Unit)
      (σ := (∅ : WasmHeapMap (Option UInt8)))
      (globalσ := (∅ : WasmGlobalMap Value))
      (dataSegmentσ :=
        (∅ : WasmDataSegmentMap (Option (List UInt8))))
      (tableσ := tableCopyOverlapMap)
      (elementSegmentσ :=
        (∅ : WasmElementSegmentMap (Option (List (Option Nat)))))
  · exact heapAgreesWithMem_empty _
  · exact heapAddressesInBounds_empty _
  · exact globalHeapAgrees_empty _
  · exact dataSegmentHeapAgrees_empty _
  · exact tableCopyOverlapMap_agrees
  · exact elementSegmentHeapAgrees_empty _
  · decide
  · intro gs
    simp only [BI.BigSepM.bigSepM_empty.to_eq,
      tableCopyOverlapAdequacyConfig]
    simp only [runtimeModuleOwn]
    iintro ⟨_Hbytes, _Hglobals, _Hsegments, Htables, _HelementSegments, _Hruntime, _HinstFrag⟩
    ihave Htable := tableCopyOverlapMap_pointsTo $$ Htables
    have hpost : ∀ values : List Value,
        (iprop% ⌜values = []⌝ ∗
          tablePointsTo ⟨0, 0⟩
            (listWriteAt
              [.funcref none, .funcref (some 0),
                .funcref (some 1), .funcref (some 2)]
              (UInt32.toNat 1)
              (([.funcref none, .funcref (some 0),
                  .funcref (some 1), .funcref (some 2)].drop
                    (UInt32.toNat 0)).take (UInt32.toNat 3)))) ⊢
        (iprop% ∀ (store : MachineStore Unit)
            (_observations : List StepKind),
          stateInterp (GF := WasmHeapGF Unit) store 0 [] 0 -∗
          ⌜values = [] ∧
            store.wasm.tables[0]? =
              some [.funcref none, .funcref none, .funcref (some 0),
                .funcref (some 1)]⌝) := by
      intro values
      iintro ⟨%hvalues, Htable⟩
        %store %_observations Hstate
      simp only [← tablePointsToAt_eq]
      imod stateInterp_table_facts_frame
        store 0 [] 0 0
          (listWriteAt
            [.funcref none, .funcref (some 0),
              .funcref (some 1), .funcref (some 2)]
            (UInt32.toNat 1)
            (([.funcref none, .funcref (some 0),
                .funcref (some 1), .funcref (some 2)].drop
                  (UInt32.toNat 0)).take (UInt32.toNat 3))) $$
          [$Hstate $Htable] with
        ⟨Hstate, Htable, %Hphysical⟩
      ipureintro
      exact ⟨hvalues, by simpa [listWriteAt] using Hphysical⟩
    iapply wp_mono hpost
    simp only [← tablePointsToAt_eq]
    wasm_wp_next wp_tableCopySame
      (tableIndex := 0)
      (table :=
        [.funcref none, .funcref (some 0), .funcref (some 1),
          .funcref (some 2)])
      (destination := .i32 1) (source := .i32 0) (length := .i32 3)
      rfl rfl rfl (by decide) (by decide) $$ Htable
    iintro Htable
    iapply wp_mono (fun _ => BI.sep_comm.mp)
    iapply wp_frame_l
    isplitl [Htable]
    · iexact Htable
    wasm_wp_finish_value
    ipureintro
    rfl

private def tableCopyDistinctMap : WasmTableMap TableInst :=
  insert (insert ∅ (⟨0, 0⟩ : TableKey) [.funcref none, .funcref none, .funcref none])
    (⟨0, 1⟩ : TableKey) [.funcref (some 0), .funcref (some 1), .funcref (some 2)]

private theorem tableCopyDistinctMap_agrees :
    tableHeapAgrees tableCopyDistinctMap
      [[.funcref none, .funcref none, .funcref none],
       [.funcref (some 0), .funcref (some 1), .funcref (some 2)]] := by
  intro index table hget
  unfold tableCopyDistinctMap at hget
  by_cases hindex0 : index = 0
  · subst index
    simp only [get?_insert_ne (show (⟨0, 1⟩ : TableKey) ≠ ⟨0, 0⟩ by decide),
      get?_insert_eq rfl,
      Option.some.injEq] at hget
    subst table
    rfl
  by_cases hindex1 : index = 1
  · subst index
    simp only [get?_insert_eq rfl, Option.some.injEq] at hget
    subst table
    rfl
  rw [get?_insert_ne (fun h => hindex1 (congrArg TableKey.index h).symm),
    get?_insert_ne (fun h => hindex0 (congrArg TableKey.index h).symm), get?_empty] at hget
  contradiction

private theorem tableCopyDistinctMap_pointsTo [WasmTableGS α] :
    ([∗map] index ↦ table ∈ tableCopyDistinctMap,
      tablePointsTo index table) ⊢
      tablePointsTo ⟨0, 0⟩
          [.funcref none, .funcref none, .funcref none] ∗
      tablePointsTo ⟨0, 1⟩
          [.funcref (some 0), .funcref (some 1),
            .funcref (some 2)] := by
  unfold tableCopyDistinctMap
  have hmissing :
      get?
        (insert (∅ : WasmTableMap TableInst) (⟨0, 0⟩ : TableKey)
          ([.funcref none, .funcref none, .funcref none] : TableInst))
        (⟨0, 1⟩ : TableKey) = none := by
    rw [get?_insert_ne (show (⟨0, 0⟩ : TableKey) ≠ ⟨0, 1⟩ by decide), get?_empty]
  rw [(BI.BigSepM.bigSepM_insert hmissing).to_eq,
    (BI.BigSepM.bigSepM_insert (get?_empty (⟨0, 0⟩ : TableKey))).to_eq,
    BI.BigSepM.bigSepM_empty.to_eq, BI.sep_emp.to_eq]
  iintro ⟨Hsource, Hdestination⟩
  isplitl [Hdestination]
  · iexact Hdestination
  · iexact Hsource

def tableCopyDistinctAdequacyModule : Module :=
  { funcs := [{ body := [] }, { body := [] }, { body := [] }]
    tables :=
      [{ min := 3, max := some 3 }, { min := 3, max := some 3 }] }

def tableCopyDistinctAdequacyConfig : Config Unit :=
  { expr := .running
      ⟨⟨[], [], [.i32 2, .i32 1, .i32 0]⟩,
        [.tableCopy 0 1], 0, [], [], []⟩
    store :=
      { runtime := { instances := #[{ module := tableCopyDistinctAdequacyModule, host := {} }], entry := ⟨0⟩ }
        wasm :=
          { tableCopyDistinctAdequacyModule.initialStore with
            tables :=
              [[.funcref none, .funcref none, .funcref none],
               [.funcref (some 0), .funcref (some 1),
                 .funcref (some 2)]] } } }

/-- Closed cross-table copy regression. It proves the destination receives the
selected source slice while the physically separate source table is preserved
exactly. -/
theorem tableCopyDistinct_store_partiallyMeets :
    PartiallyMeets tableCopyDistinctAdequacyConfig
      (fun values store =>
        values = [] ∧
          store.wasm.tables[0]? =
            some [.funcref (some 1), .funcref (some 2), .funcref none] ∧
          store.wasm.tables[1]? =
            some [.funcref (some 0), .funcref (some 1),
              .funcref (some 2)]) := by
  apply
    wasm_smallStep_heap_globals_segments_tables_runtime_store_partiallyMeets
      (α := Unit)
      (σ := (∅ : WasmHeapMap (Option UInt8)))
      (globalσ := (∅ : WasmGlobalMap Value))
      (dataSegmentσ :=
        (∅ : WasmDataSegmentMap (Option (List UInt8))))
      (tableσ := tableCopyDistinctMap)
      (elementSegmentσ :=
        (∅ : WasmElementSegmentMap (Option (List (Option Nat)))))
  · exact heapAgreesWithMem_empty _
  · exact heapAddressesInBounds_empty _
  · exact globalHeapAgrees_empty _
  · exact dataSegmentHeapAgrees_empty _
  · exact tableCopyDistinctMap_agrees
  · exact elementSegmentHeapAgrees_empty _
  · decide
  · intro gs
    simp only [BI.BigSepM.bigSepM_empty.to_eq,
      tableCopyDistinctAdequacyConfig]
    simp only [runtimeModuleOwn]
    iintro ⟨_Hbytes, _Hglobals, _Hsegments, Htables, _HelementSegments, _Hruntime, _HinstFrag⟩
    ihave HtablePair := tableCopyDistinctMap_pointsTo $$ Htables
    icases HtablePair with ⟨Hdestination, Hsource⟩
    have hpost : ∀ values : List Value,
        (iprop% ⌜values = []⌝ ∗
          tablePointsTo ⟨0, 0⟩
            (listWriteAt
              [.funcref none, .funcref none, .funcref none]
              (UInt32.toNat 0)
              (([.funcref (some 0), .funcref (some 1),
                  .funcref (some 2)].drop (UInt32.toNat 1)).take
                    (UInt32.toNat 2))) ∗
          tablePointsTo ⟨0, 1⟩
            [.funcref (some 0), .funcref (some 1),
              .funcref (some 2)]) ⊢
        (iprop% ∀ (store : MachineStore Unit)
            (_observations : List StepKind),
          stateInterp (GF := WasmHeapGF Unit) store 0 [] 0 -∗
          ⌜values = [] ∧
            store.wasm.tables[0]? =
              some [.funcref (some 1), .funcref (some 2),
                .funcref none] ∧
            store.wasm.tables[1]? =
              some [.funcref (some 0), .funcref (some 1),
                .funcref (some 2)]⌝) := by
      intro values
      iintro ⟨%hvalues, Hdestination, Hsource⟩
        %store %_observations Hstate
      simp only [← tablePointsToAt_eq]
      imod stateInterp_table_facts_frame
        store 0 [] 0 0
          (listWriteAt
            [.funcref none, .funcref none, .funcref none]
            (UInt32.toNat 0)
            (([.funcref (some 0), .funcref (some 1),
                .funcref (some 2)].drop (UInt32.toNat 1)).take
                  (UInt32.toNat 2))) $$
          [$Hstate $Hdestination] with
        ⟨Hstate, Hdestination, %HdestinationPhysical⟩
      imod stateInterp_table_facts_frame
        store 0 [] 0 1
          [.funcref (some 0), .funcref (some 1),
            .funcref (some 2)] $$ [$Hstate $Hsource] with
        ⟨Hstate, Hsource, %HsourcePhysical⟩
      ipureintro
      exact ⟨hvalues,
        by simpa [listWriteAt] using HdestinationPhysical,
        HsourcePhysical⟩
    have hframe : ∀ values : List Value,
        (iprop%
          (tablePointsTo ⟨0, 0⟩
              (listWriteAt
                [.funcref none, .funcref none, .funcref none]
                (UInt32.toNat 0)
                (([.funcref (some 0), .funcref (some 1),
                    .funcref (some 2)].drop (UInt32.toNat 1)).take
                      (UInt32.toNat 2))) ∗
            tablePointsTo ⟨0, 1⟩
              [.funcref (some 0), .funcref (some 1),
                .funcref (some 2)]) ∗
          ⌜values = []⌝) ⊢
        (iprop% ⌜values = []⌝ ∗
          (tablePointsTo ⟨0, 0⟩
              (listWriteAt
                [.funcref none, .funcref none, .funcref none]
                (UInt32.toNat 0)
                (([.funcref (some 0), .funcref (some 1),
                    .funcref (some 2)].drop (UInt32.toNat 1)).take
                      (UInt32.toNat 2))) ∗
            tablePointsTo ⟨0, 1⟩
              [.funcref (some 0), .funcref (some 1),
                .funcref (some 2)])) := by
      intro values
      iintro ⟨⟨Hdestination, Hsource⟩, %hvalues⟩
      isplitl []
      · ipureintro
        exact hvalues
      · isplitl [Hdestination]
        · iexact Hdestination
        · iexact Hsource
    iapply wp_mono hpost
    simp only [← tablePointsToAt_eq]
    icombine Hdestination Hsource as HtablePair
    wasm_wp_next wp_tableCopyDistinct
      (destinationTableIndex := 0) (sourceTableIndex := 1)
      (destinationTable :=
        [.funcref none, .funcref none, .funcref none])
      (sourceTable :=
        [.funcref (some 0), .funcref (some 1), .funcref (some 2)])
      (destination := .i32 0) (source := .i32 1) (length := .i32 2)
      rfl rfl rfl (by decide) (by decide) $$ HtablePair
    iintro Hdestination Hsource
    simp only [tablePointsToAt_eq]
    iapply wp_mono hframe
    iapply wp_frame_l
    isplitl [Hdestination Hsource]
    · isplitl [Hdestination]
      · iexact Hdestination
      · iexact Hsource
    wasm_wp_finish_value
    ipureintro
    rfl

private def tableInitDropTableMap : WasmTableMap TableInst :=
  insert ∅ (⟨0, 0⟩ : TableKey)
    [.funcref none, .funcref none, .funcref none, .funcref none]

private def tableInitDropElementMap :
    WasmElementSegmentMap (Option (List (Option Nat))) :=
  insert ∅ (⟨0, 0⟩ : ElementSegmentKey) (some [some 0, none, some 0])

private theorem tableInitDropTableMap_agrees :
    tableHeapAgrees tableInitDropTableMap
      [[.funcref none, .funcref none, .funcref none,
        .funcref none]] := by
  intro index table hget
  unfold tableInitDropTableMap at hget
  by_cases hindex : index = 0
  · subst index
    simp only [get?_insert_eq rfl, Option.some.injEq] at hget
    subst table
    rfl
  · rw [get?_insert_ne (fun h => hindex (congrArg TableKey.index h).symm), get?_empty] at hget
    contradiction

private theorem tableInitDropElementMap_agrees :
    elementSegmentHeapAgrees tableInitDropElementMap
      [some [some 0, none, some 0]] := by
  intro index value hget
  unfold tableInitDropElementMap at hget
  by_cases hindex : index = 0
  · subst index
    simp only [get?_insert_eq rfl, Option.some.injEq] at hget
    subst value
    rfl
  · rw [get?_insert_ne (fun h => hindex (congrArg ElementSegmentKey.index h).symm), get?_empty] at hget
    contradiction

private theorem tableInitDropTableMap_pointsTo [WasmTableGS α] :
    ([∗map] index ↦ table ∈ tableInitDropTableMap,
      tablePointsTo index table) ⊢
      tablePointsTo ⟨0, 0⟩
        [.funcref none, .funcref none, .funcref none,
          .funcref none] := by
  unfold tableInitDropTableMap
  rw [(BI.BigSepM.bigSepM_insert (get?_empty (⟨0, 0⟩ : TableKey))).to_eq,
    BI.BigSepM.bigSepM_empty.to_eq, BI.sep_emp.to_eq]

private theorem tableInitDropElementMap_pointsTo [WasmElementSegmentGS α] :
    ([∗map] index ↦ value ∈ tableInitDropElementMap,
      elementSegmentPointsTo index value) ⊢
      elementSegmentPointsTo ⟨0, 0⟩ (some [some 0, none, some 0]) := by
  unfold tableInitDropElementMap
  rw [(BI.BigSepM.bigSepM_insert (get?_empty (⟨0, 0⟩ : ElementSegmentKey))).to_eq,
    BI.BigSepM.bigSepM_empty.to_eq, BI.sep_emp.to_eq]

def tableInitDropAdequacyModule : Module :=
  { funcs := [{ body := [] }]
    tables := [{ min := 4, max := some 4 }]
    elements := [{ funcs := [some 0, none, some 0] }] }

def tableInitDropAdequacyConfig : Config Unit :=
  { expr := .running
      ⟨⟨[], [], [.i32 3, .i32 0, .i32 1]⟩,
        [.tableInit 0 0, .elemDrop 0], 0, [], [], []⟩
    store :=
      { runtime := { instances := #[{ module := tableInitDropAdequacyModule, host := {} }], entry := ⟨0⟩ }
        wasm := tableInitDropAdequacyModule.initialStore } }

/-- Closed physical-state regression for element segments. `table.init`
copies the live instantiated values into the table; `elem.drop` then changes
the segment to its authoritative dropped state without changing that table. -/
theorem tableInitDrop_store_partiallyMeets :
    PartiallyMeets tableInitDropAdequacyConfig
      (fun values store =>
        values = [] ∧
          store.wasm.tables[0]? =
            some [.funcref none, .funcref (some 0), .funcref none,
              .funcref (some 0)] ∧
          store.wasm.elementSegments[0]? = some none) := by
  apply
    wasm_smallStep_heap_globals_segments_tables_runtime_store_partiallyMeets
      (α := Unit)
      (σ := (∅ : WasmHeapMap (Option UInt8)))
      (globalσ := (∅ : WasmGlobalMap Value))
      (dataSegmentσ :=
        (∅ : WasmDataSegmentMap (Option (List UInt8))))
      (tableσ := tableInitDropTableMap)
      (elementSegmentσ := tableInitDropElementMap)
  · exact heapAgreesWithMem_empty _
  · exact heapAddressesInBounds_empty _
  · exact globalHeapAgrees_empty _
  · exact dataSegmentHeapAgrees_empty _
  · exact tableInitDropTableMap_agrees
  · exact tableInitDropElementMap_agrees
  · decide
  · intro gs
    simp only [BI.BigSepM.bigSepM_empty.to_eq,
      tableInitDropAdequacyConfig, RuntimeEnv.currentModule_mk1]
    simp only [runtimeModuleOwn]
    iintro
      ⟨_Hbytes, _Hglobals, _HdataSegments, Htables,
        HelementSegments, Hruntime, HinstFrag⟩
    iintuitionistic Hruntime
    ihave Htable := tableInitDropTableMap_pointsTo $$ Htables
    ihave Helement :=
      tableInitDropElementMap_pointsTo $$ HelementSegments
    have hpost : ∀ values : List Value,
        (iprop% ⌜values = []⌝ ∗
          tablePointsTo ⟨0, 0⟩
            (listWriteAt
              [.funcref none, .funcref none, .funcref none,
                .funcref none]
              (UInt32.toNat 1)
              (((tableInitDropAdequacyModule.elements[0]?.map
                  ElementSegment.values).getD []).drop
                    (UInt32.toNat 0) |>.take (UInt32.toNat 3))) ∗
          elementSegmentPointsTo ⟨0, 0⟩ none) ⊢
        (iprop% ∀ (store : MachineStore Unit)
            (_observations : List StepKind),
          stateInterp (GF := WasmHeapGF Unit) store 0 [] 0 -∗
          ⌜values = [] ∧
            store.wasm.tables[0]? =
              some [.funcref none, .funcref (some 0), .funcref none,
                .funcref (some 0)] ∧
            store.wasm.elementSegments[0]? = some none⌝) := by
      intro values
      iintro ⟨%hvalues, Htable, Helement⟩
        %store %_observations Hstate
      simp only [← tablePointsToAt_eq]
      imod stateInterp_table_facts_frame
        store 0 [] 0 0
          (listWriteAt
            [.funcref none, .funcref none, .funcref none,
              .funcref none]
            (UInt32.toNat 1)
            (((tableInitDropAdequacyModule.elements[0]?.map
                ElementSegment.values).getD []).drop
                  (UInt32.toNat 0) |>.take (UInt32.toNat 3))) $$
          [$Hstate $Htable] with
        ⟨Hstate, Htable, %HtablePhysical⟩
      simp only [← elementSegmentPointsToAt_eq]
      ihave_pure HelementPhysical :
          ⌜store.wasm.elementSegments[0]? = some none⌝ using
        stateInterp_elementSegment_facts store 0 [] 0 0 none $$ [Hstate Helement]
      ipureintro
      exact ⟨hvalues,
        by simpa [tableInitDropAdequacyModule,
            ElementSegment.values, ElementSegment.plainValues, listWriteAt]
          using HtablePhysical,
        HelementPhysical⟩
    iapply wp_mono hpost
    simp only [← tablePointsToAt_eq, ← elementSegmentPointsToAt_eq]
    ihave Hresources :
        tablePointsToAt 0 0
            [.funcref none, .funcref none, .funcref none,
              .funcref none] ∗
          elementSegmentPointsToAt 0 0 (some [some 0, none, some 0]) ∗
          runtimeModuleOwn ⟨0⟩ tableInitDropAdequacyModule $$
        [Htable Helement Hruntime HinstFrag]
    · isplitl [Htable]
      · iexact Htable
      · isplitl [Helement]
        · iexact Helement
        · unfold runtimeModuleOwn
          isplitl [Hruntime]
          · unfold runtimeModuleElem; iexact Hruntime
          · unfold currentInstanceOwnN; iexact HinstFrag
    wasm_wp_next wp_tableInitLive tableInitDropAdequacyModule ⟨0⟩
      (tableIndex := 0) (elementIndex := 0)
      (table :=
        [.funcref none, .funcref none, .funcref none, .funcref none])
      (entries := [some 0, none, some 0])
      (destination := .i32 1) (source := 0) (length := 3)
      rfl (by decide) (by decide) $$ Hresources
    iintro Htable Helement Hruntime
    wasm_wp_next wp_elemDrop $$ Helement
    iintro Helement
    iapply wp_mono (fun _ => sep_pair_pure_rotate _ _ _)
    iapply wp_frame_l
    isplitl [Htable Helement]
    · isplitl [Htable]
      · iexact Htable
      · iexact Helement
    wasm_wp_finish_value
    ipureintro
    rfl

/-! ## Parametric total-correctness examples

Three small modules exercised end to end: a signed branch (pure control flow),
a bulk fill followed by a load (memory), and a `try_table` that catches a
thrown exception (tags).  Each is stated for *symbolic* inputs, and each is
paired with a `.wat` source whose decoded module is checked to agree with the
hand-written one on a spread of concrete inputs. -/

def signedBranchModule : Module :=
  { funcs := [{ params := [.i32, .i32],
                body := [.block 0 0 [.localGet 0, .localGet 1, .geS, .br_if 0, .const 0, .ret],
                          .const 1, .ret]
                results := [.i32] }] }

def signedBranchConfig (a b : UInt32) : Config Unit :=
  { expr := .running ⟨⟨[.i32 a, .i32 b], [], []⟩,
      signedBranchModule.funcs[0]!.body, 1, [], [], []⟩
    store :=
      { runtime := { instances := #[{ module := signedBranchModule, host := {} }], entry := ⟨0⟩ }
        wasm := signedBranchModule.initialStore } }

/-- `i32.ge_s` on the two parameters: returns 1 if `a ≥ b` as signed 32-bit
integers, 0 otherwise. -/
theorem signedBranch_terminatesWith (a b : UInt32) :
    TerminatesWith (signedBranchConfig a b)
      (fun values _store => values = [.i32 (if a.toInt32 ≥ b.toInt32 then 1 else 0)]) := by
  apply wasm_smallStep_terminates (signedBranchConfig a b)
    (fun values => values = [.i32 (if a.toInt32 ≥ b.toInt32 then 1 else 0)])
  intro hlc gs
  simp only [signedBranchConfig,
    show signedBranchModule.funcs[0]!.body =
        [.block 0 0 [.localGet 0, .localGet 1, .geS, .br_if 0, .const 0, .ret],
          .const 1, .ret] from rfl]
  wasm_twp_pures [twp_block twp_localGet twp_localGet]
  by_cases h : a.toInt32 ≥ b.toInt32
  · iapply twp_geS (result := 1) (by simp [h])
    iapply twp_brIf (condition := 1) (by decide) rfl
    wasm_twp_pures [twp_const]
    wasm_twp_terminal_value twp_returnFromFunction
    ipureintro
    simp [h]
  · iapply twp_geS (result := 0) (by simp [h])
    wasm_twp_pures [twp_brIfZero twp_const]
    wasm_twp_terminal_value twp_returnFromFunction
    ipureintro
    simp [h]

/-- Splat conversion for the fill-then-read example: after `memory.fill`
writes `b` into four bytes at address 0, the byte range is the little-endian
layout of the 32-bit word with all four bytes equal to `b`. -/
private theorem splat_bytes_as_u32 [WasmHeapGS Unit] (b : UInt8) :
    pointsToBytes (α := Unit) 0 0 (List.replicate 4 b) ⊢
      pointsTo_u32 0 0
        (b.toUInt32 ||| (b.toUInt32 <<< 8) ||| (b.toUInt32 <<< 16) ||| (b.toUInt32 <<< 24)) := by
  have hb0 : u32Byte (b.toUInt32 ||| (b.toUInt32 <<< 8) |||
      (b.toUInt32 <<< 16) ||| (b.toUInt32 <<< 24)) 0 = b := by
    simp only [u32Byte]; bv_decide
  have hb1 : u32Byte (b.toUInt32 ||| (b.toUInt32 <<< 8) |||
      (b.toUInt32 <<< 16) ||| (b.toUInt32 <<< 24)) 1 = b := by
    simp only [u32Byte]; bv_decide
  have hb2 : u32Byte (b.toUInt32 ||| (b.toUInt32 <<< 8) |||
      (b.toUInt32 <<< 16) ||| (b.toUInt32 <<< 24)) 2 = b := by
    simp only [u32Byte]; bv_decide
  have hb3 : u32Byte (b.toUInt32 ||| (b.toUInt32 <<< 8) |||
      (b.toUInt32 <<< 16) ||| (b.toUInt32 <<< 24)) 3 = b := by
    simp only [u32Byte]; bv_decide
  have hl : List.replicate 4 b =
      [u32Byte (b.toUInt32 ||| (b.toUInt32 <<< 8) |||
          (b.toUInt32 <<< 16) ||| (b.toUInt32 <<< 24)) 0,
       u32Byte (b.toUInt32 ||| (b.toUInt32 <<< 8) |||
          (b.toUInt32 <<< 16) ||| (b.toUInt32 <<< 24)) 1,
       u32Byte (b.toUInt32 ||| (b.toUInt32 <<< 8) |||
          (b.toUInt32 <<< 16) ||| (b.toUInt32 <<< 24)) 2,
       u32Byte (b.toUInt32 ||| (b.toUInt32 <<< 8) |||
          (b.toUInt32 <<< 16) ||| (b.toUInt32 <<< 24)) 3] := by
    rw [hb0, hb1, hb2, hb3]
    rfl
  rw [hl]
  exact (pointsTo_u32_as_bytes 0 0 _).mpr

def fillThenReadModule : Module :=
  { funcs := [{ params := [.i32],
                body := [.const 0, .localGet 0, .const 4, .memoryFill,
                         .const 0, .load32 0],
                results := [.i32] }]
    memory := some { pagesMin := 1 } }

def fillThenReadConfig (val : UInt32) : Config Unit :=
  let initial := fillThenReadModule.initialStore
  { expr := .running ⟨⟨[.i32 val], [], []⟩,
      fillThenReadModule.funcs[0]!.body, 1, [], [], []⟩
    store :=
      { runtime := { instances := #[{ module := fillThenReadModule, host := {} }], entry := ⟨0⟩ }
        wasm := { initial with mem := initial.mem.write32 0 0 } } }

private def fillThenReadInitialHeap : WasmHeapMap (Option UInt8) :=
  store32Heap ∅ 0 0 0

/-- The store the example starts from before the pre-written zero word. -/
private def fillThenReadBaseStore : MachineStore Unit :=
  { runtime := { instances := #[{ module := fillThenReadModule, host := {} }], entry := ⟨0⟩ }
    wasm := fillThenReadModule.initialStore }

private theorem fillThenRead_resolve (val : UInt32) :
    storeResolve (fillThenReadConfig val).store =
      (fun id : Nat =>
        if id = 0 then some ((fillThenReadModule.initialStore : Store Unit).mem.write32 0 0)
        else storeResolve fillThenReadBaseStore id) := by
  funext id
  by_cases h : id = 0 <;>
    simp [h, storeResolve, fillThenReadConfig, fillThenReadBaseStore]

private theorem fillThenReadBase_resolve_zero :
    storeResolve fillThenReadBaseStore 0 =
      some (fillThenReadModule.initialStore : Store Unit).mem := by
  simp [storeResolve, fillThenReadBaseStore]

private theorem fillThenReadInitialHeap_agrees (val : UInt32) :
    heapAgreesWithMem fillThenReadInitialHeap
      (storeResolve (fillThenReadConfig val).store) := by
  rw [fillThenRead_resolve val]
  exact store32_sound ∅ (storeResolve fillThenReadBaseStore) 0
    (fillThenReadModule.initialStore : Store Unit).mem 0 0 fillThenReadBase_resolve_zero
    rfl rfl rfl (heapAgreesWithMem_empty _)

private theorem fillThenReadInitialHeap_inBounds (val : UInt32)
    (hpages : 1 ≤ (fillThenReadModule.initialStore : Store Unit).mem.pages) :
    heapAddressesInBounds fillThenReadInitialHeap
      (storeResolve (fillThenReadConfig val).store) := by
  rw [fillThenRead_resolve val]
  refine store32_inBounds ∅ (storeResolve fillThenReadBaseStore) 0
    (fillThenReadModule.initialStore : Store Unit).mem 0 0 fillThenReadBase_resolve_zero
    rfl rfl rfl (heapAddressesInBounds_empty _) ?_
  simp only [UInt32.toNat_zero, Nat.zero_add]
  have : 65536 ≤ (fillThenReadModule.initialStore : Store Unit).mem.pages * 65536 :=
    Nat.mul_le_mul_right 65536 hpages
  omega

private theorem fillThenReadInitialHeap_pointsTo [WasmHeapGS Unit] :
    ([∗map] address ↦ value ∈ fillThenReadInitialHeap,
      pointsTo (GF := WasmHeapGF Unit) (H := WasmHeapMap)
        address (DFrac.own 1) value) ⊢
      pointsTo_u32 0 0 0 := by
  unfold fillThenReadInitialHeap
  iintro Hheap
  ihave H0 := store32Heap_pointsTo
    (∅ : WasmHeapMap (Option UInt8)) 0 0 0
    (by simp [get?_empty]) (by simp [get?_empty])
    (by simp [get?_empty]) (by simp [get?_empty])
    (by decide) (by decide) (by decide) $$ Hheap
  icases H0 with ⟨H0, _⟩
  iexact H0

/-- `memory.fill` of four bytes with the low byte of the parameter, then
`i32.load` of the filled word: the result is the parameter's low byte splatted
across all four byte positions. -/
theorem fillThenRead_terminatesWith (val : UInt32) :
    TerminatesWith (fillThenReadConfig val)
      (fun values _store =>
        values = [.i32 (val.toUInt8.toUInt32 ||| (val.toUInt8.toUInt32 <<< 8) |||
                        (val.toUInt8.toUInt32 <<< 16) ||| (val.toUInt8.toUInt32 <<< 24))]) := by
  apply wasm_smallStep_heap_terminates (fillThenReadConfig val)
    fillThenReadInitialHeap
    (fun values =>
      values = [.i32 (val.toUInt8.toUInt32 ||| (val.toUInt8.toUInt32 <<< 8) |||
                      (val.toUInt8.toUInt32 <<< 16) ||| (val.toUInt8.toUInt32 <<< 24))])
  · apply fillThenReadInitialHeap_agrees
  · apply fillThenReadInitialHeap_inBounds
    native_decide
  · simp [fillThenReadConfig]
  · intro hlc gs
    simp only [fillThenReadConfig,
      show fillThenReadModule.funcs[0]!.body =
          [.const 0, .localGet 0, .const 4, .memoryFill, .const 0, .load32 0] from rfl]
    iintro Hbytes
    ihave H0 := fillThenReadInitialHeap_pointsTo $$ Hbytes
    ihave Hb := (pointsTo_u32_as_bytes 0 0 0).mp $$ H0
    wasm_twp_pures [twp_const twp_localGet twp_const]
    iapply twp_memoryFill32
        [u32Byte 0 0, u32Byte 0 1, u32Byte 0 2, u32Byte 0 3]
        rfl (by decide) (by decide) $$ Hb
    iintro Hb
    ihave H0 := splat_bytes_as_u32 val.toUInt8 $$ Hb
    wasm_twp_pures [twp_const]
    iapply twp_load32_addr _ rfl rfl rfl $$ H0
    iintro H0
    iapply twp_finish
        (locals := { params := [.i32 val], locals := [], values := [] })
        (values := [.i32 (val.toUInt8.toUInt32 ||| (val.toUInt8.toUInt32 <<< 8) |||
                          (val.toUInt8.toUInt32 <<< 16) ||| (val.toUInt8.toUInt32 <<< 24))])
        (arity := 1) (remainder := [])
    iapply twp.value rfl
    ipureintro
    rfl

def exceptionLifecycleModule : Module :=
  { tags := [{ params := [.i32] }]
    funcs := [{ params := [.i32],
                body := [.tryTable 0 1 [.catch 0 0] [.localGet 0, .throwI 0],
                          .const 99]
                results := [.i32] }] }

def exceptionLifecycleConfig (arg : UInt32) : Config Unit :=
  { expr := .running
      ⟨⟨[.i32 arg], [], []⟩, exceptionLifecycleModule.funcs[0]!.body, 1, [], [], []⟩
    store :=
      { runtime :=
          { instances := #[{ module := exceptionLifecycleModule, host := {} }], entry := ⟨0⟩ }
        wasm := exceptionLifecycleModule.initialStore } }

/-- Tag 0 is the first entry of the entry module's tag table, so the
interpreter's tag canonicalisation is the identity on it. -/
private theorem exceptionLifecycle_tagCanonical :
    TagIndexCanonical
      (exceptionLifecycleModule.initialStore : Store Unit).tagIds 0 :=
  ⟨0, by decide, by decide⟩

/-- `try_table` with a `catch` clause catches a `throw` of the same tag and
receives the thrown value, parametric in the thrown argument. -/
theorem exceptionLifecycle_terminatesWith (arg : UInt32) :
    TerminatesWith (exceptionLifecycleConfig arg)
      (fun values _store => values = [.i32 arg]) := by
  apply wasm_smallStep_runtime_tags_terminates (exceptionLifecycleConfig arg)
    (fun values => values = [.i32 arg])
  · simp [exceptionLifecycleConfig]
  intro hlc gs
  simp only [exceptionLifecycleConfig, RuntimeEnv.currentModule_mk1,
    show exceptionLifecycleModule.funcs[0]!.body =
        [.tryTable 0 1 [.catch 0 0] [.localGet 0, .throwI 0], .const 99] from rfl]
  iintro ⟨Hruntime, Htags⟩
  iapply twp_tryTable
  wasm_twp_pures [twp_localGet]
  iapply (twp_throwI exceptionLifecycleModule ⟨0⟩ 0
    (tagType := { params := [.i32] }) (htag := rfl)
    (tagIds := (exceptionLifecycleModule.initialStore : Store Unit).tagIds)
    (hcanonical := exceptionLifecycle_tagCanonical)
    (hargs := by simp)) $$ Hruntime Htags
  iintro Hruntime'
  iapply twp_catchException
    (clause := .catch 0 0) (targetCode := []) (targetControl := [])
    (targetValues := [.i32 arg])
    (hclause := Or.inl ⟨0, 0, rfl⟩)
    (htarget := fun _ => rfl) (hthrow := rfl) (hmatch := by decide)
  wasm_twp_terminal_value twp_finish
  ipureintro
  rfl

/-! ### Decoder agreement

Each example's `.wat` source decodes to a module that behaves identically to
the hand-written one on a spread of concrete inputs. -/

private def signedBranchWat : String := include_str "signed_branch.wat"

private def signedBranchModuleDecoded : Module :=
  match Wasm.Decoder.Wat.decode signedBranchWat with
  | .ok m => m
  | .error _ => default

private def runSignedBranch (fuel : Nat) (m : Module) (a b : UInt32) : Option (List Value) :=
  match initConfig { module := m, host := (default : HostEnv Unit) } 0
      m.initialStore [.i32 a, .i32 b] with
  | .error _ => none
  | .ok config => (runSteps fuel config).result.values?

/-- Exercises both branch outcomes across varied inputs. -/
theorem signedBranch_decoded_agrees :
    runSignedBranch 10 signedBranchModule 5 3 = runSignedBranch 10 signedBranchModuleDecoded 5 3 ∧
    runSignedBranch 15 signedBranchModule 0 1 = runSignedBranch 15 signedBranchModuleDecoded 0 1 ∧
    runSignedBranch 20 signedBranchModule 100 100 =
      runSignedBranch 20 signedBranchModuleDecoded 100 100 ∧
    runSignedBranch 50 signedBranchModule 4294967295 0 =
      runSignedBranch 50 signedBranchModuleDecoded 4294967295 0 ∧
    runSignedBranch 100 signedBranchModule 42 43 =
      runSignedBranch 100 signedBranchModuleDecoded 42 43 := by
  native_decide

private def fillThenReadWat : String := include_str "fill_then_read.wat"

private def fillThenReadModuleDecoded : Module :=
  match Wasm.Decoder.Wat.decode fillThenReadWat with
  | .ok m => m
  | .error _ => default

private def runFillThenRead (fuel : Nat) (m : Module) (val : UInt32) : Option (List Value) :=
  match initConfig { module := m, host := (default : HostEnv Unit) } 0
      m.initialStore [.i32 val] with
  | .error _ => none
  | .ok config => (runSteps fuel config).result.values?

theorem fillThenRead_decoded_agrees :
    runFillThenRead 10 fillThenReadModule 0 = runFillThenRead 10 fillThenReadModuleDecoded 0 ∧
    runFillThenRead 15 fillThenReadModule 5 = runFillThenRead 15 fillThenReadModuleDecoded 5 ∧
    runFillThenRead 20 fillThenReadModule 255 = runFillThenRead 20 fillThenReadModuleDecoded 255 ∧
    runFillThenRead 50 fillThenReadModule 171 = runFillThenRead 50 fillThenReadModuleDecoded 171 ∧
    runFillThenRead 100 fillThenReadModule 1000 =
      runFillThenRead 100 fillThenReadModuleDecoded 1000 := by
  native_decide

private def exceptionLifecycleWat : String := include_str "exception_lifecycle.wat"

private def exceptionLifecycleModuleDecoded : Module :=
  match Wasm.Decoder.Wat.decode exceptionLifecycleWat with
  | .ok m => m
  | .error _ => default

private def runExceptionLifecycle (fuel : Nat) (m : Module) (arg : UInt32) :
    Option (List Value) :=
  match initConfig { module := m, host := (default : HostEnv Unit) } 0
      m.initialStore [.i32 arg] with
  | .error _ => none
  | .ok config => (runSteps fuel config).result.values?

theorem exceptionLifecycle_decoded_agrees :
    runExceptionLifecycle 10 exceptionLifecycleModule 0 =
      runExceptionLifecycle 10 exceptionLifecycleModuleDecoded 0 ∧
    runExceptionLifecycle 15 exceptionLifecycleModule 5 =
      runExceptionLifecycle 15 exceptionLifecycleModuleDecoded 5 ∧
    runExceptionLifecycle 20 exceptionLifecycleModule 100 =
      runExceptionLifecycle 20 exceptionLifecycleModuleDecoded 100 ∧
    runExceptionLifecycle 50 exceptionLifecycleModule 255 =
      runExceptionLifecycle 50 exceptionLifecycleModuleDecoded 255 ∧
    runExceptionLifecycle 100 exceptionLifecycleModule 1000 =
      runExceptionLifecycle 100 exceptionLifecycleModuleDecoded 1000 := by
  native_decide

end Wasm.SmallStep
